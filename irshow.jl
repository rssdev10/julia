@eval Base.IRShow begin

function show_ir(io::IO, code::IRCode, expr_type_printer=default_expr_type_printer; verbose_linetable=false)
    cols = (displaysize(io)::Tuple{Int,Int})[2]
    used = BitSet()
    stmts = code.stmts
    isempty(stmts) && return # unlikely, but avoid errors from reducing over empty sets
    cfg = code.cfg
    bb_idx = 1
    for stmt in stmts
        scan_ssa_use!(push!, used, stmt[:inst])
    end
    pop_newnode! = ircode_new_nodes_iter(code, used)
    if verbose_linetable
        line_info_preprinter = ircode_verbose_linfo_printer(code, used)
    else
        line_info_preprinter = ircode_default_linfo_printer(code)
    end
    for idx in 1:length(stmts)
        bb_idx = show_ir_stmt2(io, code, idx, line_info_preprinter, default_expr_type_printer, used, cfg, bb_idx, pop_newnode!)
    end
end

function ircode_new_nodes_iter(code::IRCode, used::BitSet)
    stmts = code.stmts
    new_nodes = code.new_nodes.stmts
    new_nodes_info = code.new_nodes.info
    new_nodes_perm = if any(i -> !isassigned(new_nodes.inst, i), 1:length(new_nodes))
        printstyled(io, "ERROR: New node array has unset entry\n", color=:red)
        filter(i -> isassigned(new_nodes.inst, i), 1:length(new_nodes))
    else
        collect(1:length(new_nodes))
    end
    for nn in new_nodes_perm
        scan_ssa_use!(push!, used, new_nodes[nn][:inst])
    end
    sort!(new_nodes_perm, by = x -> (x = new_nodes_info[x]; (x.pos, x.attach_after)))
    perm_idx = Ref(1)

    function (idx::Int)
        perm_idx[] <= length(new_nodes_perm) || return nothing
        node_idx = new_nodes_perm[perm_idx[]]
        if new_nodes_info[node_idx].pos != idx
            return nothing
        end
        perm_idx[] += 1
        new_node = new_nodes[node_idx]
        node_idx += length(stmts)
        return node_idx, new_node
    end
end

function ircode_default_linfo_printer(code::IRCode)
    loc_annotations, loc_methods, loc_lineno = compute_ir_line_annotations(code)
    max_loc_width = maximum(length, loc_annotations)
    max_lineno_width = maximum(length, loc_lineno)
    max_method_width = maximum(length, loc_methods)

    function (io::IO, indent::String, idx::Int)
        cols = (displaysize(io)::Tuple{Int,Int})[2]

        if idx == 0
            annotation = ""
            loc_method = ""
            lineno = ""
        elseif idx <= length(loc_annotations)
            # N.B.: The line array length not matching is invalid,
            # but let's be robust here
            annotation = loc_annotations[idx]
            loc_method = loc_methods[idx]
            lineno = loc_lineno[idx]
        else
            annotation = "!"
            loc_method = ""
            lineno = ""
        end
        # Print location information right aligned. If the line below is too long, it'll overwrite this,
        # but that's what we want.
        if get(io, :color, false)
            method_start_column = cols - max_method_width - max_loc_width - 2
            filler = " "^(max_loc_width-length(annotation))
            printstyled(io, "\e[$(method_start_column)G$(annotation)$(filler)$(loc_method)\e[1G", color = :light_black)
        end
        printstyled(io, lineno, " "^(max_lineno_width - length(lineno) + 1); color = :light_black)
        return ""
    end
end

function ircode_verbose_linfo_printer(code::IRCode, used::BitSet)
    stmts = code.stmts
    max_depth = maximum(compute_inlining_depth(code.linetable, stmts[i][:line]) for i in 1:length(stmts.line))
    last_stack = Ref(Int[])
    maxlength_idx = if isempty(used)
        0
    else
        maxused = maximum(used)
        length(string(maxused))
    end

    function (io::IO, indent::String, idx::Int)
        idx == 0 && return ""
        cols = (displaysize(io)::Tuple{Int,Int})[2]
        stmt = stmts[idx]

        stack = compute_loc_stack(code.linetable, stmt[:line])
        # We need to print any stack frames that did not exist in the last stack
        ndepth = max(1, length(stack))
        rail = string(" "^(max_depth+1-ndepth), "│"^ndepth)
        start_column = cols - max_depth - 10
        for (i, x) in enumerate(stack)
            if i > length(last_stack[]) || last_stack[][i] != x
                entry = code.linetable[x]
                printstyled(io, "\e[$(start_column)G$(rail)\e[1G", color = :light_black)
                print(io, indent)
                ssa_guard = " "^(maxlength_idx + 4 + i)
                entry_label = "$(ssa_guard)$(method_name(entry)) at $(entry.file):$(entry.line) "
                hline = string("─"^(start_column-length(entry_label)-length(indent)+max_depth-i), "┐")
                printstyled(io, string(entry_label, hline), "\n"; color=:light_black)
            end
        end
        last_stack[] = stack
        printstyled(io, "\e[$(start_column)G$(rail)\e[1G", color = :light_black)
        return ""
    end
end

_stmts(code::IRCode) = code.stmts
_stmts(code::CodeInfo) = code.code

_types(code::IRCode) = code.argtypes
_types(code::CodeInfo) = code.ssavaluetypes

function normalize_statement_indices(@nospecialize(stmt), cfg::CFG)
    # convert statement index to labels, as expected by print_stmt
    if stmt isa Expr
        if stmt.head === :enter && length(stmt.args) == 1 && stmt.args[1] isa Int
            stmt = Expr(:enter, block_for_inst(cfg, stmt.args[1]::Int))
        end
    elseif isa(stmt, GotoIfNot)
        stmt = GotoIfNot(stmt.cond, block_for_inst(cfg, stmt.dest))
    elseif stmt isa GotoNode
        stmt = GotoNode(block_for_inst(cfg, stmt.label))
    elseif stmt isa PhiNode
        e = stmt.edges
        stmt = PhiNode(Int32[block_for_inst(cfg, Int(e[i])) for i in 1:length(e)], stmt.values)
    end
end

function show_ir_stmt2(io::IO, code::Union{IRCode, CodeInfo}, idx::Int, line_info_preprinter, line_info_postprinter, used::BitSet, cfg::CFG, bb_idx::Int, pop_newnode! = _ -> nothing)
    stmts = _stmts(code)
    types = _types(code)
    max_bb_idx_size = length(string(length(cfg.blocks)))

    if isempty(used)
        maxlength_idx = 0
    else
        maxused = maximum(used)
        maxlength_idx = length(string(maxused))
    end

    if !isassigned(stmts.inst, idx)
        # This is invalid, but do something useful rather
        # than erroring, to make debugging easier
        printstyled(io, "#UNDEF\n", color=:red)
        return bb_idx
    end
    stmt = stmts[idx]
    # Compute BB guard rail
    if bb_idx > length(cfg.blocks)
        # If invariants are violated, print a special leader
        linestart = " "^(max_bb_idx_size + 2) # not inside a basic block bracket
        inlining_indent = line_info_preprinter(io, linestart, idx)
        printstyled(io, "!!! ", "─"^max_bb_idx_size, color=:light_black)
    else
        bbrange = cfg.blocks[bb_idx].stmts
        bbrange = bbrange.start:bbrange.stop
        # Print line info update
        linestart = idx == first(bbrange) ? "  " : sprint(io -> printstyled(io, "│ ", color=:light_black), context=io)
        linestart *= " "^max_bb_idx_size
        inlining_indent = line_info_preprinter(io, linestart, idx)
        if idx == first(bbrange)
            bb_idx_str = string(bb_idx)
            bb_pad = max_bb_idx_size - length(bb_idx_str)
            bb_type = length(cfg.blocks[bb_idx].preds) <= 1 ? "─" : "┄"
            printstyled(io, bb_idx_str, " ", bb_type, "─"^bb_pad, color=:light_black)
        elseif idx == last(bbrange) # print separator
            printstyled(io, "└", "─"^(1 + max_bb_idx_size), color=:light_black)
        else
            printstyled(io, "│ ", " "^max_bb_idx_size, color=:light_black)
        end
    end
    print(io, inlining_indent, " ")
    
    # print new nodes first in the right position
    while (next = pop_newnode!(idx)) !== nothing
        node_idx, new_node = next
        show_type = should_print_ssa_type(new_node[:inst])
        with_output_color(:green, io) do io′
            print_stmt(io′, node_idx, new_node[:inst], used, maxlength_idx, false, show_type)
        end
        if !isassigned(stmts.type, idx) # try to be robust against errors
            printstyled(io, "::#UNDEF", color=:red)
        elseif show_type
            expr_type_printer(io, new_node[:type], node_idx in used)
        end
        println(io)
        

        # Compute BB guard rail
        if bb_idx > length(cfg.blocks)
            # If invariants are violated, print a special leader
            linestart = " "^(max_bb_idx_size + 2) # not inside a basic block bracket
            inlining_indent = line_info_preprinter(io, linestart, 0)
            printstyled(io, "!!! ", "─"^max_bb_idx_size, color=:light_black)
        else
            bbrange = cfg.blocks[bb_idx].stmts
            bbrange = bbrange.start:bbrange.stop
            # Print line info update
            linestart = idx == first(bbrange) ? "  " : sprint(io -> printstyled(io, "│ ", color=:light_black), context=io)
            linestart *= " "^max_bb_idx_size
            inlining_indent = line_info_preprinter(io, linestart, 0)
            printstyled(io, "│ ", " "^max_bb_idx_size, color=:light_black)
        end
        print(io, inlining_indent, " ")
    end
    show_type = should_print_ssa_type(stmt[:inst])
    print_stmt(io, idx, stmt[:inst], used, maxlength_idx, true, show_type)
    if !isassigned(stmts.type, idx) # try to be robust against errors
        printstyled(io, "::#UNDEF", color=:red)
    elseif show_type
        line_info_postprinter(io, stmt[:type], idx in used)
    end
    println(io)
    if bb_idx <= length(cfg.blocks) && idx == last(bbrange)
        bb_idx += 1
    end
    return bb_idx
end

end
