@eval Base.IRShow begin

function show_ir(io::IO, code::IRCode, expr_type_printer=default_expr_type_printer; verbose_linetable=false)
    cols = (displaysize(io)::Tuple{Int,Int})[2]
    used = BitSet()
    stmts = code.stmts
    isempty(stmts) && return # unlikely, but avoid errors from reducing over empty sets
    cfg = code.cfg
    max_bb_idx_size = length(string(length(cfg.blocks)))
    new_nodes = code.new_nodes.stmts
    new_nodes_info = code.new_nodes.info
    bb_idx = 1
    for stmt in stmts
        scan_ssa_use!(push!, used, stmt[:inst])
    end
    if any(i -> !isassigned(new_nodes.inst, i), 1:length(new_nodes))
        printstyled(io, "ERROR: New node array has unset entry\n", color=:red)
        new_nodes_perm = filter(i -> isassigned(new_nodes.inst, i), 1:length(new_nodes))
    else
        new_nodes_perm = collect(1:length(new_nodes))
    end
    for nn in new_nodes_perm
        scan_ssa_use!(push!, used, new_nodes[nn][:inst])
    end
    sort!(new_nodes_perm, by = x -> (x = new_nodes_info[x]; (x.pos, x.attach_after)))
    perm_idx = 1

    if isempty(used)
        maxlength_idx = 0
    else
        maxused = maximum(used)
        maxlength_idx = length(string(maxused))
    end
    if !verbose_linetable
        (loc_annotations, loc_methods, loc_lineno) = compute_ir_line_annotations(code)
        max_loc_width = maximum(length(str) for str in loc_annotations)
        max_lineno_width = maximum(length(str) for str in loc_lineno)
        max_method_width = maximum(length(str) for str in loc_methods)
    end
    max_depth = maximum(compute_inlining_depth(code.linetable, stmts[i][:line]) for i in 1:length(stmts.line))
    last_stack = []
    for idx in 1:length(stmts)
        bb_idx = show_ir_stmt2(io, code, idx, expr_type_printer; verbose_linetable)
    end
end

_stmts(code::IRCode) = code.stmts
_stmts(code::CodeInfo) = code.code

_types(code::IRCode) = code.argtypes
_types(code::CodeInfo) = code.ssavaluetypes

function ircode_default_linfo_printer(code::IRCode)
    loc_annotations, loc_methods, loc_lineno = compute_ir_line_annotations(code)
    max_loc_width = maximum(length, loc_annotations)
    max_lineno_width = maximum(length, loc_lineno)
    max_method_width = maximum(length, loc_methods)

    function (io::IO, indent::String, idx::Int)
        cols = (displaysize(io)::Tuple{Int,Int})[2]

        if idx <= length(loc_annotations)
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
    end
end

function ircode_verbose_linfo_printer(code::IRCode)
    stmts = code.stmts
    max_depth = maximum(compute_inlining_depth(code.linetable, stmts[i][:line]) for i in 1:length(stmts.line))
    last_stack = Ref(Int[])

    function (io::IO, indent::String, idx::Int)
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
                print(io, bb_guard_rail)
                ssa_guard = " "^(maxlength_idx + 4 + (i - 1))
                entry_label = "$(ssa_guard)$(method_name(entry)) at $(entry.file):$(entry.line) "
                hline = string("─"^(start_column-length(entry_label)-length(bb_guard_rail)+max_depth-i), "┐")
                printstyled(io, string(entry_label, hline), "\n"; color=:light_black)
                bb_guard_rail = bb_guard_rail_cont
                floop = false
            end
        end
        printstyled(io, "\e[$(start_column)G$(rail)\e[1G", color = :light_black)
        last_stack[] = stack
    end
end

function show_ir_stmt2(io::IO, code::Union{IRCode, CodeInfo}, idx::Int, expr_type_printer; verbose_linetable)
    stmts = _stmts(code)
    types = _types(code)
    max_bb_idx_size = length(string(length(cfg.blocks)))

    if !isassigned(stmts.inst, idx)
        # This is invalid, but do something useful rather
        # than erroring, to make debugging easier
        printstyled(io, "#UNDEF\n", color=:red)
        return bb_idx
    end
    stmt = stmts[idx]
    # Compute BB guard rail
    if bb_idx > length(cfg.blocks)
        # Even if invariants are violated, try our best to still print
        bbrange = (length(cfg.blocks) == 0 ? 1 : last(cfg.blocks[end].stmts) + 1):typemax(Int)
        bb_idx_str = "!"
        bb_type = "─"
    else
        bbrange = cfg.blocks[bb_idx].stmts
        bbrange = bbrange.start:bbrange.stop
        bb_idx_str = string(bb_idx)
        bb_type = length(cfg.blocks[bb_idx].preds) <= 1 ? "─" : "┄"
    end
    bb_pad = max_bb_idx_size - length(bb_idx_str)
    bb_start_str = string(bb_idx_str, " ", bb_type, "─"^bb_pad, " ")
    bb_guard_rail_cont = string("│  ", " "^max_bb_idx_size)
    if idx == first(bbrange)
        bb_guard_rail = bb_start_str
    else
        bb_guard_rail = bb_guard_rail_cont
    end
    floop = true
    # Print linetable information
    if verbose_linetable
        stack = compute_loc_stack(code.linetable, stmt[:line])
        # We need to print any stack frames that did not exist in the last stack
        ndepth = max(1, length(stack))
        rail = string(" "^(max_depth+1-ndepth), "│"^ndepth)
        start_column = cols - max_depth - 10
        for (i, x) in enumerate(stack)
            if i > length(last_stack) || last_stack[i] != x
                entry = code.linetable[x]
                printstyled(io, "\e[$(start_column)G$(rail)\e[1G", color = :light_black)
                print(io, bb_guard_rail)
                ssa_guard = " "^(maxlength_idx + 4 + (i - 1))
                entry_label = "$(ssa_guard)$(method_name(entry)) at $(entry.file):$(entry.line) "
                hline = string("─"^(start_column-length(entry_label)-length(bb_guard_rail)+max_depth-i), "┐")
                printstyled(io, string(entry_label, hline), "\n"; color=:light_black)
                bb_guard_rail = bb_guard_rail_cont
                floop = false
            end
        end
        printstyled(io, "\e[$(start_column)G$(rail)\e[1G", color = :light_black)
        last_stack = stack
    else
        if idx <= length(loc_annotations)
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
    end
    idx != last(bbrange) && print(io, bb_guard_rail)
    print_sep = false
    if idx == last(bbrange)
        print_sep = true
    end
    # print new nodes first in the right position
    while perm_idx <= length(new_nodes_perm)
        node_idx = new_nodes_perm[perm_idx]
        if new_nodes_info[node_idx].pos != idx
            break
        end
        perm_idx += 1
        if !floop && !verbose_linetable
            print(io, " "^(max_lineno_width + 1))
        end
        if print_sep
            if idx == first(bbrange) && floop
                print(io, bb_start_str)
            else
                print(io, "│  ", " "^max_bb_idx_size)
            end
        end
        print_sep = true
        floop = false
        new_node = new_nodes[node_idx]
        node_idx += length(stmts)
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
    end
    if !floop && !verbose_linetable
        print(io, " "^(max_lineno_width + 1))
    end
    if print_sep
        if idx == first(bbrange) && floop
            print(io, bb_start_str)
        elseif idx == last(bbrange)
            print(io, "└", "─"^(1 + max_bb_idx_size), " ")
        else
            print(io, "│  ", " "^max_bb_idx_size)
        end
    end
    if idx == last(bbrange)
        bb_idx += 1
    end
    show_type = should_print_ssa_type(stmt[:inst])
    print_stmt(io, idx, stmt[:inst], used, maxlength_idx, true, show_type)
    if !isassigned(stmts.type, idx) # try to be robust against errors
        printstyled(io, "::#UNDEF", color=:red)
    elseif show_type
        expr_type_printer(io, stmt[:type], idx in used)
    end
    println(io)
end
