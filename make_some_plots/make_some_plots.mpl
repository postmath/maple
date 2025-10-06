make_some_plots := module()
# Module for creating 2D and 3D visualizations of Taylor series approximations

local
    # Compute the degree-like measure of an expression with respect to a variable.
    # Returns infinity for transcendental terms or non-polynomial expressions.
    # Logarithmic factors (of polynomials) are ignored.
    degree_ish := proc(expr :: algebraic,
                       nm :: name,
                       $)
        if type(expr, ':-polynom'(':-anything', nm)) then
            return degree(expr, nm);

        elif type(expr, ':-`+`') then
            return max(map(thisproc, [op(expr)], nm));

        elif type(expr, ':-`*`') then
            return add(map(thisproc, [op(expr)], nm));

        elif type(expr, ':-`^`') then
            if depends(op(2, expr), nm) then
                # Transcendental!
                return infinity;

            else
                return op(2, expr) * thisproc(op(1, expr), nm);
            end if;

        elif type(expr, ':-specfunc'({ln, log})) then
            # Logarithms contribute zero degree unless argument is transcendental
            local inner := thisproc(op(expr), nm);
            if type(inner, ':-infinity') then
                # Transcendental!
                return infinity;

            else
                return 0;
            end if;

        else
            # Transcendental!
            return infinity;
        end if;
    end proc;

local
    # Generate Taylor series approximations at multiple degrees.
    # Iteratively increases series order until the desired degree range is achieved.
    make_series := proc(expr :: algebraic,
                        expansionpoint :: name = algebraic,
                        degreerange :: nonnegint .. posint,
                        $)
    local x := lhs(expansionpoint);
    local d := rhs(degreerange);

    local sl, ds;
        # Try up to 6 times with increasing series orders
        to 6 do
            local s := series(expr, expansionpoint, d+1);
            s := convert(s, ':-polynom');
            sl := convert(s, ':-list', ':-`+`');  # Break into list of terms
            ds := map(degree_ish, sl, x);  # Compute degree of each term
            local actual_d := max(remove(type, ds, ':-infinity'));

            if actual_d >= rhs(degreerange) then
                # Build list of approximations for each degree in range
                return [for local dd in [seq(degreerange)] do
                            # Keep only terms up to degree dd
                            local keep := select(i -> ds[i] <= dd, [seq(1 .. numelems(ds))]);
                            add(sl[keep]);
                        end do];
            end if;

            # Increase series order for next iteration
            d := min(d + 15, max(d + 3, ceil(d * 3/2)));
        end do;

        error "unable to determine series up to degree %1", rhs(degreerange);
    end proc;

local
    # Access the internal Plot:-Utilities:-SmartView function.
    # Temporarily disables opaque modules to access private plot utilities.
    plot_smartview := proc($)
    option remember;
        local kom := kernelopts(':-opaquemodules' = false);
        try
            return Plot:-Utilities:-SmartView;
        finally
            kernelopts(':-opaquemodules' = kom);
        end try;
    end proc;

local
    # Determine appropriate y-axis view range using SmartView.
    # Falls back to plot data bounds if SmartView returns no recommendation.
    smartview := proc(plotstructure :: specfunc(PLOT),
                      domain :: float .. float,
                      plotdata :: nonemptylist([string, list, Matrix]),
                      $)
    local sv_result := [plot_smartview()(plotstructure, ':-VIEW'(domain, ':-DEFAULT'), false)];

        if sv_result = [] then
            # No non-default view recommended: use the view from the plot data.
            local pd_views := map(lst -> lst[2][2], plotdata);
            return min(map(lhs, pd_views)) .. max(map(rhs, pd_views));
        else
            return sv_result[2];
        end if;
    end proc;

local
    # Build a 3D mesh array for displaying multiple curves as a surface.
    # Each curve becomes a ribbon at a different y-coordinate, with offset in z.
    make_mesh_rtable := proc(plot_data :: list(list([string, list, Matrix])),
                             offset :: float,
                             domain :: float .. float,
                             low_y :: float,
                             $)
    local l;
    # Determine maximum number of points across all curves
    local n_points := map(lst -> add(upperbound(l[3], 1), l in lst), plot_data);
        n_points := max(n_points);

    # Create array: rows=points, columns=3*number of curves, depth=3 (for x,y,z coords)
    local result := Array(1 .. n_points, 1 .. 3*numelems(plot_data), 1 .. 3,
                          ':-datatype' = ':-float');

    local equally_spaced_x := Vector(n_points, [seq(domain, ':-numelems' = n_points)],
                                     ':-datatype' = ':-float');
        for local i to numelems(plot_data) do
            # Left edge of ribbon (at y = i - 0.1, z = low_y)
            result[.., 3*i-2, 1] := equally_spaced_x;
            result[.., 3*i-2, 2] := i - 0.1;
            result[.., 3*i-2, 3] := low_y;

            # Concatenate all curve segments for this approximation
            local concatenation;
            if numelems(plot_data[i]) = 1 then
                concatenation := plot_data[i][1][3];
            else
                concatenation := `<,>`(op(map(l -> l[3], plot_data[i])));
            end if;

            # Pad with last point if necessary to match n_points
            if upperbound(concatenation, 1) < n_points then
                local to_append := concatenation[-1];
                concatenation := (<concatenation,
                                  to_append $ (n_points - upperbound(concatenation, 1))>);
            end if;

            # Center line of ribbon (the actual curve data, vertically offset)
            result[.., 3*i-1, 1] := concatenation[.., 1];
            result[.., 3*i-1, 2] := i;
            result[.., 3*i-1, 3] := concatenation[.., 2] +~ ((i-1) * offset);

            # Right edge of ribbon (at y = i + 0.1, z = low_y)
            result[.., 3*i, 1] := equally_spaced_x;
            result[.., 3*i, 2] := i + 0.1;
            result[.., 3*i, 3] := low_y;
        end do;

        return result;
end proc;

local
    # Main procedure: creates 2D and 3D plots of Taylor series approximations.
    # Returns a 2D plot (with vertically stacked curves) and a 3D mesh plot.
    ModuleApply := proc(expr :: algebraic,
                        expansionpoint :: name = algebraic,
                        xrange :: range := NULL,
                        yrange :: range := NULL,
                        {yoffset :: algebraic := 0.4},
                        {degreerange :: nonnegint .. posint := 2..5},
                        {includef :: truefalse := false},
                        $)
        if rhs(degreerange) < lhs(degreerange) then
            error "expected: right hand side of degree range greater than left hand side, but "
            "received: %1", degreerange;
        end if;

    local x := lhs(expansionpoint);
    local approximations := make_series(expr, expansionpoint, degreerange);
        if includef then
            approximations := [op(approximations), expr];
        end if;

    local domain;
        if xrange = NULL then
            # Auto-determine x-range using ReasonableDomain.
            # Include (x - expansion_point)^2 to ensure expansion point is visible.
            domain := evalf(ReasonableDomain([op(approximations), (x - rhs(expansionpoint))^2], x));
        else
            domain := evalf(xrange);
        end if;

    # Generate plot structures and extract raw plot data
    local plot_structures := map(plot, approximations, x = domain);
    local plot_data := map([plottools:-getdata], plot_structures);
        
    local codomain;
        if yrange = NULL then
            # Auto-determine y-range by finding intersection of SmartView recommendations
            local views := zip(
                (plotstructure, plotdata) -> smartview(plotstructure, domain, plotdata),
                plot_structures, plot_data);
            codomain := evalf(max(map(lhs, views)) .. min(map(rhs, views)));
        else
            codomain := evalf(yrange);
        end if;

    # Calculate vertical offset between successive curves
    local total_offset := (rhs - lhs)(codomain) * yoffset;
    local offset := total_offset / (numelems(approximations) - 1);

    local mesh_rtable := make_mesh_rtable(plot_data, offset, domain, lhs(codomain));

    local i;
        return (
            # 2D plot: stack curves with vertical translation
            plots:-display([seq(plottools:-translate(plot_structures[i], 0, i * offset),
                                i = 1 .. numelems(approximations))],
                           ':-view' = [':-DEFAULT',
                                       lhs(codomain) .. rhs(codomain) + total_offset]),
            # 3D plot: display as mesh surface with specified orientation
            plots:-display(':-PLOT3D'(':-MESH'(mesh_rtable)),
                           ':-view' = [':-DEFAULT' $ 2,
                                       lhs(codomain) .. rhs(codomain) + total_offset],
                           ':-orientation' = [-100, 60, 0]),
            NULL);
    end proc;
end module;
