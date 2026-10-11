import Whatwg
import WhatwgTest.Audit.AutoCensus

/-! Invocations of the auto census (ruling R-S10 of `COORDINATION.md`). Run it from the
repository root after `lake build`, and edit the lines below to the module and the bank under
study:

    lake env lean workshop/AutoCensus.lean

Each line reports which theorems of a module the search closes from their statements alone.
No module imports this file, and no gate reads its output. -/

#whatwg_auto_census Whatwg.Svg.Data.Mask using aesop (rule_sets := [Whatwg.Mask])
#whatwg_auto_census Whatwg.Svg.Content.Context using aesop (rule_sets := [Whatwg.Mask])
#whatwg_auto_census Whatwg.Html.Svg using aesop
#whatwg_auto_census Whatwg.Html.Content.Valid using aesop