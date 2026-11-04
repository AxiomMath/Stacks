module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.BrauerGroupFunctionField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFieldTranscendenceDegreeOne
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.MultiplicativeSheaf
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the étale cohomology of `𝐆_m` over a transcendence-degree-one extension

Let `k` be an algebraically closed field and `K/k` a field extension of transcendence degree
one. Then `H^q_étale(Spec K, 𝐆_m) = 0` for every `q ≥ 1`.

The source's proof has two steps. The first identifies étale cohomology over a field with the
Galois cohomology of the absolute Galois group (Stacks 03QU) and invokes the criterion of
Stacks 03R8: if the Brauer group of every finite extension of `K` is trivial, then the Galois
cohomology of `(K^{sep})^*` vanishes in every positive degree. The second step verifies that
Brauer hypothesis. Only the second step is proved here; the first is carried as the explicit
hypothesis `h03R8`, stated in the étale form in which Stacks 03R8's own proof records it, since
neither the positive-degree part of Stacks 03QU nor Stacks 03R8 is in this library.

## Main results

* `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_trdeg_eq_one`:
  **Stacks 03RG**, over Stacks 03R8 and Stacks 03QU as the single hypothesis `h03R8`.
* `Stacks.EtaleCohomology.brauerGroup_eq_one_of_module_finite_functionField`: the Brauer group of
  every finite extension of the function field of a curve over an algebraically closed field is
  trivial.

## Implementation notes

**The carried hypothesis, and the tags it is.** `h03R8` says: if the Brauer group of every
finite extension of `K` is trivial, then `H^q_étale(Spec K, 𝐆_m) = 0` for `q ≥ 1`. That is
exactly part (1) of **Stacks 03R8** read through **Stacks 03QU**, and it is how Stacks 03R8's
own proof states what it is going to prove — "the proposition is equivalent to showing that if
`H^2(Spec K', 𝐆_m) = 0` for all finite extensions `K'/K` then `H^q(Spec K, 𝐆_m) = 0` for all
`q ≥ 1`", the passage between the Brauer group and `H^2` being Stacks 03R7. Of Stacks 03QU the
library has only part (2), degree zero
(`AlgebraicGeometry.etaleH0AddEquivGaloisInvariants`); of Stacks 03R8 it has nothing. Nothing
else is assumed: the hypotheses on `k` and `K` are the source's, the degree range is the
source's, and the conclusion is quantified over the degree.

**What is proved rather than carried.** The Brauer premise of `h03R8`. The source discharges it
by writing a finite extension `K'/K` as the filtered colimit of its finitely generated
subextensions of transcendence degree one and using that the Brauer group commutes with that
colimit; that commutation is in neither this library nor Mathlib. It is replaced here by
`brauerGroup_eq_one_of_module_finite_of_trdeg_eq_one`, which runs the same reduction one
polynomial at a time on the \(C_1\) property instead — see
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.CFieldTranscendenceDegreeOne`.
This is the whole mathematical content of Stacks 03RG beyond its two citations.

**The function-field form.** For the function field of a curve the Brauer premise is cheaper
still: the function field is already a \(C_1\) field
(`AlgebraicGeometry.isCField_one_functionField`, Stacks 03RF), and a finite extension of a
\(C_1\) field is a \(C_1\) field (`isCField_one_of_module_finite`), so no transcendence-degree
bookkeeping is needed at all. That is
`Stacks.EtaleCohomology.brauerGroup_eq_one_of_module_finite_functionField`.

**Coefficients and pinned universes.** Abelian sheaves are taken with coefficients in
`AddCommGrpCat.{u + 1}` for `K : Type u`, and cohomology is
`CategoryTheory.Sheaf.H.{u + 1, u + 1}`, matching
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupHigherVanishing`. The
Grothendieck abelian structure has to be recorded with its coefficient universe pinned, because
the general instance is indexed by `max (u + 1) v` and instance search cannot solve
`max (u + 1) ?v = u + 1`; that is what makes `HasExt.{u + 1}` available.

## References

* [Stacks Project, Tag 03RG](https://stacks.math.columbia.edu/tag/03RG): the theorem, proved
  here over `h03R8`.
* [Stacks Project, Tag 03R8](https://stacks.math.columbia.edu/tag/03R8): carried, with Tag
  03QU, as `h03R8`.
* [Stacks Project, Tag 03QU](https://stacks.math.columbia.edu/tag/03QU): carried, with Tag
  03R8, as `h03R8`; part (2) alone is in the library.
* [Stacks Project, Tag 03R7](https://stacks.math.columbia.edu/tag/03R7): the identification of
  the Brauer group with `H^2`, which is why `h03R8` may be stated with a Brauer-group premise.
* [Stacks Project, Tag 03RF](https://stacks.math.columbia.edu/tag/03RF): used from the library
  for the function-field form.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- Abelian sheaves on the small étale site of `X : Scheme.{u}` with coefficients in
`AddCommGrpCat.{u + 1}` form a Grothendieck abelian category relative to `u + 1`. This is
`Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale` with its coefficient universe
pinned, which is what makes `HasExt.{u + 1}` available and so
`CategoryTheory.Sheaf.H.{u + 1, u + 1}` elaborate without a hypothesis. -/
local instance isGrothendieckAbelian_sheaf_smallEtale_pinnedCoefficients (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  isGrothendieckAbelian_sheaf_smallEtale.{u, u + 1} X

/-! ### The function field of a curve -/

/-- **The Brauer group of every finite extension of the function field of a curve over an
algebraically closed field is trivial.** The function field is a \(C_1\) field by Stacks 03RF,
a finite extension of a \(C_1\) field is a \(C_1\) field, and a \(C_1\) field has trivial
Brauer group by Stacks 03RC. -/
@[sga "4½ Arcata 3.2.2" "special case"]
theorem brauerGroup_eq_one_of_module_finite_functionField (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] (K' : Type u) [Field K']
    [Algebra X.functionField K'] [Module.Finite X.functionField K'] (y : BrauerGroup K') :
    y = 1 :=
  brauerGroup_eq_one_of_isCField K'
    (isCField_one_of_module_finite _ K' (isCField_one_functionField k f)) y

end Stacks.EtaleCohomology

end
