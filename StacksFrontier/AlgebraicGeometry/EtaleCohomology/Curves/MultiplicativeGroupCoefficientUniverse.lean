module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupSmoothCurveVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleCoefficientLift
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NonemptyOpen

/-!
# Stacks 03RM at every coefficient universe, and on the opens of a smooth curve

Stacks 03RM, `H^q_étale(X, 𝐆_m) = 0` for `q ≥ 2` on a smooth curve `X` over an algebraically
closed field, is proved in the library at the coefficient universe `u + 1` with `Ext` in universe
`u + 1` (`Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve`). The
statements of Situation 0A52 are made at the étale coefficient universe `max (u + 1) v` with an
arbitrary `Ext` universe. This file transports the vanishing there, and records that a nonempty
open subscheme of a curve is a curve, so that the vanishing applies to the opens of `X` as well.

## Main results

* `AlgebraicGeometry.isCurve_opensι_comp`: a nonempty open subscheme of a curve is a curve.
* `Stacks.EtaleCohomology.multiplicativeSheafUliftIso`: `𝐆_m` at the coefficient universe
  `max (u + 1) v` is the universe lift of `𝐆_m` at `u + 1`.
* `Stacks.EtaleCohomology.subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve_univ`:
  **Stacks 03RM** at the coefficient universe `max (u + 1) v` and any `Ext` universe.

## Implementation notes

The transport is `Stacks.Cohomology.CoefficientLift.subsingleton_sheafH_ulift_iff`, whose two
hypotheses on the small étale site — compatibility of the universe lift with sheafification and
preservation of injective objects — are `AlgebraicGeometry.etaleUlift_properties`.

## References

* [Stacks Project, Tag 03RM](https://stacks.math.columbia.edu/tag/03RM)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u v w

namespace AlgebraicGeometry

/-- **A nonempty open subscheme of a curve is a curve.** It is integral as a nonempty open
subscheme of an integral scheme, separated and of finite type as an open subscheme of a
Noetherian separated scheme of finite type, and of dimension one by Tag 0A21. -/
theorem isCurve_opensι_comp (k : Type u) [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
    [IsCurve k g] (U : X.Opens) [Nonempty U] : IsCurve k (U.ι ≫ g) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian g
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace g
  have : IsNoetherian X := { }
  have : CompactSpace U :=
    isCompact_iff_compactSpace.mp (TopologicalSpace.NoetherianSpace.isCompact _)
  have : QuasiCompact (U.ι ≫ g) := (quasiCompact_iff_compactSpace _).mpr inferInstance
  refine (isCurve_iff k _).2 ⟨{ }, ?_⟩
  rw [← IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)]
  obtain ⟨x⟩ := ‹Nonempty U›
  exact (topologicalKrullDim_eq_of_isOpen k X g (U : Set X) U.isOpen ⟨x.1, x.2⟩).symm

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

open Stacks.Cohomology.CoefficientLift

/-- **`𝐆_m` at the étale coefficient universe is the universe lift of `𝐆_m` at `u + 1`.** Both
have the invertible global functions of an étale `X`-scheme as sections, up to the two `ULift`s. -/
def multiplicativeSheafUliftIso (X : Scheme.{u}) :
    (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{v, u + 1}).obj
        (Stacks.Kummer.multiplicativeSheaf.{u, u + 1} X) ≅
      Stacks.Kummer.multiplicativeSheaf.{u, v} X :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents
      (fun _ => AddEquiv.toAddCommGrpIso
        ((AddEquiv.ulift.trans AddEquiv.ulift).trans AddEquiv.ulift.symm))
      (fun _ => rfl))

/-- Universe lifting of the coefficients is compatible with sheafification on the small étale
site, from `u + 1` to `max (u + 1) v`. -/
local instance preservesSheafification_uliftFunctor_succ (X : Scheme.{u}) :
    X.smallEtaleTopology.PreservesSheafification AddCommGrpCat.uliftFunctor.{v, u + 1} :=
  (etaleUlift_properties.{u, u + 1, v} X).1

/-- Universe lifting of the coefficients preserves injective sheaves on the small étale site,
from `u + 1` to `max (u + 1) v`. -/
local instance preservesInjectiveObjects_uliftFunctor_succ (X : Scheme.{u}) :
    (sheafCompose X.smallEtaleTopology
      AddCommGrpCat.uliftFunctor.{v, u + 1}).PreservesInjectiveObjects :=
  (etaleUlift_properties.{u, u + 1, v} X).2

/-- **Raising the coefficient universe from `u + 1` preserves vanishing of étale cohomology.**
If the degree-`n` étale cohomology of `F` at coefficients `AddCommGrpCat.{u + 1}` (and `Ext` in
universe `u + 1`) vanishes, so does the cohomology of every sheaf at the coefficient universe
`max (u + 1) v` isomorphic to its universe lift, in every `Ext` universe. -/
theorem subsingleton_sheafH_of_iso_ulift {X : Scheme.{u}}
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (e : (sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{v, u + 1}).obj F ≅ G)
    (n : ℕ)
    (h : haveI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
      Subsingleton (Sheaf.H.{u + 1, u + 1} F n)) :
    Subsingleton (Sheaf.H.{w} G n) := by
  have := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  have : EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    enoughInjectives_sheaf_smallEtale.{u, u + 1} X
  exact (subsingleton_sheafH_congr e n).1
    ((subsingleton_sheafH_ulift_iff.{u + 1, u + 1, v, w} X.smallEtaleTopology F n).2 h)

/-- **Stacks Project, Tag 03RM, at the étale coefficient universe.** Let `X` be a smooth curve
over an algebraically closed field `k`. Then `H^q_étale(X, 𝐆_m) = 0` for every `q ≥ 2`, for `𝐆_m`
with coefficients in `AddCommGrpCat.{max (u + 1) v}` and cohomology in any `Ext` universe. -/
theorem subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve_univ {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} X) q) :=
  subsingleton_sheafH_of_iso_ulift _ _ (multiplicativeSheafUliftIso.{u, v} X) q
    (subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve g q hq)

/-- **Stacks 03RM on a nonempty open subscheme of a smooth curve**: for every nonempty open `U`
of a smooth curve `X` over an algebraically closed field, `H^q_étale(U, 𝐆_m) = 0` for `q ≥ 2`,
`U` being again a smooth curve. -/
theorem subsingleton_sheafH_multiplicativeSheaf_opens_of_smoothCurve {k : Type u} [Field k]
    [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]
    (U : X.Opens) [Nonempty U]
    [HasExt.{w} (Sheaf (U : Scheme.{u}).smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (q : ℕ) (hq : 2 ≤ q) :
    Subsingleton (Sheaf.H.{w} (Stacks.Kummer.multiplicativeSheaf.{u, v} (U : Scheme.{u})) q) :=
  have := isCurve_opensι_comp k g U
  subsingleton_sheafH_multiplicativeSheaf_of_smoothCurve_univ (U.ι ≫ g) q hq

end Stacks.EtaleCohomology

end
