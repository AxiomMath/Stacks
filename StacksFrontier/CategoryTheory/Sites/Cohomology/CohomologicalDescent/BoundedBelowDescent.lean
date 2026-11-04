module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.PullbackExactness
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomological descent for bounded below complexes

Let `f : (Sh(C), O_X) ⟶ (Sh(D), O_Y)` be a flat morphism of ringed topoi and let `Lf^* ⊣ Rf_*`
be the derived adjunction. For a bounded below object `K`:

* if `H^q(K) ⟶ Rf_*Lf^*H^q(K)` is an isomorphism for every `q`, then so is `K ⟶ Rf_*Lf^*K`;
* dually, if `Lf^*Rf_*H^q(K) ⟶ H^q(K)` is an isomorphism for every `q`, then so is
  `Lf^*Rf_*K ⟶ K`.

The two statements are one theorem,
`CategoryTheory.NatTrans.isIso_app_of_isGE`, read at the unit and at the counit of the
adjunction: nothing in the argument uses the geometry, only that both `Lf^*` and `Rf_*` are
exact, commute with the shift, and keep an object of `D^{≥n}` in `D^{≥n}`. This file supplies
those three facts for the derived adjunction of a flat morphism and reads the theorem off.

## Main results

* `Stacks.Cohomology.CohomologicalDescent.isIso_derivedPullbackComparison`: for a morphism along
  which degreewise pullback is exact, the derived pullback *is* degreewise pullback: the
  canonical comparison is invertible.
* `Stacks.Cohomology.CohomologicalDescent.derivedPullbackObjIso`: consequently `Lf^*K` is
  `f^*` of `K` computed in the derived category.
* `Stacks.Cohomology.CohomologicalDescent.isGE_derivedPullback_obj` and
  `isLE_derivedPullback_obj`: `Lf^*` preserves boundedness below and above.
* `Stacks.Cohomology.CohomologicalDescent.isGE_derivedPushforward_obj`: `Rf_*` preserves
  boundedness below.
* `Stacks.Cohomology.CohomologicalDescent.isIso_derivedUnit_app_of_isIso_homology`:
  **the unit statement.**
* `Stacks.Cohomology.CohomologicalDescent.isIso_derivedCounit_app_of_isIso_homology`:
  **the counit statement.**

## Implementation notes

**Flatness and the morphism-of-sites condition are the hypotheses of the source, not additions.**
Flatness of `f` is flatness of the inverse-image form `f⁻¹O_Y ⟶ O_X` of its structure map, and
`f.u.IsMorphismOfSites` is what makes the continuous functor `f.u` present a morphism of topoi at
all. Together they give exactness of degreewise pullback
(`AlgebraicGeometry.RingedToposSiteHom.pullbackTopos_exact`), and everything below is derived from
*that*: the derived pullback exists, the adjunction exists, both derived functors are exact, and
no further hypothesis on `f` is carried.

**`Rf_*` preserves boundedness below for formal reasons.** `D^{≥n}` is the right orthogonal of
`D^{≤n-1}`, and a morphism from an object of `D^{≤n-1}` into `Rf_*K` is adjoint to a morphism
from `Lf^*` of that object — which is still in `D^{≤n-1}`, because `Lf^*` is exact — into `K`,
hence zero. So only the statement for `Lf^*` needs the computation, and that one is
`isIso_derivedPullbackComparison` together with the fact that an exact functor commutes with the
cohomology functors of the derived category.

**Why the general theorem is stated for a pair of endofunctors.** At the unit the pair is
`(𝟭, Lf^* ⋙ Rf_*)` on `D(O_Y)` and at the counit it is `(Rf_* ⋙ Lf^*, 𝟭)` on `D(O_X)`; stating
it for `η : H₁ ⟶ H₂` is what makes the two instances of one proof rather than two proofs.

**The two main statements open with `letI`, and that is the faithful shape.** The *type* of
`Lf^*` mentions the instance that says degreewise pullback has a left derived functor, so the
unit cannot even be written down before that instance is in scope. Taking it — or exactness of
`f^*`, which supplies it — as an instance hypothesis would state something weaker than the
source: it would be a statement about a morphism along which pullback happens to be exact, not
about a *flat* morphism. So the two instances are produced from `hmos` and the flatness
hypothesis inside the statement, by the same device Mathlib uses in
`CategoryTheory.Functor.IsRightDerivedFunctor`-style statements and this tree uses in
`CategoryTheory.Functor.IsLeftDerivedFunctor.natTrans_commShift`. Nothing about `f`
beyond flatness and the morphism-of-sites condition appears anywhere in either statement.

## References

* [Stacks Project, Tag 0D7T](https://stacks.math.columbia.edu/tag/0D7T)
* [Stacks Project, Tag 0D7S](https://stacks.math.columbia.edu/tag/0D7S)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.CohomologicalDescent

universe w

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposSiteHom X Y)

section Exact

variable [PreservesFiniteLimits f.pullbackTopos] [PreservesFiniteColimits f.pullbackTopos]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (ComplexShape.up ℤ))]

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **For a morphism along which degreewise pullback is exact, the derived pullback is computed
by degreewise pullback.** An exact functor carries every quasi-isomorphism to a
quasi-isomorphism, so degreewise pullback followed by localization inverts the whole class the
derived functor is taken with respect to, and the canonical comparison of a total left derived
functor of an inverting functor is invertible. -/
theorem isIso_derivedPullbackComparison : IsIso (derivedPullbackComparison f) :=
  Functor.isIso_of_isLeftDerivedFunctor_of_inverts (derivedPullback f)
    (derivedPullbackComparison f)
    (Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso
      f.pullbackTopos)

/-- `Lf^*K` is `f^*` of `K`, computed in the derived category: the derived pullback agrees with
the functor induced on derived categories by the exact functor `f^*`. -/
noncomputable def derivedPullbackObjIso
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullback f).obj K ≅ f.pullbackTopos.mapDerivedCategory.obj K :=
  have := isIso_derivedPullbackComparison f
  (derivedPullback f).mapIso (DerivedCategory.Qh.objObjPreimageIso K).symm ≪≫
    asIso ((derivedPullbackComparison f).app (DerivedCategory.Qh.objPreimage K)) ≪≫
      (f.pullbackTopos.mapDerivedCategoryFactorsh.app
        (DerivedCategory.Qh.objPreimage K)).symm ≪≫
        f.pullbackTopos.mapDerivedCategory.mapIso (DerivedCategory.Qh.objObjPreimageIso K)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The derived pullback preserves boundedness below.** It is degreewise pullback, which is
exact, and an exact functor commutes with the cohomology functors. -/
theorem isGE_derivedPullback_obj
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (n : ℤ)
    (hK : K.IsGE n) : ((derivedPullback f).obj K).IsGE n := by
  have := hK
  have hmap : (f.pullbackTopos.mapDerivedCategory.obj K).IsGE n := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact (f.pullbackTopos.map_isZero
      (DerivedCategory.isZero_of_isGE K n i hi)).of_iso
        ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
          f.pullbackTopos i).app K)
  exact DerivedCategory.TStructure.t.isGE_of_iso (derivedPullbackObjIso f K).symm n

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The derived pullback preserves boundedness above**, by the same argument. -/
theorem isLE_derivedPullback_obj
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))) (n : ℤ)
    (hK : K.IsLE n) : ((derivedPullback f).obj K).IsLE n := by
  have := hK
  have hmap : (f.pullbackTopos.mapDerivedCategory.obj K).IsLE n := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact (f.pullbackTopos.map_isZero
      (DerivedCategory.isZero_of_isLE K n i hi)).of_iso
        ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
          f.pullbackTopos i).app K)
  exact DerivedCategory.TStructure.t.isLE_of_iso (derivedPullbackObjIso f K).symm n

/-- **The derived pushforward preserves boundedness below.** This is
`Stacks.Sheaves.RingedToposDerivedPullback.isGE_derivedPushforward_obj_of_adjunction` at the
adjunction supplied by exactness of degreewise pullback. -/
theorem isGE_derivedPushforward_obj
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (n : ℤ) (hK : K.IsGE n) : ((derivedPushforward f).obj K).IsGE n :=
  have : (derivedPullback f).IsTriangulated :=
    Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated f
      (Stacks.Sheaves.RingedToposDerivedPullback.pullbackInvertsQuasiIso_isKFlat_of_exact f)
  Stacks.Sheaves.RingedToposDerivedPullback.isGE_derivedPushforward_obj_of_adjunction f
    (derivedPullbackPushforwardAdjunctionOfExact f)
    (fun L m hL => isLE_derivedPullback_obj f L m hL) K n hK

/-- Under exactness of degreewise pullback, the derived adjunction is triangulated, with the
commutation with shifts it inherits from the derived pullback. -/
private theorem exists_isTriangulated_adjunction {P : Prop}
    (h : ∀ [(derivedPullback f).IsTriangulated] [(derivedPushforward f).CommShift ℤ]
      [(derivedPullbackPushforwardAdjunctionOfExact f).CommShift ℤ]
      [(derivedPullbackPushforwardAdjunctionOfExact f).IsTriangulated], P) : P := by
  let : (derivedPullback f).IsTriangulated :=
    Stacks.Sheaves.RingedToposDerivedPullback.derivedPullback_isTriangulated f
      (Stacks.Sheaves.RingedToposDerivedPullback.pullbackInvertsQuasiIso_isKFlat_of_exact f)
  set adj := derivedPullbackPushforwardAdjunctionOfExact f with hadj
  let : (derivedPushforward f).CommShift ℤ := adj.rightAdjointCommShift ℤ
  let : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  let : adj.IsTriangulated := Adjunction.IsTriangulated.mk' adj
  exact h

end Exact

section Descent

variable (hmos : f.u.IsMorphismOfSites Y.J X.J)
  (hf : SheafOfModules.IsFlatMapULift.{w, w, w} (StacksPullbackFactorization.auxHomH f).fSharp)

include hmos hf

/-- **Stacks 0D7T.** Let `f` be a flat morphism of ringed topoi and let `K` be a bounded below
object of `D(O_Y)`. If the unit `H^q(K) ⟶ Rf_*Lf^*H^q(K)` of the derived adjunction is an
isomorphism for every `q`, with each cohomology object placed in degree zero, then the unit
`K ⟶ Rf_*Lf^*K` is an isomorphism.

The pair of functors is `(𝟭, Lf^* ⋙ Rf_*)`: both are exact, both commute with the shift, and
both carry `D^{≥m}` into `D^{≥m}`, so this is
`CategoryTheory.NatTrans.isIso_app_of_isGE` at the unit. -/
@[stacks 0D7T]
theorem isIso_derivedUnit_app_of_isIso_homology :
    letI := f.pullbackTopos_preservesFiniteLimits hmos hf
    letI := f.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
    ∀ (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))),
      DerivedCategory.TStructure.t.plus K →
      (∀ q : ℤ, IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q).obj K)))) →
      IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app K) := by
  let := f.pullbackTopos_preservesFiniteLimits hmos hf
  let := f.pullbackTopos_preservesFiniteColimits
  let := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
  intro K hK hH
  obtain ⟨a, hGE⟩ := hK
  refine exists_isTriangulated_adjunction f ?_
  exact NatTrans.isIso_app_of_isGE (derivedPullbackPushforwardAdjunctionOfExact f).unit
    (fun _ _ h ↦ h)
    (fun L m h ↦ isGE_derivedPushforward_obj f _ m (isGE_derivedPullback_obj f L m h)) K a hGE hH

/-- **Stacks 0D7S.** Let `f` be a flat morphism of ringed topoi and let `K` be a bounded below
object of `D(O_X)`. If the counit `Lf^*Rf_*H^q(K) ⟶ H^q(K)` of the derived adjunction is an
isomorphism for every `q`, with each cohomology object placed in degree zero, then the counit
`Lf^*Rf_*K ⟶ K` is an isomorphism.

This is the previous statement with the pair of functors reversed: here it is
`(Rf_* ⋙ Lf^*, 𝟭)`, and the theorem applied at the counit. -/
@[stacks 0D7S]
theorem isIso_derivedCounit_app_of_isIso_homology :
    letI := f.pullbackTopos_preservesFiniteLimits hmos hf
    letI := f.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
    ∀ (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
      DerivedCategory.TStructure.t.plus K →
      (∀ q : ℤ, IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app
        ((DerivedCategory.singleFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).obj K)))) →
      IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app K) := by
  let := f.pullbackTopos_preservesFiniteLimits hmos hf
  let := f.pullbackTopos_preservesFiniteColimits
  let := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
  intro K hK hH
  obtain ⟨a, hGE⟩ := hK
  refine exists_isTriangulated_adjunction f ?_
  exact NatTrans.isIso_app_of_isGE (derivedPullbackPushforwardAdjunctionOfExact f).counit
    (fun L m h ↦ isGE_derivedPullback_obj f _ m (isGE_derivedPushforward_obj f L m h))
    (fun _ _ h ↦ h) K a hGE hH

end Descent

end Stacks.Cohomology.CohomologicalDescent

end
