module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.StrictlyPerfectTensorCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PseudoCoherentEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.DerivedPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceDerivedCategoryPerfect
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.TriangulatedSubcategory

/-!
# `E ⊗^L K` is pseudo-coherent for `E` perfect and `K` pseudo-coherent on an algebraic space

Let `X` be an algebraic space. If `E` is a perfect and `K` a pseudo-coherent object of
`D(𝒪_X)`, then `E ⊗^L_{𝒪_X} K` is pseudo-coherent. This is the case of Stacks 09J9 (2) in which
the first factor is perfect, on the small étale site of `X`, for the derived tensor product
`AlgebraicGeometry.Space.smallEtaleDerivedTensor`.

## Main results

* `AlgebraicGeometry.Space.isPseudoCoherent_smallEtaleDerivedTensor_of_isPerfect`: `E ⊗^L K` is
  pseudo-coherent for `E` perfect and `K` pseudo-coherent, in `spaceDerivedCategory X`.
* `AlgebraicGeometry.Space.isPseudoCoherent_smallEtaleDerivedTensor_Q_of_isRetractOfFiniteFree`:
  `P ⊗^L K` is pseudo-coherent for `P` a bounded complex of retracts of finite free modules and
  `K` pseudo-coherent.
* `AlgebraicGeometry.Space.isPseudoCoherent_smallEtaleDerivedTensor_single_unit`: the case of a
  single term `𝒪_X`, and
  `isPseudoCoherent_smallEtaleDerivedTensor_single_of_isRetractOfFiniteFree` (same namespace):
  the case of a single term which is a retract of a finite free module.

## Implementation notes

The argument is local, and does not go through the quantitative part (1) of Stacks 09J9.
Pseudo-coherence is étale local (`isPseudoCoherentFrom_of_forall_isAffineChart`), and on an
affine étale chart `p : W ⟶ X` the derived pullback of `E ⊗^L K` is `Lp^*E ⊗^L Lp^*K` by
Stacks 07A4, where `Lp^*E` is perfect (Stacks 08H6), hence has a strictly perfect model `P`, and
`Lp^*K` is pseudo-coherent (Stacks 08H4). Along the stupid filtration of `P`, `P ⊗^L Lp^*K` is an
iterated extension of shifts of `Pⁱ ⊗^L Lp^*K`, each a retract of a finite sum of copies of
`Lp^*K` by the unit law. Pseudo-coherent objects are closed under extensions (Stacks 08FV), under
shifts, and under summands (Stacks 08FW), so this suffices: these are the instances on
`AlgebraicGeometry.RingedSite.isPseudoCoherentObject`.

All derived categories are at the standard model, the one
`AlgebraicGeometry.Space.smallEtaleDerivedTensor` is stated on; it is named in the statements by
`letI` (for the main result through `AlgebraicGeometry.Space.spaceDerivedCategory`,
`AlgebraicGeometry.Space.spaceHasDerivedCategory` and `AlgebraicGeometry.Space.spaceIsPerfect`),
and no instance is installed. The intermediate results read pseudo-coherence on the small étale
ringed topos of `X`, `(smallEtaleRingedTopos B S hS X).toRingedSite`, which reduces to the
spelling `ringedToposStructureRingSheaf` of the modules that `smallEtaleDerivedTensor` uses; the
main result reads it on `smallEtaleRingedSite`, the two being the same ringed site by `rfl`.

## References

* [Stacks Project, Tag 09J9](https://stacks.math.columbia.edu/tag/09J9)
* [Stacks Project, Tag 08FV](https://stacks.math.columbia.edu/tag/08FV)
* [Stacks Project, Tag 08FW](https://stacks.math.columbia.edu/tag/08FW)
* [Stacks Project, Tag 08H4](https://stacks.math.columbia.edu/tag/08H4)
* [Stacks Project, Tag 08H6](https://stacks.math.columbia.edu/tag/08H6)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (Z : AlgebraicSpaces B S hS)

/-- **`𝒪_Z ⊗^L H` is pseudo-coherent** for `H` pseudo-coherent, by the unit law
`𝒪_Z[0] ⊗^L H ≅ H`. The derived category is the standard model, the one
`AlgebraicGeometry.Space.smallEtaleDerivedTensor` is stated on. -/
theorem isPseudoCoherent_smallEtaleDerivedTensor_single_unit :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
    ∀ H : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)),
      RingedSite.isPseudoCoherentObject (smallEtaleRingedTopos B S hS Z).toRingedSite H →
        RingedSite.isPseudoCoherentObject (smallEtaleRingedTopos B S hS Z).toRingedSite
          (((smallEtaleDerivedTensor B S hS Z).obj ((DerivedCategory.singleFunctor _ 0).obj
            (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Z)))).obj H) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))
  have := RingedSite.isPseudoCoherentObject_isClosedUnderIsomorphisms
    (smallEtaleRingedTopos B S hS Z).toRingedSite
  intro H hH
  let e₀ := (smallEtaleDerivedTensor B S hS Z).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app
        (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Z))) ≪≫
    (smallEtaleDerivedTensorProduct B S hS Z).leftSingleUnitNatIso 0 ≪≫
      shiftFunctorZero' _ (-0 : ℤ) (by simp)
  exact ObjectProperty.prop_of_iso _ (e₀.app H).symm hH

/-- **`M ⊗^L H` is pseudo-coherent** for `M` a retract of a finite free `𝒪_Z`-module, placed in
degree `0`, and `H` pseudo-coherent: it is a retract of a finite sum of copies of `𝒪_Z ⊗^L H`. -/
theorem isPseudoCoherent_smallEtaleDerivedTensor_single_of_isRetractOfFiniteFree
    (M : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
    (hM : IsRetractOfFiniteFree
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Z)) M) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
    ∀ H : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)),
      RingedSite.isPseudoCoherentObject (smallEtaleRingedTopos B S hS Z).toRingedSite H →
        RingedSite.isPseudoCoherentObject (smallEtaleRingedTopos B S hS Z).toRingedSite
          (((smallEtaleDerivedTensor B S hS Z).obj ((DerivedCategory.singleFunctor _ 0).obj M)).obj
            H) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))
  have := RingedSite.isPseudoCoherentObject_isTriangulated
    (smallEtaleRingedTopos B S hS Z).toRingedSite
  have := RingedSite.isPseudoCoherentObject_isStableUnderRetracts
    (smallEtaleRingedTopos B S hS Z).toRingedSite
  intro H hH
  let T := smallEtaleDerivedTensorProduct B S hS Z
  let : ((smallEtaleDerivedTensor B S hS Z).flip.obj H).CommShift ℤ := T.commShift_left H
  have : ((smallEtaleDerivedTensor B S hS Z).flip.obj H).IsTriangulated := T.exact_left H
  obtain ⟨n, ι, π, hιπ⟩ := hM
  let O := SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Z)
  let sΦ := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) 0 ⋙
    (smallEtaleDerivedTensor B S hS Z).flip.obj H
  have hunit : RingedSite.isPseudoCoherentObject (smallEtaleRingedTopos B S hS Z).toRingedSite
      (sΦ.obj O) :=
    isPseudoCoherent_smallEtaleDerivedTensor_single_unit Z H hH
  have hfree : RingedSite.isPseudoCoherentObject (smallEtaleRingedTopos B S hS Z).toRingedSite
      (sΦ.obj (⨁ fun _ : Fin n => O)) :=
    ObjectProperty.prop_of_iso _ (sΦ.mapBiproduct fun _ : Fin n => O).symm
      (ObjectProperty.prop_of_isLimit_fan _ (biproduct.isLimit _) fun _ => hunit)
  exact ObjectProperty.prop_of_retract _
    ⟨sΦ.map ι, sΦ.map π, by rw [← sΦ.map_comp, hιπ, CategoryTheory.Functor.map_id]; rfl⟩ hfree

/-- **`P ⊗^L H` is pseudo-coherent** for `P` a bounded complex of retracts of finite free
`𝒪_Z`-modules and `H` pseudo-coherent, on the small étale site of an algebraic space `Z`. Along
the stupid filtration of `P` this reduces to a single term, a retract of `𝒪_Z^{⊕ n}` placed in
one degree. The derived category is the standard model, the one
`AlgebraicGeometry.Space.smallEtaleDerivedTensor` is stated on. -/
theorem isPseudoCoherent_smallEtaleDerivedTensor_Q_of_isRetractOfFiniteFree
    (P : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)) ℤ)
    (hP : ∀ j, IsRetractOfFiniteFree
      (SheafOfModules.unit (ringedToposStructureRingSheaf B S hS Z)) (P.X j))
    (hPb : {i : ℤ | ¬ IsZero (P.X i)}.Finite) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
    ∀ H : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z)),
      RingedSite.isPseudoCoherentObject (smallEtaleRingedTopos B S hS Z).toRingedSite H →
        RingedSite.isPseudoCoherentObject (smallEtaleRingedTopos B S hS Z).toRingedSite
          (((smallEtaleDerivedTensor B S hS Z).obj (DerivedCategory.Q.obj P)).obj H) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))
  have := RingedSite.isPseudoCoherentObject_isTriangulated
    (smallEtaleRingedTopos B S hS Z).toRingedSite
  have := RingedSite.isPseudoCoherentObject_isStableUnderRetracts
    (smallEtaleRingedTopos B S hS Z).toRingedSite
  intro H hH
  let T := smallEtaleDerivedTensorProduct B S hS Z
  let : ((smallEtaleDerivedTensor B S hS Z).flip.obj H).CommShift ℤ := T.commShift_left H
  have : ((smallEtaleDerivedTensor B S hS Z).flip.obj H).IsTriangulated := T.exact_left H
  exact StacksDraft.ExtremalDegrees.prop_map_Q_of_terms
    ((smallEtaleDerivedTensor B S hS Z).flip.obj H)
    (RingedSite.isPseudoCoherentObject (smallEtaleRingedTopos B S hS Z).toRingedSite) P hPb
    fun i _ =>
      isPseudoCoherent_smallEtaleDerivedTensor_single_of_isRetractOfFiniteFree Z (P.X i) (hP i)
        H hH

variable {Z} in
/-- **Stacks 09J9 (2), for a perfect factor, on an algebraic space.** Let `X` be an algebraic
space. If `E` is a perfect and `K` a pseudo-coherent object of `D(𝒪_X)`, then
`E ⊗^L_{𝒪_X} K` is pseudo-coherent. A perfect object is pseudo-coherent, so this is the case of
Stacks 09J9 (2) in which the first factor is perfect. The objects live in
`AlgebraicGeometry.Space.spaceDerivedCategory X`, the standard model of `D(𝒪_X)`, which is the
one `AlgebraicGeometry.Space.smallEtaleDerivedTensor` is stated on.

Pseudo-coherence in every degree is checked on the affine étale charts. On such a chart
`p : W ⟶ X`, `Lp^*(E ⊗^L K) ≅ Lp^*E ⊗^L Lp^*K` (Stacks 07A4); `Lp^*E` is perfect (Stacks 08H6)
on the affine `W`, so it has a strictly perfect model, and `Lp^*K` is pseudo-coherent
(Stacks 08H4). -/
theorem isPseudoCoherent_smallEtaleDerivedTensor_of_isPerfect
    (E K : spaceDerivedCategory B S hS Z) (hE : spaceIsPerfect B S hS Z E)
    (hK : letI := spaceHasDerivedCategory B S hS Z
      (smallEtaleRingedSite B S hS Z.1 Z.2).IsPseudoCoherent K) :
    letI := spaceHasDerivedCategory B S hS Z
    (smallEtaleRingedSite B S hS Z.1 Z.2).IsPseudoCoherent
      (((smallEtaleDerivedTensor B S hS Z).obj E).obj K) := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Z))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))
  refine (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2 fun m => ?_
  refine isPseudoCoherentFrom_of_forall_isAffineChart _ m fun A hA => ?_
  let U₀ := (SmallEtale.toOver B S hS Z.1).obj A
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U₀) := hA
  let W := schemeSpace (B := B) (S := S) (hS := hS) U₀
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS W))
  let := HasDerivedCategory.standard (SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS W.1 W.2).O))
  let p := chartToSpace B S hS Z A
  have hEW := isPerfect_smallEtaleDerivedModulePullback p E hE
  obtain ⟨P, hP, ⟨c, d, hc, hd⟩, ⟨eP⟩⟩ := hasStrictlyPerfectModel_of_isCompactObject_yoneda U₀
    ⟨_, qcohDerived_of_isPerfect _ _ _ W _ hEW⟩
    (isCompactObject_of_isPerfect_yoneda U₀ _ hEW)
  have hPb : {i : ℤ | ¬ IsZero (P.X i)}.Finite :=
    (Set.finite_Icc c d).subset fun i hi =>
      ⟨not_lt.1 fun h => hi (P.isZero_of_isStrictlyGE c i h),
        not_lt.1 fun h => hi (P.isZero_of_isStrictlyLE d i h)⟩
  have hK' : (smallEtaleRingedSite B S hS W.1 W.2).IsPseudoCoherent
      ((smallEtaleDerivedModulePullback B S hS p).obj K) :=
    (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).2 fun n =>
      isPseudoCoherentFrom_smallEtaleDerivedModulePullback_general p K n
        ((RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1 hK n)
  have hK'' : RingedSite.isPseudoCoherentObject (smallEtaleRingedTopos B S hS W).toRingedSite
      ((smallEtaleDerivedModulePullback B S hS p).obj K) := hK'
  have hW := isPseudoCoherent_smallEtaleDerivedTensor_Q_of_isRetractOfFiniteFree W P hP hPb _ hK''
  let e : (smallEtaleDerivedModulePullback B S hS p).obj
        (((smallEtaleDerivedTensor B S hS Z).obj E).obj K) ≅
      ((smallEtaleDerivedTensor B S hS W).obj (DerivedCategory.Q.obj P)).obj
        ((smallEtaleDerivedModulePullback B S hS p).obj K) :=
    (smallEtaleDerivedPullbackTensorIso p).app (E, K) ≪≫
      ((smallEtaleDerivedTensor B S hS W).mapIso eP).app _
  have := RingedSite.isPseudoCoherentObject_isClosedUnderIsomorphisms
    (smallEtaleRingedTopos B S hS W).toRingedSite
  exact (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom _ _).1
    (ObjectProperty.prop_of_iso
      (RingedSite.isPseudoCoherentObject (smallEtaleRingedTopos B S hS W).toRingedSite)
      e.symm hW) m

end AlgebraicGeometry.Space

end
