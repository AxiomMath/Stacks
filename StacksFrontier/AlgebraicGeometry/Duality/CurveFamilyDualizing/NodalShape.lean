module

public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.SeparatedComplex
public import StacksFrontier.AlgebraicGeometry.Duality.CurveFamilyDualizing.SyntomicOverField
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFibreInvertible
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenBetti
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenHypothesesNecessary
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalDescentAlongLimit

/-!
# The shape of a relative dualizing complex of a syntomic curve

Let `f : X ⟶ S` be syntomic of relative dimension one, over an arbitrary base `S`, and let
`(K, ξ)` be a relative dualizing complex for `f` (Stacks 0E2T) relative to any diagonal open
`W ⊆ X ×_S X`. This file shows that `K` is an invertible module placed in degree `-1`:
`H^j(K) = 0` for `j ≠ -1`, `H^{-1}(K)` is finite locally free of rank one and invertible, and
`K ≅ H^{-1}(K)[1]`. The same holds for an at-worst-nodal morphism of relative dimension one.

## Main results

* `Stacks.Duality.NodalShape.derivedFiberBetti_eq_of_syntomicOfRelativeDimension_one`: the
  derived-fibre Betti numbers of `K` are those of `κ(x)[1]` at every point `x`.
* `Stacks.Duality.NodalShape.isRelativeDualizingComplex_shape_of_syntomicOfRelativeDimension_one`
  and `Stacks.Duality.NodalShape.isRelativeDualizingComplex_shape_of_isAtWorstNodal`: the shape
  of `K`.

## The argument

Fix `x ∈ X` over `s ∈ S` and the fibre square of `f` over `Spec κ(s) ⟶ S`. The derived base
change of `(K, ξ)` to the fibre is a relative dualizing complex for the fibre morphism (Stacks
0E2Y), relative to the part of the coborder diagonal open of the fibre morphism mapped into `W`
(`baseChangeDiagonalOpen`). The fibre morphism is syntomic of relative dimension one over the
field `κ(s)`, so the base change is `𝒪[1]` near the point of the fibre over `x`
(`Stacks.Duality.SyntomicOverField.exists_derivedPullback_iso_single`). Derived-fibre Betti
numbers are invariant under derived pullback (Stacks 0BDI), so those of `K` at `x` are those of
`𝒪[1]`, namely `1` in degree `-1` and `0` elsewhere, and
`PseudoCoherentFibreInvertible.isRelativeDualizingComplex_shape_of_forall_derivedFiberBetti`
applies.

## Implementation notes

Everything is stated at the standard model `HasDerivedCategory.standard` of the derived
categories, the model of relative dualizing complexes and of derived-fibre Betti numbers. The
statements name it explicitly (`letI := HasDerivedCategory.standard _` in each binder and
conclusion that needs it), since instance search would otherwise choose the locally small model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open StrictlyPerfect (OXMod)
open AlgebraicGeometry.Scheme.Hom (DiagonalOpen pullbackMapOfIsPullback)

universe u

namespace Stacks.Duality.NodalShape

/-- The standard model of `D(𝒪_T)`, for `letI`. -/
local macro "stdᴰ[" T:term "]" : term => `(HasDerivedCategory.standard (OXMod $T))

/-- The standard models of `D(𝒪_{T|_U})` for all opens `U` of `T` (in the form
`AlgebraicGeometry.ComplexAndDivisorSituation.restrictHasDerivedCategory`, which is
`HasDerivedCategory.standard`), for `letI`. -/
local macro "stdOpens[" T:term "]" : term =>
  `(AlgebraicGeometry.ComplexAndDivisorSituation.restrictHasDerivedCategory $T)

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

/-! ### The diagonal open of a base change -/

section BaseChange

variable {X S X' S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  (hpb : IsPullback g' f' f g) (D : DiagonalOpen f)

/-- The open of the coborder diagonal open of `f'` mapped by `g' × g'` into a given diagonal open
`W` of `f`. -/
def baseChangeOpen : (DiagonalOpen.coborder f').W.Opens :=
  ((DiagonalOpen.coborder f').ι ≫ pullbackMapOfIsPullback hpb) ⁻¹ᵁ D.ι.opensRange

/-- The open `baseChangeOpen` contains the diagonal of `f'`: `g' × g'` carries the diagonal of
`f'` into the diagonal of `f`, which lies in `W`. -/
theorem range_diag_subset_baseChangeOpen :
    Set.range (DiagonalOpen.coborder f').diag ⊆ baseChangeOpen hpb D := by
  rintro _ ⟨x, rfl⟩
  change ((DiagonalOpen.coborder f').ι ≫ pullbackMapOfIsPullback hpb)
    ((DiagonalOpen.coborder f').diag x) ∈ D.ι.opensRange
  rw [← Scheme.Hom.comp_apply, ← Category.assoc, (DiagonalOpen.coborder f').fac,
    Scheme.Hom.diagonal_comp_pullbackMapOfIsPullback hpb, ← D.fac, Scheme.Hom.comp_apply,
    Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

/-- The diagonal open of `f'` mapped by `g' × g'` into the diagonal open `W` of `f`. -/
def baseChangeDiagonalOpen : DiagonalOpen f' :=
  (DiagonalOpen.coborder f').restrictOpen (baseChangeOpen hpb D)
    (range_diag_subset_baseChangeOpen hpb D)

/-- `g' × g'` restricted to `baseChangeDiagonalOpen`, landing in `W`. -/
def baseChangeW : (baseChangeDiagonalOpen hpb D).W ⟶ D.W :=
  IsOpenImmersion.lift D.ι ((baseChangeDiagonalOpen hpb D).ι ≫ pullbackMapOfIsPullback hpb) (by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := x.2
    exact ⟨y, hy⟩)

/-- `baseChangeW` followed by the inclusion of `W` is `g' × g'` on `baseChangeDiagonalOpen`. -/
theorem baseChangeW_ι :
    baseChangeW hpb D ≫ D.ι =
      (baseChangeDiagonalOpen hpb D).ι ≫ pullbackMapOfIsPullback hpb := by
  unfold baseChangeW
  exact IsOpenImmersion.lift_fac _ _ _

end BaseChange

/-! ### The structure sheaf in degree `-1` -/

/-- **The structure sheaf placed in degree `-1` is pseudo-coherent.** The complex concentrated in
degree `-1` on `𝒪_X` is strictly perfect. -/
theorem isPseudoCoherent_singleFunctor_neg_one_unit (X : Scheme.{u}) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules (-1)).obj
        (SheafOfModules.unit X.ringCatSheaf)) :=
  letI (T : RingedSpace.{u, u}) := HasDerivedCategory.standard (OXMod.{u, u} T)
  letI (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  letI (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules (structureSheafRing T.toSheafedSpace))
  ⟨(CochainComplex.singleFunctor X.Modules (-1)).obj (SheafOfModules.unit X.ringCatSheaf),
    (RingedSpace.isPerfectComplex_of_isStrictlyPerfect
      (StrictlyPerfect.isStrictlyPerfect_single
        (StrictlyPerfect.isDirectSummandOfFiniteFree_structureModule X.toRingedSpace)
        (-1))).isPseudoCoherentComplex,
    ⟨((DerivedCategory.singleFunctorIsoCompQ X.Modules (-1)).app
      (SheafOfModules.unit X.ringCatSheaf)).symm⟩⟩

/-- **The derived-fibre Betti numbers of `𝒪_X[1]`.** They are `1` in degree `-1` and `0`
elsewhere. -/
theorem derivedFiberBetti_singleFunctor_neg_one_unit (X : Scheme.{u})
    (hE : letI := HasDerivedCategory.standard (X.Modules)
      letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
      RingedSpace.IsPseudoCoherent.{u, u + 1} (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules (-1)).obj
        (SheafOfModules.unit X.ringCatSheaf))) (j : ℤ) (x : X) :
    letI := HasDerivedCategory.standard (X.Modules)
    letI := HasDerivedCategory.standard (OXMod.{u, u} X.toRingedSpace)
    DerivedFibreBetti.derivedFiberBetti X
        ((DerivedCategory.singleFunctor X.Modules (-1)).obj
          (SheafOfModules.unit X.ringCatSheaf)) hE j x =
      if j = -1 then 1 else 0 := by
  let (T : RingedSpace.{u, u}) := HasDerivedCategory.standard (OXMod.{u, u} T)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  split_ifs with hj
  · subst hj
    exact BottomRankStratum.derivedFiberBetti_single_eq_rank _ (-1) 1
      (AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit X) hE x
  · exact BottomRankStratum.derivedFiberBetti_single_eq_zero _ (-1)
      (Scheme.Modules.isFlat_unit X) hE j hj x

/-! ### The derived-fibre Betti numbers of the relative dualizing complex -/

/-- **The derived-fibre Betti numbers of a relative dualizing complex of a syntomic curve.** Let
`f : X ⟶ S` be syntomic of relative dimension one and `(K, ξ)` a relative dualizing complex for
`f` relative to a diagonal open `D`. At every point `x` of `X` the derived fibre of `K` has
cohomology only in degree `-1`, of dimension one: the derived-fibre Betti numbers of `K` at `x`
are those of `𝒪[1]`.

The base change of `(K, ξ)` to the fibre of `f` through `x` is a relative dualizing complex for
the fibre morphism (Stacks 0E2Y), which is syntomic of relative dimension one over a field, so
that base change is `𝒪[1]` near the point over `x`; derived-fibre Betti numbers are invariant
under derived pullback (Stacks 0BDI). -/
theorem derivedFiberBetti_eq_of_syntomicOfRelativeDimension_one {X S : Scheme.{u}}
    (f : X ⟶ S) (hf : SyntomicOfRelativeDimension 1 f) (D : f.DiagonalOpen)
    (K : @DerivedCategory (OXMod.{u, u} X.toRingedSpace) _ _ (HasDerivedCategory.standard _))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hK : letI := stdᴰ[RingedSpace.inverseImage S.toRingedSpace f.base]
      letI := stdOpens[RingedSpace.inverseImage S.toRingedSpace f.base]
      haveI := SyntomicOverField.flat_of_syntomicOfRelativeDimension hf
      haveI := SyntomicOverField.locallyOfFinitePresentation_of_syntomicOfRelativeDimension hf
      f.IsRelativeDualizingComplex
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    (x : X) (j : ℤ) :
    letI := stdᴰ[X.toRingedSpace]; letI := HasDerivedCategory.standard X.Modules
    letI := stdᴰ[RingedSpace.inverseImage S.toRingedSpace f.base]
    letI := stdOpens[RingedSpace.inverseImage S.toRingedSpace f.base]
    haveI := SyntomicOverField.flat_of_syntomicOfRelativeDimension hf
    haveI := SyntomicOverField.locallyOfFinitePresentation_of_syntomicOfRelativeDimension hf
    DerivedFibreBetti.derivedFiberBetti X K hK.isPerfectRelativeTo.1 j x =
      if j = -1 then 1 else 0 := by
  let (T : RingedSpace.{u, u}) := HasDerivedCategory.standard (OXMod.{u, u} T)
  let (T : Scheme.{u}) := HasDerivedCategory.standard T.Modules
  let (T : Scheme.{u}) :=
    HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing T.toSheafedSpace))
  let := stdᴰ[RingedSpace.inverseImage S.toRingedSpace f.base]
  let := stdOpens[RingedSpace.inverseImage S.toRingedSpace f.base]
  have := SyntomicOverField.flat_of_syntomicOfRelativeDimension hf
  have := SyntomicOverField.locallyOfFinitePresentation_of_syntomicOfRelativeDimension hf
  -- the fibre square through `x`
  have hpb : IsPullback (f.fiberι (f x)) (f.fiberToSpecResidueField (f x)) f
      (S.fromSpecResidueField (f x)) :=
    IsPullback.of_hasPullback f (S.fromSpecResidueField (f x))
  have hf' : SyntomicOfRelativeDimension 1 (f.fiberToSpecResidueField (f x)) := by
    have := syntomicOfRelativeDimension_isStableUnderBaseChange.{u} 1
    exact MorphismProperty.of_isPullback (P := @SyntomicOfRelativeDimension 1) hpb hf
  -- the base change of `(K, ξ)` to the fibre
  have hK' := hK.baseChange hpb (baseChangeDiagonalOpen hpb D) (baseChangeW hpb D)
    (baseChangeW_ι hpb D)
  obtain ⟨U', hxU', ⟨e⟩⟩ :=
    SyntomicOverField.exists_derivedPullback_iso_single (k := S.residueField (f x))
      (f.fiberToSpecResidueField (f x)) hf' _ _ _ hK' (f.asFiber x)
  -- Betti numbers along `fiberι` and along `U'.ι`
  let L := DiagonalOpen.baseChangeComplex (f.fiberι (f x)) K
  have hL : RingedSpace.IsPseudoCoherent (X := (f.fiber (f x)).toRingedSpace) L :=
    DerivedFibreBetti.isPseudoCoherent_derivedPullback (f.fiberι (f x)) K
      hK.isPerfectRelativeTo.1
  have h₁ := congrFun (DerivedFibreBetti.derivedFiberBetti_derivedPullback (f.fiberι (f x)) K
    hK.isPerfectRelativeTo.1 j) (f.asFiber x)
  have h₂ := congrFun (DerivedFibreBetti.derivedFiberBetti_derivedPullback U'.ι L hL j)
    ⟨f.asFiber x, hxU'⟩
  have h₃ := congrFun (FibreBetti.derivedFiberBetti_eq_of_iso U'.toScheme
    (DerivedFibreBetti.isPseudoCoherent_derivedPullback U'.ι L hL)
    (isPseudoCoherent_singleFunctor_neg_one_unit U'.toScheme) e j) ⟨f.asFiber x, hxU'⟩
  simp only [Function.comp_apply, Scheme.Hom.fiberι_asFiber] at h₁
  rw [← h₁]
  exact (h₂.symm.trans (h₃.trans
    (derivedFiberBetti_singleFunctor_neg_one_unit U'.toScheme _ j ⟨f.asFiber x, hxU'⟩)) :)

/-! ### The shape of the relative dualizing complex -/

/-- **A relative dualizing complex of a syntomic curve is an invertible module in degree `-1`.**
Let `f : X ⟶ S` be syntomic of relative dimension one, over an arbitrary base, and `(K, ξ)` a
relative dualizing complex for `f` relative to a diagonal open `D`. Then the cohomology sheaves
of `K` vanish outside degree `-1`, `H^{-1}(K)` is finite locally free of rank one and invertible,
and `K ≅ H^{-1}(K)[1]`. -/
theorem isRelativeDualizingComplex_shape_of_syntomicOfRelativeDimension_one {X S : Scheme.{u}}
    (f : X ⟶ S) (hf : SyntomicOfRelativeDimension 1 f) (D : f.DiagonalOpen)
    (K : @DerivedCategory (OXMod.{u, u} X.toRingedSpace) _ _ (HasDerivedCategory.standard _))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hK : letI := stdᴰ[RingedSpace.inverseImage S.toRingedSpace f.base]
      letI := stdOpens[RingedSpace.inverseImage S.toRingedSpace f.base]
      haveI := SyntomicOverField.flat_of_syntomicOfRelativeDimension hf
      haveI := SyntomicOverField.locallyOfFinitePresentation_of_syntomicOfRelativeDimension hf
      f.IsRelativeDualizingComplex
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ) :
    letI := stdᴰ[X.toRingedSpace]; letI := HasDerivedCategory.standard X.Modules
    (∀ j : ℤ, j ≠ -1 → IsZero ((DerivedCategory.homologyFunctor X.Modules j).obj K)) ∧
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((DerivedCategory.homologyFunctor X.Modules (-1)).obj K) 1 ∧
      AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        ((DerivedCategory.homologyFunctor X.Modules (-1)).obj K) ∧
      Nonempty (K ≅ (DerivedCategory.singleFunctor X.Modules (-1)).obj
        ((DerivedCategory.homologyFunctor X.Modules (-1)).obj K)) := by
  let := stdᴰ[RingedSpace.inverseImage S.toRingedSpace f.base]
  let := stdOpens[RingedSpace.inverseImage S.toRingedSpace f.base]
  have := SyntomicOverField.flat_of_syntomicOfRelativeDimension hf
  have := SyntomicOverField.locallyOfFinitePresentation_of_syntomicOfRelativeDimension hf
  exact PseudoCoherentFibreInvertible.isRelativeDualizingComplex_shape_of_forall_derivedFiberBetti
    f _ D K ξ hK (derivedFiberBetti_eq_of_syntomicOfRelativeDimension_one f hf D K ξ hK)

/-- **A relative dualizing complex of an at-worst-nodal curve is an invertible module in degree
`-1`.** Let `f : X ⟶ S` be at-worst-nodal of relative dimension one and `(K, ξ)` a relative
dualizing complex for `f` relative to a diagonal open `D`. Then the cohomology sheaves of `K`
vanish outside degree `-1`, `H^{-1}(K)` is finite locally free of rank one and invertible, and
`K ≅ H^{-1}(K)[1]`. -/
theorem isRelativeDualizingComplex_shape_of_isAtWorstNodal {X S : Scheme.{u}}
    (f : X ⟶ S) (hf : IsAtWorstNodalOfRelativeDimensionOne f) (D : f.DiagonalOpen)
    (K : @DerivedCategory (OXMod.{u, u} X.toRingedSpace) _ _ (HasDerivedCategory.standard _))
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hK : letI := stdᴰ[RingedSpace.inverseImage S.toRingedSpace f.base]
      letI := stdOpens[RingedSpace.inverseImage S.toRingedSpace f.base]
      haveI := SyntomicOverField.flat_of_syntomicOfRelativeDimension hf.1
      haveI := SyntomicOverField.locallyOfFinitePresentation_of_syntomicOfRelativeDimension hf.1
      f.IsRelativeDualizingComplex
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
          (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ) :
    letI := stdᴰ[X.toRingedSpace]; letI := HasDerivedCategory.standard X.Modules
    (∀ j : ℤ, j ≠ -1 → IsZero ((DerivedCategory.homologyFunctor X.Modules j).obj K)) ∧
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((DerivedCategory.homologyFunctor X.Modules (-1)).obj K) 1 ∧
      AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
        ((DerivedCategory.homologyFunctor X.Modules (-1)).obj K) ∧
      Nonempty (K ≅ (DerivedCategory.singleFunctor X.Modules (-1)).obj
        ((DerivedCategory.homologyFunctor X.Modules (-1)).obj K)) :=
  isRelativeDualizingComplex_shape_of_syntomicOfRelativeDimension_one f hf.1 D K ξ hK

end Stacks.Duality.NodalShape

end
