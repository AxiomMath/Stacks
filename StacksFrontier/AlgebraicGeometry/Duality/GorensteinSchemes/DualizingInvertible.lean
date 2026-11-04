module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineDualizingPair
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.GlobalInvertible
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.OverEquivInvertible
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.PullbackIsoInvertible
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StructureSheafDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingModelSliceSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.SliceDerivedSheafHomTransposeIsIso
public import StacksFrontier.RingTheory.Dualizing.GorensteinRingDualizing

/-!
# A scheme is Gorenstein exactly when its dualizing complex is invertible

Let `X` be a locally Noetherian scheme with a dualizing complex `ω_X^•`
(`Stacks.Duality.IsDualizingComplex`, [Stacks, Tag 0A87]). This file proves
[Stacks, Tag 0BFQ], clause (1)(a):

**`X` is Gorenstein ⟺ `ω_X^•` is an invertible object of `D(𝒪_X)`.**

The direction "invertible ⟹ Gorenstein" is
`Stacks.Duality.isGorenstein_of_isInvertible_dualizingComplex`. The converse follows the
source's proof, "looking affine locally":

* *Over an affine open `U`.* `A = Γ(X, U)` is a Noetherian Gorenstein ring and `ω_X^•|_U` is the
  complex associated to a dualizing complex `ω_A` over `A`. By [Stacks, Tag 0DW9] (2) the ring
  `A` in degree zero is a dualizing complex too, so by the affine case of [Stacks, Tag 0ATP] the
  two complexes associated to `A[0]` and to `ω_A` on `Spec A` differ by an invertible object;
  the first being the unit, `ω̃_A` is invertible
  (`Stacks.Duality.isInvertible_derivedTilde_of_isGorensteinRing`). Restriction along
  `U ≅ Spec A` and the equivalence of the slice site with the open subscheme carry this to the
  restriction of `ω_X^•` to the slice site over `U`
  (`Stacks.Duality.isInvertible_restrictD_of_isGorenstein`).
* *Glueing.* Invertibility in `D(𝒪_X)` is local on a covering by opens,
  `Stacks.Cohomology.SliceDerivedSheafHom.isInvertible_of_isInvertible_restriction`, through
  the mate of the slice tensor comparison being an isomorphism.

## Main results

* `Stacks.Duality.isInvertible_dualizingComplex_of_isGorenstein`: the dualizing complex of a
  Gorenstein scheme is invertible.
* `Stacks.Duality.isGorenstein_iff_isInvertible_dualizingComplex`:
  **[Stacks, Tag 0BFQ], clause (1)(a).**

## Implementation notes

The model of `D(𝒪_X)` is `HasDerivedCategory.standard`, the localization of the homotopy
category at the quasi-isomorphisms; the derived internal hom, the tensor–hom bijection of
[Stacks, Tag 08J8] and the locality of invertibility are stated at that model. The monoidal
structure is the one of [Stacks, Tag 0FPT], `AlgebraicGeometry.Scheme.Modules.derivedMonoidal`,
for which the direction "invertible ⟹ Gorenstein" is stated as well.

## References

* [Stacks Project, Tag 0A87](https://stacks.math.columbia.edu/tag/0A87)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0DW9](https://stacks.math.columbia.edu/tag/0DW9)
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace

universe u

namespace Stacks.Duality

attribute [local instance 10000] HasDerivedCategory.standard

/-- Invertibility is preserved when passing to a braided monoidal structure with an isomorphic
tensor bifunctor and an isomorphic unit. -/
private theorem isInvertible_of_curriedTensor_iso {C : Type*} [Category C]
    (M M' : MonoidalCategory C) (B : @BraidedCategory C _ M')
    (e : @curriedTensor C _ M ≅ @curriedTensor C _ M')
    (u : @tensorUnit C _ M.toMonoidalCategoryStruct ≅ @tensorUnit C _ M'.toMonoidalCategoryStruct)
    {K : C} (h : @MonoidalCategory.IsInvertible _ _ M K) :
    @MonoidalCategory.IsInvertible _ _ M' K :=
  @MonoidalCategory.isInvertible_of_tensorComparison_of_braided _ _ M _ _ M' B (𝟭 _)
    (fun A B => (e.app A).app B) u _ h

/-! ### The affine case -/

/-- **The complex associated to a dualizing complex over a Noetherian Gorenstein ring is an
invertible object of `D(𝒪_{Spec R})`.** By [Stacks, Tag 0DW9] (2), `R` in degree zero is a
dualizing complex as well, so by the affine case of [Stacks, Tag 0ATP],
`Stacks.Duality.exists_isInvertible_tensor_iso_derivedTildeStandard`, `ω̃ ≅ R̃[0] ⊗ L` for an
invertible `L`; and `R̃[0]` is the unit. -/
public theorem isInvertible_derivedTilde_of_isGorensteinRing (R : CommRingCat.{u})
    [IsNoetherianRing R]
    [HasSheafify (Opens.grothendieckTopology (Spec R)) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology (Spec R)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Spec R).sheaf).Additive]
    [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (Spec R).sheaf).obj M).Additive]
    [∀ (K₁ K₂ : CochainComplex
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Spec R).sheaf)) ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂
        (Stacks.SheafOfModules.Tensor.sheafTensor (Spec R).sheaf) (ComplexShape.up ℤ)]
    (hR : Dualizing.IsGorensteinRing R)
    {ω : DerivedCategory (ModuleCat.{u} R)} (hω : Dualizing.IsDualizingComplex ω) :
    letI := Stacks.SheafOfModules.derivedMonoidalStructure (Spec R).sheaf
    MonoidalCategory.IsInvertible ((derivedTildeStructureSheafModules R).obj ω) := by
  let := Stacks.SheafOfModules.derivedMonoidalStructure (Spec R).sheaf
  let := Stacks.SheafOfModules.derivedSymmetricStructure (Spec R).sheaf
  have hA := (Dualizing.exists_isDualizingComplex_iff_regularModule.{u, u} (R : Type u) hR).mp
    ⟨ω, hω⟩
  obtain ⟨L, hL, ⟨e⟩⟩ := exists_isInvertible_tensor_iso_derivedTildeStandard R hA hω
  let eU : (derivedTildeStructureSheafModules R).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)) ≅
      𝟙_ (DerivedCategory (Stacks.SheafOfModules.StructureSheafModules (Spec R).sheaf)) :=
    ((tilde.functor R).mapDerivedCategorySingleFunctor 0).app (ModuleCat.of (R : Type u) R) ≪≫
      (DerivedCategory.singleFunctor
        (Stacks.SheafOfModules.StructureSheafModules (Spec R).sheaf) 0).mapIso tildeSelf
  exact Dualizing.isInvertible_of_iso
    ((λ_ L).symm ≪≫ MonoidalCategory.whiskerRightIso eU.symm L ≪≫ e) hL

/-! ### The restriction to the slice site over an affine open -/

section Scheme

variable {X : Scheme.{u}}

/-- **On a Gorenstein scheme the restriction of a dualizing complex to the slice site over an
affine open is invertible.** The dualizing model `ω` over `Γ(X, U)` of
[Stacks, Tag 0A87] has invertible associated complex on `Spec Γ(X, U)`
(`Stacks.Duality.isInvertible_derivedTilde_of_isGorensteinRing`), and invertibility is carried
along restriction to `U ≅ Spec Γ(X, U)`
(`Stacks.SheafOfModules.PullbackIsoTensor.isInvertible_restrictFunctor`) and reflected along
the equivalence of the slice site with the open subscheme
(`Stacks.SheafOfModules.OverEquivTensor.isInvertible_of_isInvertible_overEquiv`), the monoidal
structures of [Stacks, Tag 0FPT] and their re-seatings onto the derived tensor product being
compared by `CategoryTheory.MonoidalCategory.isInvertible_of_tensorComparison_of_braided`. -/
public theorem isInvertible_restrictD_of_isGorenstein [AlgebraicGeometry.IsGorenstein X]
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K) (U : X.Opens)
    (hU : IsAffineOpen U) :
    letI := RingedSite.derivedTensorMonoidal
      ((Stacks.SheafOfModules.ringedSite X.sheaf).over U)
    MonoidalCategory.IsInvertible
      ((Stacks.Cohomology.SliceDerivedSheafHom.restrictD
        (Stacks.SheafOfModules.ringedSite X.sheaf) U).obj K) := by
  have : HasSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} := inferInstance
  have : HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u} := inferInstance
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  obtain ⟨ω, hω, ⟨e⟩⟩ :=
    exists_isDualizingComplex_iso_overFunctor_of_isDualizingComplex U K hU hK
  have h := isInvertible_derivedTilde_of_isGorensteinRing Γ(X, U)
    (isGorensteinRing_sections U hU) hω
  -- the reseated structure on `Spec Γ(U)` back to the structure of 0FPT
  have h1 : @MonoidalCategory.IsInvertible _ _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal (Spec Γ(X, U)).sheaf)
      ((derivedTildeStructureSheafModules Γ(X, U)).obj ω) :=
    isInvertible_of_curriedTensor_iso
      (Stacks.SheafOfModules.derivedMonoidalStructure (Spec Γ(X, U)).sheaf) _
      (Stacks.SheafOfModules.DerivedMonoidal.derivedSymmetric
        (Spec Γ(X, U)).sheaf).toBraidedCategory
      (Stacks.SheafOfModules.derivedTensorMonoidalIso (Spec Γ(X, U)).sheaf).symm
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso (Spec Γ(X, U)).sheaf).symm h
  -- restriction along `U ≅ Spec Γ(U)`
  have h2 := Stacks.SheafOfModules.PullbackIsoTensor.isInvertible_restrictFunctor hU.isoSpec.hom
    ((derivedTildeStructureSheafModules Γ(X, U)).obj ω) h1
  -- the slice site
  have h3 := @Dualizing.isInvertible_of_iso _ _
    (Stacks.SheafOfModules.DerivedMonoidal.derivedMonoidal
      (Stacks.SheafOfModules.OverEquivTensor.openRingSheaf X U)) _ _
    (((Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
      (tilde.functor Γ(X, U)) (Scheme.Modules.restrictFunctor hU.isoSpec.hom)).app ω).symm ≪≫
        e.symm) h2
  have h4 := Stacks.SheafOfModules.OverEquivTensor.isInvertible_of_isInvertible_overEquiv X U _ h3
  exact isInvertible_of_curriedTensor_iso _ _
      (RingedSite.derivedTensorSymmetric
        ((Stacks.SheafOfModules.ringedSite X.sheaf).over U)).toBraidedCategory
      (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso
        (Stacks.SheafOfModules.OverEquivTensor.sliceRingSheaf X U)
        (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct.{u, u + 1}
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct
            ((Stacks.SheafOfModules.ringedSite X.sheaf).over U))))
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso
        (Stacks.SheafOfModules.OverEquivTensor.sliceRingSheaf X U)) h4

/-- **The dualizing complex of a Gorenstein scheme is an invertible object of `D(𝒪_X)`.** Its
restriction to the slice site over every affine open is invertible
(`Stacks.Duality.isInvertible_restrictD_of_isGorenstein`), the affine opens cover `X`, and
invertibility is local
(`Stacks.Cohomology.SliceDerivedSheafHom.isInvertible_of_isInvertible_restriction`); the
re-seated monoidal structure the glueing is stated at is then compared with the one of
[Stacks, Tag 0FPT]. -/
public theorem isInvertible_dualizingComplex_of_isGorenstein [AlgebraicGeometry.IsGorenstein X]
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K) :
    letI := Scheme.Modules.derivedMonoidal X
    MonoidalCategory.IsInvertible K := by
  have hY : (Stacks.SheafOfModules.ringedSite X.sheaf).J.CoversTop
      (fun V : X.affineOpens => (V : X.Opens)) :=
    (Opens.coversTop_iff _ _).2 (TopologicalSpace.IsOpenCover.mk (iSup_affineOpens_eq_top X))
  have h := Stacks.Cohomology.SliceDerivedSheafHom.isInvertible_of_isInvertible_restriction
    (Stacks.SheafOfModules.ringedSite X.sheaf) hY K
    (fun V => isInvertible_restrictD_of_isGorenstein K hK V V.2)
  exact isInvertible_of_curriedTensor_iso
      (RingedSite.derivedTensorMonoidal (Stacks.SheafOfModules.ringedSite X.sheaf)) _
      (Scheme.Modules.derivedSymmetric X).toBraidedCategory
      (Stacks.SheafOfModules.DerivedMonoidal.derivedTensorMonoidalIso X.sheaf
        (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct.{u, u + 1}
          (Stacks.SheafOfModules.canonicalDerivedTensorProduct
            (Stacks.SheafOfModules.ringedSite X.sheaf)))).symm
      (Stacks.SheafOfModules.DerivedMonoidal.canonicalUnitIso X.sheaf).symm h

/-- **Stacks Project, Tag 0BFQ, clause (1)(a).** A locally Noetherian scheme `X` carrying a
dualizing complex `ω_X^•` is Gorenstein if and only if `ω_X^•` is an invertible object of
`D(𝒪_X)`. -/
@[stacks 0BFQ "(1)(a): X is Gorenstein iff its dualizing complex is invertible in D(O_X)"]
public theorem isGorenstein_iff_isInvertible_dualizingComplex [IsLocallyNoetherian X]
    (K : DerivedCategory X.Modules) (hK : IsDualizingComplex K) :
    AlgebraicGeometry.IsGorenstein X ↔
      letI := Scheme.Modules.derivedMonoidal X
      MonoidalCategory.IsInvertible K :=
  ⟨fun _ => isInvertible_dualizingComplex_of_isGorenstein K hK,
    isGorenstein_of_isInvertible_dualizingComplex K hK⟩

end Scheme

end Stacks.Duality

end
