module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CompactPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedCompactGeneration
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidal
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedMonoidalUnitors
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleComparison
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ProjectionFormulaLocallySmall

/-!
# A perfect complex annihilating a morphism into an object supported on a closed subset

For `X` quasi-compact and quasi-separated, `U ⊆ X` a quasi-compact open and `α : P ⟶ E` in
`D_QCoh(𝒪_X)` with `E|_U = 0`, where `P` is perfect, or `P` is pseudo-coherent and `E` is bounded
below, there is a perfect `I ⟶ 𝒪_X`, invertible on `U`, with `I ⊗ᴸ P ⟶ P ⟶ E` zero.

## Main results

* `Stacks.Duality.exists_isPerfect_map_comp_eq_zero_of_represents`: the statement for an arbitrary
  functor `Ψ` in place of `- ⊗ᴸ P`, given an object `K` representing `I ↦ Hom(Ψ I, E)` with
  `K|_U = 0`.
* `Stacks.Duality.exists_isPerfect_whiskerRight_comp_eq_zero_of_represents`: the statement given
  an object representing `I ↦ Hom(I ⊗ᴸ P, E)` vanishing on `U`.
* `Stacks.Duality.exists_isPerfect_whiskerRight_comp_eq_zero`: the statement itself.

## References

* [Stacks Project, Tag 0A9C](https://stacks.math.columbia.edu/tag/0A9C)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.Pretriangulated

universe u

namespace Stacks.Duality

open OpenImmersion

/-- Morphisms out of `Ψ I` into `E` correspond to morphisms out of `I` into `K` when, after a
fully faithful `ι`, `Ψ` becomes a left adjoint `L` whose right adjoint carries `E` to `ι K`. -/
def _root_.CategoryTheory.Adjunction.homEquivOfFullyFaithful {C Cq : Type*} [Category C]
    [Category Cq] {ι : Cq ⥤ C} (hι : ι.FullyFaithful) {Ψ : Cq ⥤ Cq}
    {L : C ⥤ C} {R : C ⥤ C} (adj : L ⊣ R) (ψ : Ψ ⋙ ι ≅ ι ⋙ L) {E K : Cq}
    (eK : ι.obj K ≅ R.obj (ι.obj E)) (I : Cq) : (Ψ.obj I ⟶ E) ≃ (I ⟶ K) :=
  hι.homEquiv.trans (((ψ.app I).homCongr (Iso.refl _)).trans
    ((adj.homEquiv _ _).trans ((Iso.refl _).homCongr eK.symm |>.trans hι.homEquiv.symm)))

/-- The bijection `Adjunction.homEquivOfFullyFaithful` is natural in `I`: for `h : I ⟶ I'`,
the image of `Ψ.map h ≫ y` is `h` composed with the image of `y`. -/
theorem _root_.CategoryTheory.Adjunction.homEquivOfFullyFaithful_naturality {C Cq : Type*}
    [Category C] [Category Cq] {ι : Cq ⥤ C} (hι : ι.FullyFaithful) {Ψ : Cq ⥤ Cq}
    {L : C ⥤ C} {R : C ⥤ C} (adj : L ⊣ R) (ψ : Ψ ⋙ ι ≅ ι ⋙ L) {E K : Cq}
    (eK : ι.obj K ≅ R.obj (ι.obj E)) {I I' : Cq} (h : I ⟶ I') (y : Ψ.obj I' ⟶ E) :
    adj.homEquivOfFullyFaithful hι ψ eK I (Ψ.map h ≫ y) =
      h ≫ adj.homEquivOfFullyFaithful hι ψ eK I' y := by
  apply hι.map_injective
  simp only [Adjunction.homEquivOfFullyFaithful, Equiv.trans_apply,
    Functor.FullyFaithful.homEquiv_apply, Functor.FullyFaithful.homEquiv_symm_apply,
    Functor.FullyFaithful.map_preimage, Iso.homCongr_apply, Iso.refl_inv, Iso.refl_hom,
    Category.id_comp, Category.comp_id, Functor.map_comp, Iso.symm_hom]
  rw [← Category.assoc (ι.map h), ← Adjunction.homEquiv_naturality_left]
  congr 2
  have := ψ.inv.naturality h
  simp only [Functor.comp_map] at this
  rw [Iso.app_inv, Iso.app_inv, ← Category.assoc, ← this, Category.assoc]

/-- For a fully faithful additive `ι` between preadditive categories, the inverse of
`Adjunction.homEquivOfFullyFaithful` sends the zero morphism `I ⟶ K` to the zero morphism. -/
theorem _root_.CategoryTheory.Adjunction.homEquivOfFullyFaithful_symm_zero {C Cq : Type*}
    [Category C] [Category Cq] [Preadditive C] [Preadditive Cq]
    {ι : Cq ⥤ C} [ι.Additive] (hι : ι.FullyFaithful) {Ψ : Cq ⥤ Cq}
    {L : C ⥤ C} {R : C ⥤ C} (adj : L ⊣ R) (ψ : Ψ ⋙ ι ≅ ι ⋙ L) {E K : Cq}
    (eK : ι.obj K ≅ R.obj (ι.obj E)) (I : Cq) :
    (adj.homEquivOfFullyFaithful hι ψ eK I).symm 0 = 0 := by
  have := adj.isLeftAdjoint
  apply hι.map_injective
  simp [Adjunction.homEquivOfFullyFaithful, Adjunction.homEquiv_counit]

/-- **[Stacks, Tag 0A9C] from a representing object, for an arbitrary functor.** Let
`Ψ : D_QCoh(𝒪_X) ⥤ D`, `x : Ψ(𝒪_X) ⟶ E` and let `K` represent `I ↦ Hom(Ψ I, E)` on
`D_QCoh(𝒪_X)`, naturally in `I`, with `K|_U = 0`. Then there is a perfect `u : I ⟶ 𝒪_X`,
invertible on `U`, with `Ψ u ≫ x = 0`. -/
theorem exists_isPerfect_map_comp_eq_zero_of_represents {X U : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (j : U ⟶ X) [IsOpenImmersion j]
    [AlgebraicGeometry.QuasiCompact j] {D : Type*} [Category D] [Preadditive D]
    (Ψ : quasiCoherentDerivedCategory X ⥤ D) {E : D} {K : quasiCoherentDerivedCategory X}
    (x : Ψ.obj (𝟙_ (quasiCoherentDerivedCategory X)) ⟶ E)
    (hK : IsZero ((derivedRestrict j).obj K.obj))
    (e : ∀ I : quasiCoherentDerivedCategory X, (Ψ.obj I ⟶ E) ≃ (I ⟶ K))
    (he : ∀ {I I' : quasiCoherentDerivedCategory X} (h : I ⟶ I') (y : Ψ.obj I' ⟶ E),
      e I (Ψ.map h ≫ y) = h ≫ e I' y)
    (he0 : ∀ I, (e I).symm 0 = 0) :
    ∃ (I : quasiCoherentDerivedCategory X) (u : I ⟶ 𝟙_ (quasiCoherentDerivedCategory X)),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) I.obj ∧
        IsIso ((derivedRestrict j).map ((ObjectProperty.ι _).map u)) ∧ Ψ.map u ≫ x = 0 := by
  have : IsCompactObject.{u} (𝟙_ (quasiCoherentDerivedCategory X)) := by
    rw [tensorUnit_quasiCoherentDerivedCategory]
    exact isCompactObject_of_isPerfect _
      (isPerfect_singleFunctor_of_isFiniteLocallyFree X _ (isFiniteLocallyFree_unit X))
  have hK' : IsZero ((restrictedDerivedRestrict j).obj K) :=
    IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ hK
  obtain ⟨I, Z, u, v, w, hT, hZc, hZ0, hu⟩ :=
    SupportedGeneration.exists_distTriang_comp_eq_zero j hK' (e _ x)
  have hIc : IsCompactObject.{u} I := by
    have h1 : IsCompactObject.{u} (I⟦(1 : ℤ)⟧) :=
      isCompactObject_obj₃ _ (rot_of_distTriang _ hT)
        (inferInstance : IsCompactObject.{u} (𝟙_ (quasiCoherentDerivedCategory X))) hZc
    exact isCompactObject_of_iso ((shiftFunctorCompIsoId _ (1 : ℤ) (-1) (by simp)).app I).symm
      (isCompactObject_shift h1 (-1))
  refine ⟨I, u, isPerfect_of_isCompactObject I hIc, ?_, ?_⟩
  · have : IsIso ((restrictedDerivedRestrict j).map u) :=
      (Triangle.isZero₃_iff_isIso₁ _ ((restrictedDerivedRestrict j).map_distinguished _ hT)).1 hZ0
    exact (inferInstance : IsIso ((ObjectProperty.ι _).map ((restrictedDerivedRestrict j).map u)))
  · rw [← (e I).symm_apply_apply (Ψ.map u ≫ x), he, hu, he0]

/-- **[Stacks, Tag 0A9C] from a representing object.** Let `α : P ⟶ E` in `D_QCoh(𝒪_X)` and let
`K` represent `I ↦ Hom(I ⊗ P, E)` on `D_QCoh(𝒪_X)`, naturally in `I`, with `K|_U = 0`. Then there
is a perfect `u : I ⟶ 𝒪_X`, invertible on `U`, with `I ⊗ P ⟶ P ⟶ E` zero. -/
theorem exists_isPerfect_whiskerRight_comp_eq_zero_of_represents {X U : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X] (j : U ⟶ X) [IsOpenImmersion j]
    [AlgebraicGeometry.QuasiCompact j] {P E K : quasiCoherentDerivedCategory X} (α : P ⟶ E)
    (hK : IsZero ((derivedRestrict j).obj K.obj))
    (e : ∀ I : quasiCoherentDerivedCategory X, (I ⊗ P ⟶ E) ≃ (I ⟶ K))
    (he : ∀ {I I' : quasiCoherentDerivedCategory X} (h : I ⟶ I') (x : I' ⊗ P ⟶ E),
      e I (h ▷ P ≫ x) = h ≫ e I' x)
    (he0 : ∀ I, (e I).symm 0 = 0) :
    ∃ (I : quasiCoherentDerivedCategory X) (u : I ⟶ 𝟙_ (quasiCoherentDerivedCategory X)),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) I.obj ∧
        IsIso ((derivedRestrict j).map ((ObjectProperty.ι _).map u)) ∧
          (u ▷ P) ≫ (λ_ P).hom ≫ α = 0 :=
  exists_isPerfect_map_comp_eq_zero_of_represents j (MonoidalCategory.tensorRight P)
    ((λ_ P).hom ≫ α) hK e he he0

/-- **[Stacks, Tag 0A9C].** Let `X` be quasi-compact and quasi-separated, `U ⊆ X` a quasi-compact
open and `α : P ⟶ E` a morphism of `D_QCoh(𝒪_X)` with `E` supported on `X \ U`, where either `P`
is perfect, or `P` is pseudo-coherent and `E` is bounded below. Then there is a perfect complex
`I` and a map `u : I ⟶ 𝒪_X` invertible on `U` such that `I ⊗ᴸ P ⟶ P ⟶ E` is zero. -/
@[stacks 0A9C]
theorem exists_isPerfect_whiskerRight_comp_eq_zero {X U : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (j : U ⟶ X) [IsOpenImmersion j] [AlgebraicGeometry.QuasiCompact j]
    {P E : quasiCoherentDerivedCategory X} (α : P ⟶ E)
    (hE : IsZero ((derivedRestrict j).obj E.obj))
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) P.obj ∨
      (AlgebraicGeometry.RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) P.obj ∧
        DerivedCategoryB.IsBoundedBelow E.obj)) :
    ∃ (I : quasiCoherentDerivedCategory X) (u : I ⟶ 𝟙_ (quasiCoherentDerivedCategory X)),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) I.obj ∧
        IsIso ((derivedRestrict j).map ((ObjectProperty.ι _).map u)) ∧
          (u ▷ P) ≫ (λ_ P).hom ≫ α = 0 := by
  let K : quasiCoherentDerivedCategory X :=
    ⟨(Stacks.Duality.InternalHom.derivedSheafHom P.obj).obj E.obj, by
      rcases hP with hP | ⟨hP, hb⟩
      · exact Stacks.Duality.InternalHom.isQuasicoherent_homology_derivedSheafHom_of_isPerfect
          P.obj E.obj hP E.2
      · exact
          Stacks.Duality.InternalHom.isQuasicoherent_homology_derivedSheafHom_of_isPseudoCoherent
            P.obj E.obj hP ⟨hb, E.2⟩⟩
  let ψ := ProjectionFormulaLocallySmall.derivedTensorRightIso X P.obj
  let adj := Stacks.Duality.InternalHom.derivedTensorSheafHomAdjunction P.obj
  let ι := ObjectProperty.ι (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf))
  let hι : ι.FullyFaithful := ObjectProperty.fullyFaithfulι _
  let ψ' : MonoidalCategory.tensorRight P ⋙ ι ≅
      ι ⋙ Stacks.Duality.InternalHom.derivedTensorRight P.obj :=
    NatIso.ofComponents (fun I ↦ ψ.app I.obj) (fun f ↦ ψ.hom.naturality (ι.map f))
  exact exists_isPerfect_map_comp_eq_zero_of_represents j (MonoidalCategory.tensorRight P)
    ((λ_ P).hom ≫ α)
    (Stacks.Duality.InternalHom.isZero_derivedRestrict_derivedSheafHom j P.obj E.obj hE)
    (adj.homEquivOfFullyFaithful hι ψ' (K := K) (Iso.refl _))
    (adj.homEquivOfFullyFaithful_naturality hι ψ' _) (adj.homEquivOfFullyFaithful_symm_zero hι ψ' _)

end Stacks.Duality

end
