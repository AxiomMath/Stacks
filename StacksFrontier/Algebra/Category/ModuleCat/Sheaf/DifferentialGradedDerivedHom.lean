module

public import Mathlib.CategoryTheory.ObjectProperty.Local
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Yoneda
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedCategory

/-!
# Morphisms in the derived category of a sheaf of differential graded algebras

Let `R` be a sheaf of rings on a site admitting sheafification and let `A` be a sheaf of
differential graded `R`-algebras. A right differential graded `A`-module `I` is *local for the
quasi-isomorphisms* when precomposition with a quasi-isomorphism is bijective on homotopy
classes of morphisms into `I`. For such an `I` the localization functor
`K(Mod(A, d)) ⟶ D(A, d)` is bijective on morphisms into `I`, so for any quasi-isomorphism
`N ⟶ I` one has `Hom_{D(A, d)}(M, N) = Hom_{K(Mod(A, d))}(M, I)`; and a quasi-isomorphism
between two such modules is already invertible in `K(Mod(A, d))`, hence is sent to an
isomorphism by every functor out of the homotopy category.

The underlying statement is about an arbitrary localization: morphisms of `C` into a
`W`-local object `I` are the same as morphisms of `W.Localization` into the image of `I`.

## Main definitions

* `CategoryTheory.MorphismProperty.localizationHomEquiv`: for `I` a `W`-local object, the
  bijection between `M ⟶ I` and `W.Q.obj M ⟶ W.Q.obj I`.
* `SheafOfModules.DifferentialGradedModule.derivedHomEquivHomotopyHom`: the identification
  `Hom_{D(A, d)}(M, N) = Hom_{K(Mod(A, d))}(M, I)` attached to a quasi-isomorphism `N ⟶ I`
  with `I` local for the quasi-isomorphisms.

## Main results

* `CategoryTheory.MorphismProperty.Q_map_bijective_of_isLocal`: the localization functor is
  bijective on morphisms into a `W`-local object.
* `SheafOfModules.DifferentialGradedModule.isIso_toDerivedCategory_map_quotient_map`: the
  localization functor `K(Mod(A, d)) ⟶ D(A, d)` inverts quasi-isomorphisms.
* `SheafOfModules.DifferentialGradedModule.derivedHomEquivHomotopyHom_symm_apply`: the
  inverse of the identification above sends a homotopy class to its image in `D(A, d)` composed
  with the inverse of the given quasi-isomorphism.
* `SheafOfModules.DifferentialGradedModule.isIso_quotient_map_of_quasiIso_of_isLocal`: a
  quasi-isomorphism between two modules local for the quasi-isomorphisms is an isomorphism of
  `K(Mod(A, d))`.

## References

* [Stacks Project, Tag 0FT8](https://stacks.math.columbia.edu/tag/0FT8)
* [Stacks Project, Tag 0FTN](https://stacks.math.columbia.edu/tag/0FTN)
* [Stacks Project, Tag 0FSX](https://stacks.math.columbia.edu/tag/0FSX)
* [Stacks Project, Tag 0FT5](https://stacks.math.columbia.edu/tag/0FT5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Localization.Construction

/-! ### Morphisms into a local object of a localized category -/

namespace CategoryTheory.MorphismProperty

universe v u

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C}

/-- Morphisms into a fixed object `I`, as a functor to the opposite of the category of types.
It inverts `W` exactly when `I` is `W`-local. -/
private noncomputable abbrev homInto (I : C) : C ⥤ (Type v)ᵒᵖ := (yoneda.obj I).rightOp

private theorem homInto_isInvertedBy {I : C} (hI : W.isLocal I) :
    W.IsInvertedBy (homInto.{v} I) := by
  intro X Y w hw
  rw [Functor.rightOp_map, isIso_op_iff, isIso_iff_bijective]
  exact hI w hw

/-- The functor `X ↦ (X ⟶ I)` on the localized category, for `I` a `W`-local object. -/
private noncomputable def homIntoLocalization {I : C} (hI : W.isLocal I) :
    W.Localization ⥤ (Type v)ᵒᵖ :=
  Localization.Construction.lift (homInto.{v} I) (homInto_isInvertedBy hI)

/-- The left inverse of the localization functor on morphisms into a `W`-local object:
evaluate the lifted functor `X ↦ (X ⟶ I)` at the identity of `I`. -/
private noncomputable def retractOfLocal {I : C} (hI : W.isLocal I) {M : C}
    (z : W.Q.obj M ⟶ W.Q.obj I) : M ⟶ I :=
  ((homIntoLocalization.{v} hI).map z).unop (𝟙 I)

private theorem retractOfLocal_Q_map {I : C} (hI : W.isLocal I) {M : C} (f : M ⟶ I) :
    retractOfLocal hI (W.Q.map f) = f := by
  show ((homInto.{v} I).map f).unop (𝟙 I) = f
  simp

/-- The localization functor is injective on morphisms into a `W`-local object. -/
theorem Q_map_injective_of_isLocal {I : C} (hI : W.isLocal I) (M : C) :
    Function.Injective (fun f : M ⟶ I => W.Q.map f) := fun f g hfg =>
  (retractOfLocal_Q_map hI f).symm.trans
    ((congrArg (retractOfLocal hI) hfg).trans (retractOfLocal_Q_map hI g))

/-- The morphisms of the localized category factoring, after composition with a morphism into
a `W`-local object `I`, through a morphism of `C` into `I`. -/
private def factorsThroughLocal (I : C) : MorphismProperty W.Localization :=
  fun X Y h => ∀ ⦃M N : C⦄ (eM : W.Q.obj M = X) (eN : W.Q.obj N = Y) (g : N ⟶ I),
    ∃ f : M ⟶ I, eqToHom eM ≫ h ≫ eqToHom eN.symm ≫ W.Q.map g = W.Q.map f

private instance (I : C) : (factorsThroughLocal (W := W) I).IsStableUnderComposition where
  comp_mem {_ Y _} h₁ h₂ p₁ p₂ := by
    intro M P eM eP g
    have eY : W.Q.obj ((objEquiv W).symm Y) = Y := (objEquiv W).right_inv Y
    obtain ⟨f₂, hf₂⟩ := p₂ eY eP g
    obtain ⟨f₁, hf₁⟩ := p₁ eM eY f₂
    exact ⟨f₁, by rw [← hf₁, ← hf₂]; simp⟩

private theorem factorsThroughLocal_eq_top {I : C} (hI : W.isLocal I) :
    factorsThroughLocal (W := W) I = ⊤ := by
  refine morphismProperty_eq_top _ ?_ ?_
  · intro X Y f M N eM eN g
    obtain rfl : M = X := (objEquiv W).injective eM
    obtain rfl : N = Y := (objEquiv W).injective eN
    exact ⟨f ≫ g, by simp⟩
  · intro X Y w hw M N eM eN g
    obtain rfl : M = Y := (objEquiv W).injective eM
    obtain rfl : N = X := (objEquiv W).injective eN
    obtain ⟨g', hg'⟩ := (hI w hw).2 g
    refine ⟨g', ?_⟩
    rw [show g = w ≫ g' from hg'.symm, Functor.map_comp]
    simp only [eqToHom_refl, Category.id_comp]
    rw [← Category.assoc, show wInv w hw ≫ W.Q.map w = 𝟙 _ from (wIso w hw).inv_hom_id,
      Category.id_comp]

/-- The localization functor is surjective on morphisms into a `W`-local object. -/
theorem Q_map_surjective_of_isLocal {I : C} (hI : W.isLocal I) (M : C) :
    Function.Surjective (fun f : M ⟶ I => W.Q.map f) := by
  intro h
  have hP : factorsThroughLocal (W := W) I h := by
    rw [factorsThroughLocal_eq_top hI]
    exact MorphismProperty.top_apply h
  obtain ⟨f, hf⟩ := hP rfl rfl (𝟙 I)
  exact ⟨f, by simpa using hf.symm⟩

/-- **Morphisms into a `W`-local object are not changed by localization**: for `I` a `W`-local
object the localization functor is bijective from `M ⟶ I` onto `W.Q.obj M ⟶ W.Q.obj I`. -/
theorem Q_map_bijective_of_isLocal {I : C} (hI : W.isLocal I) (M : C) :
    Function.Bijective (fun f : M ⟶ I => W.Q.map f) :=
  ⟨Q_map_injective_of_isLocal hI M, Q_map_surjective_of_isLocal hI M⟩

/-- The bijection `(M ⟶ I) ≃ (W.Q.obj M ⟶ W.Q.obj I)` given by the localization functor, for
`I` a `W`-local object. -/
noncomputable def localizationHomEquiv {I : C} (hI : W.isLocal I) (M : C) :
    (M ⟶ I) ≃ (W.Q.obj M ⟶ W.Q.obj I) :=
  Equiv.ofBijective _ (Q_map_bijective_of_isLocal hI M)

/-- `localizationHomEquiv` sends `f : M ⟶ I` to `W.Q.map f`. -/
@[simp]
theorem localizationHomEquiv_apply {I : C} (hI : W.isLocal I) (M : C) (f : M ⟶ I) :
    localizationHomEquiv hI M f = W.Q.map f := rfl

/-- A morphism of `W` between two `W`-local objects is an isomorphism. -/
theorem isIso_of_isLocal {I I' : C} (hI : W.isLocal I) (hI' : W.isLocal I') {w : I ⟶ I'}
    (hw : W w) : IsIso w :=
  (ObjectProperty.isLocal_iff_isIso _ w hI hI').1 (W.le_isLocal_isLocal w hw)

end CategoryTheory.MorphismProperty

/-! ### Morphisms in the derived category of a sheaf of differential graded algebras -/

namespace SheafOfModules.DifferentialGradedModule

universe t a m v u

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  {A : DifferentialGradedAlgebra.{t, a} R}

/-- The localization functor `K(Mod(A, d)) ⟶ D(A, d)` inverts quasi-isomorphisms. -/
theorem isIso_toDerivedCategory_map_quotient_map {M N : DifferentialGradedModule.{t, a, m} A}
    (b : M ⟶ N) (hb : QuasiIso b.toHomologicalComplex) :
    IsIso ((toDerivedCategory.{t, a, m} A).map ((HomotopyCategory.quotient A).map b)) :=
  MorphismProperty.Q_inverts _ _ ((quasiIsomorphisms_quotient_map_iff b).2 hb)

/-- The image in `D(A, d)` of a quasi-isomorphism of right differential graded modules, as an
isomorphism. -/
noncomputable def toDerivedCategoryIso {M N : DifferentialGradedModule.{t, a, m} A} (b : M ⟶ N)
    (hb : QuasiIso b.toHomologicalComplex) :
    (toDerivedCategory.{t, a, m} A).obj ((HomotopyCategory.quotient A).obj M) ≅
      (toDerivedCategory.{t, a, m} A).obj ((HomotopyCategory.quotient A).obj N) :=
  letI := isIso_toDerivedCategory_map_quotient_map b hb
  asIso ((toDerivedCategory.{t, a, m} A).map ((HomotopyCategory.quotient A).map b))

/-- Let `(A, d)` be a sheaf of differential graded algebras, let `M`, `N` be right differential
graded `A`-modules and let `N ⟶ I` be a quasi-isomorphism into a right differential graded module
`I` which is local for the quasi-isomorphisms of `K(Mod(A, d))`. Then morphisms `M ⟶ N` in
`D(A, d)` are the homotopy classes of morphisms `M ⟶ I`. -/
noncomputable def derivedHomEquivHomotopyHom {M N I : DifferentialGradedModule.{t, a, m} A}
    (hI : (quasiIsomorphisms.{t, a, m} A).isLocal ((HomotopyCategory.quotient A).obj I))
    {b : N ⟶ I} (hb : QuasiIso b.toHomologicalComplex) :
    ((toDerivedCategory.{t, a, m} A).obj ((HomotopyCategory.quotient A).obj M) ⟶
        (toDerivedCategory.{t, a, m} A).obj ((HomotopyCategory.quotient A).obj N)) ≃
      ((HomotopyCategory.quotient A).obj M ⟶ (HomotopyCategory.quotient A).obj I) :=
  ((Iso.refl _).homCongr (toDerivedCategoryIso b hb)).trans
    (MorphismProperty.localizationHomEquiv hI ((HomotopyCategory.quotient A).obj M)).symm

/-- The inverse of `derivedHomEquivHomotopyHom` sends a homotopy class `f : M ⟶ I` to its image in
`D(A, d)` composed with the inverse of the given quasi-isomorphism. -/
theorem derivedHomEquivHomotopyHom_symm_apply {M N I : DifferentialGradedModule.{t, a, m} A}
    (hI : (quasiIsomorphisms.{t, a, m} A).isLocal ((HomotopyCategory.quotient A).obj I))
    {b : N ⟶ I} (hb : QuasiIso b.toHomologicalComplex)
    (f : (HomotopyCategory.quotient A).obj M ⟶ (HomotopyCategory.quotient A).obj I) :
    (derivedHomEquivHomotopyHom (M := M) hI hb).symm f =
      (toDerivedCategory.{t, a, m} A).map f ≫ (toDerivedCategoryIso b hb).inv := by
  simp [derivedHomEquivHomotopyHom, Iso.homCongr]

/-- A quasi-isomorphism between two right differential graded modules which are local for the
quasi-isomorphisms of `K(Mod(A, d))` is an isomorphism of `K(Mod(A, d))`. -/
theorem isIso_quotient_map_of_quasiIso_of_isLocal
    {I I' : DifferentialGradedModule.{t, a, m} A}
    (hI : (quasiIsomorphisms.{t, a, m} A).isLocal ((HomotopyCategory.quotient A).obj I))
    (hI' : (quasiIsomorphisms.{t, a, m} A).isLocal ((HomotopyCategory.quotient A).obj I'))
    {w : I ⟶ I'} (hw : QuasiIso w.toHomologicalComplex) :
    IsIso ((HomotopyCategory.quotient A).map w) :=
  MorphismProperty.isIso_of_isLocal hI hI' ((quasiIsomorphisms_quotient_map_iff w).2 hw)

/-- Every functor out of `K(Mod(A, d))` sends a quasi-isomorphism between two right differential
graded modules which are local for the quasi-isomorphisms to an isomorphism. -/
theorem isIso_map_quotient_map_of_quasiIso_of_isLocal {D : Type*} [Category D]
    (T : HomotopyCategory.{t, a, m} A ⥤ D) {I I' : DifferentialGradedModule.{t, a, m} A}
    (hI : (quasiIsomorphisms.{t, a, m} A).isLocal ((HomotopyCategory.quotient A).obj I))
    (hI' : (quasiIsomorphisms.{t, a, m} A).isLocal ((HomotopyCategory.quotient A).obj I'))
    {w : I ⟶ I'} (hw : QuasiIso w.toHomologicalComplex) :
    IsIso (T.map ((HomotopyCategory.quotient A).map w)) :=
  let := isIso_quotient_map_of_quasiIso_of_isLocal hI hI' hw
  inferInstance

end SheafOfModules.DifferentialGradedModule

end
