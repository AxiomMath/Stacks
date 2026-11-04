module

public import StacksFrontier.RingTheory.Dualizing.RelativeBaseChangeAssembly
public import StacksFrontier.RingTheory.Dualizing.RelativeGeneratorBaseChange

/-!
# Generators of the diagonal Hom module and their base change

Let `R → A` be flat of finite presentation, `B = A ⊗[R] A`, `K` in `D(A)` and
`M = K ⊗ᴸ_A B`. A morphism `f : X ⟶ Y` is a *postcomposition generator* if every morphism
`X ⟶ Y` is `a ≫ f` for an endomorphism `a` of `X`. The endomorphisms of the diagonal are the
scalars (`Dualizing.diagonal_endomorphism_eq_smul_id`), so for `X` the diagonal this is the same
as generating the cyclic module `Hom_{D(B)}(A, M)`. This file studies when the derived base
change along `B → B' = A' ⊗[R'] A'` of such a generator `ξ : A ⟶ M` is a generator of
`Hom_{D(B')}(A', M')`.

## Main definitions

* `Dualizing.IsPostcompGenerator` — the property above.
* `Dualizing.PreservesGenerators` — a functor carries every postcomposition generator `X ⟶ Y` to
  one.
* `Dualizing.IsGeneratorPreservingAt` — derived base change along `B → B'` carries every
  postcomposition generator `A ⟶ K ⊗ᴸ_A B` to one.

## Main results

* `Dualizing.isGeneratorPreservingAt_of_exists` — it is enough that *one* postcomposition
  generator is carried to one.
* `Dualizing.IsGeneratorPreservingAt.of_iso` — the property depends only on the isomorphism class
  of `K`.
* `Dualizing.exists_isPostcompGenerator` — for a relative dualizing complex, a postcomposition
  generator exists.
* `Dualizing.span_derivedBaseChange_diagonalGenerator_of_isGeneratorPreservingAt` — under the
  property, the derived base change of a generator of the `B`-module `Hom_{D(B)}(A, M)` generates
  the `B'`-module `Hom_{D(B')}(A', M')`.

## References

* [Stacks Project, Tag 0E2F](https://stacks.math.columbia.edu/tag/0E2F)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct
open CochainComplex.DerivedExtensionScalars

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] Dualizing.smulHomRestrictedUnitSingle

universe u

namespace Dualizing

section Generator

variable {C D : Type*} [Category* C] [Category* D]

/-- `f : X ⟶ Y` is a **postcomposition generator** if every morphism `X ⟶ Y` factors as `a ≫ f`
through an endomorphism `a` of `X`. -/
def IsPostcompGenerator {X Y : C} (f : X ⟶ Y) : Prop :=
  Function.Surjective (fun a : X ⟶ X => a ≫ f)

namespace IsPostcompGenerator

/-- Conjugating by isomorphisms of the source and the target preserves the property. -/
theorem conj {X X' Y Y' : C} (eX : X ≅ X') (eY : Y ≅ Y') {f : X ⟶ Y}
    (hf : IsPostcompGenerator f) : IsPostcompGenerator (eX.inv ≫ f ≫ eY.hom) :=
  postcomp_surjective_iso eX eY f hf

/-- A morphism equal to a conjugate of a postcomposition generator is one. -/
theorem of_conj {X X' Y Y' : C} (eX : X ≅ X') (eY : Y ≅ Y') {f : X ⟶ Y} {f' : X' ⟶ Y'}
    (hf : IsPostcompGenerator f) (h : eX.inv ≫ f ≫ eY.hom = f') : IsPostcompGenerator f' :=
  h ▸ hf.conj eX eY

/-- Postcomposing with an isomorphism preserves the property. -/
theorem comp_iso {X Y Y' : C} {f : X ⟶ Y} (hf : IsPostcompGenerator f) (eY : Y ≅ Y') :
    IsPostcompGenerator (f ≫ eY.hom) :=
  hf.of_conj (Iso.refl X) eY (by simp)

/-- A fully faithful functor preserves the property. -/
theorem map {X Y : C} {f : X ⟶ Y} (hf : IsPostcompGenerator f) (F : C ⥤ D) [F.Full]
    [F.Faithful] : IsPostcompGenerator (F.map f) := by
  intro g
  obtain ⟨a, ha⟩ := hf (F.preimage g)
  exact ⟨F.map a, by
    dsimp only at ha ⊢
    rw [← F.map_comp, ha, F.map_preimage]⟩

/-- A fully faithful functor reflects the property. -/
theorem of_map {X Y : C} {f : X ⟶ Y} (F : C ⥤ D) [F.Full] [F.Faithful]
    (hf : IsPostcompGenerator (F.map f)) : IsPostcompGenerator f := by
  intro g
  obtain ⟨a, ha⟩ := hf (F.map g)
  refine ⟨F.preimage a, F.map_injective ?_⟩
  dsimp only at ha ⊢
  rw [F.map_comp, F.map_preimage, ha]

/-- The property for the image under a functor transports along a natural isomorphism. -/
theorem map_natIso {X Y : C} {f : X ⟶ Y} {F G : C ⥤ D} (α : F ≅ G)
    (hf : IsPostcompGenerator (F.map f)) : IsPostcompGenerator (G.map f) :=
  hf.of_conj (α.app X) (α.app Y) (by simp)

/-- If `f₀` factors as `a ≫ f` and the image of `f₀` under a functor is a postcomposition
generator, so is the image of `f`. -/
theorem map_of_factor {X Y : C} (F : C ⥤ D) {f f₀ : X ⟶ Y} (a : X ⟶ X) (h : a ≫ f = f₀)
    (hf₀ : IsPostcompGenerator (F.map f₀)) : IsPostcompGenerator (F.map f) := by
  intro g
  obtain ⟨b, hb⟩ := hf₀ g
  refine ⟨b ≫ F.map a, ?_⟩
  dsimp only at hb ⊢
  rw [Category.assoc, ← F.map_comp, h, hb]

end IsPostcompGenerator

/-- `F` **preserves the generators** `X ⟶ Y`: it carries every postcomposition generator
`X ⟶ Y` to one. -/
def PreservesGenerators (F : C ⥤ D) (X Y : C) : Prop :=
  ∀ f : X ⟶ Y, IsPostcompGenerator f → IsPostcompGenerator (F.map f)

namespace PreservesGenerators

variable {E : Type*} [Category* E]

/-- A fully faithful functor preserves all generators. -/
theorem of_fullyFaithful (F : C ⥤ D) [F.Full] [F.Faithful] (X Y : C) :
    PreservesGenerators F X Y :=
  fun _ hf => hf.map F

/-- The property transports along a natural isomorphism. -/
theorem of_natIso {F G : C ⥤ D} (α : F ≅ G) {X Y : C} (h : PreservesGenerators F X Y) :
    PreservesGenerators G X Y :=
  fun f hf => (h f hf).map_natIso α

/-- The property transports along isomorphisms of the two objects. -/
theorem of_iso {F : C ⥤ D} {X Y X' Y' : C} (h : PreservesGenerators F X Y) (eX : X ≅ X')
    (eY : Y ≅ Y') : PreservesGenerators F X' Y' := by
  intro f hf
  refine (h (eX.hom ≫ f ≫ eY.inv) (hf.of_conj eX.symm eY.symm (by simp))).of_conj
    (F.mapIso eX) (F.mapIso eY) ?_
  rw [Functor.mapIso_inv, Functor.mapIso_hom, ← F.map_comp, ← F.map_comp]
  congr 1
  simp

/-- If `F` preserves the generators `X ⟶ Y` and `G` preserves the generators `F X ⟶ F Y`, then
`F ⋙ G` preserves the generators `X ⟶ Y`. -/
theorem comp {F : C ⥤ D} {G : D ⥤ E} {X Y : C} (hF : PreservesGenerators F X Y)
    (hG : PreservesGenerators G (F.obj X) (F.obj Y)) : PreservesGenerators (F ⋙ G) X Y :=
  fun f hf => hG _ (hF f hf)

/-- If `F ⋙ G` preserves the generators `X ⟶ Y` and one generator `X ⟶ Y` exists, then `G`
preserves the generators `F X ⟶ F Y`. -/
theorem of_comp {F : C ⥤ D} {G : D ⥤ E} {X Y : C}
    (hFG : PreservesGenerators (F ⋙ G) X Y) (hex : ∃ ξ : X ⟶ Y, IsPostcompGenerator ξ) :
    PreservesGenerators G (F.obj X) (F.obj Y) := by
  obtain ⟨ξ, hξ⟩ := hex
  intro g hg
  obtain ⟨b, hb⟩ := hg (F.map ξ)
  exact IsPostcompGenerator.map_of_factor G b hb (hFG ξ hξ)

end PreservesGenerators

end Generator

section Diagonal

variable (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
  [Module.Flat R A]

/-- Derived base change preserves the diagonal generators of `K`: for every postcomposition
generator `ξ : A ⟶ K ⊗ᴸ_A B` in `D(B)`, its derived base change along `B → B' = A' ⊗[R'] A'` is
a postcomposition generator. -/
def IsGeneratorPreservingAt (K : DerivedCategory (ModuleCat.{u} A)) : Prop :=
  ∀ ξ : diagonalSingle R A ⟶ (diagonalDerivedExtension R A).obj K, IsPostcompGenerator ξ →
    IsPostcompGenerator
      ((totalDerivedExtensionScalars.{u, u, u} (envelopingBaseChangeRingHom R A R')).functor.map ξ)

variable {R A R'}

/-- If some postcomposition generator `ξ₀ : A ⟶ K ⊗ᴸ_A B` has a derived base change that is
one, then so does every postcomposition generator. -/
theorem isGeneratorPreservingAt_of_exists {K : DerivedCategory (ModuleCat.{u} A)}
    (h : ∃ ξ₀ : diagonalSingle R A ⟶ (diagonalDerivedExtension R A).obj K,
      IsPostcompGenerator ξ₀ ∧ IsPostcompGenerator
        ((totalDerivedExtensionScalars.{u, u, u}
          (envelopingBaseChangeRingHom R A R')).functor.map ξ₀)) :
    IsGeneratorPreservingAt R A R' K := by
  obtain ⟨ξ₀, -, hξ₀⟩ := h
  intro ξ hξ
  obtain ⟨a, ha⟩ := hξ ξ₀
  exact IsPostcompGenerator.map_of_factor _ a ha hξ₀

/-- The property depends only on the isomorphism class of `K`. -/
theorem IsGeneratorPreservingAt.of_iso {K L : DerivedCategory (ModuleCat.{u} A)}
    (hK : IsGeneratorPreservingAt R A R' K) (e : K ≅ L) :
    IsGeneratorPreservingAt R A R' L := by
  intro ξ hξ
  let eM := (diagonalDerivedExtension R A).mapIso e
  let D := (totalDerivedExtensionScalars.{u, u, u} (envelopingBaseChangeRingHom R A R')).functor
  refine ((hK (ξ ≫ eM.inv) (hξ.comp_iso eM.symm)).comp_iso (D.mapIso eM)).of_conj
    (Iso.refl _) (Iso.refl _) ?_
  simp only [Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id, Functor.mapIso_hom]
  rw [← Functor.map_comp, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- If `K` satisfies `Dualizing.IsGeneratorPreservingAt` and `ξ` generates the `B`-module
`Hom_{D(B)}(A, K ⊗ᴸ_A B)`, then its derived base change generates the `B'`-module
`Hom_{D(B')}(A', K' ⊗ᴸ_{A'} B')`, through any identifications `eΔ`, `eM`. -/
theorem span_derivedBaseChange_diagonalGenerator_of_isGeneratorPreservingAt
    {K : DerivedCategory (ModuleCat.{u} A)} (hG : IsGeneratorPreservingAt R A R' K)
    (ξ : diagonalSingle R A ⟶ (diagonalDerivedExtension R A).obj K)
    (hξ : Submodule.span (A ⊗[R] A) ({ξ} : Set _) = ⊤) :
    letI : Module.Flat R' (A ⊗[R] R') := flat_baseChange R A R'
    ∀ (eΔ : (totalDerivedExtensionScalars.{u, u, u}
            (envelopingBaseChangeRingHom R A R')).functor.obj (diagonalSingle R A) ≅
          diagonalSingle R' (A ⊗[R] R'))
      (eM : (totalDerivedExtensionScalars.{u, u, u}
            (envelopingBaseChangeRingHom R A R')).functor.obj
              ((diagonalDerivedExtension R A).obj K) ≅
          (diagonalDerivedExtension R' (A ⊗[R] R')).obj
            ((totalDerivedExtensionScalars.{u, u, u}
              (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] R')).functor.obj K)),
      Submodule.span ((A ⊗[R] R') ⊗[R'] (A ⊗[R] R'))
        ({eΔ.inv ≫ (totalDerivedExtensionScalars.{u, u, u}
          (envelopingBaseChangeRingHom R A R')).functor.map ξ ≫ eM.hom} : Set _) = ⊤ := by
  intro eΔ eM
  exact span_singleton_of_postcomp_surjective _
    (diagonal_endomorphism_eq_smul_id R' (A ⊗[R] R'))
    ((hG ξ (postcomp_surjective_of_span_singleton ξ hξ)).conj eΔ eM)

/-- If `K` is a relative dualizing complex for `R → A`, some morphism `A ⟶ K ⊗ᴸ_A B` in `D(B)`
is a postcomposition generator. -/
theorem exists_isPostcompGenerator [Algebra.FinitePresentation R A]
    {K : DerivedCategory (ModuleCat.{u} A)} (hK : IsRelativeDualizingComplex R A K) :
    ∃ ξ : diagonalSingle R A ⟶ (diagonalDerivedExtension R A).obj K, IsPostcompGenerator ξ := by
  obtain ⟨e⟩ := nonempty_linearEquiv_hom_diagonalDerivedExtension R A K hK
  let ξ' := e.symm 1
  have hξ' : IsPostcompGenerator ξ' := by
    intro g
    refine ⟨smulRestrictedUnitSingle
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom (e g) 0, ?_⟩
    show e g • e.symm 1 = g
    rw [← e.symm.map_smul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]
  exact ⟨_, hξ'.comp_iso ((shiftFunctorZero (DerivedCategory (ModuleCat.{u} (A ⊗[R] A))) ℤ).app
    ((diagonalDerivedExtension R A).obj K))⟩

end Diagonal

end Dualizing

end
