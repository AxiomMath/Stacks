module

public import StacksFrontier.AlgebraicGeometry.Stacks.TensorFunctors.TensorFunctorAlgebra
public import StacksFrontier.AlgebraicGeometry.Descent.UniversallyInjective.Defs
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.WithAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Universal injectivity of the unit of the algebra obtained from a tensor functor

Let `F : Q ⥤ ModuleCat R` be a monoidal functor and let `s : 𝟙 ⟶ X` be a morphism of `Q`.  Write
`e = F s (1) ∈ F X`.  This file proves the formal part of the proof of Stacks 0GRL.

* If there is an *evaluation* `ev : X ⊗ D ⟶ 𝟙` such that evaluation at `s`, the composite
  `D ≅ 𝟙 ⊗ D ⟶ X ⊗ D ⟶ 𝟙`, is an epimorphism, and `F` preserves epimorphisms, then
  `b ↦ b • e` has an `R`-linear left inverse: choose `λ ∈ F D` mapping to `1` and send `ξ` to
  `F ev (ξ ⊗ λ)`.
* If `s : 𝟙 ⟶ G` is the colimit of a filtered system of such maps `t : 𝟙 ⟶ X_j` (meaning
  `t ≫ ι_j = s`), each having such a left inverse, and `F` preserves the colimit, then
  `b ↦ b • F s (1)` is universally injective.

Applied to the unit `η : 𝟙 ⟶ G` of a commutative monoid object `G` this says that the structure
map `R ⟶ F G` of the commutative `R`-algebra `F G` is universally injective.

## Main definitions

* `CategoryTheory.Functor.unitElement`: the element `F s (1)` of `F X` attached to `s : 𝟙 ⟶ X`.

## Main results

* `CategoryTheory.Functor.exists_linearMap_unitElement_eq_one`: the left inverse produced by an
  evaluation.
* `CategoryTheory.Functor.universallyInjective_toSpanSingleton_unitElement`: universal injectivity
  of `b ↦ b • F s (1)` for a filtered colimit of maps with left inverses.
* `CategoryTheory.Functor.universallyInjective_algebraMap_tensorFunctor`: the structure map
  `R ⟶ F G` of the algebra `F G` is universally injective.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits MonObj Cardinal

universe u

namespace CategoryTheory.Functor

variable {Q : Type*} [Category* Q] [MonoidalCategory Q] {R : Type u} [CommRing R]
  (F : Q ⥤ ModuleCat.{u} R)

section LaxMonoidal

variable [F.LaxMonoidal]

/-- The element `F s (1)` of `F X` attached to a morphism `s : 𝟙 ⟶ X`. -/
noncomputable def unitElement {X : Q} (s : 𝟙_ Q ⟶ X) : F.obj X :=
  (F.map s).hom ((LaxMonoidal.ε F).hom (1 : R))

/-- Applying `F f` to the element `F s (1)` gives the element `F (s ≫ f) (1)`. -/
theorem map_unitElement {X Y : Q} (s : 𝟙_ Q ⟶ X) (f : X ⟶ Y) :
    (F.map f).hom (F.unitElement s) = F.unitElement (s ≫ f) := by
  simp [unitElement]

/-- Multiplying the element `F s (1)` by a section `d` of `F D` is applying `F` of the composite
`D ≅ 𝟙 ⊗ D ⟶ X ⊗ D` to `d`. -/
theorem μ_unitElement_tmul {X D : Q} (s : 𝟙_ Q ⟶ X) (d : F.obj D) :
    (LaxMonoidal.μ F X D).hom (F.unitElement s ⊗ₜ d) =
      (F.map ((λ_ D).inv ≫ s ▷ D)).hom d := by
  have h : ((LaxMonoidal.ε F ≫ F.map s) ▷ F.obj D) ≫ LaxMonoidal.μ F X D =
      (λ_ (F.obj D)).hom ≫ F.map ((λ_ D).inv ≫ s ▷ D) := by
    rw [comp_whiskerRight, Category.assoc, LaxMonoidal.μ_natural_left, LaxMonoidal.left_unitality,
      F.map_comp]
    simp only [Category.assoc, ← F.map_comp_assoc, Iso.hom_inv_id, F.map_id, Category.id_comp]
  change (((LaxMonoidal.ε F ≫ F.map s) ▷ F.obj D) ≫ LaxMonoidal.μ F X D).hom ((1 : R) ⊗ₜ d) = _
  rw [h, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_hom_apply,
    one_smul]

end LaxMonoidal

section Monoidal

variable [F.Monoidal]

/-- **An evaluation which is an epimorphism at `s` splits `b ↦ b • F s (1)`.**  Given
`ev : X ⊗ D ⟶ 𝟙` such that evaluation at `s` is an epimorphism and a functor `F` preserving
epimorphisms, there is an `R`-linear map `F X ⟶ R` sending `F s (1)` to `1`: pick `λ ∈ F D` over
`1 ∈ F 𝟙 = R` and send `ξ` to `F ev (ξ ⊗ λ)`. -/
theorem exists_linearMap_unitElement_eq_one [F.PreservesEpimorphisms] {X D : Q}
    (s : 𝟙_ Q ⟶ X) (ev : X ⊗ D ⟶ 𝟙_ Q) [Epi ((λ_ D).inv ≫ s ▷ D ≫ ev)] :
    ∃ r : F.obj X →ₗ[R] R, r (F.unitElement s) = 1 := by
  have hsurj : Function.Surjective (F.map ((λ_ D).inv ≫ s ▷ D ≫ ev)).hom :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  obtain ⟨d, hd⟩ := hsurj ((LaxMonoidal.ε F).hom (1 : R))
  refine ⟨(OplaxMonoidal.η F).hom ∘ₗ (F.map ev).hom ∘ₗ (LaxMonoidal.μ F X D).hom ∘ₗ
    (TensorProduct.mk R (F.obj X) (F.obj D)).flip d, ?_⟩
  have hη : (OplaxMonoidal.η F).hom ((LaxMonoidal.ε F).hom (1 : R)) = 1 := by
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, Monoidal.ε_η]
    rfl
  simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
    μ_unitElement_tmul]
  rw [← LinearMap.comp_apply (F.map ev).hom, ← ModuleCat.hom_comp, ← F.map_comp,
    Category.assoc, hd, hη]

end Monoidal

section Colimit

variable [F.LaxMonoidal]

/-- **Universal injectivity of `b ↦ b • F s (1)` along a filtered colimit.**  Let `s : 𝟙 ⟶ c.pt`
be the colimit of maps `t : 𝟙 ⟶ X_j` into the members of a filtered diagram (`t ≫ ι_j = s`), let
`F` preserve the colimit, and suppose that for every such `t` the map `b ↦ b • F t (1)` has an
`R`-linear left inverse.  Then `b ↦ b • F s (1)` is universally injective: an element `n` of a
module `N` with `F s (1) ⊗ n = 0` already has `F t (1) ⊗ n = 0` at some stage, where it is killed
by the left inverse. -/
theorem universallyInjective_toSpanSingleton_unitElement {J : Type u} [SmallCategory J]
    [IsFiltered J] {Φ : J ⥤ Q} {c : Cocone Φ} (hc : IsColimit (F.mapCocone c))
    (s : 𝟙_ Q ⟶ c.pt) {j₀ : J} (t₀ : 𝟙_ Q ⟶ Φ.obj j₀) (ht₀ : t₀ ≫ c.ι.app j₀ = s)
    (hret : ∀ (j : J) (t : 𝟙_ Q ⟶ Φ.obj j), t ≫ c.ι.app j = s →
      ∃ r : F.obj (Φ.obj j) →ₗ[R] R, r (F.unitElement t) = 1) :
    UniversallyInjective (LinearMap.toSpanSingleton R (F.obj c.pt) (F.unitElement s)) := by
  intro N _ _
  let T : ModuleCat.{u} R ⥤ ModuleCat.{u} R := tensorRight (ModuleCat.of R N)
  have : PreservesColimit (Φ ⋙ F) T :=
    preservesColimit_of_natIso _ (BraidedCategory.tensorLeftIsoTensorRight (ModuleCat.of R N))
  have hT : IsColimit (T.mapCocone (F.mapCocone c)) := isColimitOfPreserves T hc
  have key : ∀ n : N, F.unitElement s ⊗ₜ[R] n = 0 → n = 0 := by
    intro n hn
    have h0 : (T.mapCocone (F.mapCocone c)).ι.app j₀ (F.unitElement t₀ ⊗ₜ[R] n) =
        (T.mapCocone (F.mapCocone c)).ι.app j₀ 0 := by
      rw [map_zero, ← hn, ← ht₀, ← map_unitElement]
      rfl
    obtain ⟨k, f, g, hfg⟩ :=
      Concrete.isColimit_exists_of_rep_eq.{u} (Φ ⋙ F ⋙ T) hT _ _ h0
    have hfg' : F.unitElement (t₀ ≫ Φ.map f) ⊗ₜ[R] n = 0 := by
      rwa [← map_unitElement]
    obtain ⟨r, hr⟩ := hret k (t₀ ≫ Φ.map f) (by rw [Category.assoc, c.w, ht₀])
    simpa [hr] using congrArg (TensorProduct.lid R N ∘ r.rTensor N) hfg'
  intro x y hxy
  obtain ⟨x, rfl⟩ := (TensorProduct.lid R N).symm.surjective x
  obtain ⟨y, rfl⟩ := (TensorProduct.lid R N).symm.surjective y
  congr 1
  rw [← sub_eq_zero]
  apply key
  have : ∀ z : N, ((LinearMap.toSpanSingleton R (F.obj c.pt) (F.unitElement s)).rTensor N)
      ((TensorProduct.lid R N).symm z) = F.unitElement s ⊗ₜ[R] z := fun z => by simp
  rw [TensorProduct.tmul_sub, ← this, ← this, hxy, sub_self]

end Colimit

section Algebra

open ModuleCat.MonModuleEquivalenceAlgebra

variable [BraidedCategory Q] (G : Q) [MonObj G] [IsCommMonObj G] [F.LaxBraided]

/-- The structure map of the commutative `R`-algebra `F G` is `b ↦ b • F η (1)`. -/
theorem algebraLinearMap_tensorFunctor_eq :
    letI := tensorFunctorCommRing F G
    letI := tensorFunctorAlgebraStr F G
    Algebra.linearMap R (F.obj G) = LinearMap.toSpanSingleton R (F.obj G) (F.unitElement η[G]) := by
  let := tensorFunctorCommRing F G
  let := tensorFunctorAlgebraStr F G
  ext
  simp only [Algebra.linearMap_apply, LinearMap.toSpanSingleton_apply, one_smul]
  rfl

/-- **The structure map `R ⟶ F G` of the algebra `F G` is universally injective** as soon as the
unit `η : 𝟙 ⟶ G` is a filtered colimit, preserved by `F`, of maps `t : 𝟙 ⟶ X_j` for each of which
`b ↦ b • F t (1)` has a left inverse. -/
theorem universallyInjective_algebraMap_tensorFunctor {J : Type u} [SmallCategory J]
    [IsFiltered J] {Φ : J ⥤ Q} {c : Cocone Φ} (hcG : c.pt = G)
    (hc : IsColimit (F.mapCocone c)) {j₀ : J} (t₀ : 𝟙_ Q ⟶ Φ.obj j₀)
    (ht₀ : t₀ ≫ c.ι.app j₀ ≫ eqToHom hcG = η[G])
    (hret : ∀ (j : J) (t : 𝟙_ Q ⟶ Φ.obj j), t ≫ c.ι.app j ≫ eqToHom hcG = η[G] →
      ∃ r : F.obj (Φ.obj j) →ₗ[R] R, r (F.unitElement t) = 1) :
    letI := tensorFunctorCommRing F G
    letI := tensorFunctorAlgebraStr F G
    Algebra.UniversallyInjective R (F.obj G) := by
  subst hcG
  let := tensorFunctorCommRing F c.pt
  let := tensorFunctorAlgebraStr F c.pt
  simp only [eqToHom_refl, Category.comp_id] at ht₀ hret
  unfold Algebra.UniversallyInjective
  rw [algebraLinearMap_tensorFunctor_eq]
  exact universallyInjective_toSpanSingleton_unitElement F hc η[c.pt] t₀ ht₀ hret

end Algebra

section AlgebraOfInd

/-- **The structure map `R ⟶ F G` is universally injective when `G` is a filtered colimit of
objects with evaluations.**  Let `F` be a braided monoidal functor preserving epimorphisms and
filtered colimits, let the unit `𝟙` be finitely presentable, and let `G` be a filtered colimit of
objects satisfying `P`.  Suppose that for every `X` satisfying `P` and every factorization
`η = t ≫ ι` of the unit of `G` through `X` there is an evaluation `ev : X ⊗ D ⟶ 𝟙` whose
evaluation at `t` is an epimorphism.  Then `R ⟶ F G` is universally injective. -/
theorem universallyInjective_algebraMap_tensorFunctor_of_ind [BraidedCategory Q] [F.Braided]
    [F.PreservesEpimorphisms] [PreservesFilteredColimitsOfSize.{u, u} F]
    (P : ObjectProperty Q) (G : Q) [MonObj G] [IsCommMonObj G]
    (hunit : IsFinitelyPresentable.{u} (𝟙_ Q)) (hG : P.ind.{u} G)
    (hdual : ∀ (X : Q), P X → ∀ (t : 𝟙_ Q ⟶ X) (ι : X ⟶ G), t ≫ ι = η[G] →
      ∃ (D : Q) (ev : X ⊗ D ⟶ 𝟙_ Q), Epi ((λ_ D).inv ≫ t ▷ D ≫ ev)) :
    letI := tensorFunctorCommRing F G
    letI := tensorFunctorAlgebraStr F G
    Algebra.UniversallyInjective R (F.obj G) := by
  obtain ⟨J, _, _, pres, hP⟩ := hG
  have : Fact Cardinal.aleph0.{u}.IsRegular := Cardinal.fact_isRegular_aleph0
  have : IsCardinalFiltered J Cardinal.aleph0.{u} := (isCardinalFiltered_aleph0_iff J).mpr ‹_›
  obtain ⟨j₀, t₀, ht₀⟩ :=
    IsCardinalPresentable.exists_hom_of_isColimit Cardinal.aleph0.{u} pres.isColimit η[G]
  refine universallyInjective_algebraMap_tensorFunctor F G (c := Cocone.mk G pres.ι) rfl
    (isColimitOfPreserves F pres.isColimit) t₀ (by simpa using ht₀) fun j t ht => by
      obtain ⟨D, ev, hev⟩ := hdual _ (hP j) t (pres.ι.app j) (by simpa using ht)
      exact exists_linearMap_unitElement_eq_one F t ev

end AlgebraOfInd

section Descent

/-- **A map to `𝟙` is an epimorphism if it is one after tensoring with a faithfully flat algebra,
and it is so as soon as the unit of the algebra lifts.**  Let `G` be a monoid object such that
`G ⊗ -` reflects epimorphisms, and let `f : D ⟶ 𝟙`.  If `G ⊗ f : G ⊗ D ⟶ G` hits the unit
`η : 𝟙 ⟶ G`, that is `t ≫ (G ◁ f) = η ≫ ρ⁻¹` for some `t : 𝟙 ⟶ G ⊗ D`, then `G ◁ f` is a split
epimorphism (its `G`-linear section is `G ≅ G ⊗ 𝟙 ⟶ G ⊗ G ⊗ D ⟶ G ⊗ D`), hence `f` is an
epimorphism. -/
theorem epi_of_whiskerLeft_comp_eq (G : Q) [MonObj G] [(tensorLeft G).ReflectsEpimorphisms]
    {D : Q} (f : D ⟶ 𝟙_ Q) (t : 𝟙_ Q ⟶ G ⊗ D) (ht : t ≫ G ◁ f = η[G] ≫ (ρ_ G).inv) :
    Epi f := by
  obtain ⟨σ, hσ⟩ : ∃ σ : G ⟶ G ⊗ D, σ ≫ G ◁ f = (ρ_ G).inv :=
    ⟨(ρ_ G).inv ≫ G ◁ t ≫ (α_ G G D).inv ≫ μ[G] ▷ D, by
      simp only [Category.assoc]
      rw [← whisker_exchange, ← associator_inv_naturality_right_assoc,
        ← MonoidalCategory.whiskerLeft_comp_assoc, ht]
      simp⟩
  have : IsSplitEpi (G ◁ f) := ⟨⟨(ρ_ G).hom ≫ σ, by rw [Category.assoc, hσ, Iso.hom_inv_id]⟩⟩
  exact (tensorLeft G).epi_of_epi_map (f := f) (inferInstanceAs (Epi (G ◁ f)))

end Descent

end CategoryTheory.Functor
