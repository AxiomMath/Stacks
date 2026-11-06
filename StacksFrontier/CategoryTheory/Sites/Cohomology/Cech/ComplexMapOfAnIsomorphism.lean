module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.ComplexMapOfARefinement

/-!
# The Čech complex is invariant under isomorphisms of families

Let `E = {U_i → U}` and `G = {V_j → V}` be families of morphisms with fixed target and let
`φ : E → G` be a morphism of families (Stacks 00VT) over an isomorphism `f : U ⟶ V`, whose map
of index sets is bijective and whose components `U_i ⟶ V_{φ(i)}` are isomorphisms. Then the
map of Čech complexes induced by `φ` (Stacks 03F4) is an isomorphism, so the two families have
the same Čech cohomology with coefficients in every presheaf.

## Main results

* `Stacks.CechSite.isIso_cechProductMap_of_isIso`: the maps of iterated fibre products induced
  by `φ` are isomorphisms.
* `Stacks.CechSite.isIso_cechComplexMap_of_isIso`: the induced map of Čech complexes is an
  isomorphism.
* `Stacks.CechSite.cechCohomologyIsoOfIsIso`: the resulting isomorphism of Čech cohomology.

## References

* [Stacks Project, Tag 03F4](https://stacks.math.columbia.edu/tag/03F4)
* [Stacks Project, Tag 00VT](https://stacks.math.columbia.edu/tag/00VT)
-/

@[expose] public section

universe w v v' u u'

namespace Stacks.CechSite

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] cechFormalCoproduct cechFormalCoproductMap

/-- Two morphisms into the underlying object of a nonempty product in a slice category agree as
soon as they agree after every projection. -/
theorem over_pi_left_hom_ext {C : Type u} [Category.{v} C] {U : C} {ι : Type w} {Z : ι → Over U}
    [HasProduct Z] (b₀ : ι) {W : C} {g h : W ⟶ (∏ᶜ Z).left}
    (hgh : ∀ b, g ≫ (Pi.π Z b).left = h ≫ (Pi.π Z b).left) : g = h := by
  have hw : h ≫ (∏ᶜ Z).hom = g ≫ (∏ᶜ Z).hom := by
    rw [← Over.w (Pi.π Z b₀), ← Category.assoc, ← Category.assoc, hgh b₀]
  exact congrArg CommaMorphism.left <|
    Pi.hom_ext (Over.homMk g rfl : Over.mk (g ≫ (∏ᶜ Z).hom) ⟶ ∏ᶜ Z) (Over.homMk h hw)
      fun b ↦ Over.OverMorphism.ext (hgh b)

variable {C : Type u} [Category.{v} C] {U V : C}
  {E : PreZeroHypercover.{w} U} {G : PreZeroHypercover.{w} V} {f : U ⟶ V}
  (φ : E.HomOver G f)

section Products

variable (n : ℕ) (i : Fin (n + 1) → E.I₀)
  [hE : ∀ i : Fin (n + 1) → E.I₀, HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [hG : ∀ i : Fin (n + 1) → G.I₀, HasProduct (fun a ↦ Over.mk (G.f (i a)))]

/-- The map of iterated fibre products induced by `φ`, followed by a projection. -/
@[reassoc]
theorem cechProductMap_comp_π_left (b : Fin (n + 1)) :
    cechProductMap E G φ n i ≫ (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) b).left =
      (Pi.π (fun a ↦ Over.mk (E.f (i a))) b).left ≫ φ.h₀ (i b) := by
  rw [cechProductMap, ← Over.comp_left, Pi.lift_comp_π]
  rfl

variable [IsIso f] [∀ j, IsIso (φ.h₀ j)]

/-- The inverse of the map of iterated fibre products induced by a morphism of families whose
components and whose morphism of targets are isomorphisms. -/
noncomputable def cechProductMapInv :
    (∏ᶜ (fun a ↦ Over.mk (G.f (φ.s₀ (i a))))).left ⟶ (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left :=
  (Pi.lift (P := Over.mk ((∏ᶜ (fun a ↦ Over.mk (G.f (φ.s₀ (i a))))).hom ≫ inv f))
    (fun a ↦ Over.homMk
      ((Pi.π (fun b ↦ Over.mk (G.f (φ.s₀ (i b)))) a).left ≫ inv (φ.h₀ (i a))) (by
        have hw : inv (φ.h₀ (i a)) ≫ E.f (i a) = G.f (φ.s₀ (i a)) ≫ inv f := by
          rw [IsIso.inv_comp_eq, ← Category.assoc, φ.w₀, Category.assoc, IsIso.hom_inv_id,
            Category.comp_id]
        simp only [Over.mk_hom]
        rw [Category.assoc, hw, ← Category.assoc]
        exact congrArg (· ≫ inv f) (Over.w (Pi.π (fun b ↦ Over.mk (G.f (φ.s₀ (i b)))) a))))).left

/-- The inverse map of iterated fibre products, followed by a projection: it is the projection
followed by the inverse of the component `φ.h₀ (i b)`. -/
@[reassoc]
theorem cechProductMapInv_comp_π_left (b : Fin (n + 1)) :
    cechProductMapInv φ n i ≫ (Pi.π (fun a ↦ Over.mk (E.f (i a))) b).left =
      (Pi.π (fun a ↦ Over.mk (G.f (φ.s₀ (i a)))) b).left ≫ inv (φ.h₀ (i b)) := by
  rw [cechProductMapInv, ← Over.comp_left, Pi.lift_comp_π]
  rfl

/-- **The maps of iterated fibre products induced by an isomorphism of families are
isomorphisms.** -/
theorem isIso_cechProductMap_of_isIso : IsIso (cechProductMap E G φ n i) := by
  refine ⟨⟨cechProductMapInv φ n i, ?_, ?_⟩⟩ <;>
    refine over_pi_left_hom_ext 0 (fun b ↦ ?_) <;>
    simp [cechProductMapInv_comp_π_left, cechProductMap_comp_π_left,
      cechProductMapInv_comp_π_left_assoc, cechProductMap_comp_π_left_assoc]

end Products

section Complex

variable [IsIso f] [∀ j, IsIso (φ.h₀ j)]
  {A : Type u'} [Category.{v'} A] [Preadditive A] [HasProducts.{w} A]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [∀ (n : ℕ) (i : Fin (n + 1) → G.I₀), HasProduct (fun a ↦ Over.mk (G.f (i a)))]

/-- **Stacks 03F4 along an isomorphism of families.** A morphism of families over an
isomorphism of targets, with bijective map of index sets and invertible components, induces an
isomorphism of Čech complexes. -/
theorem isIso_cechComplexMap_of_isIso (hs : Function.Bijective φ.s₀) (F : Cᵒᵖ ⥤ A) :
    IsIso (cechComplexMap E G φ F) := by
  have hdeg : ∀ n, IsIso ((cechComplexMap E G φ F).f n) := by
    intro n
    let e : (Fin (n + 1) → E.I₀) ≃ (Fin (n + 1) → G.I₀) :=
      Equiv.ofBijective (fun i ↦ φ.s₀ ∘ i) hs.comp_left
    have : ∀ i, IsIso (cechProductMap E G φ n i) := fun i ↦ isIso_cechProductMap_of_isIso φ n i
    let w : ∀ i : Fin (n + 1) → E.I₀,
        F.obj (op ((∏ᶜ (fun a ↦ Over.mk (G.f (e i a)))).left)) ≅
          F.obj (op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left)) :=
      fun i ↦ F.mapIso (asIso (cechProductMap E G φ n i)).op
    let ι : (∏ᶜ fun i : Fin (n + 1) → E.I₀ ↦
          F.obj (op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left))) ≅
        ∏ᶜ fun j : Fin (n + 1) → G.I₀ ↦
          F.obj (op ((∏ᶜ (fun a ↦ Over.mk (G.f (j a)))).left)) :=
      Pi.whiskerEquiv e w
    have h : ((cechComplexMap E G φ F).f n : (∏ᶜ fun j : Fin (n + 1) → G.I₀ ↦
          F.obj (op ((∏ᶜ (fun a ↦ Over.mk (G.f (j a)))).left))) ⟶
        ∏ᶜ fun i : Fin (n + 1) → E.I₀ ↦
          F.obj (op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left))) = ι.inv := by
      refine Pi.hom_ext _ _ (fun i ↦ ?_)
      exact (cechComplexMap_f_Pi_π E G φ F n i).trans <|
        (Pi.map'_comp_π (f := fun j : Fin (n + 1) → G.I₀ ↦
          F.obj (op ((∏ᶜ (fun a ↦ Over.mk (G.f (j a)))).left)))
        (g := fun i : Fin (n + 1) → E.I₀ ↦
          F.obj (op ((∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left))) e (fun j ↦ (w j).hom) i).symm
    exact h ▸ (inferInstance : IsIso ι.inv)
  exact HomologicalComplex.Hom.isIso_of_components _

end Complex

section Cohomology

variable [IsIso f] [∀ j, IsIso (φ.h₀ j)]
  {A : Type u'} [Category.{v'} A] [Abelian A] [HasProducts.{w} A]
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun a ↦ Over.mk (E.f (i a)))]
  [∀ (n : ℕ) (i : Fin (n + 1) → G.I₀), HasProduct (fun a ↦ Over.mk (G.f (i a)))]

/-- **Čech cohomology is invariant under an isomorphism of families with an isomorphism of
targets.** -/
noncomputable def cechCohomologyIsoOfIsIso (hs : Function.Bijective φ.s₀) (F : Cᵒᵖ ⥤ A)
    (p : ℕ) : cechCohomology G F p ≅ cechCohomology E F p :=
  have := isIso_cechComplexMap_of_isIso φ hs F
  (HomologicalComplex.homologyFunctor A (ComplexShape.up ℕ) p).mapIso
    (asIso (cechComplexMap E G φ F))

/-- Vanishing of Čech cohomology transfers along an isomorphism of families. -/
theorem isZero_cechCohomology_of_isIso (hs : Function.Bijective φ.s₀) (F : Cᵒᵖ ⥤ A) (p : ℕ)
    (h : IsZero (cechCohomology G F p)) : IsZero (cechCohomology E F p) :=
  h.of_iso (cechCohomologyIsoOfIsIso φ hs F p).symm

end Cohomology

end Stacks.CechSite

end
