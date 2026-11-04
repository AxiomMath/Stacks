module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.SigmaPresheafComparison

/-!
# A coproduct of sheaves is the sheafification of the coproduct of the presheaves

Let `G : I → Sheaf J A` be a family of sheaves on a site admitting sheafification. The comparison
morphism `CategoryTheory.Sheaf.sigmaPresheafComparison` from the coproduct of the underlying
presheaves to the underlying presheaf of the coproduct of the sheaves becomes an isomorphism after
sheafification: sheafification is a left adjoint, so it preserves the coproduct, and on a sheaf
its counit is an isomorphism.

Consequently the comparison is locally injective and locally surjective. Those are the two facts
about a coproduct of sheaves that a concrete computation with its sections needs: a section of the
coproduct is, locally on a covering, a finitely supported family of sections of the summands, and
two such families with the same image are locally equal.

## Main results

* `CategoryTheory.Sheaf.isIso_presheafToSheaf_map_sigmaPresheafComparison`: the comparison becomes
  an isomorphism after sheafification.
* `CategoryTheory.Sheaf.isLocallyInjective_sigmaPresheafComparison` and
  `CategoryTheory.Sheaf.isLocallySurjective_sigmaPresheafComparison`: **the comparison is locally
  bijective.**

## Implementation notes

The isomorphism is produced by exhibiting a two-sided inverse rather than by transporting colimit
cocones: the coproduct of sheaves has a universal property for morphisms out of it, which gives
one composite directly, and the other composite is checked through the injectivity of the
sheafification adjunction's hom-equivalence, which reduces it to a statement about morphisms out
of the coproduct of presheaves. Transporting cocones instead would require identifying
`Discrete.functor (fun i ↦ (G i).obj) ⋙ presheafToSheaf J A` with
`Discrete.functor (fun i ↦ (presheafToSheaf J A).obj (G i).obj)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w' w v₂ u₂ v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {A : Type u₂}
  [Category.{v₂} A] [HasWeakSheafify J A] {I : Type w} (G : I → Sheaf J A) [HasCoproduct G]
  [HasCoproduct fun i ↦ (G i).obj]

/-- **The comparison morphism from the coproduct of the underlying presheaves of a family of
sheaves to the underlying presheaf of their coproduct becomes an isomorphism after
sheafification.**

Sheafification is a left adjoint, so the coproduct of the presheaves sheafifies to the coproduct
of their sheafifications, and the sheafification of a sheaf is that sheaf. -/
theorem isIso_presheafToSheaf_map_sigmaPresheafComparison :
    IsIso ((presheafToSheaf J A).map (sigmaPresheafComparison G)) := by
  set L := presheafToSheaf J A with hL
  set adj := sheafificationAdjunction J A with hadj
  set P := ∐ fun i ↦ (G i).obj with hP
  set ε : ∀ i, L.obj ((G i).obj) ⟶ G i := fun i => adj.counit.app (G i) with hε
  set Φ : L.obj P ⟶ ∐ G := L.map (sigmaPresheafComparison G) ≫ adj.counit.app (∐ G) with hΦ
  set Ψ : (∐ G) ⟶ L.obj P := Sigma.desc fun i =>
    inv (ε i) ≫ L.map (Sigma.ι (fun j ↦ (G j).obj) i) with hΨ
  have hunit : ∀ i, adj.unit.app ((G i).obj) = (sheafToPresheaf J A).map (inv (ε i)) := by
    intro i
    have e1 : adj.unit.app ((G i).obj) ≫ (sheafToPresheaf J A).map (ε i) = 𝟙 _ :=
      adj.right_triangle_components (G i)
    have e2 : (sheafToPresheaf J A).map (inv (ε i)) ≫
        (sheafToPresheaf J A).map (ε i) = 𝟙 _ := by
      rw [← Functor.map_comp, IsIso.inv_hom_id, Functor.map_id]
    have : IsIso ((sheafToPresheaf J A).map (ε i)) := inferInstance
    exact (cancel_mono ((sheafToPresheaf J A).map (ε i))).mp (e1.trans e2.symm)
  have hιcomp : ∀ i, Sigma.ι (fun j ↦ (G j).obj) i ≫ sigmaPresheafComparison G =
      (sheafToPresheaf J A).map (Sigma.ι G i) := fun i => ι_sigmaPresheafComparison G i
  have hkey : ∀ i, L.map (Sigma.ι (fun j ↦ (G j).obj) i) ≫ Φ = ε i ≫ Sigma.ι G i := by
    intro i
    rw [hΦ, ← Category.assoc, ← L.map_comp, hιcomp i]
    exact adj.counit.naturality (Sigma.ι G i)
  have h1 : Ψ ≫ Φ = 𝟙 _ := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [Category.comp_id, ← Category.assoc, hΨ, Sigma.ι_desc, Category.assoc, hkey i,
      IsIso.inv_hom_id_assoc]
  have hΦhom : adj.unit.app P ≫ (sheafToPresheaf J A).map Φ = sigmaPresheafComparison G :=
    (adj.homEquiv P (∐ G)).apply_symm_apply (sigmaPresheafComparison G)
  have hΨhom : ∀ i, (sheafToPresheaf J A).map (Sigma.ι G i) ≫
      (sheafToPresheaf J A).map Ψ = Sigma.ι (fun j ↦ (G j).obj) i ≫ adj.unit.app P := by
    intro i
    rw [← Functor.map_comp, hΨ, Sigma.ι_desc, Functor.map_comp, ← hunit i]
    exact (adj.unit.naturality (Sigma.ι (fun j ↦ (G j).obj) i)).symm
  have h2 : Φ ≫ Ψ = 𝟙 _ := by
    refine (adj.homEquiv P (L.obj P)).injective ?_
    have hL1 : adj.homEquiv P (L.obj P) (Φ ≫ Ψ) =
        (adj.unit.app P ≫ (sheafToPresheaf J A).map Φ) ≫ (sheafToPresheaf J A).map Ψ := by
      rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    have hR1 : adj.homEquiv P (L.obj P) (𝟙 (L.obj P)) = adj.unit.app P := by
      rw [Adjunction.homEquiv_unit, Functor.map_id]
      exact Category.comp_id _
    rw [hL1, hR1, hΦhom]
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, hιcomp i, hΨhom i]
  have hiso : IsIso Φ := ⟨Ψ, h2, h1⟩
  have hcancel : L.map (sigmaPresheafComparison G) = Φ ≫ inv (adj.counit.app (∐ G)) := by
    rw [hΦ, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [hcancel]
  infer_instance

section Concrete

variable {FA : A → A → Type*} {CA : A → Type w'} [∀ Y Z, FunLike (FA Y Z) (CA Y) (CA Z)]
  [ConcreteCategory.{w'} A FA]

/-- The comparison morphism is among the morphisms inverted by sheafification. -/
private theorem W_sigmaPresheafComparison [J.WEqualsLocallyBijective A] :
    J.W (sigmaPresheafComparison G) :=
  (GrothendieckTopology.W_iff J _).2 (isIso_presheafToSheaf_map_sigmaPresheafComparison G)

/-- **The comparison morphism to the underlying presheaf of a coproduct of sheaves is locally
injective**: two finitely supported families of sections of the summands with the same image agree
on a covering. -/
theorem isLocallyInjective_sigmaPresheafComparison [J.WEqualsLocallyBijective A] :
    Presheaf.IsLocallyInjective J (sigmaPresheafComparison G) :=
  (W_sigmaPresheafComparison G).isLocallyInjective

/-- **The comparison morphism to the underlying presheaf of a coproduct of sheaves is locally
surjective**: a section of the coproduct of a family of sheaves is, on a covering, a finitely
supported family of sections of the summands. -/
theorem isLocallySurjective_sigmaPresheafComparison [J.WEqualsLocallyBijective A] :
    Presheaf.IsLocallySurjective J (sigmaPresheafComparison G) :=
  (W_sigmaPresheafComparison G).isLocallySurjective

end Concrete

end CategoryTheory.Sheaf

end
