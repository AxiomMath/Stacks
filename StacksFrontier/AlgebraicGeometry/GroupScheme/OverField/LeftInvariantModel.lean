/-
Copyright (c) 2026 AxiomMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.GenericQuotientFlat
public import Mathlib.AlgebraicGeometry.Birational.RationalMap

/-!
# A rational action of a group scheme from a point of its generic fibre

Let `G` be an integral group scheme over an algebraically closed field `k` and `π : V ⟶ X` a
dominant morphism from an open of `G` to a separated integral `k`-scheme of finite type. A
`k`-morphism `φ : Spec K(G × X) ⟶ X` spreads out to a morphism `F` on a dense open of `G × X`. If
`φ ∘ (id × π)` and `π ∘ μ` agree on `Spec 𝒪_{G × G, θ}` at one point `θ` of `G × V` lying over the
generic point of `G × X`, then `F (a, π b) = π (a b)` on a dense open of `G × G`, and `π` is flat
on a nonempty open of `V`.

## Main results

* `AlgebraicGeometry.GenericQuotientFlat.exists_localRationalAction_of_functionFieldAction`: `φ`
  spreads out to a morphism `F` with `F (a, π b) = π (a b)` on a dense open of `G × G`.
* `AlgebraicGeometry.GenericQuotientFlat.exists_open_flatAt_of_functionFieldAction`: `π` is flat
  on a nonempty open of `V`.
* `AlgebraicGeometry.GenericQuotientFlat.SpecMap_stalkMapOfEq_fromSpecStalk`,
  `AlgebraicGeometry.GenericQuotientFlat.fromSpecStalkOfMem_homOfLE`: naturality of the
  canonical maps `Spec 𝒪_{X, x} ⟶ X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CartesianMonoidalCategory MonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.GenericQuotientFlat

/-- The canonical maps `Spec 𝒪_{X, x} ⟶ X` are natural, with the target point up to equality. -/
lemma SpecMap_stalkMapOfEq_fromSpecStalk {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (y : Y)
    (h : f x = y) :
    Spec.map (f.stalkMapOfEq x y h) ≫ Y.fromSpecStalk y = X.fromSpecStalk x ≫ f := by
  subst h
  rw [Scheme.Hom.stalkMapOfEq, stalkCongr_hom_self, Category.id_comp,
    Scheme.SpecMap_stalkMap_fromSpecStalk]

/-- `Spec 𝒪_{X, x} ⟶ U ⟶ V` for opens `x ∈ U ⊆ V`. -/
lemma fromSpecStalkOfMem_homOfLE {X : Scheme.{u}} {U V : X.Opens} (hUV : U ≤ V) (x : X)
    (hx : x ∈ U) : U.fromSpecStalkOfMem x hx ≫ X.homOfLE hUV = V.fromSpecStalkOfMem x (hUV hx) := by
  rw [← cancel_mono V.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.Opens.fromSpecStalkOfMem_ι,
    Scheme.Opens.fromSpecStalkOfMem_ι]

/-- Over an algebraically closed field the product of two integral schemes is integral. -/
instance isIntegral_tensor_left {k : Type u} [Field k] [IsAlgClosed k]
    (A B : Over (Spec (.of k))) [IsIntegral A.left] [IsIntegral B.left] :
    IsIntegral (A ⊗ B).left :=
  isIntegral_pullback_of_isAlgClosed A.hom B.hom

section Model

variable {k : Type u} [Field k] (G : Over (Spec (.of k))) [GrpObj G] (X : Over (Spec (.of k)))

/-- **A rational action from a point of the generic fibre.** Let `π : V ⟶ X` be a dominant
morphism from an open of an integral group scheme `G` over an algebraically closed field to a
separated integral `k`-scheme of finite type, and let `φ : Spec K(G × X) ⟶ X` be a `k`-point of
`X` over the function field of `G × X`. If, at some point `θ` of `G × V` with `μ θ ∈ V` and
`(id × π) θ` the generic point of `G × X`, the two maps `Spec 𝒪_θ ⟶ X` given by `π ∘ μ` and by `φ`
after `id × π` agree, then `φ` spreads out to a morphism `F` on a dense open `D` of `G × X` with
`F (a, π b) = π (a b)` on a dense open `U` of the canonical domain. -/
theorem exists_localRationalAction_of_functionFieldAction [IsAlgClosed k] [IsIntegral G.left]
    [IsIntegral X.left] [LocallyOfFiniteType X.hom]
    (V : G.left.Opens) (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ G.hom)
    (φ : Spec (G ⊗ X).left.functionField ⟶ X.left)
    (hφ : φ ≫ X.hom = (G ⊗ X).left.fromSpecStalk _ ≫ (G ⊗ X).hom)
    (θ : (G ⊗ G).left) (hθE : θ ∈ EV G V) (hθμ : θ ∈ μ[G].left ⁻¹ᵁ V)
    (hθgen : onePi G X V π hπ ⟨θ, hθE⟩ = genericPoint (G ⊗ X).left)
    (σ : Spec ((G ⊗ G).left.presheaf.stalk θ) ⟶ Spec (G ⊗ X).left.functionField)
    (hσ : (EV G V).fromSpecStalkOfMem θ hθE ≫ onePi G X V π hπ =
      σ ≫ (G ⊗ X).left.fromSpecStalk _)
    (hLI : σ ≫ φ = (EV G V ⊓ μ[G].left ⁻¹ᵁ V).fromSpecStalkOfMem θ ⟨hθE, hθμ⟩ ≫
      IsOpenImmersion.lift V.ι ((EV G V ⊓ μ[G].left ⁻¹ᵁ V).ι ≫ μ[G].left)
        (range_ι_comp_subset _ inf_le_right) ≫ π) :
    ∃ (D : (G ⊗ X).left.Opens) (F : D.toScheme ⟶ X.left)
      (_ : F ≫ X.hom = D.ι ≫ (G ⊗ X).hom) (U : (G ⊗ G).left.Opens)
      (hU : U ≤ canonicalDomain G X V π hπ D), Dense (U : Set (G ⊗ G).left) ∧
      (G ⊗ G).left.homOfLE hU ≫ IsOpenImmersion.lift D.ι _
          (canonicalDomain_range G X V π hπ D) ≫ F =
        (G ⊗ G).left.homOfLE hU ≫ IsOpenImmersion.lift V.ι
          ((canonicalDomain G X V π hπ D).ι ≫ μ[G].left)
          (range_ι_comp_subset _ (canonicalDomain_le_mu G X V π hπ D)) ≫ π := by
  let F' := Scheme.PartialMap.ofFromSpecStalk (x := genericPoint (G ⊗ X).left)
    (G ⊗ X).hom X.hom φ hφ
  have hF : F'.hom ≫ X.hom = F'.domain.ι ≫ (G ⊗ X).hom :=
    Scheme.PartialMap.ofFromSpecStalk_comp _ _ _ _
  have hgen : genericPoint (G ⊗ X).left ∈ F'.domain :=
    Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _
  have hφF : F'.domain.fromSpecStalkOfMem _ hgen ≫ F'.hom = φ :=
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk _ _ _ _
  set D := F'.domain
  set F := F'.hom
  set D'' := canonicalDomain G X V π hπ D
  have hθD : θ ∈ D'' := ⟨⟨⟨θ, hθE⟩, show onePi G X V π hπ ⟨θ, hθE⟩ ∈ D by
    rwa [hθgen], rfl⟩, hθμ⟩
  have hdense : Dense (D'' : Set (G ⊗ G).left) := D''.2.dense ⟨θ, hθD⟩
  let L : D''.toScheme ⟶ X.left :=
    IsOpenImmersion.lift D.ι _ (canonicalDomain_range G X V π hπ D) ≫ F
  let R : D''.toScheme ⟶ X.left :=
    IsOpenImmersion.lift V.ι (D''.ι ≫ μ[G].left)
      (range_ι_comp_subset _ (canonicalDomain_le_mu G X V π hπ D)) ≫ π
  let Lpm : (G ⊗ G).left.PartialMap X.left := ⟨D'', hdense, L⟩
  let Rpm : (G ⊗ G).left.PartialMap X.left := ⟨D'', hdense, R⟩
  have k1 : D''.fromSpecStalkOfMem θ hθD ≫
      IsOpenImmersion.lift D.ι _ (canonicalDomain_range G X V π hπ D) =
      σ ≫ D.fromSpecStalkOfMem _ hgen := by
    rw [← cancel_mono D.ι, Category.assoc, IsOpenImmersion.lift_fac, ← Category.assoc,
      fromSpecStalkOfMem_homOfLE, hσ, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι]
  have k2 : D''.fromSpecStalkOfMem θ hθD ≫ IsOpenImmersion.lift V.ι (D''.ι ≫ μ[G].left)
      (range_ι_comp_subset _ (canonicalDomain_le_mu G X V π hπ D)) =
      (EV G V ⊓ μ[G].left ⁻¹ᵁ V).fromSpecStalkOfMem θ ⟨hθE, hθμ⟩ ≫
        IsOpenImmersion.lift V.ι ((EV G V ⊓ μ[G].left ⁻¹ᵁ V).ι ≫ μ[G].left)
          (range_ι_comp_subset _ inf_le_right) := by
    rw [← cancel_mono V.ι, Category.assoc, IsOpenImmersion.lift_fac, Category.assoc,
      IsOpenImmersion.lift_fac, Scheme.Opens.fromSpecStalkOfMem_ι_assoc]
    exact (Scheme.Opens.fromSpecStalkOfMem_ι_assoc _ _ _ _).symm
  have key : Lpm.fromSpecStalkOfMem hθD = Rpm.fromSpecStalkOfMem hθD := by
    show D''.fromSpecStalkOfMem θ hθD ≫ L = D''.fromSpecStalkOfMem θ hθD ≫ R
    rw [← Category.assoc, k1, Category.assoc, hφF, hLI, ← Category.assoc, ← k2,
      Category.assoc]
  obtain ⟨W, hW, hWl, hWr, e⟩ :=
    Scheme.PartialMap.equiv_of_fromSpecStalkOfMem_eq Lpm Rpm hθD hθD key
  exact ⟨D, F, hF, W, hWl, hW, e⟩

/-- **Flatness from a point of the generic fibre.** In the situation of
`exists_localRationalAction_of_functionFieldAction`, `π` is flat on a nonempty open of `V`. -/
theorem exists_open_flatAt_of_functionFieldAction [IsAlgClosed k] [IsIntegral G.left]
    [IsIntegral X.left] [IsSeparated X.hom] [LocallyOfFiniteType X.hom]
    (V : G.left.Opens) (π : V.toScheme ⟶ X.left) (hπ : π ≫ X.hom = V.ι ≫ G.hom)
    [IsDominant π] (φ : Spec (G ⊗ X).left.functionField ⟶ X.left)
    (hφ : φ ≫ X.hom = (G ⊗ X).left.fromSpecStalk _ ≫ (G ⊗ X).hom)
    (θ : (G ⊗ G).left) (hθE : θ ∈ EV G V) (hθμ : θ ∈ μ[G].left ⁻¹ᵁ V)
    (hθgen : onePi G X V π hπ ⟨θ, hθE⟩ = genericPoint (G ⊗ X).left)
    (σ : Spec ((G ⊗ G).left.presheaf.stalk θ) ⟶ Spec (G ⊗ X).left.functionField)
    (hσ : (EV G V).fromSpecStalkOfMem θ hθE ≫ onePi G X V π hπ =
      σ ≫ (G ⊗ X).left.fromSpecStalk _)
    (hLI : σ ≫ φ = (EV G V ⊓ μ[G].left ⁻¹ᵁ V).fromSpecStalkOfMem θ ⟨hθE, hθμ⟩ ≫
      IsOpenImmersion.lift V.ι ((EV G V ⊓ μ[G].left ⁻¹ᵁ V).ι ≫ μ[G].left)
        (range_ι_comp_subset _ inf_le_right) ≫ π) :
    ∃ V' : G.left.Opens, ∃ hV' : V' ≤ V, (V' : Set G.left).Nonempty ∧
      ∀ v (hv : v ∈ V'), FlatAt π ⟨v, hV' hv⟩ := by
  obtain ⟨D, F, hF, W, hWl, hW, e⟩ := exists_localRationalAction_of_functionFieldAction G X V π
    hπ φ hφ θ hθE hθμ hθgen σ hσ hLI
  exact exists_open_flatAt_of_localRationalAction G X V π hπ D F hF W hWl hW.nonempty e

end Model

end AlgebraicGeometry.GenericQuotientFlat
