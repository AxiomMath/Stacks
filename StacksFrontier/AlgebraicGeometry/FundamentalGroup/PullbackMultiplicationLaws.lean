module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicAlgebraDataAssembly
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerHoms
public import StacksFrontier.AlgebraicGeometry.ExternalTensorPullback.ComparisonSections
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeTFAE
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.TowerPushforwardPullback
public import StacksFrontier.AlgebraicGeometry.ChartTransNonNested.PushforwardCocycle
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FormalCoverNeighbourhoodLift

/-!
# Multiplications on pullbacks of modules, and their restriction

Let `g : Y ⟶ V` be a morphism of schemes and `G` an `𝒪_V`-module. A morphism
`μ : g^*(G ⊗ G) ⟶ g^*G` is read as a multiplication on `g^*G` through the comparison
`g^*(G ⊗ G) ≅ g^*G ⊗ g^*G` of [Stacks, Tag 01CD]. The algebra laws of such a multiplication can
be written in two ways: with tensor products of morphisms between pullbacks and the pullbacks of
the symmetry, associator and left unitor of `G`, or as the laws of the multiplication
`g^*G ⊗ g^*G ⟶ g^*G` itself; the two readings are equivalent. The first reading has the
advantage of being compatible with restriction along a factorization `j ≫ g = g'`
(`Stacks.Algebraization.pullbackHomMap`), so that a law which holds after restriction to every
term of a tower of thickenings, and hence after restriction to a smaller open by condition (4) of
[Stacks, Tag 0EK2], holds for the restricted multiplication.

A multiplication transported from an algebra sheaf along an isomorphism `g^*G ≅ M` satisfies all
the laws.

## Main definitions

* `Stacks.Algebraization.pullbackTensorHom` — the tensor product of two morphisms between
  pullbacks.
* `Stacks.Algebraization.moduleAlgebraDataOfLaws` — the algebra data of a commutative,
  associative and unital multiplication out of the sheafified tensor square.

## Main results

* `Stacks.Algebraization.pullbackHomMap_pullbackTensorHom` — restriction commutes with tensor
  products of morphisms between pullbacks.
* `Stacks.Algebraization.pullbackTensorHom_assoc_iff`, `pullback_tensorSheafSwap_iff`,
  `pullback_leftUnitor_inv_comp` — the two readings of the algebra laws.
* `Stacks.Algebraization.pullbackTensorHom_assoc_of_iso`, `pullback_tensorSheafSwap_of_iso`,
  `pullback_leftUnitor_inv_of_iso` — the laws of a transported multiplication.
* `Stacks.Algebraization.pullbackObjFactorIso_pullbackUnitIso` — the identifications
  `g^* 𝒪 ≅ 𝒪` are compatible with composition.
* `Stacks.Algebraization.isFiniteLocallyFree_unit`, `isFiniteLocallyFree_tensorObj` — the
  structure sheaf and tensor products of finite locally free modules are finite locally free.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0EK2](https://stacks.math.columbia.edu/tag/0EK2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open Stacks.Tag01VSPullbackTensor (schemePullbackTensorIso)

universe u

namespace Stacks.Algebraization

attribute [local instance] AlgebraicGeometry.monoidalOfScheme


/-! ### Algebra sheaves, in monoidal notation -/

/-- A morphism of algebra sheaves commutes with the multiplications, in monoidal notation. -/
public theorem multiplication_comp_underlyingModuleMap_tensorHom {X : Scheme.{u}}
    {A B : Stacks.RelativeSpec.AlgebraSheaf X} (ψ : A ⟶ B) :
    Stacks.RelativeSpec.AlgebraSheaf.multiplication A ≫
        Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap ψ =
      (Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap ψ ⊗ₘ
          Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap ψ) ≫
        Stacks.RelativeSpec.AlgebraSheaf.multiplication B :=
  Stacks.PullbackTensorCoherence.tensor_hom_ext fun U x y =>
    ((congrArg (fun t => ((Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap ψ).val.app U) t)
        (multiplication_tmul' A U x y)).trans
      (Stacks.RelativeSpec.AlgebraSheaf.underlyingModuleMap_mulSection ψ U x y)).trans
    ((multiplication_tmul' B U _ _).symm.trans
      (congrArg (fun t => ((Stacks.RelativeSpec.AlgebraSheaf.multiplication B).val.app U) t)
        (Stacks.PullbackTensorCoherence.tensorHom_tmul _ _ U x y).symm))

/-! ### Restriction of morphisms between pullbacks -/

section PullbackHomMap

variable {Z : Scheme.{u}} {A B : Scheme.{u}} {a : A ⟶ Z} {b : B ⟶ Z} (g : A ⟶ B) (hg : g ≫ b = a)

/-- Restriction of morphisms between pullbacks commutes with composition. -/
public theorem pullbackHomMap_comp (E F G : Z.Modules)
    (φ : (Scheme.Modules.pullback b).obj E ⟶ (Scheme.Modules.pullback b).obj F)
    (ψ : (Scheme.Modules.pullback b).obj F ⟶ (Scheme.Modules.pullback b).obj G) :
    pullbackHomMap E G g hg (φ ≫ ψ) = pullbackHomMap E F g hg φ ≫ pullbackHomMap F G g hg ψ := by
  simp [pullbackHomMap]

/-- Restricting the pullback of a morphism gives the pullback of the morphism. -/
public theorem pullbackHomMap_pullback_map {E F : Z.Modules} (f : E ⟶ F) :
    pullbackHomMap E F g hg ((Scheme.Modules.pullback b).map f) =
      (Scheme.Modules.pullback a).map f := by
  have h := (pullbackFactorIso b g a hg).hom.naturality f
  simp only [Functor.comp_map] at h
  simp only [pullbackHomMap, pullbackObjFactorIso, Iso.app_hom, Iso.app_inv]
  rw [h, Iso.inv_hom_id_app_assoc]

end PullbackHomMap



/-! ### Monoidal algebra -/

section Monoidal

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- Associativity laws transported along isomorphisms, in an abstract monoidal category. -/
private theorem assoc_transport {X₂ X₃ X₃' N : C} (t : X₂ ≅ N ⊗ N) (s : X₃ ≅ X₂ ⊗ N)
    (s' : X₃' ≅ N ⊗ X₂) (A : X₃ ⟶ X₃') (μ : X₂ ⟶ N)
    (hA : A ≫ s'.hom ≫ (N ◁ t.hom) = s.hom ≫ (t.hom ▷ N) ≫ (α_ N N N).hom) :
    (s.hom ≫ (μ ⊗ₘ 𝟙 N) ≫ t.inv ≫ μ = A ≫ s'.hom ≫ (𝟙 N ⊗ₘ μ) ≫ t.inv ≫ μ) ↔
      (((t.inv ≫ μ) ▷ N) ≫ t.inv ≫ μ = (α_ N N N).hom ≫ (N ◁ (t.inv ≫ μ)) ≫ t.inv ≫ μ) := by
  have e₁ : (μ ⊗ₘ 𝟙 N) = (t.hom ▷ N) ≫ ((t.inv ≫ μ) ▷ N) := by
    rw [← comp_whiskerRight, Iso.hom_inv_id_assoc, tensorHom_id]
  have e₂ : (𝟙 N ⊗ₘ μ) = (N ◁ t.hom) ≫ (N ◁ (t.inv ≫ μ)) := by
    rw [← whiskerLeft_comp, Iso.hom_inv_id_assoc, id_tensorHom]
  have e₃ : A ≫ s'.hom ≫ (𝟙 N ⊗ₘ μ) ≫ t.inv ≫ μ =
      (s.hom ≫ (t.hom ▷ N)) ≫ (α_ N N N).hom ≫ (N ◁ (t.inv ≫ μ)) ≫ t.inv ≫ μ := by
    rw [e₂]
    simp only [Category.assoc]
    rw [reassoc_of% hA]
  rw [e₃, e₁]
  simp only [Category.assoc]
  constructor
  · intro h
    have := (cancel_epi (s.hom ≫ (t.hom ▷ N))).1 (by simpa only [Category.assoc] using h)
    exact this
  · intro h
    rw [h]

omit [MonoidalCategory C] in
/-- Commutativity laws transported along an isomorphism, in an abstract category. -/
private theorem comm_transport {X₂ T N : C} (t : X₂ ≅ T) (S : X₂ ⟶ X₂) (s : T ⟶ T)
    (μ : X₂ ⟶ N) (hS : S ≫ t.hom = t.hom ≫ s) :
    (S ≫ μ = μ) ↔ (s ≫ t.inv ≫ μ = t.inv ≫ μ) := by
  constructor
  · intro h
    rw [← cancel_epi t.hom, ← reassoc_of% hS]
    simp [h]
  · intro h
    calc S ≫ μ = S ≫ t.hom ≫ t.inv ≫ μ := by simp
      _ = t.hom ≫ s ≫ t.inv ≫ μ := by rw [reassoc_of% hS]
      _ = μ := by rw [h]; simp

/-- Left unit laws transported along isomorphisms, in an abstract monoidal category. -/
private theorem unit_transport {X₁ X₂ U N : C} (t : X₂ ≅ N ⊗ N) (s : X₁ ≅ U ⊗ N)
    (p : U ≅ 𝟙_ C) (Λ : X₁ ≅ N) (hΛ : Λ.hom = s.hom ≫ (p.hom ▷ N) ≫ (λ_ N).hom)
    (η : U ⟶ N) (μ : X₂ ⟶ N) :
    Λ.inv ≫ (s.hom ≫ (η ⊗ₘ 𝟙 N) ≫ t.inv) ≫ μ =
      (λ_ N).inv ≫ ((p.inv ≫ η) ▷ N) ≫ t.inv ≫ μ := by
  have hinv : Λ.inv = (λ_ N).inv ≫ (p.inv ▷ N) ≫ s.inv := by
    rw [← cancel_mono Λ.hom, Iso.inv_hom_id, hΛ]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp,
      Iso.inv_hom_id]
  rw [hinv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [tensorHom_id, ← comp_whiskerRight_assoc]

/-- A multiplication conjugated by an isomorphism stays associative. -/
private theorem conj_assoc {N M : C} (φ : N ≅ M) (mul : M ⊗ M ⟶ M)
    (h : (mul ▷ M) ≫ mul = (α_ M M M).hom ≫ (M ◁ mul) ≫ mul) :
    (((φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv) ▷ N) ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv =
      (α_ N N N).hom ≫ (N ◁ ((φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv)) ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫
        φ.inv := by
  have l : (((φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv) ▷ N) ≫ (φ.hom ⊗ₘ φ.hom) =
      ((φ.hom ⊗ₘ φ.hom) ⊗ₘ φ.hom) ≫ (mul ▷ M) := by
    simp only [← tensorHom_id, tensorHom_comp_tensorHom]
    congr 1 <;> simp
  have r : (N ◁ ((φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv)) ≫ (φ.hom ⊗ₘ φ.hom) =
      (φ.hom ⊗ₘ (φ.hom ⊗ₘ φ.hom)) ≫ (M ◁ mul) := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom]
    congr 1 <;> simp
  rw [reassoc_of% l, reassoc_of% r, reassoc_of% h, associator_naturality_assoc]

/-- A multiplication conjugated by an isomorphism keeps its left unit. -/
private theorem conj_one {N M : C} (φ : N ≅ M) (mul : M ⊗ M ⟶ M) (u : 𝟙_ C ⟶ M)
    (h : (u ▷ M) ≫ mul = (λ_ M).hom) :
    (λ_ N).inv ≫ ((u ≫ φ.inv) ▷ N) ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv = 𝟙 N := by
  have l : ((u ≫ φ.inv) ▷ N) ≫ (φ.hom ⊗ₘ φ.hom) = (𝟙_ C ◁ φ.hom) ≫ (u ▷ M) := by
    simp only [← tensorHom_id, ← id_tensorHom, tensorHom_comp_tensorHom]
    congr 1 <;> simp
  rw [reassoc_of% l, reassoc_of% h, leftUnitor_naturality_assoc]
  simp

/-- `assoc_transport` and `conj_assoc` combined. -/
private theorem assoc_of_conj {X₂ X₃ X₃' N M : C} (t : X₂ ≅ N ⊗ N) (s : X₃ ≅ X₂ ⊗ N)
    (s' : X₃' ≅ N ⊗ X₂) (A : X₃ ⟶ X₃')
    (hA : A ≫ s'.hom ≫ (N ◁ t.hom) = s.hom ≫ (t.hom ▷ N) ≫ (α_ N N N).hom)
    (φ : N ≅ M) (mul : M ⊗ M ⟶ M)
    (h : (mul ▷ M) ≫ mul = (α_ M M M).hom ≫ (M ◁ mul) ≫ mul) :
    (s.hom ≫ ((t.hom ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv) ⊗ₘ 𝟙 N) ≫ t.inv) ≫
        t.hom ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv =
      A ≫ (s'.hom ≫ (𝟙 N ⊗ₘ (t.hom ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv)) ≫ t.inv) ≫
        t.hom ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv := by
  simp only [Category.assoc]
  refine (assoc_transport t s s' A _ hA).2 ?_
  simpa only [Iso.inv_hom_id_assoc] using conj_assoc φ mul h

omit [MonoidalCategory C] in
/-- The commutativity of a conjugated multiplication, as pure category algebra. -/
private theorem comm_of_conj {X₂ T T' M' N : C} (t : X₂ ≅ T) (S : X₂ ⟶ X₂) (s : T ⟶ T)
    (hS : S ≫ t.hom = t.hom ≫ s) (c : T ⟶ T') (s' : T' ⟶ T') (m : T' ⟶ M') (d : M' ⟶ N)
    (hc : s ≫ c = c ≫ s') (hm : s' ≫ m = m) :
    S ≫ t.hom ≫ c ≫ m ≫ d = t.hom ≫ c ≫ m ≫ d := by
  rw [reassoc_of% hS, reassoc_of% hc, reassoc_of% hm]

/-- `unit_transport` and `conj_one` combined. -/
private theorem unit_of_conj {X₁ X₂ U N M : C} (t : X₂ ≅ N ⊗ N) (s : X₁ ≅ U ⊗ N)
    (p : U ≅ 𝟙_ C) (Λ : X₁ ≅ N) (hΛ : Λ.hom = s.hom ≫ (p.hom ▷ N) ≫ (λ_ N).hom)
    (φ : N ≅ M) (mul : M ⊗ M ⟶ M) (u : 𝟙_ C ⟶ M) (h : (u ▷ M) ≫ mul = (λ_ M).hom) :
    Λ.inv ≫ (s.hom ≫ ((p.hom ≫ u ≫ φ.inv) ⊗ₘ 𝟙 N) ≫ t.inv) ≫
        t.hom ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv = 𝟙 N := by
  rw [unit_transport t s p Λ hΛ]
  simpa only [Iso.inv_hom_id_assoc] using conj_one φ mul u h

end Monoidal

/-! ### Tensor products of morphisms between pullbacks -/

section Tensor

/-- An abstract form of the compatibility of tensor products of morphisms with restriction. -/
private theorem tensor_restrict_chain {C D : Type*} [Category C] [MonoidalCategory C] [Category D]
    [MonoidalCategory D] (F : D ⥤ C) {X X' A A' B B' : D} {X₁ X₁' A₁ A₁' B₁ B₁' : C}
    (t₁ : X ≅ A ⊗ B) (t₂ : X' ≅ A' ⊗ B') (a : A ⟶ A') (b : B ⟶ B')
    (τ₁ : F.obj (A ⊗ B) ≅ F.obj A ⊗ F.obj B) (τ₂ : F.obj (A' ⊗ B') ≅ F.obj A' ⊗ F.obj B')
    (f₁ : F.obj X ≅ X₁) (f₂ : F.obj X' ≅ X₁') (fA : F.obj A ≅ A₁) (fB : F.obj B ≅ B₁)
    (fA' : F.obj A' ≅ A₁') (fB' : F.obj B' ≅ B₁') (t₁' : X₁ ≅ A₁ ⊗ B₁) (t₂' : X₁' ≅ A₁' ⊗ B₁')
    (K₁ : (F.map t₁.hom ≫ τ₁.hom) ≫ (fA.hom ⊗ₘ fB.hom) = f₁.hom ≫ t₁'.hom)
    (K₂ : (F.map t₂.hom ≫ τ₂.hom) ≫ (fA'.hom ⊗ₘ fB'.hom) = f₂.hom ≫ t₂'.hom)
    (K₃ : F.map (a ⊗ₘ b) ≫ τ₂.hom = τ₁.hom ≫ (F.map a ⊗ₘ F.map b)) :
    f₁.inv ≫ F.map (t₁.hom ≫ (a ⊗ₘ b) ≫ t₂.inv) ≫ f₂.hom =
      t₁'.hom ≫ ((fA.inv ≫ F.map a ≫ fA'.hom) ⊗ₘ (fB.inv ≫ F.map b ≫ fB'.hom)) ≫ t₂'.inv := by
  have K₂' : F.map t₂.inv ≫ f₂.hom = τ₂.hom ≫ (fA'.hom ⊗ₘ fB'.hom) ≫ t₂'.inv := by
    rw [← cancel_epi (F.map t₂.hom), ← F.map_comp_assoc, Iso.hom_inv_id, F.map_id,
      Category.id_comp, ← Category.assoc, ← Category.assoc, K₂, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  rw [Iso.inv_comp_eq, ← reassoc_of% K₁]
  simp only [Functor.map_comp, Category.assoc, K₂']
  rw [reassoc_of% K₃]
  congr 2
  simp only [← Category.assoc, ← tensorHom_comp_tensorHom]
  simp

variable {V Y Y' : Scheme.{u}}

/-- The comparison of [Stacks, Tag 01CD] against pseudofunctoriality, with the tensor product of
the two contractions written as a monoidal product. -/
public theorem schemePullbackTensorIso_pullbackObjFactorIso (j : Y' ⟶ Y) (g : Y ⟶ V)
    {g' : Y' ⟶ V} (hj : j ≫ g = g') (P Q : V.Modules) :
    ((Scheme.Modules.pullback j).map (schemePullbackTensorIso g P Q).hom ≫
        (schemePullbackTensorIso j ((Scheme.Modules.pullback g).obj P)
          ((Scheme.Modules.pullback g).obj Q)).hom) ≫
      ((pullbackObjFactorIso P j hj).hom ⊗ₘ (pullbackObjFactorIso Q j hj).hom) =
    (pullbackObjFactorIso (P ⊗ Q) j hj).hom ≫ (schemePullbackTensorIso g' P Q).hom :=
  (congrArg (fun z => ((Scheme.Modules.pullback j).map (schemePullbackTensorIso g P Q).hom ≫
        (schemePullbackTensorIso j ((Scheme.Modules.pullback g).obj P)
          ((Scheme.Modules.pullback g).obj Q)).hom) ≫ z)
      (tensorSheafMap_eq_tensorHom _ _)).symm.trans
    (Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso_pullbackCompCongr j g hj P Q)

/-- The comparison of [Stacks, Tag 01CD] is natural, in monoidal notation. -/
public theorem schemePullbackTensorIso_naturality (j : Y' ⟶ Y) {P P' Q Q' : Y.Modules}
    (a : P ⟶ P') (b : Q ⟶ Q') :
    (Scheme.Modules.pullback j).map (a ⊗ₘ b) ≫ (schemePullbackTensorIso j P' Q').hom =
      (schemePullbackTensorIso j P Q).hom ≫
        ((Scheme.Modules.pullback j).map a ⊗ₘ (Scheme.Modules.pullback j).map b) :=
  (congrArg (fun z => (Scheme.Modules.pullback j).map z ≫ (schemePullbackTensorIso j P' Q').hom)
      (tensorSheafMap_eq_tensorHom a b)).symm.trans
    ((Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso_tensorSheafMap_hom j a b).trans
      (congrArg (fun z => (schemePullbackTensorIso j P Q).hom ≫ z)
        (tensorSheafMap_eq_tensorHom _ _)))

/-- **The tensor product of two morphisms between pullbacks**, read through the comparison
`g^*(P ⊗ Q) ≅ g^*P ⊗ g^*Q` of [Stacks, Tag 01CD]. -/
public def pullbackTensorHom (g : Y ⟶ V) {P P' Q Q' : V.Modules}
    (a : (Scheme.Modules.pullback g).obj P ⟶ (Scheme.Modules.pullback g).obj P')
    (b : (Scheme.Modules.pullback g).obj Q ⟶ (Scheme.Modules.pullback g).obj Q') :
    (Scheme.Modules.pullback g).obj (P ⊗ Q) ⟶ (Scheme.Modules.pullback g).obj (P' ⊗ Q') :=
  (schemePullbackTensorIso g P Q).hom ≫ (a ⊗ₘ b) ≫ (schemePullbackTensorIso g P' Q').inv

/-- **Restriction commutes with tensor products of morphisms between pullbacks.** -/
public theorem pullbackHomMap_pullbackTensorHom (j : Y' ⟶ Y) (g : Y ⟶ V) {g' : Y' ⟶ V}
    (hj : j ≫ g = g') {P P' Q Q' : V.Modules}
    (a : (Scheme.Modules.pullback g).obj P ⟶ (Scheme.Modules.pullback g).obj P')
    (b : (Scheme.Modules.pullback g).obj Q ⟶ (Scheme.Modules.pullback g).obj Q') :
    pullbackHomMap (P ⊗ Q) (P' ⊗ Q') j hj (pullbackTensorHom g a b) =
      pullbackTensorHom g' (pullbackHomMap P P' j hj a) (pullbackHomMap Q Q' j hj b) :=
  tensor_restrict_chain (Scheme.Modules.pullback j) (schemePullbackTensorIso g P Q)
    (schemePullbackTensorIso g P' Q') a b
    (schemePullbackTensorIso j _ _) (schemePullbackTensorIso j _ _)
    (pullbackObjFactorIso (P ⊗ Q) j hj) (pullbackObjFactorIso (P' ⊗ Q') j hj)
    (pullbackObjFactorIso P j hj) (pullbackObjFactorIso Q j hj)
    (pullbackObjFactorIso P' j hj) (pullbackObjFactorIso Q' j hj)
    (schemePullbackTensorIso g' P Q) (schemePullbackTensorIso g' P' Q')
    (schemePullbackTensorIso_pullbackObjFactorIso j g hj P Q)
    (schemePullbackTensorIso_pullbackObjFactorIso j g hj P' Q')
    (schemePullbackTensorIso_naturality j a b)


section Laws

variable (g : Y ⟶ V) (G : V.Modules)
  (μ : (Scheme.Modules.pullback g).obj (G ⊗ G) ⟶ (Scheme.Modules.pullback g).obj G)

/-- **The associativity of a multiplication on a pullback, in two readings.** For
`μ : g^*(G ⊗ G) ⟶ g^*G`, the associativity law written with the tensor products of morphisms
between pullbacks and the pullback of the associator of `G` is the associativity law of the
multiplication `g^*G ⊗ g^*G ≅ g^*(G ⊗ G) ⟶ g^*G`. -/
public theorem pullbackTensorHom_assoc_iff :
    (pullbackTensorHom g μ (𝟙 _) ≫ μ =
        (Scheme.Modules.pullback g).map (α_ G G G).hom ≫ pullbackTensorHom g (𝟙 _) μ ≫ μ) ↔
      ((((schemePullbackTensorIso g G G).inv ≫ μ) ▷ (Scheme.Modules.pullback g).obj G) ≫
          (schemePullbackTensorIso g G G).inv ≫ μ =
        (α_ _ _ _).hom ≫ ((Scheme.Modules.pullback g).obj G ◁
          ((schemePullbackTensorIso g G G).inv ≫ μ)) ≫
          (schemePullbackTensorIso g G G).inv ≫ μ) := by
  have := assoc_transport (schemePullbackTensorIso g G G) (schemePullbackTensorIso g (G ⊗ G) G)
    (schemePullbackTensorIso g G (G ⊗ G)) ((Scheme.Modules.pullback g).map (α_ G G G).hom) μ
    (schemePullbackTensorIso_associator g G G G)
  simp only [pullbackTensorHom]
  exact this

/-- **The commutativity of a multiplication on a pullback, in two readings.** -/
public theorem pullback_tensorSheafSwap_iff :
    ((Scheme.Modules.pullback g).map
        (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap V.toRingedSpace G G).hom ≫ μ =
        μ) ↔
      ((Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap Y.toRingedSpace
          ((Scheme.Modules.pullback g).obj G) ((Scheme.Modules.pullback g).obj G)).hom ≫
          (schemePullbackTensorIso g G G).inv ≫ μ = (schemePullbackTensorIso g G G).inv ≫ μ) :=
  comm_transport (schemePullbackTensorIso g G G) _ _ μ
    (schemePullbackTensorIso_tensorSheafSwap g G G)

/-- **The left unit law of a multiplication on a pullback, in two readings.** -/
public theorem pullback_leftUnitor_inv_comp
    (η : (Scheme.Modules.pullback g).obj (𝟙_ V.Modules) ⟶ (Scheme.Modules.pullback g).obj G) :
    (Scheme.Modules.pullback g).map (λ_ G).inv ≫ pullbackTensorHom g η (𝟙 _) ≫ μ =
      (λ_ _).inv ≫ (((Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g).inv ≫ η) ▷
        (Scheme.Modules.pullback g).obj G) ≫ (schemePullbackTensorIso g G G).inv ≫ μ := by
  have := unit_transport (schemePullbackTensorIso g G G) (schemePullbackTensorIso g _ G)
    (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g)
    ((Scheme.Modules.pullback g).mapIso (λ_ G)) (schemePullbackTensorIso_leftUnitor g G) η μ
  exact this

end Laws


/-! ### Multiplications transported from an algebra -/

section Conjugate

variable (g : Y ⟶ V) (G : V.Modules) {M : Y.Modules} (φ : (Scheme.Modules.pullback g).obj G ≅ M)
  (mul : M ⊗ M ⟶ M)

/-- **A multiplication on a pullback transported from an associative one is associative.** -/
public theorem pullbackTensorHom_assoc_of_iso
    (h : (mul ▷ M) ≫ mul = (α_ M M M).hom ≫ (M ◁ mul) ≫ mul) :
    pullbackTensorHom g ((schemePullbackTensorIso g G G).hom ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv)
        (𝟙 _) ≫ (schemePullbackTensorIso g G G).hom ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv =
      (Scheme.Modules.pullback g).map (α_ G G G).hom ≫ pullbackTensorHom g (𝟙 _)
        ((schemePullbackTensorIso g G G).hom ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv) ≫
          (schemePullbackTensorIso g G G).hom ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv :=
  assoc_of_conj (schemePullbackTensorIso g G G) (schemePullbackTensorIso g (G ⊗ G) G)
    (schemePullbackTensorIso g G (G ⊗ G)) ((Scheme.Modules.pullback g).map (α_ G G G).hom)
    (schemePullbackTensorIso_associator g G G G) φ mul h

/-- **A multiplication on a pullback transported from a commutative one is commutative.** -/
public theorem pullback_tensorSheafSwap_of_iso
    (h : (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap Y.toRingedSpace M M).hom ≫
      mul = mul) :
    (Scheme.Modules.pullback g).map
        (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap V.toRingedSpace G G).hom ≫
        (schemePullbackTensorIso g G G).hom ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv =
      (schemePullbackTensorIso g G G).hom ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫ φ.inv := by
  have hn : (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap Y.toRingedSpace _ _).hom ≫
      (φ.hom ⊗ₘ φ.hom) = (φ.hom ⊗ₘ φ.hom) ≫
        (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap Y.toRingedSpace M M).hom :=
    (congrArg (fun z => (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap
        Y.toRingedSpace _ _).hom ≫ z) (tensorSheafMap_eq_tensorHom φ.hom φ.hom).symm).trans
      ((Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap_naturality
        Y.toRingedSpace φ.hom φ.hom).trans
      (congrArg (fun z => z ≫ (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap
        Y.toRingedSpace M M).hom) (tensorSheafMap_eq_tensorHom φ.hom φ.hom)))
  exact comm_of_conj (schemePullbackTensorIso g G G) _ _
    (schemePullbackTensorIso_tensorSheafSwap g G G) _ _ mul φ.inv hn h

/-- **A multiplication on a pullback transported from a unital one has the transported unit as
a left unit.** -/
public theorem pullback_leftUnitor_inv_of_iso (u : 𝟙_ Y.Modules ⟶ M)
    (h : (u ▷ M) ≫ mul = (λ_ M).hom) :
    (Scheme.Modules.pullback g).map (λ_ G).inv ≫
        pullbackTensorHom g ((Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g).hom ≫
          u ≫ φ.inv) (𝟙 _) ≫ (schemePullbackTensorIso g G G).hom ≫ (φ.hom ⊗ₘ φ.hom) ≫ mul ≫
            φ.inv = 𝟙 _ :=
  unit_of_conj (schemePullbackTensorIso g G G) (schemePullbackTensorIso g _ G)
    (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g)
    ((Scheme.Modules.pullback g).mapIso (λ_ G)) (schemePullbackTensorIso_leftUnitor g G) φ mul u h

end Conjugate

end Tensor

/-! ### Finite local freeness of the structure sheaf and of tensor products -/

section FiniteLocallyFree

/-- **The structure sheaf is finite locally free.** -/
public theorem isFiniteLocallyFree_unit (X : Scheme.{u}) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (𝟙_ X.Modules) := by
  have h := (Stacks.Morphisms.isFiniteLocallyFree_iff (𝟙 X)).mp
    ((Stacks.Morphisms.isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation
      (𝟙 X)).mpr ⟨inferInstance, inferInstance, inferInstance⟩)
  have := h.2
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso
    ((Scheme.Modules.pushforwardId X).app (SheafOfModules.unit X.ringCatSheaf))

/-- **The tensor product of two finite locally free modules is finite locally free.** -/
public theorem isFiniteLocallyFree_tensorObj {X : Scheme.{u}} (F G : X.Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G) := by
  have key : ∀ H : X.Modules, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} H →
      _root_.SheafOfModules.IsLocallyFree.{u, u, u} (R := structureSheafRing X.toRingedSpace) H ∧
        _root_.SheafOfModules.IsFiniteType.{u, u, u} (R := structureSheafRing X.toRingedSpace) H :=
    fun H hH => by
      obtain ⟨q, _, hq⟩ := hH.exists_isFiniteLocallyFreeData
      exact ⟨q.isLocallyFree, { exists_localGeneratorsData := ⟨q, hq⟩ }⟩
  obtain ⟨hFl, hFt⟩ := key F hF
  obtain ⟨hGl, hGt⟩ := key G hG
  let T : X.Modules := ((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj G
  have hTl : _root_.SheafOfModules.IsLocallyFree.{u, u, u} T :=
    @AlgebraicGeometry.SheafOfModules.tensorSheaf_isLocallyFree X.toRingedSpace F G hFl hGl
  have hTt : _root_.SheafOfModules.IsFiniteType.{u, u, u} T :=
    @AlgebraicGeometry.SheafOfModules.tensorSheaf_isFiniteType X.toRingedSpace F G hFt hGt
  have : T.IsQuasicoherent := by
    obtain ⟨q, hq⟩ := hTl.exists_isLocallyFreeData
    exact q.quasiCoherentData.isQuasicoherent
  have key := (Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae T).out 3 4
  exact key.mp ⟨hTl, hTt⟩

end FiniteLocallyFree


/-! ### Laws of multiplications on pullbacks, under restriction -/

section Restriction

variable {V Y Y' : Scheme.{u}} (j : Y' ⟶ Y) (g : Y ⟶ V) {g' : Y' ⟶ V} (hj : j ≫ g = g')
  (G : V.Modules)

/-- Restriction of the left side of the associativity law. -/
public theorem pullbackHomMap_assoc_left
    (μ : (Scheme.Modules.pullback g).obj (G ⊗ G) ⟶ (Scheme.Modules.pullback g).obj G) :
    pullbackHomMap ((G ⊗ G) ⊗ G) G j hj (pullbackTensorHom g μ (𝟙 _) ≫ μ) =
      pullbackTensorHom g' (pullbackHomMap (G ⊗ G) G j hj μ) (𝟙 _) ≫
        pullbackHomMap (G ⊗ G) G j hj μ := by
  rw [pullbackHomMap_comp, pullbackHomMap_pullbackTensorHom, pullbackHomMap_id]

/-- Restriction of the right side of the associativity law. -/
public theorem pullbackHomMap_assoc_right
    (μ : (Scheme.Modules.pullback g).obj (G ⊗ G) ⟶ (Scheme.Modules.pullback g).obj G) :
    pullbackHomMap ((G ⊗ G) ⊗ G) G j hj
        ((Scheme.Modules.pullback g).map (α_ G G G).hom ≫ pullbackTensorHom g (𝟙 _) μ ≫ μ) =
      (Scheme.Modules.pullback g').map (α_ G G G).hom ≫
        pullbackTensorHom g' (𝟙 _) (pullbackHomMap (G ⊗ G) G j hj μ) ≫
          pullbackHomMap (G ⊗ G) G j hj μ := by
  rw [pullbackHomMap_comp, pullbackHomMap_comp, pullbackHomMap_pullback_map,
    pullbackHomMap_pullbackTensorHom, pullbackHomMap_id]

/-- Restriction of the commutativity law. -/
public theorem pullbackHomMap_swap
    (μ : (Scheme.Modules.pullback g).obj (G ⊗ G) ⟶ (Scheme.Modules.pullback g).obj G) :
    pullbackHomMap (G ⊗ G) G j hj ((Scheme.Modules.pullback g).map
        (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap V.toRingedSpace G G).hom ≫ μ) =
      (Scheme.Modules.pullback g').map
        (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap V.toRingedSpace G G).hom ≫
        pullbackHomMap (G ⊗ G) G j hj μ :=
  (pullbackHomMap_comp j hj _ _ _ _ _).trans (congrArg (· ≫ _) (pullbackHomMap_pullback_map j hj _))

/-- Restriction of the left unit law. -/
public theorem pullbackHomMap_unit_left
    (μ : (Scheme.Modules.pullback g).obj (G ⊗ G) ⟶ (Scheme.Modules.pullback g).obj G)
    (η : (Scheme.Modules.pullback g).obj (𝟙_ V.Modules) ⟶ (Scheme.Modules.pullback g).obj G) :
    pullbackHomMap G G j hj
        ((Scheme.Modules.pullback g).map (λ_ G).inv ≫ pullbackTensorHom g η (𝟙 _) ≫ μ) =
      (Scheme.Modules.pullback g').map (λ_ G).inv ≫
        pullbackTensorHom g' (pullbackHomMap (𝟙_ V.Modules) G j hj η) (𝟙 _) ≫
          pullbackHomMap (G ⊗ G) G j hj μ := by
  rw [pullbackHomMap_comp, pullbackHomMap_comp, pullbackHomMap_pullback_map,
    pullbackHomMap_pullbackTensorHom, pullbackHomMap_id]

end Restriction

namespace InfinitesimalTower

variable {S : Scheme.{u}} (T : InfinitesimalTower S)

/-- The factorization through a smaller open is compatible with the inclusion. -/
public theorem homToOpen_homOfLE {W W' : S.Opens} (hW : T.support ⊆ W) (hW' : T.support ⊆ W')
    (h : W' ≤ W) (n : ℕ) : T.homToOpen hW' n ≫ S.homOfLE h = T.homToOpen hW n :=
  (cancel_mono W.ι).1 (by rw [Category.assoc, Scheme.homOfLE_ι, T.homToOpen_ι, T.homToOpen_ι])

/-- The morphisms on the terms of the tower induced by a restriction are the ones induced by the
original morphism. -/
public theorem homAt_homRestrict (E F : S.Modules) {W W' : S.Opens} (hW : T.support ⊆ W)
    (hW' : T.support ⊆ W') (h : W' ≤ W) (n : ℕ)
    (φ : (Scheme.Modules.pullback W.ι).obj E ⟶ (Scheme.Modules.pullback W.ι).obj F) :
    T.homAt E F hW' n (homRestrict E F h φ) = T.homAt E F hW n φ :=
  pullbackHomMap_pullbackHomMap E F (S.homOfLE h) (S.homOfLE_ι h) (T.homToOpen hW' n)
    (T.homToOpen_ι hW' n) (T.homToOpen hW n) (T.homToOpen_homOfLE hW hW' h n) φ

end InfinitesimalTower

/-- Restriction to smaller and smaller opens is restriction to the smallest one. -/
public theorem homRestrict_homRestrict {S : Scheme.{u}} (E F : S.Modules) {W W' W'' : S.Opens}
    (h : W' ≤ W) (h' : W'' ≤ W')
    (φ : (Scheme.Modules.pullback W.ι).obj E ⟶ (Scheme.Modules.pullback W.ι).obj F) :
    homRestrict E F h' (homRestrict E F h φ) = homRestrict E F (h'.trans h) φ :=
  pullbackHomMap_pullbackHomMap E F (S.homOfLE h) (S.homOfLE_ι h) (S.homOfLE h')
    (S.homOfLE_ι h') (S.homOfLE (h'.trans h)) (by simp) φ

/-- **The identification `g^* 𝒪 ≅ 𝒪` is compatible with composition.** For `j ≫ g = g'`, the
identification for `g'` is the one for `g` pulled back along `j`, followed by the one for `j`. -/
public theorem pullbackObjFactorIso_pullbackUnitIso {V Y Y' : Scheme.{u}} (j : Y' ⟶ Y)
    (g : Y ⟶ V) {g' : Y' ⟶ V} (hj : j ≫ g = g') :
    (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g').hom =
      (pullbackObjFactorIso (Stacks.AlgebraicGeometry.AffineBaseChange.unitObj V) j hj).inv ≫
        (Scheme.Modules.pullback j).map
          (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g).hom ≫
        (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso j).hom := by
  have hPU : ∀ {Y₀ : Scheme.{u}} {V₀ : Scheme.{u}} (g₀ : Y₀ ⟶ V₀),
      pullbackHomEquivPushforward g₀ _ _
        (Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom g₀) =
      (Stacks.AlgebraicGeometry.AffineBaseChange.pullbackUnitIso g₀).hom := fun g₀ =>
    (Equiv.symm_apply_eq _).2
      (Stacks.AlgebraicGeometry.AffineBaseChange.homEquiv_pullbackUnitIso g₀).symm
  have key := pullbackHomEquivPushforward_comp g j g' hj
    (Stacks.AlgebraicGeometry.AffineBaseChange.unitObj V)
    (Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom j)
    (Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom g)
  rw [hPU, hPU] at key
  refine Eq.trans ?_ key
  rw [← hPU g']
  congr 1
  subst hj
  rw [Stacks.AlgebraicGeometry.PushforwardCocycle.pushforwardComp_hom_app_eq_id,
    pushforwardCongr_rfl_hom_app]
  apply SheafOfModules.hom_ext
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun r => ?_)
  rfl


attribute [local instance] AlgebraicGeometry.moduleOnSectionsAtSchemePresheaf in
/-- **The algebra data of a commutative, associative and unital multiplication** out of the
sheafified tensor square. -/
public def moduleAlgebraDataOfLaws {Y : Scheme.{u}} (E : Y.Modules)
    (μ : (E ⊗ E : Y.Modules) ⟶ E) (η : (𝟙_ Y.Modules) ⟶ E)
    (hcomm : (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap Y.toRingedSpace E E).hom ≫
      μ = μ)
    (hassoc : (μ ▷ E) ≫ μ = (α_ E E E).hom ≫ (E ◁ μ) ≫ μ)
    (hone : (λ_ E).inv ≫ (η ▷ E) ≫ μ = 𝟙 E) :
    Stacks.FundamentalGroup.ModuleAlgebraData E where
  unit := η
  mul := AlgebraicGeometry.mulPresheafOfHom E μ
  mul_comm := AlgebraicGeometry.mulPresheafOfHom_comm E μ hcomm
  mul_assoc := AlgebraicGeometry.mulPresheafOfHom_assoc E μ hassoc
  one_mul := AlgebraicGeometry.mulPresheafOfHom_one_mul E μ η hone

end Stacks.Algebraization
