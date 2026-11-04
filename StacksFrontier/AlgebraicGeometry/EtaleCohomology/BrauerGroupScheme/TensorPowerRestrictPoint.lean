module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Data.Fin.Tuple.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.EtalePointGlue
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.TensorPowerPullback

/-!
# Restricting a tensor of points of a pullback of a sheaf of algebras

Let `ρ : V ⟶ T` and `φ : T ⟶ S` be morphisms of schemes with composite `ψ`, and let `B` be a
sheaf of `𝒪_S`-algebras. A point of the pullback `φ^* B` is a morphism `𝒪_T ⟶ φ^* B` out of the
structure sheaf, and `AlgebraicGeometry.restrictPoint` restricts such a point along `ρ` to a
point of `ψ^* B`.

The proof of [Stacks, Tag 0A2L] has to compare, on the pairwise fibre products of a trivialising
étale covering, two expressions for one section of `B^{⊗ d}`, each of which is a sum of tensors of
points of a pullback of `B`. This file supplies the two compatibilities needed for that
comparison: restriction of points is additive, and — the main result — **restriction commutes
with the tensor of a finite family of points**, the tensor being formed *inside* the pullback,
through the unit and the tensorator of the monoidal functor `modulePullback`.

## Main definitions

* `Stacks.EtaleCohomology.BrauerScheme.pullbackNatTensorPowPoint`: the tensor of a finite family
  of points of `φ^* B`, as a point of `φ^*(B^{⊗ m})`.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.restrictPoint_sum`: **restriction of points is additive**,
  the pullback of sheaves of modules being an additive functor.
* `Stacks.EtaleCohomology.BrauerScheme.restrictPoint_pullbackNatTensorPowPoint`: **restriction
  commutes with the tensor of a finite family of points.**

## Implementation notes

Every step of the induction proving the main result is phrased as an abstract statement about a
monoidal natural transformation `τ : F' ⋙ F ⟶ G` between lax monoidal functors, and transported
to the scheme spelling by `exact`. This is the discipline recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.TensorPowerFreeMatrix` and of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.TensorPowerAlgebraPoints`: at the
scheme spelling the objects of `ModuleSheaf S` carry a monoidal structure which `rw` cannot
abstract over, and `Stacks.TensorPowers.natTensorPow B (m + 1)` is `natTensorPow B m ⊗ B` only
definitionally, so no lemma keyed on a tensor product fires against it. Accordingly
`eps_comp_map_tensor_comp_app` takes the two restricted factors as *variables* together with
equations identifying them, so that the induction hypothesis is consumed by `exact` and no
rewriting whatsoever happens in the category `ModuleSheaf S`.

`AlgebraicGeometry.restrictPoint` is defined with three comparison isomorphisms, and
`restrictPoint_eq` is the observation that at the reflexivity factorisation `ρ ≫ φ = ρ ≫ φ` only
two of them survive: `AlgebraicGeometry.Scheme.Modules.pullbackCongr rfl` is the identity, and the
other two are, definitionally, the unit `Functor.LaxMonoidal.ε (modulePullback ρ)` of the monoidal
functor of Tag 01CD and the composition law `modulePullbackComp ρ φ` of Tag 0097 — whose
monoidality `isMonoidal_modulePullbackComp` is the whole input to the main result.

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0097](https://stacks.math.columbia.edu/tag/0097)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MonoidalCategory

universe v₁ v₂ v₃ u₁ u₂ u₃ u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

/-! ### Two statements about an abstract monoidal natural transformation -/

section Abstract

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-- **A monoidal natural transformation out of a composite of lax monoidal functors carries the
unit of the composite to the unit of the target**, with the unit of the composite expanded by
`CategoryTheory.Functor.LaxMonoidal.comp_ε`. This is the unit axiom of
`CategoryTheory.NatTrans.IsMonoidal` in the shape in which the degree-zero case of
`Stacks.EtaleCohomology.BrauerScheme.restrictPoint_pullbackNatTensorPowPoint` needs it. -/
private theorem eps_comp_map_eps_comp_app (F' : C ⥤ D) (F : D ⥤ E) (G : C ⥤ E)
    [F'.LaxMonoidal] [F.LaxMonoidal] [G.LaxMonoidal] (τ : F' ⋙ F ⟶ G)
    [NatTrans.IsMonoidal τ] :
    Functor.LaxMonoidal.ε F ≫ F.map (Functor.LaxMonoidal.ε F') ≫ τ.app (𝟙_ C) =
      Functor.LaxMonoidal.ε G := by
  have h : Functor.LaxMonoidal.ε (F' ⋙ F) ≫ τ.app (𝟙_ C) = Functor.LaxMonoidal.ε G :=
    NatTrans.IsMonoidal.unit
  rw [Functor.LaxMonoidal.comp_ε, Category.assoc] at h
  exact h

/-- **A monoidal natural transformation out of a composite of lax monoidal functors carries a
tensor of two points, multiplied inside the composite, to the tensor of their images.**

The two images are taken as variables `p'` and `r'` together with the equations identifying them,
so that an induction hypothesis can be consumed without any rewriting in the category where the
statement is applied; see the implementation notes. -/
private theorem eps_comp_map_tensor_comp_app (F' : C ⥤ D) (F : D ⥤ E) (G : C ⥤ E)
    [F'.LaxMonoidal] [F.LaxMonoidal] [G.LaxMonoidal] (τ : F' ⋙ F ⟶ G)
    [NatTrans.IsMonoidal τ] (X Y : C) (p : 𝟙_ D ⟶ F'.obj X) (r : 𝟙_ D ⟶ F'.obj Y)
    (p' : 𝟙_ E ⟶ G.obj X) (r' : 𝟙_ E ⟶ G.obj Y)
    (hp : Functor.LaxMonoidal.ε F ≫ F.map p ≫ τ.app X = p')
    (hr : Functor.LaxMonoidal.ε F ≫ F.map r ≫ τ.app Y = r') :
    Functor.LaxMonoidal.ε F ≫
        F.map ((λ_ (𝟙_ D)).inv ≫ (p ⊗ₘ r) ≫ Functor.LaxMonoidal.μ F' X Y) ≫ τ.app (X ⊗ Y) =
      (λ_ (𝟙_ E)).inv ≫ (p' ⊗ₘ r') ≫ Functor.LaxMonoidal.μ G X Y := by
  subst hp
  subst hr
  have h1 : Functor.LaxMonoidal.ε F ≫ F.map (λ_ (𝟙_ D)).inv =
      (λ_ (𝟙_ E)).inv ≫ (Functor.LaxMonoidal.ε F ⊗ₘ Functor.LaxMonoidal.ε F) ≫
        Functor.LaxMonoidal.μ F (𝟙_ D) (𝟙_ D) := by
    rw [Functor.LaxMonoidal.ε_tensorHom_comp_μ, leftUnitor_naturality_assoc,
      Iso.inv_hom_id_assoc]
  have h3 : Functor.LaxMonoidal.μ F (F'.obj X) (F'.obj Y) ≫
        F.map (Functor.LaxMonoidal.μ F' X Y) ≫ τ.app (X ⊗ Y) =
      (τ.app X ⊗ₘ τ.app Y) ≫ Functor.LaxMonoidal.μ G X Y := by
    have h : Functor.LaxMonoidal.μ (F' ⋙ F) X Y ≫ τ.app (X ⊗ Y) =
        (τ.app X ⊗ₘ τ.app Y) ≫ Functor.LaxMonoidal.μ G X Y :=
      NatTrans.IsMonoidal.tensor X Y
    rw [Functor.LaxMonoidal.comp_μ, Category.assoc] at h
    exact h
  calc Functor.LaxMonoidal.ε F ≫
        F.map ((λ_ (𝟙_ D)).inv ≫ (p ⊗ₘ r) ≫ Functor.LaxMonoidal.μ F' X Y) ≫ τ.app (X ⊗ Y)
      = (Functor.LaxMonoidal.ε F ≫ F.map (λ_ (𝟙_ D)).inv) ≫ F.map (p ⊗ₘ r) ≫
          F.map (Functor.LaxMonoidal.μ F' X Y) ≫ τ.app (X ⊗ Y) := by
        simp only [Functor.map_comp, Category.assoc]
    _ = (λ_ (𝟙_ E)).inv ≫ (Functor.LaxMonoidal.ε F ⊗ₘ Functor.LaxMonoidal.ε F) ≫
          Functor.LaxMonoidal.μ F (𝟙_ D) (𝟙_ D) ≫ F.map (p ⊗ₘ r) ≫
          F.map (Functor.LaxMonoidal.μ F' X Y) ≫ τ.app (X ⊗ Y) := by
        rw [h1]
        simp only [Category.assoc]
    _ = (λ_ (𝟙_ E)).inv ≫ (Functor.LaxMonoidal.ε F ⊗ₘ Functor.LaxMonoidal.ε F) ≫
          (F.map p ⊗ₘ F.map r) ≫ Functor.LaxMonoidal.μ F (F'.obj X) (F'.obj Y) ≫
          F.map (Functor.LaxMonoidal.μ F' X Y) ≫ τ.app (X ⊗ Y) := by
        rw [← Functor.LaxMonoidal.μ_natural_assoc]
    _ = (λ_ (𝟙_ E)).inv ≫
          ((Functor.LaxMonoidal.ε F ≫ F.map p ≫ τ.app X) ⊗ₘ
            (Functor.LaxMonoidal.ε F ≫ F.map r ≫ τ.app Y)) ≫
          Functor.LaxMonoidal.μ G X Y := by
        simp only [h3, tensorHom_comp_tensorHom_assoc]

end Abstract

/-! ### Restriction of points -/

/-- `AlgebraicGeometry.restrictPoint` at the reflexivity factorisation `ρ ≫ φ = ρ ≫ φ`: the
comparison `AlgebraicGeometry.Scheme.Modules.pullbackCongr rfl` is the identity, and the two
remaining factors are the unit of the monoidal functor `modulePullback ρ` of Tag 01CD and the
composition law `modulePullbackComp ρ φ` of Tag 0097. -/
private theorem restrictPoint_eq {V T S : Scheme.{u}} (ρ : V ⟶ T) (φ : T ⟶ S)
    {M : ModuleSheaf S} (q : 𝟙_ (ModuleSheaf T) ⟶ (modulePullback φ).obj M) :
    AlgebraicGeometry.restrictPoint ρ φ (ρ ≫ φ) rfl q =
      Functor.LaxMonoidal.ε (modulePullback ρ) ≫ (modulePullback ρ).map q ≫
        (modulePullbackComp ρ φ).hom.app M := by
  refine Eq.trans ?_ (congrArg
    (fun z => Functor.LaxMonoidal.ε (modulePullback ρ) ≫ (modulePullback ρ).map q ≫ z)
    (Category.comp_id ((modulePullbackComp ρ φ).hom.app M)))
  rfl

/-- **Restriction of points is additive.** The pullback of sheaves of modules along a morphism of
schemes is an additive functor, being a left adjoint between abelian categories, and the three
comparison isomorphisms in `AlgebraicGeometry.restrictPoint` are composed with on either side. -/
theorem restrictPoint_sum {V T S : Scheme.{u}} (ρ : V ⟶ T) (φ : T ⟶ S) (ψ : V ⟶ S)
    (w : ρ ≫ φ = ψ) {M : S.Modules} {κ : Type*} (s : Finset κ)
    (q : κ → (Scheme.unitModule T ⟶ (Scheme.Modules.pullback φ).obj M)) :
    AlgebraicGeometry.restrictPoint ρ φ ψ w (∑ i ∈ s, q i)
      = ∑ i ∈ s, AlgebraicGeometry.restrictPoint ρ φ ψ w (q i) := by
  unfold AlgebraicGeometry.restrictPoint
  simp only [Functor.map_sum, Preadditive.sum_comp, Preadditive.comp_sum]

/-! ### The tensor of a family of points of a pullback -/

/-- The tensor of a finite family of points of the pullback `φ^* B` of a sheaf of
`𝒪_S`-algebras, as a point of `φ^*(B^{⊗ m})`: the factors are multiplied *inside* the pullback,
through the tensorator of `modulePullback φ`. -/
def pullbackNatTensorPowPoint {T S : Scheme.{u}} (φ : T ⟶ S) (B : AlgebraSheaf S) :
    ∀ (m : ℕ), (Fin m → (𝟙_ (ModuleSheaf T) ⟶ ((algebraPullback φ).obj B).X)) →
      (𝟙_ (ModuleSheaf T) ⟶
        ((algebraPullback φ).obj (Stacks.TensorPowers.natTensorPow B m)).X)
  | 0, _ => Functor.LaxMonoidal.ε (modulePullback φ)
  | m + 1, ps => (λ_ (𝟙_ (ModuleSheaf T))).inv ≫
      (pullbackNatTensorPowPoint φ B m (Fin.init ps) ⊗ₘ ps (Fin.last m)) ≫
      Functor.LaxMonoidal.μ (modulePullback φ)
        (Stacks.TensorPowers.natTensorPow B m).X B.X

/-- The empty tensor of points is the unit of the monoidal functor `modulePullback φ`. -/
@[simp]
lemma pullbackNatTensorPowPoint_zero {T S : Scheme.{u}} (φ : T ⟶ S) (B : AlgebraSheaf S)
    (ps : Fin 0 → (𝟙_ (ModuleSheaf T) ⟶ ((algebraPullback φ).obj B).X)) :
    pullbackNatTensorPowPoint φ B 0 ps = Functor.LaxMonoidal.ε (modulePullback φ) :=
  rfl

/-- One more factor, multiplied in on the right through the tensorator. -/
@[simp]
lemma pullbackNatTensorPowPoint_succ {T S : Scheme.{u}} (φ : T ⟶ S) (B : AlgebraSheaf S) (m : ℕ)
    (ps : Fin (m + 1) → (𝟙_ (ModuleSheaf T) ⟶ ((algebraPullback φ).obj B).X)) :
    pullbackNatTensorPowPoint φ B (m + 1) ps = (λ_ (𝟙_ (ModuleSheaf T))).inv ≫
      (pullbackNatTensorPowPoint φ B m (Fin.init ps) ⊗ₘ ps (Fin.last m)) ≫
      Functor.LaxMonoidal.μ (modulePullback φ)
        (Stacks.TensorPowers.natTensorPow B m).X B.X :=
  rfl

/-- **Restriction commutes with the tensor of a finite family of points.** Restricting along
`ρ : V ⟶ T` the tensor, formed inside `φ^* B`, of a family of points of `φ^* B` gives the tensor,
formed inside `ψ^* B`, of the restricted points.

The whole content is the monoidality `isMonoidal_modulePullbackComp` of the composition law of
Tag 0097: its unit axiom settles the empty tensor, and its tensor axiom, together with the left
unitality and the naturality of the tensorator of `modulePullback ρ`, settles one more factor. -/
theorem restrictPoint_pullbackNatTensorPowPoint {V T S : Scheme.{u}} (ρ : V ⟶ T) (φ : T ⟶ S)
    (ψ : V ⟶ S) (w : ρ ≫ φ = ψ) (B : AlgebraSheaf S) :
    ∀ (m : ℕ) (ps : Fin m → (𝟙_ (ModuleSheaf T) ⟶ ((algebraPullback φ).obj B).X)),
      AlgebraicGeometry.restrictPoint ρ φ ψ w (pullbackNatTensorPowPoint φ B m ps)
        = pullbackNatTensorPowPoint ψ B m
            (fun j => AlgebraicGeometry.restrictPoint ρ φ ψ w (ps j)) := by
  subst w
  let := isMonoidal_modulePullbackComp ρ φ
  intro m
  induction m with
  | zero =>
    intro ps
    refine (restrictPoint_eq ρ φ _).trans ?_
    exact eps_comp_map_eps_comp_app (modulePullback φ) (modulePullback ρ)
      (modulePullback (ρ ≫ φ)) (modulePullbackComp ρ φ).hom
  | succ m ih =>
    intro ps
    have hP := (restrictPoint_eq ρ φ (M := (Stacks.TensorPowers.natTensorPow B m).X)
      (pullbackNatTensorPowPoint φ B m (Fin.init ps))).symm.trans (ih (Fin.init ps))
    have hr := (restrictPoint_eq ρ φ (M := B.X) (ps (Fin.last m))).symm
    refine (restrictPoint_eq ρ φ _).trans ?_
    exact eps_comp_map_tensor_comp_app (modulePullback φ) (modulePullback ρ)
      (modulePullback (ρ ≫ φ)) (modulePullbackComp ρ φ).hom
      (Stacks.TensorPowers.natTensorPow B m).X B.X
      (pullbackNatTensorPowPoint φ B m (Fin.init ps)) (ps (Fin.last m)) _ _ hP hr

end Stacks.EtaleCohomology.BrauerScheme

end

end
