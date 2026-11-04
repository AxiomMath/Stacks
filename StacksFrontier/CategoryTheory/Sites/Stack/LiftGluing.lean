module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.Defs
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing

/-!
# Gluing along lifts in a stack in groupoids

Two gluing statements phrased without chosen pullbacks, for use where the local data are
given on arbitrary objects mapping to the object being glued over.

For a sheaf of types `F` on a site, a relation `Q g z` between morphisms `g : V ⟶ T` and
sections `z` of `F` over `V`, which is functional, stable under restriction and locally
satisfiable, is the graph of restriction of a unique section of `F` over `T`
(`CategoryTheory.Presheaf.existsUnique_of_locally`).

For a stack in groupoids `p : 𝒳 ⥤ 𝒮` and objects `x`, `y` over `U`, a relation `Q φ ψ`
between morphisms `φ : x' ⟶ x` and `ψ : x' ⟶ y` which is functional, stable under
precomposition, compatible with the base, and locally satisfiable over a covering sieve of
`U`, is of the form `ψ = φ ≫ m` for a morphism `m : x ⟶ y` over the identity of `U`
(`CategoryTheory.Functor.IsStack.exists_hom_of_locally`). This is condition (2) of
Stacks 026F, read through the lifts rather than through the chosen pullbacks of
`CategoryTheory.Functor.morPresheaf`.

## Main results

* `CategoryTheory.Presheaf.existsUnique_of_locally`.
* `CategoryTheory.Functor.IsStack.eq_of_locally`: two morphisms over the same base morphism
  which agree after precomposition with lifts of the members of a covering sieve are equal.
* `CategoryTheory.Functor.IsStack.exists_hom_of_locally`.
-/

@[expose] public section

namespace CategoryTheory

open Opposite

universe v₁ v₂ u₁ u₂ w

namespace Presheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {F : Cᵒᵖ ⥤ Type w}

/-- **Gluing a section from a local relation.** Let `F` be a sheaf of types, `R` a covering sieve
of `T` and `Q g z` a relation between morphisms `g : V ⟶ T` and sections `z` of `F` over `V`. If
`Q` is stable under restriction, and for every member `g` of `R` the relation `Q g` has exactly
one solution, then there is a unique section `y` over `T` with `z = y|_V` whenever `Q g z`. -/
theorem existsUnique_of_locally (hF : Presheaf.IsSheaf J F) {T : C} {R : Sieve T} (hR : R ∈ J T)
    (Q : ∀ ⦃V : C⦄, (V ⟶ T) → F.obj (op V) → Prop)
    (hfun : ∀ ⦃V : C⦄ (g : V ⟶ T), R g → ∀ z z' : F.obj (op V), Q g z → Q g z' → z = z')
    (hres : ∀ ⦃V W : C⦄ (g : V ⟶ T) (c : W ⟶ V) (z : F.obj (op V)), Q g z →
      Q (c ≫ g) (F.map c.op z))
    (hloc : ∀ ⦃V : C⦄ (g : V ⟶ T), R g → ∃ z, Q g z) :
    ∃! y : F.obj (op T), ∀ ⦃V : C⦄ (g : V ⟶ T) (z : F.obj (op V)), Q g z →
      z = F.map g.op y := by
  have hS := (isSheaf_iff_isSheaf_of_type J F).1 hF
  choose z hz using hloc
  let fam : Presieve.FamilyOfElements F R.arrows := fun _ g hg => z g hg
  have hcompat : fam.Compatible := by
    intro W₁ W₂ Z c₁ c₂ g₁ g₂ hg₁ hg₂ heq
    have h1 := hres g₁ c₁ _ (hz g₁ hg₁)
    have h2 := hres g₂ c₂ _ (hz g₂ hg₂)
    rw [heq] at h1
    exact hfun _ (R.downward_closed hg₂ c₂) _ _ h1 h2
  obtain ⟨y, hy, -⟩ := hS R hR fam hcompat
  have key : ∀ ⦃V : C⦄ (g : V ⟶ T) (z' : F.obj (op V)), Q g z' → z' = F.map g.op y := by
    intro V g z' hq
    refine (hS _ (J.pullback_stable g hR)).isSeparatedFor.ext fun W c hc => ?_
    rw [← Functor.map_comp_apply, ← op_comp, hy (c ≫ g) hc]
    exact hfun _ hc _ _ (hres g c z' hq) (hz _ hc)
  refine ⟨y, key, fun y' hy' => (hS R hR).isSeparatedFor.ext fun V g hg => ?_⟩
  exact (hy' g _ (hz g hg)).symm.trans (key g _ (hz g hg))

end Presheaf

namespace Functor

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {p : 𝒳 ⥤ 𝒮} {J : GrothendieckTopology 𝒮}

/-- In a category fibred in groupoids, a morphism over `g` factors through any other morphism
over `g` with the same target, by a morphism over the identity. -/
theorem IsFiberedInGroupoids.exists_isHomLift_id_comp (hp : p.IsFiberedInGroupoids)
    {V U : 𝒮} {g : V ⟶ U} {x x' x'' : 𝒳} (φ : x' ⟶ x) (π : x'' ⟶ x) [p.IsHomLift g φ]
    [p.IsHomLift g π] : ∃ ε : x'' ⟶ x', p.IsHomLift (𝟙 V) ε ∧ ε ≫ φ = π := by
  have := hp.isStronglyCartesian_homLift g φ
  exact ⟨IsCartesian.map p g φ π, inferInstance, IsCartesian.fac p g φ π⟩

/-- **Separatedness, read through lifts.** In a stack in groupoids, two morphisms over the
identity of `U` which agree after precomposition with a lift of every member of a covering
sieve of `U` are equal. -/
theorem IsStack.hom_ext_of_locally (hst : p.IsStack J) (hp : p.IsFiberedInGroupoids)
    {U : 𝒮} {x y : 𝒳} (m m' : x ⟶ y) [p.IsHomLift (𝟙 U) m] [p.IsHomLift (𝟙 U) m']
    {R : Sieve U} (hR : R ∈ J U)
    (h : ∀ ⦃V : 𝒮⦄ (g : V ⟶ U), R g →
      ∃ (x' : 𝒳) (φ : x' ⟶ x), p.IsHomLift g φ ∧ φ ≫ m = φ ≫ m') :
    m = m' := by
  have := hst.isFibered
  let a : p.Fiber U := ⟨x, IsHomLift.domain_eq p (𝟙 U) m⟩
  let b : p.Fiber U := ⟨y, IsHomLift.codomain_eq p (𝟙 U) m⟩
  let M : a ⟶ b := ⟨m, inferInstance⟩
  let M' : a ⟶ b := ⟨m', inferInstance⟩
  have hMM' : M = M' := by
    refine eq_of_pullbackFiberHom_locally_eq p (hst.isMorSheaf U a b) hR ?_
    intro V g hg
    obtain ⟨x', φ, hφ, he⟩ := h g hg
    obtain ⟨ε, -, hε⟩ := hp.exists_isHomLift_id_comp (g := g) φ (IsPreFibered.pullbackMap a.2 g)
    refine pullbackFiberHom_uniq M' g _ ?_
    rw [pullbackFiberHom_fac]
    show IsPreFibered.pullbackMap a.2 g ≫ m = IsPreFibered.pullbackMap a.2 g ≫ m'
    rw [← hε, Category.assoc, Category.assoc, he]
  exact congrArg Subtype.val hMM'

/-- **Separatedness over a base morphism, read through lifts.** In a stack in groupoids, two
morphisms over the same `g : V ⟶ U` which agree after precomposition with a lift of every
member of a covering sieve of `V` are equal. -/
theorem IsStack.eq_of_locally (hst : p.IsStack J) (hp : p.IsFiberedInGroupoids)
    {V U : 𝒮} {g : V ⟶ U} {x y : 𝒳} (ψ ψ' : x ⟶ y) [p.IsHomLift g ψ] [p.IsHomLift g ψ']
    {R : Sieve V} (hR : R ∈ J V)
    (h : ∀ ⦃W : 𝒮⦄ (c : W ⟶ V), R c →
      ∃ (x' : 𝒳) (χ : x' ⟶ x), p.IsHomLift c χ ∧ χ ≫ ψ = χ ≫ ψ') :
    ψ = ψ' := by
  obtain ⟨ε, hε, hεψ⟩ := hp.exists_isHomLift_id_comp (g := g) ψ' ψ
  have hε1 : ε = 𝟙 x := by
    have : p.IsHomLift (𝟙 V) (𝟙 x) := IsHomLift.id (IsHomLift.domain_eq p g ψ)
    refine hst.hom_ext_of_locally hp ε (𝟙 x) hR (fun W c hc => ?_)
    obtain ⟨x', χ, hχ, hχψ⟩ := h c hc
    refine ⟨x', χ, hχ, ?_⟩
    have := hp.isStronglyCartesian_homLift g ψ'
    refine IsStronglyCartesian.ext p g ψ' c ?_
    rw [Category.assoc, hεψ, hχψ, Category.comp_id]
  rw [← hεψ, hε1, Category.id_comp]

/-- **Gluing a morphism of a stack in groupoids from a local relation.** Let `x` and `y` lie
over `U`, and let `Q φ ψ` be a relation between morphisms `φ : x' ⟶ x` and `ψ : x' ⟶ y`. If
`Q φ` has at most one solution when `φ` lies over a morphism of the base, `Q` is stable under
precomposition, a solution lies over the same base morphism as `φ`, and over every member of a
covering sieve of `U` some lift `φ` has a solution, then there is a morphism `m : x ⟶ y` over the
identity of `U` with `ψ = φ ≫ m` whenever `Q φ ψ`. -/
theorem IsStack.exists_hom_of_locally (hst : p.IsStack J) (hp : p.IsFiberedInGroupoids)
    {U : 𝒮} {x y : 𝒳} (hx : p.obj x = U) (hy : p.obj y = U)
    (Q : ∀ ⦃x' : 𝒳⦄, (x' ⟶ x) → (x' ⟶ y) → Prop)
    (hfun : ∀ ⦃V : 𝒮⦄ ⦃x' : 𝒳⦄ (g : V ⟶ U) (φ : x' ⟶ x) (ψ ψ' : x' ⟶ y),
      p.IsHomLift g φ → Q φ ψ → Q φ ψ' → ψ = ψ')
    (hres : ∀ ⦃x' x'' : 𝒳⦄ (χ : x'' ⟶ x') (φ : x' ⟶ x) (ψ : x' ⟶ y), Q φ ψ →
      Q (χ ≫ φ) (χ ≫ ψ))
    (hlift : ∀ ⦃V : 𝒮⦄ ⦃x' : 𝒳⦄ (g : V ⟶ U) (φ : x' ⟶ x) (ψ : x' ⟶ y), Q φ ψ →
      p.IsHomLift g φ → p.IsHomLift g ψ)
    {R : Sieve U} (hR : R ∈ J U)
    (hloc : ∀ ⦃V : 𝒮⦄ (g : V ⟶ U), R g →
      ∃ (x' : 𝒳) (φ : x' ⟶ x) (ψ : x' ⟶ y), p.IsHomLift g φ ∧ Q φ ψ) :
    ∃ m : x ⟶ y, p.IsHomLift (𝟙 U) m ∧
      ∀ ⦃V : 𝒮⦄ ⦃x' : 𝒳⦄ (g : V ⟶ U) (φ : x' ⟶ x) (ψ : x' ⟶ y), p.IsHomLift g φ →
        Q φ ψ → ψ = φ ≫ m := by
  have := hst.isFibered
  let a : p.Fiber U := ⟨x, hx⟩
  let b : p.Fiber U := ⟨y, hy⟩
  have hQπ : ∀ ⦃V : 𝒮⦄ (g : V ⟶ U), R g →
      ∃ ψ : (pullbackFiber p a g).1 ⟶ y, Q (IsPreFibered.pullbackMap a.2 g) ψ := by
    intro V g hg
    obtain ⟨x', φ, ψ, hφ, hQ⟩ := hloc g hg
    obtain ⟨ε, -, hε⟩ := hp.exists_isHomLift_id_comp (g := g) φ (IsPreFibered.pullbackMap a.2 g)
    exact ⟨ε ≫ ψ, hε ▸ hres ε φ ψ hQ⟩
  choose θ' hθ' using hQπ
  have hθ'lift : ∀ ⦃V : 𝒮⦄ (g : V ⟶ U) (hg : R g), p.IsHomLift g (θ' g hg) :=
    fun V g hg => hlift g _ _ (hθ' g hg) inferInstance
  have hθ : ∀ ⦃V : 𝒮⦄ (g : V ⟶ U) (hg : R g), ∃ t : pullbackFiber p a g ⟶ pullbackFiber p b g,
      Fiber.fiberInclusion.map t ≫ IsPreFibered.pullbackMap b.2 g = θ' g hg := fun V g hg => by
    have := hθ'lift g hg
    have := IsPreFibered.pullbackMap.IsCartesian b.2 g
    exact ⟨⟨IsCartesian.map p g (IsPreFibered.pullbackMap b.2 g) (θ' g hg), inferInstance⟩,
      IsCartesian.fac p g _ _⟩
  choose θ hθfac using hθ
  obtain ⟨m, hm⟩ := exists_fiberHom_of_locally p (hst.isMorSheaf U a b) hR θ (by
    intro V W f hf γ c hc hc'
    apply fiber_hom_ext_of_cartesian c (IsPreFibered.pullbackMap b.2 c) inferInstance
    rw [hθfac, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc,
      pullbackFiberCompIso'_hom_fac, pullbackFiberHom_fac_assoc, hθfac]
    refine hfun c _ _ _ inferInstance (hθ' c hc') ?_
    have := hres (Fiber.fiberInclusion.map (pullbackFiberCompIso' a f γ c hc).inv ≫
      IsPreFibered.pullbackMap (pullbackFiber p a f).2 γ) _ _ (hθ' f hf)
    rwa [Category.assoc, Category.assoc, pullbackFiberCompIso'_inv_fac] at this)
  have hQm : ∀ ⦃V : 𝒮⦄ (g : V ⟶ U), R g → ∀ ⦃x' : 𝒳⦄ (φ : x' ⟶ x), p.IsHomLift g φ →
      Q φ (φ ≫ m.1) := by
    intro V g hg x' φ hφ
    have h1 : IsPreFibered.pullbackMap a.2 g ≫ m.1 = θ' g hg := by
      rw [← hθfac g hg, ← hm g hg]
      exact (pullbackFiberHom_fac m g).symm
    obtain ⟨ε, -, hε⟩ := hp.exists_isHomLift_id_comp (g := g) (IsPreFibered.pullbackMap a.2 g) φ
    have := hres ε _ _ (hθ' g hg)
    rwa [← h1, ← Category.assoc, hε] at this
  have hm1 : p.IsHomLift (𝟙 U) m.1 := m.2
  refine ⟨m.1, hm1, fun V x' g φ ψ hφ hQ => ?_⟩
  have := hlift g φ ψ hQ hφ
  refine hst.eq_of_locally hp (g := g) ψ (φ ≫ m.1) (J.pullback_stable g hR) (fun W c hc => ?_)
  obtain ⟨x'', χ, hχ⟩ := hp.exists_lift c x' (IsHomLift.domain_eq p g φ)
  refine ⟨x'', χ, hχ, ?_⟩
  rw [← Category.assoc]
  exact hfun (c ≫ g) (χ ≫ φ) _ _ inferInstance (hres χ φ ψ hQ)
    (hQm (c ≫ g) hc (χ ≫ φ) inferInstance)

end Functor

end CategoryTheory

end
