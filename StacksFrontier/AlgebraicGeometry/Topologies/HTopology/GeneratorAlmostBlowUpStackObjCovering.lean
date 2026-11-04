module

public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.GeneratorAlmostBlowUpStackObjGlue

/-!
# Gluing a solution of a descent problem along an h covering of the base

Fix a descent datum `D` relative to an h covering family `f i : V i ⟶ U` of the big h category over
`S`, and a morphism `F : W ⟶ U` of the site.  Suppose given an h covering family `γ c : W c ⟶ W`
and, over each member, a solution of `D`
(`AlgebraicGeometry.BigHOver.DescentSolution`); suppose moreover given an object `y` of the fibre
over `W` whose chosen pullback along each `γ c` is identified with the object of the solution
there.

The main result of this file, `AlgebraicGeometry.BigHOver.nonempty_descentSolution_of_covering`,
says that `y` carries a solution of `D` over `F` as soon as the *local comparisons* those
identifications produce,
`AlgebraicGeometry.BigHOver.DescentSolution.glueLocalMor`, do not depend on which member of the
covering they are read through.

This is the one place where an object of a fibre is glued, and all four locality steps of the
criterion of Stacks 0EX9 for descent of objects go through it: what differs between them is only
where the object `y` and its identifications come from — effective descent for the Zariski topology
in the Zariski step, and essential surjectivity of the comparison functor
`AlgebraicGeometry.BigHOver.twoFibreProductComparison` in the three remaining steps, through
`AlgebraicGeometry.BigHOver.exists_fiberObj`.

## Main definitions

* `AlgebraicGeometry.BigHOver.DescentSolution.glueLocalMor`: the comparison, over an object mapping
  to a member `W c` of the covering and to a member `V i` of the family, between the chosen
  pullback of `y` and the chosen pullback of the object of `D` at `i`, read through the solution
  over `W c`.
* `AlgebraicGeometry.BigHOver.DescentSolution.IsGlueMor`: the property of a morphism of a fibre of
  restricting to the local comparisons.

## Main results

* `AlgebraicGeometry.BigHOver.DescentSolution.glueLocalMor_baseChange`: the local comparisons are
  compatible with base change.
* `AlgebraicGeometry.BigHOver.DescentSolution.IsGlueMor.eq` and
  `AlgebraicGeometry.BigHOver.DescentSolution.exists_isGlueMor`: a morphism restricting to the
  local comparisons is unique, and exists as soon as they agree.
* `AlgebraicGeometry.BigHOver.nonempty_descentSolution_of_covering`: **the gluing.**

## Implementation notes

The identifications of the glued solution are the morphisms
`AlgebraicGeometry.BigHOver.DescentSolution.IsGlueMor` characterizes, and both remaining axioms of
a solution — compatibility with the gluing isomorphisms of `D` and with base change — are proved
from that characterization alone: each side restricts to the same local comparison, so the two are
equal by uniqueness.  No cocycle condition on the covering is used anywhere, which is what lets the
three non-Zariski steps supply their object through a two-fibre product carrying no such condition.

That the identifications are *isomorphisms* and not merely morphisms is where the fibres being
groupoids is used, and that is the only use of it: condition (1) of Stacks 0EX9 asserts a stack in
groupoids, so `CategoryTheory.Functor.IsFiberedInGroupoids.fiber_isGroupoid` applies.

## References

* [Stacks Project, Tag 0EX9](https://stacks.math.columbia.edu/tag/0EX9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe t v u

namespace AlgebraicGeometry

namespace BigHOver

variable {B : BigHSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒳 : Type t} [Category.{v} 𝒳] {p : 𝒳 ⥤ BigHOver B S hS} [p.IsFibered]
variable {U : BigHOver B S hS} {I : Type (u + 1)} {V : I → BigHOver B S hS} {f : ∀ i, V i ⟶ U}
variable {D : (Functor.IsFibered.pullbackPseudofunctor p).DescentData f}
variable {W : BigHOver B S hS} {F : W ⟶ U} {K : Type (u + 1)} {Wc : K → BigHOver B S hS}
  {γ : ∀ c, Wc c ⟶ W} {Fc : ∀ c, Wc c ⟶ U}

namespace DescentSolution

/-! ### The local comparisons -/

/-- **The local comparison of `y` with the objects of `D`, read through the solution over a member
of the covering.**  Over an object mapping to the member `W c` and to the member `V i` of the
family, compatibly over `U`, the chosen pullback of `y` is identified with the chosen pullback of
the object of `D` at `i` by contracting the iterated chosen pullback of `y`, applying the given
identification of `y` with the object of the solution over `W c`, and then the identification that
solution carries. -/
public def glueLocalMor {s : ∀ c, DescentSolution D (Fc c)} {y : p.Fiber W}
    (hFc : ∀ c, γ c ≫ F = Fc c)
    (β : ∀ c, Functor.pullbackFiber p y (γ c) ≅ (s c).obj) (c : K) ⦃T : BigHOver B S hS⦄
    (ε : T ⟶ Wc c) (r : T ⟶ W) (hr : ε ≫ γ c = r) (i : I) (ζ : T ⟶ V i) (qq : T ⟶ U)
    (hqq : r ≫ F = qq) (hζ : ζ ≫ f i = qq) :
    Functor.pullbackFiber p y r ⟶ Functor.pullbackFiber p (descentObj D i) ζ :=
  (Functor.pullbackFiberCompIso' y (γ c) ε r hr).inv ≫ Functor.pullbackFiberHom (β c).hom ε ≫
    ((s c).iso i ε ζ qq (by rw [← hFc c, ← Category.assoc, hr]; exact hqq) hζ).hom

/-- `AlgebraicGeometry.BigHOver.DescentSolution.glueLocalMor` unfolded, with the factorization of
the composite into `U` through the member of the covering supplied explicitly. -/
public theorem glueLocalMor_eq {s : ∀ c, DescentSolution D (Fc c)} {y : p.Fiber W}
    (hFc : ∀ c, γ c ≫ F = Fc c)
    (β : ∀ c, Functor.pullbackFiber p y (γ c) ≅ (s c).obj) (c : K) ⦃T : BigHOver B S hS⦄
    (ε : T ⟶ Wc c) (r : T ⟶ W) (hr : ε ≫ γ c = r) (i : I) (ζ : T ⟶ V i) (qq : T ⟶ U)
    (hqq : r ≫ F = qq) (hζ : ζ ≫ f i = qq) (hεq : ε ≫ Fc c = qq) :
    glueLocalMor hFc β c ε r hr i ζ qq hqq hζ =
      (Functor.pullbackFiberCompIso' y (γ c) ε r hr).inv ≫ Functor.pullbackFiberHom (β c).hom ε ≫
        ((s c).iso i ε ζ qq hεq hζ).hom := rfl

/-- Factoring a composite through `g` and then through a member `Fc` of the covering. -/
private theorem comp_eq_of_comp_comp_eq {C : Type*} [Category C] {T X Y Z : C} {a : T ⟶ X}
    {g : X ⟶ Y} {k : Y ⟶ Z} {k' : X ⟶ Z} {r : T ⟶ Y} {qq : T ⟶ Z} (hk : g ≫ k = k')
    (hr : a ≫ g = r) (hqq : r ≫ k = qq) : a ≫ k' = qq := by
  rw [← hk, ← Category.assoc, hr, hqq]

/-- The two squares of a pullback of `f` along `g`, composed with a morphism `k` out of `Z`. -/
private theorem pullback_fst_comp_comp_comp_eq {C : Type*} [Category C] {X Y Z Z' : C}
    [Limits.HasPullbacks C] (f : X ⟶ Z) (g : Y ⟶ Z) {k : Z ⟶ Z'} {q : Y ⟶ Z'} (h : g ≫ k = q) :
    (Limits.pullback.fst f g ≫ f) ≫ k = Limits.pullback.snd f g ≫ q := by
  rw [Limits.pullback.condition, Category.assoc, h]

/-- **The local comparisons are compatible with base change.** -/
public theorem glueLocalMor_baseChange {s : ∀ c, DescentSolution D (Fc c)} {y : p.Fiber W}
    (hFc : ∀ c, γ c ≫ F = Fc c)
    (β : ∀ c, Functor.pullbackFiber p y (γ c) ≅ (s c).obj) (c : K) ⦃T T' : BigHOver B S hS⦄
    (ε : T ⟶ Wc c) (r : T ⟶ W) (hr : ε ≫ γ c = r) (i : I) (ζ : T ⟶ V i) (qq : T ⟶ U)
    (hqq : r ≫ F = qq) (hζ : ζ ≫ f i = qq) (μ : T' ⟶ T) (ε' : T' ⟶ Wc c) (hε' : μ ≫ ε = ε')
    (r' : T' ⟶ W) (hr' : μ ≫ r = r') (hrr : ε' ≫ γ c = r') (ζ' : T' ⟶ V i) (hζ' : μ ≫ ζ = ζ')
    (qq' : T' ⟶ U) (hqq' : r' ≫ F = qq') (hζq : ζ' ≫ f i = qq') :
    Functor.baseChangeFiberMor (glueLocalMor hFc β c ε r hr i ζ qq hqq hζ) μ r' hr' ζ' hζ' =
      glueLocalMor hFc β c ε' r' hrr i ζ' qq' hqq' hζq := by
  have hεq := comp_eq_of_comp_comp_eq (hFc c) hr hqq
  have hεq' := comp_eq_of_comp_comp_eq (hFc c) hrr hqq'
  rw [glueLocalMor_eq hFc β c ε r hr i ζ qq hqq hζ hεq,
    glueLocalMor_eq hFc β c ε' r' hrr i ζ' qq' hqq' hζq hεq',
    Functor.baseChangeFiberMor_comp _ _ μ r' hr' ε' hε' ζ' hζ',
    Functor.baseChangeFiberMor_comp _ _ μ ε' hε' ε' hε' ζ' hζ',
    baseChangeFiberMor_pullbackFiberCompIso'_inv y (γ c) ε r hr μ ε' hε' r' hrr hr',
    ← Functor.pullbackFiberHom_eq_baseChangeFiberMor (β c).hom ε μ ε' hε',
    (s c).iso_baseChange i ε ζ qq hεq hζ μ ε' hε' ζ' hζ' qq' hεq' hζq]

/-! ### The glued morphisms -/

/-- **The property of restricting to the local comparisons.**  A morphism between the chosen
pullback of `y` along `δ : Z ⟶ W` and the chosen pullback of the object of `D` at `i` along
`ζ : Z ⟶ V i` *glues* the local comparisons when its base change to any object mapping to `Z` and
to a member of the covering is the local comparison read through that member. -/
public def IsGlueMor {s : ∀ c, DescentSolution D (Fc c)} {y : p.Fiber W}
    (hFc : ∀ c, γ c ≫ F = Fc c)
    (β : ∀ c, Functor.pullbackFiber p y (γ c) ≅ (s c).obj) (i : I) ⦃Z : BigHOver B S hS⦄
    (δ : Z ⟶ W) (ζ : Z ⟶ V i) (_q : Z ⟶ U)
    (M : Functor.pullbackFiber p y δ ⟶ Functor.pullbackFiber p (descentObj D i) ζ) : Prop :=
  ∀ (c : K) ⦃T : BigHOver B S hS⦄ (σ : T ⟶ Wc c) (π : T ⟶ Z) (r : T ⟶ W) (hσ : σ ≫ γ c = r)
    (hπ : π ≫ δ = r) (ζ' : T ⟶ V i) (hζ' : π ≫ ζ = ζ') (qq : T ⟶ U) (hqq : r ≫ F = qq)
    (hζq : ζ' ≫ f i = qq),
    Functor.baseChangeFiberMor M π r hπ ζ' hζ' = glueLocalMor hFc β c σ r hσ i ζ' qq hqq hζq

/-- **A base change of a glued morphism glues the local comparisons.** -/
public theorem IsGlueMor.baseChange {s : ∀ c, DescentSolution D (Fc c)} {y : p.Fiber W}
    {hFc : ∀ c, γ c ≫ F = Fc c}
    {β : ∀ c, Functor.pullbackFiber p y (γ c) ≅ (s c).obj} {i : I} ⦃Z Z' : BigHOver B S hS⦄
    {δ : Z ⟶ W} {ζ : Z ⟶ V i} {q : Z ⟶ U}
    {M : Functor.pullbackFiber p y δ ⟶ Functor.pullbackFiber p (descentObj D i) ζ}
    (hM : IsGlueMor hFc β i δ ζ q M) (κ : Z' ⟶ Z) (δ' : Z' ⟶ W) (hδ' : κ ≫ δ = δ')
    (ζ' : Z' ⟶ V i) (hζ' : κ ≫ ζ = ζ') (q' : Z' ⟶ U) :
    IsGlueMor hFc β i δ' ζ' q' (Functor.baseChangeFiberMor M κ δ' hδ' ζ' hζ') := by
  intro c T σ π r hσ hπ ζ'' hζ'' qq hqq hζq
  rw [Functor.baseChangeFiberMor_baseChangeFiberMor M κ δ' hδ' ζ' hζ' π r hπ ζ'' hζ'']
  exact hM c σ (π ≫ κ) r hσ (by rw [Category.assoc, hδ']; exact hπ) ζ''
    (by rw [Category.assoc, hζ']; exact hζ'') qq hqq hζq

/-- The canonical fibre products of the covering with a morphism into `W` form an h covering of its
source: this is `AlgebraicGeometry.BigHOver.sieve_ofArrows_pullback_mem_topology` for the covering
of `W` rather than for the covering of `U`. -/
public theorem sieve_ofArrows_pullback_mem_topology_covering
    (hcov : Sieve.ofArrows Wc γ ∈ BigHOver.topology B S hS W) {Z : BigHOver B S hS} (δ : Z ⟶ W) :
    Sieve.ofArrows (fun c ↦ Limits.pullback (γ c) δ)
      (fun c ↦ Limits.pullback.snd (γ c) δ) ∈ BigHOver.topology B S hS Z :=
  sieve_ofArrows_pullback_mem_topology hcov δ

/-- **A morphism gluing the local comparisons is unique.**  The canonical fibre products
`W c ×_W Z` form an h covering of `Z` and the base change to each of them is prescribed, so
`AlgebraicGeometry.BigHOver.eq_of_pullbackFiberHom_eq_of_covering` identifies two of them. -/
public theorem IsGlueMor.eq
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hcov : Sieve.ofArrows Wc γ ∈ BigHOver.topology B S hS W)
    {s : ∀ c, DescentSolution D (Fc c)} {y : p.Fiber W} {hFc : ∀ c, γ c ≫ F = Fc c}
    {β : ∀ c, Functor.pullbackFiber p y (γ c) ≅ (s c).obj} {i : I} ⦃Z : BigHOver B S hS⦄
    {δ : Z ⟶ W} {ζ : Z ⟶ V i} {q : Z ⟶ U} (h₁ : δ ≫ F = q) (h₂ : ζ ≫ f i = q)
    {M M' : Functor.pullbackFiber p y δ ⟶ Functor.pullbackFiber p (descentObj D i) ζ}
    (hM : IsGlueMor hFc β i δ ζ q M) (hM' : IsGlueMor hFc β i δ ζ q M') : M = M' := by
  refine eq_of_pullbackFiberHom_eq_of_covering h1 h2 h3 h4 M M'
    (fun c ↦ Limits.pullback.snd (γ c) δ)
    (sieve_ofArrows_pullback_mem_topology_covering hcov δ) fun c ↦ ?_
  have hπ : Limits.pullback.snd (γ c) δ ≫ δ = Limits.pullback.fst (γ c) δ ≫ γ c :=
    Limits.pullback.condition.symm
  have hqq := pullback_fst_comp_comp_comp_eq (γ c) δ h₁
  have hζq : (Limits.pullback.snd (γ c) δ ≫ ζ) ≫ f i = Limits.pullback.snd (γ c) δ ≫ q := by
    rw [Category.assoc, h₂]
  refine pullbackFiberHom_eq_of_baseChangeFiberMor_eq' M M' (Limits.pullback.snd (γ c) δ)
    (mx := Limits.pullback.fst (γ c) δ ≫ γ c) hπ
    (my := Limits.pullback.snd (γ c) δ ≫ ζ) rfl ?_
  rw [hM c (Limits.pullback.fst (γ c) δ) (Limits.pullback.snd (γ c) δ) _ rfl hπ _ rfl _ hqq hζq,
    hM' c (Limits.pullback.fst (γ c) δ) (Limits.pullback.snd (γ c) δ) _ rfl hπ _ rfl _ hqq hζq]

/-- **A morphism gluing the local comparisons exists** as soon as the local comparisons agree.  The
canonical fibre products `W c ×_W Z` form an h covering of `Z`, over each of them a morphism is
prescribed, and the hypothesis makes those prescriptions agree over any further object, so
`AlgebraicGeometry.BigHOver.existsUnique_fiberHom_of_covering` amalgamates them.  The gluing
property over an arbitrary object follows because any pair of morphisms into `Z` and into `W c`
agreeing over `W` factors through `W c ×_W Z` by `CategoryTheory.Limits.pullback.lift`. -/
public theorem exists_isGlueMor
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hcov : Sieve.ofArrows Wc γ ∈ BigHOver.topology B S hS W)
    {s : ∀ c, DescentSolution D (Fc c)} {y : p.Fiber W} (hFc : ∀ c, γ c ≫ F = Fc c)
    (β : ∀ c, Functor.pullbackFiber p y (γ c) ≅ (s c).obj)
    (hβ : ∀ (c c' : K) (T : BigHOver B S hS) (ε : T ⟶ Wc c) (ε' : T ⟶ Wc c') (r : T ⟶ W)
      (hr : ε ≫ γ c = r) (hr' : ε' ≫ γ c' = r) (i : I) (ζ : T ⟶ V i) (qq : T ⟶ U)
      (hqq : r ≫ F = qq) (hζ : ζ ≫ f i = qq),
      glueLocalMor hFc β c ε r hr i ζ qq hqq hζ = glueLocalMor hFc β c' ε' r hr' i ζ qq hqq hζ)
    (i : I) ⦃Z : BigHOver B S hS⦄ (δ : Z ⟶ W) (ζ : Z ⟶ V i) (q : Z ⟶ U) (h₁ : δ ≫ F = q)
    (h₂ : ζ ≫ f i = q) :
    ∃ M : Functor.pullbackFiber p y δ ⟶ Functor.pullbackFiber p (descentObj D i) ζ,
      IsGlueMor hFc β i δ ζ q M := by
  classical
  have hπ : ∀ c, Limits.pullback.snd (γ c) δ ≫ δ = Limits.pullback.fst (γ c) δ ≫ γ c :=
    fun c ↦ Limits.pullback.condition.symm
  have hqq := fun c ↦ pullback_fst_comp_comp_comp_eq (γ c) δ h₁
  have hζq : ∀ c, (Limits.pullback.snd (γ c) δ ≫ ζ) ≫ f i = Limits.pullback.snd (γ c) δ ≫ q :=
    fun c ↦ by rw [Category.assoc, h₂]
  -- the prescribed morphism over the canonical fibre product `W c ×_W Z`, read between the
  -- iterated chosen pullbacks
  let ψ : ∀ c, Functor.pullbackFiber p (Functor.pullbackFiber p y δ)
        (Limits.pullback.snd (γ c) δ) ⟶
      Functor.pullbackFiber p (Functor.pullbackFiber p (descentObj D i) ζ)
        (Limits.pullback.snd (γ c) δ) := fun c ↦
    (Functor.pullbackFiberCompIso' y δ (Limits.pullback.snd (γ c) δ) _ (hπ c)).hom ≫
      glueLocalMor hFc β c (Limits.pullback.fst (γ c) δ) _ rfl i _ _ (hqq c) (hζq c) ≫
        (Functor.pullbackFiberCompIso' (descentObj D i) ζ (Limits.pullback.snd (γ c) δ)
          _ rfl).inv
  have hψ : ∀ c, ψ c = (Functor.pullbackFiberCompIso' y δ (Limits.pullback.snd (γ c) δ)
        _ (hπ c)).hom ≫
      glueLocalMor hFc β c (Limits.pullback.fst (γ c) δ) _ rfl i _ _ (hqq c) (hζq c) ≫
        (Functor.pullbackFiberCompIso' (descentObj D i) ζ (Limits.pullback.snd (γ c) δ)
          _ rfl).inv := fun c ↦ rfl
  -- the base change of a prescribed morphism to an arbitrary further object
  have key : ∀ (c : K) (T : BigHOver B S hS) (μ : T ⟶ Limits.pullback (γ c) δ) (ρ : T ⟶ Z)
      (hρ : μ ≫ Limits.pullback.snd (γ c) δ = ρ) (hrρ : (ρ ≫ δ) ≫ F = ρ ≫ q)
      (hζρ : (ρ ≫ ζ) ≫ f i = ρ ≫ q)
      (hμσ : (μ ≫ Limits.pullback.fst (γ c) δ) ≫ γ c = ρ ≫ δ),
      Functor.baseChangeFiberMor (ψ c) μ ρ hρ ρ hρ =
        (Functor.pullbackFiberCompIso' y δ ρ (ρ ≫ δ) rfl).hom ≫
          glueLocalMor hFc β c (μ ≫ Limits.pullback.fst (γ c) δ) (ρ ≫ δ) hμσ i (ρ ≫ ζ) (ρ ≫ q)
              hrρ hζρ ≫
            (Functor.pullbackFiberCompIso' (descentObj D i) ζ ρ (ρ ≫ ζ) rfl).inv := by
    intro c T μ ρ hρ hrρ hζρ hμσ
    have hmid : μ ≫ Limits.pullback.fst (γ c) δ ≫ γ c = ρ ≫ δ := by
      rw [← Category.assoc]; exact hμσ
    have hmid' : μ ≫ Limits.pullback.snd (γ c) δ ≫ ζ = ρ ≫ ζ := by
      rw [← Category.assoc, hρ]
    rw [hψ c,
      baseChangeFiberMor_conj' (hπ c) rfl _ hρ hρ rfl hmid rfl hmid',
      glueLocalMor_baseChange hFc β c (Limits.pullback.fst (γ c) δ) _ rfl i _ _ (hqq c) (hζq c)
        μ (μ ≫ Limits.pullback.fst (γ c) δ) rfl (ρ ≫ δ) hmid hμσ (ρ ≫ ζ) hmid' (ρ ≫ q)
        hrρ hζρ]
  -- the prescriptions agree over any further object
  have hcompat : ∀ (c c' : K) (T : BigHOver B S hS) (μ : T ⟶ Limits.pullback (γ c) δ)
      (μ' : T ⟶ Limits.pullback (γ c') δ) (ρ : T ⟶ Z)
      (hρ : μ ≫ Limits.pullback.snd (γ c) δ = ρ)
      (hρ' : μ' ≫ Limits.pullback.snd (γ c') δ = ρ),
      Functor.baseChangeFiberMor (ψ c) μ ρ hρ ρ hρ =
        Functor.baseChangeFiberMor (ψ c') μ' ρ hρ' ρ hρ' := by
    intro c c' T μ μ' ρ hρ hρ'
    have hrρ : (ρ ≫ δ) ≫ F = ρ ≫ q := by rw [Category.assoc, h₁]
    have hζρ : (ρ ≫ ζ) ≫ f i = ρ ≫ q := by rw [Category.assoc, h₂]
    have hμσ : (μ ≫ Limits.pullback.fst (γ c) δ) ≫ γ c = ρ ≫ δ := by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hρ]
    have hμσ' : (μ' ≫ Limits.pullback.fst (γ c') δ) ≫ γ c' = ρ ≫ δ := by
      rw [Category.assoc, Limits.pullback.condition, ← Category.assoc, hρ']
    rw [key c T μ ρ hρ hrρ hζρ hμσ, key c' T μ' ρ hρ' hrρ hζρ hμσ',
      hβ c c' T (μ ≫ Limits.pullback.fst (γ c) δ) (μ' ≫ Limits.pullback.fst (γ c') δ) (ρ ≫ δ)
        hμσ hμσ' i (ρ ≫ ζ) (ρ ≫ q) hrρ hζρ]
  obtain ⟨M, hMψ, -⟩ := existsUnique_fiberHom_of_covering h1 h2 h3 h4
    (sieve_ofArrows_pullback_mem_topology_covering hcov δ) (ψ := ψ)
    (fun c c' T μ μ' ρ hρ hρ' ↦ hcompat c c' T μ μ' ρ hρ hρ')
  -- the gluing property at the canonical fibre products
  have hweak : ∀ c, Functor.baseChangeFiberMor M (Limits.pullback.snd (γ c) δ) _ (hπ c) _ rfl =
      glueLocalMor hFc β c (Limits.pullback.fst (γ c) δ) _ rfl i _ _ (hqq c) (hζq c) := by
    intro c
    rw [Functor.baseChangeFiberMor, hMψ c, hψ c, ← Category.assoc, ← Category.assoc,
      Iso.inv_hom_id, Category.id_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  refine ⟨M, fun c T σ π r hσ hπ' ζ' hζ' qq hqq' hζq' ↦ ?_⟩
  -- the pair `(σ, π)` factors through the canonical fibre product `W c ×_W Z`
  have hlift : σ ≫ γ c = π ≫ δ := by rw [hσ, hπ']
  have hlf : Limits.pullback.lift σ π hlift ≫ Limits.pullback.fst (γ c) δ = σ :=
    Limits.pullback.lift_fst _ _ _
  have hls : Limits.pullback.lift σ π hlift ≫ Limits.pullback.snd (γ c) δ = π :=
    Limits.pullback.lift_snd _ _ _
  have hmid : Limits.pullback.lift σ π hlift ≫ Limits.pullback.fst (γ c) δ ≫ γ c = r := by
    rw [← Category.assoc, hlf, hσ]
  have hmid' : Limits.pullback.lift σ π hlift ≫ Limits.pullback.snd (γ c) δ ≫ ζ = ζ' := by
    rw [← Category.assoc, hls, hζ']
  have hstep := congrArg
    (fun ξ ↦ Functor.baseChangeFiberMor ξ (Limits.pullback.lift σ π hlift) r hmid ζ' hmid')
    (hweak c)
  rw [Functor.baseChangeFiberMor_baseChangeFiberMor M (Limits.pullback.snd (γ c) δ) _ (hπ c)
      _ rfl (Limits.pullback.lift σ π hlift) r hmid ζ' hmid',
    glueLocalMor_baseChange hFc β c (Limits.pullback.fst (γ c) δ) _ rfl i _ _ (hqq c) (hζq c)
      (Limits.pullback.lift σ π hlift) σ hlf r hmid hσ ζ' hmid' qq hqq' hζq'] at hstep
  have hmid2 : (Limits.pullback.lift σ π hlift ≫ Limits.pullback.snd (γ c) δ) ≫ δ = r := by
    rw [hls]; exact hπ'
  have hmid3 : (Limits.pullback.lift σ π hlift ≫ Limits.pullback.snd (γ c) δ) ≫ ζ = ζ' := by
    rw [hls]; exact hζ'
  rw [Functor.baseChangeFiberMor_congr M hls.symm hπ' hmid2 hζ' hmid3]
  exact hstep

end DescentSolution

/-! ### The gluing -/

open DescentSolution in
/-- **A solution of `D` over `F` glued from solutions over an h covering of its source.**  Given an
h covering family `γ c : W c ⟶ W`, a solution of `D` over each `W c ⟶ U`, an object `y` of the
fibre over `W` identified over each `W c` with the object of the solution there, and the hypothesis
that the resulting local comparisons do not depend on which member of the covering they are read
through, `y` carries a solution of `D` over `F`.

Its identifications are the morphisms
`AlgebraicGeometry.BigHOver.DescentSolution.IsGlueMor` characterizes; they are isomorphisms because
the fibres of a category fibred in groupoids are groupoids, and the two axioms of a solution follow
from the uniqueness of such a morphism. -/
public theorem nonempty_descentSolution_of_covering
    (h1 : IsZariskiStackInGroupoids B S hS p)
    (h2 : IsAffineFlatProperFinitePresentationDescent B S hS p)
    (h3 : IsOneGeneratorAlmostBlowUpStack B S hS p)
    (h4 : IsTwoGeneratorAlmostBlowUpStack B S hS p)
    (hcov : Sieve.ofArrows Wc γ ∈ BigHOver.topology B S hS W)
    {s : ∀ c, DescentSolution D (Fc c)} {y : p.Fiber W} (hFc : ∀ c, γ c ≫ F = Fc c)
    (β : ∀ c, Functor.pullbackFiber p y (γ c) ≅ (s c).obj)
    (hβ : ∀ (c c' : K) (T : BigHOver B S hS) (ε : T ⟶ Wc c) (ε' : T ⟶ Wc c') (r : T ⟶ W)
      (hr : ε ≫ γ c = r) (hr' : ε' ≫ γ c' = r) (i : I) (ζ : T ⟶ V i) (qq : T ⟶ U)
      (hqq : r ≫ F = qq) (hζ : ζ ≫ f i = qq),
      glueLocalMor hFc β c ε r hr i ζ qq hqq hζ = glueLocalMor hFc β c' ε' r hr' i ζ qq hqq hζ) :
    Nonempty (DescentSolution D F) := by
  classical
  have hgpd : ∀ T : BigHOver B S hS, IsGroupoid (p.Fiber T) :=
    h1.isFiberedInGroupoids.fiber_isGroupoid
  have hex : ∀ (i : I) (Z : BigHOver B S hS) (δ : Z ⟶ W) (ζ : Z ⟶ V i) (q : Z ⟶ U)
      (h₁ : δ ≫ F = q) (h₂ : ζ ≫ f i = q),
      ∃ e : Functor.pullbackFiber p y δ ≅ Functor.pullbackFiber p (descentObj D i) ζ,
        IsGlueMor hFc β i δ ζ q e.hom := by
    intro i Z δ ζ q h₁ h₂
    obtain ⟨M, hM⟩ := exists_isGlueMor h1 h2 h3 h4 hcov hFc β hβ i δ ζ q h₁ h₂
    have := hgpd Z
    have : IsIso M := IsGroupoid.all_isIso M
    exact ⟨asIso M, hM⟩
  choose e he using hex
  refine ⟨{ obj := y
            iso := fun i ⦃Z⦄ δ ζ q h₁ h₂ ↦ e i Z δ ζ q h₁ h₂
            compat := ?_
            iso_baseChange := ?_ }⟩
  · intro i j Z δ ζ ζ' q h h' h''
    refine IsGlueMor.eq h1 h2 h3 h4 hcov h h'' ?_ (he j Z δ ζ' q h h'')
    intro c T σ π r hσ hπ ζ₂ hζ₂ qq hqq hζq
    have hζ₁ : (π ≫ ζ) ≫ f i = qq := by
      rw [Category.assoc, h', ← hqq, ← hπ, Category.assoc, h]
    have hεq := comp_eq_of_comp_comp_eq (hFc c) hσ hqq
    rw [Functor.baseChangeFiberMor_comp _ _ π r hπ (π ≫ ζ) rfl ζ₂ hζ₂,
      he i Z δ ζ q h h' c σ π r hσ hπ (π ≫ ζ) rfl qq hqq hζ₁,
      descentIso_baseChange i j ζ ζ' q h' h'' π (π ≫ ζ) rfl ζ₂ hζ₂ qq hζ₁ hζq,
      glueLocalMor_eq hFc β c σ r hσ i (π ≫ ζ) qq hqq hζ₁ hεq,
      glueLocalMor_eq hFc β c σ r hσ j ζ₂ qq hqq hζq hεq, Category.assoc, Category.assoc,
      (s c).compat i j σ (π ≫ ζ) ζ₂ qq hεq hζ₁ hζq]
  · intro i Z Z' δ ζ q h h' κ δ' hδ' ζ' hζ' q' hq hq'
    exact IsGlueMor.eq h1 h2 h3 h4 hcov hq hq'
      ((he i Z δ ζ q h h').baseChange κ δ' hδ' ζ' hζ' q') (he i Z' δ' ζ' q' hq hq')

end BigHOver

end AlgebraicGeometry

end
