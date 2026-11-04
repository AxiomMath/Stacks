module

public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingRelativeDescent
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.AffinePullbackSystem
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
public import StacksFrontier.CategoryTheory.Sites.Stack.DescentDataEquivalence
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.MorGluing
public import StacksFrontier.CategoryTheory.Sites.Stack.MorSeparated
public import StacksFrontier.CategoryTheory.Sites.Stack.SingleArrowCoverMorphisms
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence

/-!
# Gluing a descended object at a finite stage

Let `T = lim Tᵢ` be a cofiltered limit of affine schemes over `S`, let `{W ⟶ T}` be the base change
of a single-member fppf covering `{W₀ ⟶ T₀}` of a stage, and let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of
stacks in groupoids over the big fppf site of `S`. This file shows that an object `x` of `𝒳` over
`T`, together with a morphism `f x ⟶ y` to the pullback of an object `y` of `𝒴` over a stage,
descends to a finite stage as soon as its restriction to `W` does and `f` satisfies relative
descent of morphisms and of equalities along cofiltered limits of affine schemes. This is the
gluing step of the proof of Stacks 0CMX: the restriction to `W` is descended, the transition
isomorphism on `W ×_T W` is descended by relative descent of morphisms, its cocycle condition by
relative descent of equalities, and the resulting descent datum at a finite stage is effective
because `𝒳` is a stack.

## Main results

* `AlgebraicGeometry.Stack.GlueKernel.transition`: the transition morphisms of the descent datum,
  defined by a universal property from a single morphism over the fibre product `V ×_U V`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor CategoryTheory.Functor.IsFibered

universe v₁ v₂ u₁ u₂

namespace AlgebraicGeometry.Stack.GlueKernel

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

/-- Lifts compose, with the base morphism rewritten along an equality. -/
private lemma isHomLift_comp_of_eq {C : Type*} [Category C] {𝒳 : Type*} [Category 𝒳]
    {p : 𝒳 ⥤ C} {R S T : C} {a b c : 𝒳} {f : R ⟶ S} {g : S ⟶ T} {fg : R ⟶ T} {φ : a ⟶ b}
    {ψ : b ⟶ c} (h : f ≫ g = fg) (hφ : p.IsHomLift f φ) (hψ : p.IsHomLift g ψ) :
    p.IsHomLift fg (φ ≫ ψ) := by
  subst h
  infer_instance

/-- Precomposing `pullback.lift` with a morphism lifts the precomposed legs. -/
private lemma comp_pullback_lift {C : Type*} [Category C] {X Y Z W W' : C} {f : X ⟶ Z}
    {g : Y ⟶ Z} [HasPullback f g] (t : W' ⟶ W) {a : W ⟶ X} {b : W ⟶ Y} {h : a ≫ f = b ≫ g}
    {a' : W' ⟶ X} {b' : W' ⟶ Y} {h' : a' ≫ f = b' ≫ g} (ha : t ≫ a = a') (hb : t ≫ b = b') :
    t ≫ pullback.lift a b h = pullback.lift a' b' h' := by
  subst ha hb
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]

/-! ### The transition morphisms of a single morphism over the fibre square -/

section Kernel

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  (p : 𝒳 ⥤ C) [p.IsFibered]

/-- A *gluing kernel*: an object `X₀` over `V₀`, a morphism `τ : V ⟶ V₀`, a morphism `v : V ⟶ U`,
and an object `E` over the fibre square `V ×_U V` with two morphisms `κ, ĥ : E ⟶ X₀` over the two
composites `V ×_U V ⇉ V ⟶ V₀`. It is the datum from which the transition morphisms of a descent
datum along `v` are read off. -/
structure Kernel where
  /-- The base of the reference object. -/
  V₀ : C
  /-- The source of the covering morphism. -/
  V : C
  /-- The target of the covering morphism. -/
  U : C
  /-- The morphism to the base of the reference object. -/
  τ : V ⟶ V₀
  /-- The covering morphism. -/
  v : V ⟶ U
  /-- The reference object. -/
  X₀ : p.Fiber V₀
  /-- The object over the fibre square. -/
  E : 𝒳
  /-- The morphism over the first composite. -/
  κ : E ⟶ X₀.1
  /-- The morphism over the second composite. -/
  ĥ : E ⟶ X₀.1
  isHomLift_κ : p.IsHomLift (pullback.fst v v ≫ τ) κ
  isHomLift_ĥ : p.IsHomLift (pullback.snd v v ≫ τ) ĥ

attribute [instance] Kernel.isHomLift_κ Kernel.isHomLift_ĥ

variable {p} (hp : p.IsFiberedInGroupoids) (K : Kernel p)

/-- The lift into `E`, over `(e₁, e₂) : Z ⟶ V ×_U V`, of the chosen pullback of `X₀` along
`e₁ ≫ τ`, through the morphism `κ` over the first projection. -/
noncomputable def transitionLift {Z : C} (e₁ e₂ : Z ⟶ K.V) (h : e₁ ≫ K.v = e₂ ≫ K.v) :
    (pullbackFiber p K.X₀ (e₁ ≫ K.τ)).1 ⟶ K.E :=
  haveI := hp.isStronglyCartesian_homLift (pullback.fst K.v K.v ≫ K.τ) K.κ
  IsStronglyCartesian.map p (pullback.fst K.v K.v ≫ K.τ) K.κ (g := pullback.lift e₁ e₂ h)
    (f' := e₁ ≫ K.τ) (by rw [pullback.lift_fst_assoc])
    (IsPreFibered.pullbackMap K.X₀.2 (e₁ ≫ K.τ))

/-- The morphism `transitionLift` lies over `(e₁, e₂) : Z ⟶ V ×_U V`. -/
instance {Z : C} (e₁ e₂ : Z ⟶ K.V) (h : e₁ ≫ K.v = e₂ ≫ K.v) :
    p.IsHomLift (pullback.lift e₁ e₂ h) (transitionLift hp K e₁ e₂ h) := by
  have := hp.isStronglyCartesian_homLift (pullback.fst K.v K.v ≫ K.τ) K.κ
  unfold transitionLift
  infer_instance

/-- The composite of `transitionLift` with `κ` is the chosen pullback morphism of `X₀` along
`e₁ ≫ τ`. -/
@[reassoc (attr := simp)]
lemma transitionLift_fac {Z : C} (e₁ e₂ : Z ⟶ K.V) (h : e₁ ≫ K.v = e₂ ≫ K.v) :
    transitionLift hp K e₁ e₂ h ≫ K.κ = IsPreFibered.pullbackMap K.X₀.2 (e₁ ≫ K.τ) := by
  have := hp.isStronglyCartesian_homLift (pullback.fst K.v K.v ≫ K.τ) K.κ
  exact IsStronglyCartesian.fac p _ K.κ _ _

/-- A morphism into `E` over `(e₁, e₂)` whose composite with `κ` is the chosen pullback morphism
of `X₀` along `e₁ ≫ τ` is `transitionLift`. -/
lemma transitionLift_uniq {Z : C} (e₁ e₂ : Z ⟶ K.V) (h : e₁ ≫ K.v = e₂ ≫ K.v)
    (ψ : (pullbackFiber p K.X₀ (e₁ ≫ K.τ)).1 ⟶ K.E) [p.IsHomLift (pullback.lift e₁ e₂ h) ψ]
    (hψ : ψ ≫ K.κ = IsPreFibered.pullbackMap K.X₀.2 (e₁ ≫ K.τ)) :
    ψ = transitionLift hp K e₁ e₂ h := by
  have := hp.isStronglyCartesian_homLift (pullback.fst K.v K.v ≫ K.τ) K.κ
  exact IsStronglyCartesian.map_uniq p _ K.κ _ _ ψ hψ

/-- The composite of `transitionLift` with `ĥ` lies over `e₂ ≫ τ`. -/
instance {Z : C} (e₁ e₂ : Z ⟶ K.V) (h : e₁ ≫ K.v = e₂ ≫ K.v) :
    p.IsHomLift (e₂ ≫ K.τ) (transitionLift hp K e₁ e₂ h ≫ K.ĥ) := by
  have : p.IsHomLift (pullback.lift e₁ e₂ h ≫ pullback.snd K.v K.v ≫ K.τ)
      (transitionLift hp K e₁ e₂ h ≫ K.ĥ) := inferInstance
  rwa [pullback.lift_snd_assoc] at this

/-- The transition morphism `(e₁ ≫ τ)^* X₀ ⟶ (e₂ ≫ τ)^* X₀` of the fibre over `Z`, for a pair
`e₁, e₂ : Z ⟶ V` agreeing over `U`: the lift of the chosen pullback into `E` followed by `ĥ`,
read as a vertical morphism into the chosen pullback along `e₂ ≫ τ`. -/
noncomputable def transition {Z : C} (e₁ e₂ : Z ⟶ K.V) (h : e₁ ≫ K.v = e₂ ≫ K.v) :
    pullbackFiber p K.X₀ (e₁ ≫ K.τ) ⟶ pullbackFiber p K.X₀ (e₂ ≫ K.τ) :=
  toPullbackFiber p _ K.X₀ (e₂ ≫ K.τ) (transitionLift hp K e₁ e₂ h ≫ K.ĥ)

/-- The transition morphism followed by the chosen pullback morphism along `e₂ ≫ τ` is
`transitionLift` followed by `ĥ`. -/
@[reassoc (attr := simp)]
lemma transition_fac {Z : C} (e₁ e₂ : Z ⟶ K.V) (h : e₁ ≫ K.v = e₂ ≫ K.v) :
    Fiber.fiberInclusion.map (transition hp K e₁ e₂ h) ≫
        IsPreFibered.pullbackMap K.X₀.2 (e₂ ≫ K.τ) =
      transitionLift hp K e₁ e₂ h ≫ K.ĥ :=
  toPullbackFiber_fac p _ K.X₀ _ _

/-- **Naturality of the transition morphisms.** The transition morphism for `(g ≫ e₁, g ≫ e₂)` is
the base change along `g` of the one for `(e₁, e₂)`, after contracting the iterated chosen
pullbacks. -/
lemma transition_natural {Z Z' : C} (g : Z' ⟶ Z) (e₁ e₂ : Z ⟶ K.V) (h : e₁ ≫ K.v = e₂ ≫ K.v)
    (e₁' e₂' : Z' ⟶ K.V) (h₁ : g ≫ e₁ = e₁') (h₂ : g ≫ e₂ = e₂')
    (h' : e₁' ≫ K.v = e₂' ≫ K.v) :
    (pullbackFiberCompIso' K.X₀ (e₁ ≫ K.τ) g (e₁' ≫ K.τ)
        (by rw [← h₁, Category.assoc])).inv ≫
      pullbackFiberHom (transition hp K e₁ e₂ h) g ≫
      (pullbackFiberCompIso' K.X₀ (e₂ ≫ K.τ) g (e₂' ≫ K.τ)
        (by rw [← h₂, Category.assoc])).hom =
    transition hp K e₁' e₂' h' := by
  subst h₁ h₂
  refine fiber_hom_ext_of_cartesian ((g ≫ e₂) ≫ K.τ) (IsPreFibered.pullbackMap K.X₀.2 _)
    (IsPreFibered.pullbackMap.IsCartesian _ _) _ _ ?_
  simp only [Functor.map_comp, Category.assoc, pullbackFiberCompIso'_hom_fac,
    pullbackFiberHom_fac_assoc, transition_fac]
  have i₁ : p.IsHomLift (𝟙 Z') (Fiber.fiberInclusion.map (pullbackFiberCompIso' K.X₀
      (e₁ ≫ K.τ) g ((g ≫ e₁) ≫ K.τ) (by rw [Category.assoc])).inv) := inferInstance
  have i₂ : p.IsHomLift g
      (IsPreFibered.pullbackMap (pullbackFiber p K.X₀ (e₁ ≫ K.τ)).2 g) :=
    (IsPreFibered.pullbackMap.IsCartesian _ g).toIsHomLift
  have i₃ : p.IsHomLift (pullback.lift e₁ e₂ h) (transitionLift hp K e₁ e₂ h) :=
    inferInstance
  have i₁₂₃ : p.IsHomLift (pullback.lift (g ≫ e₁) (g ≫ e₂) h')
      (Fiber.fiberInclusion.map (pullbackFiberCompIso' K.X₀
        (e₁ ≫ K.τ) g ((g ≫ e₁) ≫ K.τ) (by rw [Category.assoc])).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p K.X₀ (e₁ ≫ K.τ)).2 g ≫
          transitionLift hp K e₁ e₂ h) :=
    isHomLift_comp_of_eq (Category.id_comp _) i₁
      (isHomLift_comp_of_eq (comp_pullback_lift g rfl rfl) i₂ i₃)
  have hψκ : (Fiber.fiberInclusion.map (pullbackFiberCompIso' K.X₀
        (e₁ ≫ K.τ) g ((g ≫ e₁) ≫ K.τ) (by rw [Category.assoc])).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p K.X₀ (e₁ ≫ K.τ)).2 g ≫
          transitionLift hp K e₁ e₂ h) ≫ K.κ =
      IsPreFibered.pullbackMap K.X₀.2 ((g ≫ e₁) ≫ K.τ) := by
    simp only [Category.assoc, transitionLift_fac, pullbackFiberCompIso'_inv_fac]
  rw [← @transitionLift_uniq _ _ _ _ _ _ _ hp K _ (g ≫ e₁) (g ≫ e₂) h' _ i₁₂₃ hψκ]
  simp only [Category.assoc]

/-- The image of a transition morphism under a functor is compatible with a morphism out of the
image of `X₀` which coequalizes the images of `κ` and `ĥ`. -/
@[reassoc]
lemma map_transition {𝒴 : Type*} [Category 𝒴] (F : 𝒳 ⥤ 𝒴) {Y : 𝒴} (γ₀ : F.obj K.X₀.1 ⟶ Y)
    (hF : F.map K.ĥ ≫ γ₀ = F.map K.κ ≫ γ₀) {Z : C} (e₁ e₂ : Z ⟶ K.V)
    (h : e₁ ≫ K.v = e₂ ≫ K.v) :
    F.map (Fiber.fiberInclusion.map (transition hp K e₁ e₂ h)) ≫
        F.map (IsPreFibered.pullbackMap K.X₀.2 (e₂ ≫ K.τ)) ≫ γ₀ =
      F.map (IsPreFibered.pullbackMap K.X₀.2 (e₁ ≫ K.τ)) ≫ γ₀ := by
  rw [← F.map_comp_assoc, transition_fac, F.map_comp_assoc, hF, ← F.map_comp_assoc,
    transitionLift_fac]

/-- The transition morphisms compose after base change along `g` as soon as their base changes
along `g` compose. -/
lemma transition_comp_of_pullbackFiberHom {Z Y : C} (r₁ r₂ r₃ : Z ⟶ K.V)
    (h₁₂ : r₁ ≫ K.v = r₂ ≫ K.v) (h₂₃ : r₂ ≫ K.v = r₃ ≫ K.v) (h₁₃ : r₁ ≫ K.v = r₃ ≫ K.v)
    (g : Y ⟶ Z) (e₁ e₂ e₃ : Y ⟶ K.V) (he₁ : g ≫ r₁ = e₁) (he₂ : g ≫ r₂ = e₂)
    (he₃ : g ≫ r₃ = e₃) (h'₁₂ : e₁ ≫ K.v = e₂ ≫ K.v) (h'₂₃ : e₂ ≫ K.v = e₃ ≫ K.v)
    (h'₁₃ : e₁ ≫ K.v = e₃ ≫ K.v)
    (hg : pullbackFiberHom (transition hp K r₁ r₂ h₁₂ ≫ transition hp K r₂ r₃ h₂₃) g =
      pullbackFiberHom (transition hp K r₁ r₃ h₁₃) g) :
    transition hp K e₁ e₂ h'₁₂ ≫ transition hp K e₂ e₃ h'₂₃ = transition hp K e₁ e₃ h'₁₃ := by
  rw [← transition_natural hp K g r₁ r₂ h₁₂ e₁ e₂ he₁ he₂ h'₁₂,
    ← transition_natural hp K g r₂ r₃ h₂₃ e₂ e₃ he₂ he₃ h'₂₃,
    ← transition_natural hp K g r₁ r₃ h₁₃ e₁ e₃ he₁ he₃ h'₁₃, ← hg, pullbackFiberHom_comp]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- The transition morphism of a pair `(e', e')` with `e' = g ≫ e` is the identity as soon as the
base change along `g` of the one of `(e, e)` is. -/
lemma transition_self_of_pullbackFiberHom {Z Y : C} (e : Z ⟶ K.V) (g : Y ⟶ Z) (e' : Y ⟶ K.V)
    (he' : g ≫ e = e') (hg : pullbackFiberHom (transition hp K e e rfl) g = 𝟙 _) :
    transition hp K e' e' rfl = 𝟙 _ := by
  rw [← transition_natural hp K g e e rfl e' e' he' he' rfl, hg]
  simp

end Kernel

/-! ### Equality of base changes from equality along a lift -/

section BaseChangeEq

variable {C : Type u₁} [Category.{v₁} C] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {p : 𝒳 ⥤ C} [p.IsFibered] (hp : p.IsFiberedInGroupoids)

include hp in
/-- Two morphisms of a fibre which agree after precomposition with a lift `d` over `ς` have the
same base change along every morphism factoring through `ς`. -/
lemma pullbackFiberHom_eq_of_comp_eq {W Z Y : C} {y y' : p.Fiber W} (m m' : y ⟶ y') {b : 𝒳}
    (ς : Z ⟶ W) (d : b ⟶ y.1) [p.IsHomLift ς d]
    (hd : d ≫ Fiber.fiberInclusion.map m = d ≫ Fiber.fiberInclusion.map m') (g : Y ⟶ Z) :
    pullbackFiberHom m (g ≫ ς) = pullbackFiberHom m' (g ≫ ς) := by
  have := hp.isStronglyCartesian_homLift ς d
  set ω := IsStronglyCartesian.map p ς d (g := g) rfl (IsPreFibered.pullbackMap y.2 (g ≫ ς))
    with hω
  have hωd : ω ≫ d = IsPreFibered.pullbackMap y.2 (g ≫ ς) := IsStronglyCartesian.fac p ς d _ _
  refine pullbackFiberHom_uniq m' (g ≫ ς) _ ?_
  rw [pullbackFiberHom_fac, ← hωd, Category.assoc, Category.assoc, hd]

end BaseChangeEq

/-! ### The kernel at the limit -/

section Limit

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {p : 𝒳 ⥤ C} [p.IsFibered] (hp : p.IsFiberedInGroupoids)

omit [p.IsFibered] [HasPullbacks C] in
/-- A lift of a morphism of the base is a lift of every equal morphism of the base. -/
lemma isHomLift_of_eq {R S : C} {a b : 𝒳} {f f' : R ⟶ S} (φ : a ⟶ b) (h : f = f')
    [p.IsHomLift f φ] : p.IsHomLift f' φ := by
  subst h
  infer_instance

omit [HasPullbacks C] [p.IsFibered] in
/-- A lift of a morphism of the base is a lift of every equal morphism, with the lift passed
explicitly. -/
lemma isHomLift_of_eq' {R S : C} {a b : 𝒳} {f f' : R ⟶ S} {φ : a ⟶ b} (h : f = f')
    (hφ : p.IsHomLift f φ) : p.IsHomLift f' φ := by
  subst h
  exact hφ

omit [HasPullbacks C] [p.IsFibered] in
include hp in
/-- The lift through a lift in a category fibred in groupoids, with the lifts passed
explicitly. -/
lemma exists_lift' {R S R' : C} {a b a' : 𝒳} {f : R ⟶ S} {φ : a ⟶ b} (hφ : p.IsHomLift f φ)
    (g : R' ⟶ R) {f' : R' ⟶ S} (hf' : f' = g ≫ f) {φ' : a' ⟶ b} (hφ' : p.IsHomLift f' φ') :
    ∃ ψ : a' ⟶ a, p.IsHomLift g ψ ∧ ψ ≫ φ = φ' :=
  have := hp.isStronglyCartesian_homLift f φ
  ⟨IsStronglyCartesian.map p f φ hf' φ', inferInstance, IsStronglyCartesian.fac p f φ hf' φ'⟩

omit [HasPullbacks C] [p.IsFibered] in
include hp in
/-- Morphisms into a lift in a category fibred in groupoids are determined by their composites
with it, with the lifts passed explicitly. -/
lemma ext' {R S R' : C} {a b a' : 𝒳} {f : R ⟶ S} {φ : a ⟶ b} (hφ : p.IsHomLift f φ)
    (g : R' ⟶ R) {ψ ψ' : a' ⟶ a} (h₁ : p.IsHomLift g ψ) (h₂ : p.IsHomLift g ψ')
    (h : ψ ≫ φ = ψ' ≫ φ) : ψ = ψ' :=
  have := hp.isStronglyCartesian_homLift f φ
  @IsStronglyCartesian.ext _ _ _ _ p _ _ _ _ f φ _ _ _ g ψ ψ' h₁ h₂ h

omit [HasPullbacks C] [p.IsFibered] in
/-- The lift through a strongly cartesian morphism, as an existence statement. -/
lemma exists_lift_of_isStronglyCartesian {R S R' : C} {a b a' : 𝒳} (f : R ⟶ S) (φ : a ⟶ b)
    [p.IsStronglyCartesian f φ] (g : R' ⟶ R) {f' : R' ⟶ S} (hf' : f' = g ≫ f) (φ' : a' ⟶ b)
    [p.IsHomLift f' φ'] : ∃ ψ : a' ⟶ a, p.IsHomLift g ψ ∧ ψ ≫ φ = φ' :=
  ⟨IsStronglyCartesian.map p f φ hf' φ', inferInstance, IsStronglyCartesian.fac p f φ hf' φ'⟩

variable (K : Kernel p)

/-- The restriction of a gluing kernel to the limit: an object `x` over `T`, its pullback `xW` to
`W` and the lift `ε₀ : xW ⟶ X₀`, the pullback `x₂` of `x` to `W ×_T W` with its two lifts `θ₁, θ₂`
to `xW`, and a lift `ε : x₂ ⟶ E` over the leg `W ×_T W ⟶ V ×_U V` along which `κ` and `ĥ` become
the two composites `x₂ ⇉ xW ⟶ X₀`. -/
structure LimitData where
  /-- The limit. -/
  T : C
  /-- The covering of the limit. -/
  W : C
  /-- The covering morphism of the limit. -/
  vT : W ⟶ T
  /-- The leg from the covering of the limit to the covering of the stage. -/
  ℓ : W ⟶ K.V
  /-- The leg from the limit to the stage. -/
  πU : T ⟶ K.U
  hℓ : ℓ ≫ K.v = vT ≫ πU
  /-- The object over the limit. -/
  x : 𝒳
  /-- Its pullback to the covering of the limit. -/
  xW : 𝒳
  /-- The pullback morphism. -/
  ρ : xW ⟶ x
  isHomLift_ρ : p.IsHomLift vT ρ
  /-- The comparison of the pullback with the reference object. -/
  ε₀ : xW ⟶ K.X₀.1
  isHomLift_ε₀ : p.IsHomLift (ℓ ≫ K.τ) ε₀
  /-- The pullback of `x` to the fibre square of the covering of the limit. -/
  x₂ : 𝒳
  /-- Its pullback morphism. -/
  ρ₂ : x₂ ⟶ x
  isHomLift_ρ₂ : p.IsHomLift (pullback.fst vT vT ≫ vT) ρ₂
  /-- The lift to `xW` over the first projection. -/
  θ₁ : x₂ ⟶ xW
  /-- The lift to `xW` over the second projection. -/
  θ₂ : x₂ ⟶ xW
  isHomLift_θ₁ : p.IsHomLift (pullback.fst vT vT) θ₁
  isHomLift_θ₂ : p.IsHomLift (pullback.snd vT vT) θ₂
  hθ₁ : θ₁ ≫ ρ = ρ₂
  hθ₂ : θ₂ ≫ ρ = ρ₂
  /-- The lift to `E`. -/
  ε : x₂ ⟶ K.E
  isHomLift_ε : p.IsHomLift
    (pullback.lift (f := K.v) (g := K.v) (pullback.fst vT vT ≫ ℓ) (pullback.snd vT vT ≫ ℓ)
    (by rw [Category.assoc, Category.assoc, hℓ, pullback.condition_assoc])) ε
  hεκ : ε ≫ K.κ = θ₁ ≫ ε₀
  hεĥ : ε ≫ K.ĥ = θ₂ ≫ ε₀

attribute [instance] LimitData.isHomLift_ρ LimitData.isHomLift_ε₀ LimitData.isHomLift_ρ₂
  LimitData.isHomLift_θ₁ LimitData.isHomLift_θ₂ LimitData.isHomLift_ε

variable {K} (L : LimitData K)

omit [p.IsFibered] in
include hp in
/-- **The kernel at the limit is the canonical transport.** A lift `λ` into `E`, over the pair
`(g₁ ≫ ℓ, g₂ ≫ ℓ)` for `g₁, g₂ : Z ⟶ W` agreeing over `T`, whose composite with `κ` is `ζ ≫ ε₀`
for a lift `ζ` to `xW` over `g₁`, has composite with `ĥ` equal to `ζ' ≫ ε₀`, where `ζ'` is the lift
to `xW` over `g₂` with the same image in `x`. -/
lemma limit_transitionLift {Z : C} (g₁ g₂ : Z ⟶ L.W) (hg : g₁ ≫ L.vT = g₂ ≫ L.vT) {A : 𝒳}
    (ζ ζ' : A ⟶ L.xW) [p.IsHomLift g₁ ζ] [p.IsHomLift g₂ ζ'] (hζ : ζ ≫ L.ρ = ζ' ≫ L.ρ)
    (lam : A ⟶ K.E)
    [p.IsHomLift (pullback.lift (f := K.v) (g := K.v) (g₁ ≫ L.ℓ) (g₂ ≫ L.ℓ)
      (by rw [Category.assoc, Category.assoc, L.hℓ, reassoc_of% hg])) lam]
    (hlam : lam ≫ K.κ = ζ ≫ L.ε₀) : lam ≫ K.ĥ = ζ' ≫ L.ε₀ := by
  have := hp.isStronglyCartesian_homLift (pullback.fst L.vT L.vT ≫ L.vT) L.ρ₂
  have := hp.isStronglyCartesian_homLift L.vT L.ρ
  have := hp.isStronglyCartesian_homLift (pullback.fst K.v K.v ≫ K.τ) K.κ
  let G : Z ⟶ pullback L.vT L.vT := pullback.lift g₁ g₂ hg
  let ξ : A ⟶ L.x₂ := IsStronglyCartesian.map p (pullback.fst L.vT L.vT ≫ L.vT) L.ρ₂ (g := G)
    (f' := g₁ ≫ L.vT) (by rw [pullback.lift_fst_assoc]) (ζ ≫ L.ρ)
  have hξ : ξ ≫ L.ρ₂ = ζ ≫ L.ρ := IsStronglyCartesian.fac p _ L.ρ₂ _ _
  have iξθ₁ : p.IsHomLift g₁ (ξ ≫ L.θ₁) :=
    isHomLift_of_eq (ξ ≫ L.θ₁) (pullback.lift_fst g₁ g₂ hg)
  have iξθ₂ : p.IsHomLift g₂ (ξ ≫ L.θ₂) :=
    isHomLift_of_eq (ξ ≫ L.θ₂) (pullback.lift_snd g₁ g₂ hg)
  have hξθ₁ : ξ ≫ L.θ₁ = ζ :=
    IsStronglyCartesian.ext p L.vT L.ρ g₁ (by rw [Category.assoc, L.hθ₁, hξ])
  have hξθ₂ : ξ ≫ L.θ₂ = ζ' :=
    IsStronglyCartesian.ext p L.vT L.ρ g₂ (by rw [Category.assoc, L.hθ₂, hξ, hζ])
  have iξε : p.IsHomLift (pullback.lift (f := K.v) (g := K.v) (g₁ ≫ L.ℓ) (g₂ ≫ L.ℓ)
      (by rw [Category.assoc, Category.assoc, L.hℓ, reassoc_of% hg])) (ξ ≫ L.ε) :=
    isHomLift_comp_of_eq (comp_pullback_lift G (pullback.lift_fst_assoc ..)
      (pullback.lift_snd_assoc ..)) inferInstance L.isHomLift_ε
  have hlamξ : lam = ξ ≫ L.ε :=
    IsStronglyCartesian.ext p (pullback.fst K.v K.v ≫ K.τ) K.κ
      (pullback.lift (f := K.v) (g := K.v) (g₁ ≫ L.ℓ) (g₂ ≫ L.ℓ) _)
      (by rw [hlam, Category.assoc, L.hεκ, ← Category.assoc, hξθ₁])
  rw [hlamξ, Category.assoc, L.hεĥ, ← Category.assoc, hξθ₂]

include hp in
/-- **The transition morphisms at the limit are the canonical transport.** -/
lemma limit_transition {Z Z' : C} (e₁ e₂ : Z ⟶ K.V) (he : e₁ ≫ K.v = e₂ ≫ K.v) (h : Z' ⟶ Z)
    (g₁ g₂ : Z' ⟶ L.W) (hg : g₁ ≫ L.vT = g₂ ≫ L.vT) (hg₁ : g₁ ≫ L.ℓ = h ≫ e₁)
    (hg₂ : g₂ ≫ L.ℓ = h ≫ e₂) {A : 𝒳} (δ : A ⟶ (pullbackFiber p K.X₀ (e₁ ≫ K.τ)).1)
    [p.IsHomLift h δ] (ζ ζ' : A ⟶ L.xW) [p.IsHomLift g₁ ζ] [p.IsHomLift g₂ ζ']
    (hζ : ζ ≫ L.ρ = ζ' ≫ L.ρ)
    (hδ : δ ≫ IsPreFibered.pullbackMap K.X₀.2 (e₁ ≫ K.τ) = ζ ≫ L.ε₀) :
    δ ≫ Fiber.fiberInclusion.map (transition hp K e₁ e₂ he) ≫
        IsPreFibered.pullbackMap K.X₀.2 (e₂ ≫ K.τ) = ζ' ≫ L.ε₀ := by
  rw [transition_fac, ← Category.assoc]
  have : p.IsHomLift (pullback.lift (f := K.v) (g := K.v) (g₁ ≫ L.ℓ) (g₂ ≫ L.ℓ)
      (by rw [Category.assoc, Category.assoc, L.hℓ, reassoc_of% hg]))
      (δ ≫ transitionLift hp K e₁ e₂ he) :=
    isHomLift_comp_of_eq (comp_pullback_lift h hg₁.symm hg₂.symm) inferInstance inferInstance
  exact limit_transitionLift hp L g₁ g₂ hg ζ ζ' hζ _
    (by rw [Category.assoc, transitionLift_fac, hδ])

end Limit

/-! ### The descent datum at a stage -/

section Stage

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.homMk CategoryTheory.Functor.pullbackFiberHom
  CategoryTheory.Functor.IsFibered.pullbackPseudofunctor
  CategoryTheory.Functor.IsFibered.pbObj CategoryTheory.Functor.IsFibered.pbMap
  CategoryTheory.Functor.IsFibered.fiberPullback
  CategoryTheory.Functor.IsFibered.fiberPullbackMap
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  CategoryTheory.Cat.str CategoryTheory.LocallyDiscrete.categoryStruct
  CategoryTheory.catToReflQuiver
  CategoryTheory.Functor.Fiber.fiberCategory Quiver.Hom.toLoc

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {p : 𝒳 ⥤ C} [p.IsFibered] (hp : p.IsFiberedInGroupoids) (K : Kernel p)
  {V' U' : C} (σ : V' ⟶ K.V) (v' : V' ⟶ U') (t : U' ⟶ K.U) (hσ : σ ≫ K.v = v' ≫ t)

include hσ in
/-- Morphisms `f₁, f₂ : Y ⟶ V'` agreeing over `U'` give morphisms `f₁ ≫ σ, f₂ ≫ σ : Y ⟶ V`
agreeing over `U`. -/
lemma stage_compat {Y : C} {f₁ f₂ : Y ⟶ V'} (h : f₁ ≫ v' = f₂ ≫ v') :
    (f₁ ≫ σ) ≫ K.v = (f₂ ≫ σ) ≫ K.v := by
  rw [Category.assoc, Category.assoc, hσ, reassoc_of% h]

/-- The object of the descent datum at the stage: the chosen pullback of `X₀` to `V'`. -/
noncomputable abbrev stageObj : p.Fiber V' := pullbackFiber p K.X₀ (σ ≫ K.τ)

/-- The chosen cartesian morphism from the pullback along `f` of the object at the stage to
`X₀`. -/
noncomputable abbrev stageMap {Y : C} (f : Y ⟶ V') :
    (pullbackFiber p (stageObj K σ) f).1 ⟶ K.X₀.1 :=
  IsPreFibered.pullbackMap (stageObj K σ).2 f ≫ IsPreFibered.pullbackMap K.X₀.2 (σ ≫ K.τ)

/-- The morphism `stageMap` is cartesian over `(f ≫ σ) ≫ τ`. -/
lemma stageMap_isCartesian {Y : C} (f : Y ⟶ V') :
    p.IsCartesian ((f ≫ σ) ≫ K.τ) (stageMap K σ f) :=
  isCartesian_pullbackMap_comp_pullbackMap K.X₀ (σ ≫ K.τ) f _ (by rw [Category.assoc])

/-- The transition morphisms of the descent datum at the stage. -/
noncomputable def stageHom {Y : C} (f₁ f₂ : Y ⟶ V') (h : f₁ ≫ v' = f₂ ≫ v') :
    pullbackFiber p (stageObj K σ) f₁ ⟶ pullbackFiber p (stageObj K σ) f₂ :=
  (pullbackFiberCompIso' K.X₀ (σ ≫ K.τ) f₁ ((f₁ ≫ σ) ≫ K.τ) (by rw [Category.assoc])).hom ≫
    transition hp K (f₁ ≫ σ) (f₂ ≫ σ) (stage_compat K σ v' t hσ h) ≫
    (pullbackFiberCompIso' K.X₀ (σ ≫ K.τ) f₂ ((f₂ ≫ σ) ≫ K.τ) (by rw [Category.assoc])).inv

/-- The lift into `E` that characterizes the transition morphism at the stage. -/
noncomputable def stageLift {Y : C} (f₁ f₂ : Y ⟶ V') (h : f₁ ≫ v' = f₂ ≫ v') :
    (pullbackFiber p (stageObj K σ) f₁).1 ⟶ K.E :=
  Fiber.fiberInclusion.map (pullbackFiberCompIso' K.X₀ (σ ≫ K.τ) f₁ ((f₁ ≫ σ) ≫ K.τ)
    (by rw [Category.assoc])).hom ≫
    transitionLift hp K (f₁ ≫ σ) (f₂ ≫ σ) (stage_compat K σ v' t hσ h)

/-- The composite of `stageLift` with `κ` is `stageMap` along `f₁`. -/
lemma stageLift_fac {Y : C} (f₁ f₂ : Y ⟶ V') (h : f₁ ≫ v' = f₂ ≫ v') :
    stageLift hp K σ v' t hσ f₁ f₂ h ≫ K.κ = stageMap K σ f₁ := by
  simp only [stageLift, Category.assoc, transitionLift_fac, pullbackFiberCompIso'_hom_fac]

/-- The morphism `stageLift` lies over `(f₁ ≫ σ, f₂ ≫ σ) : Y ⟶ V ×_U V`. -/
instance {Y : C} (f₁ f₂ : Y ⟶ V') (h : f₁ ≫ v' = f₂ ≫ v') :
    p.IsHomLift (pullback.lift (f₁ ≫ σ) (f₂ ≫ σ) (stage_compat K σ v' t hσ h))
      (stageLift hp K σ v' t hσ f₁ f₂ h) := by
  have : p.IsHomLift (𝟙 Y ≫ pullback.lift (f₁ ≫ σ) (f₂ ≫ σ) (stage_compat K σ v' t hσ h))
      (stageLift hp K σ v' t hσ f₁ f₂ h) := by
    unfold stageLift
    infer_instance
  rwa [Category.id_comp] at this

/-- The transition morphism at the stage followed by `stageMap` along `f₂` is `stageLift`
followed by `ĥ`. -/
@[reassoc]
lemma stageHom_fac {Y : C} (f₁ f₂ : Y ⟶ V') (h : f₁ ≫ v' = f₂ ≫ v') :
    Fiber.fiberInclusion.map (stageHom hp K σ v' t hσ f₁ f₂ h) ≫ stageMap K σ f₂ =
      stageLift hp K σ v' t hσ f₁ f₂ h ≫ K.ĥ := by
  simp only [stageHom, stageLift, Functor.map_comp, Category.assoc,
    pullbackFiberCompIso'_inv_fac, transition_fac]

/-- The transition morphisms at the stage are compatible with base change. -/
lemma stageHom_pullback {Y Y' : C} (g : Y' ⟶ Y) (f₁ f₂ : Y ⟶ V') (h : f₁ ≫ v' = f₂ ≫ v') :
    (pullbackFiberCompIso (stageObj K σ) f₁ g).inv ≫
        pullbackFiberHom (stageHom hp K σ v' t hσ f₁ f₂ h) g ≫
        (pullbackFiberCompIso (stageObj K σ) f₂ g).hom =
      stageHom hp K σ v' t hσ (g ≫ f₁) (g ≫ f₂) (by rw [Category.assoc, h, Category.assoc]) := by
  have hgh : (g ≫ f₁) ≫ v' = (g ≫ f₂) ≫ v' := by rw [Category.assoc, h, Category.assoc]
  have := stageMap_isCartesian K σ (g ≫ f₂)
  refine fiber_hom_ext_of_cartesian (((g ≫ f₂) ≫ σ) ≫ K.τ) (stageMap K σ (g ≫ f₂))
    inferInstance _ _ ?_
  rw [stageHom_fac]
  unfold stageMap
  simp only [Functor.map_comp, Category.assoc, pullbackFiberCompIso_hom_fac_assoc,
    pullbackFiberHom_fac_assoc]
  rw [← stageMap, stageHom_fac]
  -- the two lifts into `E`
  have := hp.isStronglyCartesian_homLift (pullback.fst K.v K.v ≫ K.τ) K.κ
  have i₁ : p.IsHomLift (pullback.lift ((g ≫ f₁) ≫ σ) ((g ≫ f₂) ≫ σ)
      (stage_compat K σ v' t hσ hgh))
      (Fiber.fiberInclusion.map (pullbackFiberCompIso (stageObj K σ) f₁ g).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p (stageObj K σ) f₁).2 g ≫
          stageLift hp K σ v' t hσ f₁ f₂ h) :=
    isHomLift_comp_of_eq (Category.id_comp _) inferInstance
      (isHomLift_comp_of_eq (comp_pullback_lift g (Category.assoc ..).symm
        (Category.assoc ..).symm) inferInstance inferInstance)
  have hl : Fiber.fiberInclusion.map (pullbackFiberCompIso (stageObj K σ) f₁ g).inv ≫
        IsPreFibered.pullbackMap (pullbackFiber p (stageObj K σ) f₁).2 g ≫
          stageLift hp K σ v' t hσ f₁ f₂ h =
      stageLift hp K σ v' t hσ (g ≫ f₁) (g ≫ f₂) hgh :=
    IsStronglyCartesian.ext p (pullback.fst K.v K.v ≫ K.τ) K.κ
      (pullback.lift ((g ≫ f₁) ≫ σ) ((g ≫ f₂) ≫ σ) (stage_compat K σ v' t hσ hgh))
      (by rw [Category.assoc, Category.assoc, stageLift_fac, stageLift_fac, stageMap,
        pullbackFiberCompIso_inv_fac_assoc])
  rw [reassoc_of% hl]

/-- The image of a transition morphism at the stage under a functor is compatible with a
morphism out of the image of `X₀` which coequalizes the images of `κ` and `ĥ`. -/
@[reassoc]
lemma map_stageHom {𝒴 : Type*} [Category 𝒴] (F : 𝒳 ⥤ 𝒴) {Y' : 𝒴} (γ₀ : F.obj K.X₀.1 ⟶ Y')
    (hF : F.map K.ĥ ≫ γ₀ = F.map K.κ ≫ γ₀) {Y : C} (f₁ f₂ : Y ⟶ V')
    (h : f₁ ≫ v' = f₂ ≫ v') :
    F.map (Fiber.fiberInclusion.map (stageHom hp K σ v' t hσ f₁ f₂ h)) ≫
        F.map (stageMap K σ f₂) ≫ γ₀ = F.map (stageMap K σ f₁) ≫ γ₀ := by
  rw [← F.map_comp_assoc, stageHom_fac, F.map_comp_assoc, hF, ← F.map_comp_assoc,
    stageLift_fac]

/-- The descent datum at the stage, relative to the single morphism `v'`. -/
noncomputable def stageDescentData
    (hself : ∀ ⦃Z : C⦄ (e : Z ⟶ V'), transition hp K (e ≫ σ) (e ≫ σ) rfl = 𝟙 _)
    (hcomp : ∀ ⦃Z : C⦄ (e₁ e₂ e₃ : Z ⟶ V') (h₁₂ : e₁ ≫ v' = e₂ ≫ v')
      (h₂₃ : e₂ ≫ v' = e₃ ≫ v') (h₁₃ : e₁ ≫ v' = e₃ ≫ v'),
      transition hp K (e₁ ≫ σ) (e₂ ≫ σ) (stage_compat K σ v' t hσ h₁₂) ≫
        transition hp K (e₂ ≫ σ) (e₃ ≫ σ) (stage_compat K σ v' t hσ h₂₃) =
      transition hp K (e₁ ≫ σ) (e₃ ≫ σ) (stage_compat K σ v' t hσ h₁₃)) :
    (pullbackPseudofunctor p).DescentData (fun _ : Unit => v') where
  obj _ := stageObj K σ
  hom Y q _ _ f₁ f₂ hf₁ hf₂ := stageHom hp K σ v' t hσ f₁ f₂ (hf₁.trans hf₂.symm)
  pullHom_hom Y' Y g q q' hq _ _ f₁ f₂ hf₁ hf₂ gf₁ gf₂ hgf₁ hgf₂ := by
    subst hgf₁ hgf₂
    exact (pullHom_eq p _ _ f₁ f₂ g _).trans (stageHom_pullback hp K σ v' t hσ g f₁ f₂ _)
  hom_self Y q _ g hg := by
    simp only [stageHom, hself, Category.id_comp, Iso.hom_inv_id]
    rfl
  hom_comp Y q _ _ _ f₁ f₂ f₃ hf₁ hf₂ hf₃ := by
    simp only [stageHom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% (hcomp f₁ f₂ f₃ (hf₁.trans hf₂.symm) (hf₂.trans hf₃.symm)
      (hf₁.trans hf₃.symm))]

/-- **Gluing at the stage.** When `𝒳` is a stack and `v'` covers, the descent datum at the stage
is effective: there are an object `x'` over `U'` and a morphism `ζ` from the object at the stage to
`x'` over `v'` which coequalizes the transition morphisms. -/
theorem exists_stageGlue {J : GrothendieckTopology C} (hpS : p.IsStack J)
    (hv' : Sieve.ofArrows (fun _ : Unit => V') (fun _ => v') ∈ J U')
    (hself : ∀ ⦃Z : C⦄ (e : Z ⟶ V'), transition hp K (e ≫ σ) (e ≫ σ) rfl = 𝟙 _)
    (hcomp : ∀ ⦃Z : C⦄ (e₁ e₂ e₃ : Z ⟶ V') (h₁₂ : e₁ ≫ v' = e₂ ≫ v')
      (h₂₃ : e₂ ≫ v' = e₃ ≫ v') (h₁₃ : e₁ ≫ v' = e₃ ≫ v'),
      transition hp K (e₁ ≫ σ) (e₂ ≫ σ) (stage_compat K σ v' t hσ h₁₂) ≫
        transition hp K (e₂ ≫ σ) (e₃ ≫ σ) (stage_compat K σ v' t hσ h₂₃) =
      transition hp K (e₁ ≫ σ) (e₃ ≫ σ) (stage_compat K σ v' t hσ h₁₃)) :
    ∃ (x' : p.Fiber U') (ζ : (stageObj K σ).1 ⟶ x'.1), p.IsHomLift v' ζ ∧
      ∀ ⦃Y : C⦄ (f₁ f₂ : Y ⟶ V') (h : f₁ ≫ v' = f₂ ≫ v'),
        IsPreFibered.pullbackMap (stageObj K σ).2 f₁ ≫ ζ =
          Fiber.fiberInclusion.map (stageHom hp K σ v' t hσ f₁ f₂ h) ≫
            IsPreFibered.pullbackMap (stageObj K σ).2 f₂ ≫ ζ := by
  have := isEquivalence_toDescentData_of_isStack p hpS (fun _ : Unit => v') hv'
  let D := stageDescentData hp K σ v' t hσ hself hcomp
  let L := (pullbackPseudofunctor p).toDescentData (fun _ : Unit => v')
  let x' : p.Fiber U' := L.objPreimage D
  let α : L.obj x' ≅ D := L.objObjPreimageIso D
  let a : stageObj K σ ⟶ pullbackFiber p x' v' := α.inv.hom ()
  refine ⟨x', Fiber.fiberInclusion.map a ≫ IsPreFibered.pullbackMap x'.2 v', ?_,
    fun Y f₁ f₂ h => ?_⟩
  · have : p.IsHomLift (𝟙 V' ≫ v')
        (Fiber.fiberInclusion.map a ≫ IsPreFibered.pullbackMap x'.2 v') := inferInstance
    rwa [Category.id_comp] at this
  · have hc := α.inv.comm (i₁ := ()) (i₂ := ()) (f₁ ≫ v') f₁ f₂ rfl h.symm
    rw [pullbackPseudofunctor_map_map, pullbackPseudofunctor_map_map,
      toDescentData_obj_hom p (fun _ : Unit => v') x' (i₁ := ()) (i₂ := ()) (f₁ ≫ v') f₁ f₂ rfl
        h.symm h] at hc
    have h2 : Fiber.fiberInclusion.map (pullbackFiberHom a f₁) ≫
        Fiber.fiberInclusion.map (pullbackFiberComparison x' f₁ f₂ h).hom =
        Fiber.fiberInclusion.map (stageHom hp K σ v' t hσ f₁ f₂ h) ≫
          Fiber.fiberInclusion.map (pullbackFiberHom a f₂) :=
      congrArg Subtype.val hc
    have h3 := h2 =≫
      (IsPreFibered.pullbackMap (pullbackFiber p x' v').2 f₂ ≫ IsPreFibered.pullbackMap x'.2 v')
    simp only [Category.assoc] at h3
    rw [pullbackFiberComparison_hom_fac, pullbackFiberHom_fac_assoc,
      pullbackFiberHom_fac_assoc] at h3
    exact h3

end Stage

/-! ### From the glued object to the descent of the given object -/

section Final

universe v₃ u₃

variable {C : Type u₁} [Category.{v₁} C] [HasPullbacks C] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {p : 𝒳 ⥤ C} {q : 𝒴 ⥤ C} [p.IsFibered] [q.IsFibered]
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (F : 𝒳 ⥤ 𝒴) (hFq : F ⋙ q = p)
  {J : GrothendieckTopology C}

include hFq hp hq in
/-- **The glued object descends the given one.** Given a gluing kernel and its restriction to
the limit, compatible with a morphism `γ₀ : F X₀ ⟶ Y` and with `γ : F x ⟶ Y`, and an object `x'`
glued at a stage from the kernel, the pullback of `x'` to the limit is isomorphic to `x`, and the
image of `x'` maps to `Y` compatibly with `γ`. -/
theorem exists_descent_of_stageGlue (hpS : p.IsStack J) (hqS : q.IsStack J) (K : Kernel p)
    (L : LimitData K) {Y : 𝒴} {YB : C} (t₀ : K.V₀ ⟶ YB) (γ₀ : F.obj K.X₀.1 ⟶ Y)
    (iγ₀ : q.IsHomLift t₀ γ₀) (hKF : F.map K.ĥ ≫ γ₀ = F.map K.κ ≫ γ₀)
    (πY : L.T ⟶ YB) (γ : F.obj L.x ⟶ Y) (iγ : q.IsHomLift πY γ)
    (hγ₀ : F.map L.ε₀ ≫ γ₀ = F.map L.ρ ≫ γ)
    {V' U' : C} (σ : V' ⟶ K.V) (v' : V' ⟶ U') (t : U' ⟶ K.U) (hσ : σ ≫ K.v = v' ≫ t)
    (x' : p.Fiber U') (ζ : (stageObj K σ).1 ⟶ x'.1) (iζ : p.IsHomLift v' ζ)
    (hζ : ∀ ⦃Y' : C⦄ (f₁ f₂ : Y' ⟶ V') (h : f₁ ≫ v' = f₂ ≫ v'),
      IsPreFibered.pullbackMap (stageObj K σ).2 f₁ ≫ ζ =
        Fiber.fiberInclusion.map (stageHom hp K σ v' t hσ f₁ f₂ h) ≫
          IsPreFibered.pullbackMap (stageObj K σ).2 f₂ ≫ ζ)
    (ℓ' : L.W ⟶ V') (hℓ' : ℓ' ≫ σ = L.ℓ) (π' : L.T ⟶ U') (hπ' : ℓ' ≫ v' = L.vT ≫ π')
    (hvU : Sieve.ofArrows (fun _ : Unit => V') (fun _ => v') ∈ J U')
    (hvT : Sieve.ofArrows (fun _ : Unit => L.W) (fun _ => L.vT) ∈ J L.T)
    (g' : U' ⟶ YB) (hg' : (σ ≫ K.τ) ≫ t₀ = v' ≫ g') (hπg : π' ≫ g' = πY)
    (hx : p.obj L.x = L.T) :
    ∃ (xU : p.Fiber L.T) (δ : xU.1 ⟶ x'.1) (β : xU.1 ⟶ L.x) (γ' : F.obj x'.1 ⟶ Y),
      p.IsHomLift π' δ ∧ p.IsHomLift (𝟙 L.T) β ∧ q.IsHomLift g' γ' ∧
        F.map δ ≫ γ' = F.map β ≫ γ := by
  classical
  let O := stageObj K σ
  have iFζ : q.IsHomLift v' (F.map ζ) :=
    CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFq _ _ iζ
  have iπO : p.IsHomLift (σ ≫ K.τ) (IsPreFibered.pullbackMap K.X₀.2 (σ ≫ K.τ)) :=
    (IsPreFibered.pullbackMap.IsCartesian K.X₀.2 (σ ≫ K.τ)).toIsHomLift
  have iψ : q.IsHomLift (v' ≫ g') (F.map (IsPreFibered.pullbackMap K.X₀.2 (σ ≫ K.τ)) ≫ γ₀) :=
    isHomLift_comp_of_eq hg'
      (CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFq _ _ iπO) iγ₀
  have hYB : q.obj Y = YB := IsHomLift.codomain_eq q t₀ γ₀
  -- the image of a pullback of the object at the stage
  have iFπ : ∀ {Z : C} (e : Z ⟶ V'), q.IsHomLift e
      (F.map (IsPreFibered.pullbackMap O.2 e)) := fun e =>
    CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFq _ _
      (IsPreFibered.pullbackMap.IsCartesian O.2 e).toIsHomLift
  -- the morphism `γ'`
  have hψ : ∀ ⦃Z : C⦄ (e₁ e₂ : Z ⟶ V'), e₁ ≫ v' = e₂ ≫ v' → ∀ ⦃A : 𝒴⦄
      (a₁ a₂ : A ⟶ F.obj O.1), q.IsHomLift e₁ a₁ → q.IsHomLift e₂ a₂ →
      a₁ ≫ F.map ζ = a₂ ≫ F.map ζ →
      a₁ ≫ F.map (IsPreFibered.pullbackMap K.X₀.2 (σ ≫ K.τ)) ≫ γ₀ =
        a₂ ≫ F.map (IsPreFibered.pullbackMap K.X₀.2 (σ ≫ K.τ)) ≫ γ₀ := by
    intro Z e₁ e₂ he A a₁ a₂ ia₁ ia₂ ha
    obtain ⟨ι₁, iι₁, hι₁⟩ := exists_lift' hq (iFπ e₁) (𝟙 Z) (Category.id_comp _).symm ia₁
    have iH := (stageHom hp K σ v' t hσ e₁ e₂ he).2
    have iR : q.IsHomLift e₂ (ι₁ ≫ F.map (Fiber.fiberInclusion.map
        (stageHom hp K σ v' t hσ e₁ e₂ he) ≫ IsPreFibered.pullbackMap O.2 e₂)) :=
      isHomLift_comp_of_eq (by rw [Category.id_comp, Category.id_comp]) iι₁
          (CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFq _ _
            (isHomLift_comp_of_eq rfl iH
              (IsPreFibered.pullbackMap.IsCartesian O.2 e₂).toIsHomLift))
    have ha₂ : a₂ = ι₁ ≫ F.map (Fiber.fiberInclusion.map
        (stageHom hp K σ v' t hσ e₁ e₂ he) ≫ IsPreFibered.pullbackMap O.2 e₂) := by
      refine ext' hq iFζ e₂ ia₂ iR ?_
      rw [← ha, ← hι₁, Category.assoc, Category.assoc, ← F.map_comp, ← F.map_comp,
        hζ e₁ e₂ he, Category.assoc]
    have e₁' : F.map (IsPreFibered.pullbackMap O.2 e₁) ≫
        F.map (IsPreFibered.pullbackMap K.X₀.2 (σ ≫ K.τ)) ≫ γ₀ =
          F.map (stageMap K σ e₁) ≫ γ₀ := by
      rw [← F.map_comp_assoc]
    have e₂' : F.map (Fiber.fiberInclusion.map (stageHom hp K σ v' t hσ e₁ e₂ he) ≫
        IsPreFibered.pullbackMap O.2 e₂) ≫
          F.map (IsPreFibered.pullbackMap K.X₀.2 (σ ≫ K.τ)) ≫ γ₀ =
          F.map (stageMap K σ e₁) ≫ γ₀ := by
      rw [← F.map_comp_assoc, Category.assoc]
      show F.map (Fiber.fiberInclusion.map (stageHom hp K σ v' t hσ e₁ e₂ he) ≫
        stageMap K σ e₂) ≫ γ₀ = _
      rw [F.map_comp_assoc, map_stageHom hp K σ v' t hσ F γ₀ hKF e₁ e₂ he]
    rw [ha₂, ← hι₁, Category.assoc, Category.assoc, e₁', e₂']
  let x'' : q.Fiber U' := ⟨F.obj x'.1, (Functor.congr_obj hFq x'.1).trans x'.2⟩
  have := iFζ
  have := iψ
  obtain ⟨γ', iγ', hγ'⟩ := exists_comp_eq_of_singleCover q hq hvU (x := x'')
    (fun y => hqS.isMorSheaf U' x'' y) (F.map ζ) g' hYB _ hψ
  -- the pullback of the glued object to the limit, and its comparison with `x`
  let xU : p.Fiber L.T := pullbackFiber p x' π'
  have iδ : p.IsHomLift π' (IsPreFibered.pullbackMap x'.2 π') :=
    (IsPreFibered.pullbackMap.IsCartesian x'.2 π').toIsHomLift
  let OT : p.Fiber L.W := pullbackFiber p xU L.vT
  have iζT : p.IsHomLift L.vT (IsPreFibered.pullbackMap xU.2 L.vT) :=
    (IsPreFibered.pullbackMap.IsCartesian xU.2 L.vT).toIsHomLift
  obtain ⟨κT, iκT, hκT⟩ := exists_lift' hp iζ ℓ' hπ'.symm
    (isHomLift_comp_of_eq rfl iζT iδ)
  have hℓτ : ℓ' ≫ σ ≫ K.τ = 𝟙 _ ≫ L.ℓ ≫ K.τ := by rw [Category.id_comp, ← hℓ',
    Category.assoc]
  obtain ⟨ω, iω, hω⟩ := exists_lift' hp L.isHomLift_ε₀ (𝟙 _) hℓτ
    (isHomLift_comp_of_eq rfl iκT iπO)
  have iψT : p.IsHomLift (L.vT ≫ 𝟙 L.T) (ω ≫ L.ρ) :=
    isHomLift_comp_of_eq (by rw [Category.id_comp, Category.comp_id]) iω L.isHomLift_ρ
  have hψT : ∀ ⦃Z : C⦄ (e₁ e₂ : Z ⟶ L.W), e₁ ≫ L.vT = e₂ ≫ L.vT → ∀ ⦃A : 𝒳⦄
      (a₁ a₂ : A ⟶ OT.1), p.IsHomLift e₁ a₁ → p.IsHomLift e₂ a₂ →
      a₁ ≫ IsPreFibered.pullbackMap xU.2 L.vT = a₂ ≫ IsPreFibered.pullbackMap xU.2 L.vT →
      a₁ ≫ ω ≫ L.ρ = a₂ ≫ ω ≫ L.ρ := by
    intro Z e₁ e₂ he A a₁ a₂ ia₁ ia₂ ha
    have he' : (e₁ ≫ ℓ') ≫ v' = (e₂ ≫ ℓ') ≫ v' := by
      rw [Category.assoc, Category.assoc, hπ', reassoc_of% he]
    have ib₁ : p.IsHomLift (e₁ ≫ ℓ') (a₁ ≫ κT) :=
      isHomLift_comp_of_eq rfl ia₁ iκT
    have ib₂ : p.IsHomLift (e₂ ≫ ℓ') (a₂ ≫ κT) :=
      isHomLift_comp_of_eq rfl ia₂ iκT
    obtain ⟨ι₁, iι₁, hι₁⟩ := exists_lift' hp
      (IsPreFibered.pullbackMap.IsCartesian O.2 (e₁ ≫ ℓ')).toIsHomLift (𝟙 Z)
      (Category.id_comp _).symm ib₁
    have iH := (stageHom hp K σ v' t hσ (e₁ ≫ ℓ') (e₂ ≫ ℓ') he').2
    have iR : p.IsHomLift (e₂ ≫ ℓ') (ι₁ ≫ Fiber.fiberInclusion.map
        (stageHom hp K σ v' t hσ (e₁ ≫ ℓ') (e₂ ≫ ℓ') he') ≫
          IsPreFibered.pullbackMap O.2 (e₂ ≫ ℓ')) :=
      isHomLift_comp_of_eq (by rw [Category.id_comp, Category.id_comp]) iι₁
        (isHomLift_comp_of_eq rfl iH
          (IsPreFibered.pullbackMap.IsCartesian O.2 (e₂ ≫ ℓ')).toIsHomLift)
    have hb₂ : a₂ ≫ κT = ι₁ ≫ Fiber.fiberInclusion.map
        (stageHom hp K σ v' t hσ (e₁ ≫ ℓ') (e₂ ≫ ℓ') he') ≫
          IsPreFibered.pullbackMap O.2 (e₂ ≫ ℓ') := by
      refine ext' hp iζ (e₂ ≫ ℓ') ib₂ iR ?_
      rw [Category.assoc, hκT, ← reassoc_of% ha, ← hκT, ← Category.assoc, ← hι₁,
        Category.assoc, Category.assoc, Category.assoc, hζ (e₁ ≫ ℓ') (e₂ ≫ ℓ') he']
    -- the lift through `ρ` of `a₁ ≫ ω ≫ ρ` over `e₂`
    obtain ⟨ξ, iξ, hξ⟩ := exists_lift' hp L.isHomLift_ρ e₂ he
      (isHomLift_comp_of_eq (by rw [Category.comp_id])
        (isHomLift_comp_of_eq rfl ia₁ iω) L.isHomLift_ρ)
    have hbase : 𝟙 Z ≫ pullback.lift ((e₁ ≫ ℓ') ≫ σ) ((e₂ ≫ ℓ') ≫ σ)
        (stage_compat K σ v' t hσ he') = pullback.lift (f := K.v) (g := K.v) (e₁ ≫ L.ℓ)
          (e₂ ≫ L.ℓ) (by rw [Category.assoc, Category.assoc, L.hℓ, reassoc_of% he]) :=
      comp_pullback_lift (𝟙 Z) (by rw [Category.id_comp, Category.assoc, hℓ'])
        (by rw [Category.id_comp, Category.assoc, hℓ'])
    have ilam : p.IsHomLift (pullback.lift (f := K.v) (g := K.v) (e₁ ≫ L.ℓ) (e₂ ≫ L.ℓ)
        (by rw [Category.assoc, Category.assoc, L.hℓ, reassoc_of% he]))
        (ι₁ ≫ stageLift hp K σ v' t hσ (e₁ ≫ ℓ') (e₂ ≫ ℓ') he') :=
      isHomLift_comp_of_eq hbase iι₁ inferInstance
    have := isHomLift_comp_of_eq rfl ia₁ iω
    have iω₁ : p.IsHomLift e₁ (a₁ ≫ ω) :=
      isHomLift_comp_of_eq (Category.comp_id e₁) ia₁ iω
    have := iω₁
    have := iξ
    have hl := limit_transitionLift hp L e₁ e₂ he (a₁ ≫ ω) ξ (by rw [hξ, Category.assoc])
      (ι₁ ≫ stageLift hp K σ v' t hσ (e₁ ≫ ℓ') (e₂ ≫ ℓ') he')
      (by rw [Category.assoc, stageLift_fac, ← Category.assoc, hι₁, Category.assoc,
        Category.assoc, hω])
    have hω₂ : a₂ ≫ ω = ξ := by
      refine ext' hp L.isHomLift_ε₀ e₂
        (isHomLift_comp_of_eq (Category.comp_id e₂) ia₂ iω) iξ ?_
      rw [Category.assoc, hω, ← Category.assoc, hb₂, ← hl, Category.assoc, Category.assoc,
        stageHom_fac, Category.assoc]
    rw [← Category.assoc a₂, hω₂, hξ, Category.assoc]
  obtain ⟨β, iβ, hβ⟩ := exists_comp_eq_of_singleCover p hp hvT (x := xU)
    (fun y => hpS.isMorSheaf L.T xU y) (IsPreFibered.pullbackMap xU.2 L.vT) (𝟙 L.T) hx _
    (by have := iψT; exact hψT)
  -- the compatibility with `γ`, checked on the covering of the limit
  refine ⟨xU, IsPreFibered.pullbackMap x'.2 π', β, γ', iδ, iβ, iγ', ?_⟩
  let xU'' : q.Fiber L.T := ⟨F.obj xU.1, (Functor.congr_obj hFq xU.1).trans xU.2⟩
  have iFζT : q.IsHomLift L.vT (F.map (IsPreFibered.pullbackMap xU.2 L.vT)) :=
    CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFq _ _ iζT
  have iφ₁ : q.IsHomLift πY (F.map (IsPreFibered.pullbackMap x'.2 π') ≫ γ') :=
    isHomLift_comp_of_eq hπg
      (CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFq _ _ iδ) iγ'
  have iφ₂ : q.IsHomLift πY (F.map β ≫ γ) :=
    isHomLift_comp_of_eq (Category.id_comp πY)
      (CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFq _ _ iβ) iγ
  have := iFζT
  have := iφ₁
  have := iφ₂
  refine eq_of_comp_eq_of_singleCover q hq hvT (x := xU'')
    (fun y => hqS.isMorSheaf L.T xU'' y) (F.map (IsPreFibered.pullbackMap xU.2 L.vT)) πY
    _ _ ?_
  rw [← F.map_comp_assoc, ← hκT, F.map_comp_assoc, hγ', ← F.map_comp_assoc, ← hω,
    F.map_comp_assoc, hγ₀, ← F.map_comp_assoc, ← hβ, F.map_comp_assoc]

end Final

end AlgebraicGeometry.Stack.GlueKernel

/-! ### The gluing step -/

namespace AlgebraicGeometry.Stack

open GlueKernel BigAffineFppf

universe u

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion CategoryTheory.Bicategory.InducedBicategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] {𝒴 : Type (u + 1)} [Category.{u} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS) [p.IsFibered] [q.IsFibered]
  (F : 𝒳 ⥤ 𝒴)

/-- **Relative descent of morphisms**, for a functor `F : 𝒳 ⥤ 𝒴` over the big fppf site: the
condition `AlgebraicGeometry.Stack.RelativeDescentHom` spelled out for arbitrary categories
over the site. -/
def GenRelativeDescentHom {J : Type u} [Category.{u} J] (D : J ⥤ BigAffineFppf B S hS)
    (c : Cone D) : Prop :=
  ∀ (i : J) (a₁ a₂ : p.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (x₁ x₂ : p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt))
    (δ₁ : x₁.1 ⟶ a₁.1) (δ₂ : x₂.1 ⟶ a₂.1),
    p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) δ₁ →
    p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) δ₂ →
    ∀ (β : F.obj a₁.1 ⟶ F.obj a₂.1),
      q.IsHomLift (𝟙 ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) β →
    ∀ (α : x₁.1 ⟶ x₂.1),
      p.IsHomLift (𝟙 ((BigAffineFppf.inclusion B S hS).obj c.pt)) α →
      F.map α ≫ F.map δ₂ = F.map δ₁ ≫ β →
    ∃ (k : J) (s : k ⟶ i) (b₁ b₂ : p.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj k)))
      (d₁ : b₁.1 ⟶ a₁.1) (d₂ : b₂.1 ⟶ a₂.1) (ε : x₁.1 ⟶ b₁.1) (m : b₁.1 ⟶ b₂.1),
      p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (D.map s)) d₁ ∧
      p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (D.map s)) d₂ ∧
      p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (c.π.app k)) ε ∧
      p.IsHomLift (𝟙 ((BigAffineFppf.inclusion B S hS).obj (D.obj k))) m ∧
      ε ≫ d₁ = δ₁ ∧ ε ≫ m ≫ d₂ = α ≫ δ₂ ∧ F.map m ≫ F.map d₂ = F.map d₁ ≫ β

/-- **Relative descent of equalities**, for a functor `F : 𝒳 ⥤ 𝒴` over the big fppf site: the
condition `AlgebraicGeometry.Stack.RelativeDescentEq` spelled out for arbitrary categories over
the site. -/
def GenRelativeDescentEq {J : Type u} [Category.{u} J] (D : J ⥤ BigAffineFppf B S hS)
    (c : Cone D) : Prop :=
  ∀ (i : J) (b₁ b₂ : p.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (x : p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt)) (δ : x.1 ⟶ b₁.1),
    p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) δ →
    ∀ (m m' : b₁.1 ⟶ b₂.1),
      p.IsHomLift (𝟙 ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) m →
      p.IsHomLift (𝟙 ((BigAffineFppf.inclusion B S hS).obj (D.obj i))) m' →
      δ ≫ m = δ ≫ m' → F.map m = F.map m' →
    ∃ (k : J) (s : k ⟶ i) (b : p.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj k)))
      (d : b.1 ⟶ b₁.1), p.IsHomLift ((BigAffineFppf.inclusion B S hS).map (D.map s)) d ∧
        d ≫ m = d ≫ m'

omit [q.IsFibered] in
/-- **The gluing kernel produced by relative descent of morphisms.** The restriction of `x` to
the fibre square of the covering of the limit is descended, by relative descent of morphisms, to
a morphism over the fibre square of the covering at a stage. -/
theorem exists_kernelData
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hFq : F ⋙ q = p)
    (hHom : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤ BigAffineFppf B S hS)
      (c : Cone D), IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
        GenRelativeDescentHom B S hS p q F D c)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
    (i : I) (y : q.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (x : p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt))
    (γ : F.obj x.1 ⟶ y.1)
    (i₀ : I) (s₀ : i₀ ⟶ i) {W₀ : BigFppfOver B S hS} (hW₀ : IsAffineOver B S hS W₀)
    (w : W₀ ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i₀))
    (j₁ : Over i₀) (X₀ : p.Fiber ((baseChangeSystem D i₀ w).obj j₁))
    (xW : 𝒳) (ρ : xW ⟶ x.1) (ε₀ : xW ⟶ X₀.1) (γ₀ : F.obj X₀.1 ⟶ y.1)
    (iρ : p.IsHomLift (pullback.snd w ((BigAffineFppf.inclusion B S hS).map (c.π.app i₀))) ρ)
    (iε₀ : p.IsHomLift ((baseChangeCone D c i₀ w).π.app j₁) ε₀)
    (iγ₀ : q.IsHomLift (pullback.snd w ((BigAffineFppf.inclusion B S hS).map (D.map j₁.hom)) ≫
        (BigAffineFppf.inclusion B S hS).map (D.map (j₁.hom ≫ s₀))) γ₀)
    (hγ₀ : F.map ε₀ ≫ γ₀ = F.map ρ ≫ γ) :
    ∃ (k : Over i₀) (s₁ : k ⟶ j₁) (E : 𝒳) (κ ĥ : E ⟶ X₀.1) (x₂ : 𝒳) (ρ₂ : x₂ ⟶ x.1)
      (θ₁ θ₂ : x₂ ⟶ xW) (ε : x₂ ⟶ E),
      p.IsHomLift (pullback.fst ((baseChangeSnd D i₀ w).app k) ((baseChangeSnd D i₀ w).app k) ≫
          (baseChangeSystem D i₀ w).map s₁) κ ∧
      p.IsHomLift (pullback.snd ((baseChangeSnd D i₀ w).app k) ((baseChangeSnd D i₀ w).app k) ≫
          (baseChangeSystem D i₀ w).map s₁) ĥ ∧
      p.IsHomLift (pullback.fst (pullback.snd w ((BigAffineFppf.inclusion B S hS).map
          (c.π.app i₀))) (pullback.snd w ((BigAffineFppf.inclusion B S hS).map (c.π.app i₀))) ≫
        pullback.snd w ((BigAffineFppf.inclusion B S hS).map (c.π.app i₀))) ρ₂ ∧
      p.IsHomLift (pullback.fst (pullback.snd w ((BigAffineFppf.inclusion B S hS).map
          (c.π.app i₀))) (pullback.snd w ((BigAffineFppf.inclusion B S hS).map
          (c.π.app i₀)))) θ₁ ∧
      p.IsHomLift (pullback.snd (pullback.snd w ((BigAffineFppf.inclusion B S hS).map
          (c.π.app i₀))) (pullback.snd w ((BigAffineFppf.inclusion B S hS).map
          (c.π.app i₀)))) θ₂ ∧
      θ₁ ≫ ρ = ρ₂ ∧ θ₂ ≫ ρ = ρ₂ ∧
      p.IsHomLift ((baseChangePairCone D c i₀ w).π.app k) ε ∧
      ε ≫ κ = θ₁ ≫ ε₀ ∧ ε ≫ ĥ = θ₂ ≫ ε₀ ∧ F.map ĥ ≫ γ₀ = F.map κ ≫ γ₀ := by
  classical
  let ι := BigAffineFppf.inclusion B S hS
  -- the base change system and its fibre products
  let V := baseChangeSystem D i₀ w
  let Vc := baseChangeCone D c i₀ w
  have hVlim : IsLimit ((BigFppfOver.toScheme B S hS).mapCone Vc) :=
    isLimit_baseChangeCone D c i₀ w hc
  let vT := pullback.snd w (ι.map (c.π.app i₀))
  let Vs := baseChangeSnd D i₀ w
  have hVsc : ∀ j, Vc.π.app j ≫ Vs.app j = vT ≫ (overCone D c i₀).π.app j :=
    baseChangeCone_π_app_snd D c i₀ w
  let V₂ := baseChangePairSystem D i₀ w
  let V₂c := baseChangePairCone D c i₀ w
  have hV₂lim : IsLimit ((BigFppfOver.toScheme B S hS).mapCone V₂c) :=
    isLimit_pullbackSystemCone hVsc hVsc hVlim hVlim (isLimit_overCone D c i₀ hc)
  -- affineness, to read the systems in the big affine fppf category
  have hVaff : ∀ j, IsAffineOver B S hS (V.obj j) :=
    fun j => isAffineOver_pullback _ _ hW₀ (D.obj j.left).2 (D.obj i₀).2
  have hVcaff : IsAffineOver B S hS Vc.pt :=
    isAffineOver_pullback _ _ hW₀ c.pt.2 (D.obj i₀).2
  have hV₂aff : ∀ j, IsAffineOver B S hS (V₂.obj j) :=
    fun j => isAffineOver_pullback _ _ (hVaff j) (hVaff j) (D.obj j.left).2
  have hV₂caff : IsAffineOver B S hS V₂c.pt :=
    isAffineOver_pullback _ _ hVcaff hVcaff c.pt.2
  have hV₂Hom := hHom ((IsAffineOver B S hS).lift V₂ hV₂aff) (liftCone hV₂aff V₂c hV₂caff)
    (isLimitLiftCone hV₂aff V₂c hV₂caff hV₂lim)
  -- the data to which relative descent of morphisms is applied, at the stage `j₁`
  let pr₁ := pullback.fst (Vs.app j₁) (Vs.app j₁)
  let pr₂ := pullback.snd (Vs.app j₁) (Vs.app j₁)
  obtain ⟨a₁, π₁, iπ₁⟩ : ∃ (a : p.Fiber (V₂.obj j₁)) (π : a.1 ⟶ X₀.1), p.IsHomLift pr₁ π :=
    ⟨pullbackFiber p X₀ pr₁, IsPreFibered.pullbackMap X₀.2 pr₁,
      (IsPreFibered.pullbackMap.IsCartesian X₀.2 pr₁).toIsHomLift⟩
  obtain ⟨a₂, π₂, iπ₂⟩ : ∃ (a : p.Fiber (V₂.obj j₁)) (π : a.1 ⟶ X₀.1), p.IsHomLift pr₂ π :=
    ⟨pullbackFiber p X₀ pr₂, IsPreFibered.pullbackMap X₀.2 pr₂,
      (IsPreFibered.pullbackMap.IsCartesian X₀.2 pr₂).toIsHomLift⟩
  let q₁ := pullback.fst vT vT
  let q₂ := pullback.snd vT vT
  obtain ⟨x₁, ρ₂, iρ₂⟩ : ∃ (x₁ : p.Fiber V₂c.pt) (ρ₂ : x₁.1 ⟶ x.1), p.IsHomLift (q₁ ≫ vT) ρ₂ :=
    ⟨pullbackFiber p x (q₁ ≫ vT), IsPreFibered.pullbackMap x.2 (q₁ ≫ vT),
      (IsPreFibered.pullbackMap.IsCartesian x.2 (q₁ ≫ vT)).toIsHomLift⟩
  have := hp.isStronglyCartesian_homLift vT ρ
  obtain ⟨θ₁, iθ₁, hθ₁⟩ : ∃ θ : x₁.1 ⟶ xW, p.IsHomLift q₁ θ ∧ θ ≫ ρ = ρ₂ :=
    ⟨_, inferInstance, IsStronglyCartesian.fac p vT ρ (g := q₁) rfl ρ₂⟩
  obtain ⟨θ₂, iθ₂, hθ₂⟩ : ∃ θ : x₁.1 ⟶ xW, p.IsHomLift q₂ θ ∧ θ ≫ ρ = ρ₂ :=
    ⟨_, inferInstance,
      IsStronglyCartesian.fac p vT ρ (g := q₂) pullback.condition ρ₂⟩
  -- the restatements of the given lifts in terms of the systems, with the cone legs named
  have iγ₀' : q.IsHomLift (Vs.app j₁ ≫ ι.map (D.map (j₁.hom ≫ s₀))) γ₀ := iγ₀
  obtain ⟨ℓ₁, hℓ₁⟩ : ∃ ℓ : Vc.pt ⟶ V.obj j₁, ℓ = Vc.π.app j₁ := ⟨_, rfl⟩
  have iε₀' : p.IsHomLift ℓ₁ ε₀ := by rw [hℓ₁]; exact iε₀
  have iρ' : p.IsHomLift vT ρ := iρ
  obtain ⟨ℓ₂₁, hℓ₂₁⟩ : ∃ ℓ : V₂c.pt ⟶ V₂.obj j₁, ℓ = V₂c.π.app j₁ := ⟨_, rfl⟩
  -- the two lifts of `x₁` to the two pullbacks of `X₀`
  have hV₂c₁ : ℓ₂₁ ≫ pr₁ = q₁ ≫ ℓ₁ := by
    rw [hℓ₂₁, hℓ₁]; exact pullbackSystemCone_π_app_fst hVsc hVsc j₁
  have hV₂c₂ : ℓ₂₁ ≫ pr₂ = q₂ ≫ ℓ₁ := by
    rw [hℓ₂₁, hℓ₁]; exact pullbackSystemCone_π_app_snd hVsc hVsc j₁
  obtain ⟨δ₁, iδ₁, hδ₁⟩ := exists_lift' hp
    iπ₁ ℓ₂₁ hV₂c₁.symm
    (isHomLift_comp_of_eq rfl iθ₁ iε₀')
  obtain ⟨δ₂, iδ₂, hδ₂⟩ := exists_lift' hp
    iπ₂ ℓ₂₁ hV₂c₂.symm
    (isHomLift_comp_of_eq rfl iθ₂ iε₀')
  -- the comparison of the images of the two pullbacks in `𝒴`, over `y`
  let tj₁ := ι.map (D.map (j₁.hom ≫ s₀))
  have iχ₁ : q.IsHomLift (pr₁ ≫ Vs.app j₁ ≫ tj₁)
      (F.map (π₁) ≫ γ₀) :=
    isHomLift_comp_of_eq rfl
      (CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFq pr₁ _ iπ₁) iγ₀'
  have iχ₂ : q.IsHomLift (pr₂ ≫ Vs.app j₁ ≫ tj₁)
      (F.map (π₂) ≫ γ₀) :=
    isHomLift_comp_of_eq rfl
      (CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFq pr₂ _ iπ₂) iγ₀'
  obtain ⟨β, iβ, hβ⟩ := exists_lift' hq iχ₂ (𝟙 _)
    (by rw [Category.id_comp, pullback.condition_assoc]) iχ₁
  -- the compatibility needed for relative descent of morphisms
  have hFδ : ∀ (θ : x₁.1 ⟶ xW) (δ : x₁.1 ⟶ X₀.1), θ ≫ ε₀ = δ → θ ≫ ρ = ρ₂ →
      F.map δ ≫ γ₀ = F.map ρ₂ ≫ γ := by
    intro θ δ hθδ hθρ
    rw [← hθδ, ← hθρ, F.map_comp, F.map_comp, Category.assoc, Category.assoc, hγ₀]
  have iFδ₁ : q.IsHomLift ℓ₂₁ (F.map δ₁) :=
    CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFq ℓ₂₁ δ₁ iδ₁
  have iFδ₂ : q.IsHomLift ℓ₂₁ (F.map δ₂) :=
    CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFq ℓ₂₁ δ₂ iδ₂
  have hcond : F.map (𝟙 x₁.1) ≫ F.map δ₂ = F.map δ₁ ≫ β := by
    rw [F.map_id, Category.id_comp]
    refine ext' hq iχ₂ ℓ₂₁ iFδ₂ (by
      have : q.IsHomLift (ℓ₂₁ ≫ 𝟙 _) (F.map δ₁ ≫ β) :=
        isHomLift_comp_of_eq rfl iFδ₁ iβ
      rwa [Category.comp_id] at this) ?_
    rw [Category.assoc, hβ, ← F.map_comp_assoc, ← F.map_comp_assoc, hδ₁, hδ₂,
      hFδ θ₁ _ rfl hθ₁, hFδ θ₂ _ rfl hθ₂]
  obtain ⟨k, s₁, b₁, b₂, d₁, d₂, ε, m, id₁, id₂, iε, im, hεd₁, hεmd₂, hFm⟩ :=
    hV₂Hom j₁ a₁ a₂ x₁ x₁ δ₁ δ₂ (by subst hℓ₂₁; exact iδ₁) (by subst hℓ₂₁; exact iδ₂) β iβ
      (𝟙 x₁.1) (IsHomLift.id x₁.2) hcond
  refine ⟨k, s₁, b₁.1, d₁ ≫ π₁, m ≫ d₂ ≫ π₂, x₁.1, ρ₂, θ₁, θ₂, ε, ?_, ?_, iρ₂, iθ₁, iθ₂,
    hθ₁, hθ₂, iε, ?_, ?_, ?_⟩
  · have id₁' : p.IsHomLift (V₂.map s₁) d₁ := id₁
    have hnat₁ : V₂.map s₁ ≫ pr₁ = pullback.fst (Vs.app k) (Vs.app k) ≫ V.map s₁ :=
      (pullbackSystemFst Vs Vs).naturality s₁
    exact isHomLift_comp_of_eq hnat₁ id₁' iπ₁
  · have id₂' : p.IsHomLift (V₂.map s₁) d₂ := id₂
    have im' : p.IsHomLift (𝟙 (V₂.obj k)) m := im
    have hnat₂ : V₂.map s₁ ≫ pr₂ = pullback.snd (Vs.app k) (Vs.app k) ≫ V.map s₁ :=
      (pullbackSystemSnd Vs Vs).naturality s₁
    exact isHomLift_comp_of_eq ((Category.id_comp _).trans hnat₂) im'
      (isHomLift_comp_of_eq rfl id₂' iπ₂)
  · rw [← Category.assoc, hεd₁, hδ₁]
  · rw [← Category.assoc, ← Category.assoc, Category.assoc ε, hεmd₂, Category.id_comp, hδ₂]
  · simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hFm, hβ]

/-- **Descent of an object along a single-member covering descended to a stage.** Let
`T = lim Tᵢ` be a cofiltered limit of affine schemes over `S`, let `w : W₀ ⟶ T_{i₀}` be a morphism
from an affine scheme whose base changes are single-member fppf coverings, and let `x` be an object
of `𝒳` over `T` with a morphism `γ : F x ⟶ y` to an object `y` of `𝒴` over a stage `Tᵢ`. If the
restriction of `x` to `W = W₀ ×_{T_{i₀}} T` descends to a stage compatibly with `y`, and `F`
satisfies relative descent of morphisms and of equalities along cofiltered limits of affine
schemes, then `x` descends to a stage compatibly with `y`, in the sense of Stacks 06CU. -/
theorem exists_descent_of_singleCover
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (hFq : F ⋙ q = p)
    (h𝒳 : p.IsStack (BigFppfOver.topology B S hS))
    (h𝒴 : q.IsStack (BigFppfOver.topology B S hS))
    (hHom : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤ BigAffineFppf B S hS)
      (c : Cone D), IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
        GenRelativeDescentHom B S hS p q F D c)
    (hEq : ∀ {J : Type u} [Category.{u} J] [IsCofiltered J] (D : J ⥤ BigAffineFppf B S hS)
      (c : Cone D), IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
        GenRelativeDescentEq B S hS p F D c)
    {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ BigAffineFppf B S hS) (c : Cone D)
    (hc : IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c))
    (i : I) (y : q.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
    (x : p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt))
    (γ : F.obj x.1 ⟶ y.1)
    (hγ : q.IsHomLift ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) γ)
    (i₀ : I) (s₀ : i₀ ⟶ i) {W₀ : BigFppfOver B S hS} (hW₀ : IsAffineOver B S hS W₀)
    (w : W₀ ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i₀))
    (hcov : ∀ (Z : BigFppfOver B S hS) (g : Z ⟶ (BigAffineFppf.inclusion B S hS).obj (D.obj i₀)),
      Sieve.ofArrows (fun _ : Unit => pullback w g) (fun _ => pullback.snd w g) ∈
        BigFppfOver.topology B S hS Z)
    (hobj : ∃ (j₁ : Over i₀) (X₀ : p.Fiber ((baseChangeSystem D i₀ w).obj j₁))
      (xW : 𝒳) (ρ : xW ⟶ x.1) (ε₀ : xW ⟶ X₀.1) (γ₀ : F.obj X₀.1 ⟶ y.1),
      p.IsHomLift (pullback.snd w ((BigAffineFppf.inclusion B S hS).map (c.π.app i₀))) ρ ∧
      p.IsHomLift ((baseChangeCone D c i₀ w).π.app j₁) ε₀ ∧
      q.IsHomLift (pullback.snd w ((BigAffineFppf.inclusion B S hS).map (D.map j₁.hom)) ≫
        (BigAffineFppf.inclusion B S hS).map (D.map (j₁.hom ≫ s₀))) γ₀ ∧
      F.map ε₀ ≫ γ₀ = F.map ρ ≫ γ) :
    ∃ (i' : I) (j : i' ⟶ i)
      (x' : p.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj i')))
      (xU : p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt))
      (δ : xU.1 ⟶ x'.1) (β : xU.1 ⟶ x.1) (γ' : F.obj x'.1 ⟶ y.1),
      p.IsStronglyCartesian ((BigAffineFppf.inclusion B S hS).map (c.π.app i')) δ ∧
      p.IsHomLift (𝟙 ((BigAffineFppf.inclusion B S hS).obj c.pt)) β ∧ IsIso β ∧
      q.IsStronglyCartesian ((BigAffineFppf.inclusion B S hS).map (D.map j)) γ' ∧
      F.map δ ≫ γ' = F.map β ≫ γ := by
  classical
  let ι := BigAffineFppf.inclusion B S hS
  obtain ⟨j₁, X₀, xW, ρ, ε₀, γ₀, iρ, iε₀, iγ₀, hγ₀⟩ := hobj
  -- the base change system and its fibre products
  let V := baseChangeSystem D i₀ w
  let Vc := baseChangeCone D c i₀ w
  have hVlim : IsLimit ((BigFppfOver.toScheme B S hS).mapCone Vc) :=
    isLimit_baseChangeCone D c i₀ w hc
  let vT := pullback.snd w (ι.map (c.π.app i₀))
  let Vs := baseChangeSnd D i₀ w
  have hVsc : ∀ j, Vc.π.app j ≫ Vs.app j = vT ≫ (overCone D c i₀).π.app j :=
    baseChangeCone_π_app_snd D c i₀ w
  let V₂ := baseChangePairSystem D i₀ w
  let V₂c := baseChangePairCone D c i₀ w
  have hV₂lim : IsLimit ((BigFppfOver.toScheme B S hS).mapCone V₂c) :=
    isLimit_pullbackSystemCone hVsc hVsc hVlim hVlim (isLimit_overCone D c i₀ hc)
  -- affineness, to read the systems in the big affine fppf category
  have hVaff : ∀ j, IsAffineOver B S hS (V.obj j) :=
    fun j => isAffineOver_pullback _ _ hW₀ (D.obj j.left).2 (D.obj i₀).2
  have hVcaff : IsAffineOver B S hS Vc.pt :=
    isAffineOver_pullback _ _ hW₀ c.pt.2 (D.obj i₀).2
  have hV₂aff : ∀ j, IsAffineOver B S hS (V₂.obj j) :=
    fun j => isAffineOver_pullback _ _ (hVaff j) (hVaff j) (D.obj j.left).2
  have hV₂caff : IsAffineOver B S hS V₂c.pt :=
    isAffineOver_pullback _ _ hVcaff hVcaff c.pt.2
  have hV₂Hom := hHom ((IsAffineOver B S hS).lift V₂ hV₂aff) (liftCone hV₂aff V₂c hV₂caff)
    (isLimitLiftCone hV₂aff V₂c hV₂caff hV₂lim)
  -- the gluing kernel, from relative descent of morphisms
  obtain ⟨k, s₁, E, κ, ĥ, x₂, ρ₂, θ₁, θ₂, ε, iκ, iĥ, iρ₂, iθ₁, iθ₂, hθ₁, hθ₂, iε, hεκ, hεĥ,
    hKF⟩ := exists_kernelData B S hS p q F hp hq hFq hHom D c hc i y x γ i₀ s₀ hW₀ w j₁ X₀ xW ρ
      ε₀ γ₀ iρ iε₀ iγ₀ hγ₀
  let tj₁ := ι.map (D.map (j₁.hom ≫ s₀))
  have iγ₀' : q.IsHomLift (Vs.app j₁ ≫ tj₁) γ₀ := iγ₀
  have iρ' : p.IsHomLift vT ρ := iρ
  obtain ⟨ℓ₁, hℓ₁⟩ : ∃ ℓ : Vc.pt ⟶ V.obj j₁, ℓ = Vc.π.app j₁ := ⟨_, rfl⟩
  have iε₀' : p.IsHomLift ℓ₁ ε₀ := by rw [hℓ₁]; exact iε₀
  let q₁ := pullback.fst vT vT
  let q₂ := pullback.snd vT vT
  let K : Kernel p :=
    { V₀ := V.obj j₁
      V := V.obj k
      U := (overSystem D i₀).obj k
      τ := V.map s₁
      v := Vs.app k
      X₀ := X₀
      E := E
      κ := κ
      ĥ := ĥ
      isHomLift_κ := iκ
      isHomLift_ĥ := iĥ }
  -- the kernel at the limit
  obtain ⟨ℓk, hℓk⟩ : ∃ ℓ : pullback w (ι.map (c.π.app i₀)) ⟶ V.obj k, ℓ = Vc.π.app k :=
    ⟨_, rfl⟩
  obtain ⟨πk, hπk⟩ : ∃ π : ι.obj c.pt ⟶ (overSystem D i₀).obj k,
      π = (overCone D c i₀).π.app k := ⟨_, rfl⟩
  have hℓkv : ℓk ≫ Vs.app k = vT ≫ πk := by rw [hℓk, hπk]; exact hVsc k
  have hℓkτ : ℓk ≫ V.map s₁ = ℓ₁ := by rw [hℓk, hℓ₁]; exact Vc.w s₁
  have hV₂ck : V₂c.π.app k =
      pullback.lift (f := Vs.app k) (g := Vs.app k) (q₁ ≫ ℓk) (q₂ ≫ ℓk)
        (by rw [Category.assoc, Category.assoc, hℓkv, pullback.condition_assoc]) := by
    refine pullback.hom_ext ?_ ?_
    · subst hℓk
      exact (pullbackSystemCone_π_app_fst hVsc hVsc k).trans (pullback.lift_fst _ _ _).symm
    · subst hℓk
      exact (pullbackSystemCone_π_app_snd hVsc hVsc k).trans (pullback.lift_snd _ _ _).symm
  let L : LimitData K :=
    { T := ι.obj c.pt
      W := pullback w (ι.map (c.π.app i₀))
      vT := vT
      ℓ := ℓk
      πU := πk
      hℓ := hℓkv
      x := x.1
      xW := xW
      ρ := ρ
      isHomLift_ρ := iρ'
      ε₀ := ε₀
      isHomLift_ε₀ := isHomLift_of_eq' hℓkτ.symm iε₀'
      x₂ := x₂
      ρ₂ := ρ₂
      isHomLift_ρ₂ := iρ₂
      θ₁ := θ₁
      θ₂ := θ₂
      isHomLift_θ₁ := iθ₁
      isHomLift_θ₂ := iθ₂
      hθ₁ := hθ₁
      hθ₂ := hθ₂
      ε := ε
      isHomLift_ε := by
        have := iε
        rw [hV₂ck] at this
        exact this
      hεκ := hεκ
      hεĥ := hεĥ }
  -- the comparison of the images in `𝒴` of the chosen pullbacks of `X₀`
  have hχ : ∀ {Z : BigFppfOver B S hS} (e : Z ⟶ K.V),
      q.IsHomLift ((e ≫ K.τ) ≫ Vs.app j₁ ≫ tj₁)
        (F.map (IsPreFibered.pullbackMap K.X₀.2 (e ≫ K.τ)) ≫ γ₀) := fun e =>
    isHomLift_comp_of_eq rfl
      (CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFq _ _
        (IsPreFibered.pullbackMap.IsCartesian K.X₀.2 (e ≫ K.τ)).toIsHomLift) iγ₀'
  have hFv : ∀ {Z : BigFppfOver B S hS} {e₁ e₃ : Z ⟶ K.V}
      (u u' : pullbackFiber p K.X₀ (e₁ ≫ K.τ) ⟶ pullbackFiber p K.X₀ (e₃ ≫ K.τ)),
      F.map (Fiber.fiberInclusion.map u) ≫
          F.map (IsPreFibered.pullbackMap K.X₀.2 (e₃ ≫ K.τ)) ≫ γ₀ =
        F.map (Fiber.fiberInclusion.map u') ≫
          F.map (IsPreFibered.pullbackMap K.X₀.2 (e₃ ≫ K.τ)) ≫ γ₀ →
      F.map (Fiber.fiberInclusion.map u) = F.map (Fiber.fiberInclusion.map u') := by
    intro Z e₁ e₃ u u' h
    exact ext' hq (hχ e₃) (𝟙 _)
      (CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFq _ _ u.2)
      (CategoryTheory.PresheafOfCategories.isHomLift_map_of_comp hFq _ _ u'.2) h
  -- the condition `hom_self`, from relative descent of equalities on the base change system
  have hVHEq := hEq ((IsAffineOver B S hS).lift V hVaff) (liftCone hVaff Vc hVcaff)
    (isLimitLiftCone hVaff Vc hVcaff hVlim)
  have hxW : p.obj xW = pullback w (ι.map (c.π.app i₀)) := IsHomLift.domain_eq p vT ρ
  obtain ⟨δ₀, iδ₀, hδ₀⟩ := exists_lift' hp
    (IsPreFibered.pullbackMap.IsCartesian K.X₀.2 (𝟙 K.V ≫ K.τ)).toIsHomLift ℓk
    (by rw [Category.id_comp]) L.isHomLift_ε₀
  have hT₀ : δ₀ ≫ Fiber.fiberInclusion.map (transition hp K (𝟙 K.V) (𝟙 K.V) rfl) =
      δ₀ ≫ 𝟙 _ := by
    refine ext' hp (IsPreFibered.pullbackMap.IsCartesian K.X₀.2 (𝟙 K.V ≫ K.τ)).toIsHomLift ℓk
      (isHomLift_comp_of_eq (Category.comp_id ℓk) iδ₀
        (transition hp K (𝟙 K.V) (𝟙 K.V) rfl).2)
      (isHomLift_comp_of_eq (Category.comp_id ℓk) iδ₀
        (IsHomLift.id (pullbackFiber p K.X₀ (𝟙 K.V ≫ K.τ)).2)) ?_
    rw [Category.comp_id, hδ₀, Category.assoc]
    have := iδ₀
    have : p.IsHomLift (𝟙 (pullback w (ι.map (c.π.app i₀)))) (𝟙 xW) := IsHomLift.id hxW
    have := limit_transition hp L (𝟙 K.V) (𝟙 K.V) rfl ℓk (𝟙 _) (𝟙 _) rfl
      (by rw [Category.id_comp, Category.comp_id]) (by rw [Category.id_comp, Category.comp_id])
      δ₀ (𝟙 xW) (𝟙 xW) rfl (by rw [hδ₀, Category.id_comp])
    rw [this, Category.id_comp]
  obtain ⟨k₃, s₃, bb, d, id, hd⟩ := hVHEq k (pullbackFiber p K.X₀ (𝟙 K.V ≫ K.τ))
    (pullbackFiber p K.X₀ (𝟙 K.V ≫ K.τ)) ⟨xW, hxW⟩ δ₀ (by subst hℓk; exact iδ₀)
    (Fiber.fiberInclusion.map (transition hp K (𝟙 K.V) (𝟙 K.V) rfl)) (𝟙 _)
    (transition hp K (𝟙 K.V) (𝟙 K.V) rfl).2
    (IsHomLift.id (pullbackFiber p K.X₀ (𝟙 K.V ≫ K.τ)).2) hT₀
    (hFv _ (𝟙 _) (by
      rw [map_transition hp K F γ₀ hKF, Fiber.fiberInclusion.map_id, F.map_id]
      exact (Category.id_comp _).symm))
  have hself : ∀ ⦃Z : BigFppfOver B S hS⦄ (e : Z ⟶ V.obj k₃),
      transition hp K (e ≫ V.map s₃) (e ≫ V.map s₃) rfl = 𝟙 _ := by
    intro Z e
    have id' : p.IsHomLift (V.map s₃) d := id
    refine transition_self_of_pullbackFiberHom hp K (𝟙 K.V) (e ≫ V.map s₃) _
      (Category.comp_id _) ?_
    rw [pullbackFiberHom_eq_of_comp_eq hp _ (𝟙 _) (V.map s₃) d hd e]
    exact pullbackFiberHom_id _
  -- the cocycle condition, from relative descent of equalities on the triple fibre products
  have hA : ∀ j, V₂c.π.app j ≫ (pullbackSystemSnd Vs Vs).app j = q₂ ≫ Vc.π.app j :=
    pullbackSystemCone_π_app_snd hVsc hVsc
  have hB : ∀ j, V₂c.π.app j ≫ (pullbackSystemFst Vs Vs).app j = q₁ ≫ Vc.π.app j :=
    pullbackSystemCone_π_app_fst hVsc hVsc
  let V₃ := pullbackSystem (pullbackSystemSnd Vs Vs) (pullbackSystemFst Vs Vs)
  let V₃c := pullbackSystemCone (c₁ := V₂c) (c₂ := V₂c) (c₃ := Vc) hA hB
  have hV₃lim : IsLimit ((BigFppfOver.toScheme B S hS).mapCone V₃c) :=
    isLimit_pullbackSystemCone hA hB hV₂lim hV₂lim hVlim
  have hV₃aff : ∀ j, IsAffineOver B S hS (V₃.obj j) :=
    fun j => isAffineOver_pullback _ _ (hV₂aff j) (hV₂aff j) (hVaff j)
  have hV₃caff : IsAffineOver B S hS V₃c.pt :=
    isAffineOver_pullback _ _ hV₂caff hV₂caff hVcaff
  have hV₃Eq := hEq ((IsAffineOver B S hS).lift V₃ hV₃aff) (liftCone hV₃aff V₃c hV₃caff)
    (isLimitLiftCone hV₃aff V₃c hV₃caff hV₃lim)
  -- the three projections of the triple fibre product at the stage `k₃`
  obtain ⟨P₁₂, hP₁₂⟩ : ∃ P, P = (pullbackSystemFst (pullbackSystemSnd Vs Vs)
      (pullbackSystemFst Vs Vs)).app k₃ := ⟨_, rfl⟩
  obtain ⟨P₂₃, hP₂₃⟩ : ∃ P, P = (pullbackSystemSnd (pullbackSystemSnd Vs Vs)
      (pullbackSystemFst Vs Vs)).app k₃ := ⟨_, rfl⟩
  obtain ⟨f₂, hf₂⟩ : ∃ f, f = (pullbackSystemFst Vs Vs).app k₃ := ⟨_, rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ g, g = (pullbackSystemSnd Vs Vs).app k₃ := ⟨_, rfl⟩
  have hr₂ : P₁₂ ≫ g₂ = P₂₃ ≫ f₂ := by
    rw [hP₁₂, hP₂₃, hf₂, hg₂]
    exact pullbackSystem_condition (pullbackSystemSnd Vs Vs) (pullbackSystemFst Vs Vs) k₃
  have hfg : f₂ ≫ Vs.app k₃ = g₂ ≫ Vs.app k₃ := by
    rw [hf₂, hg₂]; exact pullbackSystem_condition Vs Vs k₃
  have hVsn : V.map s₃ ≫ Vs.app k = Vs.app k₃ ≫ (overSystem D i₀).map s₃ := Vs.naturality s₃
  obtain ⟨e₁, he₁⟩ : ∃ e : V₃.obj k₃ ⟶ K.V, e = P₁₂ ≫ f₂ ≫ V.map s₃ := ⟨_, rfl⟩
  obtain ⟨e₂, he₂⟩ : ∃ e : V₃.obj k₃ ⟶ K.V, e = P₁₂ ≫ g₂ ≫ V.map s₃ := ⟨_, rfl⟩
  obtain ⟨e₃, he₃⟩ : ∃ e : V₃.obj k₃ ⟶ K.V, e = P₂₃ ≫ g₂ ≫ V.map s₃ := ⟨_, rfl⟩
  have h₁₂ : e₁ ≫ K.v = e₂ ≫ K.v := by
    show e₁ ≫ Vs.app k = e₂ ≫ Vs.app k
    rw [he₁, he₂, Category.assoc, Category.assoc, Category.assoc, Category.assoc, hVsn,
      reassoc_of% hfg]
  have h₂₃ : e₂ ≫ K.v = e₃ ≫ K.v := by
    show e₂ ≫ Vs.app k = e₃ ≫ Vs.app k
    rw [he₂, he₃, reassoc_of% hr₂, Category.assoc, Category.assoc, Category.assoc, hVsn,
      reassoc_of% hfg, Category.assoc g₂, hVsn]
  have h₁₃ : e₁ ≫ K.v = e₃ ≫ K.v := h₁₂.trans h₂₃
  -- the triple fibre product at the limit
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q, Q = pullback.fst q₂ q₁ ≫ q₁ := ⟨_, rfl⟩
  obtain ⟨Q₂, hQ₂⟩ : ∃ Q, Q = pullback.fst q₂ q₁ ≫ q₂ := ⟨_, rfl⟩
  obtain ⟨Q₃, hQ₃⟩ : ∃ Q, Q = pullback.snd q₂ q₁ ≫ q₂ := ⟨_, rfl⟩
  have hqv : q₁ ≫ vT = q₂ ≫ vT := pullback.condition
  have hQ₁₂ : Q₁ ≫ vT = Q₂ ≫ vT := by
    rw [hQ₁, hQ₂, Category.assoc, Category.assoc, hqv]
  have hQ₂₃ : Q₂ ≫ vT = Q₃ ≫ vT := by
    rw [hQ₂, hQ₃, Category.assoc, pullback.condition_assoc, Category.assoc, hqv]
  obtain ⟨x₃, ρ₃, iρ₃⟩ : ∃ (x₃ : p.Fiber V₃c.pt) (ρ₃ : x₃.1 ⟶ x.1),
      p.IsHomLift (Q₁ ≫ vT) ρ₃ :=
    ⟨pullbackFiber p x (Q₁ ≫ vT), IsPreFibered.pullbackMap x.2 (Q₁ ≫ vT),
      (IsPreFibered.pullbackMap.IsCartesian x.2 (Q₁ ≫ vT)).toIsHomLift⟩
  obtain ⟨ζ₁, iζ₁, hζ₁⟩ := exists_lift' hp iρ' Q₁ rfl iρ₃
  obtain ⟨ζ₂, iζ₂, hζ₂⟩ := exists_lift' hp iρ' Q₂ hQ₁₂ iρ₃
  obtain ⟨ζ₃, iζ₃, hζ₃⟩ := exists_lift' hp iρ' Q₃ (hQ₁₂.trans hQ₂₃) iρ₃
  obtain ⟨ℓ₃, hℓ₃⟩ : ∃ ℓ : pullback q₂ q₁ ⟶ V₃.obj k₃, ℓ = V₃c.π.app k₃ := ⟨_, rfl⟩
  obtain ⟨ℓ₂₃, hℓ₂₃⟩ : ∃ ℓ : pullback vT vT ⟶ V₂.obj k₃, ℓ = V₂c.π.app k₃ := ⟨_, rfl⟩
  obtain ⟨ℓ₁₃, hℓ₁₃⟩ : ∃ ℓ : pullback w (ι.map (c.π.app i₀)) ⟶ V.obj k₃,
      ℓ = Vc.π.app k₃ := ⟨_, rfl⟩
  have hk₃ : ℓ₁₃ ≫ V.map s₃ = ℓk := by rw [hℓk, hℓ₁₃]; exact Vc.w s₃
  have hℓP₁₂ : ℓ₃ ≫ P₁₂ = pullback.fst q₂ q₁ ≫ ℓ₂₃ := by
    rw [hℓ₃, hP₁₂, hℓ₂₃]; exact pullbackSystemCone_π_app_fst hA hB k₃
  have hℓP₂₃ : ℓ₃ ≫ P₂₃ = pullback.snd q₂ q₁ ≫ ℓ₂₃ := by
    rw [hℓ₃, hP₂₃, hℓ₂₃]; exact pullbackSystemCone_π_app_snd hA hB k₃
  have hℓf₂ : ℓ₂₃ ≫ f₂ = q₁ ≫ ℓ₁₃ := by rw [hℓ₂₃, hf₂, hℓ₁₃]; exact hB k₃
  have hℓg₂ : ℓ₂₃ ≫ g₂ = q₂ ≫ ℓ₁₃ := by rw [hℓ₂₃, hg₂, hℓ₁₃]; exact hA k₃
  have hℓe₁ : Q₁ ≫ ℓk = ℓ₃ ≫ e₁ := by
    rw [he₁, reassoc_of% hℓP₁₂, reassoc_of% hℓf₂, hk₃, hQ₁, Category.assoc]
  have hℓe₂ : Q₂ ≫ ℓk = ℓ₃ ≫ e₂ := by
    rw [he₂, reassoc_of% hℓP₁₂, reassoc_of% hℓg₂, hk₃, hQ₂, Category.assoc]
  have hℓe₃ : Q₃ ≫ ℓk = ℓ₃ ≫ e₃ := by
    rw [he₃, reassoc_of% hℓP₂₃, reassoc_of% hℓg₂, hk₃, hQ₃, Category.assoc]
  obtain ⟨δ₃, iδ₃, hδ₃⟩ := exists_lift' hp
    (IsPreFibered.pullbackMap.IsCartesian K.X₀.2 (e₁ ≫ K.τ)).toIsHomLift ℓ₃
    (by rw [← Category.assoc ℓ₃, ← hℓe₁, Category.assoc])
    (isHomLift_comp_of_eq rfl iζ₁ L.isHomLift_ε₀)
  have hTT : δ₃ ≫ Fiber.fiberInclusion.map (transition hp K e₁ e₂ h₁₂ ≫
        transition hp K e₂ e₃ h₂₃) = δ₃ ≫ Fiber.fiberInclusion.map (transition hp K e₁ e₃ h₁₃) := by
    have iT₁₂ := (transition hp K e₁ e₂ h₁₂).2
    have iT₂₃ := (transition hp K e₂ e₃ h₂₃).2
    have iT₁₃ := (transition hp K e₁ e₃ h₁₃).2
    have iδ' : p.IsHomLift ℓ₃ (δ₃ ≫ Fiber.fiberInclusion.map (transition hp K e₁ e₂ h₁₂)) :=
      isHomLift_comp_of_eq (Category.comp_id ℓ₃) iδ₃ iT₁₂
    have hA' : δ₃ ≫ Fiber.fiberInclusion.map (transition hp K e₁ e₂ h₁₂) ≫
        IsPreFibered.pullbackMap K.X₀.2 (e₂ ≫ K.τ) = ζ₂ ≫ L.ε₀ := by
      have := iδ₃; have := iζ₁; have := iζ₂
      exact limit_transition hp L e₁ e₂ h₁₂ ℓ₃ Q₁ Q₂ hQ₁₂ hℓe₁ hℓe₂ δ₃ ζ₁ ζ₂
        (hζ₁.trans hζ₂.symm) hδ₃
    have hB' : (δ₃ ≫ Fiber.fiberInclusion.map (transition hp K e₁ e₂ h₁₂)) ≫
        Fiber.fiberInclusion.map (transition hp K e₂ e₃ h₂₃) ≫
          IsPreFibered.pullbackMap K.X₀.2 (e₃ ≫ K.τ) = ζ₃ ≫ L.ε₀ := by
      have := iδ'; have := iζ₂; have := iζ₃
      exact limit_transition hp L e₂ e₃ h₂₃ ℓ₃ Q₂ Q₃ hQ₂₃ hℓe₂ hℓe₃ _ ζ₂ ζ₃
        (hζ₂.trans hζ₃.symm) (by rw [Category.assoc]; exact hA')
    have hC' : δ₃ ≫ Fiber.fiberInclusion.map (transition hp K e₁ e₃ h₁₃) ≫
        IsPreFibered.pullbackMap K.X₀.2 (e₃ ≫ K.τ) = ζ₃ ≫ L.ε₀ := by
      have := iδ₃; have := iζ₁; have := iζ₃
      exact limit_transition hp L e₁ e₃ h₁₃ ℓ₃ Q₁ Q₃ (hQ₁₂.trans hQ₂₃) hℓe₁ hℓe₃ δ₃ ζ₁ ζ₃
        (hζ₁.trans hζ₃.symm) hδ₃
    refine ext' hp
      (IsPreFibered.pullbackMap.IsCartesian K.X₀.2 (e₃ ≫ K.τ)).toIsHomLift ℓ₃
      (isHomLift_comp_of_eq (Category.comp_id ℓ₃) iδ₃
        (transition hp K e₁ e₂ h₁₂ ≫ transition hp K e₂ e₃ h₂₃).2)
      (isHomLift_comp_of_eq (Category.comp_id ℓ₃) iδ₃ iT₁₃) ?_
    show (δ₃ ≫ (Fiber.fiberInclusion.map (transition hp K e₁ e₂ h₁₂) ≫
        Fiber.fiberInclusion.map (transition hp K e₂ e₃ h₂₃))) ≫
          IsPreFibered.pullbackMap K.X₀.2 (e₃ ≫ K.τ) =
      (δ₃ ≫ Fiber.fiberInclusion.map (transition hp K e₁ e₃ h₁₃)) ≫
          IsPreFibered.pullbackMap K.X₀.2 (e₃ ≫ K.τ)
    exact (Category.assoc _ _ _).trans ((congrArg (δ₃ ≫ ·) (Category.assoc _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans (hB'.trans (hC'.symm.trans
        (Category.assoc _ _ _).symm))))
  have hFTT : F.map (Fiber.fiberInclusion.map (transition hp K e₁ e₂ h₁₂ ≫
        transition hp K e₂ e₃ h₂₃)) = F.map (Fiber.fiberInclusion.map
          (transition hp K e₁ e₃ h₁₃)) := by
    refine hFv _ _ ?_
    show F.map (Fiber.fiberInclusion.map (transition hp K e₁ e₂ h₁₂) ≫
        Fiber.fiberInclusion.map (transition hp K e₂ e₃ h₂₃)) ≫ _ = _
    rw [F.map_comp]
    refine (Category.assoc _ _ _).trans ?_
    rw [map_transition hp K F γ₀ hKF e₂ e₃ h₂₃, map_transition hp K F γ₀ hKF e₁ e₂ h₁₂,
      map_transition hp K F γ₀ hKF e₁ e₃ h₁₃]
  have iδ₃' : p.IsHomLift (V₃c.π.app k₃) δ₃ := hℓ₃ ▸ iδ₃
  obtain ⟨k₄, s₄, bb', d', id', hd'⟩ := hV₃Eq k₃ (pullbackFiber p K.X₀ (e₁ ≫ K.τ))
    (pullbackFiber p K.X₀ (e₃ ≫ K.τ)) x₃ δ₃ iδ₃' _ _
    (transition hp K e₁ e₂ h₁₂ ≫ transition hp K e₂ e₃ h₂₃).2
    (transition hp K e₁ e₃ h₁₃).2 hTT hFTT
  -- the descent datum at the final stage `k₄`
  have id₃ : p.IsHomLift (V.map s₃) d := id
  have id₄ : p.IsHomLift (V₃.map s₄) d' := id'
  obtain ⟨σ, hσdef⟩ : ∃ σ : V.obj k₄ ⟶ K.V, σ = V.map (s₄ ≫ s₃) := ⟨_, rfl⟩
  have hσ : σ ≫ K.v = Vs.app k₄ ≫ (overSystem D i₀).map (s₄ ≫ s₃) := by
    rw [hσdef]; exact Vs.naturality (s₄ ≫ s₃)
  have hσ' : σ = V.map s₄ ≫ V.map s₃ := by rw [hσdef, Functor.map_comp]
  have hself' : ∀ ⦃Z : BigFppfOver B S hS⦄ (e : Z ⟶ V.obj k₄),
      transition hp K (e ≫ σ) (e ≫ σ) rfl = 𝟙 _ := by
    intro Z e
    refine transition_self_of_pullbackFiberHom hp K (𝟙 K.V) ((e ≫ V.map s₄) ≫ V.map s₃) _
      (by rw [Category.comp_id, Category.assoc, hσ']) ?_
    rw [pullbackFiberHom_eq_of_comp_eq hp _ (𝟙 _) (V.map s₃) d hd (e ≫ V.map s₄)]
    exact pullbackFiberHom_id _
  have hn₁₂ : V₃.map s₄ ≫ P₁₂ =
      (pullbackSystemFst (pullbackSystemSnd Vs Vs) (pullbackSystemFst Vs Vs)).app k₄ ≫
        V₂.map s₄ := by
    rw [hP₁₂]; exact (pullbackSystemFst _ _).naturality s₄
  have hn₂₃ : V₃.map s₄ ≫ P₂₃ =
      (pullbackSystemSnd (pullbackSystemSnd Vs Vs) (pullbackSystemFst Vs Vs)).app k₄ ≫
        V₂.map s₄ := by
    rw [hP₂₃]; exact (pullbackSystemSnd _ _).naturality s₄
  have hnf : V₂.map s₄ ≫ f₂ = (pullbackSystemFst Vs Vs).app k₄ ≫ V.map s₄ := by
    rw [hf₂]; exact (pullbackSystemFst _ _).naturality s₄
  have hng : V₂.map s₄ ≫ g₂ = (pullbackSystemSnd Vs Vs).app k₄ ≫ V.map s₄ := by
    rw [hg₂]; exact (pullbackSystemSnd _ _).naturality s₄
  have hcomp' : ∀ ⦃Z : BigFppfOver B S hS⦄ (e₁' e₂' e₃' : Z ⟶ V.obj k₄)
      (h₁₂' : e₁' ≫ Vs.app k₄ = e₂' ≫ Vs.app k₄) (h₂₃' : e₂' ≫ Vs.app k₄ = e₃' ≫ Vs.app k₄)
      (h₁₃' : e₁' ≫ Vs.app k₄ = e₃' ≫ Vs.app k₄),
      transition hp K (e₁' ≫ σ) (e₂' ≫ σ) (stage_compat K σ _ _ hσ h₁₂') ≫
        transition hp K (e₂' ≫ σ) (e₃' ≫ σ) (stage_compat K σ _ _ hσ h₂₃') =
      transition hp K (e₁' ≫ σ) (e₃' ≫ σ) (stage_compat K σ _ _ hσ h₁₃') := by
    intro Z e₁' e₂' e₃' h₁₂' h₂₃' h₁₃'
    let L₁₂ : Z ⟶ V₂.obj k₄ := pullback.lift e₁' e₂' h₁₂'
    let L₂₃ : Z ⟶ V₂.obj k₄ := pullback.lift e₂' e₃' h₂₃'
    have hL : L₁₂ ≫ (pullbackSystemSnd Vs Vs).app k₄ = L₂₃ ≫ (pullbackSystemFst Vs Vs).app k₄ :=
      (pullback.lift_snd _ _ _).trans (pullback.lift_fst _ _ _).symm
    let g : Z ⟶ V₃.obj k₄ := pullback.lift L₁₂ L₂₃ hL
    have hg₁₂ : g ≫ (pullbackSystemFst (pullbackSystemSnd Vs Vs)
        (pullbackSystemFst Vs Vs)).app k₄ = L₁₂ := pullback.lift_fst _ _ _
    have hg₂₃ : g ≫ (pullbackSystemSnd (pullbackSystemSnd Vs Vs)
        (pullbackSystemFst Vs Vs)).app k₄ = L₂₃ := pullback.lift_snd _ _ _
    have hL₁ : L₁₂ ≫ (pullbackSystemFst Vs Vs).app k₄ = e₁' := pullback.lift_fst _ _ _
    have hL₂ : L₁₂ ≫ (pullbackSystemSnd Vs Vs).app k₄ = e₂' := pullback.lift_snd _ _ _
    have hL₃ : L₂₃ ≫ (pullbackSystemSnd Vs Vs).app k₄ = e₃' := pullback.lift_snd _ _ _
    refine transition_comp_of_pullbackFiberHom hp K e₁ e₂ e₃ h₁₂ h₂₃ h₁₃ (g ≫ V₃.map s₄)
      (e₁' ≫ σ) (e₂' ≫ σ) (e₃' ≫ σ) ?_ ?_ ?_ _ _ _
      (pullbackFiberHom_eq_of_comp_eq hp
        (transition hp K e₁ e₂ h₁₂ ≫ transition hp K e₂ e₃ h₂₃) (transition hp K e₁ e₃ h₁₃)
        (V₃.map s₄) d' hd' g)
    · rw [he₁, Category.assoc, reassoc_of% hn₁₂, reassoc_of% hnf, reassoc_of% hg₁₂,
        reassoc_of% hL₁, hσ']
    · rw [he₂, Category.assoc, reassoc_of% hn₁₂, reassoc_of% hng, reassoc_of% hg₁₂,
        reassoc_of% hL₂, hσ']
    · rw [he₃, Category.assoc, reassoc_of% hn₂₃, reassoc_of% hng, reassoc_of% hg₂₃,
        reassoc_of% hL₃, hσ']
  obtain ⟨x', ζ, iζ, hζ⟩ := exists_stageGlue hp K σ (Vs.app k₄)
    ((overSystem D i₀).map (s₄ ≫ s₃)) hσ h𝒳 (hcov _ (ι.map (D.map k₄.hom))) hself' hcomp'
  -- the descent of `x`
  let tk₄ := ι.map (D.map (k₄.hom ≫ s₀))
  have hbase : (σ ≫ K.τ) ≫ Vs.app j₁ ≫ tj₁ = Vs.app k₄ ≫ tk₄ := by
    have h₁ : σ ≫ K.τ = V.map (s₄ ≫ s₃ ≫ s₁) := by
      show σ ≫ V.map s₁ = _
      rw [hσdef, ← Functor.map_comp, Category.assoc]
    have h₂ : V.map (s₄ ≫ s₃ ≫ s₁) ≫ Vs.app j₁ =
        Vs.app k₄ ≫ (overSystem D i₀).map (s₄ ≫ s₃ ≫ s₁) := Vs.naturality _
    rw [h₁, reassoc_of% h₂]
    show Vs.app k₄ ≫ ι.map (D.map (s₄ ≫ s₃ ≫ s₁).left) ≫
      ι.map (D.map (j₁.hom ≫ s₀)) = Vs.app k₄ ≫ ι.map (D.map (k₄.hom ≫ s₀))
    rw [← ι.map_comp, ← D.map_comp, ← Category.assoc, Over.w]
  obtain ⟨ℓ₄, hℓ₄⟩ : ∃ ℓ : pullback w (ι.map (c.π.app i₀)) ⟶ V.obj k₄, ℓ = Vc.π.app k₄ :=
    ⟨_, rfl⟩
  have hℓ₄σ : ℓ₄ ≫ σ = ℓk := by rw [hℓ₄, hσdef, hℓk]; exact Vc.w (s₄ ≫ s₃)
  have hℓ₄v : ℓ₄ ≫ Vs.app k₄ = vT ≫ ι.map (c.π.app k₄.left) := by rw [hℓ₄]; exact hVsc k₄
  have hπg : ι.map (c.π.app k₄.left) ≫ tk₄ = ι.map (c.π.app i) := by
    show ι.map (c.π.app k₄.left) ≫ ι.map (D.map (k₄.hom ≫ s₀)) = _
    rw [← ι.map_comp, c.w]
  obtain ⟨xU, δx, β, γ', iδx, iβ, iγ', heq⟩ := exists_descent_of_stageGlue hp hq F hFq h𝒳 h𝒴
    K L (Vs.app j₁ ≫ tj₁) γ₀ iγ₀' hKF (ι.map (c.π.app i)) γ hγ hγ₀ σ (Vs.app k₄)
    ((overSystem D i₀).map (s₄ ≫ s₃)) hσ x' ζ iζ hζ ℓ₄ hℓ₄σ (ι.map (c.π.app k₄.left)) hℓ₄v
    (hcov _ (ι.map (D.map k₄.hom))) (hcov _ (ι.map (c.π.app i₀))) tk₄ hbase hπg x.2
  refine ⟨k₄.left, k₄.hom ≫ s₀, x', xU, δx, β, γ', ?_, iβ, ?_, ?_, heq⟩
  · exact hp.isStronglyCartesian_homLift _ _
  · have := hp.isStronglyCartesian_homLift (𝟙 (ι.obj c.pt)) β
    exact IsStronglyCartesian.isIso_of_base_isIso p (𝟙 (ι.obj c.pt)) β
  · exact hq.isStronglyCartesian_homLift _ _

end AlgebraicGeometry.Stack

end
