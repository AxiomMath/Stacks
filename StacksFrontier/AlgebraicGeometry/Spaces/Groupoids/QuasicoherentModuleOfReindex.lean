module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.DescentTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TransitionReindexComp

/-!
# Quasi-coherent modules on a groupoid from a transition morphism on another space

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces, `ρ : U ⟶ Z` a morphism to an algebraic
space carrying a quasi-coherent module `ℳ`, and `α : a^*ℳ ⟶ b^*ℳ` a morphism of inverse images
along two morphisms `a, b : V ⟶ Z`, with a morphism `τ : R ⟶ V` such that `t ≫ ρ = τ ≫ a` and
`τ ≫ b = s ≫ ρ`. If `α` satisfies the cocycle law at the images in `V` of the composition and
the two projections of the composable pairs of arrows, and restricts to the identification of
inverse images along the image of the unit, then `(ρ^*ℳ, τ^*α)` is a quasi-coherent module on
the groupoid (Stacks 0441).

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentModuleOfReindex`: the module on the groupoid.

## Main results

* `AlgebraicGeometry.Space.transitionCocycle_of_descentTransport`,
  `AlgebraicGeometry.Space.transitionUnit_of_descentTransport`: a morphism whose reindexings are
  transported identifications satisfies the cocycle law, resp. the unit law.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces Stacks.AlgebraicGeometry.EquivariantQuasicoherentPullback

section Predicates

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The cocycle law, written with composition. -/
theorem TransitionCocycle.eq_comp {W V Z : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS Z.1 Z.2} {a b : V ⟶ Z}
    {α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M}
    {P Q R : W ⟶ V} (h : TransitionCocycle B S hS M α P Q R) (ht : R ≫ a = P ≫ a)
    (hm : P ≫ b = Q ≫ a) (hs : R ≫ b = Q ≫ b) :
    modulePullbackReindex R α =
      pullbackTransport M ht ≫
        (modulePullbackReindex P α ≫ pullbackTransport M hm ≫ modulePullbackReindex Q α) ≫
        pullbackTransport M hs.symm :=
  (transitionReindex_eq_modulePullbackReindex M α R).symm.trans
    ((h ht hm hs).trans (transitionComposite_eq_comp M α P Q R ht hm hs))

/-- The cocycle law, from its form written with composition. -/
theorem TransitionCocycle.of_eq_comp {W V Z : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS Z.1 Z.2} {a b : V ⟶ Z}
    {α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M} {P Q R : W ⟶ V}
    (h : ∀ (ht : R ≫ a = P ≫ a) (hm : P ≫ b = Q ≫ a) (hs : R ≫ b = Q ≫ b),
      modulePullbackReindex R α =
        pullbackTransport M ht ≫
          (modulePullbackReindex P α ≫ pullbackTransport M hm ≫ modulePullbackReindex Q α) ≫
          pullbackTransport M hs.symm) : TransitionCocycle B S hS M α P Q R := fun ht hm hs =>
  (transitionReindex_eq_modulePullbackReindex M α R).trans
    ((h ht hm hs).trans (transitionComposite_eq_comp M α P Q R ht hm hs).symm)

/-- The unit law, written with `AlgebraicGeometry.Space.modulePullbackReindex`. -/
theorem TransitionUnit.eq' {W V Z : AlgebraicSpaces B S hS} {M : Modules.{u, u} B S hS Z.1 Z.2}
    {a b : V ⟶ Z} {α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M}
    {e : W ⟶ V} (h : TransitionUnit B S hS M α e) (hab : e ≫ a = e ≫ b) :
    modulePullbackReindex e α = pullbackTransport M hab :=
  (transitionReindex_eq_modulePullbackReindex M α e).symm.trans (h hab)

/-- The unit law, from its form written with `AlgebraicGeometry.Space.modulePullbackReindex`. -/
theorem TransitionUnit.of_eq' {W V Z : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS Z.1 Z.2} {a b : V ⟶ Z}
    {α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M} {e : W ⟶ V}
    (h : ∀ hab : e ≫ a = e ≫ b, modulePullbackReindex e α = pullbackTransport M hab) :
    TransitionUnit B S hS M α e := fun hab =>
  (transitionReindex_eq_modulePullbackReindex M α e).trans (h hab)

/-- Reindexing along `f` is injective exactly where the inverse image along `f` is. -/
theorem modulePullbackReindex_eq_iff {W V Z : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS Z.1 Z.2} {a b : V ⟶ Z} (f : W ⟶ V)
    (α β : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M) :
    modulePullbackReindex f α = modulePullbackReindex f β ↔
      (modulePullback B S hS f).map α = (modulePullback B S hS f).map β := by
  refine ⟨fun h => ?_, fun h => by simp only [modulePullbackReindex, h]⟩
  have h' := congrArg (fun z => (modulePullbackCompIso B S hS f a).hom.app M ≫ z ≫
    (modulePullbackCompIso B S hS f b).inv.app M) h
  simp only [modulePullbackReindex, Category.assoc, Iso.hom_inv_id_app_assoc,
    Iso.hom_inv_id_app] at h'
  exact (Category.comp_id _).symm.trans (h'.trans (Category.comp_id _))

/-- Precomposing both sides of an equation of composites with `k` and reassociating. -/
private theorem comp_assoc_congr {C : Type*} [Category C] {X Y Z T : C} (k : X ⟶ Y)
    {f g : Y ⟶ Z} {c d : Z ⟶ T} (e : f ≫ c = g ≫ d) : (k ≫ f) ≫ c = (k ≫ g) ≫ d := by
  rw [Category.assoc, e, Category.assoc]

/-- **The cocycle law at a composed triple gives the equality of the reindexings of the two
sides of the law at the triple.** -/
theorem TransitionCocycle.transitionReindex_eq {W W' V Z : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS Z.1 Z.2) {a b : V ⟶ Z}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) {p q r : W ⟶ V}
    (ht : r ≫ a = p ≫ a) (hm : p ≫ b = q ≫ a) (hs : r ≫ b = q ≫ b) (k : W' ⟶ W)
    (h : TransitionCocycle B S hS F α (k ≫ p) (k ≫ q) (k ≫ r)) :
    transitionReindex B S hS F (transitionReindex B S hS F α r) k =
      transitionReindex B S hS F (transitionComposite B S hS F α p q r ht hm hs) k := by
  have ht' := comp_assoc_congr k ht
  have hm' := comp_assoc_congr k hm
  have hs' := comp_assoc_congr k hs
  rw [transitionReindex_comp, h ht' hm' hs',
    transitionReindex_transitionComposite B S hS F α p q r ht hm hs k ht' hm' hs']

/-- **The equality of the reindexings of the two sides of the cocycle law at a triple gives the
cocycle law at the composed triple.** -/
theorem TransitionCocycle.of_transitionReindex_eq {W W' V Z : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS Z.1 Z.2) {a b : V ⟶ Z}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) {p q r : W ⟶ V}
    (ht : r ≫ a = p ≫ a) (hm : p ≫ b = q ≫ a) (hs : r ≫ b = q ≫ b) (k : W' ⟶ W)
    (h : transitionReindex B S hS F (transitionReindex B S hS F α r) k =
      transitionReindex B S hS F (transitionComposite B S hS F α p q r ht hm hs) k) :
    TransitionCocycle B S hS F α (k ≫ p) (k ≫ q) (k ≫ r) := by
  intro ht' hm' hs'
  rw [← transitionReindex_comp, h,
    transitionReindex_transitionComposite B S hS F α p q r ht hm hs k ht' hm' hs']

/-- **The unit law along a composite gives the equality of the reindexings of the two sides of
the law.** -/
theorem TransitionUnit.transitionReindex_eq {W W' V Z : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS Z.1 Z.2) {a b : V ⟶ Z}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) {f : W ⟶ V}
    (hf : f ≫ a = f ≫ b) (k : W' ⟶ W) (h : TransitionUnit B S hS F α (k ≫ f)) :
    transitionReindex B S hS F (transitionReindex B S hS F α f) k =
      transitionReindex B S hS F (pullbackTransport F hf) k := by
  rw [transitionReindex_comp, h (comp_assoc_congr k hf),
    transitionReindex_pullbackTransport]

/-- **The equality of the reindexings of the two sides of the unit law gives the unit law along
the composite.** -/
theorem TransitionUnit.of_transitionReindex_eq {W W' V Z : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS Z.1 Z.2) {a b : V ⟶ Z}
    (α : (modulePullback B S hS a).obj F ⟶ (modulePullback B S hS b).obj F) {f : W ⟶ V}
    (hf : f ≫ a = f ≫ b) (k : W' ⟶ W)
    (h : transitionReindex B S hS F (transitionReindex B S hS F α f) k =
      transitionReindex B S hS F (pullbackTransport F hf) k) :
    TransitionUnit B S hS F α (k ≫ f) := by
  intro h'
  rw [← transitionReindex_comp, h, transitionReindex_pullbackTransport]

end Predicates

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : AlgebraicSpaces B S hS} (Γ : GroupoidInAlgebraicSpaces B S hS A)
  {Z V : AlgebraicSpaces B S hS} (ρ : Γ.objects ⟶ Z) (M : Modules.{u, u} B S hS Z.1 Z.2)
  {a b : V ⟶ Z} (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M)
  (τ : Γ.arrows ⟶ V) (ha : Γ.target ≫ ρ = τ ≫ a) (hb : τ ≫ b = Γ.source ≫ ρ)

/-- The transition morphism `t^*ρ^*ℳ ⟶ s^*ρ^*ℳ` induced by `α` along `τ`. -/
def transitionOfReindex :
    (modulePullback B S hS Γ.target).obj ((modulePullback B S hS ρ).obj M) ⟶
      (modulePullback B S hS Γ.source).obj ((modulePullback B S hS ρ).obj M) :=
  modulePullbackUnflatten ρ
    (comp₃ (pullbackTransport M ha) (modulePullbackReindex τ α) (pullbackTransport M hb))

/-- `AlgebraicGeometry.Space.transitionOfReindex` unfolded. -/
theorem transitionOfReindex_eq :
    transitionOfReindex Γ ρ M α τ ha hb = modulePullbackUnflatten ρ
      (comp₃ (pullbackTransport M ha) (modulePullbackReindex τ α) (pullbackTransport M hb)) :=
  rfl

/-- Flattened, the induced transition morphism is the composite of `τ^*α` with the two
transports along `ha` and `hb`. -/
theorem modulePullbackFlatten_transitionOfReindex :
    modulePullbackFlatten ρ (transitionOfReindex Γ ρ M α τ ha hb) =
      pullbackTransport M ha ≫ modulePullbackReindex τ α ≫ pullbackTransport M hb :=
  (modulePullbackFlatten_unflatten ρ _).trans
    (comp₃_eq (pullbackTransport M ha) (modulePullbackReindex τ α) (pullbackTransport M hb))

/-- **The cocycle law for the induced transition morphism.** -/
theorem transitionOfReindex_cocycle
    (hcoc : TransitionCocycle B S hS M α (firstArrow Γ ≫ τ) (secondArrow Γ ≫ τ) (Γ.comp ≫ τ)) :
    groupoidPullbackTransition B S hS Γ ((modulePullback B S hS ρ).obj M)
        (transitionOfReindex Γ ρ M α τ ha hb) Γ.comp =
      groupoidTransitionComposite B S hS Γ ((modulePullback B S hS ρ).obj M)
        (transitionOfReindex Γ ρ M α τ ha hb) := by
  have ht : (Γ.comp ≫ τ) ≫ a = (firstArrow Γ ≫ τ) ≫ a := by
    rw [Category.assoc, Category.assoc, ← ha, ← Category.assoc, comp_comp_target,
      Category.assoc]
  have hm : (firstArrow Γ ≫ τ) ≫ b = (secondArrow Γ ≫ τ) ≫ a := by
    rw [Category.assoc, Category.assoc, hb, ← ha, ← Category.assoc, firstArrow_comp_source,
      Category.assoc]
  have hs : (Γ.comp ≫ τ) ≫ b = (secondArrow Γ ≫ τ) ≫ b := by
    rw [Category.assoc, Category.assoc, hb, ← Category.assoc, comp_comp_source,
      Category.assoc]
  rw [groupoidPullbackTransition_eq_transitionReindex,
    transitionReindex_eq_modulePullbackReindex, groupoidTransitionComposite_eq,
    transitionComposite_eq_comp]
  exact modulePullbackReindex_cocycle_of_flatten (modulePullbackCompIsoAssoc B S hS) ρ τ M α
    (transitionOfReindex Γ ρ M α τ ha hb)
    (modulePullbackFlatten_transitionOfReindex Γ ρ M α τ ha hb)
    (firstArrow Γ) (secondArrow Γ) Γ.comp (firstArrow Γ ≫ τ) (secondArrow Γ ≫ τ) (Γ.comp ≫ τ)
    rfl rfl rfl (comp_comp_target Γ) (firstArrow_comp_source Γ) (comp_comp_source Γ) ht hm hs
    (hcoc.eq_comp ht hm hs)

/-- **The unit law for the induced transition morphism.** -/
theorem transitionOfReindex_unit (hunit : TransitionUnit B S hS M α (identityArrow Γ ≫ τ)) :
    groupoidPullbackTransition B S hS Γ ((modulePullback B S hS ρ).obj M)
        (transitionOfReindex Γ ρ M α τ ha hb) (identityArrow Γ) =
      pullbackTransport ((modulePullback B S hS ρ).obj M)
        ((identityArrow_comp_target Γ).trans (identityArrow_comp_source Γ).symm) := by
  have E : identityArrow Γ ≫ Γ.target ≫ ρ = identityArrow Γ ≫ Γ.source ≫ ρ := by
    rw [← Category.assoc, identityArrow_comp_target, ← Category.assoc,
      identityArrow_comp_source]
  have e₁ : identityArrow Γ ≫ Γ.target ≫ ρ = identityArrow Γ ≫ τ ≫ a :=
    congrArg (identityArrow Γ ≫ ·) ha
  have e₂ : identityArrow Γ ≫ τ ≫ b = identityArrow Γ ≫ Γ.source ≫ ρ :=
    congrArg (identityArrow Γ ≫ ·) hb
  have E₁ : identityArrow Γ ≫ τ ≫ a = (identityArrow Γ ≫ τ) ≫ a := (Category.assoc _ _ _).symm
  have E₂ : (identityArrow Γ ≫ τ) ≫ b = identityArrow Γ ≫ τ ≫ b := Category.assoc _ _ _
  have hab : (identityArrow Γ ≫ τ) ≫ a = (identityArrow Γ ≫ τ) ≫ b := by
    rw [← E₁, ← e₁, E, ← e₂, E₂]
  refine modulePullbackFlatten_injective ρ ?_
  rw [groupoidPullbackTransition_eq_transitionReindex,
    transitionReindex_eq_modulePullbackReindex,
    modulePullbackFlatten_pullbackTransport ρ _ M E, transitionOfReindex_eq,
    modulePullbackFlatten_reindex_unflatten B S hS ρ _ (identityArrow Γ),
    comp₃_eq (pullbackTransport M ha) (modulePullbackReindex τ α) (pullbackTransport M hb),
    modulePullbackReindex_comp₃ B S hS _ _ _ _,
    modulePullbackReindex_pullbackTransport _ ha M e₁,
    modulePullbackReindex_pullbackTransport _ hb M e₂,
    modulePullbackReindex_comp' (modulePullbackCompIsoAssoc B S hS) (identityArrow Γ) τ _ rfl α
      E₁ E₂, hunit.eq' hab,
    pullbackTransport_comp₃ B S hS M E₁ hab E₂ (E₁.trans (hab.trans E₂)),
    pullbackTransport_comp₃ B S hS M e₁ _ e₂ E]

/-- **A quasi-coherent module on a groupoid from a transition morphism on another space**
(Stacks 0441): `(ρ^*ℳ, τ^*α)`, given the cocycle and the unit law of `α` at the images of the
composable pairs and of the unit. -/
def quasicoherentModuleOfReindex (hM : M.IsQuasicoherentOnSite)
    (hcoc : TransitionCocycle B S hS M α (firstArrow Γ ≫ τ) (secondArrow Γ ≫ τ) (Γ.comp ≫ τ))
    (hunit : TransitionUnit B S hS M α (identityArrow Γ ≫ τ)) :
    QuasicoherentModule B S hS Γ where
  F := ⟨(modulePullback B S hS ρ).obj M,
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS ρ M hM⟩
  alpha := transitionOfReindex Γ ρ M α τ ha hb
  cocycle := transitionOfReindex_cocycle Γ ρ M α τ ha hb hcoc
  unit := transitionOfReindex_unit Γ ρ M α τ ha hb hunit

/-! ### The laws for transported identifications -/

section Transported

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A morphism whose reindexings are transported identifications satisfies the cocycle
law**, at a triple whose endpoints match in `U`. -/
theorem transitionCocycle_of_descentTransport {U Y Z V W : AlgebraicSpaces B S hS} {π : U ⟶ Z}
    {u : U ⟶ Y} {M : Modules.{u, u} B S hS Z.1 Z.2} {G : Modules.{u, u} B S hS Y.1 Y.2}
    (ι : (modulePullback B S hS π).obj M ≅ (modulePullback B S hS u).obj G) {a b : V ⟶ Z}
    (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M) (P Q R : W ⟶ V)
    {xP yP xQ yQ xR yR : W ⟶ U}
    (haP : xP ≫ π = P ≫ a) (hbP : yP ≫ π = P ≫ b) (hP : xP ≫ u = yP ≫ u)
    (haQ : xQ ≫ π = Q ≫ a) (hbQ : yQ ≫ π = Q ≫ b) (hQ : xQ ≫ u = yQ ≫ u)
    (haR : xR ≫ π = R ≫ a) (hbR : yR ≫ π = R ≫ b) (hR : xR ≫ u = yR ≫ u)
    (hαP : modulePullbackReindex P α = descentTransport π u ι haP hbP hP)
    (hαQ : modulePullbackReindex Q α = descentTransport π u ι haQ hbQ hQ)
    (hαR : modulePullbackReindex R α = descentTransport π u ι haR hbR hR)
    (h₁ : xR = xP) (h₂ : yP = xQ) (h₃ : yR = yQ) :
    TransitionCocycle B S hS M α P Q R := by
  refine TransitionCocycle.of_eq_comp fun ht hm hs => ?_
  have hPQ : xP ≫ u = yQ ≫ u := hP.trans ((congrArg (· ≫ u) h₂).trans hQ)
  have haQ' : xQ ≫ π = P ≫ b := haQ.trans hm.symm
  have haR' : xP ≫ π = R ≫ a := (congrArg (· ≫ π) h₁.symm).trans haR
  have hbR' : yQ ≫ π = R ≫ b := (congrArg (· ≫ π) h₃.symm).trans hbR
  refine hαR.trans ((descentTransport_congr ι haR hbR hR h₁ h₃ haR' hbR' hPQ).trans ?_)
  refine Eq.symm ((comp₃_congr rfl (comp₃_congr hαP rfl hαQ) rfl).trans ?_)
  refine (congrArg (fun z => pullbackTransport M ht ≫ (descentTransport π u ι haP hbP hP ≫ z) ≫
    pullbackTransport M hs.symm)
      (pullbackTransport_comp_descentTransport ι haQ hbQ hQ hm haQ')).trans ?_
  refine (congrArg (fun z => pullbackTransport M ht ≫ z ≫ pullbackTransport M hs.symm)
    (descentTransport_comp ι haP hbP haQ' hbQ hP hQ h₂ hPQ)).trans ?_
  exact pullbackTransport_comp_descentTransport_comp ι haP hbQ hPQ ht hs.symm haR' hbR'

/-- **A morphism whose reindexing along `e` is a transported identification of equal
morphisms satisfies the unit law at `e`.** -/
theorem transitionUnit_of_descentTransport {U Y Z V W : AlgebraicSpaces B S hS} {π : U ⟶ Z}
    {u : U ⟶ Y} {M : Modules.{u, u} B S hS Z.1 Z.2} {G : Modules.{u, u} B S hS Y.1 Y.2}
    (ι : (modulePullback B S hS π).obj M ≅ (modulePullback B S hS u).obj G) {a b : V ⟶ Z}
    (α : (modulePullback B S hS a).obj M ⟶ (modulePullback B S hS b).obj M) (e : W ⟶ V)
    {x y : W ⟶ U} (ha : x ≫ π = e ≫ a) (hb : y ≫ π = e ≫ b) (h : x ≫ u = y ≫ u)
    (hα : modulePullbackReindex e α = descentTransport π u ι ha hb h) (hxy : x = y) :
    TransitionUnit B S hS M α e := TransitionUnit.of_eq' fun hab =>
  hα.trans (descentTransport_eq_pullbackTransport ι ha hb h hxy hab)

end Transported

end AlgebraicGeometry.Space

end
