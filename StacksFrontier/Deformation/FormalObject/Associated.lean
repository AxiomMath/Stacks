module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Cofibered
public import StacksFrontier.Deformation.Completed.Basic
public import StacksFrontier.Deformation.FormalObject.Basic
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.Smooth.Pushforward
import StacksCore.Tactic.EgaSgaAttribute
import StacksFrontier.Deformation.FormalObject.AdicQuotient

/-!
# The morphism associated to a formal object

A formal object determines a morphism from the localization of the
completed base category at its underlying algebra.

## Main definitions

* `ChosenPushforwards` is a simultaneous
  choice of a pushforward along every arrow of the base category.
* `AssociatedMorphism` records the associated
  morphism and its prescribed value at every Artinian point of `R`.
* `associatedMorphism` constructs this morphism
  from a formal object and chosen pushforwards.

## Implementation notes

The restriction of the represented functor is `restrictedCoyoneda`; its associated
cofibered set is its category of elements, with projection `CategoryOfElements.π`.  Since the
formal object uses the quotient by `𝔪_R^(n+1)` at level `n`, the least positive exponent
`m` in the source is represented below by `n + 1`.

The tagged construction `associatedMorphism` returns a based functor together with its object
formula and the commuting triangles that characterize its action on arrows.  The field
`toBasedFunctor` supplies the functor and its equality over the base; `obj_eq` and
`map_pointInclusion` expose the two defining formulas without unfolding the construction.
The transition from a common later level is the composite `transitionTo` of the given
transition maps.  Cocartesianness makes the arrow satisfying the displayed triangle unique.

## References

* [Stacks Project, Tag 06HC](https://stacks.math.columbia.edu/tag/06HC)
-/

@[expose] public section

namespace Deformation

/-! ### The morphism associated to a formal object -/

section
open CategoryTheory
universe u v w uF vF

open IsLocalRing

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- A simultaneous choice of a cocartesian pushforward in `F` along every arrow of the
base category. -/
public abbrev ChosenPushforwards (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) :=
  ∀ ⦃B A : ArtinianLocalAlgCat.{u, v, w} Λ k⦄ (f : B ⟶ A), PushforwardChoice p f

/-- A category cofibered in groupoids admits a choice of pushforwards: a pushforward of every
object along every arrow of the base exists, and in a category cofibered in groupoids every
arrow is cocartesian over its image. -/
public noncomputable def chosenPushforwardsOfCofibered
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k) (hp : IsCofiberedInGroupoids p) :
    ChosenPushforwards p := by
  classical
  intro B A f
  choose y i hi using fun x : p.Fiber B ↦ exists_pushforward hp f x.1 x.2
  exact
    { obj := fun x ↦ ⟨y x, by
        have := hi x
        exact IsHomLift.codomain_eq p f (i x)⟩
      inclusion := i
      cocartesian := fun x ↦
        isStronglyCocartesian_of_isCofiberedInGroupoids hp f (i x) (hi x) }

/-- The map `a` is induced by the Artinian point `α` at the least positive nilpotence
exponent of the target maximal ideal.  Level `n` is the quotient by `𝔪_R^(n+1)`. -/
public abbrev IsTruncationFactorization
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (α : (restrictedCoyoneda R).obj A) (n : ℕ)
    (a : AdicTruncation.obj R n ⟶ A) : Prop :=
  (maximalIdeal A ^ (n + 1) = ⊥) ∧
    (∀ j : ℕ, (maximalIdeal A ^ (j + 1) = ⊥ → n ≤ j)) ∧
      a.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) = α.hom

/-- The composite of the transition maps from level `n + d` of a formal object to level `n`. -/
@[implicit_reducible]
public def transitionIter (ξ : FormalObject p) (n : ℕ) :
    (d : ℕ) → ξ.level (n + d) ⟶ ξ.level n
  | 0 => 𝟙 _
  | d + 1 => ξ.transition (n + d) ≫ transitionIter ξ n d

/-- The transition map from a later level `m` of a formal object to an earlier level `n`. -/
@[implicit_reducible]
public def transitionTo (ξ : FormalObject p) {n m : ℕ} (h : n ≤ m) :
    ξ.level m ⟶ ξ.level n :=
  eqToHom (congrArg ξ.level (Nat.add_sub_of_le h).symm) ≫ transitionIter ξ n (m - n)

/-- The morphism associated to a formal object, together with the formula specifying its value
at every Artinian point of the complete local base. -/
public structure AssociatedMorphism
    (ξ : FormalObject p) (pushforwards : ChosenPushforwards p) where
  /-- The underlying morphism of categories over `𝒞_Λ`. -/
  toBasedFunctor :
    BasedFunctor
      (BasedCategory.ofFunctor (CategoryOfElements.π (restrictedCoyoneda ξ.base)))
      (BasedCategory.ofFunctor p)
  /-- The least nilpotence exponent of the target maximal ideal, minus one. -/
  level : (α : (restrictedCoyoneda ξ.base).Elements) → ℕ
  /-- The map from the selected adic truncation induced by the Artinian point. -/
  factor : (α : (restrictedCoyoneda ξ.base).Elements) →
    AdicTruncation.obj ξ.base (level α) ⟶ α.1
  /-- The selected level is least and `factor α` is induced by `α`. -/
  factor_spec : ∀ α, IsTruncationFactorization α.2 (level α) (factor α)
  /-- At `α : R → A`, the associated morphism is the chosen pushforward of `ξ_n` along
  the induced map `R/𝔪_R^(n+1) → A`, for the least such `n`. -/
  obj_eq : ∀ α, toBasedFunctor.obj α =
    ((pushforwards (factor α)).obj ⟨ξ.level (level α), ξ.level_eq (level α)⟩).1
  /-- The canonical arrow from the selected level of `ξ` to the value at `α`. -/
  pointInclusion : ∀ α, ξ.level (level α) ⟶ toBasedFunctor.obj α
  /-- `pointInclusion` is the chosen cocartesian arrow, after identifying its codomain by
  `obj_eq`. -/
  pointInclusion_eq : ∀ α,
    pointInclusion α ≫ eqToHom (obj_eq α) =
      (pushforwards (factor α)).inclusion
        ⟨ξ.level (level α), ξ.level_eq (level α)⟩
  /-- The action on arrows is induced by the transition maps and the chosen pushforwards:
  after passing both endpoints to a common level, the defining triangle commutes. -/
  map_pointInclusion : ∀ {α β} (g : α ⟶ β),
    transitionTo ξ (Nat.le_max_left (level α) (level β)) ≫
        pointInclusion α ≫ toBasedFunctor.map g =
      transitionTo ξ (Nat.le_max_right (level α) (level β)) ≫
        pointInclusion β

private alias exists_nilpotence := exists_maximalIdeal_pow_succ_eq_bot_of_isArtinian

private lemma exists_factor {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k} (α : (restrictedCoyoneda R).obj A)
    {n : ℕ} (hn : maximalIdeal A ^ (n + 1) = ⊥) :
    ∃ a : AdicTruncation.obj R n ⟶ A,
      a.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) = α.hom := by
  have : IsLocalHom α.hom.toRingHom := α.isLocal
  let : Nontrivial (R ⧸ AdicTruncation.ideal R n) :=
    inferInstanceAs (Nontrivial (AdicTruncation.obj R n))
  let : IsLocalRing (R ⧸ AdicTruncation.ideal R n) :=
    inferInstanceAs (IsLocalRing (AdicTruncation.obj R n))
  have hker : AdicTruncation.ideal R n ≤ RingHom.ker α.hom.toRingHom := by
    show AdicTruncation.ideal R n ≤
      (⊥ : Ideal (artinianToComplete.obj A)).comap α.hom.toRingHom
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact (Ideal.pow_right_mono (map_maximalIdeal_le α.hom.toRingHom) _).trans_eq hn
  let f := Ideal.Quotient.liftₐ (AdicTruncation.ideal R n) α.hom hker
  have hf : IsLocalHom f.toRingHom := by
    constructor; intro x hx
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Ideal.Quotient.mk (AdicTruncation.ideal R n)).isUnit_map
      (α.isLocal.map_nonunit r hx)
  refine ⟨{ hom := f, isLocal := hf, residue_comm := ?_ }, ?_⟩
  · intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    show A.residueEquiv (residue A (α.hom r)) =
      AdicTruncation.residueEquiv R n (residue _ (Ideal.Quotient.mk _ r))
    rw [AdicTruncation.residueEquiv_residue_mk]
    exact α.residue_comm r
  · ext r; rfl

private lemma exists_truncation {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k} (α : (restrictedCoyoneda R).obj A) :
    ∃ n, ∃ a : AdicTruncation.obj R n ⟶ A, IsTruncationFactorization α n a := by
  classical
  obtain ⟨a, ha⟩ := exists_factor α (Nat.find_spec (exists_nilpotence A))
  exact ⟨_, a, Nat.find_spec (exists_nilpotence A),
    fun j hj ↦ Nat.find_min' (exists_nilpotence A) hj, ha⟩

/-- The transition map from a level of a formal object to itself is the identity. -/
public lemma transitionTo_self (ξ : FormalObject p) (n : ℕ) :
    transitionTo ξ (le_refl n) = 𝟙 _ := by
  unfold transitionTo; generalize_proofs h; revert h; rw [Nat.sub_self]
  intro h; simp [transitionIter]

/-- The transition map from level `m + 1` factors through the transition map from level `m`. -/
public lemma transitionTo_succ (ξ : FormalObject p) {n m : ℕ} (h : n ≤ m) :
    transitionTo ξ (h.trans (Nat.le_succ m)) =
      ξ.transition m ≫ transitionTo ξ h := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold transitionTo
  generalize_proofs h₁ h₂
  revert h₁ h₂
  rw [Nat.succ_sub h, Nat.add_sub_cancel_left]
  intro h₁ h₂
  simp [transitionIter]

/-- The transition maps of a formal object compose. -/
public lemma transitionTo_comp (ξ : FormalObject p) {n m l : ℕ}
    (h : n ≤ m) (h' : m ≤ l) :
    transitionTo ξ h' ≫ transitionTo ξ h = transitionTo ξ (h.trans h') := by
  induction l, h' using Nat.le_induction with
  | base => simp [transitionTo_self]
  | succ l hl ih =>
    rw [transitionTo_succ ξ hl, transitionTo_succ ξ (h.trans hl), Category.assoc, ih]

/-- A transition map of a formal object lies over a map of adic truncations compatible with
the quotient maps from the complete base. -/
public lemma transitionTo_lift (ξ : FormalObject p) {n m : ℕ} (h : n ≤ m) :
    ∃ t : AdicTruncation.obj ξ.base m ⟶ AdicTruncation.obj ξ.base n,
      t.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base m)) =
        Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base n) ∧
      p.IsHomLift t (transitionTo ξ h) := by
  induction m, h using Nat.le_induction with
  | base =>
    refine ⟨𝟙 _, rfl, ?_⟩
    rw [transitionTo_self]; exact IsHomLift.id (ξ.level_eq n)
  | succ m hm ih =>
    obtain ⟨t, ht, htl⟩ := ih
    refine ⟨AdicTruncation.transition ξ.base m ≫ t, ?_, ?_⟩
    · apply AlgHom.ext; intro r
      exact DFunLike.congr_fun ht r
    · rw [transitionTo_succ ξ hm]
      have : p.IsHomLift (AdicTruncation.transition ξ.base m) (ξ.transition m) :=
        ξ.transition_lift m
      exact IsHomLift.comp p _ _ _ _

/-- A lift of a point of `α` at level `n` extends to every later level `m`, along the
transition map of `ξ`. -/
public lemma point_lift (ξ : FormalObject p)
    {α : (restrictedCoyoneda ξ.base).Elements} {n m : ℕ}
    {a : AdicTruncation.obj ξ.base n ⟶ α.1}
    (ha : a.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base n)) = α.2.hom)
    {x : F} (i : ξ.level n ⟶ x) (hi : p.IsHomLift a i) (h : n ≤ m) :
    ∃ b : AdicTruncation.obj ξ.base m ⟶ α.1,
      b.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base m)) = α.2.hom ∧
      p.IsHomLift b (transitionTo ξ h ≫ i) := by
  obtain ⟨t, ht, htl⟩ := transitionTo_lift ξ h
  refine ⟨t ≫ a, ?_, IsHomLift.comp p _ _ _ _⟩
  refine AlgHom.ext fun r => ?_
  show a.hom (t.hom (Ideal.Quotient.mk _ r)) = α.2.hom r
  exact (congrArg a.hom (DFunLike.congr_fun ht r)).trans (DFunLike.congr_fun ha r)

private lemma point_base_comp {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    {α β : (restrictedCoyoneda R).Elements} (g : α ⟶ β) {n : ℕ}
    {a : AdicTruncation.obj R n ⟶ α.1} {b : AdicTruncation.obj R n ⟶ β.1}
    (ha : a.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) = α.2.hom)
    (hb : b.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal R n)) = β.2.hom) :
    a ≫ g.hom = b := by
  apply ArtinianLocalAlgCat.hom_ext; apply AlgHom.ext; intro x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  show g.hom.hom (a.hom (Ideal.Quotient.mk _ r)) = b.hom (Ideal.Quotient.mk _ r)
  have hg := congrArg (fun f : (restrictedCoyoneda R).obj β.1 ↦ f.hom r) g.map_val
  change g.hom.hom (α.2.hom r) = β.2.hom r at hg
  exact (congrArg g.hom.hom (DFunLike.congr_fun ha r)).trans
    (hg.trans (DFunLike.congr_fun hb r).symm)

private lemma exists_point_map (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p) {α β : (restrictedCoyoneda ξ.base).Elements} (g : α ⟶ β)
    {nα nβ : ℕ} {a : AdicTruncation.obj ξ.base nα ⟶ α.1}
    {b : AdicTruncation.obj ξ.base nβ ⟶ β.1}
    (ha : a.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base nα)) = α.2.hom)
    (hb : b.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base nβ)) = β.2.hom)
    {x y : F} (i : ξ.level nα ⟶ x) (j : ξ.level nβ ⟶ y)
    (hi : p.IsHomLift a i) (hj : p.IsHomLift b j) :
    ∃ φ : x ⟶ y, p.IsHomLift g.hom φ ∧
      ∀ (m : ℕ) (hα : nα ≤ m) (hβ : nβ ≤ m),
        transitionTo ξ hα ≫ i ≫ φ = transitionTo ξ hβ ≫ j := by
  obtain ⟨a', ha', hia⟩ := point_lift ξ ha i hi (Nat.le_max_left nα nβ)
  obtain ⟨b', hb', hjb⟩ := point_lift ξ hb j hj (Nat.le_max_right nα nβ)
  have := isStronglyCocartesian_of_isCofiberedInGroupoids hp a'
    (transitionTo ξ (Nat.le_max_left nα nβ) ≫ i) inferInstance
  obtain ⟨φ, ⟨hφ, hfac⟩, _⟩ := Functor.IsStronglyCocartesian.universal_property
    p a' (transitionTo ξ (Nat.le_max_left nα nβ) ≫ i) g.hom b'
    (point_base_comp g ha' hb').symm (transitionTo ξ (Nat.le_max_right nα nβ) ≫ j)
  refine ⟨φ, hφ, ?_⟩
  intro m hα hβ
  have h := congrArg (fun t ↦ transitionTo ξ (max_le hα hβ) ≫ t) hfac
  simpa only [← Category.assoc, transitionTo_comp] using h

private lemma point_map_ext (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p) {α : (restrictedCoyoneda ξ.base).Elements} {n m : ℕ}
    {a : AdicTruncation.obj ξ.base n ⟶ α.1}
    (ha : a.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base n)) = α.2.hom)
    {x y : F} (i : ξ.level n ⟶ x) (hi : p.IsHomLift a i) (h : n ≤ m)
    {B : ArtinianLocalAlgCat.{u, v, w} Λ k} (g : α.1 ⟶ B)
    {φ ψ : x ⟶ y} (hφ : p.IsHomLift g φ) (hψ : p.IsHomLift g ψ)
    (hw : transitionTo ξ h ≫ i ≫ φ = transitionTo ξ h ≫ i ≫ ψ) : φ = ψ := by
  obtain ⟨b, _, hb⟩ := point_lift ξ ha i hi h
  have := isStronglyCocartesian_of_isCofiberedInGroupoids hp b (transitionTo ξ h ≫ i) inferInstance
  apply Functor.IsStronglyCocartesian.ext p b (transitionTo ξ h ≫ i) g
  simpa only [Category.assoc] using hw

private lemma exists_associatedMorphism
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (pushforwards : ChosenPushforwards p) : Nonempty (AssociatedMorphism ξ pushforwards) := by
  classical
  choose l a ha using
    (fun α : (restrictedCoyoneda ξ.base).Elements ↦ exists_truncation α.2)
  let O (α : (restrictedCoyoneda ξ.base).Elements) : F :=
    ((pushforwards (a α)).obj ⟨ξ.level (l α), ξ.level_eq (l α)⟩).1
  let i (α : (restrictedCoyoneda ξ.base).Elements) : ξ.level (l α) ⟶ O α :=
    (pushforwards (a α)).inclusion ⟨ξ.level (l α), ξ.level_eq (l α)⟩
  have hi (α : (restrictedCoyoneda ξ.base).Elements) : p.IsHomLift (a α) (i α) :=
    (pushforwards (a α)).cocartesian ⟨ξ.level (l α), ξ.level_eq (l α)⟩ |>.toIsHomLift
  have hO (α : (restrictedCoyoneda ξ.base).Elements) : p.obj (O α) = α.1 :=
    ((pushforwards (a α)).obj ⟨ξ.level (l α), ξ.level_eq (l α)⟩).2
  have hm {α β : (restrictedCoyoneda ξ.base).Elements} (g : α ⟶ β) :=
    exists_point_map hp ξ g (ha α).2.2 (ha β).2.2 (i α) (i β) (hi α) (hi β)
  let φ {α β : (restrictedCoyoneda ξ.base).Elements} (g : α ⟶ β) : O α ⟶ O β :=
    Classical.choose (hm g)
  have hφ {α β : (restrictedCoyoneda ξ.base).Elements} (g : α ⟶ β) :
      p.IsHomLift g.hom (φ g) := (Classical.choose_spec (hm g)).1
  have htriangle {α β : (restrictedCoyoneda ξ.base).Elements} (g : α ⟶ β)
      (m : ℕ) (hα : l α ≤ m) (hβ : l β ≤ m) :
      transitionTo ξ hα ≫ i α ≫ φ g = transitionTo ξ hβ ≫ i β :=
    (Classical.choose_spec (hm g)).2 m hα hβ
  have hid (α : (restrictedCoyoneda ξ.base).Elements) : φ (𝟙 α) = 𝟙 (O α) := by
    apply point_map_ext hp ξ (ha α).2.2 (i α) (hi α) (le_refl (l α)) (𝟙 α.1)
      (hφ (𝟙 α)) (IsHomLift.id (hO α))
    simpa only [Category.comp_id] using htriangle (𝟙 α) (l α) le_rfl le_rfl
  have hcomp {α β γ : (restrictedCoyoneda ξ.base).Elements} (g : α ⟶ β) (h : β ⟶ γ) :
      φ (g ≫ h) = φ g ≫ φ h := by
    let m := max (max (l α) (l β)) (l γ)
    have hα : l α ≤ m := (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
    have hβ : l β ≤ m := (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
    have hγ : l γ ≤ m := Nat.le_max_right _ _
    have hg := hφ g
    have hh := hφ h
    apply point_map_ext hp ξ (ha α).2.2 (i α) (hi α) hα (g.hom ≫ h.hom)
      (hφ (g ≫ h)) (IsHomLift.comp p _ _ _ _)
    rw [htriangle (g ≫ h) m hα hγ, ← Category.assoc (i α),
      ← Category.assoc, htriangle g m hα hβ, Category.assoc, htriangle h m hβ hγ]
  let H : (restrictedCoyoneda ξ.base).Elements ⥤ F :=
    { obj := O, map := φ, map_id := hid, map_comp := hcomp }
  have hH : H ⋙ p = CategoryOfElements.π (restrictedCoyoneda ξ.base) := by
    refine CategoryTheory.Functor.ext hO ?_
    intro α β g; have := hφ g; exact IsHomLift.fac' p g.hom (φ g)
  exact ⟨{ toBasedFunctor := { toFunctor := H, w := hH }, level := l,
           factor := a, factor_spec := ha, obj_eq := fun _ ↦ rfl,
           pointInclusion := i, pointInclusion_eq := fun α ↦ Category.comp_id (i α),
           map_pointInclusion := fun {α β} g ↦
             htriangle g _ (Nat.le_max_left (l α) (l β)) (Nat.le_max_right (l α) (l β)) }⟩

/-- **Stacks Project, Tag 06HC.** After choosing pushforwards, a formal object `ξ` over `R`
determines a morphism from the restriction of the cofibered set represented by `R` to `F`.
On an Artinian point `α : R → A`, it is the pushforward of the level indexed by the
least nilpotence exponent of the maximal ideal of `A`, minus one. -/
@[implicit_reducible,
  stacks 06HC "associated_morphism_of_formal_object",
  sga "7 VI 2.2(d)" "construction of ξ^#"]
public noncomputable def associatedMorphism
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (pushforwards : ChosenPushforwards p) : AssociatedMorphism ξ pushforwards :=
  Classical.choice (by exact exists_associatedMorphism hp ξ pushforwards)

end

end Deformation
