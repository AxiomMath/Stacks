module

public import StacksFrontier.CategoryTheory.Sites.Stackification.Stackification
public import StacksFrontier.CategoryTheory.Sites.Stackification.Uniqueness
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.UliftHomStack
public import Mathlib.CategoryTheory.Sigma.Basic

/-!
# The coproduct of a family of stacks in groupoids

Let `(𝒞, J)` be a site and let `pᵢ : 𝒳ᵢ ⥤ 𝒞`, `i ∈ I`, be a family of categories fibred in
groupoids over `𝒞`. Their disjoint union `Σ i, 𝒳ᵢ` (`CategoryTheory.Sigma`) is fibred in
groupoids over `𝒞`, but it is in general *not* a stack, even when every `𝒳ᵢ` is: over an object
`T` of `𝒞` which is a disjoint union `T = T₁ ⊔ T₂`, an object of a stack restricting to objects of
two different summands over `T₁` and `T₂` belongs to no single summand, and over an object covered
by the empty sieve the disjoint union has one object per summand instead of one in all. The
coproduct `∐ᵢ 𝒳ᵢ` in the 2-category of stacks is the stackification of the disjoint union.

## Main definitions

* `CategoryTheory.Functor.sigmaProj`: the structure functor `Σ i, 𝒳ᵢ ⥤ 𝒞` of the disjoint union.
* `CategoryTheory.Functor.StackCoproduct`: the coproduct `∐ᵢ 𝒳ᵢ` of stacks, the stackification
  (Stacks 02ZN) of the disjoint union, with its structure functor
  `CategoryTheory.Functor.stackCoproductProj` and its inclusions
  `CategoryTheory.Functor.stackCoproductι`.

## Main results

* `CategoryTheory.Functor.sigmaProj_isFiberedInGroupoids`: the disjoint union is fibred in
  groupoids.
* `CategoryTheory.Functor.stackCoproductProj_isStack`: `∐ᵢ 𝒳ᵢ` is a stack.
* `CategoryTheory.Functor.exists_isEquivalenceOver_stackCoproduct`: a recognition criterion. If
  `q : 𝒵 ⥤ 𝒞` is a stack in groupoids and `Fᵢ : 𝒳ᵢ ⥤ 𝒵` are fully faithful 1-morphisms over `𝒞`
  such that there are no morphisms between images of different summands except over objects
  covered by the empty sieve, and every object of `𝒵` lies locally in the image of some `Fᵢ`, then
  the functor `∐ᵢ 𝒳ᵢ ⥤ 𝒵` extending the `Fᵢ` is an equivalence over `𝒞`.

## Implementation notes

The stackification of Stacks 02ZN is constructed in the tree for a fibred category whose
morphisms live in a universe containing the universes of the objects of the base and of the
fibred category; the morphisms of the disjoint union are therefore raised by `ULiftHom` before it
is stackified, which changes neither its objects nor its structure functor.
-/

@[expose] public section

namespace CategoryTheory

open Opposite

namespace Functor

universe w vb v v₃ u₁ u₂ u₃

section Equivalence

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒜 : Type u₂} [Category.{v} 𝒜]
  {𝒵 : Type u₃} [Category.{v₃} 𝒵]

/-- A morphism of the morphism-universe lift lies over a morphism of the base exactly when the
underlying morphism does. -/
lemma isHomLift_uliftHomProj_iff (q : 𝒵 ⥤ 𝒞) {R T : 𝒞} (f : R ⟶ T) {a b : ULiftHom.{w} 𝒵}
    (φ : a ⟶ b) : (uliftHomProj q).IsHomLift f φ ↔ q.IsHomLift f φ.down := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := h
    exact isHomLift_map_of_comp_eq (G := ULiftHom.down) (q := q) rfl f φ
  · exact isHomLift_of_isHomLift_map_of_comp_eq (G := ULiftHom.down) (q := q) rfl f φ h

/-- An equivalence over `𝒞` onto the morphism-universe lift of a category over `𝒞`, followed by
forgetting the lift, is an equivalence over `𝒞` onto the category itself. -/
def IsEquivalenceOver.compULiftHomDown {p : 𝒜 ⥤ 𝒞} {q : 𝒵 ⥤ 𝒞} {H : 𝒜 ⥤ ULiftHom.{w} 𝒵}
    (e : IsEquivalenceOver p (uliftHomProj q) H) :
    IsEquivalenceOver p q (H ⋙ ULiftHom.down) where
  inv := ULiftHom.up ⋙ e.inv
  inv_over := by rw [Functor.assoc, e.inv_over]; rfl
  unitIso := e.unitIso
  counitIso :=
    Functor.isoWhiskerLeft ULiftHom.up (Functor.isoWhiskerRight e.counitIso ULiftHom.down)
  unit_vertical := e.unit_vertical
  counit_vertical X := (isHomLift_uliftHomProj_iff q _ _).mp (e.counit_vertical (ULiftHom.objUp X))

end Equivalence

section Sigma

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {I : Type w} {𝒳 : I → Type u₂}
  [∀ i, Category.{v} (𝒳 i)] (p : ∀ i, 𝒳 i ⥤ 𝒞)

/-- The structure functor of the disjoint union `Σ i, 𝒳ᵢ` of a family of categories over `𝒞`. -/
abbrev sigmaProj : (Σ i, 𝒳 i) ⥤ 𝒞 := Sigma.desc p

/-- The structure functor of the disjoint union restricts on the summand `𝒳ᵢ` to `pᵢ`. -/
lemma incl_comp_sigmaProj (i : I) : Sigma.incl i ⋙ sigmaProj p = p i := rfl

/-- **The disjoint union of categories fibred in groupoids is fibred in groupoids.** A morphism of
the base lifts in the summand of its target, and fill-ins exist and are unique in that summand,
morphisms of the disjoint union lying within a single summand. -/
theorem sigmaProj_isFiberedInGroupoids (h : ∀ i, (p i).IsFiberedInGroupoids) :
    (sigmaProj p).IsFiberedInGroupoids where
  exists_lift {V U} f x hx := by
    obtain ⟨i, a⟩ := x
    obtain ⟨y, φ, hφ⟩ := (h i).exists_lift f a hx
    exact ⟨⟨i, y⟩, Sigma.SigmaHom.mk φ, isHomLift_map_of_comp_eq (incl_comp_sigmaProj p i) f φ⟩
  unique_lift {x y z} φ ψ f hf := by
    rcases φ with ⟨φ⟩
    rcases ψ with ⟨ψ⟩
    obtain ⟨χ, ⟨hχ₁, hχ₂⟩, hχ⟩ := (h _).unique_lift φ ψ f hf
    refine ⟨Sigma.SigmaHom.mk χ, ⟨hχ₁, congrArg Sigma.SigmaHom.mk hχ₂⟩, ?_⟩
    rintro ⟨χ'⟩ ⟨h₁, h₂⟩
    exact congrArg Sigma.SigmaHom.mk (hχ χ' ⟨h₁, by injection h₂⟩)

variable (J : GrothendieckTopology 𝒞) (hp : ∀ i, (p i).IsFiberedInGroupoids)

/-- The structure functor of the disjoint union with its morphisms raised to the universe in
which the stackification of Stacks 02ZN is constructed. -/
abbrev sigmaProjLift : ULiftHom.{max u₁ w u₂ vb} (Σ i, 𝒳 i) ⥤ 𝒞 := uliftHomProj (sigmaProj p)

include hp in
/-- The disjoint union of categories fibred in groupoids, with its morphisms raised to a larger
universe, is fibred in groupoids. -/
lemma sigmaProjLift_isFiberedInGroupoids : (sigmaProjLift p).IsFiberedInGroupoids :=
  isFiberedInGroupoids_uliftHomProj _ (sigmaProj_isFiberedInGroupoids p hp)

include hp in
/-- The disjoint union is fibred; this instance is supplied from the fibredness in groupoids of
the summands. -/
lemma sigmaProjLift_isFibered : (sigmaProjLift p).IsFibered :=
  (sigmaProjLift_isFiberedInGroupoids p hp).isFibered

/-- **The coproduct `∐ᵢ 𝒳ᵢ` of a family of stacks in groupoids**: the stackification (Stacks 02ZN)
of their disjoint union. -/
abbrev StackCoproduct : Type _ :=
  have := sigmaProjLift_isFibered p hp
  (sigmaProjLift p).StageThree J

/-- The structure functor `∐ᵢ 𝒳ᵢ ⥤ 𝒞` of the coproduct of stacks. -/
abbrev stackCoproductProj : StackCoproduct p J hp ⥤ 𝒞 :=
  have := sigmaProjLift_isFibered p hp
  (sigmaProjLift p).stageThreeProj J

/-- The 1-morphism from the disjoint union to the coproduct of stacks. -/
noncomputable def toStackCoproduct :
    ULiftHom.{max u₁ w u₂ vb} (Σ i, 𝒳 i) ⥤ StackCoproduct p J hp :=
  have := sigmaProjLift_isFibered p hp
  (sigmaProjLift p).toStageThree J

/-- The inclusion `𝒳ᵢ ⥤ ∐ᵢ 𝒳ᵢ` of a summand into the coproduct of stacks. -/
noncomputable def stackCoproductι (i : I) : 𝒳 i ⥤ StackCoproduct p J hp :=
  Sigma.incl i ⋙ ULiftHom.up ⋙ toStackCoproduct p J hp

/-- **The coproduct of stacks is a stack** (Stacks 02ZN). -/
theorem stackCoproductProj_isStack : (stackCoproductProj p J hp).IsStack J :=
  have := sigmaProjLift_isFibered p hp
  (isStackification_toStageThree.{v, u₁, max w u₂, vb} (sigmaProjLift p) J).1

/-- The inclusions of the summands into the coproduct of stacks are 1-morphisms over `𝒞`. -/
theorem stackCoproductι_comp (i : I) :
    stackCoproductι p J hp i ⋙ stackCoproductProj p J hp = p i := by
  have := sigmaProjLift_isFibered p hp
  show Sigma.incl i ⋙ ULiftHom.up ⋙ ((sigmaProjLift p).toStageThree J ⋙
    (sigmaProjLift p).stageThreeProj J) = p i
  rw [toStageThree_comp_stageThreeProj]
  rfl

end Sigma

section Criterion

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {I : Type w} {𝒳 : I → Type u₂}
  [∀ i, Category.{v} (𝒳 i)]

/-- A morphism between images of objects of the disjoint union under `Sigma.desc F` comes from a
morphism of the disjoint union when both objects lie in the same summand. -/
lemma sigma_desc_full_or {𝒵 : Type u₃} [Category.{v₃} 𝒵] (F : ∀ i, 𝒳 i ⥤ 𝒵)
    [∀ i, (F i).Full] (P : (Σ i, 𝒳 i) → (Σ i, 𝒳 i) → Prop)
    (hP : ∀ (i j : I), i ≠ j → ∀ (a : 𝒳 i) (b : 𝒳 j), ((F i).obj a ⟶ (F j).obj b) → P ⟨i, a⟩ ⟨j, b⟩)
    (a b : Σ i, 𝒳 i) (G : (Sigma.desc F).obj a ⟶ (Sigma.desc F).obj b) :
    (∃ g : a ⟶ b, (Sigma.desc F).map g = G) ∨ P a b := by
  obtain ⟨i, a⟩ := a
  obtain ⟨j, b⟩ := b
  by_cases hij : i = j
  · subst hij
    exact Or.inl ⟨Sigma.SigmaHom.mk ((F i).preimage G), (F i).map_preimage G⟩
  · exact Or.inr (hP i j hij a b G)

/-- The functor `Sigma.desc F` induced by a family of faithful functors is faithful. -/
lemma sigma_desc_map_injective {𝒵 : Type u₃} [Category.{v₃} 𝒵] (F : ∀ i, 𝒳 i ⥤ 𝒵)
    [∀ i, (F i).Faithful] {a b : Σ i, 𝒳 i} (u u' : a ⟶ b)
    (h : (Sigma.desc F).map u = (Sigma.desc F).map u') : u = u' := by
  rcases u with ⟨u⟩
  rcases u' with ⟨u'⟩
  exact congrArg Sigma.SigmaHom.mk ((F _).map_injective h)

/-- Composing `Sigma.desc F` with a functor `q` gives the functor induced by the family
`Fᵢ ⋙ q`. -/
lemma sigma_desc_comp {𝒵 : Type u₃} [Category.{v₃} 𝒵] (F : ∀ i, 𝒳 i ⥤ 𝒵) (q : 𝒵 ⥤ 𝒞) :
    Sigma.desc F ⋙ q = Sigma.desc (fun i => F i ⋙ q) :=
  Functor.hext (fun _ => rfl) (by rintro ⟨i, a⟩ ⟨j, b⟩ ⟨g⟩; exact HEq.rfl)

variable {p : ∀ i, 𝒳 i ⥤ 𝒞} {J : GrothendieckTopology 𝒞} (hp : ∀ i, (p i).IsFiberedInGroupoids)
  {𝒵 : Type u₃} [Category.{max u₁ w u₂ v vb} 𝒵] {q : 𝒵 ⥤ 𝒞}

/-- **Recognising the coproduct of stacks in groupoids.** Let `(𝒞, J)` be a site, let
`pᵢ : 𝒳ᵢ ⥤ 𝒞` be categories fibred in groupoids and let `q : 𝒵 ⥤ 𝒞` be a stack in groupoids.
Let `Fᵢ : 𝒳ᵢ ⥤ 𝒵` be fully faithful functors over `𝒞` such that

* (`hdisj`) a morphism from an object in the image of `Fᵢ` to an object in the image of `Fⱼ`,
  `i ≠ j`, exists only over an object of `𝒞` covered by the empty sieve, and
* (`hloc`) every object of `𝒵` is, locally on `𝒞`, the target of a morphism lying over the
  given morphism of `𝒞` out of an object in the image of some `Fᵢ`.

Then there is an equivalence `∐ᵢ 𝒳ᵢ ⥤ 𝒵` over `𝒞` from the coproduct of stacks whose
restriction to each summand `𝒳ᵢ` is isomorphic to `Fᵢ`. -/
theorem exists_isEquivalenceOver_stackCoproduct (hq : q.IsFiberedInGroupoids) (hqs : q.IsStack J)
    (F : ∀ i, 𝒳 i ⥤ 𝒵) (hF : ∀ i, F i ⋙ q = p i) [∀ i, (F i).Full] [∀ i, (F i).Faithful]
    (hdisj : ∀ (i j : I), i ≠ j → ∀ (a : 𝒳 i) (b : 𝒳 j), ((F i).obj a ⟶ (F j).obj b) →
      (⊥ : Sieve ((p i).obj a)) ∈ J ((p i).obj a))
    (hloc : ∀ z : 𝒵, ∃ R ∈ J (q.obj z), ∀ ⦃V : 𝒞⦄ (f : V ⟶ q.obj z), R f →
      ∃ (i : I) (a : 𝒳 i) (φ : (F i).obj a ⟶ z), q.IsHomLift f φ) :
    ∃ H : StackCoproduct p J hp ⥤ 𝒵, Nonempty (IsEquivalenceOver (stackCoproductProj p J hp) q H) ∧
      ∀ i, Nonempty (stackCoproductι p J hp i ⋙ H ≅ F i) := by
  obtain rfl : p = fun i => F i ⋙ q := funext fun i => (hF i).symm
  have := sigmaProjLift_isFibered _ hp
  have : q.IsFibered := hq.isFibered
  let F' : ULiftHom.{max u₁ w u₂ vb} (Σ i, 𝒳 i) ⥤ 𝒵 := ULiftHom.down ⋙ Sigma.desc F
  have hF'c : F' ⋙ q = sigmaProjLift (fun i => F i ⋙ q) := by
    show ULiftHom.down ⋙ (Sigma.desc F ⋙ q) = ULiftHom.down ⋙ Sigma.desc (fun i => F i ⋙ q)
    rw [sigma_desc_comp]
  have hF'1 : IsFibredOneMorphism (sigmaProjLift (fun i => F i ⋙ q)) q F' :=
    IsFibredOneMorphism.of_isFiberedInGroupoids hq hF'c
  have hG := isFibredOneMorphism_toStageThree (sigmaProjLift (fun i => F i ⋙ q)) J
  obtain ⟨hst, hGmor, hGobj⟩ :=
    isStackification_toStageThree.{v, u₁, max w u₂, vb} (sigmaProjLift (fun i => F i ⋙ q)) J
  have hFmor : ∀ (U : 𝒞) (a b : (sigmaProjLift (fun i => F i ⋙ q)).Fiber U),
      Presheaf.IsLocallyInjective (J.over U) (hF'1.morPresheafMap a b) ∧
        Presheaf.IsLocallySurjective (J.over U) (hF'1.morPresheafMap a b) := by
    intro U a b
    refine ⟨isLocallyInjective_morPresheafMap hF'1 (fun {a b} u u' huu => ?_) U a b,
      isLocallySurjective_morPresheafMap hF'1 (fun {a b} G => ?_) U a b⟩
    · have : u = u' := ULift.ext (sigma_desc_map_injective F u.down u'.down huu)
      subst this
      exact ⟨rfl, ⊤, J.top_mem _, fun _ _ _ => rfl⟩
    · rcases sigma_desc_full_or F (fun a _ => (⊥ : Sieve ((sigmaProj (fun i => F i ⋙ q)).obj a)) ∈
          J ((sigmaProj (fun i => F i ⋙ q)).obj a)) (fun i j hij a b m => hdisj i j hij a b m)
          (ULiftHom.objDown a) (ULiftHom.objDown b) G with ⟨g, hg⟩ | hbot
      · refine ⟨⊤, J.top_mem _, fun w ρ _ => ⟨ρ ≫ ULift.up g, ?_⟩⟩
        rw [F'.map_comp]
        exact congrArg (F'.map ρ ≫ ·) hg.symm
      · exact ⟨⊥, hbot, fun w ρ hρ => hρ.elim⟩
  have hFobj : ∀ (U : 𝒞) (x : q.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
      (fiberFunctorOfCompEq hF'1.comp_eq V).essImage (pullbackFiber q x f) := by
    rintro U ⟨x, rfl⟩
    obtain ⟨R, hR, hRloc⟩ := hloc x
    refine ⟨R, hR, fun V f hf => ?_⟩
    obtain ⟨i, a, φ, hφ⟩ := hRloc f hf
    have ha' : q.obj ((F i).obj a) = V := @IsHomLift.domain_eq _ _ _ _ q _ _ _ _ f φ hφ
    have ha : (sigmaProjLift (fun i => F i ⋙ q)).obj (ULiftHom.objUp ⟨i, a⟩) = V := ha'
    have := hφ
    have hcart : q.IsStronglyCartesian f φ := hq.isStronglyCartesian_homLift f φ
    exact ⟨⟨ULiftHom.objUp ⟨i, a⟩, ha⟩, ⟨fiberIsoOfCartesian f
      (z := (fiberFunctorOfCompEq hF'1.comp_eq V).obj ⟨ULiftHom.objUp ⟨i, a⟩, ha⟩) φ
      (IsPreFibered.pullbackMap (⟨x, rfl⟩ : q.Fiber (q.obj x)).2 f)
      (inferInstance : q.IsCartesian f φ) inferInstance⟩⟩
  obtain ⟨e⟩ := Stackification.nonempty_isEquivalenceOver_extend hG J hF'1 hGmor hGobj hFmor hFobj
    hst hqs
  refine ⟨_, ⟨e⟩, fun i => ⟨?_⟩⟩
  exact Functor.isoWhiskerLeft (Sigma.incl i ⋙ ULiftHom.up)
    (Stackification.unit hG hF'1 hGmor hqs.isMorSheaf hGobj hqs.hasEffectiveDescent) ≪≫
    Sigma.inclDesc F i

end Criterion

end Functor

end CategoryTheory
