module

public import StacksFrontier.Deformation.FormalObject.Filtration.FilteredObject

/-!
# Comparison functors for a different filtration

The functors from filtered formal objects to the fibre of the usual category of formal objects
over `R`, and back.  They are the two halves of `filteredFormalObjectsEquivalence`.

## References

* [Stacks Project, Tag 06H6](https://stacks.math.columbia.edu/tag/06H6)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory
open IsLocalRing
universe u v w uF vF


variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

@[implicit_reducible]
noncomputable def toAdicObject {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : FilteredFormalObject p R I) :
    FormalObject p := by
  let b := toAdicIndex I
  let q (n : ℕ) := idealToAdic I (toAdicIndex_le I n)
  let η (n : ℕ) := pushforwardObj hp (q n) (X.level (b n)) (X.level_eq (b n))
  let u (n : ℕ) := chosenPushforwardMap hp (q n) (X.level (b n)) (X.level_eq (b n))
  have hu (n : ℕ) : p.IsHomLift (q n) (u n) :=
    chosenPushforwardMap_lift hp (q n) (X.level (b n)) (X.level_eq (b n))
  have hη (n : ℕ) : p.obj (η n) = AdicTruncation.obj R n :=
    pushforwardObj_eq hp (q n) (X.level (b n)) (X.level_eq (b n))
  have hb (n : ℕ) : b n ≤ b (n + 1) := toAdicIndex_mono I (Nat.le_succ n)
  have hψ (n : ℕ) : p.IsHomLift (q (n + 1) ≫ AdicTruncation.transition R n)
      (filteredPath X (b n) (b (n + 1)) (hb n) ≫ u n) :=
    toAdicPsi_lift p R I hp X n
  let t (n : ℕ) : η (n + 1) ⟶ η n :=
    pushforwardDesc hp (q (n + 1)) (AdicTruncation.transition R n)
      (X.level (b (n + 1))) (η n) (X.level_eq (b (n + 1)))
      (filteredPath X (b n) (b (n + 1)) (hb n) ≫ u n) (hψ n)
  have ht (n : ℕ) : p.IsHomLift (AdicTruncation.transition R n) (t n) :=
    pushforwardDesc_lift hp (q (n + 1)) (AdicTruncation.transition R n)
      (X.level (b (n + 1))) (η n) (X.level_eq (b (n + 1)))
      (filteredPath X (b n) (b (n + 1)) (hb n) ≫ u n) (hψ n)
  exact
    { base := R
      level := η
      level_eq := hη
      transition := t
      transition_lift := fun n ↦ by
        simpa only [AdicTruncation.transitionNat] using ht n }

lemma toAdicObject_base {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : FilteredFormalObject p R I) :
    (toAdicObject p R I hp X).base = R := rfl

lemma toAdicObject_transition_fac {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : FilteredFormalObject p R I)
    (n : ℕ) :
    chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I (n + 1)))
        (X.level (toAdicIndex I (n + 1)))
        (X.level_eq (toAdicIndex I (n + 1))) ≫
      (toAdicObject p R I hp X).transition n =
      filteredPath X (toAdicIndex I n) (toAdicIndex I (n + 1))
          (toAdicIndex_mono I (Nat.le_succ n)) ≫
        chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I n))
          (X.level (toAdicIndex I n)) (X.level_eq (toAdicIndex I n)) := by
  exact pushforwardDesc_fac hp _ _ _ _ _ _ (toAdicPsi_lift p R I hp X n)

lemma toAdicApp_psi_lift {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    {X Y : FilteredFormalObject p R I} (f : X ⟶ Y) (n : ℕ) :
    p.IsHomLift (idealToAdic I (toAdicIndex_le I n) ≫
        𝟙 (AdicTruncation.obj R n))
      (f.app (toAdicIndex I n) ≫
        chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I n))
          (Y.level (toAdicIndex I n)) (Y.level_eq (toAdicIndex I n))) := by
  let := f.app_lift (toAdicIndex I n)
  let := chosenPushforwardMap_lift hp (idealToAdic I (toAdicIndex_le I n))
    (Y.level (toAdicIndex I n)) (Y.level_eq (toAdicIndex I n))
  have h : p.IsHomLift
      (𝟙 (I.quotient (toAdicIndex I n)) ≫ idealToAdic I (toAdicIndex_le I n))
      (f.app (toAdicIndex I n) ≫
        chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I n))
          (Y.level (toAdicIndex I n)) (Y.level_eq (toAdicIndex I n))) := inferInstance
  simpa only [Category.id_comp, Category.comp_id] using h

noncomputable def toAdicApp {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    {X Y : FilteredFormalObject p R I} (f : X ⟶ Y) (n : ℕ) :
    (toAdicObject p R I hp X).level n ⟶
      (toAdicObject p R I hp Y).level n :=
  pushforwardDesc hp (idealToAdic I (toAdicIndex_le I n))
    (𝟙 (AdicTruncation.obj R n))
    (X.level (toAdicIndex I n))
    ((toAdicObject p R I hp Y).level n)
    (X.level_eq (toAdicIndex I n))
    (f.app (toAdicIndex I n) ≫
      chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I n))
        (Y.level (toAdicIndex I n)) (Y.level_eq (toAdicIndex I n)))
    (toAdicApp_psi_lift p R I hp f n)

lemma toAdicApp_lift {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    {X Y : FilteredFormalObject p R I} (f : X ⟶ Y) (n : ℕ) :
    p.IsHomLift (𝟙 (AdicTruncation.obj R n)) (toAdicApp p R I hp f n) := by
  unfold toAdicApp
  exact pushforwardDesc_lift hp _ _ _ _ _ _ _

lemma toAdicApp_fac {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    {X Y : FilteredFormalObject p R I} (f : X ⟶ Y) (n : ℕ) :
    chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I n))
        (X.level (toAdicIndex I n)) (X.level_eq (toAdicIndex I n)) ≫
      toAdicApp p R I hp f n =
      f.app (toAdicIndex I n) ≫
        chosenPushforwardMap hp (idealToAdic I (toAdicIndex_le I n))
          (Y.level (toAdicIndex I n)) (Y.level_eq (toAdicIndex I n)) := by
  unfold toAdicApp
  exact pushforwardDesc_fac hp _ _ _ _ _ _ _

/-- Two arrows out of a chosen pushforward over the same morphism agree if they agree after
precomposition with the pushforward map. -/
private theorem pushforward_hom_ext {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k} (hp : IsCofiberedInGroupoids p)
    {A B C : ArtinianLocalAlgCat.{u, v, w} Λ k} (q : A ⟶ B) (g : B ⟶ C) {x y : F}
    (hx : p.obj x = A) {ψ ψ' : pushforwardObj hp q x hx ⟶ y}
    (hψ : p.IsHomLift g ψ) (hψ' : p.IsHomLift g ψ')
    (h : chosenPushforwardMap hp q x hx ≫ ψ = chosenPushforwardMap hp q x hx ≫ ψ') : ψ = ψ' := by
  let := chosenPushforwardMap_lift hp q x hx
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hp q _
    (chosenPushforwardMap_lift hp q x hx)
  exact Functor.IsStronglyCocartesian.ext p q (chosenPushforwardMap hp q x hx) g h

/-- A square of transition maps and level maps commutes as soon as it does after precomposition
with the pushforward map `u`, given the commutation of the transition and level maps with the
chosen pushforward maps. -/
private theorem pushforward_square_comm {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k} (hp : IsCofiberedInGroupoids p)
    {A B C : ArtinianLocalAlgCat.{u, v, w} Λ k} (q : A ⟶ B) (T : B ⟶ C) {x : F}
    (hx : p.obj x = A) {x' y y' X₀ Y₀ Y₁ : F} {tX : pushforwardObj hp q x hx ⟶ X₀}
    {tY : Y₁ ⟶ Y₀} {a₀ : X₀ ⟶ Y₀} {a₁ : pushforwardObj hp q x hx ⟶ Y₁}
    (htX : p.IsHomLift T tX) (htY : p.IsHomLift T tY) (ha₀ : p.IsHomLift (𝟙 C) a₀)
    (ha₁ : p.IsHomLift (𝟙 B) a₁) {pX : x ⟶ x'} {pY : y ⟶ y'} {fx : x ⟶ y} {fx' : x' ⟶ y'}
    {uX : x' ⟶ X₀} {uY : y ⟶ Y₁} {uY' : y' ⟶ Y₀}
    (hXt : chosenPushforwardMap hp q x hx ≫ tX = pX ≫ uX) (hYt : uY ≫ tY = pY ≫ uY')
    (h₀ : uX ≫ a₀ = fx' ≫ uY') (h₁ : chosenPushforwardMap hp q x hx ≫ a₁ = fx ≫ uY)
    (hnat : pX ≫ fx' = fx ≫ pY) : tX ≫ a₀ = a₁ ≫ tY := by
  let := htX
  let := htY
  let := ha₀
  let := ha₁
  refine pushforward_hom_ext hp q T hx inferInstance inferInstance ?_
  rw [← Category.assoc, hXt, Category.assoc, h₀, ← Category.assoc, hnat, Category.assoc, ← hYt,
    ← Category.assoc, ← h₁, Category.assoc]

lemma toAdicApp_naturality {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    {X Y : FilteredFormalObject p R I} (f : X ⟶ Y) (n : ℕ) :
    (toAdicObject p R I hp X).transition n ≫ toAdicApp p R I hp f n =
      toAdicApp p R I hp f (n + 1) ≫
        (toAdicObject p R I hp Y).transition n := by
  have ht (Z : FilteredFormalObject p R I) : p.IsHomLift (AdicTruncation.transition R n)
      ((toAdicObject p R I hp Z).transition n) := by
    simpa only [AdicTruncation.transitionNat, toAdicObject_base] using
      (toAdicObject p R I hp Z).transition_lift n
  exact pushforward_square_comm hp (idealToAdic I (toAdicIndex_le I (n + 1)))
    (AdicTruncation.transition R n) (X.level_eq (toAdicIndex I (n + 1))) (ht X) (ht Y)
    (toAdicApp_lift p R I hp f n) (toAdicApp_lift p R I hp f (n + 1))
    (toAdicObject_transition_fac p R I hp X n) (toAdicObject_transition_fac p R I hp Y n)
    (toAdicApp_fac p R I hp f n) (toAdicApp_fac p R I hp f (n + 1))
    (filteredPath_naturality f _ _ _)

lemma toAdicApp_id {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : FilteredFormalObject p R I)
    (n : ℕ) :
    toAdicApp p R I hp (𝟙 X) n = 𝟙 ((toAdicObject p R I hp X).level n) := by
  refine pushforward_hom_ext hp (idealToAdic I (toAdicIndex_le I n)) (𝟙 (AdicTruncation.obj R n))
    (X.level_eq (toAdicIndex I n)) (toAdicApp_lift p R I hp (𝟙 X) n)
    (IsHomLift.id ((toAdicObject p R I hp X).level_eq n)) ?_
  rw [toAdicApp_fac]
  change (𝟙 _ ≫ _) = _ ≫ 𝟙 _
  simp

lemma toAdicApp_comp {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    {X Y Z : FilteredFormalObject p R I} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) :
    toAdicApp p R I hp (f ≫ g) n =
      toAdicApp p R I hp f n ≫ toAdicApp p R I hp g n := by
  have := toAdicApp_lift p R I hp f n
  have := toAdicApp_lift p R I hp g n
  refine pushforward_hom_ext hp (idealToAdic I (toAdicIndex_le I n)) (𝟙 (AdicTruncation.obj R n))
    (X.level_eq (toAdicIndex I n)) (toAdicApp_lift p R I hp (f ≫ g) n) inferInstance ?_
  rw [toAdicApp_fac, ← Category.assoc, toAdicApp_fac, Category.assoc, toAdicApp_fac,
    ← Category.assoc]
  rfl

noncomputable def toAdicFunctor {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) :
    FilteredFormalObject p R I ⥤
      (FormalObject.projection (p := p)).Fiber R where
  obj X := ⟨toAdicObject p R I hp X, toAdicObject_base p R I hp X⟩
  map {X Y} f := by
    let φ : toAdicObject p R I hp X ⟶ toAdicObject p R I hp Y :=
      { base := 𝟙 R
        app := toAdicApp p R I hp f
        app_lift := fun n ↦ by
          have hmap : (AdicTruncation.functor (Λ := Λ) (k := k) n).map (𝟙 R) =
              𝟙 (AdicTruncation.obj R n) :=
            (AdicTruncation.functor n).map_id R
          rw [hmap]
          exact toAdicApp_lift p R I hp f n
        naturality := toAdicApp_naturality p R I hp f }
    refine ⟨φ, ?_⟩
    apply IsHomLift.of_fac (FormalObject.projection (p := p))
      (𝟙 R) φ (toAdicObject_base p R I hp X) (toAdicObject_base p R I hp Y)
    cases toAdicObject_base p R I hp X
    cases toAdicObject_base p R I hp Y
    simp [φ, FormalObject.projection]
  map_id X := by
    apply Functor.Fiber.hom_ext
    exact FormalObject.Hom.ext rfl (toAdicApp_id p R I hp X)
  map_comp {X Y Z} f g := by
    apply Functor.Fiber.hom_ext
    exact FormalObject.Hom.ext rfl (toAdicApp_comp p R I hp f g)

@[implicit_reducible]
noncomputable def toIdealObject {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : FormalObject p)
    (hX : X.base = R) : FilteredFormalObject p R I := by
  let a := toIdealIndex I
  let q (n : ℕ) := adicToIdeal I (toIdealIndex_le I n)
  have hlevel (n : ℕ) : p.obj (X.level n) = AdicTruncation.obj R n := by
    simpa only [hX, AdicTruncation.functor] using X.level_eq n
  let η (n : ℕ) := pushforwardObj hp (q n) (X.level (a n)) (hlevel (a n))
  let u (n : ℕ) := chosenPushforwardMap hp (q n) (X.level (a n)) (hlevel (a n))
  have hη (n : ℕ) : p.obj (η n) = I.quotient n :=
    pushforwardObj_eq hp (q n) (X.level (a n)) (hlevel (a n))
  have ha (n : ℕ) : a n ≤ a (n + 1) := toIdealIndex_mono I (Nat.le_succ n)
  have hψ (n : ℕ) : p.IsHomLift (q (n + 1) ≫ I.transition n)
      (formalPath X (a n) (a (n + 1)) (ha n) ≫ u n) :=
    toIdealPsi_lift p R I hp X hX n
  let t (n : ℕ) : η (n + 1) ⟶ η n :=
    pushforwardDesc hp (q (n + 1)) (I.transition n)
      (X.level (a (n + 1))) (η n) (hlevel (a (n + 1)))
      (formalPath X (a n) (a (n + 1)) (ha n) ≫ u n) (hψ n)
  have ht (n : ℕ) : p.IsHomLift (I.transition n) (t n) :=
    pushforwardDesc_lift hp (q (n + 1)) (I.transition n)
      (X.level (a (n + 1))) (η n) (hlevel (a (n + 1)))
      (formalPath X (a n) (a (n + 1)) (ha n) ≫ u n) (hψ n)
  exact
    { level := η
      level_eq := hη
      transition := t
      transition_lift := ht }

lemma toIdealObject_transition_fac {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (X : FormalObject p) (hX : X.base = R)
    (hp : IsCofiberedInGroupoids p) (n : ℕ) :
    chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I (n + 1)))
        (X.level (toIdealIndex I (n + 1)))
        (by simpa only [hX, AdicTruncation.functor] using
          X.level_eq (toIdealIndex I (n + 1))) ≫
      (toIdealObject p R I hp X hX).transition n =
      formalPath X (toIdealIndex I n) (toIdealIndex I (n + 1))
          (toIdealIndex_mono I (Nat.le_succ n)) ≫
        chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I n))
          (X.level (toIdealIndex I n))
          (by simpa only [hX, AdicTruncation.functor] using
            X.level_eq (toIdealIndex I n)) := by
  exact pushforwardDesc_fac hp _ _ _ _ _ _ (toIdealPsi_lift p R I hp X hX n)

lemma fiber_level_eq {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (X : (FormalObject.projection (p := p)).Fiber R) (n : ℕ) :
    p.obj (X.val.level n) = AdicTruncation.obj R n := by
  rcases X with ⟨X, hX⟩
  change X.base = R at hX
  subst R
  exact X.level_eq n

lemma fiber_app_lift {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    {X Y : (FormalObject.projection (p := p)).Fiber R}
    (f : X ⟶ Y) (n : ℕ) :
    p.IsHomLift (𝟙 (AdicTruncation.obj R n)) (f.val.app n) := by
  rcases X with ⟨⟨RX, lx, ex, tx, etx⟩, hX⟩
  rcases Y with ⟨⟨RY, ly, ey, ty, ety⟩, hY⟩
  change RX = R at hX
  change RY = R at hY
  cases hX
  cases hY
  have hb : f.val.base = 𝟙 R := by
    let : (FormalObject.projection (p := p)).IsHomLift (𝟙 R) f.val :=
      f.property
    have heq := IsHomLift.fac (FormalObject.projection (p := p))
      (𝟙 R) f.val
    simpa [FormalObject.projection] using heq.symm
  have hid : AdicTruncation.map (Λ := Λ) (k := k) (𝟙 R) n =
      𝟙 (AdicTruncation.obj R n) :=
    (AdicTruncation.functor n).map_id R
  simpa only [AdicTruncation.functor, hb, hid] using f.val.app_lift n

lemma fiber_transition_lift {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (X : (FormalObject.projection (p := p)).Fiber R) (n : ℕ) :
    p.IsHomLift (AdicTruncation.transition R n) (X.val.transition n) := by
  rcases X with ⟨X, hX⟩
  change X.base = R at hX
  subst R
  simpa only [AdicTruncation.transitionNat] using X.transition_lift n

lemma toIdealApp_psi_lift {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    {X Y : (FormalObject.projection (p := p)).Fiber R}
    (f : X ⟶ Y) (n : ℕ) :
    p.IsHomLift (adicToIdeal I (toIdealIndex_le I n) ≫ 𝟙 (I.quotient n))
      (f.val.app (toIdealIndex I n) ≫
        chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I n))
          (Y.val.level (toIdealIndex I n)) (fiber_level_eq p R Y (toIdealIndex I n))) := by
  let := fiber_app_lift p R f (toIdealIndex I n)
  let := chosenPushforwardMap_lift hp (adicToIdeal I (toIdealIndex_le I n))
    (Y.val.level (toIdealIndex I n)) (fiber_level_eq p R Y (toIdealIndex I n))
  have h : p.IsHomLift
      (𝟙 (AdicTruncation.obj R (toIdealIndex I n)) ≫
        adicToIdeal I (toIdealIndex_le I n))
      (f.val.app (toIdealIndex I n) ≫
        chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I n))
          (Y.val.level (toIdealIndex I n))
          (fiber_level_eq p R Y (toIdealIndex I n))) := inferInstance
  simpa only [Category.id_comp, Category.comp_id] using h

noncomputable def toIdealApp {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    {X Y : (FormalObject.projection (p := p)).Fiber R}
    (f : X ⟶ Y) (n : ℕ) :
    (toIdealObject p R I hp X.val X.property).level n ⟶
      (toIdealObject p R I hp Y.val Y.property).level n :=
  pushforwardDesc hp (adicToIdeal I (toIdealIndex_le I n)) (𝟙 (I.quotient n))
    (X.val.level (toIdealIndex I n))
    ((toIdealObject p R I hp Y.val Y.property).level n)
    (fiber_level_eq p R X (toIdealIndex I n))
    (f.val.app (toIdealIndex I n) ≫
      chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I n))
        (Y.val.level (toIdealIndex I n)) (fiber_level_eq p R Y (toIdealIndex I n)))
    (toIdealApp_psi_lift p R I hp f n)

lemma toIdealApp_lift {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    {X Y : (FormalObject.projection (p := p)).Fiber R}
    (f : X ⟶ Y) (n : ℕ) :
    p.IsHomLift (𝟙 (I.quotient n)) (toIdealApp p R I hp f n) := by
  unfold toIdealApp
  exact pushforwardDesc_lift hp _ _ _ _ _ _ _

lemma toIdealApp_fac {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    {X Y : (FormalObject.projection (p := p)).Fiber R}
    (f : X ⟶ Y) (n : ℕ) :
    chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I n))
        (X.val.level (toIdealIndex I n)) (fiber_level_eq p R X (toIdealIndex I n)) ≫
      toIdealApp p R I hp f n =
      f.val.app (toIdealIndex I n) ≫
        chosenPushforwardMap hp (adicToIdeal I (toIdealIndex_le I n))
          (Y.val.level (toIdealIndex I n)) (fiber_level_eq p R Y (toIdealIndex I n)) := by
  unfold toIdealApp
  exact pushforwardDesc_fac hp _ _ _ _ _ _ _

lemma toIdealApp_naturality {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    {X Y : (FormalObject.projection (p := p)).Fiber R} (f : X ⟶ Y) (n : ℕ) :
    (toIdealObject p R I hp X.val X.property).transition n ≫ toIdealApp p R I hp f n =
      toIdealApp p R I hp f (n + 1) ≫
        (toIdealObject p R I hp Y.val Y.property).transition n :=
  pushforward_square_comm hp (adicToIdeal I (toIdealIndex_le I (n + 1))) (I.transition n)
    (fiber_level_eq p R X (toIdealIndex I (n + 1)))
    ((toIdealObject p R I hp X.val X.property).transition_lift n)
    ((toIdealObject p R I hp Y.val Y.property).transition_lift n)
    (toIdealApp_lift p R I hp f n) (toIdealApp_lift p R I hp f (n + 1))
    (toIdealObject_transition_fac p R I X.val X.property hp n)
    (toIdealObject_transition_fac p R I Y.val Y.property hp n)
    (toIdealApp_fac p R I hp f n) (toIdealApp_fac p R I hp f (n + 1))
    (formalPath_naturality f.val _ _ _)

lemma toIdealApp_id {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) (X : (FormalObject.projection (p := p)).Fiber R)
    (n : ℕ) :
    toIdealApp p R I hp (𝟙 X) n = 𝟙 ((toIdealObject p R I hp X.val X.property).level n) := by
  refine pushforward_hom_ext hp (adicToIdeal I (toIdealIndex_le I n)) (𝟙 (I.quotient n))
    (fiber_level_eq p R X (toIdealIndex I n)) (toIdealApp_lift p R I hp (𝟙 X) n)
    (IsHomLift.id ((toIdealObject p R I hp X.val X.property).level_eq n)) ?_
  rw [toIdealApp_fac]
  change (𝟙 _ ≫ _) = _ ≫ 𝟙 _
  simp

lemma toIdealApp_comp {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p)
    {X Y Z : (FormalObject.projection (p := p)).Fiber R} (f : X ⟶ Y) (g : Y ⟶ Z)
    (n : ℕ) :
    toIdealApp p R I hp (f ≫ g) n =
      toIdealApp p R I hp f n ≫ toIdealApp p R I hp g n := by
  have := toIdealApp_lift p R I hp f n
  have := toIdealApp_lift p R I hp g n
  refine pushforward_hom_ext hp (adicToIdeal I (toIdealIndex_le I n)) (𝟙 (I.quotient n))
    (fiber_level_eq p R X (toIdealIndex I n)) (toIdealApp_lift p R I hp (f ≫ g) n)
    inferInstance ?_
  rw [toIdealApp_fac, ← Category.assoc, toIdealApp_fac, Category.assoc, toIdealApp_fac,
    ← Category.assoc]
  rfl

noncomputable def toIdealFunctor {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (I : IdealFiltration R)
    (hp : IsCofiberedInGroupoids p) :
    (FormalObject.projection (p := p)).Fiber R ⥤
      FilteredFormalObject p R I where
  obj X := toIdealObject p R I hp X.val X.property
  map f :=
    { app := toIdealApp p R I hp f
      app_lift := toIdealApp_lift p R I hp f
      naturality := toIdealApp_naturality p R I hp f }
  map_id X := FilteredFormalObject.Hom.ext (fun n ↦ toIdealApp_id p R I hp X n)
  map_comp f g := FilteredFormalObject.Hom.ext (fun n ↦ toIdealApp_comp p R I hp f g n)

end

end Deformation
