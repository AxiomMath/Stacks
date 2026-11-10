module

public import Mathlib.CategoryTheory.Limits.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.Connected
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Sum
public import StacksCore.Tactic.StacksAttribute

/-!
# Connected finite limits (Stacks 04AT)

A category `C` has limits of every finite *connected* shape if and only if it has
equalizers and pullbacks. Connectedness is what removes the terminal object from
the picture: equalizers and pullbacks alone never produce one, so the unrestricted
finite-limit statement (Stacks 002O) is genuinely stronger.

The finite connected shapes are rendered as
`∀ (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J], HasLimitsOfShape J C`,
matching the universe convention of `HasFiniteLimits.out`. Mathlib's `IsConnected`
already includes nonemptiness, which is the reading Stacks intends.

The easy direction specialises at `WalkingParallelPair` and `WalkingCospan`, both
finite and connected. The hard direction goes in two steps:

* **Finite wide pullbacks from binary pullbacks.** Induct over the finite index
  type with `Finite.induction_empty_option`, gluing one leg at a time with a single
  binary pullback (`hasFiniteWidePullbacks_of_hasPullbacks`). Mathlib has
  `hasFiniteWidePullbacks_of_hasFiniteLimits` and `hasPullbacks_of_hasWidePullbacks`
  but not this direction.

* **Assembling an arbitrary finite connected limit.** For each object `b` of the
  shape, take the joint equalizer `EndoEqualizer` of the finite family
  `{G.map e : e ∈ End b}` against the identity; then build a partial limit
  candidate over a `Finset` of objects and grow it one object at a time along a
  spanning tree of the connected shape. Each growth step glues in a new object over
  a *single* base object, which is exactly where connectedness is used — a product
  is never needed. The gluing step itself is one binary pullback followed by a
  joint equalizer of the remaining incidences.
-/

@[expose] public section

namespace CategoryTheory.Limits

universe v u

/-! ### Finite wide pullbacks from binary pullbacks -/

/-- The map from a wide-pullback cone over `Option α` into the wide pullback over `α`, obtained
by forgetting the leg at `none`. -/
private noncomputable def WidePullbackCone.liftSome {C : Type u} [Category.{v} C] {α : Type}
    {B : C} {objs : Option α → C} {arrows : ∀ j, objs j ⟶ B}
    [HasWidePullback B (fun a => objs (some a)) (fun a => arrows (some a))]
    (t : WidePullbackCone arrows) :
    t.pt ⟶ widePullback B (fun a => objs (some a)) (fun a => arrows (some a)) :=
  WidePullback.lift t.base (fun a => t.π (some a)) fun a => WidePullbackCone.condition t (some a)

/-- `liftSome` is compatible with the legs of the wide pullback over `α`. -/
private lemma WidePullbackCone.liftSome_π {C : Type u} [Category.{v} C] {α : Type}
    {B : C} {objs : Option α → C} {arrows : ∀ j, objs j ⟶ B}
    [HasWidePullback B (fun a => objs (some a)) (fun a => arrows (some a))]
    (t : WidePullbackCone arrows) (a : α) :
    t.liftSome ≫ WidePullback.π (fun a => arrows (some a)) a = t.π (some a) :=
  WidePullback.lift_π _ _ _ _ a

/-- `liftSome` is compatible with the base of the wide pullback over `α`. -/
private lemma WidePullbackCone.liftSome_base {C : Type u} [Category.{v} C] {α : Type}
    {B : C} {objs : Option α → C} {arrows : ∀ j, objs j ⟶ B}
    [HasWidePullback B (fun a => objs (some a)) (fun a => arrows (some a))]
    (t : WidePullbackCone arrows) :
    t.liftSome ≫ WidePullback.base (fun a => arrows (some a)) = t.base :=
  WidePullback.lift_base _ _ _ _

/-- The wide pullback over `Option α` exists, built from the wide pullback over `α`
(the inductive hypothesis) and a single binary pullback gluing on the extra leg. -/
private lemma hasWidePullback_option {C : Type u} [Category.{v} C] [HasPullbacks C]
    {α : Type} [HasLimitsOfShape (WidePullbackShape α) C]
    (B : C) (objs : Option α → C) (arrows : ∀ j, objs j ⟶ B) :
    HasWidePullback B objs arrows := by
  have : HasWidePullback B (fun a => objs (some a)) (fun a => arrows (some a)) := inferInstance
  set g := WidePullback.base (fun a => arrows (some a))
  have hcond : ∀ t : WidePullbackCone arrows, t.liftSome ≫ g = t.π none ≫ arrows none :=
    fun t => (WidePullbackCone.liftSome_base t).trans (WidePullbackCone.condition t none).symm
  set P := pullback g (arrows none)
  let proj : ∀ j, P ⟶ objs j := fun j =>
    Option.rec (pullback.snd g (arrows none))
      (fun a => pullback.fst g (arrows none) ≫ WidePullback.π (fun a => arrows (some a)) a) j
  have hfb : pullback.fst g (arrows none) ≫ g = pullback.snd g (arrows none) ≫ arrows none :=
    pullback.condition
  let bse : P ⟶ B := pullback.snd g (arrows none) ≫ arrows none
  have hfac : ∀ j, proj j ≫ arrows j = bse := by
    rintro (_ | a)
    · rfl
    · change (pullback.fst g (arrows none) ≫ WidePullback.π (fun a => arrows (some a)) a) ≫
        arrows (some a) = _
      rw [Category.assoc, WidePullback.π_arrow]
      exact hfb
  refine ⟨⟨WidePullbackCone.mk bse proj hfac, ?_⟩⟩
  refine WidePullbackCone.IsLimit.mk _
    (fun t => pullback.lift t.liftSome (t.π none) (hcond t)) ?_ ?_ ?_
  · intro t
    change pullback.lift t.liftSome (t.π none) (hcond t) ≫
      (pullback.snd g (arrows none) ≫ arrows none) = t.base
    rw [← Category.assoc, pullback.lift_snd, WidePullbackCone.condition t none]
  · rintro t (_ | a)
    · change pullback.lift t.liftSome (t.π none) (hcond t) ≫ pullback.snd g (arrows none)
        = t.π none
      rw [pullback.lift_snd]
    · change pullback.lift t.liftSome (t.π none) (hcond t) ≫
          (pullback.fst g (arrows none) ≫ WidePullback.π (fun a => arrows (some a)) a) =
            t.π (some a)
      rw [← Category.assoc, pullback.lift_fst]
      exact WidePullbackCone.liftSome_π t a
  · intro t m hbase hproj
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      apply WidePullback.hom_ext
      · intro a
        exact (Category.assoc _ _ _).trans
          ((hproj (some a)).trans (WidePullbackCone.liftSome_π t a).symm)
      · exact (Category.assoc _ _ _).trans
          (((congrArg (fun x => m ≫ x) hfb).trans hbase).trans
            (WidePullbackCone.liftSome_base t).symm)
    · rw [pullback.lift_snd]
      exact hproj none

/-- The inductive step: limits over `WidePullbackShape (Option α)` exist once they
exist over `WidePullbackShape α`. -/
private lemma hasLimitsOfShape_widePullback_option {C : Type u} [Category.{v} C] [HasPullbacks C]
    (α : Type) [HasLimitsOfShape (WidePullbackShape α) C] :
    HasLimitsOfShape (WidePullbackShape (Option α)) C := by
  refine ⟨fun F => ?_⟩
  have := hasWidePullback_option (F.obj none) (fun j => F.obj (some j))
    (fun j => F.map (WidePullbackShape.Hom.term j))
  exact hasLimit_of_iso (WidePullbackShape.diagramIsoWideCospan F).symm

/-- Base case: limits over the empty wide pullback shape always exist (the shape has
a single object, which serves as the limit). -/
private lemma hasLimitsOfShape_widePullback_empty {C : Type u} [Category.{v} C] :
    HasLimitsOfShape (WidePullbackShape PEmpty) C := by
  have huniq : ∀ (X : WidePullbackShape PEmpty), X = none := by
    rintro (_ | ⟨⟨⟩⟩)
    rfl
  refine ⟨fun F => ?_⟩
  refine HasLimit.mk { cone := ?_, isLimit := ?_ }
  · refine Cone.mk (F.obj none) ?_
    refine { app := fun X => eqToHom (by rw [huniq X]; exact Functor.const_obj_obj _ _ _),
             naturality := ?_ }
    intro X Y f
    obtain rfl := huniq X
    obtain rfl := huniq Y
    rw [Subsingleton.elim f (𝟙 _)]
    simp
  · refine { lift := fun s => s.π.app none, fac := ?_, uniq := ?_ }
    · intro s X
      obtain rfl := huniq X
      simp
    · intro s m hm
      simpa using hm none

/-- Binary pullbacks suffice for *finite wide* pullbacks: glue the legs on one at a
time, by `Finite.induction_empty_option` over the index type.

Mathlib has `hasFiniteWidePullbacks_of_hasFiniteLimits` and
`hasPullbacks_of_hasWidePullbacks`, but not this direction. -/
theorem hasFiniteWidePullbacks_of_hasPullbacks
    (C : Type u) [Category.{v} C] [HasPullbacks C] :
    HasFiniteWidePullbacks C := by
  refine ⟨fun J _ => ?_⟩
  refine Finite.induction_empty_option
    (P := fun J => HasLimitsOfShape (WidePullbackShape J) C) ?_ ?_ ?_ J
  · intro α β e _
    exact hasLimitsOfShape_of_equivalence (WidePullbackShape.equivalenceOfEquiv _ e)
  · exact hasLimitsOfShape_widePullback_empty
  · intro α _ _
    exact hasLimitsOfShape_widePullback_option α

/-! ### Joint equalizers of endomorphism families -/

/-- The joint equalizer of a finite family of parallel pairs `f i, g i : A ⟶ Z i`,
restricted to a `Finset` of indices. -/
structure JointEqualizer {C : Type u} [Category.{v} C] (A : C) {ι : Type} (Z : ι → C)
    (f g : ∀ i, A ⟶ Z i) (S : Finset ι) where
  /-- The equalizing object. -/
  pt : C
  /-- The mono leg into `A`. -/
  e : pt ⟶ A
  /-- The leg equalizes `f i` against `g i` for every index in `S`. -/
  cond : ∀ i ∈ S, e ≫ f i = e ≫ g i
  /-- Every map into `A` equalizing the family factors through `pt`. -/
  lift : ∀ (W : C) (k : W ⟶ A), (∀ i ∈ S, k ≫ f i = k ≫ g i) → (W ⟶ pt)
  /-- The factorisation produced by `lift` is one. -/
  fac : ∀ (W : C) (k : W ⟶ A) (h : ∀ i ∈ S, k ≫ f i = k ≫ g i), lift W k h ≫ e = k
  /-- The leg is mono. -/
  emono : Mono e

/-- A finite family of parallel pairs has a joint equalizer, by iterating binary
equalizers over the `Finset` of indices. -/
private lemma nonempty_jointEqualizer {C : Type u} [Category.{v} C] [HasEqualizers C] (A : C)
    {ι : Type} (Z : ι → C) (f g : ∀ i, A ⟶ Z i) (S : Finset ι) :
    Nonempty (JointEqualizer A Z f g S) := by
  classical
  induction S using Finset.induction with
  | empty =>
    exact ⟨{ pt := A, e := 𝟙 A, cond := by simp, lift := fun W k _ => k
             fac := by simp, emono := inferInstance }⟩
  | @insert a S' ha ih =>
    obtain ⟨P, e, cond, lift, fac, emono⟩ := ih
    let E : C := equalizer (e ≫ f a) (e ≫ g a)
    let q : E ⟶ P := equalizer.ι (e ≫ f a) (e ≫ g a)
    refine ⟨{ pt := E, e := q ≫ e, cond := ?_, lift := ?_, fac := ?_, emono := ?_ }⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi'
      · rw [Category.assoc, Category.assoc, equalizer.condition]
      · rw [Category.assoc, Category.assoc, cond i hi']
    · intro W k h
      have hk_S' : ∀ i ∈ S', k ≫ f i = k ≫ g i := fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine equalizer.lift (lift W k hk_S') ?_
      rw [← Category.assoc, ← Category.assoc, fac W k hk_S', h a (Finset.mem_insert_self a S')]
    · intro W k h
      rw [← Category.assoc, equalizer.lift_ι]
      exact fac W k fun i hi => h i (Finset.mem_insert_of_mem hi)
    · have : Mono q := equalizer.ι_mono
      exact mono_comp q e

/-- An *endo-equalizer datum* for an object `b` of a diagram `D : G ⥤ C`: an object
`obj` with a leg `ι : obj ⟶ D.obj b` equalizing every endomorphism of `b` against the
identity, universal among such maps (so `ι` is mono via `uniq`). This packages the
joint equalizer of `{D.map e : e ∈ End b}` against `𝟙 (D.obj b)`. -/
structure EndoEqualizer {C : Type u} [Category.{v} C] (G : Type) [SmallCategory G]
    (D : G ⥤ C) (b : G) where
  /-- The equalizing object. -/
  obj : C
  /-- The mono leg into `D.obj b`. -/
  ι : obj ⟶ D.obj b
  /-- The leg is unchanged by every endomorphism of `b`. -/
  equalizes : ∀ e : b ⟶ b, ι ≫ D.map e = ι
  /-- Every map into `D.obj b` unchanged by the endomorphisms factors through `obj`. -/
  lift : ∀ (W : C) (k : W ⟶ D.obj b), (∀ e : b ⟶ b, k ≫ D.map e = k) → (W ⟶ obj)
  /-- The factorisation produced by `lift` is one. -/
  fac : ∀ (W : C) (k : W ⟶ D.obj b) (h : ∀ e : b ⟶ b, k ≫ D.map e = k), lift W k h ≫ ι = k
  /-- The leg `ι` is mono, stated as cancellability. -/
  uniq : ∀ (W : C) (l l' : W ⟶ obj), l ≫ ι = l' ≫ ι → l = l'

/-- For a finite shape and any object `b`, the joint equalizer of the finite
endomorphism family `{D.map e : e ∈ End b}` against the identity exists: it is the joint
equalizer of `nonempty_jointEqualizer` for the family `D.map e` against the constant family
`𝟙 (D.obj b)`. Uses neither connectedness nor wide pullbacks. -/
private lemma nonempty_endoEqualizer {C : Type u} [Category.{v} C] [HasEqualizers C]
    (G : Type) [SmallCategory G] [FinCategory G]
    (D : G ⥤ C) (b : G) : Nonempty (EndoEqualizer G D b) := by
  classical
  obtain ⟨pt, e, cond, lift, fac, emono⟩ := nonempty_jointEqualizer (D.obj b)
    (fun _ : b ⟶ b => D.obj b) D.map (fun _ => 𝟙 (D.obj b)) Finset.univ
  have hlift : ∀ (W : C) (k : W ⟶ D.obj b), (∀ g : b ⟶ b, k ≫ D.map g = k) →
      ∀ g ∈ Finset.univ, k ≫ D.map g = k ≫ 𝟙 (D.obj b) :=
    fun _ k h g _ => by simpa using h g
  exact ⟨{ obj := pt
           ι := e
           equalizes := fun g => by simpa using cond g (Finset.mem_univ g)
           lift := fun W k h => lift W k (hlift W k h)
           fac := fun W k h => fac W k (hlift W k h)
           uniq := fun _ _ _ hll' => (cancel_mono e).1 hll' }⟩

/-! ### Gluing along a nonempty finite family of cospans -/

/-- The result of gluing two objects `P, F` along a finite *nonempty* family of
cospans `P → Z l ← F`: one binary pullback over the base picked out by any single
index, refined by the joint equalizer of the remaining constraints. -/
structure CospanGlue {C : Type u} [Category.{v} C] (P F : C) {L : Type} (Z : L → C)
    (pP : ∀ l, P ⟶ Z l) (pF : ∀ l, F ⟶ Z l) where
  /-- The glued object. -/
  pt : C
  /-- The projection to `P`. -/
  w : pt ⟶ P
  /-- The projection to `F`. -/
  v : pt ⟶ F
  /-- Every cospan in the family commutes on `pt`. -/
  cond : ∀ l, w ≫ pP l = v ≫ pF l
  /-- A compatible pair of maps out of `W` factors through `pt`. -/
  lift : ∀ (W : C) (wW : W ⟶ P) (vW : W ⟶ F),
          (∀ l, wW ≫ pP l = vW ≫ pF l) → (W ⟶ pt)
  /-- The factorisation respects the projection to `P`. -/
  fac_w : ∀ W wW vW h, lift W wW vW h ≫ w = wW
  /-- The factorisation respects the projection to `F`. -/
  fac_v : ∀ W wW vW h, lift W wW vW h ≫ v = vW
  /-- The two projections are jointly monic. -/
  uniq : ∀ (W : C) (m m' : W ⟶ pt), m ≫ w = m' ≫ w → m ≫ v = m' ≫ v → m = m'

/-- Gluing data exists whenever `C` has pullbacks and equalizers and the index family
is finite and nonempty. Nonemptiness is what lets a *pullback* rather than a product
carry the construction — this is where the connectedness of the shape is spent. -/
private lemma nonempty_cospanGlue {C : Type u} [Category.{v} C] [HasPullbacks C] [HasEqualizers C]
    {L : Type} [Finite L] (P F : C) (Z : L → C) (pP : ∀ l, P ⟶ Z l) (pF : ∀ l, F ⟶ Z l)
    (hne : Nonempty L) : Nonempty (CospanGlue P F Z pP pF) := by
  classical
  have : Fintype L := Fintype.ofFinite L
  obtain ⟨a₀⟩ := hne
  let Q : C := pullback (pP a₀) (pF a₀)
  let wQ : Q ⟶ P := pullback.fst (pP a₀) (pF a₀)
  let vQ : Q ⟶ F := pullback.snd (pP a₀) (pF a₀)
  obtain ⟨E, e, cond, lift, fac, emono⟩ :=
    nonempty_jointEqualizer Q Z (fun l => wQ ≫ pP l) (fun l => vQ ≫ pF l) Finset.univ
  refine
    ⟨{ pt := E
       w := e ≫ wQ
       v := e ≫ vQ
       cond := ?_
       lift := ?_
       fac_w := ?_
       fac_v := ?_
       uniq := ?_ }⟩
  · intro l
    simpa only [Category.assoc] using cond l (Finset.mem_univ l)
  · intro W wW vW h
    refine lift W (pullback.lift wW vW (h a₀)) ?_
    intro l _
    rw [← Category.assoc, ← Category.assoc, pullback.lift_fst, pullback.lift_snd]
    exact h l
  · intro W wW vW h
    rw [← Category.assoc, fac, pullback.lift_fst]
  · intro W wW vW h
    rw [← Category.assoc, fac, pullback.lift_snd]
  · intro W m m' hw hv
    rw [← cancel_mono e]
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hw
    · simpa only [Category.assoc] using hv

/-! ### Growing a partial limit along a spanning tree -/

section Assemble
variable {C : Type u} [Category.{v} C]
variable (B : Type) [SmallCategory B] [FinCategory B]
    (G : B ⥤ C) (endo : ∀ b : B, EndoEqualizer B G b)

/-- A limit candidate for the restriction of `G` to the objects in `S`: an object with
a leg into each `endo b` for `b ∈ S`, compatible with every arrow of `B` between
objects of `S`, universal among such data. -/
structure PartialConnectedLimit (S : Finset B) where
  /-- The candidate apex. -/
  pt : C
  /-- The leg at each object of `S`, landing in the endo-equalizer. -/
  ρ : ∀ b, b ∈ S → (pt ⟶ (endo b).obj)
  /-- The legs are compatible with every arrow between objects of `S`. -/
  cross : ∀ {s t : B} (g : s ⟶ t) (hs : s ∈ S) (ht : t ∈ S),
            ρ s hs ≫ (endo s).ι ≫ G.map g = ρ t ht ≫ (endo t).ι
  /-- Compatible legs out of `W` factor through the apex. -/
  lift : ∀ (W : C) (k : ∀ b, b ∈ S → (W ⟶ (endo b).obj)),
          (∀ {s t : B} (g : s ⟶ t) (hs : s ∈ S) (ht : t ∈ S),
              k s hs ≫ (endo s).ι ≫ G.map g = k t ht ≫ (endo t).ι) → (W ⟶ pt)
  /-- The factorisation produced by `lift` is one. -/
  fac : ∀ (W : C) (k) (h) (b : B) (hb : b ∈ S), lift W k h ≫ ρ b hb = k b hb
  /-- The legs are jointly monic. -/
  uniq : ∀ (W : C) (m m' : W ⟶ pt),
          (∀ (b : B) (hb : b ∈ S), m ≫ ρ b hb = m' ≫ ρ b hb) → m = m'

omit [FinCategory B] in
/-- Base case: over a single object the endo-equalizer itself is a partial limit. -/
private lemma nonempty_partialConnectedLimit_singleton (b₀ : B) :
    Nonempty (PartialConnectedLimit B G endo {b₀}) := by
  classical
  refine
    ⟨{ pt := (endo b₀).obj
       ρ := fun b hb => eqToHom (by rw [Finset.mem_singleton.1 hb])
       cross := ?_
       lift := fun W k _ => k b₀ (Finset.mem_singleton_self b₀)
       fac := ?_
       uniq := ?_ }⟩
  · intro s t g hs ht
    obtain rfl := Finset.mem_singleton.1 hs
    obtain rfl := Finset.mem_singleton.1 ht
    simpa using (endo t).equalizes g
  · intro W k h b hb
    obtain rfl := Finset.mem_singleton.1 hb
    simp
  · intro W m m' hmm
    simpa using hmm b₀ (Finset.mem_singleton_self b₀)

/-- Adjacency in `B`: an arrow in one direction or the other. -/
private def Adjacent (a b : B) : Prop := Nonempty (a ⟶ b) ∨ Nonempty (b ⟶ a)

section Incidence
variable (S : Finset B) (b' : B)

/-- The incidences between a new object `b'` and a `Finset` `S` of objects: an arrow of `B`
from `b'` to an object of `S`, or from an object of `S` to `b'`. -/
private abbrev Incidence : Type := Σ s : {x // x ∈ S}, ((b' ⟶ s.1) ⊕ (s.1 ⟶ b'))

/-- The object of `C` an incidence between `b'` and `S` constrains: the image under `G` of the
target of the arrow. -/
@[implicit_reducible]
private def incidenceObj : Incidence B S b' → C
  | ⟨s, Sum.inl _⟩ => G.obj s.1
  | ⟨_, Sum.inr _⟩ => G.obj b'

/-- The leg of a partial limit over `S` at an incidence. -/
private def incidenceLegPartial (P : PartialConnectedLimit B G endo S) :
    ∀ l : Incidence B S b', P.pt ⟶ incidenceObj B G S b' l
  | ⟨⟨s, hs⟩, Sum.inl _⟩ => P.ρ s hs ≫ (endo s).ι
  | ⟨⟨s, hs⟩, Sum.inr g⟩ => P.ρ s hs ≫ (endo s).ι ≫ G.map g

/-- The leg of the endo-equalizer of `b'` at an incidence. -/
private def incidenceLegEndo :
    ∀ l : Incidence B S b', (endo b').obj ⟶ incidenceObj B G S b' l
  | ⟨_, Sum.inl g⟩ => (endo b').ι ≫ G.map g
  | ⟨_, Sum.inr _⟩ => (endo b').ι

omit [FinCategory B] in
/-- Adjacency to an object of `S` exhibits an incidence, so the incidence family of an
adjacent object is nonempty. -/
private lemma nonempty_incidence_of_adjacent (hadj : ∃ s₀ ∈ S, Adjacent B s₀ b') :
    Nonempty (Incidence B S b') := by
  obtain ⟨s₀, hs₀, hadj0⟩ := hadj
  exact hadj0.elim (fun ⟨g⟩ => ⟨⟨⟨s₀, hs₀⟩, Sum.inr g⟩⟩) fun ⟨g⟩ => ⟨⟨⟨s₀, hs₀⟩, Sum.inl g⟩⟩

end Incidence

section InsertGlue

omit [FinCategory B] in
/-- The glued legs are compatible with every arrow between objects of `insert b' S`: for an
arrow inside `S` this is the compatibility of `P`, for an arrow meeting `b'` it is the
corresponding incidence condition of the glue, and for an endomorphism of `b'` it is the
defining property of the endo-equalizer. -/
private lemma cross_insert_of_glue [DecidableEq B] (S : Finset B) (b' : B)
    (P : PartialConnectedLimit B G endo S)
    (Q : CospanGlue P.pt (endo b').obj (incidenceObj B G S b')
      (incidenceLegPartial B G endo S b' P) (incidenceLegEndo B G endo S b'))
    (ρ' : ∀ b, b ∈ insert b' S → (Q.pt ⟶ (endo b).obj))
    (hρb' : ∀ hb : b' ∈ insert b' S, ρ' b' hb = Q.v)
    (hρS : ∀ b (hbS : b ∈ S) (hb : b ∈ insert b' S), ρ' b hb = Q.w ≫ P.ρ b hbS)
    {s t : B} (g : s ⟶ t) (hs : s ∈ insert b' S) (ht : t ∈ insert b' S) :
    ρ' s hs ≫ (endo s).ι ≫ G.map g = ρ' t ht ≫ (endo t).ι := by
  by_cases hsb : s = b' <;> by_cases htb : t = b'
  · subst hsb htb
    rw [hρb' hs, (endo t).equalizes g]
  · subst hsb
    have htS : t ∈ S := Finset.mem_of_mem_insert_of_ne ht htb
    rw [hρb' hs, hρS t htS ht]
    simpa [incidenceLegPartial, incidenceLegEndo] using (Q.cond ⟨⟨t, htS⟩, Sum.inl g⟩).symm
  · subst htb
    have hsS : s ∈ S := Finset.mem_of_mem_insert_of_ne hs hsb
    rw [hρb' ht, hρS s hsS hs]
    simpa [incidenceLegPartial, incidenceLegEndo] using Q.cond ⟨⟨s, hsS⟩, Sum.inr g⟩
  · have hsS : s ∈ S := Finset.mem_of_mem_insert_of_ne hs hsb
    have htS : t ∈ S := Finset.mem_of_mem_insert_of_ne ht htb
    rw [hρS s hsS hs, hρS t htS ht]
    simp only [Category.assoc, P.cross g hsS htS]

omit [FinCategory B] in
/-- A compatible family of legs at the objects of `insert b' S` factors through the glued
object: its restriction to `S` factors through `P`, its value at `b'` is a leg into the
endo-equalizer of `b'`, and the two are compatible at every incidence. -/
private lemma exists_lift_insert_of_glue [DecidableEq B] (S : Finset B) (b' : B)
    (P : PartialConnectedLimit B G endo S)
    (Q : CospanGlue P.pt (endo b').obj (incidenceObj B G S b')
      (incidenceLegPartial B G endo S b' P) (incidenceLegEndo B G endo S b'))
    (ρ' : ∀ b, b ∈ insert b' S → (Q.pt ⟶ (endo b).obj))
    (hρb' : ∀ hb : b' ∈ insert b' S, ρ' b' hb = Q.v)
    (hρS : ∀ b (hbS : b ∈ S) (hb : b ∈ insert b' S), ρ' b hb = Q.w ≫ P.ρ b hbS)
    (W : C) (k : ∀ b, b ∈ insert b' S → (W ⟶ (endo b).obj))
    (h : ∀ {s t : B} (g : s ⟶ t) (hs : s ∈ insert b' S) (ht : t ∈ insert b' S),
      k s hs ≫ (endo s).ι ≫ G.map g = k t ht ≫ (endo t).ι) :
    ∃ l : W ⟶ Q.pt, ∀ b (hb : b ∈ insert b' S), l ≫ ρ' b hb = k b hb := by
  have hcrossP : ∀ {s t : B} (g : s ⟶ t) (hs : s ∈ S) (ht : t ∈ S),
      k s (Finset.mem_insert_of_mem hs) ≫ (endo s).ι ≫ G.map g
        = k t (Finset.mem_insert_of_mem ht) ≫ (endo t).ι :=
    fun g hs ht => h g (Finset.mem_insert_of_mem hs) (Finset.mem_insert_of_mem ht)
  let wcand : W ⟶ P.pt := P.lift W (fun b hbS => k b (Finset.mem_insert_of_mem hbS)) hcrossP
  have hwfac : ∀ b (hbS : b ∈ S), wcand ≫ P.ρ b hbS = k b (Finset.mem_insert_of_mem hbS) :=
    fun b hbS => P.fac W _ hcrossP b hbS
  let vcand : W ⟶ (endo b').obj := k b' (Finset.mem_insert_self b' S)
  have hgl : ∀ l, wcand ≫ incidenceLegPartial B G endo S b' P l
      = vcand ≫ incidenceLegEndo B G endo S b' l := by
    rintro ⟨⟨s, hsS⟩, g | g⟩ <;>
      rw [incidenceLegPartial, incidenceLegEndo, ← Category.assoc, hwfac s hsS]
    · exact (h g (Finset.mem_insert_self b' S) (Finset.mem_insert_of_mem hsS)).symm
    · exact h g (Finset.mem_insert_of_mem hsS) (Finset.mem_insert_self b' S)
  refine ⟨Q.lift W wcand vcand hgl, fun b hb => ?_⟩
  by_cases hbb : b = b'
  · subst hbb
    rw [hρb' hb]
    exact Q.fac_v W wcand vcand hgl
  · have hbS : b ∈ S := Finset.mem_of_mem_insert_of_ne hb hbb
    rw [hρS b hbS hb, ← Category.assoc, Q.fac_w W wcand vcand hgl]
    exact hwfac b hbS

omit [FinCategory B] in
/-- The glued legs are jointly monic: the legs over `S` detect the projection to `P`, and the
leg at `b'` is the projection to the endo-equalizer of `b'`. -/
private lemma uniq_insert_of_glue [DecidableEq B] (S : Finset B) (b' : B)
    (P : PartialConnectedLimit B G endo S)
    (Q : CospanGlue P.pt (endo b').obj (incidenceObj B G S b')
      (incidenceLegPartial B G endo S b' P) (incidenceLegEndo B G endo S b'))
    (ρ' : ∀ b, b ∈ insert b' S → (Q.pt ⟶ (endo b).obj))
    (hρb' : ∀ hb : b' ∈ insert b' S, ρ' b' hb = Q.v)
    (hρS : ∀ b (hbS : b ∈ S) (hb : b ∈ insert b' S), ρ' b hb = Q.w ≫ P.ρ b hbS)
    (W : C) (m m' : W ⟶ Q.pt)
    (hmm : ∀ (b : B) (hb : b ∈ insert b' S), m ≫ ρ' b hb = m' ≫ ρ' b hb) : m = m' := by
  refine Q.uniq W m m' (P.uniq W _ _ fun b hbS => ?_) ?_
  · have hb := hmm b (Finset.mem_insert_of_mem hbS)
    rwa [hρS b hbS (Finset.mem_insert_of_mem hbS), ← Category.assoc, ← Category.assoc] at hb
  · have hb := hmm b' (Finset.mem_insert_self b' S)
    rwa [hρb' (Finset.mem_insert_self b' S)] at hb

end InsertGlue

variable [HasPullbacks C] [HasEqualizers C]

/-- Growth step: a partial limit over `S` extends over `insert b' S`, provided `b'` is
adjacent to some object already in `S`. That adjacency makes the index family of
incidences between `b'` and `S` nonempty, so `CospanGlue` applies. -/
private lemma nonempty_partialConnectedLimit_insert [DecidableEq B]
    (S : Finset B) (b' : B) (hb' : b' ∉ S)
    (hadj : ∃ s₀ ∈ S, Adjacent B s₀ b') (P : PartialConnectedLimit B G endo S) :
    Nonempty (PartialConnectedLimit B G endo (insert b' S)) := by
  classical
  obtain ⟨Q⟩ := nonempty_cospanGlue P.pt (endo b').obj (incidenceObj B G S b')
    (incidenceLegPartial B G endo S b' P) (incidenceLegEndo B G endo S b')
    (nonempty_incidence_of_adjacent B S b' hadj)
  let ρ' : ∀ b, b ∈ insert b' S → (Q.pt ⟶ (endo b).obj) := fun b hb =>
    if hbb : b = b' then Q.v ≫ eqToHom (by rw [hbb])
    else Q.w ≫ P.ρ b (Finset.mem_of_mem_insert_of_ne hb hbb)
  have hρb' : ∀ hb : b' ∈ insert b' S, ρ' b' hb = Q.v := fun _ => by
    simp [ρ']
  have hρS : ∀ b (hbS : b ∈ S) (hb : b ∈ insert b' S), ρ' b hb = Q.w ≫ P.ρ b hbS := by
    intro b hbS hb
    have hne : b ≠ b' := fun h => hb' (h ▸ hbS)
    simp [ρ', hne]
  exact ⟨{ pt := Q.pt
           ρ := ρ'
           cross := fun g hs ht => cross_insert_of_glue B G endo S b' P Q ρ' hρb' hρS g hs ht
           lift := fun W k h =>
             (exists_lift_insert_of_glue B G endo S b' P Q ρ' hρb' hρS W k h).choose
           fac := fun W k h b hb =>
             (exists_lift_insert_of_glue B G endo S b' P Q ρ' hρb' hρS W k h).choose_spec b hb
           uniq := uniq_insert_of_glue B G endo S b' P Q ρ' hρb' hρS }⟩

/-- In a connected shape, a nonempty proper subset of the objects has an object
adjacent to one outside it — otherwise the subset would be closed under arrows in
both directions and `induct_on_objects` would force it to be everything. -/
private lemma exists_adjacent_notMem [IsConnected B] (S : Finset B) (hne : S ≠ ∅)
    (hnu : S ≠ Finset.univ) : ∃ s ∈ S, ∃ b' ∉ S, Adjacent B s b' := by
  by_contra h
  push Not at h
  obtain ⟨j₀, hj₀⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  have hcl : ∀ {j₁ j₂ : B} (_ : j₁ ⟶ j₂), j₁ ∈ S ↔ j₂ ∈ S := fun f =>
    ⟨fun h₁ => Classical.byContradiction fun h₂ => h _ h₁ _ h₂ (Or.inl ⟨f⟩),
      fun h₂ => Classical.byContradiction fun h₁ => h _ h₂ _ h₁ (Or.inr ⟨f⟩)⟩
  exact hnu <| Finset.eq_univ_of_forall
    (induct_on_objects (S : Set B) (j₀ := j₀) hj₀ fun {_ _} f => hcl f)

/-- Growing from a single object along the connected shape reaches every object. -/
private lemma nonempty_partialConnectedLimit_univ [IsConnected B] :
    Nonempty (PartialConnectedLimit B G endo Finset.univ) := by
  classical
  obtain ⟨b₀⟩ := (inferInstance : Nonempty B)
  suffices H : ∀ (m : ℕ) (S : Finset B), (Finset.univ \ S).card = m →
      S.Nonempty → Nonempty (PartialConnectedLimit B G endo S) →
      Nonempty (PartialConnectedLimit B G endo Finset.univ) from
    H _ {b₀} rfl ⟨b₀, Finset.mem_singleton_self b₀⟩
      (nonempty_partialConnectedLimit_singleton B G endo b₀)
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro S hcard hne hP
    by_cases hnu : S = Finset.univ
    · exact hnu ▸ hP
    · obtain ⟨s, hsS, b', hb', hadj⟩ :=
        exists_adjacent_notMem B S (Finset.nonempty_iff_ne_empty.mp hne) hnu
      have hlt : (Finset.univ \ insert b' S).card < m := by
        rw [← hcard, Finset.sdiff_insert]
        exact Finset.card_erase_lt_of_mem (Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hb'⟩)
      exact ih _ hlt (insert b' S) rfl ⟨b', Finset.mem_insert_self b' S⟩
        (nonempty_partialConnectedLimit_insert B G endo S b' hb' ⟨s, hsS, hadj⟩ hP.some)

include endo in
/-- The total partial limit is a limit of `G`: its legs, postcomposed with the
endo-equalizer monos, form a cone, and its universal property is exactly the cone
universal property once every cone leg is factored through its endo-equalizer. -/
private lemma hasLimit_of_endoEqualizer [IsConnected B] : HasLimit G := by
  classical
  obtain ⟨P⟩ := nonempty_partialConnectedLimit_univ B G endo
  let π : ∀ b : B, P.pt ⟶ G.obj b := fun b => P.ρ b (Finset.mem_univ b) ≫ (endo b).ι
  let cone : Cone G :=
    { pt := P.pt
      π := { app := π
             naturality := fun a b g => by
               simpa only [π, Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
                 Category.assoc] using (P.cross g (Finset.mem_univ a) (Finset.mem_univ b)).symm } }
  refine HasLimit.mk { cone := cone, isLimit := ?_ }
  let ν : ∀ (s : Cone G) b, b ∈ (Finset.univ : Finset B) → (s.pt ⟶ (endo b).obj) :=
    fun s b _ => (endo b).lift s.pt (s.π.app b) s.w
  have hνfac : ∀ (s : Cone G) b (hb : b ∈ (Finset.univ : Finset B)),
      ν s b hb ≫ (endo b).ι = s.π.app b :=
    fun s b _ => (endo b).fac s.pt (s.π.app b) s.w
  have hνcross : ∀ (s : Cone G), ∀ {a b : B} (g : a ⟶ b) (ha : a ∈ (Finset.univ : Finset B))
      (hb : b ∈ (Finset.univ : Finset B)),
      ν s a ha ≫ (endo a).ι ≫ G.map g = ν s b hb ≫ (endo b).ι := by
    intro s a b g ha hb
    rw [← Category.assoc, hνfac s a ha, hνfac s b hb]
    exact s.w g
  let liftf : ∀ (s : Cone G), s.pt ⟶ P.pt := fun s => P.lift s.pt (ν s) (hνcross s)
  have hliftfac : ∀ (s : Cone G) b (hb : b ∈ (Finset.univ : Finset B)),
      liftf s ≫ P.ρ b hb = ν s b hb :=
    fun s b hb => P.fac s.pt (ν s) (hνcross s) b hb
  refine { lift := liftf, fac := ?_, uniq := ?_ }
  · intro s b
    dsimp only [cone, π]
    rw [← Category.assoc, hliftfac s b (Finset.mem_univ b), hνfac s b (Finset.mem_univ b)]
  · intro s m hm
    apply P.uniq
    intro b hb
    apply (endo b).uniq
    rw [Category.assoc, show m ≫ P.ρ b hb ≫ (endo b).ι = s.π.app b from hm b,
      hliftfac s b hb, hνfac s b hb]

end Assemble

/-- Every diagram over a finite connected shape has a limit, given finite wide
pullbacks and equalizers: take the per-object endo-equalizers and assemble them
along a spanning tree of the shape. -/
private lemma hasLimit_of_finite_connected {C : Type u} [Category.{v} C]
    [HasFiniteWidePullbacks C] [HasEqualizers C]
    (B : Type) [SmallCategory B] [FinCategory B] [IsConnected B]
    (G : B ⥤ C) : HasLimit G :=
  hasLimit_of_endoEqualizer B G fun b => (nonempty_endoEqualizer B G b).some

/-- The hard direction of Stacks 04AT, in its per-shape form: finite wide pullbacks
and equalizers give limits of every finite connected shape. -/
theorem hasLimitsOfShape_of_isConnected
    (C : Type u) [Category.{v} C] [HasFiniteWidePullbacks C] [HasEqualizers C]
    (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J] :
    HasLimitsOfShape J C :=
  ⟨fun F => hasLimit_of_finite_connected J F⟩

/-- **Stacks 04AT.** A category `C` admits limits over every finite connected shape
if and only if it has equalizers and pullbacks. -/
@[stacks 04AT]
theorem hasLimitsOfShape_isConnected_iff_hasEqualizers_and_hasPullbacks
    (C : Type u) [Category.{v} C] :
    (∀ (J : Type) [SmallCategory J] [FinCategory J] [IsConnected J], HasLimitsOfShape J C) ↔
      (HasEqualizers C ∧ HasPullbacks C) := by
  refine ⟨fun h => ⟨h WalkingParallelPair, h WalkingCospan⟩, ?_⟩
  rintro ⟨_, _⟩ J _ _ _
  have : HasFiniteWidePullbacks C := hasFiniteWidePullbacks_of_hasPullbacks C
  exact hasLimitsOfShape_of_isConnected C J

end CategoryTheory.Limits
