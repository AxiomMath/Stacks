module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack

/-! # Stacks 04TU needs its "isomorphic" read fibrewise

Conditions (1) and (3) of Stacks 04TU ask of an object `y` of `𝒳` that it be *isomorphic to an
object of `𝒮'`*. Read plainly — some isomorphism of `𝒳` onto an object of `𝒮'`, which is
`CategoryTheory.ObjectProperty.isoClosure` — the lemma is false, and this file proves it false, so
that the fibrewise reading `CategoryTheory.Functor.IsoOverId` used by
`CategoryTheory.Functor.IsStack.fullSubcategory` is pinned down as a repair of the statement rather
than a convenience.

The counterexample is as small as it can be. The base `Pt` has one object whose automorphism group
is `ℤ/2`, written as `Bool` under `xor`; the total category `Ob` has two objects and exactly one
morphism between any two of them; and `proj : Ob ⥤ Pt` sends the morphism between the two distinct
objects to the nontrivial automorphism. So the two objects of `Ob` are isomorphic, but only over
that automorphism: the fibre of `proj` over the unique object of `Pt` is discrete with two objects.
Take for `𝒮'` the subcategory containing just the object `⟨false⟩`.

Then `proj` is a stack for the trivial topology, and both conditions hold in the plain reading —
indeed vacuously, since *every* object of `Ob` is isomorphic to `⟨false⟩` — while the full
subcategory is not a stack, because it is not even prefibered: the nontrivial automorphism of the
base has no lift at all inside `𝒮'`, which is precisely the step the source's proof hint attributes
to condition (1), "the first condition guarantees that `𝒮'` is a fibred category". Since the two
objects lie over the *same* object of the base, the example equally refutes the intermediate
reading that asks only for an isomorphism onto an object of `𝒮'` lying over the same object
of `𝒮`.

## Main results

* `CategoryTheory.PlainIsoCounterexample.plainConditions_not_sufficient`, the four facts together.
-/

@[expose] public section

namespace CategoryTheory.PlainIsoCounterexample

open Opposite

/-! ### A sheaf criterion

The morphism presheaves of the example have at most one section over every object, and every
covering sieve of the trivial topology contains an identity, so they are sheaves for the reason
that nothing has to be glued. -/

/-- A presheaf of subsingletons is a sheaf for any topology whose covering sieves all contain an
identity: the section over the identity is the only candidate amalgamation, and every equation
demanded of it holds in a subsingleton. -/
lemma isSheaf_of_subsingleton {C : Type*} [Category C] (K : GrothendieckTopology C)
    (F : Cᵒᵖ ⥤ Type*) (hsub : ∀ X, Subsingleton (F.obj X))
    (hid : ∀ (X : C) (S : Sieve X), S ∈ K X → S.arrows (𝟙 X)) :
    Presheaf.IsSheaf K F := by
  rw [isSheaf_iff_isSheaf_of_type]
  intro X S hS fam _
  refine ⟨fam (𝟙 X) (hid X S hS), fun Y f hf => (hsub _).elim _ _, fun t _ => (hsub _).elim _ _⟩

/-! ### The base and the total category -/

/-- The base: one object, whose automorphism group is `ℤ/2` written as `Bool` under `xor`. -/
inductive Pt : Type
  | pt

/-- The total category: two objects, one morphism between any two of them. -/
structure Ob : Type where
  /-- The `Bool` distinguishing the two objects. `proj` sends a morphism to the difference of the
  tags of its endpoints, so a morphism is vertical exactly when the tags agree. -/
  tag : Bool

/-- `xor` composes tag differences: this is functoriality of `proj`. -/
lemma xor_cocycle (a b c : Bool) : xor a c = xor (xor a b) (xor b c) := by revert a b c; decide

/-- Cancellation of `xor`, used to lift a morphism of the base to `Ob`. -/
lemma xor_cancel (a b : Bool) : xor (xor a b) b = a := by revert a b; decide

/-- One object, `Bool` worth of endomorphisms composing by `xor`. -/
instance categoryPt : Category.{0} Pt where
  Hom _ _ := Bool
  id _ := false
  comp f g := xor f g
  id_comp f := Bool.false_xor f
  comp_id f := Bool.xor_false f
  assoc f g h := Bool.xor_assoc f g h

/-- Two objects, exactly one morphism between any two of them. -/
instance categoryOb : Category.{0} Ob where
  Hom _ _ := PUnit
  id _ := ⟨⟩
  comp _ _ := ⟨⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- There is at most one morphism between two objects of `Ob`. -/
instance obHomSubsingleton (x y : Ob) : Subsingleton (x ⟶ y) := ⟨fun _ _ => rfl⟩

/-- Every morphism of `Ob` is an isomorphism. -/
instance obIsIso {x y : Ob} (φ : x ⟶ y) : IsIso φ := ⟨⟨⟩, rfl, rfl⟩

/-- Any two objects of `Ob` are isomorphic. -/
def obIso (x y : Ob) : x ≅ y where
  hom := ⟨⟩
  inv := ⟨⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The projection: it collapses the two objects of `Ob`, sending the isomorphism between the two
distinct ones to the nontrivial automorphism of the base. -/
def proj : Ob ⥤ Pt where
  obj _ := Pt.pt
  map {x y} _ := xor x.tag y.tag
  map_id x := Bool.xor_self x.tag
  map_comp {x y z} _ _ := xor_cocycle x.tag y.tag z.tag

/-- `proj` sends a morphism to the difference of the tags of its endpoints. -/
@[simp]
lemma proj_map {x y : Ob} (φ : x ⟶ y) : proj.map φ = xor x.tag y.tag := rfl

/-- A morphism of `Ob` lifts exactly the difference of the tags of its endpoints. In particular it
is vertical exactly when the tags agree. -/
lemma isHomLift_iff {x y : Ob} {R S : Pt} (f : R ⟶ S) (φ : x ⟶ y) :
    proj.IsHomLift f φ ↔ xor x.tag y.tag = f := by
  obtain ⟨⟩ := R; obtain ⟨⟩ := S
  refine ⟨fun _ => ?_, fun h => ?_⟩
  · rw [IsHomLift.eq_of_isHomLift proj f φ, proj_map]
  · rw [← h, ← proj_map φ]; infer_instance

/-- Every morphism of `Ob` is strongly cartesian over the difference of the tags of its endpoints,
since it is an isomorphism. -/
lemma isStronglyCartesian_of_tag {x y : Ob} {R S : Pt} (f : R ⟶ S) (φ : x ⟶ y)
    (h : xor x.tag y.tag = f) : proj.IsStronglyCartesian f φ :=
  have : proj.IsHomLift f φ := (isHomLift_iff f φ).2 h
  Functor.IsStronglyCartesian.of_isIso proj f φ

/-- `proj` is a fibred category: every morphism of the base is lifted, at either object of `Ob`, by
the unique morphism with the right difference of tags. -/
instance projIsFibered : proj.IsFibered :=
  Functor.IsFibered.of_exists_isStronglyCartesian fun a _ f =>
    ⟨⟨xor f a.tag⟩, ⟨⟩, isStronglyCartesian_of_tag f ⟨⟩ (xor_cancel f a.tag)⟩

/-- An object over the base admits a cartesian morphism to another exactly when the difference of
the tags is the morphism of the base being lifted; this reads off the tag of a pullback. -/
lemma tag_eq_of_isCartesian {x y : Ob} {R S : Pt} (f : R ⟶ S) (φ : x ⟶ y)
    (h : proj.IsCartesian f φ) : xor x.tag y.tag = f :=
  have := h
  (isHomLift_iff f φ).1 inferInstance

/-! ### The subcategory -/

/-- The subcategory containing just the object with tag `false`. It is not closed under
isomorphism: the object with tag `true` is isomorphic to it, over the nontrivial automorphism of
the base. -/
def tagFalse : ObjectProperty Ob := fun x => x.tag = false

/-- Condition (1) of Stacks 04TU in the plain reading holds, and vacuously so: every object of `Ob`
is isomorphic to the object with tag `false`. -/
lemma closedUnderStronglyCartesianUpToIso :
    Functor.ClosedUnderStronglyCartesianUpToIso proj tagFalse := by
  intro _ _ y _ _ _ _ _
  exact ⟨⟨false⟩, rfl, ⟨obIso y ⟨false⟩⟩⟩

/-- Condition (3) of Stacks 04TU in the plain reading holds, for the same reason. -/
lemma locallyClosedUpToIso (J : GrothendieckTopology Pt) :
    Functor.LocallyClosedUpToIso proj tagFalse J := by
  intro _ _ _ _ _ x _
  exact ⟨⟨false⟩, rfl, ⟨obIso x.1 ⟨false⟩⟩⟩

/-! ### `proj` is a stack for the trivial topology -/

/-- Every covering sieve of the trivial topology on `Over Pt.pt` is the maximal one. -/
lemma arrows_id_of_mem_over {Y : Over Pt.pt} (S : Sieve Y)
    (hS : S ∈ ((GrothendieckTopology.trivial Pt).over Pt.pt) Y) : S.arrows (𝟙 Y) := by
  rw [GrothendieckTopology.mem_over_iff, GrothendieckTopology.trivial_covering] at hS
  have : S = ⊤ := (Sieve.overEquiv Y).injective (by rw [hS, OrderIso.map_top])
  rw [this]
  trivial

/-- Condition (2) of Stacks 026F: the morphism presheaves have at most one section over each object
of `Pt/U`, so they are sheaves. -/
lemma isMorSheaf_trivial (U : Pt) (x y : proj.Fiber U) :
    Functor.IsMorSheaf proj (GrothendieckTopology.trivial Pt) U x y := by
  obtain ⟨⟩ := U
  exact isSheaf_of_subsingleton _ _ (fun _ => ⟨fun _ _ => Functor.Fiber.hom_ext rfl⟩)
    fun _ S hS => arrows_id_of_mem_over S hS

/-- The three tag equations that a gluing isomorphism of a descent datum produces, combined. -/
lemma bool_glue (a b f tL tR : Bool) (hL : xor tL a = false) (hR : xor tR b = f)
    (hI : xor tL tR = false) : a = xor f b := by revert a b f tL tR; decide

/-- Reading the tag equation of a descent datum as the tag equation of a cartesian morphism. -/
lemma bool_cancel_of_eq (a b f : Bool) (h : a = xor f b) : xor a b = f := by revert a b f; decide

/-- The tag of a chosen pullback of `a` along `f` differs from the tag of `a` by `f`. -/
private lemma tag_pullbackFiber {R S : Pt} (a : proj.Fiber S) (f : R ⟶ S) :
    xor (Functor.pullbackFiber proj a f).1.tag a.1.tag = f :=
  tag_eq_of_isCartesian f (Functor.IsPreFibered.pullbackMap a.2 f)
    (Functor.IsPreFibered.pullbackMap.IsCartesian a.2 f)

/-- The tag of the object a descent datum attaches to an arrow `f` is determined by the tag of the
object it attaches to the identity: the chosen pullbacks of the two along `f` and the identity are
glued by a vertical isomorphism, and a vertical morphism of `Ob` forces the tags to agree. -/
lemma tag_obj_eq {R : Sieve Pt.pt} (D : Functor.SieveDescentDatum proj R)
    (hid : R.arrows (𝟙 Pt.pt)) {V : Pt} (f : V ⟶ Pt.pt) (hf : R.arrows f) :
    (D.obj f hf).1.tag = xor f (D.obj (𝟙 Pt.pt) hid).1.tag := by
  obtain ⟨⟩ := V
  have heq : 𝟙 Pt.pt ≫ f = f ≫ 𝟙 Pt.pt := by rw [Category.id_comp, Category.comp_id]
  refine bool_glue _ _ f
    (Functor.pullbackFiber proj (D.obj f hf) (𝟙 Pt.pt)).1.tag
    (Functor.pullbackFiber proj (D.obj (𝟙 Pt.pt) hid) f).1.tag ?_ ?_ ?_
  · exact tag_pullbackFiber (D.obj f hf) (𝟙 Pt.pt)
  · exact tag_pullbackFiber (D.obj (𝟙 Pt.pt) hid) f
  · exact (isHomLift_iff _ _).1 (D.iso hf hid (𝟙 Pt.pt) f heq).hom.2

/-- Condition (3) of Stacks 026F: every descent datum relative to a covering sieve of the trivial
topology — that is, relative to the maximal sieve — is effective, the object it descends to
being the one the datum attaches to the identity. -/
lemma hasEffectiveDescent_trivial :
    Functor.HasEffectiveDescent proj (GrothendieckTopology.trivial Pt) := by
  intro U R hR D
  obtain ⟨⟩ := U
  rw [GrothendieckTopology.trivial_covering] at hR
  subst hR
  have hid : (⊤ : Sieve Pt.pt).arrows (𝟙 Pt.pt) := trivial
  refine ⟨D.obj (𝟙 Pt.pt) hid, fun _ _ _ => ⟨⟩, fun V f hf => ?_, fun V W Z f hf g hg ε ε' heq =>
    rfl⟩
  have : proj.IsStronglyCartesian f (⟨⟩ : (D.obj f hf).1 ⟶ (D.obj (𝟙 Pt.pt) hid).1) :=
    isStronglyCartesian_of_tag f ⟨⟩ (bool_cancel_of_eq _ _ _ (tag_obj_eq D hid f hf))
  exact inferInstanceAs (proj.IsCartesian f (⟨⟩ : (D.obj f hf).1 ⟶ (D.obj (𝟙 Pt.pt) hid).1))

/-- `proj` is a stack for the trivial topology. -/
theorem isStack : Functor.IsStack proj (GrothendieckTopology.trivial Pt) where
  isFibered := inferInstance
  isMorSheaf := isMorSheaf_trivial
  hasEffectiveDescent := hasEffectiveDescent_trivial

/-! ### The conclusion -/

/-- The restriction of `proj` to `tagFalse` is not prefibered: the nontrivial automorphism of the
base has no lift inside the subcategory, because the only object of the subcategory lies over the
base with tag `false`. -/
lemma not_isPreFibered_restrict : ¬ (Functor.restrict proj tagFalse).IsPreFibered := by
  intro h
  have := h
  obtain ⟨b, φ, hφ⟩ := Functor.IsPreFibered.exists_isCartesian'
    (p := Functor.restrict proj tagFalse) (a := ⟨⟨false⟩, rfl⟩) (R := Pt.pt) (f := true)
  have h1 : (Functor.restrict proj tagFalse).IsHomLift (R := Pt.pt) (S := Pt.pt) true φ :=
    hφ.toIsHomLift
  have h2 : proj.IsHomLift (R := Pt.pt) (S := Pt.pt) true (tagFalse.ι.map φ) :=
    (Functor.isHomLift_restrict_iff proj tagFalse (V := Pt.pt) (U := Pt.pt) true φ).1 h1
  have h3 : xor b.1.tag (⟨false⟩ : Ob).tag = true := (isHomLift_iff _ _).1 h2
  rw [show b.1.tag = false from b.2] at h3
  exact absurd h3 (by decide)

/-- The restriction of `proj` to `tagFalse` is not a stack: a stack is in particular a fibred
category, and this is not even prefibered. -/
theorem not_isStack_restrict :
    ¬ Functor.IsStack (Functor.restrict proj tagFalse) (GrothendieckTopology.trivial Pt) :=
  fun h => not_isPreFibered_restrict h.isFibered.toIsPreFibered

/-- **Stacks 04TU read with a plain "isomorphic" is false.** `proj` is a stack over the site
`(Pt, trivial)`, the subcategory `tagFalse` is full by construction — condition (2) — and satisfies
conditions (1) and (3) with "isomorphic to an object of `𝒮'`" read as an isomorphism of the ambient
category, yet the full subcategory it cuts out is not a stack. So the fibrewise reading
`CategoryTheory.Functor.IsoOverId` used in `CategoryTheory.Functor.IsStack.fullSubcategory` is
not a strengthening for convenience but a necessary reading of the source. -/
theorem plainConditions_not_sufficient :
    Functor.IsStack proj (GrothendieckTopology.trivial Pt) ∧
      Functor.ClosedUnderStronglyCartesianUpToIso proj tagFalse ∧
      Functor.LocallyClosedUpToIso proj tagFalse (GrothendieckTopology.trivial Pt) ∧
      ¬ Functor.IsStack (Functor.restrict proj tagFalse) (GrothendieckTopology.trivial Pt) :=
  ⟨isStack, closedUnderStronglyCartesianUpToIso, locallyClosedUpToIso _, not_isStack_restrict⟩

end CategoryTheory.PlainIsoCounterexample
