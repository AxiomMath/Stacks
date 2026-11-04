module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeMorphismSheaf

/-!
# The presheaf of pairs behind the excision equivalence

Let `f : V ⟶ W` and `h : Y ⟶ V` be morphisms of algebraic spaces over a scheme `S`. The
quasi-inverse of the base-change functor of Stacks 0BGY is built from the presheaf whose
sections over a scheme `T` are the pairs `(w, y)` consisting of a morphism `w : T ⟶ W` and a
morphism `y : T ×_{w, W} V ⟶ Y` *over `V`*.

The relative morphism functor of Stacks 05Y2,
`AlgebraicGeometry.Space.relativeHom B S hS V Y W f (h ≫ f)`, already has the pairs `(w, y)`
with `y` a morphism over `W` as its sections, and is already known to be an fppf sheaf. The
pairs wanted here are cut out of it by one equation, `y ≫ h = pullback.snd w f`, so they form
a subfunctor; and that subfunctor is a sheaf because the equation is the equalizer of two
morphisms of presheaves into another relative morphism functor.

## Main definitions

* `AlgebraicGeometry.Space.RelativeMorphism.ext_of_heq` is the extensionality of pairs that the
  dependence of the type of the second component on the first forces.
* `AlgebraicGeometry.Space.RelativeMorphism.post` and
  `AlgebraicGeometry.Space.RelativeMorphism.taut` are the two operations on pairs being
  compared: postcomposing the second component with `h`, and replacing it by the tautological
  projection.
* `AlgebraicGeometry.Space.excisionSub` is the subfunctor of the relative morphism functor on
  which those two operations agree.
* `AlgebraicGeometry.Space.excisionSpace` and `AlgebraicGeometry.Space.excisionProj` are that
  subfunctor read as a presheaf and its projection to `W`.
* `AlgebraicGeometry.Space.excisionDesc` turns a pair `(a : P ⟶ W, b : P ×_{a, W} V ⟶ Y)` over
  `V` into a morphism `P ⟶ excisionSpace` over `W`.

## Main results

* `AlgebraicGeometry.Space.mem_excisionSub_iff`: membership in the subfunctor is the equation
  `y ≫ h = pullback.snd w f`.
* `AlgebraicGeometry.Space.isSheaf_excisionSpace`: the presheaf of pairs is an fppf sheaf.
* `AlgebraicGeometry.Space.excisionDesc_comp_excisionProj` and
  `AlgebraicGeometry.Space.excisionBaseEquiv_excisionDesc`: the morphism produced by
  `excisionDesc` lies over the given morphism to `W`, and its sections are the restrictions of
  the given pair.

## Implementation notes

`AlgebraicGeometry.Space.natTransEqualizer` is the subfunctor on which two morphisms of
presheaves agree. It is not `CategoryTheory.Subfunctor.equalizer`, which equalizes two
morphisms out of `A.toFunctor` for a subfunctor `A` and would have to be applied at `A = ⊤`
and then transported along `CategoryTheory.Subfunctor.ι` of the top subfunctor.

Both components of a section are extracted through
`AlgebraicGeometry.Space.relativeHomSections`, the identification of the sections of the
relative morphism functor with the pairs of Stacks 05Y1, whose restriction maps are literally
restriction of pairs by `AlgebraicGeometry.Space.relativeHomSections_map`. That lemma is
restated here as `AlgebraicGeometry.Space.excisionBaseEquiv_map` and
`AlgebraicGeometry.Space.excisionTargetEquiv_map`, with the restriction map indexed by a
morphism of the opposite category rather than by its opposite, which is the form every rewrite
below needs.

## References

* [Stacks Project, Tag 05Y1](https://stacks.math.columbia.edu/tag/05Y1)
* [Stacks Project, Tag 05Y2](https://stacks.math.columbia.edu/tag/05Y2)
* [Stacks Project, Tag 05Y3](https://stacks.math.columbia.edu/tag/05Y3)
* [Stacks Project, Tag 0BGY](https://stacks.math.columbia.edu/tag/0BGY)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u u₁ v₁ w₁

namespace AlgebraicGeometry.Space

/-! ### The subfunctor on which two morphisms of presheaves agree -/

section Equalizer

variable {C : Type u₁} [Category.{v₁} C] {F G : Cᵒᵖ ⥤ Type w₁} (α β : F ⟶ G)

/-- The subfunctor of sections on which two morphisms of presheaves agree. -/
def natTransEqualizer : Subfunctor F where
  obj A := {s | α.app A s = β.app A s}
  map i s hs := by
    have hs' : α.app _ s = β.app _ s := hs
    change α.app _ (F.map i s) = β.app _ (F.map i s)
    rw [NatTrans.naturality_apply α i s, NatTrans.naturality_apply β i s, hs']

/-- A section lies in the equalizer subfunctor exactly when the two morphisms agree on it. -/
@[simp]
theorem mem_natTransEqualizer_iff {A : Cᵒᵖ} (s : F.obj A) :
    s ∈ (natTransEqualizer α β).obj A ↔ α.app A s = β.app A s := Iff.rfl

/-- The subfunctor on which two morphisms into a separated presheaf agree is a sheaf as soon as
the source is: a section which locally lies in it has the two images equal locally, hence
equal. -/
theorem isSheaf_natTransEqualizer {J : GrothendieckTopology C}
    (hF : Presieve.IsSheaf J F) (hG : Presieve.IsSeparated J G) :
    Presieve.IsSheaf J (natTransEqualizer α β).toFunctor := by
  rw [Subfunctor.isSheaf_iff _ hF]
  intro A s hs
  show α.app A s = β.app A s
  refine hG _ hs (fun T i _ => G.map i.op (α.app A s)) _ _ (fun T i _ => rfl)
    (fun T i hi => ?_)
  have hi' : α.app (op T) (F.map i.op s) = β.app (op T) (F.map i.op s) := hi
  rw [← NatTrans.naturality_apply β i.op s, ← hi', NatTrans.naturality_apply α i.op s]

end Equalizer

/-! ### Two operations on the pairs of Stacks 05Y1 -/

section Operations

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Two pairs are equal as soon as their first components are and their second components are
equal up to the resulting identification of types. -/
theorem RelativeMorphism.ext_of_heq {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {z : Z ⟶ Q}
    {x : X ⟶ Q} {p q : RelativeMorphism B S hS Z X Q z x T} (hbase : p.base = q.base)
    (hm : HEq p.morphism q.morphism) : p = q := by
  obtain ⟨pb, pm, pc⟩ := p
  obtain ⟨qb, qm, qc⟩ := q
  cases hbase
  cases eq_of_heq hm
  rfl

/-- Postcompose the second component of a pair with a morphism over the base. -/
noncomputable def RelativeMorphism.post {Z X X' Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} {x' : X' ⟶ Q} (k : X ⟶ X') (hk : k ≫ x' = x)
    (p : RelativeMorphism B S hS Z X Q z x T) : RelativeMorphism B S hS Z X' Q z x' T where
  base := p.base
  morphism := p.morphism ≫ k
  commutes := by rw [Category.assoc, hk]; exact p.commutes

/-- Postcomposition does not change the first component of a pair. -/
@[simp]
theorem RelativeMorphism.post_base {Z X X' Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} {x' : X' ⟶ Q} (k : X ⟶ X') (hk : k ≫ x' = x)
    (p : RelativeMorphism B S hS Z X Q z x T) :
    (RelativeMorphism.post k hk p).base = p.base := rfl

/-- Postcomposition with `k` composes the second component of a pair with `k`. -/
@[simp]
theorem RelativeMorphism.post_morphism {Z X X' Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} {x' : X' ⟶ Q} (k : X ⟶ X') (hk : k ≫ x' = x)
    (p : RelativeMorphism B S hS Z X Q z x T) :
    (RelativeMorphism.post k hk p).morphism = p.morphism ≫ k := rfl

/-- Postcomposition commutes with restriction. -/
theorem RelativeMorphism.post_restrict {Z X X' Q T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} {x' : X' ⟶ Q} (k : X ⟶ X') (hk : k ≫ x' = x) (t : T' ⟶ T)
    (p : RelativeMorphism B S hS Z X Q z x T) :
    RelativeMorphism.post k hk (RelativeMorphism.restrict t p) =
      RelativeMorphism.restrict t (RelativeMorphism.post k hk p) := by
  refine RelativeMorphism.ext_of_heq rfl (heq_of_eq ?_)
  simp

/-- A pair whose second component is a morphism over `Z` restricts to one. -/
theorem RelativeMorphism.restrict_morphism_comp {Z X Q T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (k : X ⟶ Z) (t : T' ⟶ T)
    (p : RelativeMorphism B S hS Z X Q z x T)
    (hp : p.morphism ≫ k = pullback.snd p.base z) :
    (RelativeMorphism.restrict t p).morphism ≫ k =
      pullback.snd (RelativeMorphism.restrict t p).base z := by
  simp only [RelativeMorphism.restrict_morphism, RelativeMorphism.restrict_base,
    Category.assoc, hp, pullback.map_snd, Category.comp_id]

/-- Replace the second component of a pair by the tautological projection. -/
noncomputable def RelativeMorphism.taut {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (p : RelativeMorphism B S hS Z X Q z x T) :
    RelativeMorphism B S hS Z Z Q z z T where
  base := p.base
  morphism := pullback.snd p.base z
  commutes := rfl

/-- The tautological pair has the same first component as the given pair. -/
@[simp]
theorem RelativeMorphism.taut_base {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (p : RelativeMorphism B S hS Z X Q z x T) :
    (RelativeMorphism.taut p).base = p.base := rfl

/-- The second component of the tautological pair is the projection `pullback.snd`. -/
@[simp]
theorem RelativeMorphism.taut_morphism {Z X Q T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (p : RelativeMorphism B S hS Z X Q z x T) :
    (RelativeMorphism.taut p).morphism = pullback.snd p.base z := rfl

/-- The tautological pair commutes with restriction. -/
theorem RelativeMorphism.taut_restrict {Z X Q T T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {z : Z ⟶ Q} {x : X ⟶ Q} (t : T' ⟶ T) (p : RelativeMorphism B S hS Z X Q z x T) :
    RelativeMorphism.taut (RelativeMorphism.restrict t p) =
      RelativeMorphism.restrict t (RelativeMorphism.taut (x := x) p) := by
  refine RelativeMorphism.ext_of_heq rfl (heq_of_eq ?_)
  have key := RelativeMorphism.restrict_morphism_comp (𝟙 Z) t
    (RelativeMorphism.taut (x := x) p) (Category.comp_id _)
  rw [Category.comp_id] at key
  exact key.symm

end Operations

/-! ### The presheaf of pairs -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {V W Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : V ⟶ W) (h : Y ⟶ V)
  (hV : IsAlgebraicSpace B S hS V) (hW : IsAlgebraicSpace B S hS W)
  (hY : IsAlgebraicSpace B S hS Y)

/-- The relative morphism functor of `f` and `h ≫ f`, whose sections are the pairs `(w, y)`
with `y` a morphism over `W`. -/
noncomputable abbrev excisionBase : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  relativeHom B S hS V Y W f (h ≫ f) hV hY hW

/-- The relative morphism functor of `f` with itself, in which the two components of a section
of `AlgebraicGeometry.Space.excisionBase` are compared. -/
noncomputable abbrev excisionTarget : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  relativeHom B S hS V V W f f hV hV hW

/-- The sections of `AlgebraicGeometry.Space.excisionBase` over a scheme of the site are the
pairs of Stacks 05Y1. -/
noncomputable abbrev excisionBaseEquiv (A : (BigFppfOver B S hS)ᵒᵖ) :
    (excisionBase B S hS f h hV hW hY).obj A ≃
      RelativeMorphism B S hS V Y W f (h ≫ f) (yoneda.obj A.unop) :=
  relativeHomSections B S hS V Y W f (h ≫ f) hV hY hW A.unop

/-- The sections of `AlgebraicGeometry.Space.excisionTarget` over a scheme of the site are the
pairs of Stacks 05Y1. -/
noncomputable abbrev excisionTargetEquiv (A : (BigFppfOver B S hS)ᵒᵖ) :
    (excisionTarget B S hS f hV hW).obj A ≃
      RelativeMorphism B S hS V V W f f (yoneda.obj A.unop) :=
  relativeHomSections B S hS V V W f f hV hV hW A.unop

/-- The restriction maps of the relative morphism functor of `f` and `h ≫ f` are restriction
of pairs. -/
theorem excisionBaseEquiv_map {A A' : (BigFppfOver B S hS)ᵒᵖ} (i : A ⟶ A')
    (p : (excisionBase B S hS f h hV hW hY).obj A) :
    excisionBaseEquiv B S hS f h hV hW hY A' ((excisionBase B S hS f h hV hW hY).map i p) =
      RelativeMorphism.restrict (yoneda.map i.unop)
        (excisionBaseEquiv B S hS f h hV hW hY A p) :=
  relativeHomSections_map B S hS V Y W f (h ≫ f) hV hY hW i.unop p

/-- The restriction maps of the relative morphism functor of `f` with itself are restriction of
pairs. -/
theorem excisionTargetEquiv_map {A A' : (BigFppfOver B S hS)ᵒᵖ} (i : A ⟶ A')
    (p : (excisionTarget B S hS f hV hW).obj A) :
    excisionTargetEquiv B S hS f hV hW A' ((excisionTarget B S hS f hV hW).map i p) =
      RelativeMorphism.restrict (yoneda.map i.unop)
        (excisionTargetEquiv B S hS f hV hW A p) :=
  relativeHomSections_map B S hS V V W f f hV hV hW i.unop p

/-- Compose the second component of a pair with `h`. -/
noncomputable def excisionAlpha :
    excisionBase B S hS f h hV hW hY ⟶ excisionTarget B S hS f hV hW where
  app A := ↾fun p =>
    (excisionTargetEquiv B S hS f hV hW A).symm
      (RelativeMorphism.post h rfl (excisionBaseEquiv B S hS f h hV hW hY A p))
  naturality A A' i := by
    ext p
    refine ((excisionTargetEquiv B S hS f hV hW A').injective ?_ :
      (excisionTargetEquiv B S hS f hV hW A').symm
          (RelativeMorphism.post h rfl (excisionBaseEquiv B S hS f h hV hW hY A'
            ((excisionBase B S hS f h hV hW hY).map i p))) =
        (excisionTarget B S hS f hV hW).map i
          ((excisionTargetEquiv B S hS f hV hW A).symm
            (RelativeMorphism.post h rfl (excisionBaseEquiv B S hS f h hV hW hY A p))))
    rw [Equiv.apply_symm_apply, excisionTargetEquiv_map, Equiv.apply_symm_apply,
      excisionBaseEquiv_map, RelativeMorphism.post_restrict]

/-- Replace the second component of a pair by the tautological projection. -/
noncomputable def excisionBeta :
    excisionBase B S hS f h hV hW hY ⟶ excisionTarget B S hS f hV hW where
  app A := ↾fun p =>
    (excisionTargetEquiv B S hS f hV hW A).symm
      (RelativeMorphism.taut (excisionBaseEquiv B S hS f h hV hW hY A p))
  naturality A A' i := by
    ext p
    refine ((excisionTargetEquiv B S hS f hV hW A').injective ?_ :
      (excisionTargetEquiv B S hS f hV hW A').symm
          (RelativeMorphism.taut (excisionBaseEquiv B S hS f h hV hW hY A'
            ((excisionBase B S hS f h hV hW hY).map i p))) =
        (excisionTarget B S hS f hV hW).map i
          ((excisionTargetEquiv B S hS f hV hW A).symm
            (RelativeMorphism.taut (excisionBaseEquiv B S hS f h hV hW hY A p))))
    rw [Equiv.apply_symm_apply, excisionTargetEquiv_map, Equiv.apply_symm_apply,
      excisionBaseEquiv_map, RelativeMorphism.taut_restrict]

/-- `excisionAlpha` sends a pair to the pair with second component composed with `h`. -/
@[simp]
theorem excisionAlpha_app {A : (BigFppfOver B S hS)ᵒᵖ}
    (p : (excisionBase B S hS f h hV hW hY).obj A) :
    (excisionAlpha B S hS f h hV hW hY).app A p =
      (excisionTargetEquiv B S hS f hV hW A).symm
        (RelativeMorphism.post h rfl (excisionBaseEquiv B S hS f h hV hW hY A p)) := rfl

/-- `excisionBeta` sends a pair to the tautological pair with the same first component. -/
@[simp]
theorem excisionBeta_app {A : (BigFppfOver B S hS)ᵒᵖ}
    (p : (excisionBase B S hS f h hV hW hY).obj A) :
    (excisionBeta B S hS f h hV hW hY).app A p =
      (excisionTargetEquiv B S hS f hV hW A).symm
        (RelativeMorphism.taut (excisionBaseEquiv B S hS f h hV hW hY A p)) := rfl

/-- **The pairs `(w, y)` of the proof of Stacks 0BGY**: the subfunctor of the relative morphism
functor of `f` and `h ≫ f` cut out by the condition that the second component be a morphism
over `V`. -/
noncomputable def excisionSub : Subfunctor (excisionBase B S hS f h hV hW hY) :=
  natTransEqualizer (excisionAlpha B S hS f h hV hW hY) (excisionBeta B S hS f h hV hW hY)

/-- A section of the relative morphism functor lies in the subfunctor of pairs exactly when its
second component is a morphism over `V`. -/
theorem mem_excisionSub_iff {A : (BigFppfOver B S hS)ᵒᵖ}
    (p : (excisionBase B S hS f h hV hW hY).obj A) :
    p ∈ (excisionSub B S hS f h hV hW hY).obj A ↔
      (excisionBaseEquiv B S hS f h hV hW hY A p).morphism ≫ h =
        pullback.snd (excisionBaseEquiv B S hS f h hV hW hY A p).base f := by
  rw [excisionSub, mem_natTransEqualizer_iff, excisionAlpha_app, excisionBeta_app,
    (excisionTargetEquiv B S hS f hV hW A).symm.apply_eq_iff_eq]
  refine ⟨fun hp => ?_, fun hp => ?_⟩
  · have h2 : HEq (RelativeMorphism.post h rfl
        (excisionBaseEquiv B S hS f h hV hW hY A p)).morphism
      (RelativeMorphism.taut (excisionBaseEquiv B S hS f h hV hW hY A p)).morphism := by
      rw [hp]
    exact eq_of_heq h2
  · exact RelativeMorphism.ext_of_heq rfl (heq_of_eq (by simpa using hp))

/-- **The presheaf of pairs of the proof of Stacks 0BGY.** -/
noncomputable def excisionSpace : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (excisionSub B S hS f h hV hW hY).toFunctor

/-- The presheaf of pairs is an fppf sheaf: the relative morphism functor is one by
**Stacks 05Y3**, and the condition cut out of it is an equalizer. -/
theorem isSheaf_excisionSpace :
    Presheaf.IsSheaf (BigFppfOver.topology B S hS) (excisionSpace B S hS f h hV hW hY) := by
  rw [isSheaf_iff_isSheaf_of_type]
  refine isSheaf_natTransEqualizer _ _ ?_ ?_
  · rw [← isSheaf_iff_isSheaf_of_type]
    exact isSheaf_relativeHom B S hS V Y W f (h ≫ f) hV hY hW
  · exact ((isSheaf_iff_isSheaf_of_type _ _).1
      (isSheaf_relativeHom B S hS V V W f f hV hV hW)).isSeparated

/-- The projection of the presheaf of pairs to `W`, remembering the first component. -/
noncomputable def excisionProj : excisionSpace B S hS f h hV hW hY ⟶ W :=
  (excisionSub B S hS f h hV hW hY).ι ≫
    relativeHomProjection B S hS V Y W f (h ≫ f) hV hY hW

/-- The projection of the presheaf of pairs reads off the first component. -/
theorem excisionProj_app {A : (BigFppfOver B S hS)ᵒᵖ}
    (p : (excisionSpace B S hS f h hV hW hY).obj A) :
    (excisionProj B S hS f h hV hW hY).app A p =
      yonedaEquiv (excisionBaseEquiv B S hS f h hV hW hY A p.1).base := rfl

/-! ### Morphisms into the presheaf of pairs -/

variable {P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : P ⟶ W) (b : pullback a f ⟶ Y)
  (hb : b ≫ h = pullback.snd a f)

/-- The pair of Stacks 05Y1 determined by a morphism to `W` and a morphism over `V` out of its
fibre product with `f`. -/
noncomputable def excisionPairOf : RelativeMorphism B S hS V Y W f (h ≫ f) P where
  base := a
  morphism := b
  commutes := by rw [← Category.assoc, hb]

/-- The first component of `excisionPairOf` is `a`. -/
@[simp]
theorem excisionPairOf_base : (excisionPairOf B S hS f h a b hb).base = a := rfl

/-- The second component of `excisionPairOf` is `b`. -/
@[simp]
theorem excisionPairOf_morphism : (excisionPairOf B S hS f h a b hb).morphism = b := rfl

/-- The first component of the restriction of `excisionPairOf` along `t` is `t ≫ a`. -/
@[simp]
theorem restrict_excisionPairOf_base {P' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : P' ⟶ P) :
    (RelativeMorphism.restrict t (excisionPairOf B S hS f h a b hb)).base = t ≫ a := rfl

/-- The second component of the restriction of `excisionPairOf` along `t` is `b` precomposed
with the induced map of fibre products. -/
@[simp]
theorem restrict_excisionPairOf_morphism {P' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (t : P' ⟶ P) :
    (RelativeMorphism.restrict t (excisionPairOf B S hS f h a b hb)).morphism =
      pullback.map (t ≫ a) f a f t (𝟙 V) (𝟙 W) (by simp) (by simp) ≫ b := rfl

/-- **A pair `(a, b)` over an arbitrary presheaf induces a morphism to the presheaf of
pairs.** -/
noncomputable def excisionDesc : P ⟶ excisionSpace B S hS f h hV hW hY where
  app A := ↾fun t =>
    ⟨(excisionBaseEquiv B S hS f h hV hW hY A).symm
        (RelativeMorphism.restrict (yonedaEquiv.symm t) (excisionPairOf B S hS f h a b hb)),
      by
        rw [mem_excisionSub_iff, Equiv.apply_symm_apply]
        exact RelativeMorphism.restrict_morphism_comp h _ _ hb⟩
  naturality A A' i := by
    ext t
    refine Subtype.ext ?_
    refine ((excisionBaseEquiv B S hS f h hV hW hY A').injective ?_ :
      (excisionBaseEquiv B S hS f h hV hW hY A').symm
          (RelativeMorphism.restrict (yonedaEquiv.symm (P.map i t))
            (excisionPairOf B S hS f h a b hb)) =
        (excisionBase B S hS f h hV hW hY).map i
          ((excisionBaseEquiv B S hS f h hV hW hY A).symm
            (RelativeMorphism.restrict (yonedaEquiv.symm t)
              (excisionPairOf B S hS f h a b hb))))
    rw [Equiv.apply_symm_apply, excisionBaseEquiv_map, Equiv.apply_symm_apply,
      RelativeMorphism.restrict_comp, yonedaEquiv_symm_map]

/-- The pair named by a section of the morphism induced by `(a, b)` is the restriction of
`(a, b)`. -/
theorem excisionBaseEquiv_excisionDesc {A : (BigFppfOver B S hS)ᵒᵖ} (t : P.obj A) :
    excisionBaseEquiv B S hS f h hV hW hY A
        ((excisionDesc B S hS f h hV hW hY a b hb).app A t).1 =
      RelativeMorphism.restrict (yonedaEquiv.symm t) (excisionPairOf B S hS f h a b hb) :=
  Equiv.apply_symm_apply _ _

/-- The projection of the section produced by `excisionDesc` is the given section of `W`. -/
theorem excisionProj_excisionDesc_app {A : (BigFppfOver B S hS)ᵒᵖ} (t : P.obj A) :
    (excisionProj B S hS f h hV hW hY).app A
        ((excisionDesc B S hS f h hV hW hY a b hb).app A t) = a.app A t := by
  rw [excisionProj_app, excisionBaseEquiv_excisionDesc, RelativeMorphism.restrict_base,
    excisionPairOf_base, yonedaEquiv_symm_naturality_right, Equiv.apply_symm_apply]

/-- The morphism induced by a pair lies over the first component of the pair. -/
theorem excisionDesc_comp_excisionProj :
    excisionDesc B S hS f h hV hW hY a b hb ≫ excisionProj B S hS f h hV hW hY = a := by
  ext A t
  exact excisionProj_excisionDesc_app B S hS f h hV hW hY a b hb t

end AlgebraicGeometry.Space

end
