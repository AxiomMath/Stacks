module

public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyExistence

/-! # The 1-morphism extending `F` along a stackification

Let `(𝒞, J)` be a site, let `p : 𝒮 ⥤ 𝒞` be a fibred category, let `G : 𝒮 ⥤ 𝒮'` exhibit `𝒮'` as the
stackification of `𝒮` in the sense of Stacks 02ZN, and let `F : 𝒮 ⥤ 𝒳` be a 1-morphism of fibred
categories over `𝒞` into a stack.
`StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyExistence` proves the object half
of Stacks 0435: every object of a fibre of `𝒮'` is presented, along a covering sieve, by objects of
`𝒮` whose images under `F` descend to an object of `𝒳`. This file builds the 1-morphism
`H : 𝒮' ⥤ 𝒳` itself, shows it is a 1-morphism of fibred categories over `𝒞`, and constructs the
components of the 2-isomorphism `G ⋙ H ≅ F`.

The organising notion is a *local presentation*
(`CategoryTheory.Functor.LocalPresentation`) of an object `x` of a fibre relative to a sieve `R`:
an object of the fibre over the source of each member of `R` together with an identification of it
with the chosen pullback of `x`. Every such presentation carries a cartesian morphism to `x` over
each member of the sieve, a comparison of the presenting objects along a refinement, and — given a
morphism `m : x ⟶ x'` of the total category and a second presentation of `x'` — a *transition
morphism* of the fibres determined by the universal property of the cartesian morphism at the
target. The three of them satisfy exactly the compatibilities that
`CategoryTheory.Functor.exists_fiberHom_of_locally` needs, so a family of candidate transition
morphisms over a covering sieve glues to a morphism of the total category.

The notion is used twice over, on both sides of the stackification. A family of local objects
`s f` of `𝒮` presenting an object `x'` of `𝒮'` is a local presentation of `x'` by the images
`G (s f)`, and — once `CategoryTheory.Functor.Stackification.descentDatum` is known to descend to
an object `y` of `𝒳` — a local presentation of `y` by the images `F (s f)`, whose cartesian
morphisms are the descending family. The two are intertwined by the transfer of
`UniversalPropertyExistence`: the comparison of the presenting objects of `y` along a refinement is
the transfer of the comparison for `x'`
(`CategoryTheory.Functor.Stackification.presF_isoAlong_hom`), and therefore the transferred
transition morphisms satisfy the gluing hypothesis
(`CategoryTheory.Functor.Stackification.isoAlong_comp_transfer_transition`). Gluing them is the
action of `H` on morphisms.

## Main definitions

* `CategoryTheory.Functor.LocalPresentation`, a local presentation of an object of a fibre, with
  `CategoryTheory.Functor.LocalPresentation.mor` its cartesian morphisms,
  `CategoryTheory.Functor.LocalPresentation.isoAlong` the comparison of its presenting objects
  along a refinement, and `CategoryTheory.Functor.LocalPresentation.transition` the transition
  morphism induced by a morphism of the total category;
* `CategoryTheory.Functor.Stackification.presG` and
  `CategoryTheory.Functor.Stackification.presF`, the two presentations attached to a local
  presentation along the stackification;
* `CategoryTheory.Functor.Stackification.extend`, the 1-morphism `H : 𝒮' ⥤ 𝒳` of Stacks 0435, and
  `CategoryTheory.Functor.Stackification.unitHom`, the components of the 2-isomorphism
  `G ⋙ H ≅ F`.

## Main results

* `CategoryTheory.Functor.LocalPresentation.exists_hom_of_transition`, that a compatible family of
  transition morphisms glues, and
  `CategoryTheory.Functor.LocalPresentation.hom_ext_of_locally`, that the glued morphism is
  unique;
* `CategoryTheory.Functor.Stackification.exists_hom_of_descends`, the action on morphisms of the
  extension;
* `CategoryTheory.Functor.Stackification.extend_comp_eq` and
  `CategoryTheory.Functor.Stackification.extend_isFibredOneMorphism`, that the extension is a
  1-morphism of fibred categories over `𝒞`;
* `CategoryTheory.Functor.Stackification.isIso_unitHom` and
  `CategoryTheory.Functor.Stackification.unitHom_naturality`, that the components of the
  2-isomorphism are invertible and natural.

## Implementation notes

The universes are those of `UniversalPropertyExistence`: four independent object universes; the
hom universe of the base; the hom universe shared by `𝒮` and `𝒮'`, which
`IsFibredOneMorphism.morPresheafMap` forces because clause (1) of Stacks 02ZN is a map from the
presheaf `Mor(·, ·)` of the one to that of the other; and the hom universe of the target `𝒳`,
independent of all of them. No `UnivLE` hypothesis occurs.

## References

* [Stacks 0435](https://stacks.math.columbia.edu/tag/0435).
-/

@[expose] public section

namespace CategoryTheory

open Opposite

namespace Functor

/-! ### Local presentations -/

section Presentation

universe v₁ v₂ u₁ u₂

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- A *local presentation* of an object `x` of the fibre of `p` over `U` relative to a sieve `R`
on `U`: an object of the fibre over the source of each member of `R`, together with an
identification of it with the chosen pullback of `x` along that member. -/
structure LocalPresentation (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮} (x : p.Fiber U) (R : Sieve U) where
  /-- The object presenting `x` over the source of a member of the sieve. -/
  obj : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U), R.arrows f → p.Fiber V
  /-- Its identification with the chosen pullback of `x`. -/
  iso : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f), obj f hf ≅ pullbackFiber p x f

namespace LocalPresentation

variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U : 𝒮} {x : p.Fiber U} {R : Sieve U}
  (P : LocalPresentation p x R)

/-- The cartesian morphism to `x` over `f` that a local presentation carries at a member `f` of
the sieve: the identification with the chosen pullback, followed by the chosen cartesian lift. -/
noncomputable def mor ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f) : (P.obj f hf).1 ⟶ x.1 :=
  Fiber.fiberInclusion.map (P.iso f hf).hom ≫ IsPreFibered.pullbackMap x.2 f

/-- An isomorphism of a fibre onto a chosen pullback, followed by the chosen cartesian lift, is
strongly cartesian. -/
private lemma isStronglyCartesian_fiberInclusion_map_comp_pullbackMap {V W : 𝒮} {a : p.Fiber V}
    (x : p.Fiber W) (f : V ⟶ W) (e : a ⟶ pullbackFiber p x f) [IsIso e] :
    p.IsStronglyCartesian f (Fiber.fiberInclusion.map e ≫ IsPreFibered.pullbackMap x.2 f) := by
  have h1 : p.IsHomLift (𝟙 V) (Fiber.fiberInclusion.map e) := e.2
  have h1i : IsIso (Fiber.fiberInclusion.map e) := inferInstance
  have h1' : p.IsStronglyCartesian (𝟙 V) (Fiber.fiberInclusion.map e) :=
    IsStronglyCartesian.of_isIso p (𝟙 V) _
  have h0 : p.IsStronglyCartesian (𝟙 V ≫ f)
    (Fiber.fiberInclusion.map e ≫ IsPreFibered.pullbackMap x.2 f) := inferInstance
  rwa [Category.id_comp] at h0

/-- Two morphisms of a fibre into an iterated chosen pullback agree as soon as their composites
with the two chosen cartesian lifts do. -/
private lemma hom_ext_pullbackFiber_pullbackFiber {T U V : 𝒮} (x' : p.Fiber T) (fb : U ⟶ T)
    (g : V ⟶ U) {z : p.Fiber V} (ψ ψ' : z ⟶ pullbackFiber p (pullbackFiber p x' fb) g)
    (h : Fiber.fiberInclusion.map ψ ≫ IsPreFibered.pullbackMap (pullbackFiber p x' fb).2 g ≫
        IsPreFibered.pullbackMap x'.2 fb =
      Fiber.fiberInclusion.map ψ' ≫ IsPreFibered.pullbackMap (pullbackFiber p x' fb).2 g ≫
        IsPreFibered.pullbackMap x'.2 fb) :
    ψ = ψ' :=
  fiber_hom_ext_of_cartesian (g ≫ fb)
    (IsPreFibered.pullbackMap (pullbackFiber p x' fb).2 g ≫ IsPreFibered.pullbackMap x'.2 fb)
    (isCartesian_pullbackMap_comp_pullbackMap x' fb g (g ≫ fb) rfl) _ _ h

/-- `CategoryTheory.Functor.LocalPresentation.mor` is strongly cartesian over the member of the
sieve it is attached to: it is an isomorphism over an identity followed by a chosen lift. -/
lemma isStronglyCartesian_mor ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f) :
    p.IsStronglyCartesian f (P.mor f hf) := by
  rw [mor]
  exact isStronglyCartesian_fiberInclusion_map_comp_pullbackMap x _ _

/-- The weak form of `CategoryTheory.Functor.LocalPresentation.isStronglyCartesian_mor`. -/
lemma isCartesian_mor ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f) : p.IsCartesian f (P.mor f hf) :=
  have := P.isStronglyCartesian_mor f hf
  inferInstance

/-- The chosen cartesian lift of `γ` at the presenting object over `V`, followed by the cartesian
morphism of the presentation, is strongly cartesian over any morphism the composite `γ ≫ f`
equals. -/
lemma isStronglyCartesian_pullbackMap_comp_mor ⦃V W : 𝒮⦄ {f : V ⟶ U} (hf : R.arrows f)
    (γ : W ⟶ V) {b : W ⟶ U} (hb : γ ≫ f = b) :
    p.IsStronglyCartesian b (IsPreFibered.pullbackMap (P.obj f hf).2 γ ≫ P.mor f hf) := by
  have hc : p.IsCartesian γ (IsPreFibered.pullbackMap (P.obj f hf).2 γ) :=
    IsPreFibered.pullbackMap.IsCartesian _ _
  have hc' : p.IsStronglyCartesian γ (IsPreFibered.pullbackMap (P.obj f hf).2 γ) := inferInstance
  have h2 := P.isStronglyCartesian_mor f hf
  have h0 : p.IsStronglyCartesian (γ ≫ f)
    (IsPreFibered.pullbackMap (P.obj f hf).2 γ ≫ P.mor f hf) := inferInstance
  rwa [hb] at h0

/-- **The comparison of the presenting objects along a refinement.** The chosen pullback along `γ`
of the object presenting `x` at `f` and the object presenting `x` at a member `b` of the sieve
that `γ ≫ f` equals both carry a cartesian morphism to `x` over `b`, hence are canonically
isomorphic in the fibre. -/
noncomputable def isoAlong ⦃V W : 𝒮⦄ {f : V ⟶ U} (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U}
    (hb : γ ≫ f = b) (hb' : R.arrows b) : pullbackFiber p (P.obj f hf) γ ≅ P.obj b hb' :=
  have _h1 := P.isStronglyCartesian_pullbackMap_comp_mor hf γ hb
  fiberIsoOfCartesian b (IsPreFibered.pullbackMap (P.obj f hf).2 γ ≫ P.mor f hf) (P.mor b hb')
    inferInstance (P.isCartesian_mor b hb')

/-- The defining factorization of `CategoryTheory.Functor.LocalPresentation.isoAlong`. -/
@[reassoc (attr := simp)]
lemma isoAlong_hom_fac ⦃V W : 𝒮⦄ {f : V ⟶ U} (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U}
    (hb : γ ≫ f = b) (hb' : R.arrows b) :
    Fiber.fiberInclusion.map (P.isoAlong hf γ hb hb').hom ≫ P.mor b hb' =
      IsPreFibered.pullbackMap (P.obj f hf).2 γ ≫ P.mor f hf :=
  fiberIsoOfCartesian_hom_fac _ _ _ _ _

/-- The inverse form of the defining factorization of
`CategoryTheory.Functor.LocalPresentation.isoAlong`. -/
@[reassoc (attr := simp)]
lemma isoAlong_inv_fac ⦃V W : 𝒮⦄ {f : V ⟶ U} (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U}
    (hb : γ ≫ f = b) (hb' : R.arrows b) :
    Fiber.fiberInclusion.map (P.isoAlong hf γ hb hb').inv ≫
        IsPreFibered.pullbackMap (P.obj f hf).2 γ ≫ P.mor f hf =
      P.mor b hb' :=
  fiberIsoOfCartesian_inv_fac _ _ _ _ _

/-- The identification of a presenting object with the chosen pullback, read backwards and
followed by the cartesian morphism of the presentation, is the chosen cartesian lift. -/
@[reassoc (attr := simp)]
lemma iso_inv_comp_mor ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f) :
    Fiber.fiberInclusion.map (P.iso f hf).inv ≫ P.mor f hf = IsPreFibered.pullbackMap x.2 f := by
  rw [mor, ← Category.assoc, ← Fiber.fiberInclusion.map_comp, Iso.inv_hom_id,
    Fiber.fiberInclusion.map_id, Category.id_comp]

/-- Two morphisms of a fibre into a presenting object agree as soon as their composites with the
cartesian morphism of the presentation do. -/
lemma hom_ext ⦃V : 𝒮⦄ {f : V ⟶ U} (hf : R.arrows f) {z : p.Fiber V} (ψ ψ' : z ⟶ P.obj f hf)
    (h : Fiber.fiberInclusion.map ψ ≫ P.mor f hf = Fiber.fiberInclusion.map ψ' ≫ P.mor f hf) :
    ψ = ψ' :=
  fiber_hom_ext_of_cartesian f (P.mor f hf) (P.isCartesian_mor f hf) _ _ h

/-- **The identification at a refinement, in terms of the comparison of the presenting objects.**
The identification of the presenting object at `b` with the chosen pullback of `x` along `b` is,
read backwards, the contraction of the iterated chosen pullback followed by the base change of
the identification at `f` and the comparison of the presenting objects.

This is the form in which the comparison
`CategoryTheory.Functor.LocalPresentation.isoAlong` enters the gluing of a morphism. -/
lemma iso_inv_eq ⦃V W : 𝒮⦄ {f : V ⟶ U} (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U}
    (hb : γ ≫ f = b) (hb' : R.arrows b) :
    (P.iso b hb').inv = (pullbackFiberCompIso' x f γ b hb).inv ≫
      pullbackFiberHom (P.iso f hf).inv γ ≫ (P.isoAlong hf γ hb hb').hom := by
  refine P.hom_ext hb' _ _ ?_
  rw [Fiber.fiberInclusion.map_comp, Fiber.fiberInclusion.map_comp, Category.assoc,
    Category.assoc, isoAlong_hom_fac, pullbackFiberHom_fac_assoc, iso_inv_comp_mor,
    iso_inv_comp_mor, pullbackFiberCompIso'_inv_fac]

/-- The tautological local presentation of an object of a fibre by its own chosen pullbacks. -/
@[simps]
noncomputable def self (x : p.Fiber U) (R : Sieve U) : LocalPresentation p x R where
  obj := fun ⦃_V⦄ f _ => pullbackFiber p x f
  iso := fun ⦃_V⦄ _ _ => Iso.refl _

/-- The structure morphisms of the tautological local presentation are the chosen pullback
morphisms. -/
@[simp]
lemma self_mor (x : p.Fiber U) (R : Sieve U) ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R.arrows f) :
    (self x R).mor f hf = IsPreFibered.pullbackMap x.2 f := by
  rw [mor]
  simp only [self_iso, Iso.refl_hom]
  exact Category.id_comp _

/-! #### The transition morphism induced by a morphism of the total category -/

variable {T : 𝒮} {x' : p.Fiber T} {R' : Sieve T} (Q : LocalPresentation p x' R')

/-- **The transition morphism of a morphism of `𝒳` between two locally presented objects.** Let
`m : x ⟶ x'` be a morphism of `𝒳` over `fb : U ⟶ T`, let `g` be a member of the sieve presenting
`x` and let `h` be a member of the sieve presenting `x'` that `g ≫ fb` equals. Then there is a
unique morphism of the fibre over the common source from the object presenting `x` at `g` to the
object presenting `x'` at `h` compatible with `m` and the two cartesian morphisms. -/
noncomputable def transition {fb : U ⟶ T} (m : x.1 ⟶ x'.1) (hm : p.IsHomLift fb m)
    ⦃V : 𝒮⦄ {g : V ⟶ U} (hg : R.arrows g) {h : V ⟶ T} (hh : R'.arrows h) (hgh : g ≫ fb = h) :
    P.obj g hg ⟶ Q.obj h hh :=
  have := hm
  have hcart := Q.isCartesian_mor h hh
  have hg' := P.isCartesian_mor g hg
  have hlift : p.IsHomLift h (P.mor g hg ≫ m) := by
    have h0 : p.IsHomLift (g ≫ fb) (P.mor g hg ≫ m) := inferInstance
    rwa [hgh] at h0
  ⟨IsCartesian.map p h (Q.mor h hh) (P.mor g hg ≫ m), inferInstance⟩

/-- The defining factorization of `CategoryTheory.Functor.LocalPresentation.transition`. -/
@[reassoc (attr := simp)]
lemma transition_fac {fb : U ⟶ T} (m : x.1 ⟶ x'.1) (hm : p.IsHomLift fb m)
    ⦃V : 𝒮⦄ {g : V ⟶ U} (hg : R.arrows g) {h : V ⟶ T} (hh : R'.arrows h) (hgh : g ≫ fb = h) :
    Fiber.fiberInclusion.map (P.transition Q m hm hg hh hgh) ≫ Q.mor h hh = P.mor g hg ≫ m := by
  have := hm
  have hcart := Q.isCartesian_mor h hh
  have hg' := P.isCartesian_mor g hg
  have hlift : p.IsHomLift h (P.mor g hg ≫ m) := by
    have h0 : p.IsHomLift (g ≫ fb) (P.mor g hg ≫ m) := inferInstance
    rwa [hgh] at h0
  exact IsCartesian.fac p h (Q.mor h hh) (P.mor g hg ≫ m)

/-- The transition morphism does not depend on the morphism of the base that `m` is read as lying
over. -/
lemma transition_base_congr {fb fb' : U ⟶ T} (m : x.1 ⟶ x'.1) (hm : p.IsHomLift fb m)
    (hm' : p.IsHomLift fb' m) ⦃V : 𝒮⦄ {g : V ⟶ U} (hg : R.arrows g) {h : V ⟶ T}
    (hh : R'.arrows h) (hgh : g ≫ fb = h) (hgh' : g ≫ fb' = h) :
    P.transition Q m hm hg hh hgh = P.transition Q m hm' hg hh hgh' :=
  Q.hom_ext hh _ _ (by rw [transition_fac, transition_fac])

/-- `CategoryTheory.Functor.LocalPresentation.transition` is the only morphism of the fibre with
its defining factorization. -/
lemma transition_uniq {fb : U ⟶ T} (m : x.1 ⟶ x'.1) (hm : p.IsHomLift fb m)
    ⦃V : 𝒮⦄ {g : V ⟶ U} (hg : R.arrows g) {h : V ⟶ T} (hh : R'.arrows h) (hgh : g ≫ fb = h)
    (w : P.obj g hg ⟶ Q.obj h hh)
    (hw : Fiber.fiberInclusion.map w ≫ Q.mor h hh = P.mor g hg ≫ m) :
    w = P.transition Q m hm hg hh hgh :=
  Q.hom_ext hh _ _ (by rw [hw, transition_fac])

/-- The transition morphism of an identity, between one presentation and itself, is the
identity. -/
@[simp]
lemma transition_id ⦃V : 𝒮⦄ {g : V ⟶ U} (hg : R.arrows g) :
    P.transition P (𝟙 x.1) (IsHomLift.id x.2) hg hg (Category.comp_id g) = 𝟙 _ :=
  (P.transition_uniq P (𝟙 x.1) (IsHomLift.id x.2) hg hg (Category.comp_id g) (𝟙 _)
    (by rw [Fiber.fiberInclusion.map_id, Category.id_comp, Category.comp_id])).symm

/-- The transition morphisms of a composite compose. -/
lemma transition_comp {T' : 𝒮} {x'' : p.Fiber T'} {R'' : Sieve T'}
    (S : LocalPresentation p x'' R'') {fb : U ⟶ T} (m : x.1 ⟶ x'.1) (hm : p.IsHomLift fb m)
    {fb' : T ⟶ T'} (m' : x'.1 ⟶ x''.1) (hm' : p.IsHomLift fb' m')
    ⦃V : 𝒮⦄ {g : V ⟶ U} (hg : R.arrows g) {h : V ⟶ T} (hh : R'.arrows h) (hgh : g ≫ fb = h)
    {k : V ⟶ T'} (hk : R''.arrows k) (hhk : h ≫ fb' = k) :
    P.transition Q m hm hg hh hgh ≫ Q.transition S m' hm' hh hk hhk =
      P.transition (fb := fb ≫ fb') S (m ≫ m') (have := hm; have := hm'; inferInstance) hg hk
        (by rw [← hhk, ← hgh, Category.assoc]) := by
  refine P.transition_uniq (fb := fb ≫ fb') S (m ≫ m')
    (have := hm; have := hm'; inferInstance) hg hk
    (by rw [← hhk, ← hgh, Category.assoc]) _ ?_
  rw [Fiber.fiberInclusion.map_comp, Category.assoc, transition_fac, ← Category.assoc,
    transition_fac, Category.assoc]

/-- The chosen cartesian morphism of the source presentation, followed by a morphism `m` of `𝒳`
over `fb`, is strongly cartesian over any morphism that `g ≫ fb` equals. -/
lemma isStronglyCartesian_mor_comp {fb : U ⟶ T} (m : x.1 ⟶ x'.1)
    (hm : p.IsStronglyCartesian fb m) ⦃V : 𝒮⦄ {g : V ⟶ U} (hg : R.arrows g) {h : V ⟶ T}
    (hgh : g ≫ fb = h) : p.IsStronglyCartesian h (P.mor g hg ≫ m) := by
  have h1 := P.isStronglyCartesian_mor g hg
  have := hm
  have h0 : p.IsStronglyCartesian (g ≫ fb) (P.mor g hg ≫ m) := inferInstance
  rwa [hgh] at h0

/-- **The transition morphism of a strongly cartesian morphism is an isomorphism.** Both the
cartesian morphism of the source presentation followed by `m` and the cartesian morphism of the
target presentation are cartesian over the same morphism of the base, so the transition morphism
is the canonical comparison of the two. -/
lemma isIso_transition {fb : U ⟶ T} (m : x.1 ⟶ x'.1) (hm : p.IsStronglyCartesian fb m)
    ⦃V : 𝒮⦄ {g : V ⟶ U} (hg : R.arrows g) {h : V ⟶ T} (hh : R'.arrows h) (hgh : g ≫ fb = h) :
    IsIso (P.transition Q m (have := hm; inferInstance) hg hh hgh) := by
  have hc := P.isStronglyCartesian_mor_comp m hm hg hgh
  have hc' : p.IsCartesian h (P.mor g hg ≫ m) := inferInstance
  have heq : P.transition Q m (have := hm; inferInstance) hg hh hgh =
      (fiberIsoOfCartesian h (P.mor g hg ≫ m) (Q.mor h hh) hc'
        (Q.isCartesian_mor h hh)).hom :=
    (P.transition_uniq Q m (have := hm; inferInstance) hg hh hgh _
      (fiberIsoOfCartesian_hom_fac _ _ _ _ _)).symm
  rw [heq]
  infer_instance

/-- **The transition morphisms against a refinement.** Comparing the presenting objects along `γ`
and then taking the transition morphism at the refined pair of members of the two sieves is base
changing the transition morphism at the original pair and then comparing the presenting objects
of the target. -/
lemma isoAlong_comp_transition {fb : U ⟶ T} (m : x.1 ⟶ x'.1) (hm : p.IsHomLift fb m)
    ⦃V W : 𝒮⦄ {g : V ⟶ U} (hg : R.arrows g) {h : V ⟶ T} (hh : R'.arrows h) (hgh : g ≫ fb = h)
    (γ : W ⟶ V) {g' : W ⟶ U} (hgg : γ ≫ g = g') (hg' : R.arrows g') {h' : W ⟶ T}
    (hhh : γ ≫ h = h') (hh' : R'.arrows h') :
    (P.isoAlong hg γ hgg hg').hom ≫
        P.transition Q m hm hg' hh' (by rw [← hgg, ← hhh, ← hgh, Category.assoc]) =
      pullbackFiberHom (P.transition Q m hm hg hh hgh) γ ≫ (Q.isoAlong hh γ hhh hh').hom := by
  refine Q.hom_ext hh' _ _ ?_
  rw [Fiber.fiberInclusion.map_comp, Fiber.fiberInclusion.map_comp, Category.assoc,
    Category.assoc, transition_fac, isoAlong_hom_fac, isoAlong_hom_fac_assoc,
    pullbackFiberHom_fac_assoc, transition_fac]

/-! #### Gluing a morphism from a family of transition morphisms -/

section Glue

variable {J : GrothendieckTopology 𝒮}

/-- **A morphism of `𝒳` glued from local transition morphisms.** Let `x` and `x'` be objects of
the fibres over `U` and `T`, locally presented relative to sieves `R` and `R'`, and let
`fb : U ⟶ T`. A family of morphisms `τ g` from the object presenting `x` at `g` to the object
presenting `x'` at `g ≫ fb`, given over the members `g` of a covering sieve of `U` and compatible
with the comparisons `CategoryTheory.Functor.LocalPresentation.isoAlong` along a refinement, comes
from a morphism `x ⟶ x'` of `𝒳` over `fb`; and if every member of the family is invertible the
glued morphism is strongly cartesian.

The family is turned into a family of morphisms of the chosen pullbacks of `x` and of `fb^* x'`
and glued by `CategoryTheory.Functor.exists_fiberHom_of_locally`; the compatibility hypothesis of
that theorem is the hypothesis here, read through
`CategoryTheory.Functor.LocalPresentation.iso_inv_eq`. -/
theorem exists_hom_of_transition (P : LocalPresentation p x R) {T : 𝒮} {x' : p.Fiber T}
    {R' : Sieve T} (Q : LocalPresentation p x' R')
    (hmor : ∀ (a b : p.Fiber U), IsMorSheaf p J U a b)
    (fb : U ⟶ T) {R₀ : Sieve U} (hR₀ : R₀ ∈ J U)
    (hsub : ∀ ⦃V : 𝒮⦄ ⦃g : V ⟶ U⦄, R₀.arrows g → R.arrows g)
    (hsub' : ∀ ⦃V : 𝒮⦄ ⦃g : V ⟶ U⦄, R₀.arrows g → R'.arrows (g ≫ fb))
    (τ : ∀ ⦃V : 𝒮⦄ (g : V ⟶ U) (hg : R₀.arrows g),
      P.obj g (hsub hg) ⟶ Q.obj (g ≫ fb) (hsub' hg))
    (hτ : ∀ ⦃V W : 𝒮⦄ (g : V ⟶ U) (hg : R₀.arrows g) (γ : W ⟶ V) (b : W ⟶ U) (hb : γ ≫ g = b)
      (hb' : R₀.arrows b),
      (P.isoAlong (hsub hg) γ hb (hsub hb')).hom ≫ τ b hb' =
        pullbackFiberHom (τ g hg) γ ≫
          (Q.isoAlong (hsub' hg) γ (by rw [← hb, Category.assoc]) (hsub' hb')).hom) :
    ∃ m : x.1 ⟶ x'.1, p.IsHomLift fb m ∧
      (∀ ⦃V : 𝒮⦄ (g : V ⟶ U) (hg : R₀.arrows g),
        P.mor g (hsub hg) ≫ m =
          Fiber.fiberInclusion.map (τ g hg) ≫ Q.mor (g ≫ fb) (hsub' hg)) ∧
      ((∀ ⦃V : 𝒮⦄ (g : V ⟶ U) (hg : R₀.arrows g), IsIso (τ g hg)) →
        p.IsStronglyCartesian fb m) := by
  -- The local family of morphisms between the chosen pullbacks of `x` and of `fb^* x'`.
  set Θ : ∀ ⦃V : 𝒮⦄ (g : V ⟶ U), R₀.arrows g →
      (pullbackFiber p x g ⟶ pullbackFiber p (pullbackFiber p x' fb) g) :=
    fun ⦃_V⦄ g hg => (P.iso g (hsub hg)).inv ≫ τ g hg ≫ (Q.iso (g ≫ fb) (hsub' hg)).hom ≫
      (pullbackFiberCompIso' x' fb g (g ≫ fb) rfl).inv with hΘdef
  -- Its composite with the composite of the two chosen cartesian lifts.
  have hfac : ∀ ⦃V : 𝒮⦄ (g : V ⟶ U) (hg : R₀.arrows g),
      Fiber.fiberInclusion.map (Θ g hg) ≫
          IsPreFibered.pullbackMap (pullbackFiber p x' fb).2 g ≫
          IsPreFibered.pullbackMap x'.2 fb =
        Fiber.fiberInclusion.map (P.iso g (hsub hg)).inv ≫
          Fiber.fiberInclusion.map (τ g hg) ≫ Q.mor (g ≫ fb) (hsub' hg) := by
    intro V g hg
    rw [hΘdef, mor]
    simp
  -- Compatibility with base change, which is the hypothesis read through `iso_inv_eq`.
  have hcompat : ∀ ⦃V W : 𝒮⦄ (g : V ⟶ U) (hg : R₀.arrows g) (γ : W ⟶ V) (b : W ⟶ U)
      (hb : γ ≫ g = b) (hb' : R₀.arrows b),
      Θ b hb' = (pullbackFiberCompIso' x g γ b hb).inv ≫
        pullbackFiberHom (Θ g hg) γ ≫
        (pullbackFiberCompIso' (pullbackFiber p x' fb) g γ b hb).hom := by
    intro V W g hg γ b hb hb'
    -- The fibre-level identity behind the compatibility.
    have key : (P.iso b (hsub hb')).inv ≫ τ b hb' =
        (pullbackFiberCompIso' x g γ b hb).inv ≫
          pullbackFiberHom ((P.iso g (hsub hg)).inv ≫ τ g hg) γ ≫
          (Q.isoAlong (hsub' hg) γ (by rw [← hb, Category.assoc]) (hsub' hb')).hom := by
      rw [P.iso_inv_eq (hsub hg) γ hb (hsub hb'), Category.assoc, Category.assoc,
        hτ g hg γ b hb hb', pullbackFiberHom_comp]
      simp [Category.assoc]
    refine hom_ext_pullbackFiber_pullbackFiber x' fb b _ _ ?_
    have key' := congrArg Fiber.fiberInclusion.map key
    simp only [Fiber.fiberInclusion.map_comp] at key'
    rw [hfac b hb', reassoc_of% key']
    simp only [Fiber.fiberInclusion.map_comp, Category.assoc, isoAlong_hom_fac,
      pullbackFiberHom_fac_assoc, pullbackFiberCompIso'_hom_fac_assoc]
    rw [hfac g hg]
  obtain ⟨v, hv⟩ := exists_fiberHom_of_locally p (hmor x (pullbackFiber p x' fb)) hR₀ Θ
    (fun ⦃_V _W⦄ g hg γ b hb hb' => hcompat g hg γ b hb hb')
  have h1 : p.IsHomLift (𝟙 U) (Fiber.fiberInclusion.map v) := v.2
  refine ⟨Fiber.fiberInclusion.map v ≫ IsPreFibered.pullbackMap x'.2 fb, ?_, ?_, ?_⟩
  · have h0 : p.IsHomLift (𝟙 U ≫ fb)
      (Fiber.fiberInclusion.map v ≫ IsPreFibered.pullbackMap x'.2 fb) := inferInstance
    rwa [Category.id_comp] at h0
  · intro V g hg
    rw [mor, Category.assoc, ← Category.assoc (IsPreFibered.pullbackMap x.2 g),
      ← pullbackFiberHom_fac v g, Category.assoc, hv g hg, hfac g hg,
      ← Category.assoc, ← Fiber.fiberInclusion.map_comp, Iso.hom_inv_id,
      Fiber.fiberInclusion.map_id]
    exact Category.id_comp _
  · -- If every transition morphism is invertible, so is every member of the glued family, hence
    -- the glued morphism of the fibre, and the result is a chosen cartesian lift up to that
    -- isomorphism.
    intro hiso
    have hΘiso : ∀ ⦃V : 𝒮⦄ (g : V ⟶ U) (hg : R₀.arrows g), IsIso (Θ g hg) := by
      intro V g hg
      have := hiso g hg
      rw [hΘdef]
      infer_instance
    obtain ⟨e, he⟩ := exists_fiberIso_of_locally p hmor hR₀
      (fun ⦃_V⦄ g hg => @asIso _ _ _ _ (Θ g hg) (hΘiso g hg))
      (fun ⦃_V _W⦄ g hg γ b hb hb' => hcompat g hg γ b hb hb')
    have hev : e.hom = v := by
      refine eq_of_pullbackFiberHom_locally_eq p (hmor x (pullbackFiber p x' fb)) hR₀ ?_
      intro V g hg
      rw [he g hg, hv g hg, asIso_hom]
    have hvi : IsIso v := hev ▸ inferInstance
    exact isStronglyCartesian_fiberInclusion_map_comp_pullbackMap x' fb v

/-- **A morphism out of a locally presented object is determined by its restrictions.** Two
morphisms `x ⟶ x'` of `𝒳` over one and the same morphism of the base that agree after composition
with the cartesian morphisms of a local presentation, over the members of a covering sieve, are
equal. -/
theorem hom_ext_of_locally (P : LocalPresentation p x R) {T : 𝒮} {x' : p.Fiber T}
    (hmor : ∀ (a b : p.Fiber U), IsMorSheaf p J U a b)
    {fb : U ⟶ T} {R₀ : Sieve U} (hR₀ : R₀ ∈ J U)
    (hsub : ∀ ⦃V : 𝒮⦄ ⦃g : V ⟶ U⦄, R₀.arrows g → R.arrows g)
    {m m' : x.1 ⟶ x'.1} (hm : p.IsHomLift fb m) (hm' : p.IsHomLift fb m')
    (h : ∀ ⦃V : 𝒮⦄ (g : V ⟶ U) (hg : R₀.arrows g),
      P.mor g (hsub hg) ≫ m = P.mor g (hsub hg) ≫ m') :
    m = m' := by
  have hcart : p.IsCartesian fb (IsPreFibered.pullbackMap x'.2 fb) :=
    IsPreFibered.pullbackMap.IsCartesian _ _
  have := hm
  have := hm'
  -- The two morphisms, read as morphisms of the fibre into the chosen pullback of `x'`.
  set v : x ⟶ pullbackFiber p x' fb :=
    ⟨IsCartesian.map p fb (IsPreFibered.pullbackMap x'.2 fb) m, inferInstance⟩ with hvdef
  set v' : x ⟶ pullbackFiber p x' fb :=
    ⟨IsCartesian.map p fb (IsPreFibered.pullbackMap x'.2 fb) m', inferInstance⟩ with hv'def
  have hvfac : Fiber.fiberInclusion.map v ≫ IsPreFibered.pullbackMap x'.2 fb = m :=
    IsCartesian.fac p fb (IsPreFibered.pullbackMap x'.2 fb) m
  have hv'fac : Fiber.fiberInclusion.map v' ≫ IsPreFibered.pullbackMap x'.2 fb = m' :=
    IsCartesian.fac p fb (IsPreFibered.pullbackMap x'.2 fb) m'
  have hvv' : v = v' := by
    refine eq_of_pullbackFiberHom_locally_eq p (hmor x (pullbackFiber p x' fb)) hR₀ ?_
    intro V g hg
    refine hom_ext_pullbackFiber_pullbackFiber x' fb g _ _ ?_
    rw [← Category.assoc, ← Category.assoc, pullbackFiberHom_fac, pullbackFiberHom_fac,
      Category.assoc, Category.assoc, hvfac, hv'fac,
      ← P.iso_inv_comp_mor g (hsub hg), Category.assoc, Category.assoc, h g hg]
  rw [← hvfac, ← hv'fac, hvv']

end Glue

end LocalPresentation

end Presentation

/-! ### The two local presentations attached to a local presentation along a stackification

A family of local objects `s f` of `𝒮` presenting an object `x'` of a fibre of `𝒮'` gives a local
presentation of `x'` by the images `G (s f)`, and — once the descent datum of the images
`F (s f)` is known to descend to an object `y` of `𝒳` — a local presentation of `y` by those
images. The two are intertwined by the transfer. -/

section Bridge

universe vb v v₄ v' u₁ u₂ u₃ u₄

-- The chosen pullbacks, the fibre inclusion and the induced functor on fibres are semireducible,
-- so the endpoints of the composites below agree only once they unfold.
set_option backward.isDefEq.respectTransparency false

variable {𝒞 : Type u₁} [Category.{vb} 𝒞] {𝒮 : Type u₂} [Category.{v} 𝒮] {𝒮' : Type u₃}
  [Category.{v} 𝒮'] {𝒳 : Type u₄} [Category.{v₄} 𝒳] {J : GrothendieckTopology 𝒞}
  {p : 𝒮 ⥤ 𝒞} {p' : 𝒮' ⥤ 𝒞} {q : 𝒳 ⥤ 𝒞} {G : 𝒮 ⥤ 𝒮'} {F : 𝒮 ⥤ 𝒳}
  [p.IsFibered] [p'.IsFibered] [q.IsFibered]

/-- Contracting the chosen pullback of an image along an identity is the image of the
contraction. -/
lemma IsFibredOneMorphism.mapPullbackFiberIso_id_inv_comp {𝒴 : Type u₃} [Category.{v'} 𝒴]
    {r : 𝒴 ⥤ 𝒞} [r.IsFibered] {K : 𝒮 ⥤ 𝒴} (hK : p.IsFibredOneMorphism r K) {V : 𝒞}
    (a : p.Fiber V) :
    (hK.mapPullbackFiberIso a (𝟙 V)).inv ≫
        (pullbackFiberIdIso ((fiberFunctorOfCompEq hK.comp_eq V).obj a)).hom =
      (fiberFunctorOfCompEq hK.comp_eq V).map (pullbackFiberIdIso a).hom := by
  refine Fiber.hom_ext ?_
  rw [Fiber.fiberInclusion.map_comp, pullbackFiberIdIso_hom_fac,
    IsFibredOneMorphism.mapPullbackFiberIso_inv_fac,
    fiberInclusion_map_fiberFunctorOfCompEq_map, pullbackFiberIdIso_hom_fac]

namespace Stackification

variable (hG : p.IsFibredOneMorphism p' G) (hF : p.IsFibredOneMorphism q F)
  (hmor : ∀ (U : 𝒞) (x y : p.Fiber U),
    Presheaf.IsLocallyInjective (J.over U) (hG.morPresheafMap x y) ∧
      Presheaf.IsLocallySurjective (J.over U) (hG.morPresheafMap x y))
  (hqmor : ∀ (U : 𝒞) (x y : q.Fiber U), IsMorSheaf q J U x y)

/-- The transfer of an isomorphism of fibres is an isomorphism: the transfer of its inverse is an
inverse, by functoriality of the transfer. -/
lemma isIso_transfer {U : 𝒞} {a b : p.Fiber U}
    (θ : (fiberFunctorOfCompEq hG.comp_eq U).obj a ⟶ (fiberFunctorOfCompEq hG.comp_eq U).obj b)
    [IsIso θ] : IsIso (transfer hG hF hmor hqmor θ) :=
  ⟨⟨transfer hG hF hmor hqmor (_root_.CategoryTheory.inv θ),
    by rw [← transfer_comp, IsIso.hom_inv_id, transfer_id],
    by rw [← transfer_comp, IsIso.inv_hom_id, transfer_id]⟩⟩

section Presentations

variable {U : 𝒞} {x' : p'.Fiber U} {R : Sieve U}
  (s : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R.arrows f → p.Fiber V)
  (φ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
    (fiberFunctorOfCompEq hG.comp_eq V).obj (s f hf) ≅ pullbackFiber p' x' f)

/-- The local presentation of `x'` in `𝒮'` by the images under `G` of the local objects. -/
@[simps]
def presG : LocalPresentation p' x' R where
  obj := fun ⦃V⦄ f hf => (fiberFunctorOfCompEq hG.comp_eq V).obj (s f hf)
  iso := φ

/-- **The comparison of the presenting objects of `x'`, in the form the transfer reads it.**
Conjugated by the comparison `IsFibredOneMorphism.mapPullbackFiberIso` of `G`, the comparison
`CategoryTheory.Functor.LocalPresentation.isoAlong` of the presentation of `x'` by the images of
the local objects is the comparison
`CategoryTheory.Functor.Stackification.localIso` of the local presentations at `(f, γ)` and
`(b, 𝟙)`, contracted at the chosen pullback along the identity.

Both composites with the cartesian morphism of the presentation at `b` are the image under `G` of
the chosen cartesian lift of `γ`, followed by the cartesian morphism at `f`. -/
lemma mapPullbackFiberIso_inv_comp_isoAlong ⦃V W : 𝒞⦄ {f : V ⟶ U} (hf : R.arrows f) (γ : W ⟶ V)
    {b : W ⟶ U} (hb : γ ≫ f = b) (hb' : R.arrows b) :
    (hG.mapPullbackFiberIso (s f hf) γ).inv ≫ ((presG hG s φ).isoAlong hf γ hb hb').hom =
      (localIso hG s φ hf hb' γ (𝟙 W) (by rw [Category.id_comp]; exact hb)).hom ≫
        (fiberFunctorOfCompEq hG.comp_eq W).map (pullbackFiberIdIso (s b hb')).hom := by
  refine (presG hG s φ).hom_ext hb' _ _ ?_
  rw [Fiber.fiberInclusion.map_comp, Category.assoc, LocalPresentation.isoAlong_hom_fac]
  simp [LocalPresentation.mor, presG_iso, localIso_hom, localIsoCore_hom,
    Fiber.fiberInclusion.map_comp, fiberInclusion_map_fiberFunctorOfCompEq_map,
    pullbackFiberIdIso_hom_fac, IsFibredOneMorphism.mapPullbackFiberIso_inv_fac_assoc,
    pullbackFiberHom_fac_assoc, pullbackFiberComparison_hom_fac]

variable {y : q.Fiber U}
  {ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
    ((descentDatum hG hF hmor hqmor s φ).obj f hf).1 ⟶ y.1}

/-- The local presentation of the descended object `y` in `𝒳` by the images under `F` of the
local objects. Its cartesian morphisms are the family `ζ` along which the descent datum
descends. -/
@[simps]
noncomputable def presF (hζ : (descentDatum hG hF hmor hqmor s φ).Descends q y ζ) :
    LocalPresentation q y R where
  obj := fun ⦃V⦄ f hf => (fiberFunctorOfCompEq hF.comp_eq V).obj (s f hf)
  iso := fun ⦃_V⦄ f hf => (SieveDescentDatum.descendsIso hζ f hf).symm

/-- The cartesian morphisms of the local presentation of the descended object are the family
along which the descent datum descends. -/
@[simp]
lemma presF_mor (hζ : (descentDatum hG hF hmor hqmor s φ).Descends q y ζ) ⦃V : 𝒞⦄ (f : V ⟶ U)
    (hf : R.arrows f) : (presF hG hF hmor hqmor s φ hζ).mor f hf = ζ f hf :=
  SieveDescentDatum.descendsIso_inv_fac hζ f hf

/-- The comparison of the presenting objects of `y` along a refinement is the gluing isomorphism
of the descent datum. -/
lemma presF_isoAlong (hζ : (descentDatum hG hF hmor hqmor s φ).Descends q y ζ) ⦃V W : 𝒞⦄
    {f : V ⟶ U} (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U} (hb : γ ≫ f = b) (hb' : R.arrows b) :
    (presF hG hF hmor hqmor s φ hζ).isoAlong hf γ hb hb' =
      (descentDatum hG hF hmor hqmor s φ).isoAlong hf γ hb hb' := by
  refine Iso.ext ((presF hG hF hmor hqmor s φ hζ).hom_ext hb' _ _ ?_)
  rw [LocalPresentation.isoAlong_hom_fac, presF_mor, presF_mor,
    SieveDescentDatum.isoAlong_comp hζ hf γ hb hb']

/-- **The comparison of the presenting objects of `y` is the transfer of the comparison of the
presenting objects of `x'`.** This is the bridge between the two local presentations: conjugated
by the comparisons `IsFibredOneMorphism.mapPullbackFiberIso` of `F` and of `G`, the two
comparisons `CategoryTheory.Functor.LocalPresentation.isoAlong` correspond under the transfer. -/
lemma presF_isoAlong_hom (hζ : (descentDatum hG hF hmor hqmor s φ).Descends q y ζ) ⦃V W : 𝒞⦄
    {f : V ⟶ U} (hf : R.arrows f) (γ : W ⟶ V) {b : W ⟶ U} (hb : γ ≫ f = b) (hb' : R.arrows b) :
    ((presF hG hF hmor hqmor s φ hζ).isoAlong hf γ hb hb').hom =
      (hF.mapPullbackFiberIso (s f hf) γ).hom ≫
        transfer hG hF hmor hqmor ((hG.mapPullbackFiberIso (s f hf) γ).inv ≫
          ((presG hG s φ).isoAlong hf γ hb hb').hom) := by
  rw [mapPullbackFiberIso_inv_comp_isoAlong hG s φ hf γ hb hb', transfer_comp,
    transfer_map hG hF hmor hqmor (pullbackFiberIdIso (s b hb')).hom,
    ← hF.mapPullbackFiberIso_id_inv_comp (s b hb'),
    presF_isoAlong hG hF hmor hqmor s φ hζ hf γ hb hb', SieveDescentDatum.isoAlong,
    Iso.trans_hom, descentDatum_iso_hom]
  simp only [Category.assoc]
  rfl

/-- **A morphism out of a descended object is determined by its restrictions.** Two morphisms out
of the object a descent datum of local presentations descends to, lying over one and the same
morphism of the base and agreeing after composition with the descending family, are equal. -/
theorem hom_ext_of_descends (hζ : (descentDatum hG hF hmor hqmor s φ).Descends q y ζ)
    {R₀ : Sieve U} (hR₀ : R₀ ∈ J U)
    (hsub : ∀ ⦃V : 𝒞⦄ ⦃g : V ⟶ U⦄, R₀.arrows g → R.arrows g)
    {T : 𝒞} {z : q.Fiber T} {fb : U ⟶ T} {n n' : y.1 ⟶ z.1}
    (hn : q.IsHomLift fb n) (hn' : q.IsHomLift fb n')
    (h : ∀ ⦃V : 𝒞⦄ (g : V ⟶ U) (hg : R₀.arrows g),
      ζ g (hsub hg) ≫ n = ζ g (hsub hg) ≫ n') : n = n' := by
  refine LocalPresentation.hom_ext_of_locally (presF hG hF hmor hqmor s φ hζ) (hqmor U) hR₀
    hsub hn hn' ?_
  intro V g hg
  simp only [presF_mor]
  exact h g hg

end Presentations

/-! #### The transferred transition morphisms -/

section Transition

variable {U T : 𝒞} {x' : p'.Fiber U} {x'' : p'.Fiber T} {R : Sieve U} {R' : Sieve T}
  (s : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), R.arrows f → p.Fiber V)
  (φ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
    (fiberFunctorOfCompEq hG.comp_eq V).obj (s f hf) ≅ pullbackFiber p' x' f)
  (s' : ∀ ⦃V : 𝒞⦄ (f : V ⟶ T), R'.arrows f → p.Fiber V)
  (φ' : ∀ ⦃V : 𝒞⦄ (f : V ⟶ T) (hf : R'.arrows f),
    (fiberFunctorOfCompEq hG.comp_eq V).obj (s' f hf) ≅ pullbackFiber p' x'' f)
  {y : q.Fiber U} {y' : q.Fiber T}
  {ζ : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : R.arrows f),
    ((descentDatum hG hF hmor hqmor s φ).obj f hf).1 ⟶ y.1}
  {ζ' : ∀ ⦃V : 𝒞⦄ (f : V ⟶ T) (hf : R'.arrows f),
    ((descentDatum hG hF hmor hqmor s' φ').obj f hf).1 ⟶ y'.1}

/-- **The transferred transition morphisms are compatible with a refinement.** This is the
hypothesis of `CategoryTheory.Functor.LocalPresentation.exists_hom_of_transition` for the family
of transfers of the transition morphisms of the presentations in `𝒮'`: it is the corresponding
statement there, `CategoryTheory.Functor.LocalPresentation.isoAlong_comp_transition`, transferred
through `CategoryTheory.Functor.Stackification.presF_isoAlong_hom` and the compatibility of the
transfer with base change. -/
lemma isoAlong_comp_transfer_transition
    (hζ : (descentDatum hG hF hmor hqmor s φ).Descends q y ζ)
    (hζ' : (descentDatum hG hF hmor hqmor s' φ').Descends q y' ζ')
    {fb : U ⟶ T} (m : x'.1 ⟶ x''.1) (hm : p'.IsHomLift fb m)
    ⦃V W : 𝒞⦄ {g : V ⟶ U} (hg : R.arrows g) {h : V ⟶ T} (hh : R'.arrows h) (hgh : g ≫ fb = h)
    (γ : W ⟶ V) {g₁ : W ⟶ U} (hgg : γ ≫ g = g₁) (hg₁ : R.arrows g₁)
    {h₁ : W ⟶ T} (hhh : γ ≫ h = h₁) (hh₁ : R'.arrows h₁) :
    ((presF hG hF hmor hqmor s φ hζ).isoAlong hg γ hgg hg₁).hom ≫
        transfer hG hF hmor hqmor ((presG hG s φ).transition (presG hG s' φ') m hm hg₁ hh₁
          (by rw [← hgg, ← hhh, ← hgh, Category.assoc])) =
      pullbackFiberHom (transfer hG hF hmor hqmor
          ((presG hG s φ).transition (presG hG s' φ') m hm hg hh hgh)) γ ≫
        ((presF hG hF hmor hqmor s' φ' hζ').isoAlong hh γ hhh hh₁).hom := by
  have hGid := LocalPresentation.isoAlong_comp_transition (presG hG s φ) (presG hG s' φ') m hm
    hg hh hgh γ hgg hg₁ hhh hh₁
  have key : ((hG.mapPullbackFiberIso (s g hg) γ).inv ≫
        ((presG hG s φ).isoAlong hg γ hgg hg₁).hom) ≫
        (presG hG s φ).transition (presG hG s' φ') m hm hg₁ hh₁
          (by rw [← hgg, ← hhh, ← hgh, Category.assoc]) =
      ((hG.mapPullbackFiberIso (s g hg) γ).inv ≫
        pullbackFiberHom ((presG hG s φ).transition (presG hG s' φ') m hm hg hh hgh) γ ≫
        (hG.mapPullbackFiberIso (s' h hh) γ).hom) ≫
        ((hG.mapPullbackFiberIso (s' h hh) γ).inv ≫
          ((presG hG s' φ').isoAlong hh γ hhh hh₁).hom) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg (fun z => (hG.mapPullbackFiberIso (s g hg) γ).inv ≫ z) hGid
  rw [presF_isoAlong_hom hG hF hmor hqmor s φ hζ hg γ hgg hg₁,
    presF_isoAlong_hom hG hF hmor hqmor s' φ' hζ' hh γ hhh hh₁,
    pullbackFiberHom_transfer]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← transfer_comp, ← transfer_comp, key]

/-- **The morphism of `𝒳` induced by a morphism of `𝒮'`.** Let `x'` and `x''` be objects of the
fibres of `𝒮'` over `U` and `T`, presented along covering sieves by local objects of `𝒮` whose
images under `F` descend to `y` and `y'`, and let `m : x' ⟶ x''` be a morphism of `𝒮'` over
`fb : U ⟶ T`. Then there is a morphism `y ⟶ y'` of `𝒳` over `fb` whose restriction to a member
`g` of the first sieve with `g ≫ fb` in the second is the transfer along `G` of the transition
morphism of the two local presentations; and it is strongly cartesian as soon as every transition
morphism is invertible.

This is the action on morphisms of the extension of `F` along `G` asserted by Stacks 0435. Its
existence is `CategoryTheory.Functor.LocalPresentation.exists_hom_of_transition` applied to the
family of transfers, whose compatibility with refinements is
`CategoryTheory.Functor.Stackification.isoAlong_comp_transfer_transition`. -/
theorem exists_hom_of_descends
    (hζ : (descentDatum hG hF hmor hqmor s φ).Descends q y ζ)
    (hζ' : (descentDatum hG hF hmor hqmor s' φ').Descends q y' ζ')
    (hR : R ∈ J U) (hR' : R' ∈ J T)
    {fb : U ⟶ T} (m : x'.1 ⟶ x''.1) (hm : p'.IsHomLift fb m) :
    ∃ n : y.1 ⟶ y'.1, q.IsHomLift fb n ∧
      (∀ ⦃V : 𝒞⦄ (g : V ⟶ U) (hg : R.arrows g) {h : V ⟶ T} (hh : R'.arrows h)
        (hgh : g ≫ fb = h),
        ζ g hg ≫ n =
          Fiber.fiberInclusion.map (transfer hG hF hmor hqmor
            ((presG hG s φ).transition (presG hG s' φ') m hm hg hh hgh)) ≫ ζ' h hh) ∧
      ((∀ ⦃V : 𝒞⦄ (g : V ⟶ U) (hg : R.arrows g) {h : V ⟶ T} (hh : R'.arrows h)
          (hgh : g ≫ fb = h),
          IsIso ((presG hG s φ).transition (presG hG s' φ') m hm hg hh hgh)) →
        q.IsStronglyCartesian fb n) := by
  have hR₀ : R ⊓ Sieve.pullback fb R' ∈ J U :=
    J.intersection_covering hR (J.pullback_stable fb hR')
  obtain ⟨n, hn, hloc, hcart⟩ := LocalPresentation.exists_hom_of_transition
    (presF hG hF hmor hqmor s φ hζ) (presF hG hF hmor hqmor s' φ' hζ')
    (hqmor U) fb hR₀ (fun ⦃_V⦄ ⦃_g⦄ hg => hg.1) (fun ⦃_V⦄ ⦃_g⦄ hg => hg.2)
    (fun ⦃_V⦄ g hg => transfer hG hF hmor hqmor
      ((presG hG s φ).transition (presG hG s' φ') m hm hg.1 hg.2 rfl))
    (fun ⦃_V _W⦄ g hg γ b hb hb' =>
      isoAlong_comp_transfer_transition hG hF hmor hqmor s φ s' φ' hζ hζ' m hm
        hg.1 hg.2 rfl γ hb hb'.1 (by rw [← hb, Category.assoc]) hb'.2)
  refine ⟨n, hn, ?_, ?_⟩
  · intro V g hg h hh hgh
    subst hgh
    have hl := hloc g ⟨hg, hh⟩
    rwa [presF_mor, presF_mor] at hl
  · intro hiso
    refine hcart ?_
    intro V g hg
    have := hiso g hg.1 hg.2 rfl
    exact isIso_transfer hG hF hmor hqmor _

end Transition

/-! ### The extension of `F` along `G` -/

section Extension

/-- The data chosen at an object of a fibre of `𝒮'`: a covering sieve, a local presentation of the
object by objects of `𝒮` along it, and an object of `𝒳` to which the images under `F` of those
objects descend. -/
structure DescentData {U : 𝒞} (x' : p'.Fiber U) where
  /-- The sieve along which the object is presented. -/
  sieve : Sieve U
  /-- It covers. -/
  mem : sieve ∈ J U
  /-- The local objects of `𝒮`. -/
  obj : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U), sieve.arrows f → p.Fiber V
  /-- Their images under `G` present the object. -/
  iso : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : sieve.arrows f),
    (fiberFunctorOfCompEq hG.comp_eq V).obj (obj f hf) ≅ pullbackFiber p' x' f
  /-- The object of `𝒳` the images under `F` descend to. -/
  pt : q.Fiber U
  /-- The descending family of cartesian morphisms. -/
  hom : ∀ ⦃V : 𝒞⦄ (f : V ⟶ U) (hf : sieve.arrows f),
    ((descentDatum hG hF hmor hqmor obj iso).obj f hf).1 ⟶ pt.1
  /-- It exhibits `pt` as the object the datum descends to. -/
  descends : (descentDatum hG hF hmor hqmor obj iso).Descends q pt hom

/-- An object of `𝒮`, read as an object of the fibre over its image. -/
abbrev selfFiber (A : 𝒮) : p.Fiber (p.obj A) := Fiber.mk rfl

omit [Category.{v₄, u₄} 𝒳] [p.IsFibered] [p'.IsFibered] [q.IsFibered] in
/-- The identity of `G A`, read as a morphism over the identification of the two ways of reading
`G A` in a fibre of `𝒮'`. -/
lemma isHomLift_id_map (A : 𝒮) :
    p'.IsHomLift (eqToHom (Functor.congr_obj hG.comp_eq A)) (𝟙 (G.obj A)) := by
  refine IsHomLift.of_fac' p' (eqToHom (Functor.congr_obj hG.comp_eq A)) (𝟙 (G.obj A)) rfl
    (Functor.congr_obj hG.comp_eq A) ?_
  simp

/-- The tautological presentation of `G A` in `𝒮'` by the chosen pullbacks of `A`, relative to the
maximal sieve. -/
noncomputable abbrev presGSelf (A : 𝒮) :
    LocalPresentation p'
      ((fiberFunctorOfCompEq hG.comp_eq (p.obj A)).obj (selfFiber A)) ⊤ :=
  presG hG (pullbackObjects (selfFiber A) ⊤) (pullbackPresentation hG (selfFiber A) ⊤)

omit [Category.{v₄, u₄} 𝒳] [q.IsFibered] in
/-- The cartesian morphism of the tautological presentation of `G A` is the image under `G` of the
chosen cartesian lift. -/
@[simp]
lemma presGSelf_mor (A : 𝒮) ⦃V : 𝒞⦄ (f : V ⟶ p.obj A) (hf : (⊤ : Sieve (p.obj A)).arrows f) :
    (presGSelf hG A).mor f hf = G.map (IsPreFibered.pullbackMap (selfFiber A).2 f) := by
  rw [LocalPresentation.mor]
  exact hG.mapPullbackFiberIso_inv_fac (selfFiber A) f

variable (hobj : ∀ (U : 𝒞) (x' : p'.Fiber U), ∃ R ∈ J U, ∀ ⦃V : 𝒞⦄ ⦃f : V ⟶ U⦄, R.arrows f →
    (fiberFunctorOfCompEq hG.comp_eq V).essImage (pullbackFiber p' x' f))
  (hdesc : HasEffectiveDescent q J)

include hobj hdesc

/-- Every object of a fibre of `𝒮'` admits such a datum: it is locally in the essential image of
`G` by clause (2) of Stacks 02ZN, and the descent datum of any local presentation is effective
because `𝒳` is a stack. -/
lemma nonempty_descentData {U : 𝒞} (x' : p'.Fiber U) :
    Nonempty (DescentData hG hF hmor hqmor x') := by
  obtain ⟨R, hR, hess⟩ := hobj U x'
  obtain ⟨y, s, φ, ζ, hζ⟩ :=
    exists_descends_of_locally_essImage hG hF hmor hqmor hdesc x' hR hess
  exact ⟨⟨R, hR, s, φ, y, ζ, hζ⟩⟩

/-- A choice of such a datum at each object of `𝒮'`, read in the fibre over its image. -/
noncomputable def chosen (X : 𝒮') :
    DescentData hG hF hmor hqmor (Fiber.mk (rfl : p'.obj X = p'.obj X)) :=
  (nonempty_descentData hG hF hmor hqmor hobj hdesc _).some

/-- **The value on objects of the extension of `F` along `G`.** -/
noncomputable def extendObj (X : 𝒮') : 𝒳 := (chosen hG hF hmor hqmor hobj hdesc X).pt.1

/-- The value of the extension at `X` lies over the image of `X` in `𝒞`. -/
lemma extendObj_proj (X : 𝒮') : q.obj (extendObj hG hF hmor hqmor hobj hdesc X) = p'.obj X :=
  (chosen hG hF hmor hqmor hobj hdesc X).pt.2

/-- The local presentation of `X` in `𝒮'` carried by the chosen datum. -/
noncomputable def presGOf (X : 𝒮') :
    LocalPresentation p' (Fiber.mk (rfl : p'.obj X = p'.obj X))
      (chosen hG hF hmor hqmor hobj hdesc X).sieve :=
  presG hG (chosen hG hF hmor hqmor hobj hdesc X).obj (chosen hG hF hmor hqmor hobj hdesc X).iso

/-- **The value on morphisms of the extension of `F` along `G`**, chosen by
`CategoryTheory.Functor.Stackification.exists_hom_of_descends`. -/
noncomputable def extendMap {X Y : 𝒮'} (ψ : X ⟶ Y) :
    extendObj hG hF hmor hqmor hobj hdesc X ⟶ extendObj hG hF hmor hqmor hobj hdesc Y :=
  (exists_hom_of_descends hG hF hmor hqmor _ (chosen hG hF hmor hqmor hobj hdesc X).iso
    _ (chosen hG hF hmor hqmor hobj hdesc Y).iso
    (chosen hG hF hmor hqmor hobj hdesc X).descends
    (chosen hG hF hmor hqmor hobj hdesc Y).descends
    (chosen hG hF hmor hqmor hobj hdesc X).mem (chosen hG hF hmor hqmor hobj hdesc Y).mem
    (fb := p'.map ψ) ψ inferInstance).choose

/-- The three properties of the morphism glued by `exists_hom_of_descends` that define
`extendMap`. -/
private lemma extendMap_choose_spec {X Y : 𝒮'} (ψ : X ⟶ Y) :
    q.IsHomLift (p'.map ψ) (extendMap hG hF hmor hqmor hobj hdesc ψ) ∧
      (∀ ⦃V : 𝒞⦄ (g : V ⟶ p'.obj X) (hg : (chosen hG hF hmor hqmor hobj hdesc X).sieve.arrows g)
        {h : V ⟶ p'.obj Y} (hh : (chosen hG hF hmor hqmor hobj hdesc Y).sieve.arrows h)
        (hgh : g ≫ p'.map ψ = h),
        (chosen hG hF hmor hqmor hobj hdesc X).hom g hg ≫
            extendMap hG hF hmor hqmor hobj hdesc ψ =
          Fiber.fiberInclusion.map (transfer hG hF hmor hqmor
            ((presGOf hG hF hmor hqmor hobj hdesc X).transition
              (presGOf hG hF hmor hqmor hobj hdesc Y) ψ inferInstance hg hh hgh)) ≫
            (chosen hG hF hmor hqmor hobj hdesc Y).hom h hh) ∧
      ((∀ ⦃V : 𝒞⦄ (g : V ⟶ p'.obj X) (hg : (chosen hG hF hmor hqmor hobj hdesc X).sieve.arrows g)
          {h : V ⟶ p'.obj Y} (hh : (chosen hG hF hmor hqmor hobj hdesc Y).sieve.arrows h)
          (hgh : g ≫ p'.map ψ = h),
          IsIso ((presGOf hG hF hmor hqmor hobj hdesc X).transition
            (presGOf hG hF hmor hqmor hobj hdesc Y) ψ inferInstance hg hh hgh)) →
        q.IsStronglyCartesian (p'.map ψ) (extendMap hG hF hmor hqmor hobj hdesc ψ)) :=
  (exists_hom_of_descends hG hF hmor hqmor _ (chosen hG hF hmor hqmor hobj hdesc X).iso
    _ (chosen hG hF hmor hqmor hobj hdesc Y).iso
    (chosen hG hF hmor hqmor hobj hdesc X).descends
    (chosen hG hF hmor hqmor hobj hdesc Y).descends
    (chosen hG hF hmor hqmor hobj hdesc X).mem (chosen hG hF hmor hqmor hobj hdesc Y).mem
    (fb := p'.map ψ) ψ inferInstance).choose_spec

/-- The value of the extension at `ψ` lies over the image of `ψ` in `𝒞`. -/
lemma isHomLift_extendMap {X Y : 𝒮'} (ψ : X ⟶ Y) :
    q.IsHomLift (p'.map ψ) (extendMap hG hF hmor hqmor hobj hdesc ψ) :=
  (extendMap_choose_spec hG hF hmor hqmor hobj hdesc ψ).1

/-- **The local characterization of the value on morphisms.** Over a member `g` of the chosen
sieve at `X` whose composite with `p' ψ` is a member of the chosen sieve at `Y`, the extension of
`ψ` is the transfer along `G` of the transition morphism of the two local presentations. -/
lemma extendMap_spec {X Y : 𝒮'} (ψ : X ⟶ Y) ⦃V : 𝒞⦄ (g : V ⟶ p'.obj X)
    (hg : (chosen hG hF hmor hqmor hobj hdesc X).sieve.arrows g) {h : V ⟶ p'.obj Y}
    (hh : (chosen hG hF hmor hqmor hobj hdesc Y).sieve.arrows h) (hgh : g ≫ p'.map ψ = h) :
    (chosen hG hF hmor hqmor hobj hdesc X).hom g hg ≫
        extendMap hG hF hmor hqmor hobj hdesc ψ =
      Fiber.fiberInclusion.map (transfer hG hF hmor hqmor
        ((presGOf hG hF hmor hqmor hobj hdesc X).transition
          (presGOf hG hF hmor hqmor hobj hdesc Y) ψ inferInstance hg hh hgh)) ≫
        (chosen hG hF hmor hqmor hobj hdesc Y).hom h hh :=
  (extendMap_choose_spec hG hF hmor hqmor hobj hdesc ψ).2.1 g hg hh hgh

/-- The extension of an identity is the identity: the transition morphism of one presentation with
itself along an identity is the identity, and so is its transfer. -/
lemma extendMap_id (X : 𝒮') :
    extendMap hG hF hmor hqmor hobj hdesc (𝟙 X) = 𝟙 (extendObj hG hF hmor hqmor hobj hdesc X) := by
  have hid : q.IsHomLift (p'.map (𝟙 X)) (𝟙 (extendObj hG hF hmor hqmor hobj hdesc X)) := by
    rw [p'.map_id]
    exact IsHomLift.id (chosen hG hF hmor hqmor hobj hdesc X).pt.2
  refine hom_ext_of_descends hG hF hmor hqmor _ (chosen hG hF hmor hqmor hobj hdesc X).iso
    (chosen hG hF hmor hqmor hobj hdesc X).descends
    (chosen hG hF hmor hqmor hobj hdesc X).mem (fun ⦃_V⦄ ⦃_g⦄ hg => hg)
    (isHomLift_extendMap hG hF hmor hqmor hobj hdesc (𝟙 X)) hid ?_
  intro V g hg
  have hgh : g ≫ p'.map (𝟙 X) = g := by rw [p'.map_id, Category.comp_id]
  have htriv : (presGOf hG hF hmor hqmor hobj hdesc X).transition
      (presGOf hG hF hmor hqmor hobj hdesc X) (𝟙 X) inferInstance hg hg hgh = 𝟙 _ :=
    ((presGOf hG hF hmor hqmor hobj hdesc X).transition_uniq
      (presGOf hG hF hmor hqmor hobj hdesc X) (𝟙 X) inferInstance hg hg hgh
      (𝟙 _) (by
        rw [Fiber.fiberInclusion.map_id, Category.id_comp]
        exact (Category.comp_id _).symm)).symm
  rw [extendMap_spec hG hF hmor hqmor hobj hdesc (𝟙 X) g hg hg hgh, htriv]
  rw [show (𝟙 ((presGOf hG hF hmor hqmor hobj hdesc X).obj g hg)) =
      𝟙 ((fiberFunctorOfCompEq hG.comp_eq V).obj
        ((chosen hG hF hmor hqmor hobj hdesc X).obj g hg)) from rfl,
    transfer_id, Fiber.fiberInclusion.map_id, Category.id_comp]
  exact (Category.comp_id _).symm

/-- The extension of a composite is the composite of the extensions: the transition morphisms
compose, and the transfer is functorial. -/
lemma extendMap_comp {X Y Z : 𝒮'} (ψ₁ : X ⟶ Y) (ψ₂ : Y ⟶ Z) :
    extendMap hG hF hmor hqmor hobj hdesc (ψ₁ ≫ ψ₂) =
      extendMap hG hF hmor hqmor hobj hdesc ψ₁ ≫ extendMap hG hF hmor hqmor hobj hdesc ψ₂ := by
  have hcomp : q.IsHomLift (p'.map (ψ₁ ≫ ψ₂))
      (extendMap hG hF hmor hqmor hobj hdesc ψ₁ ≫ extendMap hG hF hmor hqmor hobj hdesc ψ₂) := by
    have h1 := isHomLift_extendMap hG hF hmor hqmor hobj hdesc ψ₁
    have h2 := isHomLift_extendMap hG hF hmor hqmor hobj hdesc ψ₂
    have h0 : q.IsHomLift (p'.map ψ₁ ≫ p'.map ψ₂)
      (extendMap hG hF hmor hqmor hobj hdesc ψ₁ ≫
        extendMap hG hF hmor hqmor hobj hdesc ψ₂) := inferInstance
    rwa [← p'.map_comp] at h0
  have hR₀ : (chosen hG hF hmor hqmor hobj hdesc X).sieve ⊓
      Sieve.pullback (p'.map ψ₁) (chosen hG hF hmor hqmor hobj hdesc Y).sieve ⊓
      Sieve.pullback (p'.map (ψ₁ ≫ ψ₂)) (chosen hG hF hmor hqmor hobj hdesc Z).sieve ∈
        J (p'.obj X) :=
    J.intersection_covering
      (J.intersection_covering (chosen hG hF hmor hqmor hobj hdesc X).mem
        (J.pullback_stable _ (chosen hG hF hmor hqmor hobj hdesc Y).mem))
      (J.pullback_stable _ (chosen hG hF hmor hqmor hobj hdesc Z).mem)
  refine hom_ext_of_descends hG hF hmor hqmor _ (chosen hG hF hmor hqmor hobj hdesc X).iso
    (chosen hG hF hmor hqmor hobj hdesc X).descends hR₀ (fun ⦃_V⦄ ⦃_g⦄ hg => hg.1.1)
    (isHomLift_extendMap hG hF hmor hqmor hobj hdesc (ψ₁ ≫ ψ₂)) hcomp ?_
  rintro V g ⟨⟨hgX, hgY⟩, hgZ⟩
  have hassoc : (g ≫ p'.map ψ₁) ≫ p'.map ψ₂ = g ≫ p'.map (ψ₁ ≫ ψ₂) := by
    rw [p'.map_comp, Category.assoc]
  have hcomp' :
      (presGOf hG hF hmor hqmor hobj hdesc X).transition
          (presGOf hG hF hmor hqmor hobj hdesc Y) ψ₁ inferInstance hgX hgY rfl ≫
        (presGOf hG hF hmor hqmor hobj hdesc Y).transition
          (presGOf hG hF hmor hqmor hobj hdesc Z) ψ₂ inferInstance hgY hgZ hassoc =
      (presGOf hG hF hmor hqmor hobj hdesc X).transition
        (presGOf hG hF hmor hqmor hobj hdesc Z) (ψ₁ ≫ ψ₂) inferInstance hgX hgZ rfl := by
    rw [LocalPresentation.transition_comp]
    rfl
  rw [extendMap_spec hG hF hmor hqmor hobj hdesc (ψ₁ ≫ ψ₂) g hgX hgZ rfl, ← Category.assoc,
    extendMap_spec hG hF hmor hqmor hobj hdesc ψ₁ g hgX hgY rfl, Category.assoc,
    extendMap_spec hG hF hmor hqmor hobj hdesc ψ₂ (g ≫ p'.map ψ₁) hgY hgZ hassoc,
    ← Category.assoc, ← Fiber.fiberInclusion.map_comp, ← transfer_comp, hcomp']

/-- **The extension preserves strongly cartesian morphisms**, in the form in which the morphism of
the base is the image of the morphism. Every transition morphism of a strongly cartesian morphism
is an isomorphism, hence so is its transfer, and a morphism glued from isomorphisms is strongly
cartesian. -/
lemma isStronglyCartesian_extendMap {X Y : 𝒮'} (ψ : X ⟶ Y)
    (hψ : p'.IsStronglyCartesian (p'.map ψ) ψ) :
    q.IsStronglyCartesian (p'.map ψ) (extendMap hG hF hmor hqmor hobj hdesc ψ) := by
  refine (extendMap_choose_spec hG hF hmor hqmor hobj hdesc ψ).2.2 ?_
  intro V g hg h hh hgh
  exact LocalPresentation.isIso_transition (presGOf hG hF hmor hqmor hobj hdesc X)
    (presGOf hG hF hmor hqmor hobj hdesc Y) ψ hψ hg hh hgh

/-- **The functor underlying the extension of `F` along `G`**, Stacks 0435. Its value on an object
`X` of `𝒮'` is the object of `𝒳` to which the images under `F` of a chosen local presentation of
`X` descend, and its value on a morphism is the morphism glued from the transfers along `G` of the
transition morphisms of the chosen presentations. -/
@[stacks 0435, simps]
noncomputable def extend : 𝒮' ⥤ 𝒳 where
  obj := extendObj hG hF hmor hqmor hobj hdesc
  map := extendMap hG hF hmor hqmor hobj hdesc
  map_id := extendMap_id hG hF hmor hqmor hobj hdesc
  map_comp := extendMap_comp hG hF hmor hqmor hobj hdesc

/-- **The extension is strictly over `𝒞`.** Its value on an object lies in the fibre over the
image of that object, and its value on a morphism lies over the image of that morphism. -/
theorem extend_comp_eq : extend hG hF hmor hqmor hobj hdesc ⋙ q = p' := by
  refine Functor.ext (fun X => extendObj_proj hG hF hmor hqmor hobj hdesc X) ?_
  intro X Y ψ
  have := isHomLift_extendMap hG hF hmor hqmor hobj hdesc ψ
  exact IsHomLift.fac' q (p'.map ψ) (extendMap hG hF hmor hqmor hobj hdesc ψ)

/-- **The extension is a 1-morphism of fibred categories over `𝒞`**: it is strictly over `𝒞` and
preserves strongly cartesian morphisms. -/
@[stacks 0435]
theorem extend_isFibredOneMorphism :
    p'.IsFibredOneMorphism q (extend hG hF hmor hqmor hobj hdesc) where
  comp_eq := extend_comp_eq hG hF hmor hqmor hobj hdesc
  map_isStronglyCartesian := by
    intro Rb Tb f a b ψ hψ
    have := hψ
    have hab : p'.obj a = Rb := IsHomLift.domain_eq p' f ψ
    have hbb : p'.obj b = Tb := IsHomLift.codomain_eq p' f ψ
    subst hab
    subst hbb
    have hf : f = p'.map ψ := IsHomLift.eq_of_isHomLift p' f ψ
    subst hf
    exact isStronglyCartesian_extendMap hG hF hmor hqmor hobj hdesc ψ hψ

/-! #### The 2-isomorphism `G ⋙ H ≅ F` -/

/-- **The component at `A` of the 2-isomorphism of Stacks 0435**, obtained by comparing the chosen
presentation of `G A` with the tautological presentation of `G A` by the chosen pullbacks of `A`,
whose images under `F` descend to `F A`. -/
noncomputable def unitHom (A : 𝒮) :
    (extend hG hF hmor hqmor hobj hdesc).obj (G.obj A) ⟶ F.obj A :=
  (exists_hom_of_descends hG hF hmor hqmor
    (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).obj
    (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).iso
    (pullbackObjects (selfFiber A) ⊤) (pullbackPresentation hG (selfFiber A) ⊤)
    (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).descends
    (descentDatum_descends_map hG hF hmor hqmor (selfFiber A) ⊤)
    (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).mem (J.top_mem (p.obj A))
    (fb := eqToHom (Functor.congr_obj hG.comp_eq A)) (𝟙 (G.obj A)) (isHomLift_id_map hG A)).choose

/-- The three properties of the morphism glued by `exists_hom_of_descends` that define
`unitHom`. -/
private lemma unitHom_choose_spec (A : 𝒮) :
    q.IsHomLift (eqToHom (Functor.congr_obj hG.comp_eq A))
        (unitHom hG hF hmor hqmor hobj hdesc A) ∧
      (∀ ⦃V : 𝒞⦄ (g : V ⟶ p'.obj (G.obj A))
        (hg : (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).sieve.arrows g)
        {h : V ⟶ p.obj A} (hh : (⊤ : Sieve (p.obj A)).arrows h)
        (hgh : g ≫ eqToHom (Functor.congr_obj hG.comp_eq A) = h),
        (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).hom g hg ≫
            unitHom hG hF hmor hqmor hobj hdesc A =
          Fiber.fiberInclusion.map (transfer hG hF hmor hqmor
            ((presGOf hG hF hmor hqmor hobj hdesc (G.obj A)).transition (presGSelf hG A)
              (𝟙 (G.obj A)) (isHomLift_id_map hG A) hg hh hgh)) ≫
            F.map (IsPreFibered.pullbackMap (selfFiber A).2 h)) ∧
      ((∀ ⦃V : 𝒞⦄ (g : V ⟶ p'.obj (G.obj A))
          (hg : (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).sieve.arrows g)
          {h : V ⟶ p.obj A} (hh : (⊤ : Sieve (p.obj A)).arrows h)
          (hgh : g ≫ eqToHom (Functor.congr_obj hG.comp_eq A) = h),
          IsIso ((presGOf hG hF hmor hqmor hobj hdesc (G.obj A)).transition (presGSelf hG A)
            (𝟙 (G.obj A)) (isHomLift_id_map hG A) hg hh hgh)) →
        q.IsStronglyCartesian (eqToHom (Functor.congr_obj hG.comp_eq A))
          (unitHom hG hF hmor hqmor hobj hdesc A)) :=
  (exists_hom_of_descends hG hF hmor hqmor
    (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).obj
    (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).iso
    (pullbackObjects (selfFiber A) ⊤) (pullbackPresentation hG (selfFiber A) ⊤)
    (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).descends
    (descentDatum_descends_map hG hF hmor hqmor (selfFiber A) ⊤)
    (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).mem (J.top_mem (p.obj A))
    (fb := eqToHom (Functor.congr_obj hG.comp_eq A)) (𝟙 (G.obj A))
    (isHomLift_id_map hG A)).choose_spec

/-- The component at `A` of the 2-isomorphism lies over the identification of the images of
`G A` and `A` in `𝒞`. -/
lemma isHomLift_unitHom (A : 𝒮) :
    q.IsHomLift (eqToHom (Functor.congr_obj hG.comp_eq A)) (unitHom hG hF hmor hqmor hobj hdesc A) :=
  (unitHom_choose_spec hG hF hmor hqmor hobj hdesc A).1

/-- The local characterization of the component of the 2-isomorphism. -/
lemma unitHom_spec (A : 𝒮) ⦃V : 𝒞⦄ (g : V ⟶ p'.obj (G.obj A))
    (hg : (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).sieve.arrows g)
    {h : V ⟶ p.obj A} (hh : (⊤ : Sieve (p.obj A)).arrows h)
    (hgh : g ≫ eqToHom (Functor.congr_obj hG.comp_eq A) = h) :
    (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).hom g hg ≫
        unitHom hG hF hmor hqmor hobj hdesc A =
      Fiber.fiberInclusion.map (transfer hG hF hmor hqmor
        ((presGOf hG hF hmor hqmor hobj hdesc (G.obj A)).transition (presGSelf hG A)
          (𝟙 (G.obj A)) (isHomLift_id_map hG A) hg hh hgh)) ≫
        F.map (IsPreFibered.pullbackMap (selfFiber A).2 h) :=
  (unitHom_choose_spec hG hF hmor hqmor hobj hdesc A).2.1 g hg hh hgh

/-- The component of the 2-isomorphism is strongly cartesian over an isomorphism of the base,
hence an isomorphism. -/
lemma isIso_unitHom (A : 𝒮) : IsIso (unitHom hG hF hmor hqmor hobj hdesc A) := by
  have hid : p'.IsStronglyCartesian (eqToHom (Functor.congr_obj hG.comp_eq A)) (𝟙 (G.obj A)) :=
    have := isHomLift_id_map hG A
    IsStronglyCartesian.of_isIso p' (eqToHom (Functor.congr_obj hG.comp_eq A)) (𝟙 (G.obj A))
  have hcart : q.IsStronglyCartesian (eqToHom (Functor.congr_obj hG.comp_eq A))
      (unitHom hG hF hmor hqmor hobj hdesc A) := by
    refine (unitHom_choose_spec hG hF hmor hqmor hobj hdesc A).2.2 ?_
    intro V g hg h hh hgh
    exact LocalPresentation.isIso_transition
      (presGOf hG hF hmor hqmor hobj hdesc (G.obj A)) (presGSelf hG A)
      (𝟙 (G.obj A)) hid hg hh hgh
  exact IsStronglyCartesian.isIso_of_base_isIso q (eqToHom (Functor.congr_obj hG.comp_eq A)) _

omit [Category.{v₄, u₄} 𝒳] [p.IsFibered] [p'.IsFibered] [q.IsFibered] hobj hdesc in
/-- The image under `G` of a morphism of `𝒮`, read over the identifications of the fibres. -/
lemma map_comp_eqToHom {A B : 𝒮} (u : A ⟶ B) :
    p'.map (G.map u) ≫ eqToHom (Functor.congr_obj hG.comp_eq B) = eqToHom (Functor.congr_obj hG.comp_eq A) ≫ p.map u := by
  have h := Functor.congr_hom hG.comp_eq u
  rw [Functor.comp_map] at h
  rw [h]
  simp

/-- **Naturality of the 2-isomorphism.** Both sides are determined by their restrictions along the
chosen presentation of `G A`, where each is the transfer of a composite of transition morphisms,
and the two composites agree because the transition morphisms are pinned down by the cartesian
morphisms of the presentations. -/
lemma unitHom_naturality {A B : 𝒮} (u : A ⟶ B) :
    extendMap hG hF hmor hqmor hobj hdesc (G.map u) ≫
        unitHom hG hF hmor hqmor hobj hdesc B =
      unitHom hG hF hmor hqmor hobj hdesc A ≫ F.map u := by
  have hbase := map_comp_eqToHom hG u
  have hFu : q.IsHomLift (p.map u) (F.map u) := isHomLift_map_of_comp_eq hF.comp_eq (p.map u) u
  -- Both sides lie over the same morphism of the base.
  have hL : q.IsHomLift (eqToHom (Functor.congr_obj hG.comp_eq A) ≫ p.map u)
      (extendMap hG hF hmor hqmor hobj hdesc (G.map u) ≫
        unitHom hG hF hmor hqmor hobj hdesc B) := by
    have h1 := isHomLift_extendMap hG hF hmor hqmor hobj hdesc (G.map u)
    have h2 := isHomLift_unitHom hG hF hmor hqmor hobj hdesc B
    have h0 : q.IsHomLift (p'.map (G.map u) ≫ eqToHom (Functor.congr_obj hG.comp_eq B))
      (extendMap hG hF hmor hqmor hobj hdesc (G.map u) ≫
        unitHom hG hF hmor hqmor hobj hdesc B) := inferInstance
    rwa [hbase] at h0
  have hR : q.IsHomLift (eqToHom (Functor.congr_obj hG.comp_eq A) ≫ p.map u)
      (unitHom hG hF hmor hqmor hobj hdesc A ≫ F.map u) := by
    have h1 := isHomLift_unitHom hG hF hmor hqmor hobj hdesc A
    have h2 := hFu
    infer_instance
  have hR₀ : (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).sieve ⊓
      Sieve.pullback (p'.map (G.map u))
        (chosen hG hF hmor hqmor hobj hdesc (G.obj B)).sieve ∈ J (p'.obj (G.obj A)) :=
    J.intersection_covering (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).mem
      (J.pullback_stable _ (chosen hG hF hmor hqmor hobj hdesc (G.obj B)).mem)
  refine hom_ext_of_descends hG hF hmor hqmor _
    (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).iso
    (chosen hG hF hmor hqmor hobj hdesc (G.obj A)).descends hR₀
    (fun ⦃_V⦄ ⦃_g⦄ hg => hg.1)
    (z := (fiberFunctorOfCompEq hF.comp_eq (p.obj B)).obj (selfFiber B))
    (fb := eqToHom (Functor.congr_obj hG.comp_eq A) ≫ p.map u) hL hR ?_
  rintro V g ⟨hgA, hgB⟩
  -- Name the three composites so that reassociation cannot reach into the sieve indices.
  obtain ⟨h, hh⟩ : ∃ k : V ⟶ p'.obj (G.obj B), g ≫ p'.map (G.map u) = k := ⟨_, rfl⟩
  obtain ⟨g₂, hg₂⟩ : ∃ k : V ⟶ p.obj A, g ≫ eqToHom (Functor.congr_obj hG.comp_eq A) = k := ⟨_, rfl⟩
  obtain ⟨h₂, hh₂⟩ : ∃ k : V ⟶ p.obj B, h ≫ eqToHom (Functor.congr_obj hG.comp_eq B) = k := ⟨_, rfl⟩
  have hgB' : (chosen hG hF hmor hqmor hobj hdesc (G.obj B)).sieve.arrows h := hh ▸ hgB
  -- The morphism of `𝒮` comparing the chosen pullbacks of `A` and of `B` over `V`.
  have hg2 : g₂ ≫ p.map u = h₂ := by
    rw [← hg₂, ← hh₂, ← hh, Category.assoc, Category.assoc, hbase]
  set w := (LocalPresentation.self (selfFiber A) (⊤ : Sieve (p.obj A))).transition
    (LocalPresentation.self (selfFiber B) (⊤ : Sieve (p.obj B))) u inferInstance
    (g := g₂) trivial trivial hg2 with hwdef
  have hwfac : Fiber.fiberInclusion.map w ≫ IsPreFibered.pullbackMap (selfFiber B).2 h₂ =
      IsPreFibered.pullbackMap (selfFiber A).2 g₂ ≫ u := by
    have hfac := LocalPresentation.transition_fac
      (LocalPresentation.self (selfFiber A) (⊤ : Sieve (p.obj A)))
      (LocalPresentation.self (selfFiber B) (⊤ : Sieve (p.obj B))) u inferInstance
      (g := g₂) trivial trivial hg2
    rwa [LocalPresentation.self_mor, LocalPresentation.self_mor, ← hwdef] at hfac
  -- The two composites of transition morphisms in `𝒮'` agree.
  have hkey :
      (presGOf hG hF hmor hqmor hobj hdesc (G.obj A)).transition
          (presGOf hG hF hmor hqmor hobj hdesc (G.obj B)) (G.map u) inferInstance hgA hgB' hh ≫
        (presGOf hG hF hmor hqmor hobj hdesc (G.obj B)).transition (presGSelf hG B)
          (𝟙 (G.obj B)) (isHomLift_id_map hG B) hgB' trivial hh₂ =
      (presGOf hG hF hmor hqmor hobj hdesc (G.obj A)).transition (presGSelf hG A)
          (𝟙 (G.obj A)) (isHomLift_id_map hG A) hgA trivial hg₂ ≫
        (fiberFunctorOfCompEq hG.comp_eq V).map w := by
    -- The two transition morphisms of an identity, composed with the cartesian morphism of the
    -- tautological presentation.
    have hT2 : Fiber.fiberInclusion.map
          ((presGOf hG hF hmor hqmor hobj hdesc (G.obj B)).transition (presGSelf hG B)
            (𝟙 (G.obj B)) (isHomLift_id_map hG B) hgB' trivial hh₂) ≫
          (presGSelf hG B).mor h₂ trivial =
        (presGOf hG hF hmor hqmor hobj hdesc (G.obj B)).mor h hgB' := by
      rw [LocalPresentation.transition_fac]
      exact Category.comp_id _
    have hT3 : Fiber.fiberInclusion.map
          ((presGOf hG hF hmor hqmor hobj hdesc (G.obj A)).transition (presGSelf hG A)
            (𝟙 (G.obj A)) (isHomLift_id_map hG A) hgA trivial hg₂) ≫
          (presGSelf hG A).mor g₂ trivial =
        (presGOf hG hF hmor hqmor hobj hdesc (G.obj A)).mor g hgA := by
      rw [LocalPresentation.transition_fac]
      exact Category.comp_id _
    refine (presGSelf hG B).hom_ext trivial _ _ ?_
    rw [Fiber.fiberInclusion.map_comp, Fiber.fiberInclusion.map_comp, Category.assoc,
      Category.assoc, hT2, LocalPresentation.transition_fac, presGSelf_mor,
      fiberInclusion_map_fiberFunctorOfCompEq_map, ← G.map_comp, hwfac, G.map_comp,
      ← Category.assoc, ← presGSelf_mor hG A g₂ trivial, hT3]
  -- Restrict both sides and compare.
  rw [← Category.assoc, extendMap_spec hG hF hmor hqmor hobj hdesc (G.map u) g hgA hgB' hh,
    Category.assoc, unitHom_spec hG hF hmor hqmor hobj hdesc B h hgB' trivial hh₂,
    ← Category.assoc, ← Fiber.fiberInclusion.map_comp, ← transfer_comp, hkey,
    transfer_comp, transfer_map, Fiber.fiberInclusion.map_comp, Category.assoc,
    fiberInclusion_map_fiberFunctorOfCompEq_map, ← F.map_comp, hwfac, F.map_comp,
    ← Category.assoc, ← unitHom_spec hG hF hmor hqmor hobj hdesc A g hgA trivial hg₂,
    Category.assoc]

/-- The component of the 2-isomorphism lies over an identity: it lies over the identification of
the two ways of reading `G A` in a fibre, which is the identity once both sides are read in the
fibre over the image of `A`. -/
lemma isHomLift_id_unitHom (A : 𝒮) :
    q.IsHomLift (𝟙 (p.obj A)) (unitHom hG hF hmor hqmor hobj hdesc A) := by
  have hlift := isHomLift_unitHom hG hF hmor hqmor hobj hdesc A
  have hfac := IsHomLift.fac' q (eqToHom (Functor.congr_obj hG.comp_eq A))
    (unitHom hG hF hmor hqmor hobj hdesc A)
  refine IsHomLift.of_fac' q (𝟙 (p.obj A)) _
    ((extendObj_proj hG hF hmor hqmor hobj hdesc (G.obj A)).trans (Functor.congr_obj hG.comp_eq A))
    (IsHomLift.codomain_eq q (eqToHom (Functor.congr_obj hG.comp_eq A))
      (unitHom hG hF hmor hqmor hobj hdesc A)) ?_
  rw [hfac]
  simp

/-- **The 2-isomorphism `G ⋙ H ≅ F` of Stacks 0435.** Its component at `A` compares the object of
`𝒳` that the chosen presentation of `G A` descends to with `F A`, and it is an isomorphism because
both are descents of presentations of one and the same object of `𝒮'`. -/
@[stacks 0435]
noncomputable def unit : G ⋙ extend hG hF hmor hqmor hobj hdesc ≅ F :=
  have : ∀ A : 𝒮, IsIso (unitHom hG hF hmor hqmor hobj hdesc A) :=
    isIso_unitHom hG hF hmor hqmor hobj hdesc
  NatIso.ofComponents (fun A => asIso (unitHom hG hF hmor hqmor hobj hdesc A))
    (fun {_A _B} u => unitHom_naturality hG hF hmor hqmor hobj hdesc u)

/-- The component at `A` of the 2-isomorphism `G ⋙ H ≅ F` is `unitHom A`. -/
@[simp]
lemma unit_hom_app (A : 𝒮) :
    (unit hG hF hmor hqmor hobj hdesc).hom.app A = unitHom hG hF hmor hqmor hobj hdesc A := rfl

/-- Every component of the 2-isomorphism lies over an identity, so it is a 2-morphism of fibred
categories over `𝒞`. -/
@[stacks 0435]
lemma isHomLift_unit_app (A : 𝒮) :
    q.IsHomLift (𝟙 (p.obj A)) ((unit hG hF hmor hqmor hobj hdesc).hom.app A) :=
  isHomLift_id_unitHom hG hF hmor hqmor hobj hdesc A

end Extension

end Stackification

end Bridge

end Functor

end CategoryTheory
