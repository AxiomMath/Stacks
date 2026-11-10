module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.SystemTransitionCalculus
public import StacksFrontier.CategoryTheory.Sites.ConstantSheaf.MorphismOfSitesGlobalSections
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.PushforwardComparison
public import StacksFrontier.CategoryTheory.Sites.Simplicial.SimplicialSemiRepresentableSite

/-! # Coherence of the direct-image comparisons of an inverse system of sites

`Stacks.WeakSites.ColimitSiteCohomology.abelianSheafPushforwardIdIso` and
`...abelianSheafPushforwardCompIso` identify direct image along an identity transition with the
identity functor, and direct image along a composite with the composite of the direct images. A
diagram over `(Over i)ᵒᵖ` of the sheaves of a system pushed down to a fixed index has both of them
in its arrows, so its `map_id` and `map_comp` laws need the corresponding *coherence* statements,
which neither Mathlib nor this development has. This file supplies the two of the three general
rewrites those coherences need that the repository did not already have; the coherences themselves
are not proved here.

What blocks them is no longer the opacity of the two comparison definitions: those were defined in
tactic mode, so unfolding them left an opaque `id (…)` around an `Iso.trans` of structure literals
that `simp` could not project `.hom.app P` through, and they are now term-mode, which removes that
at source.

What blocks them now is **unfolding `abelianSheafPushforward` itself**. With that definition in the
simp set the `map_id` goal reduces to one line,

`whiskerLeft (u_b).op (𝟙 ((𝟭).op ⋙ P.obj)) ≫ eqToHom h₁ ≫ (eqToHom h₂).hom = 𝟙 ((u_b).op ⋙ P.obj)`

but no further rewrite applies to it, and an explicit `rw [Functor.whiskerLeft_id']` reports why:

> The target expression is not type-correct under the `implicit` transparency level, which is
> usually caused by unfolding of semireducible definitions in prior tactic steps.

`abelianSheafPushforward` is a semireducible `def`, so unfolding it rewrites the ambient term into
`ObjectProperty.lift (Presheaf.IsSheaf …) …` while the `eqToHom` proof obligations in the goal keep
their types stated in terms of `abelianSheafPushforward`; the goal is then ill-typed at implicit
transparency and every subsequent rewrite — including `Sheaf.eqToHom_hom`, which otherwise matches
the trailing projection exactly — is refused. It is not an instance mismatch, which was the earlier
hypothesis recorded here.

The obstruction is a **class**, not one instance of unfolding, and that is the finding that rules
out the component-lemma route as first framed.
`CategoryTheory.Functor.sheafPushforwardContinuousId` and `...sheafPushforwardContinuousComp` have
bodies `Iso.refl _` whose type differs *syntactically* from the stated type —
`sheafPushforwardContinuousId : pf (𝟭 C) ≅ 𝟭 _` has body `Iso.refl (pf (𝟭 C))`, which only
typechecks because the two sides are defeq. So `dsimp` replacing the constant by its body makes the
surrounding `.symm` ill-typed at implicit transparency, exactly as unfolding
`abelianSheafPushforward` does. Component lemmas of the form
`((abelianSheafPushforwardIdIso D j).hom.app P).hom = eqToHom …` need precisely that unfolding in
their proofs, so they are not provable as stated: the `rw` reports

> Application type mismatch: `Iso.refl (pf (𝟭 C))` has type `pf (𝟭 C) ≅ pf (𝟭 C)` but is expected
> to have type `pf (𝟭 C) ≅ 𝟭 (Sheaf (D.J j) Ab)`.

The general rule this yields: **none of these `Iso.refl`-bodied comparison definitions may be
unfolded by `dsimp`/`simp`**, and since Mathlib provides no propositional component or composition
lemmas for them (they carry `@[simps!]`, whose output is generated rather than written, and nothing
in `Mathlib/CategoryTheory/Sites/` states a composition law for `sheafPushforwardContinuousIso`),
there is nothing to rewrite with either.

What this leaves is to stop using the Mathlib comparisons in the diagram's arrows at all. The
system supplies `comp` and `id_map` as *equalities of functors*, and direct image is precomposition
with `u_a.op`, which is associative definitionally — so `abelianSheafPushforward a ⋙
abelianSheafPushforward b` and `abelianSheafPushforward (a ≫ b)` are equal functors, and the
arrows can be built from `eqToHom` of that equality directly, with no `Iso.refl`-bodied constant
anywhere. That is the next design to try, and `abelianSheafPushforward_map_hom` below — the
`@[simps]`-shaped action-on-morphisms lemma those definitions never generated, which *is* provable
by `rfl` because its two sides are genuinely defeq — is its first piece.

## Main results

* `CategoryTheory.whiskerRight_natTransOp_eqToHom`: whiskering `NatTrans.op (eqToHom h)` into a
  functor is the `eqToHom` of the corresponding equality of composites.
* `CategoryTheory.Sheaf.eqToHom_hom`: the underlying map of presheaves of an `eqToHom` of sheaves
  is an `eqToHom`.
* `CategoryTheory.whiskerLeft_congr`: whiskering on the left transports along an equality of the
  whiskering functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sites.InverseSystem

universe v u w t s

namespace CategoryTheory

/-- **Whiskering the opposite of an `eqToHom` of functors is an `eqToHom`.** For an equality
`h : u = u'` of functors `A ⥤ B` and any `P : Bᵒᵖ ⥤ E`, the natural transformation
`u'.op ⋙ P ⟶ u.op ⋙ P` obtained by whiskering `NatTrans.op (eqToHom h)` into `P` is the
transport along the induced equality of composites.

This is what makes a chain of direct-image comparisons telescope: the comparisons of
`CategoryTheory.Functor.sheafPushforwardContinuous` are built from
`...sheafPushforwardContinuousIso`, whose components are exactly such whiskerings. -/
public theorem whiskerRight_natTransOp_eqToHom {A : Type*} [Category A] {B : Type*} [Category B]
    {E : Type*} [Category E] {u u' : A ⥤ B} (h : u = u') (P : Bᵒᵖ ⥤ E) :
    Functor.whiskerRight (NatTrans.op (eqToHom h)) P =
      eqToHom (congrArg (fun v : A ⥤ B => v.op ⋙ P) h.symm) := by
  subst h
  simp

/-- **The underlying map of presheaves of an `eqToHom` of sheaves is an `eqToHom`.** Mathlib has
this for no coefficient category; it is the second rewrite a chain of direct-image comparisons
needs in order to telescope, the comparisons being `eqToHom`s of sheaves whose presheaf maps the
computation sees. -/
public theorem Sheaf.eqToHom_hom {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A : Type*} [Category A] {S S' : Sheaf J A} (h : S = S') :
    (eqToHom h : S ⟶ S').hom = eqToHom (congrArg (fun T : Sheaf J A => T.obj) h) := by
  subst h
  simp

/-- **Whiskering on the left transports along an equality of the whiskering functor.** For
`h : F = F'` an equality of functors `A ⥤ B` and `α : G ⟶ G'` between functors `B ⥤ E`, whiskering
`α` by `F` is whiskering by `F'` conjugated by the two transports.

Mathlib has `CategoryTheory.Functor.whiskerLeft_twice` for the interchange of two whiskerings and
`whiskerLeft_eqToHom` for an `eqToHom` in the *transformation* argument, but nothing for an
equality in the *functor* argument; that is what an inverse system of sites needs, its `comp` and
`id_map` being equalities of transition functors. -/
public theorem whiskerLeft_congr {A : Type*} [Category A] {B : Type*} [Category B]
    {E : Type*} [Category E] {F F' : A ⥤ B} (h : F = F') {G G' : B ⥤ E} (α : G ⟶ G') :
    Functor.whiskerLeft F α =
      eqToHom (congrArg (fun v : A ⥤ B => v ⋙ G) h) ≫ Functor.whiskerLeft F' α ≫
        eqToHom (congrArg (fun v : A ⥤ B => v ⋙ G') h).symm := by
  subst h
  simp

/-- **Two nested left whiskerings are one, along an equality of the composite functor.** For
`h : F ⋙ G = H` and `α : X ⟶ Y` between functors `E ⥤ Z`, whiskering `α` by `G` and then by `F` is
whiskering by `H`, conjugated by the two transports.

This is `CategoryTheory.Functor.whiskerLeft_twice` and `whiskerLeft_congr` in one step, and the
combination is what a consumer wants: `whiskerLeft_twice` alone introduces
`CategoryTheory.Functor.associator`s, whose components are identities but which are not
syntactically `𝟙` as natural transformations, so a goal carrying them does not close by rewriting.
-/
public theorem whiskerLeft_whiskerLeft_congr {A : Type*} [Category A] {B : Type*} [Category B]
    {E : Type*} [Category E] {Z : Type*} [Category Z] {F : A ⥤ B} {G : B ⥤ E} {H : A ⥤ E}
    (h : F ⋙ G = H) {X Y : E ⥤ Z} (α : X ⟶ Y) :
    Functor.whiskerLeft F (Functor.whiskerLeft G α) =
      eqToHom (congrArg (fun v : A ⥤ E => v ⋙ X) h) ≫ Functor.whiskerLeft H α ≫
        eqToHom (congrArg (fun v : A ⥤ E => v ⋙ Y) h).symm := by
  subst h
  ext Z'
  simp

end CategoryTheory

namespace Stacks.WeakSites.ColimitSiteCohomology

open InverseSystemOfFiniteSites

variable (D : InverseSystemOfFiniteSites.{v, u, w})

/-- **Successive direct images are direct image along the composite**, as an *equality* of
functors rather than an isomorphism. The system's `comp` is an equality of transition functors and
`CategoryTheory.Functor.sheafPushforwardContinuousComp` is `Iso.refl`, so once that equality is
rewritten the two functors are definitionally equal.

This is what lets a diagram of pushed-down sheaves take its arrows from `eqToHom` with no
`Iso.refl`-bodied comparison definition appearing, and so without the implicit-transparency failure
those definitions cause when unfolded. Unfolding `abelianSheafPushforward` is safe *here*, where
the goal is a bare equality of functors: the failure needs an `eqToHom` obligation whose type is
stated in terms of the unfolded definition, and this goal has none. -/
public theorem abelianSheafPushforward_comp {i j k : D.I} (a : i ⟶ j) (b : j ⟶ k) :
    abelianSheafPushforward.{v, u, w, t} D a ⋙ abelianSheafPushforward.{v, u, w, t} D b =
      abelianSheafPushforward.{v, u, w, t} D (a ≫ b) := by
  dsimp only [abelianSheafPushforward]
  simp only [D.comp a b]
  rfl

/-- **Direct image along an identity transition is the identity functor**, as an *equality* of
functors. The system's `id_map` is an equality of transition functors and
`CategoryTheory.Functor.sheafPushforwardContinuousId` is `Iso.refl`. -/
public theorem abelianSheafPushforward_id (j : D.I) :
    abelianSheafPushforward.{v, u, w, t} D (𝟙 j) = 𝟭 (Sheaf (D.J j) (Ab.{max u v w t})) := by
  dsimp only [abelianSheafPushforward]
  simp only [D.id_map j]
  rfl

/-- **The action of a direct-image functor of the system on morphisms, on underlying presheaves.**
Direct image is precomposition with `u_a.op`, so it acts by whiskering. Stated with
`abelianSheafPushforward` left opaque on the left-hand side, the unfolding confined to the proof.
-/
public theorem abelianSheafPushforward_map_hom {i j : D.I} (a : i ⟶ j)
    {X Y : Sheaf (D.J i) (Ab.{max u v w t})} (g : X ⟶ Y) :
    ((abelianSheafPushforward.{v, u, w, t} D a).map g).hom =
      Functor.whiskerLeft (D.u a).op g.hom :=
  rfl


variable (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, w, t} D)

/-- **The transition at an identity, as a sheaf morphism, is a transport.** The `eqToHom` form of
`transition_id_eq`, with `abelianSheafPushforward_id` supplying the equality of functors in
place of `abelianSheafPushforwardIdIso`. -/
public theorem pushforwardTransition_id_eqToHom (j : D.I) :
    pushforwardTransition D F (𝟙 j) =
      eqToHom (congrArg
        (fun G : Sheaf (D.J j) (Ab.{max u v w t}) ⥤ Sheaf (D.J j) (Ab.{max u v w t}) =>
          G.obj (F.obj j))
        (abelianSheafPushforward_id.{v, u, w, t} D j).symm) := by
  apply Sheaf.hom_ext
  rw [pushforwardTransition_hom, transition_id_eq, Sheaf.eqToHom_hom]
  rfl

/-- The arrow of the pushed-down diagram attached to `f : B ⟶ A` in `Over i`: the transition of
`f`, pushed to the index `i`, followed by the transport along the system's own equalities. -/
public def pushedSystemMap (i : D.I) {A B : Over i} (f : B ⟶ A) :
    (abelianSheafPushforward.{v, u, w, t} D A.hom).obj (F.obj A.left) ⟶
      (abelianSheafPushforward.{v, u, w, t} D B.hom).obj (F.obj B.left) :=
  (abelianSheafPushforward.{v, u, w, t} D A.hom).map (pushforwardTransition D F f.left) ≫
    eqToHom (congrArg
      (fun G : Sheaf (D.J B.left) (Ab.{max u v w t}) ⥤ Sheaf (D.J i) (Ab.{max u v w t}) =>
        G.obj (F.obj B.left))
      ((abelianSheafPushforward_comp.{v, u, w, t} D f.left A.hom).trans
        (congrArg (fun m : B.left ⟶ i => abelianSheafPushforward.{v, u, w, t} D m) (Over.w f))))

/-- The arrow at an identity is the identity. -/
public theorem pushedSystemMap_id (i : D.I) (A : Over i) :
    pushedSystemMap D F i (𝟙 A) = 𝟙 _ := by
  dsimp only [pushedSystemMap]
  simp only [Over.id_left, pushforwardTransition_id_eqToHom, eqToHom_map, eqToHom_trans,
    eqToHom_refl]

/-- **The transition along a composite, as a sheaf morphism, in `eqToHom` form.** The companion of
`pushforwardTransition_id_eqToHom`, with `abelianSheafPushforward_comp` supplying the equality of
functors in place of `abelianSheafPushforwardCompIso`. -/
public theorem pushforwardTransition_comp_eqToHom {i j k : D.I} (a : i ⟶ j) (b : j ⟶ k) :
    pushforwardTransition D F (a ≫ b) =
      pushforwardTransition D F b ≫
        (abelianSheafPushforward.{v, u, w, t} D b).map (pushforwardTransition D F a) ≫
          eqToHom (congrArg
            (fun G : Sheaf (D.J i) (Ab.{max u v w t}) ⥤ Sheaf (D.J k) (Ab.{max u v w t}) =>
              G.obj (F.obj i))
            (abelianSheafPushforward_comp.{v, u, w, t} D a b)) := by
  apply Sheaf.hom_ext
  change transition D F (a ≫ b) =
    (pushforwardTransition D F b).hom ≫
      ((abelianSheafPushforward.{v, u, w, t} D b).map (pushforwardTransition D F a)).hom ≫
      (eqToHom (congrArg
        (fun G : Sheaf (D.J i) (Ab.{max u v w t}) ⥤ Sheaf (D.J k) (Ab.{max u v w t}) =>
          G.obj (F.obj i))
        (abelianSheafPushforward_comp.{v, u, w, t} D a b))).hom
  rw [transition_comp_eq]
  simp only [abelianSheafPushforward_map_hom, pushforwardTransition_hom, Sheaf.eqToHom_hom,
    Category.assoc]
  rfl

/-- Direct image along `f.left` and then `A.hom` is direct image along `B.hom`, for `f : B ⟶ A`
in `Over i`. -/
private theorem pushforward_comp_over_eq {i : D.I} {A B : Over i} (f : B ⟶ A) :
    abelianSheafPushforward.{v, u, w, t} D f.left ⋙
        abelianSheafPushforward.{v, u, w, t} D A.hom =
      abelianSheafPushforward.{v, u, w, t} D B.hom :=
  (abelianSheafPushforward_comp.{v, u, w, t} D f.left A.hom).trans
    (congrArg (fun m : B.left ⟶ i => abelianSheafPushforward.{v, u, w, t} D m) (Over.w f))

/-- The arrows of the pushed-down diagram compose. -/
public theorem pushedSystemMap_comp (i : D.I) {A B C : Over i} (f : B ⟶ A) (g : C ⟶ B) :
    pushedSystemMap D F i (g ≫ f) =
      pushedSystemMap D F i f ≫ pushedSystemMap D F i g := by
  dsimp only [pushedSystemMap]
  simp only [Over.comp_left, pushforwardTransition_comp_eqToHom, Functor.map_comp, eqToHom_map,
    Category.assoc, eqToHom_trans]
  rw [← Functor.comp_map,
    Functor.congr_hom (pushforward_comp_over_eq D f) (pushforwardTransition D F g.left)]
  simp only [Category.assoc, eqToHom_trans]

/-- **The diagram over `(Over i)ᵒᵖ` of the system's sheaves pushed down to the index `i`.** Every
value lives on the single site `D.J i`, so `CategoryTheory.Sheaf.Γ` applied to it is a diagram of
global sections with no further comparison needed.

The two laws are `pushedSystemMap_id` and `pushedSystemMap_comp`, which rest on the system's own
transition laws in `eqToHom` form; no `Iso.refl`-bodied comparison definition appears anywhere in
the construction. -/
public def pushedSystemDiagram (i : D.I) :
    (Over i)ᵒᵖ ⥤ Sheaf (D.J i) (Ab.{max u v w t}) where
  obj A := (abelianSheafPushforward.{v, u, w, t} D A.unop.hom).obj (F.obj A.unop.left)
  map f := pushedSystemMap D F i f.unop
  map_id A := pushedSystemMap_id D F i A.unop
  map_comp f g := pushedSystemMap_comp D F i f.unop g.unop

/-! ### The cocone at the global sections of the colimit sheaf -/

section Cocone

variable {C : Type w} [SmallCategory C] (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (K : Precoverage C) [∀ j, (uC j).IsContinuous (D.J j) K.toGrothendieck]
  (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w t}))

include hu in
/-- **Direct image to the colimit site, then down to the index, is direct image to the index.**
The mixed companion of `abelianSheafPushforward_comp`: the system's `hu` is an equality of
functors `u_a ⋙ uC j = uC i`, and direct image is precomposition, so the two composites are equal
functors. -/
public theorem pushforward_uC_comp {i j : D.I} (a : j ⟶ i) :
    (uC j).sheafPushforwardContinuous (Ab.{max u v w t}) (D.J j) K.toGrothendieck ⋙
        abelianSheafPushforward.{v, u, w, t} D a =
      (uC i).sheafPushforwardContinuous (Ab.{max u v w t}) (D.J i) K.toGrothendieck := by
  dsimp only [abelianSheafPushforward]
  simp only [← hu a]
  rfl

variable (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)

/-- The leg of the cocone at `A : Over i`: the colimit presentation's leg at the level `A.left`,
pushed down to the index `i`, followed by the transport of `pushforward_uC_comp`. -/
public def pushedSystemLeg (i : D.I) (A : Over i) :
    (abelianSheafPushforward.{v, u, w, t} D A.hom).obj (F.obj A.left) ⟶
      ((uC i).sheafPushforwardContinuous (Ab.{max u v w t}) (D.J i) K.toGrothendieck).obj 𝒢 :=
  (abelianSheafPushforward.{v, u, w, t} D A.hom).map (ObjectProperty.homMk (ι A.left)) ≫
    eqToHom (congrArg
      (fun G : Sheaf K.toGrothendieck (Ab.{max u v w t}) ⥤ Sheaf (D.J i) (Ab.{max u v w t}) =>
        G.obj 𝒢)
      (pushforward_uC_comp.{v, u, w, t} D uC hu K A.hom))

/-- **The legs of a compatible family, read as morphisms of sheaves.** The sheaf-level form of
`Stacks.WeakSites.ColimitSiteCohomology.IsCompatible`: the leg at the level `j` is the transition
of `a : k ⟶ j`, followed by the direct image of the leg at `k`, followed by the transport of
`pushforward_uC_comp`.

`IsCompatible` is a statement about maps of *presheaves*, and the three rewrites that turn the
underlying map of each factor into its presheaf form are `pushforwardTransition_hom`,
`abelianSheafPushforward_map_hom` and `Sheaf.eqToHom_hom`; the two transports that remain then
carry the same equality of presheaves and agree by proof irrelevance. No `Iso.refl`-bodied
comparison definition appears, so nothing here has to be unfolded. -/
public theorem sheafHomMk_leg_eq (hι : IsCompatible.{v, u, w, t} D uC hu F 𝒢.obj ι)
    {j k : D.I} (a : k ⟶ j) :
    (ObjectProperty.homMk (ι j) : F.obj j ⟶
        ((uC j).sheafPushforwardContinuous (Ab.{max u v w t}) (D.J j) K.toGrothendieck).obj 𝒢) =
      pushforwardTransition D F a ≫
        (abelianSheafPushforward.{v, u, w, t} D a).map (ObjectProperty.homMk (ι k)) ≫
          eqToHom (congrArg
            (fun G : Sheaf K.toGrothendieck (Ab.{max u v w t}) ⥤
                Sheaf (D.J j) (Ab.{max u v w t}) => G.obj 𝒢)
            (pushforward_uC_comp.{v, u, w, t} D uC hu K a)) := by
  apply Sheaf.hom_ext
  change ι j = _
  rw [hι a]
  simp only [ObjectProperty.FullSubcategory.comp_hom, pushforwardTransition_hom,
    abelianSheafPushforward_map_hom, Sheaf.eqToHom_hom]
  rfl

/-- **The legs of the pushed-down diagram are compatible with its arrows.** For `f : B ⟶ A` in
`Over i`, the arrow `pushedSystemMap` of `f` followed by the leg at `B` is the leg at `A`; that is,
the legs form a cocone on `pushedSystemDiagram`.

This is `sheafHomMk_leg_eq` at `f.left` and nothing else: the four transports the two sides carry
— the two of `pushforward_uC_comp` at `A.hom` and at `B.hom`, the one of
`abelianSheafPushforward_comp` inside `pushedSystemMap`, and the one `sheafHomMk_leg_eq`
introduces — telescope once `Functor.congr_hom` of the diagram's own equality of functors has
placed the direct image of the leg at `B` on the far side of the first of them. -/
public theorem pushedSystemLeg_naturality (hι : IsCompatible.{v, u, w, t} D uC hu F 𝒢.obj ι)
    (i : D.I) {A B : Over i} (f : B ⟶ A) :
    pushedSystemMap.{v, u, w, t} D F i f ≫
        pushedSystemLeg.{v, u, w, t} D F uC hu K 𝒢 ι i B =
      pushedSystemLeg.{v, u, w, t} D F uC hu K 𝒢 ι i A := by
  dsimp only [pushedSystemMap, pushedSystemLeg]
  rw [sheafHomMk_leg_eq D F uC hu K 𝒢 ι hι f.left]
  simp only [Functor.map_comp, eqToHom_map, Category.assoc, eqToHom_trans]
  rw [← Functor.comp_map, Functor.congr_hom (pushforward_comp_over_eq D f)]
  simp only [Category.assoc, eqToHom_trans]

end Cocone

/-! ### The cocone's legs on global sections, at the colimit site's vertex

`Stacks.ConstantSheaf.gammaCompPushforwardIsoAbOfMorphismOfSites` is stated at the single-universe
convention — both sites in `Type u` with coefficients `Ab.{u}` — so this section fixes the
inverse system at that convention, which is the one the geometric instantiations use
(`D : InverseSystemOfFiniteSites.{v, u, max u v w}` with coefficients `Ab.{max u v w}`).
-/

section GammaLeg

variable (Dn : InverseSystemOfFiniteSites.{v, u, max u v w}) {C : Type (max u v w)}
  [SmallCategory C] (uC : ∀ i, Dn.C i ⥤ C)
  (hu : ∀ {i j : Dn.I} (a : i ⟶ j), Dn.u a ⋙ uC i = uC j)
  (K : Precoverage C) [∀ j, (uC j).IsContinuous (Dn.J j) K.toGrothendieck]
  (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w}))
  (Fn : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, max u v w, max u v w} Dn)
  (ι : ∀ j, (Fn.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)

/-- **The leg of the cocone on global sections, with vertex the global sections of the colimit
sheaf.** `Sheaf.Γ` of `pushedSystemLeg` lands in `Γ_i((uC i)_* 𝒢)`; one application of
`Stacks.ConstantSheaf.gammaCompPushforwardIsoAbOfMorphismOfSites` at `uC i` moves the vertex to
`Γ_C(𝒢)`. The hypothesis is free at a geometric instantiation: `isMorphismOfSites` is a field of
`InverseSystemOfFiniteSites` for the transitions, and Stacks 0A35
(`InverseSystemOfFiniteSites.exists_isMorphismOfSites_sections_pullback_of_colimit`) supplies it
for the functors to the colimit site. -/
public def pushedSystemGammaLeg
    (hM : ∀ j, (uC j).IsMorphismOfSites (Dn.J j) K.toGrothendieck) (i : Dn.I) (A : Over i) :
    (Sheaf.Γ (Dn.J i) (Ab.{max u v w})).obj
        ((abelianSheafPushforward.{v, u, max u v w, max u v w} Dn A.hom).obj (Fn.obj A.left)) ⟶
      (Sheaf.Γ K.toGrothendieck (Ab.{max u v w})).obj 𝒢 :=
  (Sheaf.Γ (Dn.J i) (Ab.{max u v w})).map
      (pushedSystemLeg.{v, u, max u v w, max u v w} Dn Fn uC hu K 𝒢 ι i A) ≫
    (Stacks.ConstantSheaf.gammaCompPushforwardIsoAbOfMorphismOfSites
      (uC i) (Dn.J i) K.toGrothendieck (hM i)).hom.app 𝒢

/-- **The cocone of the pushed-down diagram on global sections, at `Γ_C(𝒢)`.**

The compatibility of the legs with the diagram is no longer carried: it is
`pushedSystemLeg_naturality`, and the only hypothesis left in its place is `hι`, the colimit
presentation's own `IsCompatible` for the family `ι`, which a consumer has as the first component
of `IsColimitPresentation`. -/
public def pushedSystemGammaCocone
    (hM : ∀ j, (uC j).IsMorphismOfSites (Dn.J j) K.toGrothendieck)
    (hι : IsCompatible.{v, u, max u v w, max u v w} Dn uC hu Fn 𝒢.obj ι)
    (i : Dn.I) :
    Cocone (pushedSystemDiagram.{v, u, max u v w, max u v w} Dn Fn i ⋙
      Sheaf.Γ (Dn.J i) (Ab.{max u v w})) where
  pt := (Sheaf.Γ K.toGrothendieck (Ab.{max u v w})).obj 𝒢
  ι :=
    { app A := pushedSystemGammaLeg Dn uC hu K 𝒢 Fn ι hM i A.unop
      naturality := by
        intro A B f
        dsimp only [pushedSystemGammaLeg, Functor.comp_map, pushedSystemDiagram]
        simp only [Functor.const_obj_map]
        rw [← Category.assoc, ← Functor.map_comp,
          pushedSystemLeg_naturality.{v, u, max u v w, max u v w} Dn Fn uC hu K 𝒢 ι hι i f.unop]
        exact (Category.comp_id _).symm }

end GammaLeg

/-! ### The legs read as maps out of the level global sections

`Stacks.WeakSites.ColimitSiteCohomology.abelianGlobalSections_colimit_pullback_of_colimit`
(Stacks 09YP in degree zero) takes the family of maps into `Γ_C(𝒢)` as a *parameter* `ρ` whose
source at a level `n` is `Γ_n(F_n)`, the global sections of the level itself, whereas the legs of
`pushedSystemGammaCocone` have source `Γ_i((u_a)^* F_n)`. The two are canonically isomorphic —
direct image along a morphism of sites does not change global sections — and this section records
that isomorphism and the resulting `ρ`.
-/

section GammaRho

variable (Dn : InverseSystemOfFiniteSites.{v, u, max u v w})

/-- **Global sections of a direct image along a transition functor are the global sections of the
level.** For `a : i ⟶ j` in the index category, `abelianSheafPushforward Dn a` is precomposition
with `Dn.u a : Dn.C j ⥤ Dn.C i`, and the `isMorphismOfSites` field of
`InverseSystemOfFiniteSites` says that functor is a morphism of sites, so
`Stacks.ConstantSheaf.gammaCompPushforwardIsoAbOfMorphismOfSites` applies and identifies
`Γ_j((u_a)^* F)` with `Γ_i(F)`, naturally in `F`.

The instance carried by the type of `abelianSheafPushforward` is `Dn.continuous a`, which is by
definition the `isContinuous` half of `Dn.isMorphismOfSites a`, so the body's type and the stated
type agree without transport. -/
public def gammaAbelianSheafPushforwardIso {i j : Dn.I} (a : i ⟶ j) :
    abelianSheafPushforward.{v, u, max u v w, max u v w} Dn a ⋙
        Sheaf.Γ (Dn.J j) (Ab.{max u v w}) ≅ Sheaf.Γ (Dn.J i) (Ab.{max u v w}) :=
  letI := Dn.continuous a
  Stacks.ConstantSheaf.gammaCompPushforwardIsoAbOfMorphismOfSites
    (Dn.u a) (Dn.J j) (Dn.J i) (Dn.isMorphismOfSites a)

variable {C : Type (max u v w)} [SmallCategory C] (uC : ∀ i, Dn.C i ⥤ C)
  (hu : ∀ {i j : Dn.I} (a : i ⟶ j), Dn.u a ⋙ uC i = uC j)
  (K : Precoverage C) [∀ j, (uC j).IsContinuous (Dn.J j) K.toGrothendieck]
  (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w}))
  (Fn : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, max u v w, max u v w} Dn)
  (ι : ∀ j, (Fn.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)

/-- **The leg of `pushedSystemGammaCocone` at `a : n ⟶ i`, read as a map out of the global
sections of the level `n`.** This is the shape the parameter `ρ` of
`Stacks.WeakSites.ColimitSiteCohomology.abelianGlobalSections_colimit_pullback_of_colimit`
has.

The first factor is `CategoryTheory.Sheaf.ΓPushforwardComparison`, *not* the inverse of
`gammaAbelianSheafPushforwardIso`, although the two agree. The two directions of that comparison
are not symmetric: this one is a map **into** a limit — global sections of the direct image are
the limit of its underlying presheaf — so it is `CategoryTheory.Limits.IsLimit.lift` of the cone
of restrictions, and its compatibility with restriction is the limit's `fac`, which is
`ΓRes_pushforwardComparison_pushedSystemLeg` below. Reading the same map as the inverse of the
isomorphism makes that compatibility unavailable: the isomorphism is built from the adjoint
description of `CategoryTheory.Sheaf.Γ` and relating the two descriptions costs a chain of
lemmas, of which the library has only `CategoryTheory.Sheaf.ΓHomEquiv_symm_app`. Proving the two
factorisations equal does not help either — both are maps into the same limit, so
`CategoryTheory.Limits.IsLimit.hom_ext` reduces that equality to the very compatibility at
issue. -/
public def pushedSystemGammaRho
    (hM : ∀ j, (uC j).IsMorphismOfSites (Dn.J j) K.toGrothendieck) (i : Dn.I) {n : Dn.I}
    (a : n ⟶ i) :
    (Sheaf.Γ (Dn.J n) (Ab.{max u v w})).obj (Fn.obj n) ⟶
      (Sheaf.Γ K.toGrothendieck (Ab.{max u v w})).obj 𝒢 :=
  letI := Dn.continuous a
  Sheaf.ΓPushforwardComparison (Dn.u a) (Dn.J i) (Dn.J n) (Ab.{max u v w}) (Fn.obj n) ≫
    pushedSystemGammaLeg Dn uC hu K 𝒢 Fn ι hM i (Over.mk a)

/-- **The level half of the restriction compatibility of `pushedSystemGammaRho`.** Restricting to
an object `V` of the level `i`, the composite of `CategoryTheory.Sheaf.ΓPushforwardComparison`
with `Sheaf.Γ` of `pushedSystemLeg` is the restriction of the original global section of the
level `A.left` to `(Dn.u A.hom).obj V`, followed by the leg at `V`.

This is the whole of the hypothesis `hρ` of
`Stacks.WeakSites.ColimitGlobalSections.abelianGlobalSections_colimit_pullback_of_colimit` except
for the last factor of `pushedSystemGammaLeg`, the comparison at `uC i`, whose behaviour on
restrictions is not available; see the docstring of `pushedSystemGammaRho`. The proof is
Mathlib's `CategoryTheory.Sheaf.ΓRes_naturality` followed by
`CategoryTheory.Sheaf.ΓRes_ΓPushforwardComparison`, both of which cost nothing. -/
public theorem ΓRes_pushforwardComparison_pushedSystemLeg (i : Dn.I) (A : Over i)
    (V : Dn.C i) :
    letI := Dn.continuous A.hom
    Sheaf.ΓPushforwardComparison (Dn.u A.hom) (Dn.J i) (Dn.J A.left) (Ab.{max u v w})
          (Fn.obj A.left) ≫
        (Sheaf.Γ (Dn.J i) (Ab.{max u v w})).map
            (pushedSystemLeg.{v, u, max u v w, max u v w} Dn Fn uC hu K 𝒢 ι i A) ≫
          Sheaf.ΓRes
            (((uC i).sheafPushforwardContinuous (Ab.{max u v w}) (Dn.J i)
              K.toGrothendieck).obj 𝒢) (op V) =
      Sheaf.ΓRes (Fn.obj A.left) (op ((Dn.u A.hom).obj V)) ≫
        (pushedSystemLeg.{v, u, max u v w, max u v w} Dn Fn uC hu K 𝒢 ι i A).hom.app (op V) := by
  let := Dn.continuous A.hom
  have key : ∀ f : ((Dn.u A.hom).sheafPushforwardContinuous (Ab.{max u v w}) (Dn.J i)
        (Dn.J A.left)).obj (Fn.obj A.left) ⟶
      ((uC i).sheafPushforwardContinuous (Ab.{max u v w}) (Dn.J i) K.toGrothendieck).obj 𝒢,
      Sheaf.ΓPushforwardComparison (Dn.u A.hom) (Dn.J i) (Dn.J A.left) (Ab.{max u v w})
            (Fn.obj A.left) ≫
          (Sheaf.Γ (Dn.J i) (Ab.{max u v w})).map f ≫
            Sheaf.ΓRes
              (((uC i).sheafPushforwardContinuous (Ab.{max u v w}) (Dn.J i)
                K.toGrothendieck).obj 𝒢) (op V) =
        Sheaf.ΓRes (Fn.obj A.left) (op ((Dn.u A.hom).obj V)) ≫ f.hom.app (op V) := by
    intro f
    rw [Sheaf.ΓRes_naturality, ← Category.assoc, Sheaf.ΓRes_ΓPushforwardComparison]
    rfl
  exact key _

end GammaRho

end Stacks.WeakSites.ColimitSiteCohomology



end
