module

public import Mathlib.Topology.Sheaves.Functors
public import StacksFrontier.Topology.Maps.Proper
public import StacksFrontier.Topology.Proper.Defs
public import StacksFrontier.Topology.Sheaves.ProperPushforward.BaseChangeFibre
public import StacksFrontier.Topology.Sheaves.ProperPushforward.GermPullbackStalk

/-!
# Proper base change for sheaves of sets

Let

```
X ×_Y Z --- g' ---> X
   |                |
   f'               f
   v                v
   Z  --- g ----->  Y
```

be a cartesian square of topological spaces, with `X ×_Y Z = Function.Pullback g f`,
`f' = Function.Pullback.fst` and `g' = Function.Pullback.snd`.  For a sheaf of sets `F` on `X`
there is a canonical base-change map of sheaves of sets on `Z`

`g⁻¹(f_*F) ⟶ f'_*((g')⁻¹F)`,

and it is an isomorphism as soon as `f` is proper.  This is
[Stacks, Tag 0D90](https://stacks.math.columbia.edu/tag/0D90).

## Main definitions

* `Stacks.Topology.ProperBaseChange.pullbackFst` and
  `Stacks.Topology.ProperBaseChange.pullbackSnd`: the two projections `X ×_Y Z ⟶ Z` and
  `X ×_Y Z ⟶ X`.
* `Stacks.Topology.ProperBaseChange.pushforwardGermAt`: the transfer of a germ of `f_*F` at
  `f x`, presented as a point of the total space of germs, to a germ of `F` at `x`.
* `Stacks.Topology.ProperBaseChange.baseChangeApp`: the base-change map on sections, and
  `Stacks.Topology.ProperBaseChange.baseChangeNatTrans`: the same as a morphism of presheaves.
* `Stacks.Topology.ProperBaseChange.properBaseChangeMap`: the base-change map
  `g⁻¹(f_*F) ⟶ f'_*((g')⁻¹F)`.
* `Stacks.Topology.ProperBaseChange.properBaseChangeIso`: the base-change map as an isomorphism
  `g⁻¹(f_*F) ≅ f'_*((g')⁻¹F)`, for `f` proper.
* `Stacks.Topology.ProperBaseChange.pullbackBaseMap`: the map `Z' ×_Y X ⟶ Z ×_Y X` of fibre
  products induced by a morphism `Z' ⟶ Z` of the base over `Y`.

## Main results

* `Stacks.Topology.ProperBaseChange.properBaseChangeMap_ofSection`: the base-change map sends
  the germwise pullback of `t ∈ (f_*F)(V)` to the germwise pullback of `t` along `g'`.  This
  identifies the map without unfolding it.
* `Stacks.Topology.ProperBaseChange.baseChangeApp_comap`: **the base-change map is natural in
  the base** — it commutes with pullback of germ-model sections along a morphism `Z' ⟶ Z` over
  `Y` and the induced map of fibre products.  Both maps are substitution into a germwise
  formula, so this holds by definitional unfolding.
* `Stacks.Topology.ProperBaseChange.bijective_stalkFunctor_map`: the base-change map is
  bijective on every stalk when `f` is proper.
* `Stacks.Topology.ProperBaseChange.isIso_properBaseChangeMap`: **Stacks 0D90** — the
  base-change map is an isomorphism when `f` is proper.
* `Stacks.Topology.ProperBaseChange.isClosedMap_pullbackFst`,
  `Stacks.Topology.ProperBaseChange.isCompact_preimage_singleton` and
  `Stacks.Topology.ProperBaseChange.separated_preimage_singleton`: the three consequences of
  properness that the proof uses, all derived from Stacks 005O (5).

## Implementation notes

The inverse images are the germ models `GermPullback.sheaf`, so a section of `g⁻¹(f_*F)` over
`W ⊆ Z` is a function `W → Germs (f_*F)` which is locally the germs of a single section of
`f_*F`, and similarly on `X ×_Y Z`.  The base-change map is therefore written down germwise:
at a point `q` of `f'⁻¹(W)` the value of `σ` at `f' q` is a germ of `f_*F` based at
`g (f' q) = f (g' q)`, and `pushforwardGermAt` turns it into a germ of `F` at `g' q`.  The only
dependent-type work is the transport of the base point of that germ, isolated in
`pushforwardGermAt` and its two computation lemmas.

Invertibility is checked on stalks.  At `z : Z`:

* every germ of `g⁻¹(f_*F)` at `z` is the germ of a germwise pullback of some `t ∈ (f_*F)(V)`,
  and two such germs agree exactly when the germs of the `t` agree
  (`GermPullback.exists_ofSection_germ_eq` and `GermPullback.germ_ofSection_eq_iff`, the
  computation of the stalks of an inverse image);
* the germs of `f_*F` at `g z` are the sections of `F` on the fibre `f⁻¹(g z)`, which is
  Stacks 09V5 in degree zero (`exists_isOpen_mem_restrictToSubset_eq_of_isClosedMap` and its
  injectivity counterpart, in `Stacks.Topology.SectionsOnQuasiCompactSubset`);
* a section of `(g')⁻¹F` near the fibre `f'⁻¹(z)` restricts to a section of `F` on `f⁻¹(g z)`
  (`Stacks.Topology.ProperBaseChange.restrictToFibre`), and two sections of `(g')⁻¹F` agreeing
  on `f'⁻¹(z)` agree on `f'⁻¹(W)` for some neighbourhood `W` of `z`, because the agreement
  locus is open (`GermPullback.isOpen_agreeSet`) and `f'` is closed.

Properness of `f` enters only through its definition, Stacks 005O (5), in four places: `f'` is a
closed map because `f` is universally closed; `f` itself is closed for the same reason; the
fibres of `f` are quasi-compact by Stacks 005R; and distinct points of a fibre are separated by
disjoint opens because `f` is a separated map.  None of these is assumed: all four are derived.

All three spaces must live in one universe, because `GermPullback.Germs` is a sigma type over
the points of the space.

## References

* [Stacks, Tag 005O](https://stacks.math.columbia.edu/tag/005O)
* [Stacks, Tag 005R](https://stacks.math.columbia.edu/tag/005R)
* [Stacks, Tag 09V5](https://stacks.math.columbia.edu/tag/09V5)
* [Stacks, Tag 0D90](https://stacks.math.columbia.edu/tag/0D90)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.Topology.ProperBaseChange

open Stacks.Topology.SectionsOnQuasiCompactSubset

variable {X Y Z : TopCat.{u}}

/-! ### The projections of the fibre product -/

/-- The first projection `X ×_Y Z ⟶ Z` of the cartesian square, as a morphism of topological
spaces; this is the map `f'` of Stacks 0D90. -/
def pullbackFst (f : X ⟶ Y) (g : Z ⟶ Y) : pullbackSpace (⇑g) (⇑f) ⟶ Z :=
  TopCat.ofHom ⟨Function.Pullback.fst, continuous_pullbackFst⟩

/-- `pullbackFst` is the first projection (Stacks 0D90). -/
@[simp]
lemma pullbackFst_apply (f : X ⟶ Y) (g : Z ⟶ Y) (p : ↥(pullbackSpace (⇑g) (⇑f))) :
    pullbackFst f g p = Function.Pullback.fst p := rfl

/-- The second projection `X ×_Y Z ⟶ X` of the cartesian square, as a morphism of topological
spaces; this is the map `g'` of Stacks 0D90, along which the inverse image `(g')⁻¹F` is taken. -/
def pullbackSnd (f : X ⟶ Y) (g : Z ⟶ Y) : pullbackSpace (⇑g) (⇑f) ⟶ X :=
  TopCat.ofHom ⟨Function.Pullback.snd, continuous_pullbackSnd⟩

/-- `pullbackSnd` is the second projection (Stacks 0D90). -/
@[simp]
lemma pullbackSnd_apply (f : X ⟶ Y) (g : Z ⟶ Y) (p : ↥(pullbackSpace (⇑g) (⇑f))) :
    pullbackSnd f g p = Function.Pullback.snd p := rfl

/-- The second projection of a point of `f'⁻¹(V)` lands in the preimage under `f` of any open
`V` of `Y` containing the image of `W` under `g` (Stacks 0D90). -/
lemma snd_mem_map_of_mem {f : X ⟶ Y} {g : Z ⟶ Y} {W : Opens Z} {V : Opens Y}
    (hV : ∀ z : W, g z.1 ∈ V) (q : ↥((Opens.map (pullbackFst f g)).obj W)) :
    Function.Pullback.snd q.1 ∈ (Opens.map f).obj V := by
  have h : (⇑g) (Function.Pullback.fst q.1) = (⇑f) (Function.Pullback.snd q.1) := q.1.2
  have hmem : (⇑g) (Function.Pullback.fst q.1) ∈ V := hV ⟨Function.Pullback.fst q.1, q.2⟩
  rwa [h] at hmem

/-! ### Transfer of a germ of a pushforward -/

/-- A germ of `f_*F`, presented as a point `ξ` of the total space of germs of `f_*F` whose base
point is `f x`, determines a germ of `F` at `x`: apply
`TopCat.Presheaf.stalkPushforward`.  This is the germwise form of the counit
`f⁻¹f_*F ⟶ F`, and the only place where the base point of a germ has to be transported
(Stacks 0D90). -/
def pushforwardGermAt (f : X ⟶ Y) (F : X.Presheaf (Type u))
    (ξ : GermPullback.Germs (f _* F)) (x : ↥X) (h : ξ.1 = f x) : F.stalk x :=
  TopCat.Presheaf.stalkPushforward (Type u) f F x (cast (congrArg (f _* F).stalk h) ξ.2)

/-- `pushforwardGermAt` depends only on the germ, not on the proof that its base point is
`f x` (Stacks 0D90). -/
lemma pushforwardGermAt_congr (f : X ⟶ Y) (F : X.Presheaf (Type u))
    {ξ ζ : GermPullback.Germs (f _* F)} (he : ξ = ζ) (x : ↥X) (h : ξ.1 = f x) (h' : ζ.1 = f x) :
    pushforwardGermAt f F ξ x h = pushforwardGermAt f F ζ x h' := by
  subst he
  rfl

/-- `pushforwardGermAt` sends the germ at `f x` of a section `t` of `f_*F` on `V` to the germ of
`t` at `x`, viewed as a section of `F` on `f⁻¹(V)` (Stacks 0D90). -/
lemma pushforwardGermAt_mk (f : X ⟶ Y) (F : X.Presheaf (Type u)) (x : ↥X) {V : Opens Y}
    (hx : f x ∈ V) (t : (f _* F).obj (op V)) :
    pushforwardGermAt f F ⟨f x, (f _* F).germ V (f x) hx t⟩ x rfl
      = F.germ ((Opens.map f).obj V) x hx t :=
  TopCat.Presheaf.stalkPushforward_germ_apply (Type u) f F V x hx t

/-- A germ of `f_*F` which happens to be the germ of a section `t` of `f_*F` on `V` at `f x` is
transferred by `pushforwardGermAt` to the germ of `t` at `x` (Stacks 0D90). -/
lemma pushforwardGermAt_eq_germ (f : X ⟶ Y) (F : X.Presheaf (Type u))
    {ξ : GermPullback.Germs (f _* F)} (x : ↥X) (h : ξ.1 = f x) {V : Opens Y} (hx : f x ∈ V)
    (t : (f _* F).obj (op V)) (he : ξ = ⟨f x, (f _* F).germ V (f x) hx t⟩) :
    pushforwardGermAt f F ξ x h = F.germ ((Opens.map f).obj V) x hx t :=
  (pushforwardGermAt_congr f F he x h rfl).trans (pushforwardGermAt_mk f F x hx t)

/-! ### The base-change map -/

/-- The base-change map on sections: a section `σ` of `g⁻¹(f_*F)` on `W ⊆ Z` goes to the section
of `(g')⁻¹F` on `f'⁻¹(W)` whose value at `q` is the germ of `F` at `g' q` obtained from the germ
of `f_*F` which is the value of `σ` at `f' q` (Stacks 0D90). -/
def baseChangeApp (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Presheaf (Type u)) {W : Opens Z}
    (σ : (GermPullback.sheaf (⇑g) (f _* F)).presheaf.obj (op W)) :
    (GermPullback.sheaf (Function.Pullback.snd) F).presheaf.obj
      (op ((Opens.map (pullbackFst f g)).obj W)) := by
  refine ⟨fun q ↦ ⟨Function.Pullback.snd q.1,
      pushforwardGermAt f F (σ.1 ⟨Function.Pullback.fst q.1, q.2⟩) (Function.Pullback.snd q.1)
        ((GermPullback.fst_val σ ⟨Function.Pullback.fst q.1, q.2⟩).trans q.1.2)⟩, fun q ↦ ?_⟩
  obtain ⟨W₀, hz₀, i, V, hV, t, ht⟩ :=
    GermPullback.exists_repr σ (show Function.Pullback.fst q.1 ∈ W from q.2)
  refine ⟨(Opens.map (pullbackFst f g)).obj W₀, hz₀, homOfLE (fun x hx ↦ i.le hx),
    (Opens.map f).obj V, fun r ↦ snd_mem_map_of_mem hV r, t, fun r ↦ ?_⟩
  have hxV : (⇑f) (Function.Pullback.snd r.1) ∈ V := snd_mem_map_of_mem hV r
  have he : σ.1 ⟨Function.Pullback.fst r.1, i.le r.2⟩ =
      (⟨(⇑f) (Function.Pullback.snd r.1),
        (f _* F).germ V ((⇑f) (Function.Pullback.snd r.1)) hxV t⟩ :
          GermPullback.Germs (f _* F)) :=
    (ht ⟨Function.Pullback.fst r.1, r.2⟩).trans
      (GermPullback.Germs.mk_eq_mk t r.1.2 _ hxV)
  exact congrArg (fun ζ ↦ (⟨Function.Pullback.snd r.1, ζ⟩ : GermPullback.Germs F))
    (pushforwardGermAt_eq_germ f F (Function.Pullback.snd r.1) _ hxV t he)

/-- The value of the base-change map at a point `q` of `f'⁻¹(W)` (Stacks 0D90). -/
@[simp]
lemma baseChangeApp_val (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Presheaf (Type u)) {W : Opens Z}
    (σ : (GermPullback.sheaf (⇑g) (f _* F)).presheaf.obj (op W))
    (q : ↥((Opens.map (pullbackFst f g)).obj W)) :
    (baseChangeApp f g F σ).1 q = ⟨Function.Pullback.snd q.1,
      pushforwardGermAt f F (σ.1 ⟨Function.Pullback.fst q.1, q.2⟩) (Function.Pullback.snd q.1)
        ((GermPullback.fst_val σ ⟨Function.Pullback.fst q.1, q.2⟩).trans q.1.2)⟩ := rfl

/-- The base-change map commutes with restriction to a smaller open (Stacks 0D90). -/
lemma baseChangeApp_map (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Presheaf (Type u)) {W W' : Opens Z}
    (i : W' ⟶ W) (σ : (GermPullback.sheaf (⇑g) (f _* F)).presheaf.obj (op W)) :
    baseChangeApp f g F ((GermPullback.sheaf (⇑g) (f _* F)).presheaf.map i.op σ) =
      (GermPullback.sheaf (Function.Pullback.snd) F).presheaf.map
        ((Opens.map (pullbackFst f g)).map i).op (baseChangeApp f g F σ) := rfl

/-- **The base-change map on germwise pullbacks.** The base-change map sends the germwise
pullback along `g` of a section `t` of `f_*F` on `V` to the germwise pullback along `g'` of `t`,
viewed as a section of `F` on `f⁻¹(V)`.  Together with the fact that every section of an inverse
image is locally a germwise pullback, this identifies the base-change map (Stacks 0D90). -/
lemma baseChangeApp_ofSection (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Presheaf (Type u)) {W : Opens Z}
    {V : Opens Y} (hV : ∀ z : W, g z.1 ∈ V) (t : (f _* F).obj (op V)) :
    baseChangeApp f g F (GermPullback.ofSection hV t) =
      GermPullback.ofSection (g := Function.Pullback.snd) (𝒢 := F)
        (V := (Opens.map f).obj V) (fun r ↦ snd_mem_map_of_mem hV r) t := by
  refine GermPullback.ext fun q ↦ ?_
  have hxV : (⇑f) (Function.Pullback.snd q.1) ∈ V := snd_mem_map_of_mem hV q
  have he : (GermPullback.ofSection hV t).1 ⟨Function.Pullback.fst q.1, q.2⟩ =
      (⟨(⇑f) (Function.Pullback.snd q.1),
        (f _* F).germ V ((⇑f) (Function.Pullback.snd q.1)) hxV t⟩ :
          GermPullback.Germs (f _* F)) :=
    (GermPullback.ofSection_val hV t ⟨Function.Pullback.fst q.1, q.2⟩).trans
      (GermPullback.Germs.mk_eq_mk t q.1.2 _ hxV)
  exact congrArg (fun ζ ↦ (⟨Function.Pullback.snd q.1, ζ⟩ : GermPullback.Germs F))
    (pushforwardGermAt_eq_germ f F (Function.Pullback.snd q.1) _ hxV t he)

/-- The base-change map as a morphism of presheaves of sets on `Z` (Stacks 0D90). -/
def baseChangeNatTrans (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Presheaf (Type u)) :
    (GermPullback.sheaf (⇑g) (f _* F)).presheaf ⟶
      (pullbackFst f g) _* (GermPullback.sheaf (Function.Pullback.snd) F).presheaf where
  app W := TypeCat.ofHom (baseChangeApp f g F (W := unop W))
  naturality := by
    intro W W' i
    ext σ
    exact baseChangeApp_map f g F i.unop σ

/-- **The base-change map.** The canonical morphism of sheaves of sets on `Z`
`g⁻¹(f_*F) ⟶ f'_*((g')⁻¹F)` attached to the cartesian square.  It is an isomorphism when `f` is
proper, which is Stacks 0D90. -/
def properBaseChangeMap (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Sheaf (Type u)) :
    GermPullback.sheaf (⇑g) (f _* F.presheaf) ⟶
      (TopCat.Sheaf.pushforward (Type u) (pullbackFst f g)).obj
        (GermPullback.sheaf (Function.Pullback.snd) F.presheaf) :=
  ObjectProperty.homMk (baseChangeNatTrans f g F.presheaf)

/-- The underlying morphism of presheaves of the base-change map (Stacks 0D90). -/
@[simp]
lemma properBaseChangeMap_val (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Sheaf (Type u)) :
    (properBaseChangeMap f g F).1 = baseChangeNatTrans f g F.presheaf := rfl

/-- The base-change map sends the germwise pullback along `g` of a section `t` of `f_*F` on `V`
to the germwise pullback of `t` along `g'` (Stacks 0D90). -/
lemma properBaseChangeMap_ofSection (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Sheaf (Type u))
    {W : Opens Z} {V : Opens Y} (hV : ∀ z : W, g z.1 ∈ V)
    (t : (f _* F.presheaf).obj (op V)) :
    (properBaseChangeMap f g F).1.app (op W) (GermPullback.ofSection hV t) =
      GermPullback.ofSection (g := Function.Pullback.snd) (𝒢 := F.presheaf)
        (V := (Opens.map f).obj V) (fun r ↦ snd_mem_map_of_mem hV r) t :=
  baseChangeApp_ofSection f g F.presheaf hV t

/-! ### Functoriality of the base-change map in the base -/

variable {Z' : TopCat.{u}}

/-- **The map of fibre products induced by a morphism of the base.** A morphism `k : Z' ⟶ Z`
over `Y` induces `Z' ×_Y X ⟶ Z ×_Y X`, acting as `k` on the first and as the identity on the
second coordinate (Stacks 0D90). -/
def pullbackBaseMap (f : X ⟶ Y) {g : Z ⟶ Y} {g' : Z' ⟶ Y} (k : Z' ⟶ Z)
    (hk : ∀ z, (⇑g) ((⇑k) z) = (⇑g') z) :
    pullbackSpace (⇑g') (⇑f) ⟶ pullbackSpace (⇑g) (⇑f) :=
  TopCat.ofHom
    ⟨fun p => ⟨((⇑k) p.1.1, p.1.2), (hk p.1.1).trans p.2⟩,
      Continuous.subtype_mk
        ((k.hom.continuous.comp (continuous_fst.comp continuous_subtype_val)).prodMk
          (continuous_snd.comp continuous_subtype_val)) _⟩

/-- The induced map of fibre products is `k` in the first coordinate (Stacks 0D90). -/
@[simp]
lemma pullbackBaseMap_fst (f : X ⟶ Y) {g : Z ⟶ Y} {g' : Z' ⟶ Y} (k : Z' ⟶ Z)
    (hk : ∀ z, (⇑g) ((⇑k) z) = (⇑g') z) (p : ↥(pullbackSpace (⇑g') (⇑f))) :
    Function.Pullback.fst (pullbackBaseMap f k hk p) = (⇑k) (Function.Pullback.fst p) := rfl

/-- The induced map of fibre products is the identity in the second coordinate
(Stacks 0D90). -/
@[simp]
lemma pullbackBaseMap_snd (f : X ⟶ Y) {g : Z ⟶ Y} {g' : Z' ⟶ Y} (k : Z' ⟶ Z)
    (hk : ∀ z, (⇑g) ((⇑k) z) = (⇑g') z) (p : ↥(pullbackSpace (⇑g') (⇑f))) :
    Function.Pullback.snd (pullbackBaseMap f k hk p) = Function.Pullback.snd p := rfl

/-- The induced map of fibre products commutes with the first projections (Stacks 0D90). -/
lemma pullbackBaseMap_comp_pullbackFst (f : X ⟶ Y) {g : Z ⟶ Y} {g' : Z' ⟶ Y} (k : Z' ⟶ Z)
    (hk : ∀ z, (⇑g) ((⇑k) z) = (⇑g') z) :
    pullbackBaseMap f k hk ≫ pullbackFst f g = pullbackFst f g' ≫ k :=
  rfl

/-- The induced map of fibre products commutes with the second projections (Stacks 0D90). -/
lemma pullbackBaseMap_comp_pullbackSnd (f : X ⟶ Y) {g : Z ⟶ Y} {g' : Z' ⟶ Y} (k : Z' ⟶ Z)
    (hk : ∀ z, (⇑g) ((⇑k) z) = (⇑g') z) :
    pullbackBaseMap f k hk ≫ pullbackSnd f g = pullbackSnd f g' :=
  rfl

/-- **The base-change map is natural in the base.** Pulling a section of `g⁻¹(f_*F)` back along
a morphism `k : Z' ⟶ Z` over `Y` and then applying the base-change map for `g'` is the same as
applying the base-change map for `g` and pulling the result back along the induced map of fibre
products.  Both `GermPullback.comap` and the base-change map are given by substitution into a
germwise formula, so the two sides are literally the same function (Stacks 0D90). -/
lemma baseChangeApp_comap (f : X ⟶ Y) {g : Z ⟶ Y} {g' : Z' ⟶ Y} (k : Z' ⟶ Z)
    (hk : ∀ z, (⇑g) ((⇑k) z) = (⇑g') z) (F : X.Presheaf (Type u))
    {W : Opens Z} {W' : Opens Z'} (hW : ∀ z : W', (⇑k) z.1 ∈ W)
    (σ : (GermPullback.sheaf (⇑g) (f _* F)).presheaf.obj (op W)) :
    baseChangeApp f g' F (GermPullback.comap k.hom.continuous (fun z => (hk z).symm) hW σ) =
      GermPullback.comap (pullbackBaseMap f k hk).hom.continuous (fun _ => rfl)
        (fun q => hW ⟨Function.Pullback.fst q.1, q.2⟩) (baseChangeApp f g F σ) :=
  rfl

/-! ### Properness of `f` and its consequences -/

/-- The base change `f' : X ×_Y Z → Z` of a proper map `f` is a closed map: this is Stacks
005O (4), universal closedness of `f`, applied to `g`.  No translation is needed, because the
fibre product appearing in that definition is the one used here (Stacks 0D90). -/
lemma isClosedMap_pullbackFst (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (⇑f)) :
    IsClosedMap (⇑(pullbackFst f g)) :=
  hf.2 ↥Z (⇑g) g.hom.continuous

/-- A proper map is closed: base change along the identity recovers `f` (Stacks 005O). -/
lemma isClosedMap_of_isProperMap (f : X ⟶ Y)
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (⇑f)) : IsClosedMap (⇑f) :=
  hf.2.isClosedMap f.hom.continuous

/-- The fibres of a proper map are quasi-compact: the implication (3) ⇒ (4) of Stacks 005R,
applied to universal closedness, Stacks 005O (4). -/
lemma isCompact_preimage_singleton (f : X ⟶ Y)
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (⇑f)) (y : ↥Y) :
    IsCompact ((⇑f) ⁻¹' {y}) := by
  have huc : IsUniversallyClosed (⇑f) := fun T _ gg hgg ↦ hf.2 T gg hgg
  have h4 : IsClosedMap (⇑f) ∧ ∀ y : ↥Y, IsQuasiCompactSubset ((⇑f) ⁻¹' {y}) :=
    ((isProperMap_tfae (⇑f) f.hom.continuous).out 3 4).mp huc
  exact h4.2 y

/-- Two distinct points in one fibre of a proper map are separated by disjoint open subsets of
the source: this is separatedness of `f`, Stacks 005O (5) and Stacks 0CY1. -/
lemma separated_preimage_singleton (f : X ⟶ Y)
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (⇑f)) (y : ↥Y) :
    ∀ x ∈ ((⇑f) ⁻¹' {y}), ∀ x' ∈ ((⇑f) ⁻¹' {y}), x ≠ x' →
      ∃ A B : Set ↥X, IsOpen A ∧ IsOpen B ∧ x ∈ A ∧ x' ∈ B ∧ Disjoint A B :=
  fun x hx x' hx' hne ↦
    hf.1 x x' (by rw [show (⇑f) x = y from hx, show (⇑f) x' = y from hx']) hne

/-! ### The base-change map on stalks -/

/-- The fibre inclusion over `z` lands in `f'⁻¹(W)` for every open `W` containing `z`
(Stacks 0D90). -/
lemma fibreInclusion_mem_map {f : X ⟶ Y} {g : Z ⟶ Y} {W : Opens Z} {z : ↥Z} (hz : z ∈ W)
    (x : ((⇑f) ⁻¹' {(⇑g) z} : Set ↥X)) :
    fibreInclusion (⇑f) (⇑g) z x ∈ (Opens.map (pullbackFst f g)).obj W := hz

/-- A point of the fibre product lying over `z` is the fibre inclusion of its second projection
(Stacks 0D90). -/
lemma eq_fibreInclusion {f : X ⟶ Y} {g : Z ⟶ Y} {z : ↥Z}
    {p : ↥(pullbackSpace (⇑g) (⇑f))} (hp : Function.Pullback.fst p = z) :
    p = fibreInclusion (⇑f) (⇑g) z ⟨Function.Pullback.snd p, snd_mem_preimage_of_fst_eq hp⟩ :=
  Subtype.ext (Prod.ext hp rfl)

/-- The base-change map carries the germ at `z` of the germwise pullback of `t ∈ (f_*F)(V)` to
the germ at `z` of the germwise pullback of `t` along `g'` (Stacks 0D90). -/
lemma stalkFunctor_map_germ_ofSection (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Sheaf (Type u)) {z : ↥Z}
    {V : Opens Y} {W : Opens Z} (hzW : z ∈ W) (hV : ∀ x : W, g x.1 ∈ V)
    (t : (f _* F.presheaf).obj (op V)) :
    (TopCat.Presheaf.stalkFunctor (Type u) z).map (properBaseChangeMap f g F).1
        ((GermPullback.sheaf (⇑g) (f _* F.presheaf)).presheaf.germ W z hzW
          (GermPullback.ofSection hV t))
      = ((pullbackFst f g) _*
          (GermPullback.sheaf (Function.Pullback.snd) F.presheaf).presheaf).germ W z hzW
          (GermPullback.ofSection (Z := pullbackSpace (⇑g) (⇑f)) (Y := X)
            (g := Function.Pullback.snd) (𝒢 := F.presheaf)
            (W := (Opens.map (pullbackFst f g)).obj W) (V := (Opens.map f).obj V)
            (fun r ↦ snd_mem_map_of_mem hV r) t) := by
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  exact congrArg
    (fun ρ ↦ ((pullbackFst f g) _*
      (GermPullback.sheaf (Function.Pullback.snd) F.presheaf).presheaf).germ W z hzW ρ)
    (properBaseChangeMap_ofSection f g F hV t)

/-- **Injectivity of the base-change map on stalks.** Two germs of `g⁻¹(f_*F)` at `z` with the
same image are germs of germwise pullbacks of sections `t`, `t'` of `f_*F`, whose families of
germs along the fibre `f⁻¹(g z)` then agree; by Stacks 09V5 in degree zero, `t` and `t'` already
agree on the preimage of a neighbourhood of `g z` (Stacks 0D90). -/
lemma injective_stalkFunctor_map (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Sheaf (Type u))
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (⇑f)) (z : ↥Z) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor (Type u) z).map
      (properBaseChangeMap f g F).1) := by
  intro a a' hEq
  obtain ⟨V, W, hzW, hV, t, rfl⟩ := GermPullback.exists_ofSection_germ_eq a
  obtain ⟨V', W', hzW', hV', t', rfl⟩ := GermPullback.exists_ofSection_germ_eq a'
  rw [stalkFunctor_map_germ_ofSection f g F hzW hV t,
    stalkFunctor_map_germ_ofSection f g F hzW' hV' t'] at hEq
  have hgzV : (⇑g) z ∈ V := hV ⟨z, hzW⟩
  have hgzV' : (⇑g) z ∈ V' := hV' ⟨z, hzW'⟩
  obtain ⟨W₂, hzW₂, j, j', hj⟩ :=
    ((pullbackFst f g) _*
      (GermPullback.sheaf (Function.Pullback.snd) F.presheaf).presheaf).germ_eq z hzW hzW' _ _ hEq
  have hrestr : restrictToSubset F.presheaf (preimage_singleton_subset_comap f.hom hgzV) t
      = restrictToSubset F.presheaf (preimage_singleton_subset_comap f.hom hgzV') t' :=
    GermPullback.ext fun w ↦ congrArg
      (fun ρ ↦ ρ.1 ⟨fibreInclusion (⇑f) (⇑g) z w.1, fibreInclusion_mem_map hzW₂ w.1⟩) hj
  obtain ⟨V'', hzV'', hleV, hleV', heq⟩ :=
    exists_isOpen_mem_map_eq_of_restrictToSubset_eq_of_isClosedMap F f.hom
      (isClosedMap_of_isProperMap f hf) hgzV hgzV' t t' hrestr
  exact (GermPullback.germ_ofSection_eq_iff g.hom.continuous hzW hzW' hV hV' t t').2
    (TopCat.Presheaf.germ_ext (f _* F.presheaf) V'' hzV'' (homOfLE hleV) (homOfLE hleV') heq)

/-- Two sections of `(g')⁻¹F` on `f'⁻¹(W₀)` which agree along the fibre `f'⁻¹(z)` agree on
`f'⁻¹(W₃)` for some open neighbourhood `W₃` of `z`, when `f` is proper (Stacks 0D90). -/
lemma exists_isOpen_preimage_subset_agreeSet (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Presheaf (Type u))
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (⇑f)) {z : ↥Z} {W₀ : Opens Z}
    (hzW₀ : z ∈ W₀) (σ₁ σ₂ : (GermPullback.sheaf (Function.Pullback.snd) F).presheaf.obj
      (op ((Opens.map (pullbackFst f g)).obj W₀)))
    (hagree : ∀ (p : ↥(pullbackSpace (⇑g) (⇑f))) (_ : Function.Pullback.fst p = z)
      (hmem : p ∈ (Opens.map (pullbackFst f g)).obj W₀), σ₁.1 ⟨p, hmem⟩ = σ₂.1 ⟨p, hmem⟩) :
    ∃ W₃ : Set ↥Z, IsOpen W₃ ∧ z ∈ W₃ ∧ (⇑(pullbackFst f g)) ⁻¹' W₃ ⊆
      {p | ∃ hp : p ∈ (Opens.map (pullbackFst f g)).obj W₀, σ₁.1 ⟨p, hp⟩ = σ₂.1 ⟨p, hp⟩} := by
  have hopen : IsOpen {p : ↥(pullbackSpace (⇑g) (⇑f)) |
      ∃ hp : p ∈ (Opens.map (pullbackFst f g)).obj W₀, σ₁.1 ⟨p, hp⟩ = σ₂.1 ⟨p, hp⟩} :=
    GermPullback.isOpen_agreeSet continuous_pullbackSnd σ₁ σ₂
  refine exists_isOpen_preimage_subset_of_isClosedMap (isClosedMap_pullbackFst f g hf) hopen
    fun p hp ↦ ?_
  have hpz : Function.Pullback.fst p = z := hp
  exact ⟨show Function.Pullback.fst p ∈ W₀ by rwa [hpz], hagree p hpz _⟩

/-- **Surjectivity of the base-change map on stalks.** A germ of `f'_*((g')⁻¹F)` at `z` is
represented by a section `τ` of `(g')⁻¹F` on `f'⁻¹(W)`; restricting `τ` to the fibre `f'⁻¹(z)`
and extending by Stacks 09V5 in degree zero produces a section `s` of `F` on the preimage of a
neighbourhood `V` of `g z`.  The germwise pullback of `s` and `τ` then agree on the fibre, hence,
the agreement locus being open and `f'` closed, on `f'⁻¹(W₃)` for some neighbourhood `W₃` of `z`
(Stacks 0D90). -/
lemma surjective_stalkFunctor_map (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Sheaf (Type u))
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (⇑f)) (z : ↥Z) :
    Function.Surjective ((TopCat.Presheaf.stalkFunctor (Type u) z).map
      (properBaseChangeMap f g F).1) := by
  intro b
  obtain ⟨W, hzW, τ, rfl⟩ :=
    ((pullbackFst f g) _*
      (GermPullback.sheaf (Function.Pullback.snd) F.presheaf).presheaf).exists_germ_eq b
  obtain ⟨V, hzV, s, hs⟩ :=
    exists_isOpen_mem_restrictToSubset_eq_of_isClosedMap F f.hom
      (isClosedMap_of_isProperMap f hf) ((⇑g) z) (isCompact_preimage_singleton f hf _)
      (separated_preimage_singleton f hf _)
      (restrictToFibre F.presheaf z (fun x ↦ fibreInclusion_mem_map hzW x) τ)
  set W₀ : Opens Z := W ⊓ GermPullback.preimageOpens g.hom.continuous V
  have hzW₀ : z ∈ W₀ := ⟨hzW, hzV⟩
  have hV₀ : ∀ w : W₀, (⇑g) w.1 ∈ V := fun w ↦ w.2.2
  refine ⟨(GermPullback.sheaf (⇑g) (f _* F.presheaf)).presheaf.germ W₀ z hzW₀
    (GermPullback.ofSection hV₀ s), ?_⟩
  rw [stalkFunctor_map_germ_ofSection f g F hzW₀ hV₀ s]
  set σ₁ := GermPullback.ofSection (g := Function.Pullback.snd) (𝒢 := F.presheaf)
    (V := (Opens.map f).obj V) (fun r ↦ snd_mem_map_of_mem hV₀ r) s
  set σ₂ := (GermPullback.sheaf (Function.Pullback.snd) F.presheaf).presheaf.map
    ((Opens.map (pullbackFst f g)).map (homOfLE (inf_le_left : W₀ ≤ W))).op τ
  -- The two sections agree at every point of the fibre `f'⁻¹(z)`.
  have hagree : ∀ (p : ↥(pullbackSpace (⇑g) (⇑f))) (hp : Function.Pullback.fst p = z)
      (hmem : p ∈ (Opens.map (pullbackFst f g)).obj W₀),
      σ₁.1 ⟨p, hmem⟩ = σ₂.1 ⟨p, hmem⟩ := by
    intro p hp hmem
    have hx : Function.Pullback.snd p ∈ ((⇑f) ⁻¹' {(⇑g) z} : Set ↥X) :=
      snd_mem_preimage_of_fst_eq hp
    calc σ₁.1 ⟨p, hmem⟩
        = (restrictToSubset F.presheaf (preimage_singleton_subset_comap f.hom hzV) s).1
            ⟨⟨Function.Pullback.snd p, hx⟩, trivial⟩ := rfl
      _ = (restrictToFibre F.presheaf z (fun x ↦ fibreInclusion_mem_map hzW x) τ).1
            ⟨⟨Function.Pullback.snd p, hx⟩, trivial⟩ :=
          congrArg (fun ρ ↦ ρ.1 ⟨⟨Function.Pullback.snd p, hx⟩, trivial⟩) hs
      _ = τ.1 ⟨fibreInclusion (⇑f) (⇑g) z ⟨Function.Pullback.snd p, hx⟩,
            fibreInclusion_mem_map hzW ⟨Function.Pullback.snd p, hx⟩⟩ := rfl
      _ = τ.1 ⟨p, hmem.1⟩ :=
          congrArg τ.1 (Subtype.ext (eq_fibreInclusion (f := f) (g := g) hp).symm)
      _ = σ₂.1 ⟨p, hmem⟩ := rfl
  -- The agreement locus is open and contains the fibre, so it contains `f'⁻¹(W₃)`.
  obtain ⟨W₃, hW₃open, hzW₃, hW₃sub⟩ :=
    exists_isOpen_preimage_subset_agreeSet f g F.presheaf hf hzW₀ σ₁ σ₂ hagree
  refine TopCat.Presheaf.germ_ext _ (W₀ ⊓ ⟨W₃, hW₃open⟩) ⟨hzW₀, hzW₃⟩
    (homOfLE (inf_le_left : (W₀ ⊓ ⟨W₃, hW₃open⟩ : Opens Z) ≤ W₀))
    (homOfLE ((inf_le_left : (W₀ ⊓ ⟨W₃, hW₃open⟩ : Opens Z) ≤ W₀).trans
      (inf_le_left : W₀ ≤ W))) ?_
  exact GermPullback.ext fun r ↦ (hW₃sub (show (⇑(pullbackFst f g)) r.1 ∈ W₃ from r.2.2)).2

/-- **The base-change map is bijective on stalks** when `f` is proper (Stacks 0D90). -/
theorem bijective_stalkFunctor_map (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Sheaf (Type u))
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (⇑f)) (z : ↥Z) :
    Function.Bijective ((TopCat.Presheaf.stalkFunctor (Type u) z).map
      (properBaseChangeMap f g F).1) :=
  ⟨injective_stalkFunctor_map f g F hf z, surjective_stalkFunctor_map f g F hf z⟩

/-! ### Proper base change -/

/-- **Proper base change for sheaves of sets, Stacks 0D90.** Let

```
X ×_Y Z --- g' ---> X
   |                |
   f'               f
   v                v
   Z  --- g ----->  Y
```

be a cartesian square of topological spaces with `f` proper in the sense of Stacks 005O (5).
Then for every sheaf of sets `F` on `X` the canonical base-change map
`g⁻¹(f_*F) ⟶ f'_*((g')⁻¹F)` is an isomorphism. -/
@[stacks 0D90]
theorem isIso_properBaseChangeMap (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Sheaf (Type u))
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (⇑f)) :
    IsIso (properBaseChangeMap f g F) := by
  have hstalk : ∀ z : ↥Z,
      IsIso ((TopCat.Presheaf.stalkFunctor (Type u) z).map (properBaseChangeMap f g F).1) :=
    fun z ↦ (ConcreteCategory.isIso_iff_bijective _).2 (bijective_stalkFunctor_map f g F hf z)
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso (properBaseChangeMap f g F)

/-- **Proper base change for sheaves of sets, Stacks 0D90**, as an isomorphism
`g⁻¹(f_*F) ≅ f'_*((g')⁻¹F)` of sheaves of sets on `Z`. -/
def properBaseChangeIso (f : X ⟶ Y) (g : Z ⟶ Y) (F : X.Sheaf (Type u))
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} (⇑f)) :
    GermPullback.sheaf (⇑g) (f _* F.presheaf) ≅
      (TopCat.Sheaf.pushforward (Type u) (pullbackFst f g)).obj
        (GermPullback.sheaf (Function.Pullback.snd) F.presheaf) :=
  haveI := isIso_properBaseChangeMap f g F hf
  asIso (properBaseChangeMap f g F)

end Stacks.Topology.ProperBaseChange

end
