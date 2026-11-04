module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutFlatEquivalence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGluingUnconditional
public import StacksFrontier.AlgebraicGeometry.Pushout.FlatSectionsDescent

/-!
# The closing paragraph of Tag 07RX: gluing and base change are quasi-inverse on flat schemes

Let `i : X ⟶ X'` be a thickening of schemes, let `f : X ⟶ Y` be an affine morphism and let
`Y' = Y ⨿_X X'` be the pushout of [Stacks Project, Tag 07RT].  The functors `F` and `G` of
[Stacks Project, Tag 07RV] are `Stacks.Pushout.baseChangeFunctor` and
`Stacks.Pushout.gluingFunctor`, and `Stacks.Pushout.gluingAdjunction` is the adjunction
`G ⊣ F`.  Its unit is invertible with no further hypothesis
(`Stacks.Pushout.gluingAdjunction_unit_isIso`, the last assertion of Tag 07RV); its counit is
not, and the closing paragraph of [Stacks Project, Tag 07RX] says exactly when it is: *if `W'`
is flat over `Y'`, then the adjunction mapping `G(F(W')) ⟶ W'` is an isomorphism; hence `F` and
`G` define mutually quasi-inverse functors between the category of schemes flat over `Y'` and
the category of triples `(V, U', φ)` with `V ⟶ Y` and `U' ⟶ X'` flat.*  This file proves both
assertions.

## Main definitions

* `Stacks.Pushout.flatOverPushout` is the property of a scheme over the pushout that its
  structure morphism is flat, and `Stacks.Pushout.flatGluingData` the property of a compatible
  pair that both of its components are flat over their own base.  The two categories of the
  closing paragraph are the full subcategories they cut out.
* `Stacks.Pushout.flatGluingAdjunction` is `Stacks.Pushout.gluingAdjunction` restricted to those
  two full subcategories, which is possible because gluing and base change both preserve
  flatness.
* `Stacks.Pushout.FlatGluingEquivalenceData` bundles an equivalence between those two categories
  with the two natural isomorphisms identifying its functor with gluing and its inverse with base
  change; without them an equivalence of categories would not say that `F` and `G` are the
  quasi-inverse pair.

## Main results

* `Stacks.Pushout.gluingAdjunction_counit_app_isIso_of_flat` is the first assertion of the
  closing paragraph: the counit `G(F(W')) ⟶ W'` is an isomorphism at a scheme `W'` flat over
  `Y'`.
* `Stacks.Pushout.flatGluingEquivalence` is the second: gluing and base change are mutually
  quasi-inverse equivalences between flat compatible pairs and schemes flat over `Y'`.
* `Stacks.Pushout.isIso_of_isIso_gluingToPair` is the general form in which the first assertion
  is proved: a morphism `k : G(V, U', φ) ⟶ Z` out of a glued scheme, into a scheme `Z` flat over
  `Y'`, is an isomorphism as soon as its transpose `Stacks.Pushout.gluingToPair` is one — that is,
  as soon as `k` exhibits the two components of the triple as the two base changes of `Z`.  The
  counit is the case `Z = W'` and `(V, U', φ) = F(W')`, where the transpose is the identity.

## The proof of the counit assertion

Write `P = V ⨿_U U'` for the glued scheme, `k : P ⟶ Z` for the morphism and `hk` for the
hypothesis that its transpose is invertible.  Nothing here repeats the hard work of Tag 07RV:
the two cartesian squares of that tag, `Stacks.Pushout.gluing_components_isPullback`, are used as
they stand.

1. **`k` is affine.**  The map `V ⟶ P` is a thickening — it is the base change along the
   thickening `U ⟶ U'` of the second assertion of Tag 07RT, which is
   `Stacks.Pushout.gluing_inr_isThickening` — and its composite with `k` is, by `hk`, an
   isomorphism followed by the projection `Z ×_{Y'} Y ⟶ Z`, which is affine because `Y ⟶ Y'` is a
   closed immersion.  A morphism out of a thickening is affine as soon as that composite is,
   which is `Stacks.Pushout.isAffineHom_of_isThickening_comp`, and this is the only place where
   [Stacks Project, Tag 06AD] is used again.
2. **`P` is flat over `Y'`.**  By `hk` the two components of the triple are isomorphic over `Y`
   and over `X'` to the two base changes of `Z`, hence flat, so clause (2) of Tag 07RX —
   `Stacks.Pushout.flat_gluingFunctor_obj_iff` — makes `P ⟶ Y'` flat.
3. **The two base changes of `k` are isomorphisms.**  Base change along `Y ⟶ Y'` carries `P` to
   `V` by the first cartesian square of Tag 07RV and `Z` to `Z ×_{Y'} Y`, and the induced map is
   the transpose of `k`, invertible by `hk`; likewise along `X' ⟶ Y'`.
4. **Invertibility is affine-local on `Z`.**  Since `k` is affine it suffices, over an affine
   open `U` of `Z` lying over an affine open `S` of `Y'`, to invert `Γ(Z, U) ⟶ Γ(P, k ⁻¹ᵁ U)`.
   The ring `Γ(Y', S)` is a fibre product `Γ(Y, ·) ×_{Γ(X, ·)} Γ(X', ·)` along a surjection by
   the fourth assertion of Tag 07RT, in the form `Stacks.Pushout.chartSections_isPullback`, and
   both `Γ(Z, U)` and `Γ(P, k ⁻¹ᵁ U)` are flat over it by step 2.  Step 3 makes the two base
   changes of that map of flat algebras isomorphisms, by
   `AlgebraicGeometry.isIso_sectionsPushoutMap_of_isIso_pullback`, and a map of flat algebras
   over a ring fibre product with invertible base changes is invertible — the reconstruction half
   of [Stacks Project, Tag 07RU], `MilnorPatching.isIso_of_isIso_baseChange_of_isPullback`.  This
   is where flatness is really used, and it is the one step the source's proof names.

## Implementation notes

Everything here is phrased over Mathlib's canonical pushout `pushout i f`, whose very notation
needs a `HasPushout i f` instance.  The two assertions of Tag 07RX open with
`letI := hasPushout_of_isThickening i f hi` instead of binding one, exactly as the statements of
[Stacks Project, Tag 07RV] and the clauses (1)–(5) in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningPushoutGluingUnconditional` do, so that
nothing beyond `hi` and the affineness of `f` — the hypotheses of the source — is assumed.  The
auxiliary lemmas on the way there still take `[HasPushout i f]` as an instance argument, which
costs nothing: every application of them supplies that instance from `hi`.

Several steps go through small helpers that take an invertibility or affineness hypothesis as an
explicit argument rather than as an instance.  That is not decoration: the objects
`(Over.pullback g).obj Z` and `pullback Z.hom g` are equal by definition but not as terms, and
instance search, which runs at `instances` transparency, does not identify them — so an instance
proved about one spelling is invisible to a goal written in the other, while an explicit argument
is unified at the elaborator's own transparency.  The same remark is why
`Stacks.Pushout.isIso_pullback_map_of_isPullback` is stated over an arbitrary object of
`Over (pushout i f)` instead of over the glued scheme: with the glued scheme written out, a
rewrite whose motive mentions `pullback ((gluingFunctor i f hi).obj T).hom j` is not type-correct
without unfolding the colimit that defines it.

## References

* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 07RU](https://stacks.math.columbia.edu/tag/07RU)
* [Stacks Project, Tag 07RV](https://stacks.math.columbia.edu/tag/07RV)
* [Stacks Project, Tag 07RX](https://stacks.math.columbia.edu/tag/07RX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

variable {X X' Y : Scheme.{u}}

/-! ### Small adapters

Each of these turns an instance argument into an explicit one, so that the unification of
`(Over.pullback j).obj Z` with `pullback Z.hom j` happens in the elaborator rather than in
instance search, which cannot do it. -/

private theorem isAffineHom_of_eq_comp_isIso {A B C : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ C}
    {c : A ⟶ C} (hc : c = a ≫ b) (ha : IsIso a) (hb : IsAffineHom b) : IsAffineHom c := by
  subst hc
  have := ha
  have := hb
  infer_instance

private theorem flat_of_eq_comp_isIso {A B C : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ C}
    {c : A ⟶ C} (hc : c = a ≫ b) (ha : IsIso a) (hb : Flat b) : Flat c := by
  subst hc
  have := ha
  have := hb
  infer_instance

private theorem isAffineHom_of_isThickening_comp_of_isAffineHom {A B C : Scheme.{u}}
    (p : A ⟶ B) (g : B ⟶ C) (hp : IsThickening p) (h : IsAffineHom (p ≫ g)) :
    IsAffineHom g := by
  have := h
  exact isAffineHom_of_isThickening_comp forall_isAffine_of_isThickening p g hp

/-- **A base change is detected by a cartesian square.**  If `p`, `q` exhibit `A` as the fibre
product of `B` over `j`, and the morphism `g` into `pullback C.hom j` induced by `p ≫ m.left` and
`q` is invertible, then the base change of `m : B ⟶ C` along `j` is invertible.

Stated over arbitrary objects of `Over S` on purpose: with the glued scheme of a triple written
out, a rewrite whose motive mentions `pullback ((gluingFunctor i f hi).obj T).hom j` is not
type-correct without unfolding the colimit defining that pushout. -/
theorem isIso_pullback_map_of_isPullback {S W : Scheme.{u}} (j : W ⟶ S)
    {B C : Over S} (m : B ⟶ C) {A : Scheme.{u}} {p : A ⟶ B.left} {q : A ⟶ W}
    (hd : IsPullback p q B.hom j) (g : A ⟶ pullback C.hom j) (hg : IsIso g)
    (hgf : g ≫ pullback.fst C.hom j = p ≫ m.left)
    (hgs : g ≫ pullback.snd C.hom j = q) :
    IsIso (((Over.pullback j).map m).left) := by
  have := hg
  have hstep : hd.isoPullback.hom ≫ ((Over.pullback j).map m).left = g := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, show ((Over.pullback j).map m).left ≫ pullback.fst C.hom j = _ from
        pullback.lift_fst _ _ _, ← Category.assoc, hd.isoPullback_hom_fst, hgf]
    · rw [Category.assoc, show ((Over.pullback j).map m).left ≫ pullback.snd C.hom j = _ from
        pullback.lift_snd _ _ _, hd.isoPullback_hom_snd, hgs]
  have : IsIso (hd.isoPullback.hom ≫ ((Over.pullback j).map m).left) := by
    rw [hstep]
    infer_instance
  exact IsIso.of_isIso_comp_left hd.isoPullback.hom _

/-! ### A morphism out of a glued scheme whose transpose is invertible -/

section Counit

variable (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i)
  [IsAffineHom f] [HasPushout i f] {T : gluingData i f} {Z : Over (pushout i f)}
  (k : (gluingFunctor i f hi).obj T ⟶ Z)

/-- The `V`-component of the transpose of `k`, as a morphism of schemes, is invertible when the
transpose is. -/
theorem isIso_gluingToPair_left_left (hk : IsIso (gluingToPair i f hi k)) :
    IsIso ((gluingToPair i f hi k).hom.left.left) := by
  have : IsIso (gluingToPair i f hi k) := hk
  have : IsIso (gluingToPair i f hi k).hom := (ObjectProperty.isIso_hom_iff _).mpr hk
  have : IsIso ((gluingToPair i f hi k).hom.left) :=
    Functor.map_isIso (Comma.fst (Over.pullback f) (Over.pullback i))
      (gluingToPair i f hi k).hom
  exact Functor.map_isIso (Over.forget Y) ((gluingToPair i f hi k).hom.left)

/-- The `U'`-component of the transpose of `k`, as a morphism of schemes, is invertible when the
transpose is. -/
theorem isIso_gluingToPair_right_left (hk : IsIso (gluingToPair i f hi k)) :
    IsIso ((gluingToPair i f hi k).hom.right.left) := by
  have : IsIso (gluingToPair i f hi k) := hk
  have : IsIso (gluingToPair i f hi k).hom := (ObjectProperty.isIso_hom_iff _).mpr hk
  have : IsIso ((gluingToPair i f hi k).hom.right) :=
    Functor.map_isIso (Comma.snd (Over.pullback f) (Over.pullback i))
      (gluingToPair i f hi k).hom
  exact Functor.map_isIso (Over.forget X') ((gluingToPair i f hi k).hom.right)

/-- **A morphism out of a glued scheme whose transpose is invertible is affine.**  The map
`V ⟶ V ⨿_U U'` is a thickening, and its composite with `k` is the transpose followed by the
projection `Z ×_{Y'} Y ⟶ Z`, which is affine because `Y ⟶ Y'` is a closed immersion. -/
theorem isAffineHom_left_of_isIso_gluingToPair (hk : IsIso (gluingToPair i f hi k)) :
    IsAffineHom k.left := by
  let := gluingHasPushout i f hi T
  have : IsClosedImmersion (pushout.inr i f) :=
    (pushout_inr_isThickening forall_isAffine_of_isThickening i f hi).1
  exact isAffineHom_of_isThickening_comp_of_isAffineHom _ k.left
    (gluing_inr_isThickening i f hi T)
    (isAffineHom_of_eq_comp_isIso (gluingToPair_left_comp_fst i f hi k).symm
      (isIso_gluingToPair_left_left i f hi k hk)
      (MorphismProperty.of_isPullback (P := @IsAffineHom)
        (IsPullback.of_hasPullback Z.hom (pushout.inr i f)).flip inferInstance))

/-- **The glued scheme is flat over `Y'`.**  The transpose being invertible identifies the two
components of the triple with the two base changes of `Z`, which are flat; clause (2) of
[Stacks Project, Tag 07RX] then makes the glued scheme flat. -/
theorem flat_gluingFunctor_obj_of_isIso_gluingToPair (hZ : Flat Z.hom)
    (hk : IsIso (gluingToPair i f hi k)) : Flat ((gluingFunctor i f hi).obj T).hom := by
  let := gluingHasPushout i f hi T
  refine (flat_gluingFunctor_obj_iff i f hi T).mpr ⟨?_, ?_⟩
  · exact flat_of_eq_comp_isIso (gluingToPair_left_comp_snd i f hi k).symm
      (isIso_gluingToPair_left_left i f hi k hk)
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback Z.hom (pushout.inr i f)) hZ)
  · exact flat_of_eq_comp_isIso (gluingToPair_right_comp_snd i f hi k).symm
      (isIso_gluingToPair_right_left i f hi k hk)
      (MorphismProperty.of_isPullback (IsPullback.of_hasPullback Z.hom (pushout.inl i f)) hZ)

/-- Base change of `k` along `Y ⟶ Y'` is an isomorphism: its source is `V` by the first
cartesian square of [Stacks Project, Tag 07RV] and the induced map is the transpose of `k`. -/
theorem isIso_pullback_inr_map_of_isIso_gluingToPair (hk : IsIso (gluingToPair i f hi k)) :
    IsIso (((Over.pullback (pushout.inr i f)).map k).left) := by
  let := gluingHasPushout i f hi T
  exact isIso_pullback_map_of_isPullback (pushout.inr i f) k
    (gluing_components_isPullback i f hi T).1 (gluingToPair i f hi k).hom.left.left
    (isIso_gluingToPair_left_left i f hi k hk)
    (gluingToPair_left_comp_fst i f hi k) (gluingToPair_left_comp_snd i f hi k)

/-- Base change of `k` along `X' ⟶ Y'` is an isomorphism, by the second cartesian square of
[Stacks Project, Tag 07RV]. -/
theorem isIso_pullback_inl_map_of_isIso_gluingToPair (hk : IsIso (gluingToPair i f hi k)) :
    IsIso (((Over.pullback (pushout.inl i f)).map k).left) := by
  let := gluingHasPushout i f hi T
  exact isIso_pullback_map_of_isPullback (pushout.inl i f) k
    (gluing_components_isPullback i f hi T).2 (gluingToPair i f hi k).hom.right.left
    (isIso_gluingToPair_right_left i f hi k hk)
    (gluingToPair_right_comp_fst i f hi k) (gluingToPair_right_comp_snd i f hi k)

/-- **A morphism out of a glued scheme, into a flat scheme, whose transpose is invertible is
itself invertible.**  This is the general form of the first assertion of the closing paragraph of
[Stacks Project, Tag 07RX]; the four steps are the ones listed in the module documentation. -/
theorem isIso_of_isIso_gluingToPair (hZ : Flat Z.hom) (hk : IsIso (gluingToPair i f hi k)) :
    IsIso k := by
  let := gluingHasPushout i f hi T
  have : IsClosedImmersion i := hi.1
  have hZf : Flat Z.hom := hZ
  have hGf : Flat ((gluingFunctor i f hi).obj T).hom :=
    flat_gluingFunctor_obj_of_isIso_gluingToPair i f hi k hZ hk
  have hka : IsAffineHom k.left := isAffineHom_left_of_isIso_gluingToPair i f hi k hk
  have : IsClosedImmersion (pushout.inr i f) :=
    (pushout_inr_isThickening forall_isAffine_of_isThickening i f hi).1
  have : IsAffineHom (pushout.inl i f) := isAffineHom_pushout_inl_of_isThickening i f hi
  have hcomp : k.left ≫ Z.hom = ((gluingFunctor i f hi).obj T).hom := k.w
  have hPBr : IsIso (((Over.pullback (pushout.inr i f)).map k).left) :=
    isIso_pullback_inr_map_of_isIso_gluingToPair i f hi k hk
  have hPBl : IsIso (((Over.pullback (pushout.inl i f)).map k).left) :=
    isIso_pullback_inl_map_of_isIso_gluingToPair i f hi k hk
  have hLocal : ∀ x : Z.left, ∃ U : Z.left.Opens, x ∈ U ∧ IsIso (k.left ∣_ U) := by
    intro x
    obtain ⟨_, ⟨S, hS, rfl⟩, hmem, -⟩ :=
      (pushout i f).isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (Z.hom x)) isOpen_univ
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUS⟩ :=
      Z.left.isBasis_affineOpens.exists_subset_of_mem_open
        (a := x) (show x ∈ Z.hom ⁻¹ᵁ S from hmem) (Z.hom ⁻¹ᵁ S).2
    have hApp : IsIso (k.left.app U) := by
      have hSU : k.left ⁻¹ᵁ U ≤ ((gluingFunctor i f hi).obj T).hom ⁻¹ᵁ S := by
        calc k.left ⁻¹ᵁ U ≤ k.left ⁻¹ᵁ (Z.hom ⁻¹ᵁ S) := k.left.preimage_mono hUS
          _ = (k.left ≫ Z.hom) ⁻¹ᵁ S := (Scheme.Hom.comp_preimage k.left Z.hom S).symm
          _ = _ := by rw [hcomp]
      have hpre : IsAffineOpen (k.left ⁻¹ᵁ U) := hU.preimage k.left
      have hA' : IsAffineOpen (pushout.inl i f ⁻¹ᵁ S) := hS.preimage (pushout.inl i f)
      have hsurj : Function.Surjective (chartSurjection i f S) := by
        have h := i.app_surjective (pushout.inl i f ⁻¹ᵁ S) hA'
        rwa [← Scheme.Hom.appLE_eq_app] at h
      have hsq : IsPullback
          ((pushout.inr i f).appLE S (pushout.inr i f ⁻¹ᵁ S) le_rfl)
          ((pushout.inl i f).appLE S (pushout.inl i f ⁻¹ᵁ S) le_rfl)
          (f.appLE (pushout.inr i f ⁻¹ᵁ S) ((i ≫ pushout.inl i f) ⁻¹ᵁ S)
            (commonBase_le_targetBase i f S))
          (i.appLE (pushout.inl i f ⁻¹ᵁ S) ((i ≫ pushout.inl i f) ⁻¹ᵁ S) le_rfl) := by
        have h := chartSections_isPullback i f hi S
        rwa [Scheme.Hom.app_eq_appLE (pushout.inr i f),
          Scheme.Hom.app_eq_appLE (pushout.inl i f)] at h
      let Cobj : CommRingCat.flat.Under ⊤ (CommRingCat.of Γ(pushout i f, S)) :=
        MorphismProperty.Under.mk ⊤ (Z.hom.appLE S U hUS) (by
          rw [CommRingCat.flat_iff]
          exact Z.hom.flat_appLE hS hU hUS)
      let Dobj : CommRingCat.flat.Under ⊤ (CommRingCat.of Γ(pushout i f, S)) :=
        MorphismProperty.Under.mk ⊤
          (((gluingFunctor i f hi).obj T).hom.appLE S (k.left ⁻¹ᵁ U) hSU) (by
            rw [CommRingCat.flat_iff]
            exact ((gluingFunctor i f hi).obj T).hom.flat_appLE hS hpre hSU)
      let fObj : Cobj ⟶ Dobj :=
        MorphismProperty.Under.homMk (k.left.appLE U (k.left ⁻¹ᵁ U) le_rfl) (by
          show Z.hom.appLE S U hUS ≫ k.left.appLE U (k.left ⁻¹ᵁ U) le_rfl =
            ((gluingFunctor i f hi).obj T).hom.appLE S (k.left ⁻¹ᵁ U) hSU
          have hSU' : k.left ⁻¹ᵁ U ≤ (k.left ≫ Z.hom) ⁻¹ᵁ S := by
            rw [hcomp]
            exact hSU
          calc Z.hom.appLE S U hUS ≫ k.left.appLE U (k.left ⁻¹ᵁ U) le_rfl
              = (k.left ≫ Z.hom).appLE S (k.left ⁻¹ᵁ U) hSU' :=
                Scheme.Hom.appLE_comp_appLE k.left Z.hom S U (k.left ⁻¹ᵁ U) hUS le_rfl
            _ = _ := Scheme.Hom.appLE_congr_hom hcomp S (k.left ⁻¹ᵁ U) hSU' hSU)
      have hPush : ∀ {W : Scheme.{u}} (j : W ⟶ pushout i f) [IsAffineHom j],
          IsIso (((Over.pullback j).map k).left) →
          IsIso ((MorphismProperty.Under.pushout CommRingCat.flat ⊤
            (j.appLE S (j ⁻¹ᵁ S) le_rfl)).map fObj) := fun j _ hj =>
        isIso_sectionsPushoutMap_of_isIso_pullback ((gluingFunctor i f hi).obj T).hom Z.hom
          k.left j hcomp hS hU hUS hj
      have hRing : IsIso fObj :=
        MilnorPatching.isIso_of_isIso_baseChange_of_isPullback
          ((pushout.inr i f).appLE S (pushout.inr i f ⁻¹ᵁ S) le_rfl).hom
          ((pushout.inl i f).appLE S (pushout.inl i f ⁻¹ᵁ S) le_rfl).hom
          (chartToBase i f S) (chartSurjection i f S) hsq hsurj fObj (hPush _ hPBr) (hPush _ hPBl)
      have hForget := Functor.map_isIso (CategoryTheory.Under.forget
        (CommRingCat.of Γ(pushout i f, S)))
        ((MorphismProperty.Under.forget CommRingCat.flat ⊤
          (CommRingCat.of Γ(pushout i f, S))).map fObj)
      change IsIso (k.left.appLE U (k.left ⁻¹ᵁ U) le_rfl) at hForget
      simpa only [Scheme.Hom.app_eq_appLE] using hForget
    exact ⟨U, hxU, (isIso_morphismRestrict_iff_isIso_app k.left hU).2 hApp⟩
  have hkl : IsIso k.left := IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict hLocal
  have : IsIso ((Over.forget (pushout i f)).map k) := by
    show IsIso k.left
    exact hkl
  exact isIso_of_reflects_iso k (Over.forget (pushout i f))

end Counit

section CounitApp

variable (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]

/-- The counit of `Stacks.Pushout.gluingAdjunction` is the morphism out of the glued scheme that
the hom-set bijection of [Stacks Project, Tag 07RV] assigns to the identity of `F(W')`. -/
theorem gluingAdjunction_counit_app_eq (W' : Over (pushout i f)) :
    (gluingAdjunction i f hi).counit.app W' =
      gluingFromPair i f hi (𝟙 ((baseChangeFunctor i f hi).obj W')) := by
  have h : ((gluingAdjunction i f hi).homEquiv ((baseChangeFunctor i f hi).obj W') W').symm
      (𝟙 ((baseChangeFunctor i f hi).obj W')) =
      (gluingFunctor i f hi).map (𝟙 ((baseChangeFunctor i f hi).obj W')) ≫
        (gluingAdjunction i f hi).counit.app W' :=
    CategoryTheory.Adjunction.homEquiv_counit (gluingAdjunction i f hi)
      ((baseChangeFunctor i f hi).obj W') W' (𝟙 ((baseChangeFunctor i f hi).obj W'))
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  have h2 : (gluingAdjunction i f hi).homEquiv = gluingHomEquiv i f hi := by
    dsimp only [gluingAdjunction]
    exact CategoryTheory.Adjunction.mkOfHomEquiv_homEquiv _
  rw [← h, h2]
  rfl

/-- The transpose of the counit is the identity: that is the triangle the hom-set bijection
makes. -/
theorem gluingToPair_counit_app (W' : Over (pushout i f)) :
    gluingToPair i f hi ((gluingAdjunction i f hi).counit.app W') =
      𝟙 ((baseChangeFunctor i f hi).obj W') := by
  rw [gluingAdjunction_counit_app_eq i f hi W']
  exact (gluingHomEquiv i f hi ((baseChangeFunctor i f hi).obj W') W').apply_symm_apply _

end CounitApp

/-- **[Stacks, Tag 07RX], the closing paragraph, first assertion.**  If `W'` is flat over the
pushout `Y' = Y ⨿_X X'` of a thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y`, then
the adjunction mapping `G(F(W')) ⟶ W'` is an isomorphism: `W'` is glued from its two base
changes to `Y` and to `X'`. -/
@[stacks 07RX "the closing paragraph: the counit G(F(W')) ⟶ W' is an isomorphism for W' flat \
over Y', for the adjunction of Tag 07RV over Mathlib's canonical pushout"]
theorem gluingAdjunction_counit_app_isIso_of_flat (i : X ⟶ X') (f : X ⟶ Y)
    (hi : IsThickening i) [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    ∀ W' : Over (pushout i f), Flat W'.hom →
      IsIso ((gluingAdjunction i f hi).counit.app W') := by
  let := hasPushout_of_isThickening i f hi
  intro W' hW'
  refine isIso_of_isIso_gluingToPair i f hi ((gluingAdjunction i f hi).counit.app W') hW' ?_
  rw [gluingToPair_counit_app i f hi W']
  infer_instance

/-! ### The equivalence of categories -/

/-- Schemes flat over the pushout `Y' = Y ⨿_X X'`.  This is stated at the pushout, the only
base at which the closing paragraph of Tag 07RX uses it; the analogous properties for étale and
for affine structure morphisms are `AlgebraicGeometry.IsEtaleOver` and
`AlgebraicGeometry.IsAffineHomOver`. -/
abbrev flatOverPushout (i : X ⟶ X') (f : X ⟶ Y) [HasPushout i f] :
    ObjectProperty (Over (pushout i f)) := fun W ↦ Flat W.hom

/-- Compatible pairs both of whose components are flat over their own base. -/
abbrev flatGluingData (i : X ⟶ X') (f : X ⟶ Y) : ObjectProperty (gluingData i f) :=
  fun T ↦ Flat T.obj.left.hom ∧ Flat T.obj.right.hom

section Equivalence

variable (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] [HasPushout i f]

/-- Gluing preserves flatness: clause (2) of [Stacks Project, Tag 07RX]. -/
theorem flatOver_gluingFunctor_obj (T : (flatGluingData i f).FullSubcategory) :
    flatOverPushout i f (((flatGluingData i f).ι ⋙ gluingFunctor i f hi).obj T) :=
  (flat_gluingFunctor_obj_iff i f hi T.obj).mpr T.property

/-- Base change preserves flatness. -/
theorem flatGluingData_baseChangeFunctor_obj
    (W : (flatOverPushout i f).FullSubcategory) :
    flatGluingData i f (((flatOverPushout i f).ι ⋙ baseChangeFunctor i f hi).obj W) := by
  refine ⟨?_, ?_⟩
  · exact MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback W.obj.hom (pushout.inr i f)) W.property
  · exact MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback W.obj.hom (pushout.inl i f)) W.property

/-- `Stacks.Pushout.gluingAdjunction` restricted to the flat objects on both sides. -/
noncomputable def flatGluingAdjunction :
    (flatOverPushout i f).lift ((flatGluingData i f).ι ⋙ gluingFunctor i f hi)
        (flatOver_gluingFunctor_obj i f hi) ⊣
      (flatGluingData i f).lift
        ((flatOverPushout i f).ι ⋙ baseChangeFunctor i f hi)
        (flatGluingData_baseChangeFunctor_obj i f hi) :=
  (gluingAdjunction i f hi).restrictFullyFaithful
    (flatGluingData i f).fullyFaithfulι (flatOverPushout i f).fullyFaithfulι
    ((flatOverPushout i f).liftCompιIso _ (flatOver_gluingFunctor_obj i f hi)).symm
    ((flatGluingData i f).liftCompιIso _ (flatGluingData_baseChangeFunctor_obj i f hi)).symm

/-- The unit of the restricted adjunction is invertible, because the unit of
`Stacks.Pushout.gluingAdjunction` is. -/
theorem flatGluingAdjunction_unit_app_isIso (T : (flatGluingData i f).FullSubcategory) :
    IsIso ((flatGluingAdjunction i f hi).unit.app T) := by
  apply ((flatGluingData i f).isIso_hom_iff _).mp
  show IsIso ((flatGluingData i f).ι.map ((flatGluingAdjunction i f hi).unit.app T))
  rw [flatGluingAdjunction, CategoryTheory.Adjunction.map_restrictFullyFaithful_unit_app]
  have : IsIso ((gluingAdjunction i f hi).unit.app ((flatGluingData i f).ι.obj T)) :=
    gluingAdjunction_unit_app_isIso i f hi T.obj
  infer_instance

/-- The counit of the restricted adjunction is invertible, by
`Stacks.Pushout.gluingAdjunction_counit_app_isIso_of_flat`: every object of the restricted
target category is flat over `Y'`. -/
theorem flatGluingAdjunction_counit_app_isIso
    (W : (flatOverPushout i f).FullSubcategory) :
    IsIso ((flatGluingAdjunction i f hi).counit.app W) := by
  apply ((flatOverPushout i f).isIso_hom_iff _).mp
  show IsIso ((flatOverPushout i f).ι.map
    ((flatGluingAdjunction i f hi).counit.app W))
  rw [flatGluingAdjunction, CategoryTheory.Adjunction.map_restrictFullyFaithful_counit_app]
  have : IsIso ((gluingAdjunction i f hi).counit.app
      ((flatOverPushout i f).ι.obj W)) :=
    gluingAdjunction_counit_app_isIso_of_flat i f hi W.obj W.property
  infer_instance

end Equivalence

/-- An equivalence between flat compatible pairs and schemes flat over the pushout, together with
the two natural isomorphisms identifying its functor with gluing and its inverse with base
change.  The two isomorphisms are what makes this say that `F` and `G` of
[Stacks Project, Tag 07RV] are the quasi-inverse pair, rather than merely that the two categories
are equivalent. -/
structure FlatGluingEquivalenceData (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i)
    [IsAffineHom f] [HasPushout i f] where
  /-- The equivalence of categories. -/
  equivalence : (flatGluingData i f).FullSubcategory ≌
    (flatOverPushout i f).FullSubcategory
  /-- Its functor is the gluing functor `G`. -/
  gluing : equivalence.functor ⋙ (flatOverPushout i f).ι ≅
    (flatGluingData i f).ι ⋙ gluingFunctor i f hi
  /-- Its inverse is the base-change functor `F`. -/
  restriction : equivalence.inverse ⋙ (flatGluingData i f).ι ≅
    (flatOverPushout i f).ι ⋙ baseChangeFunctor i f hi

/-- **[Stacks, Tag 07RX], the closing paragraph, second assertion.**  For the pushout
`Y' = Y ⨿_X X'` of a thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y`, the functors `F`
and `G` of [Stacks Project, Tag 07RV] are mutually quasi-inverse between the category of schemes
flat over `Y'` and the category of triples `(V, U', φ)` with `V ⟶ Y` and `U' ⟶ X'` flat.

Both functors restrict to those subcategories, so the adjunction of Tag 07RV does; its unit is
invertible by the last assertion of that tag and its counit by
`Stacks.Pushout.gluingAdjunction_counit_app_isIso_of_flat`. -/
@[stacks 07RX "the closing paragraph: F and G are mutually quasi-inverse between the schemes \
flat over Y' and the triples with both components flat, for Tag 07RV over Mathlib's canonical \
pushout"]
noncomputable def flatGluingEquivalence (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i)
    [IsAffineHom f] :
    letI := hasPushout_of_isThickening i f hi
    FlatGluingEquivalenceData i f hi :=
  letI := hasPushout_of_isThickening i f hi
  haveI := flatGluingAdjunction_unit_app_isIso i f hi
  haveI := flatGluingAdjunction_counit_app_isIso i f hi
  { equivalence := (flatGluingAdjunction i f hi).toEquivalence
    gluing := (flatOverPushout i f).liftCompιIso _ (flatOver_gluingFunctor_obj i f hi)
    restriction := (flatGluingData i f).liftCompιIso _
      (flatGluingData_baseChangeFunctor_obj i f hi) }

end Stacks.Pushout

end
