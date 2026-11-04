module

public import StacksFrontier.AlgebraicGeometry.Pushout.Chart
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout

/-!
# Pushouts along a thickening and an affine morphism: the global statement

Let `i : X ⟶ X'` be a thickening of schemes and `f : X ⟶ Y` an affine morphism.
[Stacks Project, Tag 07RT] asserts that the pushout `Y' = Y ⨿_X X'` exists in the category of
schemes and that the pushout square is simultaneously cartesian.

`StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout` proves both assertions when `X'` and
`Y` are affine.  This file globalizes them, with one hypothesis left open: that **any thickening
of an affine scheme is affine**, which is [Stacks Project, Tag 06AD].  That hypothesis is taken
as an explicit universally quantified argument `H`, exactly as in
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFiniteOrder`, because it is a
statement about *all* thickenings of *all* affine schemes and is applied to restrictions of `i`,
not to `i` itself.

## Main results

* `Stacks.Pushout.exists_affineChart_of_isPushout_of_isClosedImmersion`: the affine chart of a
  pushout of locally ringed spaces along a closed immersion, over an open whose two preimages are
  affine.  This is `Stacks.Pushout.exists_affineChart_of_isPushout` with the hypothesis that the
  second leg be integral removed, together with the conclusion that used it.
* `Stacks.Pushout.exists_scheme_isPushout_of_isPushout`: a pushout of locally ringed spaces along
  a closed immersion is a scheme as soon as every point lies in an open with affine preimages.
* `Stacks.Pushout.isPullback_of_isPushout_forgetToLocallyRingedSpace`: such a pushout square is
  also cartesian.
* `Stacks.Pushout.isAffineOpen_opensCongr_preimage_of_isThickening`: granted
  [Stacks Project, Tag 06AD], the open of `X'` matching the preimage of an affine open of `Y` is
  affine.  This is the only place where that tag is used.
* `Stacks.Pushout.exists_isPushout_isPullback_of_isThickening`: granted
  [Stacks Project, Tag 06AD], the pushout of a thickening and an affine morphism exists and its
  defining square is cartesian.
* `Stacks.Pushout.hasPushout_of_isThickening_of_isAffineHom` and
  `Stacks.Pushout.isPullback_pushout_of_isThickening_of_isAffineHom` are the first and third
  assertions of [Stacks Project, Tag 07RT], for Mathlib's canonical pushout, granted
  [Stacks Project, Tag 06AD].

## Implementation notes

The construction is the one of [Stacks Project, Tag 0E25] in
`StacksFrontier.AlgebraicGeometry.Pushout.Gluing`: form the pushout of *locally ringed spaces*,
exhibit an affine chart around every point, and conclude by
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.scheme`.  Three things differ.

First, Tag 0E25 asks the second leg of the span to be **integral**, while Tag 07RT asks it to be
**affine**.  Integrality is used in the chart construction of
`StacksFrontier.AlgebraicGeometry.Pushout.Chart` only to see that the affine model's map from `X` is
integral, which no part of the construction consumes; so
`Stacks.Pushout.exists_affineChart_of_isPushout_of_isClosedImmersion` restates that lemma without
it.  When the two developments are merged, the integrality-free form should replace the other.

Second, the fibrewise condition of [Stacks Project, Tag 0ECI] — each fibre of the second leg maps
into one affine open — is not needed here, and neither is [Stacks Project, Tag 0ECJ], which
derives a compatible pair of affine opens from it.  A thickening is a homeomorphism on points, so
the open of `X'` matching `f ⁻¹ᵁ V` is already compatible with `V` by
`Stacks.Thickenings.IsThickening.preimage_opensCongr`; what has to be supplied instead is that it
is *affine*, and that is [Stacks Project, Tag 06AD].

Third, the statements here are about an arbitrary scheme carrying the pushout square rather than
about a chosen construction, so no new definition is introduced: the existence statements produce
the scheme and its two maps, and the two assertions of Tag 07RT are read off Mathlib's canonical
pushout by transporting along `CategoryTheory.IsPushout.isoPushout`.

**The hypothesis `H`.**  It is [Stacks Project, Tag 06AD], and it assumes nothing: that tag is
a theorem, `Stacks.Thickenings.isAffine_of_isThickening`, proved in
`StacksFrontier.AlgebraicGeometry.Thickenings.Affine` through finite surjective morphisms, with
`Stacks.Thickenings.forall_isAffine_of_isThickening` the universally quantified form that `H`
wants.  The source instead proves it as a special case of [Stacks Project, Tag 05YU]; see also
the implementation notes of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffine`, which reduces it to the
surjectivity of `i.appTop`, and of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningAffineFiniteOrder`, which reduces the
finite-order case to the first-order one.  Note that a thickening of an affine scheme need *not*
be of finite order — the kernel ideal is nil but need not be nilpotent — so the finite-order
route does not suffice.

## References

* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Pushout

open Stacks.Thickenings

/-! ### The affine chart, without an integrality hypothesis -/

section Chart

variable {X Y Z : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) {P : LocallyRingedSpace.{u}}
  {a : Scheme.forgetToLocallyRingedSpace.obj X ⟶ P}
  {b : Scheme.forgetToLocallyRingedSpace.obj Y ⟶ P}

private lemma map_morphismRestrict_comp_ι (U : X.Opens) :
    Scheme.forgetToLocallyRingedSpace.map (i ∣_ U) ≫ Scheme.forgetToLocallyRingedSpace.map U.ι =
      Scheme.forgetToLocallyRingedSpace.map (i ⁻¹ᵁ U).ι ≫
        Scheme.forgetToLocallyRingedSpace.map i := by
  rw [← Functor.map_comp, ← Functor.map_comp, morphismRestrict_ι]

private lemma map_resLE_comp_ι (V : Y.Opens) (W : Z.Opens) (e : W ≤ j ⁻¹ᵁ V) :
    Scheme.forgetToLocallyRingedSpace.map (j.resLE V W e) ≫
        Scheme.forgetToLocallyRingedSpace.map V.ι =
      Scheme.forgetToLocallyRingedSpace.map W.ι ≫ Scheme.forgetToLocallyRingedSpace.map j := by
  rw [← Functor.map_comp, ← Functor.map_comp, Scheme.Hom.resLE_comp_ι]

/-- A map out of the affine model compatible with the two legs lands in `W`. -/
theorem base_mem_of_isPushout_affineModel [IsClosedImmersion i] {W : Opens P} {U : X.Opens}
    {V : Y.Opens} (hUW : U = (Opens.map a.base).obj W) (hVW : V = (Opens.map b.base).obj W)
    (hTV : i ⁻¹ᵁ U = j ⁻¹ᵁ V) [IsAffine U.toScheme] [IsAffine V.toScheme]
    [IsAffine (i ⁻¹ᵁ U).toScheme]
    {g : Scheme.forgetToLocallyRingedSpace.obj
      (affineModel (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ⟶ P}
    (hga : Scheme.forgetToLocallyRingedSpace.map
        (affineModelInl (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ≫ g =
      Scheme.forgetToLocallyRingedSpace.map U.ι ≫ a)
    (hgb : Scheme.forgetToLocallyRingedSpace.map
        (affineModelInr (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ≫ g =
      Scheme.forgetToLocallyRingedSpace.map V.ι ≫ b) (q) :
    g.base q ∈ W := by
  have HQ := isPushout_affineModel_locallyRingedSpace (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)
  have hiU' : Function.Injective (Scheme.forgetToLocallyRingedSpace.map (i ∣_ U)).base :=
    (i ∣_ U).isClosedEmbedding.injective
  have hgapp : ∀ x, g.base ((Scheme.forgetToLocallyRingedSpace.map
      (affineModelInl (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le))).base x) =
      a.base ((Scheme.forgetToLocallyRingedSpace.map U.ι).base x) := fun x ↦
    ConcreteCategory.congr_hom (congrArg (fun f : _ ⟶ P ↦ f.base) hga) x
  have hgbpp : ∀ y, g.base ((Scheme.forgetToLocallyRingedSpace.map
      (affineModelInr (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le))).base y) =
      b.base ((Scheme.forgetToLocallyRingedSpace.map V.ι).base y) := fun y ↦
    ConcreteCategory.congr_hom (congrArg (fun f : _ ⟶ P ↦ f.base) hgb) y
  obtain ⟨s, hs⟩ :=
    (isQuotientMap_sum_of_isPushout _ _ hiU' (isPushout_base_of_isPushout HQ)).surjective q
  rcases s with x | y
  · subst hs
    show g.base ((Scheme.forgetToLocallyRingedSpace.map (affineModelInl _ _)).base x) ∈ W
    rw [hgapp x]
    exact hUW.le (show ((Scheme.forgetToLocallyRingedSpace.map U.ι).base x) ∈ U from x.2)
  · subst hs
    show g.base ((Scheme.forgetToLocallyRingedSpace.map (affineModelInr _ _)).base y) ∈ W
    rw [hgbpp y]
    exact hVW.le (show ((Scheme.forgetToLocallyRingedSpace.map V.ι).base y) ∈ V from y.2)

/-- A map out of the affine model compatible with the two legs is an open embedding onto `W`. -/
theorem isOpenEmbedding_base_of_isPushout_affineModel [IsClosedImmersion i]
    (h : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map j) a b) {W : Opens P} {U : X.Opens}
    {V : Y.Opens} (hUW : U = (Opens.map a.base).obj W) (hVW : V = (Opens.map b.base).obj W)
    (hTV : i ⁻¹ᵁ U = j ⁻¹ᵁ V) [IsAffine U.toScheme] [IsAffine V.toScheme]
    [IsAffine (i ⁻¹ᵁ U).toScheme]
    {g : Scheme.forgetToLocallyRingedSpace.obj
      (affineModel (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ⟶ P}
    (hga : Scheme.forgetToLocallyRingedSpace.map
        (affineModelInl (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ≫ g =
      Scheme.forgetToLocallyRingedSpace.map U.ι ≫ a)
    (hgb : Scheme.forgetToLocallyRingedSpace.map
        (affineModelInr (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ≫ g =
      Scheme.forgetToLocallyRingedSpace.map V.ι ≫ b) :
    Topology.IsOpenEmbedding g.base ∧ Set.range g.base = (W : Set P) := by
  have HQ := isPushout_affineModel_locallyRingedSpace (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)
  have hgW := base_mem_of_isPushout_affineModel i j hUW hVW hTV hga hgb
  have hg0 : IsIso (toOpens g.base W hgW) := by
    refine IsPushout.isIso_of_comp_eq (isPushout_base_of_isPushout HQ) ?_
      (toOpens g.base W hgW) rfl rfl
    refine isPushout_of_isOpenEmbedding (Scheme.forgetToLocallyRingedSpace.map i).base
      (Scheme.forgetToLocallyRingedSpace.map j).base i.isClosedEmbedding.injective
      (isPushout_base_of_isPushout h)
      (u := (Scheme.forgetToLocallyRingedSpace.map U.ι).base)
      (v := (Scheme.forgetToLocallyRingedSpace.map V.ι).base) (w := Opens.inclusion' W)
      (t := (Scheme.forgetToLocallyRingedSpace.map (i ⁻¹ᵁ U).ι).base)
      (Opens.isOpenEmbedding U) (Opens.isOpenEmbedding V) (Opens.isOpenEmbedding W)
      ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · rw [← LocallyRingedSpace.comp_base, ← LocallyRingedSpace.comp_base,
        map_morphismRestrict_comp_ι]
    · rw [← LocallyRingedSpace.comp_base, ← LocallyRingedSpace.comp_base, map_resLE_comp_ι]
    · rw [Category.assoc, toOpens_comp_inclusion, ← LocallyRingedSpace.comp_base,
        ← LocallyRingedSpace.comp_base, hga]
    · rw [Category.assoc, toOpens_comp_inclusion, ← LocallyRingedSpace.comp_base,
        ← LocallyRingedSpace.comp_base, hgb]
    · rintro x ⟨p, hp⟩
      refine ⟨⟨x, hUW.ge (show (a.base x : P) ∈ W from ?_)⟩, rfl⟩
      rw [← hp]
      exact p.2
    · rintro y ⟨p, hp⟩
      refine ⟨⟨y, hVW.ge (show (b.base y : P) ∈ W from ?_)⟩, rfl⟩
      rw [← hp]
      exact p.2
    · rintro z ⟨p, hp⟩
      refine ⟨⟨z, show ((Scheme.forgetToLocallyRingedSpace.map i).base z) ∈ U from ?_⟩, rfl⟩
      rw [← hp]
      exact p.2
  let e := TopCat.homeoOfIso (@asIso _ _ _ _ _ hg0)
  refine ⟨(Opens.isOpenEmbedding W).comp e.isOpenEmbedding,
    Set.Subset.antisymm (Set.range_subset_iff.2 hgW) fun p hp ↦ ?_⟩
  obtain ⟨q, hq⟩ := e.surjective ⟨p, hp⟩
  exact ⟨q, congrArg Subtype.val hq⟩

/-- A map out of the affine model compatible with the two legs is an open immersion. -/
theorem isOpenImmersion_of_isPushout_affineModel [IsClosedImmersion i]
    (h : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map j) a b) {W : Opens P} {U : X.Opens}
    {V : Y.Opens} (hUW : U = (Opens.map a.base).obj W) (hVW : V = (Opens.map b.base).obj W)
    (hTV : i ⁻¹ᵁ U = j ⁻¹ᵁ V) [IsAffine U.toScheme] [IsAffine V.toScheme]
    [IsAffine (i ⁻¹ᵁ U).toScheme]
    {g : Scheme.forgetToLocallyRingedSpace.obj
      (affineModel (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ⟶ P}
    (hga : Scheme.forgetToLocallyRingedSpace.map
        (affineModelInl (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ≫ g =
      Scheme.forgetToLocallyRingedSpace.map U.ι ≫ a)
    (hgb : Scheme.forgetToLocallyRingedSpace.map
        (affineModelInr (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ≫ g =
      Scheme.forgetToLocallyRingedSpace.map V.ι ≫ b) :
    LocallyRingedSpace.IsOpenImmersion g := by
  have HQ := isPushout_affineModel_locallyRingedSpace (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)
  have hgW := base_mem_of_isPushout_affineModel i j hUW hVW hTV hga hgb
  have hbo := (isOpenEmbedding_base_of_isPushout_affineModel i j h hUW hVW hTV hga hgb).1
  refine ⟨hbo, fun S ↦ ?_⟩
  have hOW : (hbo.functor.obj S : Opens P) ≤ W := by
    rintro p ⟨q, -, rfl⟩
    exact hgW q
  have hleU : (Opens.map a.base).obj (hbo.functor.obj S) ≤ U := fun x hx ↦
    hUW.ge (show (a.base x : P) ∈ W from hOW hx)
  have hleV : (Opens.map b.base).obj (hbo.functor.obj S) ≤ V := fun y hy ↦
    hVW.ge (show (b.base y : P) ∈ W from hOW hy)
  have hsq : ∀ {C D E F : LocallyRingedSpace.{u}} {f : C ⟶ D} {g : D ⟶ F} {h : C ⟶ E}
      {k : E ⟶ F}, f ≫ g = h ≫ k →
      lrsToPresheafedSpace.map f ≫ lrsToPresheafedSpace.map g =
        lrsToPresheafedSpace.map h ≫ lrsToPresheafedSpace.map k := fun w ↦ by
    rw [← Functor.map_comp, ← Functor.map_comp, w]
  exact isIso_app_of_isPushout_comparison (h.map lrsToPresheafedSpace)
    (HQ.map lrsToPresheafedSpace) (hsq hga) (hsq hgb) (hsq (map_morphismRestrict_comp_ι i _))
    (hsq (map_resLE_comp_ι j _ _ hTV.le)) (hbo.functor.obj S)
    (isIso_ι_app_of_le U _ hleU) (isIso_ι_app_of_le V _ hleV)
    (isIso_ι_app_of_le (i ⁻¹ᵁ U) _ (i.preimage_mono hleU))

/-- **The pushout is the affine model over an open with affine preimages.**  Let `i`, `j`, `a`,
`b` be a pushout square of locally ringed spaces with `i : Z ⟶ X` a closed immersion of schemes
and `j : Z ⟶ Y` arbitrary, and let `W` be an open of the apex whose preimages `U` in `X` and `V`
in `Y` are affine.  Then there is a ring `R` — the fibre product
`Γ(Y, V) ×_{Γ(Z, i ⁻¹ V)} Γ(X, U)` — and an open immersion from `Spec R` onto `W`, compatible
with the two canonical maps of the affine model of [Stacks Project, Tag 0ET0].

This is `Stacks.Pushout.exists_affineChart_of_isPushout` with the hypothesis that `j` be integral
dropped, along with the conclusion `IsIntegralHom α` that used it.  Nothing else in the proof
needs it. -/
theorem exists_affineChart_of_isPushout_of_isClosedImmersion [IsClosedImmersion i]
    (h : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map j) a b) (W : Opens P)
    (U : X.Opens) (V : Y.Opens) (hUW : U = (Opens.map a.base).obj W)
    (hVW : V = (Opens.map b.base).obj W)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hTV : i ⁻¹ᵁ U = j ⁻¹ᵁ V) :
    ∃ (R : CommRingCat.{u}) (α : U.toScheme ⟶ Spec R) (β : V.toScheme ⟶ Spec R)
      (g : Scheme.forgetToLocallyRingedSpace.obj (Spec R) ⟶ P),
      IsClosedImmersion β ∧
      IsPullback (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le) α β ∧
      Scheme.forgetToLocallyRingedSpace.map α ≫ g =
        Scheme.forgetToLocallyRingedSpace.map U.ι ≫ a ∧
      Scheme.forgetToLocallyRingedSpace.map β ≫ g =
        Scheme.forgetToLocallyRingedSpace.map V.ι ≫ b ∧
      LocallyRingedSpace.IsOpenImmersion g ∧ Set.range g.base = (W : Set P) := by
  have instU : IsAffine U.toScheme := hU
  have instV : IsAffine V.toScheme := hV
  have instT : IsAffine (i ⁻¹ᵁ U).toScheme := hU.preimage i
  have HQ := isPushout_affineModel_locallyRingedSpace (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)
  obtain ⟨g, hga, hgb⟩ : ∃ g : Scheme.forgetToLocallyRingedSpace.obj
      (affineModel (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ⟶ P,
      Scheme.forgetToLocallyRingedSpace.map
          (affineModelInl (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ≫ g =
        Scheme.forgetToLocallyRingedSpace.map U.ι ≫ a ∧
      Scheme.forgetToLocallyRingedSpace.map
          (affineModelInr (i ∣_ U) (j.resLE V (i ⁻¹ᵁ U) hTV.le)) ≫ g =
        Scheme.forgetToLocallyRingedSpace.map V.ι ≫ b := by
    refine ⟨HQ.desc _ _ ?_, HQ.inl_desc _ _ _, HQ.inr_desc _ _ _⟩
    rw [← Category.assoc, ← Category.assoc, map_morphismRestrict_comp_ι,
      map_resLE_comp_ι, Category.assoc, Category.assoc, h.w]
  exact ⟨_, affineModelInl _ _, affineModelInr _ _, g, inferInstance, isPullback_affineModel _ _,
    hga, hgb, isOpenImmersion_of_isPushout_affineModel i j h hUW hVW hTV hga hgb,
    (isOpenEmbedding_base_of_isPushout_affineModel i j h hUW hVW hTV hga hgb).2⟩

/-- **A pushout of locally ringed spaces along a closed immersion is a scheme**, as soon as every
point of it lies in an open whose preimages in the two schemes are affine: the affine charts are
`Stacks.Pushout.exists_affineChart_of_isPushout_of_isClosedImmersion`, and
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.scheme` assembles them.

The two canonical maps are produced together with the scheme, and the chart condition is restated
for them, because that is what the cartesianness of the square is proved from. -/
theorem exists_scheme_isPushout_of_isPushout [IsClosedImmersion i]
    (h : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map j) a b)
    (hch : ∀ p : P, ∃ W : Opens P, p ∈ W ∧ IsAffineOpen ((Opens.map a.base).obj W) ∧
      IsAffineOpen ((Opens.map b.base).obj W)) :
    ∃ (Q : Scheme.{u}) (A : X ⟶ Q) (B : Y ⟶ Q),
      IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map j)
        (Scheme.forgetToLocallyRingedSpace.map A) (Scheme.forgetToLocallyRingedSpace.map B) ∧
      ∀ p : Q, ∃ W : Q.Opens, p ∈ W ∧ IsAffineOpen (A ⁻¹ᵁ W) ∧ IsAffineOpen (B ⁻¹ᵁ W) := by
  have hpre : ∀ W : Opens P, i ⁻¹ᵁ ((Opens.map a.base).obj W) =
      j ⁻¹ᵁ ((Opens.map b.base).obj W) := fun W ↦
    congrArg (fun k : Scheme.forgetToLocallyRingedSpace.obj Z ⟶ P ↦
      (Opens.map k.base).obj W) h.w
  refine ⟨LocallyRingedSpace.IsOpenImmersion.scheme P (fun p ↦ ?_),
    Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimage a,
    Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimage b, ?_, ?_⟩
  · obtain ⟨W, hpW, hU, hV⟩ := hch p
    obtain ⟨R, α, β, g, -, -, -, -, hgoi, hgr⟩ :=
      exists_affineChart_of_isPushout_of_isClosedImmersion i j h W _ _ rfl rfl hU hV (hpre W)
    exact ⟨R, g, hgr.ge hpW, hgoi⟩
  · exact h
  · exact hch

end Chart

/-! ### Cartesianness of a pushout square of schemes -/

section Pullback

variable {X Y Z Q : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (A : X ⟶ Q) (B : Y ⟶ Q)

/-- The two preimages in `Z` of an open of the apex agree. -/
theorem preimage_preimage_eq_of_comm (hw : i ≫ A = j ≫ B) (W : Q.Opens) :
    i ⁻¹ᵁ (A ⁻¹ᵁ W) = j ⁻¹ᵁ (B ⁻¹ᵁ W) :=
  congrArg (fun k : Z ⟶ Q ↦ k ⁻¹ᵁ W) hw

/-- **The affine chart of the apex, at the scheme level.**  Around every point there is an open
`W`, an affine scheme `Spec R` isomorphic to `W`, and a cartesian square identifying the
restricted span with the affine model of [Stacks Project, Tag 0ET0]. -/
theorem exists_chart_of_isPushout_forgetToLocallyRingedSpace [IsClosedImmersion i]
    (h : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map j) (Scheme.forgetToLocallyRingedSpace.map A)
      (Scheme.forgetToLocallyRingedSpace.map B))
    (hw : i ≫ A = j ≫ B)
    (hch : ∀ p : Q, ∃ W : Q.Opens, p ∈ W ∧ IsAffineOpen (A ⁻¹ᵁ W) ∧ IsAffineOpen (B ⁻¹ᵁ W))
    (p : Q) :
    ∃ (W : Q.Opens) (R : CommRingCat.{u}) (α : (A ⁻¹ᵁ W).toScheme ⟶ Spec R)
      (β : (B ⁻¹ᵁ W).toScheme ⟶ Spec R) (e : Spec R ≅ W.toScheme),
      p ∈ W ∧ α ≫ e.hom = A ∣_ W ∧ β ≫ e.hom = B ∣_ W ∧
      IsPullback (i ∣_ (A ⁻¹ᵁ W)) (j.resLE (B ⁻¹ᵁ W) (i ⁻¹ᵁ (A ⁻¹ᵁ W))
        (preimage_preimage_eq_of_comm i j A B hw W).le) α β := by
  obtain ⟨W, hpW, hU, hV⟩ := hch p
  obtain ⟨R, α, β, g, -, hpb, hga, hgb, hgoi, hgr⟩ :=
    exists_affineChart_of_isPushout_of_isClosedImmersion i j h W (A ⁻¹ᵁ W) (B ⁻¹ᵁ W) rfl rfl
      hU hV (preimage_preimage_eq_of_comm i j A B hw W)
  obtain ⟨gS, hgS⟩ : ∃ gS : Spec R ⟶ Q, Scheme.forgetToLocallyRingedSpace.map gS = g :=
    ⟨Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimage g,
      Scheme.fullyFaithfulForgetToLocallyRingedSpace.map_preimage _⟩
  have hoi : IsOpenImmersion gS := by rwa [← hgS] at hgoi
  have hrange : Set.range gS.base = Set.range (W.ι).base :=
    (congrArg (fun k : Scheme.forgetToLocallyRingedSpace.obj (Spec R) ⟶
      Scheme.forgetToLocallyRingedSpace.obj Q ↦ Set.range k.base) hgS).trans
      (hgr.trans (Scheme.Opens.range_ι W).symm)
  obtain ⟨e, he⟩ : ∃ e : Spec R ≅ W.toScheme, e.hom ≫ W.ι = gS :=
    ⟨IsOpenImmersion.isoOfRangeEq gS W.ι hrange,
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩
  have key : ∀ {T : Scheme.{u}} (γ : T ⟶ Spec R) (δ : T ⟶ W.toScheme) (t : T ⟶ Q),
      δ ≫ W.ι = t → Scheme.forgetToLocallyRingedSpace.map γ ≫ g =
        Scheme.forgetToLocallyRingedSpace.map t → γ ≫ e.hom = δ := fun γ δ t hδ hγ ↦ by
    rw [← cancel_mono W.ι, Category.assoc, he, hδ]
    exact Scheme.forgetToLocallyRingedSpace.map_injective (by rw [Functor.map_comp, hgS, hγ])
  exact ⟨W, R, α, β, e, hpW, key _ _ _ (morphismRestrict_ι _ _) (by rw [Functor.map_comp, hga]),
    key _ _ _ (morphismRestrict_ι _ _) (by rw [Functor.map_comp, hgb]), hpb⟩

/-- **The universal property of the fibre square.**  A commutative square over the pushout square
factors through `Z`.  The factorisation is built over each chart from the affine model's own
cartesian square and glued with `AlgebraicGeometry.Scheme.Cover.glueMorphisms`. -/
theorem exists_lift_of_isPushout_forgetToLocallyRingedSpace [IsClosedImmersion i]
    (h : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map j) (Scheme.forgetToLocallyRingedSpace.map A)
      (Scheme.forgetToLocallyRingedSpace.map B))
    (hw : i ≫ A = j ≫ B)
    (hch : ∀ p : Q, ∃ W : Q.Opens, p ∈ W ∧ IsAffineOpen (A ⁻¹ᵁ W) ∧ IsAffineOpen (B ⁻¹ᵁ W))
    {S : Scheme.{u}} (u : S ⟶ X) (v : S ⟶ Y) (huv : u ≫ A = v ≫ B) :
    ∃ w : S ⟶ Z, w ≫ i = u ∧ w ≫ j = v := by
  have hloc : ∀ x : S, ∃ (O : S.Opens) (t : O.toScheme ⟶ Z), x ∈ O ∧
      t ≫ i = O.ι ≫ u ∧ t ≫ j = O.ι ≫ v := by
    intro x
    obtain ⟨W, R, α, β, e, hpW, hαe, hβe, hpb⟩ :=
      exists_chart_of_isPushout_forgetToLocallyRingedSpace i j A B h hw hch ((u ≫ A) x)
    have hlu : (u ≫ A) ⁻¹ᵁ W ≤ u ⁻¹ᵁ (A ⁻¹ᵁ W) := le_rfl
    have hlv : (u ≫ A) ⁻¹ᵁ W ≤ v ⁻¹ᵁ (B ⁻¹ᵁ W) :=
      le_of_eq (congrArg (fun k : S ⟶ Q ↦ k ⁻¹ᵁ W) huv)
    have hcompat : u.resLE (A ⁻¹ᵁ W) ((u ≫ A) ⁻¹ᵁ W) hlu ≫ α =
        v.resLE (B ⁻¹ᵁ W) ((u ≫ A) ⁻¹ᵁ W) hlv ≫ β := by
      rw [← cancel_mono e.hom, Category.assoc, Category.assoc, hαe, hβe, ← cancel_mono W.ι,
        Category.assoc, Category.assoc, morphismRestrict_ι, morphismRestrict_ι, ← Category.assoc,
        ← Category.assoc, Scheme.Hom.resLE_comp_ι, Scheme.Hom.resLE_comp_ι, Category.assoc,
        Category.assoc, huv]
    refine ⟨(u ≫ A) ⁻¹ᵁ W, hpb.lift _ _ hcompat ≫ (i ⁻¹ᵁ (A ⁻¹ᵁ W)).ι, hpW, ?_, ?_⟩
    · rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hpb.lift_fst,
        Scheme.Hom.resLE_comp_ι]
    · rw [Category.assoc,
        ← Scheme.Hom.resLE_comp_ι j (preimage_preimage_eq_of_comm i j A B hw W).le,
        ← Category.assoc, hpb.lift_snd, Scheme.Hom.resLE_comp_ι]
  choose O t hxO hti htj using hloc
  let 𝒰 : S.OpenCover :=
    { I₀ := S, X x := (O x), f x := (O x).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨fun x ↦ ⟨x, by simpa using hxO x⟩, inferInstance⟩ }
  refine ⟨𝒰.glueMorphisms t ?_, ?_, ?_⟩
  · intro x y
    rw [← cancel_mono i, Category.assoc, Category.assoc, hti, hti, ← Category.assoc,
      ← Category.assoc, pullback.condition]
  · refine 𝒰.hom_ext _ _ fun x ↦ ?_
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hti]
  · refine 𝒰.hom_ext _ _ fun x ↦ ?_
    rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, htj]

/-- **A pushout square of locally ringed spaces along a closed immersion is also a fibre square**,
as soon as every point of the apex lies in an open with affine preimages.  Uniqueness of the lift
is free because a closed immersion is a monomorphism. -/
theorem isPullback_of_isPushout_forgetToLocallyRingedSpace [IsClosedImmersion i]
    (h : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map j) (Scheme.forgetToLocallyRingedSpace.map A)
      (Scheme.forgetToLocallyRingedSpace.map B))
    (hch : ∀ p : Q, ∃ W : Q.Opens, p ∈ W ∧ IsAffineOpen (A ⁻¹ᵁ W) ∧ IsAffineOpen (B ⁻¹ᵁ W)) :
    IsPullback i j A B := by
  have hw : i ≫ A = j ≫ B :=
    (IsPushout.of_map_of_faithful Scheme.forgetToLocallyRingedSpace h).w
  choose l hl₁ hl₂ using fun c : PullbackCone A B ↦
    exists_lift_of_isPushout_forgetToLocallyRingedSpace i j A B h hw hch c.fst c.snd c.condition
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk hw l hl₁ hl₂
    fun c m h1 _ ↦ (cancel_mono i).1 (h1.trans (hl₁ c).symm))

end Pullback

/-! ### The global statement of Tag 07RT, granted Tag 06AD -/

section Global

variable {X X' Y : Scheme.{u}}

/-- **The open of the ambient scheme matching the preimage of an affine open is affine.**  This is
the one and only use of [Stacks Project, Tag 06AD], supplied here as the hypothesis `H`: the open
`hi.opensCongr (f ⁻¹ᵁ V)` of `X'` is a thickening of `f ⁻¹ᵁ V`, which is affine because `f` is an
affine morphism. -/
theorem isAffineOpen_opensCongr_preimage_of_isThickening
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    {i : X ⟶ X'} (hi : IsThickening i) (f : X ⟶ Y) [IsAffineHom f]
    {V : Y.Opens} (hV : IsAffineOpen V) : IsAffineOpen (hi.opensCongr (f ⁻¹ᵁ V)) := by
  have hsrc : IsAffineOpen (i ⁻¹ᵁ hi.opensCongr (f ⁻¹ᵁ V)) := by
    rw [hi.preimage_opensCongr]
    exact hV.preimage f
  exact H _ _ (i ∣_ hi.opensCongr (f ⁻¹ᵁ V)) (hi.morphismRestrict _) hsrc

/-- **Every point of the apex lies in an open with affine preimages.**  A thickening is surjective
on points, so every point of a pushout of `Y ← X → X'` is in the image of `Y`; around such a point
take an affine open `V` of `Y`, and for the open of `X'` take the one matching `f ⁻¹ᵁ V` under the
homeomorphism of the thickening, which is affine by
`Stacks.Pushout.isAffineOpen_opensCongr_preimage_of_isThickening`.  The two are compatible by
construction, so `Stacks.Pushout.exists_opens_preimage_eq_of_isPushout_base'` spans them by an
open of the apex.

This is what replaces [Stacks Project, Tag 0ECJ] and the fibrewise hypothesis of
[Stacks Project, Tag 0ECI] in the construction of [Stacks Project, Tag 0E25]. -/
theorem exists_opens_isAffineOpen_preimage_of_isThickening
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    {i : X ⟶ X'} (hi : IsThickening i) (f : X ⟶ Y) [IsAffineHom f]
    {P : LocallyRingedSpace.{u}} {a : Scheme.forgetToLocallyRingedSpace.obj X' ⟶ P}
    {b : Scheme.forgetToLocallyRingedSpace.obj Y ⟶ P}
    (hbase : IsPushout (Scheme.forgetToLocallyRingedSpace.map i).base
      (Scheme.forgetToLocallyRingedSpace.map f).base a.base b.base)
    (p : P) :
    ∃ W : Opens P, p ∈ W ∧ IsAffineOpen ((Opens.map a.base).obj W) ∧
      IsAffineOpen ((Opens.map b.base).obj W) := by
  have := hi.1
  have hinj : Function.Injective (Scheme.forgetToLocallyRingedSpace.map i).base :=
    i.isClosedEmbedding.injective
  have hcross : ∀ z : X, a.base ((Scheme.forgetToLocallyRingedSpace.map i).base z) =
      b.base ((Scheme.forgetToLocallyRingedSpace.map f).base z) := fun z ↦
    (ConcreteCategory.comp_apply _ _ z).symm.trans
      ((ConcreteCategory.congr_hom hbase.w z).trans (ConcreteCategory.comp_apply _ _ z))
  obtain ⟨y, hy⟩ : ∃ y : Y, b.base y = p := by
    obtain ⟨s, hs⟩ := (isQuotientMap_sum_of_isPushout _ _ hinj hbase).surjective p
    rcases s with x | y
    · obtain ⟨z, hz⟩ := hi.2 x
      exact ⟨(Scheme.forgetToLocallyRingedSpace.map f).base z,
        ((hcross z).symm.trans (congrArg a.base hz)).trans hs⟩
    · exact ⟨y, hs⟩
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) (by simp)
  obtain ⟨W, hWset, hWa, hWb⟩ := exists_opens_preimage_eq_of_isPushout_base' i f hbase hinj
    (hi.opensCongr (f ⁻¹ᵁ V)) V (hi.preimage_opensCongr _)
  refine ⟨W, ?_, hWa ▸ isAffineOpen_opensCongr_preimage_of_isThickening H hi f hV, hWb ▸ hV⟩
  rw [← SetLike.mem_coe, hWset]
  exact Or.inr ⟨y, hyV, hy⟩

/-- **Stacks Project, Tag 07RT, granted Tag 06AD: the pushout exists and its square is
cartesian.**  For a thickening `i : X ⟶ X'` and an affine morphism `f : X ⟶ Y` there is a scheme
`Q` with maps from `X'` and `Y` making the square both cocartesian and cartesian, provided every
thickening of an affine scheme is affine. -/
theorem exists_isPushout_isPullback_of_isThickening
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] :
    ∃ (Q : Scheme.{u}) (A : X' ⟶ Q) (B : Y ⟶ Q), IsPushout i f A B ∧ IsPullback i f A B := by
  have := hi.1
  have hcol : IsPushout (Scheme.forgetToLocallyRingedSpace.map i)
      (Scheme.forgetToLocallyRingedSpace.map f)
      (colimit.ι (span (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)) WalkingSpan.left)
      (colimit.ι (span (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)) WalkingSpan.right) :=
    IsPushout.of_isColimit_cocone (colimit.isColimit
      (span (Scheme.forgetToLocallyRingedSpace.map i)
        (Scheme.forgetToLocallyRingedSpace.map f)))
  obtain ⟨Q, A, B, hpush, hch⟩ := exists_scheme_isPushout_of_isPushout i f hcol
    (exists_opens_isAffineOpen_preimage_of_isThickening H hi f
      (isPushout_base_of_isPushout hcol))
  exact ⟨Q, A, B, IsPushout.of_map_of_faithful Scheme.forgetToLocallyRingedSpace hpush,
    isPullback_of_isPushout_forgetToLocallyRingedSpace i f A B hpush hch⟩

/-- **Stacks Project, Tag 07RT, first assertion, granted Tag 06AD.**  A thickening and an affine
morphism have a pushout in schemes. -/
theorem hasPushout_of_isThickening_of_isAffineHom
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] : HasPushout i f := by
  obtain ⟨Q, A, B, hpo, -⟩ := exists_isPushout_isPullback_of_isThickening H i f hi
  exact hpo.hasPushout

/-- **Stacks Project, Tag 07RT, third assertion, granted Tag 06AD.**  The pushout square of a
thickening and an affine morphism is also cartesian, stated for Mathlib's canonical pushout. -/
theorem isPullback_pushout_of_isThickening_of_isAffineHom
    (H : ∀ (Z Z' : Scheme.{u}) (k : Z ⟶ Z'), IsThickening k → IsAffine Z → IsAffine Z')
    (i : X ⟶ X') (f : X ⟶ Y) (hi : IsThickening i) [IsAffineHom f] [HasPushout i f] :
    IsPullback i f (pushout.inl i f) (pushout.inr i f) := by
  obtain ⟨Q, A, B, hpo, hpb⟩ := exists_isPushout_isPullback_of_isThickening H i f hi
  rw [← hpo.inl_isoPushout_hom, ← hpo.inr_isoPushout_hom]
  exact hpb.of_iso' (Iso.refl X) (Iso.refl X') (Iso.refl Y) hpo.isoPushout.symm (by simp)
    (by simp) (by simp) (by simp)

end Global

end Stacks.Pushout

end
