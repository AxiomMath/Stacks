module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint

/-!
# Representability of a separated locally quasi-finite algebraic space descends along a
surjective étale chart of the base

The last paragraph of Stacks 03XW is this: the open subspace `U ⊆ X` whose base change
`T' ×_T U` has been shown to be a scheme over `T'` is itself a scheme, because `T' ⟶ W` is a
surjective étale covering of the open image `W ⊆ T` of `T'` and the base change is quasi-affine
over `T'`, so the descent datum it carries is effective.

This file proves that implication, in the shape in which it is consumed: for a morphism
`f : Z ⟶ yoneda.obj W` of algebraic spaces over `S` with representable target which is
separated and locally quasi-finite, and a morphism `q : T' ⟶ W` of the site whose underlying
morphism of schemes is surjective and étale, the mere *representability* of the base change
`Z ×_W T'` already makes `Z` representable.

Two inputs make this unconditional. The first is
`isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_locallyQuasiFinite_inf_lft` in
the namespace `AlgebraicGeometry.Space`,
effective descent along a surjective étale morphism of the site at the property of Stacks 02W8,
which rests on Tag 0247. The second is that the property descended is the one the hypotheses
already supply: no appeal to Tag 02LR is needed to turn the base change into a quasi-affine
morphism first, because separatedness, local quasi-finiteness and being locally of finite type
descend directly. Quasi-compactness of the base change is likewise not needed.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.presheaf_inverseImage_of_isRepresentable`: for a morphism to a
  representable presheaf whose source is representable, the relative form of a property of
  morphisms of schemes is the property of the corresponding morphism of schemes.
* `AlgebraicGeometry.Space.exists_openImage_surjective_etale`: **the covering `{T' ⟶ W}` of the
  last paragraph of Stacks 03XW.** An étale morphism of the big fppf category over `S` factors
  as a surjective étale morphism onto an object of the site whose underlying scheme is the open
  image, followed by an open immersion.
* `AlgebraicGeometry.Space.exists_lift_yoneda_of_forall_exists_factor`: a morphism to a
  representable presheaf factors through a monomorphism of the site as soon as each of its
  sections does.
* `AlgebraicGeometry.Space.isSeparated_of_mono`: **Stacks 042N**, and the separatedness clause
  of **Stacks 0463** — a monomorphism of presheaves is a separated morphism of algebraic spaces
  over `S`.
* `AlgebraicGeometry.Space.isSeparated_of_comp_mono` and
  `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_comp_etale`: separatedness and the
  every-étale-chart condition pass from a composite to its left factor, for a right factor
  which is respectively a monomorphism and étale after every representable base change.
* `AlgebraicGeometry.Space.isRepresentable_of_isRepresentable_pullback_of_surjectiveEtaleChart`:
  **the last paragraph of Stacks 03XW.** Representability of a separated, locally quasi-finite
  morphism to a representable presheaf descends along a surjective étale chart of the target.

## Implementation notes

Nothing here carries the tag 03XW: the tag also asserts that the image of `V'` in `X` is a
quasi-compact open subspace — which is
`AlgebraicGeometry.Space.isOpenSubspace_isQuasiCompactSpace_image_of_isQuasiAffineHom` in
`StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage` — and that it is representable, and the
latter is exactly what the hypothesis `hrep` below carries. The tag itself is proved, with no
hypothesis beyond its own, in
`StacksFrontier.AlgebraicGeometry.Spaces.ImageRepresentableInduction` as
`AlgebraicGeometry.Space.isOpenSubspace_isQuasiCompactSpace_isRepresentable_image`, and the two
things `hrep` needs are proved there as well. Producing `hrep` is the induction on the degrees of
the fibres of `T' ⟶ T`, which is
`AlgebraicGeometry.Space.isRepresentable_pullback_image_of_boundsFiberDegrees_aux`, its bound
coming from Tag 03JA (`AlgebraicGeometry.hasUniversallyBoundedFibers_of_locallyQuasiFinite`); and
the factorisation of the image `U ⟶ yoneda.obj T` through `yoneda.obj W` for the `W` which
`AlgebraicGeometry.Space.exists_openImage_surjective_etale` produces, which is what lets the
descent below be applied to `U` with the chart `T' ⟶ W`, is carried out in
`AlgebraicGeometry.Space.isRepresentable_image_of_isRepresentable_pullback_image`, the consumer
of the theorem below.

`AlgebraicGeometry.Space.IsSeparated` is the representable closed-immersion property of the
relative diagonal, and `AlgebraicGeometry.Space.IsLocallyQuasiFinite` is a condition on every
square of étale charts; both therefore have to be read off the representing object of the base
change before the scheme-level property which the descent consumes is available. For the second
this is a single instantiation of the chart condition at the representation itself; for the
first it is `AlgebraicGeometry.Space.isSeparated_yoneda_map_iff` (Tag 03KY), the transport of
the relative diagonal along `yoneda` and along `AlgebraicGeometry.BigFppfOver.toScheme`.

The passage from relative representability over a representable target to representability of
the source is Tag 03KC,
`CategoryTheory.Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable`.

## References

* [Stacks Project, Tag 03XW](https://stacks.math.columbia.edu/tag/03XW)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 02W5](https://stacks.math.columbia.edu/tag/02W5)
* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 042N](https://stacks.math.columbia.edu/tag/042N)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism `g : A ⟶ yoneda.obj T'` of presheaves on the big fppf site of `S` with
representable source has the relative form of a property `P` of morphisms of schemes as soon as
the morphism of schemes corresponding to it through a representation `e` of `A` has `P`.

Only `AlgebraicGeometry.BigFppfOver.presheaf_inverseImage_yoneda_map_iff` and the fact that the
relative property respects isomorphisms are used. -/
theorem presheaf_inverseImage_of_isRepresentable (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] [P.IsStableUnderBaseChange]
    {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T' : BigFppfOver B S hS} {g : A ⟶ yoneda.obj T'}
    {a : BigFppfOver B S hS} (e : yoneda.obj a ≅ A)
    (hP : P ((BigFppfOver.toScheme B S hS).map (yoneda.preimage (e.hom ≫ g)))) :
    (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf g := by
  have h1 : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf
      (yoneda.map (yoneda.preimage (e.hom ≫ g))) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ _).2 hP
  rw [Functor.map_preimage] at h1
  rw [show g = e.inv ≫ e.hom ≫ g by rw [Iso.inv_hom_id_assoc]]
  exact MorphismProperty.RespectsIso.precomp _ _ _ h1

/-! ### The open image of an étale morphism of the site -/

/-- **The covering `{T' ⟶ W}` of the last paragraph of Stacks 03XW.** An étale morphism
`t : T' ⟶ T` of the big fppf category over `S` factors as a surjective étale morphism onto an
object `W` of the site, followed by an open immersion `W ⟶ T` whose range is the image of `t`.

The underlying map of an étale morphism of schemes is open, so its range is an open subscheme of
the target, and an open subscheme of an object of the site is again an object of the site —
`AlgebraicGeometry.exists_restrict_bigFppfOver`, which also supplies the factorisation of `t`
itself through it. Surjectivity of the factor is the definition of the open set, read through
injectivity of the open immersion, and its étaleness is cancellation of the open immersion out
of `t`. -/
@[sga "1 V 3.5" "partial"]
theorem exists_openImage_surjective_etale {T' T : BigFppfOver B S hS} (t : T' ⟶ T)
    (ht : Etale ((BigFppfOver.toScheme B S hS).map t)) :
    ∃ (W : BigFppfOver B S hS) (q : T' ⟶ W) (w : W ⟶ T),
      q ≫ w = t ∧
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map w) ∧
        Set.range ((BigFppfOver.toScheme B S hS).map w) =
          Set.range ((BigFppfOver.toScheme B S hS).map t) ∧
        Surjective ((BigFppfOver.toScheme B S hS).map q) ∧
        Etale ((BigFppfOver.toScheme B S hS).map q) ∧
        ∀ {T'' : BigFppfOver B S hS} (g : T'' ⟶ T),
          Set.range ((BigFppfOver.toScheme B S hS).map g) ⊆
            Set.range ((BigFppfOver.toScheme B S hS).map t) →
            ∃ h : T'' ⟶ W, h ≫ w = g := by
  have _ht := ht
  obtain ⟨W, w, hwoi, hwrange, hfac⟩ := exists_restrict_bigFppfOver T
    ⟨Set.range ((BigFppfOver.toScheme B S hS).map t).base,
      ((BigFppfOver.toScheme B S hS).map t).isOpenMap.isOpen_range⟩
  obtain ⟨q, hq⟩ := hfac t (by rfl)
  have _hwoi := hwoi
  have hinj : Function.Injective ((BigFppfOver.toScheme B S hS).map w).base :=
    ((BigFppfOver.toScheme B S hS).map w).isOpenEmbedding.injective
  refine ⟨W, q, w, hq, hwoi, hwrange, ⟨?_⟩, ?_, fun g hg => hfac g hg⟩
  · intro z
    obtain ⟨x, hx⟩ := hwrange.subset (Set.mem_range_self z)
    refine ⟨x, hinj ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hq]
    exact hx
  · have hcomp : Etale ((BigFppfOver.toScheme B S hS).map q ≫
        (BigFppfOver.toScheme B S hS).map w) := by
      rw [← Functor.map_comp, hq]; exact ht
    exact MorphismProperty.HasOfPostcompProperty.of_postcomp (W' := @Etale)
      ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map w)
      inferInstance hcomp

/-- A morphism `f : Z ⟶ yoneda.obj T` of presheaves on the big fppf site of `S` factors
through a monomorphism `w : W ⟶ T` of the site as soon as each of its sections does.

The factorisation of a section is unique because `w` is a monomorphism, so the pointwise
factorisations are automatically natural; this is what turns the pointwise statement that the
image of a section lies in an open subscheme of `T` into a morphism of presheaves. -/
theorem exists_lift_yoneda_of_forall_exists_factor
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T W : BigFppfOver B S hS}
    {f : Z ⟶ yoneda.obj T} {w : W ⟶ T} (hw : Mono w)
    (hfac : ∀ (a : (BigFppfOver B S hS)ᵒᵖ) (x : Z.obj a),
      ∃ h : a.unop ⟶ W, h ≫ w = f.app a x) :
    ∃ g : Z ⟶ yoneda.obj W, g ≫ yoneda.map w = f := by
  classical
  have _hw := hw
  choose lift hlift using hfac
  refine ⟨{ app := fun a => ↾fun x => lift a x, naturality := ?_ }, ?_⟩
  · intro a b φ
    ext x
    have key : lift b (Z.map φ x) = φ.unop ≫ lift a x := by
      refine (cancel_mono w).1 ?_
      rw [hlift b (Z.map φ x), Category.assoc, hlift a x]
      simp
    simpa using key
  · ext a x
    exact hlift a x

/-! ### Transfer along a monomorphism of the target -/

/-- **Stacks 042N.** A monomorphism of presheaves on the big fppf site of `S` is a separated
morphism of algebraic spaces over `S`: its relative diagonal is an isomorphism, and an
isomorphism is a closed immersion. The statement is made for an arbitrary morphism of presheaves
on the big fppf site of `S`; no algebraic-space hypothesis is used.

This strictly generalises `AlgebraicGeometry.Space.isSeparated_of_isIso`, which is the same
statement for an isomorphism. -/
@[stacks 042N, stacks 0463 "separatedness"]
theorem isSeparated_of_mono {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (m : F ⟶ G) (hm : Mono m) :
    IsSeparated B S hS m := by
  have hid : MorphismProperty.ContainsIdentities
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have _hid : MorphismProperty.ContainsIdentities (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
  have _hri : MorphismProperty.RespectsIso (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
  have : IsIso (pullback.diagonal m) := (pullback.isIso_diagonal_iff m).2 hm
  exact MorphismProperty.presheaf_of_isIso _ (pullback.diagonal m)

/-- Separatedness of a morphism of algebraic spaces over `S` descends to a left factor whose
complementary right factor is a monomorphism.

For a monomorphism `m` the fibre product of `g` with itself is also the fibre product of `g ≫ m`
with itself (`CategoryTheory.Limits.pullbackIsPullbackOfCompMono`), and the two relative
diagonals agree under that identification. -/
theorem isSeparated_of_comp_mono {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : F ⟶ G) (m : G ⟶ H) (hm : Mono m) (h : IsSeparated B S hS (g ≫ m)) :
    IsSeparated B S hS g := by
  have _hm := hm
  set Q := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS) with hQ
  have sq : IsPullback (pullback.fst g g) (pullback.snd g g) (g ≫ m) (g ≫ m) :=
    IsPullback.of_isLimit (pullbackIsPullbackOfCompMono g g m)
  obtain ⟨e, hf, hs⟩ : ∃ e : (pullback g g : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) ≅
      pullback (g ≫ m) (g ≫ m),
      e.hom ≫ pullback.fst (g ≫ m) (g ≫ m) = pullback.fst g g ∧
        e.hom ≫ pullback.snd (g ≫ m) (g ≫ m) = pullback.snd g g :=
    ⟨sq.isoIsPullback _ _ (IsPullback.of_hasPullback (g ≫ m) (g ≫ m)),
      sq.isoIsPullback_hom_fst _ _ _, sq.isoIsPullback_hom_snd _ _ _⟩
  have hd : pullback.diagonal g ≫ e.hom = pullback.diagonal (g ≫ m) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hf]; simp
    · rw [Category.assoc, hs]; simp
  have h0 : Q.presheaf (pullback.diagonal (g ≫ m)) := h
  rw [← hd] at h0
  exact (Q.presheaf.cancel_right_of_respectsIso (pullback.diagonal g) e.hom).1 h0

/-- A property of morphisms of schemes which holds on every étale chart of `g ≫ m` holds on
every étale chart of `g`, for `m` étale after every representable base change: a chart square of
`g` is turned into one of `g ≫ m` by composing the chart of the target with `m`.

This is the converse direction of
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_etale_comp`, which composes on the *source*.
The name records that the cancelled right factor is étale; the cancellation
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_comp` asks nothing of the right factor and
instead asks that the property be étale local on source and target and cancel on the left. -/
theorem holdsOnEveryEtaleChart_of_comp_etale {P : MorphismProperty Scheme.{u}}
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : F ⟶ G) (m : G ⟶ H)
    (hm : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf m)
    (h : HoldsOnEveryEtaleChart B S hS P (g ≫ m)) :
    HoldsOnEveryEtaleChart B S hS P g := by
  have hmul := isMultiplicative_presheaf_etale B S hS
  intro U V a b k ha hb hcomm
  exact h U V a (b ≫ m) k ha (MorphismProperty.comp_mem _ b m hb hm)
    (by rw [← Category.assoc, hcomm, Category.assoc])

/-! ### The descent -/

/-- **The last paragraph of Stacks 03XW.** Let `f : Z ⟶ yoneda.obj W` be a separated, locally
quasi-finite morphism from an algebraic space over `S` to a representable presheaf, and let
`q : T' ⟶ W` be a morphism of the site whose underlying morphism of schemes is surjective and
étale. If the base change `Z ×_W T'` is representable then so is `Z`.

In the situation of Stacks 03XW, `Z` is the image `U ⊆ X` of `V'`, `W ⊆ T` is the open image of
`T'` and the base change is `T' ×_T U`, which the induction on the degrees of the fibres of
`T' ⟶ T` produces as a quasi-compact scheme.

The descent used is
`isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_locallyQuasiFinite_inf_lft` in
the namespace `AlgebraicGeometry.Space`,
effectivity along a surjective étale morphism of the site at the property of Stacks 02W8; it is
applied through `AlgebraicGeometry.Space.presheaf_of_surjectiveEtaleChart`, the representability
half of Stacks 03I2. The base change inherits separatedness from Tag 03KL and local
quasi-finiteness from Tag 03XL, and those two space-level properties are converted into the
scheme-level property of the descended morphism on the representing object of the base
change. -/
theorem isRepresentable_of_isRepresentable_pullback_of_surjectiveEtaleChart
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ : IsAlgebraicSpace B S hS Z)
    {W : BigFppfOver B S hS} (f : Z ⟶ yoneda.obj W)
    (hsep : IsSeparated B S hS f) (hlqf : IsLocallyQuasiFinite B S hS f)
    {T' : BigFppfOver B S hS} {q : T' ⟶ W}
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    (hrep : (pullback f (yoneda.map q)).IsRepresentable) :
    Z.IsRepresentable := by
  have _hbcP :=
    isSeparated_inf_locallyQuasiFinite_inf_locallyOfFiniteType_isStableUnderBaseChange.{u}
  have _hriP : MorphismProperty.RespectsIso
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  set g := pullback.snd f (yoneda.map q) with hg
  -- the base change, as a morphism of algebraic spaces over `S`
  have hsep' : IsSeparated B S hS g := isSeparated_pullbackSnd B S hS (yoneda.map q) hsep
  have hlqf' : IsLocallyQuasiFinite B S hS g :=
    IsLocallyQuasiFinite.of_isPullback B S hS (IsPullback.of_hasPullback f (yoneda.map q)).flip
      hZ (isAlgebraicSpace_yoneda B S hS W) hlqf
  -- the same properties, read off the representing object
  set e := (pullback f (yoneda.map q)).reprW with he
  set k := yoneda.preimage (e.hom ≫ g) with hk
  have hmap : yoneda.map k = e.hom ≫ g := Functor.map_preimage _ _
  have hsepk : _root_.AlgebraicGeometry.IsSeparated
      ((BigFppfOver.toScheme B S hS).map k) := by
    refine (isSeparated_yoneda_map_iff B S hS k).1 ?_
    rw [hmap]
    exact isSeparated_comp B S hS e.hom g (isSeparated_of_isIso B S hS e.hom) hsep'
  have hlqfk : ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      ((BigFppfOver.toScheme B S hS).map k) :=
    hlqf' _ T' e.hom (𝟙 (yoneda.obj T')) k (presheaf_etale_of_iso B S hS e)
      (presheaf_etale_of_iso B S hS (Iso.refl (yoneda.obj T'))) (by rw [hmap]; simp)
  -- the descent
  have hbc : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf g :=
    presheaf_inverseImage_of_isRepresentable _ e
      (by rw [← hk]; exact ⟨⟨hsepk, hlqfk.2⟩, hlqfk.1⟩)
  exact Functor.isRepresentable_of_relativelyRepresentable_of_target_isRepresentable _
    (presheaf_of_surjectiveEtaleChart
    (isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_locallyQuasiFinite_inf_lft B S hS)
    hZ.isSheaf (isAlgebraicSpace_yoneda B S hS W).isSheaf
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqs)
    ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ q).2 hqe) hbc).rep

end AlgebraicGeometry.Space

end
