module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.OpenImmersionMap
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension

/-!
# The finite part only sees the locally quasi-finite locus

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, and let `X' ⊆ X` be the maximal open subspace over which `f` is locally quasi-finite,
that is `AlgebraicGeometry.Space.locallyQuasiFinitePart` of Stacks 04NW. Then the finite part
of `f` and the finite part of `f|_{X'}` agree: the canonical injection
`(X'/Y)_fin ⟶ (X/Y)_fin` of Stacks 04PF is an isomorphism.

## Main definitions

* `AlgebraicGeometry.Space.locallyQuasiFinitePartSpace` and
  `AlgebraicGeometry.Space.locallyQuasiFinitePartInclusion`: the maximal locally quasi-finite
  open subspace of the source, packaged as an algebraic space over `S` together with its open
  immersion into the source.
* `AlgebraicGeometry.Space.finitePartIsoLocallyQuasiFinitePart`: the resulting isomorphism
  `(X'/Y)_fin ≅ (X/Y)_fin`.

## Main results

* `AlgebraicGeometry.Space.isIso_finiteOpenSubspaceMap_locallyQuasiFinitePart` — Stacks 04PG:
  the canonical map of Stacks 04PF for the inclusion of the maximal locally quasi-finite open
  subspace is an isomorphism of presheaves.

## Implementation notes

The source's `(X/Y)_fin = (X'/Y)_fin` is an equality of two separately constructed objects, so
it cannot be read as a propositional equality here: in this repository the finite part is a
`AlgebraicGeometry.Space.FinitePartPresheaf`, whose underlying presheaf is built by shrinking a
type of pairs, and the two sides of the source's equality are built from different data. What
the source means is that the evident map between them is a bijection, and that map already
exists: it is the monomorphism `AlgebraicGeometry.Space.finiteOpenSubspaceMap` of Stacks 04PF,
pinned down by its description on finite open pairs. So the statement taken here is that this
map is an isomorphism, together with the isomorphism itself. Nothing weaker would do: an
abstract isomorphism of the two presheaves would not say that it is compatible with the
projections to `Y` and with the open subspaces, whereas the 04PF map is.

The argument is the source's. Injectivity is Stacks 04PF, so only surjectivity on sections is
left. A section of `(X/Y)_fin` over a test scheme `T` is a morphism `a : T ⟶ Y` together with
an open subspace `Z` of `T ×_Y X` whose projection to `T` is finite. A finite morphism is
locally quasi-finite, Stacks 04NY, so `Z ⟶ T` is locally quasi-finite; by maximality of the
locally quasi-finite part of `T ×_Y X ⟶ T` the subspace `Z` is contained in it, and by
compatibility of the locally quasi-finite part with base change — the third clause of Stacks
04NW, `AlgebraicGeometry.Space.locallyQuasiFinitePart_preimage_of_isPullback` — that part is
the inverse image of `X'` in `T ×_Y X`. Hence `Z` lands in `T ×_Y X'`, where it is the inverse
image of itself along the open immersion `T ×_Y X' ⟶ T ×_Y X`, and that inverse image is a
finite open subspace of `T ×_Y X'` mapping to the given section.

The preimage subfunctor `CategoryTheory.Subfunctor.preimage` is used throughout rather than a
chosen fibre product, so "`Z` lands in `T ×_Y X'`" is literally a containment of subfunctors
and the lifted open subspace is `Z.preimage` of the comparison morphism; that the comparison
`Z.fromPreimage` is then an isomorphism is what transports finiteness back and forth.

## References

* [Stacks Project, Tag 04PG](https://stacks.math.columbia.edu/tag/04PG)
* [Stacks Project, Tag 04NW](https://stacks.math.columbia.edu/tag/04NW)
* [Stacks Project, Tag 04NY](https://stacks.math.columbia.edu/tag/04NY)
* [Stacks Project, Tag 04PD](https://stacks.math.columbia.edu/tag/04PD)
* [Stacks Project, Tag 04PF](https://stacks.math.columbia.edu/tag/04PF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance (priority := high) hasPullbacks_presheaf_locallyQuasiFinitePart :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-- Small products of presheaves on the big fppf site over `S` (instance search times out
without this shortcut). -/
private instance (priority := high) hasProducts_presheaf_locallyQuasiFinitePart :
    HasProducts.{0} ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  fun _ => Limits.functorCategoryHasLimitsOfShape

private instance (priority := high) hasPullback_presheaf_locallyQuasiFinitePart
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_locallyQuasiFinitePart B S hS).has_limit _

/-- The comparison morphism `T ×_Y X' ⟶ T ×_Y X` induced by a monomorphism `X' ⟶ X` over `Y`
is a monomorphism: its two components after the projections determine it, and the second one
is cancelled by the monomorphism. -/
@[sga "4 IV 8.5.1" "partial"]
private lemma mono_pullbackMap_of_mono {C : Type*} [Category C] [HasPullbacks C]
    {T X' X Y : C} (b : T ⟶ Y) (j : X' ⟶ X) (f : X ⟶ Y) [Mono j] :
    Mono (pullback.map b (j ≫ f) b f (𝟙 T) j (𝟙 Y) (by simp) (by simp)) := by
  refine ⟨fun {W} g h hgh => pullback.hom_ext ?_ ((cancel_mono j).mp ?_)⟩
  · simpa [pullback.map, pullback.lift_fst] using congrArg (· ≫ pullback.fst b f) hgh
  · simpa [pullback.map, pullback.lift_snd] using congrArg (· ≫ pullback.snd b f) hgh

/-- Finiteness of a morphism of algebraic spaces over `S` is unchanged by precomposition with
an isomorphism: an affine representative of a base change of the morphism is one of the
precomposition, after transporting the Cartesian square along the isomorphism. -/
private theorem isFinite_iso_hom_comp {A C D : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : A ≅ C)
    (f : C ⟶ D) (hf : IsFinite B S hS f) : IsFinite B S hS (e.hom ≫ f) := by
  intro U hU ξ
  obtain ⟨V, p, i, hV, hp, hs⟩ := hf U hU ξ
  refine ⟨V, p, i ≫ e.inv, hV, hp, ?_⟩
  simpa using hs.of_iso (Iso.refl _) e.symm (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

/-- If the inclusion of a subfunctor `Z` of the target of a monomorphism `a` factors through
`a`, then the comparison `Z.fromPreimage a` is an isomorphism: the factorization lands in the
inverse image and splits the comparison, which is itself a monomorphism as the base change of
the monomorphism `Z.ι`. -/
private lemma isIso_fromPreimage_of_factor {C : Type*} [Category C] {F G : Cᵒᵖ ⥤ Type u}
    (Z : Subfunctor G) (a : F ⟶ G) [Mono a] (b : Z.toFunctor ⟶ F) (hb : b ≫ a = Z.ι) :
    IsIso (Z.fromPreimage a) := by
  have hle : Subfunctor.range b ≤ Z.preimage a := by
    intro i x hx
    obtain ⟨z, rfl⟩ := hx
    show a.app i (b.app i z) ∈ Z.obj i
    have hb' : a.app i (b.app i z) = Z.ι.app i z := by
      simpa only [NatTrans.comp_app, comp_apply] using congrArg (fun k => k.app i z) hb
    rw [hb']
    exact z.property
  let b' : Z.toFunctor ⟶ (Z.preimage a).toFunctor := Subfunctor.lift b hle
  have hbsec : b' ≫ Z.fromPreimage a = 𝟙 Z.toFunctor := by
    apply (cancel_mono Z.ι).mp
    rw [Category.assoc, Subfunctor.fromPreimage_ι, ← Category.assoc, Subfunctor.lift_ι, hb]
    simp
  have _ : Mono (Z.fromPreimage a) := (Subfunctor.isPullback_preimage a Z).mono_fst_of_mono
  have _ : IsSplitEpi (Z.fromPreimage a) := IsSplitEpi.mk' ⟨b', hbsec⟩
  exact isIso_of_mono_of_isSplitEpi (Z.fromPreimage a)

/-- Two finite open pairs of Stacks 04PC with the same morphism to `Y` whose open subspaces are
identified compatibly with both projections of the ambient fibre product are equal: the two
inclusions then agree after an isomorphism, hence have the same range, and a subfunctor is the
range of its own inclusion. -/
private lemma finiteOpenSubspace_eq_of_common_source {X Y T : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (p q : FiniteOpenSubspace B S hS f T) (hbase : p.toBase = q.toBase)
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : W ≅ p.subspace.toFunctor)
    (e' : W ≅ q.subspace.toFunctor)
    (hfst : e.hom ≫ p.subspace.ι ≫ pullback.fst p.toBase.hom f.hom =
      e'.hom ≫ q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom)
    (hsnd : e.hom ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f.hom =
      e'.hom ≫ q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom) : p = q := by
  obtain ⟨b, Z, hZ, hfin⟩ := p
  obtain ⟨b', Z', hZ', hfin'⟩ := q
  dsimp only at hbase e e' hfst hsnd
  subst b'
  have hι : e.hom ≫ Z.ι = e'.hom ≫ Z'.ι := by
    apply pullback.hom_ext
    · simpa only [Category.assoc] using hfst
    · simpa only [Category.assoc] using hsnd
  have hZeq : Z = Z' := by
    have he : Epi e.hom := IsIso.epi_of_iso _
    have he' : Epi e'.hom := IsIso.epi_of_iso _
    have hr := congrArg Subfunctor.range hι
    rwa [Subfunctor.range_comp e.hom Z.ι, Subfunctor.range_comp e'.hom Z'.ι,
      @Subfunctor.range_eq_top _ _ _ _ _ he, @Subfunctor.range_eq_top _ _ _ _ _ he',
      Subfunctor.image_top Z.ι, Subfunctor.image_top Z'.ι, Subfunctor.range_ι,
      Subfunctor.range_ι] at hr
  subst Z'
  rfl

/-- A finite open pair of Stacks 04PC whose open subspace lands in an open subspace `U` of the
target of the morphism comes from a finite open pair for the restriction of the morphism to
`U`, with the same morphism to `Y` and an isomorphic open subspace.

The lifted open subspace is the inverse image of the given one along the comparison morphism
`T ×_Y U ⟶ T ×_Y X`; the containment hypothesis provides the factorization which makes that
comparison an isomorphism onto the given open subspace, and finiteness transports along it. -/
private lemma exists_finiteOpenSubspace_of_le_preimage {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (U : {U : Subfunctor X.obj // IsOpenSubspace B S hS U})
    (T : AlgebraicSpaces B S hS) (q : FiniteOpenSubspace B S hS f T)
    (hle : q.subspace ≤ U.1.preimage (pullback.snd q.toBase.hom f.hom)) :
    ∃ p : FiniteOpenSubspace B S hS
        ((ObjectProperty.homMk U.1.ι : (⟨U.1.toFunctor, U.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)
          ≫ f) T,
      p.toBase = q.toBase ∧
        ∃ k : p.subspace.toFunctor ≅ q.subspace.toFunctor,
          k.hom ≫ q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom =
            p.subspace.ι ≫ pullback.fst p.toBase.hom (U.1.ι ≫ f.hom) ∧
          k.hom ≫ q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom =
            p.subspace.ι ≫ pullback.snd p.toBase.hom (U.1.ι ≫ f.hom) ≫ U.1.ι := by
  classical
  let X' : AlgebraicSpaces B S hS := ⟨U.1.toFunctor, U.2.1⟩
  let j : X' ⟶ X := ObjectProperty.homMk U.1.ι
  have _ : Mono j.hom := inferInstanceAs (Mono U.1.ι)
  let g := pullback.map q.toBase.hom (j.hom ≫ f.hom) q.toBase.hom f.hom (𝟙 _) j.hom (𝟙 _)
    (by simp) (by simp)
  let W := q.subspace.preimage g
  have hWopen : IsOpenSubspace B S hS W :=
    isOpenSubspace_preimage B S hS g q.subspace
      (isAlgebraicSpace_pullback B S hS q.toBase.hom f.hom T.property X.property Y.property)
      (isAlgebraicSpace_pullback B S hS q.toBase.hom (j.hom ≫ f.hom) T.property X'.property
        Y.property)
      q.isOpen
  have hfac : Subfunctor.range (q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom) ≤ U.1 := by
    intro i z hz
    obtain ⟨x, rfl⟩ := hz
    exact hle i x.property
  let c := Subfunctor.lift (q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom) hfac
  let b := pullback.lift (f := q.toBase.hom) (g := j.hom ≫ f.hom)
    (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) c (by
      show (q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom) ≫ q.toBase.hom =
        c ≫ U.1.ι ≫ f.hom
      rw [← Category.assoc c, Subfunctor.lift_ι, Category.assoc, Category.assoc,
        pullback.condition])
  have hb : b ≫ g = q.subspace.ι := by
    apply pullback.hom_ext <;>
      simp [b, g, pullback.map, Category.assoc, c, j, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_snd_assoc]
  have _ : Mono g := mono_pullbackMap_of_mono q.toBase.hom j.hom f.hom
  have hiso : IsIso (q.subspace.fromPreimage g) :=
    isIso_fromPreimage_of_factor q.subspace g b hb
  let e : W.toFunctor ≅ q.subspace.toFunctor := asIso (q.subspace.fromPreimage g)
  have he : e.hom ≫ q.subspace.ι = W.ι ≫ g := Subfunctor.fromPreimage_ι _ _
  have hfst : e.hom ≫ q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom =
      W.ι ≫ pullback.fst q.toBase.hom (j.hom ≫ f.hom) := by
    rw [← Category.assoc, he, Category.assoc]; congr 1; simp [g, pullback.map, pullback.lift_fst]
  have hsnd : e.hom ≫ q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom =
      W.ι ≫ pullback.snd q.toBase.hom (j.hom ≫ f.hom) ≫ j.hom := by
    rw [← Category.assoc, he, Category.assoc]; congr 1; simp [g, pullback.map, pullback.lift_snd]
  have hfinite : IsFinite B S hS (W.ι ≫ pullback.fst q.toBase.hom (j.hom ≫ f.hom)) := by
    rw [← hfst]
    exact isFinite_iso_hom_comp B S hS e _ q.finite_projection
  exact ⟨⟨q.toBase, W, hWopen, hfinite⟩, rfl, e, hfst, hsnd⟩

/-- If every finite open pair of Stacks 04PC for `f` has its open subspace contained in the
inverse image of a fixed open subspace `U` of the source, then the canonical injection of
Stacks 04PF for the inclusion of `U` is an isomorphism.

Injectivity is Stacks 04PF; surjectivity on each test scheme is
`AlgebraicGeometry.Space.exists_finiteOpenSubspace_of_le_preimage`, whose lifted pair has the
same image under the 04PF map as the given pair by
`AlgebraicGeometry.Space.finiteOpenSubspace_eq_of_common_source`. -/
private theorem isIso_finiteOpenSubspaceMap_of_forall_le {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (U : {U : Subfunctor X.obj // IsOpenSubspace B S hS U})
    (hU : ∀ (T : AlgebraicSpaces B S hS) (q : FiniteOpenSubspace B S hS f T),
      q.subspace ≤ U.1.preimage (pullback.snd q.toBase.hom f.hom)) :
    IsIso (finiteOpenSubspaceMap B S hS
      (ObjectProperty.homMk U.1.ι : (⟨U.1.toFunctor, U.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X)
      ((ObjectProperty.homMk U.1.ι :
        (⟨U.1.toFunctor, U.2.1⟩ : AlgebraicSpaces B S hS) ⟶ X) ≫ f) f rfl U.2.2).1 := by
  classical
  let X' : AlgebraicSpaces B S hS := ⟨U.1.toFunctor, U.2.1⟩
  let j : X' ⟶ X := ObjectProperty.homMk U.1.ι
  let m := (finiteOpenSubspaceMap B S hS j (j ≫ f) f rfl U.2.2).1
  have hm : Mono m := (finiteOpenSubspaceMap B S hS j (j ≫ f) f rfl U.2.2).2.1
  have hEpi : Epi m := by
    have hApp : ∀ T, Epi (m.app T) := by
      intro T
      rw [epi_iff_surjective]
      intro s
      let P := finiteOpenSubspacePresheaf B S hS f
      let P' := finiteOpenSubspacePresheaf B S hS (j ≫ f)
      let q := P.sections T.unop s
      obtain ⟨p, hpbase, e, hfst, hsnd⟩ := exists_finiteOpenSubspace_of_le_preimage B S hS f U
        (schemeSpace T.unop) q (hU (schemeSpace T.unop) q)
      let s' := (P'.sections T.unop).symm p
      refine ⟨s', ?_⟩
      have hspec := (finiteOpenSubspaceMap B S hS j (j ≫ f) f rfl U.2.2).2.2 T.unop s'
      change (P'.sections T.unop s').toBase = _ ∧ _ at hspec
      have hps : P'.sections T.unop s' = p := (P'.sections T.unop).apply_symm_apply p
      rw [hps] at hspec
      obtain ⟨hbase, k, hk, hkfst, hksnd⟩ := hspec
      have _ : IsIso k := hk
      exact (P.sections T.unop).injective <|
        finiteOpenSubspace_eq_of_common_source B S hS f (P.sections T.unop (m.app T s')) q
          (hbase.symm.trans hpbase) (asIso k) e (hkfst.trans hfst.symm) (hksnd.trans hsnd.symm)
    exact NatTrans.epi_of_epi_app m
  exact isIso_of_mono_of_epi m

/-- Every finite open pair of Stacks 04PC for a morphism locally of finite type has its open
subspace contained in the inverse image of the maximal locally quasi-finite open subspace of
the source.

Its projection to the test space is finite, hence locally quasi-finite by Stacks 04NY, so by
maximality it lands in the locally quasi-finite part of the projection `T ×_Y X ⟶ T`; that part
is the inverse image of `AlgebraicGeometry.Space.locallyQuasiFinitePart` by the base-change
clause of Stacks 04NW. -/
private lemma finiteOpenSubspace_le_preimage_locallyQuasiFinitePart
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) (T : AlgebraicSpaces B S hS)
    (q : FiniteOpenSubspace B S hS f T) :
    q.subspace ≤
      (locallyQuasiFinitePart B S hS X.property Y.property f.hom hf).1.preimage
        (pullback.snd q.toBase.hom f.hom) := by
  have hQ : IsAlgebraicSpace B S hS (pullback q.toBase.hom f.hom) :=
    isAlgebraicSpace_pullback B S hS q.toBase.hom f.hom T.property X.property Y.property
  obtain ⟨hfQ, hEq⟩ := locallyQuasiFinitePart_preimage_of_isPullback B S hS
    (IsPullback.of_hasPullback q.toBase.hom f.hom).flip hQ X.property T.property Y.property hf
  have hmax := le_locallyQuasiFinitePart B S hS hQ T.property
    (pullback.fst q.toBase.hom f.hom) hfQ ⟨q.subspace, q.isOpen⟩
    (isQuasiFinite_of_isFinite B S hS _ q.isOpen.1 T.property q.finite_projection).1
  change q.subspace ≤ (locallyQuasiFinitePart B S hS hQ T.property
    (pullback.fst q.toBase.hom f.hom) hfQ).1 at hmax
  rwa [hEq] at hmax

/-- **Stacks 04NW, the canonical open subspace as an algebraic space.** The maximal open
subspace of the source of a morphism of algebraic spaces over `S` which is locally of finite
type over which the morphism is locally quasi-finite, regarded as an algebraic space over
`S`. -/
noncomputable def locallyQuasiFinitePartSpace {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) : AlgebraicSpaces B S hS :=
  ⟨(locallyQuasiFinitePart B S hS X.property Y.property f.hom hf).1.toFunctor,
    (locallyQuasiFinitePart B S hS X.property Y.property f.hom hf).2.1⟩

/-- The open immersion of the maximal locally quasi-finite open subspace of the source into the
source. -/
noncomputable def locallyQuasiFinitePartInclusion {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom) :
    locallyQuasiFinitePartSpace B S hS f hf ⟶ X :=
  ObjectProperty.homMk (locallyQuasiFinitePart B S hS X.property Y.property f.hom hf).1.ι

/-- The inclusion of the maximal locally quasi-finite open subspace of the source is an open
immersion. -/
theorem isOpenImmersion_locallyQuasiFinitePartInclusion {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) :
    IsOpenImmersion B S hS (locallyQuasiFinitePartInclusion B S hS f hf).hom :=
  (locallyQuasiFinitePart B S hS X.property Y.property f.hom hf).2.2

/-- **Stacks 04PG.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which
is locally of finite type and let `X' ⊆ X` be the maximal open subspace over which `f` is
locally quasi-finite, Stacks 04NW. Then `(X/Y)_fin = (X'/Y)_fin`, in the sense that the
canonical injection `(X'/Y)_fin ⟶ (X/Y)_fin` of Stacks 04PF is an isomorphism. -/
@[stacks 04PG]
theorem isIso_finiteOpenSubspaceMap_locallyQuasiFinitePart {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) :
    IsIso (finiteOpenSubspaceMap B S hS (locallyQuasiFinitePartInclusion B S hS f hf)
      (locallyQuasiFinitePartInclusion B S hS f hf ≫ f) f rfl
      (isOpenImmersion_locallyQuasiFinitePartInclusion B S hS f hf)).1 :=
  isIso_finiteOpenSubspaceMap_of_forall_le B S hS f
    (locallyQuasiFinitePart B S hS X.property Y.property f.hom hf)
    (finiteOpenSubspace_le_preimage_locallyQuasiFinitePart B S hS f hf)

/-- **Stacks 04PG, as an isomorphism.** The identification `(X'/Y)_fin ≅ (X/Y)_fin` of the
finite part of the restriction of `f` to its maximal locally quasi-finite open subspace with
the finite part of `f`, namely the canonical map of Stacks 04PF. -/
noncomputable def finitePartIsoLocallyQuasiFinitePart {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom) :
    (finiteOpenSubspacePresheaf B S hS
        (locallyQuasiFinitePartInclusion B S hS f hf ≫ f)).toFunctor ≅
      (finiteOpenSubspacePresheaf B S hS f).toFunctor :=
  haveI := isIso_finiteOpenSubspaceMap_locallyQuasiFinitePart B S hS f hf
  asIso (finiteOpenSubspaceMap B S hS (locallyQuasiFinitePartInclusion B S hS f hf)
    (locallyQuasiFinitePartInclusion B S hS f hf ≫ f) f rfl
    (isOpenImmersion_locallyQuasiFinitePartInclusion B S hS f hf)).1

end AlgebraicGeometry.Space

end
