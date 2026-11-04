module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IsFibreSectionsFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFactorizationLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# The restriction of scalars along a finite morphism is étale over the base, in the separated case

Let `z : Z ⟶ Q` be a finite morphism of algebraic spaces over `S` and let `x : X ⟶ Z` be étale.
Sending a pair of Stacks 05Y9 for `(x, z)` to the pair of Stacks 04PC it defines, which is
`AlgebraicGeometry.Space.restrictionPairFinitePart`, is a morphism of presheaves from the
restriction of scalars `Res_{Z/Q}(X)` of Stacks 05YA to the finite part `(X/Q)_fin` of the
composite `x ≫ z`, and it is a monomorphism.

That comparison is in fact an open immersion: over a scheme-valued point of the finite part it
cuts out the locus on which the comparison of the named open subspace with `T ×_Q Z` becomes an
isomorphism, and that locus is open. Since the finite part of a separated morphism locally of
finite type is an algebraic space étale over `Q` by Stacks 04QH, the restriction of scalars is an
algebraic space étale over `Q` as soon as `x` is separated. **This is Stacks 05XR for a separated
`x`, in the form in which Stacks 05YD and Stacks 05YF consume it** — over an arbitrary base `Q`
rather than over the final algebraic space, and for an arbitrary finite `z` rather than for an
object of the site.

`StacksFrontier/AlgebraicGeometry/Spaces/SectionSpaceSeparated.lean` proves the absolute case, where
`Q` is the final algebraic space of the site and `Z` is an object of the site, for the space of
sections `AlgebraicGeometry.Space.sectionSpace`. Neither statement is an instance of the other,
and the arguments only look alike: there the ambient object is the product `T × Z` and the
comparison with it has to be assembled out of two projections, while here it is the fibre product
`T ×_Q Z` and the comparison *is* the base change of `x`, so no comparison with a product occurs
at all. What is needed downstream is the relative form, because the fibre of a morphism of
restrictions of scalars is a restriction of scalars over a representable base and not over the
final algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.finitePairZComparison`: the comparison of the open subspace of a pair
  of Stacks 04PC for `x ≫ z` with `T ×_Q Z`.
* `AlgebraicGeometry.Space.finitePairZProjection`: the projection of that open subspace to `T`.
* `AlgebraicGeometry.Space.restrictionOfScalarsToFinitePart`: the comparison morphism.

## Main results

* `AlgebraicGeometry.Space.mono_restrictionOfScalarsToFinitePart` and
  `AlgebraicGeometry.Space.isOpenImmersion_restrictionOfScalarsToFinitePart`: the comparison
  morphism is a monomorphism, and an open immersion.
* `AlgebraicGeometry.Space.exists_restrictionPairFinitePart_eq_iff`: a pair of Stacks 04PC comes
  from a pair for the restriction of scalars exactly when its comparison with `T ×_Q Z` is an
  isomorphism.
* `AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars_of_isSeparated` and
  `AlgebraicGeometry.Space.isEtale_projection_restrictionOfScalars_of_isSeparated`: **Stacks 05XR
  for a separated `x`, over an arbitrary base.**

## Implementation notes

The isomorphism locus used is the unconditional one for a flat morphism,
`AlgebraicGeometry.Space.exists_isOpenSubspace_iff_isIso_baseChange_of_isFlat`, available because
the comparison of the open subspace of a pair with `T ×_Q Z` is étale. In particular no
flat-locus hypothesis is carried, and no hypothesis of any kind: every input is an unconditional
result of the library.

Neither main result carries a `@[stacks]` attribute. The general case of Stacks 05XR, where `x`
is not assumed separated, is what the source states; the separated case is an intermediate step
of its proof, and the tag belongs on the general statement, which is
`AlgebraicGeometry.Space.isAlgebraicSpace_restrictionOfScalars` and
`AlgebraicGeometry.Space.isEtale_projection_restrictionOfScalars` in
`StacksFrontier/AlgebraicGeometry/Spaces/IsFibreSectionsGeneral.lean` and carries it.

## References

* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04QH](https://stacks.math.columbia.edu/tag/04QH)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05YA](https://stacks.math.columbia.edu/tag/05YA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Z Q : AlgebraicSpaces B S hS}

/-! ### The comparison of a pair of Stacks 04PC with `T ×_Q Z` -/

section Comparison

variable (x : X ⟶ Z) (z : Z ⟶ Q)

/-- **The comparison of the open subspace of a pair of Stacks 04PC for `x ≫ z` with
`T ×_Q Z`**: the inclusion of the open subspace followed by the base change of `x`. -/
noncomputable def finitePairZComparison {T : BigFppfOver B S hS}
    (q : FiniteOpenSubspace B S hS (x ≫ z) (schemeSpace T)) :
    q.subspace.toFunctor ⟶ pullback q.toBase.hom z.hom :=
  q.subspace.ι ≫ pairAmbientProjection x z q.toBase.hom

/-- **The projection of the open subspace of a pair of Stacks 04PC to the base.** -/
noncomputable def finitePairZProjection {T : BigFppfOver B S hS}
    (q : FiniteOpenSubspace B S hS (x ≫ z) (schemeSpace T)) :
    q.subspace.toFunctor ⟶ (schemeSpace T).obj :=
  q.subspace.ι ≫ pullback.fst q.toBase.hom (x ≫ z).hom

/-- The comparison of the open subspace of a pair with `T ×_Q Z`, followed by the projection to
`T`, is the projection of the open subspace to `T`. -/
theorem finitePairZComparison_comp_fst {T : BigFppfOver B S hS}
    (q : FiniteOpenSubspace B S hS (x ≫ z) (schemeSpace T)) :
    finitePairZComparison x z q ≫ pullback.fst q.toBase.hom z.hom =
      finitePairZProjection x z q := by
  simp only [finitePairZComparison, finitePairZProjection, Category.assoc,
    pairAmbientProjection_comp_fst]

/-- The comparison of the open subspace of a pair with `T ×_Q Z`, followed by the projection to
`Z`, is the projection of the open subspace to `X` followed by `x`. -/
theorem finitePairZComparison_comp_snd {T : BigFppfOver B S hS}
    (q : FiniteOpenSubspace B S hS (x ≫ z) (schemeSpace T)) :
    finitePairZComparison x z q ≫ pullback.snd q.toBase.hom z.hom =
      (q.subspace.ι ≫ pullback.snd q.toBase.hom (x ≫ z).hom) ≫ x.hom := by
  simp only [finitePairZComparison, Category.assoc, pairAmbientProjection_comp_snd]

/-- The projection of the open subspace of a pair to the base is finite. -/
theorem isFinite_finitePairZProjection {T : BigFppfOver B S hS}
    (q : FiniteOpenSubspace B S hS (x ≫ z) (schemeSpace T)) :
    IsFinite B S hS (finitePairZProjection x z q) :=
  q.finite_projection

/-- The comparison of the open subspace of a pair with `T ×_Q Z` is étale: the inclusion of an
open subspace is étale and so is the base change of `x`. -/
theorem isEtale_finitePairZComparison (hx : IsEtale B S hS x.hom) {T : BigFppfOver B S hS}
    (q : FiniteOpenSubspace B S hS (x ≫ z) (schemeSpace T)) :
    IsEtale B S hS (finitePairZComparison x z q) :=
  isEtale_comp B S hS
    (isEtale_of_presheafEtaleProperty B S hS _
      (presheaf_etale_of_isOpenImmersion B S hS q.isOpen.2))
    (isEtale_pairAmbientProjection x z hx q.toBase.hom)

/-- **The open locus in the base over which the comparison of a pair with `T ×_Q Z` becomes an
isomorphism.** The comparison is étale, hence flat and locally of finite presentation, the
projection of the open subspace to the base is finite, hence locally of finite type and
universally closed, and the projection `T ×_Q Z ⟶ T` is finite, hence separated and closed; so
the isomorphism locus of a flat morphism applies. -/
theorem exists_isOpenSubspace_finitePairZComparison_isIso (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) {T : BigFppfOver B S hS}
    (q : FiniteOpenSubspace B S hS (x ≫ z) (schemeSpace T)) :
    ∃ V : Subfunctor ((schemeSpace T).obj), IsOpenSubspace B S hS V ∧
      ∀ (A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS A)
        (g : A ⟶ (schemeSpace T).obj),
        (∃ r : A ⟶ V.toFunctor, r ≫ V.ι = g) ↔
          IsIso (baseChangeOverBase B S hS (finitePairZComparison x z q)
            (finitePairZProjection x z q) (pullback.fst q.toBase.hom z.hom)
            (finitePairZComparison_comp_fst x z q) g) := by
  have halgS := q.isOpen.1
  have halgP := isAlgebraicSpace_pullback_base z q.toBase.hom
  have halgT := isAlgebraicSpace_yoneda B S hS T
  have hfet := isEtale_finitePairZComparison x z hx q
  have hpproper := (isFinite_iff_isAffineHom_and_isProper B S hS halgS halgT
    (finitePairZProjection x z q)).mp (isFinite_finitePairZProjection x z q)
  have hqproper := (isFinite_iff_isAffineHom_and_isProper B S hS halgP halgT
    (pullback.fst q.toBase.hom z.hom)).mp (isFinite_pullback_fst_base z hz q.toBase.hom)
  exact exists_isOpenSubspace_iff_isIso_baseChange_of_isFlat B S hS halgS halgP halgT
    (finitePairZComparison x z q) (finitePairZProjection x z q)
    (pullback.fst q.toBase.hom z.hom) (finitePairZComparison_comp_fst x z q)
    (isFlat_of_isEtale B S hS hfet) (isLocallyOfFinitePresentation_of_isEtale B S hS hfet)
    hpproper.2.2.1.1 hpproper.2.2.2 hqproper.2.1
    (isClosed_of_universallyClosed B S hS halgT _ hqproper.2.2.2)

end Comparison

/-! ### Pairs of Stacks 04PC that come from a pair -/

section FromPair

variable {x : X ⟶ Z} {z : Z ⟶ Q}

/-- For a pair of Stacks 04PC coming from a pair the comparison with `T ×_Q Z` is the inverse of
the comparison of `T ×_Q Z` with the image of `AlgebraicGeometry.Space.pairLift`, hence an
isomorphism. -/
theorem finitePairZComparison_restrictionPairFinitePart (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) {T : BigFppfOver B S hS}
    (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    finitePairZComparison x z (restrictionPairFinitePart hx hz p) = (pairLiftRangeIso p).inv :=
  range_pairLift_ι_comp_pairAmbientProjection p

/-- **An open subspace of `T ×_Q X` whose comparison with `T ×_Q Z` is an isomorphism is the
image of the lift of a pair.** The inverse of the comparison, followed by the projection to `X`,
is the second component of the pair, and the image of its lift is the given subspace. -/
theorem exists_pairLift_range_eq {T : BigFppfOver B S hS} (a : yoneda.obj T ⟶ Q.obj)
    (Sq : Subfunctor (pullback a (x ≫ z).hom))
    (hiso : IsIso (Sq.ι ≫ pairAmbientProjection x z a)) :
    ∃ (l : pullback a z.hom ⟶ X.obj) (hl : l ≫ x.hom = pullback.snd a z.hom),
      Subfunctor.range
          (pairLift (⟨a, l, hl⟩ : RestrictionPair B S hS x z (yoneda.obj T))) = Sq := by
  set e := Sq.ι ≫ pairAmbientProjection x z a with he
  have hsnd : e ≫ pullback.snd a z.hom = (Sq.ι ≫ pullback.snd a (x ≫ z).hom) ≫ x.hom := by
    simp only [he, Category.assoc, pairAmbientProjection_comp_snd]
  have hfst : e ≫ pullback.fst a z.hom = Sq.ι ≫ pullback.fst a (x ≫ z).hom := by
    simp only [he, Category.assoc, pairAmbientProjection_comp_fst]
  have hl : (inv e ≫ Sq.ι ≫ pullback.snd a (x ≫ z).hom) ≫ x.hom = pullback.snd a z.hom := by
    rw [Category.assoc, ← hsnd, IsIso.inv_hom_id_assoc]
  refine ⟨inv e ≫ Sq.ι ≫ pullback.snd a (x ≫ z).hom, hl, ?_⟩
  have hlift : pairLift (⟨a, inv e ≫ Sq.ι ≫ pullback.snd a (x ≫ z).hom, hl⟩ :
      RestrictionPair B S hS x z (yoneda.obj T)) = inv e ≫ Sq.ι := by
    refine pullback.hom_ext ?_ ?_
    · rw [pairLift_comp_fst, Category.assoc, ← hfst, IsIso.inv_hom_id_assoc]
    · rw [pairLift_comp_snd]
      simp only [Category.assoc]
  rw [hlift, Subfunctor.range_comp, Subfunctor.range_eq_top, Subfunctor.image_top,
    Subfunctor.range_ι]

/-- **A pair of Stacks 04PC for `x ≫ z` comes from a pair for the restriction of scalars exactly
when its comparison with `T ×_Q Z` is an isomorphism.** -/
theorem exists_restrictionPairFinitePart_eq_iff (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) {T : BigFppfOver B S hS}
    (q : FiniteOpenSubspace B S hS (x ≫ z) (schemeSpace T)) :
    (∃ p : RestrictionPair B S hS x z (yoneda.obj T),
        restrictionPairFinitePart hx hz p = q) ↔ IsIso (finitePairZComparison x z q) := by
  constructor
  · rintro ⟨p, rfl⟩
    rw [finitePairZComparison_restrictionPairFinitePart]
    exact (pairLiftRangeIso p).isIso_inv
  · intro hiso
    obtain ⟨a, Sq, hSopen, hSfin⟩ := q
    obtain ⟨l, hl, rfl⟩ := exists_pairLift_range_eq a.hom Sq hiso
    exact ⟨⟨a.hom, l, hl⟩, rfl⟩

end FromPair

/-! ### The comparison morphism -/

section ToFinitePart

variable {x : X ⟶ Z} {z : Z ⟶ Q}

/-- **The comparison of the restriction of scalars `Res_{Z/Q}(X)` with the finite part
`(X/Q)_fin`**: a pair of Stacks 05Y9 is sent to the pair of Stacks 04PC it defines. -/
noncomputable def restrictionOfScalarsToFinitePart (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) :
    (restrictionOfScalars B S hS x z).presheaf ⟶
      (finiteOpenSubspacePresheaf B S hS (x ≫ z)).toFunctor where
  app T := ↾fun v =>
    ((finiteOpenSubspacePresheaf B S hS (x ≫ z)).sections T.unop).symm
      (restrictionPairFinitePart hx hz ((restrictionOfScalars B S hS x z).pairEquiv T.unop v))
  naturality := by
    rintro ⟨T⟩ ⟨T'⟩ f
    ext v
    change ((finiteOpenSubspacePresheaf B S hS (x ≫ z)).sections T').symm
        (restrictionPairFinitePart hx hz ((restrictionOfScalars B S hS x z).pairEquiv T'
          ((restrictionOfScalars B S hS x z).presheaf.map f.unop.op v))) =
      (finiteOpenSubspacePresheaf B S hS (x ≫ z)).toFunctor.map f.unop.op
        (((finiteOpenSubspacePresheaf B S hS (x ≫ z)).sections T).symm
          (restrictionPairFinitePart hx hz ((restrictionOfScalars B S hS x z).pairEquiv T v)))
    have hpair : (restrictionOfScalars B S hS x z).pairEquiv T'
          ((restrictionOfScalars B S hS x z).presheaf.map f.unop.op v) =
        RestrictionPair.restrict (yoneda.map f.unop)
          ((restrictionOfScalars B S hS x z).pairEquiv T v) :=
      RestrictionPair.eq_restrict_of_isPullbackAlong
        ((restrictionOfScalars B S hS x z).natural f.unop v)
    have h1 := (finiteOpenSubspacePresheaf B S hS (x ≫ z)).map_isBaseChange f.unop
      (((finiteOpenSubspacePresheaf B S hS (x ≫ z)).sections T).symm
        (restrictionPairFinitePart hx hz ((restrictionOfScalars B S hS x z).pairEquiv T v)))
    rw [Equiv.apply_symm_apply] at h1
    apply ((finiteOpenSubspacePresheaf B S hS (x ≫ z)).sections T').injective
    rw [Equiv.apply_symm_apply, hpair]
    exact FiniteOpenSubspace.IsBaseChange.unique B S hS
      (isBaseChange_restrictionPairFinitePart hx hz f.unop
        ((restrictionOfScalars B S hS x z).pairEquiv T v)) h1

/-- The components of the comparison morphism: a pair is sent to the pair of Stacks 04PC it
defines. -/
theorem restrictionOfScalarsToFinitePart_sections (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) (T : BigFppfOver B S hS)
    (v : (restrictionOfScalars B S hS x z).presheaf.obj (op T)) :
    (finiteOpenSubspacePresheaf B S hS (x ≫ z)).sections T
        ((restrictionOfScalarsToFinitePart hx hz).app (op T) v) =
      restrictionPairFinitePart hx hz ((restrictionOfScalars B S hS x z).pairEquiv T v) :=
  Equiv.apply_symm_apply _ _

/-- The comparison morphism is a monomorphism: a pair is determined by the pair of Stacks 04PC
it defines. -/
theorem mono_restrictionOfScalarsToFinitePart (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) : Mono (restrictionOfScalarsToFinitePart hx hz) := by
  rw [NatTrans.mono_iff_mono_app]
  rintro ⟨T⟩
  rw [mono_iff_injective]
  intro v v' hvv
  refine ((restrictionOfScalars B S hS x z).pairEquiv T).injective
    (restrictionPairFinitePart_injective hx hz ?_)
  rw [← restrictionOfScalarsToFinitePart_sections hx hz T v,
    ← restrictionOfScalarsToFinitePart_sections hx hz T v', hvv]

/-- A morphism of the site lies in a subfunctor of the presheaf its target represents exactly
when it factors through that subfunctor. -/
private theorem mem_subfunctor_iff' {T₀ : BigFppfOver B S hS}
    (V : Subfunctor ((schemeSpace T₀).obj)) {T' : BigFppfOver B S hS} (r : T' ⟶ T₀) :
    r ∈ V.obj (op T') ↔
      ∃ s : (schemeSpace T').obj ⟶ V.toFunctor,
        s ≫ V.ι = (yoneda.map r : (schemeSpace T').obj ⟶ (schemeSpace T₀).obj) := by
  constructor
  · intro hr
    refine ⟨Subfunctor.lift (yoneda.map r) ?_, Subfunctor.lift_ι _ _⟩
    rintro ⟨A⟩ _ ⟨y, rfl⟩
    exact V.map y.op hr
  · rintro ⟨s, hs⟩
    have hle : Subfunctor.range
        (yoneda.map r : (schemeSpace T').obj ⟶ (schemeSpace T₀).obj) ≤ V := by
      rw [← hs]
      exact (Subfunctor.range_comp_le s V.ι).trans (Subfunctor.range_ι V).le
    exact hle (op T') ⟨𝟙 T', by simp⟩

/-- A section over `T'` of a presheaf named by a morphism out of a representable presheaf is the
restriction of the section naming that morphism. -/
private theorem app_eq_map_app_id' {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {T₀ : BigFppfOver B S hS} (g : yoneda.obj T₀ ⟶ F) {T' : BigFppfOver B S hS}
    (r : T' ⟶ T₀) : g.app (op T') r = F.map r.op (g.app (op T₀) (𝟙 T₀)) := by
  simpa using NatTrans.naturality_apply g r.op (𝟙 T₀)

/-- **The comparison of a base-changed pair of Stacks 04PC with `T' ×_Q Z` is the base change of
the comparison of the original pair with `T ×_Q Z`**, up to the two canonical isomorphisms, so
one is an isomorphism exactly when the other is.

Every occurrence of the morphism `T' ⟶ T` is written with its target spelled as
`(schemeSpace T).obj` rather than as `yoneda.obj T`. The two are definitionally equal but not
syntactically so, and the first component of a pair of Stacks 04PC is a morphism out of
`(schemeSpace T).obj`, so a statement mixing the two spellings makes every rewrite below fail
its motive check. -/
private theorem isIso_finitePairZComparison_iff {T T' : BigFppfOver B S hS}
    (p : FiniteOpenSubspace B S hS (x ≫ z) (schemeSpace T))
    (q : FiniteOpenSubspace B S hS (x ≫ z) (schemeSpace T'))
    (k : (schemeSpace T').obj ⟶ (schemeSpace T).obj)
    (hbase : q.toBase.hom = k ≫ p.toBase.hom)
    (j : q.subspace.toFunctor ⟶ p.subspace.toFunctor)
    (hj : IsPullback (q.subspace.ι ≫ pullback.fst q.toBase.hom (x ≫ z).hom) j k
      (p.subspace.ι ≫ pullback.fst p.toBase.hom (x ≫ z).hom))
    (hjr : j ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom (x ≫ z).hom =
      q.subspace.ι ≫ pullback.snd q.toBase.hom (x ≫ z).hom) :
    IsIso (finitePairZComparison x z q) ↔
      IsIso (baseChangeOverBase B S hS (finitePairZComparison x z p)
        (finitePairZProjection x z p) (pullback.fst p.toBase.hom z.hom)
        (finitePairZComparison_comp_fst x z p) k) := by
  have hj' : IsPullback (finitePairZProjection x z q) j k (finitePairZProjection x z p) := hj
  have hbase' := IsPullback.of_hasPullback (finitePairZProjection x z p) k
  have hambbase := IsPullback.of_hasPullback (pullback.fst p.toBase.hom z.hom) k
  have hamb := isPullback_ambientBaseChangeMap z k p.toBase.hom q.toBase.hom hbase
  have he₁fst : (hj'.flip.isoIsPullback _ _ hbase').hom ≫
      pullback.fst (finitePairZProjection x z p) k = j :=
    hj'.flip.isoIsPullback_hom_fst _ _ hbase'
  have he₁snd : (hj'.flip.isoIsPullback _ _ hbase').hom ≫
      pullback.snd (finitePairZProjection x z p) k = finitePairZProjection x z q :=
    hj'.flip.isoIsPullback_hom_snd _ _ hbase'
  have he₂fst : (hamb.flip.isoIsPullback _ _ hambbase).hom ≫
      pullback.fst (pullback.fst p.toBase.hom z.hom) k =
      ambientBaseChangeMap z k p.toBase.hom q.toBase.hom hbase :=
    hamb.flip.isoIsPullback_hom_fst _ _ hambbase
  have he₂snd : (hamb.flip.isoIsPullback _ _ hambbase).hom ≫
      pullback.snd (pullback.fst p.toBase.hom z.hom) k = pullback.fst q.toBase.hom z.hom :=
    hamb.flip.isoIsPullback_hom_snd _ _ hambbase
  have hmid : finitePairZComparison x z q ≫
      ambientBaseChangeMap z k p.toBase.hom q.toBase.hom hbase =
      j ≫ finitePairZComparison x z p := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, ambientBaseChangeMap_comp_fst, ← Category.assoc,
        finitePairZComparison_comp_fst, Category.assoc, finitePairZComparison_comp_fst]
      exact hj'.w
    · rw [Category.assoc, ambientBaseChangeMap_comp_snd, Category.assoc,
        finitePairZComparison_comp_snd, finitePairZComparison_comp_snd, ← Category.assoc]
      exact congrArg (fun t => t ≫ x.hom) hjr.symm
  have hsq : finitePairZComparison x z q ≫ (hamb.flip.isoIsPullback _ _ hambbase).hom =
      (hj'.flip.isoIsPullback _ _ hbase').hom ≫
        baseChangeOverBase B S hS (finitePairZComparison x z p) (finitePairZProjection x z p)
          (pullback.fst p.toBase.hom z.hom) (finitePairZComparison_comp_fst x z p) k := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, he₂fst, Category.assoc]
      simp only [baseChangeOverBase, pullback.lift_fst]
      rw [← Category.assoc, he₁fst, hmid]
    · rw [Category.assoc, he₂snd, Category.assoc]
      simp only [baseChangeOverBase, pullback.lift_snd]
      rw [he₁snd, finitePairZComparison_comp_fst]
  rw [← isIso_comp_right_iff (finitePairZComparison x z q)
    (hamb.flip.isoIsPullback _ _ hambbase).hom, hsq, isIso_comp_left_iff]

/-- **The comparison of the restriction of scalars with the finite part is an open immersion.**
Over a scheme-valued point of the finite part, the sections of the restriction of scalars are the
morphisms of the site over which the comparison of the named pair with `T ×_Q Z` becomes an
isomorphism, and that locus is an open subspace. -/
theorem isOpenImmersion_restrictionOfScalarsToFinitePart (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) :
    IsOpenImmersion B S hS (restrictionOfScalarsToFinitePart hx hz) := by
  refine @isOpenImmersion_of_isOpenSubspace_range_preimage B S hS _ _
    (restrictionOfScalarsToFinitePart hx hz) (mono_restrictionOfScalarsToFinitePart hx hz) ?_
  intro T₀ g
  obtain ⟨V, hV, hVprop⟩ := exists_isOpenSubspace_finitePairZComparison_isIso x z hx hz
    ((finiteOpenSubspacePresheaf B S hS (x ≫ z)).sections T₀ (g.app (op T₀) (𝟙 T₀)))
  have key : ∀ (T' : BigFppfOver B S hS) (r : T' ⟶ T₀),
      g.app (op T') r ∈ Set.range ((restrictionOfScalarsToFinitePart hx hz).app (op T')) ↔
        r ∈ V.obj (op T') := by
    intro T' r
    obtain ⟨hqbase, jq, hjq, hjqr⟩ :=
      (finiteOpenSubspacePresheaf B S hS (x ≫ z)).map_isBaseChange r (g.app (op T₀) (𝟙 T₀))
    have h1 : (r ∈ V.obj (op T')) ↔
        IsIso (finitePairZComparison x z
          ((finiteOpenSubspacePresheaf B S hS (x ≫ z)).sections T'
            ((finiteOpenSubspacePresheaf B S hS (x ≫ z)).toFunctor.map r.op
              (g.app (op T₀) (𝟙 T₀))))) := by
      rw [mem_subfunctor_iff' V r,
        hVprop ((schemeSpace T').obj) (isAlgebraicSpace_yoneda B S hS T')
          (yoneda.map r : (schemeSpace T').obj ⟶ (schemeSpace T₀).obj)]
      exact (isIso_finitePairZComparison_iff _ _ _ hqbase jq hjq hjqr).symm
    rw [h1, ← exists_restrictionPairFinitePart_eq_iff hx hz]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨(restrictionOfScalars B S hS x z).pairEquiv T' v,
        (restrictionOfScalarsToFinitePart_sections hx hz T' v).symm.trans
          (congrArg ((finiteOpenSubspacePresheaf B S hS (x ≫ z)).sections T')
            (hv.trans (app_eq_map_app_id' g r)))⟩
    · rintro ⟨p, hp⟩
      refine ⟨((restrictionOfScalars B S hS x z).pairEquiv T').symm p, ?_⟩
      have hs := restrictionOfScalarsToFinitePart_sections hx hz T'
        (((restrictionOfScalars B S hS x z).pairEquiv T').symm p)
      rw [Equiv.apply_symm_apply, hp] at hs
      exact (((finiteOpenSubspacePresheaf B S hS (x ≫ z)).sections T').injective hs).trans
        (app_eq_map_app_id' g r).symm
  have hEq : (Subfunctor.range (restrictionOfScalarsToFinitePart hx hz)).preimage g = V :=
    le_antisymm (fun (T' : (BigFppfOver B S hS)ᵒᵖ) r hr => (key T'.unop r).1 hr)
      (fun (T' : (BigFppfOver B S hS)ᵒᵖ) r hr => (key T'.unop r).2 hr)
  rwa [hEq]

end ToFinitePart

/-! ### Stacks 05XR for a separated étale `x`, over an arbitrary base -/

section Separated

variable {x : X ⟶ Z} {z : Z ⟶ Q}

/-- The composite `x ≫ z : X ⟶ Q` is separated when `x` is: `z` is finite, hence separated, and
separatedness is stable under composition. -/
private theorem isSeparated_comp_of_isFinite (hz : IsFinite B S hS z.hom)
    (hxsep : IsSeparated B S hS x.hom) : IsSeparated B S hS (x ≫ z).hom :=
  isSeparated_comp B S hS x.hom z.hom hxsep
    (isSeparated_of_isFinite B S hS z.hom Z.property Q.property hz)

/-- The composite `x ≫ z : X ⟶ Q` is locally of finite type: `x` is étale and `z` is finite. -/
private theorem isLocallyOfFiniteType_comp_of_isFinite (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) : IsLocallyOfFiniteType B S hS (x ≫ z).hom :=
  isLocallyOfFiniteType_comp B S hS X.property Z.property Q.property x.hom z.hom
    (isLocallyOfFiniteType_of_isEtale B S hS Z.property hx)
    (isLocallyOfFiniteType_of_isFinite B S hS Z.property Q.property hz)

/-- **Stacks 05XR for a separated étale `x`, over an arbitrary base.** The restriction of scalars
`Res_{Z/Q}(X)` of a separated étale `x : X ⟶ Z` along a finite `z : Z ⟶ Q` is an algebraic space
over `S`. It receives an open immersion, in particular a representable morphism, into the finite
part of `x ≫ z`, which is an algebraic space by Stacks 04QH. -/
theorem isAlgebraicSpace_restrictionOfScalars_of_isSeparated (hx : IsEtale B S hS x.hom)
    (hxsep : IsSeparated B S hS x.hom) (hz : IsFinite B S hS z.hom) :
    IsAlgebraicSpace B S hS (restrictionOfScalars B S hS x z).presheaf :=
  isAlgebraicSpace_of_relativelyRepresentable B S hS (restrictionOfScalarsToFinitePart hx hz)
    (isOpenImmersion_restrictionOfScalarsToFinitePart hx hz).1
    (isAlgebraicSpace_finiteOpenSubspacePresheaf B S hS (x ≫ z)
      (isSeparated_comp_of_isFinite hz hxsep)
      (isLocallyOfFiniteType_comp_of_isFinite hx hz))

/-- The comparison of the restriction of scalars with the finite part lies over `Q`: both
projections read off the first component of a pair. -/
theorem restrictionOfScalarsToFinitePart_app_comp_baseMap (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) (T : BigFppfOver B S hS)
    (v : (restrictionOfScalars B S hS x z).presheaf.obj (op T)) :
    (finiteOpenSubspacePresheaf B S hS (x ≫ z)).baseMap.app (op T)
        ((restrictionOfScalarsToFinitePart hx hz).app (op T) v) =
      (restrictionOfScalars B S hS x z).projection.app (op T) v := by
  refine yonedaEquiv.symm.injective ?_
  rw [(finiteOpenSubspacePresheaf B S hS (x ≫ z)).baseMap_spec T
      ((restrictionOfScalarsToFinitePart hx hz).app (op T) v),
    restrictionOfScalarsToFinitePart_sections hx hz T v,
    restrictionPairFinitePart_toBase hx hz,
    (restrictionOfScalars B S hS x z).projection_pairEquiv T v, Equiv.symm_apply_apply]

/-- The comparison of the restriction of scalars with the finite part lies over `Q`: both
projections read off the first component of a pair. -/
theorem restrictionOfScalarsToFinitePart_comp_baseMap (hx : IsEtale B S hS x.hom)
    (hz : IsFinite B S hS z.hom) :
    restrictionOfScalarsToFinitePart hx hz ≫
        (finiteOpenSubspacePresheaf B S hS (x ≫ z)).baseMap =
      (restrictionOfScalars B S hS x z).projection := by
  ext T v
  exact restrictionOfScalarsToFinitePart_app_comp_baseMap hx hz T.unop v

/-- **Stacks 05XR for a separated étale `x`, over an arbitrary base.** The projection
`Res_{Z/Q}(X) ⟶ Q` of the restriction of scalars of a separated étale `x : X ⟶ Z` along a finite
`z : Z ⟶ Q` is étale. It is the comparison with the finite part of `x ≫ z`, which is an open
immersion, followed by the projection of the finite part to `Q`, which is étale by
Stacks 04QH. -/
theorem isEtale_projection_restrictionOfScalars_of_isSeparated (hx : IsEtale B S hS x.hom)
    (hxsep : IsSeparated B S hS x.hom) (hz : IsFinite B S hS z.hom) :
    IsEtale B S hS (restrictionOfScalars B S hS x z).projection := by
  rw [← restrictionOfScalarsToFinitePart_comp_baseMap hx hz]
  exact isEtale_comp B S hS
    (isEtale_of_presheafEtaleProperty B S hS _ (presheaf_etale_of_isOpenImmersion B S hS
      (isOpenImmersion_restrictionOfScalarsToFinitePart hx hz)))
    (isEtale_baseMap_finiteOpenSubspacePresheaf B S hS (x ≫ z)
      (isSeparated_comp_of_isFinite hz hxsep)
      (isLocallyOfFiniteType_comp_of_isFinite hx hz))

end Separated

end AlgebraicGeometry.Space

end
