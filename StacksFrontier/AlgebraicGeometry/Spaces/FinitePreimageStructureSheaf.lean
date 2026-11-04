module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSurjectiveIndexChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyNoetherianFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupportProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The structure sheaf of the inverse image of a closed subspace under a finite surjection

Let `f : Y ⟶ X` be a finite surjective morphism of algebraic spaces over a scheme `S` with `X`
locally Noetherian, let `i : Z ⟶ X` be a closed immersion, let `Z' = Y ×_X Z` be the inverse
image of `Z` and let `f' : Z' ⟶ Z` be the induced morphism.  Then `𝒢 = f'_*𝒪_{Z'}` is a
coherent `𝒪_Z`-module whose support is all of `Z`.  This is Stacks 0GF7.

Coherence and the support are independent of each other and are proved separately: coherence
needs the finiteness of `f` and the local Noetherianity of `X`, and the support needs only the
surjectivity of `f`.

## Main results

* `AlgebraicGeometry.Space.exists_isSurjective_index`: for an étale scheme chart `V` of the
  target of `f : X ⟶ Y` there is an étale scheme chart of `X` above `X ×_Y V` whose morphism to
  `X ×_Y V` is surjective on points.
* `AlgebraicGeometry.Space.one_ne_zero_structureRingSheaf_obj`: the ring of regular functions
  on a nonempty étale scheme chart of an algebraic space is not the zero ring.
* `AlgebraicGeometry.Space.one_ne_zero_structureRingSheafDirectImage`: the sections of `f_*𝒪_X`
  over an étale scheme chart `V` of `Y` form a nonzero ring as soon as the sections of `𝒪_X`
  over one étale scheme chart of `X` above `X ×_Y V` do.
* `AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_structureSheaf_eq_univ`: for a
  surjective morphism `f : X ⟶ Y` of algebraic spaces the support of `f_*𝒪_X` is all of `Y`.
* `AlgebraicGeometry.Space.isCoherent_modulePushforward_structureSheaf_preimage`: **the
  coherence assertion of Stacks 0GF7**, granted the chart case `hchart` of Stacks 03DW that
  Stacks 07UH already carries.
* `AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_structureSheaf_preimage_eq_univ`:
  **the support assertion of Stacks 0GF7**, unconditionally.

## Implementation notes

The inverse image of `Z` is taken as an arbitrary cartesian square `IsPullback i' f' f i` of
algebraic spaces rather than as the chosen fibre product, so the two assertions apply to any
presentation of `Y ×_X Z`.

`𝒢` is the `𝒪_Z`-module `(modulePushforward f').obj 𝒪_{Z'}` of Stacks 03LU.  Its underlying
abelian sheaf is, on the nose, the one underlying the sheaf of rings `f'_*𝒪_{Z'}` of
Stacks 03G8, so the support of Stacks 04KA may be computed with the unit sections: a point of
an étale chart of `Z` lies over a point of the support exactly when the unit section of
`f'_*𝒪_{Z'}` does not vanish near it, which is
`AlgebraicGeometry.Space.pointsMap_mem_supportOfSheaf_iff`.  Vanishing of that unit section on
a chart `V` would make the ring of sections of `f'_*𝒪_{Z'}` over `V` the zero ring; the
sections over `V` are the limit of the sections of `𝒪_{Z'}` over the étale scheme charts of
`Z'` above `Z' ×_Z V`, so one such chart with a point already contradicts that, and
surjectivity of `f'` produces a point of `Z' ×_Z V` from a point of `V`.

Coherence is Stacks 07UH applied to the coherent module `𝒪_{Z'}`: `Z` is locally Noetherian
because a closed immersion is locally of finite type (Stacks 06ED and 04ZK), `Z'` is locally
Noetherian because `f'` is finite hence locally of finite type, the structure sheaf of a
locally Noetherian algebraic space is coherent (Stacks 07UB), and `f'` is finite by
Stacks 03ZS.  `AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite` carries the
étale-site form of Stacks 01Y6, that is Stacks 03DW, as the named hypothesis `hchart`, which
this development does not have; that hypothesis is therefore carried here as well and is
recorded in the attribute string.

## References

* [Stacks Project, Lemma 69.17.1 (Tag 0GF7)](https://stacks.math.columbia.edu/tag/0GF7)
* [Stacks Project, Tag 07UH](https://stacks.math.columbia.edu/tag/07UH)
* [Stacks Project, Tag 07UB](https://stacks.math.columbia.edu/tag/07UB)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
* [Stacks Project, Tag 04KC](https://stacks.math.columbia.edu/tag/04KC)
* [Stacks Project, Tag 04ZK](https://stacks.math.columbia.edu/tag/04ZK)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
* [Stacks Project, Tag 03MH](https://stacks.math.columbia.edu/tag/03MH)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open Stacks.Sheaves.ToposPullback

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z Z' : AlgebraicSpaces B S hS}

attribute [local instance] pointTopology

/-! ### An étale chart surjecting onto a base-changed chart -/

/-- For an étale scheme chart `V` of the target of `f : X ⟶ Y` there is an étale scheme chart of
`X` above `X ×_Y V` whose morphism to `X ×_Y V` is surjective on points: an atlas of the
algebraic space `X ×_Y V`, composed with the structure morphism, is such a chart.

This is the hypothesis-free counterpart of
`AlgebraicGeometry.Space.exists_isAffine_isSurjective_index`, which produces an *affine* such
chart for a quasi-compact `f` over an affine chart `V`. -/
theorem exists_isSurjective_index (f : X ⟶ Y) (V : SmallEtale B S hS Y.1) :
    ∃ j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op,
      IsSurjective B S hS ((SpacesEtale.toSpaces B S hS X).map j.hom.unop).hom := by
  obtain ⟨W, p, hpsurj, hpetale⟩ :=
    ((SpacesEtale.toSpaces B S hS X).obj (chartBaseChange B S hS f V)).2.exists_atlas
  have hpE : IsEtale B S hS p := (isEtale_iff_presheaf_of_yoneda B S hS p).2 hpetale
  have hbEtale : IsEtale B S hS (p ≫
      (((SpacesEtale.inclusion B S hS X).obj (chartBaseChange B S hS f V)).hom.hom)) :=
    isEtale_comp B S hS hpE (chartBaseChange B S hS f V).property
  have hsurj : IsSurjective B S hS p :=
    (presheafSurjective_iff_isSurjective_yoneda B S hS
      ((SpacesEtale.toSpaces B S hS X).obj (chartBaseChange B S hS f V)).1
      ((SpacesEtale.toSpaces B S hS X).obj (chartBaseChange B S hS f V)).property W p).1 hpsurj
  refine ⟨StructuredArrow.mk
      (Y := op (⟨CostructuredArrow.mk (p ≫
          (((SpacesEtale.inclusion B S hS X).obj (chartBaseChange B S hS f V)).hom.hom)),
        presheaf_etale_of_isEtale B S hS hbEtale⟩ : SmallEtale B S hS X.1))
      (ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk p) rfl)).op, ?_⟩
  exact hsurj

/-! ### Nonvanishing of the unit section of a direct image of a structure sheaf -/

/-- The ring of regular functions on an étale scheme chart of an algebraic space which has a
point is not the zero ring: the germ at that point lands in a local ring. -/
theorem one_ne_zero_structureRingSheaf_obj (A : SmallEtale B S hS X.1)
    (w : ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A))) :
    (1 : ToType ((structureRingSheaf B S hS X).obj.obj (op A))) ≠ 0 := by
  intro h
  have h' : (1 : Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj A), ⊤)) = 0 := h
  have h2 := congrArg (((BigFppfOver.toScheme B S hS).obj
    ((SmallEtale.toOver B S hS X.1).obj A)).presheaf.germ ⊤ w trivial) h'
  simp at h2

/-- The sections of `f_*𝒪_X` over an étale scheme chart `V` of `Y` form a nonzero ring as soon
as the sections of `𝒪_X` over one étale scheme chart of `X` above `X ×_Y V` do.

The sections over `V` are the limit of the sections of `𝒪_X` over those charts, and the
projection of the limit to a chart is a ring homomorphism by
`AlgebraicGeometry.Space.chartProjection`, so it carries the unit section to the unit section
and the zero section to the zero section. -/
theorem one_ne_zero_structureRingSheafDirectImage (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (h : (1 : ToType ((structureRingSheaf B S hS X).obj.obj j.right)) ≠ 0) :
    (1 : ToType ((structureRingSheafDirectImage B S hS f).obj.obj (op V))) ≠ 0 := by
  intro h1
  refine h ?_
  have h2 : (1 : ToType ((pullbackRingSheaf.{u, u, u, u + 1, u, u + 1}
        (SmallEtale.topology B S hS Y.1) (smallEtaleDirectImageRan B S hS f)
        (structureRingSheaf B S hS X)).obj.obj (op V))) = 0 := by
    have hmap := congrArg (fun t ↦
      ((pullbackRingSheafMapOfNatTrans (SmallEtale.topology B S hS Y.1)
        (structureRingSheaf B S hS X)
        (smallEtaleDirectImageRanIso B S hS f).hom).hom.app (op V)).hom t) h1
    simpa using hmap
  have hone : (chartProjection B S hS f V j).app (structureSetSheaf B S hS X)
      (ringOneObj (structureRingSheaf B S hS X) (directImageSections B S hS f V)) =
      (1 : ToType ((structureRingSheaf B S hS X).obj.obj j.right)) :=
    (ringOneObj_naturality (structureRingSheaf B S hS X)
      (chartProjection B S hS f V j)).trans
      (sectionsFunctor_map_ringOneHom (structureRingSheaf B S hS X) j.right default)
  have hzero : (chartProjection B S hS f V j).app (structureSetSheaf B S hS X)
      (ringZeroObj (structureRingSheaf B S hS X) (directImageSections B S hS f V)) =
      (0 : ToType ((structureRingSheaf B S hS X).obj.obj j.right)) :=
    (ringZeroObj_naturality (structureRingSheaf B S hS X)
      (chartProjection B S hS f V j)).trans
      (sectionsFunctor_map_ringZeroHom (structureRingSheaf B S hS X) j.right default)
  have h3 : ringOneObj (structureRingSheaf B S hS X) (directImageSections B S hS f V) =
      ringZeroObj (structureRingSheaf B S hS X) (directImageSections B S hS f V) := h2
  rw [← hone, h3, hzero]

/-! ### The support of the direct image of a structure sheaf along a surjection -/

/-- The direct image of the structure sheaf along a surjective morphism of algebraic spaces has
full support: `supp(f_*𝒪_X) = |Y|` for every surjective `f : X ⟶ Y`.

The support of `f_*𝒪_X` is computed on an étale atlas `C` of `Y` by the unit sections
(Stacks 04KC): a point `y` of `C` lies over a point of the support exactly when the unit
section of `f_*𝒪_X` does not vanish near `y`.  Vanishing on a chart `V ⟶ C` through `y` would
make the ring of sections of `f_*𝒪_X` over `V` the zero ring, which
`AlgebraicGeometry.Space.one_ne_zero_structureRingSheafDirectImage` rules out: `V` has a point
over `y`, surjectivity of `f` lifts its image to `X`, and Stacks 03H4 turns the two into a
point of `X ×_Y V`, which an étale chart of `X` above `X ×_Y V` then reaches. -/
theorem supportOfSheaf_modulePushforward_structureSheaf_eq_univ (f : X ⟶ Y)
    (hf : IsSurjective B S hS f.hom) :
    supportOfSheaf B S hS Y.1 ((SheafOfModules.toSheaf _).obj
        ((modulePushforward B S hS f).obj
          (SheafOfModules.unit (structureRingSheaf B S hS X)))) = Set.univ := by
  refine Set.eq_univ_of_forall fun x ↦ ?_
  show x ∈ supportOfSheaf B S hS Y.1
    (toAddCommGrp B S hS Y.1 (structureRingSheafDirectImage B S hS f))
  obtain ⟨A, a, hsurj, hetale⟩ := Y.2.exists_atlas
  let C : SmallEtale B S hS Y.1 := ⟨CostructuredArrow.mk a, hetale⟩
  have hsurjC : Function.Surjective
      (pointsMap B S hS (yoneda.obj C.obj.left) C.obj.hom) :=
    (surjective_iff_surjective_pointsMap B S hS Y.1 Y.2 A a).1 hsurj
  obtain ⟨y, rfl⟩ := hsurjC x
  rw [pointsMap_mem_supportOfSheaf_iff B S hS Y.1 _ Y.2 C y]
  rintro ⟨V, g, hzero, y', hy'⟩
  have h1 : (1 : ToType ((structureRingSheafDirectImage B S hS f).obj.obj (op V))) = 0 := by
    have hr : ((structureRingSheafDirectImage B S hS f).obj.map g.op).hom
        (1 : ToType ((structureRingSheafDirectImage B S hS f).obj.obj (op C))) = 1 := map_one _
    rw [← hr]
    exact hzero
  obtain ⟨j, hj⟩ := exists_isSurjective_index B S hS f V
  have hVY : pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS Y.1).obj V))
      V.obj.hom y' = pointsMap B S hS (yoneda.obj C.obj.left) C.obj.hom y := by
    rw [← hy', ← pointsMap_comp_apply, yoneda_map_toOver_map_comp_hom g]
  obtain ⟨z, hz⟩ := hf (pointsMap B S hS (yoneda.obj C.obj.left) C.obj.hom y)
  obtain ⟨w, -, -⟩ := exists_point_of_isPullback B S hS
    ((spacesBaseChange B S hS f).isPullback ((comparisonFunctor B S hS Y).obj V))
    y' z (hVY.trans hz.symm)
  obtain ⟨t, -⟩ := hj w
  exact one_ne_zero_structureRingSheafDirectImage B S hS f V j
    (one_ne_zero_structureRingSheaf_obj B S hS j.right.unop (pointsToScheme B S hS _ t)) h1

/-! ### Stacks 0GF7 -/

/-- **The coherence assertion of Stacks 0GF7, granted the chart case `hchart`.**  Let
`f : Y ⟶ X` be a finite morphism of algebraic spaces over `S` with `X` locally Noetherian, let
`i : Z ⟶ X` be a closed immersion, and let `f' : Z' ⟶ Z` be the base change of `f` along `i`.
Then `𝒢 = f'_*𝒪_{Z'}` is a coherent `𝒪_Z`-module.

`Z` is locally Noetherian by Stacks 06ED and 04ZK, `f'` is finite by Stacks 03ZS, `Z'` is
locally Noetherian for the same reason as `Z`, and `𝒪_{Z'}` is then coherent by Stacks 07UB; so
this is `AlgebraicGeometry.Space.isCoherent_modulePushforward_of_isFinite`, whose hypothesis
`hchart` is the étale-site form of Stacks 01Y6, that is Stacks 03DW, which this development
does not carry.  Surjectivity of `f` is not used. -/
@[stacks 0GF7 "coherence of the direct image, granted the chart case hchart of Stacks 03DW \
which Tag 07UH already carries"]
theorem isCoherent_modulePushforward_structureSheaf_preimage (f : Y ⟶ X) (i : Z ⟶ X)
    {i' : Z' ⟶ Y} {f' : Z' ⟶ Z} (sq : IsPullback i' f' f i)
    (hf : IsFinite B S hS f.hom)
    (hX : HasEtaleLocalProperty B S hS X.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T))
    (hi : IsClosedImmersion B S hS i.hom)
    (V : SmallEtale B S hS Z.1) (hsurj : IsSurjective B S hS V.1.hom)
    (hchart : IsFinite B S hS (chartBaseChangeProjection B S hS f' V).hom →
      HasEtaleLocalProperty B S hS
        ((SpacesEtale.toSpaces B S hS Z).obj ((comparisonFunctor B S hS Z).obj V)).1
        (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) →
      IsCoherent B S hS Z'.1 Z'.2 (SheafOfModules.unit (structureRingSheaf B S hS Z')) →
      ((chartLocalizedModulePushforward B S hS f' V).obj
        ((moduleChartBaseChangeRestriction B S hS f' V).obj
          (SheafOfModules.unit (structureRingSheaf B S hS Z')))).IsCoherentOnSite) :
    IsCoherent B S hS Z.1 Z.2 ((modulePushforward B S hS f').obj
      (SheafOfModules.unit (structureRingSheaf B S hS Z'))) := by
  have hZ : HasEtaleLocalProperty B S hS Z.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Z.2 X.2 i.hom
      (isLocallyOfFiniteType_of_isImmersion B S hS i.hom
        (isImmersion_of_isClosedImmersion B S hS hi)) hX
  have hf' : IsFinite B S hS f'.hom :=
    isFinite_of_isPullback B S hS (AlgebraicSpaces.isPullback_hom B S hS sq) hf
  have hZ' : HasEtaleLocalProperty B S hS Z'.1 (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) :=
    isLocallyNoetherian_of_isLocallyOfFiniteType B S hS Z'.2 Z.2 f'.hom
      (isLocallyOfFiniteType_of_isFinite B S hS Z'.2 Z.2 hf') hZ
  have : Fact (HasEtaleLocalProperty B S hS Z'.1
    (fun T : Scheme.{u} ↦ IsLocallyNoetherian T)) := ⟨hZ'⟩
  exact isCoherent_modulePushforward_of_isFinite B S hS f' hf' hZ _
    (isCoherent_structureSheaf B S hS Z'.1 Z'.2) V hsurj hchart

/-- **The support assertion of Stacks 0GF7.**  Let `f : Y ⟶ X` be a surjective morphism of
algebraic spaces over `S`, let `i : Z ⟶ X` be any morphism and let `f' : Z' ⟶ Z` be the base
change of `f` along `i`.  Then the support of `𝒢 = f'_*𝒪_{Z'}` is all of `Z`.

Surjectivity is stable under base change by Stacks 03MH, so this is
`AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_structureSheaf_eq_univ`.  Neither the
finiteness of `f`, nor the local Noetherianity of `X`, nor the closedness of the immersion `i`
is used. -/
@[stacks 0GF7 "the support of the direct image is all of Z"]
theorem supportOfSheaf_modulePushforward_structureSheaf_preimage_eq_univ (f : Y ⟶ X) (i : Z ⟶ X)
    {i' : Z' ⟶ Y} {f' : Z' ⟶ Z} (sq : IsPullback i' f' f i)
    (hf : IsSurjective B S hS f.hom) :
    supportOfSheaf B S hS Z.1 ((SheafOfModules.toSheaf _).obj
        ((modulePushforward B S hS f').obj
          (SheafOfModules.unit (structureRingSheaf B S hS Z')))) = Set.univ :=
  supportOfSheaf_modulePushforward_structureSheaf_eq_univ B S hS f'
    (isSurjective_of_isPullback B S hS sq hf)

end AlgebraicGeometry.Space

end
