module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelBirational
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.AbelTranslate
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.ProjectiveJacobian
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.PicardSchemeComponents
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.DenseSeparableClosedPoints
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparablyClosed
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyLocus
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.CohomologyClassDivisor
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.EtaleLocalStructure
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Picard scheme of a smooth projective curve over a separably closed field (Stacks 0BA0)

Let `k` be separably closed and `X` a smooth projective curve over `k`. Then `X` has a rational
point `σ` ([Stacks, Tag 056U]) and is geometrically irreducible ([Stacks, Tag 020J]). The
rigidified Picard functor `Pic_{X/k,σ}`, isomorphic to `Pic_{X/k}`, is represented by a group
scheme `P` ([Stacks, Tag 0B9Z]) which is the disjoint union of its degree components `P^d`,
`g`-dimensional smooth proper varieties whose rational points are the invertible modules of degree
`d`; `P^0` is an open and closed subgroup scheme; the Abel morphisms `γ_d : Hilb^d ⟶ P^d` are
surjective for `d ≥ g`, and `γ_g` is birational.

## Main results

* `Stacks.RigidifiedPicard.exists_section_of_smooth_of_isSepClosed` — the rational point.
* `Stacks.RigidifiedPicard.exists_picardScheme_of_claim` — [Stacks, Tag 0BA0] (1)–(4), (6) and
  the surjectivity half of (5), given the claim of [Stacks, Tag 0B9X].
* `Stacks.RigidifiedPicard.exists_representableBy_cohomologyLocus` — **[Stacks, Tag 0B9X]**.
* `Stacks.RigidifiedPicard.exists_grp_iso_functor_of_isSepClosed` — **[Stacks, Tag 0B9Z]**.

The claim of [Stacks, Tag 0B9X] is discharged by
`Stacks.WeilCohomology.cohomologyLocusDivisorExistence` and
`Stacks.WeilCohomology.cohomologyLocusDivisorUniqueness`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

universe u

namespace Stacks.RigidifiedPicard

/-- **A nonempty smooth scheme over a separably closed field has a rational point**: by
[Stacks, Tag 056U] it has a closed point with residue field finite separable over `k`, hence equal
to `k`. -/
@[sga "6 X 7.18.2" "(a), special case"]
theorem exists_section_of_smooth_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Smooth f] [Nonempty X] :
    ∃ σ : Spec (.of k) ⟶ X, σ ≫ f = 𝟙 _ := by
  obtain ⟨x, -, hfin, hsep⟩ :=
    (dense_closedPoints_with_finite_separable_residueField_of_smooth f).nonempty
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have hbij : Function.Bijective (algebraMap k (X.residueField x)) :=
    IsSepClosed.algebraMap_bijective k (X.residueField x)
  have : IsIso (CommRingCat.ofHom (algebraMap k (X.residueField x))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  refine ⟨Spec.map (inv (CommRingCat.ofHom (algebraMap k (X.residueField x)))) ≫
    X.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, ← SpecMap_algebraMap_residueField f x, ← Spec.map_comp, IsIso.hom_inv_id,
    Spec.map_id]

/-- A curve over a separably closed field is geometrically irreducible ([Stacks, Tag 020J]). -/
@[ega "IV 4.4.4" "special case"]
theorem geometricallyIrreducible_of_isCurve_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] : GeometricallyIrreducible f :=
  geometricallyIrreducible_of_irreducibleSpace_of_isSepClosed k X f

/-- A smooth geometrically irreducible curve is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one_of_isCurve (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] [GeometricallyIrreducible f] :
    SmoothOfRelativeDimension 1 f :=
  Stacks.Curves.smoothOfRelativeDimension_one_of_topologicalKrullDim_eq_one k f
    (by exact_mod_cast (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)))

/-- The fibres of a curve over a field have dimension at most one. -/
theorem topologicalKrullDim_fiber_le_one_of_isCurve (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] (s : Spec (.of k)) :
    topologicalKrullDim ↥(f.fiber s) ≤ 1 := by
  rw [topologicalKrullDim_fiber_spec f s]
  exact (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le

/-- A smooth curve over a field with a rational point is geometrically irreducible: it is
geometrically connected ([Stacks, Tag 04KV]), and a geometrically connected smooth scheme is
geometrically irreducible. -/
@[sga "4 XVIII 1.6.8" "special case"]
theorem geometricallyIrreducible_of_isCurve_of_section (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) :
    GeometricallyIrreducible f := by
  have hv : IsVariety k f := IsCurve.toIsVariety
  have : IsIntegral X := hv.toIsIntegral
  have : LocallyOfFiniteType f := hv.toLocallyOfFiniteType
  have : QuasiCompact f := hv.toQuasiCompact
  exact geometricallyIrreducible_of_geometricallyConnected_of_smooth f
    (geometricallyConnected_of_connectedSpace_of_section f σ hσ)

/-- **[Stacks, Tag 0B9X], given its claim.** Let `X` be a smooth projective curve of genus `g`
over a field `k`, with a rational point `σ`. The open subfunctor `F ⊆ Pic_{X/k,σ}` of
[Stacks, Tag 0B9V] is represented by an open subscheme of `Hilb^g_{X/k}`. -/
theorem exists_representableBy_cohomologyLocus_of_claim (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] (hproj : IsProjectiveMorphism f)
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)
    (hex : Stacks.WeilCohomology.CohomologyLocusDivisorExistence k)
    (hun : Stacks.WeilCohomology.CohomologyLocusDivisorUniqueness k) :
    haveI : IsProper f := isProper_of_isProjectiveMorphism f hproj
    haveI : GeometricallyIrreducible f := geometricallyIrreducible_of_isCurve_of_section k f σ hσ
    haveI : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve k f
    ∀ (H : Over (Spec (.of k)))
      (_ : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H (genus f)),
      ∃ W : H.left.Opens, Nonempty ((cohomologyLocus f σ hσ).toFunctor.RepresentableBy
        (Over.mk (W.ι ≫ H.hom))) := by
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  have : GeometricallyIrreducible f := geometricallyIrreducible_of_isCurve_of_section k f σ hσ
  have : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve k f
  intro H hH
  exact exists_representableBy_cohomologySubfunctor f σ hσ
    (perfectDerivedPushforward_of_baseChange baseChangeDerivedPushforward)
    baseChangeDerivedPushforward 0 hH (fun T c => hex f T c)
    (fun T Z Z' => hun f T Z Z')

/-- A choice of Hilbert scheme representing `Hilb^d_{X/k}` for each `d`, for a projective `f`. -/
private def hilbertRepresentative {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (hproj : IsProjectiveMorphism f) (d : ℕ) : Σ H : Over (Spec (.of k)),
      Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d :=
  (Stacks.Hilbert.exists_representsHilbertFunctorOfRank_of_isProjectiveMorphism
    (Over.mk f) hproj d).some

/-- `Pic⁰_{X/k,σ}` of a smooth projective curve over a separably closed field is represented by a
smooth group scheme, given the claim of [Stacks, Tag 0B9X]. -/
private theorem exists_smooth_grp_iso_functorZero_of_claim {k : Type u} [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    (hproj : IsProjectiveMorphism f) (hex : Stacks.WeilCohomology.CohomologyLocusDivisorExistence k)
    (hun : Stacks.WeilCohomology.CohomologyLocusDivisorUniqueness k) (σ : Spec (.of k) ⟶ X)
    (hσ : σ ≫ f = 𝟙 _) :
    haveI : IsProper f := isProper_of_isProjectiveMorphism f hproj
    haveI : GeometricallyIrreducible f := geometricallyIrreducible_of_isCurve_of_isSepClosed k f
    haveI : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve k f
    ∃ A : Grp (Over (Spec (.of k))), Nonempty (yonedaGrp.obj A ≅
      functorZero f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ) ∧ Smooth A.X.hom := by
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  have : GeometricallyIrreducible f := geometricallyIrreducible_of_isCurve_of_isSepClosed k f
  have : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve k f
  have hdimX : topologicalKrullDim X ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  have HH := hilbertRepresentative f hproj
  have h0 := Stacks.WeilCohomology.curveHasOneDimensionalSections k f
  have := GenusOne.isEffectiveCartierDivisor f h0 σ hσ
  set θ : Stacks.Picard.ofScheme X := genus f • Stacks.Divisors.picardClass
    (Scheme.IdealSheafData.vanishingIdeal
      (⟨{GenusOne.point σ}, GenusOne.isClosed_point f σ hσ⟩ : TopologicalSpace.Closeds X))
  have hθ : invertibleCurveDegreeHom k f hdimX θ = genus f := by
    rw [map_nsmul, invertibleCurveDegreeHom_divisorPicardClass_point k f hdimX h0 σ hσ,
      nsmul_eq_mul, mul_one]
  have h0B9Y : Stacks.WeilCohomology.PrescribedCohomologyTranslate k :=
    Stacks.WeilCohomology.prescribedCohomologyTranslate_of_isSepClosed k
  exact exists_smooth_grp_iso_functorZero f hdimX _ σ hσ θ hθ
    (fun d => (HH d).1) (fun d => (HH d).2) (fun T c => hex f T c) (fun T Z Z' => hun f T Z Z')
    (fun L _ _ c hc => h0B9Y f L c _ hc θ hθ)

/-- **[Stacks, Tag 0BA0] (1)–(4), (6) and the surjectivity half of (5), given the claim of
[Stacks, Tag 0B9X].** Let `k` be separably closed and `X` a smooth projective curve over `k`, of
genus `g`. There are a rational point `σ` and a group scheme `P` representing
`Pic_{X/k,σ} ≅ Pic_{X/k}` such that:
1. `P` is the disjoint union of the open and closed `P^d`, each a proper variety, smooth of
   relative dimension `g`, of dimension `g`;
2. the rational points of `P^d` are the invertible modules of degree `d` on `X`;
3. `P^0` is an open subgroup scheme;
4. for `H_d` representing `Hilb^d_{X/k}`, the Abel morphism `γ_d : H_d ⟶ P^d` classifies the
   rigidified class of `𝒪(D_univ)`;
5. `γ_d` is surjective for `d ≥ g`;
6. `γ_g` is birational. -/
theorem exists_picardScheme_of_claim (k : Type u) [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] (hproj : IsProjectiveMorphism f)
    (hex : Stacks.WeilCohomology.CohomologyLocusDivisorExistence k)
    (hun : Stacks.WeilCohomology.CohomologyLocusDivisorUniqueness k) :
    haveI : IsProper f := isProper_of_isProjectiveMorphism f hproj
    haveI : GeometricallyIrreducible f := geometricallyIrreducible_of_isCurve_of_isSepClosed k f
    haveI : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve k f
    ∃ (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (P : Grp (Over (Spec (.of k))))
      (e : yonedaGrp.obj P ≅ functor f σ hσ),
      -- (1)
      (∀ d d' : ℤ, d ≠ d' → Disjoint
        (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d : Set P.X.left)
        (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d')) ∧
      (⨆ d, degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d = ⊤) ∧
      (∀ d : ℤ,
        IsClopen (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d :
          Set P.X.left) ∧
        IsProperVariety k
          ((degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d).ι ≫
            P.X.hom) ∧
        SmoothOfRelativeDimension (genus f)
          ((degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d).ι ≫
            P.X.hom) ∧
        topologicalKrullDim
          (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d) =
            (genus f : WithBot ℕ∞)) ∧
      -- (2)
      (∀ d : ℤ, Set.BijOn (pointClassOf f σ hσ P e)
        {r | Set.range r.left ⊆
          (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d :
            Set P.X.left)}
        {c | invertibleCurveDegreeHom k f (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
          c = d}) ∧
      -- (3)
      (∃ K : OpenSubgroupScheme P, ∃ i : degreeLocusOver f
          (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e 0 ≅ K.carrier.X,
        degreeLocusι f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e 0 =
          i.hom ≫ K.ι.hom.hom) ∧
      ∀ (H : ℕ → Over (Spec (.of k)))
        (hH : ∀ d, Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) (H d) d),
        -- (4)
        (∀ d : ℕ,
          abelMorphismDegree f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e
              (hH d) ≫
            (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d).ι =
              (abelMorphismFull f σ hσ (hH d) P e).left ∧
          ∀ {T : Over (Spec (.of k))} (m : T ⟶ H d),
            (e.hom.app (op T)).hom (m ≫ abelMorphismFull f σ hσ (hH d) P e) =
              abelElementFull f σ hσ (hH d) m) ∧
        -- (5), surjectivity
        (∀ d : ℕ, genus f ≤ d → Surjective
          (abelMorphismDegree f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e
            (hH d))) ∧
        -- (6)
        IsBirational (abelMorphismDegree f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ
          P e (hH (genus f))) := by
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  have : GeometricallyIrreducible f := geometricallyIrreducible_of_isCurve_of_isSepClosed k f
  have : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve k f
  have hdimX : topologicalKrullDim X ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  have hdim := topologicalKrullDim_fiber_le_one_of_isCurve k f
  have : IsIntegral X := isIntegral_of_smooth_geometricallyIrreducible f
  obtain ⟨σ, hσ⟩ := exists_section_of_smooth_of_isSepClosed k f
  have HH := hilbertRepresentative f hproj
  obtain ⟨A, ⟨eA⟩, hA⟩ := exists_smooth_grp_iso_functorZero_of_claim f hproj hex hun σ hσ
  have := hA
  have : IsAbelianVariety k A.X := isAbelianVariety_of_iso_functorZero_field f hdim σ hσ eA hdimX
  have h0B9Y' := fun (K : Type u) [Field K] [Algebra k K] c =>
    exists_finrank_cohomologyOverField_add_schemePullbackClass_eq_one k K f c
  obtain ⟨P, ⟨e⟩, hP⟩ := exists_smooth_grp_iso_functor f hdimX σ hσ (fun d => (HH d).1)
    (fun d => (HH d).2) (fun T c => hex f T c) (fun T Z Z' => hun f T Z Z') h0B9Y'
  have := hP
  let : IsZariskiLocalAtSource (@SmoothOfRelativeDimension (genus f)) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine ⟨σ, hσ, P, e, fun d d' h => degreeLocus_disjoint f hdim σ hσ P e h,
    iSup_degreeLocus f hdim σ hσ P e, fun d => ⟨isClopen_degreeLocus f hdim σ hσ P e d,
      isProperVariety_degreeLocus f hdimX hdim σ hσ P e A eA d,
      IsZariskiLocalAtSource.comp hP _, topologicalKrullDim_degreeLocus_eq f hdimX hdim σ hσ P e d⟩,
    fun d => bijOn_pointClassOf f hdimX hdim σ hσ P e d,
    exists_openSubgroupScheme_degreeLocus_zero f hdim σ hσ P e, fun H hH =>
      ⟨fun d => ⟨abelMorphismDegree_ι f hdim σ hσ P e (hH d),
        fun m => abelMorphismFull_spec f σ hσ (hH d) P e m⟩,
      fun d hd => surjective_abelMorphismDegree f hdimX hdim σ hσ P e (hH d) hd,
      isBirational_abelMorphismDegree f hdimX hdim σ hσ P e H hH (fun T c => hex f T c)
        (fun T Z Z' => hun f T Z Z') h0B9Y'⟩⟩

/-- **[Stacks, Tag 0B9Z], given the claim of [Stacks, Tag 0B9X].** The Picard functor of a
smooth projective curve over a separably closed field is representable: for a rational point `σ`,
`Pic_{X/k,σ} ≅ Pic_{X/k}` is represented by a group scheme over `k`. -/
theorem exists_grp_iso_functor_of_claim (k : Type u) [Field k] [IsSepClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] (hproj : IsProjectiveMorphism f)
    (hex : Stacks.WeilCohomology.CohomologyLocusDivisorExistence k)
    (hun : Stacks.WeilCohomology.CohomologyLocusDivisorUniqueness k) :
    haveI : IsProper f := isProper_of_isProjectiveMorphism f hproj
    ∃ (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (P : Grp (Over (Spec (.of k)))),
      Nonempty (yonedaGrp.obj P ≅ functor f σ hσ) := by
  obtain ⟨σ, hσ, P, e, -⟩ := exists_picardScheme_of_claim k f hproj hex hun
  exact ⟨σ, hσ, P, ⟨e⟩⟩

/-- **[Stacks, Tag 0B9X].** Let `k` be a field and `X` a smooth projective curve of genus `g` over
`k` with a rational point `σ`. The open subfunctor `F ⊆ Pic_{X/k,σ}` of [Stacks, Tag 0B9V] is
representable by an open subscheme of `Hilb^g_{X/k}`. -/
@[stacks 0B9X]
theorem exists_representableBy_cohomologyLocus (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f] (hproj : IsProjectiveMorphism f)
    (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) :
    haveI : IsProper f := isProper_of_isProjectiveMorphism f hproj
    haveI : GeometricallyIrreducible f := geometricallyIrreducible_of_isCurve_of_section k f σ hσ
    haveI : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve k f
    ∀ (H : Over (Spec (.of k)))
      (_ : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H (genus f)),
      ∃ W : H.left.Opens, Nonempty ((cohomologyLocus f σ hσ).toFunctor.RepresentableBy
        (Over.mk (W.ι ≫ H.hom))) :=
  exists_representableBy_cohomologyLocus_of_claim k f hproj σ hσ
    (Stacks.WeilCohomology.cohomologyLocusDivisorExistence k)
    (Stacks.WeilCohomology.cohomologyLocusDivisorUniqueness k)

/-- **[Stacks, Tag 0B9Z].** The Picard functor of a smooth projective curve `X` over a separably
closed field `k` is representable: for a rational point `σ`, the rigidified Picard functor
`Pic_{X/k,σ} ≅ Pic_{X/k}` is represented by a group scheme over `k`. -/
@[stacks 0B9Z "as the rigidified functor Pic_{X/k,σ} at a rational point σ, which the source's \
proof identifies with Pic_{X/k}"]
theorem exists_grp_iso_functor_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    (hproj : IsProjectiveMorphism f) :
    haveI : IsProper f := isProper_of_isProjectiveMorphism f hproj
    ∃ (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (P : Grp (Over (Spec (.of k)))),
      Nonempty (yonedaGrp.obj P ≅ functor f σ hσ) :=
  exists_grp_iso_functor_of_claim k f hproj
    (Stacks.WeilCohomology.cohomologyLocusDivisorExistence k)
    (Stacks.WeilCohomology.cohomologyLocusDivisorUniqueness k)

/-- **The Abel morphism of degree `d ≥ 2g - 1` is smooth**, for a smooth proper geometrically
irreducible curve over a field with a rational point: the smoothness clause of
[Stacks, Tag 0BA0] (5), for the Abel morphism into the group scheme representing `Pic⁰`.
Stated as a proposition so that its proof can be supplied separately. -/
def AbelMorphismSmooth : Prop :=
  ∀ {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] [Smooth f]
    [GeometricallyIrreducible f] [SmoothOfRelativeDimension 1 f]
    (hdim : ∀ s, topologicalKrullDim ↥(f.fiber s) ≤ 1) (σ : Spec (.of k) ⟶ X)
    (hσ : σ ≫ f = 𝟙 _) (θ : Stacks.Picard.ofScheme X) {d : ℕ}
    (hθ : ∀ s, relativeInvertibleDegreeHomAt f hdim s θ = d) {H : Over (Spec (.of k))}
    (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) H d)
    (A : Grp (Over (Spec (.of k)))) (eA : yonedaGrp.obj A ≅ functorZero f hdim σ hσ)
    [LocallyOfFiniteType A.X.hom], 2 * (genus f : ℤ) - 1 ≤ d →
      Smooth (abelMorphism f hdim σ hσ θ hθ hH A eA).left

/-- **[Stacks, Tag 0BA0]**, given the smoothness of the Abel morphisms of degree `d ≥ 2g - 1`
(`AbelMorphismSmooth`). -/
theorem exists_picardScheme_of_abelMorphismSmooth (k : Type u) [Field k] [IsSepClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsCurve k f] [Smooth f]
    (hproj : IsProjectiveMorphism f) (hsm : AbelMorphismSmooth.{u}) :
    haveI : IsProper f := isProper_of_isProjectiveMorphism f hproj
    haveI : GeometricallyIrreducible f := geometricallyIrreducible_of_isCurve_of_isSepClosed k f
    haveI : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve k f
    ∃ (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _) (P : Grp (Over (Spec (.of k))))
      (e : yonedaGrp.obj P ≅ functor f σ hσ),
      -- (1)
      (∀ d d' : ℤ, d ≠ d' → Disjoint
        (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d : Set P.X.left)
        (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d')) ∧
      (⨆ d, degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d = ⊤) ∧
      (∀ d : ℤ,
        IsClopen (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d :
          Set P.X.left) ∧
        IsProperVariety k
          ((degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d).ι ≫
            P.X.hom) ∧
        SmoothOfRelativeDimension (genus f)
          ((degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d).ι ≫
            P.X.hom) ∧
        topologicalKrullDim
          (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d) =
            (genus f : WithBot ℕ∞)) ∧
      -- (2)
      (∀ d : ℤ, Set.BijOn (pointClassOf f σ hσ P e)
        {r | Set.range r.left ⊆
          (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d :
            Set P.X.left)}
        {c | invertibleCurveDegreeHom k f (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
          c = d}) ∧
      -- (3)
      (∃ K : OpenSubgroupScheme P, ∃ i : degreeLocusOver f
          (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e 0 ≅ K.carrier.X,
        degreeLocusι f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e 0 =
          i.hom ≫ K.ι.hom.hom) ∧
      ∀ (H : ℕ → Over (Spec (.of k)))
        (hH : ∀ d, Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk f) (H d) d),
        -- (4)
        (∀ d : ℕ,
          abelMorphismDegree f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e
              (hH d) ≫
            (degreeLocus f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e d).ι =
              (abelMorphismFull f σ hσ (hH d) P e).left ∧
          ∀ {T : Over (Spec (.of k))} (m : T ⟶ H d),
            (e.hom.app (op T)).hom (m ≫ abelMorphismFull f σ hσ (hH d) P e) =
              abelElementFull f σ hσ (hH d) m) ∧
        -- (5), surjectivity
        (∀ d : ℕ, genus f ≤ d → Surjective
          (abelMorphismDegree f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e
            (hH d))) ∧
        -- (5), smoothness
        (∀ d : ℕ, 2 * (genus f : ℤ) - 1 ≤ d → Smooth
          (abelMorphismDegree f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ P e
            (hH d))) ∧
        -- (6)
        IsBirational (abelMorphismDegree f (topologicalKrullDim_fiber_le_one_of_isCurve k f) σ hσ
          P e (hH (genus f))) := by
  have : IsProper f := isProper_of_isProjectiveMorphism f hproj
  have : GeometricallyIrreducible f := geometricallyIrreducible_of_isCurve_of_isSepClosed k f
  have : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve k f
  have hdimX : topologicalKrullDim X ≤ 1 :=
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)).le
  have hdim := topologicalKrullDim_fiber_le_one_of_isCurve k f
  have hex : Stacks.WeilCohomology.CohomologyLocusDivisorExistence k :=
    Stacks.WeilCohomology.cohomologyLocusDivisorExistence k
  have hun : Stacks.WeilCohomology.CohomologyLocusDivisorUniqueness k :=
    Stacks.WeilCohomology.cohomologyLocusDivisorUniqueness k
  obtain ⟨σ, hσ, P, e, h1, h2, h3, h4, h5, h6⟩ := exists_picardScheme_of_claim k f hproj hex hun
  obtain ⟨A, ⟨eA⟩, hA⟩ := exists_smooth_grp_iso_functorZero_of_claim f hproj hex hun σ hσ
  have := hA
  have : LocallyOfFiniteType A.X.hom := inferInstance
  refine ⟨σ, hσ, P, e, h1, h2, h3, h4, h5, fun H hH =>
    ⟨(h6 H hH).1, (h6 H hH).2.1, fun d hd => ?_, (h6 H hH).2.2⟩⟩
  obtain ⟨θd, hθd⟩ := exists_degree_eq f hdimX hdim σ hσ d
  have := hsm f hdim σ hσ θd hθd (hH d) A eA (by omega)
  exact smooth_abelMorphismDegree_of_smooth_abelMorphism f hdim σ hσ P e θd hθd A eA (hH d)

end Stacks.RigidifiedPicard

end
