module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Misc.PointFactorization
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleAtlasQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FiniteSchemeFiltration
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedSingleton
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.FppfCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyCompactPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceGeneralizations
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.MonomorphismPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsMono
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactMonomorphicFieldRepresentative
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedFactorThroughClosedSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Factoring a morphism with singleton image through a residual space

Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` whose image on points is a single
point `x` of `|X|`, with `Y` reduced, and suppose `x` is represented by a quasi-compact
monomorphism from the spectrum of a field. That monomorphism exhibits its source as a residual
space of `X` at `x`, and `f` factors through it.

## Main results

* `AlgebraicGeometry.Space.isResidualSpaceAt_fieldMorphism_of_mono`: a monomorphic field-valued
  representative of `x` is a residual space of `X` at `x`.
* `AlgebraicGeometry.Space.exists_comp_fieldMorphism_eq_of_range_pointsMap_subset_singleton`:
  **Stacks 0H1T**, the factorization.
* `AlgebraicGeometry.Space.exists_isResidualSpaceAt_comp_fieldMorphism_eq_of_isDecentSpace`:
  the same with hypothesis (3) supplied by decency of the target.

## Implementation notes

A residual space is the predicate `AlgebraicGeometry.Space.IsResidualSpaceAt` of Stacks 06R0
on a monomorphism, not a chosen subobject, and the identification of it with the spectrum of
the field of hypothesis (3) is `isResidualSpaceAt_fieldMorphism_of_mono`, which needs neither
half of Stacks 06QZ: the spectrum of a field is reduced, locally Noetherian and has one point,
and that point goes to `x` because the representative represents `x`. The factorization is
therefore stated through `AlgebraicGeometry.Space.fieldMorphism`, the morphism presented by
that representative.

The argument is the one of the source. A quasi-compact open subspace `V` containing `x` exists
by Stacks 04NN and Stacks 03BZ, and both `f` and the representative factor through it by
Stacks 03IE, the representative staying quasi-compact because it factors through a
monomorphism. Stacks 0BBN then puts the point in a stratum of a scheme stratification of `V`:
a reduced closed subspace of an open subspace of `V` which is a scheme. Factoring once more
through that open subspace by Stacks 03IE and through the stratum by Stacks 03JJ — this is
where reducedness of `Y` is used — leaves a morphism of a reduced algebraic space into a
representable presheaf whose image on points is one point. On a surjective étale scheme chart
of `Y` that case is Stacks 0H1M, through the canonical representative
`AlgebraicGeometry.Space.schemePointRepresentative` above the image point, which Stacks 0H2X
then compares with the given representative; the resulting factorization of the chart descends
to `Y` because the chart is locally surjective for the fppf topology by Stacks 05VM and the
range of a monomorphism of sheaves is a subsheaf.

## References

* [Stacks Project, Tag 0H1T](https://stacks.math.columbia.edu/tag/0H1T)
* [Stacks Project, Tag 06R0](https://stacks.math.columbia.edu/tag/06R0)
* [Stacks Project, Tag 0BBN](https://stacks.math.columbia.edu/tag/0BBN)
* [Stacks Project, Tag 0H1M](https://stacks.math.columbia.edu/tag/0H1M)
* [Stacks Project, Tag 0H2X](https://stacks.math.columbia.edu/tag/0H2X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Preliminaries -/

/-- The pointwise form of functoriality of the map on points. -/
private theorem pointsMap_comp_point
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : F ⟶ G) (β : G ⟶ H)
    (z : points B S hS F) :
    pointsMap B S hS F (α ≫ β) z = pointsMap B S hS G β (pointsMap B S hS F α z) :=
  congrFun (pointsMap_comp B S hS F α β) z

/-- Every point of an algebraic space over `S` lies in a quasi-compact open subspace: the
quasi-compact open neighbourhoods of the point are a fundamental system by Stacks 04NN, such a
neighbourhood is the set of points of an open subspace by Stacks 03BZ, and that subspace is
quasi-compact by Stacks 03E4 because its inclusion is an embedding on points. -/
private theorem exists_isQuasiCompactSpace_openSubspace_mem
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (x : points B S hS X) :
    ∃ V : Subfunctor X, IsOpenSubspace B S hS V ∧
      IsQuasiCompactSpace B S hS V.toFunctor ∧
      ∃ v : points B S hS V.toFunctor, pointsMap B S hS V.toFunctor V.ι v = x := by
  obtain ⟨W, hW⟩ := (hasBasis_nhds_isOpen_isCompact B S hS X hX x).mem_iff.mp
    (Filter.univ_mem : (Set.univ : Set (points B S hS X)) ∈ nhds x)
  obtain ⟨V, hV, hVrange⟩ :=
    exists_isOpenSubspace_range_pointsMap_eq B S hS hX W hW.1.1
  obtain ⟨v, hv⟩ : x ∈ Set.range (pointsMap B S hS V.toFunctor V.ι) := hVrange ▸ hW.1.2.2
  refine ⟨V, hV, ?_, v, hv⟩
  refine (isQuasiCompactSpace_iff_compactSpace_points B S hS _ hV.1).2 ⟨?_⟩
  have hEmb : Topology.IsEmbedding (pointsMap B S hS V.toFunctor V.ι) :=
    isEmbedding_pointsMap_of_isImmersion B S hS hX V.ι
      (isImmersion_of_isOpenImmersion B S hS hV.2)
  refine hEmb.isCompact_iff.mpr ?_
  rw [Set.image_univ, hVrange]
  exact hW.1.2.1

/-- The presheaf represented by the site object of a field-valued point is étale-locally
reduced, being the spectrum of a field. -/
private theorem hasEtaleLocalProperty_isReduced_yoneda_siteObject
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : FieldValuedPoint B S hS X) :
    HasEtaleLocalProperty B S hS (yoneda.obj (p.siteObject B S hS X))
      (fun W : Scheme.{u} => IsReduced W) := by
  refine hasEtaleLocalProperty_of_representable B S hS _
    (fun W : Scheme.{u} => IsReduced W) (p.siteObject B S hS X) (Iso.refl _) ?_
  change IsReduced (Spec (.of p.carrier))
  infer_instance

/-- **Stacks 0H1M in the site.** A morphism of the big fppf site over `S` out of an object with
reduced underlying scheme, whose underlying morphism of schemes has image a single point,
factors through the canonical field-valued representative above that point.

The factorization of underlying schemes is Stacks 0H1M; it is lifted to the site because the
inclusion of the site in schemes is fully faithful, the compatibility with the structure
morphisms being read off the one of the target. -/
private theorem exists_comp_siteHom_schemePointRepresentative
    {P A : BigFppfOver B S hS} (h : A ⟶ P)
    [IsReduced ((BigFppfOver.toScheme B S hS).obj A)]
    (y : (BigFppfOver.toScheme B S hS).obj P)
    (hrange : Set.range ((BigFppfOver.toScheme B S hS).map h).base ⊆ {y}) :
    ∃ a : A ⟶ (schemePointRepresentative B S hS P y).siteObject B S hS (yoneda.obj P),
      a ≫ (schemePointRepresentative B S hS P y).siteHom = h := by
  obtain ⟨g, hg⟩ := exists_comp_fromSpecResidueField_eq
    ((BigFppfOver.toScheme B S hS).map h) y hrange
  set Q := (schemePointRepresentative B S hS P y).siteObject B S hS (yoneda.obj P) with hQ
  set c := (schemePointRepresentative B S hS P y).siteHom with hc
  have hcScheme : B.inclusion.map (Over.Hom.left c) =
      ((BigFppfOver.toScheme B S hS).obj P).fromSpecResidueField y :=
    toScheme_map_siteHom_schemePointRepresentative B S hS P y
  have hpre : B.inclusion.map (B.inclusion.preimage (X := A.left) (Y := Q.left) g) = g :=
    B.inclusion.map_preimage _
  have hQhom : B.inclusion.map Q.hom =
      B.inclusion.map (Over.Hom.left c) ≫ B.inclusion.map P.hom := by
    rw [← B.inclusion.map_comp, Over.w c]
  refine ⟨Over.homMk (B.inclusion.preimage (X := A.left) (Y := Q.left) g) ?_, ?_⟩
  · refine B.inclusion.map_injective ?_
    calc B.inclusion.map (B.inclusion.preimage (X := A.left) (Y := Q.left) g ≫ Q.hom)
        = B.inclusion.map (B.inclusion.preimage (X := A.left) (Y := Q.left) g) ≫
            B.inclusion.map Q.hom := B.inclusion.map_comp _ _
      _ = g ≫ B.inclusion.map (Over.Hom.left c) ≫ B.inclusion.map P.hom := by
            rw [hpre, hQhom]
            rfl
      _ = (g ≫ B.inclusion.map (Over.Hom.left c)) ≫ B.inclusion.map P.hom :=
            (Category.assoc _ _ _).symm
      _ = B.inclusion.map (Over.Hom.left h) ≫ B.inclusion.map P.hom := by
            rw [hcScheme, hg]
            rfl
      _ = B.inclusion.map (Over.Hom.left h ≫ P.hom) := (B.inclusion.map_comp _ _).symm
      _ = B.inclusion.map A.hom := congrArg B.inclusion.map (Over.w h)
  · refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp]
    change B.inclusion.map (B.inclusion.preimage (X := A.left) (Y := Q.left) g) ≫
      B.inclusion.map (Over.Hom.left c) = (BigFppfOver.toScheme B S hS).map h
    rw [hpre, hcScheme]
    exact hg

/-- The case of Stacks 0H1T in which the morphism and the field-valued representative have
already been factored through a common representable presheaf monomorphic over `X`.

On a surjective étale scheme chart of `Y` the factorization is
`AlgebraicGeometry.Space.exists_comp_siteHom_schemePointRepresentative`, through the canonical
representative above the image point; Stacks 0H2X compares that representative with the given
one, and the factorization of the chart descends to `Y` because the chart is locally surjective
for the fppf topology and the range of a monomorphism of sheaves is a subsheaf. -/
private theorem exists_comp_fieldMorphism_eq_of_yoneda_factorization
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (hred : HasEtaleLocalProperty B S hS Y (fun W : Scheme.{u} => IsReduced W))
    (f : Y ⟶ X) (x : points B S hS X) (hf : Set.range (pointsMap B S hS Y f) ⊆ {x})
    (p : FieldValuedPoint B S hS X) (hpx : p.class B S hS X = x)
    (hmono : Mono (fieldMorphism B S hS X p))
    (P : BigFppfOver B S hS) (mX : yoneda.obj P ⟶ X) (hmX : Mono mX)
    (gP : Y ⟶ yoneda.obj P) (hgP : gP ≫ mX = f)
    (pP : yoneda.obj (p.siteObject B S hS X) ⟶ yoneda.obj P)
    (hpP : pP ≫ mX = fieldMorphism B S hS X p) :
    ∃ g : Y ⟶ yoneda.obj (p.siteObject B S hS X),
      g ≫ fieldMorphism B S hS X p = f := by
  have : Subsingleton (points B S hS (yoneda.obj (p.siteObject B S hS X))) :=
    subsingleton_points_yoneda_siteObject B S hS p
  have hKalg : IsAlgebraicSpace B S hS (yoneda.obj (p.siteObject B S hS X)) :=
    isAlgebraicSpace_yoneda B S hS _
  -- The field-valued point of `h_P` determined by the representative.
  obtain ⟨qP, hqPclass⟩ :
      ∃ q : FieldValuedPoint B S hS (yoneda.obj P),
        q.class B S hS (yoneda.obj P) =
          pointsMap B S hS (yoneda.obj (p.siteObject B S hS X)) pP
            ((p.tautologicalPoint B S hS X).class B S hS
              (yoneda.obj (p.siteObject B S hS X))) :=
    ⟨FieldValuedPoint.map B S hS (yoneda.obj (p.siteObject B S hS X)) pP
      (p.tautologicalPoint B S hS X),
      (pointsMap_class B S hS _ pP (p.tautologicalPoint B S hS X)).symm⟩
  have hqPX : pointsMap B S hS (yoneda.obj P) mX (qP.class B S hS (yoneda.obj P)) = x := by
    rw [hqPclass, ← pointsMap_comp_point, hpP, pointsMap_fieldMorphism_tautologicalPoint, hpx]
  have hgPpoint : ∀ z : points B S hS Y,
      pointsMap B S hS Y gP z = qP.class B S hS (yoneda.obj P) := by
    intro z
    refine pointsMap_injective_of_mono B S hS mX ?_
    rw [← pointsMap_comp_point, hgP, hqPX]
    exact Set.mem_singleton_iff.mp (hf ⟨z, rfl⟩)
  -- A surjective étale chart of `Y`, and the morphism of schemes it gives to `P`.
  obtain ⟨A, aY, haSurj, haEtale⟩ := hY.exists_atlas
  obtain ⟨fObj, hfObj⟩ := yoneda.map_surjective (aY ≫ gP)
  have : IsReduced ((BigFppfOver.toScheme B S hS).obj A) :=
    (exists_atlas_iff_forall_etale B S hS Y (fun W : Scheme.{u} => IsReduced W) hY).mp hred
      A aY haEtale
  set xP := pointsToScheme B S hS P (qP.class B S hS (yoneda.obj P)) with hxP
  have hrange : Set.range ((BigFppfOver.toScheme B S hS).map fObj).base ⊆ {xP} := by
    rintro z ⟨w, rfl⟩
    obtain ⟨w', rfl⟩ := surjective_pointsToScheme B S hS A w
    have hz := pointsToScheme_pointsMap B S hS fObj w'
    rw [hfObj, pointsMap_comp_point, hgPpoint] at hz
    exact hz.symm
  obtain ⟨a, ha⟩ := exists_comp_siteHom_schemePointRepresentative B S hS fObj xP hrange
  -- The canonical representative above that scheme point, pushed forward to `X`.
  have hqCanClass : (schemePointRepresentative B S hS P xP).class B S hS (yoneda.obj P) =
      qP.class B S hS (yoneda.obj P) := by
    rw [hxP]
    exact class_schemePointRepresentative_pointsToScheme B S hS P _
  have hqCanMono : Mono (fieldMorphism B S hS (yoneda.obj P)
      (schemePointRepresentative B S hS P xP)) :=
    mono_fieldMorphism_schemePointRepresentative B S hS P xP
  have hqXmap : fieldMorphism B S hS X (FieldValuedPoint.map B S hS (yoneda.obj P) mX
        (schemePointRepresentative B S hS P xP)) =
      fieldMorphism B S hS (yoneda.obj P) (schemePointRepresentative B S hS P xP) ≫ mX :=
    fieldMorphism_map B S hS (yoneda.obj P) mX _
  have : Mono (fieldMorphism B S hS X (FieldValuedPoint.map B S hS (yoneda.obj P) mX
      (schemePointRepresentative B S hS P xP))) := by
    rw [hqXmap]
    exact ⟨fun g h hgh => hqCanMono.right_cancellation g h
      (hmX.right_cancellation _ _ ((Category.assoc _ _ _).trans
        (hgh.trans (Category.assoc _ _ _).symm)))⟩
  have hqXclass : p.class B S hS X = (FieldValuedPoint.map B S hS (yoneda.obj P) mX
      (schemePointRepresentative B S hS P xP)).class B S hS X := by
    rw [← pointsMap_class, hqCanClass, hqPX, hpx]
  -- Compare it with `p` by Stacks 0H2X.
  obtain ⟨φ, hφ, -⟩ := FieldValuedPoint.existsUnique_factor_of_class_eq_of_mono
    B S hS X hX p (FieldValuedPoint.map B S hS (yoneda.obj P) mX
      (schemePointRepresentative B S hS P xP)) hqXclass
  have hφcomp : yoneda.map φ ≫ fieldMorphism B S hS X p =
      fieldMorphism B S hS X (FieldValuedPoint.map B S hS (yoneda.obj P) mX
        (schemePointRepresentative B S hS P xP)) := by
    refine yonedaEquiv.injective ?_
    rw [← yonedaEquiv_naturality, yonedaEquiv_fieldMorphism, yonedaEquiv_fieldMorphism]
    exact hφ
  have hcan : yoneda.map a ≫ fieldMorphism B S hS (yoneda.obj P)
      (schemePointRepresentative B S hS P xP) = yoneda.map fObj := by
    rw [fieldMorphism_yoneda, ← Functor.map_comp, ha]
  have hchart : yoneda.map (a ≫ φ) ≫ fieldMorphism B S hS X p = aY ≫ f :=
    calc yoneda.map (a ≫ φ) ≫ fieldMorphism B S hS X p
        = (yoneda.map a ≫ yoneda.map φ) ≫ fieldMorphism B S hS X p :=
          congrArg (· ≫ fieldMorphism B S hS X p) (yoneda.map_comp a φ)
      _ = yoneda.map a ≫ (yoneda.map φ ≫ fieldMorphism B S hS X p) := Category.assoc _ _ _
      _ = yoneda.map a ≫ fieldMorphism B S hS X (FieldValuedPoint.map B S hS (yoneda.obj P)
            mX (schemePointRepresentative B S hS P xP)) :=
          congrArg (yoneda.map a ≫ ·) hφcomp
      _ = yoneda.map a ≫ (fieldMorphism B S hS (yoneda.obj P)
            (schemePointRepresentative B S hS P xP) ≫ mX) :=
          congrArg (yoneda.map a ≫ ·) hqXmap
      _ = (yoneda.map a ≫ fieldMorphism B S hS (yoneda.obj P)
            (schemePointRepresentative B S hS P xP)) ≫ mX := (Category.assoc _ _ _).symm
      _ = yoneda.map fObj ≫ mX := congrArg (· ≫ mX) hcan
      _ = (aY ≫ gP) ≫ mX := congrArg (· ≫ mX) hfObj
      _ = aY ≫ (gP ≫ mX) := Category.assoc _ _ _
      _ = aY ≫ f := congrArg (aY ≫ ·) hgP
  -- Descend the factorization of the chart along the chart.
  have : Mono (fieldMorphism B S hS X p) := hmono
  obtain ⟨gR, hgR⟩ := factorThroughSubfunctor_of_locallySurjective
    (Subfunctor.range (fieldMorphism B S hS X p)) f aY
    (isLocallySurjective_of_surjective_etale B S hS aY haSurj haEtale)
    ((isSheaf_iff_isSheaf_of_type _ _).1 hX.isSheaf)
    (Presieve.isSheaf_iso _ (asIso (Subfunctor.toRange (fieldMorphism B S hS X p)))
      ((isSheaf_iff_isSheaf_of_type _ _).1 hKalg.isSheaf))
    (yoneda.map (a ≫ φ) ≫ Subfunctor.toRange (fieldMorphism B S hS X p))
    (by rw [Category.assoc, Subfunctor.toRange_ι, hchart])
  exact ⟨gR ≫ inv (Subfunctor.toRange (fieldMorphism B S hS X p)), by
    rw [Category.assoc, (IsIso.inv_comp_eq _).2 (Subfunctor.toRange_ι _).symm, hgR]⟩

/-! ### The residual space at a point with a monomorphic field-valued representative -/

/-- The morphism presented by a monomorphic field-valued representative of a point `x` of an
algebraic space `X` over `S` exhibits the spectrum of its field as a residual space of `X`
at `x` in the sense of Stacks 06R0.

The spectrum of a field is reduced and locally Noetherian and has exactly one point, and that
point goes to `x` because the representative represents `x`. -/
@[stacks 0H1T "the residual space at the point is the spectrum of the field of hypothesis (3)"]
theorem isResidualSpaceAt_fieldMorphism_of_mono
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (x : points B S hS X)
    (p : FieldValuedPoint B S hS X) (hpx : p.class B S hS X = x)
    (hmono : Mono (fieldMorphism B S hS X p)) :
    IsResidualSpaceAt B S hS X x (fieldMorphism B S hS X p) := by
  have hsub : Subsingleton (points B S hS (yoneda.obj (p.siteObject B S hS X))) :=
    subsingleton_points_yoneda_siteObject B S hS p
  refine ⟨isAlgebraicSpace_yoneda B S hS _, hmono, ?_, ?_,
    ⟨(p.tautologicalPoint B S hS X).class B S hS (yoneda.obj (p.siteObject B S hS X))⟩,
    hsub, fun z => ?_⟩
  · exact hasEtaleLocalProperty_isReduced_yoneda_siteObject B S hS p
  · refine hasEtaleLocalProperty_of_representable B S hS _
      (fun W : Scheme.{u} => IsLocallyNoetherian W) (p.siteObject B S hS X) (Iso.refl _) ?_
    change IsLocallyNoetherian (Spec (.of p.carrier))
    infer_instance
  · rw [Subsingleton.elim z ((p.tautologicalPoint B S hS X).class B S hS
      (yoneda.obj (p.siteObject B S hS X))), pointsMap_fieldMorphism_tautologicalPoint]
    exact hpx

/-! ### The factorization -/

/-- **Stacks 0H1T.** Let `f : Y ⟶ X` be a morphism of algebraic spaces over `S` and let `x` be
a point of `|X|`. Assume that the image of `|Y|` in `|X|` is contained in `{x}`, that `Y` is
reduced, and that `x` is represented by a quasi-compact monomorphism from the spectrum of a
field. Then `f` factors through that monomorphism, which by
`AlgebraicGeometry.Space.isResidualSpaceAt_fieldMorphism_of_mono` is a residual space of `X`
at `x`.

Replace `X` by a quasi-compact open subspace containing `x` and apply Stacks 0BBN: the point
lies in a stratum, a reduced closed subspace of an open subspace which is a scheme. Both `f`
and the representative factor through that open subspace by Stacks 03IE and through the
stratum by Stacks 03JJ, which is where reducedness of `Y` enters. That leaves the case of a
morphism into a representable presheaf monomorphic over `X`, which Stacks 0H1M and Stacks 0H2X
settle on a surjective étale scheme chart of `Y`. -/
@[stacks 0H1T]
theorem exists_comp_fieldMorphism_eq_of_range_pointsMap_subset_singleton
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : Y ⟶ X) (x : points B S hS X)
    (hf : Set.range (pointsMap B S hS Y f) ⊆ {x})
    (hred : HasEtaleLocalProperty B S hS Y (fun W : Scheme.{u} => IsReduced W))
    (p : FieldValuedPoint B S hS X) (hpx : p.class B S hS X = x)
    (hmono : Mono (fieldMorphism B S hS X p))
    (hqc : IsQuasiCompact B S hS (fieldMorphism B S hS X p)) :
    ∃ g : Y ⟶ yoneda.obj (p.siteObject B S hS X),
      g ≫ fieldMorphism B S hS X p = f := by
  classical
  have : Mono (fieldMorphism B S hS X p) := hmono
  have : Subsingleton (points B S hS (yoneda.obj (p.siteObject B S hS X))) :=
    subsingleton_points_yoneda_siteObject B S hS p
  have hKalg : IsAlgebraicSpace B S hS (yoneda.obj (p.siteObject B S hS X)) :=
    isAlgebraicSpace_yoneda B S hS _
  have hKred := hasEtaleLocalProperty_isReduced_yoneda_siteObject B S hS p
  have htaut : fieldMorphism B S hS (yoneda.obj (p.siteObject B S hS X))
      (p.tautologicalPoint B S hS X) = 𝟙 (yoneda.obj (p.siteObject B S hS X)) := by
    rw [fieldMorphism_yoneda]
    exact yoneda.map_id _
  set t := (p.tautologicalPoint B S hS X).class B S hS
    (yoneda.obj (p.siteObject B S hS X)) with htdef
  have hmPoint : ∀ q : points B S hS (yoneda.obj (p.siteObject B S hS X)),
      pointsMap B S hS (yoneda.obj (p.siteObject B S hS X))
        (fieldMorphism B S hS X p) q = x := by
    intro q
    rw [Subsingleton.elim q t, htdef, pointsMap_fieldMorphism_tautologicalPoint]
    exact hpx
  -- Step 1: a quasi-compact open subspace `V` containing `x`.
  obtain ⟨V, hV, hVqc, v, hv⟩ := exists_isQuasiCompactSpace_openSubspace_mem B S hS hX x
  have : Mono V.ι := inferInstance
  -- Step 2: the representative and `f` factor through `V`.
  obtain ⟨iV, hiV⟩ := (factorsThrough_openSubspace_iff_points B S hS hX hKalg V hV
    (fieldMorphism B S hS X p)).2 (by
      rintro z ⟨q, rfl⟩
      exact ⟨v, hv.trans (hmPoint q).symm⟩)
  obtain ⟨fV, hfV⟩ := (factorsThrough_openSubspace_iff_points B S hS hX hY V hV f).2 (by
    rintro z ⟨z, rfl⟩
    exact ⟨v, hv.trans (Set.mem_singleton_iff.mp (hf ⟨z, rfl⟩)).symm⟩)
  have hiVqc : IsQuasiCompact B S hS iV :=
    IsQuasiCompact.of_comp_mono B S hS iV V.ι (by rw [hiV]; exact hqc)
  obtain ⟨pV, hpVqc, hpVclass⟩ :
      ∃ q : FieldValuedPoint B S hS V.toFunctor,
        IsQuasiCompact B S hS (fieldMorphism B S hS V.toFunctor q) ∧
        q.class B S hS V.toFunctor =
          pointsMap B S hS (yoneda.obj (p.siteObject B S hS X)) iV t := by
    have hmapiV : fieldMorphism B S hS V.toFunctor
        (FieldValuedPoint.map B S hS (yoneda.obj (p.siteObject B S hS X)) iV
          (p.tautologicalPoint B S hS X)) = iV :=
      (fieldMorphism_map B S hS _ iV (p.tautologicalPoint B S hS X)).trans
        ((congrArg (· ≫ iV) htaut).trans (Category.id_comp iV))
    refine ⟨FieldValuedPoint.map B S hS (yoneda.obj (p.siteObject B S hS X)) iV
      (p.tautologicalPoint B S hS X), ?_, ?_⟩
    · rw [hmapiV]
      exact hiVqc
    · rw [htdef, pointsMap_class]
  have hpVX : pointsMap B S hS V.toFunctor V.ι (pV.class B S hS V.toFunctor) = x := by
    rw [hpVclass, ← pointsMap_comp_point, hiV]
    exact hmPoint t
  have hfVPoint : ∀ z : points B S hS Y,
      pointsMap B S hS Y fV z = pV.class B S hS V.toFunctor := by
    intro z
    refine pointsMap_injective_of_mono B S hS V.ι ?_
    rw [← pointsMap_comp_point, hfV, hpVX]
    exact Set.mem_singleton_iff.mp (hf ⟨z, rfl⟩)
  -- Step 3: a scheme stratification of `V`, and the stratum containing the point.
  obtain ⟨strat, hstrat⟩ :=
    exists_schemeStratification_quasiCompactPoint_mem_stratum B S hS V.toFunctor hV.1 hVqc
  obtain ⟨n, zT, hzT⟩ := hstrat (pV.class B S hS V.toFunctor) pV rfl hpVqc
  have : Mono (strat.openPart n).ι := inferInstance
  have : Mono (strat.stratum n).ι := inferInstance
  have hzUw : pointsMap B S hS (strat.openPart n).toFunctor (strat.openPart n).ι
      (pointsMap B S hS (strat.stratum n).toFunctor (strat.stratum n).ι zT) =
      pV.class B S hS V.toFunctor := by
    rw [← pointsMap_comp_point]
    exact hzT
  -- Step 4: `f` factors through the open part, then through the stratum.
  obtain ⟨fU, hfU⟩ := (factorsThrough_openSubspace_iff_points B S hS hV.1 hY
    (strat.openPart n) (strat.isOpenSubspace_openPart n) fV).2 (by
      rintro z ⟨z, rfl⟩
      exact ⟨_, hzUw.trans (hfVPoint z).symm⟩)
  have hfUPoint : ∀ z : points B S hS Y, pointsMap B S hS Y fU z =
      pointsMap B S hS (strat.stratum n).toFunctor (strat.stratum n).ι zT := by
    intro z
    refine pointsMap_injective_of_mono B S hS (strat.openPart n).ι ?_
    rw [← pointsMap_comp_point, hfU, hzUw]
    exact hfVPoint z
  obtain ⟨gT, hgT⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS
    (strat.isOpenSubspace_openPart n).1 hY (strat.stratum n)
    (strat.isClosedSubspace_stratum n) hred fU).2 (by
      rintro z ⟨z, rfl⟩
      exact ⟨zT, (hfUPoint z).symm⟩)
  -- Step 5: the representative factors through the open part, then through the stratum.
  obtain ⟨iU, hiU⟩ := (factorsThrough_openSubspace_iff_points B S hS hV.1 hKalg
    (strat.openPart n) (strat.isOpenSubspace_openPart n) iV).2 (by
      rintro z ⟨q, rfl⟩
      refine ⟨_, hzUw.trans ?_⟩
      rw [hpVclass, Subsingleton.elim q t])
  have hiUPoint : ∀ q : points B S hS (yoneda.obj (p.siteObject B S hS X)),
      pointsMap B S hS (yoneda.obj (p.siteObject B S hS X)) iU q =
      pointsMap B S hS (strat.stratum n).toFunctor (strat.stratum n).ι zT := by
    intro q
    refine pointsMap_injective_of_mono B S hS (strat.openPart n).ι ?_
    rw [← pointsMap_comp_point, hiU, hzUw, hpVclass, Subsingleton.elim q t]
  obtain ⟨pT, hpT⟩ := (exists_lift_closedSubspace_iff_pointsMap_range_subset B S hS
    (strat.isOpenSubspace_openPart n).1 hKalg (strat.stratum n)
    (strat.isClosedSubspace_stratum n) hKred iU).2 (by
      rintro z ⟨q, rfl⟩
      exact ⟨zT, (hiUPoint q).symm⟩)
  -- Step 6: the stratum is a scheme, and both factorizations land in it.
  have : (strat.stratum n).toFunctor.IsRepresentable := strat.isRepresentable_stratum n
  refine exists_comp_fieldMorphism_eq_of_yoneda_factorization B S hS hX hY hred f x hf p hpx
    hmono (strat.stratum n).toFunctor.reprX ((strat.stratum n).toFunctor.reprW.hom ≫
      (strat.stratum n).ι ≫ (strat.openPart n).ι ≫ V.ι) (by
        have h1 : Mono (strat.stratum n).ι := inferInstance
        have h2 : Mono (strat.openPart n).ι := inferInstance
        have h3 : Mono V.ι := inferInstance
        have h0 : Mono (strat.stratum n).toFunctor.reprW.hom := IsIso.mono_of_iso _
        exact mono_comp' h0 (mono_comp' h1 (mono_comp' h2 h3)))
    (gT ≫ (strat.stratum n).toFunctor.reprW.inv) ?_
    (pT ≫ (strat.stratum n).toFunctor.reprW.inv) ?_
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hgT, ← Category.assoc, hfU, hfV]
  · simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc, hpT, ← Category.assoc, hiU, hiV]

/-- **Stacks 0H1T** with hypothesis (3) supplied by its parenthetical: for a decent algebraic
space `X` over `S`, a morphism `f : Y ⟶ X` from a reduced algebraic space whose image on
points is contained in `{x}` factors through a residual space of `X` at `x`, and that residual
space is the spectrum of a field.

Decency of Stacks 03I8 is condition (4) of Stacks 03JV at every point, which is hypothesis (3)
at `x`. -/
@[stacks 0H1T "hypothesis (3) supplied by decency of the target"]
theorem exists_isResidualSpaceAt_comp_fieldMorphism_eq_of_isDecentSpace
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : Y ⟶ X) (x : points B S hS X)
    (hf : Set.range (pointsMap B S hS Y f) ⊆ {x})
    (hred : HasEtaleLocalProperty B S hS Y (fun W : Scheme.{u} => IsReduced W))
    (hdecent : IsDecentSpace B S hS X) :
    ∃ p : FieldValuedPoint B S hS X,
      IsResidualSpaceAt B S hS X x (fieldMorphism B S hS X p) ∧
      ∃ g : Y ⟶ yoneda.obj (p.siteObject B S hS X),
        g ≫ fieldMorphism B S hS X p = f := by
  obtain ⟨p, hpx, hmono, hqc⟩ := hdecent x
  exact ⟨p, isResidualSpaceAt_fieldMorphism_of_mono B S hS x p hpx hmono,
    exists_comp_fieldMorphism_eq_of_range_pointsMap_subset_singleton B S hS hX hY f x hf hred
      p hpx hmono hqc⟩

end AlgebraicGeometry.Space

end
