module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.SmoothLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.InducedProperty
public import StacksFrontier.AlgebraicGeometry.Descent.Germ.Local
public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.LocalFiniteness
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.SpecField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.FieldValued
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.SpecResidueFieldClosedPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PointsOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtInfinitesimalLifting
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalLocallyOfFiniteType
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedCategory.RelocalizeAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.DiagonalFibre
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SliceOverMap
public import StacksFrontier.CategoryTheory.Sites.Stack.SlicePointIsomPresheaf
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverProdDiagonalEquiv
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverSliceProduct
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Predeformation.FibreProduct
public import StacksFrontier.Deformation.Artin.RimSchlessinger
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.FiniteResidueFieldExtension
public import StacksFrontier.Deformation.Artin.Versality.SmoothPredeformation
public import StacksFrontier.Deformation.ArtinCriteria.Versality
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.Deformation.Smooth.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Residue fields and field-valued points for a versal base change

Preparations for the smoothness of a base change of a versal object
(`Deformation.Artin.BaseChange.isSmoothAt_baseChange_of_isVersalAt`):
residue fields of finite type points and of Artinian local spectra, pointed étale charts and
their field-valued points, and the functors induced on deformation objects by a functor over
the base.

## Implementation notes

No option overrides are used.  The definitions this development must see through are named instead:
the slice functor `CategoryTheory.Over.post`, the fibre of a functor with its inclusion, the
pullback and slice functors of a choice of pullbacks, the 2-Yoneda lift, the projections of a
2-fibre product, the category over `𝒞` attached to a functor and to a presheaf of categories,
the induced bicategory underlying `CategoryTheory.CatFiberedInGroupoids`, and the field-valued
points of a presheaf all carry `attribute [local implicit_reducible]` at the top of the file,
and the private definitions of this file carry `@[implicit_reducible]` individually.  That is
what makes the goals here type-correct at `implicit` transparency, so `rw`, `simp` and instance
search see through exactly the definitions named and nothing else.

## References

* [Stacks Project, Tag 0CXM](https://stacks.math.columbia.edu/tag/0CXM)
-/
@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin.BaseChange

universe u v w u₁ v₁ u₂ v₂ u₃ v₃

-- The slice functor `Over.post`, fibres of a functor, their inclusion and formation, the
-- pullback functors of a choice of pullbacks and the slice functor of a 2-Yoneda lift are plain
-- `def`s, so goals mentioning an object of a fibre, or an object of the site read in `Over S`,
-- are not type-correct at `implicit` transparency.  Naming them here is what lets `rw`,
-- `simp only` and instance search see through exactly these and nothing else.
attribute [local implicit_reducible] CategoryTheory.Over.post
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.mk
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor
  CategoryTheory.Functor.TwoYoneda.liftBased
  CategoryTheory.Functor.TwoYoneda.liftFunctor
  CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.id
  CategoryTheory.TwoFibreProductOver.fst
  CategoryTheory.TwoFibreProductOver.snd
  CategoryTheory.TwoFibreProductOver.structureFunctor
  CategoryTheory.Functor.toPseudofunctor'
  CategoryTheory.pseudofunctorOfIsLocallyDiscrete
  Quiver.Hom.toLoc
  CategoryTheory.Pseudofunctor.CoGrothendieck.forget
  AlgebraicGeometry.Space.FieldValuedPoint.map
  AlgebraicGeometry.Space.schemePoint
  CategoryTheory.Bicategory.InducedBicategory

variable (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w}
    (AlgebraicGeometry.BigFppfOver B S hS))

/-- The two choices of Cartesian pullback used for the two-Yoneda map are
canonically isomorphic over the base. -/
@[implicit_reducible] private def twoYonedaLiftIsoSliceFunctor
    {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
    (p : X ⥤ C) (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
    (U : C) (x : p.Fiber U) :
    (Functor.TwoYoneda.liftBased p hp U x).toFunctor ≅ c.sliceFunctor x := by
  let i (a : Over U) := Functor.IsCartesian.domainUniqueUpToIso p a.hom
    (c.map a.hom x) (Functor.TwoYoneda.chosenLift p hp U x a).φ
  refine NatIso.ofComponents i ?_
  intro a b f
  have hmap : p.IsHomLift f.left
      ((Functor.TwoYoneda.liftBased p hp U x).map f) := by
    change p.IsHomLift f.left (Functor.IsStronglyCartesian.map p b.hom
      (Functor.TwoYoneda.chosenLift p hp U x b).φ (Over.w f).symm
      (Functor.TwoYoneda.chosenLift p hp U x a).φ)
    infer_instance
  let := hmap
  apply Functor.IsStronglyCartesian.ext p b.hom (c.map b.hom x) f.left
  simp only [i, Category.assoc, Functor.IsCartesian.domainUniqueUpToIso_hom,
    Functor.IsCartesian.fac, Functor.ChoiceOfPullbacks.sliceFunctor_map_fac]
  exact Functor.IsStronglyCartesian.fac p b.hom
    (Functor.TwoYoneda.chosenLift p hp U x b).φ (Over.w f).symm
    (Functor.TwoYoneda.chosenLift p hp U x a).φ

private lemma twoYonedaLiftIsoSliceFunctor_vertical
    {C : Type u₁} [Category.{v₁} C] {X : Type u₂} [Category.{v₂} X]
    (p : X ⥤ C) (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
    (U : C) (x : p.Fiber U) (a : Over U) :
    p.IsHomLift (𝟙 a.left) ((twoYonedaLiftIsoSliceFunctor p hp c U x).hom.app a) := by
  show p.IsHomLift (𝟙 a.left) (Functor.IsCartesian.map p a.hom
    (c.map a.hom x) (Functor.TwoYoneda.chosenLift p hp U x a).φ)
  infer_instance

private theorem schemeCutoff_isClosedUnderIsomorphisms
    (B : AlgebraicGeometry.BigFppfSite.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun X : Scheme.{u} ↦ X.size < B.cutoff) where
  of_iso {X Y} e h := by
    change X.size < B.cutoff at h
    rwa [← Scheme.size_congr e]

private theorem schemeCutoff_isClosedUnderLimitsOfShape_walkingCospan
    (B : AlgebraicGeometry.BigFppfSite.{u}) :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (fun X : Scheme.{u} ↦ X.size < B.cutoff) WalkingCospan :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan F))]
    exact Scheme.size_pullback_lt _ _ (hF .left) (hF .right))

attribute [local instance] schemeCutoff_isClosedUnderIsomorphisms

attribute [local instance] AlgebraicGeometry.Space.schemeCutoff_hasPullbacks
  AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

private theorem overHasBinaryProducts (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : HasBinaryProducts (AlgebraicGeometry.BigFppfOver B S hS) :=
  hasBinaryProducts_of_hasTerminal_and_pullbacks _

/-- A locally finite type field-valued point has finite residue field extension.
This is the field-extension bridge needed to apply the versality theorem after
passing to the residue field of a point of the representing space. -/
private theorem finiteResidueFieldExtension
    {T : Scheme.{u}} {K : Type u} [Field K]
    (f : Spec (.of K) ⟶ T) (hf : LocallyOfFiniteType f) :
    let q := Scheme.SpecToEquivOfField K T f
    letI : Algebra (T.residueField q.1) K := q.2.hom.toAlgebra
    Module.Finite (T.residueField q.1) K := by
  let q := Scheme.SpecToEquivOfField K T f
  let : Algebra (T.residueField q.1) K := q.2.hom.toAlgebra
  obtain ⟨_, _, _, _, _, hfinite⟩ := ((AlgebraicGeometry.finiteType_specField_tfae f).out 2 4).mp hf
  exact hfinite

/-- Factor a field-valued point through the residue field of its image. -/
private theorem fieldPoint_factorThroughResidueField
    {T : Scheme.{u}} {K : Type u} [Field K]
    (f : Spec (.of K) ⟶ T) :
    let q := Scheme.SpecToEquivOfField K T f
    letI : Algebra (T.residueField q.1) K := q.2.hom.toAlgebra
    f = Spec.map (CommRingCat.ofHom (algebraMap (T.residueField q.1) K)) ≫
      T.fromSpecResidueField q.1 := by
  let q := Scheme.SpecToEquivOfField K T f
  let : Algebra (T.residueField q.1) K := q.2.hom.toAlgebra
  exact (Scheme.SpecToEquivOfField K T).symm_apply_apply f |>.symm

/-- Package the finite residue extension and the factorization at a specified
image point. -/
private theorem fieldPoint_residueData
    {T : Scheme.{u}} {K : Type u} [Field K]
    (f : Spec (.of K) ⟶ T) (t : T)
    (ht : f (IsLocalRing.closedPoint K) = t)
    (hf : LocallyOfFiniteType f) :
    let q := Scheme.SpecToEquivOfField K T f
    q.1 = t ∧
      (letI : Algebra (T.residueField q.1) K := q.2.hom.toAlgebra
       Module.Finite (T.residueField q.1) K) ∧
      (letI : Algebra (T.residueField q.1) K := q.2.hom.toAlgebra
       f = Spec.map (CommRingCat.ofHom (algebraMap (T.residueField q.1) K)) ≫
         T.fromSpecResidueField q.1) :=
  ⟨ht, finiteResidueFieldExtension f hf, fieldPoint_factorThroughResidueField f⟩

private theorem finiteTypePoint_of_fieldPoint_locallyFiniteType
    {T : Scheme.{u}} {K : Type u} [Field K]
    (f : Spec (.of K) ⟶ T) (hf : LocallyOfFiniteType f) :
    AlgebraicGeometry.IsFiniteTypePoint
      (f (IsLocalRing.closedPoint K)) := by
  let q := Scheme.SpecToEquivOfField K T f
  let : Algebra (T.residueField q.1) K := q.2.hom.toAlgebra
  obtain ⟨hpoint, ⟨hfinite, hfactor⟩⟩ :=
    fieldPoint_residueData f (f (IsLocalRing.closedPoint K)) rfl hf
  have hq : LocallyOfFiniteType (T.fromSpecResidueField q.1) := by
    let φ := Spec.map (CommRingCat.ofHom (algebraMap (T.residueField q.1) K))
    let : Surjective φ := ⟨fun _ => ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
    let : Flat φ := by infer_instance
    let : Module.Finite (T.residueField q.1) K := hfinite
    let : LocallyOfFinitePresentation φ := by
      rw [LocallyOfFinitePresentation.SpecMap_iff]
      let : Algebra.FiniteType (T.residueField q.1) K :=
        Module.Finite.finiteType K
      exact (RingHom.finitePresentation_algebraMap).2
        (Algebra.FinitePresentation.of_finiteType.mp inferInstance)
    let : LocallyOfFiniteType (φ ≫ T.fromSpecResidueField q.1) := by rwa [← hfactor]
    exact AlgebraicGeometry.locallyOfFiniteType_of_comp_of_fppf φ
      (T.fromSpecResidueField q.1)
  rw [← hpoint]
  exact ((AlgebraicGeometry.finiteType_specField_tfae
    (T.fromSpecResidueField q.1)).out 2 1).mp hq

/-- A locally finite type field-valued point is induced by a finite extension
of the residue field of its specified image. -/
private lemma exists_finite_residueFieldAlgebra
    {T : Scheme.{u}} {K : Type u} [Field K]
    (f : Spec (.of K) ⟶ T) (t : T)
    (ht : f (IsLocalRing.closedPoint K) = t)
    (hf : LocallyOfFiniteType f) :
    ∃ a : Algebra (T.residueField t) K,
      letI := a
      Module.Finite (T.residueField t) K ∧
      f = Spec.map (CommRingCat.ofHom (algebraMap (T.residueField t) K)) ≫
        T.fromSpecResidueField t := by
  subst t
  let q := Scheme.SpecToEquivOfField K T f
  let a : Algebra (T.residueField q.1) K := q.2.hom.toAlgebra
  exact ⟨a, finiteResidueFieldExtension f hf, fieldPoint_factorThroughResidueField f⟩

/-- A morphism from an affine scheme whose image lies in an affine open factors
through that open, which exhibits an algebra structure realizing the
factorization. -/
private lemma exists_algebra_factorization
    {T : Scheme.{u}} {R A : CommRingCat.{u}} (i : Spec R ⟶ T) (hi : IsOpenImmersion i)
    (g : Spec A ⟶ T) (hg : Set.range g ⊆ Set.range i) :
    ∃ a : Algebra R A, letI := a
      Spec.map (CommRingCat.ofHom (algebraMap R A)) ≫ i = g := by
  let := hi
  let t := IsOpenImmersion.lift i g hg
  refine ⟨(Spec.preimage t).hom.toAlgebra, ?_⟩
  show Spec.map (Spec.preimage t) ≫ i = g
  rw [Spec.map_preimage]
  exact IsOpenImmersion.lift_fac i g hg

/-- A field-valued point factors through an affine open neighborhood. -/
private lemma exists_affineOpen_fieldPointFactorization
    {S : Scheme.{u}} {K : Type u} [Field K] (f : Spec (.of K) ⟶ S) :
    ∃ (R : CommRingCat.{u}) (i : Spec R ⟶ S) (a : Algebra R K),
      letI := a
      IsOpenImmersion i ∧ Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ i = f := by
  obtain ⟨R, i, hi, r, hr⟩ := Scheme.exists_Spec_apply_eq
    (f (IsLocalRing.closedPoint K))
  have hrange : Set.range f ⊆ Set.range i := by
    rintro _ ⟨s, rfl⟩
    exact ⟨r, hr.trans (congrArg f (Subsingleton.elim _ _))⟩
  obtain ⟨a, ha⟩ := exists_algebra_factorization i hi f hrange
  exact ⟨R, i, a, hi, ha⟩

private lemma finiteTypePoint_of_isClosed {T : Scheme.{u}} {t : T}
    (ht : IsClosed ({t} : Set T)) :
    AlgebraicGeometry.IsFiniteTypePoint t := by
  let : IsClosedImmersion (T.fromSpecResidueField t) :=
    isClosed_singleton_iff_isClosedImmersion.mp ht
  exact ⟨inferInstance, inferInstance⟩

/-- The residue field of a finite type point belongs to the same bounded site. -/
lemma contains_specResidueField
    (B : AlgebraicGeometry.BigFppfSite.{u}) (T : Scheme.{u}) (hT : B.Contains T)
    (t : T) (ht : AlgebraicGeometry.IsFiniteTypePoint t) :
    B.Contains (Spec (T.residueField t)) := by
  let := ht.1
  let := ht.2
  exact Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    (T.fromSpecResidueField t) hT

/-- The canonical residue-field representative of a scheme point in the site. -/
@[implicit_reducible] private def residueFieldRepresentative
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (t : U.left.1)
    (ht : B.Contains (Spec (U.left.1.residueField t))) :
    AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U) where
  carrier := U.left.1.residueField t
  contained := ht
  toBase := U.left.1.fromSpecResidueField t ≫ B.inclusion.map U.hom
  value := Over.homMk ⟨U.left.1.fromSpecResidueField t⟩

private lemma residueFieldRepresentative_schemePoint
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS) (t : U.left.1)
    (ht : B.Contains (Spec (U.left.1.residueField t))) :
    AlgebraicGeometry.Space.schemePoint B S hS U (residueFieldRepresentative B S hS U t ht) = t :=
  Scheme.fromSpecResidueField_apply _ _

private lemma dominates_residueFieldRepresentative
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U))
    (ht : B.Contains (Spec (U.left.1.residueField
      (AlgebraicGeometry.Space.schemePoint B S hS U p)))) :
    AlgebraicGeometry.Space.FieldValuedPoint.Dominates B S hS (yoneda.obj U) p
      (residueFieldRepresentative B S hS U
        (AlgebraicGeometry.Space.schemePoint B S hS U p) ht) := by
  let f := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p.value
  let q := Scheme.SpecToEquivOfField p.carrier U.left.1 f
  let g := Spec.map q.2
  have hfac : g ≫ U.left.1.fromSpecResidueField q.1 = f :=
    (Scheme.SpecToEquivOfField p.carrier U.left.1).symm_apply_apply f
  let a : p.siteObject ⟶
      (residueFieldRepresentative B S hS U
        (AlgebraicGeometry.Space.schemePoint B S hS U p) ht).siteObject :=
    Over.homMk ⟨g⟩ (by
      apply ObjectProperty.hom_ext
      show g ≫ (U.left.1.fromSpecResidueField q.1 ≫ B.inclusion.map U.hom) = p.toBase
      rw [← Category.assoc, hfac]
      exact congrArg (fun h => B.inclusion.map h) p.value.w)
  refine ⟨a, ?_⟩
  show a ≫ (residueFieldRepresentative B S hS U
    (AlgebraicGeometry.Space.schemePoint B S hS U p) ht).value = p.value
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  exact hfac

private lemma hasSmoothRepresentative_of_smoothAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (h : InfinitesimalLifting.SmoothAt f x) :
    AlgebraicGeometry.MorphismOfGerms.HasRepresentativeWithProperty (@Smooth.{u})
      (AlgebraicGeometry.MorphismOfGerms.ofSchemeHom f x) := by
  obtain ⟨W, hxW, hW⟩ := h
  have hW' : Smooth (W.ι ≫ f) := by
    have e : Arrow.mk (f.resLE ⊤ W le_top) ≅ Arrow.mk (W.ι ≫ f) :=
      Arrow.isoMk (Iso.refl _) Y.topIso (by
        simpa [Scheme.topIso] using
          (Scheme.Hom.resLE_comp_ι f (U := ⊤) (V := W) (e := le_top)).symm)
    let : MorphismProperty.RespectsIso (@Smooth.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    exact (MorphismProperty.arrow_mk_iso_iff (@Smooth.{u}) e).mp hW
  let r : AlgebraicGeometry.MorphismOfGerms.Representative
      ⟨X, x⟩ ⟨Y, f x⟩ := {
    source := W
    mem_source := hxW
    hom := W.ι ≫ f
    map_point := rfl }
  let r₀ : AlgebraicGeometry.MorphismOfGerms.Representative
      ⟨X, x⟩ ⟨Y, f x⟩ := {
    source := ⊤
    mem_source := by simp
    hom := X.topIso.hom ≫ f
    map_point := rfl }
  have hsource : X.homOfLE (show W ≤ (⊤ : X.Opens) from le_top) ≫
      X.topIso.hom = W.ι := by
    rw [Scheme.topIso_hom, Scheme.homOfLE_ι]
  have hagree : r.AgreeNear r₀ := by
    refine ⟨W, hxW, le_rfl, le_top, ?_⟩
    dsimp [r, r₀]
    simp
  exact ⟨r, AlgebraicGeometry.MorphismOfGerms.mk_eq_mk_iff.mpr hagree, hW'⟩

section SiteContainsArtinianSpectrum

open Cardinal

private theorem spec_contains_of_artinianLocal_residueEquiv
    (B : AlgebraicGeometry.BigFppfSite.{u}) {R K : Type u}
    [CommRing R] [IsLocalRing R] [IsArtinianRing R] [CommRing K]
    (hK : (Spec (.of K)).size < B.cutoff)
    (e : IsLocalRing.ResidueField R ≃+* K) :
    B.Contains (Spec (.of R)) := by
  -- A module of finite length over a local ring has cardinality at most `max ℵ₀ |k|`.
  have hlen : ∀ {M : Type u} [AddCommGroup M] [Module R M], IsFiniteLength R M →
      Cardinal.mk M ≤ max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField R)) := by
    intro M _ _ h
    let c : Cardinal := max Cardinal.aleph0 (Cardinal.mk (IsLocalRing.ResidueField R))
    induction h with
    | @of_subsingleton M _ _ hsub =>
        let : Subsingleton M := hsub
        have hinj : Function.Injective (fun _ : M => (ULift.up PUnit.unit : ULift.{u} PUnit)) :=
          fun _ _ _ => Subsingleton.elim _ _
        exact (Cardinal.mk_le_of_injective hinj).trans (by
          show Cardinal.mk (ULift.{u} PUnit) ≤ c
          exact le_trans (by simp) (le_max_left _ _))
    | @of_simple_quotient M _ _ N hsimple hN ih =>
        have hfactor : Cardinal.mk (M ⧸ N) ≤ c := by
          obtain ⟨I, hI, ⟨e⟩⟩ :=
            isSimpleModule_iff_quot_maximal.mp
              (show IsSimpleModule R (M ⧸ N) from inferInstance)
          have hIeq : I = IsLocalRing.maximalIdeal R :=
            (IsLocalRing.isMaximal_iff (R := R)).mp hI
          rw [hIeq] at e
          calc
            Cardinal.mk (M ⧸ N) = Cardinal.mk (R ⧸ IsLocalRing.maximalIdeal R) :=
              Cardinal.mk_congr e.toEquiv
            _ = Cardinal.mk (IsLocalRing.ResidueField R) := rfl
            _ ≤ c := le_max_right _ _
        have hNcard : Cardinal.mk N ≤ c := by simpa [c] using ih
        let rep : M ⧸ N → M := fun q => Classical.choose (Submodule.Quotient.mk_surjective N q)
        have hrep (q : M ⧸ N) : Submodule.Quotient.mk (rep q) = q :=
          Classical.choose_spec (Submodule.Quotient.mk_surjective N q)
        let g : (M ⧸ N) × N → M := fun z => rep z.1 + z.2
        have hg : Function.Surjective g := by
          intro m
          let q : M ⧸ N := Submodule.Quotient.mk m
          have hmN : m - rep q ∈ N := by
            apply (Submodule.Quotient.eq N).mp
            simpa [q] using (hrep q).symm
          refine ⟨(q, ⟨m - rep q, hmN⟩), ?_⟩
          simp [g]
        have hprod : Cardinal.mk ((M ⧸ N) × N) ≤ c := by
          calc
            Cardinal.mk ((M ⧸ N) × N) = Cardinal.mk (M ⧸ N) * Cardinal.mk N :=
              (by simpa only [Cardinal.lift_id] using Cardinal.mk_prod (M ⧸ N) N)
            _ ≤ max (max (Cardinal.mk (M ⧸ N)) (Cardinal.mk N)) Cardinal.aleph0 :=
              Cardinal.mul_le_max _ _
            _ ≤ c := max_le (max_le hfactor hNcard) (le_max_left _ _)
        exact (Cardinal.mk_le_of_surjective hg).trans hprod
  have hR := hlen ((isArtinianRing_iff_isFiniteLength R).mp inferInstance)
  rw [Cardinal.mk_congr e.toEquiv] at hR
  exact Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit hK hR

/-- A surjection of local rings induces an isomorphism of residue fields.

`AlgebraicGeometry.Space.residueFieldEquivOfSurjective` in
`StacksFrontier/AlgebraicGeometry/Spaces/SmoothAtInfinitesimalLifting.lean` is this same
construction, but it is `private` there, so it cannot be used from here;
`IsLocalRing.residueFieldEquivOfSurjective` is public but is stated for a surjective
`algebraMap`, not for a morphism of `CommRingCat`. -/
@[implicit_reducible] private noncomputable def residueFieldEquiv_of_surjective
    {R' R : CommRingCat.{u}} [IsLocalRing R'] [IsLocalRing R] (φ : R' ⟶ R)
    (hsurj : Function.Surjective φ.hom) :
    IsLocalRing.ResidueField R' ≃+* IsLocalRing.ResidueField R := by
  letI : IsLocalHom φ.hom := IsLocalHom.of_surjective φ.hom hsurj
  let ψ := IsLocalRing.ResidueField.map φ.hom
  have hψsurj : Function.Surjective ψ := by
    intro y
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨b', rfl⟩ := hsurj b
    exact ⟨IsLocalRing.residue R' b', by
      simp [ψ, IsLocalRing.ResidueField.map_residue]⟩
  exact RingEquiv.ofBijective ψ ⟨RingHom.injective ψ, hψsurj⟩

/-- At the closed point of the spectrum of a local ring, the canonical morphism from
the spectrum of the residue field is the one induced by the residue map. -/
private lemma specMap_residue_eq_fromSpecResidueField
    (R : CommRingCat.{u}) [IsLocalRing R] :
    Spec.map (CommRingCat.ofHom
        ((AlgebraicGeometry.residueFieldAtClosedPointEquiv (R := R)).symm.toRingHom.comp
          (IsLocalRing.residue R))) =
      (Spec R).fromSpecResidueField (IsLocalRing.closedPoint R : Spec R) := by
  dsimp only [Scheme.fromSpecResidueField]
  rw [← Spec_stalkClosedPointIso, ← Spec.map_comp]
  rfl

/-- A surjection of local rings induces the residue map on residue fields. -/
private lemma residueFieldEquiv_of_surjective_residue
    {R' R : CommRingCat.{u}} [IsLocalRing R'] [IsLocalRing R] (φ : R' ⟶ R)
    (hsurj : Function.Surjective φ.hom) (a : R') :
    residueFieldEquiv_of_surjective φ hsurj (IsLocalRing.residue R' a) =
      IsLocalRing.residue R (φ.hom a) := rfl

end SiteContainsArtinianSpectrum

/-- Identifications of definitionally equal objects compose away. -/
private lemma eqToHom_sandwich {C : Type u₁} [Category.{v₁} C] {X Y : C}
    (h₁ : X = X) (h₂ : Y = Y) (f : X ⟶ Y) : eqToHom h₁ ≫ f ≫ eqToHom h₂ = f := by
  simp

/-- A ring map is determined by the morphism of spectra it induces, after
composition with an open immersion. -/
private lemma ringHom_eq_of_specMap_comp_openImmersion
    {R A : CommRingCat.{u}} {T : Scheme.{u}} (i : Spec R ⟶ T) (hi : IsOpenImmersion i)
    {f g : R ⟶ A} (h : Spec.map f ≫ i = Spec.map g ≫ i) : f = g := by
  let := hi
  rw [← Spec.map_inj]
  exact (cancel_mono i).mp h

/-- An Artinian local algebra whose residue field is identified with the fixed field
compatibly with the base, viewed as an object of `𝒞_Λ`. -/
@[implicit_reducible] private def artinianObject {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
    (A : CommRingCat.{u}) [IsLocalRing A] [IsArtinianRing A] [Algebra Λ A]
    (eA : IsLocalRing.ResidueField A ≃+* l)
    (hbase : ∀ r : Λ, eA (IsLocalRing.residue A (algebraMap Λ A r)) = algebraMap Λ l r) :
    Deformation.ArtinianLocalAlgCat.{u, u, u} Λ l where
  carrier := A
  residueEquiv := AlgEquiv.ofRingEquiv (f := eA) (by
    intro r
    rw [IsScalarTower.algebraMap_apply Λ A (IsLocalRing.ResidueField A),
      IsLocalRing.ResidueField.algebraMap_eq]
    exact hbase r)

/-- The residue map of `artinianObject` is the chosen identification
composed with the residue map of the ring. -/
private lemma artinianObject_residueMap {Λ l : Type u} [CommRing Λ] [Field l] [Algebra Λ l]
    (A : CommRingCat.{u}) [IsLocalRing A] [IsArtinianRing A] [Algebra Λ A]
    (eA : IsLocalRing.ResidueField A ≃+* l)
    (hbase : ∀ r : Λ, eA (IsLocalRing.residue A (algebraMap Λ A r)) = algebraMap Λ l r) :
    Deformation.Artin.residueMap (artinianObject A eA hbase) =
      eA.toRingHom.comp (IsLocalRing.residue A) := rfl

/-- A smooth scheme chart at a point of an algebraic space gives smoothness at
the corresponding point of the algebraic space. -/
private lemma smoothAt_of_schemeChartSmoothAt
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (x : AlgebraicGeometry.Space.points B S hS X)
    (c : AlgebraicGeometry.Space.EtaleChartAtPoint B S hS f x)
    (h : InfinitesimalLifting.SmoothAt
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map c.h)
      (c.sourcePoint B S hS)) :
    AlgebraicGeometry.Space.IsSmoothAt B S hS f x := by
  let P : MorphismProperty Scheme.{u} := @Smooth
  let Q : ∀ {A D : AlgebraicGeometry.GermOfScheme.{u}},
      AlgebraicGeometry.MorphismOfGerms A D → Prop :=
    AlgebraicGeometry.MorphismOfGerms.HasRepresentativeWithProperty P
  have hP : AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget P :=
    AlgebraicGeometry.Smooth.isEtaleLocalOnSourceAndTarget
  have hQ : AlgebraicGeometry.MorphismOfGerms.IsEtaleLocalOnSourceAndTarget Q :=
    AlgebraicGeometry.MorphismOfGerms.hasRepresentativeWithProperty_isEtaleLocalOnSourceAndTarget
      P hP
  have hsome : AlgebraicGeometry.Space.HoldsOnSomeEtaleChartAtPoint B S hS Q f x :=
    ⟨c, hasSmoothRepresentative_of_smoothAt
      ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map c.h)
      (c.sourcePoint B S hS) h⟩
  have hall : AlgebraicGeometry.Space.HoldsOnEveryEtaleChartAtPoint B S hS Q f x :=
    (AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_some
      B S hS Q hQ hX hY f x).2 hsome
  rcases (AlgebraicGeometry.Space.holdsOnEveryEtaleChartAtPoint_iff_exists_open
      B S hS P hP hX hY f x).mp hall with ⟨U, hU, hxU, hUf⟩
  obtain ⟨xU, hxU⟩ := Set.mem_range.mp hxU
  exact ⟨U, hU, xU, hxU, hUf⟩

/-- An étale chart can be pointed by its residue field, without changing its
image point or its underlying chart. -/
@[implicit_reducible] private def residueFieldChart
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {x : AlgebraicGeometry.Space.points B S hS F}
    (c : AlgebraicGeometry.Space.EtaleChartAtPoint B S hS f x)
    (ht : B.Contains (Spec (c.U.left.1.residueField
      (AlgebraicGeometry.Space.schemePoint B S hS c.U c.representative)))) :
    AlgebraicGeometry.Space.EtaleChartAtPoint B S hS f x :=
  { c with
    representative := residueFieldRepresentative B S hS c.U
      (AlgebraicGeometry.Space.schemePoint B S hS c.U c.representative) ht
    point := IsLocalRing.closedPoint _
    maps_to := by
      have heq : (residueFieldRepresentative B S hS c.U
          (AlgebraicGeometry.Space.schemePoint B S hS c.U c.representative) ht).class B S hS
          (yoneda.obj c.U) = c.representative.class B S hS (yoneda.obj c.U) :=
        Quot.sound ⟨c.representative,
          dominates_residueFieldRepresentative B S hS c.U c.representative ht,
          AlgebraicGeometry.Space.FieldValuedPoint.dominates_refl B S hS (yoneda.obj c.U) _⟩
      rw [heq]
      exact c.maps_to }

private lemma residueFieldChart_sourcePoint
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : F ⟶ G} {x : AlgebraicGeometry.Space.points B S hS F}
    (c : AlgebraicGeometry.Space.EtaleChartAtPoint B S hS f x)
    (ht : B.Contains (Spec (c.U.left.1.residueField
      (AlgebraicGeometry.Space.schemePoint B S hS c.U c.representative)))) :
    (residueFieldChart B S hS c ht).sourcePoint B S hS = c.sourcePoint B S hS := by
  show AlgebraicGeometry.Space.schemePoint B S hS c.U
    (residueFieldRepresentative B S hS c.U
      (AlgebraicGeometry.Space.schemePoint B S hS c.U c.representative) ht) = _
  rw [residueFieldRepresentative_schemePoint]
  exact congrArg ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map c.representative.value)
    (show IsLocalRing.closedPoint c.representative.carrier = c.point from
      Subsingleton.elim _ _)

@[implicit_reducible] private noncomputable def terminalYonedaIso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    yoneda.obj (Over.mk (𝟙 (B.obj hS)) : AlgebraicGeometry.BigFppfOver B S hS) ≅
      ⊤_ ((AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := by
  let U₀ : AlgebraicGeometry.BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))
  let hU₀ : IsTerminal U₀ := Over.mkIdTerminal (X := B.obj hS)
  have hY : IsTerminal (yoneda.obj U₀) := by
    refine IsTerminal.ofUniqueHom
      (fun F => {
        app := fun V => by
          simpa only [yoneda_obj_obj] using
            (↾fun (_ : F.obj V) => hU₀.from V.unop)
        naturality := by
          intro V W f
          ext x
          apply hU₀.hom_ext })
      (fun F f => by
        ext V x
        exact hU₀.hom_ext _ _)
  exact hY.uniqueUpToIso terminalIsTerminal

private theorem schemeProperty_presheaf_id
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty Scheme.{u})
    (hIso : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsIso f → P f)
    (T : AlgebraicGeometry.BigFppfOver B S hS) :
    (MorphismProperty.presheaf
      (MorphismProperty.inverseImage P (AlgebraicGeometry.BigFppfOver.toScheme B S hS)))
      (𝟙 (yoneda.obj T)) := by
  show MorphismProperty.relative yoneda
    (MorphismProperty.inverseImage P (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
    (𝟙 (yoneda.obj T))
  constructor
  · exact Functor.relativelyRepresentable.of_isIso yoneda _
  · intro A C g fst snd hsq
    have hmap : IsIso (yoneda.map snd) := hsq.isIso_snd_of_isIso
    let : IsIso snd := Yoneda.fullyFaithful.isIso_of_isIso_map snd
    let : IsIso ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map snd) :=
      Functor.map_isIso _ snd
    exact hIso _ inferInstance

private theorem terminalYonedaIso_etale
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (MorphismProperty.presheaf
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS)))
      (terminalYonedaIso B S hS).hom := by
  let Q := MorphismProperty.presheaf
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS))
  let : Q.RespectsIso := inferInstance
  exact MorphismProperty.RespectsIso.postcomp Q
    (terminalYonedaIso B S hS).hom (𝟙 _)
    (schemeProperty_presheaf_id B S hS (@Etale.{u})
      (fun f hf => by let := hf; infer_instance)
      (Over.mk (𝟙 (B.obj hS))))

private theorem etale_presheaf_of_isEtale
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U : AlgebraicGeometry.BigFppfOver B S hS}
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : yoneda.obj U ⟶ F) (hf : AlgebraicGeometry.Space.IsEtale B S hS f) :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS)).presheaf f := by
  let Q := MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
    (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  let : Q.IsStableUnderBaseChange := by
    refine ⟨fun hs hg => ?_⟩
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Etale.{u}) (hs.map (AlgebraicGeometry.BigFppfOver.toScheme B S hS)) hg
  have hid : Q.presheaf (𝟙 (yoneda.obj U)) := by
    show Q.presheaf (yoneda.map (𝟙 U))
    exact (MorphismProperty.relative_map_iff (F := yoneda) (P := Q)).2 (by
      show Etale ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map (𝟙 U))
      infer_instance)
  simpa using hf U (𝟙 (yoneda.obj U)) hid

/-- A pointed étale chart represents the same point as any chosen field-valued
representative, up to a common field extension. We use the common extension as
the residue field for the deformation square. -/
private lemma chartRepresentative_hasCommonExtension
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (x : AlgebraicGeometry.Space.points B S hS F)
    (c : AlgebraicGeometry.Space.EtaleChartAtPoint B S hS f x)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS F)
    (hp : p.class B S hS F = x) :
    AlgebraicGeometry.Space.FieldValuedPoint.HasCommonExtension B S hS F
      (AlgebraicGeometry.Space.FieldValuedPoint.map B S hS (yoneda.obj c.U) c.a
        c.representative) p := by
  have heq : AlgebraicGeometry.Space.pointsMap B S hS (yoneda.obj c.U) c.a
      (c.representative.class B S hS (yoneda.obj c.U)) = p.class B S hS F :=
    c.maps_to.trans hp.symm
  rw [AlgebraicGeometry.Space.pointsMap_class] at heq
  exact (AlgebraicGeometry.Space.FieldValuedPoint.class_eq_class_iff B S hS F _ _).mp heq

@[implicit_reducible] private noncomputable def schemeFieldValuedPoint
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U)) :
    AlgebraicGeometry.FieldValuedPoint ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).obj U) where
  carrier := p.carrier
  map := (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map p.value

/-- Common field extensions do not change the underlying scheme point of a
representable chart. -/
private lemma schemePoint_eq_of_commonExtension
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (p q : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U))
    (h : AlgebraicGeometry.Space.FieldValuedPoint.HasCommonExtension B S hS (yoneda.obj U) p q) :
    AlgebraicGeometry.Space.schemePoint B S hS U p =
      AlgebraicGeometry.Space.schemePoint B S hS U q := by
  have hdom {r s : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj U)}
      (h : AlgebraicGeometry.Space.FieldValuedPoint.Dominates B S hS (yoneda.obj U) r s) :
      AlgebraicGeometry.FieldValuedPoint.Dominates
        (schemeFieldValuedPoint B S hS U r)
        (schemeFieldValuedPoint B S hS U s) := by
    obtain ⟨f, hf⟩ := h
    refine ⟨(AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f, ?_⟩
    show (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map f ≫
      (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map s.value =
        (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map r.value
    have hf' : f ≫ s.value = r.value := by
      change (yoneda.obj U).map f.op s.value = r.value at hf
      simp only [yoneda_obj_map, Quiver.Hom.unop_op] at hf
      change f ≫ s.value = r.value at hf
      exact hf
    rw [← Functor.map_comp, hf']
  obtain ⟨r, hp, hq⟩ := h
  have hce : AlgebraicGeometry.FieldValuedPoint.HasCommonExtension
      (schemeFieldValuedPoint B S hS U p) (schemeFieldValuedPoint B S hS U q) :=
    ⟨schemeFieldValuedPoint B S hS U r, hdom hp, hdom hq⟩
  have hpoints := (AlgebraicGeometry.FieldValuedPoint.hasCommonExtension_iff_point_eq
    (schemeFieldValuedPoint B S hS U p) (schemeFieldValuedPoint B S hS U q)).mp hce
  change (schemeFieldValuedPoint B S hS U p).point =
    (schemeFieldValuedPoint B S hS U q).point at hpoints
  exact hpoints

@[implicit_reducible] private noncomputable def restrictChartFieldPoint
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (x : AlgebraicGeometry.Space.points B S hS F)
    (c : AlgebraicGeometry.Space.EtaleChartAtPoint B S hS (terminal.from F) x)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj c.U))
    {r : AlgebraicGeometry.Space.FieldValuedPoint B S hS F}
    (f : r.siteObject ⟶ p.siteObject) :
    AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj c.U) where
  carrier := r.carrier
  field := r.field
  contained := r.contained
  toBase := r.toBase
  value := (yoneda.obj c.U).map f.op p.value

private lemma schemePoint_restrictChartFieldPoint
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (x : AlgebraicGeometry.Space.points B S hS F)
    (c : AlgebraicGeometry.Space.EtaleChartAtPoint B S hS (terminal.from F) x)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj c.U))
    {r : AlgebraicGeometry.Space.FieldValuedPoint B S hS F}
    (f : r.siteObject ⟶ p.siteObject) :
    AlgebraicGeometry.Space.schemePoint B S hS c.U
        (restrictChartFieldPoint B S hS x c p f) =
      AlgebraicGeometry.Space.schemePoint B S hS c.U p := by
  apply schemePoint_eq_of_commonExtension
  refine ⟨restrictChartFieldPoint B S hS x c p f,
    AlgebraicGeometry.Space.FieldValuedPoint.dominates_refl B S hS (yoneda.obj c.U) _, ?_⟩
  exact ⟨f, rfl⟩

private lemma restrictChartFieldPoint_mapsTo
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (x : AlgebraicGeometry.Space.points B S hS F)
    (c : AlgebraicGeometry.Space.EtaleChartAtPoint B S hS (terminal.from F) x)
    (p : AlgebraicGeometry.Space.FieldValuedPoint B S hS (yoneda.obj c.U))
    {r : AlgebraicGeometry.Space.FieldValuedPoint B S hS F}
    (f : r.siteObject ⟶ p.siteObject)
    (hf : F.map f.op
      ((AlgebraicGeometry.Space.FieldValuedPoint.map B S hS (yoneda.obj c.U) c.a p).value) =
        r.value) :
    (AlgebraicGeometry.Space.FieldValuedPoint.map B S hS (yoneda.obj c.U) c.a
      (restrictChartFieldPoint B S hS x c p f)).value = r.value := by
  show c.a.app (Opposite.op r.siteObject)
      ((yoneda.obj c.U).map f.op p.value) = r.value
  have hn := congrArg (fun k => k p.value) (c.a.naturality f.op)
  have hn' : c.a.app (Opposite.op r.siteObject)
      ((yoneda.obj c.U).map f.op p.value) =
        F.map f.op (c.a.app (Opposite.op p.siteObject) p.value) := by
    simpa only [types_comp_apply] using hn
  have hf' : F.map f.op (c.a.app (Opposite.op p.siteObject) p.value) = r.value := by
    simpa only [AlgebraicGeometry.Space.FieldValuedPoint.map] using hf
  exact hn'.trans hf'

@[instance_reducible] private def predeformationCarrierCategory
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} {iΛ : Spec (.of Λ) ⟶ S}
    {X : Type u₁} [Category.{v₁} X] {q : X ⥤ Over S} {x₀ : X}
    {hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)}
    (P : Deformation.Artin.PredeformationConstruction iΛ q x₀ hx₀) :
    Category.{max u v₁} P.carrier := P.category

attribute [local instance] predeformationCarrierCategory

private lemma deformationObject_ext
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type u₁} [Category.{v₁} X] (q : X ⥤ Over S) (x₀ : X)
    (hx₀ : q.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    {a b : Deformation.Artin.DeformationObject iΛ q x₀ hx₀}
    (hA : a.algebra = b.algebra) (hx : a.point = b.point)
    (ha : a.arrow ≫ eqToHom hx = b.arrow) : a = b := by
  cases a
  cases b
  dsimp only at hA hx ha
  cases hA
  cases hx
  simp only [eqToHom_refl, Category.comp_id] at ha
  cases ha
  rfl

/-- Transport of an `arrow_base` equation along a functor over the base. -/
private lemma eqToHom_map_left_comp_eq {S : Scheme.{u}}
    {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
    {qX : X ⥤ Over S} {qY : Y ⥤ Over S} {G : X ⥤ Y} (hG : G ⋙ qY = qX) {A B : X} (f : A ⟶ B)
    {U V : Over S} {Z : U.left ⟶ V.left} (ha : qX.obj A = U) (hb : qX.obj B = V)
    (h : eqToHom (congrArg Over.left ha).symm ≫ (qX.map f).left ≫
      eqToHom (congrArg Over.left hb) = Z) :
    eqToHom (congrArg Over.left ((Functor.congr_obj hG A).trans ha)).symm ≫
      (qY.map (G.map f)).left ≫ eqToHom (congrArg Over.left ((Functor.congr_obj hG B).trans hb)) =
        Z := by
  have h' := congrArg Over.Hom.left (Functor.congr_hom hG f)
  dsimp only [Functor.comp_map] at h'
  rw [h']
  simpa only [Over.comp_left, Over.eqToHom_left, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans] using h

/-- Applying a functor over the base to a deformation does not change its
Artinian algebra. -/
@[implicit_reducible] private def mapDeformationObject
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
    (qX : X ⥤ Over S) (qY : Y ⥤ Over S) (G : X ⥤ Y)
    (hG : G ⋙ qY = qX) (x₀ : X)
    (hx₀ : qX.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (a : Deformation.Artin.DeformationObject iΛ qX x₀ hx₀) :
    Deformation.Artin.DeformationObject iΛ qY (G.obj x₀)
      (Deformation.Artin.imageBasePoint (qY := qY) iΛ qX G hG x₀ hx₀) where
  algebra := a.algebra
  point := G.obj a.point
  arrow := G.map a.arrow
  base := (Functor.congr_obj hG a.point).trans a.base
  arrow_base := eqToHom_map_left_comp_eq hG a.arrow hx₀ a.base a.arrow_base

@[implicit_reducible] private def mapDeformationMorphism
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
    (qX : X ⥤ Over S) (qY : Y ⥤ Over S) (G : X ⥤ Y)
    (hG : G ⋙ qY = qX) (x₀ : X)
    (hx₀ : qX.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    {a b : Deformation.Artin.DeformationObject iΛ qX x₀ hx₀}
    (f : Deformation.Artin.DeformationMorphism iΛ qX x₀ hx₀ a b) :
    Deformation.Artin.DeformationMorphism iΛ qY (G.obj x₀)
      (Deformation.Artin.imageBasePoint (qY := qY) iΛ qX G hG x₀ hx₀)
      (mapDeformationObject iΛ qX qY G hG x₀ hx₀ a)
      (mapDeformationObject iΛ qX qY G hG x₀ hx₀ b) where
  ringHom := f.ringHom
  arrow := G.map f.arrow
  triangle := by
    change G.map b.arrow ≫ G.map f.arrow = G.map a.arrow
    rw [← G.map_comp, f.triangle]
  arrow_base := eqToHom_map_left_comp_eq hG f.arrow b.base a.base f.arrow_base

private lemma mapPredeformationCategory_objects
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {S : Scheme.{u}} (iΛ : Spec (.of Λ) ⟶ S)
    {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
    (qX : X ⥤ Over S) (qY : Y ⥤ Over S) (G : X ⥤ Y)
    (hG : G ⋙ qY = qX) (x₀ : X)
    (hx₀ : qX.obj x₀ = Over.mk
      (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (a : (Deformation.Artin.predeformationCategory iΛ qX x₀ hx₀).carrier) :
    (Deformation.Artin.predeformationCategory iΛ qY (G.obj x₀)
      (Deformation.Artin.imageBasePoint (qY := qY) iΛ qX G hG x₀ hx₀)).objects
        ((Deformation.Artin.mapPredeformationCategory iΛ qX qY G hG x₀ hx₀).toFunctor.obj a) =
      mapDeformationObject iΛ qX qY G hG x₀ hx₀
        ((Deformation.Artin.predeformationCategory iΛ qX x₀ hx₀).objects a) := by
  let PX := Deformation.Artin.predeformationCategory iΛ qX x₀ hx₀
  let PY := Deformation.Artin.predeformationCategory iΛ qY (G.obj x₀)
    (Deformation.Artin.imageBasePoint (qY := qY) iΛ qX G hG x₀ hx₀)
  let H := Deformation.Artin.mapPredeformationCategory iΛ qX qY G hG x₀ hx₀
  refine deformationObject_ext _ _ _ _ ?_ (H.object_point a) ?_
  · exact (PY.object_projection _).symm.trans
      ((Functor.congr_obj H.projection_comm a).trans (PX.object_projection a))
  · show (PY.objects (H.toFunctor.obj a)).arrow ≫ eqToHom (H.object_point a) =
      G.map (PX.objects a).arrow
    rw [H.object_arrow]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
    rfl

end Deformation.Artin.BaseChange

end
