module

public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.MeromorphicQuasicoherent.Criteria
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicAffineChartReconstruction
public import StacksFrontier.AlgebraicGeometry.Meromorphic.EtaleBaseChangeSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Meromorphic functions on an algebraic space represented by a scheme

Let `X` be an algebraic space over `S` which is representable by a scheme `X₀`.  The sheaf of
meromorphic functions `𝒦_{X₀}` of the scheme is a quasi-coherent sheaf of `𝒪_{X₀}`-algebras, so
it is the pushforward of the structure sheaf of a scheme `Y` affine over `X₀`, and the rule
`U ↦ Γ(U ×_{X₀} Y, 𝒪)` is a presheaf of `𝒪_X`-algebras on the small étale site of `X` whose
sheafification is the quasi-coherent `𝒪_X`-algebra associated to `𝒦_{X₀}`.

## Main definitions

* `AlgebraicGeometry.Space.schemeMeromorphicAlgebra`: the sheaf of meromorphic functions of a
  scheme, read as a sheaf of algebras over its structure sheaf.
* `AlgebraicGeometry.Space.associatedAlgebraPresheaf`: for a quasi-coherent algebra `A` on `T`,
  the presheaf of algebras `U ↦ Γ(U ×_T Spec_T A, 𝒪)` on a category of schemes over `T`.
* `AlgebraicGeometry.Space.representedChartOver`: the étale charts of a represented algebraic
  space, read as schemes over the representing scheme.
* `AlgebraicGeometry.Space.representedMeromorphicPresheaf` and
  `AlgebraicGeometry.Space.representedMeromorphicAlgebra`: the transported algebra and its
  sheafification on the small étale site of the space.
* `AlgebraicGeometry.Space.IsLocalizedOnAffineCharts`: the property of a presheaf of
  `𝒪_X`-algebras that its sections over every affine étale chart `U` are a localization of
  `𝒪_X(U)` at the nonzerodivisors of `𝒪_X(U)`.

## Main results

* `AlgebraicGeometry.Space.isEtaleChart_of_isIso`: an isomorphism onto a presheaf over `S` is an
  étale chart of it, so the representing scheme is an étale chart of `X`; hypotheses (a) and (b)
  of Stacks 0EN7 therefore hold on the representing scheme
  (`AlgebraicGeometry.Space.schemeWeaklyAssociatedPoints_representing_subset_genericPoints` and
  `AlgebraicGeometry.Space.finite_irreducibleComponents_representing`), which is what makes
  `𝒦_{X₀}` quasi-coherent.
* `AlgebraicGeometry.Space.isSheaf_affineEtale_of_isLocalizedOnAffineCharts`: a presheaf of
  `𝒪_X`-algebras localized on the affine charts is a sheaf on the affine étale charts.
* `AlgebraicGeometry.Space.isLocalizedOnAffineCharts_sheafifyUnder`: sheafification preserves
  being localized on the affine charts.
* `AlgebraicGeometry.Space.isLocalizedOnAffineCharts_representedMeromorphicPresheaf`: the
  transported algebra is localized on the affine charts: over an affine étale chart `U`,
  `Γ(U ×_{X₀} Y, 𝒪)` is the total ring of fractions of `𝒪_X(U)`.
* `AlgebraicGeometry.Space.nonempty_meromorphicFunctionSheaf_iso_representedMeromorphicAlgebra`:
  **Stacks 0EN7**.

## Implementation notes

The quasi-coherent algebra `𝒦_{X₀}` is presented through the anti-equivalence of Stacks 01SA
between schemes affine over `X₀` and quasi-coherent `𝒪_{X₀}`-algebras: writing
`Y = Spec_{X₀} 𝒦_{X₀}`, the sections `Γ(U ×_{X₀} Y, 𝒪)` of the associated algebra over a chart
`g : U ⟶ X₀` are the global functions on a fibre product, which by the base-change clause of
Stacks 01SA are the sections of `g^* 𝒦_{X₀}` over `U`, as in the construction of the étale sheaf
associated to a quasi-coherent module (Stacks 03DT).  The whole presheaf is the composite of a
single functor with `AlgebraicGeometry.Scheme.Γ`, and its restriction maps and structural map
come from the fibre-product functor and its first projection.

The comparison runs through
`AlgebraicGeometry.Space.iso_meromorphic_of_isLocalization_affineCharts`.  Over an affine étale
chart `U` the ring `Γ(U ×_{X₀} Y, 𝒪)` is the total ring of fractions of `𝒪_X(U)`: over a
principal open of `U` mapping into an affine open `V` of `X₀` it is
`Γ(U, D(r)) ⊗_{Γ(X₀, V)} Q(Γ(X₀, V))`, since `𝒦_{X₀}(V) = Q(Γ(X₀, V))` (Stacks 02OW), which is
the total ring of fractions of `Γ(U, D(r))` because `Γ(X₀, V) → Γ(U, D(r))` is étale (the
comparison of Stacks 0EN6), and total rings of fractions glue along a cover by principal opens
(`AlgebraicGeometry.isLocalization_appTop_of_isPullback_of_etale`).  The transported presheaf
therefore agrees on affine charts with the presheaf of sectionwise total fraction rings, which
is a sheaf there, so sheafification does not change its sections on affine charts
(`AlgebraicGeometry.Space.isIso_toSheafify_app_of_isAffine`), and the affine charts are cover
dense in the small étale site.

## References

* [Stacks Project, Tag 0EN7](https://stacks.math.columbia.edu/tag/0EN7)
* [Stacks Project, Tag 0EN6](https://stacks.math.columbia.edu/tag/0EN6)
* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 0BB1](https://stacks.math.columbia.edu/tag/0BB1)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped nonZeroDivisors

universe u v w

namespace AlgebraicGeometry.Space

/-- The sheaf of meromorphic functions of a scheme, read as a sheaf of algebras over the
structure sheaf. -/
public noncomputable abbrev schemeMeromorphicAlgebra (T : Scheme.{u}) :
    Stacks.RelativeSpec.AlgebraSheaf T :=
  Under.mk T.toTotalQuotientSheaf

open Stacks.AlgebraicGeometry.MeromorphicQuasicoherent in
/-- The sheaf of meromorphic functions of a scheme whose weakly associated points are generic
points of irreducible components and whose quasi-compact opens have finitely many irreducible
components is a quasi-coherent sheaf of algebras. -/
public theorem isQuasicoherent_schemeMeromorphicAlgebra (T : Scheme.{u})
    (hwa : Stacks.Divisors.schemeWeaklyAssociatedPoints T ⊆ genericPoints T)
    (hfin : ∀ V : T.Opens, IsCompact (V : Set T) → (irreducibleComponents V).Finite) :
    (schemeMeromorphicAlgebra T).IsQuasicoherent :=
  meromorphicFunctions_isQuasicoherent_of_genericHypotheses hwa hfin

/-- The scheme affine over `T` whose structure sheaf pushes forward to a quasi-coherent algebra
`A` on `T`, the relative spectrum of `A`. -/
@[ega "II 1.3.1"]
public noncomputable def quasicoherentAlgebraSpec {T : Scheme.{u}}
    (A : Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra T) : Over T :=
  ((Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.equivalence T).inverse.obj A).unop.obj

/-- The first projection `U ×_T Spec_T A ⟶ U`, natural in the scheme `U` over `T`. -/
public noncomputable def associatedAlgebraProjection {T : Scheme.{u}} {C : Type v} [Category.{w} C]
    (P : C ⥤ Over T) (A : Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra T) :
    P ⋙ Over.pullback (quasicoherentAlgebraSpec A).hom ⋙
        Over.forget (quasicoherentAlgebraSpec A).left ⟶ P ⋙ Over.forget T where
  app U := pullback.fst (P.obj U).hom (quasicoherentAlgebraSpec A).hom
  naturality _ _ _ := by
    simp only [Functor.comp_obj, Over.forget_obj, Over.pullback_obj_left, Functor.comp_map,
      Over.forget_map, Over.pullback_map_left]
    exact pullback.lift_fst _ _ _

/-- The presheaf of algebras associated to a quasi-coherent algebra `A` on `T` over a category of
schemes over `T`: its sections over `U ⟶ T` are the global functions on `U ×_T Spec_T A`, with
restriction along the induced maps of fibre products and with the structural map from the global
functions on `U` given by the first projection. -/
public noncomputable def associatedAlgebraPresheaf {T : Scheme.{u}} {C : Type v} [Category.{w} C]
    (P : C ⥤ Over T) (A : Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra T) :
    Under ((P ⋙ Over.forget T).op ⋙ Scheme.Γ) :=
  Under.mk (Functor.whiskerRight (NatTrans.op (associatedAlgebraProjection P A)) Scheme.Γ)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (T : BigFppfOver B S hS)

/-- The scheme map from an étale chart of an algebraic space represented by `T` to the scheme
underlying `T`. -/
public noncomputable def chartToRepresentingScheme (i : X.1 ≅ yoneda.obj T)
    (U : SmallEtale B S hS X.1) :
    (BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj U) ⟶
      (BigFppfOver.toScheme B S hS).obj T :=
  (BigFppfOver.toScheme B S hS).map (yoneda.preimage (U.obj.hom ≫ i.hom))

/-- The étale charts of an algebraic space represented by `T`, read as schemes over the scheme
underlying `T`. -/
public noncomputable def representedChartOver (i : X.1 ≅ yoneda.obj T) :
    SmallEtale B S hS X.1 ⥤ Over ((BigFppfOver.toScheme B S hS).obj T) :=
  Functor.toOver (SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS) _
    (chartToRepresentingScheme B S hS X T i) (by
      intro U V f
      change (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map f) ≫
          (BigFppfOver.toScheme B S hS).map (yoneda.preimage (V.obj.hom ≫ i.hom)) =
        (BigFppfOver.toScheme B S hS).map (yoneda.preimage (U.obj.hom ≫ i.hom))
      rw [← Functor.map_comp]
      congr 1
      apply yoneda.map_injective
      simp)

/-- **An isomorphism onto a presheaf over `S` is an étale chart of it.**  It is representable,
and every represented base change of it is an isomorphism of schemes, hence étale. -/
public theorem isEtaleChart_of_isIso {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : yoneda.obj T ⟶ F)
    [IsIso f] : IsEtaleChart B S hS F (CostructuredArrow.mk f) := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda f, ?_⟩
  intro a b g fst snd h
  have h' : IsPullback (g ≫ CategoryTheory.inv f) (𝟙 (yoneda.obj a)) f g :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have _ : IsIso (yoneda.map snd) := by
    have h2 : IsIso ((h.isoIsPullback _ _ h').hom ≫ 𝟙 (yoneda.obj a)) := inferInstance
    rwa [h.isoIsPullback_hom_snd _ _ h'] at h2
  have _ : IsIso snd := isIso_of_reflects_iso snd yoneda
  have _ : IsIso ((BigFppfOver.toScheme B S hS).map snd) := inferInstance
  change Etale ((BigFppfOver.toScheme B S hS).map snd)
  infer_instance

/-- The étale chart of `X` presented by an isomorphism `X ≅ yoneda.obj T`: the representing
scheme, read as an étale chart of `X`. -/
public noncomputable def representingChart (i : X.1 ≅ yoneda.obj T) : SmallEtale B S hS X.1 :=
  ⟨CostructuredArrow.mk i.inv, isEtaleChart_of_isIso B S hS T i.inv⟩

/-- **Hypothesis (a) of Stacks 0EN7 read on the representing scheme.** -/
public theorem schemeWeaklyAssociatedPoints_representing_subset_genericPoints
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (i : X.1 ≅ yoneda.obj T) :
    Stacks.Divisors.schemeWeaklyAssociatedPoints ((BigFppfOver.toScheme B S hS).obj T) ⊆
      genericPoints ((BigFppfOver.toScheme B S hS).obj T) :=
  schemeWeaklyAssociatedPoints_chartScheme_subset_genericPoints B S hS X hwa
    (representingChart B S hS X T i)

/-- **Hypothesis (b) of Stacks 0EN7 read on the representing scheme.** -/
public theorem finite_irreducibleComponents_representing
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) (i : X.1 ≅ yoneda.obj T)
    (V : ((BigFppfOver.toScheme B S hS).obj T).Opens)
    (hV : IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj T))) :
    (irreducibleComponents V).Finite :=
  finite_irreducibleComponents_chartScheme B S hS hfin (representingChart B S hS X T i) V hV

/-- The sheaf of meromorphic functions of the representing scheme, as a quasi-coherent sheaf of
algebras over its structure sheaf. -/
public noncomputable def representingSchemeMeromorphicAlgebra
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) (i : X.1 ≅ yoneda.obj T) :
    Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra
      ((BigFppfOver.toScheme B S hS).obj T) :=
  ⟨schemeMeromorphicAlgebra _, isQuasicoherent_schemeMeromorphicAlgebra _
    (schemeWeaklyAssociatedPoints_representing_subset_genericPoints B S hS X T hwa i)
    (finite_irreducibleComponents_representing B S hS X T hfin i)⟩

/-- **The algebra transported from the representing scheme**, before sheafification: the presheaf
of `𝒪_X`-algebras on the small étale site of `X` whose sections over a chart `U` are the global
functions on `U ×_{X₀} Spec_{X₀} 𝒦_{X₀}`. -/
public noncomputable def representedMeromorphicPresheaf
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) (i : X.1 ≅ yoneda.obj T) :
    Under (structurePresheaf B S hS X.1) :=
  associatedAlgebraPresheaf (representedChartOver B S hS X T i)
    (representingSchemeMeromorphicAlgebra B S hS X T hwa hfin i)

/-- A presheaf of `𝒪_X`-algebras is *localized on the affine charts* when its sections over
every étale chart of `X` with affine underlying scheme are a localization of `𝒪_X(U)` at the
nonzerodivisors of `𝒪_X(U)`. -/
public def IsLocalizedOnAffineCharts (D : Under (structurePresheaf B S hS X.1)) : Prop :=
  ∀ (U : SmallEtale B S hS X.1), IsAffine (smallEtaleScheme B S hS X.1 U) →
    letI := (D.hom.app (op U)).hom.toAlgebra
    IsLocalization ((structurePresheaf B S hS X.1).obj (op U))⁰ (D.right.obj (op U))

open RingedSite.MultiplicativeSubpresheaf (isLocalization_localizationPresheaf_toAlgebra) in
/-- **A presheaf of `𝒪_X`-algebras localized on the affine charts is a sheaf there.**  Its
sections agree with those of the presheaf of sectionwise total fraction rings, by the universal
property of localization, and that presheaf is a sheaf on the affine étale charts. -/
public theorem isSheaf_affineEtale_of_isLocalizedOnAffineCharts
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (D : Under (structurePresheaf B S hS X.1)) (hD : IsLocalizedOnAffineCharts B S hS X D) :
    Presheaf.IsSheaf (AffineEtale.topology B S hS X.1)
      ((AffineEtale.inclusion B S hS X.1).op ⋙ D.right) := by
  have e : Under.mk (Functor.whiskerLeft (AffineEtale.inclusion B S hS X.1).op D.hom) ≅
      Under.mk (toAffineRegularLocalizationPresheaf B S hS X) :=
    CategoryTheory.Under.localizationPresheafIso _ _
      (fun U => ((structurePresheaf B S hS X.1).obj (op U.unop.obj))⁰)
      (fun U => hD U.unop.obj U.unop.property)
      (fun U => by
        rw [← regularSections_eq_nonZeroDivisors B S hS X.1 U.unop.obj U.unop.property]
        exact isLocalization_localizationPresheaf_toAlgebra (regularSubpresheaf B S hS X)
          (op U.unop.obj))
  exact (Presheaf.isSheaf_of_iso_iff ((Under.forget _).mapIso e)).mpr
    (isSheaf_affineRegularLocalizationPresheaf B S hS X hwa hfin)

/-- The sheafification of a presheaf of `𝒪_X`-algebras on the small étale site of `X`, as an
algebra over `𝒪_X`. -/
public noncomputable def sheafifyUnder (D : Under (structurePresheaf B S hS X.1)) :
    Under (structurePresheaf B S hS X.1) :=
  Under.mk (D.hom ≫ toSheafify (SmallEtale.topology B S hS X.1) D.right)

/-- Being a localization is transported along an isomorphism of commutative rings under `R`. -/
private theorem isLocalization_of_commRingCatIso {R A K : CommRingCat.{u}} (φ : R ⟶ A)
    (ψ : R ⟶ K) (j : A ≅ K) (h : φ ≫ j.hom = ψ) (M : Submonoid R)
    (hA : letI := φ.hom.toAlgebra; IsLocalization M A) :
    letI := ψ.hom.toAlgebra; IsLocalization M K := by
  let := φ.hom.toAlgebra
  let := ψ.hom.toAlgebra
  exact IsLocalization.isLocalization_of_algEquiv M
    (AlgEquiv.ofRingEquiv (f := j.commRingCatIsoToRingEquiv) fun r => by subst h; rfl : A ≃ₐ[R] K)

/-- **Sheafification preserves being localized on the affine charts.**  A presheaf of algebras
localized on the affine charts is a sheaf there, so the map into its sheafification is an
isomorphism over every affine chart. -/
public theorem isLocalizedOnAffineCharts_sheafifyUnder
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (D : Under (structurePresheaf B S hS X.1)) (hD : IsLocalizedOnAffineCharts B S hS X D) :
    IsLocalizedOnAffineCharts B S hS X (sheafifyUnder B S hS X D) := by
  intro U hU
  have hiso : IsIso ((toSheafify (SmallEtale.topology B S hS X.1) D.right).app (op U)) :=
    isIso_toSheafify_app_of_isAffine B S hS X.1 X.2 _
      (isSheaf_affineEtale_of_isLocalizedOnAffineCharts B S hS X hwa hfin D hD) U hU
  exact isLocalization_of_commRingCatIso _ _
    (asIso ((toSheafify (SmallEtale.topology B S hS X.1) D.right).app (op U))) rfl _ (hD U hU)

/-- **The algebra on the small étale site of `X` transported from the representing scheme**: the
sheafification of the presheaf of global functions on the fibre products
`U ×_{X₀} Spec_{X₀} 𝒦_{X₀}`. -/
public noncomputable def representedMeromorphicAlgebra
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) (i : X.1 ≅ yoneda.obj T) :
    Under (structurePresheaf B S hS X.1) :=
  sheafifyUnder B S hS X (representedMeromorphicPresheaf B S hS X T hwa hfin i)

/-- The structure morphism of the relative spectrum of a quasi-coherent algebra is affine. -/
@[sga "3 I 4.2"]
public instance isAffineHom_quasicoherentAlgebraSpec {T : Scheme.{u}}
    (A : Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra T) :
    _root_.AlgebraicGeometry.IsAffineHom (quasicoherentAlgebraSpec A).hom :=
  ((Stacks.AlgebraPullbackQcoh.affineEquivalenceAlgebras.equivalence T).inverse.obj A).unop.property

open Stacks.AlgebraPullbackQcoh in
/-- The structure sheaf of the relative spectrum of a quasi-coherent algebra `A` pushes forward to
`A`, as an algebra over the structure sheaf of the base. -/
public noncomputable def pushforwardAlgebraSpecIso {T : Scheme.{u}}
    (A : Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra T) :
    Stacks.AffineAlgebraEquivalence.pushforwardAlgebra (quasicoherentAlgebraSpec A).hom ≅ A.obj :=
  (affineEquivalenceAlgebras.pushforwardIso T
      ((affineEquivalenceAlgebras.equivalence T).inverse.obj A).unop).symm ≪≫
    (Stacks.AffineAlgebraEquivalence.IsQuasicoherentAlgebra T).ι.mapIso
      ((affineEquivalenceAlgebras.equivalence T).counitIso.app A)

/-- Over an affine open `V` of a scheme satisfying hypotheses (a) and (b) of Stacks 0EN6, the
sections of the relative spectrum of its meromorphic functions over the preimage of `V` form the
total ring of fractions of `Γ(T, V)`. -/
public theorem isLocalization_app_quasicoherentAlgebraSpec_meromorphic {T : Scheme.{u}}
    (hwa : Stacks.Divisors.schemeWeaklyAssociatedPoints T ⊆ genericPoints T)
    (hfin : ∀ V : T.Opens, IsCompact (V : Set T) → (irreducibleComponents V).Finite)
    (V : T.Opens) (hV : IsAffineOpen V) :
    letI := ((quasicoherentAlgebraSpec
      (⟨schemeMeromorphicAlgebra T, isQuasicoherent_schemeMeromorphicAlgebra T hwa hfin⟩ :
        Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra T)).hom.app V).hom.toAlgebra
    IsLocalization Γ(T, V)⁰ Γ((quasicoherentAlgebraSpec
      (⟨schemeMeromorphicAlgebra T, isQuasicoherent_schemeMeromorphicAlgebra T hwa hfin⟩ :
        Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra T)).left,
      (quasicoherentAlgebraSpec
      (⟨schemeMeromorphicAlgebra T, isQuasicoherent_schemeMeromorphicAlgebra T hwa hfin⟩ :
        Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra T)).hom ⁻¹ᵁ V) := by
  set A : Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra T :=
    ⟨schemeMeromorphicAlgebra T, isQuasicoherent_schemeMeromorphicAlgebra T hwa hfin⟩
  let e := pushforwardAlgebraSpecIso A
  exact isLocalization_of_commRingCatIso _ _
    (((sheafToPresheaf _ _).mapIso ((Under.forget _).mapIso e.symm)).app (op V))
    (congrArg (fun φ => φ.hom.app (op V)) (Under.w e.symm.hom)) _
    (AlgebraicGeometry.isLocalization_totalQuotientSheaf_obj hwa hfin hV)

variable {B S hS X T} in
/-- The morphism from an étale chart of `X` to the scheme representing `X` is étale. -/
public theorem etale_chartToRepresentingScheme (i : X.1 ≅ yoneda.obj T)
    (U : SmallEtale B S hS X.1) : Etale (chartToRepresentingScheme B S hS X T i U) := by
  let f : U ⟶ representingChart B S hS X T i :=
    ObjectProperty.homMk (CostructuredArrow.homMk (yoneda.preimage (U.obj.hom ≫ i.hom))
      (by simp [representingChart]))
  exact etale_toScheme_toOver_map B S hS X.1 f

/-- **The transported algebra is localized on the affine charts.**  Over an étale chart `U` of
`X` with affine underlying scheme, the global functions on `U ×_{X₀} Spec_{X₀} 𝒦_{X₀}` form the
total ring of fractions of `𝒪_X(U)`. -/
public theorem isLocalizedOnAffineCharts_representedMeromorphicPresheaf
    (hwa : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (hfin : HasLocallyFiniteIrreducibleComponents B S hS X.1) (i : X.1 ≅ yoneda.obj T) :
    IsLocalizedOnAffineCharts B S hS X
      (representedMeromorphicPresheaf B S hS X T hwa hfin i) := by
  intro U hU
  have : IsAffine
      (unop ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).op.obj (op U))) := hU
  have : Etale (chartToRepresentingScheme B S hS X T i U) :=
    etale_chartToRepresentingScheme i U
  exact isLocalization_appTop_of_isPullback_of_etale
    (schemeWeaklyAssociatedPoints_representing_subset_genericPoints B S hS X T hwa i)
    (finite_irreducibleComponents_representing B S hS X T hfin i)
    (isLocalization_app_quasicoherentAlgebraSpec_meromorphic
      (schemeWeaklyAssociatedPoints_representing_subset_genericPoints B S hS X T hwa i)
      (finite_irreducibleComponents_representing B S hS X T hfin i))
    (schemeWeaklyAssociatedPoints_chartScheme_subset_genericPoints B S hS X hwa U)
    (finite_irreducibleComponents_chartScheme B S hS hfin U)
    (IsPullback.of_hasPullback (chartToRepresentingScheme B S hS X T i U)
      (quasicoherentAlgebraSpec (representingSchemeMeromorphicAlgebra B S hS X T hwa hfin i)).hom)

/-- **Stacks 0EN7.**  Let `X` be an algebraic space over `S` all of whose weakly associated
points are points of codimension `0` and which satisfies the condition of Stacks 0BB1, and let
`X` be representable by a scheme `X₀`.  Then the sheaf of meromorphic functions `𝒦_X` is, as a
sheaf of `𝒪_X`-algebras, the algebra on the small étale site of `X` associated to the
quasi-coherent algebra `𝒦_{X₀}` of meromorphic functions on `X₀`. -/
@[stacks 0EN7]
public theorem nonempty_meromorphicFunctionSheaf_iso_representedMeromorphicAlgebra
    (codimZero : ∀ z ∈ weaklyAssociatedPointsOfSpace B S hS X, localRingDimension B S hS z = 0)
    (finiteComponents : HasLocallyFiniteIrreducibleComponents B S hS X.1)
    (i : X.1 ≅ yoneda.obj T) :
    Nonempty (Under.mk (toMeromorphicFunctionSheaf B S hS X.1 X.2).hom ≅
      representedMeromorphicAlgebra B S hS X T codimZero finiteComponents i) :=
  iso_meromorphic_of_isLocalization_affineCharts B S hS X codimZero finiteComponents
    (representedMeromorphicAlgebra B S hS X T codimZero finiteComponents i)
    ((presheafToSheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u}).obj
      (representedMeromorphicPresheaf B S hS X T codimZero finiteComponents i).right).property
    (isLocalizedOnAffineCharts_sheafifyUnder B S hS X codimZero finiteComponents _
      (isLocalizedOnAffineCharts_representedMeromorphicPresheaf B S hS X T codimZero
        finiteComponents i))

end AlgebraicGeometry.Space

end
