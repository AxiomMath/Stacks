module

public import Mathlib.RingTheory.Localization.Free
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartBasicOpenLocalization
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentChartSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.DenseSchematicLocusDecent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePreimageStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSupportIrreducible
public import StacksFrontier.AlgebraicGeometry.Spaces.ReducedBasicOpenNonempty
public import StacksFrontier.AlgebraicGeometry.Spaces.SpaceRationalFunctionChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedSchematicLocus

/-!
# A coherent module is free on a nonempty affine open chart of a reduced Noetherian space

Let `X` be a Noetherian algebraic space over a scheme `S` which is étale-locally reduced and has
a point, and let `G` be a coherent `𝒪_X`-module.  This file produces an étale chart `C` of `X`
whose structure morphism is an **open immersion**, whose scheme is **affine** and has a point,
and over which the sections `G(C)` are a **free** module of finite rank over the regular
functions `𝒪_X(C)`.  Freeness then propagates: over every affine chart `W` with a morphism
`g : W ⟶ C` the restrictions of a basis of `G(C)` form a basis of `G(W)`.

This is the generic trivialization in the proof of [Stacks, Tag 07UQ]: "there exists a dense
open subspace `U ⊂ X` which is a scheme ... after shrinking `U` we may assume that
`ℱ|_U ≅ 𝒪_U^{⊕ r}`".  The open subspace which is a scheme is the schematic locus, nonempty by
Properties of Spaces, Proposition [Stacks, Tag 06NH] for the decent space `X`; the shrinking is
the direct algebra argument the source mentions as an alternative to Cohomology of Schemes,
Lemma [Stacks, Tag 01YE].  Over an affine open `Spec A` of the schematic locus the sections of
`G` are a finite `A`-module `M`, the ring `A` is reduced and Noetherian, so the localization of
`A` at a minimal prime `𝔭` is a field and `M_𝔭` is free; a basis of `M_𝔭` spreads out to a basis
of `M_r` for some `r ∉ 𝔭`, and the basic open `D(r)` is the chart.

## Main results

* `AlgebraicGeometry.Space.nonempty_basis_of_isLocalizedModule_away`: a module which is a
  localization of `M` away from `r`, over a localization of the ring away from `r`, is free as
  soon as `LocalizedModule.Away r M` is, with a basis indexed by the same type.
* `AlgebraicGeometry.Space.exists_ne_zero_basis_localizedModule_away`: over a nontrivial reduced
  Noetherian ring every finite module becomes free of finite rank away from some nonzero
  element.
* `AlgebraicGeometry.Space.isBaseChange_chartRestrictLinear`: over a morphism of affine charts the
  sections of a quasi-coherent module are the base change of the sections over the target.
* `AlgebraicGeometry.Space.exists_isOpenImmersion_isAffine_chart`: a Noetherian algebraic space
  with a point has an affine open immersion chart with a point.
* `AlgebraicGeometry.Space.exists_isOpenImmersion_isAffine_chart_basis`: **the generic
  trivialization**: an affine open immersion chart with a point over which the sections of a
  coherent module are free of finite rank.

## References

* [Stacks Project, Tag 07UQ](https://stacks.math.columbia.edu/tag/07UQ)
* [Stacks Project, Tag 06NH](https://stacks.math.columbia.edu/tag/06NH)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Algebra -/

section Algebra

variable {A R' M N : Type*} [CommRing A] [CommRing R'] [Algebra A R'] [AddCommGroup M]
  [Module A M] [AddCommGroup N] [Module A N] [Module R' N] [IsScalarTower A R' N]

/-- **A localization of `M` away from `r` is free as soon as `LocalizedModule.Away r M` is.**

The localizations of the ring are identified with `Localization.Away r` by
`IsLocalization.algEquiv`, the localizations of the module with `LocalizedModule.Away r M` by
`IsLocalizedModule.iso`, which is linear over the localization by
`LinearEquiv.extendScalarsOfIsLocalization`; the basis is moved along the second identification
and its coefficients along the first. -/
theorem nonempty_basis_of_isLocalizedModule_away (r : A) [IsLocalization.Away r R']
    (g : M →ₗ[A] N) [IsLocalizedModule (Submonoid.powers r) g] {ι : Type*}
    (b : Module.Basis ι (Localization.Away r) (LocalizedModule (Submonoid.powers r) M)) :
    Nonempty (Module.Basis ι R' N) := by
  let e : Localization.Away r ≃ₐ[A] R' :=
    IsLocalization.algEquiv (Submonoid.powers r) (Localization.Away r) R'
  let : Module (Localization.Away r) N := Module.compHom N e.toRingEquiv.toRingHom
  have : IsScalarTower A (Localization.Away r) N := by
    refine IsScalarTower.of_algebraMap_smul fun a n => ?_
    show e.toRingEquiv.toRingHom (algebraMap A (Localization.Away r) a) • n = a • n
    rw [show e.toRingEquiv.toRingHom (algebraMap A (Localization.Away r) a) =
      algebraMap A R' a from e.commutes a, algebraMap_smul]
  let φ : LocalizedModule (Submonoid.powers r) M ≃ₗ[A] N :=
    IsLocalizedModule.iso (Submonoid.powers r) g
  let φ' : LocalizedModule (Submonoid.powers r) M ≃ₗ[Localization.Away r] N :=
    φ.extendScalarsOfIsLocalization (Submonoid.powers r) (Localization.Away r)
  exact ⟨(b.map φ').mapCoeffs e.toRingEquiv fun _ _ => rfl⟩

/-- **Over a nontrivial reduced Noetherian ring a finite module is free of finite rank away from
some nonzero element.**

Localize at a minimal prime `𝔭`: the localization is a reduced ring with a single prime ideal,
hence a field, so the localized module is free of finite rank, and a basis of it spreads out to
a basis away from some `r ∉ 𝔭` by
`Module.FinitePresentation.exists_basis_localizedModule_powers`.  Such an `r` is nonzero because
`0 ∈ 𝔭`. -/
theorem exists_ne_zero_basis_localizedModule_away (A : Type u) [CommRing A] [Nontrivial A]
    [_root_.IsReduced A] [IsNoetherianRing A] (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] :
    ∃ (r : A) (n : ℕ), r ≠ 0 ∧
      Nonempty (Module.Basis (Fin n) (Localization.Away r)
        (LocalizedModule (Submonoid.powers r) M)) := by
  obtain ⟨p, hp⟩ : ∃ p : Ideal A, p ∈ minimalPrimes A := by
    obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (R := A) (I := ⊥) bot_ne_top
    exact ⟨p, hp⟩
  have hpp : p.IsPrime := Ideal.IsMinimalPrime.isPrime hp
  have hfield : IsField (Localization.AtPrime p) := by
    have := Ring.KrullDimLE.of_isLocalization p hp (Localization.AtPrime p)
    exact Ring.KrullDimLE.isField_of_isReduced
  let : Field (Localization.AtPrime p) := hfield.toField
  have : Module.FinitePresentation A M := Module.finitePresentation_of_finite A M
  have : Module.Finite (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.Finite.of_isLocalizedModule p.primeCompl (Rₚ := Localization.AtPrime p)
      (LocalizedModule.mkLinearMap p.primeCompl M)
  let b := Module.Free.chooseBasis (Localization.AtPrime p) (LocalizedModule p.primeCompl M)
  obtain ⟨r, hr, b', -⟩ := Module.FinitePresentation.exists_basis_localizedModule_powers
    p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) (Localization.AtPrime p) b
  refine ⟨r, Fintype.card (Module.Free.ChooseBasisIndex (Localization.AtPrime p)
    (LocalizedModule p.primeCompl M)), fun h0 => hr (h0 ▸ p.zero_mem),
    ⟨b'.reindex (Fintype.equivFin _)⟩⟩

end Algebra


/-! ### Sections over affine charts as base changes -/

section Chart

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Over a morphism of affine charts the sections of a module cartesian on affine charts are
the base change of the sections over the target**, with restriction of sections as the
structure map.  This is the bijectivity of `AlgebraicGeometry.Space.sectionsBaseChange` read as
`IsBaseChange`. -/
theorem isBaseChange_chartRestrictLinear {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {U V : SmallEtale B S hS F}
    (hU : IsAffine (chartScheme U)) (hV : IsAffine (chartScheme V)) (f : V ⟶ U) :
    letI := chartAlgebra (hF := hF) f
    letI := chartSectionsModule G f
    haveI := chartSections_isScalarTower G f
    IsBaseChange (chartRing B S hS F hF V) (chartRestrictLinear G f) := by
  let := chartAlgebra (hF := hF) f
  let := chartSectionsModule G f
  have := chartSections_isScalarTower G f
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective (sectionsBaseChange G f) (hG U V hU hV f))
    fun x => chartBaseChange_one_tmul G f x

/-- **A basis of the sections over an affine chart restricts to a basis of the sections over
every affine chart above it**, for a module cartesian on affine charts. -/
theorem exists_basis_restrict {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {hF : IsAlgebraicSpace B S hS F} (G : Modules.{u, u} B S hS F hF)
    (hG : IsCartesianOnAffineCharts G) {U V : SmallEtale B S hS F}
    (hU : IsAffine (chartScheme U)) (hV : IsAffine (chartScheme V)) (f : V ⟶ U) {ι : Type*}
    (b : Module.Basis ι (chartRing B S hS F hF U) (G.val.obj (op U))) :
    ∃ b' : Module.Basis ι (chartRing B S hS F hF V) (G.val.obj (op V)),
      ∀ i, b' i = G.val.map f.op (b i) := by
  let := chartAlgebra (hF := hF) f
  let := chartSectionsModule G f
  have := chartSections_isScalarTower G f
  have h := isBaseChange_chartRestrictLinear G hG hU hV f
  exact ⟨h.basis b, h.basis_apply b⟩

variable (B S hS) (X : AlgebraicSpaces B S hS)

/-- The scheme of every étale chart of a locally Noetherian algebraic space is locally
Noetherian. -/
theorem isLocallyNoetherian_chartScheme
    (hN : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsLocallyNoetherian Y))
    (V : SmallEtale B S hS X.1) : IsLocallyNoetherian (chartScheme V) :=
  (exists_atlas_iff_forall_etale B S hS X.1 (fun Y : Scheme.{u} => IsLocallyNoetherian Y)
    X.2).mp hN V.obj.left V.obj.hom V.property

/-- **A Noetherian algebraic space with a point has an affine open immersion chart with a
point.**  The space is quasi-separated, hence Zariski locally quasi-separated, hence decent, so
its schematic locus is a dense open subspace which is a scheme by [Stacks, Tag 06NH] — dense in
a nonempty space, so nonempty — and an affine open of that scheme around one of its points is
the chart. -/
theorem exists_isOpenImmersion_isAffine_chart (hZt : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZt X.1) (x : points B S hS X.1) :
    ∃ C : SmallEtale B S hS X.1, IsOpenImmersion B S hS C.1.hom ∧
      IsAffine (chartScheme C) ∧ Nonempty (chartScheme C) := by
  have hqs := isZariskiLocallyQuasiSeparatedOver_of_quasiSeparated B S hS hZt X.1 X.2 hN.2.1
  have hdec := isDecentSpace_of_isZariskiLocallyQuasiSeparatedOver B S hS hZt X.1 X.2 hqs
  obtain ⟨H, hHopen, hHrep, hHdense⟩ :=
    exists_denseRange_isRepresentable_isOpenSubspace_of_isDecentSpace B S hS X.2 hdec
  obtain ⟨w⟩ : Nonempty (points B S hS H.toFunctor) := hHdense.nonempty_iff.mpr ⟨x⟩
  let e := H.toFunctor.reprW
  let q : yoneda.obj H.toFunctor.reprX ⟶ X.1 := e.hom ≫ H.ι
  have hq : IsOpenImmersion B S hS q :=
    MorphismProperty.RespectsIso.precomp _ e.hom H.ι hHopen.2
  let C₀ : SmallEtale B S hS X.1 :=
    ⟨CostructuredArrow.mk q, presheaf_etale_of_isOpenImmersion B S hS hq⟩
  let y : chartScheme C₀ :=
    pointsToScheme B S hS H.toFunctor.reprX (pointsMap B S hS H.toFunctor e.inv w)
  obtain ⟨O, hO, hyO, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ y)
  exact ⟨openChart B S hS X.1 C₀ O, isOpenImmersion_openChart C₀ hq O, hO, ⟨⟨y, hyO⟩⟩⟩

/-- **The generic trivialization of a coherent module.**  On a Noetherian, étale-locally
reduced algebraic space with a point, a coherent module `G` has an affine open immersion chart
`C` with a point over which the sections `G(C)` are a free `𝒪_X(C)`-module of finite rank.

Start from an affine open immersion chart `C₀` with a point,
`AlgebraicGeometry.Space.exists_isOpenImmersion_isAffine_chart`.  Its ring of functions `A` is
nontrivial, reduced and Noetherian, and `G(C₀)` is a finite `A`-module because `G` is coherent;
`AlgebraicGeometry.Space.exists_ne_zero_basis_localizedModule_away` gives `r ≠ 0` with
`G(C₀)_r` free of finite rank.  The basic-open chart of `r` is again an affine open immersion
chart, it has a point because a nonzero function on a reduced scheme has a nonempty basic open,
its ring is `A_r` and the sections of `G` over it are `G(C₀)_r`, because a coherent module is
cartesian on affine charts. -/
theorem exists_isOpenImmersion_isAffine_chart_basis (hZt : B.Contains (⊤_ Scheme.{u}))
    (hN : IsNoetherian B S hS hZt X.1)
    (hred : HasEtaleLocalProperty B S hS X.1 (fun Y : Scheme.{u} => IsReduced Y))
    (x : points B S hS X.1) (G : Modules.{u, u} B S hS X.1 X.2)
    (hG : IsCoherent B S hS X.1 X.2 G) :
    ∃ C : SmallEtale B S hS X.1, IsOpenImmersion B S hS C.1.hom ∧
      IsAffine (chartScheme C) ∧ Nonempty (chartScheme C) ∧
      ∃ n : ℕ, Nonempty (Module.Basis (Fin n) (chartRing B S hS X.1 X.2 C) (G.val.obj (op C))) := by
  obtain ⟨C₀, hC₀, hC₀aff, ⟨c⟩⟩ := exists_isOpenImmersion_isAffine_chart B S hS X hZt hN x
  have hGcart : IsCartesianOnAffineCharts G :=
    isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X.1 X.2 G
      hG.toIsQuasicoherentOnSite
  have _ : IsReduced (chartScheme C₀) := isReduced_chartScheme B S hS X hred C₀
  have _ : IsLocallyNoetherian (chartScheme C₀) :=
    isLocallyNoetherian_chartScheme B S hS X hN.2.2 C₀
  have hnt : Nontrivial (chartRing B S hS X.1 X.2 C₀) :=
    ⟨⟨1, 0, one_ne_zero_structureRingSheaf_obj B S hS C₀ c⟩⟩
  have hredR : _root_.IsReduced (chartRing B S hS X.1 X.2 C₀) :=
    inferInstanceAs (_root_.IsReduced Γ(chartScheme C₀, ⊤))
  have hnoeth : IsNoetherianRing (chartRing B S hS X.1 X.2 C₀) :=
    IsLocallyNoetherian.component_noetherian (X := chartScheme C₀)
      ⟨⊤, isAffineOpen_top (chartScheme C₀)⟩
  have hfin : Module.Finite (chartRing B S hS X.1 X.2 C₀) (G.val.obj (op C₀)) :=
    moduleFinite_sections_of_isCoherent B S hS X.1 X.2 G hG hC₀aff
  obtain ⟨r, n, hr, ⟨b⟩⟩ :=
    exists_ne_zero_basis_localizedModule_away (chartRing B S hS X.1 X.2 C₀) (G.val.obj (op C₀))
  set O : (chartScheme C₀).Opens := (chartScheme C₀).basicOpen r
  let C := openChart B S hS X.1 C₀ O
  let ι := openChartInclusion B S hS X.1 C₀ O
  let := chartAlgebra (hF := X.2) ι
  let := chartSectionsModule G ι
  have := chartSections_isScalarTower G ι
  have := isLocalization_away_chartRing_openChart_basicOpen B S hS X.2 C₀ hC₀aff r
  have := isLocalizedModule_chartRestrictLinear_openChart_basicOpen B S hS X.2 G hGcart
    C₀ hC₀aff r
  obtain ⟨b'⟩ := nonempty_basis_of_isLocalizedModule_away
    (R' := chartRing B S hS X.1 X.2 C) r (chartRestrictLinear G ι) b
  obtain ⟨y, hy⟩ := nonempty_basicOpen_of_ne_zero (chartScheme C₀) (r := r) hr
  exact ⟨C, isOpenImmersion_openChart C₀ hC₀ O,
    isAffine_chartScheme_openChart_basicOpen B S hS X.1 C₀ hC₀aff r, ⟨⟨y, hy⟩⟩, n, ⟨b'⟩⟩

end Chart

end AlgebraicGeometry.Space

end
