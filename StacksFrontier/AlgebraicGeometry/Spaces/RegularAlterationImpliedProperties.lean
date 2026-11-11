module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.Purity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Japanese
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.Regular
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralAlteration
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpaceProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.GenericFlatness
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.Normal
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleOpenImmersion

/-!
# Implied properties of an algebraic space carrying a regular alteration

An integral algebraic space over `S` which admits an alteration whose source is regular has a
dense open subspace which is regular, and its normalization is finite over it. These are the two
assertions of Stacks 0BHT, and the algebraic-space forms of
`AlgebraicGeometry.exists_dense_open_isRegular` and
`AlgebraicGeometry.normalization_isFinite_of_regular_alteration`, the two assertions of
Stacks 0BGG for schemes.

## Main results

* `AlgebraicGeometry.Space.exists_isDenseOpenSubspace_hasEtaleLocalProperty_isRegular` is the
  dense regular open subspace, the assertion of Stacks 0BHT that `Y` has a regular dense open.
* `AlgebraicGeometry.Space.NormalizationData.isFinite_hom_of_regular_alteration` is the source's
  argument for finiteness of the normalization, for a target represented by an affine object of
  the site and given that the global functions of `X` are finite over it.

Stacks 0BHT itself, with both assertions, is
`AlgebraicGeometry.Space.isFinite_normalization_and_exists_isDenseOpenSubspace_isRegular` in
`StacksFrontier.AlgebraicGeometry.Spaces.NoetherianRegularAlteration`, whose finiteness assertion,
`AlgebraicGeometry.Space.isFinite_normalization_of_regular_alteration`, is proved by a different
argument, through Chow's lemma over an affine chart.

## Implementation notes

Regularity of an algebraic space is the étale-local scheme property
`AlgebraicGeometry.IsRegular` of Stacks 03E6, written out as
`AlgebraicGeometry.Space.HasEtaleLocalProperty`, as it is in Stacks 0BGT
(`AlgebraicGeometry.Space.isNormal_of_isRegular`); an open subspace is a subfunctor which is an
open subspace in the sense of Stacks 02YU, and density of it is density of the range of the map
it induces on points, which is `AlgebraicGeometry.Space.IsDenseOpenSubspace`.

**Two hypotheses of the source are unused.** The source assumes `Y` Noetherian; only
reducedness of `Y` is used here, and that is part of integrality. The source also uses the
nonempty open subspace over which an alteration is finite, in order to shrink it until the
morphism becomes flat; generic flatness is applied here to `f` itself, so that open subspace
plays no part and neither does the finiteness over it. Both omissions strengthen the statement.

The argument of the source is generic flatness followed by descent of regularity. Stacks 06QS,
`AlgebraicGeometry.Space.exists_dense_open_genericFlatness`, applied to `f` and to the structure
sheaf of `X` produces a dense open subspace `V ⊆ Y` over which `f` becomes flat and locally of
finite presentation; properness supplies the finite-type hypothesis it asks of `f`, and
reducedness of `Y` is the hypothesis it asks of the target. The base change `X ×_Y V ⟶ V` is
then surjective, because `f` is — a universally closed morphism is closed, and a closed
dominant morphism is surjective — and `X ×_Y V` is regular, being étale over `X` through the
base change of the open immersion `V ⟶ Y`. Stacks 06MK, the locally-of-finite-presentation form
of `AlgebraicGeometry.Space.hasEtaleLocalProperty_isRegular_of_isSurjective_of_isFlat`,
descends regularity from `X ×_Y V` to `V`. That descent is where the source cites Stacks 07NG,
regularity descending along a faithfully flat ring map: the engine of Stacks 06MK is
`IsRegularLocalRing.of_flat_of_isLocalHom` on the local rings of a square of étale charts, which
is the same content for the local rings the source's faithfully flat morphism induces.

The two conditions `AlgebraicGeometry.Space.IsQuasicoherentOnCharts` and
`AlgebraicGeometry.Space.IsFiniteTypeOnCharts` that Stacks 06QS asks of the module are proved
here for the structure sheaf, by transporting the corresponding scheme-level facts along
`AlgebraicGeometry.Space.restrictToChartSchemeUnitIso`: the restriction of the structure sheaf
of an algebraic space to an étale scheme chart is the structure sheaf of that chart.

### Finiteness of the normalization: why the target is representable and affine

**The source's Step 1 is not available.** It reduces finiteness of the normalization to the case
`Y = Spec A` with `A` a Noetherian *domain* by étale localization. That reduction is invalid for
algebraic spaces: an étale scheme chart of an integral algebraic space is reduced and decent but
need not be irreducible, the number of branches at a point being an étale-local invariant. The
step of the source that fails is the appeal to Stacks 0BH3,
`AlgebraicGeometry.Space.isNormalDomain_globalSections_of_isIntegralSpace`, which requires an
*integral* algebraic space: the base change of `X` to a reducible chart is regular, hence normal,
but not irreducible. Assuming instead that the chart is integral does not repair this, because
the base change of `X` along it is étale over `X` and so need not be irreducible either.

What is formalized is therefore the case the source reduces to, namely a target represented by an
affine object `Z` of the site whose scheme is integral and locally Noetherian — that is
`Y = Spec A` for a Noetherian domain `A` — in which the algebraic space Stacks 0BH3 is applied to
is `X` itself, which `AlgebraicGeometry.Space.IsAlteration` already makes integral. Confining a
clause of a tag to a representable algebraic space is the established shape in this chapter: see
`AlgebraicGeometry.Space.NormalizationData.isFinite_of_representable_of_isAnalyticallyUnramified`
for Stacks 0BHR. The general finiteness statement is proved by another route, which avoids both
the reduction and the input below, in
`AlgebraicGeometry.Space.isFinite_normalization_of_regular_alteration`.

**One input is a hypothesis**, `h02O6`: the degree-zero case of Stacks 02O6, equivalently
Stacks 08AR at `i = 0`, asserting that the ring of global regular functions on an algebraic
space proper over `Spec A` is a finite `A`-module. Stacks 08AR is
`AlgebraicGeometry.Space.isCoherent_higherDirectImage_of_isProper`; the passage from it to the
spelling of the hypothesis here is not made in this library. Its scheme
form is: `AlgebraicGeometry.FiniteGlobalSectionsOfProper` is proved by
`AlgebraicGeometry.finiteGlobalSectionsOfProper`, which is what makes the scheme analogue
`AlgebraicGeometry.normalization_isFinite_of_regular_alteration` unconditional — but that form
quantifies over schemes over `Spec A` and so does not apply to an algebraic space. The hypothesis
is phrased as
the existence of an injective finite ring map from `A` into the ring of global functions that
Stacks 0BH3 speaks about, which is the spelling the two compose at; injectivity is part of it
because this library has no global-sections functoriality for algebraic spaces at that spelling,
so the canonical pullback map — which the source makes injective by dominance of `f` — cannot be
named here. Phrasing the input existentially makes it weaker, hence the statement stronger, than
pinning that map would.

With `h02O6` in hand the source's Step 2 runs as written. `A = Γ(Z, ⊤)` is a Noetherian domain;
`X` is regular, hence normal by Stacks 0BGT (`AlgebraicGeometry.Space.isNormal_of_isRegular`),
hence its ring `C` of global regular functions is a normal domain by Stacks 0BH3; the integral
closure of `A` in its fraction field embeds into `C`, because `C` is integrally closed in its own
fraction field, and is therefore a finite `A`-module since `A` is Noetherian. Over the affine
`Z` the normalization morphism is the spectrum of that integral closure, by Stacks 035P
(`AlgebraicGeometry.preimageNormalizationIsoSpecIntegralClosure`), and the chart condition of the
normalization data identifies it with the normalization morphism of the space.

## References

* [Stacks Project, Tag 0BHT](https://stacks.math.columbia.edu/tag/0BHT)
* [Stacks Project, Tag 0BGG](https://stacks.math.columbia.edu/tag/0BGG)
* [Stacks Project, Tag 06QS](https://stacks.math.columbia.edu/tag/06QS)
* [Stacks Project, Tag 06MK](https://stacks.math.columbia.edu/tag/06MK)
* [Stacks Project, Tag 07NG](https://stacks.math.columbia.edu/tag/07NG)
* [Stacks Project, Tag 0ADA](https://stacks.math.columbia.edu/tag/0ADA)
* [Stacks Project, Tag 0BGT](https://stacks.math.columbia.edu/tag/0BGT)
* [Stacks Project, Tag 0BH3](https://stacks.math.columbia.edu/tag/0BH3)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 035P](https://stacks.math.columbia.edu/tag/035P)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

set_option synthInstance.maxHeartbeats 400000 in
-- `HasPullbacks` for presheaves on the big fppf site needs a deep instance search
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_RegularAlterationImpliedProperties :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_RegularAlterationImpliedProperties
    {P Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : P ⟶ R) (g : Q ⟶ R) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### The structure sheaf as a module which is quasi-coherent of finite type on charts -/

/-- The structure sheaf of an algebraic space over `S`, as a module over itself. -/
noncomputable abbrev unitModule (hX : IsAlgebraicSpace B S hS X) :
    Modules.{u, u} B S hS X hX :=
  SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))

/-- The structure sheaf of an algebraic space over `S` is quasi-coherent on every étale scheme
chart: its restriction to a chart is the structure sheaf of that chart, which is quasi-coherent
as a module on a scheme. -/
theorem isQuasicoherentOnCharts_unitModule (hX : IsAlgebraicSpace B S hS X) :
    IsQuasicoherentOnCharts B S hS hX (unitModule B S hS hX) := fun U =>
  ObjectProperty.prop_of_iso
    (SheafOfModules.isQuasicoherent (etaleChartScheme B S hS U).ringCatSheaf)
    (restrictToChartSchemeUnitIso B S hS X hX U).symm inferInstance

/-- The structure sheaf of an algebraic space over `S` is of finite type on every étale scheme
chart: its restriction to a chart is the structure sheaf of that chart, which is generated by
one global section. -/
theorem isFiniteTypeOnCharts_unitModule (hX : IsAlgebraicSpace B S hS X) :
    IsFiniteTypeOnCharts B S hS hX (unitModule B S hS hX) := fun U =>
  have := structureSheaf_isFiniteType (etaleChartScheme B S hS U)
  Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    (restrictToChartSchemeUnitIso B S hS X hX U).symm

/-! ### Surjectivity of a proper dominant morphism -/

/-- A proper dominant morphism of algebraic spaces over `S` is surjective: a universally closed
morphism is closed, so the range of the map it induces on points is closed, and a closed dense
subset is everything. -/
theorem isSurjective_of_isProper_of_isDominant (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hp : IsProper B S hS f) (hd : IsDominant B S hS f) : IsSurjective B S hS f :=
  Set.range_eq_univ.mp
    ((isClosed_of_universallyClosed B S hS hY f hp.2.2).isClosed_range.closure_eq.symm.trans
      hd.closure_range)

/-! ### Stacks 0BHT: a dense regular open subspace -/

/-- **The dense regular open of Stacks 0BHT.** An integral algebraic space `Y` over `S`
admitting an alteration `f : X ⟶ Y` whose source is regular has a dense open subspace which is
regular. No Noetherian hypothesis on `Y` is needed. Stacks 0BHT itself, with both of its
assertions, is
`AlgebraicGeometry.Space.isFinite_normalization_and_exists_isDenseOpenSubspace_isRegular`. -/
theorem exists_isDenseOpenSubspace_hasEtaleLocalProperty_isRegular (f : X ⟶ Y)
    (hf : IsAlteration B S hS f)
    (hXreg : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T)) :
    ∃ V : Subfunctor Y, IsDenseOpenSubspace B S hS hf.1 V ∧
      HasEtaleLocalProperty B S hS V.toFunctor (fun T : Scheme.{u} => IsRegular T) := by
  have hYsp : IsAlgebraicSpace B S hS Y := hf.1
  have hXsp : IsAlgebraicSpace B S hS X := hf.2.2.1
  have hprop : IsProper B S hS f := hf.2.2.2.2.1
  obtain ⟨V, hVdense, hVflat, hVfp, -, -⟩ :=
    exists_dense_open_genericFlatness B S hS hXsp hYsp hf.2.1.1 f hprop.2.1
      (unitModule B S hS hXsp) (isQuasicoherentOnCharts_unitModule B S hS hXsp)
      (isFiniteTypeOnCharts_unitModule B S hS hXsp)
  refine ⟨V, hVdense, ?_⟩
  have hVsp : IsAlgebraicSpace B S hS V.toFunctor := hVdense.1.1
  have hPull : IsAlgebraicSpace B S hS (pullback f V.ι) :=
    isAlgebraicSpace_pullback B S hS f V.ι hXsp hVsp hYsp
  have hsnd : IsSurjective B S hS (pullback.snd f V.ι) :=
    isSurjective_pullback_snd B S hS hXsp hYsp hVsp f V.ι
      (isSurjective_of_isProper_of_isDominant B S hS hYsp f hprop hf.2.2.2.2.2.1)
  have hfst : IsEtale B S hS (pullback.fst f V.ι) :=
    isEtale_pullback_fst B S hS hXsp hYsp hVsp f V.ι
      (isEtale_of_isOpenImmersion B S hS hVdense.1.2)
  have hPullReg : HasEtaleLocalProperty B S hS (pullback f V.ι)
      (fun T : Scheme.{u} => IsRegular T) :=
    (exists_atlas_iff_forall_etale B S hS (pullback f V.ι)
      (fun T : Scheme.{u} => IsRegular T) hPull).mpr fun W g hg =>
        (exists_atlas_iff_forall_etale B S hS X
          (fun T : Scheme.{u} => IsRegular T) hXsp).mp hXreg W
          (g ≫ pullback.fst f V.ι) (hfst W g hg)
  exact hasEtaleLocalProperty_isRegular_of_isSurjective_of_isFlat_of_isLocallyOfFinitePresentation
    B S hS hPull hVsp (pullback.snd f V.ι) hVfp hVflat hsnd hPullReg

/-! ### Stacks 0BHT: finiteness of the normalization over a representable affine target -/

/-- The integral closure of a Noetherian domain `A` in its fraction field is a finite `A`-module
as soon as `A` admits an injective finite extension by a domain integrally closed in its own
fraction field: the extension of fraction fields carries the integral closure into that
extension, `A`-linearly and injectively, and a submodule of a finite module over a Noetherian
ring is finite.

This repeats `AlgebraicGeometry.integralClosure_finite_of_finite_integrallyClosed`, which is
`private` to the `ImpliedProperties.FiniteNormalization` module of the resolution-of-surfaces
directory and therefore not available here, and relaxes its universe constraint: the ring of
global regular functions on an algebraic space does not live in the universe of its schemes. -/
private theorem module_finite_integralClosure_of_finite_isIntegrallyClosed
    (A : Type u) (C : Type v) [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing C] [IsDomain C] [Algebra A C] [IsScalarTower A C (FractionRing C)]
    [IsFractionRing C (FractionRing C)] [IsIntegrallyClosed C]
    (hAC : Function.Injective (algebraMap A C)) [Module.Finite A C] :
    Module.Finite A ↥(integralClosure A (FractionRing A)) := by
  classical
  let K := FractionRing A
  let L := FractionRing C
  have hAL : Function.Injective (algebraMap A L) :=
    (IsFractionRing.injective C L).comp hAC
  let e : K →+* L := IsFractionRing.lift hAL
  have heA : e.comp (algebraMap A K) = algebraMap A L := by
    ext a
    simp [e, K, L, IsFractionRing.lift_algebraMap]
  have he : Function.Injective e := RingHom.injective e
  let Bcl := integralClosure A K
  let eA : K →ₐ[A] L := { toRingHom := e, commutes' := fun a => by simp [e] }
  have hmemb (b : Bcl) : ∃ c : C, algebraMap C L c = e b.1 := by
    have hb : _root_.IsIntegral A (e b.1) := _root_.IsIntegral.map eA b.2
    exact (isIntegrallyClosed_iff L).mp (inferInstance : IsIntegrallyClosed C)
      (_root_.IsIntegral.tower_top hb)
  choose g hg using hmemb
  let ψ : Bcl →ₐ[A] C :=
    { toFun := g
      map_one' := IsFractionRing.injective C L (by simp [hg])
      map_mul' := fun x y => IsFractionRing.injective C L (by simp [hg])
      map_zero' := IsFractionRing.injective C L (by simp [hg])
      map_add' := fun x y => IsFractionRing.injective C L (by simp [hg])
      commutes' := fun a => IsFractionRing.injective C L (by
        rw [hg, ← IsScalarTower.algebraMap_apply A C L a]
        exact congrArg (fun φ : A →+* L => φ a) heA) }
  refine Module.Finite.of_injective ψ.toLinearMap fun x y hxy => Subtype.ext (he ?_)
  rw [← hg x, ← hg y]
  exact congrArg (algebraMap C L) hxy

/-- Finiteness of a morphism of schemes, packaged as a morphism property, satisfies the affine
criterion of finiteness of the ring map on sections. This is the local instance of
`StacksFrontier/AlgebraicGeometry/Morphisms/Normalization/Japanese.lean`, restated because it is not
exported. -/
local instance hasAffineProperty_finiteProp' :
    HasAffineProperty finiteProp.{u} (affineAnd RingHom.Finite) := by
  rw [HasAffineProperty.affineAnd_iff _ RingHom.finite_respectsIso
    RingHom.finite_localizationPreserves.away RingHom.finite_ofLocalizationSpan]
  intro X Y f
  simp [finiteProp, _root_.AlgebraicGeometry.isFinite_iff]

/-- A morphism of the big fppf site of `S` whose underlying morphism of schemes is finite is
representable with finite represented base changes, as a morphism of the presheaves it
represents. -/
private theorem relative_inverseImage_isFinite_yoneda_map' {Zν Z : BigFppfOver B S hS}
    (p : Zν ⟶ Z)
    (hp : _root_.AlgebraicGeometry.IsFinite ((BigFppfOver.toScheme B S hS).map p)) :
    (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda (yoneda.map p) := by
  have _ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    BigFppfOver.isStableUnderBaseChange_inverseImage B S hS
      (@_root_.AlgebraicGeometry.IsFinite.{u})
  exact MorphismProperty.relative_map hp

/-- **Finiteness of the normalization over a representable affine target, from finiteness of
global functions.** Let `Z` be an affine object of the site whose scheme is integral and locally
Noetherian, let `f : X ⟶ h_Z` be an alteration with `X` regular, suppose the ring of global
regular functions on `X` admits an injective finite ring map from `Γ(Z, ⊤)`, and let `D` be
normalization data for `h_Z`. Then the normalization morphism of `D` is finite.

This is the source's Step 2 run as written. The finiteness assertion of Stacks 0BHT holds without
the hypothesis on global functions, for any quasi-compact `Y` with locally Noetherian charts:
that is `AlgebraicGeometry.Space.isFinite_normalization_of_regular_alteration`. -/
theorem NormalizationData.isFinite_hom_of_regular_alteration {Z : BigFppfOver B S hS}
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    [_root_.AlgebraicGeometry.IsIntegral ((BigFppfOver.toScheme B S hS).obj Z)]
    [IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Z)]
    (f : X ⟶ yoneda.obj Z) (hf : IsAlteration B S hS f)
    (hXreg : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T))
    (h02O6 : ∃ φ : Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) →+*
        ↥(RingCat.sectionsSubring
          (structurePresheaf B S hS X ⋙ forget₂ CommRingCat.{u} RingCat.{u})),
      Function.Injective φ ∧ φ.Finite)
    (D : NormalizationData B S hS (yoneda.obj Z)) :
    IsFinite B S hS D.hom := by
  classical
  obtain ⟨hZfin, Zν, p, q, eν, hp, hpb⟩ := D.chart_self
  obtain ⟨φ, hφinj, hφfin⟩ := h02O6
  -- `A` is a Noetherian domain and `C` is a normal domain finite over it
  let : IsNormalDomain ↥(RingCat.sectionsSubring
      (structurePresheaf B S hS X ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :=
    isNormalDomain_globalSections_of_isIntegralSpace B S hS X hf.2.2.1 hf.2.2.2.1
      (isNormal_of_isRegular B S hS X hXreg)
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      ↥(RingCat.sectionsSubring
        (structurePresheaf B S hS X ⋙ forget₂ CommRingCat.{u} RingCat.{u})) := φ.toAlgebra
  let : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      ↥(RingCat.sectionsSubring
        (structurePresheaf B S hS X ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :=
    RingHom.finite_algebraMap.mp hφfin
  let : Nonempty ((⊤ : ((BigFppfOver.toScheme B S hS).obj Z).Opens)) :=
    ⟨⟨Classical.arbitrary ((BigFppfOver.toScheme B S hS).obj Z), by simp⟩⟩
  have hAnoeth : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) :=
    IsLocallyNoetherian.component_noetherian
      ⟨⊤, isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj Z)⟩
  let : IsDomain Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤) :=
    _root_.AlgebraicGeometry.IsIntegral.component_integral
      (⊤ : ((BigFppfOver.toScheme B S hS).obj Z).Opens)
  have hBfin : Module.Finite Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
      ↥(integralClosure Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
        (FractionRing Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤))) :=
    module_finite_integralClosure_of_finite_isIntegrallyClosed _ _ hφinj
  -- over the affine `Z` the normalization morphism is the spectrum of that integral closure
  let : IsReduced ((BigFppfOver.toScheme B S hS).obj Z) :=
    (_root_.AlgebraicGeometry.isIntegral_iff_irreducibleSpace_and_isReduced
      ((BigFppfOver.toScheme B S hS).obj Z)).mp inferInstance |>.2
  have hchart : _root_.AlgebraicGeometry.IsFinite
      (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj Z) hZfin) := by
    refine (IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := finiteProp.{u})
      (fun _ : Unit => (⊤ : ((BigFppfOver.toScheme B S hS).obj Z).Opens)) (by simp)).mpr
        fun _ => ?_
    have hSpec : _root_.AlgebraicGeometry.IsFinite (Spec.map (CommRingCat.ofHom
        (algebraMap Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
          (integralClosure Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)
            (FractionRing Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)))))) := by
      rw [_root_.AlgebraicGeometry.IsFinite.SpecMap_iff]
      exact RingHom.finite_algebraMap.mpr hBfin
    let eZ : Spec (.of Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)) ≅
        (⊤ : ((BigFppfOver.toScheme B S hS).obj Z).Opens).toScheme :=
      (isAffineOpen_top ((BigFppfOver.toScheme B S hS).obj Z)).isoSpec.symm
    have hcomm := preimageNormalizationIsoSpecIntegralClosure_hom_comp
      (X := (BigFppfOver.toScheme B S hS).obj Z) (hX := hZfin)
      (U := (⊤ : ((BigFppfOver.toScheme B S hS).obj Z).Opens)) (e := eZ)
    exact (MorphismProperty.arrow_mk_iso_iff finiteProp.{u}
      (CategoryTheory.Arrow.isoMk
        (preimageNormalizationIsoSpecIntegralClosure hZfin
          (⊤ : ((BigFppfOver.toScheme B S hS).obj Z).Opens) eZ) eZ.symm
        hcomm)).mpr hSpec
  -- and the chart condition identifies it with the normalization morphism of the space
  have hqiso : IsIso q := hpb.isIso_fst_of_isIso
  have hpFinite : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B S hS).map p) := by
    rw [hp]
    have _ : _root_.AlgebraicGeometry.IsFinite
      (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj Z) hZfin) := hchart
    infer_instance
  have hD : D.hom = inv q ≫ yoneda.map p := by
    rw [← cancel_epi q, IsIso.hom_inv_id_assoc]
    simpa only [Category.comp_id] using hpb.w
  have hrel := (((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda).cancel_left_of_respectsIso
      (inv q) (yoneda.map p)).mpr (relative_inverseImage_isFinite_yoneda_map' B S hS p hpFinite)
  rw [hD]
  exact (isFinite_iff_representable B S hS (inv q ≫ yoneda.map p) D.isAlgebraicSpace
    (isAlgebraicSpace_yoneda B S hS Z)).2 ⟨hrel.1, hrel⟩

end AlgebraicGeometry.Space

end
