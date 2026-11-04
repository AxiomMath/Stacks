module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Affine
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.Scheme
public import StacksFrontier.AlgebraicGeometry.ProperFiniteness.GlobalSectionsFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.DominantGenericPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationSpaceConstruction
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularAlterationImpliedProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoveringProperSurjective

/-!
# Finiteness of the normalization of an algebraic space carrying a regular alteration

The normalization of an integral algebraic space over `S` which is quasi-compact and locally
Noetherian and which admits an alteration whose source is regular is finite over it. This is one
of the two assertions of Stacks 0BHT; the other, that such an algebraic space has a dense regular
open, is `AlgebraicGeometry.Space.exists_isDenseOpenSubspace_hasEtaleLocalProperty_isRegular` in
`StacksFrontier.AlgebraicGeometry.Spaces.RegularAlterationImpliedProperties`. The scheme-level
counterpart is `AlgebraicGeometry.normalization_isFinite_of_regular_alteration`, the
corresponding assertion of Stacks 0BGG.

## Main results

* `AlgebraicGeometry.Space.localRingDimension_eq_zero_of_isDominant_of_isIntegralSpace`: a
  dominant morphism of integral algebraic spaces over `S` carries points of codimension zero to
  points of codimension zero.
* `AlgebraicGeometry.module_finite_integralClosure_of_isFinite_normalization`: the integral
  closure of a ring presenting a reduced scheme is a finite module over it as soon as the
  normalization morphism of that scheme is finite.
* `AlgebraicGeometry.Space.NormalizationData.isFinite_normalization_chart_of_regular_alteration`:
  the normalization morphism of an *affine* surjective étale scheme chart of the target is a
  finite morphism of schemes.
* `AlgebraicGeometry.Space.NormalizationData.isFinite_pullback_snd_of_regular_alteration`: the
  base change of the normalization morphism along an *affine* surjective étale scheme chart of
  the target is finite.
* `Space.NormalizationData.isFinite_hom_of_regular_alteration_of_isQuasiCompactSpace`: the
  normalization morphism of an arbitrary normalization datum of the target is finite.
* `AlgebraicGeometry.Space.isFinite_normalization_of_regular_alteration`: **Stacks 0BHT**, the
  assertion that the normalization morphism is finite, for *the* normalization.

## Implementation notes

**The shape of the statement.** Regularity of an algebraic space is the étale-local scheme
property `AlgebraicGeometry.IsRegular` of Stacks 03E6, written out as
`AlgebraicGeometry.Space.HasEtaleLocalProperty`, as it is in Stacks 0BGT
(`AlgebraicGeometry.Space.isNormal_of_isRegular`). The normalization is an arbitrary
`AlgebraicGeometry.Space.NormalizationData`, as it is throughout this directory; such data exists
by Stacks 07U4 and is unique up to isomorphism, so the results about it are stated for an
arbitrary one. The source's hypothesis that `Y` be Noetherian enters only as quasi-compactness of
`|Y|` and local Noetherianity of its étale scheme charts; the quasi-separatedness that
Stacks 03EA also asks for is unused, which strengthens the statement.

**The argument, and where it departs from the source.** The source reduces by étale localization
to `Y = Spec(A)` with `A` a Noetherian *domain*, takes `C = Γ(X, 𝒪_X)`, and concludes from
finiteness of `C` over `A` — Stacks 08AR for the proper `X ⟶ Spec(A)` — and normality of `C`
(Stacks 0BH3 applied to the normal `X`) that the integral closure of `A` in its fraction field
sits inside `C` and is therefore finite. Neither step is available here. The reduction is invalid
for algebraic spaces, an étale scheme chart of an integral algebraic space being reduced and
decent but not irreducible, the number of branches at a point being an étale-local invariant; and
Stacks 08AR is not in this library, nor can its higher direct images even be written at the
universe at which the cohomology of an algebraic space lives, as the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.ProperCohomologyFinite` record.

Both obstructions are avoided by passing to a *scheme* over the chart. Let `U` be an affine
surjective étale scheme chart of `Y` and write `A = Γ(U, 𝒪)`, a reduced Noetherian ring which
need not be a domain. Chow's lemma for algebraic spaces, Stacks 089J
(`AlgebraicGeometry.Space.hasChowSchemeCover_of_isSeparated_isFiniteType`, read over the affine
chart as
`AlgebraicGeometry.Space.exists_properSurjective_schemeCover_of_isProper_toAffine`) applied to
the base change `X ×_Y U ⟶ U` — which is proper by Stacks 04WP and surjective by Stacks 03MH,
`f` being proper and dominant hence surjective — produces an object `V` of the site, that is a
scheme, with `V ⟶ X ×_Y U` proper and surjective. The composite `p : V ⟶ U` is then a proper
surjection of *schemes*, so `Γ(V, 𝒪)` is a finite `A`-module by the degree-zero case of
Stacks 02O6 for schemes, `AlgebraicGeometry.finiteGlobalSectionsOfProper`, and `A ⟶ Γ(V, 𝒪)` is
injective because `p` is dominant and `U` is reduced.

Normality of `Γ(X, 𝒪_X)` is not needed either. What the source uses it for is to place the
integral closure `D` of `A` in its total ring of fractions inside `C`, and that placement is
supplied instead by the universal property of the normalization: `X` is regular, hence normal by
Stacks 0BGT, and `f` carries codimension-zero points to codimension-zero points (both spaces
being integral, this is Stacks 0ABL for the unique generic point), so `f` factors through the
normalization by part (4) of Stacks 0BB4. Base-changing that factorization to `U` and composing
with the Chow cover gives `V ⟶ U^ν` over `U`, where `U^ν` is the normalization of the scheme `U`
by the chart condition of the normalization data; `U` being affine, Stacks 035P
(`AlgebraicGeometry.preimageNormalizationIsoSpecIntegralClosure`) identifies `U^ν` with
`Spec(D)`, so the factorization is an `A`-algebra map `D ⟶ Γ(V, 𝒪)`. Any `A`-algebra map from an
`A`-subalgebra of the total ring of fractions of `A` into an `A`-algebra with injective structure
map is injective, so `D` is a submodule of a finite module over the Noetherian `A` and hence
finite; `Spec(D) ⟶ Spec(A)` is therefore finite, and that is the normalization morphism of `U`.

Finiteness of the normalization morphism of `Y` itself then follows because finiteness of a
morphism of algebraic spaces is étale local on the target, condition (3) of Stacks 03ZQ.

## References

* [Stacks Project, Tag 0BHT](https://stacks.math.columbia.edu/tag/0BHT)
* [Stacks Project, Tag 0BGG](https://stacks.math.columbia.edu/tag/0BGG)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 0ABL](https://stacks.math.columbia.edu/tag/0ABL)
* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 035N](https://stacks.math.columbia.edu/tag/035N)
* [Stacks Project, Tag 035P](https://stacks.math.columbia.edu/tag/035P)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 0BB4](https://stacks.math.columbia.edu/tag/0BB4)
* [Stacks Project, Tag 0BGT](https://stacks.math.columbia.edu/tag/0BGT)
* [Stacks Project, Tag 07U4](https://stacks.math.columbia.edu/tag/07U4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The integral closure in the total ring of fractions, as a submodule -/

/-- An `A`-algebra map from an `A`-subalgebra of the total ring of fractions of `A` is injective
as soon as the structure map of its target is. -/
private theorem injective_of_injective_algebraMap_of_subalgebra_fractionRing
    {A C : Type*} [CommRing A] [CommRing C] [Algebra A C]
    (D : Subalgebra A (FractionRing A)) (g : D →ₐ[A] C)
    (h : Function.Injective (algebraMap A C)) : Function.Injective g := by
  apply (injective_iff_map_eq_zero g).mpr
  intro b hb
  obtain ⟨⟨a, s⟩, heq⟩ := IsLocalization.surj (nonZeroDivisors A) b.val
  have hden : b * algebraMap A D s.val = algebraMap A D a := Subtype.ext heq
  have ha : a = 0 := h (by simpa [hb] using (congrArg g hden).symm)
  apply Subtype.ext
  have hs := IsLocalization.map_units (FractionRing A) s
  apply hs.mul_right_cancel
  simpa [ha] using heq

/-- The integral closure of a Noetherian ring `A` in its total ring of fractions is a finite
`A`-module as soon as it admits an `A`-algebra map to a finite `A`-algebra whose structure map is
injective.

No hypothesis is placed on the target beyond finiteness and injectivity of its structure map; in
particular it need not be a domain, nor integrally closed. -/
private theorem module_finite_integralClosure_of_algHom
    {A C : Type*} [CommRing A] [CommRing C] [IsNoetherianRing A]
    [Algebra A C] [Module.Finite A C]
    (g : integralClosure A (FractionRing A) →ₐ[A] C)
    (h : Function.Injective (algebraMap A C)) :
    Module.Finite A (integralClosure A (FractionRing A)) :=
  Module.Finite.of_injective g.toLinearMap
    (injective_of_injective_algebraMap_of_subalgebra_fractionRing _ g h)

/-! ### The normalization of an affine scheme -/

/-- The inclusion of the preimage of `⊤` under the normalization morphism is an isomorphism. -/
private theorem isIso_ι_normalization_top {U : Scheme.{u}} [IsReduced U]
    (hU : ∀ V : U.Opens, IsCompact (V : Set U) → (irreducibleComponents V).Finite) :
    IsIso (U.normalization hU ⁻¹ᵁ (⊤ : U.Opens)).ι := by
  have ht : U.normalization hU ⁻¹ᵁ (⊤ : U.Opens) = ⊤ := by simp
  rw [ht]
  change IsIso (U.normalizationScheme hU).topIso.hom
  infer_instance

/-- **Stacks 035P over the whole of an affine scheme.** The normalization scheme of a reduced
scheme `U` presented as `Spec A` is the spectrum of the integral closure of `A` in its total ring
of fractions. -/
private def normalizationSchemeIsoSpecIntegralClosure {U : Scheme.{u}} [IsReduced U]
    (hU : ∀ V : U.Opens, IsCompact (V : Set U) → (irreducibleComponents V).Finite)
    {A : Type u} [CommRing A] (e : Spec (.of A) ≅ U) :
    U.normalizationScheme hU ≅ Spec (.of (integralClosure A (FractionRing A))) := by
  have _ := isIso_ι_normalization_top hU
  exact (asIso (U.normalization hU ⁻¹ᵁ (⊤ : U.Opens)).ι).symm ≪≫
    preimageNormalizationIsoSpecIntegralClosure hU (⊤ : U.Opens) (e ≪≫ U.topIso.symm)

/-- Under the identification of `AlgebraicGeometry.normalizationSchemeIsoSpecIntegralClosure`
the normalization morphism of a reduced scheme presented as `Spec A` is the spectrum map of the
inclusion of `A` into its integral closure. -/
private theorem normalizationSchemeIsoSpecIntegralClosure_hom_comp {U : Scheme.{u}} [IsReduced U]
    (hU : ∀ V : U.Opens, IsCompact (V : Set U) → (irreducibleComponents V).Finite)
    {A : Type u} [CommRing A] (e : Spec (.of A) ≅ U) :
    (normalizationSchemeIsoSpecIntegralClosure hU e).hom ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap A (integralClosure A (FractionRing A)))) =
      U.normalization hU ≫ e.inv := by
  have _ := isIso_ι_normalization_top hU
  have h := preimageNormalizationIsoSpecIntegralClosure_hom_comp hU (⊤ : U.Opens)
    (e ≪≫ U.topIso.symm)
  simp only [normalizationSchemeIsoSpecIntegralClosure, Iso.trans_hom, Iso.symm_hom, asIso_inv]
  rw [Category.assoc, h]
  simp only [Iso.trans_inv, Iso.symm_inv]
  change inv (U.normalization hU ⁻¹ᵁ (⊤ : U.Opens)).ι ≫
    (U.normalization hU ∣_ (⊤ : U.Opens)) ≫ (⊤ : U.Opens).ι ≫ e.inv = _
  rw [morphismRestrict_ι_assoc]
  simp

/-- The normalization morphism of a reduced scheme presented as `Spec A` is finite if and only if
the integral closure of `A` in its total ring of fractions is a finite `A`-module. -/
private theorem isFinite_normalization_iff_module_finite_integralClosure
    {U : Scheme.{u}} [IsReduced U]
    (hU : ∀ V : U.Opens, IsCompact (V : Set U) → (irreducibleComponents V).Finite)
    {A : Type u} [CommRing A] (e : Spec (.of A) ≅ U) :
    IsFinite (U.normalization hU) ↔ Module.Finite A (integralClosure A (FractionRing A)) := by
  have _hri : MorphismProperty.RespectsIso (@IsFinite.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact (MorphismProperty.arrow_mk_iso_iff (@IsFinite.{u} : MorphismProperty Scheme.{u})
    (CategoryTheory.Arrow.isoMk (normalizationSchemeIsoSpecIntegralClosure hU e) e.symm
      (normalizationSchemeIsoSpecIntegralClosure_hom_comp hU e))).trans
    ((IsFinite.SpecMap_iff _).trans RingHom.finite_algebraMap)

/-- **The integral closure of a ring presenting a reduced scheme is a finite module over it as
soon as the normalization morphism of that scheme is finite.** Let `U` be a reduced scheme with
an isomorphism `Spec A ≅ U` and suppose the normalization morphism of `U` is a finite morphism of
schemes. Then the integral closure of `A` in its total ring of fractions is a finite `A`-module. -/
theorem module_finite_integralClosure_of_isFinite_normalization {U : Scheme.{u}} [IsReduced U]
    (hU : ∀ V : U.Opens, IsCompact (V : Set U) → (irreducibleComponents V).Finite)
    {A : Type u} [CommRing A] (e : Spec (.of A) ≅ U)
    (h : IsFinite (U.normalization hU)) :
    Module.Finite A (integralClosure A (FractionRing A)) :=
  (isFinite_normalization_iff_module_finite_integralClosure hU e).mp h

/-- **The normalization of a reduced affine locally Noetherian scheme which is properly and
surjectively dominated by a scheme over its normalization is finite.** Let `U` be such a scheme,
let `p : W ⟶ U` be proper and surjective and suppose `p` factors through the normalization
morphism of `U`. Then that normalization morphism is finite.

Neither `U` nor `W` is assumed irreducible. -/
private theorem isFinite_normalization_of_proper_factorization
    {U W : Scheme.{u}} [IsAffine U] [IsReduced U] [IsLocallyNoetherian U]
    (hU : ∀ V : U.Opens, IsCompact (V : Set U) → (irreducibleComponents V).Finite)
    (p : W ⟶ U) [IsProper p] [Surjective p]
    (t : W ⟶ U.normalizationScheme hU)
    (ht : t ≫ U.normalization hU = p) :
    IsFinite (U.normalization hU) := by
  let A := Γ(U, ⊤)
  let C := Γ(W, ⊤)
  let Dcl := integralClosure A (FractionRing A)
  have hAnoeth : IsNoetherianRing A :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top U⟩
  let a : A →+* C := p.appTop.hom
  let _ : Algebra A C := a.toAlgebra
  let g₀ : W ⟶ Spec (.of A) := p ≫ U.isoSpec.hom
  have happ : ((Scheme.ΓSpecIso (.of A)).inv ≫ g₀.appTop) = p.appTop := by
    dsimp only [g₀]
    rw [Scheme.Hom.comp_appTop, Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    exact Iso.inv_hom_id_assoc _ _
  have hafin : a.Finite := by
    have h0 : (g₀.appTop.hom).Finite := finiteGlobalSectionsOfProper A hAnoeth g₀ inferInstance
    have hc : (((Scheme.ΓSpecIso (.of A)).inv ≫ g₀.appTop).hom).Finite :=
      h0.comp (RingHom.Finite.of_surjective ((Scheme.ΓSpecIso (.of A)).inv.hom)
        (fun x => ⟨(Scheme.ΓSpecIso (.of A)).hom.hom x, by simp⟩))
    rwa [happ] at hc
  have _ : Module.Finite A C := hafin
  have _ : IsSchemeTheoreticallyDominant p := IsSchemeTheoreticallyDominant.of_isDominant p
  have hainj : Function.Injective a := p.app_injective ⊤
  let e := normalizationSchemeIsoSpecIntegralClosure hU U.isoSpec.symm
  let t' := t ≫ e.hom
  let j : CommRingCat.of A ⟶ CommRingCat.of Dcl := CommRingCat.ofHom (algebraMap A Dcl)
  have heq : t' ≫ Spec.map j = p ≫ U.isoSpec.hom := by
    dsimp only [t', j, e]
    rw [Category.assoc, normalizationSchemeIsoSpecIntegralClosure_hom_comp, ← Category.assoc, ht]
    rfl
  let c : CommRingCat.of Dcl ⟶ CommRingCat.of C := (Scheme.ΓSpecIso (.of Dcl)).inv ≫ t'.appTop
  have hjc : j ≫ c = p.appTop := by
    dsimp only [c]
    rw [← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc,
      ← Scheme.Hom.comp_appTop, heq, Scheme.Hom.comp_appTop]
    change (Scheme.ΓSpecIso (.of A)).inv ≫ U.toSpecΓ.appTop ≫ p.appTop = p.appTop
    rw [Scheme.toSpecΓ_appTop]
    exact Iso.inv_hom_id_assoc _ _
  let gA : Dcl →ₐ[A] C :=
    { toRingHom := c.hom
      commutes' := fun x => ConcreteCategory.congr_hom hjc x }
  have hD : Module.Finite A Dcl := module_finite_integralClosure_of_algHom gA hainj
  exact (isFinite_normalization_iff_module_finite_integralClosure hU U.isoSpec.symm).mpr hD

namespace Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### Codimension-zero points under a dominant morphism of integral algebraic spaces -/

/-- **A dominant morphism of integral algebraic spaces over `S` carries points of codimension
zero to points of codimension zero.** -/
theorem localRingDimension_eq_zero_of_isDominant_of_isIntegralSpace
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hIntX : IsIntegralSpace B S hS X) (hIntY : IsIntegralSpace B S hS Y)
    (f : X ⟶ Y) (hdom : IsDominant B S hS f) (z : points B S hS X)
    (hz : localRingDimension B S hS z = 0) :
    localRingDimension B S hS (pointsMap B S hS X f z) = 0 := by
  have _ : IrreducibleSpace (points B S hS X) := hIntX.2.2
  have _ : IrreducibleSpace (points B S hS Y) := hIntY.2.2
  obtain ⟨_, _⟩ := stacksSober_iff_t0_and_quasiSober.mp
    (stacksSober_points_of_isDecentSpace B S hS hX hIntX.2.1)
  obtain ⟨_, _⟩ := stacksSober_iff_t0_and_quasiSober.mp
    (stacksSober_points_of_isDecentSpace B S hS hY hIntY.2.1)
  have hzgen : z ∈ genericPoints (points B S hS X) :=
    (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hX hIntX.2.1 z).2 hz
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hzgen
  have hmap : pointsMap B S hS X f z = genericPoint (points B S hS Y) :=
    pointsMap_eq_of_isGenericPoint B S hS hY hIntY.2.1 f hdom
      (hzgen ▸ genericPoint_spec (points B S hS X)) (genericPoint_spec (points B S hS Y))
  rw [hmap]
  exact (mem_genericPoints_iff_localRingDimension_eq_zero B S hS hY hIntY.2.1 _).1
    (by rw [genericPoints_eq_singleton]; rfl)

/-! ### Stacks 0BHT: finiteness of the normalization -/

/-- The base change of a proper dominant morphism of algebraic spaces is proper and surjective. -/
theorem isProper_and_isSurjective_pullback_snd_of_isDominant
    {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hXsp : IsAlgebraicSpace B S hS X)
    (hYsp : IsAlgebraicSpace B S hS Y) (hZsp : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y)
    (a : Z ⟶ Y) (hprop : IsProper B S hS f) (hdom : IsDominant B S hS f) :
    IsProper B S hS (pullback.snd f a) ∧ IsSurjective B S hS (pullback.snd f a) :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun ⦃V W : AlgebraicSpaces B S hS⦄ (m : V ⟶ W) => IsProper B S hS m.hom)
      (AlgebraicSpaces.isPullback_fiberProduct B S hS
        (ObjectProperty.homMk f : (⟨X, hXsp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hYsp⟩)
        (ObjectProperty.homMk a : (⟨Z, hZsp⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hYsp⟩))
      hprop,
    isSurjective_pullback_snd B S hS hXsp hYsp hZsp f a
      (isSurjective_of_isProper_of_isDominant B S hS hYsp f hprop hdom)⟩

/-- A property of the scheme map underlying `m`, read off the presheaf property of `yoneda.map m`
for its inverse image along `BigFppfOver.toScheme`. -/
theorem toScheme_map_of_presheaf_inverseImage {P : MorphismProperty Scheme.{u}}
    {V U : BigFppfOver B S hS} (m : V ⟶ U)
    (h : (P.inverseImage (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map m)) :
    P ((BigFppfOver.toScheme B S hS).map m) := by
  change (P.inverseImage (BigFppfOver.toScheme B S hS)).relative yoneda (yoneda.map m) at h
  exact (MorphismProperty.of_relative_map h :)

/-- **Stacks 0BHT read on an affine surjective étale scheme chart.** Let `f : X ⟶ Y` be an
alteration of algebraic spaces over `S` with `X` regular and the étale scheme charts of `Y`
locally Noetherian, let `D` be normalization data for `Y` and let `U` be an affine surjective
étale scheme chart of `Y`. Then the normalization morphism of the *scheme* `U` is finite.

The finiteness condition on the irreducible components of the chart is a hypothesis rather than
read off the normalization datum, so that a consumer with its own proof of it — the normalization
of a scheme being formed from one — gets the statement about that proof's normalization. -/
theorem NormalizationData.isFinite_normalization_chart_of_regular_alteration
    (f : X ⟶ Y) (hf : IsAlteration B S hS f)
    (hXreg : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T))
    (hYnoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (D : NormalizationData B S hS Y) {U : BigFppfOver B S hS}
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (a : yoneda.obj U ⟶ Y) (hasurj : IsSurjective B S hS a) (haet : IsEtale B S hS a)
    (hU : ∀ V : ((BigFppfOver.toScheme B S hS).obj U).Opens,
      IsCompact (V : Set ((BigFppfOver.toScheme B S hS).obj U)) →
        (irreducibleComponents V).Finite) :
    _root_.AlgebraicGeometry.IsFinite
      (Scheme.normalization ((BigFppfOver.toScheme B S hS).obj U) hU) := by
  classical
  let T := BigFppfOver.toScheme B S hS
  obtain ⟨hYsp, hIntY, hXsp, hIntX, hprop, hdom, -⟩ := hf
  have hUsp : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  have haetP := (isEtale_iff_presheaf_of_yoneda B S hS a).mp haet
  obtain ⟨hUfin, Uν, pν, gν, eν, hnormChart, hpbChart⟩ := D.chart U a hasurj haet
  have _ : IsAffine (T.obj U) := hUaff
  have _ : _root_.AlgebraicGeometry.IsReduced (T.obj U) :=
    (exists_atlas_iff_forall_etale B S hS Y
      (fun Z : Scheme.{u} => _root_.AlgebraicGeometry.IsReduced Z) hYsp).mp hIntY.1 U a haetP
  have _ : IsLocallyNoetherian (T.obj U) :=
    (exists_atlas_iff_forall_etale B S hS Y
      (fun Z : Scheme.{u} => IsLocallyNoetherian Z) hYsp).mp hYnoeth U a haetP
  obtain ⟨φ, hφ, -⟩ := D.existsUnique_lift_hom hYsp hXsp
    (isNormal_of_isRegular B S hS X hXreg) f
    (localRingDimension_eq_zero_of_isDominant_of_isIntegralSpace B S hS hXsp hYsp hIntX hIntY
      f hdom)
  have hQ := isAlgebraicSpace_pullback B S hS f a hXsp hUsp hYsp
  obtain ⟨hqProper, hqSurj⟩ :=
    isProper_and_isSurjective_pullback_snd_of_isDominant B S hS hXsp hYsp hUsp f a hprop hdom
  obtain ⟨V, ρ, hρProper, hρSurj⟩ :=
    exists_properSurjective_schemeCover_of_isProper_toAffine B S hS U hUaff hQ
      (pullback.snd f a) hqProper
  let m : V ⟶ U := yoneda.preimage (ρ ≫ pullback.snd f a)
  have hm : yoneda.map m = ρ ≫ pullback.snd f a := yoneda.map_preimage _
  have _ : _root_.AlgebraicGeometry.IsProper (T.map m) :=
    toScheme_map_of_presheaf_inverseImage B S hS (P := @_root_.AlgebraicGeometry.IsProper.{u})
      m (by
        rw [hm]
        exact (presheaf_isProper_iff B S hS (ρ ≫ pullback.snd f a)
          (isAlgebraicSpace_yoneda B S hS V) hUsp
          (by rw [← hm]; exact Functor.relativelyRepresentable.map yoneda m)).mp
          (isProper_comp B S hS (isAlgebraicSpace_yoneda B S hS V) hQ hUsp
            ρ (pullback.snd f a) hρProper hqProper))
  have _ : _root_.AlgebraicGeometry.Surjective (T.map m) :=
    toScheme_map_of_presheaf_inverseImage B S hS (P := @_root_.AlgebraicGeometry.Surjective.{u})
      m (by
        rw [hm]
        exact (presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj U) hUsp V
          (ρ ≫ pullback.snd f a)).mpr (isSurjective_comp B S hS hρSurj hqSurj))
  let k := hpbChart.lift (ρ ≫ pullback.fst f a ≫ φ) (ρ ≫ pullback.snd f a) <| by
    simp only [Category.assoc]
    rw [hφ, pullback.condition]
  have hk : k ≫ yoneda.map pν = ρ ≫ pullback.snd f a := hpbChart.lift_snd _ _ _
  let k' : V ⟶ Uν := yoneda.preimage k
  have hk' : k' ≫ pν = m := by
    apply yoneda.map_injective
    rw [Functor.map_comp, yoneda.map_preimage, hk, ← hm]
  exact isFinite_normalization_of_proper_factorization hUfin (T.map m)
    (T.map k' ≫ eν.hom) (by rw [Category.assoc, ← hnormChart, ← T.map_comp, hk'])

/-- **Stacks 0BHT along an affine surjective étale scheme chart.** Let `f : X ⟶ Y` be an
alteration of algebraic spaces over `S` with `X` regular and the étale scheme charts of `Y`
locally Noetherian, and let `D` be normalization data for `Y`. Then the base change of the
normalization morphism of `D` along any affine surjective étale scheme chart of `Y` is finite. -/
theorem NormalizationData.isFinite_pullback_snd_of_regular_alteration
    (f : X ⟶ Y) (hf : IsAlteration B S hS f)
    (hXreg : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T))
    (hYnoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (D : NormalizationData B S hS Y) {U : BigFppfOver B S hS}
    (hUaff : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (a : yoneda.obj U ⟶ Y) (hasurj : IsSurjective B S hS a) (haet : IsEtale B S hS a) :
    IsFinite B S hS (pullback.snd D.hom a) := by
  classical
  let T := BigFppfOver.toScheme B S hS
  have hYsp : IsAlgebraicSpace B S hS Y := hf.1
  have hUsp : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  obtain ⟨hUfin, Uν, pν, gν, eν, hnormChart, hpbChart⟩ := D.chart U a hasurj haet
  have hchart : _root_.AlgebraicGeometry.IsFinite
      (Scheme.normalization (T.obj U) hUfin) :=
    NormalizationData.isFinite_normalization_chart_of_regular_alteration B S hS f hf hXreg
      hYnoeth D hUaff a hasurj haet hUfin
  have hPull : IsAlgebraicSpace B S hS (pullback D.hom a) :=
    isAlgebraicSpace_pullback B S hS D.hom a D.isAlgebraicSpace hUsp hYsp
  have hpFinite : _root_.AlgebraicGeometry.IsFinite (T.map pν) := by
    rw [hnormChart]
    infer_instance
  have hrelq : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda (pullback.snd D.hom a) := by
    refine (((MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative yoneda).cancel_left_of_respectsIso
      hpbChart.isoPullback.hom (pullback.snd D.hom a)).mp ?_
    rw [hpbChart.isoPullback_hom_snd]
    exact relative_inverseImage_isFinite_yoneda_map pν hpFinite
  exact (isFinite_iff_representable B S hS (pullback.snd D.hom a) hPull hUsp).2
    ⟨hrelq.1, hrelq⟩

/-- **Finiteness of the normalization morphism of an arbitrary normalization datum.** Let `Y` be
an integral algebraic space over `S` which is quasi-compact and whose étale scheme charts are
locally Noetherian, let `f : X ⟶ Y` be an alteration with `X` regular, and let `D` be
normalization data for `Y`. Then the normalization morphism of `D` is finite.

This takes the normalization as a hypothesis, so the tag sits on
`AlgebraicGeometry.Space.isFinite_normalization_of_regular_alteration` below, which asserts it
of the normalization the library constructs. -/
theorem NormalizationData.isFinite_hom_of_regular_alteration_of_isQuasiCompactSpace
    (f : X ⟶ Y) (hf : IsAlteration B S hS f)
    (hXreg : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T))
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYnoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (D : NormalizationData B S hS Y) :
    IsFinite B S hS D.hom := by
  obtain ⟨U, a, hUaff, haSurjP, haet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS Y hf.1).mp hYqc
  have hasurj : IsSurjective B S hS a := isSurjective_of_presheafSurjective B S hS a haSurjP
  exact isFinite_of_surjectiveEtaleChart B S hS D.isAlgebraicSpace hf.1 D.hom hasurj haet
    (NormalizationData.isFinite_pullback_snd_of_regular_alteration B S hS f hf hXreg hYnoeth D
      hUaff a hasurj haet)

/-- **Stacks 0BHT, finiteness of the normalization.** Let `Y` be an integral algebraic space over
`S` which is quasi-compact and whose étale scheme charts are locally Noetherian, and suppose
there is an alteration `f : X ⟶ Y` with `X` regular. Then **the** normalization morphism
`Y^ν ⟶ Y` of `Y` is a finite morphism of algebraic spaces.

The normalization is the constructed one, neither assumed nor existentially quantified: the
étale scheme charts of `Y` are locally Noetherian, so they satisfy the finiteness condition of
Stacks 0BB1 by Stacks 0GMB, and `AlgebraicGeometry.Space.normalizationData` is then the
normalization of `Y`, unique up to a unique isomorphism over `Y` by
`AlgebraicGeometry.Space.NormalizationData.existsUnique_iso_hom`. -/
@[stacks 0BHT "finiteness of the normalization. The source's Noetherian hypothesis on Y is used \
only as quasi-compactness of its point space and local Noetherianity of its etale charts; the \
quasi-separatedness that Stacks 03EA also asks for is unused, which is a strengthening. \
Integrality of Y is part of IsAlteration. The source's Step 1 -- etale localization to a \
Noetherian domain, which charts of an integral space do not permit -- and its appeal to \
Stacks 08AR are both replaced by Chow's lemma for spaces (Stacks 089J) over an affine chart, \
which reduces the finiteness to the degree-zero case of Stacks 02O6 for schemes; see the module \
docstring"]
theorem isFinite_normalization_of_regular_alteration
    (f : X ⟶ Y) (hf : IsAlteration B S hS f)
    (hXreg : HasEtaleLocalProperty B S hS X (fun T : Scheme.{u} => IsRegular T))
    (hYqc : IsQuasiCompactSpace B S hS Y)
    (hYnoeth : HasEtaleLocalProperty B S hS Y (fun T : Scheme.{u} => IsLocallyNoetherian T)) :
    IsFinite B S hS (normalizationData B S hS hf.1
      (hasLocallyFiniteIrreducibleComponents_of_isLocallyNoetherian B S hS Y hf.1 hYnoeth)).hom :=
  NormalizationData.isFinite_hom_of_regular_alteration_of_isQuasiCompactSpace B S hS f hf hXreg
    hYqc hYnoeth _

end Space

end AlgebraicGeometry

end
