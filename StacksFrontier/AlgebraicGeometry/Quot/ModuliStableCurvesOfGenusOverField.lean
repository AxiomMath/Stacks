module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.TerminalBaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilyCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.StableContraction.AmpleNoRationalBridge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.StalkEquivalence.FieldFiber
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.OverAField
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFamily.UniversalDirectImage
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesH01Inputs
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliSmoothCurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesOfGenus
public import StacksFrontier.Deformation.Examples.Geometric.CurvesDeformationComparison
public import StacksFrontier.Topology.Dimension.Krull
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The points of `𝓜̄_g`: stable curves of genus `g` over a field (Stacks 0E78, part (2))

Let `g ≥ 2` and let `X` be a proper scheme of dimension at most one over a field `k`. Part (2) of
Stacks 0E78 says that the following are equivalent:

* (a) the classifying morphism `Spec(k) → Curves` of `X` factors through `𝓜̄_g`;
* (b) `X` has at-worst-nodal singularities, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of `X` is
  `g`, and `X` has no rational tails and no rational bridges;
* (c) `X` has at-worst-nodal singularities, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of `X` is
  `g`, and the dualizing sheaf `ω_X` is ample.

Here `𝓜̄_g` is `AlgebraicGeometry.moduliStableCurvesOfGenus`, the substack of the families of
curves which are stable (Stacks 0E75) with every fibre of genus `g`.

## Main results

* `AlgebraicGeometry.isIso_appTop_pullback_snd_of_isIso_globalSections`: for a quasi-compact,
  quasi-separated scheme `X` over a field `k` with `k = H⁰(X, 𝒪_X)`, `Γ(T, 𝒪_T) = Γ(X_T, 𝒪)` for
  every scheme `T` over `k`, by flat base change ([Stacks, Tag 02KH]).
* `AlgebraicGeometry.hasUniversallyBijectiveGlobalFunctions_curveFamilyOfScheme_iff`: the family
  of curves of a proper scheme `X` over `k` has `f_*𝒪_X = 𝒪_S` universally exactly when
  `k = H⁰(X, 𝒪_X)`.
* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_iff_of_field`: a nonempty scheme locally
  of finite presentation over `k` is at-worst-nodal of relative dimension one over `k` exactly when
  it is equidimensional of dimension one with at-worst-nodal singularities ([Stacks, Tag 0C59]).
* `AlgebraicGeometry.isPrestableCurveFamily_curveFamilyOfScheme_iff`: the family of curves of `X`
  is prestable exactly when `X` is at-worst-nodal, of dimension one, with `k = H⁰(X, 𝒪_X)`.
* `AlgebraicGeometry.HasGenusTwoNoRationalTailNoRationalBridge.of_isPullback`: a nodal curve over
  `k` with `k = H⁰`, of genus at least two and without rational tails or bridges keeps these
  properties after any extension of the ground field.
* `AlgebraicGeometry.isStableCurveFamilyOfFibreGenus_curveFamilyOfScheme_iff`: the family of
  curves of `X` lies in `𝓜̄_g` exactly when condition (b) holds.
* `AlgebraicGeometry.factors_moduliStableCurvesOfGenus_over_field_iff`: **part (2) of
  Stacks 0E78**, the equivalence of (a), (b) and (c).

## Implementation notes

Condition `f_*𝒪_X = 𝒪_S` universally (`AlgebraicGeometry.HasUniversallyBijectiveGlobalFunctions`)
quantifies over all algebraic spaces over the base. For the family of a proper scheme `X` over
a field it is reduced to schemes `T` over `k`: the global functions of an algebraic space are the
compatible families of functions on all of its scheme charts, so bijectivity can be checked after
base change to every scheme
(`AlgebraicGeometry.Space.bijective_globalFunctionsMap_of_forall_schemeSpace`). For a scheme `T`
over `k` the morphism `T → Spec k` is flat, and degree-zero flat base change for the
quasi-compact, quasi-separated morphism `X → Spec k` gives `Γ(T, 𝒪_T) = Γ(X_T, 𝒪)`. No cohomology
and base change for algebraic spaces (Stacks 0E6B) is needed.

The fibre conditions of a stable family are imposed on every field-valued point of the base, on a
scheme presenting the fibre. Over `Spec k` such a fibre is a base change of `X` along a field
extension `K/k`. In one direction the conditions on `X` pass to `X_K`: the genus by
[Stacks, Tag 0BY9], and the absence of rational tails and bridges because, by
`AlgebraicGeometry.forall_not_isRationalTail_and_isRationalBridge_iff_isAmple`, it is ampleness of
the dualizing sheaf, which is pulled back along `X_K → X` ([Stacks, Tag 0E32]). In the other
direction the fibre over the identity point `Spec k → Spec k` is a scheme `V` isomorphic to `X`
over `k`, and `X` is in turn the base change of `V` along the identity of `k`, so the same
transfer applies with the roles exchanged.

The statement takes `2 ≤ g`: the source names `𝓜̄_g` only for `g ≥ 2`, and for `g ≤ 1` the
substack is empty while condition (b) can hold (a smooth curve of genus one has no rational tails
or bridges).

## References

* [Stacks Project, Tag 0E78](https://stacks.math.columbia.edu/tag/0E78)
* [Stacks Project, Tag 0E77](https://stacks.math.columbia.edu/tag/0E77)
* [Stacks Project, Tag 0E76](https://stacks.math.columbia.edu/tag/0E76)
* [Stacks Project, Tag 0E75](https://stacks.math.columbia.edu/tag/0E75)
* [Stacks Project, Tag 0E6T](https://stacks.math.columbia.edu/tag/0E6T)
* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 0E32](https://stacks.math.columbia.edu/tag/0E32)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-! ### Global functions of a proper scheme over a field after base change -/

/-- **`Γ(T, 𝒪_T) = Γ(X_T, 𝒪)` for a scheme over a field with only constant functions.** Let `X`
be quasi-compact and quasi-separated over a field `k` with `k = H⁰(X, 𝒪_X)`. For every morphism
`t : T ⟶ Spec k` the projection `X ×_k T ⟶ T` induces an isomorphism on global functions:
`𝒪_{Spec k} ⟶ f_*𝒪_X` is an isomorphism, and it stays one after the flat base change `t`
([Stacks, Tag 02KH] in degree zero). -/
@[sga "3 VIB 12.2" "special case"]
theorem isIso_appTop_pullback_snd_of_isIso_globalSections (k : Type u) [Field k]
    {X T : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (hf : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)) (t : T ⟶ Spec (.of k)) :
    IsIso (pullback.snd f t).appTop := by
  have : IsIso f.appTop := IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv f.appTop
  have hc : IsIso f.c :=
    (Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff_bijective_appTop f).2
      (ConcreteCategory.bijective_of_isIso f.appTop)
  have hc' : IsIso (pullback.snd f t).c :=
    Stacks.AlgebraicGeometry.isIso_c_of_isPullback_of_flat (IsPullback.of_hasPullback f t) hc
  exact (ConcreteCategory.isIso_iff_bijective _).2
    ((Stacks.AlgebraicGeometry.ProperFlatFamilyUnit.isIso_c_iff _).1 hc' ⊤)

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-! ### `f_*𝒪_X = 𝒪_S` universally, tested on schemes -/

/-- Bijectivity of pullback of global functions transfers along an isomorphism of spaces
commuting with the maps. -/
private theorem bijective_globalFunctionsMap_of_iso_comp {U V W : AlgebraicSpaces B integerBase hZ}
    (e : V ≅ U) {s : U ⟶ W} {t : V ⟶ W} (he : e.hom ≫ s = t)
    (h : Function.Bijective (Space.globalFunctionsMap B integerBase hZ s)) :
    Function.Bijective (Space.globalFunctionsMap B integerBase hZ t) := by
  rw [← he, Space.globalFunctionsMap_comp, RingHom.coe_comp]
  exact (CurveFamily.globalFunctionsMap_bijective_of_iso e).comp h

/-- **`f_*𝒪_X = 𝒪_S` universally, from the base changes to schemes.** If for every scheme `T` of
the site and every morphism `t` from it to the base of a family of curves `f : X → S` pullback of
global functions along `X ×_S T ⟶ T` is bijective, then `f_*𝒪_X = 𝒪_S` universally. -/
theorem CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_forall_schemeSpace
    {X : CurveFamily B hZ}
    (h : ∀ (T : BigFppfOver B integerBase hZ) (t : schemeSpace T ⟶ schemeSpace X.base),
      Function.Bijective (Space.globalFunctionsMap B integerBase hZ (pullback.snd X.toBase t))) :
    HasUniversallyBijectiveGlobalFunctions B hZ X := by
  intro Y' g
  refine Space.bijective_globalFunctionsMap_of_forall_schemeSpace _ fun T t => ?_
  have sq := (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ
    (ObjectProperty.homMk (pullback.snd X.toBase.hom g.hom) :
      AlgebraicSpaces.fiberProduct B integerBase hZ X.toBase g ⟶ Y') t).paste_horiz
    (AlgebraicSpaces.isPullback_fiberProduct B integerBase hZ X.toBase g)
  have he := IsPullback.isoIsPullback_hom_snd _ _ sq (IsPullback.of_hasPullback X.toBase (t ≫ g))
  exact bijective_globalFunctionsMap_of_iso_comp _ he (h T (t ≫ g))

/-- **`f_*𝒪_X = 𝒪_S` universally for the family of a proper scheme over a field.** The family
of curves of a proper scheme `X` of dimension at most one over a field `k` has
`f_*𝒪_X = 𝒪_S` universally exactly when `k = H⁰(X, 𝒪_X)`. -/
theorem hasUniversallyBijectiveGlobalFunctions_curveFamilyOfScheme_iff {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    HasUniversallyBijectiveGlobalFunctions B hZ (curveFamilyOfScheme X B hZ hk hdim) ↔
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) := by
  have hX : B.Contains X.left :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk
  constructor
  · intro hF
    let p₀ : Space.FieldValuedPoint B integerBase hZ
        (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj :=
      ⟨k, hk, specULiftZIsTerminal.from _, 𝟙 _⟩
    have h1 : schemeSpaceMap (𝟙 (integerSiteObject B hZ hk)) = 𝟙 _ :=
      (schemeSpaceFunctor B integerBase hZ).map_id _
    have hsq : IsPullback (𝟙 _) (schemeSpaceMap (integerSiteMap B hZ hX hk X.hom))
        (curveFamilyOfScheme X B hZ hk hdim).toBase (schemeSpaceMap p₀.value) := by
      change IsPullback (𝟙 _) (schemeSpaceMap (integerSiteMap B hZ hX hk X.hom))
        (schemeSpaceMap (integerSiteMap B hZ hX hk X.hom))
        (schemeSpaceMap (𝟙 (integerSiteObject B hZ hk)))
      rw [h1]
      exact IsPullback.id_horiz _
    exact CurveFamily.isIso_appTop_of_isPullback_fieldValuedPoint (p := p₀)
      (V := integerSiteObject B hZ hX) (v := integerSiteMap B hZ hX hk X.hom) (q := 𝟙 _) hF hsq
  · intro hH0
    refine CurveFamily.hasUniversallyBijectiveGlobalFunctions_of_forall_schemeSpace fun T t => ?_
    obtain ⟨T, hT, rfl⟩ : ∃ (T' : Scheme.{u}) (hT : B.Contains T'),
        T = integerSiteObject B hZ hT := by
      obtain ⟨⟨T', hT⟩, ⟨⟨⟩⟩, tHom⟩ := T
      exact ⟨T', hT, congrArg Over.mk (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))⟩
    obtain ⟨t₀, rfl⟩ : ∃ t₀ : integerSiteObject B hZ hT ⟶ (curveFamilyOfScheme X B hZ hk hdim).base,
        schemeSpaceMap t₀ = t :=
      ⟨(schemeSpaceFunctorFullyFaithful _ _).preimage t,
        (schemeSpaceFunctorFullyFaithful _ _).map_preimage t⟩
    set φ : T ⟶ Spec (.of k) := (BigFppfOver.toScheme B integerBase hZ).map t₀ with hφ
    have ht₀ : integerSiteMap B hZ hT hk φ = t₀ := integerSiteMap_toScheme_map (hT' := hk) t₀
    have hP : B.Contains (pullback X.hom φ) :=
      Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (pullback.snd X.hom φ) hT
    have hsq := isPullback_schemeSpaceMap_integerSiteMap (B := B) (hZ := hZ) (hP := hP)
      (hQ := hX) (hR := hT) (hW := hk) (IsPullback.of_hasPullback X.hom φ)
    rw [ht₀] at hsq
    let e := (IsPullback.of_hasPullback (curveFamilyOfScheme X B hZ hk hdim).toBase
      (schemeSpaceMap t₀)).isoIsPullback _ _ hsq
    have he : e.hom ≫ schemeSpaceMap (integerSiteMap B hZ hP hT (pullback.snd X.hom φ)) =
        pullback.snd _ _ := IsPullback.isoIsPullback_hom_snd _ _ _ _
    refine bijective_globalFunctionsMap_of_iso_comp e he ?_
    have := isIso_appTop_pullback_snd_of_isIso_globalSections k X.hom hH0 φ
    have hΓ : Function.Bijective
        (Scheme.Γ.map ((BigFppfOver.toScheme B integerBase hZ).map
          (integerSiteMap B hZ hP hT (pullback.snd X.hom φ))).op).hom :=
      ConcreteCategory.bijective_of_isIso (pullback.snd X.hom φ).appTop
    have hcomm : ⇑(Scheme.Γ.map ((BigFppfOver.toScheme B integerBase hZ).map
          (integerSiteMap B hZ hP hT (pullback.snd X.hom φ))).op).hom ∘
          ⇑(Space.globalFunctionsYonedaRingEquiv B integerBase hZ (integerSiteObject B hZ hT)) =
        ⇑(Space.globalFunctionsYonedaRingEquiv B integerBase hZ (integerSiteObject B hZ hP)) ∘
          ⇑(Space.globalFunctionsMap B integerBase hZ
            (schemeSpaceMap (integerSiteMap B hZ hP hT (pullback.snd X.hom φ)))) :=
      funext fun s => (Space.globalFunctionsYonedaRingEquiv_globalFunctionsMap B integerBase hZ
        (integerSiteMap B hZ hP hT (pullback.snd X.hom φ)) s).symm
    refine (Function.Bijective.of_comp_iff' (Space.globalFunctionsYonedaRingEquiv B integerBase hZ
      (integerSiteObject B hZ hP)).bijective _).1 ?_
    rw [← hcomm]
    exact hΓ.comp (Space.globalFunctionsYonedaRingEquiv B integerBase hZ _).bijective

/-! ### Nodal curves over a field -/

/-- **At-worst-nodal of relative dimension one over a field.** A nonempty scheme `X` locally of
finite presentation over a field `k` is at-worst-nodal of relative dimension one over `k` exactly
when it is equidimensional of dimension one with at-worst-nodal singularities: by
[Stacks, Tag 0C59] this is the condition on the only fibre, which is `X` over the residue field
`κ = k` of the only point of `Spec k`. -/
theorem isAtWorstNodalOfRelativeDimensionOne_iff_of_field (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFinitePresentation f] [Nonempty X] :
    IsAtWorstNodalOfRelativeDimensionOne f ↔
      TopologicalSpace.Equidimensional X ∧ topologicalKrullDim X = 1 ∧
        (letI : X.Over (Spec (.of k)) := ⟨f⟩; Stacks.Curves.HasAtWorstNodalSingularities k X) := by
  rw [← Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff]
  obtain ⟨s⟩ : Nonempty (Spec (.of k)) := ⟨f (Classical.arbitrary X)⟩
  have hs : ∀ s' : Spec (.of k), s' = s := fun _ => Subsingleton.elim _ _
  have : IsIso ((Spec (.of k)).fromSpecResidueField s) := isIso_fromSpecResidueField_of_field k s
  have : IsIso (f.fiberι s) := isIso_fiberι_of_isIso_fromSpecResidueField f s inferInstance
  let e : f.fiber s ≃ₜ X := Scheme.homeoOfIso (asIso (f.fiberι s))
  have hdimeq : topologicalKrullDim (f.fiber s) = topologicalKrullDim X :=
    IsHomeomorph.topologicalKrullDim_eq _ e.isHomeomorph
  have hne : Nonempty (f.fiber s) := ⟨e.symm (Classical.arbitrary X)⟩
  set ψ := (Spec (.of k)).fromSpecResidueField s with hψ
  let φ : CommRingCat.of k ⟶ CommRingCat.of ((Spec (.of k)).residueField s) := Spec.preimage ψ
  have hφ : Spec.map φ = ψ := Spec.map_preimage ψ
  have : IsIso φ := by
    have : IsIso (Spec.map φ) := by rw [hφ]; infer_instance
    exact (ConcreteCategory.isIso_iff_bijective φ).2 (isIso_SpecMap_iff.1 this)
  have he₁ : inv (f.fiberι s) ≫ f.fiberToSpecResidueField s ≫ Spec.map φ = f := by
    rw [hφ, hψ, ← Scheme.Hom.fiber_fac, IsIso.inv_hom_id_assoc]
  let φinv : CommRingCat.of ((Spec (.of k)).residueField s) ⟶ CommRingCat.of k := inv φ
  have hφinv : IsIso φinv := by dsimp only [φinv]; infer_instance
  have hinvφ : ψ ≫ Spec.map φinv = 𝟙 _ := by
    change ψ ≫ Spec.map (inv φ) = _
    rw [← hφ, ← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id]
    rfl
  have he₂ : f.fiberι s ≫ f ≫ Spec.map φinv = f.fiberToSpecResidueField s := by
    rw [Scheme.Hom.fiber_fac_assoc, ← hψ, hinvφ, Category.comp_id]
  constructor
  · rintro ⟨-, -, hfib⟩
    obtain ⟨hequi, hdim, hnod⟩ := hfib s hne
    refine ⟨hequi.of_homeomorph e.symm, hdimeq ▸ hdim, ?_⟩
    exact @Stacks.Curves.hasAtWorstNodalSingularities_of_isIso _ _ _ _ _ _
      (f.fiberToSpecResidueField s) f (Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f s)
      hdim (inv (f.fiberι s)) inferInstance φ ‹IsIso φ› he₁ hnod
  · rintro ⟨hequi, hdim, hnod⟩
    refine ⟨inferInstance, inferInstance, fun s' _ => ?_⟩
    obtain rfl : s = s' := (hs s').symm
    refine ⟨hequi.of_homeomorph e, hdimeq.trans hdim, ?_⟩
    exact @Stacks.Curves.hasAtWorstNodalSingularities_of_isIso _ _ _ _ _ _
      f (f.fiberToSpecResidueField s) inferInstance hdim (f.fiberι s) inferInstance φinv
      hφinv he₂ hnod

/-- **At-worst-nodal singularities pass to an extension of the ground field**, for any cartesian
square over `Spec K ⟶ Spec k`. -/
theorem hasAtWorstNodalSingularities_of_isPullback (k K : Type u) [Field k] [Field K]
    [Algebra k K] {X' X : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of K)}
    {f : X ⟶ Spec (.of k)} (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [LocallyOfFiniteType f] (hequi : TopologicalSpace.Equidimensional X)
    (hdim : topologicalKrullDim X = 1)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X) :
    letI : X'.Over (Spec (.of K)) := ⟨f'⟩
    Stacks.Curves.HasAtWorstNodalSingularities K X' := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := ‹LocallyOfFiniteType f›
  have hP := Stacks.Curves.hasAtWorstNodalSingularities_baseChange k K X hequi hdim hnodal
  have hdimP : topologicalKrullDim
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}) = 1 :=
    (topologicalKrullDim_baseChange k K _ _ f (IsPullback.of_hasPullback _ _)).trans hdim
  exact Stacks.Curves.hasAtWorstNodalSingularities_of_isIso
    (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) f' hdimP h.isoPullback.hom
    (𝟙 _) (by rw [Spec.map_id, Category.comp_id, h.isoPullback_hom_snd]) hP

/-! ### Prestable families over a field -/

/-- **The family of a proper scheme over a field is prestable** exactly when the scheme is
at-worst-nodal, of dimension one, with `k = H⁰(X, 𝒪_X)`. -/
theorem isPrestableCurveFamily_curveFamilyOfScheme_iff {k : Type u} [Field k]
    (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k))) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    IsPrestableCurveFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) ↔
      (letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩;
        Stacks.Curves.HasAtWorstNodalSingularities k X.left) ∧
        topologicalKrullDim X.left = 1 ∧ IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) := by
  have hX : B.Contains X.left :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk
  have hnod : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ
      (curveFamilyOfScheme X B hZ hk hdim).toBase.hom ↔
        IsAtWorstNodalOfRelativeDimensionOne X.hom :=
    Space.holdsOnEveryEtaleChart_yoneda_map_iff B integerBase hZ
      isAtWorstNodalOfRelativeDimensionOne_isEtaleLocalOnSourceAndTarget
      (integerSiteMap B hZ hX hk X.hom)
  have : LocallyOfFinitePresentation X.hom := inferInstance
  unfold IsPrestableCurveFamily
  rw [hnod, hasUniversallyBijectiveGlobalFunctions_curveFamilyOfScheme_iff]
  constructor
  · rintro ⟨hn, hH0⟩
    have : Nonempty X.left := by
      by_contra hempty
      rw [not_nonempty_iff] at hempty
      have : Subsingleton Γ(X.left, ⊤) := inferInstance
      have hinj := (ConcreteCategory.bijective_of_isIso
        ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop)).1
      exact zero_ne_one (hinj (Subsingleton.elim _ _) : (0 : k) = 1)
    obtain ⟨-, hdim1, hnodal⟩ := (isAtWorstNodalOfRelativeDimensionOne_iff_of_field k X.hom).1 hn
    exact ⟨hnodal, hdim1, hH0⟩
  · rintro ⟨hnodal, hdim1, hH0⟩
    have : Nonempty X.left := by
      by_contra hempty
      rw [not_nonempty_iff] at hempty
      rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 hempty] at hdim1
      exact WithBot.bot_ne_coe hdim1
    have hequi : TopologicalSpace.Equidimensional X.left :=
      equidimensional_of_isIso_globalSections_of_dimension_one k X.hom hdim1
    exact ⟨(isAtWorstNodalOfRelativeDimensionOne_iff_of_field k X.hom).2
      ⟨hequi, hdim1, hnodal⟩, hH0⟩

/-! ### Stable curves after extension of the ground field -/

/-- **No rational tails or bridges after extension of the ground field.** Let `X` be a proper
scheme of dimension one over `k` with `k = H⁰(X, 𝒪_X)` and at-worst-nodal singularities, of
genus at least two, without rational tails and without rational bridges, and let `X'` be its base
change along a field extension `K/k`, in any cartesian square. Then `X'` over `K` has genus at
least two and no rational tails or bridges. By
`AlgebraicGeometry.forall_not_isRationalTail_and_isRationalBridge_iff_isAmple` the absence of
rational tails and bridges is ampleness of the dualizing sheaf; `ω_{X'}` is the pullback of `ω_X`
([Stacks, Tag 0E32]) along the affine morphism `X' ⟶ X`, hence ample. -/
theorem HasGenusTwoNoRationalTailNoRationalBridge.of_isPullback (k K : Type u) [Field k]
    [Field K] [Algebra k K] {X' X : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Spec (.of K)}
    {f : X ⟶ Spec (.of k)} (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    [IsProper f] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]
    (hdim : topologicalKrullDim X = 1)
    (hnodal : letI : X.Over (Spec (.of k)) := ⟨f⟩
      Stacks.Curves.HasAtWorstNodalSingularities k X)
    (hX : HasGenusTwoNoRationalTailNoRationalBridge k f) :
    HasGenusTwoNoRationalTailNoRationalBridge K f' := by
  let : X.Over (Spec (.of k)) := ⟨f⟩
  have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop))
  obtain ⟨hg, htail, _, hbridge⟩ := hX
  have hω := (forall_not_isRationalTail_and_isRationalBridge_iff_isAmple hdim hnodal hg).1
    ⟨htail, hbridge⟩
  have : IsProper f' := isProper_of_isPullback_specMapAlgebraMap k K g' f' f h
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f'.appTop) :=
    isIso_globalSections_baseChange k K g' f' f h
  have hdim' : topologicalKrullDim X' = 1 :=
    (topologicalKrullDim_baseChange k K g' f' f h).trans hdim
  have hequi : TopologicalSpace.Equidimensional X :=
    equidimensional_of_isIso_globalSections_of_dimension_one k f hdim
  have hnodal' := hasAtWorstNodalSingularities_of_isPullback k K h hequi hdim hnodal
  have hg' : 2 ≤ genus f' := (genus_baseChange k K g' f' f h).symm ▸ hg
  let : X'.Over (Spec (.of K)) := ⟨f'⟩
  have : IsProper (X' ↘ Spec (.of K)) := inferInstanceAs (IsProper f')
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ (X' ↘ Spec (.of K)).appTop) :=
    inferInstanceAs (IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ f'.appTop))
  have : ConnectedSpace X := connectedSpace_of_isIso_globalSections k (X ↘ Spec (.of k))
  have : ConnectedSpace X' := connectedSpace_of_isIso_globalSections K (X' ↘ Spec (.of K))
  have hωX : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f) :=
    isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X hdim hnodal
  have hωX' : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField f') :=
    isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities K X' hdim' hnodal'
  let : AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
      ((Scheme.Modules.pullback g').obj (Stacks.Duality.dualizingSheafOverField f)) :=
    Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback g' _ hωX
  have : IsAffineHom g' := MorphismProperty.of_isPullback h.flip inferInstance
  have : CompactSpace X' := QuasiCompact.compactSpace_of_compactSpace f'
  have hω' : Scheme.Modules.IsAmple X' (Stacks.Duality.dualizingSheafOverField f') :=
    Scheme.Modules.isAmple_of_iso (Stacks.Duality.dualizingSheafOverFieldBaseChangeIso f g' f' h)
      (Scheme.Modules.isAmple_pullback_of_isAffineHom g' _ hω)
  obtain ⟨htail', hbridge'⟩ :=
    (forall_not_isRationalTail_and_isRationalBridge_iff_isAmple hdim' hnodal' hg').2 hω'
  exact ⟨hg', htail', inferInstance, hbridge'⟩

/-! ### The fibres of the family of a proper scheme over a field -/

/-- A cartesian square of representable presheaves on the site is, on underlying schemes, a
cartesian square of schemes. -/
theorem isPullback_toScheme_of_isPullback_yoneda {V T W W' : BigFppfOver B integerBase hZ}
    {q : yoneda.obj V ⟶ yoneda.obj T} {v : V ⟶ W'} {c : T ⟶ W} {d : W' ⟶ W}
    (h : IsPullback q (yoneda.map v) (yoneda.map c) (yoneda.map d)) :
    IsPullback ((BigFppfOver.toScheme B integerBase hZ).map (Yoneda.fullyFaithful.preimage q))
      ((BigFppfOver.toScheme B integerBase hZ).map v)
      ((BigFppfOver.toScheme B integerBase hZ).map c)
      ((BigFppfOver.toScheme B integerBase hZ).map d) := by
  rw [← Yoneda.fullyFaithful.map_preimage q] at h
  have h' := IsPullback.of_map yoneda (yoneda.map_injective (by
    simpa only [Functor.map_comp] using h.w)) h
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  exact h'.map (BigFppfOver.toScheme B integerBase hZ)

/-- **Stacks 0E78, part (2), on families.** For `g ≥ 2`, the family of curves of a proper scheme
`X` of dimension at most one over a field `k` is stable with every fibre of genus `g` exactly
when `X` has at-worst-nodal singularities, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of `X` is
`g`, and `X` has no rational tails and no rational bridges.

Prestability is `AlgebraicGeometry.isPrestableCurveFamily_curveFamilyOfScheme_iff`. A fibre over
a field-valued point `Spec K ⟶ Spec k` is a base change of `X` along `K/k`, to which genus
([Stacks, Tag 0BY9]) and the absence of rational tails and bridges
(`AlgebraicGeometry.HasGenusTwoNoRationalTailNoRationalBridge.of_isPullback`) pass. Conversely the
fibre `V` over the identity point is isomorphic to `X`, which is then the base change of `V` along
the identity of `k`. -/
theorem isStableCurveFamilyOfFibreGenus_curveFamilyOfScheme_iff {g : ℕ} (hg : 2 ≤ g)
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k)))
    [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1) :
    IsStableCurveFamilyOfFibreGenus B hZ g (curveFamilyOfScheme X B hZ hk hdim) ↔
      letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
      Stacks.Curves.HasAtWorstNodalSingularities k X.left ∧ topologicalKrullDim X.left = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ genus X.hom = g ∧
        (∀ C : X.left.IdealSheafData, ¬ IsRationalTail k X.left C) ∧
        ∀ C : X.left.IdealSheafData, ¬ IsRationalBridge k X.left C := by
  have hX : B.Contains X.left :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.hom hk
  have hid : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 (Spec (.of k)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hfibsq : ∀ (p : Space.FieldValuedPoint B integerBase hZ
      (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj)
      (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
      (q : yoneda.obj V ⟶ (curveFamilyOfScheme X B hZ hk hdim).total.obj),
      IsPullback q (yoneda.map v) (curveFamilyOfScheme X B hZ hk hdim).toBase.hom
        (yonedaEquiv.symm p.value) →
      ∃ a : (BigFppfOver.toScheme B integerBase hZ).obj V ⟶ X.left,
        @IsPullback Scheme.{u} _ _ _ (Spec (.of p.carrier)) (Spec (.of k)) a
          ((BigFppfOver.toScheme B integerBase hZ).map v) X.hom
          ((BigFppfOver.toScheme B integerBase hZ).map p.value) := by
    intro p V v q hq
    have hval : yonedaEquiv.symm p.value = yoneda.map p.value :=
      yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map _).symm
    rw [hval] at hq
    exact ⟨_, isPullback_toScheme_of_isPullback_yoneda (c := integerSiteMap B hZ hX hk X.hom) hq⟩
  constructor
  · rintro ⟨⟨hpre, hst⟩, hfib⟩
    obtain ⟨hnodal, hdim1, hH0⟩ :=
      (isPrestableCurveFamily_curveFamilyOfScheme_iff hk X hdim).1 hpre
    have := hH0
    have hequi : TopologicalSpace.Equidimensional X.left :=
      equidimensional_of_isIso_globalSections_of_dimension_one k X.hom hdim1
    let p₀ : Space.FieldValuedPoint B integerBase hZ
        (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj :=
      ⟨k, hk, specULiftZIsTerminal.from _, 𝟙 _⟩
    have hp₀ : (BigFppfOver.toScheme B integerBase hZ).map p₀.value =
        Spec.map (CommRingCat.ofHom (algebraMap k k)) := by
      rw [hid]
      exact (BigFppfOver.toScheme B integerBase hZ).map_id _
    obtain ⟨V, v, q, hq, hgV⟩ := hfib p₀
    obtain ⟨a, ha⟩ := hfibsq p₀ V v q hq
    rw [hp₀] at ha
    have hgen : genus X.hom = g := (genus_baseChange k k a _ X.hom ha).symm.trans hgV
    obtain ⟨V', v', q', hq', hV'⟩ := hst p₀
    obtain ⟨a', ha'⟩ := hfibsq p₀ V' v' q' hq'
    rw [hp₀] at ha'
    have ha'' : @IsPullback Scheme.{u} _ _ _ (Spec (.of k)) (Spec (.of k)) a'
        ((BigFppfOver.toScheme B integerBase hZ).map v') X.hom (𝟙 (Spec (.of k))) := by
      rwa [hid] at ha'
    have : IsIso a' := ha''.isIso_fst_of_isIso
    have hinv : @IsPullback Scheme.{u} _ _ _ (Spec (.of k)) (Spec (.of k)) (inv a') X.hom
        ((BigFppfOver.toScheme B integerBase hZ).map v')
        (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
      rw [hid]
      refine IsPullback.of_horiz_isIso ⟨?_⟩
      rw [Category.comp_id, IsIso.inv_comp_eq, ha''.w, Category.comp_id]
    have : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v') :=
      isProper_of_isPullback_specMapAlgebraMap k k a' _ X.hom ha'
    have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫
        ((BigFppfOver.toScheme B integerBase hZ).map v').appTop) :=
      isIso_globalSections_baseChange k k a' _ X.hom ha'
    have hXst := HasGenusTwoNoRationalTailNoRationalBridge.of_isPullback k k hinv
      ((topologicalKrullDim_baseChange k k a' _ X.hom ha').trans hdim1)
      (hasAtWorstNodalSingularities_of_isPullback k k ha' hequi hdim1 hnodal) hV'
    obtain ⟨-, htail, _, hbridge⟩ := hXst
    exact ⟨hnodal, hdim1, hH0, hgen, htail, hbridge⟩
  · rintro ⟨hnodal, hdim1, hH0, hgen, htail, hbridge⟩
    have := hH0
    have hpre : IsPrestableCurveFamily B hZ (curveFamilyOfScheme X B hZ hk hdim) :=
      (isPrestableCurveFamily_curveFamilyOfScheme_iff hk X hdim).2 ⟨hnodal, hdim1, hH0⟩
    have hXst : HasGenusTwoNoRationalTailNoRationalBridge k X.hom :=
      ⟨hgen ▸ hg, htail, inferInstanceAs (IsProper X.hom), hbridge⟩
    have key : ∀ p : Space.FieldValuedPoint B integerBase hZ
        (schemeSpace (curveFamilyOfScheme X B hZ hk hdim).base).obj,
        ∃ (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
          (q : yoneda.obj V ⟶ (curveFamilyOfScheme X B hZ hk hdim).total.obj),
          IsPullback q (yoneda.map v) (curveFamilyOfScheme X B hZ hk hdim).toBase.hom
            (yonedaEquiv.symm p.value) ∧
          HasGenusTwoNoRationalTailNoRationalBridge p.carrier
            ((BigFppfOver.toScheme B integerBase hZ).map v) ∧
          genus ((BigFppfOver.toScheme B integerBase hZ).map v) = g := by
      intro p
      obtain ⟨V, v, q, hsq⟩ := CurveFamily.exists_isPullback_fieldValuedPoint B hZ
        (curveFamilyOfScheme X B hZ hk hdim) p
      have hsq' : IsPullback q.hom (yoneda.map v)
          (curveFamilyOfScheme X B hZ hk hdim).toBase.hom (yonedaEquiv.symm p.value) :=
        AlgebraicSpaces.isPullback_hom B integerBase hZ hsq
      obtain ⟨a, ha⟩ := hfibsq p V v q.hom hsq'
      set φ := (BigFppfOver.toScheme B integerBase hZ).map p.value
      let : Algebra k p.carrier := (Spec.preimage φ).hom.toAlgebra
      have hφ : Spec.map (CommRingCat.ofHom (algebraMap k p.carrier)) = φ := Spec.map_preimage φ
      rw [← hφ] at ha
      refine ⟨V, v, q.hom, hsq', ?_, ?_⟩
      · exact HasGenusTwoNoRationalTailNoRationalBridge.of_isPullback k p.carrier ha hdim1
          hnodal hXst
      · exact (genus_baseChange k p.carrier a _ X.hom ha).trans hgen
    refine ⟨⟨hpre, fun p => ?_⟩, fun p => ?_⟩
    · obtain ⟨V, v, q, hq, hV, -⟩ := key p
      exact ⟨V, v, q, hq, hV⟩
    · obtain ⟨V, v, q, hq, -, hV⟩ := key p
      exact ⟨V, v, q, hq, hV⟩

/-- **Stacks 0E78, part (2).** Let `g ≥ 2` and let `X` be a proper scheme of dimension at most one
over a field `k`. The following are equivalent:

* (a) the classifying morphism `Spec(k) → Curves` of `X` factors through `𝓜̄_g`
  (`AlgebraicGeometry.moduliStableCurvesOfGenus`): a scheme-valued point `y` of `Curves` over
  `U` with `y(U) ≅ X` lifts to the full subcategory of families which are stable with every fibre
  of genus `g`;
* (b) the singularities of `X` are at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of
  `X` is `g`, and `X` has no rational tails and no rational bridges;
* (c) the singularities of `X` are at-worst-nodal, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)`, the genus of
  `X` is `g`, and the dualizing sheaf `ω_X` is ample.

(a) ⟺ (b) is `AlgebraicGeometry.isStableCurveFamilyOfFibreGenus_curveFamilyOfScheme_iff`, a
lift existing exactly when the family `y(U) ≅ X` lies in `𝓜̄_g`, because that property passes to
base changes. (b) ⟺ (c) is
`AlgebraicGeometry.forall_not_isRationalTail_and_isRationalBridge_iff_isAmple`. -/
@[sga "7 I 5.1" "special case"]
theorem factors_moduliStableCurvesOfGenus_over_field_iff {g : ℕ} (hg : 2 ≤ g)
    {k : Type u} [Field k] (hk : B.Contains (Spec (.of k))) (X : Over (Spec (.of k)))
    [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1) :
    (∀ (U : BigFppfOver B integerBase hZ)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ CurveFamily B hZ),
      y ⋙ curvesProjectionOver B hZ = Over.map U.hom →
      (y.obj (Over.mk (𝟙 U.left)) ≅ curveFamilyOfScheme X B hZ hk hdim) →
      ((∃ z : BigFppfOver B U.left.1 U.left.2 ⥤
          ObjectProperty.FullSubcategory (IsStableCurveFamilyOfFibreGenus B hZ g),
          z ⋙ ObjectProperty.ι (IsStableCurveFamilyOfFibreGenus B hZ g) = y) ↔
        letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
        haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
        Stacks.Curves.HasAtWorstNodalSingularities k X.left ∧ topologicalKrullDim X.left = 1 ∧
          IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ genus X.hom = g ∧
          (∀ C : X.left.IdealSheafData, ¬ IsRationalTail k X.left C) ∧
          ∀ C : X.left.IdealSheafData, ¬ IsRationalBridge k X.left C)) ∧
    ((letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
      Stacks.Curves.HasAtWorstNodalSingularities k X.left ∧ topologicalKrullDim X.left = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ X.hom.appTop) ∧ genus X.hom = g ∧
        (∀ C : X.left.IdealSheafData, ¬ IsRationalTail k X.left C) ∧
        ∀ C : X.left.IdealSheafData, ¬ IsRationalBridge k X.left C) ↔
      letI : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
      haveI : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
      ∃ (hnodal : Stacks.Curves.HasAtWorstNodalSingularities k X.left)
        (hdim1 : topologicalKrullDim X.left = 1)
        (hH0 : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X.left ↘ Spec (.of k)).appTop)),
        genus X.hom = g ∧
          haveI := hH0
          haveI := connectedSpace_of_isIso_globalSections k (X.left ↘ Spec (.of k))
          letI := isInvertible_dualizingSheafOverField_of_hasAtWorstNodalSingularities k X.left
            hdim1 hnodal
          Scheme.Modules.IsAmple X.left
            (Stacks.Duality.dualizingSheafOverField (X.left ↘ Spec (.of k)))) := by
  refine ⟨fun U y hy e => ?_, ?_⟩
  · rw [← isStableCurveFamilyOfFibreGenus_curveFamilyOfScheme_iff hg hk X hdim]
    constructor
    · rintro ⟨z, rfl⟩
      exact CurveFamily.isStableCurveFamilyOfFibreGenus_of_hom B hZ e.inv (z.obj _).property
    · intro h
      have hall : ∀ T, IsStableCurveFamilyOfFibreGenus B hZ g (y.obj T) := fun T =>
        CurveFamily.isStableCurveFamilyOfFibreGenus_of_hom B hZ
          (y.map (Over.homMk T.hom (by simp)) ≫ e.hom) h
      exact ⟨ObjectProperty.lift (IsStableCurveFamilyOfFibreGenus B hZ g) y hall, rfl⟩
  · let : X.left.Over (Spec (.of k)) := ⟨X.hom⟩
    have : IsProper (X.left ↘ Spec (.of k)) := inferInstanceAs (IsProper X.hom)
    constructor
    · rintro ⟨hnodal, hdim1, hH0, hgen, htail, hbridge⟩
      have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X.left ↘ Spec (.of k)).appTop) := hH0
      exact ⟨hnodal, hdim1, hH0, hgen,
        (forall_not_isRationalTail_and_isRationalBridge_iff_isAmple hdim1 hnodal
          (hgen ▸ hg)).1 ⟨htail, hbridge⟩⟩
    · rintro ⟨hnodal, hdim1, hH0, hgen, hω⟩
      have : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X.left ↘ Spec (.of k)).appTop) := hH0
      obtain ⟨htail, hbridge⟩ :=
        (forall_not_isRationalTail_and_isRationalBridge_iff_isAmple hdim1 hnodal
          (hgen ▸ hg)).2 hω
      exact ⟨hnodal, hdim1, hH0, hgen, htail, hbridge⟩

end AlgebraicGeometry

end
