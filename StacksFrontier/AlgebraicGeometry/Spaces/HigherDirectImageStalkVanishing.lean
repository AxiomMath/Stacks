module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalFunctionsGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalFunctionsGeometricStalkLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.DimensionOnePointBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.VanishingAboveTheDimensionQcqs
import StacksFrontier.Algebra.Module.FinitePresentation.Transport
import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStalkLocalProperties
import StacksFrontier.AlgebraicGeometry.Spaces.DimensionZeroOverFieldSpecialization
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeTfae
import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.QcqsCriterion
import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
import StacksFrontier.AlgebraicGeometry.Spaces.ProperHigherDirectImageCoherent
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleLocalTarget
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants

/-!
# Vanishing of stalks of higher direct images above the dimension of the fibre

Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over a scheme `S` with `Y` locally
Noetherian, let `ȳ` be a geometric point of `Y` and let `ℱ` be a coherent `𝒪_X`-module.  If the
geometric fibre `X_ȳ` has dimension at most `d`, then `(Rᵖ f_* ℱ)_ȳ = 0` for `p > d`
(Stacks 0A4T); if `X_ȳ` has discrete underlying topological space, then `(Rᵖ f_* ℱ)_ȳ = 0` for
`p > 0` (Stacks 0A4S).

The proof is the source's.  By the theorem on formal functions at a geometric point
(Stacks 08B1), the completion of `(Rᵖ f_* ℱ)_ȳ` is the limit of the cohomology groups
`Hᵖ(X_n, ℱ_n)` on the infinitesimal neighbourhoods `X_n = Spec(𝒪_{Y,ȳ}/𝔪ⁿ) ×_Y X`.  Each `X_n`
is a quasi-compact quasi-separated algebraic space, proper over the one-point affine scheme
`Spec(𝒪_{Y,ȳ}/𝔪ⁿ)`, and its dimension is that of `X_ȳ`, so its cohomology vanishes above `d` by
Stacks 0A4R.  Since `(Rᵖ f_* ℱ)_ȳ` is a finite module over the Noetherian local ring
`𝒪_{Y,ȳ}` (Stacks 08AR), the vanishing of its completion forces its vanishing.

## Main results

* `AlgebraicGeometry.Space.subsingleton_moduleHigherPushforwardGeometricStalk_of_dimension_le`:
  Stacks 0A4T, `(Rᵖ f_* ℱ)_ȳ = 0` for `p > d` when `dim X_ȳ ≤ d`.
* `AlgebraicGeometry.Space.subsingleton_moduleHigherPushforwardGeometricStalk_of_discreteTopology`:
  Stacks 0A4S, `(Rᵖ f_* ℱ)_ȳ = 0` for `p > 0` when `X_ȳ` has discrete underlying space.
* `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_isPullback_of_subsingleton`:
  the cohomology of a quasi-coherent module on the base change of a proper morphism to a
  one-point affine scheme vanishes above the dimension of the fibre over any field-valued point
  with the same image.
* `AlgebraicGeometry.Space.exists_pointsMap_idealQuotientSpec_eq_class`: the point of
  `Spec (𝒪_{Y, ȳ} / J)` maps to the point of `Y` under `ȳ`, for `J` in the maximal ideal.
* `AlgebraicGeometry.Space.subsingleton_geometricInfinitesimalNeighbourhoodCohomology`:
  `Hᵖ(X_n, ℱ_n) = 0` for `p > d` when `dim X_ȳ ≤ d`.

## Implementation notes

The vanishing of a module is stated as `Subsingleton` of its carrier.  The dimension of the
fibre is bounded rather than prescribed, `d` ranging over `WithBot ℕ∞`; this contains the
source's statement, for which `dim X_ȳ = d`.

## References

* [Stacks Project, Tag 0A4S](https://stacks.math.columbia.edu/tag/0A4S)
* [Stacks Project, Tag 0A4T](https://stacks.math.columbia.edu/tag/0A4T)
* [Stacks Project, Tag 0A4R](https://stacks.math.columbia.edu/tag/0A4R)
* [Stacks Project, Tag 08B1](https://stacks.math.columbia.edu/tag/08B1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

/-! ### A finite module with vanishing completion -/

namespace Stacks.AdicTowerComparison

open Stacks.IntertwinedFiltration

/-- **A finite module whose completion is a limit of zero modules is zero.**  If the maps
`ρ n : M ⟶ Q n` assemble into an isomorphism `M ^∧_I ≅ lim_n Q n` and every `Q n` is zero, then
`M` is zero, provided `M` is finite over a Noetherian ring `A` and `I` lies in the Jacobson
radical of `A`: by the Krull intersection theorem `M` embeds in its `I`-adic completion. -/
theorem CompletionIsoLimitOfQuotients.subsingleton {A : Type*} [CommRing A] [IsNoetherianRing A]
    {M : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M] {I : Ideal A}
    (hI : I ≤ (⊥ : Ideal A).jacobson)
    {Q : ℕ → Type*} [∀ n, AddCommGroup (Q n)] [∀ n, Module A (Q n)]
    {U : ∀ m n : ℕ, m ≤ n → Q n →ₗ[A] Q m} {ρ : ∀ n, M →ₗ[A] Q n}
    (h : CompletionIsoLimitOfQuotients I M Q U ρ) (hQ : ∀ n, Subsingleton (Q n)) :
    Subsingleton M := by
  obtain ⟨e, -⟩ := h
  have : Subsingleton (towerLimit Q U) :=
    ⟨fun a b => Subtype.ext (funext fun n => Subsingleton.elim _ _)⟩
  have : Subsingleton (AdicCompletion I M) := e.toEquiv.subsingleton
  have := IsHausdorff.of_le_jacobson I M hI
  exact (AdicCompletion.of_injective I M).subsingleton

end Stacks.AdicTowerComparison

/-- **A quotient of a local ring by an ideal whose radical is the maximal ideal has at most one
prime ideal**: every prime of `R ⧸ J` pulls back to a prime of `R` containing `J`, hence
containing its radical `𝔪`, hence equal to `𝔪`. -/
theorem IsLocalRing.subsingleton_primeSpectrum_quotient {R : Type*} [CommRing R] [IsLocalRing R]
    {J : Ideal R} (hJ : IsLocalRing.maximalIdeal R ≤ J.radical) :
    Subsingleton (PrimeSpectrum (R ⧸ J)) := by
  have key : ∀ P : PrimeSpectrum (R ⧸ J),
      PrimeSpectrum.comap (Ideal.Quotient.mk J) P = IsLocalRing.closedPoint R := fun P => by
    ext1
    refine ((IsLocalRing.maximalIdeal.isMaximal R).eq_of_le
      (PrimeSpectrum.comap (Ideal.Quotient.mk J) P).isPrime.ne_top ?_).symm
    refine hJ.trans ((Ideal.IsPrime.radical_le_iff
      (PrimeSpectrum.comap (Ideal.Quotient.mk J) P).isPrime).2 fun a ha => ?_)
    show Ideal.Quotient.mk J a ∈ P.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.2 ha]
    exact P.asIdeal.zero_mem
  exact ⟨fun P Q => PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective
    ((key P).trans (key Q).symm)⟩

namespace AlgebraicGeometry.Space

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

open Stacks.Cohomology.SiteModules in
/-- **The cohomology of the infinitesimal neighbourhoods of a fibre vanishes above its
dimension.**  Let `f : X ⟶ Y` be a proper morphism of algebraic spaces, `c : T ⟶ Y` a morphism
from an affine scheme `T` with at most one point `t`, and `X'` the base change of `f` along `c`.
If a field-valued point `p` of `Y` has the image of `t` as its image and the fibre of `f` over
`p` has dimension at most `d`, then every quasi-coherent module on `X'` has vanishing cohomology
in degrees above `d`.

This applies to `T = Spec(𝒪_{Y,ȳ}/𝔪ⁿ)`, where `X'` is the `n`-th infinitesimal neighbourhood of
the geometric fibre `X_ȳ`: `X'` is proper over the affine `T`, hence quasi-compact and
quasi-separated, it has the dimension of the fibre by
`AlgebraicGeometry.Space.dimension_pullback_eq_of_subsingleton`, and Stacks 0A4R, part (1),
applies. -/
theorem isZero_rightDerived_globalSectionsFunctor_of_isPullback_of_subsingleton
    {X Y X' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    {T : BigFppfOver B S hS} (hTa : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT : Subsingleton ((BigFppfOver.toScheme B S hS).obj T)) (c : yoneda.obj T ⟶ Y.1)
    (g' : X'.1 ⟶ X.1) (f' : X'.1 ⟶ yoneda.obj T) (sq : IsPullback g' f' f.hom c)
    (t : points B S hS (yoneda.obj T)) (p : FieldValuedPoint B S hS Y.1)
    (hp : pointsMap B S hS (yoneda.obj T) c t = p.class B S hS Y.1) (d : WithBot ℕ∞)
    (hd : dimension B S hS (pullback (yonedaEquiv.symm p.value) f.hom)
      (isAlgebraicSpace_pullback B S hS (yonedaEquiv.symm p.value) f.hom
        (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Y.1)) X.2 Y.2) ≤ d)
    (G : Modules.{u, u} B S hS X'.1 X'.2) (hG : G.IsQuasicoherentOnSite) (q : ℕ) (hq : d < q) :
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u} (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS X'.1 X'.2).O)).rightDerived q).obj G) := by
  have hTalg := isAlgebraicSpace_yoneda B S hS T
  have hf' : IsProper B S hS f' := isProper_of_isPullback B S hS X'.2 X.2 hTalg Y.2 sq hf
  have hqc : IsQuasiCompactSpace B S hS X'.1 :=
    isQuasiCompactSpace_source_of_isQuasiCompact B S hS hTalg
      (isQuasiCompactSpace_yoneda_of_isAffine B S hS T hTa) hf'.2.1.2
  have hqs : IsAbsolutelyQuasiSeparated B S hS B.contains_terminal X'.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS B.contains_terminal X'.2
      (isAbsolutelyQuasiSeparated_of_isQuasiSeparatedScheme B S hS (yoneda.obj T)
        B.contains_terminal ⟨T, inferInstance, ⟨Functor.RepresentableBy.yoneda T⟩⟩)
      (isQuasiSeparated_of_isSeparated B S hS hf'.1)
  have hdim : dimension B S hS X'.1 X'.2 ≤ d := by
    rwa [dimension_eq_of_iso B S hS X'.2
        (isAlgebraicSpace_pullback B S hS f.hom c X.2 hTalg Y.2) sq.isoPullback,
      dimension_pullback_eq_of_subsingleton B S hS f.hom X.2 Y.2 hf.2.1 hT c t p hp]
  exact isZero_rightDerived_globalSectionsFunctor_of_dimension_le B S hS X' hqc hqs d hdim G hG
    q hq

attribute [local instance] pointTopology in
/-- **A fibre with discrete underlying space has dimension at most zero.**  If `f : X ⟶ Y` is
locally of finite type and the fibre `Spec k ×_Y X` of `f` over a field-valued point `p` of `Y`
has discrete underlying topological space, then that fibre has dimension at most zero: it is
locally of finite type over the field `k`, and Stacks 0ACA applies. -/
theorem dimension_pullback_le_zero_of_discreteTopology {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hf : IsLocallyOfFiniteType B S hS f) (p : FieldValuedPoint B S hS Y)
    (hdisc : DiscreteTopology (points B S hS (pullback (yonedaEquiv.symm p.value) f))) :
    dimension B S hS (pullback (yonedaEquiv.symm p.value) f)
      (isAlgebraicSpace_pullback B S hS (yonedaEquiv.symm p.value) f
        (isAlgebraicSpace_yoneda B S hS (p.siteObject B S hS Y)) hX hY) ≤ 0 :=
  dimension_le_zero_of_discreteTopology_points B S hS _ p.contained p.toBase rfl
    (pullback.fst (yonedaEquiv.symm p.value) f)
    (isLocallyOfFiniteType_pullback_fst B S hS hX hY hf _ _) hdisc

/-- **The stalks of the higher direct images along a proper morphism are finite.**  Let
`f : X ⟶ Y` be a proper morphism of algebraic spaces with `Y` locally Noetherian and `ℱ` a
coherent `𝒪_X`-module.  Then `(Rᵖ f_* ℱ)_ȳ` is a finite module over the étale local ring
`𝒪_{Y,ȳ}` at every geometric point `ȳ`: `Rᵖ f_* ℱ` is coherent by Stacks 08AR, and the stalk of a
quasi-coherent module of finite type is finite. -/
theorem module_finite_moduleHigherPushforwardGeometricStalk {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) (p : ℕ)
    (y : GeometricPoint B S hS Y.1) :
    Module.Finite (etaleLocalRing B S hS Y.1 y)
      (moduleHigherPushforwardGeometricStalk B S hS f F p y) :=
  have hcoh := isCoherent_higherDirectImage_of_isProper B S hS f hf hY F hF p
  module_finite_geometricModuleStalk B S hS Y _ hcoh.toIsQuasicoherentOnSite
    (isFiniteTypeOnSite_of_isCoherentOnSite B S hS Y _) y

/-! ### The infinitesimal neighbourhoods of the geometric fibre -/

section InfinitesimalNeighbourhood

open IsLocalRing

variable {B S hS} {X Y : AlgebraicSpaces B S hS} (y : GeometricPoint B S hS Y.1)
  (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))

/-- The evaluation `Γ(Spec 𝒪_{Y, ȳ}, 𝒪) ⟶ κ(ȳ)` at the closed point. -/
noncomputable abbrev etaleLocalRingSpecFunctionsEval :
    Γ((BigFppfOver.toScheme B S hS).obj (etaleLocalRingSpecObject (y := y) hY), ⊤) →+*
      y.val.carrier :=
  (etaleLocalRingModelEval Y y).comp (Scheme.ΓSpecIso (.of (etaleLocalRingModel Y y))).hom.hom

/-- The evaluation `Γ(Spec 𝒪_{Y, ȳ}, 𝒪) ⟶ κ(ȳ)` at the closed point vanishes on the maximal
ideal. -/
theorem etaleLocalRingSpecFunctionsEval_eq_zero
    {a : Γ((BigFppfOver.toScheme B S hS).obj (etaleLocalRingSpecObject (y := y) hY), ⊤)}
    (ha : a ∈ maximalIdeal _) : etaleLocalRingSpecFunctionsEval y hY a = 0 := by
  refine etaleLocalRingModelEval_eq_zero Y y ((mem_maximalIdeal _).2 fun hu => ?_)
  refine (mem_maximalIdeal _).1 ha ?_
  exact (MulEquiv.isUnit_map (Scheme.ΓSpecIso
    (.of (etaleLocalRingModel Y y))).commRingCatIsoToRingEquiv.toMulEquiv).1 hu

/-- A field-valued point is the image of a field-valued point with the same field whose section
is carried to its section. -/
theorem FieldValuedPoint.map_mk_eq {G F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (α : G ⟶ F)
    (p : FieldValuedPoint B S hS F)
    (v : G.obj (Opposite.op (Over.mk (⟨p.toBase⟩ : B.obj p.contained ⟶ B.obj hS))))
    (hv : α.app _ v = p.value) :
    FieldValuedPoint.map B S hS G α
      { carrier := p.carrier, contained := p.contained, toBase := p.toBase, value := v } = p := by
  obtain ⟨K, h, b, w⟩ := p
  exact congrArg (FieldValuedPoint.mk (B := B) (S := S) (hS := hS) (F := F) K h b) hv

/-- **The closed points of the infinitesimal neighbourhoods lie over `ȳ`.**  For an ideal `J` of
`R = Γ(Spec 𝒪_{Y, ȳ}, 𝒪)` contained in the maximal ideal, the morphism
`Spec (R / J) ⟶ Spec R ⟶ U₀ ⟶ Y` carries a point of `Spec (R / J)` to the point of `Y` under `ȳ`:
the evaluation `R ⟶ κ(ȳ)` at the closed point factors through `R / J`, and the resulting
`Spec κ(ȳ) ⟶ Spec (R / J) ⟶ U₀` is the lift of `ȳ` to the chosen neighbourhood `U₀`. -/
theorem exists_pointsMap_idealQuotientSpec_eq_class
    (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj (etaleLocalRingSpecObject (y := y) hY), ⊤))
    (hJ : J ≤ maximalIdeal _) :
    ∃ t : points B S hS (yoneda.obj (idealQuotientSpecObject B S hS J)),
      pointsMap B S hS _ (schemeSpaceMap (idealQuotientSpecMap B S hS J) ≫
        schemeSpaceMap (etaleLocalRingSpecToChart (y := y) hY) ≫
        chartToSpace B S hS Y (affineEtaleNeighborhood Y y).chart).hom t =
        y.val.class B S hS Y.1 := by
  let U₀ := affineEtaleNeighborhood Y y
  let ψ : (_ ⧸ J) →+* y.val.carrier := Ideal.Quotient.lift J (etaleLocalRingSpecFunctionsEval y hY)
    fun a ha => etaleLocalRingSpecFunctionsEval_eq_zero y hY (hJ ha)
  let g : Spec (.of y.val.carrier) ⟶
      (BigFppfOver.toScheme B S hS).obj (idealQuotientSpecObject B S hS J) :=
    Spec.map (CommRingCat.ofHom ψ)
  have hgq : g ≫ (BigFppfOver.toScheme B S hS).map (idealQuotientSpecMap B S hS J) =
      etaleLocalRingSpecGeometricPoint Y y := by
    have : IsAffine (Spec (.of (etaleLocalRingModel Y y))) := inferInstance
    refine ext_of_isAffine ?_
    ext b
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, idealQuotientSpecMap_appTop]
    have h1 := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ)) (Ideal.Quotient.mk J b)
    have h2 := ConcreteCategory.congr_hom
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (etaleLocalRingModelEval Y y)))
      ((Scheme.ΓSpecIso (.of (etaleLocalRingModel Y y))).hom
        (show Γ(Spec (.of (etaleLocalRingModel Y y)), ⊤) from b))
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply, Iso.hom_inv_id_apply] at h2
    rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h1
    show (Spec.map (CommRingCat.ofHom ψ)).appTop _ =
      (Spec.map (CommRingCat.ofHom (etaleLocalRingModelEval Y y))).appTop b
    rw [← h1, ← h2]
    rfl
  have hj : (BigFppfOver.toScheme B S hS).map (etaleLocalRingSpecToChart (y := y) hY) =
      etaleLocalRingSpecToChartScheme Y y := rfl
  have hg : (g ≫ (BigFppfOver.toScheme B S hS).map (idealQuotientSpecMap B S hS J)) ≫
      (BigFppfOver.toScheme B S hS).map (etaleLocalRingSpecToChart (y := y) hY) =
      (BigFppfOver.toScheme B S hS).map U₀.point := by
    rw [hgq, hj]
    exact etaleLocalRingSpecGeometricPoint_comp Y y
  have e1 : (idealQuotientSpecObject B S hS J).hom.hom =
      (BigFppfOver.toScheme B S hS).map (idealQuotientSpecMap B S hS J) ≫
        (etaleLocalRingSpecObject (y := y) hY).hom.hom := rfl
  have e2 : (etaleLocalRingSpecObject (y := y) hY).hom.hom =
      (BigFppfOver.toScheme B S hS).map (etaleLocalRingSpecToChart (y := y) hY) ≫
        ((SmallEtale.toOver B S hS Y.1).obj U₀.chart).hom.hom := rfl
  have e3 : (BigFppfOver.toScheme B S hS).map U₀.point ≫
      ((SmallEtale.toOver B S hS Y.1).obj U₀.chart).hom.hom =
      (y.val.siteObject B S hS Y.1).hom.hom :=
    congrArg (fun k => k.hom) (Over.w U₀.point)
  let τ : y.val.siteObject B S hS Y.1 ⟶ idealQuotientSpecObject B S hS J :=
    Over.homMk (ObjectProperty.homMk g) (ObjectProperty.hom_ext _ (by
      show g ≫ (idealQuotientSpecObject B S hS J).hom.hom = _
      rw [e1, e2, ← Category.assoc, ← Category.assoc, hg]
      exact e3))
  have hτ : (τ ≫ idealQuotientSpecMap B S hS J) ≫ etaleLocalRingSpecToChart (y := y) hY =
      U₀.point :=
    Over.OverMorphism.ext (ObjectProperty.hom_ext _ hg)
  have hv : (schemeSpaceMap (idealQuotientSpecMap B S hS J) ≫
      schemeSpaceMap (etaleLocalRingSpecToChart (y := y) hY) ≫
      chartToSpace B S hS Y (affineEtaleNeighborhood Y y).chart).hom.app
        (Opposite.op (y.val.siteObject B S hS Y.1)) τ = y.val.value := by
    show U₀.chart.obj.hom.app (Opposite.op (y.val.siteObject B S hS Y.1))
      ((τ ≫ idealQuotientSpecMap B S hS J) ≫ etaleLocalRingSpecToChart (y := y) hY) = _
    rw [hτ]
    exact U₀.point_comp
  exact ⟨FieldValuedPoint.class B S hS _
      { carrier := y.val.carrier, contained := y.val.contained, toBase := y.val.toBase,
        value := τ },
    congrArg (FieldValuedPoint.class B S hS Y.1) (FieldValuedPoint.map_mk_eq
      (G := (schemeSpace (idealQuotientSpecObject B S hS J)).obj)
      (schemeSpaceMap (idealQuotientSpecMap B S hS J) ≫
        schemeSpaceMap (etaleLocalRingSpecToChart (y := y) hY) ≫
        chartToSpace B S hS Y (affineEtaleNeighborhood Y y).chart).hom y.val τ hv)⟩

/-- `Spec (R / J)` has at most one point when the radical of `J` is the maximal ideal of
`R = Γ(Spec 𝒪_{Y, ȳ}, 𝒪)`. -/
theorem subsingleton_idealQuotientSpecObject
    (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj (etaleLocalRingSpecObject (y := y) hY), ⊤))
    (hJ : maximalIdeal _ ≤ J.radical) :
    Subsingleton ((BigFppfOver.toScheme B S hS).obj (idealQuotientSpecObject B S hS J)) :=
  IsLocalRing.subsingleton_primeSpectrum_quotient hJ

variable (f : X ⟶ Y)

/-- **The cohomology of the infinitesimal neighbourhoods `X_n` vanishes above the dimension of
the geometric fibre**: `H ᵖ (X_n, F_n) = 0` for `p > d` if `dim X_ȳ ≤ d`.  For `n = 0` the
neighbourhood is empty (its cohomology is killed by `𝔪 ⁰ = R`); for `n > 0`, `Spec (R / 𝔪 ⁿ)`
is a one-point affine scheme whose point lies over `ȳ`, and
`AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_isPullback_of_subsingleton`
applies. -/
theorem subsingleton_geometricInfinitesimalNeighbourhoodCohomology (hf : IsProper B S hS f.hom)
    (d : WithBot ℕ∞)
    (hd : dimension B S hS (pullback (yonedaEquiv.symm y.val.value) f.hom)
      (isAlgebraicSpace_pullback B S hS (yonedaEquiv.symm y.val.value) f.hom
        (isAlgebraicSpace_yoneda B S hS (y.val.siteObject B S hS Y.1)) X.2 Y.2) ≤ d)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (p : ℕ) (hp : d < p)
    (n : ℕ) : Subsingleton (geometricInfinitesimalNeighbourhoodCohomology f y hY F p n) := by
  rcases n with _ | n
  · have h0 := geometricInfinitesimalNeighbourhoodCohomology_smul_eq_zero f y hY F hF p 0 1
      (by simp)
    exact ⟨fun a b => by simpa using (h0 a).trans (h0 b).symm⟩
  · let J := maximalIdeal Γ((BigFppfOver.toScheme B S hS).obj
      (etaleLocalRingSpecObject (y := y) hY), ⊤) ^ (n + 1)
    obtain ⟨t, ht⟩ := exists_pointsMap_idealQuotientSpec_eq_class y hY J
      (Ideal.pow_le_self n.succ_ne_zero)
    have hT := subsingleton_idealQuotientSpecObject y hY J
      fun a ha => ⟨n + 1, Ideal.pow_mem_pow ha _⟩
    have hG : (geometricInfinitesimalNeighbourhoodModule f y hY F (n + 1)).IsQuasicoherentOnSite :=
      isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
        (isQuasicoherentOnSite_geometricBaseChangeModule y hY F hF)
    have h := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_rightDerived_globalSectionsFunctor_of_isPullback_of_subsingleton B S hS f hf
        inferInstance hT _ _ _
        (AlgebraicSpaces.isPullback_hom B S hS
          (isPullback_geometricInfinitesimalNeighbourhood f y hY (n + 1))) t y.val ht d hd _ hG
        p hp)
    exact h

end InfinitesimalNeighbourhood

/-! ### Vanishing of the stalks -/

/-- **Stacks 0A4T: stalks of higher direct images vanish above the dimension of the fibre.**
Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with `Y` locally Noetherian,
let `ȳ` be a geometric point of `Y` such that the geometric fibre `X_ȳ = Spec κ(ȳ) ×_Y X` has
dimension at most `d`, and let `ℱ` be a coherent `𝒪_X`-module.  Then `(Rᵖ f_* ℱ)_ȳ = 0` for every
`p > d`.

By the theorem on formal functions at `ȳ` (Stacks 08B1) the completion of the finite module
`(Rᵖ f_* ℱ)_ȳ` over the Noetherian local ring `𝒪_{Y, ȳ}` is `lim_n Hᵖ(X_n, ℱ_n)`, and each term
vanishes by
`AlgebraicGeometry.Space.subsingleton_geometricInfinitesimalNeighbourhoodCohomology`; a finite
module over a Noetherian local ring embeds in its completion. -/
@[stacks 0A4T]
theorem subsingleton_moduleHigherPushforwardGeometricStalk_of_dimension_le
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (y : GeometricPoint B S hS Y.1) (d : WithBot ℕ∞)
    (hd : dimension B S hS (pullback (yonedaEquiv.symm y.val.value) f.hom)
      (isAlgebraicSpace_pullback B S hS (yonedaEquiv.symm y.val.value) f.hom
        (isAlgebraicSpace_yoneda B S hS (y.val.siteObject B S hS Y.1)) X.2 Y.2) ≤ d)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) (p : ℕ) (hp : d < p) :
    Subsingleton (moduleHigherPushforwardGeometricStalk B S hS f F p y) := by
  have := isNoetherianRing_etaleLocalRingSpecFunctions y hY
  have : Module.Finite (etaleLocalRing B S hS Y.1 y)
      (geometricModuleStalk B S hS Y y (moduleHigherPushforward B S hS f F p)) :=
    module_finite_moduleHigherPushforwardGeometricStalk B S hS f hf hY F hF p y
  have : Module.Finite
      Γ((BigFppfOver.toScheme B S hS).obj (etaleLocalRingSpecObject (y := y) hY), ⊤)
      ((ModuleCat.restrictScalars (etaleLocalRingSpecFunctionsEquiv y hY).toRingHom).obj
        (geometricModuleStalk B S hS Y y (moduleHigherPushforward B S hS f F p))) :=
    finite_restrict (M := geometricModuleStalk B S hS Y y (moduleHigherPushforward B S hS f F p)) _
      (etaleLocalRingSpecFunctionsEquiv y hY).surjective
  have h := (completionIsoLimitOfQuotients_geometricStalk f y hY hf F hF p).subsingleton
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
    (subsingleton_geometricInfinitesimalNeighbourhoodCohomology y hY f hf d hd F
      hF.toIsQuasicoherentOnSite p hp)
  exact h

attribute [local instance] pointTopology in
/-- **Stacks 0A4S: stalks of higher direct images vanish when the fibre is discrete.**
Let `f : X ⟶ Y` be a proper morphism of algebraic spaces over `S` with `Y` locally Noetherian,
let `ȳ` be a geometric point of `Y` such that the geometric fibre `X_ȳ = Spec κ(ȳ) ×_Y X` has
discrete underlying topological space, and let `ℱ` be a coherent `𝒪_X`-module.  Then
`(Rᵖ f_* ℱ)_ȳ = 0` for every `p > 0`: the fibre, locally of finite type over a field with
discrete underlying space, has dimension at most `0`, and Stacks 0A4T applies. -/
@[stacks 0A4S]
theorem subsingleton_moduleHigherPushforwardGeometricStalk_of_discreteTopology
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsProper B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V))
    (y : GeometricPoint B S hS Y.1)
    (hdisc : DiscreteTopology (points B S hS (pullback (yonedaEquiv.symm y.val.value) f.hom)))
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F) (p : ℕ) (hp : 0 < p) :
    Subsingleton (moduleHigherPushforwardGeometricStalk B S hS f F p y) :=
  subsingleton_moduleHigherPushforwardGeometricStalk_of_dimension_le B S hS f hf hY y 0
    (dimension_pullback_le_zero_of_discreteTopology B S hS f.hom X.2 Y.2 hf.2.1.1 y.val hdisc) F hF
    p (by exact_mod_cast hp)

end AlgebraicGeometry.Space

end
