module

public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapDivisorLift
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapNormalized
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapSurjective
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveGeometry
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Devissage
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapDegree
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothOfFiniteTypeLift
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardLocallyTrivial
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertFamilyPicardClass
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeCurveSupplement
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RiemannRochEffective

/-!
# The Abel map is smooth when `H¹` vanishes on the fibres of the degree-`d` classes

Let `X` be a geometrically irreducible smooth projective curve over `k` with a rational point,
`H` a scheme representing its degree-`d` Hilbert functor and `Pic^d` an object, locally of finite
type over `k`, representing the degree-`d` component of its Picard functor. If every invertible
module on every base change `X_T` whose fibres have Euler characteristic `d + 1 - g` has vanishing
`H¹` on its fibres, then `γ_d : H ⟶ Pic^d` is smooth.

The proof is the infinitesimal lifting criterion
(`Stacks.Smooth.smooth_of_forall_lift`): over an affine open `V` of `H` on which the universal
class restricted along the section is trivial, a first order thickening `Spec Γ(V) ⟶ Spec C` of
`k`-schemes over `Pic^d` gives a normalized invertible module `ℒ` on `X_C` restricting to
`𝒪(D₀)` on `X_{Γ(V)}` ([Stacks, Tag 0B9N]); the divisor `D₀` lifts to a divisor `D` on `X_C`
with `𝒪(D) ≅ ℒ` (`Stacks.AbelMap.exists_hilbertFamily_lift`), and `D` is the lift
`Spec C ⟶ H`.

## Main results

* `Stacks.AbelMap.smooth_abelMap_of_fibreVanishing`.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Divisors (divisorSheaf IsEffectiveCartierDivisor)
open Stacks.FibreCohomology (fibreCohomology)
open Stacks.PicardFunctor (picardFunctor toPicardFunctor toPicardFunctorHom baseChange
  baseChangeMap baseChangeSection picardAt picardMap testMap)

universe u

namespace Stacks.AbelMap

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)
  [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)]
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 _)
  {d : ℕ} {P : Subfunctor (picardFunctor B hX hk f)}
  (hP : IsDegreeComponent B hX hk f d P)
  (H : BigFppfOver B (Spec (.of k)) hk)
  (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
    (Over.mk (B.inclusion.map H.hom)) d)
  {Pd : BigFppfOver B (Spec (.of k)) hk} (R : P.toFunctor.RepresentableBy Pd)

/-- The class on `H` that the smoothness argument trivializes locally: the pullback along the
section of the class of `𝒪(D_univ)` of the universal family. -/
abbrev universalSectionClass : Stacks.Picard.ofScheme (B.inclusion.obj H.left) :=
  Stacks.Picard.schemePullbackClass (baseChangeSection B hX hk f σ hσ H)
    (hH.family (𝟙 _)).picardClass

omit [GeometricallyIrreducible (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] in
/-- **The pullback along the section of the class of a family that a point of `H` classifies** is
the pullback of `universalSectionClass` along that point. -/
theorem schemePullbackClass_baseChangeSection_family {T : BigFppfOver B (Spec (.of k)) hk}
    (v : T ⟶ H) :
    Stacks.Picard.schemePullbackClass (baseChangeSection B hX hk f σ hσ T)
        (hH.family (testMap B hk v)).picardClass =
      Stacks.Picard.schemePullbackClass (B.inclusion.map v.left)
        (universalSectionClass B hX hk f σ hσ H hH) := by
  rw [← picardMap_universal B hX hk f H hH v, picardMap, Stacks.Picard.schemePullbackClass_comp,
    Stacks.PicardFunctor.baseChangeSection_comp_baseChangeMap,
    ← Stacks.Picard.schemePullbackClass_comp]

/-- **`Pic^d`, locally of finite type over `k`, is locally Noetherian.** -/
private theorem isLocallyNoetherian_inclusion_obj
    [LocallyOfFiniteType (B.inclusion.map Pd.hom)] :
    IsLocallyNoetherian (B.inclusion.obj Pd.left) := by
  have : IsLocallyNoetherian (B.inclusion.obj (B.obj hk)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))
  exact LocallyOfFiniteType.isLocallyNoetherian (B.inclusion.map Pd.hom)

omit [IsProjectiveVariety k (B.inclusion.map f)] in
include hP in
/-- **The Abel map is locally of finite presentation** when `Pic^d` is locally of finite type
over `k`. -/
private theorem locallyOfFinitePresentation_abelMap [LocallyOfFiniteType (B.inclusion.map Pd.hom)] :
    LocallyOfFinitePresentation (B.inclusion.map (abelMap B hX hk f hP H hH R).left) := by
  have hHsm : Smooth (Over.mk (B.inclusion.map H.hom)).hom :=
    ((Stacks.Hilbert.Curve.hilbertScheme_geometry (B.inclusion.map f) d).2 _ hH).1
  have : Smooth (B.inclusion.map H.hom) := hHsm
  have : LocallyOfFiniteType (B.inclusion.map (abelMap B hX hk f hP H hH R).left ≫
      B.inclusion.map Pd.hom) := by
    rw [← Functor.map_comp, Over.w]
    infer_instance
  have := locallyOfFiniteType_of_comp (B.inclusion.map (abelMap B hX hk f hP H hH R).left)
    (B.inclusion.map Pd.hom)
  have := isLocallyNoetherian_inclusion_obj B hk (Pd := Pd)
  exact (LocallyOfFinitePresentation.iff_locallyOfFiniteType).2 inferInstance

include hP σ hσ in
/-- **A point of `Pic^d` restricting to the class of a point of `H`.** If `v : T ⟶ H` and
`h : T' ⟶ Pd` satisfy `v ≫ γ_d = ι ≫ h` and the universal section class pulls back to zero along
`v`, then `h` is the class of a normalized invertible module `ℒ` on `X_{T'}` whose restriction to
`X_T` is the class of the family classified by `v`. -/
private theorem exists_isInvertible_picardMap_eq {T T' : BigFppfOver B (Spec (.of k)) hk}
    (ι : T ⟶ T') (v : T ⟶ H) (h : T' ⟶ Pd) (hvh : v ≫ abelMap B hX hk f hP H hH R = ι ≫ h)
    (hv : Stacks.Picard.schemePullbackClass (B.inclusion.map v.left)
      (universalSectionClass B hX hk f σ hσ H hH) = 0) :
    ∃ (L : (baseChange B hX hk f T').Modules)
      (hL : Stacks.SheafOfModules.IsInvertible (baseChange B hX hk f T').presheaf
        (Stacks.RingedSpace.structureIsSheaf (baseChange B hX hk f T').toRingedSpace) L),
      HasFibreEuler B hX hk f T' L (d + 1 - genus (B.inclusion.map f)) ∧
      toPicardFunctorHom B hX hk f T' (Stacks.SheafOfModules.picardClass _ _ L hL) =
        (R.homEquiv h).1 ∧
      picardMap B hX hk f ι (Stacks.SheafOfModules.picardClass _ _ L hL) =
        (hH.family (testMap B hk v)).picardClass := by
  have hOiso := Stacks.PicardFunctor.isIso_baseChangeProj_c_of_isCurve B hX hk f σ hσ
  obtain ⟨L, hL, hcls, -⟩ := exists_isInvertible_of_mem B hX hk f σ hσ hP T' (R.homEquiv h)
  let xn := normalize B hX hk f σ hσ T' (Stacks.SheafOfModules.picardClass _ _ L hL)
  have hxn : toPicardFunctorHom B hX hk f T' xn = (R.homEquiv h).1 := by
    rw [toPicardFunctorHom_normalize B hX hk f σ hσ hOiso,
      Stacks.PicardFunctor.toPicardFunctorHom_apply, hcls]
  obtain ⟨Ln, hLn, hLnx⟩ := Stacks.SheafOfModules.exists_picardClass_eq _ _ xn
  refine ⟨Ln, hLn, (hP T' Ln hLn).1 ?_, hLnx ▸ hxn, ?_⟩
  · rw [← Stacks.PicardFunctor.toPicardFunctorHom_apply, hLnx, hxn]
    exact (R.homEquiv h).2
  rw [hLnx]
  refine eq_of_toPicardFunctorHom_eq_of_normalized B hX hk f σ hσ hOiso T ?_ ?_ ?_
  · rw [Stacks.PicardFunctor.toPicardFunctorHom_apply,
      Stacks.PicardFunctor.toPicardFunctor_app_naturality,
      ← Stacks.PicardFunctor.toPicardFunctorHom_apply, hxn]
    have h₂ := congrArg Subtype.val (homEquiv_comp_abelMap B hX hk f hP H hH R v)
    rw [hvh] at h₂
    exact (congrArg Subtype.val (R.homEquiv_comp ι h)).symm.trans h₂
  · rw [picardMap, Stacks.Picard.schemePullbackClass_comp,
      Stacks.PicardFunctor.baseChangeSection_comp_baseChangeMap,
      ← Stacks.Picard.schemePullbackClass_comp,
      schemePullbackClass_baseChangeSection_normalize B hX hk f σ hσ T']
    exact map_zero (Stacks.Picard.schemePullbackClassHom _)
  · rwa [schemePullbackClass_baseChangeSection_family B hX hk f σ hσ H hH v]

omit [GeometricallyIrreducible (B.inclusion.map f)] [IsProper (B.inclusion.map f)]
  [IsProjectiveVariety k (B.inclusion.map f)] in
/-- **`𝒪(D₀) ≅ ℒ|_{X_T}`** for a family `D₀` on `X_T` whose class is the restriction of the class
of an invertible module `ℒ` on `X_{T'}`. -/
private theorem nonempty_divisorSheaf_iso_of_picardMap_eq {T T' : BigFppfOver B (Spec (.of k)) hk}
    (ι : T ⟶ T') (L : (baseChange B hX hk f T').Modules)
    (hL : Stacks.SheafOfModules.IsInvertible (baseChange B hX hk f T').presheaf
      (Stacks.RingedSpace.structureIsSheaf (baseChange B hX hk f T').toRingedSpace) L)
    (D₀ : Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map T.hom)) d)
    (hD₀ : picardMap B hX hk f ι (Stacks.SheafOfModules.picardClass _ _ L hL) = D₀.picardClass) :
    Nonempty (divisorSheaf D₀.ideal ≅
      (Scheme.Modules.pullback (baseChangeMap B hX hk f ι)).obj L) := by
  have := D₀.isEffectiveCartierDivisor_ideal
  obtain ⟨e₁⟩ := Stacks.PicardCurve.nonempty_rep_picardClass_iso (divisorSheaf D₀.ideal)
    (Stacks.Divisors.isInvertible_invertibleSheaf_picard D₀.ideal)
  obtain ⟨e₂⟩ := Stacks.PicardCurve.nonempty_rep_schemePullbackClass_iso
    (baseChangeMap B hX hk f ι) (Stacks.SheafOfModules.picardClass _ _ L hL)
  obtain ⟨e₃⟩ := Stacks.PicardCurve.nonempty_rep_picardClass_iso L hL
  rw [show Stacks.Picard.schemePullbackClass (baseChangeMap B hX hk f ι) _ = _ from hD₀] at e₂
  exact ⟨e₁.symm ≪≫ e₂ ≪≫ (Scheme.Modules.pullback _).mapIso e₃⟩

omit [IsProjectiveVariety k (B.inclusion.map f)] in
/-- **A family on `X_{T'}` lifting the family of `v : T ⟶ H` along `ι : T ⟶ T'`, with `𝒪(D) ≅ ℒ`
for a module `ℒ` of class `h : T' ⟶ Pd`, is a point `b : T' ⟶ H` with `ι ≫ b = v` and
`b ≫ γ_d = h`.** -/
private theorem exists_hom_of_hilbertFamily_lift {T T' : BigFppfOver B (Spec (.of k)) hk}
    (ι : T ⟶ T') (v : T ⟶ H) (h : T' ⟶ Pd) (L : (baseChange B hX hk f T').Modules)
    (hL : Stacks.SheafOfModules.IsInvertible (baseChange B hX hk f T').presheaf
      (Stacks.RingedSpace.structureIsSheaf (baseChange B hX hk f T').toRingedSpace) L)
    (hLh : toPicardFunctorHom B hX hk f T' (Stacks.SheafOfModules.picardClass _ _ L hL) =
      (R.homEquiv h).1)
    (D : Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map T'.hom)) d)
    (hDc : D.ideal.comap (Stacks.Hilbert.familyBaseChangeMap (Over.mk (B.inclusion.map f))
      (testMap B hk ι)) = (hH.family (testMap B hk v)).ideal)
    (e : divisorSheaf D.ideal ≅ L) :
    ∃ b : T' ⟶ H, ι ≫ b = v ∧ b ≫ abelMap B hX hk f hP H hH R = h := by
  let g' : (Over.mk (B.inclusion.map T'.hom) : Over (Spec (.of k))) ⟶
      Over.mk (B.inclusion.map H.hom) := hH.family.symm D
  let b : T' ⟶ H := Over.homMk (B.inclusion.preimage g'.left) (by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, Functor.map_preimage]
    exact Over.w g')
  have htest : testMap B hk b = g' := by
    ext
    exact Functor.map_preimage B.inclusion g'.left
  refine ⟨b, ?_, ?_⟩
  · have hι : testMap B hk ι ≫ g' = testMap B hk v := by
      apply hH.family.injective
      refine Stacks.Hilbert.HilbertFamily.ext ?_
      rwa [hH.naturality, Equiv.apply_symm_apply]
    ext1
    apply B.inclusion.map_injective
    rw [Over.comp_left, Functor.map_comp,
      show B.inclusion.map b.left = g'.left from Functor.map_preimage B.inclusion g'.left]
    exact congrArg (·.left) hι
  · have hD : IsEffectiveCartierDivisor D.ideal := D.isEffectiveCartierDivisor_ideal
    apply R.homEquiv.injective
    rw [homEquiv_comp_abelMap, htest, Equiv.apply_symm_apply]
    apply Subtype.ext
    change (toPicardFunctor B hX hk f).app (op T') D.picardClass = (R.homEquiv h).1
    rw [← hLh, Stacks.PicardFunctor.toPicardFunctorHom_apply,
      Stacks.Hilbert.HilbertFamily.picardClass_eq D hD]
    congr 1
    exact (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨e⟩

/-- **The ring of a finite type thickening of an affine open of `Pic^d` is Noetherian.** -/
private theorem isNoetherianRing_of_finiteType_sections
    [LocallyOfFiniteType (B.inclusion.map Pd.hom)] {U : (B.inclusion.obj Pd.left).Opens}
    (hU : IsAffineOpen U) {C : CommRingCat.{u}} (α : Γ(B.inclusion.obj Pd.left, U) ⟶ C)
    (hα : α.hom.FiniteType) : IsNoetherianRing C := by
  have := isLocallyNoetherian_inclusion_obj B hk (Pd := Pd)
  have : IsNoetherianRing Γ(B.inclusion.obj Pd.left, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := α.hom.toAlgebra
  have : Algebra.FiniteType Γ(B.inclusion.obj Pd.left, U) C := hα
  exact Algebra.FiniteType.isNoetherianRing Γ(B.inclusion.obj Pd.left, U) C

include hP σ hσ in
/-- **The lifting property of `γ_d` along a first order thickening.** Over an affine open `V` of
`H` on which `universalSectionClass` is trivial, a first order thickening `Spec Γ(V) ⟶ Spec C` over
`Pic^d` lifts to `Spec C ⟶ H`. -/
private theorem exists_lift_abelMap [LocallyOfFiniteType (B.inclusion.map Pd.hom)]
    (hvan : ∀ (T : BigFppfOver B (Spec (.of k)) hk) (L : (baseChange B hX hk f T).Modules),
      Stacks.SheafOfModules.IsInvertible (baseChange B hX hk f T).presheaf
        (Stacks.RingedSpace.structureIsSheaf (baseChange B hX hk f T).toRingedSpace) L →
      HasFibreEuler B hX hk f T L (d + 1 - genus (B.inclusion.map f)) →
      ∀ t, Module.finrank ((B.inclusion.obj T.left).residueField t)
        (fibreCohomology (pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom)) L t 1) = 0)
    (U : (B.inclusion.obj Pd.left).Opens) (V : (B.inclusion.obj H.left).Opens)
    (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (e : V ≤ B.inclusion.map (abelMap B hX hk f hP H hH R).left ⁻¹ᵁ U)
    (hWV : Stacks.Picard.schemePullbackClass V.ι (universalSectionClass B hX hk f σ hσ H hH) = 0)
    (C : CommRingCat.{u}) (α : Γ(B.inclusion.obj Pd.left, U) ⟶ C) (hα : α.hom.FiniteType)
    (φ : C ⟶ Γ(B.inclusion.obj H.left, V)) (hφ : Function.Surjective φ.hom)
    (hφ2 : RingHom.ker φ.hom ^ 2 = ⊥)
    (hαφ : α ≫ φ = (B.inclusion.map (abelMap B hX hk f hP H hH R).left).appLE U V e) :
    ∃ g' : Spec C ⟶ B.inclusion.obj H.left, Spec.map φ ≫ g' = hV.fromSpec ∧
      g' ≫ B.inclusion.map (abelMap B hX hk f hP H hH R).left = Spec.map α ≫ hU.fromSpec := by
  classical
  set γ := B.inclusion.map (abelMap B hX hk f hP H hH R).left with hγ
  have hΓU : B.Contains (Spec Γ(B.inclusion.obj Pd.left, U)) :=
    Scheme.size_lt_of_isOpenImmersion hU.fromSpec Pd.left.property
  have hΓV : B.Contains (Spec Γ(B.inclusion.obj H.left, V)) :=
    Scheme.size_lt_of_isOpenImmersion hV.fromSpec H.left.property
  have : LocallyOfFiniteType (Spec.map α) := HasRingHomProperty.Spec_iff.2 hα
  have hC : B.Contains (Spec C) := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact
    (Spec.map α) hΓU
  let q : Spec C ⟶ Spec (.of k) := Spec.map α ≫ hU.fromSpec ≫ B.inclusion.map Pd.hom
  have hq : Spec.map φ ≫ q = hV.fromSpec ≫ B.inclusion.map H.hom := by
    simp only [q, ← Spec.map_comp_assoc, hαφ]
    rw [IsAffineOpen.SpecMap_appLE_fromSpec_assoc γ hU hV e, hγ, ← Functor.map_comp, Over.w]
  let T' : BigFppfOver B (Spec (.of k)) hk :=
    Over.mk (ObjectProperty.homMk q : B.obj hC ⟶ B.obj hk)
  let T : BigFppfOver B (Spec (.of k)) hk :=
    Over.mk (ObjectProperty.homMk (Spec.map φ ≫ q) : B.obj hΓV ⟶ B.obj hk)
  let ι : T ⟶ T' := Over.homMk (ObjectProperty.homMk (Spec.map φ)) rfl
  let v : T ⟶ H :=
    Over.homMk (ObjectProperty.homMk hV.fromSpec) (ObjectProperty.hom_ext _ hq.symm)
  let h : T' ⟶ Pd :=
    Over.homMk (ObjectProperty.homMk (Spec.map α ≫ hU.fromSpec)) (ObjectProperty.hom_ext _ rfl)
  have hvh : v ≫ abelMap B hX hk f hP H hH R = ι ≫ h := by
    ext1
    apply B.inclusion.map_injective
    change hV.fromSpec ≫ γ = Spec.map φ ≫ Spec.map α ≫ hU.fromSpec
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec γ hU hV e, ← hαφ, Spec.map_comp_assoc]
  obtain ⟨Ln, hLn, hχ, hLh, hres⟩ :=
    exists_isInvertible_picardMap_eq B hX hk f σ hσ hP H hH R ι v h hvh (by
      change Stacks.Picard.schemePullbackClass (hV.isoSpec.inv ≫ V.ι)
        (universalSectionClass B hX hk f σ hσ H hH) = 0
      rw [← Stacks.Picard.schemePullbackClass_comp, hWV]
      exact map_zero (Stacks.Picard.schemePullbackClassHom _))
  let D₀ := hH.family (testMap B hk v)
  have he := nonempty_divisorSheaf_iso_of_picardMap_eq B hX hk f ι Ln hLn D₀ hres
  have := isNoetherianRing_of_finiteType_sections B hk hU α hα
  have hLn' : AlgebraicGeometry.SheafOfModules.IsInvertible
      (baseChange B hX hk f T').presheaf (baseChange B hX hk f T').ringCatSheaf.2 Ln :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp hLn
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (pullback (B.inclusion.map f) q).sheaf.obj (pullback (B.inclusion.map f) q).ringCatSheaf.2
      Ln := hLn'
  obtain ⟨D, hDc, ⟨e'⟩⟩ := exists_hilbertFamily_lift (B.inclusion.map f) φ.hom q hφ hφ2 Ln
    (hvan T' Ln hLn hχ) D₀ he.some
  obtain ⟨b, hb₁, hb₂⟩ := exists_hom_of_hilbertFamily_lift B hX hk f hP H hH R ι v h Ln hLn hLh D
    hDc e'
  have h₁ := congrArg (fun z => B.inclusion.map z.left) hb₁
  have h₂ := congrArg (fun z => B.inclusion.map z.left) hb₂
  simp only [Over.comp_left, Functor.map_comp] at h₁ h₂
  exact ⟨B.inclusion.map b.left, h₁, h₂⟩

include hP σ hσ in
/-- **Stacks Project, Tag 0BA0, clause (5), smoothness, from the vanishing of `H¹` on the fibres.**
Let `X` be a geometrically irreducible smooth projective curve of genus `g` over `k` with a
rational point, `H` a scheme representing its degree-`d` Hilbert functor and `Pic^d` an object,
locally of finite type over `k`, representing the degree-`d` component of its Picard functor. If
`H¹` vanishes on every fibre of every invertible module on a base change of `X` whose fibres have
Euler characteristic `d + 1 - g`, then `γ_d : H ⟶ Pic^d` is smooth. -/
theorem smooth_abelMap_of_fibreVanishing [LocallyOfFiniteType (B.inclusion.map Pd.hom)]
    (hvan : ∀ (T : BigFppfOver B (Spec (.of k)) hk) (L : (baseChange B hX hk f T).Modules),
      Stacks.SheafOfModules.IsInvertible (baseChange B hX hk f T).presheaf
        (Stacks.RingedSpace.structureIsSheaf (baseChange B hX hk f T).toRingedSpace) L →
      HasFibreEuler B hX hk f T L (d + 1 - genus (B.inclusion.map f)) →
      ∀ t, Module.finrank ((B.inclusion.obj T.left).residueField t)
        (fibreCohomology (pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom)) L t 1) = 0) :
    AlgebraicGeometry.Smooth (B.inclusion.map (abelMap B hX hk f hP H hH R).left) := by
  have := locallyOfFinitePresentation_abelMap B hX hk f hP H hH R
  let x := universalSectionClass B hX hk f σ hσ H hH
  refine Stacks.Smooth.smooth_of_forall_lift _
    (fun V => Stacks.Picard.schemePullbackClass V.ι x = 0) (fun V V' hle hV => ?_)
    (fun y => Stacks.Picard.exists_mem_schemePullbackClass_eq_zero x y)
    (exists_lift_abelMap B hX hk f σ hσ hP H hH R hvan)
  rw [← Scheme.homOfLE_ι _ hle, ← Stacks.Picard.schemePullbackClass_comp, hV]
  exact map_zero (Stacks.Picard.schemePullbackClassHom _)

/-! ### `H¹` of the fibres of a degree-`d` class, `d ≥ 2g - 1` -/

section FibreVanishing

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsCurve k f] [GeometricallyIrreducible f] [Smooth f] [IsProper f]

/-- **`H¹` vanishes on the fibre of an invertible module of fibre degree at least `2g - 1`.**
Let `L` be an invertible module on a base change `X_T` of a geometrically irreducible smooth
proper curve of genus `g`, and `t ∈ T` a point at which the fibre of `L` has Euler characteristic
`d + 1 - g` with `d ≥ 2g - 1`. Then `H¹(X_t, L_t) = 0`: over an algebraic closure of `κ(t)` the
fibre is a proper curve of genus `g` and `L` has degree `d` there, so the vanishing is
[Stacks, Tag 0B90], supplied as `hvan1`. -/
theorem finrank_fibreCohomology_one_eq_zero
    (hvan1 : ∀ (K : Type u) [Field K] [IsAlgClosed K] {Z : Scheme.{u}} (fZ : Z ⟶ Spec (.of K))
      [IsProper fZ] [IsCurve K fZ] (M : Z.Modules)
      (hM : SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property M),
      2 * (genus fZ : ℤ) - 1 ≤ @invertibleCurveDegree K _ Z fZ _
        (IsCurve.topologicalKrullDim_eq_one (k := K) (f := fZ)).le M hM →
      IsZero (cohomologyOverField K fZ M 1))
    {T : Scheme.{u}} (a : T ⟶ Spec (.of k)) (L : (pullback f a).Modules)
    [SheafOfModules.IsInvertible (pullback f a).sheaf.obj (pullback f a).ringCatSheaf.property L]
    {d : ℕ} (hd : 2 * (genus f : ℤ) - 1 ≤ d) (t : T)
    (hχ : (Module.finrank (T.residueField t) (fibreCohomology (pullback.snd f a) L t 0) : ℤ) -
      Module.finrank (T.residueField t) (fibreCohomology (pullback.snd f a) L t 1) =
        d + 1 - genus f) :
    Module.finrank (T.residueField t) (fibreCohomology (pullback.snd f a) L t 1) = 0 := by
  let K := AlgebraicClosure (T.residueField t)
  let φ : T.residueField t ⟶ CommRingCat.of K :=
    CommRingCat.ofHom (algebraMap (T.residueField t) K)
  let fY := pullback.snd f a
  have : IsProper fY := MorphismProperty.of_isPullback (IsPullback.of_hasPullback f a) ‹_›
  have : L.IsQuasicoherent := isQuasicoherent_of_isInvertible L
  let b := Spec.map φ ≫ T.fromSpecResidueField t
  let gZ := pullback.fst fY b
  let fZ : pullback fY b ⟶ Spec (.of K) := pullback.snd fY b
  have hZ : IsPullback gZ fZ fY b := IsPullback.of_hasPullback _ _
  let M := (Scheme.Modules.pullback gZ).obj L
  have e0 := Stacks.FibreCohomology.finrank_eq_of_isPullback fY L t φ gZ fZ hZ M (Iso.refl _) 0
  have e1 := Stacks.FibreCohomology.finrank_eq_of_isPullback fY L t φ gZ fZ hZ M (Iso.refl _) 1
  let : Algebra k K := (Spec.preimage (b ≫ a)).hom.toAlgebra
  have hb : Spec.map (CommRingCat.ofHom (algebraMap k K)) = b ≫ a := Spec.map_preimage _
  have hZX : IsPullback (gZ ≫ pullback.fst f a) fZ f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [hb]
    exact hZ.paste_horiz (IsPullback.of_hasPullback f a)
  have : IsProper fZ := isProper_of_isPullback f _ fZ hZX
  have : IsIntegral (pullback fY b) := isIntegral_of_isPullback f _ fZ hZX
  have : IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫ fZ.appTop) :=
    isIso_globalSections_of_isPullback f _ fZ hZX
  have h1 : topologicalKrullDim (pullback fY b : Scheme.{u}) = 1 :=
    topologicalKrullDim_eq_one_of_isPullback f _ fZ hZX
  have : IsCurve K fZ := isCurve_of_topologicalKrullDim_eq_one K fZ h1
  have hgen : genus fZ = genus f := genus_baseChange k K _ fZ f hZX
  have hM : SheafOfModules.IsInvertible (pullback fY b).sheaf.obj
      (pullback fY b).ringCatSheaf.property M := Stacks.Divisors.pullback_isInvertible gZ L
  have hdim : topologicalKrullDim (pullback fY b : Scheme.{u}) ≤ 1 := h1.le
  have hdeg : @invertibleCurveDegree K _ _ fZ _ hdim M hM = d := by
    rw [@invertibleCurveDegree_eq_sub_of_isZero K _ _ fZ _ hdim M hM
      (isZero_cohomologyOverField_of_two_le' K fZ hdim M)
      (isZero_cohomologyOverField_of_two_le' K fZ hdim _),
      finrank_cohomologyOverField_unit_zero_eq_one fZ,
      ← genus_eq_finrank_cohomologyOverField_unit_one' K fZ, hgen, e0, e1, hχ]
    ring
  have hvan := hvan1 K fZ M hM (by rw [hgen]; exact hdeg ▸ hd)
  rw [← e1]
  have := ModuleCat.subsingleton_of_isZero hvan
  exact Module.finrank_zero_of_subsingleton

end FibreVanishing

include hP σ hσ in
/-- **Stacks Project, Tag 0BA0, clause (5), smoothness: `γ_d` is smooth for `d ≥ 2g - 1`**, with
the vanishing of [Stacks, Tag 0B90] on curves over algebraically closed fields supplied as
`hvan1`. -/
theorem smooth_abelMap_of_vanishing [LocallyOfFiniteType (B.inclusion.map Pd.hom)]
    (hvan1 : ∀ (K : Type u) [Field K] [IsAlgClosed K] {Z : Scheme.{u}} (fZ : Z ⟶ Spec (.of K))
      [IsProper fZ] [IsCurve K fZ] (M : Z.Modules)
      (hM : SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property M),
      2 * (genus fZ : ℤ) - 1 ≤ @invertibleCurveDegree K _ Z fZ _
        (IsCurve.topologicalKrullDim_eq_one (k := K) (f := fZ)).le M hM →
      IsZero (cohomologyOverField K fZ M 1))
    (hd : 2 * (genus (B.inclusion.map f) : ℤ) - 1 ≤ d) :
    AlgebraicGeometry.Smooth (B.inclusion.map (abelMap B hX hk f hP H hH R).left) := by
  refine smooth_abelMap_of_fibreVanishing B hX hk f σ hσ hP H hH R fun T L hL hχ t => ?_
  have hL' : AlgebraicGeometry.SheafOfModules.IsInvertible
      (baseChange B hX hk f T).presheaf (baseChange B hX hk f T).ringCatSheaf.2 L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).mp hL
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      (pullback (B.inclusion.map f) (B.inclusion.map T.hom)).sheaf.obj
      (pullback (B.inclusion.map f) (B.inclusion.map T.hom)).ringCatSheaf.property L := hL'
  exact finrank_fibreCohomology_one_eq_zero (B.inclusion.map f) hvan1 (B.inclusion.map T.hom) L
    hd t (hχ t)

end Stacks.AbelMap

end
