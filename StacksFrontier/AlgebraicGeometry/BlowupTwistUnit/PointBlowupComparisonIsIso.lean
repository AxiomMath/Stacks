module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.TopFormsTrace
public import StacksFrontier.AlgebraicGeometry.Curves.RiemannHurwitzDegree
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.GenericPointSupport
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantGenericKernel
public import StacksFrontier.AlgebraicGeometry.Divisors.StalkSurjectiveOffDivisor
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Locality
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.StalkOrder
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.StalkAtCentre
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.CanonicalSectionAway
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.AwayFromCentre
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.Extension
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupTwistDerivedCriterion
public import StacksFrontier.AlgebraicGeometry.Curves.RegularSectionGeneration.Dimension
public import StacksFrontier.AlgebraicGeometry.InvertibleRankOneScheme.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.DeterminantTwistBoundCoherent
public import StacksFrontier.AlgebraicGeometry.Chow.FirstChernClassTensor
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FiniteLocallyFreeReflexive
public import StacksFrontier.AlgebraicGeometry.Blowup.GlobalExceptionalCurveDifferentials
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistGenerators
public import StacksFrontier.AlgebraicGeometry.CurveDegreeTensor.Cohomological
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic

/-!
# The comparison at one blowup, with an invertible discrepancy

Let `b : W' ⟶ W` be the blowing up of an integral regular Noetherian surface in a closed point `w`
whose local ring has dimension two, with exceptional divisor `E`, and let `p : S ⟶ S₀`, `h : W ⟶ S`
with `Ω_{W/S₀}` coherent and of generic rank `r`. Write `L = (Ω^r_{W/S₀})^{**}` and
`L' = (Ω^r_{W'/S₀})^{**}`. This file builds a morphism

`π : Rb_*(L'[0]) ⟶ L[0]`

which, read through the pullback of forms `Ω^r_{W/S₀} ⟶ b_*L'`, is the canonical map
`Ω^r_{W/S₀} ⟶ L` followed by an **automorphism** `a` of `L`
(`Stacks.BlowupTwistUnit.exists_isIso_comparison_blowUp`).

`π` is `Rb_*` of `χ : L' ⟶ b^*L ⊗ 𝒪(E)`, followed by the inverses of the two isomorphisms
`b_*(b^*L ⊗ 𝒪(E)) ⟶ Rb_*(b^*L ⊗ 𝒪(E))` (the first direct image vanishes) and
`L ⟶ b_*(b^*L ⊗ 𝒪(E))` (the projection formula and `𝒪_W ≅ b_*𝒪(E)`). The map `χ` comes from
the dichotomy of [Stacks, Tag 0B3T]. That `a` is invertible is proved at the stalks: off `E` the
determinant of `b^*Ω_{W/S₀} ⟶ Ω_{W'/S₀}` is onto, so `b^*a` is a unit there, so `a` is invertible
off `w`; at `w` both stalks are free of rank one over a local ring of dimension two.

## Main results

The elided prefix is `Stacks.BlowupTwistUnit`.

* `bijective_of_injective_comp_eq`: a comparison of modules free of rank one over a domain.
* `isIso_singleToDerivedPushforward_blowUp`: `b_*F ⟶ Rb_*F` is invertible when `R¹b_*F = 0`.
* `isIso_of_bijective_mapFun_pullback_blowUp`: an endomorphism of an invertible module whose
  pullback is invertible at the stalks off `E` is invertible.
* `surjective_mapFun_detMap_blowUp`: off `E`, the determinant of `b^*Ω_{W/S₀} ⟶ Ω_{W'/S₀}` is
  onto at the stalks.
* `exists_isIso_comparison_blowUp`: the comparison, with invertible discrepancy.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0B4L](https://stacks.math.columbia.edu/tag/0B4L)
-/

attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Duality
open Stacks.AlgebraicGeometry.ReflexiveModules
open Stacks.ResolutionOfSurfaces

universe u

namespace Stacks.BlowupTwistUnit

/-! ### Stalks -/

section Stalks

variable {X : Scheme.{u}}

/-- A morphism invertible over an open has bijective stalk maps at the points of that open. -/
theorem bijective_mapFun_of_isIso_pullback {F G : X.Modules} (φ : F ⟶ G) (V : X.Opens)
    (hV : IsIso ((Scheme.Modules.pullback V.ι).map φ)) (x : X) (hx : x ∈ V) :
    Function.Bijective (Stacks.ModuleStalk.mapFun φ x) := by
  have hr : IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback V.ι) φ).mpr hV
  have h := isIso_stalk_of_isIso_restrict φ V hr x hx
  exact (ConcreteCategory.isIso_iff_bijective _).mp h

/-- A morphism whose stalk maps at the points of an open are bijective is invertible over that
open. -/
theorem isIso_pullback_of_bijective_mapFun {F G : X.Modules} (φ : F ⟶ G) (V : X.Opens)
    (h : ∀ x ∈ V, Function.Bijective (Stacks.ModuleStalk.mapFun φ x)) :
    IsIso ((Scheme.Modules.pullback V.ι).map φ) := by
  refine (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback V.ι) φ).mp
    (isIso_restrictFunctor_map_of_bijective_stalkHom V φ fun x hx => ?_)
  have e : ⇑(stalkHom φ x) = Stacks.ModuleStalk.mapFun φ x :=
    funext fun m => (stalkFunctor_map_apply φ x m).symm
  rw [e]
  exact h x hx

end Stalks

/-! ### Linear algebra on a module free of rank one -/

/-- **A scalar comparison on modules free of rank one.** Let `M` and `B` be modules free of rank
one over a domain, `ι : M ⟶ B` injective, `θ` a surjective endomorphism of `M` and `c` an
endomorphism of `B` with `ι ∘ θ = c ∘ ι`. Then `c` is bijective: it is multiplication by a
scalar, which acts on `M` as `θ` does and is therefore a unit. -/
theorem bijective_of_injective_comp_eq {R M B : Type*} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] [AddCommGroup B] [Module R B] (gM : M) (hgM : ∀ z : M, ∃ r : R, z = r • gM)
    (hgM0 : ∀ r : R, r • gM = 0 → r = 0) (gB : B) (hgB : ∀ z : B, ∃ r : R, z = r • gB)
    (hgB0 : ∀ r : R, r • gB = 0 → r = 0) (ι : M →ₗ[R] B) (hι : Function.Injective ι)
    (θ : M →ₗ[R] M) (hθ : Function.Surjective θ) (c : B →ₗ[R] B)
    (h : ∀ m, ι (θ m) = c (ι m)) : Function.Bijective c := by
  obtain ⟨γ, hγ⟩ := hgB (c gB)
  have hc : ∀ z, c z = γ • z := by
    intro z
    obtain ⟨s, rfl⟩ := hgB z
    rw [map_smul, hγ, smul_smul, smul_smul, mul_comm]
  have hθγ : ∀ m, θ m = γ • m := fun m => hι (by rw [h, hc, map_smul])
  obtain ⟨m₀, hm₀⟩ := hθ gM
  obtain ⟨s, rfl⟩ := hgM m₀
  have hs : (γ * s) • gM = gM := by rw [mul_smul, ← hθγ, hm₀]
  obtain ⟨t, ht⟩ := hgB (ι gM)
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    have h0 : ι gM = ι 0 := by rw [ht, map_zero]
    have := hgM0 1 (by rw [one_smul]; exact hι h0)
    exact one_ne_zero this
  have hγs : γ * s = 1 := by
    have h1 : ((γ * s) * t - t) • gB = 0 := by
      rw [sub_smul, mul_smul, ← ht, ← map_smul, hs, sub_self]
    have h2 : t * (γ * s - 1) = 0 := by
      have := hgB0 _ h1
      rw [← this]; ring
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 ht0
    · exact sub_eq_zero.mp h3
  refine ⟨fun z₁ z₂ hz => ?_, fun z => ⟨s • z, ?_⟩⟩
  · rw [hc, hc] at hz
    have := congrArg (s • ·) hz
    simp only [smul_smul] at this
    rwa [mul_comm s γ, hγs, one_smul, one_smul] at this
  · rw [hc, smul_smul, hγs, one_smul]


/-! ### The comparison `b_*F ⟶ Rb_*F` at the blowing up of a point -/

section BlowUp

variable {W : Scheme.{u}} [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsNoetherian W]

attribute [local instance 10000] HasDerivedCategory.standard in
/-- At the standard model, `b_*F ⟶ Rb_*F` is invertible at a quasi-coherent `F` with
`R^1b_*F = 0`, for `b` the blowing up of a closed point of an integral Noetherian surface. -/
theorem isIso_homotopyPushforward_blowUp_totalRightDerivedUnit_standard
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W))
    (F : (AlgebraicGeometry.blowUp (pointIdeal w hw)).Modules) [F.IsQuasicoherent]
    (h1 : IsZeroFirstDirectImageBlowUp w hw F) :
    IsIso (((homotopyPushforward
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).totalRightDerivedUnit
      DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))).app
        ((HomotopyCategory.quotient _ _).obj
          ((CochainComplex.singleFunctor _ 0).obj F))) := by
  have hqc : ∀ n, (((CochainComplex.singleFunctor _ 0).obj F).X n).IsQuasicoherent := by
    intro n
    by_cases hn : n = 0
    · subst hn
      exact (SheafOfModules.isQuasicoherent _).prop_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm inferInstance
    · exact Stacks.AlgebraicGeometry.HigherDirectImage.isQuasicoherent_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F n hn)
  have hac : ∀ n, (Scheme.Modules.pushforward
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).rightAcyclic
      (((CochainComplex.singleFunctor _ 0).obj F).X n) := by
    intro n
    by_cases hn : n = 0
    · subst hn
      exact (Scheme.Modules.pushforward _).rightAcyclic.prop_of_iso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).symm
        (rightAcyclic_pushforward_blowUpToBase_vanishingIdeal_singleton hdim w hw F h1)
    · have : Injective (((CochainComplex.singleFunctor _ 0).obj F).X n) :=
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F n hn).injective
      exact Functor.rightAcyclic_of_injective (Scheme.Modules.pushforward _) _
  exact AlgebraicGeometry.isIso_to_rightDerived_of_termwise_acyclic _
    ((CochainComplex.singleFunctor _ 0).obj F) hqc hac _ _

/-- **`b_*F ⟶ Rb_*F` is invertible at a quasi-coherent `F` with `R^1b_*F = 0`**, for `b` the
blowing up of a closed point of an integral Noetherian surface. -/
theorem isIso_singleToDerivedPushforward_blowUp (hdim : topologicalKrullDim W = 2) (w : W)
    (hw : IsClosed ({w} : Set W)) (F : (AlgebraicGeometry.blowUp (pointIdeal w hw)).Modules)
    [F.IsQuasicoherent] (h1 : IsZeroFirstDirectImageBlowUp w hw F) :
    IsIso (singleToDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) F) := by
  have h := (StacksDraft.DerivedModel.isIso_schemeDerivedPushforwardUnit_app_iff_model
    (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _)
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory _)
    (AlgebraicGeometry.Scheme.Modules.hasDerivedCategory W)
    ((HomotopyCategory.quotient _ _).obj ((CochainComplex.singleFunctor _ 0).obj F))).mp
    (isIso_homotopyPushforward_blowUp_totalRightDerivedUnit_standard hdim w hw F h1)
  rw [singleToDerivedPushforward]
  exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' inferInstance
    (IsIso.comp_isIso' h inferInstance))

end BlowUp


/-! ### Multiplication by the canonical section off the divisor -/

section CanonicalSection

/-- If `F.map f` and `F.map g` are invertible, so is `F.map (f ≫ g)`. -/
theorem isIso_map_comp_of {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b c : C} (f : a ⟶ b) (g : b ⟶ c) (hf : IsIso (F.map f)) (hg : IsIso (F.map g)) :
    IsIso (F.map (f ≫ g)) := by
  rw [F.map_comp]
  exact IsIso.comp_isIso' hf hg

/-- If `F.map (f ≫ g)` is invertible and `f` is, so is `F.map g`. -/
theorem isIso_map_of_isIso_map_comp {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {a b c : C} (f : a ⟶ b) (g : b ⟶ c) [IsIso f] (h : IsIso (F.map (f ≫ g))) :
    IsIso (F.map g) := by
  rw [F.map_comp] at h
  exact IsIso.of_isIso_comp_left (F.map f) _

variable {Y : Scheme.{u}}

/-- **Multiplication by the canonical section of `𝒪(D)` is invertible over an open disjoint from
`D`.** -/
theorem isIso_pullback_tensorCanonicalSection_of_disjoint (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (F : Y.Modules) (V : Y.Opens)
    (hV : ∀ y : V.toScheme, V.ι y ∉ D.supportSet) :
    IsIso ((Stacks.RingedSpace.pullbackFunctor V.ι.toLRSHom.toShHom).map
      (Stacks.Divisors.tensorCanonicalSection D F)) := by
  have hs := isIso_pullback_canonicalSectionHom_of_disjoint D V hV
  have he : Scheme.Modules.tensorLeftMap F (Stacks.Divisors.canonicalSectionHom D) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(Y).presheaf, (Y).IsSheaf⟩))).map
        ((Prod.mkHom (𝟙 F) (Stacks.Divisors.canonicalSectionHom D)) :
          ((F, SheafOfModules.unit (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)) :
            _ × _) ⟶ (F, Stacks.Divisors.invertibleSheaf' D)) := by
    refine Eq.symm (Eq.trans ?_ (Category.id_comp
      (Scheme.Modules.tensorLeftMap F (Stacks.Divisors.canonicalSectionHom D))))
    exact congrArg (fun t => CategoryTheory.NatTrans.app t
        (SheafOfModules.unit (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace)) ≫
      Scheme.Modules.tensorLeftMap F (Stacks.Divisors.canonicalSectionHom D))
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨(Y).presheaf, (Y).IsSheaf⟩).map_id F)
  have ht : IsIso ((Stacks.RingedSpace.pullbackFunctor V.ι.toLRSHom.toShHom).map
      (Scheme.Modules.tensorLeftMap F (Stacks.Divisors.canonicalSectionHom D))) := by
    rw [he]
    exact Stacks.AffineProjectionFormula.isIso_pullback_tensorSheaf_map
      V.ι.toLRSHom.toShHom F (Stacks.Divisors.canonicalSectionHom D) hs
  rw [Stacks.Divisors.tensorCanonicalSection]
  exact isIso_map_comp_of _ _ _ (((Stacks.RingedSpace.pullbackFunctor V.ι.toLRSHom.toShHom).mapIso
    (Scheme.Modules.tensorRightUnitor F).symm).isIso_hom) ht

/-- **Multiplication by the canonical section of `𝒪(D)` has bijective stalk maps off `D`.** -/
theorem bijective_mapFun_tensorCanonicalSection (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] (F : Y.Modules) (x : Y)
    (hx : x ∉ D.supportSet) :
    Function.Bijective
      (Stacks.ModuleStalk.mapFun (Stacks.Divisors.tensorCanonicalSection D F) x) := by
  let V : Y.Opens := ⟨D.supportSetᶜ, (D.support.isClosed : IsClosed D.supportSet).isOpen_compl⟩
  have hiso := isIso_pullback_tensorCanonicalSection_of_disjoint D F V fun y => y.2
  exact bijective_mapFun_of_isIso_pullback _ V (by exact hiso) x hx

end CanonicalSection


/-! ### The comparison at the stalks off the divisor -/

section StalkComparison

variable {Y : Scheme.{u}} [AlgebraicGeometry.IsIntegral Y]

/-- **Off the divisor, a comparison of invertible modules is invertible at the stalks.** Let
`M`, `B` be invertible on an integral scheme, `ι : M ⟶ B` a monomorphism, `c` an endomorphism
of `B`, and `μ : M ⟶ L'`, `ν : L' ⟶ M ⊗ 𝒪(D)` with
`μ ≫ ν ≫ (ι ⊗ 𝒪(D)) = ι ≫ c ≫ (multiplication by 1_D)`. At a point off `D` at which `μ` is
surjective and `ν` bijective, `c` is bijective. -/
theorem bijective_mapFun_of_comp_eq (D : Y.IdealSheafData)
    [Stacks.Divisors.IsEffectiveCartierDivisor D] {M B L' : Y.Modules}
    [Stacks.Ample.IsInvertibleModule Y M] [Stacks.Ample.IsInvertibleModule Y B]
    (ι : M ⟶ B) [Mono ι] (c : B ⟶ B) (μ : M ⟶ L')
    (ν : L' ⟶ Scheme.Modules.tensorObj M (Stacks.Divisors.invertibleSheaf' D))
    (heq : μ ≫ ν ≫ Scheme.Modules.tensorRightMap ι (Stacks.Divisors.invertibleSheaf' D) =
      ι ≫ c ≫ Stacks.Divisors.tensorCanonicalSection D B)
    (x : Y) (hx : x ∉ D.supportSet)
    (hμ : Function.Surjective (Stacks.ModuleStalk.mapFun μ x))
    (hν : Function.Bijective (Stacks.ModuleStalk.mapFun ν x)) :
    Function.Bijective (Stacks.ModuleStalk.mapFun c x) := by
  open Stacks.ModuleStalk in
  obtain ⟨gM, hgM, hgM0⟩ := Stacks.StalkOrder.exists_generator M x
  obtain ⟨gB, hgB, hgB0⟩ := Stacks.StalkOrder.exists_generator B x
  have hM := bijective_mapFun_tensorCanonicalSection D M x hx
  have hB := bijective_mapFun_tensorCanonicalSection D B x hx
  have hι := Stacks.RegularSectionGeneration.injective_mapFun_of_mono ι x
  let eM := LinearEquiv.ofBijective (map (Stacks.Divisors.tensorCanonicalSection D M) x) hM
  let θ : _ →ₗ[Y.presheaf.stalk x] _ := eM.symm.toLinearMap ∘ₗ map ν x ∘ₗ map μ x
  have hθ : Function.Surjective θ :=
    eM.symm.surjective.comp (hν.2.comp hμ)
  have hnat := Stacks.DeRham.TwistDerived.tensorCanonicalSection_naturality D ι
  refine bijective_of_injective_comp_eq gM hgM hgM0 gB hgB hgB0 (map ι x) hι θ hθ (map c x)
    fun m => ?_
  apply hB.1
  have h1 := congrArg (fun f => mapFun f x m) heq
  have h2 := congrArg (fun f => mapFun f x (θ m)) hnat
  simp only [mapFun_comp] at h1 h2
  simp only [map_apply]
  rw [h2]
  have h3 : mapFun (Stacks.Divisors.tensorCanonicalSection D M) x (θ m) =
      mapFun ν x (mapFun μ x m) := eM.apply_symm_apply _
  rw [h3, h1]

end StalkComparison

/-! ### The comparison `Rb_*(L'[0]) ⟶ L[0]` from a morphism of modules -/

section Comparison

variable {W' W : Scheme.{u}} [CompactSpace W'] [QuasiSeparatedSpace W'] [CompactSpace W]
  [QuasiSeparatedSpace W]

/-- **A comparison `Rb_*(L'[0]) ⟶ L[0]` restricting to a given map.** Let `χ : L' ⟶ N`, let
`τ : L ⟶ b_*N` be invertible and let `b_*N ⟶ Rb_*N` be invertible. If `t ≫ a = f ≫ b_*χ ≫ τ⁻¹`
then `Rb_*χ`, followed by the inverses of the two comparisons, restricts along `f` to `t ≫ a`. -/
theorem exists_comp_singleToDerivedPushforward_eq (b : W' ⟶ W) {F L : W.Modules}
    (hL : L.IsQuasicoherent) {L' N : W'.Modules} (hL' : L'.IsQuasicoherent)
    (f : F ⟶ (Scheme.Modules.pushforward b).obj L') (χ : L' ⟶ N)
    (τ : L ⟶ (Scheme.Modules.pushforward b).obj N) [IsIso τ]
    [IsIso (singleToDerivedPushforward b N)] (t : F ⟶ L) (a : L ⟶ L)
    (ha : t ≫ a = f ≫ (Scheme.Modules.pushforward b).map χ ≫ inv τ) :
    ∃ π : (quasiCoherentDerivedPushforward b
          (isQuasicoherent_homology_derivedPushforward_of_qcqs b)).obj
        (singleQuasiCoherent L' hL' 0) ⟶ singleQuasiCoherent L hL 0,
      (DerivedCategory.singleFunctor W.Modules 0).map f ≫
          singleToDerivedPushforward b L' ≫ π.hom =
        (DerivedCategory.singleFunctor W.Modules 0).map (t ≫ a) := by
  refine ⟨(quasiCoherentHomEquiv _ _).symm
    ((derivedPushforward b).map ((DerivedCategory.singleFunctor W'.Modules 0).map χ) ≫
      inv (singleToDerivedPushforward b N) ≫
      (DerivedCategory.singleFunctor W.Modules 0).map (inv τ)), ?_⟩
  have hn := (singleToDerivedPushforward_naturality b χ).symm
  have hc : (DerivedCategory.singleFunctor W.Modules 0).map f ≫
      singleToDerivedPushforward b L' ≫
      ((derivedPushforward b).map ((DerivedCategory.singleFunctor W'.Modules 0).map χ) ≫
        inv (singleToDerivedPushforward b N) ≫
          (DerivedCategory.singleFunctor W.Modules 0).map (inv τ)) =
      (DerivedCategory.singleFunctor W.Modules 0).map (t ≫ a) := by
    rw [reassoc_of% hn, IsIso.hom_inv_id_assoc, ha, Functor.map_comp, Functor.map_comp]
  exact (congrArg (fun z => (DerivedCategory.singleFunctor W.Modules 0).map f ≫
    singleToDerivedPushforward b L' ≫ z) (quasiCoherentHomEquiv_symm_hom _ _ _)).trans hc

end Comparison

/-! ### Invertibility of an endomorphism from its pullback off the exceptional divisor -/

section OffExceptional

variable {W : Scheme.{u}} [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsNoetherian W]

/-- **An endomorphism of an invertible module on a surface is invertible as soon as its pullback
to the blowing up of a closed point is invertible at the stalks off the exceptional divisor.**
Off the centre the blowing up is an isomorphism, so the endomorphism is invertible there; at the
centre, whose local ring has dimension two, both stalks are free of rank one. -/
theorem isIso_of_bijective_mapFun_pullback_blowUp (w : W) (hw : IsClosed ({w} : Set W))
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (L : W.Modules) [L.IsQuasicoherent]
    [Stacks.Ample.IsInvertibleModule W L] (a : L ⟶ L)
    (h : ∀ x' : AlgebraicGeometry.blowUp (pointIdeal w hw),
      x' ∉ (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)).supportSet →
        Function.Bijective (Stacks.ModuleStalk.mapFun
          ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).map a)
          x')) :
    IsIso a := by
  set I := pointIdeal w hw with hI
  set b := AlgebraicGeometry.blowUpToBase I with hb
  let V : W.Opens := ⟨I.supportᶜ, I.support.isClosed.isOpen_compl⟩
  haveI : IsIso (b ∣_ V) := isIso_blowUp_restrict_compl_support I
  have hsupp : ((AlgebraicGeometry.exceptionalIdeal I).support : Set _) =
      b.base ⁻¹' (I.support : Set W) := by
    show ((I.comap b).support : Set (AlgebraicGeometry.blowUp I)) = _
    rw [Scheme.IdealSheafData.support_comap]
    rfl
  have h1 : IsIso ((Scheme.Modules.pullback (b ⁻¹ᵁ V).ι).map
      ((Scheme.Modules.pullback b).map a)) := by
    refine isIso_pullback_of_bijective_mapFun _ _ fun x' hx' => h x' fun hE => hx' ?_
    have hE' : x' ∈ ((AlgebraicGeometry.exceptionalIdeal I).support : Set _) := hE
    rw [hsupp] at hE'
    exact hE'
  have h2 := Stacks.AffineProjectionFormula.isIso_pullback_pushforward_map b V _ h1
  have hu := isIso_pullback_unit_of_isIso_morphismRestrict b V L
  have hnat := (Scheme.Modules.pullbackPushforwardAdjunction b).unit.naturality a
  simp only [Functor.id_map, Functor.comp_map] at hnat
  have h3 : IsIso ((Scheme.Modules.pullback V.ι).map a) := by
    have hc : IsIso ((Scheme.Modules.pullback V.ι).map a ≫ (Scheme.Modules.pullback V.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app L)) := by
      rw [← Functor.map_comp, hnat, Functor.map_comp]
      exact IsIso.comp_isIso' hu h2
    exact IsIso.of_isIso_comp_right _ ((Scheme.Modules.pullback V.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction b).unit.app L))
  have h4 : IsIso ((Scheme.Modules.restrictFunctor V.ι).map a) :=
    (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback V.ι) a).mpr h3
  have hVw : ∀ y : W, y ≠ w → y ∈ V := by
    intro y hy
    show y ∉ (I.support : Set W)
    rw [hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact hy
  have hdim : 2 ≤ ringKrullDim (W.presheaf.stalk w) := by rw [hstalkdim]
  letI := Stacks.ModuleStalkSpecialization.stalkModule L w
  obtain ⟨g, hg, hg0⟩ := Stacks.StalkOrder.exists_generator L w
  let d : L.presheaf.stalk w ≃ₗ[W.presheaf.stalk w] W.presheaf.stalk w :=
    (LinearEquiv.ofBijective (LinearMap.toSpanSingleton (W.presheaf.stalk w) _ g)
      ⟨fun r s hrs => sub_eq_zero.mp (hg0 _ (by
          rw [sub_smul]
          exact sub_eq_zero.mpr hrs)),
        fun z => (hg z).imp fun r hr => hr.symm⟩).symm
  exact isIso_of_isIso_restrict_of_stalk_free a w V h4 hVw hdim d d

end OffExceptional

/-! ### Small lemmas -/

section Small

variable {X : Scheme.{u}}

/-- **Two maps out of a reflexive hull into a reflexive module agree as soon as they agree on the
module.** -/
theorem hom_ext_reflexiveHull {F N : X.Modules}
    [IsIso (toDoubleDual (dualSheaf (dualSheaf F)))] (hN : IsReflexive N)
    {φ ψ : reflexiveHull F ⟶ N}
    (h : (toReflexiveHull F).1 ≫ φ = (toReflexiveHull F).1 ≫ ψ) : φ = ψ := by
  have : IsIso (toReflexiveHull N).1 := (isReflexive_iff_isIso_toReflexiveHull N).mp hN
  have key : ∀ χ : reflexiveHull F ⟶ N,
      χ ≫ (toReflexiveHull N).1 = doubleDualMap ((toReflexiveHull F).1 ≫ χ) := fun χ => by
    rw [doubleDualMap_comp]
    exact (toDoubleDual_naturality χ).trans
      (congrArg (· ≫ doubleDualMap χ) (doubleDualMap_toDoubleDual F).symm)
  exact (cancel_mono (toReflexiveHull N).1).mp (by rw [key, key, h])

/-- An invertible module is finite locally free. -/
theorem isFiniteLocallyFree_of_isInvertible (F : X.Modules)
    [hF : Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F := by
  have := (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one
    X F).mp hF
  exact AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree F 1

/-- An invertible module is reflexive. -/
theorem isReflexive_of_isInvertible (F : X.Modules)
    [Stacks.SheafOfModules.IsInvertible X.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) F] : IsReflexive F :=
  Stacks.FundamentalGroup.ExtendedEtale.isReflexive_of_isFiniteLocallyFree' F
    ((Scheme.Modules.isFiniteLocallyFree_iff F).mpr (isFiniteLocallyFree_of_isInvertible F))

/-- The stalk maps of an isomorphism are bijective. -/
theorem bijective_mapFun_of_isIso {F G : X.Modules} (e : F ⟶ G) [IsIso e] (x : X) :
    Function.Bijective (Stacks.ModuleStalk.mapFun e x) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨Stacks.ModuleStalk.mapFun (inv e) x,
    fun m => ?_, fun m => ?_⟩
  · rw [← Stacks.ModuleStalk.mapFun_comp, IsIso.hom_inv_id, Stacks.ModuleStalk.mapFun_id]
  · rw [← Stacks.ModuleStalk.mapFun_comp, IsIso.inv_hom_id, Stacks.ModuleStalk.mapFun_id]

/-- **Transposing along `b^* ⊣ b_*`.** -/
theorem pullback_map_comp_eq_of_comp_eq {X' : Scheme.{u}} (b : X' ⟶ X) {F L : X.Modules}
    {N : X'.Modules} (u : F ⟶ L) (k : (Scheme.Modules.pullback b).obj F ⟶ N)
    (s : (Scheme.Modules.pullback b).obj L ⟶ N)
    (heq : u ≫ (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app L ≫
        (Scheme.Modules.pushforward b).map s =
      (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app F ≫
        (Scheme.Modules.pushforward b).map k) :
    (Scheme.Modules.pullback b).map u ≫ s = k := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _).injective
  have hnat := (Scheme.Modules.pullbackPushforwardAdjunction b).unit.naturality u
  simp only [Functor.id_map, Functor.comp_map] at hnat
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, ← heq,
    ← Category.assoc, ← hnat, Category.assoc]

end Small

section Facts

variable {X : Scheme.{u}}

/-- **An invertible module is not zero**: its stalk at any point is free of rank one over a
local ring. -/
theorem id_ne_zero_of_isInvertibleModule (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (x : X) : 𝟙 L ≠ 0 := by
  intro h0
  obtain ⟨g, -, hg0⟩ := Stacks.StalkOrder.exists_generator L x
  have hg : g = 0 := by
    have h1 := Stacks.ModuleStalk.mapFun_id L x g
    rw [h0] at h1
    obtain ⟨U, hxU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq _ g
    rw [Stacks.ModuleStalk.mapFun_germ] at h1
    simpa using h1.symm
  exact one_ne_zero (hg0 1 (by rw [one_smul, hg]))

/-- **The canonical map of top forms is `⋀^r` of the canonical map of differentials**, after the
comparison of exterior powers with pullback. -/
theorem relativeDifferentialFormsMap_eq_exteriorPowerMap {X' X S' S : Scheme.{u}} (f : X' ⟶ X)
    (p : X ⟶ S) (p' : X' ⟶ S') (g : S' ⟶ S) (hcomm : f ≫ p = p' ≫ g) (n : ℤ) :
    Scheme.Hom.relativeDifferentialFormsMap f p p' g hcomm n =
      (Scheme.Modules.exteriorPowerPullbackIso f (Scheme.Hom.relativeDifferentials p) n).hom ≫
        Scheme.Modules.exteriorPowerMap (Scheme.Hom.relativeDifferentialsMap f p p' g hcomm) n :=
  rfl

end Facts

section Surjective

variable {S₀ W : Scheme.{u}} [IsNoetherian W] [AlgebraicGeometry.IsIntegral W]

open Scheme.Modules Stacks.SheafOfModules in
/-- **Off the exceptional divisor, the determinant of `b^*Ω_{W/S₀} ⟶ Ω_{W'/S₀}` is surjective on
stalks**, for `b : W' ⟶ W` the blowing up of a closed point of a regular surface. -/
theorem surjective_mapFun_detMap_blowUp (hreg : AlgebraicGeometry.IsRegular W)
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W))
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (q : W ⟶ S₀) (r : ℕ)
    [((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials q)).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ q)).IsCoherent]
    (U : (AlgebraicGeometry.blowUp (pointIdeal w hw)).Opens)
    (hU : ∃ x : AlgebraicGeometry.blowUp (pointIdeal w hw), x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials q)).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ q)).over U) r]
    (x : AlgebraicGeometry.blowUp (pointIdeal w hw))
    (hx : x ∉ (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)).supportSet) :
    Function.Surjective (Stacks.ModuleStalk.mapFun (detMap
      (Scheme.Hom.relativeDifferentialsMap (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) q
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ q) (𝟙 S₀)
        (Category.comp_id _).symm) (r : ℤ)) x) := by
  haveI : AlgebraicGeometry.IsIntegral (AlgebraicGeometry.blowUp (pointIdeal w hw)) :=
    AlgebraicGeometry.isIntegral_blowUp _
      (Stacks.ResolutionOfSurfaces.vanishingIdeal_singleton_ne_bot hdim w hw)
  haveI : IsNoetherian (AlgebraicGeometry.blowUp (pointIdeal w hw)) :=
    Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _
  haveI : IsLocallyNoetherian (AlgebraicGeometry.blowUp (pointIdeal w hw)) := inferInstance
  have hE : Stacks.Divisors.IsEffectiveCartierDivisor
      (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _
  obtain ⟨hzero, hexact⟩ :=
    Scheme.Hom.toRelativeDifferentials_exact (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) q
  obtain ⟨G, -, ⟨hforms⟩⟩ := exists_forms_iso_pushforward_exceptionalIdeal (pointIdeal w hw)
    (pointIdeal w hw).subschemeι (Scheme.IdealSheafData.ker_subschemeι _) 1
    (Blowup.isFiniteLocallyFreeOfRank_one_relativeDifferentials_exceptionalToCentre_vanishingIdeal
      w hw (hreg.isRegularLocalRing_stalk w) hstalkdim)
  have hsurj : ∀ y, y ∉ (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)).supportSet →
      Function.Surjective (stalkHom (Scheme.Hom.relativeDifferentialsMap
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) q
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ q) (𝟙 S₀)
        (Category.comp_id _).symm) y) := fun y hy =>
    Scheme.Modules.surjective_stalkHom_of_notMem_supportSet (S := ShortComplex.mk _ _ hzero)
      hexact hforms hy
  have := isQuasicoherent_of_isCoherent ((Scheme.Modules.pullback
    (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj (Scheme.Hom.relativeDifferentials q))
  have : (exteriorPower ((Scheme.Modules.pullback
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials q)) (r : ℤ)).IsFinitePresentation :=
    _root_.isFinitePresentation_of_isCoherent _
  have : (exteriorPower (Scheme.Hom.relativeDifferentials
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ q)) (r : ℤ)).IsFinitePresentation :=
    _root_.isFinitePresentation_of_isCoherent _
  have : (dualSheaf (exteriorPower ((Scheme.Modules.pullback
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials q)) (r : ℤ))).IsFinitePresentation :=
    isFinitePresentation_dualSheaf _
  have : (dualSheaf (exteriorPower (Scheme.Hom.relativeDifferentials
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ q)) (r : ℤ))).IsFinitePresentation :=
    isFinitePresentation_dualSheaf _
  exact surjective_mapFun_detMap_of_surjective_of_genericRank _ r U hU
    (hsurj _ (genericPoint_notMem_supportSet_of_isEffectiveCartierDivisor hE)) x (hsurj x hx)

end Surjective

/-- The stalk maps of a composite of morphisms with bijective stalk maps are bijective. -/
theorem bijective_mapFun_comp {X : Scheme.{u}} {F G H : X.Modules} (e : F ⟶ G) (e' : G ⟶ H)
    (x : X) (he : Function.Bijective (Stacks.ModuleStalk.mapFun e x))
    (he' : Function.Bijective (Stacks.ModuleStalk.mapFun e' x)) :
    Function.Bijective (Stacks.ModuleStalk.mapFun (e ≫ e') x) := by
  have : Stacks.ModuleStalk.mapFun (e ≫ e') x =
      Stacks.ModuleStalk.mapFun e' x ∘ Stacks.ModuleStalk.mapFun e x :=
    funext fun m => Stacks.ModuleStalk.mapFun_comp e e' x m
  rw [this]
  exact he'.comp he

/-- The stalk maps of an isomorphism are bijective. -/
theorem bijective_mapFun_of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G) (x : X) :
    Function.Bijective (Stacks.ModuleStalk.mapFun e.hom x) :=
  bijective_mapFun_of_isIso e.hom x

/-- The comparison of the two restrictions along the canonical map to the hull, in an abstract
category. -/
theorem comp_eq_comp_of_restrict {C : Type*} [Category C] {P Q R L' N Mh B : C} (e : P ≅ Q)
    (k : Q ⟶ R) (t' : R ⟶ L') (χ : L' ⟶ N) (u : Q ⟶ Mh) (μ : Mh ⟶ L') (ι : Mh ⟶ B)
    (T : P ⟶ B) (c : B ⟶ B) (s : B ⟶ N) (X : P ⟶ B) (D : P ⟶ R) (hX : X = T ≫ c)
    (hD : D = e.hom ≫ k) (hstar : X ≫ s = D ≫ t' ≫ χ) (h1 : u ≫ μ = k ≫ t')
    (h2 : u ≫ ι = e.inv ≫ T) : u ≫ μ ≫ χ = u ≫ ι ≫ c ≫ s := by
  rw [reassoc_of% h1, reassoc_of% h2, ← Category.assoc T, ← hX, hstar, hD]
  simp

/-- If the pullback of `t` vanishes, so does `t` followed by the adjoint of any morphism out of
the pullback. -/
theorem comp_eq_zero_of_pullback_map_eq_zero {X' X : Scheme.{u}} (b : X' ⟶ X)
    {F L : X.Modules} {N : X'.Modules} (t : F ⟶ L) (s : (Scheme.Modules.pullback b).obj L ⟶ N)
    (τ : L ⟶ (Scheme.Modules.pushforward b).obj N)
    (hτ : τ = (Scheme.Modules.pullbackPushforwardAdjunction b).unit.app L ≫
      (Scheme.Modules.pushforward b).map s)
    (h : (Scheme.Modules.pullback b).map t = 0) : t ≫ τ = 0 := by
  have hnat := (Scheme.Modules.pullbackPushforwardAdjunction b).unit.naturality t
  simp only [Functor.id_map, Functor.comp_map] at hnat
  rw [hτ, ← Category.assoc, hnat, h, Functor.map_zero, comp_zero, zero_comp]

section Core

variable {S₀ S W : Scheme.{u}} [IsNoetherian W] [AlgebraicGeometry.IsIntegral W]

/-- **The comparison at one blowup, with an invertible discrepancy.** Let `b : W' ⟶ W` be the
blowing up of an integral regular Noetherian surface in a closed point whose local ring has
dimension two. There are a morphism `π : Rb_*((Ω^r_{W'/S₀})^{**}[0]) ⟶ (Ω^r_{W/S₀})^{**}[0]` and
an *automorphism* `a` of `(Ω^r_{W/S₀})^{**}` such that `π`, read through the pullback of forms,
is the canonical map `Ω^r_{W/S₀} ⟶ (Ω^r_{W/S₀})^{**}` followed by `a`. -/
theorem exists_isIso_comparison_blowUp (hreg : AlgebraicGeometry.IsRegular W)
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W))
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent]
    (V : W.Opens) (hV : ∃ x : W, x ∈ V)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (h ≫ p)).over V) r]
    (q' : AlgebraicGeometry.blowUp (pointIdeal w hw) ⟶ S₀)
    (hq' : q' = AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p))
    [((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials (h ≫ p))).IsCoherent]
    [(Scheme.Hom.relativeDifferentials q').IsCoherent]
    (U : (AlgebraicGeometry.blowUp (pointIdeal w hw)).Opens)
    (hU : ∃ x : AlgebraicGeometry.blowUp (pointIdeal w hw), x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials (h ≫ p))).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials q').over U) r]
    (branch : ((exceptionalTwistFunctor w hw).obj (pullbackHullExterior p h r w hw) ≅
        reflexiveHull (Scheme.Hom.relativeDifferentialForms q' (r : ℤ))) ⊕
      (pullbackHullExterior p h r w hw ≅
        reflexiveHull (Scheme.Hom.relativeDifferentialForms q' (r : ℤ))))
    [CompactSpace W] [QuasiSeparatedSpace W]
    [CompactSpace (AlgebraicGeometry.blowUp (pointIdeal w hw))]
    [QuasiSeparatedSpace (AlgebraicGeometry.blowUp (pointIdeal w hw))]
    (hL' : (reflexiveHull (Scheme.Hom.relativeDifferentialForms q' (r : ℤ))).IsQuasicoherent)
    (hL : (hullForms p (r : ℤ) h).IsQuasicoherent)
    (wq : AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p) = q' ≫ 𝟙 S₀) :
    ∃ (π : (quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).obj
        (singleQuasiCoherent _ hL' 0) ⟶ singleQuasiCoherent (hullForms p (r : ℤ) h) hL 0)
      (a : hullForms p (r : ℤ) h ⟶ hullForms p (r : ℤ) h), IsIso a ∧
      (DerivedCategory.singleFunctor W.Modules 0).map
          (formsToPushforwardHull (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) (h ≫ p) q'
            wq (r : ℤ)) ≫
        singleToDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) _ ≫
          π.hom =
      (DerivedCategory.singleFunctor W.Modules 0).map
        ((toReflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) (r : ℤ))).1 ≫ a) := by
  subst hq'
  haveI : IsRegularLocalRing (W.presheaf.stalk w) := hreg.isRegularLocalRing_stalk w
  haveI : AlgebraicGeometry.IsIntegral (AlgebraicGeometry.blowUp (pointIdeal w hw)) :=
    AlgebraicGeometry.isIntegral_blowUp _
      (Stacks.ResolutionOfSurfaces.vanishingIdeal_singleton_ne_bot hdim w hw)
  haveI : IsNoetherian (AlgebraicGeometry.blowUp (pointIdeal w hw)) :=
    Stacks.ResolutionOfSurfaces.isNoetherian_blowUp _
  haveI : IsLocallyNoetherian (AlgebraicGeometry.blowUp (pointIdeal w hw)) := inferInstance
  obtain ⟨hregX, hdimX⟩ :=
    AlgebraicGeometry.isRegular_and_topologicalKrullDim_blowUp_vanishingIdeal_singleton
      W hreg hdim w hw
  haveI hEc : Stacks.Divisors.IsEffectiveCartierDivisor
      (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _
  -- The four invertible modules.
  haveI hL1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (hullForms p (r : ℤ) h) 1 :=
    (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one W
      _).mp (isInvertible_hullForms hreg hdim.le p h r V hV)
  haveI hB1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (pullbackHullFormsObj p h r w hw) 1 :=
    AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ 1
  haveI hM1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (pullbackHullExterior p h r w hw) 1 :=
    (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one _
      _).mp (AlgebraicGeometry.isInvertible_reflexiveHull_exteriorPower_of_genericRank _ hregX
        hdimX.le _ r U hU)
  haveI hO1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Divisors.invertibleSheaf'
        (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw))) 1 :=
    Stacks.InvertibleRankOneScheme.isFiniteLocallyFreeOfRank_one_of_isInvertibleModule _ _
  haveI hN1 : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Modules.tensorObj (pullbackHullFormsObj p h r w hw)
        (Stacks.Divisors.invertibleSheaf'
          (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))) 1 := by
    have h1 := @AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_tensorSheaf _
      (pullbackHullFormsObj p h r w hw)
      (Stacks.Divisors.invertibleSheaf' (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))
      1 1 hB1 hO1
    rw [mul_one] at h1
    exact h1
  haveI hLs : Stacks.SheafOfModules.IsInvertible W.presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf W) (hullForms p (r : ℤ) h) :=
    (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one W
      _).mpr hL1
  have hLrefl := isReflexive_of_isInvertible (hullForms p (r : ℤ) h)
  have hBrefl := isReflexive_of_isInvertible.{u} (X := AlgebraicGeometry.blowUp (pointIdeal w hw))
    (pullbackHullFormsObj p h r w hw)
  have hNrefl := isReflexive_of_isInvertible.{u}
    (X := AlgebraicGeometry.blowUp (pointIdeal w hw))
    (Scheme.Modules.tensorObj (pullbackHullFormsObj p h r w hw)
      (Stacks.Divisors.invertibleSheaf' (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw))))
  have hMrefl := isReflexive_of_isInvertible.{u}
    (X := AlgebraicGeometry.blowUp (pointIdeal w hw)) (pullbackHullExterior p h r w hw)
  haveI : IsIso (toReflexiveHull (hullForms p (r : ℤ) h)).1 :=
    (isReflexive_iff_isIso_toReflexiveHull _).mp hLrefl
  haveI : IsIso (toDoubleDual (dualSheaf (dualSheaf
      (Scheme.Hom.relativeDifferentialForms (h ≫ p) (r : ℤ))))) :=
    (isReflexive_iff_isIso_toReflexiveHull _).mp hLrefl
  haveI : IsIso (toDoubleDual (dualSheaf (dualSheaf (Scheme.Modules.exteriorPower
      ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials (h ≫ p))) (r : ℤ))))) :=
    (isReflexive_iff_isIso_toReflexiveHull _).mp hMrefl
  haveI : (hullForms p (r : ℤ) h).IsQuasicoherent := hL
  haveI : (Scheme.Modules.tensorObj (pullbackHullFormsObj p h r w hw)
      (Stacks.Divisors.invertibleSheaf'
        (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  haveI : (pullbackHullFormsObj p h r w hw).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  -- The two comparisons.
  haveI hτ : IsIso (Stacks.DeRham.TwistDerived.twistUnderivedMap
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
      (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)) (hullForms p (r : ℤ) h)) :=
    haveI := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (hullForms p (r : ℤ) h) 1
    Stacks.DeRham.TwistDerived.isIso_twistUnderivedMap _ _ _
      (isIso_exceptionalTwistComparison_pointIdeal w hw hstalkdim)
  haveI := isQuasicoherent_exceptionalTwistPullbackHullForms hreg hdim.le w hw p h r V hV
  haveI hN' : IsIso (singleToDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
      ((exceptionalTwistFunctor w hw).obj (pullbackHullFormsObj p h r w hw))) :=
    isIso_singleToDerivedPushforward_blowUp hdim w hw _
      (isZeroFirstDirectImageBlowUp_exceptionalTwistPullback w hw hstalkdim
        (hullForms p (r : ℤ) h))
  haveI : IsIso (singleToDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
      (Scheme.Modules.tensorObj (pullbackHullFormsObj p h r w hw)
        (Stacks.Divisors.invertibleSheaf'
          (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw))))) := by
    have e := Stacks.DeRham.TwistDerived.pullbackTwistCommIso
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
      (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)) (hullForms p (r : ℤ) h)
    have hn := singleToDerivedPushforward_naturality
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) e.inv
    have hc : IsIso ((DerivedCategory.singleFunctor W.Modules 0).map
          ((Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).map
            e.inv) ≫ singleToDerivedPushforward _ _) := by
      rw [hn]
      exact IsIso.comp_isIso' hN' (inferInstanceAs (IsIso ((derivedPushforward _).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso e)).inv))
    have hf : IsIso ((DerivedCategory.singleFunctor W.Modules 0).map
        ((Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).map
          e.inv)) :=
      inferInstanceAs (IsIso ((DerivedCategory.singleFunctor W.Modules 0).mapIso
        ((Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).mapIso
          e)).inv)
    exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ hf hc
  -- The map `ν` of the branch.
  obtain ⟨ν, hν⟩ : ∃ ν : reflexiveHull (Scheme.Hom.relativeDifferentialForms
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p)) (r : ℤ)) ⟶
      Scheme.Modules.tensorObj (pullbackHullExterior p h r w hw)
        (Stacks.Divisors.invertibleSheaf' (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw))),
      ∀ x, x ∉ (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)).supportSet →
        Function.Bijective (Stacks.ModuleStalk.mapFun ν x) := by
    rcases branch with d | d
    · exact ⟨d.inv ≫ (Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorSheafSchemeCommIso _
        (Stacks.Divisors.invertibleSheaf' (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))
        (pullbackHullExterior p h r w hw)).hom, fun x _ => bijective_mapFun_comp _ _ x
          (bijective_mapFun_of_iso d.symm x)
          (bijective_mapFun_of_iso
            (Stacks.AlgebraicGeometry.TopDegreeBaseChange.tensorSheafSchemeCommIso _
            (Stacks.Divisors.invertibleSheaf'
              (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))
            (pullbackHullExterior p h r w hw)) x)⟩
    · exact ⟨d.inv ≫ Stacks.Divisors.tensorCanonicalSection _ _, fun x hx =>
        bijective_mapFun_comp _ _ x (bijective_mapFun_of_iso d.symm x)
          (bijective_mapFun_tensorCanonicalSection _ _ x hx)⟩
  -- The comparison morphism and its restriction.
  have hι := toReflexiveHull_comp_reflexiveHullExteriorPowerPullbackHom
    (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) hreg hdim.le
    (Scheme.Hom.relativeDifferentials (h ≫ p)) r V hV
  obtain ⟨a, ha⟩ : ∃ a : hullForms p (r : ℤ) h ⟶ hullForms p (r : ℤ) h,
      (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) (r : ℤ))).1 ≫ a =
        formsToPushforwardHull (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) (h ≫ p) _ wq
            (r : ℤ) ≫
          (Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).map
            (ν ≫ Scheme.Modules.tensorRightMap (pullbackHullForms_hom p h hreg hdim w hw r V hV)
              (Stacks.Divisors.invertibleSheaf'
                (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))) ≫
          inv (Stacks.DeRham.TwistDerived.twistUnderivedMap
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
            (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)) (hullForms p (r : ℤ) h)) :=
    ⟨_, toReflexiveHull_comp_extendToReflexive _⟩
  obtain ⟨π, hπ⟩ := exists_comp_singleToDerivedPushforward_eq _ hL hL' _ _ _ _ a ha
  refine ⟨π, a, ?_, hπ⟩
  -- The adjunction step `(★)`.
  have hτ' : Stacks.DeRham.TwistDerived.twistUnderivedMap
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
      (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)) (hullForms p (r : ℤ) h) =
      (Scheme.Modules.pullbackPushforwardAdjunction
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).unit.app (hullForms p (r : ℤ) h) ≫
        (Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).map
          (Stacks.Divisors.tensorCanonicalSection
            (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw))
            (pullbackHullFormsObj p h r w hw)) := rfl
  have hstar : (Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).map
        ((toReflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) (r : ℤ))).1 ≫ a) ≫
        Stacks.Divisors.tensorCanonicalSection
          (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw))
          (pullbackHullFormsObj p h r w hw) =
      Scheme.Hom.relativeDifferentialFormsMap (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (h ≫ p) _ (𝟙 S₀) wq (r : ℤ) ≫
        (toReflexiveHull (Scheme.Hom.relativeDifferentialForms
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p)) (r : ℤ))).1 ≫
        ν ≫ Scheme.Modules.tensorRightMap (pullbackHullForms_hom p h hreg hdim w hw r V hV)
          (Stacks.Divisors.invertibleSheaf'
            (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw))) := by
    refine pullback_map_comp_eq_of_comp_eq _ _ _ _ ?_
    rw [ha, ← hτ', Category.assoc, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    simp only [formsToPushforwardHull, Scheme.Hom.formsDirectImageComparisonOver,
      Functor.map_comp, Category.assoc]
  -- The restriction of the comparison morphism.
  have h2 : (toReflexiveHull (Scheme.Modules.exteriorPower
        ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
          (Scheme.Hom.relativeDifferentials (h ≫ p))) (r : ℤ))).1 ≫
        pullbackHullForms_hom p h hreg hdim w hw r V hV =
      (Scheme.Modules.exteriorPowerPullbackIso (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (Scheme.Hom.relativeDifferentials (h ≫ p)) (r : ℤ)).inv ≫
        (Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).map
          (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) (r : ℤ))).1 := hι
  -- The comparison `(★★)` on the hull.
  have hstar2 : Scheme.Modules.detMap (Scheme.Hom.relativeDifferentialsMap
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) (h ≫ p)
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p)) (𝟙 S₀)
        (Category.comp_id _).symm) (r : ℤ) ≫ ν ≫
        Scheme.Modules.tensorRightMap (pullbackHullForms_hom p h hreg hdim w hw r V hV)
          (Stacks.Divisors.invertibleSheaf'
            (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw))) =
      pullbackHullForms_hom p h hreg hdim w hw r V hV ≫
        (Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).map a ≫
        Stacks.Divisors.tensorCanonicalSection
          (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw))
          (pullbackHullFormsObj p h r w hw) :=
    hom_ext_reflexiveHull hNrefl (comp_eq_comp_of_restrict _ _ _ _ _ _ _ _ _ _ _ _
      (Functor.map_comp _ _ _)
      (relativeDifferentialFormsMap_eq_exteriorPowerMap
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) (h ≫ p)
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p)) (𝟙 S₀) wq (r : ℤ))
      hstar (toDoubleDual_naturality _).symm h2)
  -- `ι` is a monomorphism.
  have hι0 : pullbackHullForms_hom p h hreg hdim w hw r V hV ≠ 0 := by
    intro h0
    have h1 : (Scheme.Modules.exteriorPowerPullbackIso
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (Scheme.Hom.relativeDifferentials (h ≫ p)) (r : ℤ)).inv ≫
        (Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).map
          (toReflexiveHull (Scheme.Hom.relativeDifferentialForms (h ≫ p) (r : ℤ))).1 =
        (Scheme.Modules.exteriorPowerPullbackIso
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (Scheme.Hom.relativeDifferentials (h ≫ p)) (r : ℤ)).inv ≫ 0 := by
      rw [← h2, h0, comp_zero, comp_zero]
    have h3 := (cancel_epi _).mp h1
    have h4 := (comp_eq_zero_of_pullback_map_eq_zero _ _ _ _ hτ' h3).trans
      (zero_comp (f := Stacks.DeRham.TwistDerived.twistUnderivedMap
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)) (hullForms p (r : ℤ) h))).symm
    have : Mono (Stacks.DeRham.TwistDerived.twistUnderivedMap
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
        (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)) (hullForms p (r : ℤ) h)) :=
      IsIso.mono_of_iso _
    have h5 := (cancel_mono _).mp h4
    exact id_ne_zero_of_isInvertibleModule (hullForms p (r : ℤ) h) w
      (hom_ext_reflexiveHull (F := Scheme.Hom.relativeDifferentialForms (h ≫ p) (r : ℤ)) hLrefl
        (by rw [Category.comp_id, comp_zero]; exact h5))
  haveI : Stacks.SheafOfModules.IsInvertible
      (AlgebraicGeometry.blowUp (pointIdeal w hw)).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf _)
      (pullbackHullExterior p h r w hw) :=
    (Stacks.InvertibleRankOneScheme.stacksIsInvertible_iff_isFiniteLocallyFreeOfRank_one _
      _).mpr hM1
  haveI : Mono (pullbackHullForms_hom p h hreg hdim w hw r V hV) :=
    AlgebraicGeometry.mono_of_ne_zero_of_isTorsionFree (isTorsionFree_of_isReflexive _ hBrefl)
      _ hι0
  -- The stalks off the exceptional divisor.
  refine isIso_of_bijective_mapFun_pullback_blowUp w hw hstalkdim _ a fun x hx => ?_
  exact bijective_mapFun_of_comp_eq _ (pullbackHullForms_hom p h hreg hdim w hw r V hV)
    ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).map a) _ ν
    hstar2 x hx (surjective_mapFun_detMap_blowUp hreg hdim w hw hstalkdim (h ≫ p) r U hU x hx)
    (hν x hx)

end Core

end Stacks.BlowupTwistUnit
