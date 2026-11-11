module

public import StacksFrontier.AlgebraicGeometry.Thickenings.SquareZeroExtension.OfDifferentialsExtension
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationConormal
public import StacksFrontier.Deformation.Examples.Geometric.SpacesTangentSpaceSurjectiveFlatDualNumbersChart
public import StacksFrontier.Deformation.Examples.Geometric.OpenSubschemes
public import StacksFrontier.Deformation.VersalObject.MinimalVersalOrbitBijection
public import StacksFrontier.AlgebraicGeometry.CurveDegreeInvariance.Morphism

/-!
# The first-order deformation attached to an extension of the differentials by `𝒪_X`

Let `X` be a scheme over a field `k` with structure morphism `f`, and let
`0 ⟶ 𝒪_X ⟶ 𝓔 ⟶ Ω_{X/k} ⟶ 0` be a short exact sequence of `𝒪_X`-modules. The first-order
thickening `X ⊂ X'` over `k` with `𝒪_{X'} = 𝒪_X ×_{Ω_{X/k}} 𝓔`
(`Stacks.Thickenings.DifferentialsExtension.differentialsThickening`) carries the global function
`ε = (0, 1)`, with `ε² = 0`, so `X'` maps to `Spec k[ε]`. On every affine open `U` the ring
`𝒪_{X'}(U)` is an extension of `𝒪_X(U)` with ideal `ε 𝒪_X(U) ≅ 𝒪_X(U)`, so `X' ⟶ Spec k[ε]` is flat
with closed fibre `X`: `X'` is a deformation of `X` over `k[ε]` in the sense of
[Stacks Project, Tag 0DY7].

## Main definitions

* `Deformation.Examples.thickeningToDualNumbers`: the morphism `X' ⟶ Spec k[ε]`.
* `Deformation.Examples.differentialsExtensionDeformation`: the deformation `X'` of `X` over `k[ε]`.

## Main results

* `Deformation.Examples.flat_and_isPullback_thickeningToDualNumbers`: `X' ⟶ Spec k[ε]` is flat
  and its fibre over the closed point is `X`.

## References

* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 063Y](https://stacks.math.columbia.edu/tag/063Y)
* [Stacks Project, Tag 05YV](https://stacks.math.columbia.edu/tag/05YV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AlgebraicGeometry.SheafOfModules Stacks.Thickenings Stacks.Thickenings.DifferentialsExtension

universe u

namespace Deformation.Examples

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  {E : X.Modules} {j : Scheme.Modules.unitModule X ⟶ E}
  {p : E ⟶ Scheme.Hom.relativeDifferentials f} (w : j ≫ p = 0)
  (hT : (ShortComplex.mk j p w).ShortExact)

/-- The function `ε = (0, 1)` on the thickening attached to `0 ⟶ 𝒪_X ⟶ 𝓔 ⟶ Ω_{X/k} ⟶ 0`. -/
def thickeningEpsilon : Γ(differentialsThickening w hT, ⊤) :=
  extensionKernelInclusion w (op ⊤) (1 : Γ(X, ⊤))

/-- `ε² = 0`. -/
theorem thickeningEpsilon_mul_self : thickeningEpsilon w hT * thickeningEpsilon w hT = 0 :=
  extensionKernelInclusion_square_zero w _ _ _

/-- The constants `k ⟶ Γ(X', 𝒪_{X'})`, through the structure morphism `X' ⟶ Spec k`. -/
def thickeningConstants : k →+* Γ(differentialsThickening w hT, ⊤) :=
  ((differentialsThickeningToBase w hT).appTop).hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom

/-- **The ring map `k[ε] ⟶ Γ(X', 𝒪_{X'})`**, `a + b ε ↦ a + b ε`. -/
def dualNumbersToSections : DualNumber k →+* Γ(differentialsThickening w hT, ⊤) where
  toFun x :=
    thickeningConstants w hT x.fst + thickeningConstants w hT x.snd * thickeningEpsilon w hT
  map_one' := by
    rw [TrivSqZeroExt.fst_one, TrivSqZeroExt.snd_one, map_one, map_zero, zero_mul, add_zero]
  map_mul' x y := by
    rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, map_mul, map_add, map_mul, map_mul]
    linear_combination (-(thickeningConstants w hT x.snd * thickeningConstants w hT y.snd)) *
      thickeningEpsilon_mul_self w hT
  map_zero' := by
    rw [TrivSqZeroExt.fst_zero, TrivSqZeroExt.snd_zero, map_zero, zero_mul, add_zero]
  map_add' x y := by
    rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add, map_add]
    ring

/-- `k[ε] ⟶ Γ(X', 𝒪_{X'})`, on the dual-numbers object of `𝒞_k`. -/
def thickeningDualNumbersHom :
    CommRingCat.of (Deformation.artinianDualNumbers.{u, u, u} k k) ⟶
      Scheme.Γ.obj (op (differentialsThickening w hT)) :=
  CommRingCat.ofHom (R := Deformation.artinianDualNumbers.{u, u, u} k k)
    (S := Γ(differentialsThickening w hT, ⊤)) ((dualNumbersToSections w hT).comp
      (artinianDualNumbersCoordinate (Λ := k) (k := k)).toRingEquiv.toRingHom)

/-- **The morphism `X' ⟶ Spec k[ε]`** whose pullback of functions is
`Deformation.Examples.dualNumbersToSections`. -/
def thickeningToDualNumbers :
    differentialsThickening w hT ⟶ baseSpec (Deformation.artinianDualNumbers.{u, u, u} k k) :=
  (ΓSpec.adjunction.homEquiv (differentialsThickening w hT)
    (op (CommRingCat.of (Deformation.artinianDualNumbers.{u, u, u} k k))))
    (thickeningDualNumbersHom w hT).op

/-- The pullback of functions along `X' ⟶ Spec k[ε]` is `thickeningDualNumbersHom`. -/
theorem ΓSpecIso_inv_comp_thickeningToDualNumbers_appTop :
    (Scheme.ΓSpecIso (.of (Deformation.artinianDualNumbers.{u, u, u} k k))).inv ≫
        (thickeningToDualNumbers w hT).appTop =
      thickeningDualNumbersHom w hT :=
  ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _

/-- The pullback of functions along `X' ⟶ Spec k[ε]`. -/
theorem thickeningToDualNumbers_appTop (a : Deformation.artinianDualNumbers.{u, u, u} k k) :
    (thickeningToDualNumbers w hT).appTop.hom
        ((Scheme.ΓSpecIso (.of (Deformation.artinianDualNumbers.{u, u, u} k k))).inv.hom a) =
      dualNumbersToSections w hT (artinianDualNumbersCoordinate (Λ := k) (k := k) a) :=
  ConcreteCategory.congr_hom (ΓSpecIso_inv_comp_thickeningToDualNumbers_appTop w hT) a

/-- The reduction of `a + b ε` to `X` is `a`. -/
theorem differentialsThickeningι_appTop_dualNumbersToSections (x : DualNumber k) :
    (differentialsThickeningι w hT).appTop.hom (dualNumbersToSections w hT x) =
      f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom x.fst) := by
  have hc : ∀ a : k, (differentialsThickeningι w hT).appTop.hom (thickeningConstants w hT a) =
      f.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a) := fun a =>
    congrArg (fun g : X ⟶ Spec (.of k) => g.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a))
      (differentialsThickeningι_comp_toBase w hT)
  have hε : (differentialsThickeningι w hT).appTop.hom (thickeningEpsilon w hT) = 0 :=
    extensionKernelInclusion_mem_kernel w _ _
  have hx : dualNumbersToSections w hT x =
      thickeningConstants w hT x.fst + thickeningConstants w hT x.snd * thickeningEpsilon w hT :=
    rfl
  rw [hx, map_add, map_mul, hε, mul_zero, add_zero, hc]

/-- The residue map of the dual numbers object is the first coordinate. -/
theorem residueMap_artinianDualNumbers (a : Deformation.artinianDualNumbers.{u, u, u} k k) :
    Deformation.Artin.residueMap (Deformation.artinianDualNumbers.{u, u, u} k k) a =
      (artinianDualNumbersCoordinate (Λ := k) (k := k) a).fst :=
  (Deformation.squareZeroExtensionArtinian_residue k k (FGModuleCat.of k (ULift.{u} k)) a).trans
    (Deformation.dualNumbersEquiv_fst a).symm

/-- **`X ⟶ X' ⟶ Spec k[ε]` is `X ⟶ Spec k ⟶ Spec k[ε]`.** -/
theorem differentialsThickeningι_comp_thickeningToDualNumbers :
    differentialsThickeningι w hT ≫ thickeningToDualNumbers w hT =
      f ≫ residueSpecMap (Deformation.artinianDualNumbers.{u, u, u} k k) := by
  apply ext_to_Spec
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  change (differentialsThickeningι w hT).appTop.hom ((thickeningToDualNumbers w hT).appTop.hom
      ((Scheme.ΓSpecIso _).inv.hom a)) =
    f.appTop.hom ((residueSpecMap _).appTop.hom ((Scheme.ΓSpecIso _).inv.hom a))
  rw [thickeningToDualNumbers_appTop, differentialsThickeningι_appTop_dualNumbersToSections]
  have hnat := congrArg (fun g => g.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (Deformation.Artin.residueMap (Deformation.artinianDualNumbers.{u, u, u} k k))))
  change (Scheme.ΓSpecIso (.of k)).inv.hom (Deformation.Artin.residueMap _ a) =
    (residueSpecMap _).appTop.hom ((Scheme.ΓSpecIso _).inv.hom a) at hnat
  rw [← hnat, residueMap_artinianDualNumbers]

/-- **`X' ⟶ Spec k[ε] ⟶ Spec k` is the structure morphism `X' ⟶ Spec k`.** -/
theorem thickeningToDualNumbers_comp_structure :
    thickeningToDualNumbers w hT ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap k (Deformation.artinianDualNumbers.{u, u, u} k k))) =
      differentialsThickeningToBase w hT := by
  apply ext_to_Spec
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  change (thickeningToDualNumbers w hT).appTop.hom ((Spec.map (CommRingCat.ofHom
      (algebraMap k (Deformation.artinianDualNumbers.{u, u, u} k k)))).appTop.hom
        ((Scheme.ΓSpecIso _).inv.hom a)) = thickeningConstants w hT a
  have hnat := congrArg (fun g => g.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (algebraMap k (Deformation.artinianDualNumbers.{u, u, u} k k))))
  change (Scheme.ΓSpecIso _).inv.hom (algebraMap k _ a) =
    (Spec.map _).appTop.hom ((Scheme.ΓSpecIso _).inv.hom a) at hnat
  rw [← hnat, thickeningToDualNumbers_appTop, AlgEquiv.commutes]
  have hx : dualNumbersToSections w hT (algebraMap k (DualNumber k) a) =
      thickeningConstants w hT a + thickeningConstants w hT 0 * thickeningEpsilon w hT :=
    rfl
  rw [hx, map_zero, zero_mul, add_zero]

/-- The coordinate `k[ε] ≅ Γ(Spec k[ε], 𝒪)`. -/
abbrev dualNumbersBaseEquiv :
    TrivSqZeroExt k k ≃+* Γ(baseSpec (Deformation.artinianDualNumbers.{u, u, u} k k), ⊤) :=
  (baseSpecCoordinate (artinianDualNumbersCoordinate (Λ := k) (k := k))).symm

/-- `ε` pulls back to `ε` on `X'`. -/
theorem thickeningToDualNumbers_appTop_epsilon :
    (thickeningToDualNumbers w hT).appTop.hom (dualNumbersBaseEquiv (TrivSqZeroExt.inr 1)) =
      thickeningEpsilon w hT := by
  have h := thickeningToDualNumbers_appTop w hT
    ((artinianDualNumbersCoordinate (Λ := k) (k := k)).symm (TrivSqZeroExt.inr 1))
  rw [AlgEquiv.apply_symm_apply] at h
  refine h.trans ?_
  have hx : dualNumbersToSections w hT (TrivSqZeroExt.inr 1) =
      thickeningConstants w hT 0 + thickeningConstants w hT 1 * thickeningEpsilon w hT :=
    rfl
  rw [hx, map_zero, map_one, zero_add, one_mul]

/-- The function `ε` restricts to `ε` on every open. -/
theorem thickeningEpsilon_map (O : (differentialsThickening w hT).Opens) :
    (differentialsThickening w hT).presheaf.map (homOfLE le_top).op (thickeningEpsilon w hT) =
      extensionKernelInclusion w (op O) (1 : Γ(X, O)) :=
  (extensionKernelInclusion_naturality w (homOfLE le_top).op _).symm.trans
    (congrArg (extensionKernelInclusion w (op O))
      (PresheafOfModules.unit_map_one _ (homOfLE (le_top : O ≤ ⊤)).op))

/-- **`X' ⟶ Spec k[ε]` is flat and its fibre over the closed point is `X`.** On an affine open
`O` of `X'`, `𝒪_{X'}(O)` is an extension of `𝒪_X(O)` with ideal `ε 𝒪_X(O) ≅ 𝒪_X(O)`. -/
theorem flat_and_isPullback_thickeningToDualNumbers :
    Flat (thickeningToDualNumbers w hT) ∧
      IsPullback (differentialsThickeningι w hT) f (thickeningToDualNumbers w hT)
        (residueSpecMap (Deformation.artinianDualNumbers.{u, u, u} k k)) := by
  have := isClosedImmersion_differentialsThickeningι w hT
  have := residueSpecMap_isClosedImmersion (Deformation.artinianDualNumbers.{u, u, u} k k)
  refine flat_and_isPullback_of_dualNumbers_chart (differentialsThickeningι w hT)
    (residueSpecMap _) f (thickeningToDualNumbers w hT)
    (differentialsThickeningι_comp_thickeningToDualNumbers w hT) dualNumbersBaseEquiv
    (fun a => (residueSpecMap_app_eq_zero_iff _
      (artinianDualNumbersCoordinate (Λ := k) (k := k)) _).trans
      (by rw [RingEquiv.apply_symm_apply])) fun O hO hOV => ?_
  have hOX : IsAffineOpen (differentialsThickeningι w hT ⁻¹ᵁ O) :=
    hO.preimage (differentialsThickeningι w hT)
  have hinj : Function.Injective (extensionKernelInclusion w (op O)) := fun d d' h => by
    obtain ⟨_, -, huniq⟩ := extensionKernelInclusion_exact w hT (op O)
      (extensionKernelInclusion w (op O) d) (extensionKernelInclusion_mem_kernel w _ _)
    exact (huniq d rfl).trans (huniq d' h.symm).symm
  refine ⟨squareZero_sectionMap_surjective_of_affine _ _ hOX,
    extensionKernelInclusion w (op O), hinj, fun c => ?_, fun c hc => ?_, fun d => ?_,
    fun d d' => extensionKernelInclusion_square_zero w _ d d'⟩
  · have hε : (thickeningToDualNumbers w hT).appLE ⊤ O hOV
        (dualNumbersBaseEquiv (TrivSqZeroExt.inr 1)) =
          extensionKernelInclusion w (op O) (1 : Γ(X, O)) :=
      (congrArg ((differentialsThickening w hT).presheaf.map (homOfLE hOV).op).hom
        (thickeningToDualNumbers_appTop_epsilon w hT)).trans (thickeningEpsilon_map w hT O)
    refine (congrArg (· * c) hε).trans ((mul_comm _ _).trans ?_)
    refine (extensionKernelInclusion_smul w (op O) c (1 : Γ(X, O))).symm.trans ?_
    exact congrArg (extensionKernelInclusion w (op O))
      (mul_one (((differentialsThickeningι w hT).app O).hom c))
  · obtain ⟨d, hd, -⟩ := extensionKernelInclusion_exact w hT (op O) c hc
    exact ⟨d, hd⟩
  · exact extensionKernelInclusion_mem_kernel w _ _

/-- **The first-order deformation of `X` over `k[ε]` attached to `0 ⟶ 𝒪_X ⟶ 𝓔 ⟶ Ω_{X/k} ⟶ 0`**,
as an object of the deformation category of `X` ([Stacks Project, Tag 0DY7]). -/
def differentialsExtensionDeformation :
    SchemeDeformationCategory (Λ := k) (k := k) (Over.mk f) where
  base := Deformation.artinianDualNumbers.{u, u, u} k k
  scheme := differentialsThickening w hT
  toBase := thickeningToDualNumbers w hT
  flat := (flat_and_isPullback_thickeningToDualNumbers w hT).1
  specialMap := differentialsThickeningι w hT
  specialCartesian := (flat_and_isPullback_thickeningToDualNumbers w hT).2

end Deformation.Examples

end
