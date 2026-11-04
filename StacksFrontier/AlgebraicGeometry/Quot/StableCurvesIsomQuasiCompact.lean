module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyIsomQuasiCompact
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesOpenSubstackQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Quot.ModuliStableCurvesSeparatedQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesForget
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactAffineMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesHomSheafAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubschemeLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomGroupSpace
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedAlgebraicity.IsomSpaceAffine
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedInfinitesimalFiniteDimensional
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.IsomSpaceSurjectiveQuasiCompact

/-!
# The isomorphism spaces of stable curves are quasi-compact, from a polarization

Let `Y`, `X` be stable families of curves over a common base `U`. If stable families carry a
polarization compatible with all morphisms of stable families — for instance the relative
dualizing sheaf, which is relatively ample on a stable family and whose formation commutes with
base change and with isomorphisms — then `Isom_U(Y, X) ⟶ U` is quasi-compact.

The argument. Write `x_Y`, `x_X` for the polarized families of `Y` and `X`. Forgetting the
polarization (Stacks 0D3Y) maps `Isom(x_Y, x_X)` to `Isom(Y, X)`, read in the category of
finitely presented, flat and proper families, which is `Isom_U(Y, X)` because families of curves
are a full subcategory there (Stacks 0D50). The polarization being compatible with all morphisms,
every isomorphism of the restrictions of `Y` and `X` to some `V ⟶ U` lifts to an isomorphism of
the restrictions of `x_Y` and `x_X`, so the map is surjective on sections. `Isom(x_Y, x_X)` is
represented by a scheme affine over `U` (the proof of Stacks 0D42, Stacks 0DPT), hence is
quasi-compact over `U`, and quasi-compactness descends along a surjection.

## Main definitions

* `AlgebraicGeometry.StableCurvesPolarization`: a polarization of stable families of curves
  compatible with their morphisms.

## Main results

* `AlgebraicGeometry.StableCurvesPolarization.isQuasiCompact_relocalizeToYoneda_isomSpace`: the
  isomorphism spaces of two stable objects of the small model of the stack of curves are
  quasi-compact.
* `AlgebraicGeometry.isQuasiSeparated_curvesSmallOpenSubstack_of_stableCurvesPolarization`: an
  open substack of stable curves is quasi-separated over `Spec(ℤ)`.
* `AlgebraicGeometry.isSeparated_moduliStableCurvesOfGenus_of_stableCurvesPolarization`: the
  statement of Stacks 0E9A with the polarization in place of Stacks 0DSS.

## Implementation notes

The polarization is an input. It is what the relative dualizing sheaf provides, by
its compatibility with base change and with isomorphisms and by its relative ampleness on stable
families (Stacks 0E74 with Stacks 0D3D).

## References

* [Stacks Project, Tag 0D3Y](https://stacks.math.columbia.edu/tag/0D3Y)
* [Stacks Project, Tag 0D42](https://stacks.math.columbia.edu/tag/0D42)
* [Stacks Project, Tag 0DPT](https://stacks.math.columbia.edu/tag/0DPT)
* [Stacks Project, Tag 0D50](https://stacks.math.columbia.edu/tag/0D50)
* [Stacks Project, Tag 0DSQ](https://stacks.math.columbia.edu/tag/0DSQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- `Spec(ℤ)` is terminal among the schemes of the site, with the terminal maps of
`AlgebraicGeometry.schemeOverIntegers`. -/
def siteIntegerBaseIsTerminal : IsTerminal (B.obj hZ) :=
  IsTerminal.ofUniqueHom (fun Y => ObjectProperty.homMk (specULiftZIsTerminal.from Y.obj))
    (fun _ _ => ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

/-- Forgetting the polarization (Stacks 0D3Y) is a functor over the big fppf site of `Spec(ℤ)`,
the site being read through `AlgebraicGeometry.polarizedSliceProjection`. -/
theorem forgetPolarization_comp_cartesianProperFlatProjection :
    forgetPolarization B ⋙ cartesianProperFlatProjection B integerBase hZ =
      polarizedSliceProjection B hZ (siteIntegerBaseIsTerminal B hZ) :=
  rfl

/-- **A polarization of stable families of curves, compatible with their morphisms.** To every
stable family of curves `F` it assigns a polarized family `pol F` (Stacks 0D1M) whose underlying
finitely presented, flat and proper family is `F`, through a vertical isomorphism `iso F`, such
that every morphism of stable families — a cartesian square, so a base change followed by an
isomorphism — lifts to a morphism of their polarized families. The relative dualizing sheaf is
such a polarization. -/
structure StableCurvesPolarization where
  /-- The polarized family of a stable family. -/
  pol : (F : CurveFamily B hZ) → IsStableCurveFamily B hZ F → PolarizedFamily B
  /-- Its underlying proper flat family is the family itself. -/
  iso : ∀ F hF, (forgetPolarization B).obj (pol F hF) ≅ (curvesToCartesianProperFlat B hZ).obj F
  /-- The identification lies over the identity of the base. -/
  isHomLift_iso : ∀ F hF, (cartesianProperFlatProjection B integerBase hZ).IsHomLift
    (𝟙 F.base) (iso F hF).hom
  /-- Every morphism of stable families lifts to their polarized families. -/
  lift : ∀ {F G : CurveFamily B hZ} (hF : IsStableCurveFamily B hZ F)
    (hG : IsStableCurveFamily B hZ G) (φ : F ⟶ G), ∃ ψ : pol F hF ⟶ pol G hG,
      (forgetPolarization B).map ψ =
        (iso F hF).hom ≫ (curvesToCartesianProperFlat B hZ).map φ ≫ (iso G hG).inv

namespace StableCurvesPolarization

variable {B hZ} (σ : StableCurvesPolarization B hZ)

local notation "𝒫" => polarizedSliceProjection B hZ (siteIntegerBaseIsTerminal B hZ)
local notation "𝒮" => cartesianProperFlatProjection B integerBase hZ

/-- The projection of polarized families to the big fppf site of `Spec(ℤ)` is fibred. -/
instance : (𝒫).IsFibered :=
  (PolarizedDeformation.isFiberedInGroupoids_polarizedSliceProjection B hZ
    (siteIntegerBaseIsTerminal B hZ)).isFibered

/-- The projection of finitely presented, flat and proper families to their base is fibred. -/
instance : (𝒮).IsFibered :=
  (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ).isFibered

/-- A polarized family is *canonical* when it is isomorphic to the polarized family of a stable
family of curves. -/
def IsCanonical (x : PolarizedFamily B) : Prop :=
  ∃ (F : CurveFamily B hZ) (hF : IsStableCurveFamily B hZ F), Nonempty (x ≅ σ.pol F hF)

/-- **Forgetting the polarization is full between canonical polarized families.** -/
theorem exists_map_eq_of_isCanonical {x y : PolarizedFamily B} (hx : σ.IsCanonical x)
    (hy : σ.IsCanonical y) (t : (forgetPolarization B).obj x ⟶ (forgetPolarization B).obj y) :
    ∃ m : x ⟶ y, (forgetPolarization B).map m = t := by
  obtain ⟨F₁, hF₁, ⟨θ₁⟩⟩ := hx
  obtain ⟨F₂, hF₂, ⟨θ₂⟩⟩ := hy
  let s := (σ.iso F₁ hF₁).inv ≫ (forgetPolarization B).map θ₁.inv ≫ t ≫
    (forgetPolarization B).map θ₂.hom ≫ (σ.iso F₂ hF₂).hom
  have := curvesToCartesianProperFlat_full B hZ
  obtain ⟨φ, hφ⟩ := (curvesToCartesianProperFlat B hZ).map_surjective s
  obtain ⟨ψ, hψ⟩ := σ.lift hF₁ hF₂ φ
  refine ⟨θ₁.hom ≫ ψ ≫ θ₂.inv, ?_⟩
  rw [Functor.map_comp, Functor.map_comp, hψ, hφ]
  simp only [s, Category.assoc, Iso.hom_inv_id_assoc, ← Functor.map_comp_assoc,
    ← Functor.map_comp, Iso.hom_inv_id, Category.comp_id]
  simp

/-- The base of the polarized family `pol F` is the base of `F`. -/
private theorem obj_pol_eq_base (F : CurveFamily B hZ) (hF : IsStableCurveFamily B hZ F) :
    (𝒫).obj (σ.pol F hF) = F.base := by
  have := σ.isHomLift_iso F hF
  exact IsHomLift.domain_eq (𝒮) (𝟙 F.base) (σ.iso F hF).hom

/-- **The chosen pullbacks of canonical polarized families are canonical.** -/
theorem isCanonical_pullbackFiber {U : BigFppfOver B integerBase hZ} (a : (𝒫).Fiber U)
    {F : CurveFamily B hZ} (hF : IsStableCurveFamily B hZ F) (ha : a.1 = σ.pol F hF)
    {V : BigFppfOver B integerBase hZ} (g : V ⟶ U) :
    σ.IsCanonical (Functor.pullbackFiber (𝒫) a g).1 := by
  have hFU : F.base = U := (σ.obj_pol_eq_base F hF).symm.trans (ha ▸ a.2)
  subst hFU
  obtain ⟨F', φ, hb, hφ⟩ := CurveFamily.exists_hom_baseMap_eq F g
  subst hb
  have hF' : IsStableCurveFamily B hZ F' := CurveFamily.isStableCurveFamily_of_hom φ hF
  obtain ⟨ψ, hψ⟩ := σ.lift hF' hF φ
  have hr : (𝒮).IsHomLift (𝟙 F'.base ≫ φ.baseMap ≫ 𝟙 F.base) ((forgetPolarization B).map ψ) := by
    rw [hψ]
    have : (𝒮).IsHomLift φ.baseMap ((curvesToCartesianProperFlat B hZ).map φ) :=
      inferInstanceAs ((𝒮).IsHomLift ((𝒮).map ((curvesToCartesianProperFlat B hZ).map φ)) _)
    have := σ.isHomLift_iso F' hF'
    have : (𝒮).IsHomLift (𝟙 F.base) (σ.iso F hF).inv := by
      have := σ.isHomLift_iso F hF
      infer_instance
    infer_instance
  rw [Category.id_comp, Category.comp_id, hφ, eqToHom_refl, Category.id_comp] at hr
  have hp : (𝒫).IsHomLift g ψ :=
    Functor.isHomLift_of_isHomLift_map_of_comp_eq
      (forgetPolarization_comp_cartesianProperFlatProjection B hZ) _ ψ hr
  have hp' : (𝒫).IsHomLift g (ψ ≫ eqToHom ha.symm) := by
    rw [IsHomLift.eqToHom_comp_lift_iff]
    exact hp
  have : (𝒫).IsCartesian g (ψ ≫ eqToHom ha.symm) :=
    have := (PolarizedDeformation.isFiberedInGroupoids_polarizedSliceProjection B hZ
      (siteIntegerBaseIsTerminal B hZ)).isStronglyCartesian_homLift g (ψ ≫ eqToHom ha.symm)
    inferInstance
  exact ⟨F', hF', ⟨(Functor.IsCartesian.domainUniqueUpToIso (𝒫) g
    (Functor.IsPreFibered.pullbackMap a.2 g) (ψ ≫ eqToHom ha.symm)).symm⟩⟩

attribute [local instance] locallySmall_curveFamily

/-- Forgetting the polarization is a fibred 1-morphism. -/
theorem isFibredOneMorphism_forgetPolarization :
    (𝒫).IsFibredOneMorphism (𝒮) (forgetPolarization B) :=
  { comp_eq := forgetPolarization_comp_cartesianProperFlatProjection B hZ
    map_isStronglyCartesian := fun f _ _ φ _ => by
      have : (𝒮).IsHomLift f ((forgetPolarization B).map φ) :=
        Functor.isHomLift_map_of_comp_eq (p := 𝒫)
          (forgetPolarization_comp_cartesianProperFlatProjection B hZ) f φ
      exact (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ
        ).isStronglyCartesian_homLift f ((forgetPolarization B).map φ) }

/-- The inclusion of the small model of the stack of curves into finitely presented, flat and
proper families (Stacks 0D50). -/
abbrev curvesSmallToCartesianProperFlat :
    (curvesSmall B hZ).val.obj ⥤ CartesianProperFlatSpaces B integerBase hZ :=
  ShrinkHoms.inverse (CurveFamily B hZ) ⋙ curvesToCartesianProperFlat B hZ

/-- The small model of the stack of curves is fibred over the big fppf site of `Spec(ℤ)`. -/
instance : (curvesSmall B hZ).val.p.IsFibered :=
  (curvesSmall B hZ).isFiberedInGroupoids.isFibered

/-- The inclusion of the small model of the stack of curves is a fibred 1-morphism. -/
theorem isFibredOneMorphism_curvesSmallToCartesianProperFlat :
    (curvesSmall B hZ).val.p.IsFibredOneMorphism (𝒮)
      (curvesSmallToCartesianProperFlat (B := B) (hZ := hZ)) :=
  { comp_eq := rfl
    map_isStronglyCartesian := fun f _ _ φ _ => by
      have : (𝒮).IsHomLift f ((curvesSmallToCartesianProperFlat (B := B) (hZ := hZ)).map φ) :=
        Functor.isHomLift_map_of_comp_eq (p := (curvesSmall B hZ).val.p) (q := 𝒮)
          (G := curvesSmallToCartesianProperFlat (B := B) (hZ := hZ)) rfl f φ
      exact (cartesianProperFlatProjection_isFiberedInGroupoids B integerBase hZ
        ).isStronglyCartesian_homLift f
          ((curvesSmallToCartesianProperFlat (B := B) (hZ := hZ)).map φ) }

/-- The isomorphism of the fibre of finitely presented, flat and proper families over `U`
between the underlying family of the polarization of `F` and `F` itself. -/
def fiberIso {U : BigFppfOver B integerBase hZ} (F : CurveFamily B hZ)
    (hF : IsStableCurveFamily B hZ F) (hU : F.base = U)
    (h₁ : (𝒮).obj ((forgetPolarization B).obj (σ.pol F hF)) = U)
    (h₂ : (𝒮).obj ((curvesToCartesianProperFlat B hZ).obj F) = U) :
    (Functor.Fiber.mk h₁ : (𝒮).Fiber U) ≅ Functor.Fiber.mk h₂ := by
  subst hU
  exact Functor.Fiber.isoMk (σ.iso F hF) (σ.isHomLift_iso F hF)

include σ in
/-- **The isomorphism spaces of stable objects of the small model of the stack of curves are
quasi-compact**, given a polarization of stable families compatible with their morphisms and the
algebraicity of the stack of curves (`h`, Stacks 0D5A). For `y₁`, `y₂` over `U`, forgetting the
polarization maps the isomorphism space of their polarized families, which is affine over `U`
(Stacks 0D42, 0DPT), onto `Isom(y₁, y₂)`, surjectively on sections because every isomorphism of
restrictions lifts. -/
theorem isQuasiCompact_relocalizeToYoneda_isomSpace
    (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)
    {U : BigFppfOver B integerBase hZ} (y₁ y₂ : (curvesSmall B hZ).val.p.Fiber U)
    (h₁ : IsStableCurveFamily B hZ (ShrinkHoms.fromShrinkHoms y₁.1 : CurveFamily B hZ))
    (h₂ : IsStableCurveFamily B hZ (ShrinkHoms.fromShrinkHoms y₂.1 : CurveFamily B hZ)) :
    Space.IsQuasiCompact B integerBase hZ (OverShriek.relocalizeToYoneda U.hom
      (Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂)) := by
  let F₁ : CurveFamily B hZ := ShrinkHoms.fromShrinkHoms y₁.1
  let F₂ : CurveFamily B hZ := ShrinkHoms.fromShrinkHoms y₂.1
  have hU₁ : F₁.base = U := y₁.2
  have hU₂ : F₂.base = U := y₂.2
  have hp₁ : (𝒫).obj (σ.pol F₁ h₁) = U := (σ.obj_pol_eq_base F₁ h₁).trans hU₁
  have hp₂ : (𝒫).obj (σ.pol F₂ h₂) = U := (σ.obj_pol_eq_base F₂ h₂).trans hU₂
  let a₁ : (𝒫).Fiber U := ⟨σ.pol F₁ h₁, hp₁⟩
  let a₂ : (𝒫).Fiber U := ⟨σ.pol F₂ h₂, hp₂⟩
  have hF := isFibredOneMorphism_forgetPolarization (B := B) (hZ := hZ)
  have hC := isFibredOneMorphism_curvesSmallToCartesianProperFlat (B := B) (hZ := hZ)
  have := curvesToCartesianProperFlat_full B hZ
  have := curvesToCartesianProperFlat_faithful B hZ
  let M₁ := Stack.liftedMorPresheafMap.{_, _, _, _, _, u + 1} hF a₁ a₂
  have hff : (curvesSmallToCartesianProperFlat (B := B) (hZ := hZ)).FullyFaithful :=
    (ShrinkHoms.equivalence.{u} (CurveFamily B hZ)).fullyFaithfulInverse.comp
      (Functor.FullyFaithful.ofFullyFaithful (curvesToCartesianProperFlat B hZ))
  have : (curvesSmallToCartesianProperFlat (B := B) (hZ := hZ)).Full := hff.full
  have : (curvesSmallToCartesianProperFlat (B := B) (hZ := hZ)).Faithful := hff.faithful
  let M₃ := @asIso _ _ _ _ (Stack.liftedMorPresheafMap.{_, _, _, _, _, u + 1} hC y₁ y₂)
    (Stack.isIso_liftedMorPresheafMap.{_, _, _, _, _, u + 1} hC y₁ y₂)
  let e := Functor.morPresheafFiberIso (𝒮) (σ.fiberIso F₁ h₁ hU₁ hp₁ y₁.2)
    (σ.fiberIso F₂ h₂ hU₂ hp₂ y₂.2)
  let α := M₁ ≫ e.hom ≫ M₃.inv
  have hα : ∀ g, Function.Surjective (α.app g) := by
    intro g
    have h1 : Function.Surjective (M₁.app g) :=
      Stack.surjective_liftedMorPresheafMap_app hF a₁ a₂ g fun t =>
        σ.exists_map_eq_of_isCanonical (σ.isCanonical_pullbackFiber a₁ h₁ rfl g.unop.hom)
          (σ.isCanonical_pullbackFiber a₂ h₂ rfl g.unop.hom) t
    have h2 : Function.Surjective ((e.hom ≫ M₃.inv).app g) :=
      ((e ≪≫ M₃.symm).app g).toEquiv.surjective
    rw [NatTrans.comp_app]
    exact h2.comp h1
  let α₀ : (𝒫).morPresheaf a₁ a₂ ⟶ (curvesSmall B hZ).val.p.morPresheaf y₁ y₂ :=
    { app := fun g => ↾fun x => ((α.app g) (ULift.up x)).down
      naturality := fun g g' f => by
        ext x
        have := congrArg ULift.down (NatTrans.naturality_apply α f
          (show ((𝒫).morPresheaf a₁ a₂ ⋙ uliftFunctor.{u + 1}).obj g from ULift.up x))
        exact this }
  have hα₀ : ∀ g, Function.Surjective (α₀.app g) := fun g x => by
    obtain ⟨z, hz⟩ := hα g (ULift.up x)
    exact ⟨z.down, congrArg ULift.down hz⟩
  have hPg := PolarizedDeformation.isFiberedInGroupoids_polarizedSliceProjection B hZ
    (siteIntegerBaseIsTerminal B hZ)
  let β' := (Stack.morPresheafIsoIsomPresheaf (𝒫) hPg a₁ a₂).inv ≫ α₀ ≫
    (Stack.morPresheafIsoIsomPresheaf (curvesSmall B hZ).val.p
      (curvesSmall B hZ).isFiberedInGroupoids y₁ y₂).hom
  have hβ' : ∀ g, Function.Surjective (β'.app g) := by
    intro g
    simp only [β', NatTrans.comp_app]
    exact (((Stack.morPresheafIsoIsomPresheaf _ _ y₁ y₂).app g).toEquiv.surjective.comp
      (hα₀ g)).comp ((Stack.morPresheafIsoIsomPresheaf (𝒫) hPg a₁ a₂).symm.app g).toEquiv.surjective
  let β : Stack.isomSpace B integerBase hZ (polarizedStackUnconditional B hZ
      (siteIntegerBaseIsTerminal B hZ)) U a₁ a₂ ⟶
      Stack.isomSpace B integerBase hZ (curvesSmall B hZ) U y₁ y₂ :=
    Functor.whiskerLeft (Over.iteratedSliceBackward U).op β'
  obtain ⟨R, eR, -⟩ :=
    PolarizedAlgebraicity.exists_iso_yoneda_isAffineHom_polarizedIsomSpace B hZ
      (siteIntegerBaseIsTerminal B hZ) U a₁ a₂
  have hA := isAlgebraicSpace_of_iso B U.left.1 U.left.2 eR
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 R)
  have hB := Stack.isAlgebraicSpace_isomSpace B integerBase hZ (curvesSmall B hZ)
    ((isAlgebraicStack_curvesSmall_iff B hZ).2 h) U y₁ y₂
  have hqcA := (Space.isQuasiCompact_relocalizeToYoneda_iff B U.left.1 integerBase U.left.2 hZ
    U.hom _).1 (PolarizedAlgebraicity.isQuasiCompact_relocalizeToYoneda_polarizedIsomSpace B hZ
      (siteIntegerBaseIsTerminal B hZ) U a₁ a₂)
  refine (Space.isQuasiCompact_relocalizeToYoneda_iff B U.left.1 integerBase U.left.2 hZ
    U.hom _).2 ?_
  refine Space.isQuasiCompact_of_surjective_app_comp B U.left.1 U.left.2 hA hB
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 _) β _ (fun g => hβ' _) ?_
  convert hqcA using 1
  ext T x
  rfl

end StableCurvesPolarization

variable (h : Stack.IsAlgebraicStack.{u, w} B integerBase hZ (curvesFiberedCategory B hZ).val)

/-- **An open substack of stable curves is quasi-separated over `Spec(ℤ)`, from a polarization.**
Let `P` cut out an open substack `Curves^P` of the small model of the stack of curves consisting of
stable families (`hPs`). Given the algebraicity of the stack of curves (`h`, Stacks 0D5A) and a
polarization of stable families compatible with their morphisms (`σ`), `Curves^P → Spec(ℤ)` is
quasi-separated (Stacks 04YW). -/
theorem isQuasiSeparated_curvesSmallOpenSubstack_of_stableCurvesPolarization
    {P : ObjectProperty (CurveFamily B hZ)} (hP : IsOpenCurvesLocus B hZ P)
    (hPs : ∀ F, P F → IsStableCurveFamily B hZ F) (σ : StableCurvesPolarization B hZ) :
    Stack.AlgebraicStacks.IsQuasiSeparated B integerBase hZ
      ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) :=
  isQuasiSeparated_curvesSmallOpenSubstack_of_isQuasiCompact_isomSpace B hZ h hP
    fun y₁ y₂ h₁ h₂ => σ.isQuasiCompact_relocalizeToYoneda_isomSpace h y₁ y₂ (hPs _ h₁) (hPs _ h₂)

/-- **The statement of Stacks 0E9A, from a polarization of stable curves.** Let `g ≥ 2`, and let
`𝓜̄_g` and `𝓜_g` be the open substacks of the small model of the stack of curves cut out by being
stable of genus `g` (`hP`) and by being smooth with `f_*𝒪_X = 𝒪_S` universally and of genus `g`
(`hQ`). Given the algebraicity (`h`, Stacks 0D5A) and the limit preservation (`hlim`, Stacks 0D55)
of the stack of curves, a polarization of stable families compatible with their morphisms (`σ`,
which the relative dualizing sheaf provides), the density of `|𝓜_g|` in `|𝓜̄_g|` (`h0E87`, Stacks
0E87) and the uniqueness of stable models (`h0E97`, Stacks 0E97), `𝓜̄_g → Spec(ℤ)` is separated.
-/
theorem isSeparated_moduliStableCurvesOfGenus_of_stableCurvesPolarization (g : ℕ) (hg : 2 ≤ g)
    (hP : IsOpenCurvesLocus B hZ (IsStableCurveFamilyOfGenus B hZ g))
    (hQ : IsOpenCurvesLocus B hZ
      (fun X => IsSmoothH0Family B hZ X ∧ CurveFamily.HasGenus B hZ X g))
    (hlim : Deformation.Artin.IsLimitPreserving.{u, u, u, u + 1, u + 1} B integerBase hZ
      (curvesFiberedCategory B hZ))
    (σ : StableCurvesPolarization B hZ)
    (h0E87 : @Dense _ (Stack.pointTopology B integerBase hZ
        (curvesSmallOpenSubstack B hZ h hP).toAlgebraicStack.val)
      (Stack.AlgebraicStacks.pointsMap B integerBase hZ
          (curvesSmallOpenSubstack B hZ h hP).inclusion ⁻¹'
        (curvesSmallOpenSubstack B hZ h hQ).pointSet B integerBase hZ))
    (h0E97 : UniqueStableModels B hZ g) :
    Stack.AlgebraicStacks.IsSeparated B integerBase hZ
      ((curvesSmallOpenSubstack B hZ h hP).inclusion ≫
        Stack.structureMorphism B integerBase hZ (curvesAlgebraicStack B hZ h)) :=
  isSeparated_moduliStableCurvesOfGenus_of_isQuasiSeparated B hZ h g hg hP hQ hlim
    (isQuasiSeparated_curvesSmallOpenSubstack_of_stableCurvesPolarization B hZ h hP
      (fun _ hF => hF.1) σ) h0E87 h0E97

end AlgebraicGeometry

end
