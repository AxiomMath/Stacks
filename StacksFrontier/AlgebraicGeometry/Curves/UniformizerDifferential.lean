module

public import Mathlib.RingTheory.Etale.Field
public import StacksFrontier.AlgebraicGeometry.RelativeDifferentialStalkMap.Scheme
public import StacksFrontier.AlgebraicGeometry.SmoothAtJacobian.Conditions
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.RingTheory.Kaehler.BaseChange
public import StacksFrontier.RingTheory.Kaehler.Uniformizer
public import StacksCore.Tactic.StacksAttribute

/-!
# The differential of a uniformizer on a smooth curve

Let `X` be a scheme over a field `k`, smooth at a closed point `x` with one-dimensional fibre
through `x` and with separable residue field at `x`. Then the stalk at `x` of the sheaf of
relative differentials of `X` over `k` is free of rank one, and the differential of any
uniformizer of the local ring `𝒪_{X,x}` is a basis of it.

## Main results

* `AlgebraicGeometry.differential_uniformizer_basis`: the germ of the universal differential of a
  local section representing a uniformizer freely generates the stalk of relative differentials.

## Implementation notes

A uniformizer is specified by the equation `maximalIdeal 𝒪_{X,x} = Ideal.span {s}`, and a local
section `a` representing `s` is supplied together with the equation on germs; every element of a
stalk admits such a representative. Smoothness of relative dimension one at `x` is expressed by
`AlgebraicGeometry.InfinitesimalLifting.SmoothAt` together with local dimension one of the
scheme-theoretic fibre through `x`. Freeness is stated as a linear equivalence
`𝒪_{X,x} ≃ₗ[𝒪_{X,x}] Ω_{X⁄k, x}` carrying `1` to the prescribed differential, which records the
generator rather than an unspecified basis vector.

The base ring of the differentials is changed from the local ring `𝒪_{Spec k, f x}` of the base,
over which `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv` states
the identification of the stalk, to `k` itself; the comparison is an isomorphism because the
structure sheaf of `Spec k` has constant stalk `k`, so `𝒪_{Spec k, f x}` is a localization of `k`
at the trivial submonoid.

## References

* [Stacks Project, Tag 0C1E](https://stacks.math.columbia.edu/tag/0C1E)
-/

@[expose] public section

open CategoryTheory TopologicalSpace IsLocalRing Opposite
open Stacks.RelativeDifferentialStalk Stacks.RelativeDifferentialStalkMap
open Stacks.SmoothAtJacobian
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The germ at a point of the structure sheaf of the spectrum of a field, out of the whole
space, is an isomorphism: the spectrum of a field is a single point, at which the stalk is the
field itself. -/
theorem isIso_germ_top_spec_field {k : Type u} [Field k] (x : Spec (.of k)) :
    IsIso ((Spec (.of k)).presheaf.germ ⊤ x trivial) := by
  obtain rfl : x = closedPoint k := Subsingleton.elim _ _
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv]
  infer_instance

/-- The identification of a field with the local ring of its spectrum at a point. -/
noncomputable def specFieldStalkIso {k : Type u} [Field k] (x : Spec (.of k)) :
    CommRingCat.of k ≅ (Spec (.of k)).presheaf.stalk x :=
  have := isIso_germ_top_spec_field x
  (Scheme.ΓSpecIso (.of k)).symm ≪≫ asIso ((Spec (.of k)).presheaf.germ ⊤ x trivial)

/-- `AlgebraicGeometry.specFieldStalkIso` followed by the stalk map of a morphism to the spectrum
of a field is the `k`-algebra structure that the global sections of the structure morphism induce
on the local ring of the source. -/
theorem specFieldStalkIso_hom_comp_stalkMap {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    (specFieldStalkIso (f x)).hom ≫ f.stalkMap x =
      (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial := by
  have hhom : (specFieldStalkIso (f x)).hom =
      (Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).presheaf.germ ⊤ (f x) trivial := rfl
  rw [hhom, Category.assoc]
  congr 1
  simpa using Scheme.Hom.germ_stalkMap f ⊤ x trivial

/-- **The stalk map of a morphism smooth at a point is essentially of finite type.** Smoothness
at `x` gives an open neighbourhood on which the morphism is smooth, hence locally of finite type,
and the stalk map is unchanged by restriction to it. -/
theorem smoothAt_stalk_essFiniteType {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) (hsm : InfinitesimalLifting.SmoothAt f x) :
    (f.stalkMap x).hom.EssFiniteType := by
  obtain ⟨W, hxW, hW⟩ := hsm
  let g := f.resLE ⊤ W le_top
  let y : W.toScheme := ⟨x, hxW⟩
  have : Smooth g := hW
  exact (RingHom.EssFiniteType.respectsIso.arrow_mk_iso_iff
    (f.resLEStalkMap (U := ⊤) (V := W) le_top y)).mp
      (LocallyOfFiniteType.stalkMap g y)

/-- **At a point where a scheme over a field is smooth, its local ring is essentially of finite
type and formally smooth over the field.** Both properties transport from the stalk map of the
structure morphism along `AlgebraicGeometry.specFieldStalkIso`. -/
theorem smoothAt_field_stalk_properties {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (hsm : InfinitesimalLifting.SmoothAt f x) :
    letI : Algebra k (X.presheaf.stalk x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x trivial).hom.toAlgebra
    Algebra.EssFiniteType k (X.presheaf.stalk x) ∧
      Algebra.FormallySmooth k (X.presheaf.stalk x) := by
  rw [← specFieldStalkIso_hom_comp_stalkMap f x]
  let e := (specFieldStalkIso (f x)).commRingCatIsoToRingEquiv
  change RingHom.EssFiniteType _ ∧ RingHom.FormallySmooth _
  exact ⟨RingHom.EssFiniteType.respectsIso.right _ e (smoothAt_stalk_essFiniteType f x hsm),
    RingHom.FormallySmooth.respectsIso.right _ e
      (InfinitesimalLifting.SmoothAt.formallySmooth_stalkMap f x hsm)⟩

/-- **The scheme-theoretic fibre of a morphism to the spectrum of a field is the whole source**,
so local dimension is computed in either. -/
theorem topologicalKrullDimAt_fiber_eq {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = topologicalKrullDimAt X x := by
  let e : (f ⁻¹' {f x}) ≃ₜ X :=
    (Homeomorph.setCongr (by ext z; simp [Subsingleton.elim (f z) (f x)])).trans
      (Homeomorph.Set.univ X)
  have he : e ((f.fiberHomeo (f x)) (f.asFiber x)) = x := f.fiberι_asFiber x
  simpa only [Homeomorph.trans_apply, he] using topologicalKrullDimAt_eq_of_homeomorph
    ((f.fiberHomeo (f x)).trans e) (f.asFiber x)

/-- **At a closed point of a scheme over a field, smooth there with one-dimensional fibre, the
local ring has Krull dimension one.** Local dimension at a closed point of a scheme locally of
finite type over a field is the Krull dimension of its local ring, and both local dimension and
local ring are unchanged on restricting to a smooth open neighbourhood. -/
theorem ringKrullDim_stalk_eq_one_of_smoothAt {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (hx : IsClosed ({x} : Set X)) (hsm : InfinitesimalLifting.SmoothAt f x)
    (hdim : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = 1) :
    ringKrullDim (X.presheaf.stalk x) = 1 := by
  obtain ⟨W, hxW, hW⟩ := hsm
  let y : W.toScheme := ⟨x, hxW⟩
  let g := W.ι ≫ f
  have : Smooth g := by
    dsimp [g]
    rw [← f.resLE_comp_ι (U := ⊤) (V := W) le_top]
    have : Smooth (f.resLE ⊤ W le_top) := hW
    infer_instance
  have hy : IsClosed ({y} : Set W.toScheme) := by
    convert hx.preimage W.ι.continuous using 1
    ext z
    change z = y ↔ z.val = x
    exact Subtype.ext_iff
  have hd := topologicalKrullDimAt_eq_krullDimOfRing_stalk k W.toScheme g y hy
  rw [topologicalKrullDimAt_fiber_eq f x] at hdim
  have hdW : topologicalKrullDimAt W.toScheme y = 1 :=
    (W.ι.isOpenEmbedding.topologicalKrullDimAt_eq y).symm.trans hdim
  rw [hd] at hdW
  exact (asIso (W.ι.stalkMap y)).commRingCatIsoToRingEquiv.ringKrullDim.trans hdW

/-- **The stalk of the relative differentials over a field is the Kähler differentials of the
local ring over that field**, compatibly with universal differentials.

This is `Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv` with the
base ring changed from the local ring `𝒪_{Spec k, f x}` of the base to `k` itself. -/
theorem exists_relativeDifferentialStalk_kaehlerEquiv {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    letI : Algebra k (X.presheaf.stalk x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x trivial).hom.toAlgebra
    letI := relativeDifferentialStalkModule f x
    ∃ e : relativeDifferentialStalk f x ≃ₗ[X.presheaf.stalk x] Ω[X.presheaf.stalk x⁄k],
      ∀ (U : X.Opens) (hxU : x ∈ U) (a : X.presheaf.obj (op U)),
        e ((TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (Scheme.Hom.relativeDifferentials f).val.presheaf U x hxU)
          ((Scheme.Hom.universalRelativeDerivation f).d a)) =
          KaehlerDifferential.D k (X.presheaf.stalk x) ((X.presheaf.germ U x hxU).hom a) := by
  classical
  let R := X.presheaf.stalk x
  let B := (Spec (.of k)).presheaf.stalk (f x)
  let eK : CommRingCat.of k ≅ B := specFieldStalkIso (f x)
  let _ : Algebra k R := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x trivial).hom.toAlgebra
  let _ : Algebra k B := eK.hom.hom.toAlgebra
  let _ : Algebra B R := algebraStalkMap f x
  let _ : IsScalarTower k B R := IsScalarTower.of_algebraMap_eq'
    (congrArg CommRingCat.Hom.hom (specFieldStalkIso_hom_comp_stalkMap f x).symm)
  let _ : IsLocalization (⊥ : Submonoid k) B :=
    IsLocalization.of_le_isUnit_of_bijective (by
      rintro z ⟨r, hr, rfl⟩
      obtain rfl : r = 1 := hr
      simp) eK.commRingCatIsoToRingEquiv.bijective
  let L : Ω[R⁄k] ≃ₗ[R] Ω[R⁄B] := LinearEquiv.ofBijective
    (KaehlerDifferential.map k B R R) (omega_localization_base k R ⊥ B)
  let _ := relativeDifferentialStalkModule f x
  let E₀ : relativeDifferentialStalk f x ≃ₗ[R] Ω[R⁄B] :=
    relativeDifferentialsStalkKaehlerEquiv f x
  refine ⟨E₀.trans L.symm, fun U hxU a => ?_⟩
  apply L.injective
  change L (L.symm (E₀ _)) = _
  rw [L.apply_symm_apply]
  exact (relativeDifferentialsStalkKaehlerEquiv_germ_d f x
    (OrderDual.toDual (⟨U, hxU⟩ : OpenNhds x)) a).trans
      (KaehlerDifferential.map_D k B R R _).symm

/-- **Stacks Project, Tag 0C1E.** At a closed point of a scheme over a field, smooth there of
relative dimension one and with separable residue field, the differential of any uniformizer
freely generates the stalk of relative differentials. -/
@[stacks 0C1E]
theorem differential_uniformizer_basis
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (x : X) (hx : IsClosed ({x} : Set X))
    (hsm : InfinitesimalLifting.SmoothAt f x)
    (hdim : topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = 1)
    (hsep :
      letI : Algebra k (X.residueField x) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Algebra.IsSeparable k (X.residueField x))
    (s : X.presheaf.stalk x)
    (hs : maximalIdeal (X.presheaf.stalk x) = Ideal.span {s})
    (U : X.Opens) (hxU : x ∈ U) (a : X.presheaf.obj (op U))
    (hsa : ((X.presheaf.germ U x hxU).hom a) = s) :
    letI := relativeDifferentialStalkModule f x
    ∃ e : X.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] relativeDifferentialStalk f x,
      e 1 =
        (TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
            (Scheme.Hom.relativeDifferentials f).val.presheaf U x hxU)
          ((Scheme.Hom.universalRelativeDerivation f).d a) := by
  classical
  let R := X.presheaf.stalk x
  let _ : Algebra k R :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x trivial).hom.toAlgebra
  let _ : Algebra k (ResidueField R) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let _ : IsScalarTower k R (ResidueField R) := IsScalarTower.of_algebraMap_eq' rfl
  let _ : Algebra.IsSeparable k (ResidueField R) := hsep
  let _ : Algebra.FormallyEtale k (ResidueField R) :=
    Algebra.FormallyEtale.of_isSeparable k (ResidueField R)
  obtain ⟨hft, hfs⟩ := smoothAt_field_stalk_properties f x hsm
  let _ : Algebra.EssFiniteType k R := hft
  let _ : Algebra.FormallySmooth k R := hfs
  obtain ⟨e, he⟩ := differential_uniformizer_linearEquiv k R s hs
    (ringKrullDim_stalk_eq_one_of_smoothAt f x hx hsm hdim)
  let _ := relativeDifferentialStalkModule f x
  obtain ⟨E, hE⟩ := exists_relativeDifferentialStalk_kaehlerEquiv f x
  refine ⟨e.trans E.symm, ?_⟩
  apply E.injective
  rw [LinearEquiv.trans_apply, E.apply_symm_apply, he, hE, hsa]

end AlgebraicGeometry

end
