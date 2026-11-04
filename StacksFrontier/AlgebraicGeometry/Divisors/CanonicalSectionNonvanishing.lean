module

public import StacksFrontier.AlgebraicGeometry.CurveFiniteMorphism.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierAffineLocal
public import StacksFrontier.AlgebraicGeometry.Divisors.InvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalSheafEvaluation
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceSections.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiAffineNonvanishing.Basic

/-!
# The canonical section of `𝒪_X(D)` vanishes exactly on `D`

Let `X` be a scheme and `D ⊆ X` an effective Cartier divisor, with invertible sheaf
`𝒪_X(D) = SheafHom(ℐ_D, 𝒪_X)` and canonical global section `1_D`, the one corresponding to the
inclusion `ℐ_D ⟶ 𝒪_X`. The nonvanishing locus of `1_D` is the complement of the support of `D`;
for `D = n·x` with `x` a closed point and `n ≥ 1` it is `X ∖ {x}`.

## Main definitions

* `Stacks.Divisors.canonicalSections`: the canonical section `1_D` of `𝒪_X(D)`, as a
  `PresheafOfModules.sections`.

## Main results

* `Stacks.SheafOfModules.tensorPairing_evaluationIso`: the evaluation pairing, on sections of the
  presheaf tensor product, is evaluation of the functional.
* `Stacks.Divisors.stacksIsInvertible_invertibleSheaf`: `𝒪_X(D)` is invertible in the sense of
  `Stacks.SheafOfModules.IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property`.
* `Stacks.Divisors.nonvanishingLocus_canonicalSections`: `X_{1_D} = X ∖ D`.
* `Stacks.Divisors.nonvanishingChart_canonicalSections`: the same, as a subset of `X` through
  `Stacks.ProjectiveSpaceSections.nonvanishingChart`.
* `Stacks.Divisors.supportSet_pow`: the support of `n·D` is the support of `D`, for `n ≥ 1`.
* `Stacks.Divisors.nonvanishingChart_canonicalSections_vanishingIdeal_pow`: `X_{1_{n·x}}` is
  `X ∖ {x}` for a closed point `x` and `n ≥ 1`.
* `Stacks.Divisors.isAffineOpen_compl_singleton_of_canonicalSections`: on a proper curve, if
  finitely many global sections of `𝒪_X(n·x)`, one of them `1_{n·x}`, have nonvanishing loci
  covering `X`, then `X ∖ {x}` is affine.

## References

* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01WT](https://stacks.math.columbia.edu/tag/01WT)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0A27](https://stacks.math.columbia.edu/tag/0A27)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
* [Stacks Project, Tag 0FNV](https://stacks.math.columbia.edu/tag/0FNV)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace (sheafifyUnit)

universe u

namespace Stacks.SheafOfModules

variable {X : Scheme.{u}} (M : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- The evaluation pairing, read on sections, is evaluation of the functional: the pairing
`Stacks.SheafOfModules.tensorPairing` of the evaluation isomorphism, applied to sections `a` of
the dual of `M` and `b` of `M` over `W`, is `evalSection` of `a` at `b`. -/
theorem tensorPairing_evaluationIso
    [IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property M]
    (W : Opens X.carrier)
    (a : (dualSheaf X.presheaf (structureSheafRing X.toRingedSpace).property M).val.obj (op W))
    (b : M.val.obj (op W)) :
    tensorPairing (Scheme.evaluationIso X M) W a b
      = evalSection X.presheaf M.val
          (SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val (op W) a b :=
  evaluation_toSheafify X.presheaf (structureSheafRing X.toRingedSpace).property M (op W) a b

end Stacks.SheafOfModules

namespace Stacks.Divisors

variable {X : Scheme.{u}} (D : X.IdealSheafData)

/-- The canonical section `1_D` of `𝒪_X(D)`, as the `PresheafOfModules.sections` given by its
restrictions to every open. -/
noncomputable def canonicalSections : (invertibleSheaf D).sections :=
  Stacks.SheafOfModules.sectionsOfTop (X := X.toRingedSpace) (invertibleSheaf D)
    (canonicalSection D)

/-- The canonical section, evaluated over an open `W`, is the ideal inclusion over `W`. -/
theorem evalSection_canonicalSections (W : Opens X.carrier)
    (b : (negativeTwist D).val.obj (op W)) :
    Stacks.SheafOfModules.evalSection X.presheaf (negativeTwist D).val
        (SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val (op W)
        ((canonicalSections D).eval (op W)) b
      = ((idealInclusion D).val.app (op W)).hom b := rfl

/-- The comparison `Stacks.Divisors.kernelIdealSheafIso` with the sectionwise ideal sheaf is
compatible with the two inclusions into `𝒪_X`, in the direction from the sectionwise ideal sheaf
to the categorical kernel. -/
theorem idealInclusion_val_app_kernelIdealSheafIso_inv (W : Opens X.carrier)
    (z : (kernelIdealSheaf D).val.obj (op W)) :
    ((idealInclusion D).val.app (op W)).hom
        ((kernelIdealSheafIso D).inv.val.app (op W) z) = kernelSection D z :=
  congrArg (fun φ : kernelIdealSheaf D ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace) =>
      (φ.val.app (op W)).hom z)
    (IsLimit.conePointUniqueUpToIso_inv_comp
      (kernelIsKernel (structureSheafHomOfIdealSheafData D))
      (_root_.SheafOfModules.kerIsLimit (structureSheafHomOfIdealSheafData D))
      WalkingParallelPair.zero)

/-- The comparison `Stacks.Divisors.kernelIdealSheafIso` with the sectionwise ideal sheaf is
compatible with the two inclusions into `𝒪_X`, in the direction from the categorical kernel to
the sectionwise ideal sheaf. -/
theorem kernelSection_kernelIdealSheafIso_hom (W : Opens X.carrier)
    (b : (negativeTwist D).val.obj (op W)) :
    kernelSection D ((kernelIdealSheafIso D).hom.val.app (op W) b)
      = ((idealInclusion D).val.app (op W)).hom b :=
  congrArg (fun φ : Stacks.ClosedImmersion.idealSheaf D.subschemeι.toLRSHom.toShHom ⟶
        SheafOfModules.unit (structureSheafRing X.toRingedSpace) => (φ.val.app (op W)).hom b)
    (IsLimit.conePointUniqueUpToIso_hom_comp
      (kernelIsKernel (structureSheafHomOfIdealSheafData D))
      (_root_.SheafOfModules.kerIsLimit (structureSheafHomOfIdealSheafData D))
      WalkingParallelPair.zero)

/-- The ideal inclusion hits the unit section over `W` exactly when `1 ∈ ℐ_D(W)`. -/
theorem exists_idealInclusion_eq_unitSection_iff (W : Opens X.carrier) :
    (∃ b : (negativeTwist D).val.obj (op W),
        ((idealInclusion D).val.app (op W)).hom b
          = Stacks.SheafOfModules.unitSection X.toRingedSpace W) ↔
      (1 : Γ(X, W)) ∈ RingHom.ker (D.subschemeι.app W).hom := by
  refine ⟨fun ⟨b, hb⟩ ↦ ?_, fun h ↦
    ⟨(kernelIdealSheafIso D).inv.val.app (op W) (mkKernelSection D 1 h), ?_⟩⟩
  · have h := kernelSection_mem D ((kernelIdealSheafIso D).hom.val.app (op W) b)
    rwa [kernelSection_kernelIdealSheafIso_hom, hb] at h
  · rw [idealInclusion_val_app_kernelIdealSheafIso_inv, kernelSection_mkKernelSection]
    rfl

/-- Some open neighbourhood `W` of `x` has `1 ∈ ℐ_D(W)` exactly when `x` is not in the support
of `D`. -/
theorem exists_one_mem_ker_iff_notMem_supportSet (x : X) :
    (∃ (W : Opens X.carrier) (_ : x ∈ W),
        (1 : Γ(X, W)) ∈ RingHom.ker (D.subschemeι.app W).hom) ↔ x ∉ D.supportSet := by
  constructor
  · rintro ⟨W, hxW, h1⟩ hx
    obtain ⟨-, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxW W.isOpen
    have h2 := mem_ker_app_res D (show U ≤ W from hUW) h1
    rw [map_one, D.ker_subschemeι_app ⟨U, hU⟩] at h2
    rw [Scheme.IdealSheafData.mem_supportSet_iff_of_mem (U := ⟨U, hU⟩) hxU,
      Scheme.mem_zeroLocus_iff] at hx
    exact hx 1 h2 (by rw [X.basicOpen_one]; exact hxU)
  · intro hx
    obtain ⟨-, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    obtain ⟨g, hxg, htop⟩ := exists_basicOpen_ideal_eq_top D ⟨V, hV⟩ x hxV hx
    refine ⟨(X.affineBasicOpen (U := ⟨V, hV⟩) g).1, hxg,
      mem_ker_app_of_ideal_eq_span D (X.affineBasicOpen (U := ⟨V, hV⟩) g).2 (by simp [htop])⟩

/-- The support of `n·D` is the support of `D`, for `n ≥ 1`. -/
theorem supportSet_pow {n : ℕ} (hn : 0 < n) : (D ^ n).supportSet = D.supportSet :=
  congrArg (fun S : Closeds X => (S : Set X)) (D.support_pow n hn.ne')

section EffectiveCartier

variable [hD : IsEffectiveCartierDivisor D]

/-- `𝒪_X(D)` is invertible in the sense of `Stacks.SheafOfModules.IsInvertible`, with the
structure sheaf written `X.presheaf`. -/
instance stacksIsInvertible_invertibleSheaf :
    Stacks.SheafOfModules.IsInvertible X.presheaf
      (structureSheafRing X.toRingedSpace).property (invertibleSheaf D) :=
  Stacks.SheafOfModules.isInvertible_of_tensorIsoUnit X.sheaf.obj
    (structureSheafRing X.toRingedSpace).property (invertibleSheaf D) (negativeTwist D)
    (invertibleSheafPairing' D)

/-- A point lies in the nonvanishing locus `X_{1_D}` of the canonical section exactly when some
neighbourhood carries a section of `ℐ_D` whose image in `𝒪_X` is `1`. -/
theorem mem_nonvanishingLocus_canonicalSections_iff (x : X) :
    x ∈ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) (invertibleSheaf D)
        (canonicalSections D) ↔
      ∃ (W : Opens X.carrier) (_ : x ∈ W) (b : (negativeTwist D).val.obj (op W)),
        ((idealInclusion D).val.app (op W)).hom b
          = Stacks.SheafOfModules.unitSection X.toRingedSpace W := by
  have := stacksIsInvertible_negativeTwist D
  exact (Stacks.SheafOfModules.mem_nonvanishingLocus_iff
    (X := X.toRingedSpace) (L := invertibleSheaf D) (N := negativeTwist D)
    (Stacks.SheafOfModules.Scheme.evaluationIso X (negativeTwist D))
    (canonicalSections D) x).trans
    (exists_congr fun W => exists_congr fun _ => exists_congr fun b =>
      Eq.congr_left
        ((Stacks.SheafOfModules.tensorPairing_evaluationIso (negativeTwist D) W
            ((canonicalSections D).eval (op W)) b).trans
          (evalSection_canonicalSections D W b)))

/-- The canonical section of `𝒪_X(D)` vanishes exactly on `D`: `X_{1_D} = X ∖ D`. -/
theorem nonvanishingLocus_canonicalSections :
    Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) (invertibleSheaf D)
        (canonicalSections D) = (D.supportSet)ᶜ := by
  ext x
  rw [mem_nonvanishingLocus_canonicalSections_iff, Set.mem_compl_iff,
    ← exists_one_mem_ker_iff_notMem_supportSet]
  exact exists_congr fun W => exists_congr fun _ =>
    exists_idealInclusion_eq_unitSection_iff D W

/-- The nonvanishing chart of the canonical section of `𝒪_X(D)`, as a subset of `X`, is
`X ∖ D`. -/
theorem nonvanishingChart_canonicalSections :
    (Stacks.ProjectiveSpaceSections.nonvanishingChart (invertibleSheaf D)
      (canonicalSections D) : Set X) = (D.supportSet)ᶜ :=
  nonvanishingLocus_canonicalSections D

end EffectiveCartier

/-- The canonical section of `𝒪_X(n·x)` vanishes exactly at `x`: for a closed point `x` whose
`n`-fold multiple is an effective Cartier divisor and `n ≥ 1`, the nonvanishing locus of
`1_{n·x}` is `X ∖ {x}`. -/
theorem nonvanishingChart_canonicalSections_vanishingIdeal_pow {x : X}
    (hx : IsClosed ({x} : Set X)) {n : ℕ} (hn : 0 < n)
    [IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)] :
    (Stacks.ProjectiveSpaceSections.nonvanishingChart
        (invertibleSheaf (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n))
        (canonicalSections
          (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)) : Set X)
      = ({x} : Set X)ᶜ := by
  have hsupp : (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).supportSet
      = ({x} : Set X) :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal (⟨{x}, hx⟩ : Closeds X)
  rw [nonvanishingChart_canonicalSections, supportSet_pow _ hn, hsupp]

section Engine

open Stacks.ProjectiveSpaceSections

variable {k : Type u} [Field k] {f : X ⟶ Spec (.of k)}

/-- The nonvanishing chart of the canonical section of `𝒪_X(n·x)` is not all of `X`. -/
theorem nonvanishingChart_canonicalSections_ne_top {x : X} (hx : IsClosed ({x} : Set X))
    {n : ℕ} (hn : 0 < n)
    [IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)] :
    nonvanishingChart
        (invertibleSheaf (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n))
        (canonicalSections
          (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)) ≠ ⊤ := by
  intro htop
  have h := nonvanishingChart_canonicalSections_vanishingIdeal_pow hx hn
  rw [htop] at h
  exact (h ▸ (Set.mem_univ x : x ∈ (⊤ : X.Opens).carrier) : x ∈ ({x} : Set X)ᶜ) rfl

/-- The nonvanishing chart of the canonical section of `𝒪_X(n·x)` is nonempty as soon as `X` has
a point other than `x`. -/
theorem nonvanishingChart_canonicalSections_nonempty {x : X} (hx : IsClosed ({x} : Set X))
    {n : ℕ} (hn : 0 < n)
    [IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)]
    (hne : ∃ y : X, y ≠ x) :
    (nonvanishingChart
        (invertibleSheaf (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n))
        (canonicalSections
          (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)) : Set X).Nonempty :=
  hne.imp fun y hy => by rwa [nonvanishingChart_canonicalSections_vanishingIdeal_pow hx hn]

/-- Let `X` be a proper curve over `k`, let `x` be a closed point of `X` whose `n`-fold multiple
is an effective Cartier divisor, and let `s₀, …, s_m` be global sections of `𝒪_X(n·x)` whose
nonvanishing loci cover `X`, one of which is the canonical section `1_{n·x}`. Then `X ∖ {x}` is
affine. -/
theorem isAffineOpen_compl_singleton_of_canonicalSections (hf : IsProper f) (hc : IsCurve k f)
    {x : X} (hx : IsClosed ({x} : Set X)) {n : ℕ} (hn : 0 < n)
    [IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)]
    {m : ℕ}
    (s : Fin (m + 1) →
      (invertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)).sections)
    (hs : (⨆ i, nonvanishingChart
        (invertibleSheaf (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n))
        (s i)) = ⊤)
    (i₀ : Fin (m + 1))
    (h0 : s i₀ = canonicalSections
      (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n)) :
    IsAffineOpen (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens) :=
  isAffineOpen_compl_singleton_of_nonvanishingChart_eq
    (invertibleSheaf (Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) ^ n))
    s hs hf hc hx i₀
    (h0 ▸ nonvanishingChart_canonicalSections_vanishingIdeal_pow hx hn)

end Engine

end Stacks.Divisors

end
