module

public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.AffineMorphismEuler.Basic
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.FieldExtension
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.Basic
public import StacksFrontier.AlgebraicGeometry.PicardScheme.Jacobian.RiemannRochEffective
public import StacksFrontier.AlgebraicGeometry.EulerCharTruncation.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.GenusDisjointUnion
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.EulerCharAdditivity.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.LinearSeries
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DivisorFirstDifference
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Construction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerInvertible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegreeHom
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SectionDegree
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Pushforward
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Qcqs

/-!
# The cohomology of the structure sheaf of a cyclic cover

Let `Z` be a proper integral curve over a field `k` with `H⁰(Z, 𝒪_Z) = k`, `L` an invertible
`𝒪_Z`-module whose class in `Pic(Z)` has order `n ≥ 1`, and `p : X ⟶ Z_S` the cyclic cover attached
to `φ : Symⁿ L ≅ 𝒪_Z` and `c ∈ S`
(`StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.Construction`).
From `p_* 𝒪_X = ⨁_{i < n} (Symⁱ L)_S` this file computes the cohomology of `𝒪_X`: for
`0 < i < n` the module `Symⁱ L = L^{⊗ i}` is nontrivial of degree `0`, so it has no global
sections and `h¹ = g - 1` by Riemann–Roch.

## Main results

* `Stacks.CyclicCover.symPowIsoTensorPower`: `Symⁱ L ≅ L^{⊗ i}`.
* `Stacks.CyclicCover.tensorPowerNat_eq_zero`: `H⁰(Z, L^{⊗ i}) = 0` for `0 < i < n`.
* `Stacks.CyclicCover.bijective_coverSnd_appTop`: **`H⁰(X, 𝒪_X) = S`.**
* `Stacks.CyclicCover.genus_cover`: **the genus of `X` over a field `K ⊇ k` is `n(g - 1) + 1`.**

## References

* [Stacks Project, Tag 0CEH](https://stacks.math.columbia.edu/tag/0CEH)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped TensorProduct
open Stacks.RingedSpace (structureIsSheaf)

universe u

namespace Stacks.CyclicCover


variable {Z : Scheme.{u}} (L : Z.Modules)

/-- The Picard class of `L^{⊗ i}` is `i` times that of `L`. -/
theorem picardClass_tensorPowerNat
    (hL : Stacks.SheafOfModules.IsInvertible Z.presheaf (structureIsSheaf Z.toRingedSpace) L) :
    ∀ i : ℕ, Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace)
        (SheafOfModules.tensorPower (Opens.grothendieckTopology Z) L i)
        (Stacks.AlgebraicGeometry.ProjRepresentsF1.isInvertible_tensorPowerNat L hL i) =
      (i : ℤ) • Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) L hL
  | 0 => by rw [Nat.cast_zero, zero_smul]; rfl
  | 1 => by rw [Nat.cast_one, one_smul]; rfl
  | (i + 2) => by
      have h := Stacks.SheafOfModules.picardClass_tensorSheaf Z.presheaf
        (structureIsSheaf Z.toRingedSpace) L
        (SheafOfModules.tensorPower (Opens.grothendieckTopology Z) L (i + 1)) hL
        (Stacks.AlgebraicGeometry.ProjRepresentsF1.isInvertible_tensorPowerNat L hL (i + 1))
        (Stacks.AlgebraicGeometry.ProjRepresentsF1.isInvertible_tensorPowerNat L hL (i + 2))
      refine h.symm.trans ?_
      rw [picardClass_tensorPowerNat hL (i + 1)]
      push_cast
      rw [add_smul, add_smul, one_smul, show (2 : ℤ) = 1 + 1 from rfl, add_smul, one_smul]
      abel


/-- **On a proper integral curve, an invertible module of degree `0` with nonzero Picard class
has no nonzero global section** ([Stacks, Tag 0B40] part (4)). -/
theorem eq_zero_of_picardClass_ne_zero (k : Type u) [Field k] (f : Z ⟶ Spec (.of k)) [IsProper f]
    [IsIntegral Z] (hdim : topologicalKrullDim Z ≤ 1) (M : Z.Modules)
    (hM : Stacks.SheafOfModules.IsInvertible Z.presheaf (structureIsSheaf Z.toRingedSpace) M)
    (hc : Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) M hM ≠ 0)
    (hdeg : invertibleCurveDegreeHom k f hdim
      (Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) M hM) ≤ 0)
    (x : M.val.obj (op ⊤)) : x = 0 := by
  by_contra hx
  rw [invertibleCurveDegreeHom_picardClass] at hdeg
  exact hc ((Stacks.SheafOfModules.picardClass_eq_zero_iff _ _ _ _).2
    (@isTrivial_of_invertibleCurveDegree_nonpos k _ Z f _ _ hdim M hM
      (Stacks.PresheafOfModules.sectionOfTop M.val x) (by simpa using hx) hdeg))

/-- A class `c` of finite order `n ≠ 0` has degree `0`, since `n deg c = deg (n c) = 0`. -/
private theorem invertibleCurveDegreeHom_eq_zero_of_addOrderOf (k : Type u) [Field k]
    (f : Z ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim Z ≤ 1)
    (c : Stacks.Picard.ofScheme Z) {n : ℕ} (hord : addOrderOf c = n) (hn : n ≠ 0) :
    invertibleCurveDegreeHom k f hdim c = 0 := by
  have hc : n • c = 0 := hord ▸ addOrderOf_nsmul_eq_zero c
  have hdeg : (n : ℤ) * invertibleCurveDegreeHom k f hdim c = 0 := by
    rw [← smul_eq_mul, ← map_zsmul, natCast_zsmul, hc, map_zero]
  exact (mul_eq_zero.1 hdeg).resolve_left (by exact_mod_cast hn)

/-- **For `L` of order `n` on a proper integral curve, `L^{⊗ i}` has no nonzero global section
for `0 < i < n`**: its class `i [L]` is nonzero, and its degree `i deg L` is zero since
`n deg L = deg(n [L]) = 0`. -/
theorem tensorPowerNat_eq_zero (k : Type u) [Field k] (f : Z ⟶ Spec (.of k)) [IsProper f]
    [IsIntegral Z] (hdim : topologicalKrullDim Z ≤ 1)
    (hL : Stacks.SheafOfModules.IsInvertible Z.presheaf (structureIsSheaf Z.toRingedSpace) L)
    {n : ℕ} (hord : addOrderOf
      (Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) L hL) = n)
    {i : ℕ} (hi : 0 < i) (hin : i < n)
    (x : (SheafOfModules.tensorPower (Opens.grothendieckTopology Z) L i).val.obj (op ⊤)) :
    x = 0 := by
  set c := Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) L hL
  refine eq_zero_of_picardClass_ne_zero k f hdim _
    (Stacks.AlgebraicGeometry.ProjRepresentsF1.isInvertible_tensorPowerNat L hL i) ?_ ?_ x
  · rw [picardClass_tensorPowerNat L hL i, natCast_zsmul]
    exact nsmul_ne_zero_of_lt_addOrderOf hi.ne' (by rw [hord]; exact hin)
  · rw [picardClass_tensorPowerNat L hL i, map_zsmul,
      invertibleCurveDegreeHom_eq_zero_of_addOrderOf k f hdim c hord (hi.trans hin).ne', smul_zero]

end Stacks.CyclicCover

namespace Stacks.CyclicCover


attribute [local instance] Abelian.hasFiniteBiproducts

variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) {L : Z.Modules}
  [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L] {n : ℕ}
  (φ : (situation f L).symmetricAlgebra.piece (n : ℤ) ≅ SheafOfModules.unit Z.ringCatSheaf)
  (S : Type u) [CommRing S] [Algebra k S] (c : S)

variable (L) in
/-- The symmetric power `Symⁱ L`, as an `𝒪_Z`-module. -/
abbrev symPow (i : ℕ) : Z.Modules := (situation f L).symmetricAlgebra.piece (i : ℤ)

variable (L) in
/-- The tensor power `L^{⊗ i}`, as an `𝒪_Z`-module. -/
abbrev tensorPow (i : ℕ) : Z.Modules :=
  SheafOfModules.tensorPower (Opens.grothendieckTopology Z) L i

variable (L) in
/-- **`Symⁱ L = L^{⊗ i}`** for an invertible `L`. -/
def symPowIsoTensorPower (i : ℕ) : symPow f L i ≅ tensorPow L i :=
  haveI : Stacks.SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible _ _ _).2 ‹_›
  SheafOfModules.GradedAlgebra.IsUniversal.pieceIso
    (Scheme.Modules.isSymmetricAlgebra_symmetricAlgebra Z L)
    (SheafOfModules.algebras _ L).symmetric_isSymmetricAlgebra (i : ℤ) ≪≫
  Stacks.SheafOfModules.symmetricPowerIsoTensorPowerOfIsInvertible Z.sheaf L
    (SheafOfModules.algebras _ L) i


/-- For `L` of order `n`, `Symⁱ L` has no nonzero global section for `0 < i < n`. -/
theorem symPow_eq_zero [IsProper f] [IsIntegral Z] (hdim : topologicalKrullDim Z ≤ 1)
    (hord : addOrderOf
      (Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) L ‹_›) = n)
    {i : ℕ} (hi : 0 < i) (hin : i < n)
    (x : ((situation f L).symmetricAlgebra.piece (i : ℤ)).val.obj (op ⊤)) : x = 0 := by
  have h := tensorPowerNat_eq_zero L k f hdim ‹_› hord hi hin
    (((symPowIsoTensorPower f L i).hom.val.app (op ⊤)) x)
  let E := ((SheafOfModules.forget _ ⋙ PresheafOfModules.evaluation _ (op ⊤)).mapIso
    (symPowIsoTensorPower f L i)).toLinearEquiv
  exact E.injective (h.trans (map_zero E).symm)

end Stacks.CyclicCover

namespace Stacks.CyclicCover


attribute [local instance] Abelian.hasFiniteBiproducts

variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) {L : Z.Modules}
  [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L] {n : ℕ}
  (φ : (situation f L).symmetricAlgebra.piece (n : ℤ) ≅ SheafOfModules.unit Z.ringCatSheaf)
  (S : Type u) [CommRing S] [Algebra k S] (c : S)

/-- A ring map `g` with `a ↦ g a * w` bijective for some `w` is bijective. -/
theorem bijective_of_bijective_mul {A B : Type*} [CommRing A] [CommRing B] (g : A →+* B) (w : B)
    (h : Function.Bijective fun a => g a * w) : Function.Bijective g := by
  obtain ⟨c, hc⟩ := h.2 1
  obtain ⟨d, hd⟩ := h.2 (w * w)
  simp only at hc hd
  have h1 : g (c * d) * w = w := by
    rw [map_mul, mul_assoc, hd, ← mul_assoc, hc, one_mul]
  have h2 : g (c * d) = 1 := by
    calc g (c * d) = g (c * d) * (g c * w) := by rw [hc, mul_one]
      _ = g c * (g (c * d) * w) := by ring
      _ = 1 := by rw [h1, hc]
  have hw : w = g d := by
    calc w = g (c * d) * w := by rw [h2, one_mul]
      _ = g d * (g c * w) := by rw [map_mul]; ring
      _ = g d := by rw [hc, mul_one]
  refine ⟨fun a a' haa => h.1 (by simp only [haa]), fun b => ?_⟩
  obtain ⟨a, rfl⟩ := h.2 b
  exact ⟨a * d, by simp only [map_mul, ← hw]⟩

section

variable [IsProper f]

/-- `Spec S ⟶ Spec k` is flat for a `k`-algebra `S`. -/
theorem flat_specMap_algebraMap : Flat (Spec.map (CommRingCat.ofHom (algebraMap k S))) := by
  rw [Flat.SpecMap_iff]
  exact (RingHom.flat_algebraMap_iff).2 inferInstance

/-- For `L` of order `n`, `(Symⁱ L)_S` has no nonzero global section for `0 < i < n`, by flat base
change in degree zero ([Stacks, Tag 02KH]). -/
theorem pullbackSymPow_eq_zero [IsIntegral Z] (hdim : topologicalKrullDim Z ≤ 1)
    (hord : addOrderOf
      (Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) L ‹_›) = n)
    {i : ℕ} (hi : 0 < i) (hin : i < n)
    (y : Γ((Scheme.Modules.pullback (baseChangeFst f S)).obj
      ((situation f L).symmetricAlgebra.piece (i : ℤ)), ⊤)) : y = 0 := by
  have := (situation f L).isQuasicoherent_symmetricAlgebra_piece i
  have := flat_specMap_algebraMap (k := k) S
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨e, -⟩ :=
    Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k S))))
      ((situation f L).symmetricAlgebra.piece (i : ℤ))
  have : Subsingleton Γ((situation f L).symmetricAlgebra.piece (i : ℤ), ⊤) :=
    ⟨fun a b => (symPow_eq_zero f hdim hord hi hin a).trans
      (symPow_eq_zero f hdim hord hi hin b).symm⟩
  rw [← e.apply_symm_apply y, Subsingleton.elim (e.symm y) 0, map_zero]

end

end Stacks.CyclicCover


namespace Stacks.CyclicCover

attribute [local instance] Abelian.hasFiniteBiproducts

variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) {L : Z.Modules}
  [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L] {n : ℕ}
  (φ : (situation f L).symmetricAlgebra.piece (n : ℤ) ≅ SheafOfModules.unit Z.ringCatSheaf)
  (S : Type u) [CommRing S] [Algebra k S] (c : S)

/-- If `N` is free of rank one over `R` on `u₀` and `e : T ⊗_R N ≅ P`, then `t ↦ e (t ⊗ u₀)` is
bijective. -/
theorem bijective_tmul_of_linearEquiv {R T N : Type*} [CommRing R] [CommRing T] [Algebra R T]
    [AddCommGroup N] [Module R N] {P : Type*} (ε : N ≃ₗ[R] R)
    (e : T ⊗[R] N ≃ P) (u₀ : N) (hu : ε u₀ = 1) :
    Function.Bijective (fun t : T => e (t ⊗ₜ u₀)) := by
  have h : (fun t : T => e (t ⊗ₜ u₀)) =
      e ∘ (TensorProduct.congr (LinearEquiv.refl R T) ε).symm ∘ (TensorProduct.rid R T).symm := by
    funext t
    simp [← hu]
  rw [h]
  exact e.bijective.comp ((TensorProduct.congr (LinearEquiv.refl R T) ε).symm.bijective.comp
    (TensorProduct.rid R T).symm.bijective)

section H0

variable [IsProper f] [IsIntegral Z] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

omit [IsProper f] [AlgebraicGeometry.IsIntegral Z] in
include f in
/-- `H⁰(Z, 𝒪_Z) = k`, as bijectivity of `f.appTop`. -/
theorem bijective_appTop : Function.Bijective f.appTop := by
  have : (ConcreteCategory.hom f.appTop) =
      ConcreteCategory.hom ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ∘
        ConcreteCategory.hom (Scheme.ΓSpecIso (.of k)).hom := by
    funext x
    simp
  rw [this]
  exact (ConcreteCategory.bijective_of_isIso _).comp (ConcreteCategory.bijective_of_isIso _)

variable (L) in
/-- The section `1` of `Sym⁰ L = 𝒪_Z`. -/
def symPowZeroOne : Γ(symPow f L 0, ⊤) :=
  (symPowIsoTensorPower f L 0).inv.app ⊤ (show Γ(tensorPow L 0, ⊤) from (1 : Γ(Z, ⊤)))

omit [IsProper f] [AlgebraicGeometry.IsIntegral Z] in
/-- `H⁰(Z, Sym⁰ L) = k`, on the section `1`. -/
theorem symPowZero_bijective :
    Function.Bijective (fun r : Γ(Spec (.of k), ⊤) => f.appTop r • symPowZeroOne f L) := by
  let θ := symPowIsoTensorPower f L 0
  have hθ : ∀ a, θ.inv.app ⊤ (θ.hom.app ⊤ a) = a := fun a => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, θ.hom_inv_id]; rfl
  have hθ' : ∀ a, θ.hom.app ⊤ (θ.inv.app ⊤ a) = a := fun a => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, θ.inv_hom_id]; rfl
  have key : ∀ r, θ.hom.app ⊤ (f.appTop r • symPowZeroOne f L) = f.appTop r := fun r => by
    rw [Scheme.Modules.Hom.app_smul, symPowZeroOne, hθ']
    exact mul_one (f.appTop r)
  refine ⟨fun r r' h => (bijective_appTop f).1 ?_, fun a => ?_⟩
  · have := congrArg (θ.hom.app ⊤) h
    simp only at this
    rwa [key, key] at this
  · obtain ⟨r, hr⟩ := (bijective_appTop f).2 (θ.hom.app ⊤ a)
    refine ⟨r, ?_⟩
    simp only
    rw [← hθ (f.appTop r • symPowZeroOne f L), key, hr, hθ]

variable (n) in
include f in
/-- **`H⁰(X, 𝒪_X) = S`**: for `L` of order `n ≥ 1` on a proper integral curve `Z` with
`H⁰(Z, 𝒪_Z) = k`, the functions on the cyclic cover `X` over a `k`-algebra `S` are `S`. Only the
summand `i = 0` of `p_* 𝒪_X = ⨁_{i < n} (Symⁱ L)_S` has global sections, and those are
`S ⊗_k H⁰(Z, 𝒪_Z) = S` by flat base change. -/
theorem bijective_coverSnd_appTop (hdim : topologicalKrullDim Z ≤ 1) (hn : n ≠ 0)
    (hord : addOrderOf
      (Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) L ‹_›) = n) :
    Function.Bijective (coverSnd f φ S c).appTop := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  let M := fun i : Fin n => (Scheme.Modules.pullback (baseChangeFst f S)).obj
    ((situation f L).symmetricAlgebra.piece ((i : ℕ) : ℤ))
  let Ψ := (pushforwardDecomposition f n φ S c).app ⊤
  have := isIso_pushforwardDecomposition f n φ S c hn
  have hΨ : Function.Bijective Ψ := ConcreteCategory.bijective_of_isIso Ψ
  have hι : ∀ (i : Fin n) y, Ψ ((biproduct.ι M i).app ⊤ y) =
      (symPowToCoverMap f φ S c i).app ⊤ y := fun i y => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, pushforwardDecomposition,
      biproduct.ι_desc]
  have hsum : ∀ (g : Fin n → ((⨁ M) ⟶ (⨁ M))) x, ((∑ i, g i).app ⊤) x =
      ∑ i, (g i).app ⊤ x := by
    intro g x
    let A : ((⨁ M) ⟶ (⨁ M)) →+ (Γ(⨁ M, ⊤) →+ Γ(⨁ M, ⊤)) :=
      { toFun := fun t => (t.app ⊤).hom
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact (congrArg (fun F => F x) (map_sum A g Finset.univ)).trans
      (AddMonoidHom.finsetSum_apply _ _ _)
  have htot : ∀ x, x = ∑ i, (biproduct.ι M i).app ⊤ ((biproduct.π M i).app ⊤ x) := fun x => by
    have h := congrArg (fun t => t.app ⊤ x) (biproduct.total (f := M))
    simp only at h
    rw [hsum] at h
    exact h.symm
  let i₀ : Fin n := ⟨0, hn0⟩
  have hx : ∀ x, x = (biproduct.ι M i₀).app ⊤ ((biproduct.π M i₀).app ⊤ x) := fun x => by
    refine (htot x).trans ?_
    refine Finset.sum_eq_single i₀ (fun i _ hi => ?_) (by simp)
    rw [pullbackSymPow_eq_zero f S hdim hord (i := i) (Nat.pos_of_ne_zero fun h => hi (Fin.ext h))
      i.2 ((biproduct.π M i).app ⊤ x), map_zero]
  have hπι : ∀ y, (biproduct.π M i₀).app ⊤ ((biproduct.ι M i₀).app ⊤ y) = y := fun y => by
    rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, biproduct.ι_π_self]
    rfl
  -- the summand `i = 0`
  have := (situation f L).isQuasicoherent_symmetricAlgebra_piece 0
  have := flat_specMap_algebraMap (k := k) S
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace Z := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨e, he⟩ :=
    Stacks.AlgebraicGeometry.SectionsBaseChange.exists_linearEquiv_sections_baseChange
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k S))))
      ((situation f L).symmetricAlgebra.piece ((0 : ℕ) : ℤ))
  let u₀ := symPowZeroOne f L
  let := Stacks.AlgebraicGeometry.SectionsBaseChange.baseModule f
    ((situation f L).symmetricAlgebra.piece ((0 : ℕ) : ℤ)) ⊤
  have happ : ∀ r, f.appLE ⊤ ⊤ (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top f ⊤) r =
      f.appTop r := fun r => by
    rw [show f.appLE ⊤ ⊤ _ = f.appTop from Scheme.Hom.appLE_eq_app f]
  have hb : Function.Bijective (LinearMap.toSpanSingleton Γ(Spec (.of k), ⊤)
      Γ((situation f L).symmetricAlgebra.piece ((0 : ℕ) : ℤ), ⊤) u₀) := by
    convert symPowZero_bijective f (L := L) using 1
    funext r
    exact congrArg (· • u₀) (happ r)
  let ε := LinearEquiv.ofBijective _ hb
  have hε : ε.symm u₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]
    change u₀ = (1 : Γ(Spec (.of k), ⊤)) • u₀
    exact (one_smul _ _).symm
  let := Stacks.AlgebraicGeometry.SectionsBaseChange.baseAlgebra
    (Spec.map (CommRingCat.ofHom (algebraMap k S)))
  have hT := bijective_tmul_of_linearEquiv ε.symm e.toEquiv u₀ hε
  let m₀ := Stacks.AlgebraicGeometry.SectionsBaseChange.pullbackSectionsHom (baseChangeFst f S)
    ((situation f L).symmetricAlgebra.piece ((0 : ℕ) : ℤ)) ⊤ ⊤
    (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top _ ⊤) u₀
  let w₀ : Γ(cover f φ S c, ⊤) := (symPowToCoverMap f φ S c 0).app ⊤ m₀
  have hg : ∀ t, (coverSnd f φ S c).appTop t =
      (coverMap f φ S c).appTop ((baseChangeSnd f S).appLE ⊤ ⊤
        (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top _ ⊤) t) := fun t => by
    rw [show (baseChangeSnd f S).appLE ⊤ ⊤ _ = (baseChangeSnd f S).appTop from
      Scheme.Hom.appLE_eq_app _, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
      coverMap_snd]
  have key : ∀ t, (coverSnd f φ S c).appTop t * w₀ =
      Ψ ((biproduct.ι M i₀).app ⊤ (e (t ⊗ₜ u₀))) := fun t => by
    rw [he, hι]
    change _ = (symPowToCoverMap f φ S c 0).app ⊤
      ((baseChangeSnd f S).appLE ⊤ ⊤
        (Stacks.AlgebraicGeometry.SectionsBaseChange.le_preimage_top _ ⊤) t • m₀)
    rw [Scheme.Modules.Hom.app_smul, hg]
    rfl
  refine bijective_of_bijective_mul _ w₀ ⟨fun t t' htt => ?_, fun a => ?_⟩
  · simp only [key] at htt
    have h1 := congrArg (fun z => (biproduct.π M i₀).app ⊤ z) (hΨ.1 htt)
    simp only [hπι] at h1
    exact hT.1 h1
  · obtain ⟨x, rfl⟩ := hΨ.2 a
    obtain ⟨t, ht⟩ := hT.2 ((biproduct.π M i₀).app ⊤ x)
    refine ⟨t, ?_⟩
    simp only at ht ⊢
    rw [key]
    conv_rhs => rw [hx x]
    exact congrArg (fun z => Ψ ((biproduct.ι M i₀).app ⊤ z)) ht

end H0

section Genus

variable [IsProper f] [IsIntegral Z] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

omit [AlgebraicGeometry.IsIntegral Z]
    [IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop f)] in
/-- For `L` of order `n ≥ 1`, every `L^{⊗ i}` has degree `0`. -/
theorem invertibleCurveDegree_tensorPow (hdim : topologicalKrullDim Z ≤ 1) (hn : n ≠ 0)
    (hord : addOrderOf
      (Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) L ‹_›) = n)
    (i : ℕ) :
    @invertibleCurveDegree k _ Z f _ hdim (tensorPow L i)
      (Stacks.AlgebraicGeometry.ProjRepresentsF1.isInvertible_tensorPowerNat L ‹_› i) = 0 := by
  set c := Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) L ‹_›
  rw [← invertibleCurveDegreeHom_picardClass, picardClass_tensorPowerNat L ‹_› i, map_zsmul,
    invertibleCurveDegreeHom_eq_zero_of_addOrderOf k f hdim c hord hn, smul_zero]

/-- **`h¹(L^{⊗ i}) = g - 1` for `0 < i < n`**, by Riemann–Roch: `L^{⊗ i}` has degree `0` and no
global sections. -/
theorem finrank_cohomologyOverField_one_tensorPow (hdim : topologicalKrullDim Z ≤ 1)
    (hord : addOrderOf
      (Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) L ‹_›) = n)
    {i : ℕ} (hi : 0 < i) (hin : i < n) :
    (Module.finrank k (cohomologyOverField k f (tensorPow L i) 1) : ℤ) = genus f - 1 := by
  have := Stacks.AlgebraicGeometry.ProjRepresentsF1.isInvertible_tensorPowerNat L ‹_› i
  have hdeg := invertibleCurveDegree_eq_sub_of_isZero k f hdim (tensorPow L i)
    (isZero_cohomologyOverField_two_le k f hdim _) (isZero_cohomologyOverField_two_le k f hdim _)
  have h0 : Module.finrank k (cohomologyOverField k f (tensorPow L i) 0) = 0 := by
    have : Subsingleton (cohomologyOverField k f (tensorPow L i) 0) :=
      ⟨fun a b => (cohomologyOverFieldZeroEquivSections k f _).injective
        ((tensorPowerNat_eq_zero L k f hdim ‹_› hord hi hin _).trans
          (tensorPowerNat_eq_zero L k f hdim ‹_› hord hi hin _).symm)⟩
    exact Module.finrank_zero_of_subsingleton
  rw [invertibleCurveDegree_tensorPow f hdim (by omega) hord i, h0,
    finrank_cohomologyOverField_unit_zero_eq_one f,
    ← genus_eq_finrank_cohomologyOverField_unit_one' k f] at hdeg
  push_cast at hdeg
  linarith

omit [AlgebraicGeometry.IsIntegral Z]
    [IsIso ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ Scheme.Hom.appTop f)] in
/-- The cohomology of `Symⁱ L` is finite-dimensional ([Stacks, Tag 02O6]). -/
theorem finiteDimensional_cohomologyOverField_symPow (i m : ℕ) :
    FiniteDimensional k (cohomologyOverField k f (symPow f L i) m) := by
  have := Stacks.AlgebraicGeometry.ProjRepresentsF1.isInvertible_tensorPowerNat L ‹_› i
  have := SheafOfModules.isCoherent_of_isInvertible k f (tensorPow L i)
  have := finiteDimensional_cohomologyOverField_of_isProper k f (tensorPow L i) m
  exact LinearEquiv.finiteDimensional
    (cohomologyOverFieldIso k f (symPowIsoTensorPower f L i) m).toLinearEquiv.symm

end Genus

section GenusCover

variable [IsProper f] [IsIntegral Z] [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)]

variable (n) in
/-- **The genus of the cyclic cover over a field is `n(g - 1) + 1`.** For `L` of order `n ≥ 1` on
a proper integral curve `Z` of genus `g` with `H⁰(Z, 𝒪_Z) = k`, a field `K ⊇ k` and any `c ∈ K`,
`H¹(X_K, 𝒪) = ⨁_{i < n} H¹(Z, Symⁱ L) ⊗_k K`, of dimension `g + (n - 1)(g - 1)`. -/
theorem genus_cover (hdim : topologicalKrullDim Z ≤ 1) (hn : n ≠ 0)
    (hord : addOrderOf
      (Stacks.SheafOfModules.picardClass Z.presheaf (structureIsSheaf Z.toRingedSpace) L ‹_›) = n)
    (K : Type u) [Field K] [Algebra k K] (c : K) :
    (genus (coverSnd f φ K c) : ℤ) = n * (genus f - 1) + 1 := by
  have := isFinite_coverMap f φ K c hn
  have := isIso_pushforwardDecomposition f n φ K c hn
  have : ∀ i : Fin n, (symPow f L i).IsQuasicoherent := fun i =>
    (situation f L).isQuasicoherent_symmetricAlgebra_piece i
  have key : ∀ g : cover f φ K c ⟶ Spec (.of K), g = coverMap f φ K c ≫ baseChangeSnd f K →
      Module.finrank K
          (cohomologyOverField K g (SheafOfModules.unit (cover f φ K c).ringCatSheaf) 1)
        = Module.finrank K (cohomologyOverField K (coverMap f φ K c ≫ baseChangeSnd f K)
          (SheafOfModules.unit (cover f φ K c).ringCatSheaf) 1) := by
    rintro _ rfl
    rfl
  rw [genus_eq_finrank_cohomologyOverField_unit_one' K (coverSnd f φ K c),
    key _ (coverMap_snd f φ K c).symm,
    (cohomologyOverFieldPushforwardIsoOfIsAffineHom K (coverMap f φ K c) (baseChangeSnd f K)
      (SheafOfModules.unit _) 1).toLinearEquiv.finrank_eq,
    ← finrank_cohomologyOverField_eq_of_iso K (baseChangeSnd f K)
      (asIso (pushforwardDecomposition f n φ K c)) 1]
  have e1 := finrank_cohomologyOverField_eq_of_iso K (baseChangeSnd f K)
    ((Scheme.Modules.pullback (baseChangeFst f K)).mapBiproduct
      (fun i : Fin n => symPow f L i)) 1
  refine (congrArg (fun x : ℕ => (x : ℤ)) e1.symm).trans ?_
  have e2 := finrank_cohomologyOverField_eq_of_iso k f
    (biproduct.whiskerEquiv (f := fun j : ULift.{u} (Fin n) => symPow f L j.down)
      (g := fun i : Fin n => symPow f L i) (Equiv.ulift.{u} : ULift (Fin n) ≃ Fin n)
      (fun j => Iso.refl _)) 1
  rw [finrank_cohomologyOverField_baseChange_field k K (baseChangeFst f K) (baseChangeSnd f K) f
      (IsPullback.of_hasPullback _ _) _ 1, ← e2]
  have e3 := finrank_cohomologyOverField_biproduct k f
    (fun j : ULift.{u} (Fin n) => symPow f L j.down) 1
    (fun j => finiteDimensional_cohomologyOverField_symPow f j.down 1)
  have e4 : (∑ j : ULift.{u} (Fin n),
      Module.finrank k (cohomologyOverField k f (symPow f L j.down) 1)) =
      ∑ i : Fin n, Module.finrank k (cohomologyOverField k f (symPow f L i) 1) :=
    Equiv.sum_comp Equiv.ulift
      (fun i : Fin n => Module.finrank k (cohomologyOverField k f (symPow f L i) 1))
  rw [e3, e4]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [Fin.sum_univ_succ]
  have h0 : Module.finrank k (cohomologyOverField k f (symPow f L ((0 : Fin (m + 1)) : ℕ)) 1) =
      genus f := by
    change Module.finrank k (cohomologyOverField k f (symPow f L 0) 1) = _
    rw [finrank_cohomologyOverField_eq_of_iso k f (symPowIsoTensorPower f L 0) 1,
      genus_eq_finrank_cohomologyOverField_unit_one' k f]
    rfl
  have hs : ∀ j : Fin m, (Module.finrank k (cohomologyOverField k f
      (symPow f L ((Fin.succ j : Fin (m + 1)) : ℕ)) 1) : ℤ) = genus f - 1 := fun j => by
    rw [finrank_cohomologyOverField_eq_of_iso k f (symPowIsoTensorPower f L _) 1]
    exact finrank_cohomologyOverField_one_tensorPow f hdim hord (Nat.succ_pos _)
      (Fin.succ j).2
  push_cast
  rw [h0, Finset.sum_congr rfl fun j _ => hs j, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  ring

end GenusCover

end Stacks.CyclicCover

end
