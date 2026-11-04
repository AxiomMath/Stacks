module

public import StacksFrontier.AlgebraicGeometry.Perfect.BeilinsonTwistGeneration
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.TotalExtDimensionOverAFieldGeneral
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.CoherentCharacterization
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.PerfectTensorInternalHom
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectNotFibrewise
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasicoherentWeakSerre
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.Vanishing
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Characterizing bounded coherent complexes on projective space over a field

Let `k` be a field, `n ≥ 0` and `K` an object of `D_QCoh(𝒪_{ℙⁿ_k})`. [Stacks, Tag 0FYB] says
that the following are equivalent:

1. `K` is in `D^b_{Coh}(𝒪_{ℙⁿ_k})`;
2. `∑_{i ∈ ℤ} dim_k H^i(ℙⁿ_k, E ⊗^𝐋 K) < ∞` for each perfect object `E` of `D(𝒪_{ℙⁿ_k})`;
3. `∑_{i ∈ ℤ} dim_k Ext^i_{ℙⁿ_k}(E, K) < ∞` for each perfect object `E` of `D(𝒪_{ℙⁿ_k})`;
4. `∑_{i ∈ ℤ} dim_k H^i(ℙⁿ_k, K ⊗^𝐋 𝒪_{ℙⁿ_k}(d)) < ∞` for `d = 0, 1, …, n`.

This file proves the equivalence, the four conditions being `IsBoundedCoherent`,
`HasFiniteTotalTensorCohomology`, `HasFiniteTotalPerfectExt` and `HasFiniteTotalTwistCohomology`.

## The argument

* (1) ⟹ (3) is [Stacks, Tag 0FYC], `ℙⁿ_k` being proper over `k`.
* (1) ⟹ (2): for `E` perfect, `E ⊗^𝐋 K` is again in `D^b_{Coh}` ([Stacks, Tag 0FXU] (3)), and
  `H^i(ℙⁿ_k, -) = Ext^i(𝒪, -)` with `𝒪` perfect, so (1) ⟹ (3) applies to it.
* (2) ⟹ (4) is `hasFiniteTotalTwistCohomology_of_hasFiniteTotalTensorCohomology`.
* (4) ⟹ (1) and (3) ⟹ (1). The source passes through Beilinson's equivalence
  `D(R) ≃ D_QCoh(𝒪_{ℙⁿ_k})` of [Stacks, Tag 0BQU] and the compactness criterion of
  [Stacks, Tag 0FYA] over `R`; what those two results are used for is that an object of
  `D_QCoh` with finite total cohomology against the generator `P = 𝒪 ⊕ ⋯ ⊕ 𝒪(-n)` is perfect,
  and the proof below shows exactly that, directly in `D_QCoh(𝒪_{ℙⁿ_k})`, by the argument behind
  [Stacks, Tag 0FYA]: `𝒪, 𝒪(-1), …, 𝒪(-n)` is a semi-orthogonal family of exceptional objects
  (`Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.twistProbe_orth` and its
  companions, from [Stacks, Tag 01XT]) which detects the zero object of `D_QCoh`
  (`Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.isZero_of_hom_twistSingle_eq_zero`,
  [Stacks, Tag 0A9V]), so killing the finitely many morphisms out of `𝒪`, then out of `𝒪(-1)`,
  and so on, by cones, builds `K` out of shifts of the twists by finitely many extensions
  (`Stacks.Triangulated.ProbeKilling.mem_of_probes`). Hence `K` is perfect, and a perfect object
  on a Noetherian scheme is in `D^b_{Coh}` ([Stacks, Tag 0FXU] (1)); this replaces the source's
  appeal to [Stacks, Tag 09M1] and [Stacks, Tag 0FDC], whose conclusion it is. For (4) the
  morphisms out of `𝒪(-a)[0]` are measured as `H^i(ℙⁿ_k, K ⊗^𝐋 𝒪(a))` through the twisting
  autoequivalence; for (3) they are measured directly.

## Main results

* `Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.tfae_isBoundedCoherent`:
  **[Stacks, Tag 0FYB]**: for `K` in `D_QCoh(𝒪_{ℙⁿ_k})`, the four conditions above are
  equivalent.

## References

* [Stacks Project, Tag 0FYB](https://stacks.math.columbia.edu/tag/0FYB)
* [Stacks Project, Tag 0FYA](https://stacks.math.columbia.edu/tag/0FYA)
* [Stacks Project, Tag 0BQU](https://stacks.math.columbia.edu/tag/0BQU)
* [Stacks Project, Tag 0A9V](https://stacks.math.columbia.edu/tag/0A9V)
* [Stacks Project, Tag 0FYC](https://stacks.math.columbia.edu/tag/0FYC)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
* [Stacks Project, Tag 09M1](https://stacks.math.columbia.edu/tag/09M1)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)
open Stacks.Triangulated.ProbeKilling

namespace Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization

universe u

attribute [local instance 100000] HasDerivedCategory.standard
attribute [local instance] opensSheafTensorAdditive opensSheafTensorObjAdditive
  opensHasMapBifunctorSheafTensor

variable (k : Type u) [Field k] (n : ℕ)

/-! ### Finiteness from [Stacks, Tag 0FYC] -/

/-- The structure morphism `ℙⁿ_k → Spec k` is proper. -/
instance isProper_projSpaceOver : IsProper (projSpaceOver k n).hom :=
  isProper_projectiveSpaceOver n (Spec (CommRingCat.of k))

/-- Projective space `ℙⁿ_k` over a field is a Noetherian scheme. -/
instance isNoetherian_projSpace : IsNoetherian (projectiveSpaceOverRing n (CommRingCat.of k)) :=
  Stacks.AlgebraicGeometry.ProperSupportCoherent.isNoetherian_of_isProper_over_field
    (projSpaceOver k n)

/-- Global sections on the homotopy category of complexes of `𝒪_{ℙⁿ_k}`-modules, followed by the
localization to `D(Γ(ℙⁿ_k, 𝒪))`. -/
abbrev homotopySections :
    HomotopyCategory (projSpaceOver k n).left.Modules (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{u} Γ((projSpaceOver k n).left, ⊤)) :=
  (Stacks.Cohomology.sectionsFunctor (projSpaceOver k n).left ⊤).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The functor `homotopySections k n` has a right derived functor with respect to
quasi-isomorphisms. -/
instance hasRightDerivedFunctor_homotopySections :
    (homotopySections k n).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  AlgebraicGeometry.Scheme.Modules.hasRightDerivedFunctor _ _

/-- The total right derived functor of `homotopySections k n`, with its unit, is a right derived
functor with respect to quasi-isomorphisms. -/
instance isRightDerivedFunctor_homotopySections :
    ((homotopySections k n).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))).IsRightDerivedFunctor
      ((homotopySections k n).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
      (HomotopyCategory.quasiIso (projSpaceOver k n).left.Modules (ComplexShape.up ℤ)) :=
  inferInstance

/-- **[Stacks, Tag 0FYC] on `ℙⁿ_k`**: for `E` perfect and `L` in `D^b_{Coh}(𝒪_{ℙⁿ_k})`,
`∑_{i ∈ ℤ} dim_k Ext^i(E, L) < ∞`. -/
theorem hasFiniteTotalExt_of_isPerfect_of_isBoundedCoherent
    (E L : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (projectiveSpaceOverRing n (CommRingCat.of k)).toRingedSpace) E)
    (hL : IsBoundedCoherent k n L) :
    HasFiniteTotalExt k (projSpaceOver k n) E L :=
  (DerivedVarieties.CoherentCharacterization.cardinalSum_rank_ext_lt_aleph0_iff_hasFiniteTotalExt
      (projSpaceOver k n) E L).1
    (Stacks.AlgebraicGeometry.ProperSupportCoherent.cardinalSum_rank_ext_lt_aleph0_general
      (projSpaceOver k n)
      ((homotopySections k n).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
      ((homotopySections k n).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)))
      E L hE hL)

/-- **Each twist placed in degree zero is perfect.** -/
theorem isPerfect_twistSingle (d : ℤ) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (projectiveSpaceOverRing n (CommRingCat.of k)).toRingedSpace) (twistSingle k n d) :=
  isPerfect_singleFunctor_twistOver n (Spec (CommRingCat.of k)) d

/-- **[Stacks, Tag 0FYC] out of `𝒪_X[0]`**: for `L` in `D^b_{Coh}(𝒪_{ℙⁿ_k})`,
`∑_{i ∈ ℤ} dim_k H^i(ℙⁿ_k, L) < ∞`, the structure sheaf being perfect. -/
theorem hasFiniteTotalExt_unitObject_of_isBoundedCoherent
    (L : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
    (hL : IsBoundedCoherent k n L) :
    HasFiniteTotalExt k (projSpaceOver k n)
      (Stacks.DerivedTensor.RingedSite.unitObject (projSpaceSite k n)) L :=
  (hasFiniteTotalExt_of_isPerfect_of_isBoundedCoherent k n _ L (isPerfect_twistSingle k n 0)
    hL).of_iso_left (twistSingleZeroIso k n)

/-- **Each twist placed in degree zero is in `D^b_{Coh}`**: it is invertible, hence coherent on
the Noetherian scheme `ℙⁿ_k`. -/
theorem isBoundedCoherent_twistSingle (d : ℤ) : IsBoundedCoherent k n (twistSingle k n d) :=
  AlgebraicGeometry.derivedCategoryBBounded_singleFunctor_obj _ _
    (@Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible _ _ _
      ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
        (projectiveSpaceOverRing n (CommRingCat.of k)).sheaf.obj
        (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf.property
        (twistOver n (Spec (CommRingCat.of k)) d)).mpr
        (ProjTwistTensorPow.isInvertibleModule_twistOver n (Spec (CommRingCat.of k)) d)))

/-! ### The probes -/

/-- The plain probe of `𝒪(-a)[0]`, measured through the identity functor. -/
def plainProbe (a : ℤ) :
    Probe (DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) where
  P := twistSingle k n (-a)
  U := twistSingle k n (-a)
  G := 𝟭 _
  ff := Functor.FullyFaithful.id _
  ι := Iso.refl _

/-- The `k`-linear structure on `𝒪_{ℙⁿ_k}`-modules, induced by the structure morphism. -/
abbrev projLinear : Linear k (projectiveSpaceOverRing n (CommRingCat.of k)).Modules :=
  AlgebraicGeometry.modulesLinear k (projSpaceOver k n)

/-- Finite total `Ext` is the finiteness measured by a probe whose source object is the source of
the `Ext`. -/
theorem probe_FT_iff
    (p : Probe (DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules))
    (Y : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) :
    letI := projLinear k n
    p.FT k Y ↔ HasFiniteTotalExt k (projSpaceOver k n) p.U (p.G.obj Y) := by
  let := projLinear k n
  unfold Probe.FT HasFiniteTotalExt
  simp only [not_subsingleton_iff_nontrivial]
  rfl

/-- **The finiteness hypothesis on the probe objects, for the twisted probes**: the measured
morphisms out of the probe of `𝒪(-b)` into `𝒪(-a)[0]` are `Ext^•(𝒪, 𝒪(b - a))`. -/
theorem twistProbe_FT (a b : ℤ) :
    letI := projLinear k n
    (twistProbe k n b).FT k (twistProbe k n a).P := by
  let := projLinear k n
  rw [probe_FT_iff]
  exact (hasFiniteTotalExt_unitObject_of_isBoundedCoherent k n _
    (isBoundedCoherent_twistSingle k n (-a + b))).of_iso_right
      (twistSingleTensorIso k n (-a) b).symm

/-- **The finiteness hypothesis on the probe objects, for the plain probes.** -/
theorem plainProbe_FT (a b : ℤ) :
    letI := projLinear k n
    (plainProbe k n b).FT k (plainProbe k n a).P := by
  let := projLinear k n
  rw [probe_FT_iff]
  exact hasFiniteTotalExt_of_isPerfect_of_isBoundedCoherent k n _ _ (isPerfect_twistSingle k n _)
    (isBoundedCoherent_twistSingle k n _)

/-! ### (4) ⟹ (1) and (3) ⟹ (1) -/

/-- `D_QCoh(𝒪_{ℙⁿ_k})` is a triangulated subcategory of `D(𝒪_{ℙⁿ_k})`. -/
private theorem isTriangulated_derivedCategoryB_projSpace :
    (DerivedCategoryB.derivedCategoryB
      (A := (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
      (SheafOfModules.isQuasicoherent
        (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf)).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre
      (projectiveSpaceOverRing n (CommRingCat.of k)))

/-- The objects with quasi-coherent cohomology sheaves are closed under cones. -/
theorem qcoh_obj₃ (T : Pretriangulated.Triangle
      (DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules))
    (hT : T ∈ distTriang _)
    (h₁ : DerivedCategoryB.derivedCategoryB
      (A := (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
      (SheafOfModules.isQuasicoherent (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf)
      T.obj₁)
    (h₂ : DerivedCategoryB.derivedCategoryB
      (A := (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
      (SheafOfModules.isQuasicoherent (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf)
      T.obj₂) :
    DerivedCategoryB.derivedCategoryB
      (A := (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
      (SheafOfModules.isQuasicoherent (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf)
      T.obj₃ := by
  have := isTriangulated_derivedCategoryB_projSpace k n
  have := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms
    (A := (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre
      (projectiveSpaceOverRing n (CommRingCat.of k)))
  exact ObjectProperty.ext_of_isTriangulatedClosed₂ _ T.rotate
    (Pretriangulated.rot_of_distTriang T hT) h₂ (ObjectProperty.le_shift _ 1 _ h₁)

/-- The shifts of the twists have quasi-coherent cohomology sheaves. -/
theorem qcoh_twistSingle_shift (d m : ℤ) :
    DerivedCategoryB.derivedCategoryB
      (A := (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
      (SheafOfModules.isQuasicoherent (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf)
      ((twistSingle k n d)⟦m⟧) := by
  have := isTriangulated_derivedCategoryB_projSpace k n
  exact ObjectProperty.le_shift _ m _
    (Stacks.Duality.DerivedPushforward.derivedCategoryB_singleFunctor_obj _ inferInstance)

/-- A zero object of `D(𝒪_{ℙⁿ_k})` is perfect: it is the cone of an identity. -/
theorem isPerfect_of_isZero_projSpace
    (Y : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) (hY : IsZero Y) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (projectiveSpaceOverRing n (CommRingCat.of k)).toRingedSpace) Y := by
  let U := twistSingle k n 0
  let T := Pretriangulated.Triangle.mk (𝟙 U) (0 : U ⟶ Y) 0
  have hT : T ∈ distTriang _ :=
    Pretriangulated.isomorphic_distinguished _ (Pretriangulated.contractible_distinguished U) _
      (Pretriangulated.Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _)
        (hY.iso (isZero_zero _)) (by simp [T]; rfl) ((isZero_zero _).eq_of_tgt _ _)
        (hY.eq_of_src _ _))
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₃_of_distinguished T hT
    (isPerfect_twistSingle k n 0) (isPerfect_twistSingle k n 0)

/-- **The core of (4) ⟹ (1) and (3) ⟹ (1).** Let `p a` be probes of the twists `𝒪(-a)[0]`,
`0 ≤ a ≤ n`, satisfying the finiteness hypothesis on the probe objects. An object of
`D_QCoh(𝒪_{ℙⁿ_k})` with finite total measured `Hom` from every `p a` is perfect. -/
theorem isPerfect_of_probes
    (p : ℕ → Probe (DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules))
    (hP : ∀ a : ℕ, (p a).P = twistSingle k n (-(a : ℤ)))
    (hfin : letI := projLinear k n; ∀ a b : ℕ, (p b).FT k (p a).P)
    (K : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
    (hK : ∀ i, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherent)
    (hFT : letI := projLinear k n; ∀ a : ℕ, a ≤ n → (p a).FT k K) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (projectiveSpaceOverRing n (CommRingCat.of k)).toRingedSpace) K := by
  let := projLinear k n
  refine mem_of_probes k (n + 1) p
    (DerivedCategoryB.derivedCategoryB
      (A := (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
      (SheafOfModules.isQuasicoherent (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf))
    (Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (projectiveSpaceOverRing n (CommRingCat.of k)).toRingedSpace))
    (qcoh_obj₃ k n)
    (fun a _ m => by rw [hP a]; exact qcoh_twistSingle_shift k n _ m)
    (fun T hT h₁ h₃ =>
      Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished T hT h₁ h₃)
    (isPerfect_of_isZero_projSpace k n)
    (fun a _ m => by
      rw [hP a]
      exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_shift
        (isPerfect_twistSingle k n _) m)
    (fun a _ e he => by
      revert e
      rw [hP a]
      exact twistProbe_isIso_of_ne_zero k n a)
    (fun a _ => by rw [hP a]; exact twistProbe_not_isZero k n a)
    (fun a _ m hm => by rw [hP a]; exact twistProbe_self_shift k n a m hm)
    (fun a ha b hb j => by
      rw [hP a, hP b]
      exact twistProbe_orth k n a b (by omega) (by exact_mod_cast hb) (by omega) j)
    (fun a _ b _ _ => hfin a b)
    (fun Y hY hO => isZero_of_hom_twistSingle_eq_zero k n Y hY fun a ha j => by
      have := hO a (by omega) j
      rwa [hP a] at this)
    K hK (fun a ha => hFT a (by omega))

/-! ### The equivalence -/

/-- **(1) ⟹ (3).** -/
theorem hasFiniteTotalPerfectExt_of_isBoundedCoherent
    (K : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
    (hK : IsBoundedCoherent k n K) : HasFiniteTotalPerfectExt k n K :=
  fun E hE => hasFiniteTotalExt_of_isPerfect_of_isBoundedCoherent k n E K hE hK

/-- **(1) ⟹ (2).** -/
theorem hasFiniteTotalTensorCohomology_of_isBoundedCoherent
    (K : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
    (hK : IsBoundedCoherent k n K) : HasFiniteTotalTensorCohomology k n K :=
  fun E hE => hasFiniteTotalExt_unitObject_of_isBoundedCoherent k n _
    (Stacks.AlgebraicGeometry.PerfectCohomology.derivedCategoryBBounded_coherent_of_isPerfect
      (projectiveSpaceOverRing n (CommRingCat.of k)) E K hE hK).1

/-- **(4) ⟹ (1)**, for `K` in `D_QCoh(𝒪_{ℙⁿ_k})`. -/
theorem isBoundedCoherent_of_hasFiniteTotalTwistCohomology
    (K : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
    (hqc : ∀ i, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherent)
    (hK : HasFiniteTotalTwistCohomology k n K) : IsBoundedCoherent k n K :=
  Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect _ K
    (isPerfect_of_probes k n (fun a => twistProbe k n a) (fun _ => rfl)
      (fun a b => twistProbe_FT k n a b) K hqc
      (fun a ha => (probe_FT_iff k n _ K).2 (hK a ha)))

/-- **(3) ⟹ (1)**, for `K` in `D_QCoh(𝒪_{ℙⁿ_k})`. -/
theorem isBoundedCoherent_of_hasFiniteTotalPerfectExt
    (K : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
    (hqc : ∀ i, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherent)
    (hK : HasFiniteTotalPerfectExt k n K) : IsBoundedCoherent k n K :=
  Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect _ K
    (isPerfect_of_probes k n (fun a => plainProbe k n a) (fun _ => rfl)
      (fun a b => plainProbe_FT k n a b) K hqc
      (fun _ _ => (probe_FT_iff k n _ K).2 (hK _ (isPerfect_twistSingle k n _))))

/-- **[Stacks, Tag 0FYB].** Let `k` be a field, let `n ≥ 0` and let `K` be an object of
`D_QCoh(𝒪_{ℙⁿ_k})`, that is, an object of `D(𝒪_{ℙⁿ_k})` whose cohomology sheaves are
quasi-coherent. The following are equivalent:

1. `K` is in `D^b_{Coh}(𝒪_{ℙⁿ_k})`;
2. `∑_{i ∈ ℤ} dim_k H^i(ℙⁿ_k, E ⊗^𝐋 K) < ∞` for each perfect object `E` of `D(𝒪_{ℙⁿ_k})`;
3. `∑_{i ∈ ℤ} dim_k Ext^i_{ℙⁿ_k}(E, K) < ∞` for each perfect object `E` of `D(𝒪_{ℙⁿ_k})`;
4. `∑_{i ∈ ℤ} dim_k H^i(ℙⁿ_k, K ⊗^𝐋 𝒪_{ℙⁿ_k}(d)) < ∞` for `d = 0, 1, …, n`.

The four conditions are `IsBoundedCoherent`, `HasFiniteTotalTensorCohomology`,
`HasFiniteTotalPerfectExt` and `HasFiniteTotalTwistCohomology`; a finite sum of dimensions over
`k` is expressed as every term being a finite `k`-module and only finitely many being nonzero.
See the module documentation for the argument. -/
@[stacks 0FYB]
theorem tfae_isBoundedCoherent
    (K : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
    (hqc : ∀ i, ((DerivedCategory.homologyFunctor _ i).obj K).IsQuasicoherent) :
    List.TFAE [IsBoundedCoherent k n K, HasFiniteTotalTensorCohomology k n K,
      HasFiniteTotalPerfectExt k n K, HasFiniteTotalTwistCohomology k n K] := by
  tfae_have 1 → 2 := hasFiniteTotalTensorCohomology_of_isBoundedCoherent k n K
  tfae_have 2 → 4 := hasFiniteTotalTwistCohomology_of_hasFiniteTotalTensorCohomology k n K
  tfae_have 4 → 1 := isBoundedCoherent_of_hasFiniteTotalTwistCohomology k n K hqc
  tfae_have 1 → 3 := hasFiniteTotalPerfectExt_of_isBoundedCoherent k n K
  tfae_have 3 → 1 := isBoundedCoherent_of_hasFiniteTotalPerfectExt k n K hqc
  tfae_finish

end Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization

end
