module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineLocalization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivity
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.AssociatedPointsMono.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.RingTheory.Support.Finite
import all StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.GenericFlatness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A power of an ideal sheaf kills a coherent module exactly on the closed subscheme it cuts out

Let `X` be a Noetherian scheme, `F` a coherent `𝒪_X`-module and `I` a quasi-coherent sheaf of
ideals, cutting out the closed subscheme supported on `I.support`. Then `I ^ n F = 0` for some
`n` if and only if the support of `F` is contained in `I.support`.

## Main results

* `Stacks.IdealPowerSupport.exists_idealPowerMultiple_eq_bot_iff_supp_subset`.

## References

* [Stacks Project, Tag 01Y9](https://stacks.math.columbia.edu/tag/01Y9)
* [Stacks Project, Tag 00L6](https://stacks.math.columbia.edu/tag/00L6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Algebraization Stacks.AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.IdealPowerSupport

variable {X : Scheme.{u}}

/-- The subsheaf `I ^ n F` of a quasi-coherent module vanishes exactly when the submodule
`I(U) ^ n Γ(F, U)` vanishes for every affine open `U`: comparison of submodules of a sheaf of
modules is affine-local, and on an affine open the sections of `I ^ n F` are `I(U) ^ n Γ(F, U)`. -/
public lemma idealPowerMultiple_eq_bot_iff (I : X.IdealSheafData) (n : ℕ) (F : X.Modules)
    [F.IsQuasicoherent] :
    idealPowerMultiple I n F = ⊥ ↔
      ∀ U : X.affineOpens, I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) = ⊥ := by
  refine ⟨fun h U => ?_, fun h => le_antisymm ?_ bot_le⟩
  · rw [← idealPowerMultiple_toSubmodule_obj_affine I n F U, h]
    exact SheafOfModules.Submodule.bot_obj F _
  · refine submodule_le_of_affine _ _ fun U => ?_
    rw [idealPowerMultiple_toSubmodule_obj_affine I n F U, h U]
    exact bot_le

/-- Every prime of the ring of functions on an affine open is the prime of a point of that
open. -/
public lemma exists_primeIdealOf (U : X.affineOpens) (p : PrimeSpectrum Γ(X, U.1)) :
    ∃ (x : X) (hx : x ∈ U.1), U.2.primeIdealOf ⟨x, hx⟩ = p := by
  have hz : ∃ z : ↥U.1, U.2.primeIdealOf z = p :=
    ⟨U.2.isoSpec.inv p, AssociatedPointsMono.primeIdealOf_isoSpec_inv U.2 p⟩
  obtain ⟨z, hz⟩ := hz
  exact ⟨z.1, z.2, hz⟩

/-- If the support of a quasi-coherent module is contained in the support of an ideal sheaf,
then on every affine open the support of the module of sections is contained in the zero locus
of the ideal of sections. -/
public lemma support_sections_subset_zeroLocus (I : X.IdealSheafData) (F : X.Modules)
    [F.IsQuasicoherent] (h : SheafOfModules.supp F ⊆ (I.support : Set X)) (U : X.affineOpens) :
    Module.support Γ(X, U.1) Γ(F, U.1) ⊆
      PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(X, U.1)) := by
  intro p hp
  obtain ⟨x, hx, hxp⟩ := exists_primeIdealOf U p
  subst hxp
  exact ideal_le_primeIdealOf_of_mem_support I U hx
    (h ((Scheme.Modules.mem_support_sections_iff_mem_supp F U x hx).1 hp))

/-- A point at which a function of an affine open is nonzero does not have that function in its
prime. This is the converse of
`Stacks.Algebraization.mem_primeIdealOf_of_notMem_basicOpen`. -/
public lemma notMem_basicOpen_of_mem_primeIdealOf (U : X.affineOpens) {x : X} (hx : x ∈ U.1)
    (f : Γ(X, U.1)) (h : f ∈ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal) : x ∉ X.basicOpen f := by
  intro hxf
  have h1 : U.2.fromSpec (U.2.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen f := by
    rw [U.2.fromSpec_primeIdealOf ⟨x, hx⟩]; exact hxf
  have h2 : U.2.primeIdealOf ⟨x, hx⟩ ∈ U.2.fromSpec ⁻¹ᵁ (X.basicOpen f) := h1
  rw [U.2.fromSpec_preimage_basicOpen] at h2
  exact ((PrimeSpectrum.mem_basicOpen f _).1 h2) h

/-- A point of the zero locus of the ideal of sections on an affine open containing it lies in
the support of the ideal sheaf. -/
public lemma mem_support_of_ideal_le_primeIdealOf (I : X.IdealSheafData) (U : X.affineOpens)
    {x : X} (hx : x ∈ U.1) (h : I.ideal U ≤ (U.2.primeIdealOf ⟨x, hx⟩).asIdeal) :
    x ∈ I.support := by
  rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := U) hx, Scheme.mem_zeroLocus_iff]
  exact fun f hf => notMem_basicOpen_of_mem_primeIdealOf U hx f (h hf)

/-- A function on an affine open which annihilates the sections of a quasi-coherent module over
that open annihilates the sections over every smaller open.

The section is zero as soon as all its germs are, and at a point of the smaller open the germ
is computed in the stalk, which the germ map from the affine open exhibits as a localization of
the sections over it: an element of the stalk becomes the germ of a section over the affine open
after multiplication by a function invertible at the point, and that function acts invertibly on
the stalk. -/
public lemma smul_restrict_eq_zero (F : X.Modules) [F.IsQuasicoherent]
    {V : X.Opens} (hV : IsAffineOpen V) {W : X.Opens} (hWV : W ≤ V)
    (a : Γ(X, V)) (ha : ∀ s : Γ(F, V), a • s = 0) (t : Γ(F, W)) :
    (X.presheaf.map (homOfLE hWV).op a) • t = 0 := by
  refine TopCat.Presheaf.section_ext (⟨F.presheaf, F.isSheaf⟩ : TopCat.Sheaf Ab.{u} X) W _ 0 ?_
  intro y hyW
  rw [map_zero]
  have hyV : y ∈ V := hWV hyW
  let : Module (X.presheaf.stalk y) (F.presheaf.stalk y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val y
  let := affineStalkModule F W y hyW
  let := affineStalkModule F V y hyV
  let : Algebra Γ(X, V) (X.presheaf.stalk y) := (X.presheaf.germ V y hyV).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk y) (hV.primeIdealOf ⟨y, hyV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨y, hyV⟩
  have _hloc := affineGerm_isLocalized F V hV y hyV
  -- the germ of the restricted scalar multiple is the scalar multiple of the germ, taken in
  -- the module structure coming from `V`
  have hstep : (F.presheaf.germ W y hyW) ((X.presheaf.map (homOfLE hWV).op a) • t)
      = a • (F.presheaf.germ W y hyW t) := by
    have h1 : (affineGerm F W y hyW) ((X.presheaf.map (homOfLE hWV).op a) • t)
        = (X.presheaf.map (homOfLE hWV).op a) • (affineGerm F W y hyW t) :=
      (affineGerm F W y hyW).map_smul _ _
    refine h1.trans ?_
    show (X.presheaf.germ W y hyW).hom ((X.presheaf.map (homOfLE hWV).op) a) •
        (F.presheaf.germ W y hyW t) = (X.presheaf.germ V y hyV).hom a •
          (F.presheaf.germ W y hyW t)
    rw [TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hWV) y hyW a]
  rw [hstep]
  -- the germ of `t` becomes the germ of a section over `V` after an invertible multiplication
  obtain ⟨⟨m₀, c⟩, hc⟩ := IsLocalizedModule.surj
    (hV.primeIdealOf ⟨y, hyV⟩).asIdeal.primeCompl (affineGerm F V y hyV)
    (F.presheaf.germ W y hyW t)
  have hunit : IsUnit ((X.presheaf.germ V y hyV).hom (c : Γ(X, V))) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk y)
      (hV.primeIdealOf ⟨y, hyV⟩).asIdeal (c : Γ(X, V))).mpr c.2
  refine hunit.smul_left_cancel.mp ?_
  show (X.presheaf.germ V y hyV).hom (c : Γ(X, V)) • (a • (F.presheaf.germ W y hyW t))
      = (X.presheaf.germ V y hyV).hom (c : Γ(X, V)) • (0 : F.presheaf.stalk y)
  rw [smul_zero]
  have hcomm : (X.presheaf.germ V y hyV).hom (c : Γ(X, V)) •
      (a • (F.presheaf.germ W y hyW t))
      = a • ((c : Γ(X, V)) • (F.presheaf.germ W y hyW t)) := by
    show (X.presheaf.germ V y hyV).hom (c : Γ(X, V)) •
        ((X.presheaf.germ V y hyV).hom a • (F.presheaf.germ W y hyW t))
      = (X.presheaf.germ V y hyV).hom a •
        ((X.presheaf.germ V y hyV).hom (c : Γ(X, V)) • (F.presheaf.germ W y hyW t))
    rw [smul_smul, smul_smul, mul_comm]
  have hc' : (c : Γ(X, V)) • (F.presheaf.germ W y hyW t) = affineGerm F V y hyV m₀ := hc
  rw [hcomm, hc', ← map_smul, ha m₀, map_zero]

/-- The ideal of sections over a smaller affine open is generated by the restrictions of the
ideal of sections over the larger one, also after taking powers. -/
private lemma map_ideal_pow (I : X.IdealSheafData) {V W : X.affineOpens} (hWV : W ≤ V) (m : ℕ) :
    Ideal.map (X.presheaf.map (homOfLE hWV).op).hom (I.ideal V ^ m) = I.ideal W ^ m := by
  rw [Ideal.map_pow, I.map_ideal hWV]

/-- The vanishing of `I(V) ^ m Γ(F, V)` on an affine open passes to affine opens contained in
it: the ideal of sections over the smaller open is generated by the restrictions of the ideal of
sections over the larger one. -/
public lemma smul_pow_eq_bot_of_le (I : X.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent]
    {V W : X.affineOpens} (hWV : W ≤ V) {m : ℕ}
    (h : I.ideal V ^ m • (⊤ : Submodule Γ(X, V.1) Γ(F, V.1)) = ⊥) :
    I.ideal W ^ m • (⊤ : Submodule Γ(X, W.1) Γ(F, W.1)) = ⊥ := by
  refine le_antisymm ?_ bot_le
  rw [← map_ideal_pow I hWV]
  refine Submodule.smul_le.2 ?_
  intro a ha
  induction ha using Submodule.span_induction with
  | mem a hmem =>
      obtain ⟨a₀, ha₀, rfl⟩ := hmem
      intro t _
      rw [Submodule.mem_bot]
      refine smul_restrict_eq_zero F V.2 hWV a₀ (fun s => ?_) t
      have := Submodule.smul_mem_smul ha₀ (Submodule.mem_top (R := Γ(X, V.1)) (x := s))
      rwa [h, Submodule.mem_bot] at this
  | zero => intro t _; rw [zero_smul]; exact Submodule.zero_mem _
  | add a b _ _ h₁ h₂ =>
      intro t ht
      rw [add_smul]
      exact Submodule.add_mem _ (h₁ t ht) (h₂ t ht)
  | smul r a _ h₁ =>
      intro t ht
      rw [smul_eq_mul, mul_smul]
      exact Submodule.smul_mem _ _ (h₁ t ht)

/-- An affine open neighbourhood of a point inside a given open: the affine opens are a basis. -/
public lemma exists_affineOpens_le (U : X.Opens) {y : X} (hy : y ∈ U) :
    ∃ W : X.affineOpens, W.1 ≤ U ∧ y ∈ W.1 := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hy U.2
  exact ⟨⟨W, hW⟩, hWU, hyW⟩

/-- Raising the exponent preserves the vanishing of `I(U) ^ k Γ(F, U)`. -/
public lemma smul_pow_eq_bot_of_le_exponent (I : X.IdealSheafData) (F : X.Modules)
    (U : X.affineOpens) {k n : ℕ} (hkn : k ≤ n)
    (h : I.ideal U ^ k • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) = ⊥) :
    I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) = ⊥ :=
  le_antisymm (h.le.trans' (Submodule.smul_mono_left (Ideal.pow_le_pow_right hkn))) bot_le

/-- Tag 00L6 for the sections of a coherent module on an affine open of a Noetherian scheme. -/
private lemma exists_pow_smul_top_eq_bot_iff (I : X.IdealSheafData) (F : X.Modules)
    [IsNoetherian X] [F.IsQuasicoherent] [F.IsFiniteType] (U : X.affineOpens) :
    (∃ k : ℕ, I.ideal U ^ k • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) = ⊥) ↔
      Module.support Γ(X, U.1) Γ(F, U.1) ⊆ PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(X, U.1)) := by
  have _hnoeth : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have _hfin : Module.Finite Γ(X, U.1) Γ(F, U.1) := moduleFinite_sections_on_affine F U.1 U.2
  exact main_theorem_00l6 (I.ideal U)

/-- **Stacks Project, Tag 01Y9.** Let `X` be a Noetherian scheme, `I` a quasi-coherent sheaf of
ideals and `F` a coherent `𝒪_X`-module — here a quasi-coherent module of finite type, which on a
locally Noetherian scheme is the same thing by Tag 01XZ. Then some power of `I` annihilates `F`
if and only if the support of `F` is contained in the closed set cut out by `I`.

Both directions are affine-local, with the algebraic content supplied by Tag 00L6 over the
Noetherian ring of sections on an affine open: a power of an ideal kills a finite module exactly
when the support of the module lies in the zero locus of the ideal. For the forward direction one
affine open containing the point suffices. For the converse the exponent must be chosen uniformly,
and that is where quasi-compactness enters: finitely many affine opens cover `X`, the largest of
their exponents works on each of them, and `smul_pow_eq_bot_of_le` carries the vanishing from a
member of the cover to any affine open inside it, which is enough to conclude by sheaf
separation. -/
@[stacks 01Y9, ega "I 9.3.4"]
public theorem exists_idealPowerMultiple_eq_bot_iff_supp_subset {X : Scheme.{u}}
    [IsNoetherian X] (F : X.Modules) [_root_.SheafOfModules.IsCoherent F]
    (I : X.IdealSheafData) :
    (∃ n : ℕ, idealPowerMultiple I n F = ⊥) ↔
      SheafOfModules.supp F ⊆ (I.support : Set X) := by
  classical
  have _hqc : F.IsQuasicoherent := @_root_.isQuasicoherent_of_isCoherent _ _ _ F inferInstance
  have _hft : F.IsFiniteType :=
    @_root_.SheafOfModules.IsCoherent.isFiniteType _ _ _ F inferInstance
  constructor
  · rintro ⟨n, hn⟩ x hx
    obtain ⟨U, -, hxU⟩ := exists_affineOpens_le (⊤ : X.Opens) (show x ∈ (⊤ : X.Opens) from trivial)
    have hsupp := (exists_pow_smul_top_eq_bot_iff I F U).1
      ⟨n, (idealPowerMultiple_eq_bot_iff I n F).1 hn U⟩
    refine mem_support_of_ideal_le_primeIdealOf I U hxU fun f hf => ?_
    exact hsupp ((Scheme.Modules.mem_support_sections_iff_mem_supp F U x hxU).2 hx) hf
  · intro h
    -- the exponent on each affine open, from Tag 00L6
    have key : ∀ U : X.affineOpens,
        ∃ k : ℕ, I.ideal U ^ k • (⊤ : Submodule Γ(X, U.1) Γ(F, U.1)) = ⊥ := fun U =>
      (exists_pow_smul_top_eq_bot_iff I F U).2 (support_sections_subset_zeroLocus I F h U)
    choose nU hnU using key
    -- a finite affine cover, over which the exponent is maximised
    obtain ⟨s, hs⟩ := (isCompact_univ (X := X)).elim_finite_subcover
      (fun U : X.affineOpens => (U.1 : Set X)) (fun U => U.1.2) fun x _ => by
        obtain ⟨U, -, hxU⟩ :=
          exists_affineOpens_le (⊤ : X.Opens) (show x ∈ (⊤ : X.Opens) from trivial)
        exact Set.mem_iUnion.2 ⟨U, hxU⟩
    refine ⟨s.sup nU, (idealPowerMultiple_eq_bot_iff I _ F).2 fun U => ?_⟩
    refine le_antisymm (Submodule.smul_le.2 fun a ha t _ => ?_) bot_le
    rw [Submodule.mem_bot]
    refine TopCat.Presheaf.IsSheaf.section_ext F.isSheaf (U := op U.1) fun y hyU => ?_
    obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ y))
    obtain ⟨W, hWle, hyW⟩ :=
      exists_affineOpens_le (U.1 ⊓ (i : X.affineOpens).1) ⟨hyU, hyi⟩
    have hWU : W.1 ≤ U.1 := hWle.trans inf_le_left
    have hWi : W ≤ i := hWle.trans inf_le_right
    have hzero : I.ideal W ^ s.sup nU • (⊤ : Submodule Γ(X, W.1) Γ(F, W.1)) = ⊥ :=
      smul_pow_eq_bot_of_le I F hWi
        (smul_pow_eq_bot_of_le_exponent I F i (Finset.le_sup hi) (hnU i))
    have hmem : (X.presheaf.map (homOfLE hWU).op) a ∈ I.ideal W ^ s.sup nU :=
      map_ideal_pow I (V := U) hWU _ ▸ Ideal.mem_map_of_mem _ ha
    refine ⟨W.1, hWU, hyW, ?_⟩
    have hsm := Submodule.smul_mem_smul hmem (Submodule.mem_top (R := Γ(X, W.1))
      (x := (F.presheaf.map (homOfLE hWU).op) t))
    rw [hzero, Submodule.mem_bot] at hsm
    rw [map_zero, Scheme.Modules.map_smul F (homOfLE hWU) a t]
    exact hsm

end Stacks.IdealPowerSupport
