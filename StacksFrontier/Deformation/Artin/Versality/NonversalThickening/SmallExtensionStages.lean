module

public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Thickenings
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFunctor
import StacksFrontier.Deformation.ArtinCriteria.TangentSpace

/-!
# Fibre products of rings and stages of small extensions

Ring-theoretic and lifting input for the one-point thickening witnessing failure of versality:
cardinality bounds for Artinian local algebras; the fibre product `A ×_C B` of commutative rings,
whose spectrum is the pushout of spectra and whose projection to `A` is a first order thickening
when `B ⟶ C` is a small extension, with kernel identified with the residue field; and a failed
Artinian lift from non-versality, located at one stage of a factorisation of a surjection of
Artinian local algebras into small extensions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal TopologicalSpace
open Stacks.Thickenings

namespace Deformation.Artin

universe u v w

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
attribute [local instance_reducible] CategoryTheory.Over.post
attribute [local instance] Deformation.Artin.residueFieldAlgebra
attribute [local instance_reducible] AlgebraicGeometry.Scheme.residueField

-- The direct image of the structure sheaf along an isomorphism is the structure sheaf:
-- `AlgebraicGeometry.pushforwardUnitIso`, in
-- `StacksFrontier.AlgebraicGeometry.EulerCharIso.SchemeIsoDegree`. A second proof of the same
-- statement stood here.

private theorem module_card_le_quotient_mul_submodule
    {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    Cardinal.mk M ≤ Cardinal.mk (M ⧸ N) * Cardinal.mk N := by
  classical
  let rep (q : M ⧸ N) : M := Classical.choose (N.mkQ_surjective q)
  have hrep (q : M ⧸ N) : N.mkQ (rep q) = q :=
    Classical.choose_spec (N.mkQ_surjective q)
  let f : M → (M ⧸ N) × N := fun x =>
    (N.mkQ x, ⟨x - rep (N.mkQ x), by
      have hz : N.mkQ (x - rep (N.mkQ x)) = 0 := by
        rw [map_sub, hrep]
        simp
      have hm : x - rep (N.mkQ x) ∈ N.mkQ.ker := LinearMap.mem_ker.mpr hz
      simpa only [N.ker_mkQ] using hm
    ⟩)
  have hf : Function.Injective f := by
    intro x y h
    have hq : N.mkQ x = N.mkQ y := congrArg Prod.fst h
    have hn : x - rep (N.mkQ x) = y - rep (N.mkQ y) :=
      congrArg Subtype.val (congrArg Prod.snd h)
    have hn' : x - rep (N.mkQ x) = y - rep (N.mkQ x) := by
      simpa [hq] using hn
    calc
      x = (x - rep (N.mkQ x)) + rep (N.mkQ x) := by abel
      _ = (y - rep (N.mkQ x)) + rep (N.mkQ x) := by rw [hn']
      _ = y := by abel
  calc
    Cardinal.mk M ≤ Cardinal.mk ((M ⧸ N) × N) := Cardinal.mk_le_of_injective hf
    _ = Cardinal.mk (M ⧸ N) * Cardinal.mk N := by
      rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]

private theorem finiteLength_card_le_residueField_power
    {R : Type u} [CommRing R] [IsLocalRing R] {M : Type u}
    [AddCommGroup M] [Module R M] (hM : IsFiniteLength R M) :
    Cardinal.mk M ≤ (max ℵ₀ (Cardinal.mk (IsLocalRing.ResidueField R))) ^ ℵ₀ := by
  classical
  let κ := max ℵ₀ (Cardinal.mk (IsLocalRing.ResidueField R))
  have hκ : ℵ₀ ≤ κ := le_max_left _ _
  have hκ0 : κ ≠ 0 := ne_of_gt (lt_of_lt_of_le Cardinal.aleph0_pos hκ)
  induction hM with
  | @of_subsingleton M _ _ hsub =>
      let : Subsingleton M := hsub
      calc
        Cardinal.mk M ≤ 1 := Cardinal.le_one_iff_subsingleton.mpr inferInstance
        _ ≤ κ ^ ℵ₀ := Cardinal.one_le_iff_ne_zero.mpr
          (Cardinal.power_ne_zero ℵ₀ hκ0)
  | @of_simple_quotient M _ _ N _ _ ih =>
      have hquot : IsSimpleModule R (M ⧸ N) := inferInstance
      let hsimp := isSimpleModule_iff_quot_maximal.mp hquot
      let J := Classical.choose hsimp
      have hJ : J.IsMaximal := (Classical.choose_spec hsimp).1
      let e := Classical.choice (Classical.choose_spec hsimp).2
      have hJ' : J = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hJ
      change (M ⧸ N) ≃ₗ[R] R ⧸ J at e
      rw [hJ'] at e
      have hq : Cardinal.mk (M ⧸ N) ≤ κ := by
        calc
          Cardinal.mk (M ⧸ N) = Cardinal.mk (IsLocalRing.ResidueField R) :=
            Cardinal.mk_congr e.toEquiv
          _ ≤ κ := le_max_right _ _
      have hN : Cardinal.mk N ≤ κ ^ ℵ₀ := ih
      calc
        Cardinal.mk M ≤ Cardinal.mk (M ⧸ N) * Cardinal.mk N :=
          module_card_le_quotient_mul_submodule N
        _ ≤ κ * (κ ^ ℵ₀) := mul_le_mul hq hN (by positivity) (by positivity)
        _ = κ ^ ℵ₀ := by
          calc
            κ * κ ^ ℵ₀ = κ ^ 1 * κ ^ ℵ₀ := by simp
            _ = κ ^ (1 + ℵ₀) := (Cardinal.power_add κ 1 ℵ₀).symm
            _ = κ ^ ℵ₀ := congrArg (fun α : Cardinal => κ ^ α)
              (Cardinal.nat_add_aleph0 (1 : ℕ))

private theorem artinianLocalAlg_card_le
    {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    Cardinal.mk A.carrier ≤ (max ℵ₀ (Cardinal.mk k)) ^ ℵ₀ := by
  let : CommRing A.carrier := A.commRing
  let : IsLocalRing A.carrier := A.isLocalRing
  let : IsArtinianRing A.carrier := A.isArtinianRing
  have hlen : IsFiniteLength A.carrier A.carrier :=
    (isArtinianRing_iff_isFiniteLength A.carrier).mp inferInstance
  have h := finiteLength_card_le_residueField_power hlen
  have heq : Cardinal.mk (IsLocalRing.ResidueField A.carrier) = Cardinal.mk k :=
    Cardinal.mk_congr A.residueEquiv.toEquiv
  simpa only [heq] using h

theorem artinianLocalAlg_spec_contains
    (B : AlgebraicGeometry.BigFppfSite.{u}) {X : Scheme.{u}}
    (hX : B.Contains X) {Λ : Type u} {k : Type u}
    [CommRing Λ] [Field k] [Algebra Λ k]
    (hk : Cardinal.mk k ≤ X.size)
    (A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) :
    B.Contains (Spec (.of A.carrier)) := by
  let : CommRing A.carrier := A.commRing
  apply Scheme.size_Spec_lt_of_mk_le B.aleph0_lt_cutoff
    B.cutoff_isStrongPrelimit _ hX
  calc
    Cardinal.mk A.carrier ≤ (max ℵ₀ (Cardinal.mk k)) ^ ℵ₀ := artinianLocalAlg_card_le A
    _ ≤ X.size ^ ℵ₀ := Cardinal.power_le_power_right
      (max_le X.aleph0_le_size hk)

-- A square-zero kernel stays square-zero on global sections of the spectrum:
-- `Deformation.Artin.specMap_appTop_ker_sq`, public in
-- `StacksFrontier.Deformation.Artin.Infinitesimal.TangentFunctor` (closure 66; +30 modules here).
-- A SECOND `public` declaration of that same fully-qualified name, with the identical
-- statement and a different proof, stood here. It compiled only because no module imported
-- both files; any module that did would have failed with `environment already contains`.
-- Its companion `Deformation.Artin.specMap_appTop_surjective` stays below: together they say
-- that the spectrum of a square-zero surjection of rings is a square-zero surjection on
-- global sections, which is the form axiom (RS*) asks for its leg.

/-- The spectrum of a surjection with square-zero kernel is a first order thickening. -/
private theorem specMap_isFirstOrderThickening
    {R T : CommRingCat.{u}} (φ : R ⟶ T)
    (hsurj : Function.Surjective φ.hom)
    (hker : RingHom.ker φ.hom ^ 2 = ⊥) :
    Stacks.Thickenings.IsFirstOrderThickening (Spec.map φ) := by
  refine ⟨IsClosedImmersion.spec_of_surjective φ hsurj, ?_⟩
  apply Scheme.IdealSheafData.ext_of_isAffine
  simpa [AlgebraicGeometry.Scheme.ker_of_isAffine] using specMap_appTop_ker_sq φ hker

private theorem pullbackCone_fst_surjective
    {A B C : CommRingCat.{u}} (q : A ⟶ C) (p : B ⟶ C)
    (hp : Function.Surjective p.hom) :
    Function.Surjective (CommRingCat.pullbackCone q p).fst.hom := by
  intro a
  obtain ⟨b, hb⟩ := hp (q.hom a)
  refine ⟨⟨(a, b), ?_⟩, ?_⟩
  · exact hb.symm
  · rfl

private theorem spec_pullbackCone_isPushout
    {A B C : CommRingCat.{u}} (q : A ⟶ C) (p : B ⟶ C)
    (hp : Function.Surjective p.hom) :
    IsPushout (Spec.map p) (Spec.map q)
      (Spec.map (CommRingCat.pullbackCone q p).snd)
      (Spec.map (CommRingCat.pullbackCone q p).fst) := by
  exact Stacks.Pushout.isPushout_spec_map_of_isPullback_of_surjective
    p q (CommRingCat.pullbackCone q p).fst (CommRingCat.pullbackCone q p).snd
    (IsPullback.of_isLimit (CommRingCat.pullbackConeIsLimit q p)) hp

private theorem affineSpec_pullbackCone_isPushout
    {U : Scheme.{u}} [IsAffine U] {B C : CommRingCat.{u}}
    (q : Γ(U, ⊤) ⟶ C) (p : B ⟶ C)
    (hp : Function.Surjective p.hom) (φ : Spec C ⟶ U)
    (hφ : Spec.map q ≫ U.isoSpec.inv = φ) :
    IsPushout (Spec.map p) φ
      (Spec.map (CommRingCat.pullbackCone q p).snd)
      (U.isoSpec.hom ≫ Spec.map (CommRingCat.pullbackCone q p).fst) := by
  exact (spec_pullbackCone_isPushout q p hp).of_iso
    (Iso.refl _) (Iso.refl _) U.isoSpec.symm (Iso.refl _)
    (by simp) hφ (by simp) (by simp)

private theorem pullbackCone_card_le
    {A B C : CommRingCat.{u}} (q : A ⟶ C) (p : B ⟶ C) :
    Cardinal.mk (CommRingCat.pullbackCone q p).pt ≤
      max ℵ₀ (max (Cardinal.mk A) (Cardinal.mk B)) := by
  let κ := max ℵ₀ (max (Cardinal.mk A) (Cardinal.mk B))
  have hκ : ℵ₀ ≤ κ := le_max_left _ _
  have hinj : Function.Injective
      (fun x : (CommRingCat.pullbackCone q p).pt => x.1) := by
    intro x y h
    exact Subtype.ext h
  calc
    Cardinal.mk (CommRingCat.pullbackCone q p).pt ≤ Cardinal.mk (A × B) :=
      Cardinal.mk_le_of_injective hinj
    _ = Cardinal.mk A * Cardinal.mk B := by
      rw [Cardinal.mk_prod, Cardinal.lift_id, Cardinal.lift_id]
    _ ≤ κ * κ := mul_le_mul
      (le_trans (le_max_left _ _) (le_max_right _ _))
      (le_trans (le_max_right _ _) (le_max_right _ _)) (by positivity) (by positivity)
    _ = κ := Cardinal.mul_eq_self hκ

private theorem pullbackCone_spec_contains
    (B : AlgebraicGeometry.BigFppfSite.{u}) {U : Scheme.{u}} (hU : B.Contains U)
    [IsAffine U]
    {C A : CommRingCat.{u}} (q : Γ(U, ⊤) ⟶ A) (p : C ⟶ A)
    (hC : B.Contains (Spec C)) :
    B.Contains (Spec (.of (CommRingCat.pullbackCone q p).pt)) := by
  let κ := max U.size (Spec C).size
  have hκ : ℵ₀ ≤ κ := le_trans U.aleph0_le_size (le_max_left _ _)
  have hR : Cardinal.mk (Γ(U, ⊤)) ≤ U.size :=
    U.mk_sections_le_size ⟨⊤, isAffineOpen_top U⟩
  have hCcard : Cardinal.mk C ≤ (Spec C).size := by
    rw [Scheme.size_Spec]
    exact le_max_right _ _
  have hP' : Cardinal.mk (CommRingCat.pullbackCone q p).pt ≤ κ := by
    refine (pullbackCone_card_le q p).trans ?_
    apply max_le hκ (max_le (hR.trans (le_max_left _ _)) ?_)
    exact hCcard.trans (le_max_right _ _)
  have hsize : (Spec (.of (CommRingCat.pullbackCone q p).pt)).size ≤ κ := by
    rw [Scheme.size_Spec]
    exact max_le hκ hP'
  exact lt_of_le_of_lt hsize (max_lt hU hC)

/-- An element of the fibre product whose first coordinate vanishes has second coordinate in
`ker p`. -/
private theorem pullbackCone_snd_mem_ker
    {A B C : CommRingCat.{u}} (q : A ⟶ C) (p : B ⟶ C)
    (x : (CommRingCat.pullbackCone q p).pt) (hx : x.1.1 = 0) :
    x.1.2 ∈ RingHom.ker p.hom := by
  have heq : q.hom x.1.1 = p.hom x.1.2 := x.2
  rw [hx] at heq
  exact RingHom.mem_ker.mpr (by simpa using heq.symm)

private theorem pullbackCone_fst_ker_sq
    {A B C : CommRingCat.{u}} (q : A ⟶ C) (p : B ⟶ C)
    (hp : RingHom.ker p.hom ^ 2 = ⊥) :
    RingHom.ker (CommRingCat.pullbackCone q p).fst.hom ^ 2 = ⊥ := by
  rw [pow_two]
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro x hx y hy
    change x.1.1 = 0 at hx
    change y.1.1 = 0 at hy
    have hxyB : x.1.2 * y.1.2 = 0 := by
      have hmem := Ideal.mul_mem_mul (pullbackCone_snd_mem_ker q p x hx)
        (pullbackCone_snd_mem_ker q p y hy)
      rwa [← pow_two, hp, Ideal.mem_bot] at hmem
    apply Subtype.ext
    apply Prod.ext
    · show x.1.1 * y.1.1 = 0
      rw [hx, hy]
      simp
    · exact hxyB
  · exact bot_le

private def pullbackCone_fstKerEquiv
    {A B C : CommRingCat.{u}} (q : A ⟶ C) (p : B ⟶ C) :
    RingHom.ker (CommRingCat.pullbackCone q p).fst.hom ≃ RingHom.ker p.hom where
  toFun x := ⟨x.1.1.2, pullbackCone_snd_mem_ker q p x.1 x.2⟩
  invFun y := by
    have hy : p.hom y.1 = 0 := RingHom.mem_ker.mp y.2
    let z : (CommRingCat.pullbackCone q p).pt :=
      ⟨(0, y.1), by change q.hom 0 = p.hom y.1; rw [map_zero, hy]⟩
    refine ⟨z, ?_⟩
    change (CommRingCat.pullbackCone q p).fst.hom z = 0
    rfl
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · have hx : x.1.1.1 = 0 := x.2
      simp [hx]
    · rfl
  right_inv y := by
    apply Subtype.ext
    rfl

private def pullbackCone_fstKerAddHom
    {A B C : CommRingCat.{u}} (q : A ⟶ C) (p : B ⟶ C) :
    RingHom.ker (CommRingCat.pullbackCone q p).fst.hom →+
      RingHom.ker p.hom where
  toFun x := pullbackCone_fstKerEquiv q p x
  map_zero' := rfl
  map_add' _ _ := rfl

private def pullbackCone_fstKerAddEquiv
    {A B C : CommRingCat.{u}} (q : A ⟶ C) (p : B ⟶ C) :
    RingHom.ker (CommRingCat.pullbackCone q p).fst.hom ≃+ RingHom.ker p.hom :=
  AddEquiv.ofBijective (pullbackCone_fstKerAddHom q p) <| by
    constructor
    · intro x y h
      change pullbackCone_fstKerEquiv q p x =
        pullbackCone_fstKerEquiv q p y at h
      apply (pullbackCone_fstKerEquiv q p).injective
      exact h
    · intro y
      exact ⟨(pullbackCone_fstKerEquiv q p).symm y, rfl⟩

@[instance_reducible]
private def pullbackCone_fstKerModule
    {A B C : CommRingCat.{u}} (q : A ⟶ C) (p : B ⟶ C) :
    Module (CommRingCat.pullbackCone q p).pt (RingHom.ker p.hom) :=
  Module.compHom (RingHom.ker p.hom) (CommRingCat.pullbackCone q p).snd.hom

attribute [local instance] pullbackCone_fstKerModule

private def pullbackCone_fstKerLinearEquiv
    {A B C : CommRingCat.{u}} (q : A ⟶ C) (p : B ⟶ C) :
    RingHom.ker (CommRingCat.pullbackCone q p).fst.hom ≃ₗ[
      (CommRingCat.pullbackCone q p).pt] RingHom.ker p.hom :=
  (pullbackCone_fstKerAddEquiv q p).toLinearEquiv (by
    intro r x
    apply Subtype.ext
    rfl)

private theorem specMap_pullbackCone_fst_isFirstOrderThickening
    {A B C : CommRingCat.{u}} (q : A ⟶ C) (p : B ⟶ C)
    (hp : Function.Surjective p.hom)
    (hker : RingHom.ker p.hom ^ 2 = ⊥) :
    Stacks.Thickenings.IsFirstOrderThickening
      (Spec.map (CommRingCat.pullbackCone q p).fst) :=
  specMap_isFirstOrderThickening _
    (pullbackCone_fst_surjective q p hp)
    (pullbackCone_fst_ker_sq q p hker)

private theorem smallExtension_kernel_annihilated
    {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {B A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : B ⟶ A)
    (hf : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f.hom.toRingHom)) :
    ∀ b : B, b ∈ IsLocalRing.maximalIdeal B →
      ∀ z : RingHom.ker f.hom.toRingHom, b * (z : B) = 0 := by
  rcases hf with ⟨_, _, _, _, _, hlen⟩
  let I : Ideal B := RingHom.ker f.hom.toRingHom
  have hsimple : IsSimpleModule B I := Module.length_eq_one_iff.mp hlen
  have hAnn : (Module.annihilator B I).IsMaximal :=
    IsSimpleModule.annihilator_isMaximal
  have hAnnEq : Module.annihilator B I = IsLocalRing.maximalIdeal B :=
    IsLocalRing.eq_maximalIdeal hAnn
  intro b hb z
  have hmem : b ∈ Module.annihilator B I := by rw [hAnnEq]; exact hb
  have hz := (Module.mem_annihilator.mp hmem) z
  have hz' : ((b • z : I) : B) = 0 := congrArg Subtype.val hz
  simpa only [Submodule.coe_smul, smul_eq_mul] using hz'

public noncomputable def smallExtension_kernel_linearEquiv_residueField
    {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {B A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : B ⟶ A)
    (hf : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f.hom.toRingHom)) :
    letI : Module B k := Module.compHom k (Deformation.Artin.residueMap B)
    RingHom.ker f.hom.toRingHom ≃ₗ[B] k := by
  apply Classical.choice
  let : Module B k := Module.compHom k (Deformation.Artin.residueMap B)
  let I : Ideal B := RingHom.ker f.hom.toRingHom
  have hsimple : IsSimpleModule B I := Module.length_eq_one_iff.mp hf.2.2.2.2.2
  obtain ⟨J, hJ, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  have hJ' : J = IsLocalRing.maximalIdeal B := IsLocalRing.eq_maximalIdeal hJ
  subst J
  refine ⟨(e.toAddEquiv.trans B.residueEquiv.toRingEquiv.toAddEquiv).toLinearEquiv ?_⟩
  intro r z
  change B.residueEquiv (e (r • z)) = _
  rw [e.map_smul]
  change B.residueEquiv (IsLocalRing.residue B r * (show IsLocalRing.ResidueField B from e z)) =
    B.residueEquiv (IsLocalRing.residue B r) * B.residueEquiv (e z)
  exact B.residueEquiv.map_mul _ _

private noncomputable def pullbackCone_smallExtension_kernel_linearEquiv_residueField
    {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {B A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    {R : CommRingCat.{u}} (q : R ⟶ CommRingCat.of A) (f : B ⟶ A)
    (hf : InfinitesimalLifting.IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom)) :
    let P := CommRingCat.pullbackCone q (CommRingCat.ofHom f.hom.toRingHom)
    letI : Module P.pt k := Module.compHom k ((Deformation.Artin.residueMap B).comp P.snd.hom)
    RingHom.ker P.fst.hom ≃ₗ[P.pt] k := by
  let P := CommRingCat.pullbackCone q (CommRingCat.ofHom f.hom.toRingHom)
  letI : Module B k := Module.compHom k (Deformation.Artin.residueMap B)
  letI : Module P.pt k := Module.compHom k ((Deformation.Artin.residueMap B).comp P.snd.hom)
  letI : Module P.pt (RingHom.ker f.hom.toRingHom) :=
    Module.compHom (RingHom.ker f.hom.toRingHom) P.snd.hom
  let e := pullbackCone_fstKerLinearEquiv q (CommRingCat.ofHom f.hom.toRingHom)
  let eB := smallExtension_kernel_linearEquiv_residueField f hf
  refine (e.toAddEquiv.trans eB.toAddEquiv).toLinearEquiv ?_
  intro r x
  change eB (e (r • x)) = _
  exact eB.map_smul (P.snd.hom r) (e x)

public theorem smallExtension_kernel_sq_zero
    {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {B A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    (f : B ⟶ A)
    (hf : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f.hom.toRingHom)) :
    RingHom.ker f.hom.toRingHom ^ 2 = ⊥ := by
  have hf' := hf
  rcases hf with ⟨hB, hA, _, _, hsurj, _⟩
  let : IsLocalRing B := hB
  let : IsLocalRing A := hA
  let : IsLocalHom f.hom.toRingHom :=
    IsLocalHom.of_surjective f.hom.toRingHom hsurj
  rw [pow_two]
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro x hx y hy
    have hxM : x ∈ IsLocalRing.maximalIdeal B := by
      rw [IsLocalRing.mem_maximalIdeal]
      intro hxunit
      have hzero : f.hom.toRingHom x = 0 := RingHom.mem_ker.mp hx
      have hunit : IsUnit (f.hom.toRingHom x) := hxunit.map f.hom.toRingHom
      rw [hzero] at hunit
      exact not_isUnit_zero hunit
    have hxy := smallExtension_kernel_annihilated f hf' x hxM
      ⟨y, hy⟩
    have hxy' : x * y = 0 := by
      simpa only [Submodule.coe_smul, smul_eq_mul] using hxy
    exact Ideal.mem_bot.mpr hxy'
  · exact bot_le

private theorem specMap_pullbackCone_fst_isFirstOrderThickening_of_smallExtension
    {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    {B A : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
    {R : CommRingCat.{u}} (q : R ⟶ CommRingCat.of A) (f : B ⟶ A)
    (hf : InfinitesimalLifting.IsSmallExtension
      (CommRingCat.ofHom f.hom.toRingHom)) :
    Stacks.Thickenings.IsFirstOrderThickening
      (Spec.map (CommRingCat.pullbackCone q
        (CommRingCat.ofHom f.hom.toRingHom)).fst) := by
  have hf' := hf
  rcases hf with ⟨_, _, _, _, hsurj, _⟩
  exact specMap_pullbackCone_fst_isFirstOrderThickening q _ hsurj
    (smallExtension_kernel_sq_zero f hf')

theorem exists_failed_artinian_lift
    {S : Scheme.{u}} (U : Over S) {F : Type v} [Category.{w} F]
    (q : F ⥤ Over S) (u₀ : U.left) (x : F)
    (hx : q.obj x = U)
    (hnot : ¬ Deformation.Artin.IsVersalAt U q u₀ x hx) :
    let Λ := S.presheaf.stalk (Deformation.Artin.basePoint U u₀)
    let k : Type u := IsLocalRing.ResidueField (U.left.presheaf.stalk u₀)
    letI : Field k := inferInstance
    letI : Algebra Λ k := Deformation.Artin.residueFieldAlgebra U u₀
    ∃ (A B : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k)
      (f : B ⟶ A), Function.Surjective f.hom ∧
      ∃ (y z : F)
        (hy : q.obj y = Over.mk
          (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫
            S.fromSpecStalk (Deformation.Artin.basePoint U u₀)))
        (hz : q.obj z = Over.mk
          (Spec.map (CommRingCat.ofHom (algebraMap Λ B)) ≫
            S.fromSpecStalk (Deformation.Artin.basePoint U u₀))),
        ∃ (i : y ⟶ z),
          eqToHom (congrArg Over.left hy).symm ≫ (q.map i).left ≫
              eqToHom (congrArg Over.left hz) =
            Spec.map (CommRingCat.ofHom f.hom.toRingHom) ∧
          ∃ (a : y ⟶ x),
            Spec.map (CommRingCat.ofHom
              (Deformation.Artin.residueMap (Λ := Λ) (k := k) A)) ≫
                eqToHom (congrArg Over.left hy).symm ≫ (q.map a).left ≫
                eqToHom (congrArg Over.left hx) = U.left.fromSpecResidueField u₀ ∧
            ∀ b : z ⟶ x, i ≫ b ≠ a := by
  classical
  unfold Deformation.Artin.IsVersalAt at hnot
  push Not at hnot
  exact hnot

private theorem exists_first_true_step (n : ℕ) (P : ℕ → Prop)
    (h0 : ¬ P 0) (hn : P n) :
    ∃ j, 0 < j ∧ j ≤ n ∧ P j ∧ ¬ P (j - 1) := by
  classical
  let s : Set ℕ := {j | j ≤ n ∧ P j}
  have hs : s.Nonempty := ⟨n, ⟨le_rfl, hn⟩⟩
  let j := Nat.find hs
  have hj : j ≤ n ∧ P j := Nat.find_spec hs
  have hmin : ∀ m < j, m ∉ s := by
    intro m hm hms
    have hle := Nat.find_min' hs hms
    omega
  have hjpos : 0 < j := by
    by_contra h
    have hj0 : j = 0 := by omega
    exact h0 (hj0 ▸ hj.2)
  refine ⟨j, hjpos, hj.1, hj.2, ?_⟩
  intro hprev
  have hprevle : j - 1 ≤ n := by omega
  have hm : j - 1 ∈ s := ⟨hprevle, hprev⟩
  have hlt : j - 1 < j := by omega
  exact hmin (j - 1) hlt hm

noncomputable def pullbackStages
    {C : Type (u + 1)} [Category.{u, u + 1} C] {F : Type v} [Category.{w, v} F]
    (p : F ⥤ C) [p.IsFibered] {n : ℕ}
    (X : ∀ j : ℕ, j ≤ n → C)
    (f : ∀ (j : ℕ) (hj : j < n),
      X (j + 1) (Nat.succ_le_of_lt hj) ⟶ X j (Nat.le_of_lt hj))
    (x₀ : p.Fiber (X 0 (Nat.zero_le n))) :
    ∀ (j : ℕ) (hj : j ≤ n), p.Fiber (X j hj) := by
  intro j
  induction j with
  | zero =>
      intro _hj
      exact x₀
  | succ j ih =>
      intro hj
      have hj' : j < n := Nat.lt_of_succ_le hj
      let α := f j hj'
      exact (Functor.chosenPullbacks p).pullbackFunctor α |>.obj
        (ih (Nat.le_of_lt hj'))

noncomputable def pullbackStageArrow
    {C : Type (u + 1)} [Category.{u, u + 1} C] {F : Type v} [Category.{w, v} F]
    (p : F ⥤ C) [p.IsFibered] {n : ℕ}
    (X : ∀ j : ℕ, j ≤ n → C)
    (f : ∀ (j : ℕ) (hj : j < n),
      X (j + 1) (Nat.succ_le_of_lt hj) ⟶ X j (Nat.le_of_lt hj))
    (x₀ : p.Fiber (X 0 (Nat.zero_le n)))
    (j : ℕ) (hj : j < n) :
    (pullbackStages p X f x₀ (j + 1) (Nat.succ_le_of_lt hj)).1 ⟶
      (pullbackStages p X f x₀ j (Nat.le_of_lt hj)).1 := by
  let α := f j hj
  exact (Functor.chosenPullbacks p).map α
    (pullbackStages p X f x₀ j (Nat.le_of_lt hj))

private theorem pullbackStageArrow_isStronglyCartesian
    {C : Type (u + 1)} [Category.{u, u + 1} C] {F : Type v} [Category.{w, v} F]
    (p : F ⥤ C) [p.IsFibered] {n : ℕ}
    (X : ∀ j : ℕ, j ≤ n → C)
    (f : ∀ (j : ℕ) (hj : j < n),
      X (j + 1) (Nat.succ_le_of_lt hj) ⟶ X j (Nat.le_of_lt hj))
    (x₀ : p.Fiber (X 0 (Nat.zero_le n)))
    (j : ℕ) (hj : j < n) :
    p.IsStronglyCartesian (f j hj) (pullbackStageArrow p X f x₀ j hj) := by
  let α := f j hj
  exact (Functor.chosenPullbacks p).isStronglyCartesian α
    (pullbackStages p X f x₀ j (Nat.le_of_lt hj))

theorem pullbackStageArrow_isHomLift
    {C : Type (u + 1)} [Category.{u, u + 1} C] {F : Type v} [Category.{w, v} F]
    (p : F ⥤ C) [p.IsFibered] {n : ℕ}
    (X : ∀ j : ℕ, j ≤ n → C)
    (f : ∀ (j : ℕ) (hj : j < n),
      X (j + 1) (Nat.succ_le_of_lt hj) ⟶ X j (Nat.le_of_lt hj))
    (x₀ : p.Fiber (X 0 (Nat.zero_le n))) (j : ℕ) (hj : j < n) :
    p.IsHomLift (f j hj) (pullbackStageArrow p X f x₀ j hj) := by
  let hsc := pullbackStageArrow_isStronglyCartesian p X f x₀ j hj
  exact hsc.toIsHomLift

noncomputable def pullbackStagesDesc
    {C : Type (u + 1)} [Category.{u, u + 1} C] {F : Type v} [Category.{w, v} F]
    (p : F ⥤ C) [p.IsFibered] {n : ℕ}
    (X : ∀ j : ℕ, j ≤ n → C)
    (f : ∀ (j : ℕ) (hj : j < n),
      X (j + 1) (Nat.succ_le_of_lt hj) ⟶ X j (Nat.le_of_lt hj))
    (x₀ : p.Fiber (X 0 (Nat.zero_le n)))
    (j : ℕ) (hj : j ≤ n) :
    (pullbackStages p X f x₀ n (le_rfl)).1 ⟶
      (pullbackStages p X f x₀ j hj).1 := by
  by_cases h : j = n
  · subst j
    exact 𝟙 _
  · have hj' : j < n := lt_of_le_of_ne hj h
    exact pullbackStagesDesc p X f x₀ (j + 1) (Nat.succ_le_of_lt hj') ≫
      pullbackStageArrow p X f x₀ j hj'
termination_by n - j
decreasing_by omega

private theorem pullbackStagesDesc_succ
    {C : Type (u + 1)} [Category.{u, u + 1} C] {F : Type v} [Category.{w, v} F]
    (p : F ⥤ C) [p.IsFibered] {n j : ℕ}
    (X : ∀ j : ℕ, j ≤ n → C)
    (f : ∀ (j : ℕ) (hj : j < n),
      X (j + 1) (Nat.succ_le_of_lt hj) ⟶ X j (Nat.le_of_lt hj))
    (x₀ : p.Fiber (X 0 (Nat.zero_le n))) (hj : j < n) :
    pullbackStagesDesc p X f x₀ j (Nat.le_of_lt hj) =
      pullbackStagesDesc p X f x₀ (j + 1) (Nat.succ_le_of_lt hj) ≫
        pullbackStageArrow p X f x₀ j hj := by
  have hne : j ≠ n := by omega
  conv_lhs => rw [pullbackStagesDesc]
  rw [dite_eq_right hne]

private theorem pullbackStagesDesc_self
    {C : Type (u + 1)} [Category.{u} C] {F : Type v} [Category.{w} F]
    (p : F ⥤ C) [p.IsFibered] {n : ℕ}
    (X : ∀ j : ℕ, j ≤ n → C)
    (f : ∀ (j : ℕ) (hj : j < n),
      X (j + 1) (Nat.succ_le_of_lt hj) ⟶ X j (Nat.le_of_lt hj))
    (x₀ : p.Fiber (X 0 (Nat.zero_le n))) :
    pullbackStagesDesc p X f x₀ n le_rfl = 𝟙 _ := by
  rw [pullbackStagesDesc, dite_eq_left rfl]

theorem pullbackStagesDesc_map
    {C : Type (u + 1)} [Category.{u} C] {F : Type v} [Category.{w} F]
    (p : F ⥤ C) [p.IsFibered] {n : ℕ}
    (X : ∀ j : ℕ, j ≤ n → C)
    (f : ∀ (j : ℕ) (hj : j < n),
      X (j + 1) (Nat.succ_le_of_lt hj) ⟶ X j (Nat.le_of_lt hj))
    (x₀ : p.Fiber (X 0 (Nat.zero_le n)))
    (g : ∀ (j : ℕ) (hj : j ≤ n), X n le_rfl ⟶ X j hj)
    (gn : g n le_rfl = 𝟙 _)
    (gs : ∀ (j : ℕ) (hj : j < n),
      g j (Nat.le_of_lt hj) = g (j + 1) (Nat.succ_le_of_lt hj) ≫ f j hj)
    (j : ℕ) (hj : j ≤ n) :
    p.map (pullbackStagesDesc p X f x₀ j hj) =
      eqToHom (pullbackStages p X f x₀ n le_rfl).2 ≫ g j hj ≫
        eqToHom (pullbackStages p X f x₀ j hj).2.symm := by
  by_cases he : j = n
  · subst j
    simp [pullbackStagesDesc_self, gn]
  · have hj' : j < n := lt_of_le_of_ne hj he
    let := pullbackStageArrow_isHomLift p X f x₀ j hj'
    rw [pullbackStagesDesc_succ p X f x₀ hj', p.map_comp,
      pullbackStagesDesc_map p X f x₀ g gn gs (j + 1) (Nat.succ_le_of_lt hj'),
      IsHomLift.fac' p (f j hj') (pullbackStageArrow p X f x₀ j hj'), gs j hj']
    simp
termination_by n - j
decreasing_by omega

theorem exists_failed_pullbackStage
    {C : Type (u + 1)} [Category.{u} C] {F : Type v} [Category.{w} F]
    (p : F ⥤ C) [p.IsFibered] {n : ℕ}
    (X : ∀ j : ℕ, j ≤ n → C)
    (f : ∀ (j : ℕ) (hj : j < n),
      X (j + 1) (Nat.succ_le_of_lt hj) ⟶ X j (Nat.le_of_lt hj))
    (x₀ : p.Fiber (X 0 (Nat.zero_le n))) {x : F}
    (a : (pullbackStages p X f x₀ n le_rfl).1 ⟶ x)
    (hbad : ¬ ∃ b : (pullbackStages p X f x₀ 0 (Nat.zero_le n)).1 ⟶ x,
      pullbackStagesDesc p X f x₀ 0 (Nat.zero_le n) ≫ b = a) :
    ∃ (j : ℕ) (hj : j < n)
      (b : (pullbackStages p X f x₀ (j + 1) (Nat.succ_le_of_lt hj)).1 ⟶ x),
      pullbackStagesDesc p X f x₀ (j + 1) (Nat.succ_le_of_lt hj) ≫ b = a ∧
      ∀ c : (pullbackStages p X f x₀ j (Nat.le_of_lt hj)).1 ⟶ x,
        pullbackStageArrow p X f x₀ j hj ≫ c ≠ b := by
  classical
  let P : ℕ → Prop := fun j => ∃ hj : j ≤ n,
    ∃ b : (pullbackStages p X f x₀ j hj).1 ⟶ x,
      pullbackStagesDesc p X f x₀ j hj ≫ b = a
  have h0 : ¬ P 0 := by
    rintro ⟨_, b, hb⟩
    exact hbad ⟨b, hb⟩
  have hn : P n := ⟨le_rfl, a, by rw [pullbackStagesDesc_self, Category.id_comp]⟩
  obtain ⟨j, hj, hjn, ⟨_, b, hb⟩, hprev⟩ := exists_first_true_step n P h0 hn
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hj' : j < n := Nat.lt_of_succ_le hjn
  refine ⟨j, hj', b, hb, ?_⟩
  intro c hc
  change ¬ P j at hprev
  apply hprev
  refine ⟨Nat.le_of_lt hj', c, ?_⟩
  rw [pullbackStagesDesc_succ p X f x₀ hj', Category.assoc, hc]
  exact hb

end Deformation.Artin

end
