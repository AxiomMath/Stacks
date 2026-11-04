module

public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.ChartBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.GradeZeroBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjSituation.RebaseBaseChange

/-!
# The chart hypothesis of a relative-`Proj` base change along a morphism of base schemes

`Stacks.Proj.IsBaseChangeOnCharts f` is the hypothesis of
`AlgebraicGeometry.Proj.isPullback_toSpecZero_map`: for a homomorphism `f : 𝒜 →+*ᵍ ℬ` of
nonnegatively graded rings and every homogeneous `a` of positive degree,
`Away ℬ (f a) = Away 𝒜 a ⊗_{𝒜₀} ℬ₀`. It holds for
`Stacks.RelativeProj.Situation.gradedBaseChange`, the base change of graded section rings along a
morphism `g : S' ⟶ S` of base schemes.

By `Stacks.Proj.isBaseChangeOnCharts_of_isBaseChange_pieces` it is enough to have the degreewise
base change over the degree-zero rings, `𝒜'ₙ(W') = 𝒜'₀(W') ⊗_{𝒜₀(W)} 𝒜ₙ(W)`. It follows from
the base change over the base rings, `𝒜'ₙ(W') = Γ(S', W') ⊗_{Γ(S, W)} 𝒜ₙ(W)`, re-based along
the degree-zero pushout `𝒜'₀(W') = Γ(S', W') ⊗_{Γ(S, W)} 𝒜₀(W)`.

## Main definitions

* `Stacks.RelativeProj.Situation.gradePieceLinearEquiv`: the degree-`n` summand of the graded ring
  of sections is `Γ(𝒜ₙ, W)`, and `Γ(S, W)`-linearly so.

## Main results

* `Stacks.RelativeProj.isScalarTower_restrictScalars`: a tower of restrictions of scalars.
* `Stacks.RelativeProj.isBaseChange_of_isPushout_of_linearEquiv`: re-basing a base change along a
  pushout of the base rings, transported along identifications of the two modules, and
  `Stacks.RelativeProj.isBaseChange_pieceMap_of_isPushout`: the same at the spelling a graded ring
  map's degree-`n` component has.
* `Stacks.RelativeProj.Situation.isBaseChange_pieceMap_gradedBaseChange`: **the degreewise base
  change over the degree-zero rings.**
* `Stacks.RelativeProj.Situation.isBaseChangeOnCharts_gradedBaseChange`: **the chart hypothesis
  for `gradedBaseChange`.**

## Implementation notes

`↥Γ(𝒜ₙ, W)` and `↥(gradePieceSubmodule (s.sectionRingGrading W) n)` are two spellings of one
group, and a unification that has to identify them unfolds the sheaf-section projections past
any heartbeat budget. So every `Algebra`, `Module` and `IsScalarTower` structure related by
`Stacks.RelativeProj.isBaseChange_of_isPushout_of_linearEquiv` and
`Stacks.RelativeProj.isScalarTower_restrictScalars` is an explicit argument,
`Stacks.RelativeProj.Situation.gradePieceLinearEquiv` has an explicit inverse, and the steps that
mention a coercion are stated as separate lemmas.

`Stacks.RelativeProj.Situation.gradePieceModule` and `gradePieceTower` are global instances: the
`Γ(S, W)`-action on a homogeneous summand is restriction of scalars along
`Stacks.RelativeProj.Situation.baseHom`.

## References

* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite DirectSum
open HomogeneousIdeal

universe u

namespace Stacks.RelativeProj

/-! ### Towers of restricted scalars -/

/-- **A tower of restrictions of scalars.** If a `D`-module `N` carries `R`- and `C`-actions that
are restriction of scalars along `R ⟶ D` and `C ⟶ D`, and `R ⟶ C ⟶ D` is a tower of rings, then
`R ⟶ C ⟶ N` is a tower of actions. Every structure involved is an explicit argument. -/
public theorem isScalarTower_restrictScalars
    {R C D N : Type*} [CommSemiring R] [CommSemiring C] [Semiring D] [AddCommMonoid N]
    (aRC : Algebra R C) (aRD : Algebra R D) (aCD : Algebra C D) (tRCD : IsScalarTower R C D)
    (mDN : Module D N) (mRN : Module R N) (mCN : Module C N)
    (hR : ∀ (r : R) (z : N), r • z = (algebraMap R D r) • z)
    (hC : ∀ (c : C) (z : N), c • z = (algebraMap C D c) • z) :
    IsScalarTower R C N :=
  ⟨fun x y z => by
    rw [Algebra.smul_def x y, hC, hR, hC, map_mul,
      IsScalarTower.algebraMap_apply R C D x, mul_smul]⟩

/-! ### Re-basing, with the modules presented through identifications -/

/-- **Re-basing a base change along a pushout of the base rings, transported along
identifications of the two modules.** This is `Stacks.RelativeProj.isBaseChange_of_isPushout`
composed with `AlgebraicGeometry.IsBaseChange.of_linearEquiv`: if `D = S ⊗_R C`, if `ρ` exhibits
`N₀` as `S ⊗_R M₀`, and if the `C`-linear `φ : M ⟶ N` agrees with `ρ` under identifications
`M ≃ M₀` and `N ≃ N₀`, then `φ` exhibits `N` as `D ⊗_C M`. -/
public theorem isBaseChange_of_isPushout_of_linearEquiv
    {R S C D M N M₀ N₀ : Type u} [CommRing R] [CommRing S] [CommRing C] [CommRing D]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup M₀] [AddCommGroup N₀]
    (aRS : Algebra R S) (aRC : Algebra R C) (aRD : Algebra R D) (aSD : Algebra S D)
    (aCD : Algebra C D) (tRSD : IsScalarTower R S D) (tRCD : IsScalarTower R C D)
    (push : Algebra.IsPushout R S C D)
    (mRM : Module R M) (mCM : Module C M) (tRCM : IsScalarTower R C M)
    (mRN : Module R N) (mSN : Module S N) (mCN : Module C N) (mDN : Module D N)
    (tRSN : IsScalarTower R S N) (tRCN : IsScalarTower R C N)
    (tSDN : IsScalarTower S D N) (tCDN : IsScalarTower C D N)
    (mRM₀ : Module R M₀)
    (mRN₀ : Module R N₀) (mSN₀ : Module S N₀) (tRSN₀ : IsScalarTower R S N₀)
    (φ : M →ₗ[C] N) {ρ : M₀ →ₗ[R] N₀} (hρ : IsBaseChange S ρ)
    (eM : M ≃ₗ[R] M₀) (eN : N ≃ₗ[S] N₀)
    (hφ : ∀ x : M, eN (φ x) = ρ (eM x)) :
    IsBaseChange D φ :=
  isBaseChange_of_isPushout φ
    (AlgebraicGeometry.IsBaseChange.of_linearEquiv hρ eM eN (φ.restrictScalars R) hφ)

/-- **The degreewise base change over the degree-zero rings, from the one over a pair of base
rings.** For a homomorphism `f : 𝒜 →+*ᵍ ℬ` of nonnegatively graded rings and rings `R ⟶ S`
under `𝒜 0 ⟶ ℬ 0` exhibiting `ℬ 0` as `S ⊗_R 𝒜 0`, if `ρ` exhibits `N₀` as `S ⊗_R M₀` and the
degree-`n` component of `f` agrees with `ρ` under identifications of the homogeneous pieces with
`M₀` and `N₀`, then that component exhibits `ℬₙ` as `ℬ 0 ⊗_{𝒜 0} 𝒜ₙ`. -/
public theorem isBaseChange_pieceMap_of_isPushout
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B} [GradedRing 𝒜] [GradedRing ℬ]
    (f : 𝒜 →+*ᵍ ℬ) [aCD : Algebra ↥(𝒜 0) ↥(ℬ 0)]
    (halg : ∀ r : ↥(𝒜 0), (algebraMap ↥(𝒜 0) ↥(ℬ 0) r : B) = f (r : A)) (n : ℕ)
    (aRS : Algebra R S) (aRC : Algebra R ↥(𝒜 0)) (aRD : Algebra R ↥(ℬ 0))
    (aSD : Algebra S ↥(ℬ 0))
    (tRSD : IsScalarTower R S ↥(ℬ 0)) (tRCD : IsScalarTower R ↥(𝒜 0) ↥(ℬ 0))
    (push : Algebra.IsPushout R S ↥(𝒜 0) ↥(ℬ 0))
    (mRM : Module R ↥(gradePieceSubmodule 𝒜 n))
    (tRCM : IsScalarTower R ↥(𝒜 0) ↥(gradePieceSubmodule 𝒜 n))
    (mRN : Module R ↥(gradePieceSubmodule ℬ n))
    (mSN : Module S ↥(gradePieceSubmodule ℬ n))
    (tRSN : IsScalarTower R S ↥(gradePieceSubmodule ℬ n))
    (tRCN : IsScalarTower R ↥(𝒜 0) ↥(gradePieceSubmodule ℬ n))
    (tSDN : IsScalarTower S ↥(ℬ 0) ↥(gradePieceSubmodule ℬ n))
    {M₀ N₀ : Type u} [AddCommGroup M₀] [AddCommGroup N₀]
    (mRM₀ : Module R M₀) (mRN₀ : Module R N₀) (mSN₀ : Module S N₀)
    (tRSN₀ : IsScalarTower R S N₀)
    {ρ : M₀ →ₗ[R] N₀} (hρ : IsBaseChange S ρ)
    (eM : ↥(gradePieceSubmodule 𝒜 n) ≃ₗ[R] M₀)
    (eN : ↥(gradePieceSubmodule ℬ n) ≃ₗ[S] N₀)
    (hφ : ∀ x, eN (Stacks.Proj.pieceMap f halg n x) = ρ (eM x)) :
    IsBaseChange ↥(ℬ 0) (Stacks.Proj.pieceMap f halg n) :=
  by
  exact isBaseChange_of_isPushout_of_linearEquiv
    (R := R) (S := S) (C := ↥(𝒜 0)) (D := ↥(ℬ 0))
    (M := ↥(gradePieceSubmodule 𝒜 n)) (N := ↥(gradePieceSubmodule ℬ n))
    (M₀ := M₀) (N₀ := N₀)
    aRS aRC aRD aSD aCD tRSD tRCD push
    mRM _ tRCM mRN mSN _ _ tRSN tRCN tSDN _ mRM₀ mRN₀ mSN₀ tRSN₀ _ hρ eM eN hφ

namespace Situation

/-! ### The degree-`n` summand of the graded ring of sections -/

variable (s : Situation.{u})

/-- The `Γ(S, W)`-module structure on a homogeneous summand of the graded ring of sections,
by restriction of scalars along `Stacks.RelativeProj.Situation.baseHom`. -/
public instance gradePieceModule (W : s.base.Opens) (n : ℕ) :
    Module ↥Γ(s.base, W) ↥(gradePieceSubmodule (s.sectionRingGrading W) n) :=
  Module.compHom _ (s.baseHom W).hom

/-- The `Γ(S, W)`-action on a homogeneous summand of the graded ring of sections factors through
the degree-zero summand. -/
public instance gradePieceTower (W : s.base.Opens) (n : ℕ) :
    IsScalarTower ↥Γ(s.base, W) ↥(s.sectionRingGrading W 0)
      ↥(gradePieceSubmodule (s.sectionRingGrading W) n) :=
  ⟨fun x y z => mul_smul ((s.baseHom W).hom x) y z⟩

/-- **The degree-`n` summand of the graded ring of sections is the sections of `𝒜ₙ`,** and
`Γ(S, W)`-linearly so, the summand being read as an `𝒜₀(W)`-submodule of the section ring. This
is the degree-`n` analogue of `Stacks.RelativeProj.Situation.gradeZeroLinearEquiv`; its inverse
is the degree-`n` component of the direct sum. -/
public def gradePieceLinearEquiv (W : s.base.Opens) (n : ℕ) :
    ↥Γ(s.pieceNat n, W) ≃ₗ[↥Γ(s.base, W)] ↥(gradePieceSubmodule (s.sectionRingGrading W) n) where
  toFun a := ⟨DirectSum.of (s.sectionPieces W) n a, ⟨a, rfl⟩⟩
  invFun x := (x : s.sectionRing W) n
  map_add' a b := Subtype.ext (map_add (DirectSum.of (s.sectionPieces W) n) a b)
  map_smul' r a := Subtype.ext ((s.of_smul W n r a).trans (_root_.mul_comm _ _))
  left_inv a := by
    change (DirectSum.of (s.sectionPieces W) n a) n = a
    exact DirectSum.of_eq_same (β := s.sectionPieces W) n a
  right_inv x := by
    obtain ⟨a, ha⟩ : ∃ a, DirectSum.of (s.sectionPieces W) n a = (x : s.sectionRing W) := x.2
    refine Subtype.ext ?_
    change DirectSum.of (s.sectionPieces W) n ((x : s.sectionRing W) n)
      = (x : s.sectionRing W)
    exact (congrArg (DirectSum.of (s.sectionPieces W) n)
      ((congrArg (fun z : s.sectionRing W => z n) ha).symm.trans
        (DirectSum.of_eq_same (β := s.sectionPieces W) n a))).trans ha

/-- `gradePieceLinearEquiv` sends a section of `𝒜ₙ` over `W` to the corresponding element of the
degree-`n` summand of the section ring. -/
@[simp] public theorem coe_gradePieceLinearEquiv (W : s.base.Opens) (n : ℕ)
    (a : ↥Γ(s.pieceNat n, W)) :
    (gradePieceLinearEquiv s W n a : s.sectionRing W)
      = DirectSum.of (s.sectionPieces W) n a := rfl

/-- The inverse of `gradePieceLinearEquiv` is the degree-`n` component. -/
@[simp] public theorem gradePieceLinearEquiv_symm_apply (W : s.base.Opens) (n : ℕ)
    (x : ↥(gradePieceSubmodule (s.sectionRingGrading W) n)) :
    (gradePieceLinearEquiv s W n).symm x = (x : s.sectionRing W) n := rfl

/-- The degree-`n` summand of an element of the degree-`n` piece is that element. This is
`LinearEquiv.apply_symm_apply` for `Stacks.RelativeProj.Situation.gradePieceLinearEquiv`, read
inside the section ring. -/
public theorem of_gradePieceLinearEquiv_symm (W : s.base.Opens) (n : ℕ)
    (x : ↥(gradePieceSubmodule (s.sectionRingGrading W) n)) :
    DirectSum.of (s.sectionPieces W) n ((gradePieceLinearEquiv s W n).symm x)
      = (x : s.sectionRing W) :=
  (coe_gradePieceLinearEquiv s W n _).symm.trans
    (congrArg (fun y : ↥(gradePieceSubmodule (s.sectionRingGrading W) n) =>
      (y : s.sectionRing W)) ((gradePieceLinearEquiv s W n).apply_symm_apply x))

/-! ### The chart hypothesis -/

section

variable {s s' : Situation.{u}} (g : s'.base ⟶ s.base)
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom
    (Stacks.Conormal.gradedPullback g s.algebra) s'.algebra)

/-- **The degree-`n` component of a base change of section rings, read through the
identifications of the homogeneous summands,** is `rho`, the map induced on sections of the
degree-`n` pieces. -/
public theorem gradePieceLinearEquiv_symm_pieceMap (n : ℕ) (W : s.base.Opens)
    (W' : s'.base.Opens) (h : W' ≤ g ⁻¹ᵁ W)
    [Algebra ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0)]
    (halgAB : ∀ r : ↥(s.sectionRingGrading W 0),
      ((algebraMap ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) r :
          s'.sectionRing W'))
        = gradedBaseChange g Φ W W' h (r : s.sectionRing W))
    [Module ↥Γ(s.base, W) ↥Γ(s'.pieceNat n, W')]
    (rho : ↥Γ(s.pieceNat n, W) →ₗ[↥Γ(s.base, W)] ↥Γ(s'.pieceNat n, W'))
    (hrho : ∀ a, rho a = pieceSectionHom g Φ n W W' h a)
    (x : ↥(gradePieceSubmodule (s.sectionRingGrading W) n)) :
    (gradePieceLinearEquiv s' W' n).symm
        (Stacks.Proj.pieceMap (gradedBaseChange g Φ W W' h) halgAB n x)
      = rho ((gradePieceLinearEquiv s W n).symm x) := by
  refine Eq.trans ?_ (hrho ((gradePieceLinearEquiv s W n).symm x)).symm
  refine (LinearEquiv.symm_apply_eq (gradePieceLinearEquiv s' W' n)).2 (Subtype.ext ?_)
  refine (Stacks.Proj.coe_pieceMap (gradedBaseChange g Φ W W' h) halgAB n x).trans ?_
  refine (congrArg (fun z : s.sectionRing W => gradedBaseChange g Φ W W' h z)
    (of_gradePieceLinearEquiv_symm s W n x).symm).trans ?_
  refine (sectionRingBaseChange_of g Φ W W' h n _).trans ?_
  exact (coe_gradePieceLinearEquiv s' W' n _).symm

/-- **The degreewise base change, over the degree-zero rings.** For affine opens `W ⊆ S` and
`W' ⊆ g⁻¹W ⊆ S'`, extending the scalars of `𝒜ₙ(W)` along `𝒜₀(W) ⟶ 𝒜'₀(W')` gives `𝒜'ₙ(W')`. -/
public theorem isBaseChange_pieceMap_gradedBaseChange (n : ℕ)
    {W : s.base.Opens} {W' : s'.base.Opens}
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W)
    (hΦ : ∀ m : ℕ, IsIso (Φ.app (m : ℤ)))
    [instCD : Algebra ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0)]
    (halgCD : ∀ a : ↥(s.sectionRingGrading W 0),
      algebraMap ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) a
        = (gradedBaseChange g Φ W W' h).gradedZeroRingHom a)
    (halgAB : ∀ r : ↥(s.sectionRingGrading W 0),
      ((algebraMap ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) r :
          s'.sectionRing W'))
        = gradedBaseChange g Φ W W' h (r : s.sectionRing W)) :
    IsBaseChange ↥(s'.sectionRingGrading W' 0)
      (Stacks.Proj.pieceMap (gradedBaseChange g Φ W W' h) halgAB n) := by
  let aRS : Algebra ↥Γ(s.base, W) ↥Γ(s'.base, W') := (g.appLE W W' h).hom.toAlgebra
  have halgRS : ∀ r : ↥Γ(s.base, W),
      algebraMap ↥Γ(s.base, W) ↥Γ(s'.base, W') r = (g.appLE W W' h).hom r := fun _ => rfl
  let mRN' : Module ↥Γ(s.base, W) ↥Γ(s'.pieceNat n, W') :=
    Module.compHom _ (g.appLE W W' h).hom
  let tRSN' : IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W') ↥Γ(s'.pieceNat n, W') :=
    ⟨fun x y z => mul_smul ((g.appLE W W' h).hom x) y z⟩
  let rho : ↥Γ(s.pieceNat n, W) →ₗ[↥Γ(s.base, W)] ↥Γ(s'.pieceNat n, W') :=
    { toFun := fun a => pieceSectionHom g Φ n W W' h a
      map_add' := fun a b => map_add _ a b
      map_smul' := fun r a => pieceSectionHom_smul g Φ n W W' h r a }
  have hrho : IsBaseChange ↥Γ(s'.base, W') rho :=
    isBaseChange_pieceSectionHom g Φ n hW hW' h (hΦ n) halgRS rho (fun _ => rfl)
  let aRD : Algebra ↥Γ(s.base, W) ↥(s'.sectionRingGrading W' 0) :=
    (((gradedBaseChange g Φ W W' h).gradedZeroRingHom).comp (s.baseHom W).hom).toAlgebra
  let tRCD : IsScalarTower ↥Γ(s.base, W) ↥(s.sectionRingGrading W 0)
      ↥(s'.sectionRingGrading W' 0) :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext fun r => (halgCD _).symm)
  let tRSD : IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W') ↥(s'.sectionRingGrading W' 0) :=
    IsScalarTower.of_algebraMap_eq'
      (CommRingCat.hom_ext_iff.1 (baseHom_gradedBaseChange g Φ W W' h)).symm
  have hpush : Algebra.IsPushout ↥Γ(s.base, W) ↥Γ(s'.base, W')
      ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) :=
    isPushout_gradeZero_baseChange g Φ W W' hW hW' h (hΦ 0) halgRS halgCD
  let mRN : Module ↥Γ(s.base, W) ↥(gradePieceSubmodule (s'.sectionRingGrading W') n) :=
    Module.compHom _ (algebraMap ↥Γ(s.base, W) ↥(s'.sectionRingGrading W' 0))
  let tRSN : IsScalarTower ↥Γ(s.base, W) ↥Γ(s'.base, W')
      ↥(gradePieceSubmodule (s'.sectionRingGrading W') n) :=
    isScalarTower_restrictScalars aRS aRD (s'.gradeZeroAlgebra W') tRSD
      (Submodule.module _) mRN (gradePieceModule s' W' n) (fun _ _ => rfl) (fun _ _ => rfl)
  let mCN : Module ↥(s.sectionRingGrading W 0)
      ↥(gradePieceSubmodule (s'.sectionRingGrading W') n) :=
    Stacks.Proj.targetPieceModule (𝒜 := s.sectionRingGrading W)
      (ℬ := s'.sectionRingGrading W') n
  let tRCN : IsScalarTower ↥Γ(s.base, W) ↥(s.sectionRingGrading W 0)
      ↥(gradePieceSubmodule (s'.sectionRingGrading W') n) :=
    isScalarTower_restrictScalars (s.gradeZeroAlgebra W) aRD instCD tRCD
      (Submodule.module _) mRN mCN (fun _ _ => rfl) (fun _ _ => rfl)
  exact isBaseChange_pieceMap_of_isPushout
    (R := ↥Γ(s.base, W)) (S := ↥Γ(s'.base, W'))
    (A := s.sectionRing W) (B := s'.sectionRing W')
    (𝒜 := s.sectionRingGrading W) (ℬ := s'.sectionRingGrading W')
    (M₀ := ↥Γ(s.pieceNat n, W)) (N₀ := ↥Γ(s'.pieceNat n, W'))
    (aCD := instCD) (gradedBaseChange g Φ W W' h) halgAB n
    aRS (s.gradeZeroAlgebra W) aRD (s'.gradeZeroAlgebra W') tRSD tRCD hpush
    (gradePieceModule s W n) (gradePieceTower s W n) mRN (gradePieceModule s' W' n)
    tRSN tRCN (gradePieceTower s' W' n) inferInstance mRN' inferInstance tRSN' hrho
    (gradePieceLinearEquiv s W n).symm (gradePieceLinearEquiv s' W' n).symm
    (gradePieceLinearEquiv_symm_pieceMap g Φ n W W' h halgAB rho (fun _ => rfl))

/-- **The chart hypothesis for a base change of graded section rings along a morphism of base
schemes.** For affine opens `W ⊆ S` and `W' ⊆ g⁻¹W ⊆ S'`, every standard affine chart of
`Proj 𝒜'(W')` is the base change of the corresponding chart of `Proj 𝒜(W)` along
`Spec 𝒜'₀(W') ⟶ Spec 𝒜₀(W)`. -/
public theorem isBaseChangeOnCharts_gradedBaseChange
    {W : s.base.Opens} {W' : s'.base.Opens}
    (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (h : W' ≤ g ⁻¹ᵁ W)
    (hΦ : ∀ m : ℕ, IsIso (Φ.app (m : ℤ))) :
    Stacks.Proj.IsBaseChangeOnCharts (gradedBaseChange g Φ W W' h) := by
  let aCD : Algebra ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) :=
    ((gradedBaseChange g Φ W W' h).gradedZeroRingHom).toAlgebra
  have halgCD : ∀ a : ↥(s.sectionRingGrading W 0),
      algebraMap ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) a
        = (gradedBaseChange g Φ W W' h).gradedZeroRingHom a := fun _ => rfl
  have halgAB : ∀ r : ↥(s.sectionRingGrading W 0),
      ((algebraMap ↥(s.sectionRingGrading W 0) ↥(s'.sectionRingGrading W' 0) r :
          s'.sectionRing W'))
        = gradedBaseChange g Φ W W' h (r : s.sectionRing W) := fun _ => rfl
  intro i hi a ha
  exact Stacks.Proj.isBaseChangeOnCharts_of_isBaseChange_pieces (gradedBaseChange g Φ W W' h)
    halgAB
    (fun n => isBaseChange_pieceMap_gradedBaseChange g Φ n hW hW' h hΦ halgCD halgAB) hi a ha

end

end Situation

end Stacks.RelativeProj

end
