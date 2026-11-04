module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedChaoticSectionAlgebraIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionModule
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleFlip
public import StacksFrontier.Algebra.DifferentialGraded.Module.InverseSystemSemilinearBimodule
public import StacksFrontier.RingTheory.Koszul.LiftedSheafAlgebras
public import StacksFrontier.RingTheory.Koszul.PowKoszulDerivedLimit

/-!
# The sections of a module over the Koszul sheaf as an inverse system of bimodules

Let `f₁, …, f_r` be elements of a commutative ring `R`, let `K_n` be the Koszul differential
graded algebra on `f₁ ^ n, …, f_r ^ n` and let `ℬ = Koszul.liftedPowSheafAlgebra f` be the sheaf
of differential graded algebras `(K_{n+1})_n` on the chaotic site `Stacks.LiftedNat` of the proof
of Proposition 0GZK. A right differential graded `ℬ`-module `𝓜` has, over the stage `m`, the
differential graded module of sections `𝓜(m)` over the section algebra `ℬ(m)`, and restriction
of sections `𝓜(m') ⟶ 𝓜(m)` is semilinear over the restriction `ℬ(m') ⟶ ℬ(m)`.

Tag 0GZJ (`Koszul.nonempty_iso_of_isDerivedLimit_powKoszulTensorBalance`) is stated over
`R`-algebras, for an inverse system of differential graded `(K_{t+n}^{opp}, R)`-bimodules over
`Koszul.powStrictAlgebraSystem`, whose `n`-th algebra is the graded opposite of `K_{t+n}`. This
file produces such a system from `𝓜`: its `n`-th entry is the module of sections of `𝓜` over the
stage `t - 1 + n`, which carries `K_{t+n}`, read over `K_{t+n}` through
`Stacks.ChaoticSite.sectionAlgebraInv`, with `R` acting through `K_{t+n}`
(`DifferentialGradedModule.extendBaseObj`), and finally read as a left module over the graded
opposite (`DifferentialGraded.Bimodule.flip`). Its transitions are the restriction maps of `𝓜`.

## Main definitions

* `DifferentialGraded.Bimodule.flipSemilinear`: a homomorphism `M ⟶ N|_φ` of right differential
  graded modules, read as a homomorphism of the flipped bimodules over the graded opposite of `φ`.
* `DifferentialGraded.StrictAlgebraSystem.opp` and
  `DifferentialGraded.StrictBimoduleSystem.ofFlip`: the graded opposites of a strict inverse system
  of differential graded algebras, and the strict inverse system of bimodules over it given by a
  compatible family of right modules.
* `DifferentialGradedModule.extendBaseRestrictScalarsHom`: a semilinear homomorphism of modules
  over algebras regarded over a smaller base ring, carried along a commutative square of
  homomorphisms of algebras.
* `Koszul.liftedPowSectionModule`: the module of sections of `𝓜` over the stage `t - 1 + n`, as
  a right differential graded `K_{t+n}`-module over `R`.
* `Koszul.liftedPowSectionTrans`: its restriction maps, semilinear over the transitions of the
  Koszul algebras.
* `Koszul.liftedPowSectionBimoduleSystem`: **the strict inverse system of differential graded
  `(K_{t+n}^{opp}, R)`-bimodules attached to `𝓜`**, the input of Tag 0GZJ.
* `Koszul.liftedPowSectionModuleMap` and `Koszul.liftedPowSectionBimoduleMap`: functoriality in
  `𝓜`.

## Main results

* `DifferentialGraded.StrictBimoduleSystem.toBimoduleSystem_cmp_le_succ`: the comparison maps of
  the system underlying a strict system of bimodules are the derived comparisons of its one-step
  transitions, which is the hypothesis `hcmp` of Tag 0GZJ.
* `Koszul.nonempty_iso_of_isDerivedLimit_powKoszulTensorBalance_of_strict`: Tag 0GZJ for a strict
  inverse system of bimodules, with no hypothesis beyond the existence of the two products.
* `Koszul.liftedPowSectionBimoduleSystem_trans_apply`: the transitions of the system are the
  restriction maps of `𝓜`.
* `Koszul.liftedPowSectionTrans_naturality`: they commute with the maps induced by a homomorphism
  of right differential graded `ℬ`-modules.

## Implementation notes

*The indexing.* `Koszul.powStrictAlgebraSystem f ht` has `K_{t+n}` at the stage `n`, while the
stage `m` of `ℬ` carries `K_{m+1}`. The stage `n` of the system is therefore the stage
`t - 1 + n` of `ℬ`, whose algebra `K_{t-1+n+1}` is `K_{t+n}` only propositionally; it is read
over `K_{t+n}` through the transition homomorphism `K_{t+n} → K_{t-1+n+1}` of the Koszul
algebras (`Koszul.liftedPowStageAlgebraHom`), whose underlying map is the identity. Using a
transition homomorphism rather than a transport along an equality of indices keeps every
compatibility an instance of `Koszul.powTransition_comp_apply`.

*Why the constructions are generic.* The kernel decides an equality of the carriers of two
differential graded modules, one restricted along a homomorphism of algebras, by first comparing
the two modules themselves, which fails only after unfolding the homomorphism; for the Koszul
transition homomorphisms that unfolding goes through the universal property of the exterior
algebra and does not finish. Every construction that needs such an equality is therefore stated
for arbitrary homomorphisms — `DifferentialGradedModule.restrictScalarsFun`,
`DifferentialGradedModule.extendBaseRestrictScalarsHom`,
`DifferentialGraded.Bimodule.flipSemilinear`, `DifferentialGraded.StrictBimoduleSystem.ofFlip` —
and only instantiated at the Koszul algebras.

## References

* [Stacks Project, Tag 0GZJ](https://stacks.math.columbia.edu/tag/0GZJ) is the statement this
  system is the input of.
* [Stacks Project, Proposition 24.35.4 (Tag 0GZK)](https://stacks.math.columbia.edu/tag/0GZK) and
  [Remark 24.35.5 (Tag 0H1E)](https://stacks.math.columbia.edu/tag/0H1E) are where it is used.
* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ) for differential graded
  bimodules and [Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX) for restriction of scalars.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

/- This file is stated against the admissible-sequence pretriangulated structure of Tag 09KH,
which is not an instance; it is activated here explicitly. -/
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

universe u

namespace SheafOfModules.DifferentialGradedModule

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {A : SheafOfModules.DifferentialGradedAlgebra.{u, u} R}

/-- Restriction of total sections along a composite is the composite of the restrictions. -/
theorem sectionRestrictAdd_comp_apply (M : DifferentialGradedModule.{u, u, u} A) {U V W : Cᵒᵖ}
    (a : V ⟶ U) (b : W ⟶ V) (x : M.totalSections W) :
    M.sectionRestrictAdd (b ≫ a) x = M.sectionRestrictAdd a (M.sectionRestrictAdd b x) := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | of n p =>
      rw [sectionRestrictAdd_of, sectionRestrictAdd_of, sectionRestrictAdd_of,
        sectionRestrictApp_apply, sectionRestrictApp_apply, sectionRestrictApp_apply,
        PresheafOfModules.map_comp_apply]

end SheafOfModules.DifferentialGradedModule

namespace DifferentialGradedModule

open DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

section Generic

variable {A B : DifferentialGradedAlgebra.{u, u} R}

/-- The underlying function of a semilinear homomorphism `M ⟶ N|_φ`, as a function from `M` to
`N`. Stated for an arbitrary `φ`, so that the identification of the carrier of `N|_φ` with that
of `N` is made once and for all; see the implementation notes. -/
def restrictScalarsFun {φ : A.Hom B} {M : DifferentialGradedModule.{u, u, u} A}
    {N : DifferentialGradedModule.{u, u, u} B} (g : M ⟶ restrictScalars φ N) : M.M → N.M :=
  g.toFun

end Generic

section Square

variable (S : Type u) [CommRing S] [Algebra S R] {C C' : DifferentialGradedAlgebra.{u, u} R}
  {E E' : DifferentialGradedAlgebra.{u, u} S}

/-- **A semilinear homomorphism carried along a commutative square.** Let `ψ : C_S → E` and
`ψ' : C'_S → E'` be homomorphisms from differential graded `R`-algebras regarded over `S` to
differential graded `S`-algebras, let `τ : C → C'` and `σ : E → E'` be homomorphisms with
`σ ∘ ψ = ψ' ∘ τ`, and let `k : X ⟶ Y|_σ` be a `σ`-semilinear homomorphism. Then the underlying
map of `k` is a `τ`-semilinear homomorphism between `X` and `Y` read over `C` and `C'` through
`ψ` and `ψ'`, with `R` acting through `C` and `C'`. -/
def extendBaseRestrictScalarsHom (ψ : (C.restrictBase S).Hom E) (ψ' : (C'.restrictBase S).Hom E')
    (τ : C.Hom C') (σ : E.Hom E')
    (hsq : ∀ c : C.A, σ.toAlgebraHom (ψ.toAlgebraHom c) = ψ'.toAlgebraHom (τ.toAlgebraHom c))
    {X : DifferentialGradedModule.{u, u, u} E} {Y : DifferentialGradedModule.{u, u, u} E'}
    (k : X ⟶ restrictScalars σ Y) :
    extendBaseObj S (restrictScalars ψ X) ⟶
      restrictScalars τ (extendBaseObj S (restrictScalars ψ' Y)) :=
  have hk : ∀ (x : X.M) (c : C.A), k.toFun (MulOpposite.op (ψ.toAlgebraHom c) • x) =
      MulOpposite.op (ψ'.toAlgebraHom (τ.toAlgebraHom c)) • (show Y.M from k.toFun x) :=
    fun x c => (k.map_smul x (ψ.toAlgebraHom c)).trans
      (congrArg (fun e => MulOpposite.op e • (show Y.M from k.toFun x)) (hsq c))
  { toFun :=
      { toFun := k.toFun
        map_add' := k.toFun.map_add
        map_smul' := fun r x => by
          have h := hk x (algebraMap R C.A r)
          rw [τ.toAlgebraHom.commutes] at h
          exact h }
    map_smul := fun x c => hk x c
    map_grading := k.map_grading
    map_d := LinearMap.ext fun x => LinearMap.congr_fun k.map_d x }

/-- The underlying function of `DifferentialGradedModule.extendBaseRestrictScalarsHom` is that of
the given homomorphism. -/
theorem restrictScalarsFun_extendBaseRestrictScalarsHom (ψ : (C.restrictBase S).Hom E)
    (ψ' : (C'.restrictBase S).Hom E') (τ : C.Hom C') (σ : E.Hom E')
    (hsq : ∀ c : C.A, σ.toAlgebraHom (ψ.toAlgebraHom c) = ψ'.toAlgebraHom (τ.toAlgebraHom c))
    {X : DifferentialGradedModule.{u, u, u} E} {Y : DifferentialGradedModule.{u, u, u} E'}
    (k : X ⟶ restrictScalars σ Y) (x : X.M) :
    restrictScalarsFun (extendBaseRestrictScalarsHom S ψ ψ' τ σ hsq k) x = restrictScalarsFun k x :=
  rfl

end Square

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A A' : DifferentialGradedAlgebra.{u, u} R}

/-- **The flip of a semilinear homomorphism.** A homomorphism `g : M ⟶ M'|_φ` of right
differential graded modules over `φ : A → A'` is a homomorphism of differential graded
`(A^{opp}, R)`-bimodules from the flip of `M` to the restriction along the graded opposite of `φ`
of the flip of `M'`: it is `R`-linear, and it commutes with the signed left action of the graded
opposite because it commutes with the right action of `A` through `φ`. -/
def flipSemilinear (φ : A.Hom A') {M : DifferentialGradedModule.{u, u, u} A}
    {M' : DifferentialGradedModule.{u, u, u} A'} (g : M ⟶ restrictScalars φ M') :
    flip M ⟶ restrictLeft (oppHom φ) (flip M') where
  rightHom :=
    { toFun := g.toFun
      map_smul := fun x c => by
        change g.toFun (MulOpposite.op (algebraMap R A.A c) • (show M.M from x)) =
          MulOpposite.op (algebraMap R A'.A c) • (show M'.M from g.toFun x)
        rw [← smul_eq_op_algebraMap_smul M, ← smul_eq_op_algebraMap_smul M', map_smul]
      map_grading := g.map_grading
      map_d := g.map_d }
  map_left n p a x := by
    change g.toFun (oppLeftActionRingHom M (a : (oppAlgebra A).A)
        (x : (flip M).rightModule.M)) =
      oppLeftActionRingHom M' ((oppHom φ).toAlgebraHom
        (a : (oppAlgebra A).A)) (g.toFun (x : (flip M).rightModule.M))
    rw [oppLeftActionRingHom_apply_mem M a.property x.property,
      oppLeftActionRingHom_apply_mem M' ((oppHom φ).map_grading n _ a.property)
        (g.map_grading p _ x.property), map_smul, oppHom_apply,
      LinearEquiv.apply_symm_apply]
    exact congrArg (fun z => (((n * p).negOnePow : ℤ) : R) • z) (g.map_smul _ _)

/-- The underlying map of the flip of a semilinear homomorphism is the given one. -/
@[simp] theorem flipSemilinear_rightHom_toFun (φ : A.Hom A')
    {M : DifferentialGradedModule.{u, u, u} A} {M' : DifferentialGradedModule.{u, u, u} A'}
    (g : M ⟶ restrictScalars φ M') (y : M.M) :
    (flipSemilinear φ g).rightHom.toFun y = restrictScalarsFun g y := rfl

end DifferentialGraded.Bimodule

namespace DifferentialGraded

open DifferentialGradedModule DifferentialGradedAlgebra Bimodule

variable {R : Type u} [CommRing R]

/-- **The graded opposites of a strict inverse system of differential graded algebras**, given by
the algebras `A_n` and transition homomorphisms `τ_{m,n} : A_m → A_n` composing on the nose. -/
def StrictAlgebraSystem.opp (A : ℕ → DifferentialGradedAlgebra.{u, u} R)
    (τ : ∀ {n m : ℕ}, n ≤ m → (A m).Hom (A n))
    (hτ : ∀ {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k), (τ h).comp (τ h') = τ (h.trans h')) :
    StrictAlgebraSystem R where
  alg n := oppAlgebra (A n)
  trans h := oppHom (τ h)
  trans_comp h h' := (oppHom_comp (τ h') (τ h)).trans (congrArg oppHom (hτ h h'))

/-- **A strict inverse system of bimodules from a compatible family of right modules.** Right
differential graded `A_n`-modules `N_n` with semilinear transition homomorphisms
`N_m ⟶ N_n|_{τ_{m,n}}` whose underlying maps compose give, by
`DifferentialGraded.Bimodule.flipSemilinear`, a strict inverse system of differential graded
`(A_n^{opp}, R)`-bimodules over the graded opposites of the `A_n`. -/
def StrictBimoduleSystem.ofFlip (A : ℕ → DifferentialGradedAlgebra.{u, u} R)
    (τ : ∀ {n m : ℕ}, n ≤ m → (A m).Hom (A n))
    (hτ : ∀ {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k), (τ h).comp (τ h') = τ (h.trans h'))
    (N : ∀ n : ℕ, DifferentialGradedModule.{u, u, u} (A n))
    (g : ∀ {n m : ℕ} (h : n ≤ m), N m ⟶ restrictScalars (τ h) (N n))
    (hg : ∀ {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) (y : (N k).M),
      restrictScalarsFun (g (h.trans h')) y =
        restrictScalarsFun (g h) (restrictScalarsFun (g h') y)) :
    StrictBimoduleSystem (StrictAlgebraSystem.opp A τ hτ) (degreeZero R R) where
  bimod n := flip (N n)
  trans h := flipSemilinear (τ h) (g h)
  trans_comp h h' y := hg h h' y

/-- **The hypothesis `hcmp` of Tag 0GZJ holds for every strict inverse system of bimodules.** The
one-step comparison maps of the system underlying a strict one are the derived comparisons of its
one-step semilinear transitions; this holds by definition. -/
theorem StrictBimoduleSystem.toBimoduleSystem_cmp_le_succ {T : StrictAlgebraSystem R}
    {B : DifferentialGradedAlgebra.{u, u} R} (M : StrictBimoduleSystem T B) (n : ℕ) :
    M.toBimoduleSystem.cmp (Nat.le_succ n) =
      Bimodule.derivedTensorRestrictTrans (T.trans (Nat.le_succ n))
        (M.toBimoduleSystem.obj (n + 1)) (M.toBimoduleSystem.obj n)
        (Bimodule.tensorCompNatTransOfSemilinear (T.trans (Nat.le_succ n))
          (M.toBimoduleSystem.obj (n + 1)) (M.toBimoduleSystem.obj n) (M.trans (Nat.le_succ n))) :=
  rfl

end DifferentialGraded

namespace Koszul

open DifferentialGraded DifferentialGradedAlgebra DifferentialGradedModule Bimodule

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) {t : ℕ} (ht : 1 ≤ t)

/-- The transition homomorphism `K_{t+m} → K_{t+n}` of the Koszul algebras, for `n ≤ m`. -/
abbrev powShiftTransition {n m : ℕ} (h : n ≤ m) :
    (powAlgebra f (t + m)).Hom (powAlgebra f (t + n)) :=
  powTransition f (ht.trans (Nat.le_add_right t n)) (Nat.add_le_add_left h t)

/-- The transition homomorphisms `K_{t+m} → K_{t+n}` compose on the nose. -/
theorem powShiftTransition_comp {n m k : ℕ} (h : n ≤ m) (h' : m ≤ k) :
    (powShiftTransition f ht h).comp (powShiftTransition f ht h') =
      powShiftTransition f ht (h.trans h') :=
  hom_eq_of_toAlgebraHom_eq (powTransition_comp f _ _ _)

/-- `Koszul.powStrictAlgebraSystem` is the system of graded opposites of the Koszul algebras
`K_{t+n}` with their transition homomorphisms. -/
theorem powStrictAlgebraSystem_eq_opp :
    powStrictAlgebraSystem f ht = StrictAlgebraSystem.opp (fun n => powAlgebra f (t + n))
      (powShiftTransition f ht) (powShiftTransition_comp f ht) := rfl

section Strict

open CategoryTheory.Limits

variable {B : DifferentialGradedAlgebra.{u, u} R}
  (M : StrictBimoduleSystem (powStrictAlgebraSystem f ht) B)

/-- **Tag 0GZJ for a strict inverse system of bimodules.** For a strict inverse system `(M_n)` of
differential graded `(K_{t+n}^{opp}, B)`-bimodules, any derived limit of `n ↦ M_n ⊗^𝐋_{K_n} K_t`
is isomorphic to any derived limit of `n ↦ M_n ⊗^𝐋_R K_t`, the latter tower being built from the
one-step transitions of the system. This is
`Koszul.nonempty_iso_of_isDerivedLimit_powKoszulTensorBalance` with `hcmp` discharged by
`DifferentialGraded.StrictBimoduleSystem.toBimoduleSystem_cmp_le_succ`. -/
theorem nonempty_iso_of_isDerivedLimit_powKoszulTensorBalance_of_strict
    [HasProduct fun n : ℕ =>
      (M.toBimoduleSystem.tower (powRestrictedModuleSystem f ht)).obj (op n)]
    [HasProduct fun n : ℕ => (powBaseDegreeZeroDerivedTensorTower f t ht M.toBimoduleSystem.obj
      (fun n => M.trans (Nat.le_succ n))).tower.obj (op n)]
    (K K' : derivedCategory' B)
    (hK : Pretriangulated.IsDerivedLimit
      (M.toBimoduleSystem.tower (powRestrictedModuleSystem f ht)) K)
    (hK' : Pretriangulated.IsDerivedLimit (powBaseDegreeZeroDerivedTensorTower f t ht
      M.toBimoduleSystem.obj (fun n => M.trans (Nat.le_succ n))).tower K') :
    Nonempty (K ≅ K') :=
  nonempty_iso_of_isDerivedLimit_powKoszulTensorBalance f ht M.toBimoduleSystem
    (fun n => M.trans (Nat.le_succ n)) (M.toBimoduleSystem_cmp_le_succ) K K' hK hK'

end Strict

/-- Two composites of transition homomorphisms of the Koszul algebras with the same source and
target agree. -/
theorem powTransition_apply_apply_eq {p n n' m : ℕ} (h₁ : 1 ≤ p) (h₂ : p ≤ n) (h₃ : 1 ≤ n)
    (h₄ : n ≤ m) (h₅ : p ≤ n') (h₆ : 1 ≤ n') (h₇ : n' ≤ m) (x : ExteriorAlgebra R (Fin r → R)) :
    (powTransition f h₁ h₂).toAlgebraHom ((powTransition f h₃ h₄).toAlgebraHom x) =
      (powTransition f h₁ h₅).toAlgebraHom ((powTransition f h₆ h₇).toAlgebraHom x) := by
  rw [powTransition_comp_apply f h₁ h₂ h₄, powTransition_comp_apply f h₁ h₅ h₇]

section Sheaf

attribute [local instance] SheafOfModules.GradedAlgebra.sectionsGOne
  SheafOfModules.GradedAlgebra.sectionsGMul SheafOfModules.GradedAlgebra.sectionsGRing
  Stacks.uliftIntAlgebra

open Stacks Stacks.ChaoticSite

/-- The stage of `Stacks.LiftedNat` carrying `K_{t+n}`, namely `t - 1 + n`. -/
abbrev liftedPowStage (t n : ℕ) : LiftedNat.{u}ᵒᵖ := op (LiftedNat.up (t - 1 + n))

/-- The stages carrying `K_{t+n}` are monotone in `n`. -/
theorem liftedPowStage_le {n m : ℕ} (h : n ≤ m) : t - 1 + n ≤ t - 1 + m := by omega

/-- The morphism of `Stacks.LiftedNatᵒᵖ` from the stage carrying `K_{t+m}` to the one carrying
`K_{t+n}`, for `n ≤ m`. -/
abbrev liftedPowStageMap (t : ℕ) {n m : ℕ} (h : n ≤ m) :
    liftedPowStage.{u} t m ⟶ liftedPowStage t n :=
  (homOfLE (LiftedNat.up_le_up_iff.2 (liftedPowStage_le h))).op

include ht in
/-- The algebra `K_{t-1+n+1}` at the stage `t - 1 + n` has index at most `t + n`. -/
theorem liftedPowStage_succ_le (n : ℕ) : t - 1 + n + 1 ≤ t + n := by omega

/-- The diagram of Koszul algebras indexed by `Stacks.LiftedNat` of which `ℬ` is the sheaf. -/
abbrev liftedPowDiagram (f : Fin r → R) : LiftedNat.{u}ᵒᵖ ⥤ DifferentialGradedAlgebra.{u, u} R :=
  LiftedNat.liftDiagram (powAlgebraDiagram f)

/-- **`K_{t+n}` maps to the algebra at the stage `t - 1 + n`**, which is `K_{t-1+n+1}`, by the
transition homomorphism of the Koszul algebras; its underlying map is the identity. -/
def liftedPowStageAlgebraHom (n : ℕ) :
    (powAlgebra f (t + n)).Hom ((liftedPowDiagram.{u} f).obj (liftedPowStage t n)) :=
  powTransition f (Nat.le_add_left 1 _) (liftedPowStage_succ_le ht n)

/-- The restriction homomorphism of the diagram of Koszul algebras between two stages is a
transition homomorphism. -/
theorem liftedPowDiagram_map_liftedPowStageMap {n m : ℕ} (h : n ≤ m)
    (x : ((liftedPowDiagram.{u} f).obj (liftedPowStage t m)).A) :
    ((liftedPowDiagram.{u} f).map (liftedPowStageMap t h)).toAlgebraHom x =
      (powTransition f (Nat.le_add_left 1 (t - 1 + n))
        (Nat.add_le_add_right (liftedPowStage_le h) 1)).toAlgebraHom x := rfl

/-- **`K_{t+n}` maps to the section algebra of `ℬ` over the stage `t - 1 + n`**, as differential
graded algebras over the lifted integers: `Koszul.liftedPowStageAlgebraHom` followed by the
identification `Stacks.ChaoticSite.sectionAlgebraInv` of the algebra at the stage with the
sections of `ℬ` over it. -/
def liftedPowSectionAlgebraHom (n : ℕ) :
    ((powAlgebra f (t + n)).restrictBase (ULift.{u} ℤ)).Hom
      ((liftedPowSheafAlgebra f).sectionAlgebra (liftedPowStage.{u} t n)) :=
  (sectionAlgebraInv (liftedPowDiagram f) (liftedPowStage t n)).comp
    ((liftedPowStageAlgebraHom f ht n).restrictBase (ULift.{u} ℤ))

/-- **The maps to the section algebras commute with restriction**: restricting sections of `ℬ`
from the stage of `K_{t+m}` to the stage of `K_{t+n}` corresponds to the transition homomorphism
`K_{t+m} → K_{t+n}`. This is `Stacks.ChaoticSite.sectionAlgebraIso_hom_naturality`. -/
theorem sectionRestriction_liftedPowSectionAlgebraHom {n m : ℕ} (h : n ≤ m)
    (c : (powAlgebra f (t + m)).A) :
    ((liftedPowSheafAlgebra f).sectionRestriction (liftedPowStageMap t h)).toAlgebraHom
        ((liftedPowSectionAlgebraHom f ht m).toAlgebraHom c) =
      (liftedPowSectionAlgebraHom f ht n).toAlgebraHom
        ((powShiftTransition f ht h).toAlgebraHom c) := by
  set A := liftedPowDiagram.{u} f
  set U := liftedPowStage.{u} t n
  set V := liftedPowStage.{u} t m
  have hN := sectionAlgebraIso_hom_naturality A U (liftedPowStageMap t h)
  set y := (liftedPowStageAlgebraHom f ht m).toAlgebraHom c
  have h₁ := congrArg (fun φ => φ.toAlgebraHom ((sectionAlgebraInv A V).toAlgebraHom y)) hN
  change sectionRingHom A U ((systemAlgebra A).sectionRestrictRing (liftedPowStageMap t h)
      ((sectionRingEquiv A V).symm y)) =
    (A.map (liftedPowStageMap t h)).toAlgebraHom
      (sectionRingEquiv A V ((sectionRingEquiv A V).symm y)) at h₁
  rw [RingEquiv.apply_symm_apply] at h₁
  show (systemAlgebra A).sectionRestrictRing (liftedPowStageMap t h)
      ((sectionRingEquiv A V).symm y) =
    (sectionRingEquiv A U).symm ((liftedPowStageAlgebraHom f ht n).toAlgebraHom
      ((powShiftTransition f ht h).toAlgebraHom c))
  apply (sectionRingEquiv A U).injective
  rw [RingEquiv.apply_symm_apply]
  refine h₁.trans ?_
  rw [liftedPowDiagram_map_liftedPowStageMap]
  exact powTransition_apply_apply_eq f (Nat.le_add_left 1 _)
    (Nat.add_le_add_right (liftedPowStage_le h) 1) (Nat.le_add_left 1 _)
    (liftedPowStage_succ_le ht m) (liftedPowStage_succ_le ht n) (ht.trans (Nat.le_add_right t n))
    (Nat.add_le_add_left h t) c

variable (𝓜 : SheafOfModules.DifferentialGradedModule.{u, u, u} (liftedPowSheafAlgebra.{u} f))

/-- **The sections of `𝓜` over the stage carrying `K_{t+n}`, as a right differential graded
`K_{t+n}`-module over `R`**: the module of sections over the stage `t - 1 + n`, read over
`K_{t+n}` through `Koszul.liftedPowSectionAlgebraHom`, with `R` acting through `K_{t+n}`. -/
def liftedPowSectionModule (n : ℕ) : DifferentialGradedModule.{u, u, u} (powAlgebra f (t + n)) :=
  extendBaseObj (ULift.{u} ℤ)
    (restrictScalars (liftedPowSectionAlgebraHom f ht n) (𝓜.sectionModule (liftedPowStage t n)))

/-- The underlying type of `Koszul.liftedPowSectionModule` is the type of total sections of `𝓜`
over the stage `t - 1 + n`. -/
theorem liftedPowSectionModule_M (n : ℕ) :
    (liftedPowSectionModule f ht 𝓜 n).M = 𝓜.totalSections (liftedPowStage t n) := rfl

/-- **The restriction maps of `𝓜` as semilinear homomorphisms** over the transition homomorphisms
`K_{t+m} → K_{t+n}` of the Koszul algebras. -/
def liftedPowSectionTrans {n m : ℕ} (h : n ≤ m) :
    liftedPowSectionModule f ht 𝓜 m ⟶
      restrictScalars (powShiftTransition f ht h) (liftedPowSectionModule f ht 𝓜 n) :=
  extendBaseRestrictScalarsHom (ULift.{u} ℤ) (liftedPowSectionAlgebraHom f ht m)
    (liftedPowSectionAlgebraHom f ht n) (powShiftTransition f ht h)
    ((liftedPowSheafAlgebra f).sectionRestriction (liftedPowStageMap t h))
    (sectionRestriction_liftedPowSectionAlgebraHom f ht h)
    (𝓜.sectionModuleRestriction (liftedPowStageMap t h))

/-- The underlying function of the transition is restriction of sections. -/
theorem restrictScalarsFun_liftedPowSectionTrans {n m : ℕ} (h : n ≤ m)
    (x : (liftedPowSectionModule f ht 𝓜 m).M) :
    restrictScalarsFun (liftedPowSectionTrans f ht 𝓜 h) x =
      𝓜.sectionRestrictAdd (liftedPowStageMap t h) x := rfl

/-- **The inverse system of differential graded bimodules attached to `𝓜`, the input of
Tag 0GZJ.** Its `n`-th bimodule is `Koszul.liftedPowSectionModule f ht 𝓜 n`, the sections of `𝓜`
over the stage carrying `K_{t+n}`, read as a differential graded `(K_{t+n}^{opp}, R)`-bimodule,
and its transitions are the restriction maps of `𝓜`. -/
def liftedPowSectionBimoduleSystem :
    StrictBimoduleSystem (powStrictAlgebraSystem f ht) (degreeZero R R) :=
  StrictBimoduleSystem.ofFlip (fun n => powAlgebra f (t + n)) (powShiftTransition f ht)
    (powShiftTransition_comp f ht) (liftedPowSectionModule f ht 𝓜)
    (fun h => liftedPowSectionTrans f ht 𝓜 h) fun h h' y => by
      rw [restrictScalarsFun_liftedPowSectionTrans, restrictScalarsFun_liftedPowSectionTrans,
        restrictScalarsFun_liftedPowSectionTrans]
      exact (congrArg (fun a => 𝓜.sectionRestrictAdd a y) (Subsingleton.elim _ _)).trans
        (𝓜.sectionRestrictAdd_comp_apply (liftedPowStageMap t h) (liftedPowStageMap t h') y)

/-- The `n`-th bimodule of the system is the flip of the sections of `𝓜` over the stage carrying
`K_{t+n}`. -/
@[simp] theorem liftedPowSectionBimoduleSystem_bimod (n : ℕ) :
    (liftedPowSectionBimoduleSystem f ht 𝓜).bimod n = flip (liftedPowSectionModule f ht 𝓜 n) :=
  rfl

/-- The transitions of the system are the flips of the restriction maps of `𝓜`. -/
theorem liftedPowSectionBimoduleSystem_trans {n m : ℕ} (h : n ≤ m) :
    (liftedPowSectionBimoduleSystem f ht 𝓜).trans h =
      flipSemilinear (powShiftTransition f ht h) (liftedPowSectionTrans f ht 𝓜 h) :=
  rfl

/-- **The transitions of the system are the restriction maps of `𝓜`**, on underlying elements. -/
theorem liftedPowSectionBimoduleSystem_trans_apply {n m : ℕ} (h : n ≤ m)
    (y : (liftedPowSectionModule f ht 𝓜 m).M) :
    ((liftedPowSectionBimoduleSystem f ht 𝓜).trans h).rightHom.toFun y =
      𝓜.sectionRestrictAdd (liftedPowStageMap t h) y :=
  rfl

/-! ### Functoriality in the module -/

variable {𝓜} {𝓝 : SheafOfModules.DifferentialGradedModule.{u, u, u} (liftedPowSheafAlgebra.{u} f)}

/-- The homomorphism of sections over the stage carrying `K_{t+n}` induced by a homomorphism of
right differential graded `ℬ`-modules. -/
def liftedPowSectionModuleMap (φ : 𝓜 ⟶ 𝓝) (n : ℕ) :
    liftedPowSectionModule f ht 𝓜 n ⟶ liftedPowSectionModule f ht 𝓝 n :=
  extendBaseHom (ULift.{u} ℤ) (restrictScalarsHom (liftedPowSectionAlgebraHom f ht n)
    (SheafOfModules.DifferentialGradedModule.sectionMap φ (liftedPowStage t n)))

/-- The underlying function of `Koszul.liftedPowSectionModuleMap` is the map of sections. -/
theorem liftedPowSectionModuleMap_toFun (φ : 𝓜 ⟶ 𝓝) (n : ℕ)
    (x : (liftedPowSectionModule f ht 𝓜 n).M) :
    (liftedPowSectionModuleMap f ht φ n).toFun x =
      SheafOfModules.DifferentialGradedModule.sectionMapAdd φ (liftedPowStage t n) x :=
  rfl

/-- **The transitions are natural in the module**: restricting sections commutes with the maps
induced by a homomorphism of right differential graded `ℬ`-modules. -/
theorem liftedPowSectionTrans_naturality (φ : 𝓜 ⟶ 𝓝) {n m : ℕ} (h : n ≤ m)
    (x : (liftedPowSectionModule f ht 𝓜 m).M) :
    restrictScalarsFun (liftedPowSectionTrans f ht 𝓝 h)
        ((liftedPowSectionModuleMap f ht φ m).toFun x) =
      (liftedPowSectionModuleMap f ht φ n).toFun
        (restrictScalarsFun (liftedPowSectionTrans f ht 𝓜 h) x) := by
  rw [restrictScalarsFun_liftedPowSectionTrans, restrictScalarsFun_liftedPowSectionTrans,
    liftedPowSectionModuleMap_toFun]
  exact SheafOfModules.DifferentialGradedModule.sectionRestrictAdd_sectionMapAdd φ _ x

/-- The homomorphism of the `n`-th bimodules of the systems induced by a homomorphism of right
differential graded `ℬ`-modules. -/
def liftedPowSectionBimoduleMap (φ : 𝓜 ⟶ 𝓝) (n : ℕ) :
    (liftedPowSectionBimoduleSystem f ht 𝓜).bimod n ⟶
      (liftedPowSectionBimoduleSystem f ht 𝓝).bimod n :=
  flipMap (liftedPowSectionModuleMap f ht φ n)

/-- The underlying function of `Koszul.liftedPowSectionBimoduleMap` is the map of sections. -/
theorem liftedPowSectionBimoduleMap_toFun (φ : 𝓜 ⟶ 𝓝) (n : ℕ)
    (x : (liftedPowSectionModule f ht 𝓜 n).M) :
    (liftedPowSectionBimoduleMap f ht φ n).rightHom.toFun x =
      SheafOfModules.DifferentialGradedModule.sectionMapAdd φ (liftedPowStage t n) x :=
  rfl

end Sheaf

end Koszul
