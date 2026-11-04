module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesFinite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyReesSystemGraded
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesGradedModuleAffineFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ReesGradedModule
public import StacksFrontier.RingTheory.Filtration.IdealPowerSystemNoetherian
public import StacksCore.Tactic.StacksAttribute

/-!
# Further results on `CohomologyGradedReesFinite`

Results about the objects of
`StacksFrontier.AlgebraicGeometry.FormalFunctions.CohomologyGradedReesFinite` that need imports
beyond those of that module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower Stacks.Cohomology.AffineBase Stacks.Blowup
open scoped DirectSum ModuleCat.Algebra

universe u u' v' t' a' m'

namespace Stacks.Cohomology.FormalFunctions

attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra
  Stacks.Algebraization.sectionsModuleΓ Stacks.Algebraization.sectionsModuleΓSheaf

variable {A : Type u} [CommRing A] (I : Ideal A) (X : Over (Spec (.of A)))

/-! ### A system of global homogeneous sections of a sheaf of graded algebras -/

section Act

open SheafOfModules.GradedModule

/-- **A system of global homogeneous sections of a sheaf of graded algebras `𝓑` on `X`,
indexed by an `ℕ`-graded monoid `𝒢`.** This is the whole algebra-specific input of the graded
module of cohomology built below: a map sending a homogeneous element of degree `k` of `𝒢` to a
global section of `𝓑ₖ`, which is additive, sends the unit of `𝒢` to the unit of `𝓑`, and is
multiplicative.

The multiplicativity law is stated with the two factors in the order `b'`, `b` and the result
transported to degree `k + l`. That order is the one the associativity of a *right* graded
module needs — the graded module of cohomology is a left module over `𝒢`, so a product of
scalars acts in the reverse order — and in both systems constructed in this library the algebra
is commutative, so it is no extra demand. -/
structure SectionSystem (𝓑 : SheafOfModules.GradedAlgebra.{u, u} X.left.ringCatSheaf)
    (𝒢 : ℕ → Type u) [∀ n, AddCommGroup (𝒢 n)] [GradedMonoid.GMonoid 𝒢] where
  /-- The global section of `𝓑ₖ` attached to a homogeneous element of degree `k`. -/
  sec : ∀ {k : ℕ}, 𝒢 k → (𝓑.piece (k : ℤ)).val.sections
  /-- The attached section is additive. -/
  eval_add {k : ℕ} (b b' : 𝒢 k) (U : (Opens X.left)ᵒᵖ) :
    (sec (b + b')).eval U = (sec b).eval U + (sec b').eval U
  /-- The section attached to the unit is the unit. -/
  eval_one (U : (Opens X.left)ᵒᵖ) :
    (sec (GradedMonoid.GOne.one : 𝒢 0)).eval U = 𝓑.one.eval U
  /-- The section attached to a product is the product of the attached sections. -/
  castHom_mul {k l : ℕ} (b : 𝒢 k) (b' : 𝒢 l) (U : (Opens X.left)ᵒᵖ) :
    SheafOfModules.castHom 𝓑.piece (degree_add_eq k l) U
        ((𝓑.mul (l : ℤ) (k : ℤ)).app U ((sec b').eval U) ((sec b).eval U)) =
      (sec (GradedMonoid.GMul.mul b b')).eval U

variable {X}
variable {𝓑 : SheafOfModules.GradedAlgebra.{u, u} X.left.ringCatSheaf} {𝒢 : ℕ → Type u}
  [∀ n, AddCommGroup (𝒢 n)] [GradedMonoid.GMonoid 𝒢] (S : SectionSystem X 𝓑 𝒢)
  (M : SheafOfModules.GradedModule.{u, u, u} 𝓑)

/-- The section attached to the zero element vanishes. -/
theorem SectionSystem.eval_zero {k : ℕ} (U : (Opens X.left)ᵒᵖ) :
    (S.sec (0 : 𝒢 k)).eval U = 0 := by
  simpa using S.eval_add (0 : 𝒢 k) 0 U

/-- **The action of a homogeneous element of degree `k` of `𝒢` on a graded `𝓑`-module**, as a
morphism `Mₙ ⟶ Mₘ`. The target degree is an argument, supplied together with a proof that it
equals `n + k`: this is what keeps the degree bookkeeping out of the identities proved below. -/
def gradedActHom {k : ℕ} (b : 𝒢 k) (n : ℤ) {m : ℤ} (hm : n + (k : ℤ) = m) :
    M.piece n ⟶ M.piece m :=
  smulSectionsHom M n (k : ℤ) (S.sec b) ≫ pieceCast M hm

/-- The action on sections: multiplication by the attached global section, followed by the
transport to the target degree. -/
theorem gradedActHom_app {k : ℕ} (b : 𝒢 k) (n : ℤ) {m : ℤ} (hm : n + (k : ℤ) = m)
    (U : (Opens X.left)ᵒᵖ) (y : (M.piece n).val.obj U) :
    ((gradedActHom S M b n hm).val.app U) y =
      ((pieceCast M hm).val.app U)
        (((smulSectionsHom M n (k : ℤ) (S.sec b)).val.app U) y) := rfl

/-- Following the action by a transport of degrees is again an action, with a different target
degree. -/
theorem gradedActHom_comp_pieceCast {k : ℕ} (b : 𝒢 k) (n : ℤ) {m m' : ℤ}
    (hm : n + (k : ℤ) = m) (e : m = m') :
    gradedActHom S M b n hm ≫ pieceCast M e = gradedActHom S M b n (hm.trans e) := by
  rw [gradedActHom, gradedActHom, Category.assoc, pieceCast_pieceCast]

/-- The action is additive in the acting element. -/
theorem gradedActHom_add {k : ℕ} (b b' : 𝒢 k) (n : ℤ) {m : ℤ} (hm : n + (k : ℤ) = m) :
    gradedActHom S M (b + b') n hm = gradedActHom S M b n hm + gradedActHom S M b' n hm := by
  rw [gradedActHom, gradedActHom, gradedActHom,
    smulSectionsHom_eval_add M n (k : ℤ) (S.eval_add b b'), Preadditive.add_comp]

/-- The zero element acts by zero. -/
theorem gradedActHom_zero {k : ℕ} (n : ℤ) {m : ℤ} (hm : n + (k : ℤ) = m) :
    gradedActHom S M (0 : 𝒢 k) n hm = 0 := by
  rw [gradedActHom, smulSectionsHom_eval_zero M n (k : ℤ) (S.eval_zero (k := k)),
    Limits.zero_comp]

/-- Preceding the action by a transport of degrees is again an action, with a different source
degree. -/
theorem pieceCast_comp_gradedActHom {k : ℕ} (b : 𝒢 k) {n n' : ℤ} (e : n = n')
    {m : ℤ} (hm : n' + (k : ℤ) = m) (hm' : n + (k : ℤ) = m) :
    pieceCast M e ≫ gradedActHom S M b n' hm = gradedActHom S M b n hm' := by
  subst e
  rw [pieceCast_rfl, Category.id_comp]

/-- **The unit of `𝒢` acts by the identity**, up to the transport identifying the source and
target degrees. -/
theorem gradedActHom_one (n : ℤ) {m : ℤ} (hm : n + ((0 : ℕ) : ℤ) = m) (hn : n = m) :
    gradedActHom S M (GradedMonoid.GOne.one : 𝒢 0) n hm = pieceCast M hn := by
  have h1 : smulSectionsHom M n ((0 : ℕ) : ℤ) (S.sec (GradedMonoid.GOne.one : 𝒢 0)) ≫
      pieceCast M (add_zero n) = 𝟙 (M.piece n) := by
    rw [smulSectionsHom_congr M n ((0 : ℕ) : ℤ) S.eval_one]
    exact smulSectionsHom_one M n
  rw [← gradedActHom_comp_pieceCast S M _ n (add_zero n) hn, gradedActHom, h1,
    Category.id_comp]

/-- **The action of `𝒢` is associative**: acting by `b'` and then by `b` is acting by their
product `b · b'`. -/
theorem gradedActHom_comp {k l : ℕ} (b : 𝒢 k) (b' : 𝒢 l) (n : ℤ) {m₁ m₂ : ℤ}
    (h1 : n + (l : ℤ) = m₁) (h2 : m₁ + (k : ℤ) = m₂) (h3 : n + ((k + l : ℕ) : ℤ) = m₂) :
    gradedActHom S M b' n h1 ≫ gradedActHom S M b m₁ h2 =
      gradedActHom S M (GradedMonoid.GMul.mul b b') n h3 := by
  have hnij : n + (l : ℤ) + (k : ℤ) = m₂ := by rw [h1, h2]
  calc gradedActHom S M b' n h1 ≫ gradedActHom S M b m₁ h2
      = smulSectionsHom M n (l : ℤ) (S.sec b') ≫
          pieceCast M h1 ≫ gradedActHom S M b m₁ h2 := Category.assoc _ _ _
    _ = smulSectionsHom M n (l : ℤ) (S.sec b') ≫
          gradedActHom S M b (n + (l : ℤ)) hnij := by
        rw [pieceCast_comp_gradedActHom S M b h1 h2 hnij]
    _ = smulSectionsHom M n (l : ℤ) (S.sec b') ≫
          smulSectionsHom M (n + (l : ℤ)) (k : ℤ) (S.sec b) ≫ pieceCast M hnij := rfl
    _ = gradedActHom S M (GradedMonoid.GMul.mul b b') n h3 :=
        smulSectionsHom_comp M (degree_add_eq k l) h3 hnij (S.sec b') (S.sec b)
          (S.sec (GradedMonoid.GMul.mul b b')) (S.castHom_mul b b')

/-! ### The graded `𝒢`-module `⨁ₙ Hᵖ(X, Mₙ)` -/

variable (p : ℕ)

/-- `Hᵖ(X, Mₙ)` for a natural number `n`, the degree-`n` piece of the graded `𝒢`-module. -/
abbrev gradedCohomologyPieceOfGrading (n : ℕ) : Type u :=
  (cohomologyFunctor X p).obj (M.piece (n : ℤ))

/-- The action of a homogeneous element of degree `k` of `𝒢` on `Hᵖ(X, Mₙ)`. -/
def gradedCohomologySmulOfGrading {k n : ℕ} (b : 𝒢 k) (x : gradedCohomologyPieceOfGrading M p n) :
    gradedCohomologyPieceOfGrading M p (k + n) :=
  ((cohomologyFunctor X p).map (gradedActHom S M b (n : ℤ) (degree_add_eq k n))).hom x

/-- Two cohomology classes in propositionally equal degrees are equal in `Σ n, Hᵖ(X, Mₙ)` as soon
as one is the transport of the other. This is what reduces the `GradedMonoid` equations of
`DirectSum.Gmodule` to identities of morphisms. -/
theorem sigma_eq_of_pieceCast_ofGrading {m n : ℕ} (e : m = n)
    {x : gradedCohomologyPieceOfGrading M p m} {y : gradedCohomologyPieceOfGrading M p n}
    (h : ((cohomologyFunctor X p).map
        (pieceCast M (congrArg (Nat.cast (R := ℤ)) e))).hom x = y) :
    (⟨m, x⟩ : Σ j, gradedCohomologyPieceOfGrading M p j) = ⟨n, y⟩ := by
  subst e
  refine congrArg (Sigma.mk m) ?_
  rw [← h, pieceCast_rfl]
  exact (cohomologyFunctor_map_id_apply X p x).symm

/-- **The graded `𝒢`-module `⨁ₙ Hᵖ(X, Mₙ)`**, for an arbitrary graded `𝓑`-module `M` and an
arbitrary system `S` of global homogeneous sections of `𝓑` indexed by `𝒢`. The unit law and the
associativity are `gradedActHom_one` and `gradedActHom_comp`; additivity in both arguments is the
additivity of `Hᵖ(X, −)` together with `gradedActHom_add`. -/
@[instance_reducible]
def gradedCohomologyGmodule : DirectSum.Gmodule 𝒢 (gradedCohomologyPieceOfGrading M p) where
  smul := gradedCohomologySmulOfGrading S M p
  smul_add _ _ _ := map_add _ _ _
  smul_zero _ := map_zero _
  add_smul b b' x :=
    (congrArg (fun φ : _ ⟶ _ => ((cohomologyFunctor X p).map φ).hom x)
      (gradedActHom_add S M b b' _ (degree_add_eq _ _))).trans
      (cohomologyFunctor_map_add_apply X p _ _ x)
  zero_smul x :=
    (congrArg (fun φ : _ ⟶ _ => ((cohomologyFunctor X p).map φ).hom x)
      (gradedActHom_zero S M _ (degree_add_eq _ _))).trans
      (cohomologyFunctor_map_zero_apply X p x)
  one_smul := by
    rintro ⟨n, x⟩
    refine sigma_eq_of_pieceCast_ofGrading M p (Nat.zero_add n) ?_
    have key : gradedActHom S M (GradedMonoid.GOne.one : 𝒢 0) (n : ℤ) (degree_add_eq 0 n) ≫
          pieceCast M (congrArg (Nat.cast (R := ℤ)) (Nat.zero_add n)) =
        𝟙 (M.piece (n : ℤ)) := by
      rw [gradedActHom_comp_pieceCast, gradedActHom_one S M (n : ℤ) _ rfl]
      exact pieceCast_rfl M rfl
    change ((cohomologyFunctor X p).map
          (pieceCast M (congrArg (Nat.cast (R := ℤ)) (Nat.zero_add n)))).hom
        (((cohomologyFunctor X p).map
          (gradedActHom S M (GradedMonoid.GOne.one : 𝒢 0)
            (n : ℤ) (degree_add_eq 0 n))).hom x) = x
    refine (cohomologyFunctor_map_comp_apply X p _ _ x).trans ?_
    exact (congrArg (fun φ : M.piece (n : ℤ) ⟶ M.piece (n : ℤ) =>
        ((cohomologyFunctor X p).map φ).hom x) key).trans
      (cohomologyFunctor_map_id_apply X p x)
  mul_smul := by
    rintro ⟨k, b⟩ ⟨l, b'⟩ ⟨n, x⟩
    refine sigma_eq_of_pieceCast_ofGrading M p (Nat.add_assoc k l n) ?_
    have key : gradedActHom S M (GradedMonoid.GMul.mul b b')
          (n : ℤ) (degree_add_eq (k + l) n) ≫
          pieceCast M (congrArg (Nat.cast (R := ℤ)) (Nat.add_assoc k l n)) =
        gradedActHom S M b' (n : ℤ) (degree_add_eq l n) ≫
          gradedActHom S M b ((l + n : ℕ) : ℤ) (degree_add_eq k (l + n)) := by
      rw [gradedActHom_comp_pieceCast]
      exact (gradedActHom_comp S M b b' (n : ℤ) (degree_add_eq l n)
        (degree_add_eq k (l + n)) (by push_cast; ring)).symm
    change ((cohomologyFunctor X p).map
          (pieceCast M (congrArg (Nat.cast (R := ℤ)) (Nat.add_assoc k l n)))).hom
        (((cohomologyFunctor X p).map
          (gradedActHom S M (GradedMonoid.GMul.mul b b')
            (n : ℤ) (degree_add_eq (k + l) n))).hom x) =
      ((cohomologyFunctor X p).map
          (gradedActHom S M b ((l + n : ℕ) : ℤ) (degree_add_eq k (l + n)))).hom
        (((cohomologyFunctor X p).map
          (gradedActHom S M b' (n : ℤ) (degree_add_eq l n))).hom x)
    refine (cohomologyFunctor_map_comp_apply X p _ _ x).trans ?_
    exact (congrArg (fun φ : M.piece (n : ℤ) ⟶ M.piece ((k + (l + n) : ℕ) : ℤ) =>
        ((cohomologyFunctor X p).map φ).hom x) key).trans
      (cohomologyFunctor_map_comp_apply X p _ _ x).symm

end Act

/-! ### The action of `B = ⨁ₙ Iⁿ` on an arbitrary graded `𝓑 = ⨁ₙ ℐⁿ`-module -/

section ReesAct

open SheafOfModules.GradedModule

variable (M : SheafOfModules.GradedModule.{u, u, u} (baseReesAlgebra I X)) (p : ℕ)

/-- **The Rees algebra's system of global homogeneous sections**: a homogeneous element of
degree `k` of `B = ⨁ₙ Iⁿ` goes to the global section `gradedReesSection` of `𝓑ₖ = ℐᵏ`. -/
def reesSectionSystem :
    SectionSystem X (baseReesAlgebra I X) (fun n => ↥(reesGrading I n)) where
  sec := gradedReesSection I X
  eval_add b b' U := eval_gradedReesSection_add I X b b' U
  eval_one U := eval_gradedReesSection_one I X U
  castHom_mul b b' U :=
    castHom_mul_gradedReesSection I X b' b _ ((reesElt_mul I b b').trans (mul_comm _ _)) _ U

/-- **The graded `B = ⨁ₙ Iⁿ`-module `⨁ₙ Hᵖ(X, Mₙ)`**, for an arbitrary graded
`𝓑 = ⨁ₙ ℐⁿ`-module `M`. This is `gradedCohomologyGmodule` at `reesSectionSystem`. -/
@[instance_reducible]
def cohomologyGradedModuleOfGrading :
    DirectSum.Gmodule (fun n => ↥(reesGrading I n)) (gradedCohomologyPieceOfGrading M p) :=
  gradedCohomologyGmodule (reesSectionSystem I X) M p

end ReesAct

section Bridge

open SheafOfModules.GradedModule

variable (F : X.left.Modules) (p : ℕ)

/-- **The comparison.** At `M = ⨁ₙ ℐⁿℱ` the action of a homogeneous element of degree `k` of
`B = ⨁ₙ Iⁿ`, read through the identification of the two models of `ℐⁿℱ`, is the multiplication
map `Stacks.Cohomology.FormalFunctions.idealPowerSmul` by the underlying element of `Iᵏ` — the
map out of which `cohomologyIdealPowerSystem` is built.

Both sides land in a subsheaf of `ℱ`, so it suffices to compare the composites with the inclusion
into `ℱ`, where both are multiplication of an ambient section by one function on the base. -/
theorem actHom_comp_filtrationPieceIso_gradedActHom (k n : ℕ) (b : ↥(reesGrading I k)) :
    gradedActHom (reesSectionSystem I X) (reesFiltrationModule I X F) b (n : ℤ)
          (degree_add_eq k n) ≫
        filtrationPieceIso I X F (k + n) =
      filtrationPieceIso I X F n ≫
        idealPowerSmul I X F (le_refl (k + n)) (reesElt I b) (reesElt_mem I b) := by
  refine cancel_sheafSubmodule_ι _ _ _ (hom_ext_of_sections X fun U x ↦ ?_)
  have hL : (((gradedActHom (reesSectionSystem I X) (reesFiltrationModule I X F) b (n : ℤ)
        (degree_add_eq k n)).val.app U) x).1 =
      baseRingToSections A X U (reesElt I b) • (x.1 : F.val.obj U) :=
    (congrArg (fun z : ((reesFiltrationModule I X F).piece ((k + n : ℕ) : ℤ)).val.obj U => z.1)
      (gradedActHom_app (reesSectionSystem I X) (reesFiltrationModule I X F) b (n : ℤ)
        (degree_add_eq k n) U x)).trans
      ((pieceCast_reesFiltrationModule_coe I X F (degree_add_eq k n) U _).trans
        (smulSectionsHom_reesGradedModule_coe I X F k n (reesElt I b) (reesElt_mem I b) U x))
  refine (submoduleCast_coe X F (reesMultiple_natCast_eq_idealPowerSub I X F (k + n)) U
    (((gradedActHom (reesSectionSystem I X) (reesFiltrationModule I X F) b (n : ℤ)
      (degree_add_eq k n)).val.app U) x)).trans ?_
  refine hL.trans ?_
  refine (congrArg (fun z : F.val.obj U => baseRingToSections A X U (reesElt I b) • z)
    (submoduleCast_coe X F (reesMultiple_natCast_eq_idealPowerSub I X F n) U x).symm).trans ?_
  exact (idealPowerSmul_coe I X F (le_refl (k + n)) (reesElt I b) (reesElt_mem I b) U
    (((filtrationPieceIso I X F n).val.app U) x)).symm

attribute [local instance] cohomologyGradedModule

attribute [local instance] filtrationCohomologyGmodule

/-- **[Stacks, Tag 02O8], given part (1) of [Stacks, Tag 0897] for graded modules.** For `A`
Noetherian, `I ⊆ A` an ideal, `f : X → Spec A` proper and `ℱ` coherent, the graded module
`⨁_{n ≥ 0} Hᵖ(X, Iⁿℱ)` is a finite module over the Rees algebra `B = ⨁_{n ≥ 0} Iⁿ` of `I`, the
graded-module structure being the one carried by
`Stacks.Cohomology.FormalFunctions.cohomologyIdealPowerSystem`.

The hypothesis `h0897` is [Stacks, Tag 0897] part (1), carried with the source's own
antecedents: `A` Noetherian, `f` proper, and the graded `𝓑 = ⨁ₙ ℐⁿ`-module
quasi-coherent and of finite type on every affine open. It is quantified over **every** graded
`𝓑`-module `M`, and its conclusion
`Stacks.Cohomology.FormalFunctions.IsCohomologyReesFiniteOfGradedModule` speaks about that `M`
alone: it says that `⨁ₙ Hᵖ(X, Mₙ)` is a finite `B`-module, and mentions neither the ideal-power
filtration of `ℱ` nor the predicate in the conclusion below. The proof instantiates it at
`M = ⨁ₙ ℐⁿℱ`, discharging the antecedents with
`Stacks.Blowup.isFiniteTypeOnAffine_reesGradedModule_of_isCoherent` and
`isQuasicoherent_piece_reesFiltrationModule`, and transports the resulting finiteness along the
surjection `transferLinear`, whose `B`-linearity is `transferAddHom_smul`.

The finite-type antecedent is the affine-local one that
`Stacks.AlgebraicGeometry.GradedProperCohomology.moduleFinite_gradedCohomologySum`, a proof of
part (1), consumes. -/
theorem isCohomologyReesFinite_of_isCoherent_of_isFiniteTypeOnAffine [IsNoetherianRing A]
    (hX : AlgebraicGeometry.IsProper X.hom) [F.IsCoherent]
    (h0897 : ∀ M : SheafOfModules.GradedModule.{u, u, u} (baseReesAlgebra I X),
      IsNoetherianRing A → AlgebraicGeometry.IsProper X.hom →
        Stacks.Coherent.IsFiniteTypeOnAffine M →
        (∀ n : ℤ, (M.piece n).IsQuasicoherent) →
          IsCohomologyReesFiniteOfGradedModule I X M p) :
    IsCohomologyReesFinite I X F p := by
  have hft : Stacks.Coherent.IsFiniteTypeOnAffine (reesFiltrationModule I X F) :=
    isFiniteTypeOnAffine_reesGradedModule_of_isCoherent (baseIdealSheaf A I X.hom) F
      inferInstance
  have hfin : Module.Finite (⨁ n, ↥(reesGrading I n))
      (⨁ n, gradedCohomologyPieceOfGrading (reesFiltrationModule I X F) p n) :=
    h0897 (reesFiltrationModule I X F) inferInstance hX hft
      (isQuasicoherent_piece_reesFiltrationModule I X F)
  change Module.Finite (⨁ n, ↥(reesGrading I n)) (⨁ n, cohomologyIdealPower I X F p n)
  exact Module.Finite.of_surjective (transferLinear I X F p) (transferLinear_surjective I X F p)

end Bridge

end Stacks.Cohomology.FormalFunctions

end
