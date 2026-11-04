module

public import Mathlib.RingTheory.OrzechProperty
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExteriorSymmetricAlgebras
public import StacksFrontier.AlgebraicGeometry.ProjEulerSequence.WedgeFiltrationArrow
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.KoszulResolution
public import StacksFrontier.RingTheory.Koszul.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Koszul complex of a cosection of a module on a scheme

Let `Y` be a scheme, `ℰ` an `𝒪_Y`-module and `φ : ℰ ⟶ 𝒪_Y` a morphism into the structure sheaf.
The exterior algebra of `ℰ` carries the degree `-1` derivation of Stacks Tag 062K attached to
`φ`, and its homogeneous pieces form the *Koszul complex*

  `⋯ ⟶ ⋀³ℰ ⟶ ⋀²ℰ ⟶ ℰ ⟶ 𝒪_Y`,

a chain complex of `𝒪_Y`-modules with `⋀ⁿℰ` in degree `n`. This file builds that complex and
proves the stalkwise criterion for its exactness in positive degrees: the stalk of the complex at
a point `x` is the Koszul complex of the functional `ψ_x : ℰ_x ⟶ 𝒪_{Y,x}` induced by `φ`
(Stacks Tag 01CH), and exactness of a complex of sheaves is exactness at every stalk (Stacks
Tag 01AG). At a point where `ψ_x` takes the value `1` the stalk complex is contractible (Stacks
Tag 0626), and at a point where `ℰ_x` has a basis on which `ψ_x` is a Koszul-regular sequence it
is exact in positive degrees by definition (Stacks Tag 062E).

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.koszulDifferential`: the contraction `⋀^{n+1}ℰ ⟶ ⋀ⁿℰ`.
* `AlgebraicGeometry.Scheme.Modules.koszulChainComplex`: the Koszul complex of `φ`.
* `AlgebraicGeometry.Scheme.Modules.koszulStalkDual`: the functional `ψ_x` on the stalk.

## Main results

* `exteriorPower.contraction_exact_of_apply_eq_one`: the Koszul complex of a functional taking
  the value `1` is exact.
* `exteriorPower.contraction_exact_of_basis`: the Koszul complex of a functional which is a
  Koszul-regular sequence on a basis is exact in positive degrees.
* `Module.Basis.exists_eq_of_span_eq_top`: a spanning family of `r` vectors of a free module of
  rank `r` is a basis.
* `AlgebraicGeometry.Scheme.Modules.exteriorGenerator_comp_koszulDifferential_zero`: the first
  differential is `φ`, through `ℰ ≅ ⋀¹ℰ` and `⋀⁰ℰ ≅ 𝒪_Y`.
* `AlgebraicGeometry.Scheme.Modules.koszulChainComplex_exactAt_succ`: exactness of the Koszul
  complex in a positive degree, from exactness of the stalk Koszul complexes.
* `AlgebraicGeometry.Scheme.Modules.koszulChainComplex_exactAt_succ_of_forall`: the same, from
  the two local situations above.

## References

* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 062E](https://stacks.math.columbia.edu/tag/062E)
* [Stacks Project, Tag 0626](https://stacks.math.columbia.edu/tag/0626)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-! ### The module-level Koszul complex -/

namespace exteriorPower

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- The contraction of `exteriorPower.contraction` is the restriction of the Clifford
contraction, `exteriorPower.contract`. -/
theorem contraction_eq_contract (ψ : Module.Dual R M) (n : ℕ) :
    contraction ψ n = contract ψ n := by
  rw [contraction_eq_koszulD]
  rfl

/-- **The Koszul complex of a functional taking the value `1` is exact** (Stacks Tag 0626):
wedging with a vector on which the functional is `1` is a contracting homotopy. -/
theorem contraction_exact_of_apply_eq_one (ψ : Module.Dual R M) {e : M} (he : ψ e = 1)
    (n : ℕ) : Function.Exact (contraction ψ (n + 1)) (contraction ψ n) := by
  rw [contraction_eq_contract, contraction_eq_contract]
  exact contract_exact_of_apply_eq_one ψ he n

/-- **The Koszul complex of a Koszul-regular functional is exact in positive degrees.** If `ψ`
is a Koszul-regular sequence on a basis `b` of `M`, then `M ≅ Rʳ` carries `ψ` to the functional
of that sequence, so the Koszul complex of `ψ` is the Koszul complex of the sequence. -/
theorem contraction_exact_of_basis {r : ℕ} (ψ : Module.Dual R M) (b : Module.Basis (Fin r) R M)
    (hreg : Koszul.IsKoszulRegular fun j => ψ (b j)) (n : ℕ) :
    Function.Exact (contraction ψ (n + 1)) (contraction ψ n) := by
  set f : Fin r → R := fun j => ψ (b j)
  have hexact : Function.Exact (Koszul.d (Koszul.seqDual f) (n + 1))
      (Koszul.d (Koszul.seqDual f) n) := by
    have h := hreg (n + 1) (Nat.succ_ne_zero n)
    rw [← HomologicalComplex.exactAt_iff_isZero_homology,
      HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp),
      CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h
    change Function.Exact (ModuleCat.Hom.hom ((Koszul.seqComplex f).d (n + 1 + 1) (n + 1)))
      (ModuleCat.Hom.hom ((Koszul.seqComplex f).d (n + 1) n)) at h
    rw [Koszul.seqComplex_d, Koszul.seqComplex_d] at h
    exact h
  set g : M ≃ₗ[R] (Fin r → R) := b.equivFun
  have hξ : Koszul.seqDual f ∘ₗ g.toLinearMap = ψ := by
    refine b.ext fun j => ?_
    simp [g, f, Koszul.seqDual_apply, Module.Basis.equivFun_apply, Finsupp.single_apply]
  let e : ∀ p : ℕ, ⋀[R]^p M ≃ₗ[R] ⋀[R]^p (Fin r → R) := fun p =>
    LinearEquiv.ofLinear (map p g.toLinearMap) (map p g.symm.toLinearMap)
      (by rw [← map_comp]; simp) (by rw [← map_comp]; simp)
  have hnat : ∀ p : ℕ, Koszul.d (Koszul.seqDual f) p ∘ₗ (e (p + 1)).toLinearMap =
      (e p).toLinearMap ∘ₗ contraction ψ p := fun p => by
    rw [← contraction_eq_koszulD, ← hξ]
    exact (map_comp_contraction (Koszul.seqDual f) g.toLinearMap p).symm
  exact (Function.Exact.iff_of_ladder_linearEquiv (hnat (n + 1)) (hnat n)).1 hexact

end exteriorPower

namespace Module.Basis

/-- **A spanning family of `r` vectors of a free module of rank `r` is a basis.** The family
defines a surjection `Rʳ ⟶ M ≅ Rʳ`, and a surjective endomorphism of a finitely generated module
over a commutative ring is injective. -/
@[sga "3 X 3.8" "special case"]
theorem exists_eq_of_span_eq_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {r : ℕ} (β : Module.Basis (Fin r) R M) (v : Fin r → M)
    (hv : Submodule.span R (Set.range v) = ⊤) :
    ∃ c : Module.Basis (Fin r) R M, ⇑c = v := by
  set F : (Fin r → R) →ₗ[R] M := Fintype.linearCombination R v
  have hF : Function.Surjective F := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hv]
  have hG : Function.Injective (β.equivFun.toLinearMap ∘ₗ F) :=
    OrzechProperty.injective_of_surjective_endomorphism _
      (β.equivFun.surjective.comp hF)
  have hFi : Function.Injective F := fun a b hab => hG (by simp [hab])
  refine ⟨Module.Basis.mk (linearIndependent_iff_injective_fintypeLinearCombination.2 hFi)
    hv.ge, ?_⟩
  exact Module.Basis.coe_mk _ _

end Module.Basis

/-! ### The Koszul complex of a cosection -/

namespace AlgebraicGeometry.Scheme.Modules

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

variable {Y : Scheme.{u}} (ℰ : Y.Modules) (φ : ℰ ⟶ SheafOfModules.unit Y.ringCatSheaf)

/-- **The Koszul differential `⋀^{n+1}ℰ ⟶ ⋀ⁿℰ`** of a cosection `φ : ℰ ⟶ 𝒪_Y`: the contraction
`s₀ ∧ ⋯ ∧ sₙ ↦ ∑ₖ (-1)ᵏ φ(sₖ) s₀ ∧ ⋯ ∧ ŝₖ ∧ ⋯ ∧ sₙ` of Stacks Tag 062K. -/
def koszulDifferential (n : ℕ) :
    exteriorPower ℰ ((n + 1 : ℕ) : ℤ) ⟶ exteriorPower ℰ (n : ℤ) :=
  SheafOfModules.exteriorContraction (Osharp := Y.sheaf) ℰ (exteriorAlgebra ℰ)
    (exteriorGenerator ℰ) (isExteriorAlgebra_exteriorAlgebra ℰ) φ n

/-- The Koszul differential squares to zero. -/
@[reassoc (attr := simp)]
theorem koszulDifferential_comp (n : ℕ) :
    koszulDifferential ℰ φ (n + 1) ≫ koszulDifferential ℰ φ n = 0 :=
  SheafOfModules.exteriorContraction_comp_exteriorContraction (Osharp := Y.sheaf) ℰ
    (exteriorAlgebra ℰ) (exteriorGenerator ℰ) (isExteriorAlgebra_exteriorAlgebra ℰ) φ n

/-- **The Koszul complex of a cosection `φ : ℰ ⟶ 𝒪_Y`**: the chain complex with `⋀ⁿℰ` in degree
`n` and the Koszul differentials. -/
def koszulChainComplex : ChainComplex Y.Modules ℕ :=
  ChainComplex.of (fun n => exteriorPower ℰ (n : ℤ))
    (fun n => koszulDifferential ℰ φ n) (fun n => koszulDifferential_comp ℰ φ n)

/-- The term of the Koszul complex in degree `n` is `⋀ⁿℰ`. -/
theorem koszulChainComplex_X (n : ℕ) :
    (koszulChainComplex ℰ φ).X n = exteriorPower ℰ (n : ℤ) :=
  rfl

/-- The differential of the Koszul complex from degree `n + 1` to degree `n` is the Koszul
differential of the cosection. -/
theorem koszulChainComplex_d (n : ℕ) :
    (koszulChainComplex ℰ φ).d (n + 1) n = koszulDifferential ℰ φ n :=
  ChainComplex.of_d (fun k : ℕ => exteriorPower ℰ (k : ℤ))
    (fun k : ℕ => koszulDifferential ℰ φ k) n

/-- **The first Koszul differential is the cosection**: through `ℰ ≅ ⋀¹ℰ` and `⋀⁰ℰ ≅ 𝒪_Y`,
`d : ⋀¹ℰ ⟶ ⋀⁰ℰ` is `φ`. This is the defining equation `d(e) = φ(e)` of Stacks Tag 062K. -/
theorem exteriorGenerator_comp_koszulDifferential_zero :
    exteriorGenerator ℰ ≫ koszulDifferential ℰ φ 0 ≫
      (SheafOfModules.algebras _ ℰ).exteriorPieceZeroIsoUnit.hom = φ := by
  refine SheafOfModules.hom_ext ?_
  refine PresheafOfModules.hom_ext fun U => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
  have hι : ∀ p : ℕ, ((exteriorAlgebra ℰ).extPowCmp (hO := (Sheaf.toRingCat
      (Opens.grothendieckTopology Y) Y.sheaf).property) (exteriorGenerator ℰ)
      (isExteriorAlgebra_exteriorAlgebra ℰ).1 p).app U (exteriorPower.ιMulti _ p fun _ => s) =
      (exteriorAlgebra ℰ).toPresheafGradedAlgebra.homogeneousProd U p
        fun _ => (exteriorGenerator ℰ).val.app U s := fun p =>
    Stacks.GradedAlgebra.extCmpSections_ιMulti
      (exteriorAlgebra ℰ).toPresheafGradedAlgebra (exteriorGenerator ℰ).val
      (fun Y y => (isExteriorAlgebra_exteriorAlgebra ℰ).1 Y y) p U fun _ => s
  have h1 : (exteriorGenerator ℰ).val.app U s = _ := ((hι 1).trans
    (eq_of_heq ((exteriorAlgebra ℰ).toPresheafGradedAlgebra.one_mul 1 U _))).symm
  have h2 := SheafOfModules.extPowCmp_app_exteriorContraction_one (Osharp := Y.sheaf) ℰ
    (exteriorAlgebra ℰ) (exteriorGenerator ℰ) (isExteriorAlgebra_exteriorAlgebra ℰ) φ U s
  show (SheafOfModules.algebras _ ℰ).exteriorPieceZeroIsoUnit.hom.val.app U
    ((koszulDifferential ℰ φ 0).val.app U ((exteriorGenerator ℰ).val.app U s)) = _
  rw [h1]
  refine (congrArg _ h2).trans ?_
  have h0 := hι 0
  refine (congrArg (fun w => ((SheafOfModules.algebras _ ℰ).exteriorPieceZeroIsoUnit.hom.val.app
    U).hom w) (LinearMap.map_smul (((exteriorAlgebra ℰ).extPowCmp (hO := (Sheaf.toRingCat
      (Opens.grothendieckTopology Y) Y.sheaf).property) (exteriorGenerator ℰ)
      (isExteriorAlgebra_exteriorAlgebra ℰ).1 0).app U).hom
      (SheafOfModules.unitDualApp φ U s) _)).trans ?_
  refine (congrArg (fun w => ((SheafOfModules.algebras _ ℰ).exteriorPieceZeroIsoUnit.hom.val.app
    U).hom (SheafOfModules.unitDualApp φ U s • w)) h0).trans ?_
  refine (LinearMap.map_smul ((SheafOfModules.algebras _ ℰ).exteriorPieceZeroIsoUnit.hom.val.app
    U).hom (SheafOfModules.unitDualApp φ U s) _).trans ?_
  refine (congrArg (fun z => SheafOfModules.unitDualApp φ U s • z)
    ((SheafOfModules.algebras _ ℰ).exteriorPieceZeroIsoUnit_one U)).trans ?_
  exact mul_one (SheafOfModules.unitDualApp φ U s)

variable {ℰ}

/-- **The functional `ψ_x : ℰ_x ⟶ 𝒪_{Y,x}` induced by `φ` on the stalk at `x`**: the stalk of
`φ`, with the stalk of the unit module read as the local ring. -/
def koszulStalkDual (x : Y) :
    ↑(TopCat.Presheaf.stalk ℰ.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk Y.sheaf.obj x)]
      ↑(TopCat.Presheaf.stalk Y.sheaf.obj x) :=
  (Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv Y.sheaf x).toLinearMap ∘ₗ
    PresheafOfModules.stalkMapL x φ.val

/-- The value of `ψ_x` on a germ is the germ of the value of `φ`. -/
theorem koszulStalkDual_germ (x : Y) (V : Y.Opens) (hv : x ∈ V)
    (t : ℰ.val.obj (Opposite.op V)) :
    koszulStalkDual φ x (TopCat.Presheaf.germ ℰ.val.presheaf V x hv t) =
      TopCat.Presheaf.germ Y.sheaf.obj V x hv (SheafOfModules.unitDualApp φ (Opposite.op V) t) :=
  Eq.trans (congrArg (Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv Y.sheaf x)
    (PresheafOfModules.stalkMapL_germ x φ.val V hv t))
    (Stacks.AlgebraicGeometry.ProjEulerSequence.unitStalkCommEquiv_germ Y.sheaf x V hv _)

/-- **The stalk of the Koszul differential is the Koszul differential of the stalk**, through
the comparison `(⋀ᵐℰ)ₓ ≅ ⋀ᵐ(ℰₓ)` of Stacks Tag 01CH. -/
theorem exteriorPowerStalkEquiv_stalkMapL_koszulDifferential (x : Y) (m : ℕ)
    (t : ↑(TopCat.Presheaf.stalk (exteriorPower ℰ ((m + 1 : ℕ) : ℤ)).val.presheaf x)) :
    SheafOfModules.exteriorPowerStalkEquiv (Osharp := Y.sheaf)
      (exteriorAlgebra ℰ) (exteriorGenerator ℰ) (isExteriorAlgebra_exteriorAlgebra ℰ) m x
        (PresheafOfModules.stalkMapL x (koszulDifferential ℰ φ m).val t) =
      exteriorPower.contraction (koszulStalkDual φ x) m
        (SheafOfModules.exteriorPowerStalkEquiv (Osharp := Y.sheaf)
          (exteriorAlgebra ℰ) (exteriorGenerator ℰ) (isExteriorAlgebra_exteriorAlgebra ℰ)
          (m + 1) x t) :=
  SheafOfModules.exteriorPowerStalkEquiv_stalkMapL_exteriorContraction (Osharp := Y.sheaf)
    (exteriorAlgebra ℰ) (exteriorGenerator ℰ) (isExteriorAlgebra_exteriorAlgebra ℰ) φ m x
    (koszulStalkDual φ x) (koszulStalkDual_germ φ x) t

/-- **Exactness of the Koszul complex in a positive degree is stalkwise** (Stacks Tags 01AG,
01CH): it holds as soon as the Koszul complex of `ψ_x` is exact in that degree at every point. -/
theorem koszulChainComplex_exactAt_succ (n : ℕ)
    (h : ∀ x : Y, Function.Exact (exteriorPower.contraction (koszulStalkDual φ x) (n + 1))
      (exteriorPower.contraction (koszulStalkDual φ x) n)) :
    (koszulChainComplex ℰ φ).ExactAt (n + 1) := by
  refine (Stacks.RegularSequence.exactAt_iff_forall_stalkAbFunctor_exactAt (Osharp := Y.sheaf)
    (koszulChainComplex ℰ φ) (n + 1)).2 fun x => ?_
  rw [HomologicalComplex.exactAt_iff' _ (n + 1 + 1) (n + 1) n (by simp) (by simp),
    ShortComplex.ab_exact_iff_function_exact]
  show Function.Exact
    (PresheafOfModules.stalkMapL x ((koszulChainComplex ℰ φ).d (n + 1 + 1) (n + 1)).val)
    (PresheafOfModules.stalkMapL x ((koszulChainComplex ℰ φ).d (n + 1) n).val)
  rw [koszulChainComplex_d, koszulChainComplex_d]
  let e : ∀ m : ℕ, _ := fun m => (SheafOfModules.exteriorPowerStalkEquiv (Osharp := Y.sheaf)
      (exteriorAlgebra ℰ) (exteriorGenerator ℰ) (isExteriorAlgebra_exteriorAlgebra ℰ) m x)
  refine (Function.Exact.iff_of_ladder_addEquiv (e (n + 1 + 1)).toAddEquiv
    (e (n + 1)).toAddEquiv (e n).toAddEquiv
    (f₁₂ := (PresheafOfModules.stalkMapL x (koszulDifferential ℰ φ (n + 1)).val).toAddMonoidHom)
    (f₂₃ := (PresheafOfModules.stalkMapL x (koszulDifferential ℰ φ n).val).toAddMonoidHom)
    (g₁₂ := (exteriorPower.contraction (koszulStalkDual φ x) (n + 1)).toAddMonoidHom)
    (g₂₃ := (exteriorPower.contraction (koszulStalkDual φ x) n).toAddMonoidHom)
    ?_ ?_).1 (h x)
  · exact AddMonoidHom.ext fun t =>
      (exteriorPowerStalkEquiv_stalkMapL_koszulDifferential φ x (n + 1) t).symm
  · exact AddMonoidHom.ext fun t =>
      (exteriorPowerStalkEquiv_stalkMapL_koszulDifferential φ x n t).symm

/-- **The local criterion for exactness of the Koszul complex in positive degrees.** If at every
point either `ψ_x` takes the value `1`, or `ℰ_x` has a basis on which `ψ_x` is a Koszul-regular
sequence, then the Koszul complex of `φ` is exact in every positive degree. -/
theorem koszulChainComplex_exactAt_succ_of_forall {r : ℕ}
    (h : ∀ x : Y, (∃ e, koszulStalkDual φ x e = 1) ∨
      ∃ b : Module.Basis (Fin r) ↑(TopCat.Presheaf.stalk Y.sheaf.obj x)
          ↑(TopCat.Presheaf.stalk ℰ.val.presheaf x),
        Koszul.IsKoszulRegular fun j => koszulStalkDual φ x (b j))
    (n : ℕ) : (koszulChainComplex ℰ φ).ExactAt (n + 1) := by
  refine koszulChainComplex_exactAt_succ φ n fun x => ?_
  rcases h x with ⟨e, he⟩ | ⟨b, hb⟩
  · exact exteriorPower.contraction_exact_of_apply_eq_one _ he n
  · exact exteriorPower.contraction_exact_of_basis _ b hb n

end AlgebraicGeometry.Scheme.Modules

end
