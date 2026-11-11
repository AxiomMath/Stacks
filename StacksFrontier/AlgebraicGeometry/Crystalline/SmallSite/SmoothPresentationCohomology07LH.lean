module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.EnvelopeBaseChangeRows
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalDeRhamComputesCohomology
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrystalPairFormsConnection
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceCompletedBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmoothPresentationBaseChange

/-!
# The de Rham complex of a smooth presentation computes crystalline cohomology

Let `ℱ` be a crystal in quasi-coherent modules over an affine crystalline situation, `(M, ∇)` its
pair over the completed envelope `D` of the presentation `A[x_i : i ∈ ι] → C` of the system
(the instance `...SmallSite.WholeSpacePresentation S hp`, by default the tautological
`A[x_c : c ∈ C] → C`)
([Stacks, Lemma 60.17.3, Tag 07JG]), and `A → P' → C` a smooth presentation with completed
envelope `D'`.  [Stacks, Lemma 60.21.4, Tag 07LH] says that the complex
`M' ⊗^∧_{D'} Ω^*_{D'}` of the pair `(M', ∇')` over `D'` corresponding to `ℱ` computes
`RΓ(Cris(X/S), ℱ)`.  This module proves its inputs — the stratification of the crystal and the
quasi-isomorphy of the base change `M ⊗^∧_D Ω^*_D → M' ⊗^∧_{D'} Ω^*_{D'}` — and its reading on
cohomology groups; the isomorphism in the derived category, which is the tag, is
`...SmallSite.smoothPresentationPairDerivedPlusIso` of
`SmallSite/SmoothPresentationDerived07LH.lean`.

The proof is the source's.  [Stacks, Tag 07LG] says that `M ⊗^∧_D Ω^*_D` computes
`RΓ(Cris(X/S), ℱ)`, and `Crystalline.quasiIso_baseChangeHom_smoothPresentation` says that the
base change `M ⊗^∧_D Ω^*_D → M' ⊗^∧_{D'} Ω^*_{D'}` along a divided power map `D → D'` is a
quasi-isomorphism, as soon as two facts about the crystal hold, both of which are proved here:

* the base changes of `M` along the two coprojections `σ, δ : D → D(1)` are identified by a
  horizontal isomorphism, the stratification of the crystal: both are identified with
  `M(1) = lim_e Γ(T(1)_e, ℱ)` by the linear extensions of the two transition maps
  `M(0) → M(1)`, bijective because `ℱ` is a crystal, and horizontal for the base-change connection
  on `M(1)` because the transition maps are;
* the base change along every coprojection `D → D(b)` is a quasi-isomorphism: it is the row
  coprojection of the double complex of [Stacks, Tag 07LG], a quasi-isomorphism by
  [Stacks, Lemma 60.21.2, Tag 07LD], read through the same identification of the base change with
  `M(b)`.

Everything is built on the side of `Crystalline.FormsData`: the linear extensions are constructed
there (`Crystalline.FormsData.ConnModule.baseChangeLift`), and only the facts that do not mention
the base-changed modules are transported from the cosimplicial side.

## Main definitions

* `...SmallSite.crystalPairConnModule` — the pair `(M, ∇)` of a crystal as a module with
  integrable connection over `D`.
* `...SmallSite.crystalStratification` — its stratification `σ^* M ≅ δ^* M`.
* `...SmallSite.smoothPresentationPair` — the pair `(M', ∇')` over `D'`: the base change of
  `(M, ∇)` along a divided power map `D → D'`.

## Main results

* `...SmallSite.quasiIso_crystalPair_baseChangeHom_coprojection` — the base change along every
  coprojection `D → D(b)` is a quasi-isomorphism.
* `...SmallSite.smoothPresentationPair_computesCohomology` — the cohomology groups of
  `M' ⊗^∧_{D'} Ω^*_{D'}` are those of `Cris(X/S)`; [Stacks, Tag 07LH] itself, in the derived
  category, is `...SmallSite.smoothPresentationPairDerivedPlusIso` of
  `SmallSite/SmoothPresentationDerived07LH.lean`.

## References

* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers Simplicial
open scoped TensorProduct

universe u

namespace Crystalline

section Canonical

variable (s : AffineCrystallineSituation.{u, u}) {ι₀ : Type u}
  {f₀ : MvPolynomial ι₀ s.A →ₐ[s.A] s.C} (hf₀ : Function.Surjective f₀)

include hf₀

attribute [local instance] tensorPowerEnvelopeAlgebraInstance

/-- **The comparison of forms of a completed reindexing morphism is the transition map of the
forms of the cosimplicial envelope.** -/
theorem presTowerReindexHom_psi {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ)
    (x : (presTowerFormsData s f₀ m.len).Om a) :
    (presTowerReindexHom s f₀ hf₀ φ).psi a x =
      (envelopeDPAlgebra s (f₀)).formsMapCompleted s.p φ a x :=
  FormsData.Hom.ofCompletion_psi_eq s.p s.A _ _ _ _ _ _
    (envelopeReindexAlgHomOfSimplex s _ φ) (envelopeReindex s _ φ).1.isDPMorphism
    (completedReindex_of s _ φ) a x

end Canonical

namespace CompletedConnection

variable {p : ℕ} {D : Type u} [CommRing D] {Om : Type u} [AddCommGroup Om] [Module D Om]
  {d : D → Om} {N₁ N₂ N : Type u} [AddCommGroup N₁] [Module D N₁] [AddCommGroup N₂]
  [Module D N₂] [AddCommGroup N] [Module D N]

/-- **Horizontal maps into a common module compose through the inverse of one of them**: if
`e₁ : N₁ → N` and the equivalence `e₂ : N₂ ≃ N` are horizontal, so is `e₂⁻¹ ∘ e₁`. -/
theorem horizontal_symm_comp (nabla₁ : CompletedConnection p D Om d N₁)
    (nabla₂ : CompletedConnection p D Om d N₂) (nabla : CompletedConnection p D Om d N)
    (e₁ : N₁ →ₗ[D] N) (e₂ : N₂ ≃ₗ[D] N)
    (h₁ : ∀ x, nabla (e₁ x) = AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map e₁ (LinearMap.id (R := D) (M := Om))) (nabla₁ x))
    (h₂ : ∀ y, nabla (e₂ y) = AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map e₂.toLinearMap (LinearMap.id (R := D) (M := Om))) (nabla₂ y))
    (x : N₁) :
    nabla₂ (e₂.symm (e₁ x)) = AdicCompletion.map (pAdicIdeal (A := D) p)
      (TensorProduct.map (e₂.symm.toLinearMap ∘ₗ e₁) (LinearMap.id (R := D) (M := Om)))
        (nabla₁ x) := by
  have h := congrArg (AdicCompletion.map (pAdicIdeal (A := D) p)
    (TensorProduct.map e₂.symm.toLinearMap (LinearMap.id (R := D) (M := Om))))
    (h₂ (e₂.symm (e₁ x)))
  rw [LinearEquiv.apply_symm_apply, h₁, AdicCompletion.map_comp_apply,
    AdicCompletion.map_comp_apply, ← TensorProduct.map_comp, ← TensorProduct.map_comp] at h
  have hid : TensorProduct.map (e₂.symm.toLinearMap ∘ₗ e₂.toLinearMap)
      (LinearMap.id (R := D) (M := Om) ∘ₗ LinearMap.id) = LinearMap.id := by
    rw [LinearEquiv.symm_comp, LinearMap.id_comp, TensorProduct.map_id]
  rw [hid, AdicCompletion.map_id, LinearMap.id_apply, LinearMap.id_comp] at h
  exact h.symm

end CompletedConnection

namespace FormsData.ConnModule

variable {p : ℕ} {R R' : FormsData.{u} p} (g : FormsData.Hom R R') (M : ConnModule R)
  {N : Type u} [AddCommGroup N] [Module R'.ring N] [IsAdicComplete (pAdicIdeal (A := R'.ring) p) N]

/-- **The linear extension `(D' ⊗_D M)^∧ → N` of a semilinear map `μ : M → N`** into a
`p`-adically complete `D'`-module, `b ⊗ m ↦ b • μ m`. -/
def baseChangeLift (mu : M.carrier →ₛₗ[g.toRingHom] N) : (M.baseChange g).carrier →ₗ[R'.ring] N :=
  letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  completedTensorLiftₛₗ p mu

/-- The linear extension of `μ` sends `1 ⊗ m` to `μ m`. -/
theorem baseChangeLift_inclusion (mu : M.carrier →ₛₗ[g.toRingHom] N) (m : M.carrier) :
    letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
    baseChangeLift g M mu (CompletedConnection.baseChangeInclusion p R.ring R'.ring M.carrier m) =
      mu m := by
  let : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  change completedTensorLiftₛₗ p mu (AdicCompletion.of _ _ _) = _
  rw [completedTensorLiftₛₗ_of, tensorLiftₛₗ_tmul, one_smul]

/-- **The linear extension of a horizontal semilinear map is horizontal** for the base-changed
connection. -/
theorem baseChangeLift_horizontal (mu : M.carrier →ₛₗ[g.toRingHom] N)
    (nablaN : CompletedConnection p R'.ring (R'.Om 1) R'.diff N)
    (hmu : ∀ m, nablaN (mu m) = (letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
      adicCompletionMapₛₗ (TensorProduct.map mu (g.psi 1))
        (CompletedConnection.pAdicIdeal_map_le p R.ring R'.ring) (M.nabla m)))
    (x : (M.baseChange g).carrier) :
    nablaN (baseChangeLift g M mu x) = AdicCompletion.map (pAdicIdeal (A := R'.ring) p)
      (TensorProduct.map (baseChangeLift g M mu) (LinearMap.id (R := R'.ring) (M := R'.Om 1)))
      ((M.baseChange g).nabla x) := by
  let : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  exact horizontal_of_baseChangeInclusion p R.ring R'.ring M.carrier N (R.Om 1) (R'.Om 1) R'.diff
    (g.psi 1) M.nabla nablaN R'.diff_add R'.diff_mul g.psi_diff (baseChangeLift g M mu) mu
    (baseChangeLift_inclusion g M mu) hmu x

/-- **The linear extension of `μ` is bijective as soon as its reductions modulo `pⁿ` are, for
`n` large.** -/
theorem bijective_baseChangeLift (mu : M.carrier →ₛₗ[g.toRingHom] N) (N₀ : ℕ)
    (hlev : ∀ e : ℕ, letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
      Function.Bijective (adicQuotientMap (tensorLiftₛₗ mu) (pAdicIdeal_map_id_le p) (N₀ + e))) :
    Function.Bijective (baseChangeLift g M mu) :=
  let : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  bijective_completedTensorLiftₛₗ p mu N₀ hlev

/-- **Two horizontal identifications of base changes of `M` with one module give a horizontal
map between the base changes**: `L₂⁻¹ ∘ L₁`. -/
def homOfLifts (g₂ : FormsData.Hom R R')
    (nablaN : CompletedConnection p R'.ring (R'.Om 1) R'.diff N)
    (L₁ : (M.baseChange g).carrier →ₗ[R'.ring] N) (L₂ : (M.baseChange g₂).carrier →ₗ[R'.ring] N)
    (h₂ : Function.Bijective L₂)
    (hL₁ : ∀ x, nablaN (L₁ x) = AdicCompletion.map (pAdicIdeal (A := R'.ring) p)
      (TensorProduct.map L₁ (LinearMap.id (R := R'.ring) (M := R'.Om 1)))
          ((M.baseChange g).nabla x))
    (hL₂ : ∀ x, nablaN (L₂ x) = AdicCompletion.map (pAdicIdeal (A := R'.ring) p)
      (TensorProduct.map L₂ (LinearMap.id (R := R'.ring) (M := R'.Om 1)))
        ((M.baseChange g₂).nabla x)) :
    Hom (M.baseChange g) (M.baseChange g₂) where
  toLinearMap := (LinearEquiv.ofBijective L₂ h₂).symm.toLinearMap ∘ₗ L₁
  horizontal x := CompletedConnection.horizontal_symm_comp _ _ nablaN L₁
    (LinearEquiv.ofBijective L₂ h₂) hL₁ hL₂ x

omit [IsAdicComplete (pAdicIdeal (A := R'.ring) p) N] in
/-- `L₂⁻¹ ∘ L₁` is bijective when `L₁` is. -/
theorem homOfLifts_bijective (g₂ : FormsData.Hom R R')
    (nablaN : CompletedConnection p R'.ring (R'.Om 1) R'.diff N)
    (L₁ : (M.baseChange g).carrier →ₗ[R'.ring] N) (L₂ : (M.baseChange g₂).carrier →ₗ[R'.ring] N)
    (h₂ : Function.Bijective L₂) (hL₁) (hL₂) (h₁ : Function.Bijective L₁) :
    Function.Bijective (homOfLifts g M g₂ nablaN L₁ L₂ h₂ hL₁ hL₂).toLinearMap :=
  (LinearEquiv.ofBijective L₂ h₂).symm.bijective.comp h₁

omit [IsAdicComplete (pAdicIdeal (A := R'.ring) p) N] in
/-- **A base change identified with a module whose de Rham complex receives a quasi-isomorphism
from that of `M` is a quasi-isomorphism.**  Let `L : (D' ⊗_D M)^∧ → N` be a horizontal bijection
extending `μ : M → N`, and `row : M ⊗^∧_D Ω^*_D → N ⊗^∧_{D'} Ω^*_{D'}` the map `m ⊗ ω ↦ μ m ⊗ ψ ω`.
If `row` is a quasi-isomorphism, so is the base change map. -/
theorem quasiIso_baseChangeHom_of_lift (nablaN : CompletedConnection p R'.ring (R'.Om 1) R'.diff N)
    (hsqN : CompletedDeRham.IsSquareZero p R'.ring R'.Om R'.wedge R'.deRham N nablaN
      R'.isGradedLeibniz)
    (L : (M.baseChange g).carrier →ₗ[R'.ring] N) (hL : Function.Bijective L)
    (hLh : ∀ x, nablaN (L x) = AdicCompletion.map (pAdicIdeal (A := R'.ring) p)
      (TensorProduct.map L (LinearMap.id (R := R'.ring) (M := R'.Om 1))) ((M.baseChange g).nabla x))
    (mu : M.carrier →ₛₗ[g.toRingHom] N)
    (hLmu : ∀ m, (letI : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
      L (CompletedConnection.baseChangeInclusion p R.ring R'.ring M.carrier m)) = mu m)
    (row : M.complex ⟶ CompletedDeRham.complex p R'.ring R'.Om R'.wedge R'.deRham N nablaN
      R'.isGradedLeibniz hsqN)
    (hrow : ∀ (i : ℕ) (m : M.carrier) (ω : R.Om i),
      (row.f i).hom (toCompletedTensor p R.ring (R.Om i) M.carrier (m ⊗ₜ ω)) =
        toCompletedTensor p R'.ring (R'.Om i) N (mu m ⊗ₜ g.psi i ω))
    [QuasiIso row] : QuasiIso (M.baseChangeHom g) := by
  let : Algebra R.ring R'.ring := g.toRingHom.toAlgebra
  let T : (M.baseChange g).complex ⟶ CompletedDeRham.complex p R'.ring R'.Om R'.wedge R'.deRham N
      nablaN R'.isGradedLeibniz hsqN :=
    CompletedDeRham.horizontalComplexHom p R'.ring (M.baseChange g).carrier N R'.Om L
    R'.wedge R'.deRham (M.baseChange g).nabla nablaN R'.isGradedLeibniz hLh
    (R'.isSquareZero _ (M.baseChange g).isCurvatureZero) hsqN
  have : IsIso T := CompletedDeRham.isIso_horizontalComplexHom p R'.ring
    (M.baseChange g).carrier N R'.Om (LinearEquiv.ofBijective L hL) R'.wedge R'.deRham
    (M.baseChange g).nabla nablaN R'.isGradedLeibniz hLh _ hsqN
  have hT : M.baseChangeHom g ≫ T = row := by
    refine HomologicalComplex.hom_ext _ _ fun i ↦ AddCommGrpCat.ext fun z ↦ ?_
    have h := completedTensor_addMonoidHom_ext p
      (f := (CompletedDeRham.horizontalTerm p R'.ring (M.baseChange g).carrier N R'.Om L i).comp
        (CompletedDeRham.baseChangeTerm p R.ring R'.ring M.carrier R.Om R'.Om g.psi i))
      (g := (row.f i).hom) fun m ω ↦ by
        refine (congrArg (CompletedDeRham.horizontalTerm p R'.ring (M.baseChange g).carrier N R'.Om
          L i) (CompletedDeRham.baseChangeTerm_of_tmul p R.ring R'.ring M.carrier R.Om R'.Om g.psi
            i m ω)).trans ?_
        refine (CompletedDeRham.horizontalTerm_of_tmul p R'.ring (M.baseChange g).carrier N R'.Om
          L i _ _).trans ?_
        rw [hLmu]
        exact (hrow i m ω).symm
    exact DFunLike.congr_fun h z
  have : QuasiIso (M.baseChangeHom g ≫ T) := by rw [hT]; infer_instance
  exact quasiIso_of_comp_right (M.baseChangeHom g) T

end FormsData.ConnModule

namespace CosimplicialCompletedModule

section Stratification

variable (s : AffineCrystallineSituation.{u, u}) {ι₀ : Type u}
  {f₀ : MvPolynomial ι₀ s.A →ₐ[s.A] s.C} (hf₀ : Function.Surjective f₀)

include hf₀

attribute [local instance] tensorPowerEnvelopeAlgebraInstance

variable
  (V : CosimplicialCompletedModule.{u, u, u} (envelopeDPAlgebra s (f₀)) s.p)
  (nabla : CompletedConnection s.p
    ((envelopeDPAlgebra s (f₀)).completedRing s.p 0)
    ((envelopeDPAlgebra s (f₀)).forms s.p 1 0)
    ((envelopeDPAlgebra s (f₀)).differential s.p 0) (V.carrier 0))
  (hcomplete : IsPAdicallyComplete s.p
    ((envelopeDPAlgebra s (f₀)).completedRing s.p 0) (V.carrier 0))
  (hint : CompletedDeRham.HasIntegrableConnection s.p
    ((envelopeDPAlgebra s (f₀)).completedRing s.p 0)
    (fun a => (envelopeDPAlgebra s (f₀)).forms s.p a 0)
    ((envelopeDPAlgebra s (f₀)).wedge s.p 0)
    ((envelopeDPAlgebra s (f₀)).deRham s.p 0) (V.carrier 0) nabla
    ((envelopeDPAlgebra s (f₀)).isGradedLeibniz s.p 0))

/-- **The degree zero of a cosimplicial module with an integrable connection, as a module with
connection over `D(0)`** with its completed forms. -/
abbrev degreeZeroConnModule : FormsData.ConnModule (presTowerFormsData s f₀ 0) where
  carrier := V.carrier 0
  addCommGroup := V.addCommGroup 0
  module := V.module 0
  isPAdicallyComplete := hcomplete
  nabla := nabla
  isCurvatureZero := hint

/-- `M(b)` as a module over the ring of `Crystalline.presTowerFormsData`, which is the completed
ring of the degree `b`, for the presentation `f₀`. -/
instance canonicalFormsDataModule (b : ℕ) :
    Module (presTowerFormsData s f₀ b).ring (V.carrier b) :=
  V.module b

/-- **The linear extension `(D(b) ⊗_{D(0), φ} M(0))^∧ → M(b)` of a transition map**
`M(φ) : M(0) → M(b)`, for `φ : ⦋0⦌ ⟶ ⦋b⦌`. -/
def mapLift {b : ℕ} (φ : ⦋0⦌ ⟶ ⦋b⦌)
    [IsAdicComplete (pAdicIdeal (A := (presTowerFormsData s f₀ b).ring) s.p) (V.carrier b)] :
    ((degreeZeroConnModule s V nabla hcomplete hint).baseChange
      (presTowerReindexHom s f₀ hf₀ φ)).carrier →ₗ[(presTowerFormsData s f₀ b).ring] V.carrier b :=
  FormsData.ConnModule.baseChangeLift (presTowerReindexHom s f₀ hf₀ φ)
    (degreeZeroConnModule s V nabla hcomplete hint) (V.map φ)

/-- **The linear extension of a horizontal transition map is horizontal.** -/
theorem mapLift_horizontal {b : ℕ} (φ : ⦋0⦌ ⟶ ⦋b⦌)
    [IsAdicComplete (pAdicIdeal (A := (presTowerFormsData s f₀ b).ring) s.p) (V.carrier b)]
    (nablab : CompletedConnection s.p
        ((envelopeDPAlgebra s (f₀)).completedRing s.p b)
        ((envelopeDPAlgebra s (f₀)).forms s.p 1 b)
      ((envelopeDPAlgebra s (f₀)).differential s.p b) (V.carrier b))
    (hmu : ∀ m, nablab (V.map φ m) = V.tensorMap φ 1 (nabla m))
    (x : ((degreeZeroConnModule s V nabla hcomplete hint).baseChange
      (presTowerReindexHom s f₀ hf₀ φ)).carrier) :
    nablab (mapLift s hf₀ V nabla hcomplete hint φ x) = AdicCompletion.map
      (pAdicIdeal (A := (presTowerFormsData s f₀ b).ring) s.p)
      (TensorProduct.map (mapLift s hf₀ V nabla hcomplete hint φ)
        (LinearMap.id (R := (presTowerFormsData s f₀ b).ring) (M := (presTowerFormsData s f₀ b).Om
            1)))
      (((degreeZeroConnModule s V nabla hcomplete hint).baseChange
        (presTowerReindexHom s f₀ hf₀ φ)).nabla x) := by
  refine FormsData.ConnModule.baseChangeLift_horizontal (presTowerReindexHom s f₀ hf₀ φ)
    (degreeZeroConnModule s V nabla hcomplete hint) (V.map φ) nablab (fun m ↦ (hmu m).trans ?_) x
  have hψ : ((presTowerReindexHom s f₀ hf₀ φ).psi 1 :
      (envelopeDPAlgebra s (f₀)).forms s.p 1 0
          →ₛₗ[(envelopeDPAlgebra s (f₀)).completedRingMap s.p φ]
          (envelopeDPAlgebra s (f₀)).forms s.p 1 b) =
      (envelopeDPAlgebra s (f₀)).formsMapCompleted s.p φ 1 :=
    LinearMap.ext fun ω ↦ presTowerReindexHom_psi s hf₀ φ 1 ω
  rw [hψ]
  rfl

variable
  (beta : ∀ b : ℕ, letI := (envelopeDPAlgebra s (f₀)).coprojectionAlgebra s.p b
    CompletedConnection.baseChangeCarrier s.p
        ((envelopeDPAlgebra s (f₀)).completedRing s.p 0)
      ((envelopeDPAlgebra s (f₀)).completedRing s.p b) (V.carrier 0)
          ≃ₗ[(envelopeDPAlgebra s (f₀)).completedRing s.p b] V.carrier b)
  (hbeta : ∀ (b : ℕ) (x : (envelopeDPAlgebra s (f₀)).completedRing s.p b)
      (m : V.carrier 0),
    letI := (envelopeDPAlgebra s (f₀)).coprojectionAlgebra s.p b
    beta b (AdicCompletion.of
        (pAdicIdeal (A := (envelopeDPAlgebra s (f₀)).completedRing s.p b) s.p)
        ((envelopeDPAlgebra s (f₀)).completedRing s.p b
            ⊗[(envelopeDPAlgebra s (f₀)).completedRing s.p 0] V.carrier 0)
        (x ⊗ₜ[(envelopeDPAlgebra s (f₀)).completedRing s.p 0] m)) =
      x • V.map (CosimplicialDPAlgebra.coprojection b) m)
  (hδ : ∀ m, V.baseChangeConnection nabla beta 1 (V.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) m) =
    V.tensorMap (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1) 1 (nabla m))
  [IsAdicComplete (pAdicIdeal (A := (presTowerFormsData s f₀ 1).ring) s.p) (V.carrier 1)]

include hbeta hδ in
/-- **The stratification** on the base changes of `M(0)` along the two coprojections
`σ, δ : D(0) → D(1)`: the composite `σ^* M → M(1) ≃ δ^* M` of the linear extensions of the two
transition maps `M(0) → M(1)`, horizontal because both transition maps are, for the
base-change connection on `M(1)`. -/
def stratification
    (hbij : Function.Bijective
      (mapLift s hf₀ V nabla hcomplete hint (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1))) :
    FormsData.ConnModule.Hom
      ((degreeZeroConnModule s V nabla hcomplete hint).baseChange
        (presTowerReindexHom s f₀ hf₀ (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)))
      ((degreeZeroConnModule s V nabla hcomplete hint).baseChange
        (presTowerReindexHom s f₀ hf₀ (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1))) :=
  FormsData.ConnModule.homOfLifts _ _ _ (V.baseChangeConnection nabla beta 1)
    (mapLift s hf₀ V nabla hcomplete hint (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0))
    (mapLift s hf₀ V nabla hcomplete hint (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)) hbij
    (mapLift_horizontal s hf₀ V nabla hcomplete hint _ _
      (V.baseChangeConnection_map_coprojection nabla beta hbeta 1))
    (mapLift_horizontal s hf₀ V nabla hcomplete hint _ _ hδ)

/-- The stratification is bijective. -/
theorem stratification_bijective
    (hbijσ : Function.Bijective
      (mapLift s hf₀ V nabla hcomplete hint (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)))
    (hbij : Function.Bijective
      (mapLift s hf₀ V nabla hcomplete hint (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1))) :
    Function.Bijective
      (stratification s hf₀ V nabla hcomplete hint beta hbeta hδ hbij).toLinearMap :=
  FormsData.ConnModule.homOfLifts_bijective _ _ _ _ _ _ _ _ _ hbijσ

include hbeta in
/-- **The de Rham complex of `M(0)` is the row zero of the double complex of the base-change
connections**: the connection of the degree zero is `∇` itself. -/
def degreeZeroComplexIso :
    (degreeZeroConnModule s V nabla hcomplete hint).complex ≅
      (V.baseChangePair nabla beta hbeta hδ hint).degreeDeRhamComplex 0 :=
  HomologicalComplex.Hom.isoOfComponents (fun _ ↦ Iso.refl _) fun i j hij ↦ by
    change i + 1 = j at hij
    subst hij
    have h : V.baseChangeConnection nabla beta 0 = nabla :=
      CompletedConnection.ext fun y ↦ V.baseChangeConnection_zero nabla beta hbeta y
    have e1 : (degreeZeroConnModule s V nabla hcomplete hint).complex.d i (i + 1) =
        AddCommGrpCat.ofHom
            (CompletedDeRham.differential s.p
            ((envelopeDPAlgebra s (f₀)).completedRing s.p 0)
          (fun a ↦ (envelopeDPAlgebra s (f₀)).forms s.p a 0)
              ((envelopeDPAlgebra s (f₀)).wedge s.p 0)
              ((envelopeDPAlgebra s (f₀)).deRham s.p 0) (V.carrier 0)
          nabla ((envelopeDPAlgebra s (f₀)).isGradedLeibniz s.p 0) i) :=
      CompletedDeRham.complex_d _ _ _ _ _ _ _ _ _ i
    rw [CosimplicialCompletedPair.degreeDeRhamComplex_d, e1]
    refine AddCommGrpCat.ext fun x ↦ ?_
    change CompletedDeRham.differential s.p
        ((envelopeDPAlgebra s (f₀)).completedRing s.p 0)
        (fun a ↦ (envelopeDPAlgebra s (f₀)).forms s.p a 0)
            ((envelopeDPAlgebra s (f₀)).wedge s.p 0)
            ((envelopeDPAlgebra s (f₀)).deRham s.p 0) (V.carrier 0)
        (V.baseChangeConnection nabla beta 0)
            ((envelopeDPAlgebra s (f₀)).isGradedLeibniz s.p 0) i x =
      CompletedDeRham.differential s.p
          ((envelopeDPAlgebra s (f₀)).completedRing s.p 0)
        (fun a ↦ (envelopeDPAlgebra s (f₀)).forms s.p a 0)
            ((envelopeDPAlgebra s (f₀)).wedge s.p 0)
            ((envelopeDPAlgebra s (f₀)).deRham s.p 0) (V.carrier 0)
        nabla ((envelopeDPAlgebra s (f₀)).isGradedLeibniz s.p 0) i x
    rw [h]

omit [IsAdicComplete (pAdicIdeal (A := (presTowerFormsData s f₀ 1).ring) s.p) (V.carrier 1)] in
include hbeta in
/-- **The base change along the coprojection `σ_b : D(0) → D(b)` is a quasi-isomorphism** as soon
as the coprojection of the double complex `M(0) ⊗^∧ Ω^*_{D(0)} → M(b) ⊗^∧ Ω^*_{D(b)}` is one and
the linear extension of `M(σ_b)` identifies the base change with `M(b)`. -/
theorem quasiIso_baseChangeHom_coprojection
    (b : ℕ) [IsAdicComplete (pAdicIdeal (A := (presTowerFormsData s f₀ b).ring) s.p) (V.carrier b)]
    (hbij : Function.Bijective
      (mapLift s hf₀ V nabla hcomplete hint (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0)))
    [hq : QuasiIso ((V.baseChangePair nabla beta hbeta hδ hint).rowFromZeroHom b)] :
    QuasiIso ((degreeZeroConnModule s V nabla hcomplete hint).baseChangeHom
      (presTowerReindexHom s f₀ hf₀ (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0))) := by
  have hsq := (V.baseChangePair nabla beta hbeta hδ hint).isSquareZero b
  have hh := mapLift_horizontal s hf₀ V nabla hcomplete hint (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) _
      (V.baseChangeConnection_map_coprojection nabla beta hbeta b)
  have hinc := FormsData.ConnModule.baseChangeLift_inclusion
    (presTowerReindexHom s f₀ hf₀ (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0))
    (degreeZeroConnModule s V nabla hcomplete hint) (V.map (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0))
  have hq' : QuasiIso ((degreeZeroComplexIso s V nabla hcomplete hint beta hbeta hδ).hom ≫
      (V.baseChangePair nabla beta hbeta hδ hint).rowFromZeroHom b) := inferInstance
  have key := FormsData.ConnModule.quasiIso_baseChangeHom_of_lift
    (presTowerReindexHom s f₀ hf₀ (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0))
    (degreeZeroConnModule s V nabla hcomplete hint)
    (V.baseChangeConnection nabla beta b) hsq _ hbij hh _ hinc
    ((degreeZeroComplexIso s V nabla hcomplete hint beta hbeta hδ).hom ≫
      (V.baseChangePair nabla beta hbeta hδ hint).rowFromZeroHom b)
  exact @key (fun i m ω ↦ (V.tensorMap_of_tmul _ i m ω).trans
    (congrArg (fun z ↦ toCompletedTensor s.p _ _ _ (V.map (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) m ⊗ₜ z))
      (presTowerReindexHom_psi s hf₀ _ i ω).symm)) hq'

end Stratification

end CosimplicialCompletedModule

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open AlgebraicGeometry CohomologyRestriction

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) [WholeSpacePresentation S hp] (Fc : QuasiCoherentCrystal S)

/-- `M(b)` is a module over the ring of `Crystalline.presTowerFormsData`, the completed ring of
the degree `b`. -/
instance crystalCanonicalFormsDataModule (b : ℕ) :
    Module (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) b).ring
      ((wholeSpaceCosimplicialModule hp Fc).carrier b) :=
  (wholeSpaceCosimplicialModule hp Fc).module b

/-- `M(b)` is `p`-adically complete over the ring of `Crystalline.presTowerFormsData`. -/
instance crystalCanonicalFormsDataComplete (b : ℕ) :
    IsAdicComplete
      (pAdicIdeal (A := (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp)
          b).ring)
        (affineSituation S hp).p)
      ((wholeSpaceCosimplicialModule hp Fc).carrier b) :=
  wholeSpaceSectionsIsAdicComplete hp Fc ⦋b⦌

/-- **The pair `(M, ∇)` of a crystal of [Stacks, Lemma 60.17.3, Tag 07JG] as a module with
integrable connection over `D`** with its completed forms: `M = lim_e Γ(T_e, ℱ)` with the
connection `...SmallSite.crystalPairFormsConnection`. -/
abbrev crystalPairConnModule :
    FormsData.ConnModule (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp)
        0) :=
  CosimplicialCompletedModule.degreeZeroConnModule (affineSituation S hp)
    (wholeSpaceCosimplicialModule hp Fc) (crystalPairFormsConnection hp Fc)
    (wholeSpaceSectionsIsAdicComplete hp Fc ⦋0⦌)
    (hasIntegrableConnection_crystalPairFormsConnection hp Fc)

include hp Fc in
/-- **The linear extensions of the transition maps of `M(•)` are bijective**: `ℱ` is a crystal,
so modulo `(p)^{N+e}` they are the base changes of sections over the levels, bijective by
`...SmallSite.bijective_levelAmbientBaseChange`. -/
theorem bijective_crystalMapLift {b : ℕ} (φ : ⦋0⦌ ⟶ ⦋b⦌) :
    Function.Bijective (CosimplicialCompletedModule.mapLift (affineSituation S hp)
    (wholeSpacePresentation_surjective S hp)
      (wholeSpaceCosimplicialModule hp Fc) (crystalPairFormsConnection hp Fc)
      (wholeSpaceSectionsIsAdicComplete hp Fc ⦋0⦌)
      (hasIntegrableConnection_crystalPairFormsConnection hp Fc) φ) := by
  have hM : IsSurjectiveComparison Fc.obj.val :=
    isSurjectiveComparison_of_isSheafCrystal Fc.property.2
  refine FormsData.ConnModule.bijective_baseChangeLift _ _ _
    (_root_.Crystalline.uniformLevel (affineSituation S hp)) fun e ↦ ?_
  let := (presTowerReindexHom (affineSituation S hp) (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp) φ).toRingHom.toAlgebra
  refine bijective_adicQuotientMap_tensorLiftₛₗ (affineSituation S hp).p _
    (A := (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) ⦋0⦌.len).ring)
    (B := (presTowerFormsData (affineSituation S hp) (wholeSpacePresentation S hp) ⦋b⦌.len).ring)
    (M := (crystalPairConnModule hp Fc).carrier)
    (M' := (wholeSpaceCosimplicialModule hp Fc).carrier b)
    ((wholeSpaceCosimplicialModule hp Fc).map φ)
    (πA := levelAmbientScalars hp 0 e) (πB := levelRingAlongReduce hp φ e)
    (ρ := levelSectionsTopReduce hp Fc 0 e) (ρ' := levelSectionsTopReduce hp Fc b e)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ (levelAmbientBaseChange hp Fc φ e) ?_ ?_ ?_
  · exact levelAmbientScalars_smul_levelRingAlongReduce hp φ e
  · exact levelSectionsTopReduce_smul hp Fc e 0
  · exact surjective_levelSectionsScalars hp _ e
  · exact surjective_levelSectionsScalars hp _ e
  · exact surjective_levelSectionsTopReduce hp e hM 0
  · exact fun b hb ↦ (levelSectionsScalars_eq_zero_iff hp _ e b).1 hb
  · exact fun y hy ↦ (levelSectionsTopReduce_eq_zero_iff hp e hM 0 y).1 hy
  · exact bijective_levelAmbientBaseChange hp Fc φ e
  · exact fun b x ↦ levelAmbientBaseChange_tmul hp Fc φ e b x
  · exact fun y ↦ levelSectionsTopReduce_eq_zero_iff hp e hM b y

/-- **The stratification of the pair of a crystal**: the horizontal isomorphism `σ^* M ≅ δ^* M`
between the base changes of `(M, ∇)` along the two coprojections `D → D(1)`. -/
def crystalStratification :
    FormsData.ConnModule.Hom
      ((crystalPairConnModule hp Fc).baseChange
        (presTowerReindexHom (affineSituation S hp) (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp) (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)))
      ((crystalPairConnModule hp Fc).baseChange
        (presTowerReindexHom (affineSituation S hp) (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp) (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1))) :=
  CosimplicialCompletedModule.stratification (affineSituation S hp)
    (wholeSpacePresentation_surjective S hp)
    (wholeSpaceCosimplicialModule hp Fc) (crystalPairFormsConnection hp Fc)
    (wholeSpaceSectionsIsAdicComplete hp Fc ⦋0⦌)
    (hasIntegrableConnection_crystalPairFormsConnection hp Fc) (crystalCoprojectionBeta hp Fc)
    (crystalCoprojectionBeta_of_tmul hp Fc) (crystalPairFormsConnection_horizontal_delta hp Fc)
    (bijective_crystalMapLift hp Fc _)

/-- The stratification of the pair of a crystal is bijective. -/
theorem crystalStratification_bijective :
    Function.Bijective (crystalStratification hp Fc).toLinearMap :=
  CosimplicialCompletedModule.stratification_bijective (affineSituation S hp)
    (wholeSpacePresentation_surjective S hp)
    (wholeSpaceCosimplicialModule hp Fc) (crystalPairFormsConnection hp Fc)
    (wholeSpaceSectionsIsAdicComplete hp Fc ⦋0⦌)
    (hasIntegrableConnection_crystalPairFormsConnection hp Fc) (crystalCoprojectionBeta hp Fc)
    (crystalCoprojectionBeta_of_tmul hp Fc) (crystalPairFormsConnection_horizontal_delta hp Fc)
    (bijective_crystalMapLift hp Fc _) (bijective_crystalMapLift hp Fc _)

/-- **The base change of the pair of a crystal along every coprojection `D → D(b)` is a
quasi-isomorphism of completed de Rham complexes.** -/
theorem quasiIso_crystalPair_baseChangeHom_coprojection (b : ℕ) :
    QuasiIso ((crystalPairConnModule hp Fc).baseChangeHom
      (presTowerReindexHom (affineSituation S hp) (wholeSpacePresentation S hp)
          (wholeSpacePresentation_surjective S hp) (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0))) :=
  @CosimplicialCompletedModule.quasiIso_baseChangeHom_coprojection (affineSituation S hp)
    _ _ (wholeSpacePresentation_surjective S hp)
    (wholeSpaceCosimplicialModule hp Fc) (crystalPairFormsConnection hp Fc)
    (wholeSpaceSectionsIsAdicComplete hp Fc ⦋0⦌)
    (hasIntegrableConnection_crystalPairFormsConnection hp Fc) (crystalCoprojectionBeta hp Fc)
    (crystalCoprojectionBeta_of_tmul hp Fc) (crystalPairFormsConnection_horizontal_delta hp Fc)
    b _ (bijective_crystalMapLift hp Fc _)
    (quasiIso_crystalCosimplicialPair_rowFromZeroHom hp Fc b)

section SmoothPresentation

/-- The tautological presentation `A[x_c : c ∈ C] → C` has a variable, `x_0`. -/
instance nonempty_wholeSpaceIndex_instWholeSpacePresentation :
    Nonempty (@wholeSpaceIndex S hp (instWholeSpacePresentation S hp)) :=
  ⟨(0 : Γ(S.X, ⊤))⟩

attribute [local instance] tensorPowerEnvelopeAlgebraInstance presentationEnvelopeAlgebraInst

variable {P' : Type u} [CommRing P'] [Algebra (affineSituation S hp).A P']
  (f' : P' →ₐ[(affineSituation S hp).A] (affineSituation S hp).C) (hf' : Function.Surjective f')
  (a : AdicCompletion (pAdicIdeal (A := (tensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp) 0).object) (affineSituation S hp).p)
      (tensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp) 0).object →ₐ[(affineSituation S hp).A]
    AdicCompletion (pAdicIdeal (A := (presentationEnvelope (affineSituation S hp) f').object)
        (affineSituation S hp).p) (presentationEnvelope (affineSituation S hp) f').object)
  (ha : IsDPMorphism (completionDividedPowers (affineSituation S hp).p
      (tensorPowerEnvelope (affineSituation S hp)
        (wholeSpacePresentation S hp) 0).object.dividedPowers
      (tensorPowerEnvelope_prime_nilpotent (affineSituation S hp) _
        (wholeSpacePresentation_surjective S hp) 0))
    (completionDividedPowers (affineSituation S hp).p
      (presentationEnvelope (affineSituation S hp) f').object.dividedPowers
      (presentationEnvelope_prime_nilpotent (affineSituation S hp) f' hf')) a.toRingHom)

/-- **The pair `(M', ∇')` over `D'` corresponding to `ℱ`** ([Stacks, Lemma 60.17.5, Tag 07L5]):
the base change `(D' ⊗_D M)^∧` of the pair `(M, ∇)` of [Stacks, Lemma 60.17.3, Tag 07JG] along a
divided power `A`-algebra map `a : D → D'`, with the base-changed connection, where `D'` is the
`p`-adic completion of the divided power envelope `D_{P', γ}(J')` of the kernel of `P' → C`.
The functor of the equivalence of [Stacks, Tag 07L5] is this base change. -/
def smoothPresentationPair :
    FormsData.ConnModule (presentationFormsData (affineSituation S hp) f') :=
  (crystalPairConnModule hp Fc).baseChange (FormsData.Hom.ofCompletion (affineSituation S hp).p
    (affineSituation S hp).A _ (presTowerPrime_nilpotent (affineSituation S hp)
        (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) 0) _
    (presentationEnvelope_prime_nilpotent (affineSituation S hp) f' hf') a ha)

/-- [Stacks, Lemma 60.21.4, Tag 07LH] for a presentation of the system some tensor power of which
surjects onto `P'` compatibly with the maps to `C` (`htower`): the form in which the lemma is
proved, `...SmallSite.smoothPresentationPair_computesCohomology` supplying `htower` when the
presentation has a variable. -/
theorem smoothPresentationPair_computesCohomologyOfTower
    [Algebra.Smooth ((affineSituation S hp).A : Type u) P']
    (htower : ∃ (n : ℕ) (q : MvPolynomial (Fin (n + 1) × wholeSpaceIndex S hp)
        (affineSituation S hp).A →ₐ[(affineSituation S hp).A] P'),
      Function.Surjective q ∧
        f'.comp q = tensorPowerPresentation (affineSituation S hp) (wholeSpacePresentation S hp) n)
    (haug : (completedEnvelopeAugmentation (affineSituation S hp) f' hf').comp a.toRingHom =
      completedEnvelopeAugmentation (affineSituation S hp)
        (tensorPowerPresentation (affineSituation S hp)
          (wholeSpacePresentation S hp) 0)
        (tensorPowerPresentation_surjective (affineSituation S hp) _
          (wholeSpacePresentation_surjective S hp) 0)) :
    ∀ j : ℕ, Nonempty (AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        ((smoothPresentationPair hp Fc f' hf' a ha).complex.homology j) ≅
      (cohomologyFunctor S j).obj (abelianSheaf Fc.obj)) := by
  have := quasiIso_baseChangeHom_smoothPresentationOfTower (affineSituation S hp)
    (wholeSpacePresentation S hp) (wholeSpacePresentation_surjective S hp)
    (crystalPairConnModule hp Fc) (quasiIso_crystalPair_baseChangeHom_coprojection hp Fc)
    (crystalStratification hp Fc) (crystalStratification_bijective hp Fc) f' hf'
    htower a ha haug
  intro j
  exact ⟨AddCommGrpCat.uliftFunctor.{u + 1, u}.mapIso
    (asIso (HomologicalComplex.homologyMap ((crystalPairConnModule hp Fc).baseChangeHom
      (FormsData.Hom.ofCompletion (affineSituation S hp).p (affineSituation S hp).A _
        (presTowerPrime_nilpotent (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) 0) _
        (presentationEnvelope_prime_nilpotent (affineSituation S hp) f' hf') a ha)) j)).symm ≪≫
    crystalPairDeRhamCohomologyIso hp Fc j⟩

/-- **The cohomology groups of `M' ⊗^∧_{D'} Ω^*_{D'}` are the crystalline cohomology groups**, the
degreewise reading of [Stacks, Lemma 60.21.4, Tag 07LH]: in the situation of
[Stacks, Proposition 60.21.3, Tag 07LG] (`X` and `S` affine, `p` nilpotent on `X`), let
`ℱ` be a crystal in quasi-coherent `𝒪_{X/S}`-modules, `A → P' → C` ring maps with `A → P'`
smooth and `P' → C` surjective with kernel `J'`, `D'` the `p`-adic completion of
`D_{P', γ}(J')` and `(M', ∇')` the pair over `D'` corresponding to `ℱ`: the base change of the
pair `(M, ∇)` of `ℱ` along any divided power `A`-algebra map `a : D → D'` compatible with the
augmentations to `C` (one exists, `Crystalline.exists_smoothPresentationMap`).  Here `D` is the
completed envelope of the presentation `A[x_i : i ∈ ι] → C` of the system, any one with a variable
(the instance `...SmallSite.WholeSpacePresentation S hp`, by default the tautological
`A[x_c : c ∈ C] → C`).  Then for every degree `j`, `H^j(M' ⊗^∧_{D'} Ω^*_{D'})` is
`H^j(Cris(X/S), ℱ)`.

[Stacks, Tag 07LH] itself, the isomorphism `M' ⊗^∧_{D'} Ω^*_{D'} ≅ RΓ(Cris(X/S), ℱ)` in the
derived category, is `...SmallSite.smoothPresentationPairDerivedPlusIso` of
`SmallSite/SmoothPresentationDerived07LH.lean`, whose cohomology recovers this statement
(`...SmallSite.smoothPresentationPair_computesCohomology_of_derived`). -/
theorem smoothPresentationPair_computesCohomology [Nonempty (wholeSpaceIndex S hp)]
    [Algebra.Smooth ((affineSituation S hp).A : Type u) P']
    (haug : (completedEnvelopeAugmentation (affineSituation S hp) f' hf').comp a.toRingHom =
      completedEnvelopeAugmentation (affineSituation S hp)
        (tensorPowerPresentation (affineSituation S hp)
          (wholeSpacePresentation S hp) 0)
        (tensorPowerPresentation_surjective (affineSituation S hp) _
          (wholeSpacePresentation_surjective S hp) 0)) :
    ∀ j : ℕ, Nonempty (AddCommGrpCat.uliftFunctor.{u + 1, u}.obj
        ((smoothPresentationPair hp Fc f' hf' a ha).complex.homology j) ≅
      (cohomologyFunctor S j).obj (abelianSheaf Fc.obj)) :=
  smoothPresentationPair_computesCohomologyOfTower hp Fc f' hf' a ha
    (exists_tensorPowerSurjectionOfTower (affineSituation S hp) (wholeSpacePresentation S hp)
      (wholeSpacePresentation_surjective S hp) P' f' hf') haug

end SmoothPresentation

end Crystalline.GlobalCrystallineSituation.SmallSite

end
