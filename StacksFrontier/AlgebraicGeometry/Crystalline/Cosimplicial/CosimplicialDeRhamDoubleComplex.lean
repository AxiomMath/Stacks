module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedConnectionBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.BigradedForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.Envelope

/-!
# The double complex `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` of [Stacks, Tag 07LG]

This file constructs the double complex

`K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}`

of [Stacks, Proposition 60.21.3, Tag 07LG], as a cochain complex of cosimplicial abelian groups:
the `b` direction is the cosimplicial direction of the cosimplicial envelope `D(*)`, and the `a`
direction is the de Rham direction of the completed divided power forms. The module half, a
cosimplicial module `M(•)` over the completed cosimplicial rings `D̂(*)` with a completed
connection in each degree, compatible with the transition maps and with square-zero de Rham
differential, is taken as data.

The de Rham differential is a morphism of cosimplicial objects, because a semilinear comparison
`μ : M →ₛₗ[σ] M'` of completed de Rham complexes which is horizontal for the connections is a
chain map.

## Main definitions

* `Crystalline.CosimplicialDPAlgebra.completedRing` and
  `Crystalline.CosimplicialDPAlgebra.completedRingMap` — the completed cosimplicial rings `D̂(*)`
  and their transition maps.
* `Crystalline.CosimplicialDPAlgebra.formsMapCompleted` — the transition map of the forms, read
  as semilinear over the *completed* scalars.
* `Crystalline.CompletedDeRham.comparisonValues` — the degree-`i` component of a semilinear
  comparison of two completed de Rham complexes.
* `Crystalline.CosimplicialCompletedModule` and `Crystalline.CosimplicialCompletedPair` — the
  module half of the double complex, as data.
* `Crystalline.CosimplicialCompletedModule.column` — the exterior degree `a` of the double
  complex as a cosimplicial abelian group, `b ↦ M(b) ⊗̂_{D(b)} Ω^a_{D(b)}`.
* `Crystalline.CosimplicialCompletedPair.degreeDifferential` — the de Rham differential of the
  double complex in one cosimplicial degree.
* `Crystalline.CosimplicialCompletedPair.doubleComplex` — the double complex `K`, as a
  `CochainComplex (CosimplicialObject AddCommGrpCat) ℕ`.

## Main results

* `Crystalline.CosimplicialCompletedModule.tensorMap_id` and
  `Crystalline.CosimplicialCompletedModule.tensorMap_comp` — the cosimplicial functoriality of
  each exterior degree.
* `Crystalline.CompletedDeRham.comparisonValues_wedgeMap` — left exterior multiplication
  commutes with a semilinear comparison.
* `Crystalline.CompletedDeRham.differential_comparisonValues` — a semilinear comparison of
  completed de Rham complexes is a chain map.
* `Crystalline.CosimplicialCompletedPair.degreeDifferential_tensorMap` — the two differentials
  of the double complex commute.
* `Crystalline.CosimplicialCompletedPair.doubleComplex_X` and
  `Crystalline.CosimplicialCompletedPair.doubleComplex_d` — the exterior degree `a` of `K` is the
  column and its differential is the de Rham differential.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Tag 07JC](https://stacks.math.columbia.edu/tag/07JC)
-/

@[expose] public noncomputable section

open CategoryTheory
open DividedPowers
open scoped TensorProduct

universe u v w uD uD' uM uM' uO uO'

namespace Crystalline

/-! ### The semilinear comparison of two completed de Rham complexes

For a semilinear map `μ : M →ₛₗ[σ] M'` and semilinear maps `ψ_i` of forms compatible with the
wedge products and the de Rham differentials, the induced comparison of completed de Rham
complexes commutes with the de Rham differentials when `μ` is horizontal for the connections.
For `μ = baseChangeInclusion` this is `Crystalline.CompletedDeRham.baseChangeTerm_comm`. -/

namespace CompletedDeRham

section SemilinearComparison

variable (p : ℕ) (D : Type uD) [CommRing D] (D' : Type uD') [CommRing D'] (σ : D →+* D')
  (M : Type uM) [AddCommGroup M] [Module D M]
  (M' : Type uM') [AddCommGroup M'] [Module D' M'] (mu : M →ₛₗ[σ] M')
  (Om : ℕ → Type uO) [∀ i, AddCommGroup (Om i)] [∀ i, Module D (Om i)]
  (Om' : ℕ → Type uO') [∀ i, AddCommGroup (Om' i)] [∀ i, Module D' (Om' i)]
  (psi : ∀ i, Om i →ₛₗ[σ] Om' i)
  (wedge : ∀ i, Om i →ₗ[D] Om 1 →ₗ[D] Om (i + 1))
  (wedge' : ∀ i, Om' i →ₗ[D'] Om' 1 →ₗ[D'] Om' (i + 1))
  (deRham : ∀ i, Om i →+ Om (i + 1)) (deRham' : ∀ i, Om' i →+ Om' (i + 1))
  {d : D → Om 1} {d' : D' → Om' 1}
  (nabla : CompletedConnection p D (Om 1) d M)
  (nabla' : CompletedConnection p D' (Om' 1) d' M')
  (hleib : IsGradedLeibniz D Om wedge deRham d)
  (hleib' : IsGradedLeibniz D' Om' wedge' deRham' d')

/-- **The degree-`i` component of a semilinear comparison of completed de Rham complexes**:
the completed map `m ⊗ ω ↦ μ m ⊗ ψ_i ω`. -/
def comparisonValues (i : ℕ) :
    CompletedTensor p D (Om i) M →ₛₗ[σ] CompletedTensor p D' (Om' i) M' :=
  adicCompletionMapₛₗ (TensorProduct.map mu (psi i)) (map_pAdicIdeal_le p σ)

/-- The comparison on the image of an uncompleted pure tensor. -/
theorem comparisonValues_of_tmul (i : ℕ) (m : M) (ω : Om i) :
    comparisonValues p D D' σ M M' mu Om Om' psi i
        (toCompletedTensor p D (Om i) M (m ⊗ₜ[D] ω)) =
      toCompletedTensor p D' (Om' i) M' (mu m ⊗ₜ[D'] psi i ω) := by
  rw [comparisonValues, adicCompletionMapₛₗ_of]
  rfl

/-- The composite of left exterior multiplication by an `i`-form with the comparison of the
uncompleted tensor products. -/
private def comparisonWedgeComposite (i : ℕ) (ω : Om i) :
    (M ⊗[D] Om 1) →ₛₗ[σ] (M' ⊗[D'] Om' (i + 1)) :=
  (TensorProduct.map mu (psi (i + 1))).comp (LinearMap.lTensor M (wedge i ω))

variable (hpsi_wedge : ∀ (i : ℕ) (ω : Om i) (η : Om 1),
    psi (i + 1) (wedge i ω η) = wedge' i (psi i ω) (psi 1 η))

include hpsi_wedge in
/-- **Left exterior multiplication commutes with a semilinear comparison.** -/
theorem comparisonValues_wedgeMap (i : ℕ) (ω : Om i) (z : CompletedTensor p D (Om 1) M) :
    comparisonValues p D D' σ M M' mu Om Om' psi (i + 1)
        (wedgeMap p D Om wedge M i ω z) =
      wedgeMap p D' Om' wedge' M' i (psi i ω)
        (comparisonValues p D D' σ M M' mu Om Om' psi 1 z) := by
  have hwl : wedgeMap p D Om wedge M i ω z =
      adicCompletionMapₛₗ (LinearMap.lTensor M (wedge i ω))
        (le_of_eq (Ideal.map_id (pAdicIdeal (A := D) p))) z :=
    adicCompletionMap_eq_mapₛₗ _ _ z
  have hwr : wedgeMap p D' Om' wedge' M' i (psi i ω)
        (comparisonValues p D D' σ M M' mu Om Om' psi 1 z) =
      adicCompletionMapₛₗ (LinearMap.lTensor M' (wedge' i (psi i ω)))
          (le_of_eq (Ideal.map_id (pAdicIdeal (A := D') p)))
        (comparisonValues p D D' σ M M' mu Om Om' psi 1 z) :=
    adicCompletionMap_eq_mapₛₗ _ _ _
  have hcomp : ∀ y : M ⊗[D] Om 1,
      comparisonWedgeComposite D D' σ M M' mu Om Om' psi wedge i ω y =
        LinearMap.lTensor M' (wedge' i (psi i ω)) (TensorProduct.map mu (psi 1) y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul m η =>
      change mu m ⊗ₜ[D'] psi (i + 1) (wedge i ω η) =
        mu m ⊗ₜ[D'] wedge' i (psi i ω) (psi 1 η)
      rw [hpsi_wedge i ω η]
    | add y z hy hz => simp only [map_add, hy, hz]
  rw [hwl, hwr, comparisonValues, comparisonValues]
  trans adicCompletionMapₛₗ (comparisonWedgeComposite D D' σ M M' mu Om Om' psi wedge i ω)
    (map_pAdicIdeal_le p σ) z
  · exact (adicCompletionMapₛₗ_comp_apply (LinearMap.lTensor M (wedge i ω))
      (TensorProduct.map mu (psi (i + 1)))
      (comparisonWedgeComposite D D' σ M M' mu Om Om' psi wedge i ω) (le_of_eq (Ideal.map_id _))
      (map_pAdicIdeal_le p σ) (map_pAdicIdeal_le p σ) (fun _ => rfl) z).symm
  · exact adicCompletionMapₛₗ_comp_apply (TensorProduct.map mu (psi 1))
      (LinearMap.lTensor M' (wedge' i (psi i ω)))
      (comparisonWedgeComposite D D' σ M M' mu Om Om' psi wedge i ω) (map_pAdicIdeal_le p σ)
      (le_of_eq (Ideal.map_id _)) (map_pAdicIdeal_le p σ) hcomp z

variable (hpsi_deRham : ∀ (i : ℕ) (ω : Om i), psi (i + 1) (deRham i ω) = deRham' i (psi i ω))
  (hnabla : ∀ m : M, nabla' (mu m) =
    comparisonValues p D D' σ M M' mu Om Om' psi 1 (nabla m))

include hpsi_wedge hpsi_deRham hnabla in
private theorem rawDifferential_comparisonValues (i : ℕ) (y : M ⊗[D] Om i) :
    rawDifferential p D' Om' wedge' deRham' M' nabla' hleib' i
        (TensorProduct.map mu (psi i) y) =
      comparisonValues p D D' σ M M' mu Om Om' psi (i + 1)
        (rawDifferential p D Om wedge deRham M nabla hleib i y) := by
  induction y using TensorProduct.inductionOn with
  | tmul m ω =>
    rw [TensorProduct.map_tmul, rawDifferential_tmul, rawDifferential_tmul, map_add,
      comparisonValues_wedgeMap p D D' σ M M' mu Om Om' psi wedge wedge' hpsi_wedge,
      comparisonValues_of_tmul, hpsi_deRham i ω, hnabla m]
  | add y z hy hz => simp only [map_add, hy, hz]

include hpsi_wedge hpsi_deRham hnabla in
/-- **A semilinear comparison of completed de Rham complexes is a chain map**: its degree-`i`
component commutes with the two de Rham differentials. -/
theorem differential_comparisonValues (i : ℕ) (x : CompletedTensor p D (Om i) M) :
    differential p D' Om' wedge' deRham' M' nabla' hleib' i
        (comparisonValues p D D' σ M M' mu Om Om' psi i x) =
      comparisonValues p D D' σ M M' mu Om Om' psi (i + 1)
        (differential p D Om wedge deRham M nabla hleib i x) := by
  have key := rawDifferential_comparisonValues p D D' σ M M' mu Om Om' psi wedge wedge'
    deRham deRham' nabla nabla' hleib hleib' hpsi_wedge hpsi_deRham hnabla i
  refine AdicCompletion.ext fun k => ?_
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective
    ((pAdicIdeal (A := D) p) ^ k • ⊤ : Submodule D (M ⊗[D] Om i)) (x.val k)
  have hBi : (comparisonValues p D D' σ M M' mu Om Om' psi i x).val k =
      Submodule.Quotient.mk (TensorProduct.map mu (psi i) y) := by
    change adicQuotientMap (TensorProduct.map mu (psi i)) (map_pAdicIdeal_le p σ) k (x.val k) = _
    rw [← hy]
    rfl
  change levelDifferential p D' Om' wedge' deRham' M' nabla' hleib' i k
      ((comparisonValues p D D' σ M M' mu Om Om' psi i x).val k) =
    adicQuotientMap (TensorProduct.map mu (psi (i + 1))) (map_pAdicIdeal_le p σ) k
      ((differential p D Om wedge deRham M nabla hleib i x).val k)
  rw [hBi, levelDifferential_mk, differential_val, ← hy, levelDifferential_mk]
  exact congrArg (fun z : CompletedTensor p D' (Om' (i + 1)) M' => z.val k) (key y)

end SemilinearComparison

end CompletedDeRham

namespace CosimplicialDPAlgebra

variable {A : Type u} [CommRing A] (E : CosimplicialDPAlgebra.{u, v} A) (p : ℕ)

/-- **The completed divided power ring `D̂(b)` of the cosimplicial degree `b`.** -/
abbrev completedRing (b : ℕ) : Type v :=
  completedDividedPowerRing p (B := E.carrier b)

/-- **The transition ring map `D̂(m) → D̂(n)`** of the completed cosimplicial rings: the `p`-adic
completion of the transition map of the carriers. -/
def completedRingMap {m n : SimplexCategory} (φ : m ⟶ n) :
    E.completedRing p m.len →+* E.completedRing p n.len :=
  adicCompletionRingMap (E.map φ).toRingHom (map_pAdicIdeal_le p _)

/-- The transition ring map of an identity is the identity. -/
theorem completedRingMap_id (n : SimplexCategory) (x : E.completedRing p n.len) :
    E.completedRingMap p (𝟙 n) x = x :=
  adicCompletionMapₛₗ_id_apply (ringHomₛₗ (E.map (𝟙 n)).toRingHom) _
    (fun y => by
      change (E.map (𝟙 n)) y = y
      rw [E.map_id n]
      rfl) x

/-- The transition ring maps compose. -/
theorem completedRingMap_comp {m n k : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ k)
    (x : E.completedRing p m.len) :
    E.completedRingMap p (φ ≫ ψ) x = E.completedRingMap p ψ (E.completedRingMap p φ x) :=
  adicCompletionMapₛₗ_comp_apply (ringHomₛₗ (E.map φ).toRingHom)
    (ringHomₛₗ (E.map ψ).toRingHom) (ringHomₛₗ (E.map (φ ≫ ψ)).toRingHom) _ _ _
    (fun y => by
      change (E.map (φ ≫ ψ)) y = (E.map ψ) ((E.map φ) y)
      rw [E.map_comp φ ψ]
      rfl) x

/-- **The transition map of the forms, semilinear over the completed scalars.**  Its underlying
function is `Crystalline.CosimplicialDPAlgebra.formsMap`. -/
def formsMapCompleted {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ) :
    E.forms p a m.len →ₛₗ[E.completedRingMap p φ] E.forms p a n.len where
  toFun := E.formsMap p φ a
  map_add' := map_add _
  map_smul' r x := adicCompletionMapₛₗ_smul _ _ r x

end CosimplicialDPAlgebra

/-! ### The module half of the double complex, as data -/

/-- **A cosimplicial module over the completed cosimplicial rings `D̂(*)`.**  This is the module
half of the double complex `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` of
[Stacks, Proposition 60.21.3, Tag 07LG], without the connections. -/
structure CosimplicialCompletedModule {A : Type u} [CommRing A]
    (E : CosimplicialDPAlgebra.{u, v} A) (p : ℕ) where
  /-- The module of the cosimplicial degree `b`. -/
  carrier : ℕ → Type w
  /-- Each module is an abelian group. -/
  [addCommGroup : ∀ b, AddCommGroup (carrier b)]
  /-- Each module is a module over the completed ring of its degree. -/
  [module : ∀ b, Module (E.completedRing p b) (carrier b)]
  /-- The transition map, semilinear over the transition of the completed rings. -/
  map {m n : SimplexCategory} (φ : m ⟶ n) :
    carrier m.len →ₛₗ[E.completedRingMap p φ] carrier n.len
  /-- The transition map of an identity is the identity. -/
  map_id_apply (n : SimplexCategory) (x : carrier n.len) : map (𝟙 n) x = x
  /-- The transition maps compose. -/
  map_comp_apply {m n k : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ k) (x : carrier m.len) :
    map (φ ≫ ψ) x = map ψ (map φ x)

attribute [instance] CosimplicialCompletedModule.addCommGroup CosimplicialCompletedModule.module

namespace CosimplicialCompletedModule

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  (W : CosimplicialCompletedModule.{u, v, w} E p)

/-- **The degree-`(a, b)` term `M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` of the double complex.** -/
abbrev obj (a b : ℕ) : Type (max v w) :=
  CompletedTensor p (E.completedRing p b) (E.forms p a b) (W.carrier b)

/-- **The transition map `M(m) ⊗̂_{D(m)} Ω^a_{D(m)} → M(n) ⊗̂_{D(n)} Ω^a_{D(n)}`** of the
double complex in the cosimplicial direction: the `p`-adic completion of the tensor product of
the transition of the modules with the transition of the forms. -/
def tensorMap {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ) :
    W.obj a m.len →ₛₗ[E.completedRingMap p φ] W.obj a n.len :=
  adicCompletionMapₛₗ (TensorProduct.map (W.map φ) (E.formsMapCompleted p φ a))
    (map_pAdicIdeal_le p _)

/-- The transition map of the double complex on the image of an uncompleted pure tensor. -/
theorem tensorMap_of_tmul {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ) (x : W.carrier m.len)
    (ω : E.forms p a m.len) :
    W.tensorMap φ a (toCompletedTensor p (E.completedRing p m.len) (E.forms p a m.len)
        (W.carrier m.len) (x ⊗ₜ[E.completedRing p m.len] ω)) =
      toCompletedTensor p (E.completedRing p n.len) (E.forms p a n.len) (W.carrier n.len)
        (W.map φ x ⊗ₜ[E.completedRing p n.len] E.formsMap p φ a ω) := by
  rw [tensorMap, adicCompletionMapₛₗ_of]
  rfl

/-- **The transition map of an identity is the identity.** -/
theorem tensorMap_id (n : SimplexCategory) (a : ℕ) (x : W.obj a n.len) :
    W.tensorMap (𝟙 n) a x = x :=
  adicCompletionMapₛₗ_id_apply _ _
    (fun y => by
      induction y using TensorProduct.inductionOn with
      | tmul x ω =>
        change (W.map (𝟙 n) x) ⊗ₜ[E.completedRing p n.len] (E.formsMap p (𝟙 n) a ω) = _
        rw [W.map_id_apply, E.formsMap_id]
      | add y z hy hz => rw [map_add, hy, hz]) x

/-- **The transition maps compose.** -/
theorem tensorMap_comp {m n k : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ k) (a : ℕ)
    (x : W.obj a m.len) :
    W.tensorMap (φ ≫ ψ) a x = W.tensorMap ψ a (W.tensorMap φ a x) :=
  adicCompletionMapₛₗ_comp_apply
    (TensorProduct.map (W.map φ) (E.formsMapCompleted p φ a))
    (TensorProduct.map (W.map ψ) (E.formsMapCompleted p ψ a))
    (TensorProduct.map (W.map (φ ≫ ψ)) (E.formsMapCompleted p (φ ≫ ψ) a)) _ _ _
    (fun y => by
      induction y using TensorProduct.inductionOn with
      | tmul x ω =>
        change (W.map (φ ≫ ψ) x) ⊗ₜ[E.completedRing p k.len] (E.formsMap p (φ ≫ ψ) a ω) = _
        rw [W.map_comp_apply, E.formsMap_comp]
        rfl
      | add y z hy hz => simp only [map_add, hy, hz]) x

/-- The degree-`(a, b)` term of the double complex as an object of `AddCommGrpCat`. -/
def columnObj (a b : ℕ) : AddCommGrpCat.{max v w} := AddCommGrpCat.of (W.obj a b)

/-- **The exterior degree `a` of the double complex, as a cosimplicial abelian group**:
in cosimplicial degree `b` the group `M(b) ⊗̂_{D(b)} Ω^a_{D(b)}`. -/
def column (a : ℕ) : CosimplicialObject AddCommGrpCat.{max v w} where
  obj n := W.columnObj a n.len
  map φ := AddCommGrpCat.ofHom (W.tensorMap φ a).toAddMonoidHom
  map_id n := AddCommGrpCat.ext fun x => W.tensorMap_id n a x
  map_comp φ ψ := AddCommGrpCat.ext fun x => W.tensorMap_comp φ ψ a x

/-- The cosimplicial degree `b` of the column `K^{a,•}` is `M(b) ⊗̂_{D(b)} Ω^a_{D(b)}`. -/
theorem column_obj (a : ℕ) (n : SimplexCategory) :
    (W.column a).obj n = AddCommGrpCat.of (W.obj a n.len) := rfl

/-- The degree-`(a, b)` term, unfolded. -/
theorem columnObj_eq (a b : ℕ) : W.columnObj a b = AddCommGrpCat.of (W.obj a b) := rfl

end CosimplicialCompletedModule

/-! ### The connections, and the de Rham direction -/

/-- **A cosimplicial module over `D̂(*)` carrying a completed connection in each cosimplicial
degree.**  This is the full module half of the double complex
`K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` of [Stacks, Proposition 60.21.3, Tag 07LG]. -/
structure CosimplicialCompletedPair {A : Type u} [CommRing A]
    (E : CosimplicialDPAlgebra.{u, v} A) (p : ℕ)
    extends CosimplicialCompletedModule.{u, v, w} E p where
  /-- The completed connection of the cosimplicial degree `b`. -/
  nabla (b : ℕ) : CompletedConnection p (E.completedRing p b) (E.forms p 1 b)
    (E.differential p b) (carrier b)
  /-- **The connections are compatible with the cosimplicial direction.** -/
  nabla_tensorMap {m n : SimplexCategory} (φ : m ⟶ n) (x : carrier m.len) :
    nabla n.len (map φ x) = toCosimplicialCompletedModule.tensorMap φ 1 (nabla m.len x)
  /-- Consecutive de Rham differentials compose to zero in each cosimplicial degree. -/
  isSquareZero (b : ℕ) : CompletedDeRham.IsSquareZero p (E.completedRing p b)
    (fun a => E.forms p a b) (E.wedge p b) (E.deRham p b) (carrier b) (nabla b)
    (E.isGradedLeibniz p b)

namespace CosimplicialCompletedPair

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  (W : CosimplicialCompletedPair.{u, v, w} E p)

/-- **The de Rham differential `M(b) ⊗̂_{D(b)} Ω^a_{D(b)} → M(b) ⊗̂_{D(b)} Ω^{a+1}_{D(b)}`** of
the double complex, in one cosimplicial degree.  It is
`Crystalline.CompletedDeRham.differential`, the differential `∇(m ⊗ ω) = ∇(m) ∧ ω + m ⊗ d ω` of
the connection of that degree. -/
def degreeDifferential (b a : ℕ) :
    W.toCosimplicialCompletedModule.obj a b →+ W.toCosimplicialCompletedModule.obj (a + 1) b :=
  CompletedDeRham.differential p (E.completedRing p b) (fun i => E.forms p i b)
    (E.wedge p b) (E.deRham p b) (W.carrier b) (W.nabla b) (E.isGradedLeibniz p b) a

/-- **The two differentials of the double complex commute**: the de Rham differential of the `a`
direction is a morphism of cosimplicial objects. -/
theorem degreeDifferential_tensorMap {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ)
    (x : W.toCosimplicialCompletedModule.obj a m.len) :
    W.degreeDifferential n.len a (W.toCosimplicialCompletedModule.tensorMap φ a x) =
      W.toCosimplicialCompletedModule.tensorMap φ (a + 1) (W.degreeDifferential m.len a x) :=
  CompletedDeRham.differential_comparisonValues p (E.completedRing p m.len)
    (E.completedRing p n.len) (E.completedRingMap p φ) (W.carrier m.len) (W.carrier n.len)
    (W.map φ) (fun i => E.forms p i m.len) (fun i => E.forms p i n.len)
    (fun i => E.formsMapCompleted p φ i) (E.wedge p m.len) (E.wedge p n.len)
    (E.deRham p m.len) (E.deRham p n.len) (W.nabla m.len) (W.nabla n.len)
    (E.isGradedLeibniz p m.len) (E.isGradedLeibniz p n.len)
    (fun i ω η => E.formsMap_wedge p φ i ω η) (fun i ω => E.formsMap_deRham p φ i ω)
    (fun y => W.nabla_tensorMap φ y) a x

/-- **The de Rham differential of the double complex, as a morphism of cosimplicial abelian
groups** `K^{a,•} ⟶ K^{a+1,•}`. -/
def columnDifferential (a : ℕ) :
    W.toCosimplicialCompletedModule.column a ⟶ W.toCosimplicialCompletedModule.column (a + 1)
    where
  app n := AddCommGrpCat.ofHom (W.degreeDifferential n.len a)
  naturality {_m _n} φ := AddCommGrpCat.ext fun x => W.degreeDifferential_tensorMap φ a x

/-- The composite of two consecutive de Rham differentials `K^{a,•} ⟶ K^{a+2,•}` is zero. -/
theorem columnDifferential_comp (a : ℕ) :
    W.columnDifferential a ≫ W.columnDifferential (a + 1) = 0 :=
  NatTrans.ext (funext fun n =>
    AddCommGrpCat.ext fun x => DFunLike.congr_fun (W.isSquareZero n.len a) x)

/-- **The double complex `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` of
[Stacks, Proposition 60.21.3, Tag 07LG]**, as a cochain complex of cosimplicial abelian groups:
the `a` direction is the de Rham complex of the connections and the `b` direction is still
cosimplicial. -/
def doubleComplex : CochainComplex (CosimplicialObject AddCommGrpCat.{max v w}) ℕ :=
  CochainComplex.of W.toCosimplicialCompletedModule.column W.columnDifferential
    W.columnDifferential_comp

/-- The exterior degree `a` of `K` is the column `K^{a,•}`. -/
theorem doubleComplex_X (a : ℕ) :
    W.doubleComplex.X a = W.toCosimplicialCompletedModule.column a := rfl

/-- The differential of `K` is the de Rham differential of the connections. -/
theorem doubleComplex_d (a : ℕ) :
    W.doubleComplex.d a (a + 1) = W.columnDifferential a :=
  CochainComplex.of_d W.toCosimplicialCompletedModule.column W.columnDifferential a

end CosimplicialCompletedPair

end Crystalline

end
