module

public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyTruncationLEPairing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupBoundary
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyDevissage
public import StacksFrontier.LinearAlgebra.PerfectPairing.FiveLemma
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# Duality on a complex from duality on its graded pieces

Let `K` be a bounded below complex of `𝒪_X`-modules concentrated in degrees `[0, d]`, for which
Čech cohomology computes the cohomology of every term, and `γ : K ⊗ K ⟶ K` a pairing. Let `k` be
a field mapping to `Γ(X, 𝒪_X)` and `t : Hᴺ(X, K) ⟶ k` a linear form. If for all `a + b = d` the
pairings

`Hⁱ(X, Kᵃ[-a]) × Hʲ(X, Kᵇ[-b]) ⟶ Hᴺ(X, K) ⟶ k`, `i + j = N`,

induced by `γ` in bidegree `(a, b)` are perfect, then so are the pairings

`Hⁱ(X, K) × Hʲ(X, K) ⟶ Hᴺ(X, K) ⟶ k`, `(ξ, ξ') ↦ t(ξ ∪ ξ')`, `i + j = N`.

This is the argument of the proof of [Stacks, Tag 0FW7], there for the de Rham complex of a
smooth proper scheme over a field: by induction on `p` the pairings between
`Hⁱ(X, σ^{≤p}K)` and `Hʲ(X, σ^{≥d-p}K)` are perfect. The induction step compares the long exact
sequences of `0 ⟶ K^{p+1}[-p-1] ⟶ σ^{≤p+1}K ⟶ σ^{≤p}K ⟶ 0` and
`0 ⟶ σ^{≥d-p}K ⟶ σ^{≥d-p-1}K ⟶ K^{d-p-1}[-d+p+1] ⟶ 0` by the five lemma
(`LinearMap.isPerfPair_of_five`); the compatibility of the pairings with the connecting maps is
[Stacks, Tag 07MC] (`Stacks.Cech.Hypercohomology.cup_boundary_of_pairing`), and with the other maps
the naturality of the cup product.

## Main results

* `Stacks.Cech.Hypercohomology.isPerfPair_cupK_of_gradedPerfect`: if the pairings induced by `γ` on
  the graded pieces of `K` are perfect, then so are the pairings `Hⁱ(X, K) × Hʲ(X, K) ⟶ k`.

## References

* [Stacks Project, Tag 0FW7](https://stacks.math.columbia.edu/tag/0FW7)
* [Stacks Project, Tag 07MC](https://stacks.math.columbia.edu/tag/07MC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing sectionsPresheafFunctor)
open Stacks.Cech.LinearCupProduct (ComplexPairing tensorPresheafModules)
open Stacks.Cohomology.RightDerivedBoundary (toSC)

universe u

/-- A pairing between subsingletons is perfect. -/
theorem LinearMap.IsPerfPair.of_subsingleton {R M N : Type*} [Field R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [Subsingleton M] [Subsingleton N]
    (P : M →ₗ[R] N →ₗ[R] R) : P.IsPerfPair :=
  ⟨⟨fun _ _ _ => Subsingleton.elim _ _, fun φ => ⟨0, LinearMap.ext fun m => by
      rw [Subsingleton.elim m 0, map_zero, map_zero]⟩⟩,
    ⟨fun _ _ _ => Subsingleton.elim _ _, fun φ => ⟨0, LinearMap.ext fun m => by
      rw [Subsingleton.elim m 0, map_zero, map_zero]⟩⟩⟩

namespace Stacks.Cech.LinearCupProduct

/-- Two pairings of complexes with the same components are equal. -/
theorem ComplexPairing.ext' {C : Type*} [Category* C] {R : Type u} [CommRing R]
    {K L M : CochainComplex (PresheafModules.{u} C R) ℤ} {D D' : ComplexPairing R K L M}
    (h : ∀ a b n hn, D.μ a b n hn = D'.μ a b n hn) : D = D' := by
  cases D
  cases D'
  congr
  funext a b n hn
  exact h a b n hn

end Stacks.Cech.LinearCupProduct

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing
open scoped Stacks.StandardDerivedModel

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-! ### The long exact sequence with arbitrary indexing -/

section LongExact

variable (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
  (hS : (toSC S).ShortExact)

include hS in
/-- The composite `Hⁿ(X, K₁) ⟶ Hⁿ(X, K₂) ⟶ Hⁿ(X, K₃)` vanishes. -/
theorem hypercohomologyMap_f_g (n : ℤ) (a : hypercohomology O S.X₁ n) :
    hypercohomologyMap O S.g n (hypercohomologyMap O S.f n a) = 0 := by
  have h : hypercohomologyMap O S.f n ≫ hypercohomologyMap O S.g n = 0 :=
    (Functor.map_comp (DerivedCategory.homologyFunctor _ n) (derivedTriangle O S hS).mor₁
      (derivedTriangle O S hS).mor₂).symm.trans (by
        rw [Pretriangulated.comp_distTriang_mor_zero₁₂ _ (derivedTriangle_distinguished O S hS),
          Functor.map_zero]
        rfl)
  rw [← ConcreteCategory.comp_apply, h]
  rfl

include hS in
/-- `Hⁿ(X, K₁) ⟶ Hⁿ(X, K₂) ⟶ Hⁿ(X, K₃)` is exact. -/
theorem exact_f_g (n : ℤ) :
    Function.Exact (hypercohomologyMap O S.f n) (hypercohomologyMap O S.g n) := fun b =>
  ⟨fun hb => hypercohomology_exact₂ O S hS n b hb,
    fun ⟨a, ha⟩ => ha ▸ hypercohomologyMap_f_g O S hS n a⟩

/-- `Hⁿ(X, K₂) ⟶ Hⁿ(X, K₃) ⟶ Hⁿ⁺¹(X, K₁)` is exact. -/
theorem exact_g_boundary (n n' : ℤ) (h : n + 1 = n') :
    Function.Exact (hypercohomologyMap O S.g n) (boundary O S hS n n' h) := by
  subst h
  exact fun c => ⟨fun hc => exact_boundary O S hS n c hc,
    fun ⟨b, hb⟩ => hb ▸ boundary_hypercohomologyMap O S hS n b⟩

/-- `Hⁿ(X, K₃) ⟶ Hⁿ⁺¹(X, K₁) ⟶ Hⁿ⁺¹(X, K₂)` is exact. -/
theorem exact_boundary_f (n n' : ℤ) (h : n + 1 = n') :
    Function.Exact (boundary O S hS n n' h) (hypercohomologyMap O S.f n') := by
  subst h
  exact fun a => ⟨fun ha => hypercohomology_exact₁ O S hS n a ha, fun ⟨c, hc⟩ => hc ▸ by
    rw [← ConcreteCategory.comp_apply, boundary_comp_hypercohomologyMap]
    rfl⟩

end LongExact

/-! ### The cup product over a field -/

section Field

variable {k : Type u} [Field k] (ρ : k →+* SectionRing (ringSheaf O) ⊤)

/-- Hypercohomology as a vector space over `k`, along `ρ : k ⟶ Γ(X, 𝒪_X)`. -/
abbrev hypercohomologyK (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (n : ℤ) :
    ModuleCat.{u} k :=
  (ModuleCat.restrictScalars ρ).obj (hypercohomology O K n)

/-- The map induced on hypercohomology, as a `k`-linear map. -/
abbrev hypercohomologyMapK {K L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (f : K ⟶ L) (n : ℤ) : hypercohomologyK O ρ K n →ₗ[k] hypercohomologyK O ρ L n :=
  ((ModuleCat.restrictScalars ρ).map (hypercohomologyMap O f n)).hom

/-- The boundary map, as a `k`-linear map. -/
abbrev boundaryK (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n n' : ℤ) (h : n + 1 = n') :
    hypercohomologyK O ρ S.X₃ n →ₗ[k] hypercohomologyK O ρ S.X₁ n' :=
  ((ModuleCat.restrictScalars ρ).map (boundary O S hS n n' h)).hom

/-- **The cup product of Cohomology, Section 01FP**, as a `k`-bilinear map. -/
def cupK {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G) (γ : Pairing O F G H) (p q t : ℤ)
    (ht : p + q = t) :
    hypercohomologyK O ρ F p →ₗ[k] hypercohomologyK O ρ G q →ₗ[k] hypercohomologyK O ρ H t :=
  LinearMap.mk₂ k (cup O hF hG γ p q t ht) (cup_add_left O hF hG γ p q t ht)
    (fun c a b => cup_smul_left O hF hG γ p q t ht a b (ρ c)) (cup_add_right O hF hG γ p q t ht)
    (fun c a b => cup_smul_right O hF hG γ p q t ht a b (ρ c))

/-- The `k`-bilinear cup product `cupK` agrees with the cup product `cup`. -/
theorem cupK_apply {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G) (γ : Pairing O F G H) (p q t : ℤ)
    (ht : p + q = t) (a : hypercohomology O F p) (b : hypercohomology O G q) :
    cupK O ρ hF hG γ p q t ht a b = cup O hF hG γ p q t ht a b :=
  rfl

/-! ### Tag 07MC with arbitrary indexing -/

/-- [Stacks, Tag 07MC] (`Stacks.Cech.Hypercohomology.cup_boundary_of_pairing`) with the degrees
of the two boundary maps and of the cup products given by arbitrary equations. -/
theorem cup_boundary_of_pairing'
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact)
    (T : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hT : (toSC T).ShortExact) (H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (γ₁ : Pairing O S.X₁ T.X₃ H) (γ₂ : Pairing O S.X₂ T.X₂ H) (γ₃ : Pairing O S.X₃ T.X₁ H)
    (h₁ : ∀ a b n (hn : a + b = n),
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
          (((Stacks.Cech.Refinement.sectionsComplex O).obj S.X₁.obj).X a)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map T.g.hom).f b) ≫ γ₁.μ a b n hn =
        ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map S.f.hom).f a)).app
            (((Stacks.Cech.Refinement.sectionsComplex O).obj T.X₂.obj).X b) ≫ γ₂.μ a b n hn)
    (h₂ : ∀ a b n (hn : a + b = n),
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
          (((Stacks.Cech.Refinement.sectionsComplex O).obj S.X₂.obj).X a)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map T.f.hom).f b) ≫ γ₂.μ a b n hn =
        ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map S.g.hom).f a)).app
            (((Stacks.Cech.Refinement.sectionsComplex O).obj T.X₁.obj).X b) ≫ γ₃.μ a b n hn)
    (hF₁ : ∀ p, CechComputesSheaf O (S.X₁.obj.X p)) (hF₂ : ∀ p, CechComputesSheaf O (S.X₂.obj.X p))
    (hF₃ : ∀ p, CechComputesSheaf O (S.X₃.obj.X p)) (hG₁ : ∀ q, CechComputesSheaf O (T.X₃.obj.X q))
    (hG₂ : ∀ q, CechComputesSheaf O (T.X₂.obj.X q)) (hG₃ : ∀ q, CechComputesSheaf O (T.X₁.obj.X q))
    (hS₁ : CechComputes O S.X₁) (hS₃ : CechComputes O S.X₃) (hT₁ : CechComputes O T.X₁)
    (hT₃ : CechComputes O T.X₃) (n n₁ m m₁ N : ℤ) (hn : n + 1 = n₁) (hm : m + 1 = m₁)
    (h₁N : n₁ + m = N) (h₃N : n + m₁ = N) (a₃ : hypercohomology O S.X₃ n)
    (b₁ : hypercohomology O T.X₃ m) :
    cup O hS₁ hT₃ γ₁ n₁ m N h₁N (boundary O S hS n n₁ hn a₃) b₁ =
      (n₁.negOnePow : ℤ) • cup O hS₃ hT₁ γ₃ n m₁ N h₃N a₃ (boundary O T hT m m₁ hm b₁) := by
  subst hn hm
  obtain rfl : N = n + m + 1 := by omega
  exact cup_boundary_of_pairing O S hS T hT H γ₁ γ₂ γ₃ h₁ h₂ hF₁ hF₂ hF₃ hG₁ hG₂ hG₃ n m a₃ b₁

/-- Two pairings agreeing after precomposition with `f` on the left and `g` on the right have
compatible cup products. -/
theorem cup_map_left_eq_cup_map_right
    {A A' B B' H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hA : CechComputes O A) (hA' : CechComputes O A') (hB : CechComputes O B)
    (hB' : CechComputes O B') (f : A ⟶ A') (g : B ⟶ B') (γ' : Pairing O A' B H)
    (γ : Pairing O A B' H) (e : γ'.precompLeft f = γ.precompRight g) (i j N : ℤ)
    (hij : i + j = N) (a : hypercohomology O A i) (b : hypercohomology O B j) :
    cup O hA' hB γ' i j N hij (hypercohomologyMap O f i a) b =
      cup O hA hB' γ i j N hij a (hypercohomologyMap O g j b) :=
  (cup_precompLeft O hA' hA hB γ' f i j N hij a b).symm.trans
    ((congrArg (fun D => cup O hA hB D i j N hij a b) e).trans
      (cup_precompRight O hA hB' hB γ g i j N hij a b))

/-! ### The induction along the brutal truncations -/

section Duality

variable {O} (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
  (hK : ∀ j, CechComputesSheaf O (K.obj.X j)) (γ : Pairing O K K K) (d : ℤ)
  (hd : ∀ n, d < n → IsZero (K.obj.X n)) (N : ℤ) (t : hypercohomologyK O ρ K N →ₗ[k] k)

include hK in
/-- Čech cohomology computes the cohomology of the brutal truncation `σ^{≤p}K`. -/
theorem cechComputes_truncLEPlus (p : ℤ) : CechComputes O (truncLEPlus O K p) :=
  cechComputes_of_terms O _ (cechComputesSheaf_truncLEPlus_X hK p)

include hK in
/-- Čech cohomology computes the cohomology of the brutal truncation `σ^{≥e}K`. -/
theorem cechComputes_truncPlus (e : ℤ) : CechComputes O (truncPlus O K.obj e) :=
  cechComputes_of_terms O _ (cechComputesSheaf_truncPlus_X hK e)

include hK in
/-- Čech cohomology computes the cohomology of the graded piece `Kᵃ[-a]`. -/
theorem cechComputes_singlePlus_X (a : ℤ) : CechComputes O (singlePlus O (K.obj.X a) a) :=
  (hK a).singlePlus O a

/-- **The pairings of the truncations are perfect**: for `p + e = d` and all `i + j = N`,
`Hⁱ(X, σ^{≤p}K) × Hʲ(X, σ^{≥e}K) ⟶ Hᴺ(X, K) ⟶ k` is perfect. -/
def TruncPerfect (p e : ℤ) (hpe : p + e = d) : Prop :=
  ∀ i j (hij : i + j = N), ((cupK O ρ (cechComputes_truncLEPlus K hK p)
    (cechComputes_truncPlus K hK e) (truncLEGEPairing K γ d hd p e hpe.ge) i j N hij).compr₂
      t).IsPerfPair

/-- **The pairings of the graded pieces are perfect** in bidegree `(a, b)`, `a + b = d`. -/
def GradedPerfect (a b : ℤ) (hab : a + b = d) : Prop :=
  ∀ i j (hij : i + j = N), ((cupK O ρ (cechComputes_singlePlus_X K hK a)
    (cechComputes_singlePlus_X K hK b) (gradedPairing K γ d hd a b hab) i j N hij).compr₂
      t).IsPerfPair

/-- The scalar `(-1)ⁿ` as a unit of `k`. -/
abbrev negOnePowK (n : ℤ) : kˣ := Units.map (Int.castRingHom k).toMonoidHom n.negOnePow

/-- [Stacks, Tag 07MC] for the brutal truncation sequences of the induction step. -/
theorem cup_boundary_truncLESC_truncSC (p e : ℤ) (hpe : p + 1 + e = d) (n n₁ m m₁ : ℤ)
    (hn : n + 1 = n₁) (hm : m + 1 = m₁) (h₁N : n₁ + m = N) (h₃N : n + m₁ = N)
    (a : hypercohomology O (truncLESC O K (p + 1) p rfl).X₃ n)
    (b : hypercohomology O (truncSC O K.obj e).X₃ m) :
    cup O (cechComputes_singlePlus_X K hK (p + 1)) (cechComputes_singlePlus_X K hK e)
        (gradedPairing K γ d hd (p + 1) e hpe) n₁ m N h₁N
        (boundary O (truncLESC O K (p + 1) p rfl) (truncLESC_shortExact O K (p + 1) p rfl) n n₁
          hn a) b =
      (n₁.negOnePow : ℤ) • cup O (cechComputes_truncLEPlus K hK p)
        (cechComputes_truncPlus K hK (e + 1)) (truncLEGEPairing K γ d hd p (e + 1) (by omega))
        n m₁ N h₃N a
        (boundary O (truncSC O K.obj e) (truncSC_shortExact O K.obj e) m m₁ hm b) :=
  cup_boundary_of_pairing' O _ (truncLESC_shortExact O K (p + 1) p rfl) _
    (truncSC_shortExact O K.obj e) K (gradedPairing K γ d hd (p + 1) e hpe)
    (truncLEGEPairing K γ d hd (p + 1) e hpe.ge) (truncLEGEPairing K γ d hd p (e + 1) (by omega))
    (gradedPairing_compat K γ d hd p e hpe) (truncLEGEPairing_compat K γ d hd p e hpe)
    (cechComputesSheaf_singlePlus_X' (hK (p + 1)) (p + 1))
    (cechComputesSheaf_truncLEPlus_X hK (p + 1)) (cechComputesSheaf_truncLEPlus_X hK p)
    (cechComputesSheaf_singlePlus_X' (hK e) e) (cechComputesSheaf_truncPlus_X hK e)
    (cechComputesSheaf_truncPlus_X hK (e + 1)) (cechComputes_singlePlus_X K hK (p + 1))
    (cechComputes_truncLEPlus K hK p) (cechComputes_truncPlus K hK (e + 1))
    (cechComputes_singlePlus_X K hK e) n n₁ m m₁ N hn hm h₁N h₃N a b

/-- A linear form turns `x = (-1)ⁿ • y` into `t x = (-1)ⁿ * t y`. -/
private theorem apply_eq_negOnePowK_mul {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (t : M →ₗ[k] k) (n : ℤ) {x y : M} (h : x = (n.negOnePow : ℤ) • y) :
    t x = ((negOnePowK n : kˣ) : k) * t y :=
  (congrArg t h).trans ((map_zsmul t _ _).trans (zsmul_eq_mul _ _))

/-- **The induction step**: perfectness for `(σ^{≤p}K, σ^{≥e+1}K)` and for the graded pieces in
bidegree `(p + 1, e)` gives perfectness for `(σ^{≤p+1}K, σ^{≥e}K)`, by the five lemma. -/
theorem truncPerfect_succ (p e : ℤ) (hpe : p + 1 + e = d)
    (hIH : TruncPerfect ρ K hK γ d hd N t p (e + 1) (by omega))
    (hgr : GradedPerfect ρ K hK γ d hd N t (p + 1) e hpe) :
    TruncPerfect ρ K hK γ d hd N t (p + 1) e hpe := by
  intro i j hij
  let S := truncLESC O K (p + 1) p rfl
  have hS : (toSC S).ShortExact := truncLESC_shortExact O K (p + 1) p rfl
  let T := truncSC O K.obj e
  have hT : (toSC T).ShortExact := truncSC_shortExact O K.obj e
  have hc₁ := cechComputes_singlePlus_X K hK (p + 1)
  have hc₂ := cechComputes_truncLEPlus K hK (p + 1)
  have hc₃ := cechComputes_truncLEPlus K hK p
  have hd₁ := cechComputes_truncPlus K hK (e + 1)
  have hd₂ := cechComputes_truncPlus K hK e
  have hd₃ := cechComputes_singlePlus_X K hK e
  let γ₁ := gradedPairing K γ d hd (p + 1) e hpe
  let γ₂ := truncLEGEPairing K γ d hd (p + 1) e hpe.ge
  let γ₃ := truncLEGEPairing K γ d hd p (e + 1) (by omega)
  refine LinearMap.isPerfPair_of_five
    (boundaryK O ρ S hS (i - 1) i (by omega)) (hypercohomologyMapK O ρ S.f i)
    (hypercohomologyMapK O ρ S.g i) (boundaryK O ρ S hS i (i + 1) rfl)
    (boundaryK O ρ T hT j (j + 1) rfl) (hypercohomologyMapK O ρ T.g j)
    (hypercohomologyMapK O ρ T.f j) (boundaryK O ρ T hT (j - 1) j (by omega))
    (exact_boundary_f O S hS (i - 1) i (by omega)) (exact_f_g O S hS i)
    (exact_g_boundary O S hS i (i + 1) rfl) (exact_g_boundary O T hT j (j + 1) rfl)
    (exact_f_g O T hT j) (exact_boundary_f O T hT (j - 1) j (by omega))
    ((cupK O ρ hc₃ hd₁ γ₃ (i - 1) (j + 1) N (by omega)).compr₂ t)
    ((cupK O ρ hc₁ hd₃ γ₁ i j N hij).compr₂ t) ((cupK O ρ hc₂ hd₂ γ₂ i j N hij).compr₂ t)
    ((cupK O ρ hc₃ hd₁ γ₃ i j N hij).compr₂ t)
    ((cupK O ρ hc₁ hd₃ γ₁ (i + 1) (j - 1) N (by omega)).compr₂ t)
    (negOnePowK i) 1 1 (negOnePowK (i + 1)) ?_ ?_ ?_ ?_
    (hIH (i - 1) (j + 1) (by omega)) (hgr i j hij) (hIH i j hij) (hgr (i + 1) (j - 1) (by omega))
  · refine fun (a : hypercohomology O S.X₃ (i - 1)) (b : hypercohomology O T.X₃ j) => ?_
    show t (cup O hc₁ hd₃ γ₁ i j N hij (boundary O S hS (i - 1) i (by omega) a) b) =
      _ * t (cup O hc₃ hd₁ γ₃ (i - 1) (j + 1) N (by omega) a (boundary O T hT j (j + 1) rfl b))
    exact apply_eq_negOnePowK_mul t _ (cup_boundary_truncLESC_truncSC K hK γ d hd N p e hpe
      (i - 1) i j (j + 1) (by omega) rfl hij (by omega) a b)
  · refine fun (a : hypercohomology O S.X₁ i) (b : hypercohomology O T.X₂ j) => ?_
    show t (cup O hc₂ hd₂ γ₂ i j N hij (hypercohomologyMap O S.f i a) b) =
      _ * t (cup O hc₁ hd₃ γ₁ i j N hij a (hypercohomologyMap O T.g j b))
    simp only [Units.val_one, one_mul]
    exact congrArg t (cup_map_left_eq_cup_map_right O hc₁ hc₂ hd₂ hd₃ S.f T.g γ₂ γ₁
      (ComplexPairing.ext' fun a b n hn => (gradedPairing_compat K γ d hd p e hpe a b n hn).symm)
      i j N hij a b)
  · refine fun (a : hypercohomology O S.X₂ i) (b : hypercohomology O T.X₁ j) => ?_
    show t (cup O hc₃ hd₁ γ₃ i j N hij (hypercohomologyMap O S.g i a) b) =
      _ * t (cup O hc₂ hd₂ γ₂ i j N hij a (hypercohomologyMap O T.f j b))
    simp only [Units.val_one, one_mul]
    exact congrArg t (cup_map_left_eq_cup_map_right O hc₂ hc₃ hd₁ hd₂ S.g T.f γ₃ γ₂
      (ComplexPairing.ext' fun a b n hn =>
        (truncLEGEPairing_compat K γ d hd p e hpe a b n hn).symm) i j N hij a b)
  · refine fun (a : hypercohomology O S.X₃ i) (b : hypercohomology O T.X₃ (j - 1)) => ?_
    show t (cup O hc₁ hd₃ γ₁ (i + 1) (j - 1) N (by omega) (boundary O S hS i (i + 1) rfl a) b) =
      _ * t (cup O hc₃ hd₁ γ₃ i j N hij a (boundary O T hT (j - 1) j (by omega) b))
    exact apply_eq_negOnePowK_mul t _ (cup_boundary_truncLESC_truncSC K hK γ d hd N p e hpe
      i (i + 1) (j - 1) j rfl (by omega) (by omega) hij a b)

include hd in
/-- **The base of the induction**: `σ^{≤-1}K` and `σ^{≥d+1}K` vanish, so the pairing between them
is perfect. -/
theorem truncPerfect_base (h0 : ∀ n, n < 0 → IsZero (K.obj.X n)) :
    TruncPerfect ρ K hK γ d hd N t (-1) (d + 1) (by omega) := by
  intro i j hij
  have h₁ : IsZero (hypercohomology O (truncLEPlus O K (-1)) i) :=
    isZero_hypercohomology_of_isZero_X O _ (fun q => by
      by_cases hq : q ≤ -1
      · exact (h0 q (by omega)).of_iso
          (StacksDraft.StupidTruncation.stupidTruncLEXIso K.obj (-1) q hq)
      · exact isZero_truncLEPlus_X O K (by omega)) i
  have h₂ : IsZero (hypercohomology O (truncPlus O K.obj (d + 1)) j) :=
    isZero_hypercohomology_of_isZero_X O _ (fun q => by
      by_cases hq : d + 1 ≤ q
      · exact (hd q (by omega)).of_iso
          (StacksDraft.StupidTruncation.stupidTruncGEXIso K.obj (d + 1) q hq)
      · exact CochainComplex.isZero_of_isStrictlyGE
          (K.obj.stupidTrunc (embeddingUpIntGE (d + 1))) (d + 1) q (by omega)) j
  have s₁ := ModuleCat.subsingleton_of_isZero h₁
  have s₂ := ModuleCat.subsingleton_of_isZero h₂
  have : Subsingleton (hypercohomologyK O ρ (truncLEPlus O K (-1)) i) := s₁
  have : Subsingleton (hypercohomologyK O ρ (truncPlus O K.obj (d + 1)) j) := s₂
  exact LinearMap.IsPerfPair.of_subsingleton _

include hd in
/-- **The induction along the brutal truncations**: the pairings of `σ^{≤p}K` and `σ^{≥d-p}K`
are perfect for `-1 ≤ p ≤ d`. -/
theorem truncPerfect_of_gradedPerfect (h0 : ∀ n, n < 0 → IsZero (K.obj.X n))
    (hgr : ∀ a b (hab : a + b = d), 0 ≤ a → 0 ≤ b → GradedPerfect ρ K hK γ d hd N t a b hab) :
    ∀ n : ℕ, (n : ℤ) ≤ d + 1 → ∀ p e (hpe : p + e = d), p = n - 1 →
      TruncPerfect ρ K hK γ d hd N t p e hpe := by
  intro n
  induction n with
  | zero =>
    intro _ p e hpe hp
    obtain rfl : p = -1 := by omega
    obtain rfl : e = d + 1 := by omega
    exact truncPerfect_base ρ K hK γ d hd N t h0
  | succ n ih =>
    intro hn p e hpe hp
    obtain ⟨p₀, rfl⟩ : ∃ p₀, p = p₀ + 1 := ⟨p - 1, by omega⟩
    exact truncPerfect_succ ρ K hK γ d hd N t p₀ e hpe
      (ih (by omega) p₀ (e + 1) (by omega) (by omega)) (hgr (p₀ + 1) e hpe (by omega) (by omega))

include hd in
/-- **Duality on a complex from duality on its graded pieces.** Let `K` be concentrated in degrees
`[0, d]`, with Čech cohomology computing the cohomology of its terms, `γ : K ⊗ K ⟶ K` a pairing
and `t : Hᴺ(X, K) ⟶ k` linear. If the pairings
`Hⁱ(X, Kᵃ[-a]) × Hʲ(X, Kᵇ[-b]) ⟶ Hᴺ(X, K) ⟶ k` induced by `γ` in bidegree `(a, b)` are perfect for
all `a, b ≥ 0` with `a + b = d` and all `i + j = N`, then so are the pairings
`Hⁱ(X, K) × Hʲ(X, K) ⟶ Hᴺ(X, K) ⟶ k`, `(ξ, ξ') ↦ t(ξ ∪ ξ')`. -/
theorem isPerfPair_cupK_of_gradedPerfect (h0 : ∀ n, n < 0 → IsZero (K.obj.X n))
    (hgr : ∀ a b (hab : a + b = d), 0 ≤ a → 0 ≤ b → GradedPerfect ρ K hK γ d hd N t a b hab)
    (hd0 : 0 ≤ d) (i j : ℤ) (hij : i + j = N) :
    ((cupK O ρ (cechComputes_of_terms O K hK) (cechComputes_of_terms O K hK) γ i j N
      hij).compr₂ t).IsPerfPair := by
  have hT := truncPerfect_of_gradedPerfect ρ K hK γ d hd N t h0 hgr (d + 1).toNat (by omega) d 0
    (by omega) (by omega) i j hij
  have : K.obj.IsStrictlyLE d := (CochainComplex.isStrictlyLE_iff K.obj d).2 hd
  have : K.obj.IsStrictlyGE 0 := (CochainComplex.isStrictlyGE_iff K.obj 0).2 h0
  let eπ : K ≅ truncLEPlus O K d :=
    ObjectProperty.isoMk _ (@asIso _ _ _ _ (K.obj.πStupidTrunc (embeddingUpIntLE d))
      (StacksDraft.StupidTruncation.isIso_πStupidTruncLE K.obj d))
  let eι : truncPlus O K.obj 0 ≅ K := truncPlusIso O K 0
  let e₁ := ((ModuleCat.restrictScalars ρ).mapIso (hypercohomologyMapIso O eπ i)).toLinearEquiv
  let e₂ := ((ModuleCat.restrictScalars ρ).mapIso (hypercohomologyMapIso O eι j)).toLinearEquiv
  let D := γ.precompRight (ιTruncPlus O K 0)
  have hD := precompRight_ιTruncPlus_vanish K γ d hd d 0 (by omega)
  refine LinearMap.isPerfPair_of_linearEquiv _ _ e₁ e₂.symm (fun a b => ?_) hT
  have key : ∀ b' : hypercohomology O K j,
      cup O (cechComputes_truncLEPlus K hK d) (cechComputes_truncPlus K hK 0) (D.descLE d hD) i j N
        hij (hypercohomologyMap O (truncLEπ O K d) i a) (hypercohomologyMap O eι.inv j b') =
      cup O (cechComputes_of_terms O K hK) (cechComputes_of_terms O K hK) γ i j N hij a b' := by
    intro b'
    have h₁ := cup_natural O (cechComputes_of_terms O K hK) (cechComputes_truncPlus K hK 0)
      (cechComputes_truncLEPlus K hK d) (cechComputes_truncPlus K hK 0) (truncLEπ O K d) (𝟙 _)
      (𝟙 _) D (D.descLE d hD) (pairingHom_descLE D d hD) i j N hij a
      (hypercohomologyMap O eι.inv j b')
    rw [hypercohomologyMap_id, hypercohomologyMap_id, ConcreteCategory.id_apply,
      ConcreteCategory.id_apply] at h₁
    have h₂ := cup_precompRight O (cechComputes_of_terms O K hK) (cechComputes_of_terms O K hK)
      (cechComputes_truncPlus K hK 0) γ (ιTruncPlus O K 0) i j N hij a
      (hypercohomologyMap O eι.inv j b')
    have h₃ :
        hypercohomologyMap O (ιTruncPlus O K 0) j (hypercohomologyMap O eι.inv j b') = b' := by
      rw [← ConcreteCategory.comp_apply, ← hypercohomologyMap_comp]
      show hypercohomologyMap O (eι.inv ≫ eι.hom) j b' = b'
      rw [eι.inv_hom_id, hypercohomologyMap_id]
      rfl
    exact h₁.symm.trans (h₂.trans (congrArg _ h₃))
  exact congrArg t (key b)

end Duality

end Field

end Stacks.Cech.Hypercohomology

end
