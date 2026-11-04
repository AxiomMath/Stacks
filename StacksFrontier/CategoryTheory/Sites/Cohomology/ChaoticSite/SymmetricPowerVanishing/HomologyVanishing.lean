module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksFrontier.AlgebraicTopology.SimplicialTensorConnectivity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolutionOfModules
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse
public import StacksFrontier.LinearAlgebra.SymmetricPower.Free
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
public import StacksFrontier.RingTheory.Flat.Lazard
public import StacksFrontier.RingTheory.Koszul.DifferentialGradedAlgebra
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.RingTheory.Koszul.Regular
public import StacksFrontier.RingTheory.TensorAlgebra.Colimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing.KoszulDirectLimit
import StacksCore.Tactic.StacksAttribute

/-!
# Vanishing of the low homology of a symmetric power

The sectionwise homogeneous Koszul complex of a flat diagram, the comparison of tensor products
of chain complexes with their extensions to `ℤ`, and the main vanishing results
`isZero_homology_symmetricPowerDiagram_of_lt` and
`isZero_leftDerivedColim_symmetricPowerDiagram_of_lt` (Tag 08RD).

This file is one part of `SymmetricPowerVanishing`, which imports all of them.
-/


@[expose] public noncomputable section

open scoped DirectSum TensorProduct

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Stacks.ChaoticSite

universe u v w

attribute [local instance] HasDerivedCategory.standard

/-- If the `n`th homology of a chain complex of modules vanishes, every `n`-cycle is a
boundary. -/
lemma chain_cycle_is_boundary {R : Type u} [Ring R]
    (K : ChainComplex (ModuleCat.{v} R) ℕ) (n : ℕ) (h : IsZero (K.homology n))
    (x : K.X n) (hx : K.d n (n - 1) x = 0) :
    ∃ y : K.X (n + 1), K.d (n + 1) n y = x := by
  have hh := (K.exactAt_iff_isZero_homology n).mpr h
  rw [K.exactAt_iff' (n + 1) n (n - 1) (by simp) (by cases n <;> simp),
    ShortComplex.moduleCat_exact_iff] at hh
  exact hh x hx

/-- Let `⋯ → K₂ → K₁ → K₀` be a sequence of chain complexes with zero composites, exact in
each degree `n` at `Kᵢ` whenever `i + n < l`, with `Hₙ(K_{i+1}) = 0` whenever `i + n = l`. If
`i + n = l` and `y ∈ (K_{i+1})ₙ` maps to a cycle of `Kᵢ`, then the image of `y` in `Kᵢ` is
the image of a boundary of `K_{i+1}`. -/
lemma resolution_boundary_lift {R : Type u} [Ring R]
    (K : ℕ → ChainComplex (ModuleCat.{v} R) ℕ) (f : ∀ i, K (i + 1) ⟶ K i)
    (hff : ∀ i, f (i + 1) ≫ f i = 0) (l : ℕ)
    (hex : ∀ i n, i + n < l →
      Function.Exact ((f (i + 1)).f n).hom ((f i).f n).hom)
    (hvan : ∀ i n, i + n = l → IsZero ((K (i + 1)).homology n))
    (n i : ℕ) (hin : i + n = l)
    (y : (K (i + 1)).X n) (hy : (K i).d n (n - 1) ((f i).f n y) = 0) :
    ∃ w : (K (i + 1)).X (n + 1),
      (f i).f n ((K (i + 1)).d (n + 1) n w) = (f i).f n y := by
  have hnat (i a b : ℕ) (x : (K (i + 1)).X a) :
      (f i).f b ((K (i + 1)).d a b x) = (K i).d a b ((f i).f a x) :=
    (ConcreteCategory.congr_hom ((f i).comm a b) x).symm
  have hcomp (i n : ℕ) (x : (K (i + 2)).X n) :
      (f i).f n ((f (i + 1)).f n x) = 0 := by
    have hh := congrArg (fun t => t.f n) (hff i)
    exact ConcreteCategory.congr_hom hh x
  induction n generalizing i with
  | zero =>
      obtain ⟨w, hw⟩ := chain_cycle_is_boundary (K (i + 1)) 0 (hvan i 0 hin) y (by
        rw [(K (i + 1)).shape 0 0 (by simp)]; rfl)
      exact ⟨w, congrArg ((f i).f 0) hw⟩
  | succ n ih =>
      have hdy : (f i).f n ((K (i + 1)).d (n + 1) n y) = 0 := by
        simpa only [Nat.add_sub_cancel] using (hnat i (n + 1) n y).trans hy
      obtain ⟨z, hz⟩ := (hex i n (by omega) _).mp hdy
      have hdz : (K (i + 1)).d n (n - 1) ((f (i + 1)).f n z) = 0 := by
        rw [hz]
        exact ConcreteCategory.congr_hom ((K (i + 1)).d_comp_d (n + 1) n (n - 1)) y
      obtain ⟨w, hw⟩ := ih (i + 1) (by omega) z hdz
      have hcycle : (K (i + 1)).d (n + 1) n (y - (f (i + 1)).f (n + 1) w) = 0 := by
        rw [map_sub, ← hnat (i + 1) (n + 1) n w, hw, hz, sub_self]
      obtain ⟨v, hv⟩ := chain_cycle_is_boundary (K (i + 1)) (n + 1)
        (hvan i (n + 1) hin) (y - (f (i + 1)).f (n + 1) w) (by simpa using hcycle)
      refine ⟨v, ?_⟩
      rw [hv, map_sub, hcomp, sub_zero]

/-- Let `⋯ → K₂ → K₁ → K₀` be a sequence of chain complexes with zero composites, exact in
each degree `n` at `Kᵢ` whenever `i + n < l`, with `Hₙ(K_{i+1}) = 0` whenever `i + n = l`, and
with `(K₁)_l → (K₀)_l` surjective. Then `H_l(K₀) = 0`. -/
lemma homology_isZero_of_exact_resolution {R : Type u} [Ring R]
    (K : ℕ → ChainComplex (ModuleCat.{v} R) ℕ) (f : ∀ i, K (i + 1) ⟶ K i)
    (hff : ∀ i, f (i + 1) ≫ f i = 0) (l : ℕ)
    (hex : ∀ i n, i + n < l →
      Function.Exact ((f (i + 1)).f n).hom ((f i).f n).hom)
    (hvan : ∀ i n, i + n = l → IsZero ((K (i + 1)).homology n))
    (hsurj : Function.Surjective ((f 0).f l).hom) :
    IsZero ((K 0).homology l) := by
  rw [← (K 0).exactAt_iff_isZero_homology,
    (K 0).exactAt_iff' (l + 1) l (l - 1) (by simp) (by cases l <;> simp),
    ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  obtain ⟨w, hw⟩ := resolution_boundary_lift K f hff l hex hvan l 0 (by omega) y hx
  refine ⟨(f 0).f (l + 1) w, ?_⟩
  exact (ConcreteCategory.congr_hom ((f 0).comm (l + 1) l) w).trans hw

/-- The homogeneous Koszul differential as a morphism in `ModuleCat B`. -/
abbrev homogeneousKoszulDifferentialHom
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M] (p q : ℕ) :
    ModuleCat.of B ((⋀[B]^(p + 1) M) ⊗[B] SymPow.symmetricPower q B M) ⟶
      ModuleCat.of B ((⋀[B]^p M) ⊗[B] SymPow.symmetricPower (q + 1) B M) :=
  ModuleCat.ofHom (homogeneousKoszulDifferential B M p q)

/-- The homogeneous Koszul differential, composed with the identification of symmetric powers
along `q + 1 = r`, is natural in the module. -/
lemma homogeneousKoszulDifferential_naturality_cast
    {B : Type w} {M N : Type v} [CommRing B] [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] (f : M →ₗ[B] N) (p q r : ℕ) (h : q + 1 = r) :
    ModuleCat.ofHom (TensorProduct.map (exteriorPower.map (p + 1) f) (SymPow.symMap q f)) ≫
        homogeneousKoszulDifferentialHom B N p q ≫
          eqToHom (congrArg (fun n => ModuleCat.of B
            ((⋀[B]^p N) ⊗[B] SymPow.symmetricPower n B N)) h) =
      (homogeneousKoszulDifferentialHom B M p q ≫
          eqToHom (congrArg (fun n => ModuleCat.of B
            ((⋀[B]^p M) ⊗[B] SymPow.symmetricPower n B M)) h)) ≫
        ModuleCat.ofHom (TensorProduct.map (exteriorPower.map p f) (SymPow.symMap r f)) := by
  subst r
  simp only [eqToHom_refl, Category.comp_id]
  apply ModuleCat.hom_ext
  exact (homogeneousKoszulDifferential_naturality f p q).symm

/-- The differential of the homogeneous Koszul complex is natural in the module. -/
lemma homogeneousKoszulComplexDifferential_naturality
    {B : Type w} {M N : Type v} [CommRing B] [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] (f : M →ₗ[B] N) (k p : ℕ) :
    ModuleCat.ofHom (TensorProduct.map (exteriorPower.map (p + 1) f)
        (SymPow.symMap (k - (p + 1)) f)) ≫
        homogeneousKoszulComplexDifferential B N k p =
      homogeneousKoszulComplexDifferential B M k p ≫
        ModuleCat.ofHom (TensorProduct.map (exteriorPower.map p f)
          (SymPow.symMap (k - p) f)) := by
  by_cases hp : p < k
  · simp only [homogeneousKoszulComplexDifferential, dite_eq_left hp]
    exact homogeneousKoszulDifferential_naturality_cast f p
      (k - (p + 1)) (k - p) (by omega)
  · simp [homogeneousKoszulComplexDifferential, hp]

/-- The sectionwise term `∧^p F ⊗ Sym^{k-p} F` of the homogeneous Koszul complex of a diagram of
modules `F`. -/
abbrev homogeneousKoszulDiagram
    (C : Type u) [Category.{v} C] (B : Type w) [CommRing B]
    (F : Cᵒᵖ ⥤ ModuleCat.{max u v w} B) (k p : ℕ) :
    Cᵒᵖ ⥤ ModuleCat.{max u v w} B :=
  MonoidalCategory.tensorObj (exteriorPowerDiagram C B F p)
    (symmetricPowerDiagram C B F (k - p))

/-- The sectionwise homogeneous Koszul differential
`∧^{p+1} F ⊗ Sym^{k-p-1} F → ∧^p F ⊗ Sym^{k-p} F`, as a morphism of diagrams. -/
def homogeneousKoszulDiagramDifferential
    (C : Type u) [Category.{v} C] (B : Type w) [CommRing B]
    (F : Cᵒᵖ ⥤ ModuleCat.{max u v w} B) (k p : ℕ) :
    homogeneousKoszulDiagram C B F k (p + 1) ⟶
      homogeneousKoszulDiagram C B F k p where
  app X := homogeneousKoszulComplexDifferential B (F.obj X) k p
  naturality _ _ f := homogeneousKoszulComplexDifferential_naturality (F.map f).hom k p

/-- Two consecutive sectionwise homogeneous Koszul differentials compose to zero. -/
lemma homogeneousKoszulDiagramDifferential_comp
    (C : Type u) [Category.{v} C] (B : Type w) [CommRing B]
    (F : Cᵒᵖ ⥤ ModuleCat.{max u v w} B) (k p : ℕ) :
    homogeneousKoszulDiagramDifferential C B F k (p + 1) ≫
      homogeneousKoszulDiagramDifferential C B F k p = 0 := by
  ext X : 2
  exact homogeneousKoszulComplexDifferential_comp B (F.obj X) k p

/-- For a flat module, two consecutive homogeneous Koszul differentials, composed with the
identifications of symmetric powers along `q + 1 = r` and `r + 1 = s`, form an exact pair. -/
lemma homogeneousKoszulDifferential_exact_cast
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M]
    [Module.Flat B M] (p q r s : ℕ) (hqr : q + 1 = r) (hrs : r + 1 = s) :
    Function.Exact
      (homogeneousKoszulDifferentialHom B M (p + 1) q ≫
        eqToHom (congrArg (fun n => ModuleCat.of B
          ((⋀[B]^(p + 1) M) ⊗[B] SymPow.symmetricPower n B M)) hqr)).hom
      (homogeneousKoszulDifferentialHom B M p r ≫
        eqToHom (congrArg (fun n => ModuleCat.of B
          ((⋀[B]^p M) ⊗[B] SymPow.symmetricPower n B M)) hrs)).hom := by
  subst r s
  simp only [eqToHom_refl, Category.comp_id]
  exact homogeneousKoszul_exact_of_flat B M p q

/-- For a flat module and `p + 1 < k`, the homogeneous Koszul complex in total degree `k` is
exact at degree `p + 1`. -/
@[sga "6 IX 1.8" "partial"]
lemma homogeneousKoszulComplexDifferential_exact
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M]
    [Module.Flat B M] (k p : ℕ) (hp : p + 1 < k) :
    Function.Exact (homogeneousKoszulComplexDifferential B M k (p + 1)).hom
      (homogeneousKoszulComplexDifferential B M k p).hom := by
  have hp' : p < k := by omega
  simp only [homogeneousKoszulComplexDifferential, dite_eq_left hp, dite_eq_left hp']
  exact homogeneousKoszulDifferential_exact_cast B M p
    (k - (p + 1 + 1)) (k - (p + 1)) (k - p) (by omega) (by omega)

/-- For `k > 0`, the last differential `∧^1 M ⊗ Sym^{k-1} M → ∧^0 M ⊗ Sym^k M` of the
homogeneous Koszul complex is surjective. -/
@[sga "6 IX 1.8" "partial"]
lemma homogeneousKoszulComplexDifferential_surjective
    (B M : Type*) [CommRing B] [AddCommGroup M] [Module B M]
    (k : ℕ) (hk : 0 < k) :
    Function.Surjective (homogeneousKoszulComplexDifferential B M k 0).hom := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simpa [homogeneousKoszulComplexDifferential] using
    homogeneousKoszulDifferential_zero_surjective B M q

/-- Let `F` be a flat diagram of modules and `l < k`. If the Moore complex of
`∧^{p+1} F ⊗ Sym^{k-p-1} F` on `U` has vanishing `Hₙ` whenever `p + n = l`, then the Moore
complex of `∧^0 F ⊗ Sym^k F` on `U` has vanishing `H_l`. -/
lemma homogeneousKoszulDiagram_homology_isZero
    (C : Type u) [SmallCategory C] (B : Type w) [CommRing B]
    (U : CosimplicialObject C) (F : Cᵒᵖ ⥤ ModuleCat.{max u w} B)
    (hF : ∀ X, Module.Flat B (F.obj X)) (k l : ℕ) (hl : l < k)
    (hvan : ∀ p n, p + n = l →
      IsZero (((alternatingFaceMapComplex (ModuleCat.{max u w} B)).obj
        (U.op ⋙ homogeneousKoszulDiagram C B F k (p + 1))).homology n)) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max u w} B)).obj
      (U.op ⋙ homogeneousKoszulDiagram C B F k 0)).homology l) := by
  let T := (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (ModuleCat.{max u w} B)).obj U.op ⋙
    alternatingFaceMapComplex (ModuleCat.{max u w} B)
  let K := fun p => T.obj (homogeneousKoszulDiagram C B F k p)
  let f := fun p => T.map (homogeneousKoszulDiagramDifferential C B F k p)
  apply homology_isZero_of_exact_resolution K f _ l _ hvan
  · exact homogeneousKoszulComplexDifferential_surjective B _ k (by omega)
  · intro p
    rw [← T.map_comp, homogeneousKoszulDiagramDifferential_comp]
    exact T.map_zero _ _
  · intro p n hpn
    have := hF (U.op.obj (Opposite.op (SimplexCategory.mk n)))
    exact homogeneousKoszulComplexDifferential_exact B _ k p (by omega)

/-- The isomorphism `∧^0 M ⊗ Sym^k M ≃ Sym^k M` is natural in `M`. -/
lemma homogeneousKoszulZeroIso_naturality
    {B M N : Type*} [CommRing B] [AddCommGroup M] [Module B M]
    [AddCommGroup N] [Module B N] (f : M →ₗ[B] N) (k : ℕ) :
    (homogeneousKoszulZeroIso B N k).toLinearMap.comp
      (TensorProduct.map (exteriorPower.map 0 f) (SymPow.symMap k f)) =
    (SymPow.symMap k f).comp (homogeneousKoszulZeroIso B M k).toLinearMap := by
  apply TensorProduct.ext
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  dsimp [homogeneousKoszulZeroIso]
  simp only [map_smul]
  exact congrArg (fun r : B => r • SymPow.symMap k f y)
    (LinearMap.congr_fun (exteriorPower.zeroEquiv_naturality f) x)

/-- The isomorphism of diagrams `∧^0 F ⊗ Sym^k F ≅ Sym^k F`. -/
def homogeneousKoszulZeroDiagramIso
    (C : Type u) [Category.{v} C] (B : Type w) [CommRing B]
    (F : Cᵒᵖ ⥤ ModuleCat.{max u v w} B) (k : ℕ) :
    homogeneousKoszulDiagram C B F k 0 ≅ symmetricPowerDiagram C B F k :=
  NatIso.ofComponents (fun X => (homogeneousKoszulZeroIso B (F.obj X) k).toModuleIso)
    (by intro X Y f; apply ModuleCat.hom_ext
        exact homogeneousKoszulZeroIso_naturality (F.map f).hom k)

/-- Let `F` be a flat diagram of modules and `l < k`. If the Moore complex of
`∧^{p+1} F ⊗ Sym^{k-p-1} F` on `U` has vanishing `Hₙ` whenever `p + n = l`, then the Moore
complex of `Sym^k F` on `U` has vanishing `H_l`. -/
lemma symmetricPowerDiagram_homology_isZero_of_koszul
    (C : Type u) [SmallCategory C] (B : Type w) [CommRing B]
    (U : CosimplicialObject C) (F : Cᵒᵖ ⥤ ModuleCat.{max u w} B)
    (hF : ∀ X, Module.Flat B (F.obj X)) (k l : ℕ) (hl : l < k)
    (hvan : ∀ p n, p + n = l →
      IsZero (((alternatingFaceMapComplex (ModuleCat.{max u w} B)).obj
        (U.op ⋙ homogeneousKoszulDiagram C B F k (p + 1))).homology n)) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max u w} B)).obj
      (U.op ⋙ symmetricPowerDiagram C B F k)).homology l) := by
  let T := (Functor.whiskeringLeft SimplexCategoryᵒᵖ Cᵒᵖ (ModuleCat.{max u w} B)).obj U.op ⋙
    alternatingFaceMapComplex (ModuleCat.{max u w} B) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{max u w} B) (ComplexShape.down ℕ) l
  exact (homogeneousKoszulDiagram_homology_isZero C B U F hF k l hl hvan).of_iso
    (T.mapIso (homogeneousKoszulZeroDiagramIso C B F k)).symm

section TensorExtension

open HomologicalComplex MonoidalCategory

variable {B : Type w} [CommRing B]
/-- The monoidal structure on `ModuleCat.{max w v} B` given by the tensor product of modules. -/
local instance : MonoidalCategoryStruct (ModuleCat.{max w v} B) :=
  ModuleCat.liftedModuleMonoidalStruct
/-- The monoidal category `ModuleCat.{max w v} B` under the tensor product of modules. -/
local instance : MonoidalCategory (ModuleCat.{max w v} B) :=
  ModuleCat.liftedModuleMonoidal
/-- A chain complex indexed by `ℕ`, viewed as a cochain complex indexed by `ℤ` concentrated in
nonpositive degrees, with `K_p` in degree `-p`. -/
abbrev negExtend (K : ChainComplex (ModuleCat.{max w v} B) ℕ) :=
  K.extend ComplexShape.embeddingDownNat
/-- The term of `negExtend K` in degree `-p` is `K_p`. -/
abbrev negExtendIso (K : ChainComplex (ModuleCat.{max w v} B) ℕ) (p : ℕ) :
    (negExtend K).X (-(p : ℤ)) ≅ K.X p :=
  K.extendXIso ComplexShape.embeddingDownNat rfl
/-- The comparison map from the degree `n` term of `K ⊗ L` to the degree `-n` term of
`negExtend K ⊗ negExtend L`. -/
def tensorNegExtendHom
    (K L : ChainComplex (ModuleCat.{max w v} B) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj K L).X n ⟶
      (HomologicalComplex.tensorObj (negExtend K) (negExtend L)).X (-(n : ℤ)) :=
  mapBifunctorDesc (fun p q hpq =>
    ((negExtendIso K p).inv ⊗ₘ (negExtendIso L q).inv) ≫
      ιTensorObj (negExtend K) (negExtend L) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ))
        (by change _ + _ = _ at hpq; omega))
/-- The comparison map from the degree `-n` term of `negExtend K ⊗ negExtend L` to the degree
`n` term of `K ⊗ L`. -/
def tensorNegExtendInv
    (K L : ChainComplex (ModuleCat.{max w v} B) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj (negExtend K) (negExtend L)).X (-(n : ℤ)) ⟶
      (HomologicalComplex.tensorObj K L).X n :=
  mapBifunctorDesc (fun p q hpq =>
    if hp : p ≤ 0 then if hq : q ≤ 0 then
      ((K.extendXIso ComplexShape.embeddingDownNat
          (i := (-p).toNat) (by change -(((-p).toNat : ℕ) : ℤ) = p; omega)).hom ⊗ₘ
        (L.extendXIso ComplexShape.embeddingDownNat
          (i := (-q).toNat) (by change -(((-q).toNat : ℕ) : ℤ) = q; omega)).hom) ≫
        ιTensorObj K L (-p).toNat (-q).toNat n (by change _ + _ = _ at hpq; omega)
    else 0 else 0)

/-- The inclusion of `K_p ⊗ L_q` into `(K ⊗ L)_n`, precomposed with the identifications of the
terms of the extended complexes, does not depend on the indices `pp`, `qq` used to name them. -/
lemma tensorNegExtendInv_term
    (K L : ChainComplex (ModuleCat.{max w v} B) ℕ) (p q n pp qq : ℕ)
    (hp : ComplexShape.embeddingDownNat.f pp = -(p : ℤ))
    (hq : ComplexShape.embeddingDownNat.f qq = -(q : ℤ))
    (h : p + q = n) (hh : pp + qq = n) :
    ((K.extendXIso ComplexShape.embeddingDownNat hp).hom ⊗ₘ
      (L.extendXIso ComplexShape.embeddingDownNat hq).hom) ≫ ιTensorObj K L pp qq n hh =
    ((negExtendIso K p).hom ⊗ₘ (negExtendIso L q).hom) ≫ ιTensorObj K L p q n h := by
  have hpp : pp = p := by change -(pp : ℤ) = -(p : ℤ) at hp; omega
  have hqq : qq = q := by change -(qq : ℤ) = -(q : ℤ) at hq; omega
  subst pp qq
  rfl

/-- `tensorNegExtendInv` sends the summand in degrees `(-p, -q)` to the summand `K_p ⊗ L_q`. -/
lemma tensorNegExtendInv_ι
    (K L : ChainComplex (ModuleCat.{max w v} B) ℕ) (p q n : ℕ) (h : p + q = n) :
    ιTensorObj (negExtend K) (negExtend L) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ))
      (by omega) ≫ tensorNegExtendInv K L n =
    ((negExtendIso K p).hom ⊗ₘ (negExtendIso L q).hom) ≫ ιTensorObj K L p q n h := by
  dsimp only [tensorNegExtendInv]
  rw [ι_mapBifunctorDesc]
  simp only [dite_eq_left (show -(p : ℤ) ≤ 0 by omega),
    dite_eq_left (show -(q : ℤ) ≤ 0 by omega)]
  exact tensorNegExtendInv_term K L p q n _ _ _ _ h _

/-- `tensorNegExtendInv` is a left inverse of `tensorNegExtendHom`. -/
lemma tensorNegExtendHom_inv
    (K L : ChainComplex (ModuleCat.{max w v} B) ℕ) (n : ℕ) :
    tensorNegExtendHom K L n ≫ tensorNegExtendInv K L n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  simp only [tensorNegExtendHom, ι_mapBifunctorDesc_assoc, Category.assoc,
    tensorNegExtendInv_ι K L p q n hpq, tensorHom_comp_tensorHom_assoc,
    Iso.inv_hom_id, id_tensorHom_id, Category.id_comp, Category.comp_id]

/-- `tensorNegExtendInv` is a right inverse of `tensorNegExtendHom`. -/
lemma tensorNegExtendInv_hom
    (K L : ChainComplex (ModuleCat.{max w v} B) ℕ) (n : ℕ) :
    tensorNegExtendInv K L n ≫ tensorNegExtendHom K L n = 𝟙 _ := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  by_cases hp : p ≤ 0
  · by_cases hq : q ≤ 0
    · obtain ⟨p, rfl⟩ : ∃ p' : ℕ, p = -(p' : ℤ) := ⟨(-p).toNat, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q' : ℕ, q = -(q' : ℤ) := ⟨(-q).toNat, by omega⟩
      have hn : p + q = n := by change _ + _ = _ at hpq; omega
      rw [← Category.assoc, tensorNegExtendInv_ι K L p q n hn]
      simp only [tensorNegExtendHom, Category.assoc, ι_mapBifunctorDesc,
        tensorHom_comp_tensorHom_assoc, Iso.hom_inv_id, id_tensorHom_id,
        Category.id_comp, Category.comp_id]
    · have hz : IsZero ((negExtend K).X p ⊗ (negExtend L).X q) :=
        (tensorLeft _).map_isZero (L.isZero_extend_X ComplexShape.embeddingDownNat q
          (by intro i; change -(i : ℤ) ≠ q; omega))
      exact hz.eq_of_src _ _
  · have hz : IsZero ((negExtend K).X p ⊗ (negExtend L).X q) :=
      (tensorRight _).map_isZero (K.isZero_extend_X ComplexShape.embeddingDownNat p
        (by intro i; change -(i : ℤ) ≠ p; omega))
    exact hz.eq_of_src _ _

/-- The isomorphism between the degree `n` term of `K ⊗ L` and the degree `-n` term of
`negExtend K ⊗ negExtend L`. -/
def tensorNegExtendIso
    (K L : ChainComplex (ModuleCat.{max w v} B) ℕ) (n : ℕ) :
    (HomologicalComplex.tensorObj K L).X n ≅
      (HomologicalComplex.tensorObj (negExtend K) (negExtend L)).X (-(n : ℤ)) where
  hom := tensorNegExtendHom K L n
  inv := tensorNegExtendInv K L n
  hom_inv_id := tensorNegExtendHom_inv K L n
  inv_hom_id := tensorNegExtendInv_hom K L n

/-- The sign `ε₁` of the tensor product of complexes of a shape with itself is `1`. -/
lemma tensor_epsilon₁ {I : Type*} [AddMonoid I]
    (c : ComplexShape I) [c.TensorSigns] (p q : I) :
    ComplexShape.ε₁ c c c (p, q) = 1 := rfl

/-- The sign `ε₂` of the tensor product of complexes of a shape with itself at `(p, q)` is
`ε p`. -/
lemma tensor_epsilon₂ {I : Type*} [AddMonoid I]
    (c : ComplexShape I) [c.TensorSigns] (p q : I) :
    ComplexShape.ε₂ c c c (p, q) = c.ε p := rfl

/-- For cochain complexes indexed by `ℤ`, the sign `ε` at `-p` is `(-1)ᵖ`. -/
lemma tensor_epsilon_neg (p : ℕ) :
    (ComplexShape.up ℤ).ε (-(p : ℤ)) = (-1 : ℤˣ) ^ p := by
  change (-(p : ℤ)).negOnePow = _
  rw [Int.negOnePow_neg, Int.negOnePow_def, zpow_natCast]

/-- `tensorNegExtendHom` is compatible with the component `d₁` of the differential coming from
the first factor. -/
lemma tensorNegExtendHom_d₁
    (K L : ChainComplex (ModuleCat.{max w v} B) ℕ) (p q n : ℕ)
    (h : p + q = n + 1) :
    mapBifunctor.d₁ K L (curriedTensor _) (ComplexShape.down ℕ) p q n ≫
        tensorNegExtendHom K L n =
      ((negExtendIso K p).inv ⊗ₘ (negExtendIso L q).inv) ≫
        mapBifunctor.d₁ (negExtend K) (negExtend L) (curriedTensor _)
          (ComplexShape.up ℤ) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) := by
  cases p with
  | zero =>
      rw [mapBifunctor.d₁_eq_zero K L _ _ _ _ _ (by simp), zero_comp]
      rw [mapBifunctor.d₁_eq _ _ _ _ (i₁' := 1) (by simp) _ _ (by dsimp; omega)]
      simp only [Nat.cast_zero, neg_zero]
      rw [K.extend_d_from_eq_zero ComplexShape.embeddingDownNat (-((0 : ℕ) : ℤ)) 1 0 rfl (by simp)]
      simp
  | succ p =>
      rw [mapBifunctor.d₁_eq K L _ _ (i₁' := p) rfl _ _ (by dsimp; omega),
        mapBifunctor.d₁_eq _ _ _ _ (i₁' := -(p : ℤ)) (by change _ + 1 = _; push_cast; omega)
          _ _ (by dsimp; omega)]
      simp only [tensor_epsilon₁, one_smul, Category.assoc,
        tensorNegExtendHom, ι_mapBifunctorDesc]
      change (K.d (p + 1) p ▷ L.X q) ≫
          ((negExtendIso K p).inv ⊗ₘ (negExtendIso L q).inv) ≫ _ =
        ((negExtendIso K (p + 1)).inv ⊗ₘ (negExtendIso L q).inv) ≫
          ((negExtend K).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ▷ (negExtend L).X (-(q : ℤ))) ≫ _
      rw [← tensorHom_id, ← tensorHom_id, tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc]
      rw [K.extend_d_eq ComplexShape.embeddingDownNat (i := p + 1) (j := p)
        (i' := -((p + 1 : ℕ) : ℤ)) (j' := -(p : ℤ)) rfl rfl]
      simp [negExtendIso]

/-- `tensorNegExtendHom` is compatible with the component `d₂` of the differential coming from
the second factor. -/
lemma tensorNegExtendHom_d₂
    (K L : ChainComplex (ModuleCat.{max w v} B) ℕ) (p q n : ℕ)
    (h : p + q = n + 1) :
    mapBifunctor.d₂ K L (curriedTensor _) (ComplexShape.down ℕ) p q n ≫
        tensorNegExtendHom K L n =
      ((negExtendIso K p).inv ⊗ₘ (negExtendIso L q).inv) ≫
        mapBifunctor.d₂ (negExtend K) (negExtend L) (curriedTensor _)
          (ComplexShape.up ℤ) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) := by
  cases q with
  | zero =>
      rw [mapBifunctor.d₂_eq_zero K L _ _ _ _ _ (by simp), zero_comp]
      rw [mapBifunctor.d₂_eq _ _ _ _ _ (i₂' := 1) (by simp) _ (by dsimp; omega)]
      simp only [Nat.cast_zero, neg_zero]
      rw [L.extend_d_from_eq_zero ComplexShape.embeddingDownNat (-((0 : ℕ) : ℤ)) 1 0 rfl (by simp)]
      simp
  | succ q =>
      rw [mapBifunctor.d₂_eq K L _ _ _ (i₂' := q) rfl _ (by dsimp; omega),
        mapBifunctor.d₂_eq _ _ _ _ _ (i₂' := -(q : ℤ)) (by change _ + 1 = _; push_cast; omega)
          _ (by dsimp; omega)]
      simp only [tensor_epsilon₂, tensor_epsilon_neg, ComplexShape.ε_down_ℕ, Linear.units_smul_comp,
        Linear.comp_units_smul, Category.assoc, tensorNegExtendHom, ι_mapBifunctorDesc]
      congr 1
      change (K.X p ◁ L.d (q + 1) q) ≫
          ((negExtendIso K p).inv ⊗ₘ (negExtendIso L q).inv) ≫ _ =
        ((negExtendIso K p).inv ⊗ₘ (negExtendIso L (q + 1)).inv) ≫
          ((negExtend K).X (-(p : ℤ)) ◁ (negExtend L).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ))) ≫ _
      rw [← id_tensorHom, ← id_tensorHom, tensorHom_comp_tensorHom_assoc,
        tensorHom_comp_tensorHom_assoc]
      rw [L.extend_d_eq ComplexShape.embeddingDownNat (i := q + 1) (j := q)
        (i' := -((q + 1 : ℕ) : ℤ)) (j' := -(q : ℤ)) rfl rfl]
      simp [negExtendIso]

/-- `tensorNegExtendHom` commutes with the differentials of `K ⊗ L` and of
`negExtend K ⊗ negExtend L`. -/
lemma tensorNegExtendHom_comm
    (K L : ChainComplex (ModuleCat.{max w v} B) ℕ) (n : ℕ) :
    tensorNegExtendHom K L (n + 1) ≫
      (HomologicalComplex.tensorObj (negExtend K) (negExtend L)).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
    (HomologicalComplex.tensorObj K L).d (n + 1) n ≫ tensorNegExtendHom K L n := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  rw [← Category.assoc]
  simp only [tensorNegExtendHom, ι_mapBifunctorDesc]
  simp only [mapBifunctor.d_eq, Category.assoc, Preadditive.comp_add, Preadditive.add_comp,
    mapBifunctor.ι_D₁, mapBifunctor.ι_D₂, mapBifunctor.ι_D₁_assoc, mapBifunctor.ι_D₂_assoc]
  exact congrArg₂ (· + ·) (tensorNegExtendHom_d₁ K L p q n hpq).symm
    (tensorNegExtendHom_d₂ K L p q n hpq).symm

/-- The tensor product `K ⊗ L` of chain complexes indexed by `ℕ` is isomorphic to the restriction
to nonpositive degrees of `negExtend K ⊗ negExtend L`. -/
def tensorNegExtendComplexIso
    (K L : ChainComplex (ModuleCat.{max w v} B) ℕ) :
    HomologicalComplex.tensorObj K L ≅
      (HomologicalComplex.tensorObj (negExtend K) (negExtend L)).restriction
        ComplexShape.embeddingDownNat :=
  Hom.isoOfComponents (fun n => tensorNegExtendIso K L n) (by
    intro i j hij
    have h : j + 1 = i := hij
    subst i
    exact tensorNegExtendHom_comm K L j)

/-- For `n > 0`, `Hₙ(K ⊗ L) ≅ H^{-n}(negExtend K ⊗ negExtend L)`. -/
def tensorNegExtendHomologyIso
    (K L : ChainComplex (ModuleCat.{max w v} B) ℕ) (n : ℕ) (hn : 0 < n) :
    (HomologicalComplex.tensorObj K L).homology n ≅
      (HomologicalComplex.tensorObj (negExtend K) (negExtend L)).homology (-(n : ℤ)) :=
  (homologyFunctor _ (ComplexShape.down ℕ) n).mapIso (tensorNegExtendComplexIso K L) ≪≫
    restrictionHomologyIso _ ComplexShape.embeddingDownNat (n + 1) n (n - 1)
      (by simp) (by cases n <;> simp) rfl rfl rfl
      (by simp; omega) (by simp; omega)

end TensorExtension
/-- If a chain complex `K` indexed by `ℕ` has `Hₙ(K) = 0` for `n < a`, then its extension to a
cochain complex indexed by `ℤ` has cohomology in degrees `≤ -a`. -/
lemma extend_isLE_of_homology_vanishing
    {B : Type w} [CommRing B] (K : ChainComplex (ModuleCat.{max u w} B) ℕ)
    (a : ℕ) (h : ∀ n, n < a → IsZero (K.homology n)) :
    CochainComplex.IsLE (K.extend ComplexShape.embeddingDownNat) (-(a : ℤ)) := by
  rw [CochainComplex.isLE_iff]
  intro i hi
  by_cases hi' : 0 < i
  · exact (K.extend ComplexShape.embeddingDownNat).exactAt_of_isSupported
      (ComplexShape.embeddingUpIntLE 0) i
      (by simpa only [ComplexShape.notMem_range_embeddingUpIntLE_iff] using hi')
  · let n := (-i).toNat
    have hn : -(n : ℤ) = i := by dsimp [n]; omega
    exact ((K.extend ComplexShape.embeddingDownNat).exactAt_iff_isZero_homology i).mpr
      ((h n (by omega)).of_iso
        (K.extendHomologyIso ComplexShape.embeddingDownNat hn))

/-- The extension to `ℤ` of a chain complex of flat modules consists of flat modules. -/
lemma extend_module_flat
    {B : Type w} [CommRing B] (K : ChainComplex (ModuleCat.{max u w} B) ℕ)
    (h : ∀ n, Module.Flat B (K.X n)) (i : ℤ) :
    Module.Flat B ((K.extend ComplexShape.embeddingDownNat).X i) := by
  by_cases hi : ∃ n : ℕ, -(n : ℤ) = i
  · obtain ⟨n, hn⟩ := hi
    have := h n
    exact Module.Flat.of_linearEquiv
      (K.extendXIso ComplexShape.embeddingDownNat hn).toLinearEquiv
  · have : Subsingleton ((K.extend ComplexShape.embeddingDownNat).X i) :=
      ModuleCat.subsingleton_of_isZero
        (K.isZero_extend_X ComplexShape.embeddingDownNat i (by simpa using hi))
    infer_instance

/-- Let `K` and `L` be chain complexes of flat modules indexed by `ℕ` with `Hₙ(K) = 0` for
`n < a` and `Hₙ(L) = 0` for `n < b`. Then the tensor product of their extensions to `ℤ` has
cohomology in degrees `≤ -a - b`. -/
lemma tensor_extend_isLE
    {B : Type w} [CommRing B] (K L : ChainComplex (ModuleCat.{max u w} B) ℕ)
    (hK : ∀ n, Module.Flat B (K.X n)) (hL : ∀ n, Module.Flat B (L.X n))
    (a b : ℕ) (ha : ∀ n, n < a → IsZero (K.homology n))
    (hb : ∀ n, n < b → IsZero (L.homology n)) :
    (CochainComplex.DerivedTensor.tensorComplex
      (K.extend ComplexShape.embeddingDownNat)
      (L.extend ComplexShape.embeddingDownNat)).IsLE (-(a : ℤ) - (b : ℤ)) := by
  let P : CochainComplex (ModuleCat.{max u w} B) ℤ := K.extend ComplexShape.embeddingDownNat
  let Q : CochainComplex (ModuleCat.{max u w} B) ℤ := L.extend ComplexShape.embeddingDownNat
  have : P.IsLE (-(a : ℤ)) := extend_isLE_of_homology_vanishing K a ha
  have : Q.IsLE (-(b : ℤ)) := extend_isLE_of_homology_vanishing L b hb
  have hflat (K : ChainComplex (ModuleCat.{max u w} B) ℕ) (hK : ∀ n, Module.Flat B (K.X n)) :
      CochainComplex.DerivedTensor.IsKFlat (K.extend ComplexShape.embeddingDownNat) := by
    apply (CochainComplex.DerivedTensor.isKFlat_iff_kFlat _).mpr
    have (i : ℤ) := extend_module_flat K hK i
    exact CochainComplex.KFlat.kFlat_of_flat _ 0
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProductGeneral.{w, u} B
  have := derivedTensor_isLE T (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q)
    (-(a : ℤ)) (-(b : ℤ))
  have hz := DerivedCategory.TStructure.t.isLE_of_iso (T.comparison P Q (hflat K hK) (hflat L hL))
    (-(a : ℤ) + -(b : ℤ))
  have hz' : (DerivedCategory.Q.obj
      (CochainComplex.DerivedTensor.tensorComplex P Q)).IsLE (-(a : ℤ) + -(b : ℤ)) := hz
  rwa [DerivedCategory.isLE_Q_obj_iff, ← sub_eq_add_neg] at hz'

/-- If the Moore complex of a simplicial module `M` has vanishing `H₀`, then so does that of the
degreewise tensor product `M ⊗ N`. -/
lemma simplicialTensor_homology_zero
    {B : Type w} [CommRing B]
    (M N : SimplicialObject (ModuleCat.{max u w} B))
    (hM : IsZero (((alternatingFaceMapComplex _).obj M).homology 0)) :
    IsZero (((alternatingFaceMapComplex _).obj
      (MonoidalCategory.tensorObj M N)).homology 0) := by
  apply (alternatingFaceMap_homology_zero_iff _).mpr
  have hsurj := (alternatingFaceMap_homology_zero_iff M).mp hM
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul x y =>
      obtain ⟨z, hz⟩ := hsurj x
      refine ⟨z ⊗ₜ[B] N.σ (0 : Fin 1) y, ?_⟩
      change M.δ (0 : Fin 2) z ⊗ₜ[B] N.δ (0 : Fin 2) (N.σ (0 : Fin 1) y) -
        M.δ (1 : Fin 2) z ⊗ₜ[B] N.δ (1 : Fin 2) (N.σ (0 : Fin 1) y) = x ⊗ₜ[B] y
      rw [show N.δ (0 : Fin 2) (N.σ (0 : Fin 1) y) = y from
        ConcreteCategory.congr_hom (N.δ_comp_σ_self (i := (0 : Fin 1))) y,
        show N.δ (1 : Fin 2) (N.σ (0 : Fin 1) y) = y from
        ConcreteCategory.congr_hom (N.δ_comp_σ_succ (i := (0 : Fin 1))) y,
        ← TensorProduct.sub_tmul]
      exact congrArg (fun z => z ⊗ₜ[B] y) hz
  | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩

/-- Let `M` be a degreewise flat simplicial module whose Moore complex has vanishing `H₀`, and
let `N` be a simplicial module whose Moore complex has vanishing `Hᵢ` for `i < b`. Then the
Moore complex of `M ⊗ N` has vanishing `Hₙ` for `n ≤ b`. -/
lemma simplicialTensor_homology_isZero
    {B : Type w} [CommRing B]
    (M N : SimplicialObject (ModuleCat.{max u w} B))
    (hMflat : ∀ i, Module.Flat B (M.obj i))
    (hM : IsZero (((alternatingFaceMapComplex _).obj M).homology 0))
    (b n : ℕ) (hN : ∀ i, i < b →
      IsZero (((alternatingFaceMapComplex _).obj N).homology i)) (hn : n < b + 1) :
    IsZero (((alternatingFaceMapComplex _).obj
      (MonoidalCategory.tensorObj M N)).homology n) :=
  StacksDraft.SimplicialTensor.isZero_homology_tensor_of_lt M N hMflat
    (fun N' => simplicialTensor_homology_zero M N' hM) b n hN hn

/-- Let `F` be a flat diagram of modules whose Moore complex on `U` has vanishing `H₀`. Then the
Moore complex of `Sym^k F` on `U` has vanishing `H_l` for `l < k`. -/
lemma symmetricPowerDiagram_homology_vanishing
    (C : Type u) [SmallCategory C] (B : Type w) [CommRing B]
    (U : CosimplicialObject C) (F : Cᵒᵖ ⥤ ModuleCat.{max u w} B)
    (hF : ∀ X, Module.Flat B (F.obj X))
    (h₀ : IsZero (((alternatingFaceMapComplex (ModuleCat.{max u w} B)).obj
      (U.op ⋙ F)).homology 0)) (k l : ℕ) (hl : l < k) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max u w} B)).obj
      (U.op ⋙ symmetricPowerDiagram C B F k)).homology l) := by
  induction k using Nat.strong_induction_on generalizing l with
  | h k ih =>
      apply symmetricPowerDiagram_homology_isZero_of_koszul C B U F hF k l hl
      intro p n hpn
      let M := U.op ⋙ exteriorPowerDiagram C B F (p + 1)
      let N := U.op ⋙ symmetricPowerDiagram C B F (k - (p + 1))
      change IsZero (((alternatingFaceMapComplex _).obj
        (MonoidalCategory.tensorObj M N)).homology n)
      apply simplicialTensor_homology_isZero M N
        (fun i => by
          have := hF (U.op.obj i)
          exact exteriorPower_flat B _ (p + 1))
        (exteriorPowerDiagram_homology_zero C B U F h₀ (p + 1) (by omega))
        (k - (p + 1)) n
      · intro j hj
        exact ih (k - (p + 1)) (by omega) j hj
      · omega

/-- Let `C` be a small category with the chaotic topology, `B` a commutative ring, `U_•` a
cosimplicial object of `C`, and `F` a `B̲`-module on `C`, that is a diagram
`F : Cᵒᵖ ⥤ ModuleCat B`, which is flat, meaning that every module of sections is flat. If the
Moore complex of `F(U_•)` has vanishing homology in degree zero, then the Moore complex of
`Sym^k_{B̲}(F)(U_•)` has vanishing homology in every degree `l < k`. The hypothesis `_hEZ` is
not needed for the conclusion. -/
theorem isZero_homology_symmetricPowerDiagram_of_lt
    (C : Type u) [SmallCategory C] (B : Type w) [CommRing B]
    (_hEZ : FlatEilenbergZilber.{u, w} B)
    (U : CosimplicialObject C) (F : Cᵒᵖ ⥤ ModuleCat.{max u w} B)
    (hF : ∀ X, Module.Flat B (F.obj X))
    (h₀ : IsZero (((alternatingFaceMapComplex (ModuleCat.{max u w} B)).obj
      (U.op ⋙ F)).homology 0)) (k l : ℕ) (hl : l < k) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max u w} B)).obj
      (U.op ⋙ symmetricPowerDiagram C B F k)).homology l) :=
  symmetricPowerDiagram_homology_vanishing C B U F hF h₀ k l hl

/-- Let `C` be a small category with the chaotic topology, let `B` be a commutative ring and let
`F` be a `B̲`-module on `C` — that is, a diagram `F : Cᵒᵖ ⥤ ModuleCat B`, every presheaf being
a sheaf for the chaotic topology — which is flat, meaning that every module of sections is flat.
Assume `C` carries a cosimplicial object `U_•` which is a point resolution, as in Tag 08Q9, and
that `H_0(C, F) = 0`. Then `H_l(C, Sym^k_{B̲}(F)) = 0` for every `l < k`.

Here `H_l(C, -) = L_lπ_!` is the `l`th left derived functor of the colimit over `Cᵒᵖ`, as in
Tag 08PF, read at linear coefficients. -/
@[stacks 08RD "No hypothesis beyond the source statement: C is any small category, H_l(C, -) \
is L_l of the colimit over Cᵒᵖ at linear coefficients, which is Tag 08PF's definition of the \
homology of a category, the B-module F on the chaotic site is the diagram F, flat means that \
every module of sections is flat, Sym^k is the sectionwise symmetric power, U is a point \
resolution as in Tag 08Q9, and the induction on k over the Koszul resolution is carried out in \
full for every k. The Künneth input of the source proof, the Eilenberg-Zilber comparison of \
Tag 08QD, is replaced by the weaker vanishing statement \
`StacksDraft.SimplicialTensor.isZero_homology_tensor_of_lt`, which is proved here."]
theorem isZero_leftDerivedColim_symmetricPowerDiagram_of_lt
    (C : Type u) [SmallCategory C] (B : Type u) [CommRing B]
    (U : CosimplicialObject C) (hU : IsPointResolution U)
    (F : Cᵒᵖ ⥤ ModuleCat.{u} B) (hF : ∀ X, Module.Flat B (F.obj X))
    (h₀ : IsZero (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived 0).obj F))
    (k l : ℕ) (hl : l < k) :
    IsZero (((colim : (Cᵒᵖ ⥤ ModuleCat.{u} B) ⥤ ModuleCat.{u} B).leftDerived l).obj
      (symmetricPowerDiagram C B F k)) := by
  have h₀' : IsZero (((alternatingFaceMapComplex (ModuleCat.{u} B)).obj
      (U.op ⋙ F)).homology 0) :=
    h₀.of_iso ((ModuleValued.moduleLeftDerivedColimitNatIso U hU 0).app F).symm
  exact (symmetricPowerDiagram_homology_vanishing C B U F hF h₀' k l hl).of_iso
    ((ModuleValued.moduleLeftDerivedColimitNatIso U hU l).app (symmetricPowerDiagram C B F k))

end Stacks.ChaoticSite

end
