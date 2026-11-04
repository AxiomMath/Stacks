module

public import Mathlib.Algebra.Category.FGModuleCat.Abelian
import all StacksFrontier.Homology.DerivedComplete.CompleteKoszulPowers
public import StacksFrontier.Homology.DerivedComplete.CompleteKoszulPowers
public import StacksFrontier.Homology.DerivedComplete.NoetherianKoszulProIso
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.FullSubcategory
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Localization
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Ring.Shrink
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import Mathlib.CategoryTheory.Functor.KanExtension.Basic
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Limits.Constructions.EventuallyConstant
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.Data.Int.Interval
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic
public import StacksCore.Algebra.Homology.TotalComplex
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.DerivedCategory.EssentiallyConstant
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Algebra.Homology.SpectralSequence.DoubleComplex
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.KFlat.LargeUniverse
public import StacksFrontier.Homology.KFlat.QuasiIso
public import StacksFrontier.Homology.LiftAcyclicComplex
public import StacksFrontier.Homology.TensorComplex.ExactFunctor
public import StacksFrontier.Homology.TensorComplex.Monoidal
public import StacksFrontier.Homology.TorAmplitude.Defs
public import StacksFrontier.RingTheory.Koszul.Defs
public import StacksFrontier.RingTheory.Koszul.Homotopy
public import StacksFrontier.RingTheory.Koszul.Functoriality
public import StacksFrontier.RingTheory.Koszul.Relations
public import StacksFrontier.RingTheory.Module.AdicSystem.Homology
public import StacksFrontier.Homology.PseudoCoherent.Relative.PolynomialRetract
public import StacksFrontier.Homology.TwoTermComplex.BaseChange
import StacksFrontier.Homology.DerivedComplete.NoetherianKoszulProIso

/-!
# Ideal powers, Koszul complexes and adic reduction in the derived category

Let `I` be an ideal of a Noetherian ring `A`.  This file proves two pro-isomorphisms of
inverse systems in the derived category `D(A)` attached to the powers of `I`.

The first compares the positive powers `I^(n+1)`, viewed as complexes concentrated in degree
zero, with the shifted positive-degree parts of the Koszul complexes on the powered sequences
`f_i^(n+1)`, for a finite sequence `f` generating `I`.  The comparison is induced by the
Koszul differential in degree one.

The second compares, for a bounded complex `M` of finite `A`-modules, the derived reductions of
`M` modulo the powers of `I` with its degreewise reductions `M/I^n M`.  The derived reduction
is computed by reducing a bounded-above finite-free resolution of `M`.

## Main definitions

* `Stacks.AdicSystem.KoszulIdealPower.koszulIdealComplex` is the shifted positive-degree part of a
  Koszul complex, the
  complex written `sigma_{<= -1} K[-1]` in the source's cohomological convention.
* `Stacks.AdicSystem.KoszulIdealPower.koszulIdealComplexSystem` is the resulting inverse system in
  `D(A)`.
* `Stacks.AdicSystem.KoszulIdealPower.idealPowerSystem` is the inverse system of positive ideal
  powers in degree zero.
* `Stacks.AdicSystem.DerivedReductionProIso.reductionNatTrans` compares reduction modulo two nested
  ideals.
* `Stacks.AdicSystem.DerivedReductionProIso.adicReductionTransition` and
  `Stacks.AdicSystem.DerivedReductionProIso.adicReductionComparison` are the
  transition maps and the level-wise comparison maps of the second pro-isomorphism.

## Main results

* `Stacks.AdicSystem.KoszulIdealPower.idealPowerSystem_proIso_koszulIdealComplexSystem` (tag 0G3M)
  gives the canonical
  comparison of the ideal-power and truncated-Koszul systems together with a two-sided inverse
  after cofinal refinement.
* `Stacks.AdicSystem.DerivedReductionProIso.derivedReduction_proIsomorphic_adicReduction` (tag
  0G9M) produces the
  bounded-above finite-free resolution and shows that the comparison from its reductions to the
  degreewise reductions of `M` is a pro-isomorphism.

## Implementation notes

The source uses cohomological degrees for the Koszul complex; we use Mathlib's homological
one, so its degree `j` is the Koszul complex's degree `j + 1`.  Positive powers are indexed by
`n : Nat` using exponent `n + 1`.  Since Mathlib has no category of pro-objects,
pro-isomorphism is expressed by a natural comparison whose components acquire two-sided
inverses after passing to a later level, as in tag 0G3D.

Three inputs of these two tags are developed in a section of this file rather than imported,
because their conceptual homes do not yet exist: the inverse system of Koszul complexes on
powers of a sequence (tag 0BKC), the scalar null-homotopies on a Koszul complex (tag 0663), and
the pro-isomorphism of the Koszul power system with the system of quotients (tag 0921).  None
of those tags is registered here; this file provides tags 0G3M and 0G9M only.

The remaining inputs of tag 0G9M are imported: the symmetric monoidal structure on cochain
complexes (tag 0FNI) and the exactness of the tensor-total functor (tag 06Y8) from
`StacksDraft.Homology.TensorComplex`, and K-flatness of a bounded-above complex of flat
modules (tag 064K) together with its preservation of quasi-isomorphisms (tag 06Y0) from
`StacksDraft.Homology.KFlat`.  The latter two are stated there for a module universe above the
ring's, which is the generality at which `CochainComplex.KFlat` is defined; this file uses them
at the instance where the module universe and the ring's coincide.

## References

* [Stacks Project, Tag 0G3M](https://stacks.math.columbia.edu/tag/0G3M)
* [Stacks Project, Tag 0G9M](https://stacks.math.columbia.edu/tag/0G9M)
-/

@[expose] public section

-- The replayed proofs were written under this setting: the Koszul transition maps are
-- restricted exterior-power maps, and the total-complex braiding is a sum over bidegrees,
-- both of which are elaboration-intensive to normalize.
set_option maxRecDepth 4096

universe u

/-! ## Tag 0G3M -/

namespace Stacks.AdicSystem.KoszulIdealPower

open CategoryTheory CategoryTheory.Limits Opposite

/-- The shifted positive-degree part of the Koszul complex. In the source's cohomological
convention this is `σ_{≤ -1} K^•[-1]`. -/
public noncomputable def koszulIdealComplex
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    ChainComplex (ModuleCat.{u} A) ℕ :=
  let K := Koszul.seqComplex f
  ChainComplex.of (fun j ↦ K.X (j + 1))
    (fun j ↦ K.d (j + 2) (j + 1))
    (fun j ↦ K.d_comp_d (j + 3) (j + 2) (j + 1))

/-- The degree `j` term of the shifted positive-degree part is the degree `j + 1` term of the
original Koszul complex. -/
public noncomputable def koszulIdealComplexXIso
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (j : ℕ) :
    (koszulIdealComplex f).X j ≅ (Koszul.seqComplex f).X (j + 1) :=
  eqToIso (by rfl)

/-- The map on shifted positive-degree Koszul complexes induced by a map of Koszul complexes. -/
public noncomputable def koszulIdealComplexMap
    {A : Type u} [CommRing A] {r : ℕ} {f g : Fin r → A}
    (φ : Koszul.seqComplex f ⟶ Koszul.seqComplex g) :
    koszulIdealComplex f ⟶ koszulIdealComplex g :=
  ChainComplex.ofHom (fun j ↦ φ.f (j + 1)) (fun j ↦ by
    simpa only [koszulIdealComplex, ChainComplex.of_d, Nat.add_assoc, Nat.reduceAdd] using
      φ.comm (j + 2) (j + 1))

/-- The inverse system in `D(A)` formed by the shifted positive-degree parts of the Koszul
complexes on the positive powers of a finite sequence. -/
public noncomputable def koszulIdealComplexSystem
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Functor.ofOpSequence
    (X := fun n ↦ DerivedCategory.Q.obj
      ((koszulIdealComplex (fun i ↦ f i ^ (n + 1))).extend
        ComplexShape.embeddingDownNat))
    (fun n ↦ DerivedCategory.Q.map
      (HomologicalComplex.extendMap
        (koszulIdealComplexMap
          (NoetherianKoszulProIso.koszulPowerTransition f (n + 1) n (Nat.le_succ n)))
        ComplexShape.embeddingDownNat))

/-- The canonical inclusion between two powers of an ideal. -/
public def idealPowerTransition
    {A : Type u} [CommRing A] (I : Ideal A) (m n : ℕ) (h : n ≤ m) :
    ModuleCat.of A ↥(I ^ (m + 1)) ⟶ ModuleCat.of A ↥(I ^ (n + 1)) :=
  ModuleCat.ofHom (Submodule.inclusion (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))

/-- The inverse system in `D(A)` formed by the positive powers of an ideal, regarded as complexes
concentrated in degree zero. -/
public noncomputable def idealPowerSystem
    {A : Type u} [CommRing A] (I : Ideal A) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Functor.ofOpSequence
    (X := fun n ↦ DerivedCategory.Q.obj
      (((ChainComplex.single₀ (ModuleCat.{u} A)).obj
        (ModuleCat.of A ↥(I ^ (n + 1)))).extend ComplexShape.embeddingDownNat))
    (fun n ↦ DerivedCategory.Q.map
      (HomologicalComplex.extendMap
        ((ChainComplex.single₀ (ModuleCat.{u} A)).map
          (idealPowerTransition I (n + 1) n (Nat.le_succ n)))
        ComplexShape.embeddingDownNat))
section IdealPowerProIso

set_option backward.isDefEq.respectTransparency false

/-- The Koszul differential with codomain restricted to an ideal containing the sequence. -/
private noncomputable def koszulIdealDifferential
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (J : Ideal A) (hf : ∀ i, f i ∈ J) :
    (koszulIdealComplex f).X 0 ⟶ ModuleCat.of A J := by
  let d : (koszulIdealComplex f).X 0 ⟶ ModuleCat.of A A :=
    (koszulIdealComplexXIso f 0).hom ≫
      (Koszul.seqComplex f).d 1 0 ≫
      ModuleCat.ofHom (exteriorPower.zeroEquiv A (Fin r → A)).toLinearMap
  refine ModuleCat.ofHom (LinearMap.codRestrict J d.hom ?_)
  intro x
  change (exteriorPower.zeroEquiv A (Fin r → A))
    (Koszul.d (Koszul.seqDual f) 0 x) ∈ J
  rw [Koszul.zeroEquiv_d_zero, Koszul.seqDual_apply]
  exact Submodule.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (hf i)

/-- The canonical map from the positive part of a Koszul complex to an ideal containing its
defining sequence. -/
private noncomputable def koszulIdealComparison
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (J : Ideal A) (hf : ∀ i, f i ∈ J) :
    koszulIdealComplex f ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A J) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨koszulIdealDifferential f J hf, by
      apply ModuleCat.hom_ext
      ext x
      change (exteriorPower.zeroEquiv A (Fin r → A))
        (Koszul.d (Koszul.seqDual f) 0
          (Koszul.d (Koszul.seqDual f) 1 x)) = 0
      have h := (Koszul.seqComplex f).d_comp_d 2 1 0
      have hx := congrArg (fun q => (ModuleCat.Hom.hom q) x) h
      change (Koszul.d (Koszul.seqDual f) 0)
        ((Koszul.d (Koszul.seqDual f) 1) x) = 0 at hx
      exact congrArg (exteriorPower.zeroEquiv A (Fin r → A)) hx |>.trans (map_zero _)⟩

private theorem koszulIdealDifferential_subtype
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (J : Ideal A) (hf : ∀ i, f i ∈ J) :
    koszulIdealDifferential f J hf ≫ ModuleCat.ofHom J.subtype =
      (koszulIdealComplexXIso f 0).hom ≫
        (Koszul.seqComplex f).d 1 0 ≫
        ModuleCat.ofHom (exteriorPower.zeroEquiv A (Fin r → A)).toLinearMap := by
  apply ModuleCat.hom_ext
  ext x
  rfl

private theorem koszulIdealComparison_f_zero
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (J : Ideal A) (hf : ∀ i, f i ∈ J) :
    (koszulIdealComparison f J hf).f 0 = koszulIdealDifferential f J hf := by
  exact ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

set_option backward.isDefEq.respectTransparency false in
private theorem koszulPowerTransition_f_zero
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
    (m n : ℕ) (h : n ≤ m) :
    (NoetherianKoszulProIso.koszulPowerTransition f m n h).f 0 = 𝟙 _ := by
  apply ModuleCat.hom_ext
  ext x
  change (⋀[A]^0 (Fin r → A)) at x
  let g : ⋀[A]^0 (Fin r → A) :=
    ⟨ExteriorAlgebra.ιMulti A 0 (fun i : Fin 0 ↦ Fin.elim0 i),
      Koszul.ιMulti_mem 0 _⟩
  have hg : exteriorPower.zeroEquiv A (Fin r → A) g = 1 := by
    apply Koszul.zeroEquiv_eq_of_coe
    simp [g, ExteriorAlgebra.ιMulti]
  have hx : x = (exteriorPower.zeroEquiv A (Fin r → A) x) • g := by
    apply (exteriorPower.zeroEquiv A (Fin r → A)).injective
    simp [hg]
  have htg := NoetherianKoszulProIso.koszulPowerTransition_apply_ιMulti f m n h 0
    (fun i : Fin 0 ↦ Fin.elim0 i)
  have htg' : (NoetherianKoszulProIso.koszulPowerTransition f m n h).f 0 g = g := by
    rw [htg]
    apply Subtype.ext
    simp [g, ExteriorAlgebra.ιMulti]
  rw [hx]
  change (NoetherianKoszulProIso.koszulPowerTransition f m n h).f 0
      ((exteriorPower.zeroEquiv A (Fin r → A)) x • g) =
    (exteriorPower.zeroEquiv A (Fin r → A)) x • g
  rw [map_smul, htg']

private theorem generatorPower_mem_idealPower
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (n : ℕ) (i : Fin r) :
    f i ^ (n + 1) ∈ (Ideal.span (Set.range f)) ^ (n + 1) :=
  Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

set_option backward.isDefEq.respectTransparency false in
private theorem koszulIdealComparison_naturality
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (n : ℕ) :
    let I := Ideal.span (Set.range f)
    koszulIdealComplexMap
        (NoetherianKoszulProIso.koszulPowerTransition f (n + 1) n (Nat.le_succ n)) ≫
      koszulIdealComparison (fun i ↦ f i ^ (n + 1)) (I ^ (n + 1))
        (generatorPower_mem_idealPower f n) =
      koszulIdealComparison (fun i ↦ f i ^ (n + 2)) (I ^ (n + 2))
          (generatorPower_mem_idealPower f (n + 1)) ≫
        (ChainComplex.single₀ (ModuleCat.{u} A)).map
          (idealPowerTransition I (n + 1) n (Nat.le_succ n)) := by
  dsimp only
  apply (ChainComplex.toSingle₀Equiv _ _).injective
  apply Subtype.ext
  simp only [ChainComplex.toSingle₀Equiv_apply_coe, HomologicalComplex.comp_f,
    ChainComplex.single₀_map_f_zero]
  apply ModuleCat.hom_ext
  ext x
  apply Subtype.ext
  have hcomm := (NoetherianKoszulProIso.koszulPowerTransition f (n + 1) n
    (Nat.le_succ n)).comm 1 0
  simp only [koszulIdealComparison_f_zero]
  let z : (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))).X 0 ⟶
      ModuleCat.of A A :=
    ModuleCat.ofHom (exteriorPower.zeroEquiv A (Fin r → A)).toLinearMap
  have hh := congrArg (fun q => q ≫ z) hcomm
  rw [koszulPowerTransition_f_zero, Category.comp_id] at hh
  change ((NoetherianKoszulProIso.koszulPowerTransition f (n + 1) n
      (Nat.le_succ n)).f 1 ≫
      (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))).d 1 0 ≫ z) x =
    ((Koszul.seqComplex (fun i ↦ f i ^ (n + 2))).d 1 0 ≫
      z) x
  exact ConcreteCategory.congr_hom hh x

/-- The canonical comparison of the two inverse systems. -/
private noncomputable def koszulIdealComparisonSystem
    {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) :
    koszulIdealComplexSystem f ⟶ idealPowerSystem (Ideal.span (Set.range f)) :=
  NatTrans.ofOpSequence
    (fun n ↦ DerivedCategory.Q.map
      (HomologicalComplex.extendMap
        (koszulIdealComparison (fun i ↦ f i ^ (n + 1))
          ((Ideal.span (Set.range f)) ^ (n + 1))
          (generatorPower_mem_idealPower f n))
        ComplexShape.embeddingDownNat))
    (fun n ↦ by
      simp only [koszulIdealComplexSystem, idealPowerSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
      rw [← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp,
        koszulIdealComparison_naturality])

/-- The derived homology of a cochain complex vanishes in a degree where the complex does. -/
private theorem isZero_homology_Q_obj_of_isZero_X
    {R : Type u} [CommRing R] (E : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ)
    (hX : IsZero (E.X i)) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj (DerivedCategory.Q.obj E)) :=
  ((E.sc i).isZero_homology_of_isZero_X₂ hX).of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app E)

private theorem NoetherianKoszulProIso.homologyFunctor_quotientPowerSystem_isZero_of_ne_zero
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (i : ℤ) (hi : i ≠ 0) (n : ℕ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((NoetherianKoszulProIso.quotientPowerSystem f).obj (op n))) := by
  let Q := ModuleCat.of R (R ⧸ Ideal.span (Set.range fun j => f j ^ (n + 1)))
  let E := ((ChainComplex.single₀ (ModuleCat.{u} R)).obj Q).extend
    ComplexShape.embeddingDownNat
  have hE := NoetherianKoszulProIso.single_extendDown_isZero_homology_of_ne_zero Q i hi
  change IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
    (DerivedCategory.Q.obj E))
  exact hE.of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app E)

private theorem koszulPowerTransition_id
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (n : ℕ) :
    NoetherianKoszulProIso.koszulPowerTransition f n n (le_refl n) = 𝟙 _ := by
  unfold NoetherianKoszulProIso.koszulPowerTransition
  rcases Classical.choose_spec (koszulPowerComplexes_form_inverseSystem f) with
    ⟨σ, e, η, hid, hcomp, hsid, hscomp, hformula, hη, hητ, hσ, he, hlast⟩
  exact hid n

private theorem koszulPowerTransition_comp
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (k m n : ℕ) (hkm : m ≤ k) (hmn : n ≤ m) :
    NoetherianKoszulProIso.koszulPowerTransition f k m hkm ≫
        NoetherianKoszulProIso.koszulPowerTransition f m n hmn =
      NoetherianKoszulProIso.koszulPowerTransition f k n (hmn.trans hkm) := by
  unfold NoetherianKoszulProIso.koszulPowerTransition
  rcases Classical.choose_spec (koszulPowerComplexes_form_inverseSystem f) with
    ⟨σ, e, η, hid, hcomp, hsid, hscomp, hformula, hη, hητ, hσ, he, hlast⟩
  exact hcomp k m n hkm hmn

private theorem homologyMap_eq_zero_iff_cycles
    {R : Type u} [CommRing R] {S T : ShortComplex (ModuleCat.{u} R)} (φ : S ⟶ T) :
    ShortComplex.homologyMap φ = 0 ↔
      ∀ x : S.X₂, S.g x = 0 → φ.τ₂ x ∈ LinearMap.range T.f.hom := by
  have heq := ShortComplex.π_homologyMap_ι φ
  constructor
  · intro h x hx
    rw [h, zero_comp, comp_zero] at heq
    let y := S.moduleCatCyclesIso.inv ⟨x, hx⟩
    have hy : S.iCycles y = x := by
      exact ConcreteCategory.congr_hom S.moduleCatCyclesIso_inv_iCycles ⟨x, hx⟩
    apply (T.moduleCat_pOpcycles_eq_zero_iff _).1
    have hh := ConcreteCategory.congr_hom heq y
    simpa [ConcreteCategory.comp_apply, hy] using hh.symm
  · intro h
    apply (cancel_epi S.homologyπ).1
    apply (cancel_mono T.homologyι).1
    rw [Category.assoc, heq]
    simp only [comp_zero, zero_comp]
    apply ModuleCat.hom_ext
    ext y
    exact (T.moduleCat_pOpcycles_eq_zero_iff _).2
      (h (S.iCycles y) (ConcreteCategory.congr_hom S.iCycles_g y))

private noncomputable abbrev homologyZeroπ
    {R : Type u} [CommRing R] (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    K.X 0 ⟶ K.homology 0 := K.pOpcycles 0 ≫ K.isoHomologyι₀.inv

private theorem homologyZeroπ_naturality
    {R : Type u} [CommRing R] {K L : ChainComplex (ModuleCat.{u} R) ℕ} (φ : K ⟶ L) :
    homologyZeroπ K ≫ HomologicalComplex.homologyMap φ 0 = φ.f 0 ≫ homologyZeroπ L := by
  dsimp only [homologyZeroπ]
  rw [Category.assoc, ChainComplex.isoHomologyι₀_inv_naturality,
    ← Category.assoc, HomologicalComplex.p_opcyclesMap, Category.assoc]

private theorem homologyZeroπ_eq_zero_iff
    {R : Type u} [CommRing R] (K : ChainComplex (ModuleCat.{u} R) ℕ) (x : K.X 0) :
    homologyZeroπ K x = 0 ↔ x ∈ LinearMap.range (K.d 1 0).hom := by
  have hp : (ComplexShape.down ℕ).prev 0 = 1 := ComplexShape.prev_eq' _ rfl
  have hn : (ComplexShape.down ℕ).next 0 = 0 :=
    ComplexShape.next_eq_self' _ _ (by intro k h; change k + 1 = 0 at h; omega)
  let e := K.isoHomologyι₀ ≪≫ K.opcyclesIsoSc' 1 0 0 hp hn
  have he : homologyZeroπ K ≫ e.hom = (K.sc' 1 0 0).pOpcycles := by
    simp [e, homologyZeroπ, Category.assoc]
  have hx : (homologyZeroπ K x = 0) ↔ (K.sc' 1 0 0).pOpcycles x = 0 := by
    have hxe : e.hom.hom (homologyZeroπ K x) = (K.sc' 1 0 0).pOpcycles x :=
      ConcreteCategory.congr_hom he x
    constructor
    · intro h
      exact hxe.symm.trans ((congrArg e.hom.hom h).trans (map_zero _))
    · intro h
      apply (ModuleCat.mono_iff_injective e.hom).1 inferInstance
      exact (hxe.trans h).trans (map_zero _).symm
  exact hx.trans ((K.sc' 1 0 0).moduleCat_pOpcycles_eq_zero_iff x)

private theorem chain_homologyMap_eq_zero_iff_cycles
    {R : Type u} [CommRing R] {K L : ChainComplex (ModuleCat.{u} R) ℕ}
    (φ : K ⟶ L) (i j k : ℕ) (hi : (ComplexShape.down ℕ).prev j = i)
    (hk : (ComplexShape.down ℕ).next j = k) :
    HomologicalComplex.homologyMap φ j = 0 ↔
      ∀ x : K.X j, K.d j k x = 0 → φ.f j x ∈ LinearMap.range (L.d i j).hom := by
  let e := HomologicalComplex.natIsoSc' (ModuleCat.{u} R) (ComplexShape.down ℕ) i j k hi hk
  let φ' := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R)
    (ComplexShape.down ℕ) i j k).map φ
  have hnat := congrArg (fun v ↦ ShortComplex.homologyMap v) (e.hom.naturality φ)
  simp only [ShortComplex.homologyMap_comp] at hnat
  change HomologicalComplex.homologyMap φ j ≫ (L.homologyIsoSc' i j k hi hk).hom =
    (K.homologyIsoSc' i j k hi hk).hom ≫ ShortComplex.homologyMap φ' at hnat
  have heq : HomologicalComplex.homologyMap φ j = 0 ↔ ShortComplex.homologyMap φ' = 0 := by
    constructor
    · intro h
      apply (cancel_epi (K.homologyIsoSc' i j k hi hk).hom).1
      simpa [h] using hnat.symm
    · intro h
      apply (cancel_mono (L.homologyIsoSc' i j k hi hk).hom).1
      simpa [h, φ', e] using hnat
  exact heq.trans (homologyMap_eq_zero_iff_cycles φ')

private theorem exists_factor_of_ker_le
    {R : Type u} [CommRing R] {M N P : ModuleCat.{u} R}
    (q : M ⟶ N) (f : M ⟶ P) (hq : Function.Surjective q)
    (h : LinearMap.ker q.hom ≤ LinearMap.ker f.hom) :
    ∃ g : N ⟶ P, q ≫ g = f := by
  refine ⟨ModuleCat.ofHom ((q.hom.ker.liftQ f.hom h).comp
    (q.hom.quotKerEquivOfSurjective hq).symm.toLinearMap), ?_⟩
  apply ModuleCat.hom_ext
  ext x
  change q.hom.ker.liftQ f.hom h ((q.hom.quotKerEquivOfSurjective hq).symm (q x)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

private theorem koszulIdealDifferential_surjective
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) :
    Function.Surjective (koszulIdealDifferential f (Ideal.span (Set.range f))
      (fun i ↦ Ideal.subset_span (Set.mem_range_self i))) := by
  classical
  let d := (koszulIdealDifferential f (Ideal.span (Set.range f))
    (fun i ↦ Ideal.subset_span (Set.mem_range_self i)))
  have hh : Ideal.span (Set.range f) ≤
      LinearMap.range ((Ideal.span (Set.range f)).subtype.comp d.hom) := by
    apply Ideal.span_le.2
    rintro _ ⟨i, rfl⟩
    refine ⟨(exteriorPower.oneEquiv R (Fin r → R)).symm (Pi.single i 1), ?_⟩
    change exteriorPower.zeroEquiv R (Fin r → R)
      (Koszul.d (Koszul.seqDual f) 0 _) = f i
    rw [Koszul.zeroEquiv_d_zero]
    change (Koszul.seqDual f) ((exteriorPower.oneEquiv R (Fin r → R))
      ((exteriorPower.oneEquiv R (Fin r → R)).symm (Pi.single i 1))) = f i
    rw [LinearEquiv.apply_symm_apply]
    exact Koszul.seqDual_single f i
  intro x
  obtain ⟨y, hy⟩ := hh x.property
  exact ⟨y, Subtype.ext hy⟩

private theorem koszulIdealComplexMap_homologyMap_eq_zero
    {R : Type u} [CommRing R] {r : ℕ} {f g : Fin r → R}
    (φ : Koszul.seqComplex f ⟶ Koszul.seqComplex g) (j : ℕ) (hj : 0 < j)
    (h : HomologicalComplex.homologyMap φ (j + 1) = 0) :
    HomologicalComplex.homologyMap (koszulIdealComplexMap φ) j = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hj)
  have hn (a : ℕ) : (ComplexShape.down ℕ).next (a + 1) = a :=
    ComplexShape.next_eq' _ rfl
  have hp (a : ℕ) : (ComplexShape.down ℕ).prev a = a + 1 :=
    ComplexShape.prev_eq' _ rfl
  apply (chain_homologyMap_eq_zero_iff_cycles _ (k + 2) (k + 1) k (hp _) (hn _)).2
  intro x hx
  have hh := (chain_homologyMap_eq_zero_iff_cycles φ (k + 3) (k + 2) (k + 1)
    (hp _) (hn _)).1 h
  change φ.f (k + 2) x ∈ LinearMap.range ((koszulIdealComplex g).d (k + 2) (k + 1)).hom
  obtain ⟨y, hy⟩ := hh x (by
    simpa only [koszulIdealComplex, ChainComplex.of_d, Nat.add_assoc] using hx)
  refine ⟨y, ?_⟩
  change ((koszulIdealComplex g).d ((k + 1) + 1) (k + 1)) y = φ.f (k + 2) x
  have hd : (koszulIdealComplex g).d ((k + 1) + 1) (k + 1) =
      (Koszul.seqComplex g).d ((k + 1) + 2) ((k + 1) + 1) := by
    dsimp only [koszulIdealComplex, ChainComplex.of]
    exact ChainComplex.of_d _ _ _
  rw [hd]
  exact hy

private theorem homologyZeroπ_single_isIso
    {R : Type u} [CommRing R] (M : ModuleCat.{u} R) :
    IsIso (homologyZeroπ ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M)) := by
  let K := (ChainComplex.single₀ (ModuleCat.{u} R)).obj M
  have : IsIso (K.pOpcycles 0) :=
    K.isIso_pOpcycles 1 0 (ComplexShape.prev_eq' _ rfl) (by simp [K])
  exact inferInstanceAs (IsIso (K.pOpcycles 0 ≫ K.isoHomologyι₀.inv))

private theorem exists_factor_koszulIdealHomology
    {R : Type u} [CommRing R] {r : ℕ} {f g : Fin r → R}
    (φ : Koszul.seqComplex f ⟶ Koszul.seqComplex g)
    (h : HomologicalComplex.homologyMap φ 1 = 0) :
    ∃ t : ModuleCat.of R (Ideal.span (Set.range f)) ⟶ (koszulIdealComplex g).homology 0,
      koszulIdealDifferential f (Ideal.span (Set.range f))
          (fun i ↦ Ideal.subset_span (Set.mem_range_self i)) ≫ t =
        (koszulIdealComplexMap φ).f 0 ≫ homologyZeroπ (koszulIdealComplex g) := by
  apply exists_factor_of_ker_le _ _ (koszulIdealDifferential_surjective f)
  intro x hx
  change homologyZeroπ (koszulIdealComplex g) (φ.f 1 x) = 0
  rw [homologyZeroπ_eq_zero_iff]
  have hh := (chain_homologyMap_eq_zero_iff_cycles φ 2 1 0
    (ComplexShape.prev_eq' _ rfl) (ComplexShape.next_eq' _ rfl)).1 h x
  have hd : (Koszul.seqComplex f).d 1 0 x = 0 := by
    apply (exteriorPower.zeroEquiv R (Fin r → R)).injective
    have hx' := congrArg Subtype.val hx
    exact hx'.trans (map_zero _).symm
  obtain ⟨y, hy⟩ := hh hd
  refine ⟨y, ?_⟩
  change ((koszulIdealComplex g).d (0 + 1) 0) y = φ.f 1 x
  have hd' : (koszulIdealComplex g).d (0 + 1) 0 =
      (Koszul.seqComplex g).d 2 1 := by
    dsimp only [koszulIdealComplex, ChainComplex.of]
    exact ChainComplex.of_d _ _ _
  rw [hd']
  exact hy

private theorem exists_idealPower_le_generatorPowers
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (n : ℕ) :
    ∃ l : ℕ, n ≤ l ∧ (Ideal.span (Set.range f)) ^ (l + 1) ≤
      Ideal.span (Set.range fun i ↦ f i ^ (n + 1)) := by
  have h : Ideal.span (Set.range f) ≤
      (Ideal.span (Set.range fun i ↦ f i ^ (n + 1))).radical := by
    apply Ideal.span_le.2
    rintro _ ⟨i, rfl⟩
    exact ⟨n + 1, Ideal.subset_span (Set.mem_range_self i)⟩
  obtain ⟨l, hl⟩ := Ideal.exists_pow_le_of_le_radical_of_fg h
    (Submodule.fg_span (Set.finite_range f))
  exact ⟨max l n, le_max_right _ _, (Ideal.pow_le_pow_right (by omega)).trans hl⟩

private noncomputable def derivedExtendHomologyIso
    {R : Type u} [CommRing R] (K : ChainComplex (ModuleCat.{u} R) ℕ) (j : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(j : ℤ))).obj
      (DerivedCategory.Q.obj (K.extend ComplexShape.embeddingDownNat)) ≅ K.homology j :=
  (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (-(j : ℤ))).app
      (K.extend ComplexShape.embeddingDownNat) ≪≫
    K.extendHomologyIso ComplexShape.embeddingDownNat rfl

private theorem derivedExtendHomologyIso_naturality
    {R : Type u} [CommRing R] {K L : ChainComplex (ModuleCat.{u} R) ℕ}
    (φ : K ⟶ L) (j : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(j : ℤ))).map
        (DerivedCategory.Q.map (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)) ≫
      (derivedExtendHomologyIso L j).hom =
    (derivedExtendHomologyIso K j).hom ≫ HomologicalComplex.homologyMap φ j := by
  have h₁ := DerivedCategory.homologyFunctorFactors_hom_naturality
    (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat) (-(j : ℤ))
  have h₂ := HomologicalComplex.extendHomologyIso_hom_naturality φ
    ComplexShape.embeddingDownNat (j := j) (j' := -(j : ℤ)) rfl
  have h₁' := congrArg (fun q ↦ q ≫
    (L.extendHomologyIso ComplexShape.embeddingDownNat (j := j) (j' := -(j : ℤ)) rfl).hom) h₁
  have h₂' := congrArg (fun q ↦
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) (-(j : ℤ))).hom.app
      (K.extend ComplexShape.embeddingDownNat) ≫ q) h₂
  exact (Category.assoc _ _ _).symm.trans
    (h₁'.trans ((Category.assoc _ _ _).trans (h₂'.trans (Category.assoc _ _ _).symm)))

private theorem derivedExtendHomology_map_eq_zero
    {R : Type u} [CommRing R] {K L : ChainComplex (ModuleCat.{u} R) ℕ}
    (φ : K ⟶ L) (j : ℕ) (h : HomologicalComplex.homologyMap φ j = 0) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (-(j : ℤ))).map
      (DerivedCategory.Q.map
        (HomologicalComplex.extendMap φ ComplexShape.embeddingDownNat)) = 0 := by
  apply (cancel_mono (derivedExtendHomologyIso L j).hom).1
  rw [derivedExtendHomologyIso_naturality, h, comp_zero, zero_comp]

private theorem koszulIdealComplex_isZero_homology_outside
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) (i : ℤ)
    (hi : i < -(r : ℤ) ∨ 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      (DerivedCategory.Q.obj ((koszulIdealComplex f).extend ComplexShape.embeddingDownNat))) := by
  let K := koszulIdealComplex f
  have hX : IsZero ((K.extend ComplexShape.embeddingDownNat).X i) := by
    by_cases hp : ∃ j : ℕ, -(j : ℤ) = i
    · obtain ⟨j, hj⟩ := hp
      have hjr : r < j + 1 := by omega
      have hK : IsZero (K.X j) := by
        change IsZero (ModuleCat.of R (⋀[R]^(j + 1) (Fin r → R)))
        have : Subsingleton (⋀[R]^(j + 1) (Fin r → R)) :=
          exteriorPower.subsingleton_of_span_eq_top_of_card_lt
            (fun i : Fin r ↦ (Pi.single i 1 : Fin r → R))
            (Koszul.span_range_single R r) (j + 1) (by simpa using hjr)
        exact ModuleCat.isZero_of_subsingleton _
      exact hK.of_iso (K.extendXIso ComplexShape.embeddingDownNat hj)
    · exact K.isZero_extend_X ComplexShape.embeddingDownNat i
        (fun j hj ↦ hp ⟨j, hj⟩)
  exact isZero_homology_Q_obj_of_isZero_X _ i hX

private theorem koszulIdealDifferential_naturality
    {R : Type u} [CommRing R] {r : ℕ} {f g : Fin r → R}
    (φ : Koszul.seqComplex f ⟶ Koszul.seqComplex g) (hφ : φ.f 0 = 𝟙 _)
    (J L : Ideal R) (hJL : J ≤ L) (hf : ∀ i, f i ∈ J) (hg : ∀ i, g i ∈ L) :
    (koszulIdealComplexMap φ).f 0 ≫ koszulIdealDifferential g L hg =
      koszulIdealDifferential f J hf ≫ ModuleCat.ofHom (Submodule.inclusion hJL) := by
  apply ModuleCat.hom_ext
  ext x
  have hcomm := φ.comm 1 0
  rw [hφ, Category.comp_id] at hcomm
  have hx := ConcreteCategory.congr_hom hcomm x
  exact congrArg (exteriorPower.zeroEquiv R (Fin r → R)) hx

private theorem opSequence_map_eq
    {C : Type*} [Category* C] (F : ℕᵒᵖ ⥤ C)
    (t : ∀ (m n : ℕ), n ≤ m → (F.obj (op m) ⟶ F.obj (op n)))
    (hid : ∀ n, t n n (le_refl n) = 𝟙 _)
    (hcomp : ∀ k m n hkm hmn, t k m hkm ≫ t m n hmn = t k n (hmn.trans hkm))
    (hsucc : ∀ n, F.map (homOfLE (Nat.le_succ n)).op = t (n + 1) n (Nat.le_succ n))
    (m n : ℕ) (h : n ≤ m) : F.map (homOfLE h).op = t m n h := by
  induction m generalizing n with
  | zero =>
      have hn : n = 0 := by omega
      subst n
      simpa using (hid 0).symm
  | succ m ih =>
      by_cases hn : n = m + 1
      · subst n
        simpa using (hid (m + 1)).symm
      · have hnm : n ≤ m := by omega
        have hcat : (homOfLE h).op =
            (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hnm).op := Subsingleton.elim _ _
        rw [hcat, Functor.map_comp, hsucc, ih n hnm, hcomp]

private theorem koszulIdealComplexMap_id
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R) :
    koszulIdealComplexMap (𝟙 (Koszul.seqComplex f)) = 𝟙 _ := by
  ext j
  rfl

private theorem koszulIdealComplexMap_comp
    {R : Type u} [CommRing R] {r : ℕ} {f g h : Fin r → R}
    (φ : Koszul.seqComplex f ⟶ Koszul.seqComplex g)
    (ψ : Koszul.seqComplex g ⟶ Koszul.seqComplex h) :
    koszulIdealComplexMap (φ ≫ ψ) = koszulIdealComplexMap φ ≫ koszulIdealComplexMap ψ := by
  ext j
  rfl

private theorem koszulIdealComplexSystem_map_homOfLE
    {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)
    (m n : ℕ) (h : n ≤ m) :
    (koszulIdealComplexSystem f).map (homOfLE h).op =
      DerivedCategory.Q.map (HomologicalComplex.extendMap
        (koszulIdealComplexMap (NoetherianKoszulProIso.koszulPowerTransition f m n h))
        ComplexShape.embeddingDownNat) := by
  apply opSequence_map_eq (koszulIdealComplexSystem f)
    (fun m n h ↦ DerivedCategory.Q.map (HomologicalComplex.extendMap
      (koszulIdealComplexMap (NoetherianKoszulProIso.koszulPowerTransition f m n h))
      ComplexShape.embeddingDownNat))
  · intro n
    rw [koszulPowerTransition_id, koszulIdealComplexMap_id]
    simp
    rfl
  · intro k m n hkm hmn
    rw [← Functor.map_comp, ← HomologicalComplex.extendMap_comp,
      ← koszulIdealComplexMap_comp, koszulPowerTransition_comp]
  · intro n
    exact Functor.ofOpSequence_map_homOfLE_succ _ n

private theorem idealPowerTransition_id
    {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ) :
    idealPowerTransition I n n (le_refl n) = 𝟙 _ := by
  ext x
  rfl

private theorem idealPowerTransition_comp
    {R : Type u} [CommRing R] (I : Ideal R)
    (k m n : ℕ) (hkm : m ≤ k) (hmn : n ≤ m) :
    idealPowerTransition I k m hkm ≫ idealPowerTransition I m n hmn =
      idealPowerTransition I k n (hmn.trans hkm) := by
  ext x
  rfl

private theorem idealPowerSystem_map_homOfLE
    {R : Type u} [CommRing R] (I : Ideal R) (m n : ℕ) (h : n ≤ m) :
    (idealPowerSystem I).map (homOfLE h).op =
      DerivedCategory.Q.map (HomologicalComplex.extendMap
        ((ChainComplex.single₀ (ModuleCat.{u} R)).map (idealPowerTransition I m n h))
        ComplexShape.embeddingDownNat) := by
  apply opSequence_map_eq (idealPowerSystem I)
    (fun m n h ↦ DerivedCategory.Q.map (HomologicalComplex.extendMap
      ((ChainComplex.single₀ (ModuleCat.{u} R)).map (idealPowerTransition I m n h))
      ComplexShape.embeddingDownNat))
  · intro n
    rw [idealPowerTransition_id]
    simp
    rfl
  · intro k m n hkm hmn
    rw [← Functor.map_comp, ← HomologicalComplex.extendMap_comp,
      ← Functor.map_comp, idealPowerTransition_comp]
  · intro n
    exact Functor.ofOpSequence_map_homOfLE_succ _ n

private theorem homologyZeroπ_epi
    {R : Type u} [CommRing R] (K : ChainComplex (ModuleCat.{u} R) ℕ) :
    Epi (homologyZeroπ K) := by
  dsimp only [homologyZeroπ]
  infer_instance

private theorem koszulIdealComparison_homology_proInverse_zero
    {R : Type u} [CommRing R] [IsNoetherianRing R] {r : ℕ} (f : Fin r → R) (n : ℕ) :
    let I := Ideal.span (Set.range f)
    let K := fun n ↦ koszulIdealComplex (fun i ↦ f i ^ (n + 1))
    let L := fun n ↦ (ChainComplex.single₀ (ModuleCat.{u} R)).obj
      (ModuleCat.of R ↥(I ^ (n + 1)))
    let ε := fun n ↦ koszulIdealComparison (fun i ↦ f i ^ (n + 1))
      (I ^ (n + 1)) (generatorPower_mem_idealPower f n)
    ∃ (m : ℕ) (h : n ≤ m) (s : (L m).homology 0 ⟶ (K n).homology 0),
      HomologicalComplex.homologyMap (ε m) 0 ≫ s =
        HomologicalComplex.homologyMap
          (koszulIdealComplexMap (NoetherianKoszulProIso.koszulPowerTransition f m n h)) 0 ∧
      s ≫ HomologicalComplex.homologyMap (ε n) 0 =
        HomologicalComplex.homologyMap
          ((ChainComplex.single₀ (ModuleCat.{u} R)).map (idealPowerTransition I m n h)) 0 := by
  dsimp only
  let I := Ideal.span (Set.range f)
  let K := fun n ↦ koszulIdealComplex (fun i ↦ f i ^ (n + 1))
  let L := fun n ↦ (ChainComplex.single₀ (ModuleCat.{u} R)).obj
    (ModuleCat.of R ↥(I ^ (n + 1)))
  let ε := fun n ↦ koszulIdealComparison (fun i ↦ f i ^ (n + 1))
    (I ^ (n + 1)) (generatorPower_mem_idealPower f n)
  obtain ⟨k, hnk, hk⟩ := NoetherianKoszulProIso.koszulPowerTransition_homologyMap_eq_zero_pos f n 1 (by omega)
  obtain ⟨t, ht⟩ := exists_factor_koszulIdealHomology
    (NoetherianKoszulProIso.koszulPowerTransition f k n hnk) hk
  obtain ⟨m, hkm, hm⟩ := exists_idealPower_le_generatorPowers f k
  let J := Ideal.span (Set.range fun i ↦ f i ^ (k + 1))
  have hJI : J ≤ I ^ (n + 1) :=
    (Ideal.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      exact generatorPower_mem_idealPower f k i)).trans
        (Ideal.pow_le_pow_right (Nat.add_le_add_right hnk 1))
  let c : ModuleCat.of R ↥(I ^ (m + 1)) ⟶ ModuleCat.of R J :=
    ModuleCat.ofHom (Submodule.inclusion hm)
  let b : ModuleCat.of R J ⟶ ModuleCat.of R ↥(I ^ (n + 1)) :=
    ModuleCat.ofHom (Submodule.inclusion hJI)
  let d := koszulIdealDifferential (fun i ↦ f i ^ (k + 1)) J
    (fun i ↦ Ideal.subset_span (Set.mem_range_self i))
  let T := koszulIdealComplexMap (NoetherianKoszulProIso.koszulPowerTransition f k n hnk)
  let U := koszulIdealComplexMap (NoetherianKoszulProIso.koszulPowerTransition f m k hkm)
  have ht' : d ≫ t = T.f 0 ≫ homologyZeroπ (K n) := ht
  have hd : Epi d := (ModuleCat.epi_iff_surjective d).2
    (koszulIdealDifferential_surjective _)
  have hp (a : ℕ) : IsIso (homologyZeroπ (L a)) := homologyZeroπ_single_isIso _
  have hq (a : ℕ) : Epi (homologyZeroπ (K a)) := homologyZeroπ_epi _
  have hε (a : ℕ) : homologyZeroπ (K a) ≫ HomologicalComplex.homologyMap (ε a) 0 =
      koszulIdealDifferential (fun i ↦ f i ^ (a + 1)) (I ^ (a + 1))
        (generatorPower_mem_idealPower f a) ≫ homologyZeroπ (L a) := by
    rw [homologyZeroπ_naturality]
    exact congrArg (fun q ↦ q ≫ homologyZeroπ (L a)) (koszulIdealComparison_f_zero _ _ _)
  have hdb : T.f 0 ≫ koszulIdealDifferential (fun i ↦ f i ^ (n + 1))
      (I ^ (n + 1)) (generatorPower_mem_idealPower f n) = d ≫ b :=
    koszulIdealDifferential_naturality _ (koszulPowerTransition_f_zero f k n hnk)
      J (I ^ (n + 1)) hJI _ _
  have htε : t ≫ HomologicalComplex.homologyMap (ε n) 0 = b ≫ homologyZeroπ (L n) := by
    apply (cancel_epi d).1
    rw [← Category.assoc, ht', Category.assoc, hε, ← Category.assoc, hdb,
      Category.assoc]
  have hdc : U.f 0 ≫ d =
      koszulIdealDifferential (fun i ↦ f i ^ (m + 1)) (I ^ (m + 1))
        (generatorPower_mem_idealPower f m) ≫ c :=
    koszulIdealDifferential_naturality _ (koszulPowerTransition_f_zero f m k hkm)
      (I ^ (m + 1)) J hm _ _
  have hcb : c ≫ b = idealPowerTransition I m n (hnk.trans hkm) := by
    ext x
    rfl
  have hUT : U ≫ T =
      koszulIdealComplexMap (NoetherianKoszulProIso.koszulPowerTransition f m n (hnk.trans hkm)) := by
    dsimp only [U, T]
    rw [← koszulIdealComplexMap_comp, koszulPowerTransition_comp]
  refine ⟨m, hnk.trans hkm, inv (homologyZeroπ (L m)) ≫ c ≫ t, ?_, ?_⟩
  · change HomologicalComplex.homologyMap (ε m) 0 ≫
      (inv (homologyZeroπ (L m)) ≫ c ≫ t) = _
    apply (cancel_epi (homologyZeroπ (K m))).1
    rw [← Category.assoc, hε]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [← Category.assoc, ← hdc, Category.assoc, ht', ← Category.assoc]
    rw [← HomologicalComplex.comp_f, hUT, ← homologyZeroπ_naturality]
    exact Category.assoc _ _ _
  · change (inv (homologyZeroπ (L m)) ≫ c ≫ t) ≫
      HomologicalComplex.homologyMap (ε n) 0 = _
    apply (cancel_epi (homologyZeroπ (L m))).1
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
    rw [htε, ← Category.assoc, hcb]
    simpa only [homologyZeroπ, Category.assoc, ChainComplex.single₀_map_f_zero] using
      (homologyZeroπ_naturality ((ChainComplex.single₀ (ModuleCat.{u} R)).map
        (idealPowerTransition I m n (hnk.trans hkm)))).symm

private theorem proInverse_of_iso_naturality
    {C : Type*} [Category* C]
    {A B A' B' X Y X' Y' : C}
    (eA : A ≅ X) (eB : B ≅ Y) (eA' : A' ≅ X') (eB' : B' ≅ Y')
    (a : A ⟶ B) (b : A' ⟶ B') (x : A ⟶ A') (y : B ⟶ B')
    (a' : X ⟶ Y) (b' : X' ⟶ Y') (x' : X ⟶ X') (y' : Y ⟶ Y')
    (ha : a ≫ eB.hom = eA.hom ≫ a') (hb : b ≫ eB'.hom = eA'.hom ≫ b')
    (hx : x ≫ eA'.hom = eA.hom ≫ x') (hy : y ≫ eB'.hom = eB.hom ≫ y')
    (s : Y ⟶ X') (hs₁ : a' ≫ s = x') (hs₂ : s ≫ b' = y') :
    ∃ t : B ⟶ A', a ≫ t = x ∧ t ≫ b = y := by
  refine ⟨eB.hom ≫ s ≫ eA'.inv, ?_, ?_⟩
  · apply (cancel_mono eA'.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [← Category.assoc, ha, Category.assoc, hs₁, hx]
  · apply (cancel_mono eB'.hom).1
    simp only [Category.assoc]
    rw [hb]
    simp only [Iso.inv_hom_id_assoc]
    rw [hs₂, hy]

private theorem koszulIdealComparisonSystem_homology_proInverse_zero
    {R : Type u} [CommRing R] [IsNoetherianRing R] {r : ℕ} (f : Fin r → R) (n : ℕ) :
    let I := Ideal.span (Set.range f)
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0
    ∃ (m : ℕ) (h : n ≤ m)
      (s : H.obj ((idealPowerSystem I).obj (op m)) ⟶
        H.obj ((koszulIdealComplexSystem f).obj (op n))),
      H.map ((koszulIdealComparisonSystem f).app (op m)) ≫ s =
        H.map ((koszulIdealComplexSystem f).map (homOfLE h).op) ∧
      s ≫ H.map ((koszulIdealComparisonSystem f).app (op n)) =
        H.map ((idealPowerSystem I).map (homOfLE h).op) := by
  obtain ⟨m, h, s, hs₁, hs₂⟩ := koszulIdealComparison_homology_proInverse_zero f n
  refine ⟨m, h, ?_⟩
  let I := Ideal.span (Set.range f)
  let K := fun n ↦ koszulIdealComplex (fun i ↦ f i ^ (n + 1))
  let L := fun n ↦ (ChainComplex.single₀ (ModuleCat.{u} R)).obj
    (ModuleCat.of R ↥(I ^ (n + 1)))
  let ε := fun n ↦ koszulIdealComparison (fun i ↦ f i ^ (n + 1))
    (I ^ (n + 1)) (generatorPower_mem_idealPower f n)
  apply proInverse_of_iso_naturality
    (derivedExtendHomologyIso (K m) 0) (derivedExtendHomologyIso (L m) 0)
    (derivedExtendHomologyIso (K n) 0) (derivedExtendHomologyIso (L n) 0)
    _ _ _ _ (HomologicalComplex.homologyMap (ε m) 0)
    (HomologicalComplex.homologyMap (ε n) 0)
    (HomologicalComplex.homologyMap
      (koszulIdealComplexMap (NoetherianKoszulProIso.koszulPowerTransition f m n h)) 0)
    (HomologicalComplex.homologyMap
      ((ChainComplex.single₀ (ModuleCat.{u} R)).map (idealPowerTransition I m n h)) 0)
    _ _ _ _ s hs₁ hs₂
  · exact derivedExtendHomologyIso_naturality (ε m) 0
  · exact derivedExtendHomologyIso_naturality (ε n) 0
  · rw [koszulIdealComplexSystem_map_homOfLE]
    exact derivedExtendHomologyIso_naturality _ 0
  · rw [idealPowerSystem_map_homOfLE]
    exact derivedExtendHomologyIso_naturality _ 0

private theorem idealPowerSystem_isZero_homology_of_ne_zero
    {R : Type u} [CommRing R] (I : Ideal R) (i : ℤ) (hi : i ≠ 0) (n : ℕ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      ((idealPowerSystem I).obj (op n))) := by
  let Q := ModuleCat.of R ↥(I ^ (n + 1))
  let E := ((ChainComplex.single₀ (ModuleCat.{u} R)).obj Q).extend
    ComplexShape.embeddingDownNat
  exact (NoetherianKoszulProIso.single_extendDown_isZero_homology_of_ne_zero Q i hi).of_iso
    ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app E)

private theorem koszulIdealComplexSystem_homology_transition_eq_zero_neg
    {R : Type u} [CommRing R] [IsNoetherianRing R] {r : ℕ} (f : Fin r → R)
    (i : ℤ) (hi : i < 0) (n : ℕ) :
    ∃ (m : ℕ) (h : n ≤ m),
      (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
        ((koszulIdealComplexSystem f).map (homOfLE h).op) = 0 := by
  let j : ℕ := (-i).toNat
  have hj : 0 < j := by dsimp [j]; omega
  have hji : i = -(j : ℤ) := by dsimp [j]; omega
  obtain ⟨m, h, hzero⟩ := NoetherianKoszulProIso.koszulPowerTransition_homologyMap_eq_zero_pos f n (j + 1) (by omega)
  refine ⟨m, h, ?_⟩
  rw [hji, koszulIdealComplexSystem_map_homOfLE]
  exact derivedExtendHomology_map_eq_zero _ j
    (koszulIdealComplexMap_homologyMap_eq_zero _ j hj hzero)

/-- **Stacks Project, Tag 0G3M.** Over a Noetherian ring, the inverse system of positive
powers of the ideal generated by a finite sequence and the inverse system of shifted,
positive-degree Koszul complexes on its positive powers are pro-isomorphic in the derived
category. The comparison is induced by the Koszul differential into the corresponding ideal
power; the displayed identities express a two-sided inverse after cofinal refinement. -/
@[stacks 0G3M]
public theorem idealPowerSystem_proIso_koszulIdealComplexSystem
    {A : Type u} [CommRing A] [IsNoetherianRing A] {r : ℕ} (f : Fin r → A) :
    let I := Ideal.span (Set.range f)
    ∃ (ε : ∀ n : ℕ,
        koszulIdealComplex (fun i ↦ f i ^ (n + 1)) ⟶
          (ChainComplex.single₀ (ModuleCat.{u} A)).obj
            (ModuleCat.of A ↥(I ^ (n + 1))))
      (e : koszulIdealComplexSystem f ⟶ idealPowerSystem I),
      (∀ n,
        (ε n).f 0 ≫ ModuleCat.ofHom (I ^ (n + 1)).subtype =
          (koszulIdealComplexXIso (fun i ↦ f i ^ (n + 1)) 0).hom ≫
            (Koszul.seqComplex (fun i ↦ f i ^ (n + 1))).d 1 0 ≫
            ModuleCat.ofHom
              (exteriorPower.zeroEquiv A (Fin r → A)).toLinearMap) ∧
      (∀ n,
        e.app (op n) = DerivedCategory.Q.map
          (HomologicalComplex.extendMap (ε n) ComplexShape.embeddingDownNat)) ∧
      ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
        (s : (idealPowerSystem I).obj (op m) ⟶
          (koszulIdealComplexSystem f).obj (op n)),
        e.app (op m) ≫ s =
            (koszulIdealComplexSystem f).map (homOfLE h).op ∧
          s ≫ e.app (op n) =
            (idealPowerSystem I).map (homOfLE h).op := by
  let I := Ideal.span (Set.range f)
  let ε := fun n ↦ koszulIdealComparison (fun i ↦ f i ^ (n + 1))
    (I ^ (n + 1)) (generatorPower_mem_idealPower f n)
  let e := koszulIdealComparisonSystem f
  refine ⟨ε, e, ?_, ?_, ?_⟩
  · intro n
    rw [koszulIdealComparison_f_zero]
    exact koszulIdealDifferential_subtype _ _ _
  · intro n
    rfl
  · intro n
    let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A)
    have hA (i : ℤ) (hi : i < -(r : ℤ) ∨ 0 < i) (j : ℕᵒᵖ) :
        IsZero ((H i).obj ((koszulIdealComplexSystem f).obj j)) :=
      koszulIdealComplex_isZero_homology_outside (fun k ↦ f k ^ (j.unop + 1)) i hi
    have hB (i : ℤ) (hi : i < -(r : ℤ) ∨ 0 < i) (j : ℕᵒᵖ) :
        IsZero ((H i).obj ((idealPowerSystem I).obj j)) := by
      exact idealPowerSystem_isZero_homology_of_ne_zero I i (by omega) j.unop
    have hH (i : ℤ) (j : ℕᵒᵖ) :
        ∃ (k : ℕᵒᵖ) (g : k ⟶ j)
          (s : (H i).obj ((idealPowerSystem I).obj k) ⟶
            (H i).obj ((koszulIdealComplexSystem f).obj j)),
          (H i).map (e.app k) ≫ s =
            (H i).map ((koszulIdealComplexSystem f).map g) ∧
          s ≫ (H i).map (e.app j) =
            (H i).map ((idealPowerSystem I).map g) := by
      by_cases hi0 : i = 0
      · subst i
        obtain ⟨m, h, s, hs₁, hs₂⟩ :=
          koszulIdealComparisonSystem_homology_proInverse_zero f j.unop
        exact ⟨op m, (homOfLE h).op, s, hs₁, hs₂⟩
      · by_cases hin : i < 0
        · obtain ⟨m, h, hzero⟩ :=
            koszulIdealComplexSystem_homology_transition_eq_zero_neg f i hin j.unop
          have hq : IsZero ((H i).obj ((idealPowerSystem I).obj (op m))) :=
            idealPowerSystem_isZero_homology_of_ne_zero I i hi0 m
          refine ⟨op m, (homOfLE h).op, 0, ?_, ?_⟩
          · simpa using hzero.symm
          · exact hq.eq_of_src _ _
        · have hip : 0 < i := by omega
          refine ⟨j, 𝟙 j, 0, ?_, ?_⟩
          · exact (hA i (Or.inr hip) j).eq_of_tgt _ _
          · exact (hB i (Or.inr hip) j).eq_of_src _ _
    obtain ⟨k, g, s, hs₁, hs₂⟩ :=
      DerivedCategory.exists_proInverse_of_proInverse_homology e (-(r : ℤ)) 0
        hA hB hH (op n)
    have h : n ≤ k.unop := leOfHom g.unop
    have hg : g = (homOfLE h).op := Subsingleton.elim _ _
    exact ⟨k.unop, h, s, hg ▸ hs₁, hg ▸ hs₂⟩
end IdealPowerProIso

end Stacks.AdicSystem.KoszulIdealPower

/-! ## Tag 0G9M -/

namespace Stacks.AdicSystem.DerivedReductionProIso

open CategoryTheory CategoryTheory.Limits Opposite LiftAcyclic

/-- Reduction modulo a smaller ideal maps canonically to reduction modulo a larger ideal. -/
public noncomputable def reductionNatTrans {A : Type u} [CommRing A]
    {J K : Ideal A} (h : J ≤ K) : redFunctor J ⟶ redFunctor K where
  app M := ModuleCat.ofHom <| Submodule.mapQ
    (J • (⊤ : Submodule A M)) (K • (⊤ : Submodule A M)) LinearMap.id (by
      simpa using Submodule.smul_mono h (le_refl (⊤ : Submodule A M)))
  naturality M N f := by
    apply ModuleCat.hom_ext
    ext x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule A M)) x
    rfl

/-- The canonical transition from reduction modulo `I^(m+1)` to reduction modulo `I^(n+1)`
when `n ≤ m`, viewed in the derived category. -/
public noncomputable def adicReductionTransition {A : Type u} [CommRing A]
    (I : Ideal A) (K : CochainComplex (ModuleCat.{u} A) ℤ)
    {n m : ℕ} (h : n ≤ m) :
    DerivedCategory.Q.obj ((reduceComplex (I ^ (m + 1))).obj K) ⟶
      DerivedCategory.Q.obj ((reduceComplex (I ^ (n + 1))).obj K) :=
  DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex
      (reductionNatTrans (Ideal.pow_le_pow_right (Nat.add_le_add_right h 1)))
      (ComplexShape.up ℤ)).app K)

/-- The level-`n` comparison from the reduction of a resolution to the degreewise reduction
of the resolved complex. -/
public noncomputable def adicReductionComparison {A : Type u} [CommRing A]
    (I : Ideal A) {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (n : ℕ) :
    DerivedCategory.Q.obj ((reduceComplex (I ^ (n + 1))).obj P) ⟶
      DerivedCategory.Q.obj ((reduceComplex (I ^ (n + 1))).obj M) :=
  DerivedCategory.Q.map ((reduceComplex (I ^ (n + 1))).map p)

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

private def finiteFreeObject : ObjectProperty (FGModuleCat.{u} A) :=
  fun X => Module.Free A X

omit [IsNoetherianRing A] in
private lemma finiteFreeObject_containsZero : finiteFreeObject (A := A) |>.ContainsZero := by
  constructor
  · let Z : FGModuleCat.{u} A := FGModuleCat.of A (Fin 0 → A)
    refine ⟨Z, ?_, ?_⟩
    · apply IsZero.of_full_of_faithful_of_isZero (ModuleCat.isFG A).ι
      change IsZero (ModuleCat.of A (Fin 0 → A))
      exact (ModuleCat.isZero_iff_subsingleton).2 inferInstance
    · change Module.Free A (Fin 0 → A)
      infer_instance

attribute [local instance] finiteFreeObject_containsZero

omit [IsNoetherianRing A] in
private lemma finiteFreeCover (X : FGModuleCat.{u} A) :
    ∃ (Y : FGModuleCat.{u} A) (_ : finiteFreeObject Y) (p : Y ⟶ X), Epi p := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A X
  let Y : FGModuleCat.{u} A := FGModuleCat.of A (Fin n → A)
  have hY : finiteFreeObject Y := by
    change Module.Free A (Fin n → A)
    infer_instance
  let p : Y ⟶ X := FGModuleCat.ofHom f
  refine ⟨Y, hY, p, ?_⟩
  exact ((ModuleCat.isFG A).ι).epi_of_epi_map ((ModuleCat.epi_iff_surjective _).2 hf)

private lemma finiteFreeResolution
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (b : ℤ) (hMb : M.IsStrictlyLE b)
    (hMfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (p : P ⟶ M),
      P.IsStrictlyLE b ∧
      (∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Free A (P.X i)) ∧
      IsIso (DerivedCategory.Q.map p) := by
  let G : FGModuleCat.{u} A ⥤ ModuleCat.{u} A := forget₂ _ _
  let K : CochainComplex (FGModuleCat.{u} A) ℤ :=
    HomologicalComplex.liftObjectProperty (ModuleCat.isFG A) M hMfinite
  have hKb : K.IsStrictlyLE b := by
    apply (CochainComplex.isStrictlyLE_iff K b).2
    intro i hi
    apply IsZero.of_full_of_faithful_of_isZero G
    change IsZero (M.X i)
    exact (CochainComplex.isStrictlyLE_iff M b).1 hMb i hi
  have : K.IsStrictlyLE b := hKb
  obtain ⟨L, f, _, hf, hLfree, hLb⟩ :=
    (CochainComplex.exists_quasiIso_prop finiteFreeObject finiteFreeCover b).1 K
  let P : CochainComplex (ModuleCat.{u} A) ℤ :=
    (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj L
  let p : P ⟶ M := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map f
  refine ⟨P, p, ?_, ?_, ?_⟩
  · apply (CochainComplex.isStrictlyLE_iff P b).2
    intro i hi
    have : L.IsStrictlyLE b := hLb
    exact G.map_isZero (CochainComplex.isZero_of_isStrictlyLE L b i hi)
  · intro i
    exact ⟨(L.X i).property, hLfree i⟩
  · apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2
    exact HomologicalComplex.quasiIso_map_of_preservesHomology f G

omit [IsNoetherianRing A] in
/- The quotient ideals used by the Koszul system and the ordinary adic system are
cofinal. This is the ideal-theoretic part of the comparison in Stacks 0G9M. -/
private lemma powers_le_span_generator_powers {r : ℕ} (f : Fin r → A) (n : ℕ) :
    ∃ m : ℕ,
      (Ideal.span (Set.range f)) ^ m ≤
        Ideal.span (Set.range fun i => f i ^ (n + 1)) := by
  let J : Ideal A := Ideal.span (Set.range fun i => f i ^ (n + 1))
  have hrad : Ideal.span (Set.range f) ≤ J.radical := by
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (Ideal.mem_radical_iff).mpr
      ⟨n + 1, Ideal.subset_span ⟨i, rfl⟩⟩
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (Submodule.fg_span (Set.finite_range f))

omit [IsNoetherianRing A] in
private lemma span_generator_powers_le_power {r : ℕ} (f : Fin r → A) (n : ℕ) :
    Ideal.span (Set.range fun i => f i ^ (n + 1)) ≤
      (Ideal.span (Set.range f)) ^ (n + 1) := by
  apply Ideal.span_le.mpr
  rintro x ⟨i, rfl⟩
  exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) (n + 1)

private lemma exists_finite_generators_and_cofinal_powers (I : Ideal A) :
    ∃ (r : ℕ) (f : Fin r → A),
      I = Ideal.span (Set.range f) ∧
      (∀ n : ℕ, ∃ m : ℕ,
        I ^ (m + 1) ≤ Ideal.span (Set.range fun i => f i ^ (n + 1))) ∧
      (∀ n : ℕ, Ideal.span (Set.range fun i => f i ^ (n + 1)) ≤ I ^ (n + 1)) := by
  obtain ⟨r, f, hf⟩ :=
    (Submodule.fg_iff_exists_fin_generating_family).mp
      (Ideal.fg_of_isNoetherianRing I)
  change Ideal.span (Set.range f) = I at hf
  refine ⟨r, f, hf.symm, ?_, ?_⟩
  · intro n
    obtain ⟨m, hm⟩ := powers_le_span_generator_powers f n
    refine ⟨m, ?_⟩
    rw [← hf]
    exact (Ideal.pow_le_pow_right (Nat.le_succ m)).trans hm
  · intro n
    rw [← hf]
    exact span_generator_powers_le_power f n

omit [IsNoetherianRing A] in
private lemma finite_reduction_of_finite (I : Ideal A)
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    Module.Finite A ((redFunctor I).obj M) := by
  change Module.Finite A (M ⧸ I • (⊤ : Submodule A M))
  exact Module.Finite.of_surjective (Submodule.mkQ _)
    (Submodule.mkQ_surjective _)

omit [IsNoetherianRing A] in
private lemma finite_reduced_complex_of_finite (I : Ideal A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : ∀ i : ℤ, Module.Finite A (M.X i)) (i : ℤ) :
    Module.Finite A (((reduceComplex I).obj M).X i) := by
  let := hM i
  exact finite_reduction_of_finite I (M.X i)

private lemma finite_homology_of_finite_terms
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ i : ℤ, Module.Finite A (K.X i)) (i : ℤ) :
    Module.Finite A (K.homology i) := by
  have : Module.Finite A (K.X i) := hK i
  have hcyc : Module.Finite A (K.cycles i) :=
    Module.Finite.of_injective (K.iCycles i).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance)
  exact Module.Finite.of_surjective (K.homologyπ i).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)

omit [IsNoetherianRing A] in
/-- A class in the reduction of `L` modulo `I` is killed by the reduced map exactly when its
image under `f` lies in `I • M`. -/
lemma reduction_map_mk_eq_zero_iff (I : Ideal A)
    {L M : ModuleCat.{u} A} (f : L ⟶ M) (x : L) :
    ((redFunctor I).map f).hom
        (Submodule.mkQ (I • (⊤ : Submodule A L)) x) = 0 ↔
      f.hom x ∈ I • (⊤ : Submodule A M) := by
  change (Submodule.mkQ (I • (⊤ : Submodule A M)) (f.hom x)) = 0 ↔ _
  exact Submodule.Quotient.mk_eq_zero _

omit [IsNoetherianRing A] in
/-- A class in the reduction of `L` modulo `I` lies in the range of the reduced map exactly when
its representative lies in the range of `f` together with `I • L`. -/
lemma reduction_map_mk_mem_range_iff (I : Ideal A)
    {K L : ModuleCat.{u} A} (f : K ⟶ L) (y : L) :
    Submodule.mkQ (I • (⊤ : Submodule A L)) y ∈
        LinearMap.range ((redFunctor I).map f).hom ↔
      y ∈ LinearMap.range f.hom ⊔ I • (⊤ : Submodule A L) := by
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A K)) q
    have hxy : y - f.hom x ∈ I • (⊤ : Submodule A L) := by
      apply (Submodule.Quotient.eq _).mp
      change Submodule.mkQ _ (f.hom x) = Submodule.mkQ _ y at hq
      exact hq.symm
    have hdecomp : y = f.hom x + (y - f.hom x) := by abel
    rw [hdecomp]
    exact Submodule.add_mem_sup ⟨x, rfl⟩ hxy
  · intro hy
    obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp hy
    obtain ⟨x, rfl⟩ := hz
    refine ⟨Submodule.mkQ (I • (⊤ : Submodule A K)) x, ?_⟩
    change Submodule.mkQ (I • (⊤ : Submodule A L)) (f.hom x) = _
    rw [← hzw]
    have hw0 : Submodule.mkQ (I • (⊤ : Submodule A L)) w = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hw
    simp only [map_add, hw0, add_zero]

omit [IsNoetherianRing A] in
/-- The cycles of a reduced two-term complex, presented concretely as a quotient of the
comparable submodule of cycles upstairs. -/
noncomputable def reductionCyclesMap (I : Ideal A)
    {L M : ModuleCat.{u} A} (f : L ⟶ M) :
    ((I • (⊤ : Submodule A M)).comap f.hom) →ₗ[A]
      LinearMap.ker ((redFunctor I).map f).hom :=
  ((Submodule.mkQ (I • (⊤ : Submodule A L))).comp
    ((I • (⊤ : Submodule A M)).comap f.hom).subtype).codRestrict _ (by
      intro x
      exact (reduction_map_mk_eq_zero_iff I f x).2 x.property)

omit [IsNoetherianRing A] in
/-- Every cycle of a reduced two-term complex comes from a comparable cycle upstairs. -/
lemma reductionCyclesMap_surjective (I : Ideal A)
    {L M : ModuleCat.{u} A} (f : L ⟶ M) :
    Function.Surjective (reductionCyclesMap I f) := by
  intro y
  obtain ⟨x, hx⟩ :=
    Submodule.mkQ_surjective (I • (⊤ : Submodule A L)) (y : (redFunctor I).obj L)
  have hcycle : x ∈ (I • (⊤ : Submodule A M)).comap f.hom := by
    apply (reduction_map_mk_eq_zero_iff I f x).1
    rw [hx]
    exact y.property
  refine ⟨⟨x, hcycle⟩, ?_⟩
  apply Subtype.ext
  exact hx

omit [IsNoetherianRing A] in
private lemma reductionCyclesMap_ker (I : Ideal A)
    {L M : ModuleCat.{u} A} (f : L ⟶ M) :
    LinearMap.ker (reductionCyclesMap I f) =
      (I • (⊤ : Submodule A L)).comap
        ((I • (⊤ : Submodule A M)).comap f.hom).subtype := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_comap]
  constructor
  · intro hx
    exact (Submodule.Quotient.mk_eq_zero _).1
      (congrArg Subtype.val hx)
  · intro hx
    apply Subtype.ext
    exact (Submodule.Quotient.mk_eq_zero _).2 hx

omit [IsNoetherianRing A] in
private noncomputable def reductionCyclesEquiv (I : Ideal A)
    {L M : ModuleCat.{u} A} (f : L ⟶ M) :
    (((I • (⊤ : Submodule A M)).comap f.hom) ⧸
      (I • (⊤ : Submodule A L)).comap
        ((I • (⊤ : Submodule A M)).comap f.hom).subtype) ≃ₗ[A]
      LinearMap.ker ((redFunctor I).map f).hom :=
  (Submodule.quotEquivOfEq _ _ (reductionCyclesMap_ker I f).symm).trans
    ((reductionCyclesMap I f).quotKerEquivOfSurjective
      (reductionCyclesMap_surjective I f))

omit [IsNoetherianRing A] in
private lemma reductionBoundaries_le_cycles (I : Ideal A)
    {K L M : ModuleCat.{u} A} (α : K ⟶ L) (β : L ⟶ M)
    (h : α ≫ β = 0) :
    LinearMap.range α.hom ⊔ I • (⊤ : Submodule A L) ≤
      (I • (⊤ : Submodule A M)).comap β.hom := by
  apply sup_le
  · rintro y ⟨x, rfl⟩
    change β.hom (α.hom x) ∈ I • (⊤ : Submodule A M)
    have h0 : β.hom (α.hom x) = 0 := by
      exact congrArg (fun g : K ⟶ M => g.hom x) h
    rw [h0]
    exact Submodule.zero_mem _
  · exact Submodule.smul_top_le_comap_smul_top I β.hom

omit [IsNoetherianRing A] in
/-- The reduction modulo `I` of a two-term complex, as a short complex. -/
noncomputable def reductionShortComplex (I : Ideal A)
    {K L M : ModuleCat.{u} A} (α : K ⟶ L) (β : L ⟶ M)
    (h : α ≫ β = 0) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk ((redFunctor I).map α) ((redFunctor I).map β) (by
    rw [← Functor.map_comp, h, Functor.map_zero])

omit [IsNoetherianRing A] in
/-- A concrete cycle is a boundary of the reduced short complex exactly when its representative
lies in the range of `α` together with `I • L`. -/
lemma reductionCyclesMap_mem_boundaries_iff (I : Ideal A)
    {K L M : ModuleCat.{u} A} (α : K ⟶ L) (β : L ⟶ M)
    (h : α ≫ β = 0)
    (x : (I • (⊤ : Submodule A M)).comap β.hom) :
    reductionCyclesMap I β x ∈
        LinearMap.range (reductionShortComplex I α β h).moduleCatToCycles ↔
      (x : L) ∈ LinearMap.range α.hom ⊔ I • (⊤ : Submodule A L) := by
  let S := reductionShortComplex I α β h
  constructor
  · rintro ⟨q, hq⟩
    have hq' : Submodule.mkQ (I • (⊤ : Submodule A L)) (x : L) ∈
        LinearMap.range ((redFunctor I).map α).hom := by
      refine ⟨q, ?_⟩
      exact congrArg Subtype.val hq
    exact (reduction_map_mk_mem_range_iff I α x).1 hq'
  · intro hx
    obtain ⟨q, hq⟩ := (reduction_map_mk_mem_range_iff I α x).2 hx
    refine ⟨q, ?_⟩
    apply Subtype.ext
    exact hq

omit [IsNoetherianRing A] in
/-- The homology of a reduced two-term complex, presented as a quotient of the concrete cycles
by the concrete boundaries. -/
noncomputable def reductionHomologyEquiv (I : Ideal A)
    {K L M : ModuleCat.{u} A} (α : K ⟶ L) (β : L ⟶ M)
    (h : α ≫ β = 0) :
    (((I • (⊤ : Submodule A M)).comap β.hom) ⧸
      (LinearMap.range α.hom ⊔ I • (⊤ : Submodule A L)).comap
        ((I • (⊤ : Submodule A M)).comap β.hom).subtype) ≃ₗ[A]
      (reductionShortComplex I α β h).moduleCatLeftHomologyData.H := by
  let S := reductionShortComplex I α β h
  let cyc := (I • (⊤ : Submodule A M)).comap β.hom
  let bd := LinearMap.range α.hom ⊔ I • (⊤ : Submodule A L)
  let g : cyc →ₗ[A] S.moduleCatLeftHomologyData.H :=
    (LinearMap.range S.moduleCatToCycles).mkQ.comp (reductionCyclesMap I β)
  have hker : LinearMap.ker g = bd.comap cyc.subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    change (LinearMap.range S.moduleCatToCycles).mkQ
      (reductionCyclesMap I β x) = 0 ↔ (x : L) ∈ bd
    exact (Submodule.Quotient.mk_eq_zero _).trans
      (reductionCyclesMap_mem_boundaries_iff I α β h x)
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨z, rfl⟩ :=
      Submodule.mkQ_surjective (LinearMap.range S.moduleCatToCycles) y
    obtain ⟨x, rfl⟩ := reductionCyclesMap_surjective I β z
    exact ⟨x, rfl⟩
  exact (Submodule.quotEquivOfEq _ _ hker.symm).trans
    (g.quotKerEquivOfSurjective hsurj)

omit [IsNoetherianRing A] in
/-- On the class of a concrete cycle, the homology comparison is the projection of
`reductionCyclesMap`. -/
lemma reductionHomologyEquiv_mk (I : Ideal A)
    {K L M : ModuleCat.{u} A} (α : K ⟶ L) (β : L ⟶ M)
    (h : α ≫ β = 0)
    (x : (I • (⊤ : Submodule A M)).comap β.hom) :
    reductionHomologyEquiv I α β h (Submodule.Quotient.mk x) =
      (reductionShortComplex I α β h).moduleCatLeftHomologyData.π.hom
        (reductionCyclesMap I β x) := by
  rfl

omit [IsNoetherianRing A] in
private lemma reductionShortComplex_sc (I : Ideal A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    reductionShortComplex I (M.sc i).f (M.sc i).g (M.sc i).zero =
      ((reduceComplex I).obj M).sc i := by
  rfl

omit [IsNoetherianRing A] in
/-- The `i`-th homology of the degreewise reduction of a complex, presented concretely. -/
noncomputable def reducedHomologyConcreteEquiv (I : Ideal A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    (((I • (⊤ : Submodule A (M.sc i).X₃)).comap (M.sc i).g.hom) ⧸
      (LinearMap.range (M.sc i).f.hom ⊔
        I • (⊤ : Submodule A (M.sc i).X₂)).comap
        ((I • (⊤ : Submodule A (M.sc i).X₃)).comap (M.sc i).g.hom).subtype) ≃ₗ[A]
      ((reduceComplex I).obj M).homology i := by
  let S := reductionShortComplex I (M.sc i).f (M.sc i).g (M.sc i).zero
  exact (reductionHomologyEquiv I (M.sc i).f (M.sc i).g (M.sc i).zero).trans
    S.moduleCatHomologyIso.symm.toLinearEquiv

omit [IsNoetherianRing A] in
private lemma reducedHomologyConcreteEquiv_mk (I : Ideal A)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (x : (I • (⊤ : Submodule A (M.sc i).X₃)).comap (M.sc i).g.hom) :
    reducedHomologyConcreteEquiv I M i (Submodule.Quotient.mk x) =
      (((reduceComplex I).obj M).sc i).homologyπ
        ((((reduceComplex I).obj M).sc i).moduleCatCyclesIso.inv
          (reductionCyclesMap I (M.sc i).g x)) := by
  let S := reductionShortComplex I (M.sc i).f (M.sc i).g (M.sc i).zero
  change S.moduleCatHomologyIso.inv
      (reductionHomologyEquiv I (M.sc i).f (M.sc i).g (M.sc i).zero
        (Submodule.Quotient.mk x)) = _
  rw [reductionHomologyEquiv_mk]
  exact (congrArg
    (fun (f : S.moduleCatLeftHomologyData.K ⟶ S.homology) =>
      f.hom (reductionCyclesMap I (M.sc i).g x))
    S.moduleCatCyclesIso_inv_π).symm

omit [IsNoetherianRing A] in
private lemma range_moduleCatToCycles_eq_comap
    (S : ShortComplex (ModuleCat.{u} A)) :
    LinearMap.range S.moduleCatToCycles =
      (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, ?_⟩
    apply Subtype.ext
    exact hy

omit [IsNoetherianRing A] in
private noncomputable def originalHomologyConcreteEquiv
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    ((LinearMap.ker (M.sc i).g.hom) ⧸
      (LinearMap.range (M.sc i).f.hom).comap
        (LinearMap.ker (M.sc i).g.hom).subtype) ≃ₗ[A]
      M.homology i :=
  (Submodule.quotEquivOfEq _ _
    (range_moduleCatToCycles_eq_comap (M.sc i)).symm).trans
    (M.sc i).moduleCatHomologyIso.symm.toLinearEquiv

omit [IsNoetherianRing A] in
private def reductionCyclesMapOfSquare (I : Ideal A)
    {L M L' M' : ModuleCat.{u} A}
    (β : L ⟶ M) (β' : L' ⟶ M')
    (v : L ⟶ L') (w : M ⟶ M')
    (h : v ≫ β' = β ≫ w) :
    ((I • (⊤ : Submodule A M)).comap β.hom) →ₗ[A]
      ((I • (⊤ : Submodule A M')).comap β'.hom) :=
  v.hom.comp ((I • (⊤ : Submodule A M)).comap β.hom).subtype |>.codRestrict _ (by
    intro x
    change β'.hom (v.hom (x : L)) ∈ I • (⊤ : Submodule A M')
    have hh : β'.hom (v.hom (x : L)) = w.hom (β.hom (x : L)) :=
      congrArg (fun f : L ⟶ M' => f.hom x) h
    rw [hh]
    exact (Submodule.smul_top_le_comap_smul_top I w.hom) x.property)

omit [IsNoetherianRing A] in
private lemma reductionCyclesMap_naturality (I : Ideal A)
    {L M L' M' : ModuleCat.{u} A}
    (β : L ⟶ M) (β' : L' ⟶ M')
    (v : L ⟶ L') (w : M ⟶ M')
    (h : v ≫ β' = β ≫ w)
    (x : (I • (⊤ : Submodule A M)).comap β.hom) :
    ((reductionCyclesMap I β'
      (reductionCyclesMapOfSquare I β β' v w h x) : (redFunctor I).obj L')) =
      ((redFunctor I).map v).hom (reductionCyclesMap I β x) := by
  rfl

private lemma proInverse_of_common_source
    {J : Type*} [Category J] {C : Type*} [Category C]
    {Q X Y : J ⥤ C} (α : Q ⟶ X) (β : Q ⟶ Y) (p : X ⟶ Y)
    (h : α ≫ p = β)
    (hα : ∀ j : J, ∃ (k : J) (f : k ⟶ j) (s : X.obj k ⟶ Q.obj j),
      α.app k ≫ s = Q.map f ∧ s ≫ α.app j = X.map f)
    (hβ : ∀ j : J, ∃ (k : J) (f : k ⟶ j) (s : Y.obj k ⟶ Q.obj j),
      β.app k ≫ s = Q.map f ∧ s ≫ β.app j = Y.map f) :
    ∀ j : J, ∃ (k : J) (f : k ⟶ j) (s : Y.obj k ⟶ X.obj j),
      p.app k ≫ s = X.map f ∧ s ≫ p.app j = Y.map f := by
  intro j
  obtain ⟨k, f, t, ht₁, ht₂⟩ := hβ j
  obtain ⟨l, g, s, hs₁, hs₂⟩ := hα k
  have hc (j : J) : α.app j ≫ p.app j = β.app j :=
    congrArg (fun η : Q ⟶ Y => η.app j) h
  refine ⟨l, g ≫ f, Y.map g ≫ t ≫ α.app j, ?_, ?_⟩
  · calc
      p.app l ≫ (Y.map g ≫ t ≫ α.app j) =
          (X.map g ≫ p.app k) ≫ t ≫ α.app j := by
            simp only [Category.assoc, p.naturality g]
      _ = (s ≫ α.app k) ≫ p.app k ≫ t ≫ α.app j := by
            simp only [Category.assoc, hs₂]
      _ = s ≫ (β.app k ≫ t) ≫ α.app j := by
            simpa only [Category.assoc] using congrArg
              (fun q : Q.obj k ⟶ Y.obj k => s ≫ q ≫ t ≫ α.app j) (hc k)
      _ = s ≫ Q.map f ≫ α.app j := by
            simp only [ht₁]
      _ = s ≫ α.app k ≫ X.map f := by
            simp only [α.naturality f]
      _ = X.map (g ≫ f) := by
            simpa only [Category.assoc, X.map_comp] using congrArg
              (fun q : X.obj l ⟶ X.obj k => q ≫ X.map f) hs₂
  · calc
      (Y.map g ≫ t ≫ α.app j) ≫ p.app j =
          Y.map g ≫ t ≫ β.app j := by
            simp only [Category.assoc, hc j]
      _ = Y.map (g ≫ f) := by
            simp only [ht₂, Y.map_comp]

omit [IsNoetherianRing A] in
private noncomputable def concreteHomologyMap (I : Ideal A)
    {K L M K' L' M' : ModuleCat.{u} A}
    (α : K ⟶ L) (β : L ⟶ M) (_h : α ≫ β = 0)
    (α' : K' ⟶ L') (β' : L' ⟶ M') (_h' : α' ≫ β' = 0)
    (u : K ⟶ K') (v : L ⟶ L') (w : M ⟶ M')
    (h₁ : u ≫ α' = α ≫ v) (h₂ : v ≫ β' = β ≫ w) :
    (((I • (⊤ : Submodule A M)).comap β.hom) ⧸
      (LinearMap.range α.hom ⊔ I • (⊤ : Submodule A L)).comap
        ((I • (⊤ : Submodule A M)).comap β.hom).subtype) →ₗ[A]
    (((I • (⊤ : Submodule A M')).comap β'.hom) ⧸
      (LinearMap.range α'.hom ⊔ I • (⊤ : Submodule A L')).comap
        ((I • (⊤ : Submodule A M')).comap β'.hom).subtype) :=
  let cyc := (I • (⊤ : Submodule A M)).comap β.hom
  let cyc' := (I • (⊤ : Submodule A M')).comap β'.hom
  let bd := LinearMap.range α.hom ⊔ I • (⊤ : Submodule A L)
  let bd' := LinearMap.range α'.hom ⊔ I • (⊤ : Submodule A L')
  let f := reductionCyclesMapOfSquare I β β' v w h₂
  Submodule.mapQ (bd.comap cyc.subtype) (bd'.comap cyc'.subtype) f (by
    intro x hx
    change (f x : L') ∈ bd'
    have hx' : (x : L) ∈ bd := hx
    obtain ⟨y, hy, z, hz, hxyz⟩ := Submodule.mem_sup.mp hx'
    obtain ⟨a, rfl⟩ := hy
    have hy' : v.hom (α.hom a) = α'.hom (u.hom a) :=
      congrArg (fun q : K ⟶ L' => q.hom a) h₁ |>.symm
    have hz' : v.hom z ∈ I • (⊤ : Submodule A L') :=
      (Submodule.smul_top_le_comap_smul_top I v.hom) hz
    change v.hom (x : L) ∈ bd'
    rw [← hxyz, map_add, hy']
    exact Submodule.add_mem_sup ⟨u.hom a, rfl⟩ hz')

omit [IsNoetherianRing A] in
private lemma concreteHomologyMap_mk (I : Ideal A)
    {K L M K' L' M' : ModuleCat.{u} A}
    (α : K ⟶ L) (β : L ⟶ M) (h : α ≫ β = 0)
    (α' : K' ⟶ L') (β' : L' ⟶ M') (h' : α' ≫ β' = 0)
    (u : K ⟶ K') (v : L ⟶ L') (w : M ⟶ M')
    (h₁ : u ≫ α' = α ≫ v) (h₂ : v ≫ β' = β ≫ w)
    (x : (I • (⊤ : Submodule A M)).comap β.hom) :
    concreteHomologyMap I α β h α' β' h' u v w h₁ h₂
        (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (reductionCyclesMapOfSquare I β β' v w h₂ x) := by
  rfl

omit [IsNoetherianRing A] in
private noncomputable def reductionShortComplexMap (I : Ideal A)
    {K L M K' L' M' : ModuleCat.{u} A}
    (α : K ⟶ L) (β : L ⟶ M) (h : α ≫ β = 0)
    (α' : K' ⟶ L') (β' : L' ⟶ M') (h' : α' ≫ β' = 0)
    (u : K ⟶ K') (v : L ⟶ L') (w : M ⟶ M')
    (h₁ : u ≫ α' = α ≫ v) (h₂ : v ≫ β' = β ≫ w) :
    reductionShortComplex I α β h ⟶ reductionShortComplex I α' β' h' where
  τ₁ := (redFunctor I).map u
  τ₂ := (redFunctor I).map v
  τ₃ := (redFunctor I).map w
  comm₁₂ := by
    change (redFunctor I).map u ≫ (redFunctor I).map α' =
      (redFunctor I).map α ≫ (redFunctor I).map v
    rw [← Functor.map_comp, ← Functor.map_comp, h₁]
  comm₂₃ := by
    change (redFunctor I).map v ≫ (redFunctor I).map β' =
      (redFunctor I).map β ≫ (redFunctor I).map w
    rw [← Functor.map_comp, ← Functor.map_comp, h₂]

/-- A map of short complexes of modules carries a cycle to a cycle exactly as it does on the
middle terms. -/
private lemma cyclesMap_moduleCatCyclesIso_inv
    {R : Type u} [CommRing R] {S T : ShortComplex (ModuleCat.{u} R)} (φ : S ⟶ T)
    (x : LinearMap.ker S.g.hom) (y : LinearMap.ker T.g.hom)
    (h : φ.τ₂.hom (x : S.X₂) = (y : T.X₂)) :
    (ShortComplex.cyclesMap φ).hom (S.moduleCatCyclesIso.inv x) = T.moduleCatCyclesIso.inv y := by
  apply (ModuleCat.mono_iff_injective T.iCycles).1 inferInstance
  change (ShortComplex.cyclesMap φ ≫ T.iCycles).hom (S.moduleCatCyclesIso.inv x) =
    (T.moduleCatCyclesIso.inv ≫ T.iCycles).hom y
  rw [ShortComplex.cyclesMap_i, T.moduleCatCyclesIso_inv_iCycles]
  change (S.moduleCatCyclesIso.inv ≫ S.iCycles ≫ φ.τ₂).hom x = _
  rw [← Category.assoc, S.moduleCatCyclesIso_inv_iCycles]
  exact h

omit [IsNoetherianRing A] in
private lemma reductionCyclesMap_naturality_abstract (I : Ideal A)
    {K L M K' L' M' : ModuleCat.{u} A}
    (α : K ⟶ L) (β : L ⟶ M) (h : α ≫ β = 0)
    (α' : K' ⟶ L') (β' : L' ⟶ M') (h' : α' ≫ β' = 0)
    (u : K ⟶ K') (v : L ⟶ L') (w : M ⟶ M')
    (h₁ : u ≫ α' = α ≫ v) (h₂ : v ≫ β' = β ≫ w)
    (x : (I • (⊤ : Submodule A M)).comap β.hom) :
    (ShortComplex.cyclesMap
      (reductionShortComplexMap I α β h α' β' h' u v w h₁ h₂)).hom
      ((reductionShortComplex I α β h).moduleCatCyclesIso.inv
        (reductionCyclesMap I β x)) =
      (reductionShortComplex I α' β' h').moduleCatCyclesIso.inv
        (reductionCyclesMap I β'
          (reductionCyclesMapOfSquare I β β' v w h₂ x)) := by
  exact cyclesMap_moduleCatCyclesIso_inv _ _ _ (reductionCyclesMap_naturality I β β' v w h₂ x).symm

omit [IsNoetherianRing A] in
/-- A map of short complexes of modules carries the class of a cycle to the class of its image,
read through the concrete presentations of homology. -/
lemma homologyMap_moduleCatHomologyIso_inv_π
    {S T : ShortComplex (ModuleCat.{u} A)} (φ : S ⟶ T)
    (x : S.moduleCatLeftHomologyData.K) (y : T.moduleCatLeftHomologyData.K)
    (hxy : (ShortComplex.cyclesMap φ).hom (S.moduleCatCyclesIso.inv x) =
      T.moduleCatCyclesIso.inv y) :
    (ShortComplex.homologyMap φ).hom
        (S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π.hom x)) =
      T.moduleCatHomologyIso.inv (T.moduleCatLeftHomologyData.π.hom y) := by
  change (S.moduleCatLeftHomologyData.π ≫ S.moduleCatHomologyIso.inv ≫
    ShortComplex.homologyMap φ).hom x = _
  rw [← S.moduleCatCyclesIso_inv_π_assoc, ShortComplex.homologyπ_naturality]
  change T.homologyπ.hom
    ((ShortComplex.cyclesMap φ).hom (S.moduleCatCyclesIso.inv x)) = _
  rw [hxy]
  exact congrArg (fun f : T.moduleCatLeftHomologyData.K ⟶ T.homology => f.hom y)
    T.moduleCatCyclesIso_inv_π

omit [IsNoetherianRing A] in
private lemma concreteHomologyMap_naturality (I : Ideal A)
    {K L M K' L' M' : ModuleCat.{u} A}
    (α : K ⟶ L) (β : L ⟶ M) (h : α ≫ β = 0)
    (α' : K' ⟶ L') (β' : L' ⟶ M') (h' : α' ≫ β' = 0)
    (u : K ⟶ K') (v : L ⟶ L') (w : M ⟶ M')
    (h₁ : u ≫ α' = α ≫ v) (h₂ : v ≫ β' = β ≫ w) :
    let S := reductionShortComplex I α β h
    let S' := reductionShortComplex I α' β' h'
    let φ := reductionShortComplexMap I α β h α' β' h' u v w h₁ h₂
    ∀ x : (I • (⊤ : Submodule A M)).comap β.hom,
      (ShortComplex.homologyMap φ).hom
          (S.moduleCatHomologyIso.inv
            (reductionHomologyEquiv I α β h (Submodule.Quotient.mk x))) =
        S'.moduleCatHomologyIso.inv
          (reductionHomologyEquiv I α' β' h'
            (concreteHomologyMap I α β h α' β' h' u v w h₁ h₂
              (Submodule.Quotient.mk x))) := by
  intro S S' φ x
  rw [reductionHomologyEquiv_mk, concreteHomologyMap_mk,
    reductionHomologyEquiv_mk]
  exact homologyMap_moduleCatHomologyIso_inv_π φ _ _
    (reductionCyclesMap_naturality_abstract I α β h α' β' h' u v w h₁ h₂ x)

omit [IsNoetherianRing A] in
/-- Enlarging the ideal enlarges the concrete cycles of a reduced complex. -/
def reductionCyclesMapOfIdealLE {J K : Ideal A} (h : J ≤ K)
    {L M : ModuleCat.{u} A} (β : L ⟶ M) :
    ((J • (⊤ : Submodule A M)).comap β.hom) →ₗ[A]
      ((K • (⊤ : Submodule A M)).comap β.hom) :=
  Submodule.inclusion (by
    intro x hx
    exact (Submodule.smul_mono_left h) hx)

omit [IsNoetherianRing A] in
/-- The concrete cycles of a reduced complex commute with enlarging the ideal. -/
lemma reductionCyclesMap_ideal_naturality {J K : Ideal A} (h : J ≤ K)
    {L M : ModuleCat.{u} A} (β : L ⟶ M)
    (x : (J • (⊤ : Submodule A M)).comap β.hom) :
    ((reductionCyclesMap K β (reductionCyclesMapOfIdealLE h β x) :
        (redFunctor K).obj L)) =
      ((reductionNatTrans h).app L).hom (reductionCyclesMap J β x) := by
  rfl

omit [IsNoetherianRing A] in
/-- The transition in the concrete presentation of the homology of the reduced complexes, as the
ideal grows. -/
noncomputable def concreteHomologyIdealTransition {J K : Ideal A}
    (hJK : J ≤ K) {L₁ L₂ L₃ : ModuleCat.{u} A}
    (α : L₁ ⟶ L₂) (β : L₂ ⟶ L₃) (_h : α ≫ β = 0) :
    (((J • (⊤ : Submodule A L₃)).comap β.hom) ⧸
      (LinearMap.range α.hom ⊔ J • (⊤ : Submodule A L₂)).comap
        ((J • (⊤ : Submodule A L₃)).comap β.hom).subtype) →ₗ[A]
    (((K • (⊤ : Submodule A L₃)).comap β.hom) ⧸
      (LinearMap.range α.hom ⊔ K • (⊤ : Submodule A L₂)).comap
        ((K • (⊤ : Submodule A L₃)).comap β.hom).subtype) :=
  let cycJ := (J • (⊤ : Submodule A L₃)).comap β.hom
  let cycK := (K • (⊤ : Submodule A L₃)).comap β.hom
  let bdJ := LinearMap.range α.hom ⊔ J • (⊤ : Submodule A L₂)
  let bdK := LinearMap.range α.hom ⊔ K • (⊤ : Submodule A L₂)
  Submodule.mapQ (bdJ.comap cycJ.subtype) (bdK.comap cycK.subtype)
    (reductionCyclesMapOfIdealLE hJK β) (by
      intro x hx
      change (x : L₂) ∈ bdK
      change (x : L₂) ∈ bdJ at hx
      have hI : J • (⊤ : Submodule A L₂) ≤ K • (⊤ : Submodule A L₂) :=
        Submodule.smul_mono_left hJK
      exact (sup_le_sup (le_refl _) hI) hx)

omit [IsNoetherianRing A] in
/-- The ideal transition sends the class of `x` to the class of its image in the larger
reduction. -/
lemma concreteHomologyIdealTransition_mk {J K : Ideal A}
    (hJK : J ≤ K) {L₁ L₂ L₃ : ModuleCat.{u} A}
    (α : L₁ ⟶ L₂) (β : L₂ ⟶ L₃) (h : α ≫ β = 0)
    (x : (J • (⊤ : Submodule A L₃)).comap β.hom) :
    concreteHomologyIdealTransition hJK α β h (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (reductionCyclesMapOfIdealLE hJK β x) := by
  rfl

omit [IsNoetherianRing A] in
/-- The map of reduced short complexes induced by enlarging the ideal. -/
noncomputable def reductionShortComplexIdealMap {J K : Ideal A}
    (hJK : J ≤ K) {L₁ L₂ L₃ : ModuleCat.{u} A}
    (α : L₁ ⟶ L₂) (β : L₂ ⟶ L₃) (h : α ≫ β = 0) :
    reductionShortComplex J α β h ⟶ reductionShortComplex K α β h where
  τ₁ := (reductionNatTrans hJK).app L₁
  τ₂ := (reductionNatTrans hJK).app L₂
  τ₃ := (reductionNatTrans hJK).app L₃
  comm₁₂ := ((reductionNatTrans hJK).naturality α).symm
  comm₂₃ := ((reductionNatTrans hJK).naturality β).symm

omit [IsNoetherianRing A] in
/-- Naturality of the concrete cycles map in the ideal, read through the cycles of the reduced
short complexes. -/
lemma reductionCyclesMap_ideal_naturality_abstract {J K : Ideal A}
    (hJK : J ≤ K) {L₁ L₂ L₃ : ModuleCat.{u} A}
    (α : L₁ ⟶ L₂) (β : L₂ ⟶ L₃) (h : α ≫ β = 0)
    (x : (J • (⊤ : Submodule A L₃)).comap β.hom) :
    (ShortComplex.cyclesMap (reductionShortComplexIdealMap hJK α β h)).hom
      ((reductionShortComplex J α β h).moduleCatCyclesIso.inv
        (reductionCyclesMap J β x)) =
      (reductionShortComplex K α β h).moduleCatCyclesIso.inv
        (reductionCyclesMap K β (reductionCyclesMapOfIdealLE hJK β x)) := by
  exact cyclesMap_moduleCatCyclesIso_inv _ _ _ (reductionCyclesMap_ideal_naturality hJK β x).symm

omit [IsNoetherianRing A] in
/-- The ideal transition agrees with the homology map of the reduced short complexes. -/
lemma concreteHomologyIdealTransition_naturality {J K : Ideal A}
    (hJK : J ≤ K) {L₁ L₂ L₃ : ModuleCat.{u} A}
    (α : L₁ ⟶ L₂) (β : L₂ ⟶ L₃) (h : α ≫ β = 0)
    (x : ((J • (⊤ : Submodule A L₃)).comap β.hom) ⧸
      (LinearMap.range α.hom ⊔ J • (⊤ : Submodule A L₂)).comap
        ((J • (⊤ : Submodule A L₃)).comap β.hom).subtype) :
    (ShortComplex.homologyMap (reductionShortComplexIdealMap hJK α β h)).hom
        ((reductionShortComplex J α β h).moduleCatHomologyIso.inv
          (reductionHomologyEquiv J α β h x)) =
      (reductionShortComplex K α β h).moduleCatHomologyIso.inv
        (reductionHomologyEquiv K α β h
          (concreteHomologyIdealTransition hJK α β h x)) := by
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  simp only [Submodule.mkQ_apply]
  rw [concreteHomologyIdealTransition_mk, reductionHomologyEquiv_mk,
    reductionHomologyEquiv_mk]
  exact homologyMap_moduleCatHomologyIso_inv_π
    (reductionShortComplexIdealMap hJK α β h) _ _
    (reductionCyclesMap_ideal_naturality_abstract hJK α β h x)

omit [IsNoetherianRing A] in
/-- The concrete presentation of the homology of a degreewise reduction is compatible with
enlarging the ideal. -/
lemma reducedHomologyConcreteEquiv_ideal_naturality {J K : Ideal A}
    (hJK : J ≤ K) (M : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (x : ((J • (⊤ : Submodule A (M.sc i).X₃)).comap (M.sc i).g.hom) ⧸
      (LinearMap.range (M.sc i).f.hom ⊔ J • (⊤ : Submodule A (M.sc i).X₂)).comap
        ((J • (⊤ : Submodule A (M.sc i).X₃)).comap (M.sc i).g.hom).subtype) :
    (HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (reductionNatTrans hJK)
          (ComplexShape.up ℤ)).app M) i).hom
        (reducedHomologyConcreteEquiv J M i x) =
      reducedHomologyConcreteEquiv K M i
        (concreteHomologyIdealTransition hJK (M.sc i).f (M.sc i).g (M.sc i).zero x) := by
  exact concreteHomologyIdealTransition_naturality hJK
    (M.sc i).f (M.sc i).g (M.sc i).zero x

omit [IsNoetherianRing A] in
private lemma adicReductionComparison_naturality_of_le
    (I : Ideal A) {P M : CochainComplex (ModuleCat.{u} A) ℤ}
    (p : P ⟶ M) {n m : ℕ} (h : n ≤ m) :
    adicReductionTransition I P h ≫ adicReductionComparison I p n =
      adicReductionComparison I p m ≫ adicReductionTransition I M h := by
  let η := NatTrans.mapHomologicalComplex
    (reductionNatTrans (A := A)
      (Ideal.pow_le_pow_right (I := I) (Nat.add_le_add_right h 1)))
    (ComplexShape.up ℤ)
  have h := η.naturality p
  simpa only [adicReductionTransition, adicReductionComparison, reduceComplex,
    ← Functor.map_comp] using (congrArg (fun f => DerivedCategory.Q.map f) h).symm

omit [IsNoetherianRing A] in
private lemma adicReductionComparison_naturality
    (I : Ideal A) {P M : CochainComplex (ModuleCat.{u} A) ℤ}
    (p : P ⟶ M) (n : ℕ) :
    adicReductionTransition I P (Nat.le_succ n) ≫ adicReductionComparison I p n =
      adicReductionComparison I p (n + 1) ≫
        adicReductionTransition I M (Nat.le_succ n) :=
  adicReductionComparison_naturality_of_le I p (Nat.le_succ n)

omit [IsNoetherianRing A] in
private lemma reductionNatTrans_id (J : Ideal A) :
    reductionNatTrans (le_refl J) = 𝟙 (redFunctor J) := by
  ext M x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule A M)) x
  rfl

omit [IsNoetherianRing A] in
private lemma reductionNatTrans_comp {J K L : Ideal A} (hJK : J ≤ K) (hKL : K ≤ L) :
    reductionNatTrans hJK ≫ reductionNatTrans hKL = reductionNatTrans (hJK.trans hKL) := by
  ext M x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (J • (⊤ : Submodule A M)) x
  rfl

omit [IsNoetherianRing A] in
private lemma adicReductionTransition_refl (I : Ideal A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ) :
    adicReductionTransition I K (le_refl n) = 𝟙 _ := by
  unfold adicReductionTransition
  rw [reductionNatTrans_id, NatTrans.mapHomologicalComplex_id]
  simpa only [reduceComplex, NatTrans.id_app] using
    (DerivedCategory.Q.map_id
      (((redFunctor (I ^ (n + 1))).mapHomologicalComplex (ComplexShape.up ℤ)).obj K))

omit [IsNoetherianRing A] in
private lemma adicReductionTransition_comp (I : Ideal A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k) :
    adicReductionTransition I K hmk ≫ adicReductionTransition I K hnm =
      adicReductionTransition I K (hnm.trans hmk) := by
  unfold adicReductionTransition
  simp only [reduceComplex]
  rw [← Functor.map_comp, ← NatTrans.comp_app,
    ← NatTrans.mapHomologicalComplex_comp, reductionNatTrans_comp]

private noncomputable def adicReductionSystem (I : Ideal A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) where
  obj n := DerivedCategory.Q.obj ((reduceComplex (I ^ (n.unop + 1))).obj K)
  map {n m} f := adicReductionTransition I K (leOfHom f.unop)
  map_id n := by
    simpa using adicReductionTransition_refl I K n.unop
  map_comp f g := by
    simpa using
      (adicReductionTransition_comp I K (leOfHom g.unop) (leOfHom f.unop)).symm

private noncomputable def adicReductionComparisonNatTrans (I : Ideal A)
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) :
    adicReductionSystem I P ⟶ adicReductionSystem I M where
  app n := adicReductionComparison I p n.unop
  naturality {n m} f := by
    exact adicReductionComparison_naturality_of_le I p (leOfHom f.unop)

omit [IsNoetherianRing A] in
private lemma homology_adicReductionSystem_isZero_outside
    (I : Ideal A) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (a b : ℤ) (hMa : M.IsStrictlyGE a) (hMb : M.IsStrictlyLE b)
    (i : ℤ) (hi : i < a ∨ b < i) (n : ℕᵒᵖ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((adicReductionSystem I M).obj n)) := by
  let E := (reduceComplex (I ^ (n.unop + 1))).obj M
  have hX : IsZero (E.X i) := by
    change IsZero ((redFunctor (I ^ (n.unop + 1))).obj (M.X i))
    rcases hi with hi | hi
    · exact (redFunctor (I ^ (n.unop + 1))).map_isZero
        (M.isZero_of_isStrictlyGE a i hi)
    · exact (redFunctor (I ^ (n.unop + 1))).map_isZero
        (M.isZero_of_isStrictlyLE b i hi)
  exact KoszulIdealPower.isZero_homology_Q_obj_of_isZero_X E i hX

omit [IsNoetherianRing A] in
private lemma adicReductionComparison_proInverse_of_homology
    (I : Ideal A) {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M)
    (a b : ℤ)
    (hP : ∀ i : ℤ, i < a ∨ b < i → ∀ n : ℕᵒᵖ,
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((adicReductionSystem I P).obj n)))
    (hM : ∀ i : ℤ, i < a ∨ b < i → ∀ n : ℕᵒᵖ,
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        ((adicReductionSystem I M).obj n)))
    (hH : ∀ (i : ℤ) (n : ℕᵒᵖ), ∃ (k : ℕᵒᵖ) (f : k ⟶ n)
      (s : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((adicReductionSystem I M).obj k) ⟶
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
          ((adicReductionSystem I P).obj n)),
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
          ((adicReductionComparisonNatTrans I p).app k) ≫ s =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
          ((adicReductionSystem I P).map f) ∧
      s ≫ (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
          ((adicReductionComparisonNatTrans I p).app n) =
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map
          ((adicReductionSystem I M).map f))
    (n : ℕ) :
    ∃ (m : ℕ) (h : n ≤ m)
      (s : DerivedCategory.Q.obj ((reduceComplex (I ^ (m + 1))).obj M) ⟶
        DerivedCategory.Q.obj ((reduceComplex (I ^ (n + 1))).obj P)),
      adicReductionComparison I p m ≫ s = adicReductionTransition I P h ∧
      s ≫ adicReductionComparison I p n = adicReductionTransition I M h := by
  obtain ⟨k, f, s, hs₁, hs₂⟩ :=
    DerivedCategory.exists_proInverse_of_proInverse_homology
      (adicReductionComparisonNatTrans I p) a b hP hM hH (op n)
  refine ⟨k.unop, leOfHom f.unop, s, ?_, ?_⟩
  · exact hs₁
  · exact hs₂


private abbrev HasProInverse {J C : Type*} [Category J] [Category C]
    {X Y : J ⥤ C} (α : X ⟶ Y) : Prop :=
  ∀ j : J, ∃ (k : J) (f : k ⟶ j) (s : Y.obj k ⟶ X.obj j),
    α.app k ≫ s = X.map f ∧ s ≫ α.app j = Y.map f

private lemma HasProInverse.whiskerRight {J C D : Type*}
    [Category J] [Category C] [Category D]
    {X Y : J ⥤ C} {α : X ⟶ Y} (hα : HasProInverse α) (F : C ⥤ D) :
    HasProInverse (Functor.whiskerRight α F) := by
  intro j
  obtain ⟨k, f, s, hs, hs'⟩ := hα j
  refine ⟨k, f, F.map s, ?_, ?_⟩
  · simpa only [Functor.whiskerRight_app, Functor.comp_map, ← F.map_comp] using
      congrArg F.map hs
  · simpa only [Functor.whiskerRight_app, Functor.comp_map, ← F.map_comp] using
      congrArg F.map hs'

private lemma HasProInverse.comp {J C : Type*} [Category J] [Category C]
    {X Y Z : J ⥤ C} {α : X ⟶ Y} {β : Y ⟶ Z}
    (hα : HasProInverse α) (hβ : HasProInverse β) :
    HasProInverse (α ≫ β) := by
  intro j
  obtain ⟨k, f, s, hs, hs'⟩ := hα j
  obtain ⟨l, g, t, ht, ht'⟩ := hβ k
  refine ⟨l, g ≫ f, t ≫ s, ?_, ?_⟩
  · change (α.app l ≫ β.app l) ≫ t ≫ s = _
    rw [Category.assoc, ← Category.assoc (β.app l), ht,
      ← Category.assoc, ← α.naturality g, Category.assoc, hs, ← X.map_comp]
  · change (t ≫ s) ≫ (α.app j ≫ β.app j) = _
    rw [Category.assoc, ← Category.assoc s, hs', β.naturality f,
      ← Category.assoc, ht', ← Z.map_comp]

/-- `HasProInverse` for a map of inverse sequences, with levels indexed by `ℕ`. -/
private lemma hasProInverse_iff_nat {C : Type*} [Category C] {X Y : ℕᵒᵖ ⥤ C} (e : X ⟶ Y) :
    HasProInverse e ↔ ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m) (s : Y.obj (op m) ⟶ X.obj (op n)),
      e.app (op m) ≫ s = X.map (homOfLE h).op ∧ s ≫ e.app (op n) = Y.map (homOfLE h).op := by
  refine ⟨fun H n => ?_, fun H j => ?_⟩
  · obtain ⟨k, f, s, hs, hs'⟩ := H (op n)
    exact ⟨k.unop, leOfHom f.unop, s, hs, hs'⟩
  · obtain ⟨m, h, s, hs, hs'⟩ := H j.unop
    exact ⟨op m, (homOfLE h).op, s, hs, hs'⟩

private lemma hasProInverse_of_isIso {J C : Type*} [Category J] [Category C]
    {X Y : J ⥤ C} (α : X ⟶ Y) [IsIso α] : HasProInverse α := by
  intro j
  refine ⟨j, 𝟙 j, inv (α.app j), ?_, ?_⟩ <;> simp

omit [IsNoetherianRing A] in
private lemma quasiIso_tensorRight_map
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K.KFlat)
    {L M : CochainComplex (ModuleCat.{u} A) ℤ} (f : L ⟶ M) [QuasiIso f] :
    QuasiIso ((TrightCochain K).map f) := by
  have hf := (HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 ‹QuasiIso f›
  have h := (_root_.CochainComplex.KFlat.kFlat_tright_preserves_quasiIso K hK)
    ((HomotopyCategory.quotient _ _).map f) hf
  change HomotopyCategory.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ)
    ((HomotopyCategory.quotient _ _ ⋙ Tright K).map f) at h
  unfold Tright at h
  rw [descendF_comp_quotient] at h
  exact (HomotopyCategory.quotient_map_mem_quasiIso_iff _).1 h

omit [IsNoetherianRing A] in
private noncomputable def tensorRightDerived
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K.KFlat) :
    DerivedCategory (ModuleCat.{u} A) ⥤ DerivedCategory (ModuleCat.{u} A) :=
  Localization.lift (W := HomologicalComplex.quasiIso (ModuleCat.{u} A) (ComplexShape.up ℤ))
    (TrightCochain K ⋙ DerivedCategory.Q)
    (fun _ _ f hf ↦ by
      have : QuasiIso f := hf
      have := quasiIso_tensorRight_map K hK f
      exact (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 this)
    DerivedCategory.Q

omit [IsNoetherianRing A] in
private noncomputable def tensorRightDerivedFactors
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K.KFlat) :
    DerivedCategory.Q ⋙ tensorRightDerived K hK ≅ TrightCochain K ⋙ DerivedCategory.Q :=
  Localization.fac _ _ _

private lemma koszul_tensorRight_hasProInverse
    {r : ℕ} (f : Fin r → A) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (hP : P.KFlat) : HasProInverse
      (Functor.whiskerRight (NoetherianKoszulProIso.koszulQuotientComparison f)
        (tensorRightDerived P hP)) := by
  apply HasProInverse.whiskerRight
  exact (hasProInverse_iff_nat _).2
    (NoetherianKoszulProIso.koszulPowerSystem_proIso_quotientPowerSystem f)


open CategoryTheory.MonoidalCategory HomologicalComplex

set_option backward.isDefEq.respectTransparency false

omit [IsNoetherianRing A] in
/-- Tensoring a complex with a module placed in degree `0` is, degreewise, tensoring with that
module. -/
noncomputable def singleTensorXIso
    (N : ModuleCat.{u} A) (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) :
    (HomologicalComplex.tensorObj ((CochainComplex.singleFunctor _ 0).obj N) K).X n ≅
      (tensorLeft N).obj (K.X n) where
  hom := mapBifunctorDesc fun p q hpq => by
    by_cases hp : p = 0
    · subst p
      have hq : q = n := by simpa using hpq
      subst q
      exact 𝟙 _
    · exact 0
  inv := ιTensorObj ((CochainComplex.singleFunctor _ 0).obj N) K 0 n n (zero_add n)
  hom_inv_id := by
    apply mapBifunctor.hom_ext
    intro p q hpq
    rw [ι_mapBifunctorDesc_assoc]
    by_cases hp : p = 0
    · subst p
      have hq : q = n := by simpa using hpq
      subst q
      simp
    · have hz := HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) 0 N p hp
      exact ((tensorRight (K.X q)).map_isZero hz).eq_of_src _ _
  inv_hom_id := by
    change ιTensorObj ((CochainComplex.singleFunctor _ 0).obj N) K 0 n n _ ≫ _ = _
    rw [ι_mapBifunctorDesc]
    simp
    rfl

omit [IsNoetherianRing A] in
/-- The degreewise comparison of `N ⊗ K` with the tensor product of complexes commutes with the
differentials. -/
lemma singleTensorXIso_inv_comm
    (N : ModuleCat.{u} A) (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (singleTensorXIso N K i).inv ≫
        (HomologicalComplex.tensorObj ((CochainComplex.singleFunctor _ 0).obj N) K).d i j =
      (tensorLeft N).map (K.d i j) ≫ (singleTensorXIso N K j).inv := by
  change ιTensorObj ((CochainComplex.singleFunctor _ 0).obj N) K 0 i i _ ≫ _ = _
  rw [mapBifunctor.d_eq, Preadditive.comp_add,
    mapBifunctor.ι_D₁, mapBifunctor.ι_D₂,
    mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel 0 1 from rfl) i j
      (by change 1 + i = j; change i + 1 = j at hij; omega),
    mapBifunctor.d₂_eq _ _ _ _ 0 hij j (by change 0 + j = j; omega)]
  simp only [CochainComplex.singleFunctor_obj_d, Functor.map_zero,
    Limits.zero_app, zero_comp, smul_zero, zero_add]
  change (1 : ℤˣ) • ((tensorLeft N).map (K.d i j) ≫ _) = _
  rw [one_smul]
  rfl

omit [IsNoetherianRing A] in
/-- Tensoring with a module placed in degree `0` is the degreewise tensor product. -/
noncomputable def singleTensorIso
    (N : ModuleCat.{u} A) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    HomologicalComplex.tensorObj ((CochainComplex.singleFunctor _ 0).obj N) K ≅
      ((tensorLeft N).mapHomologicalComplex (ComplexShape.up ℤ)).obj K :=
  (HomologicalComplex.Hom.isoOfComponents
    (fun n => (singleTensorXIso N K n).symm)
    (fun i j hij => singleTensorXIso_inv_comm N K i j hij)).symm

omit [IsNoetherianRing A] in
/-- The comparison of `N ⊗ K` with the tensor product of complexes is natural in `N` and `K`. -/
lemma singleTensorIso_inv_naturality
    {N N' : ModuleCat.{u} A} (f : N ⟶ N')
    {K K' : CochainComplex (ModuleCat.{u} A) ℤ} (g : K ⟶ K') :
    (singleTensorIso N K).inv ≫
        HomologicalComplex.tensorHom ((CochainComplex.singleFunctor _ 0).map f) g =
      ((NatTrans.mapHomologicalComplex ((curriedTensor (ModuleCat.{u} A)).map f)
        (ComplexShape.up ℤ)).app K ≫
        ((tensorLeft N').mapHomologicalComplex (ComplexShape.up ℤ)).map g) ≫
          (singleTensorIso N' K').inv := by
  ext n : 1
  change ιTensorObj ((CochainComplex.singleFunctor _ 0).obj N) K 0 n n _ ≫
    (HomologicalComplex.tensorHom ((CochainComplex.singleFunctor _ 0).map f) g).f n = _
  rw [ι_mapBifunctorMap]
  rfl

omit [IsNoetherianRing A] in
/-- Tensoring with `A/I` is reduction modulo `I`. -/
@[ega "III 7.4.7.2" "more general"]
noncomputable def quotientTensorIsoReduction (I : Ideal A) :
    tensorLeft (ModuleCat.of A (A ⧸ I)) ≅ redFunctor I :=
  NatIso.ofComponents (fun N => (TensorProduct.quotTensorEquivQuotSMul N I).toModuleIso)
    (by
      intro N N' f
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro x y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      change TensorProduct.quotTensorEquivQuotSMul N' I
        (Ideal.Quotient.mk I x ⊗ₜ[A] f.hom y) =
        ((redFunctor I).map f).hom
          (TensorProduct.quotTensorEquivQuotSMul N I (Ideal.Quotient.mk I x ⊗ₜ[A] y))
      simp only [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
      change Submodule.Quotient.mk (x • f.hom y) = Submodule.Quotient.mk (f.hom (x • y))
      rw [map_smul])

omit [IsNoetherianRing A] in
/-- Tensoring a complex with `A/I` placed in degree `0` is its degreewise reduction. -/
noncomputable def singleQuotientTensorIsoReduction
    (I : Ideal A) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    HomologicalComplex.tensorObj
      ((CochainComplex.singleFunctor _ 0).obj (ModuleCat.of A (A ⧸ I))) K ≅
      (reduceComplex I).obj K :=
  singleTensorIso _ K ≪≫
    (NatIso.mapHomologicalComplex (quotientTensorIsoReduction I) (ComplexShape.up ℤ)).app K

omit [IsNoetherianRing A] in
/-- The canonical map `A/I ⟶ A/J` of `A`-modules for `I ≤ J`. -/
noncomputable def quotientModuleMap {I J : Ideal A} (h : I ≤ J) :
    ModuleCat.of A (A ⧸ I) ⟶ ModuleCat.of A (A ⧸ J) :=
  ModuleCat.ofHom (Submodule.mapQ I J LinearMap.id h)

omit [IsNoetherianRing A] in
private lemma quotientModuleMap_one {I J : Ideal A} (h : I ≤ J) :
    (quotientModuleMap h).hom 1 = 1 := rfl

omit [IsNoetherianRing A] in
/-- Tensoring with `A/I` agrees with reduction modulo `I`, naturally in the ideal and in the
module. -/
lemma quotientTensorIsoReduction_inv_naturality
    {I J : Ideal A} (h : I ≤ J) {N N' : ModuleCat.{u} A} (f : N ⟶ N') :
    (reductionNatTrans h).app N ≫ (redFunctor J).map f ≫
        (quotientTensorIsoReduction J).inv.app N' =
      (quotientTensorIsoReduction I).inv.app N ≫
        ((curriedTensor (ModuleCat.{u} A)).map (quotientModuleMap h)).app N ≫
          (tensorLeft (ModuleCat.of A (A ⧸ J))).map f := by
  apply ModuleCat.hom_ext
  ext x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (I • (⊤ : Submodule A N)) x
  change (TensorProduct.quotTensorEquivQuotSMul N' J).symm (Submodule.Quotient.mk (f.hom x)) =
    (TensorProduct.map (quotientModuleMap h).hom f.hom)
      ((TensorProduct.quotTensorEquivQuotSMul N I).symm (Submodule.Quotient.mk x))
  simp only [TensorProduct.quotTensorEquivQuotSMul_symm_mk, TensorProduct.map_tmul,
    ]
  rfl

omit [IsNoetherianRing A] in
/-- The comparison of `A/I ⊗ K` with the degreewise reduction of `K` is natural in the ideal and
in `K`. -/
lemma singleQuotientTensorIsoReduction_inv_naturality
    {I J : Ideal A} (h : I ≤ J)
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (p : K ⟶ L) :
    ((NatTrans.mapHomologicalComplex (reductionNatTrans h) (ComplexShape.up ℤ)).app K ≫
        (reduceComplex J).map p) ≫ (singleQuotientTensorIsoReduction J L).inv =
      (singleQuotientTensorIsoReduction I K).inv ≫
        HomologicalComplex.tensorHom
          ((CochainComplex.singleFunctor _ 0).map (quotientModuleMap h)) p := by
  unfold singleQuotientTensorIsoReduction
  simp only [Iso.trans_inv, Iso.app_inv]
  simp only [Category.assoc]
  rw [singleTensorIso_inv_naturality]
  simp only [← Category.assoc]
  congr 1
  ext n : 1
  exact quotientTensorIsoReduction_inv_naturality h (p.f n)

omit [IsNoetherianRing A] in
/-- Extending a map of single chain complexes is compatible with the comparison isomorphism of
the extended single complexes. -/
lemma extendSingleIso_naturality
    {N N' : ModuleCat.{u} A} (f : N ⟶ N') :
    HomologicalComplex.extendMap ((ChainComplex.single₀ _).map f)
        ComplexShape.embeddingDownNat ≫
          (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat N' 0 0 rfl).hom =
      (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat N 0 0 rfl).hom ≫
        (CochainComplex.singleFunctor _ 0).map f := by
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : n = 0
  · subst n
    simp [HomologicalComplex.comp_f, extendSingleIso_hom_f,
      extendMap_f _ _ (show ComplexShape.embeddingDownNat.f 0 = 0 from rfl),
      HomologicalComplex.single_map_f_self]
    rfl
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N' n hn).eq_of_tgt _ _

omit [IsNoetherianRing A] in
private noncomputable def idealReductionSystem (J : ℕ → Ideal A) (hJ : Antitone J)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) where
  obj n := DerivedCategory.Q.obj ((reduceComplex (J n.unop)).obj K)
  map f := DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex (reductionNatTrans (hJ (leOfHom f.unop)))
      (ComplexShape.up ℤ)).app K)
  map_id n := by
    rw [show hJ (leOfHom (𝟙 n).unop) = le_refl (J n.unop) from Subsingleton.elim _ _,
      reductionNatTrans_id, NatTrans.mapHomologicalComplex_id]
    exact DerivedCategory.Q.map_id _
  map_comp f g := by
    rw [← Functor.map_comp, ← NatTrans.comp_app,
      ← NatTrans.mapHomologicalComplex_comp, reductionNatTrans_comp]

omit [IsNoetherianRing A] in
private noncomputable def idealReductionComparison
    {J J' : ℕ → Ideal A} (hJ : Antitone J) (hJ' : Antitone J') (h : J ≤ J')
    (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    idealReductionSystem J hJ K ⟶ idealReductionSystem J' hJ' K where
  app n := DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex (reductionNatTrans (h n.unop))
      (ComplexShape.up ℤ)).app K)
  naturality n m f := by
    dsimp only [idealReductionSystem]
    rw [← Functor.map_comp, ← Functor.map_comp, ← NatTrans.comp_app,
      ← NatTrans.comp_app, ← NatTrans.mapHomologicalComplex_comp,
      ← NatTrans.mapHomologicalComplex_comp, reductionNatTrans_comp, reductionNatTrans_comp]

omit [IsNoetherianRing A] in
private lemma idealReductionComparison_hasProInverse
    {J J' : ℕ → Ideal A} (hJ : Antitone J) (hJ' : Antitone J') (h : J ≤ J')
    (hc : ∀ n, ∃ m, J' m ≤ J n) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    HasProInverse (idealReductionComparison hJ hJ' h K) := by
  intro n
  obtain ⟨m, hm⟩ := hc n.unop
  let k := max m n.unop
  have hkn : n.unop ≤ k := le_max_right _ _
  have hk : J' k ≤ J n.unop := (hJ' (le_max_left _ _)).trans hm
  refine ⟨op k, (homOfLE hkn).op, DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex (reductionNatTrans hk) (ComplexShape.up ℤ)).app K),
    ?_, ?_⟩ <;>
    dsimp only [idealReductionComparison, idealReductionSystem] <;>
    rw [← Functor.map_comp, ← NatTrans.comp_app,
      ← NatTrans.mapHomologicalComplex_comp, reductionNatTrans_comp]

omit [IsNoetherianRing A] in
private lemma generatorPowers_antitone {r : ℕ} (f : Fin r → A) :
    Antitone (fun n : ℕ => Ideal.span (Set.range fun i => f i ^ (n + 1))) := by
  intro n m h
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change f i ^ (m + 1) ∈ Ideal.span (Set.range fun i => f i ^ (n + 1))
  rw [show m + 1 = (n + 1) + (m - n) by omega, pow_add]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

omit [IsNoetherianRing A] in
private lemma quotientPowerTransition_eq {r : ℕ} (f : Fin r → A)
    (m n : ℕ) (h : n ≤ m) :
    NoetherianKoszulProIso.quotientPowerTransition f m n h =
      quotientModuleMap (generatorPowers_antitone f h) := by
  let q := ModuleCat.ofHom (Ideal.span (Set.range fun i => f i ^ (m + 1))).mkQ
  have : Epi q := (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)
  apply (cancel_epi q).1
  exact NoetherianKoszulProIso.quotientPowerTransition_comp_mkQ f m n h

omit [IsNoetherianRing A] in
/-- Tensoring a complex on the right with the extended single complex `A/I` is its degreewise
reduction. -/
@[ega "IV 12.3.3.5" "more general"]
noncomputable def extendedSingleQuotientTensorIsoReduction
    (I : Ideal A) (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (TrightCochain P).obj
      (((ChainComplex.single₀ _).obj (ModuleCat.of A (A ⧸ I))).extend
        ComplexShape.embeddingDownNat) ≅ (reduceComplex I).obj P :=
  (TrightCochain P).mapIso
    (HomologicalComplex.extendSingleIso ComplexShape.embeddingDownNat _ 0 0 rfl) ≪≫
      singleQuotientTensorIsoReduction I P

omit [IsNoetherianRing A] in
/-- The comparison of `A/I ⊗ P` with the degreewise reduction of `P` is natural in the ideal. -/
lemma singleQuotientTensorIsoReduction_naturality
    {I J : Ideal A} (h : I ≤ J) (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (TrightCochain P).map ((CochainComplex.singleFunctor _ 0).map (quotientModuleMap h)) ≫
        (singleQuotientTensorIsoReduction J P).hom =
      (singleQuotientTensorIsoReduction I P).hom ≫
        (NatTrans.mapHomologicalComplex (reductionNatTrans h) (ComplexShape.up ℤ)).app P := by
  have hn := singleQuotientTensorIsoReduction_inv_naturality h (𝟙 P)
  try simp only [Functor.map_id, Category.comp_id] at hn
  change HomologicalComplex.tensorHom
      ((CochainComplex.singleFunctor _ 0).map (quotientModuleMap h)) (𝟙 P) ≫ _ = _
  apply (cancel_epi (singleQuotientTensorIsoReduction I P).inv).1
  rw [← Category.assoc, ← hn]
  simp only [CategoryTheory.Functor.map_id, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]
  exact Category.comp_id _

omit [IsNoetherianRing A] in
/-- The comparison with the degreewise reduction, for the extended single complex, is natural in
the ideal. -/
lemma extendedSingleQuotientTensorIsoReduction_naturality
    {I J : Ideal A} (h : I ≤ J) (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    (TrightCochain P).map (HomologicalComplex.extendMap
        ((ChainComplex.single₀ _).map (quotientModuleMap h)) ComplexShape.embeddingDownNat) ≫
        (extendedSingleQuotientTensorIsoReduction J P).hom =
      (extendedSingleQuotientTensorIsoReduction I P).hom ≫
        (NatTrans.mapHomologicalComplex (reductionNatTrans h) (ComplexShape.up ℤ)).app P := by
  dsimp only [extendedSingleQuotientTensorIsoReduction, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ← Functor.map_comp, extendSingleIso_naturality,
    Functor.map_comp, Category.assoc, singleQuotientTensorIsoReduction_naturality,
    Category.assoc]

omit [IsNoetherianRing A] in
private noncomputable def quotientTensorDerivedIsoReduction
    (I : Ideal A) (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    (tensorRightDerived P hP).obj (DerivedCategory.Q.obj
      (((ChainComplex.single₀ _).obj (ModuleCat.of A (A ⧸ I))).extend
        ComplexShape.embeddingDownNat)) ≅
      DerivedCategory.Q.obj ((reduceComplex I).obj P) :=
  (tensorRightDerivedFactors P hP).app _ ≪≫
    DerivedCategory.Q.mapIso (extendedSingleQuotientTensorIsoReduction I P)

omit [IsNoetherianRing A] in
private lemma quotientTensorDerivedIsoReduction_naturality
    {I J : Ideal A} (h : I ≤ J) (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    (tensorRightDerived P hP).map (DerivedCategory.Q.map (HomologicalComplex.extendMap
        ((ChainComplex.single₀ _).map (quotientModuleMap h)) ComplexShape.embeddingDownNat)) ≫
        (quotientTensorDerivedIsoReduction J P hP).hom =
      (quotientTensorDerivedIsoReduction I P hP).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (reductionNatTrans h) (ComplexShape.up ℤ)).app P) := by
  dsimp only [quotientTensorDerivedIsoReduction, Iso.trans_hom, Functor.mapIso_hom]
  let q := HomologicalComplex.extendMap
    ((ChainComplex.single₀ _).map (quotientModuleMap h)) ComplexShape.embeddingDownNat
  have he := (tensorRightDerivedFactors P hP).hom.naturality q
  change (tensorRightDerived P hP).map (DerivedCategory.Q.map q) ≫
      ((tensorRightDerivedFactors P hP).app _).hom =
    ((tensorRightDerivedFactors P hP).app _).hom ≫
      DerivedCategory.Q.map ((TrightCochain P).map q) at he
  rw [← Category.assoc, he]
  change ((tensorRightDerivedFactors P hP).hom.app _ ≫
      DerivedCategory.Q.map ((TrightCochain P).map _)) ≫ _ = _
  rw [Category.assoc, ← Functor.map_comp,
    extendedSingleQuotientTensorIsoReduction_naturality, Functor.map_comp, Category.assoc]
  rfl

private noncomputable def quotientPowerTensorIsoReduction
    {r : ℕ} (f : Fin r → A) (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    NoetherianKoszulProIso.quotientPowerSystem f ⋙ tensorRightDerived P hP ≅
      idealReductionSystem (fun n => Ideal.span (Set.range fun i => f i ^ (n + 1)))
        (generatorPowers_antitone f) P := by
  let η : NoetherianKoszulProIso.quotientPowerSystem f ⋙ tensorRightDerived P hP ⟶
      idealReductionSystem (fun n => Ideal.span (Set.range fun i => f i ^ (n + 1)))
        (generatorPowers_antitone f) P :=
    NatTrans.ofOpSequence (fun n => (quotientTensorDerivedIsoReduction _ P hP).hom)
      (fun n => by
        change (tensorRightDerived P hP).map ((NoetherianKoszulProIso.quotientPowerSystem f).map _) ≫ _ = _
        simp only [NoetherianKoszulProIso.quotientPowerSystem, Functor.ofOpSequence_map_homOfLE_succ]
        rw [quotientPowerTransition_eq]
        exact quotientTensorDerivedIsoReduction_naturality _ P hP)
  have : ∀ n, IsIso (η.app n) := fun n => (quotientTensorDerivedIsoReduction _ P hP).isIso_hom
  have : IsIso η := NatIso.isIso_of_isIso_app η
  exact asIso η

omit [IsNoetherianRing A] in
private lemma quasiIso_tensorLeft_map
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (hK : K.KFlat)
    {L M : CochainComplex (ModuleCat.{u} A) ℤ} (f : L ⟶ M) [QuasiIso f] :
    QuasiIso ((TleftCochain K).map f) := by
  let S := (TotalTensorComplex.cochainComplex_symmetricMonoidalCategory A).choose
  let : SymmetricCategory (CochainComplex (ModuleCat.{u} A) ℤ) := S
  have : QuasiIso ((TrightCochain K).map f) := quasiIso_tensorRight_map K hK f
  have h : (TleftCochain K).map f ≫ (β_ K M).hom =
      (β_ K L).hom ≫ (TrightCochain K).map f := by
    exact BraidedCategory.braiding_naturality_right K f
  have : QuasiIso ((TleftCochain K).map f ≫ (β_ K M).hom) := by
    rw [h]
    infer_instance
  exact quasiIso_of_comp_right _ (β_ K M).hom

omit [IsNoetherianRing A] in
private lemma tensor_isStrictlyGE
    (K L : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [K.IsStrictlyGE a] [L.IsStrictlyGE b] :
    CochainComplex.IsStrictlyGE (HomologicalComplex.tensorObj K L) (a + b) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : IsZero (K.X p ⊗ L.X q) := by
    by_cases hp : p < a
    · exact (tensorRight (L.X q)).map_isZero (K.isZero_of_isStrictlyGE a p hp)
    · exact (tensorLeft (K.X p)).map_isZero
        (L.isZero_of_isStrictlyGE b q (by change p + q = i at hpq; omega))
  exact hz.eq_of_src _ _

omit [IsNoetherianRing A] in
private lemma tensor_isStrictlyLE
    (K L : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ)
    [K.IsStrictlyLE a] [L.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE (HomologicalComplex.tensorObj K L) (a + b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  apply (IsZero.iff_id_eq_zero _).2
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : IsZero (K.X p ⊗ L.X q) := by
    by_cases hp : a < p
    · exact (tensorRight (L.X q)).map_isZero (K.isZero_of_isStrictlyLE a p hp)
    · exact (tensorLeft (K.X p)).map_isZero
        (L.isZero_of_isStrictlyLE b q (by change p + q = i at hpq; omega))
  exact hz.eq_of_src _ _

omit [IsNoetherianRing A] in
private lemma koszulComplex_isZero_X_outside
    {r : ℕ} (f : Fin r → A) (i : ℤ) (hi : i < -(r : ℤ) ∨ 0 < i) :
    IsZero (((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat).X i) := by
  by_cases hp : ∃ j : ℕ, -(j : ℤ) = i
  · obtain ⟨j, hj⟩ := hp
    have hz : IsZero ((Koszul.seqComplex f).X j) := by
      apply ModuleCat.isZero_iff_subsingleton.mpr
      change Subsingleton (⋀[A]^j (Fin r → A))
      apply exteriorPower.subsingleton_of_span_eq_top_of_card_lt
        (fun i : Fin r => (Pi.basisFun A (Fin r)) i) (Pi.basisFun A (Fin r)).span_eq j
      rw [Nat.card_eq_fintype_card, Fintype.card_fin]
      rcases hi with hi | hi <;> omega
    exact hz.of_iso ((Koszul.seqComplex f).extendXIso ComplexShape.embeddingDownNat hj)
  · exact (Koszul.seqComplex f).isZero_extend_X ComplexShape.embeddingDownNat i
      (fun j hj => hp ⟨j, hj⟩)

omit [IsNoetherianRing A] in
private lemma koszulComplex_bounded {r : ℕ} (f : Fin r → A) :
    CochainComplex.IsStrictlyGE
        ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat) (-(r : ℤ)) ∧
      CochainComplex.IsStrictlyLE
        ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat) 0 := by
  exact ⟨(CochainComplex.isStrictlyGE_iff _ _).2
    (fun i hi => koszulComplex_isZero_X_outside f i (Or.inl hi)),
    (CochainComplex.isStrictlyLE_iff _ _).2
      (fun i hi => koszulComplex_isZero_X_outside f i (Or.inr hi))⟩

omit [IsNoetherianRing A] in
private lemma koszulComplex_kFlat {r : ℕ} (f : Fin r → A) :
    CochainComplex.KFlat ((Koszul.seqComplex f).extend ComplexShape.embeddingDownNat) := by
  let K : CochainComplex (ModuleCat.{u} A) ℤ :=
    (Koszul.seqComplex f).extend ComplexShape.embeddingDownNat
  have : K.IsStrictlyLE 0 := (koszulComplex_bounded f).2
  have (i : ℤ) : Module.Flat A (K.X i) := by
    by_cases hp : ∃ j : ℕ, -(j : ℤ) = i
    · obtain ⟨j, hj⟩ := hp
      let e := (Koszul.seqComplex f).extendXIso ComplexShape.embeddingDownNat hj
      have : Module.Flat A ((Koszul.seqComplex f).X j) := by
        change Module.Flat A (⋀[A]^j (Fin r → A))
        infer_instance
      exact Module.Flat.of_linearEquiv e.toLinearEquiv
    · have hz := (Koszul.seqComplex f).isZero_extend_X ComplexShape.embeddingDownNat i
        (fun j hj => hp ⟨j, hj⟩)
      have : Subsingleton (K.X i) := (ModuleCat.isZero_iff_subsingleton).1 hz
      infer_instance
  exact _root_.CochainComplex.KFlat.kFlat_of_flat K 0

private noncomputable def koszulAdicComparison
    {r : ℕ} (f : Fin r → A) (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    NoetherianKoszulProIso.koszulPowerSystem f ⋙ tensorRightDerived P hP ⟶
      adicReductionSystem (Ideal.span (Set.range f)) P :=
  Functor.whiskerRight (NoetherianKoszulProIso.koszulQuotientComparison f) (tensorRightDerived P hP) ≫
    (quotientPowerTensorIsoReduction f P hP).hom ≫
      idealReductionComparison (generatorPowers_antitone f)
        (fun _ _ h => Ideal.pow_le_pow_right (Nat.add_le_add_right h 1))
        (span_generator_powers_le_power f) P

private lemma koszulAdicComparison_hasProInverse
    {r : ℕ} (f : Fin r → A) (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : P.KFlat) :
    HasProInverse (koszulAdicComparison f P hP) := by
  apply HasProInverse.comp (koszul_tensorRight_hasProInverse f P hP)
  apply HasProInverse.comp (hasProInverse_of_isIso _)
  apply idealReductionComparison_hasProInverse
  intro n
  obtain ⟨m, hm⟩ := powers_le_span_generator_powers f n
  exact ⟨m, (Ideal.pow_le_pow_right (Nat.le_succ m)).trans hm⟩

omit [IsNoetherianRing A] in
private lemma koszulTensorSystem_isZero_outside
    {r : ℕ} (f : Fin r → A)
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) [QuasiIso p]
    (hP : P.KFlat) (a b : ℤ) [M.IsStrictlyGE a] [M.IsStrictlyLE b]
    (i : ℤ) (hi : i < -(r : ℤ) + a ∨ b < i) (n : ℕᵒᵖ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
      ((NoetherianKoszulProIso.koszulPowerSystem f ⋙ tensorRightDerived P hP).obj n)) := by
  let K : CochainComplex (ModuleCat.{u} A) ℤ :=
    (Koszul.seqComplex (fun j => f j ^ (n.unop + 1))).extend ComplexShape.embeddingDownNat
  have hK : K.KFlat := koszulComplex_kFlat _
  have : K.IsStrictlyGE (-(r : ℤ)) := (koszulComplex_bounded _).1
  have : K.IsStrictlyLE 0 := (koszulComplex_bounded _).2
  let E : CochainComplex (ModuleCat.{u} A) ℤ := HomologicalComplex.tensorObj K M
  have : E.IsStrictlyGE (-(r : ℤ) + a) := tensor_isStrictlyGE K M _ _
  have : E.IsStrictlyLE b := by simpa using tensor_isStrictlyLE K M 0 b
  have hX : IsZero (E.X i) := by
    rcases hi with hi | hi
    · exact E.isZero_of_isStrictlyGE _ i hi
    · exact E.isZero_of_isStrictlyLE b i hi
  have hQ := KoszulIdealPower.isZero_homology_Q_obj_of_isZero_X E i hX
  have hq : QuasiIso ((TleftCochain K).map p) := quasiIso_tensorLeft_map K hK p
  have : IsIso (DerivedCategory.Q.map ((TleftCochain K).map p)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hq
  let e : (tensorRightDerived P hP).obj (DerivedCategory.Q.obj K) ≅ DerivedCategory.Q.obj E :=
    (tensorRightDerivedFactors P hP).app K ≪≫
      asIso (DerivedCategory.Q.map ((TleftCochain K).map p))
  exact hQ.of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e)

private lemma adicReductionComparison_hasProInverse_of_homology
    (I : Ideal A) {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) [QuasiIso p]
    (hP : P.KFlat) (a b : ℤ) [M.IsStrictlyGE a] [M.IsStrictlyLE b]
    (hH : ∀ i : ℤ, HasProInverse (Functor.whiskerRight
      (adicReductionComparisonNatTrans I p) (DerivedCategory.homologyFunctor _ i))) :
    HasProInverse (adicReductionComparisonNatTrans I p) := by
  obtain ⟨r, f, hf, -, -⟩ := exists_finite_generators_and_cofinal_powers I
  subst I
  let α := adicReductionComparisonNatTrans (Ideal.span (Set.range f)) p
  let β := koszulAdicComparison f P hP
  have hβ : HasProInverse β := koszulAdicComparison_hasProInverse f P hP
  have hγ : HasProInverse (β ≫ α) := by
    apply DerivedCategory.exists_proInverse_of_proInverse_homology (β ≫ α) (-(r : ℤ) + a) b
    · exact koszulTensorSystem_isZero_outside f p hP a b
    · intro i hi n
      apply homology_adicReductionSystem_isZero_outside _ M a b inferInstance inferInstance i _ n
      rcases hi with hi | hi
      · exact Or.inl (by omega)
      · exact Or.inr hi
    · intro i
      have hcomp := (hβ.whiskerRight (DerivedCategory.homologyFunctor _ i)).comp (hH i)
      change HasProInverse (Functor.whiskerRight (β ≫ α)
        (DerivedCategory.homologyFunctor _ i))
      rw [Functor.whiskerRight_comp]
      exact hcomp
  exact proInverse_of_common_source β (β ≫ α) α rfl hβ hγ


open HomologicalComplex

set_option backward.isDefEq.respectTransparency false

omit [IsNoetherianRing A] in
private noncomputable def reductionProjection
    (I : Ideal A) (K : CochainComplex (ModuleCat.{u} A) ℤ) : K ⟶ (reduceComplex I).obj K where
  f i := ModuleCat.ofHom (I • (⊤ : Submodule A (K.X i))).mkQ
  comm' i j _ := by ext x; rfl

omit [IsNoetherianRing A] in
private lemma reductionProjection_naturality
    (I : Ideal A) {K L : CochainComplex (ModuleCat.{u} A) ℤ} (p : K ⟶ L) :
    p ≫ reductionProjection I L = reductionProjection I K ≫ (reduceComplex I).map p := by
  ext i x
  rfl

omit [IsNoetherianRing A] in
private lemma reductionProjection_ideal_naturality
    {I J : Ideal A} (h : I ≤ J) (K : CochainComplex (ModuleCat.{u} A) ℤ) :
    reductionProjection I K ≫
        (NatTrans.mapHomologicalComplex (reductionNatTrans h) (ComplexShape.up ℤ)).app K =
      reductionProjection J K := by
  ext i x
  rfl

omit [IsNoetherianRing A] in
private lemma originalHomologyConcreteEquiv_mk
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (x : LinearMap.ker (K.sc i).g.hom) :
    originalHomologyConcreteEquiv K i (Submodule.Quotient.mk x) =
      (K.sc i).moduleCatHomologyIso.inv ((K.sc i).moduleCatLeftHomologyData.π.hom x) := by
  dsimp only [originalHomologyConcreteEquiv, LinearEquiv.trans_apply]
  rw [Submodule.quotEquivOfEq_mk]
  rfl

omit [IsNoetherianRing A] in
private lemma reductionProjection_homologyMap_mk
    (I : Ideal A) (K : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (x : LinearMap.ker (K.sc i).g.hom)
    (y : (I • (⊤ : Submodule A (K.sc i).X₃)).comap (K.sc i).g.hom)
    (hxy : (y : (K.sc i).X₂) = x) :
    (HomologicalComplex.homologyMap (reductionProjection I K) i).hom
        (originalHomologyConcreteEquiv K i (Submodule.Quotient.mk x)) =
      reducedHomologyConcreteEquiv I K i (Submodule.Quotient.mk y) := by
  let S := K.sc i
  let T := ((reduceComplex I).obj K).sc i
  let φ : S ⟶ T := (HomologicalComplex.shortComplexFunctor _ _ i).map (reductionProjection I K)
  rw [originalHomologyConcreteEquiv_mk]
  change (ShortComplex.homologyMap φ).hom
    (S.moduleCatHomologyIso.inv (S.moduleCatLeftHomologyData.π.hom x)) =
      T.moduleCatHomologyIso.inv (reductionHomologyEquiv I S.f S.g S.zero (Submodule.Quotient.mk y))
  rw [reductionHomologyEquiv_mk]
  apply homologyMap_moduleCatHomologyIso_inv_π
  apply cyclesMap_moduleCatCyclesIso_inv
  change Submodule.Quotient.mk (x : S.X₂) = Submodule.Quotient.mk (y : S.X₂)
  rw [hxy]

omit [IsNoetherianRing A] in
private noncomputable def moduleReductionSystem (I : Ideal A) (N : ModuleCat.{u} A) :
    ℕᵒᵖ ⥤ ModuleCat.{u} A where
  obj n := (redFunctor (I ^ n.unop)).obj N
  map f := (reductionNatTrans (Ideal.pow_le_pow_right (leOfHom f.unop))).app N
  map_id n := by rw [reductionNatTrans_id]; rfl
  map_comp f g := by rw [← NatTrans.comp_app, reductionNatTrans_comp]

omit [IsNoetherianRing A] in
private noncomputable def moduleReductionSystemMap
    (I : Ideal A) {N N' : ModuleCat.{u} A} (p : N ⟶ N') :
    moduleReductionSystem I N ⟶ moduleReductionSystem I N' where
  app n := (redFunctor (I ^ n.unop)).map p
  naturality _ _ f := ((reductionNatTrans
    (Ideal.pow_le_pow_right (leOfHom f.unop))).naturality p).symm

omit [IsNoetherianRing A] in
private noncomputable def moduleReductionProjection (I : Ideal A)
    (N : ModuleCat.{u} A) (n : ℕ) : N ⟶ (moduleReductionSystem I N).obj (op n) :=
  ModuleCat.ofHom (I ^ n • (⊤ : Submodule A N)).mkQ

omit [IsNoetherianRing A] in
private lemma moduleReductionProjection_epi (I : Ideal A)
    (N : ModuleCat.{u} A) (n : ℕ) : Epi (moduleReductionProjection I N n) :=
  (ModuleCat.epi_iff_surjective _).2 (Submodule.mkQ_surjective _)

attribute [local instance] moduleReductionProjection_epi

omit [IsNoetherianRing A] in
private lemma moduleReductionProjection_naturality (I : Ideal A)
    {N N' : ModuleCat.{u} A} (p : N ⟶ N') (n : ℕ) :
    p ≫ moduleReductionProjection I N' n =
      moduleReductionProjection I N n ≫ (moduleReductionSystemMap I p).app (op n) := by
  ext x
  rfl

omit [IsNoetherianRing A] in
private lemma moduleReductionProjection_transition (I : Ideal A)
    (N : ModuleCat.{u} A) {n m : ℕ} (h : n ≤ m) :
    moduleReductionProjection I N m ≫ (moduleReductionSystem I N).map (homOfLE h).op =
      moduleReductionProjection I N n := by
  ext x
  rfl

omit [IsNoetherianRing A] in
private noncomputable def reductionHomologySystem (I : Ideal A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
  idealReductionSystem (fun n => I ^ n) (fun _ _ h => Ideal.pow_le_pow_right h) K ⋙
    DerivedCategory.homologyFunctor _ i

omit [IsNoetherianRing A] in
private noncomputable def originalDerivedHomologyConcreteIso
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    ModuleCat.of A ((LinearMap.ker (K.sc i).g.hom) ⧸
      (LinearMap.range (K.sc i).f.hom).comap (LinearMap.ker (K.sc i).g.hom).subtype) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj (DerivedCategory.Q.obj K) :=
  (originalHomologyConcreteEquiv K i).toModuleIso ≪≫
    ((DerivedCategory.homologyFunctorFactors _ i).app K).symm

omit [IsNoetherianRing A] in
private noncomputable def reducedDerivedHomologyConcreteIso (I : Ideal A)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    ModuleCat.of A (((I • (⊤ : Submodule A (K.sc i).X₃)).comap (K.sc i).g.hom) ⧸
      (LinearMap.range (K.sc i).f.hom ⊔ I • (⊤ : Submodule A (K.sc i).X₂)).comap
        ((I • (⊤ : Submodule A (K.sc i).X₃)).comap (K.sc i).g.hom).subtype) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (DerivedCategory.Q.obj ((reduceComplex I).obj K)) :=
  (reducedHomologyConcreteEquiv I K i).toModuleIso ≪≫
    ((DerivedCategory.homologyFunctorFactors _ i).app ((reduceComplex I).obj K)).symm

omit [IsNoetherianRing A] in
private lemma derived_homologyMap_eq
    {K L : CochainComplex (ModuleCat.{u} A) ℤ} (f : K ⟶ L) (i : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map (DerivedCategory.Q.map f) =
      ((DerivedCategory.homologyFunctorFactors _ i).app K).hom ≫
        HomologicalComplex.homologyMap f i ≫
          ((DerivedCategory.homologyFunctorFactors _ i).app L).inv := by
  apply (cancel_mono ((DerivedCategory.homologyFunctorFactors _ i).app L).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact DerivedCategory.homologyFunctorFactors_hom_naturality f i

omit [IsNoetherianRing A] in
private lemma reducedDerivedHomologyConcreteIso_naturality {I J : Ideal A} (h : I ≤ J)
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ) :
    ModuleCat.ofHom (concreteHomologyIdealTransition h (K.sc i).f (K.sc i).g (K.sc i).zero) ≫
        (reducedDerivedHomologyConcreteIso J K i).hom =
      (reducedDerivedHomologyConcreteIso I K i).hom ≫
        (DerivedCategory.homologyFunctor _ i).map (DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (reductionNatTrans h) (ComplexShape.up ℤ)).app K)) := by
  rw [derived_homologyMap_eq]
  dsimp only [reducedDerivedHomologyConcreteIso, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Category.assoc]
  congr 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (reducedHomologyConcreteEquiv_ideal_naturality h K i x).symm

omit [IsNoetherianRing A] in
private lemma derivedReductionProjection_mk
    (I : Ideal A) (K : CochainComplex (ModuleCat.{u} A) ℤ) (i : ℤ)
    (x : LinearMap.ker (K.sc i).g.hom)
    (y : (I • (⊤ : Submodule A (K.sc i).X₃)).comap (K.sc i).g.hom)
    (hxy : (y : (K.sc i).X₂) = x) :
    ((DerivedCategory.homologyFunctor _ i).map
        (DerivedCategory.Q.map (reductionProjection I K))).hom
        ((originalDerivedHomologyConcreteIso K i).hom (Submodule.Quotient.mk x)) =
      (reducedDerivedHomologyConcreteIso I K i).hom (Submodule.Quotient.mk y) := by
  rw [derived_homologyMap_eq]
  change (((originalDerivedHomologyConcreteIso K i).hom ≫
    ((DerivedCategory.homologyFunctorFactors _ i).app K).hom ≫
      HomologicalComplex.homologyMap (reductionProjection I K) i ≫
        ((DerivedCategory.homologyFunctorFactors _ i).app ((reduceComplex I).obj K)).inv).hom
          (Submodule.Quotient.mk x)) = _
  dsimp only [originalDerivedHomologyConcreteIso, reducedDerivedHomologyConcreteIso,
    Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  change ((DerivedCategory.homologyFunctorFactors _ i).app ((reduceComplex I).obj K)).inv
    ((HomologicalComplex.homologyMap (reductionProjection I K) i).hom
      (originalHomologyConcreteEquiv K i (Submodule.Quotient.mk x))) = _
  rw [reductionProjection_homologyMap_mk I K i x y hxy]
  rfl

set_option maxHeartbeats 2000000 in
-- The concrete quotient systems in the Artin–Rees comparison have large dependent types.
set_option maxRecDepth 4096 in
private lemma exists_reductionHomologyComparison
    (I : Ideal A) (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : ∀ i : ℤ, Module.Finite A (K.X i)) (i : ℤ) :
    ∃ α : moduleReductionSystem I
        ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj K)) ⟶
          reductionHomologySystem I K i,
      HasProInverse α ∧ ∀ n : ℕ,
        moduleReductionProjection I _ n ≫ α.app (op n) =
          (DerivedCategory.homologyFunctor _ i).map
            (DerivedCategory.Q.map (reductionProjection (I ^ n) K)) := by
  let S := K.sc i
  have : Module.Finite A S.X₁ := hK _
  have : Module.Finite A S.X₂ := hK _
  have : Module.Finite A S.X₃ := hK _
  obtain ⟨toLevel, t, qt, fq, hto, ht, hqt, htnat, hfq, c, hc,
      back, hback₁, hback₂, hrest⟩ :=
    Stacks.AdicSystem.ArtinReesHomology.exists_uniform_adic_homology_comparison I S.f.hom S.g.hom
      (by simpa only [ModuleCat.hom_comp, ModuleCat.hom_zero] using
        congrArg ModuleCat.Hom.hom S.zero)
  let H := (LinearMap.ker S.g.hom) ⧸
    (LinearMap.range S.f.hom).comap (LinearMap.ker S.g.hom).subtype
  let Hn := fun n : ℕ => ((I ^ n • (⊤ : Submodule A S.X₃)).comap S.g.hom) ⧸
    (LinearMap.range S.f.hom ⊔ I ^ n • (⊤ : Submodule A S.X₂)).comap
      ((I ^ n • (⊤ : Submodule A S.X₃)).comap S.g.hom).subtype
  let X : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
    Functor.ofOpSequence (X := fun n => ModuleCat.of A (Hn n)) (fun n => ModuleCat.ofHom (t n))
  let Q : ℕᵒᵖ ⥤ ModuleCat.{u} A :=
    Functor.ofOpSequence (X := fun n => ModuleCat.of A (H ⧸ I ^ n • (⊤ : Submodule A H)))
      (fun n => ModuleCat.ofHom (qt n))
  have hfq' (n : ℕ) (x : H) : fq n (Submodule.Quotient.mk x) = toLevel n x :=
    LinearMap.congr_fun (hfq n) x
  let γ : Q ⟶ X := NatTrans.ofOpSequence (fun n => ModuleCat.ofHom (fq n)) (fun n => by
    simp only [Q, X, Functor.ofOpSequence_map_homOfLE_succ]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    change fq n (qt n (Submodule.Quotient.mk x)) = t n (fq (n + 1) (Submodule.Quotient.mk x))
    rw [hqt, hfq', hfq']
    exact (LinearMap.congr_fun (htnat n) x).symm)
  have hγ : HasProInverse γ := by
    intro n
    let m := n.unop + c
    have hm : c ≤ m := by dsimp [m]; omega
    refine ⟨op m, (homOfLE (Nat.le_add_right n.unop c)).op, ?_⟩
    have hb : ∃ (h : m - c ≤ m) (s : X.obj (op m) ⟶ Q.obj (op (m - c))),
        γ.app (op m) ≫ s = Q.map (homOfLE h).op ∧
          s ≫ γ.app (op (m - c)) = X.map (homOfLE h).op := by
      exact ⟨Nat.sub_le m c, ModuleCat.ofHom (back m hm), ModuleCat.hom_ext (hback₁ m hm),
        ModuleCat.hom_ext (hback₂ m hm)⟩
    have hm' : m - c = n.unop := by dsimp [m]; omega
    rw [hm'] at hb
    obtain ⟨h, s, hs, hs'⟩ := hb
    exact ⟨s, hs, hs'⟩
  have hqt' (n : ℕ) : ModuleCat.ofHom (qt n) =
      (reductionNatTrans (Ideal.pow_le_pow_right (Nat.le_succ n))).app (ModuleCat.of A H) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    exact hqt n x
  have ht' (n : ℕ) : t n = concreteHomologyIdealTransition
      (Ideal.pow_le_pow_right (Nat.le_succ n)) S.f S.g S.zero := by
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    exact ht n x (reductionCyclesMapOfIdealLE (Ideal.pow_le_pow_right (Nat.le_succ n)) S.g x) rfl
  let eH := originalDerivedHomologyConcreteIso K i
  let εQ : Q ⟶ moduleReductionSystem I
      ((DerivedCategory.homologyFunctor _ i).obj (DerivedCategory.Q.obj K)) :=
    NatTrans.ofOpSequence (fun n => (redFunctor (I ^ n)).map eH.hom) (fun n => by
      simp only [Q, Functor.ofOpSequence_map_homOfLE_succ, hqt']
      exact ((reductionNatTrans (Ideal.pow_le_pow_right (Nat.le_succ n))).naturality eH.hom).symm)
  have : ∀ n, IsIso (εQ.app n) := fun n => by
    change IsIso ((redFunctor (I ^ n.unop)).map eH.hom)
    infer_instance
  have : IsIso εQ := NatIso.isIso_of_isIso_app εQ
  let εX : X ⟶ reductionHomologySystem I K i :=
    NatTrans.ofOpSequence (fun n => (reducedDerivedHomologyConcreteIso (I ^ n) K i).hom)
      (fun n => by
        simp only [X, Functor.ofOpSequence_map_homOfLE_succ, ht']
        exact reducedDerivedHomologyConcreteIso_naturality _ K i)
  have : ∀ n, IsIso (εX.app n) := fun n => (reducedDerivedHomologyConcreteIso _ K i).isIso_hom
  have : IsIso εX := NatIso.isIso_of_isIso_app εX
  refine ⟨inv εQ ≫ γ ≫ εX,
    (hasProInverse_of_isIso (inv εQ)).comp (hγ.comp (hasProInverse_of_isIso εX)), ?_⟩
  intro n
  apply (cancel_epi eH.hom).1
  have hproj : eH.hom ≫ moduleReductionProjection I _ n =
      moduleReductionProjection I (ModuleCat.of A H) n ≫ εQ.app (op n) :=
    moduleReductionProjection_naturality I eH.hom n
  simp only [NatTrans.comp_app]
  rw [← Category.assoc eH.hom, hproj]
  have heps : εQ.app (op n) ≫ (inv εQ).app (op n) = 𝟙 _ :=
    congrArg (fun η => η.app (op n)) (IsIso.hom_inv_id εQ)
  simp only [Category.assoc]
  rw [← Category.assoc (εQ.app (op n)), heps, Category.id_comp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
  let y : (I ^ n • (⊤ : Submodule A S.X₃)).comap S.g.hom :=
    ⟨x, Submodule.mem_comap.mpr (by
      rw [LinearMap.mem_ker.mp x.property]
      exact Submodule.zero_mem _)⟩
  change (reducedDerivedHomologyConcreteIso (I ^ n) K i).hom
      (fq n (Submodule.Quotient.mk (Submodule.Quotient.mk x))) = _
  rw [hfq', hto n x y rfl]
  exact (derivedReductionProjection_mk (I ^ n) K i x y rfl).symm

omit [IsNoetherianRing A] in
private noncomputable def reductionHomologySystemMap
    (I : Ideal A) {K L : CochainComplex (ModuleCat.{u} A) ℤ} (p : K ⟶ L) (i : ℤ) :
    reductionHomologySystem I K i ⟶ reductionHomologySystem I L i where
  app n := (DerivedCategory.homologyFunctor _ i).map
    (DerivedCategory.Q.map ((reduceComplex (I ^ n.unop)).map p))
  naturality n m f := by
    let η := NatTrans.mapHomologicalComplex
      (reductionNatTrans (Ideal.pow_le_pow_right (I := I) (leOfHom f.unop))) (ComplexShape.up ℤ)
    change (DerivedCategory.homologyFunctor _ i).map (DerivedCategory.Q.map (η.app K)) ≫ _ =
      _ ≫ (DerivedCategory.homologyFunctor _ i).map (DerivedCategory.Q.map (η.app L))
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun g => (DerivedCategory.homologyFunctor _ i).map (DerivedCategory.Q.map g))
      (η.naturality p).symm

omit [IsNoetherianRing A] in
private lemma reductionHomologyProjection_naturality
    (I : Ideal A) {K L : CochainComplex (ModuleCat.{u} A) ℤ} (p : K ⟶ L) (i : ℤ) (n : ℕ) :
    (DerivedCategory.homologyFunctor _ i).map (DerivedCategory.Q.map p) ≫
        (DerivedCategory.homologyFunctor _ i).map
          (DerivedCategory.Q.map (reductionProjection (I ^ n) L)) =
      (DerivedCategory.homologyFunctor _ i).map
          (DerivedCategory.Q.map (reductionProjection (I ^ n) K)) ≫
        (reductionHomologySystemMap I p i).app (op n) := by
  change _ = _ ≫ (DerivedCategory.homologyFunctor _ i).map (DerivedCategory.Q.map _)
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
    reductionProjection_naturality]

private lemma reductionHomologySystemMap_hasProInverse
    (I : Ideal A) {K L : CochainComplex (ModuleCat.{u} A) ℤ} (p : K ⟶ L) [QuasiIso p]
    (hK : ∀ i, Module.Finite A (K.X i)) (hL : ∀ i, Module.Finite A (L.X i)) (i : ℤ) :
    HasProInverse (reductionHomologySystemMap I p i) := by
  obtain ⟨α, hα, hαπ⟩ := exists_reductionHomologyComparison I K hK i
  obtain ⟨β, hβ, hβπ⟩ := exists_reductionHomologyComparison I L hL i
  let h := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).map (DerivedCategory.Q.map p)
  have : IsIso h := by dsimp [h]; infer_instance
  let u := moduleReductionSystemMap I h
  have : ∀ n, IsIso (u.app n) := fun n => by dsimp [u, moduleReductionSystemMap]; infer_instance
  have : IsIso u := NatIso.isIso_of_isIso_app u
  apply proInverse_of_common_source α (u ≫ β) (reductionHomologySystemMap I p i) _ hα
    ((hasProInverse_of_isIso u).comp hβ)
  apply NatTrans.ext
  funext n
  apply (cancel_epi (moduleReductionProjection I _ n.unop)).1
  change moduleReductionProjection I _ n.unop ≫ (α.app n ≫ _) =
    moduleReductionProjection I _ n.unop ≫ (u.app n ≫ β.app n)
  rw [← Category.assoc, hαπ n.unop]
  rw [← reductionHomologyProjection_naturality I p i n.unop, ← hβπ n.unop]
  rw [← Category.assoc, moduleReductionProjection_naturality I h n.unop, Category.assoc]

public def successorOp : ℕᵒᵖ ⥤ ℕᵒᵖ where
  obj n := op (n.unop + 1)
  map f := (homOfLE (Nat.add_le_add_right (leOfHom f.unop) 1)).op

private lemma HasProInverse.whiskerLeft_successor
    {C : Type*} [Category C] {X Y : ℕᵒᵖ ⥤ C} {α : X ⟶ Y} (hα : HasProInverse α) :
    HasProInverse (Functor.whiskerLeft successorOp α) := by
  intro n
  obtain ⟨k, f, s, hs, hs'⟩ := hα (op (n.unop + 1))
  have hnk : n.unop + 1 ≤ k.unop := leOfHom f.unop
  cases k using Opposite.rec
  rename_i k
  cases k with
  | zero => simp at hnk
  | succ k =>
    exact ⟨op k, (homOfLE (Nat.le_of_succ_le_succ hnk)).op, s, hs, hs'⟩

private lemma adicReductionComparison_homology_hasProInverse
    (I : Ideal A) {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) [QuasiIso p]
    (hP : ∀ i, Module.Finite A (P.X i)) (hM : ∀ i, Module.Finite A (M.X i)) (i : ℤ) :
    HasProInverse (Functor.whiskerRight (adicReductionComparisonNatTrans I p)
      (DerivedCategory.homologyFunctor _ i)) :=
  (reductionHomologySystemMap_hasProInverse I p hP hM i).whiskerLeft_successor

/-- **Stacks Project, Tag 0G9M.** Let `I` be an ideal of a Noetherian ring `A` and let `M` be a
bounded complex of finite `A`-modules.  Then `M` admits a bounded-above resolution `p : P -> M`
by finite free modules, and the canonical comparison from the derived reductions of `P` modulo
the positive powers of `I` to the degreewise reductions of `M` is compatible with the
transition maps and is an isomorphism of pro-objects in the derived category: each level
acquires a two-sided inverse after passing to a later level. -/
@[stacks 0G9M]
public theorem derivedReduction_proIsomorphic_adicReduction
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I : Ideal A) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hMbounded : ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b)
    (hMfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    ∃ (P : CochainComplex (ModuleCat.{u} A) ℤ) (p : P ⟶ M),
      (∃ b : ℤ, P.IsStrictlyLE b) ∧
      (∀ i : ℤ, Module.Finite A (P.X i) ∧ Module.Free A (P.X i)) ∧
      IsIso (DerivedCategory.Q.map p) ∧
      (∀ n : ℕ,
        adicReductionTransition I P (Nat.le_succ n) ≫ adicReductionComparison I p n =
          adicReductionComparison I p (n + 1) ≫
            adicReductionTransition I M (Nat.le_succ n)) ∧
      ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
          (s : DerivedCategory.Q.obj ((reduceComplex (I ^ (m + 1))).obj M) ⟶
            DerivedCategory.Q.obj ((reduceComplex (I ^ (n + 1))).obj P)),
          adicReductionComparison I p m ≫ s =
              adicReductionTransition I P h ∧
            s ≫ adicReductionComparison I p n =
              adicReductionTransition I M h := by
  obtain ⟨a, b, hMa, hMb⟩ := hMbounded
  obtain ⟨P, p, hPb, hPfinite, hp⟩ := finiteFreeResolution M b hMb hMfinite
  refine ⟨P, p, ⟨b, hPb⟩, hPfinite, hp,
    adicReductionComparison_naturality I p, ?_⟩
  have : P.IsStrictlyLE b := hPb
  have : M.IsStrictlyGE a := hMa
  have : M.IsStrictlyLE b := hMb
  have : ∀ i, Module.Flat A (P.X i) := fun i => by
    have : Module.Free A (P.X i) := (hPfinite i).2
    infer_instance
  have hPflat : P.KFlat := _root_.CochainComplex.KFlat.kFlat_of_flat P b
  have : QuasiIso p := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).1 hp
  have hpro := adicReductionComparison_hasProInverse_of_homology I p hPflat a b
    (adicReductionComparison_homology_hasProInverse I p (fun i => (hPfinite i).1) hMfinite)
  exact (hasProInverse_iff_nat _).1 hpro


end Stacks.AdicSystem.DerivedReductionProIso

/-! ## Support replayed for the derived tensor product

Tag 0G3N and its two consequences are stated relative to a derived tensor product presented as
a bundle of data: the bifunctor, its comparison with termwise tensor product, the universal
property making each specialization a total left derived functor, and its exactness.  That
bundle is declared here, in the general form the source statements quantify over; the canonical
derived tensor product is substituted into it in
`StacksFrontier.RingTheory.Module.AdicSystem.CanonicalDerivedTensor`, which is where the tagged
statements live.  Termwise tensoring on the right is
`StacksDraft.TorAmplitude.tensorModuleRight`, from the development of tag 0652.  Neither tag
0652 nor tag 0655 is registered here; the providers of both live elsewhere in the tree. -/

noncomputable section

namespace DerivedTensorData

open CategoryTheory CategoryTheory.MonoidalCategory

universe v

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-- A derived tensor product on `D(R)`, characterized on tensoring with modules in degree zero
by the universal property of the total left derived functor of termwise tensor product.

The comparison maps are part of the data, so `isLeftDerived` is a named formal bridge from the
bifunctor to the ordinary tensor product rather than merely an exactness assumption on an
arbitrary family of functors. Only the shift and triangulated structures needed for
Tor-amplitude propagation are included here. -/
public structure DerivedTensorProduct (R : Type u) [CommRing R] where
  /-- The bifunctor `(K, L) ↦ K ⊗ᴸ[R] L`. -/
  tensor :
    DerivedCategory (ModuleCat.{v} R) ⥤
      DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v} R)
  /-- The comparison from tensoring after localization to termwise tensor product followed by
  localization. -/
  comparison : ∀ M : ModuleCat.{v} R,
    DerivedCategory.Q ⋙
        tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) ⟶
      PseudoCoherence.tensorRightComplexToDerived M
  /-- Tensoring with `M[0]`, together with `comparison M`, is the total left derived functor of
  termwise tensoring with `M`. -/
  isLeftDerived : ∀ M : ModuleCat.{v} R,
    (tensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).IsLeftDerivedFunctor
      (comparison M) (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
  /-- Tensoring on the right with a module in degree zero commutes with shifts. -/
  commShift : ∀ M : ModuleCat.{v} R,
    (tensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).CommShift ℤ
  /-- Tensoring on the right with a module in degree zero preserves distinguished triangles. -/
  triangulated : ∀ M : ModuleCat.{v} R, letI := commShift M;
    (tensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).IsTriangulated

/-- Termwise multiplication induced by a map from a module to the tensor unit. -/
public def tensorRightUnitMapComplex {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (J : ModuleCat.{u} R)
    (j : J ⟶ 𝟙_ (ModuleCat.{u} R)) :
    (((tensoringRight (ModuleCat.{u} R)).obj J).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K ⟶ K where
  f i := ((tensoringLeft (ModuleCat.{u} R)).obj (K.X i)).map j ≫
    (MonoidalCategory.rightUnitor (K.X i)).hom
  comm' i k _ := by
    dsimp
    change (K.X i ◁ j) ≫
        (MonoidalCategory.rightUnitor (K.X i)).hom ≫ K.d i k = _
    calc
      _ = (K.X i ◁ j) ≫ (K.d i k ▷ 𝟙_ (ModuleCat R)) ≫
          (MonoidalCategory.rightUnitor (K.X k)).hom := by
            rw [MonoidalCategory.rightUnitor_naturality]
      _ = _ := by
        simpa only using
          (MonoidalCategory.whisker_exchange_assoc (K.d i k) j
            (MonoidalCategory.rightUnitor (K.X k)).hom)

end DerivedTensorData

end

/-! ## Tag 0G3N -/

noncomputable section

namespace Stacks.AdicSystem.IdealPowerTensorComparison

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory CategoryTheory.Pretriangulated Opposite LiftAcyclic
open scoped TensorProduct ZeroObject

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]

/-- The positive ideal power `Iⁿ`, regarded as an `A`-module. The index `n` represents the
exponent `n + 1`. -/
public abbrev idealPowerModule (I : Ideal A) (n : ℕ) : ModuleCat.{u} A :=
  ModuleCat.of A ↥(I ^ (n + 1))

/-- The canonical inclusion `Iⁿ⁺¹ → Iⁿ`, with positive powers indexed from zero. -/
public def idealPowerModuleTransition (I : Ideal A) (n : ℕ) :
    idealPowerModule I (n + 1) ⟶ idealPowerModule I n :=
  ModuleCat.ofHom (Submodule.inclusion
    (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.le_succ n) 1)))

/-- The inclusion of an ideal power into the tensor unit `A`. -/
public def idealPowerSubtype (I : Ideal A) (n : ℕ) :
    idealPowerModule I n ⟶ 𝟙_ (ModuleCat.{u} A) :=
  ModuleCat.ofHom (I ^ (n + 1)).subtype

/-- The termwise tensor product `M ⊗ Iⁿ`. -/
public def tensorIdealPowerComplex (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : Ideal A) (n : ℕ) : CochainComplex (ModuleCat.{u} A) ℤ :=
  ((tensoringRight (ModuleCat.{u} A)).obj (idealPowerModule I n)).mapHomologicalComplex
    (ComplexShape.up ℤ) |>.obj M

/-- Termwise scalar multiplication `M ⊗ Iⁿ → M`. -/
public def idealPowerMultiplication (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : Ideal A) (n : ℕ) : tensorIdealPowerComplex M I n ⟶ M where
  f i := ((tensoringLeft (ModuleCat.{u} A)).obj (M.X i)).map
      (idealPowerSubtype I n) ≫ (MonoidalCategory.rightUnitor (M.X i)).hom
  comm' i j _ := by
    dsimp [tensorIdealPowerComplex]
    change (M.X i ◁ idealPowerSubtype I n) ≫
        (MonoidalCategory.rightUnitor (M.X i)).hom ≫ M.d i j = _
    calc
      _ = (M.X i ◁ idealPowerSubtype I n) ≫
          (M.d i j ▷ 𝟙_ (ModuleCat A)) ≫
          (MonoidalCategory.rightUnitor (M.X j)).hom := by
            rw [MonoidalCategory.rightUnitor_naturality]
      _ = _ := by
        simpa only using
          (MonoidalCategory.whisker_exchange_assoc (M.d i j)
            (idealPowerSubtype I n) (MonoidalCategory.rightUnitor (M.X j)).hom)

/-- The termwise ideal-power complex `Iⁿ M`, realized as the image of scalar multiplication
`M ⊗ Iⁿ → M`. -/
public def idealPowerComplex (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : Ideal A) (n : ℕ) : CochainComplex (ModuleCat.{u} A) ℤ :=
  image (idealPowerMultiplication M I n)

/-- The map on termwise tensor products induced by the inclusion of consecutive powers. -/
public def tensorIdealPowerTransition (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : Ideal A) (n : ℕ) :
    tensorIdealPowerComplex M I (n + 1) ⟶ tensorIdealPowerComplex M I n :=
  (((tensoringRight (ModuleCat.{u} A)).map (idealPowerModuleTransition I n)).mapHomologicalComplex
    (ComplexShape.up ℤ)).app M

/-- The canonical map on derived tensor products induced by a module map. It is obtained
from the universal property, so comparison is automatically natural in the module. -/
public def derivedTensorModuleMap (D : DerivedTensorData.DerivedTensorProduct A)
    {J J' : ModuleCat.{u} A} (f : J ⟶ J') :
    D.tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj J) ⟶
      D.tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj J') := by
  letI := D.isLeftDerived J'
  exact Functor.leftDerivedNatTrans _ _ (D.comparison J) (D.comparison J')
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (Functor.whiskerRight (((tensoringRight (ModuleCat.{u} A)).map f).mapHomologicalComplex
      (ComplexShape.up ℤ)) DerivedCategory.Q)

/-- Compatibility of the canonical derived module map with comparison. -/
@[reassoc]
public theorem derivedTensorModuleMap_comparison (D : DerivedTensorData.DerivedTensorProduct A)
    {J J' : ModuleCat.{u} A} (f : J ⟶ J')
    (M : CochainComplex (ModuleCat.{u} A) ℤ) :
    (derivedTensorModuleMap D f).app (DerivedCategory.Q.obj M) ≫
        (D.comparison J').app M =
      (D.comparison J).app M ≫ DerivedCategory.Q.map
        ((((tensoringRight (ModuleCat.{u} A)).map f).mapHomologicalComplex
          (ComplexShape.up ℤ)).app M) := by
  let := D.isLeftDerived J'
  exact Functor.leftDerivedNatTrans_app _ _ (D.comparison J) (D.comparison J')
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (Functor.whiskerRight
      (((tensoringRight (ModuleCat.{u} A)).map f).mapHomologicalComplex
        (ComplexShape.up ℤ)) DerivedCategory.Q) M

/-- The inverse system of derived tensor products `Iⁿ ⊗ᴸ M`. The transitions derive the
ordinary inclusions, transported through the chosen symmetry. -/
public def derivedTensorIdealSystem (D : DerivedTensorData.DerivedTensorProduct A)
    (symmetry : D.tensor ≅ D.tensor.flip)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) :=
  Functor.ofOpSequence
    (X := fun n => (D.tensor.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (idealPowerModule I n))).obj
        (DerivedCategory.Q.obj M))
    (fun n =>
      ((symmetry.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (idealPowerModule I (n + 1)))).app (DerivedCategory.Q.obj M)).hom ≫
      (derivedTensorModuleMap D (idealPowerModuleTransition I n)).app
        (DerivedCategory.Q.obj M) ≫
      ((symmetry.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (idealPowerModule I n))).app (DerivedCategory.Q.obj M)).inv)

/-- The inverse system of termwise ideal-power complexes, for its canonical transition maps. -/
public def idealPowerSystem (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A)
    (t : ∀ n, idealPowerComplex M I (n + 1) ⟶ idealPowerComplex M I n) :=
  Functor.ofOpSequence
    (X := fun n => DerivedCategory.Q.obj (idealPowerComplex M I n))
    (fun n => DerivedCategory.Q.map (t n))

/-- The canonical map `Iⁿ ⊗ᴸ M → Iⁿ M`: first use the chosen natural tensor symmetry,
then compare derived tensor product with ordinary termwise tensor product and factor scalar
multiplication through its image. -/
public def derivedToIdealPowerMap (D : DerivedTensorData.DerivedTensorProduct A)
    (symmetry : D.tensor ≅ D.tensor.flip)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) (n : ℕ) :
    (derivedTensorIdealSystem D symmetry M I).obj (op n) ⟶
      DerivedCategory.Q.obj (idealPowerComplex M I n) :=
  (symmetry.hom.app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (idealPowerModule I n))).app
        (DerivedCategory.Q.obj M) ≫
    (D.comparison (idealPowerModule I n)).app M ≫
    DerivedCategory.Q.map (factorThruImage (idealPowerMultiplication M I n))

/-- Scalar multiplication commutes with the inclusion of consecutive powers. -/
@[reassoc]
public theorem tensorIdealPowerTransition_multiplication
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) (n : ℕ) :
    tensorIdealPowerTransition M I n ≫ idealPowerMultiplication M I n =
      idealPowerMultiplication M I (n + 1) := by
  ext i : 1
  change (M.X i ◁ idealPowerModuleTransition I n) ≫
      ((M.X i ◁ idealPowerSubtype I n) ≫ (ρ_ (M.X i)).hom) = _
  rw [← Category.assoc, ← MonoidalCategory.whiskerLeft_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical derived comparisons commute with every ideal-power transition compatible
with the inclusions into the original complex. This is a theorem, not additional input to
Tag 0G3N or Tag 0928. -/
public theorem derivedToIdealPowerMap_naturality (D : DerivedTensorData.DerivedTensorProduct A)
    (symmetry : D.tensor ≅ D.tensor.flip)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) (n : ℕ)
    (t : idealPowerComplex M I (n + 1) ⟶ idealPowerComplex M I n)
    (ht : t ≫ image.ι (idealPowerMultiplication M I n) =
      image.ι (idealPowerMultiplication M I (n + 1))) :
    (derivedTensorIdealSystem D symmetry M I).map (homOfLE (Nat.le_succ n)).op ≫
        derivedToIdealPowerMap D symmetry M I n =
      derivedToIdealPowerMap D symmetry M I (n + 1) ≫ DerivedCategory.Q.map t := by
  have hfactor : tensorIdealPowerTransition M I n ≫
        factorThruImage (idealPowerMultiplication M I n) =
      factorThruImage (idealPowerMultiplication M I (n + 1)) ≫ t := by
    apply (cancel_mono (image.ι (idealPowerMultiplication M I n))).1
    rw [Category.assoc, Category.assoc, ht, image.fac, image.fac,
      tensorIdealPowerTransition_multiplication]
  dsimp only [derivedTensorIdealSystem]
  rw [Functor.ofOpSequence_map_homOfLE_succ]
  dsimp only [derivedToIdealPowerMap]
  simp only [Category.assoc, Iso.app_hom, Iso.app_inv, Iso.inv_hom_id_app_app_assoc]
  rw [derivedTensorModuleMap_comparison_assoc]
  simp only [Category.assoc]
  change _ ≫ _ ≫ DerivedCategory.Q.map (tensorIdealPowerTransition M I n) ≫ _ = _
  rw [← DerivedCategory.Q.map_comp, hfactor, DerivedCategory.Q.map_comp]


private lemma hasPointwiseLeftDerivedFunctor_mapHomotopyCategory
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [EnoughProjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    [PreservesColimitsOfShape ℕ F] :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  let P : ObjectProperty A := fun X => Projective X
  let : P.ContainsZero := ⟨0, isZero_zero A, inferInstance⟩
  refine F.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex P
    (fun X Y hX hY => ?_) (fun X =>
      ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩) ?_
  · let : Projective X := hX
    let : Projective Y := hY
    exact inferInstance
  · intro a L hL hP hacyc
    let := hL
    have (n : ℤ) : Projective (L.X n) := hP n
    have := CochainComplex.isKProjective_of_projective L a
    let h := F.mapHomotopy (CochainComplex.IsKProjective.homotopyZero (𝟙 L) hacyc)
    intro n
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    apply (IsZero.iff_id_eq_zero _).2
    simpa using h.homologyMap_eq n

private def isInitial_mkId_of_map_bijective
    {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (X : C)
    (hL : ∀ Y : C, Function.Bijective (L.map : (X ⟶ Y) → _)) :
    IsInitial (StructuredArrow.mk (𝟙 (L.obj X)) : StructuredArrow (L.obj X) L) := by
  apply IsInitial.ofUniqueHom
    (fun Y => StructuredArrow.homMk ((hL Y.right).surjective Y.hom).choose
      (by simpa using ((hL Y.right).surjective Y.hom).choose_spec))
  intro Y f
  apply StructuredArrow.hom_ext
  apply (hL Y.right).injective
  change L.map f.right = L.map ((hL Y.right).surjective Y.hom).choose
  rw [((hL Y.right).surjective Y.hom).choose_spec]
  simpa using f.w

private lemma isIso_comparison_homotopy_of_isKProjective
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [EnoughProjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    [PreservesColimitsOfShape ℕ F]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (P : CochainComplex A ℤ) [P.IsKProjective] :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)) := by
  have := hasPointwiseLeftDerivedFunctor_mapHomotopyCategory F
  let h := LF.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor α
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))
  have hi := isInitial_mkId_of_map_bijective DerivedCategory.Qh
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj P)
    (fun Y => CochainComplex.IsKProjective.Qh_map_bijective P Y)
  simpa using (h _).isIso_π_app_of_isInitial _ hi

private lemma isIso_comparison_of_isKProjective
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    [EnoughProjectives A] [HasDerivedCategory A] [HasDerivedCategory B]
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    [PreservesColimitsOfShape ℕ F]
    (LF : DerivedCategory A ⥤ DerivedCategory B)
    (α : DerivedCategory.Q ⋙ LF ⟶
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    [LF.IsLeftDerivedFunctor α (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))]
    (P : CochainComplex A ℤ) [P.IsKProjective] : IsIso (α.app P) := by
  have := Functor.IsLeftDerivedFunctor.isRightKanExtension LF α
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
  let q := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let eF : q ⋙ (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ≅
      F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso B)
  let eL := DerivedCategory.quotientCompQhIso A
  let β := ((whiskeringLeft _ _ _).obj q).preimage
    ((Functor.associator _ _ _).inv ≫ whiskerRight eL.hom LF ≫ α ≫ eF.inv)
  have hβ : (Functor.associator _ _ _).hom ≫ whiskerLeft q β =
      whiskerRight eL.hom LF ≫ α ≫ eF.inv := by
    dsimp [β]
    rw [← whiskeringLeft_obj_map, map_preimage]
    simp
  have hb : LF.IsRightKanExtension β := by
    rw [TwoTermComplex.isRightKanExtension_iff_precomp_of_fullyFaithful_whiskeringLeft q LF β, hβ]
    exact (TwoTermComplex.isRightKanExtension_iff_of_iso LF eL eF.symm α).1 inferInstance
  have : LF.IsLeftDerivedFunctor β
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := ⟨hb⟩
  have hβP : IsIso (β.app (q.obj P)) :=
    isIso_comparison_homotopy_of_isKProjective F LF β P
  have heq := congr_app hβ P
  dsimp at heq
  have hi : IsIso (LF.map (eL.hom.app P) ≫ α.app P ≫ eF.inv.app P) := by
    rw [← heq, Category.id_comp]
    exact hβP
  exact (isIso_comp_right_iff (α.app P) _).1 ((isIso_comp_left_iff _ _).1 hi)

private lemma isIso_tensorComparison_of_isKProjective
    {A : Type u} [CommRing A] (D : DerivedTensorData.DerivedTensorProduct A)
    (J : ModuleCat.{u} A) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    [P.IsKProjective] : IsIso ((D.comparison J).app P) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u} A) := AB5OfSize_of_univLE.{0, 0, u, u} _
  have := D.isLeftDerived J
  have : PreservesFiniteColimits (StacksDraft.TorAmplitude.tensorModuleRight J) := by
    change PreservesFiniteColimits
      ((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat.{u} A)).obj J)
    infer_instance
  have : PreservesColimitsOfShape ℕ (StacksDraft.TorAmplitude.tensorModuleRight J) := by
    change PreservesColimitsOfShape ℕ
      ((CategoryTheory.MonoidalCategory.tensoringRight (ModuleCat.{u} A)).obj J)
    infer_instance
  apply isIso_comparison_of_isKProjective (StacksDraft.TorAmplitude.tensorModuleRight J)
    (D.tensor.flip.obj ((DerivedCategory.singleFunctor _ 0).obj J)) (D.comparison J) P

/-- Scalar multiplication by an ideal is injective after tensoring with a flat module. -/
private lemma mono_idealPowerMultiplication
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    [∀ i : ℤ, Module.Flat A (M.X i)] (I : Ideal A) (n : ℕ) :
    Mono (idealPowerMultiplication M I n) := by
  have (i : ℤ) : Mono (M.X i ◁ idealPowerSubtype I n) := by
    rw [ModuleCat.mono_iff_injective]
    exact Module.Flat.lTensor_preserves_injective_linearMap
      (I ^ (n + 1)).subtype Subtype.val_injective
  have (i : ℤ) : Mono ((idealPowerMultiplication M I n).f i) := by
    change Mono ((M.X i ◁ idealPowerSubtype I n) ≫
      (MonoidalCategory.rightUnitor (M.X i)).hom)
    infer_instance
  exact HomologicalComplex.mono_of_mono_f _ fun _ => inferInstance

set_option backward.isDefEq.respectTransparency false in
/-- For a K-projective complex of flat modules, the comparison with termwise ideal powers
is already an isomorphism at each level. -/
private lemma isIso_derivedToIdealPowerMap
    (D : DerivedTensorData.DerivedTensorProduct A) (symmetry : D.tensor ≅ D.tensor.flip)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) [M.IsKProjective]
    [∀ i : ℤ, Module.Flat A (M.X i)] (I : Ideal A) (n : ℕ) :
    IsIso (derivedToIdealPowerMap D symmetry M I n) := by
  have : Mono (idealPowerMultiplication M I n) := mono_idealPowerMultiplication M I n
  have hcomparison : IsIso ((D.comparison (idealPowerModule I n)).app M) :=
    isIso_tensorComparison_of_isKProjective D _ M
  have : IsIso (factorThruImage (idealPowerMultiplication M I n)) := by
    have : Mono (factorThruImage (idealPowerMultiplication M I n)) :=
      mono_of_mono_fac (image.fac _)
    exact isIso_of_mono_of_epi _
  have himage : IsIso (DerivedCategory.Q.map
      (factorThruImage (idealPowerMultiplication M I n))) := inferInstance
  have hsymmetry : IsIso ((symmetry.hom.app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (idealPowerModule I n))).app (DerivedCategory.Q.obj M)) :=
    ((symmetry.app _).app _).isIso_hom
  change IsIso ((symmetry.hom.app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (idealPowerModule I n))).app (DerivedCategory.Q.obj M) ≫
    (D.comparison (idealPowerModule I n)).app M ≫
      DerivedCategory.Q.map (factorThruImage (idealPowerMultiplication M I n)))
  exact IsIso.comp_isIso' hsymmetry (IsIso.comp_isIso' hcomparison himage)

/-- Termwise tensoring a morphism of complexes with an ideal power. -/
private abbrev tensorIdealPowerMap
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (I : Ideal A) (n : ℕ) :=
  (((tensoringRight (ModuleCat.{u} A)).obj (idealPowerModule I n)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map p

private lemma tensorIdealPowerMap_comp
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (I : Ideal A) (n : ℕ) :
    tensorIdealPowerMap p I n ≫ idealPowerMultiplication M I n =
      idealPowerMultiplication P I n ≫ p := by
  apply HomologicalComplex.Hom.ext
  funext i
  change (p.f i ▷ idealPowerModule I n) ≫
      (M.X i ◁ idealPowerSubtype I n) ≫ (MonoidalCategory.rightUnitor (M.X i)).hom =
    ((P.X i ◁ idealPowerSubtype I n) ≫
      (MonoidalCategory.rightUnitor (P.X i)).hom) ≫ p.f i
  rw [Category.assoc, ← MonoidalCategory.rightUnitor_naturality]
  exact (MonoidalCategory.whisker_exchange_assoc (p.f i)
    (idealPowerSubtype I n) (MonoidalCategory.rightUnitor (M.X i)).hom).symm

/-- A morphism of complexes induces a morphism on their termwise ideal powers. -/
private def idealPowerComplexMap
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (I : Ideal A) (n : ℕ) :
    idealPowerComplex P I n ⟶ idealPowerComplex M I n :=
  image.map (Arrow.homMk' (tensorIdealPowerMap p I n) p
    (tensorIdealPowerMap_comp p I n))

private lemma idealPowerComplexMap_comp
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (I : Ideal A) (n : ℕ) :
    idealPowerComplexMap p I n ≫ image.ι (idealPowerMultiplication M I n) =
      image.ι (idealPowerMultiplication P I n) ≫ p :=
  image.map_ι _

private lemma factorThruImage_idealPowerComplexMap
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (I : Ideal A) (n : ℕ) :
    factorThruImage (idealPowerMultiplication P I n) ≫ idealPowerComplexMap p I n =
      tensorIdealPowerMap p I n ≫ factorThruImage (idealPowerMultiplication M I n) :=
  image.factor_map (Arrow.homMk' (tensorIdealPowerMap p I n) p
    (tensorIdealPowerMap_comp p I n))

set_option backward.isDefEq.respectTransparency false in
private lemma derivedToIdealPowerMap_naturality_complex
    (D : DerivedTensorData.DerivedTensorProduct A) (symmetry : D.tensor ≅ D.tensor.flip)
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (I : Ideal A) (n : ℕ) :
    (D.tensor.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (idealPowerModule I n))).map (DerivedCategory.Q.map p) ≫
        derivedToIdealPowerMap D symmetry M I n =
      derivedToIdealPowerMap D symmetry P I n ≫
        DerivedCategory.Q.map (idealPowerComplexMap p I n) := by
  change (D.tensor.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (idealPowerModule I n))).map (DerivedCategory.Q.map p) ≫
      ((symmetry.hom.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (idealPowerModule I n))).app (DerivedCategory.Q.obj M) ≫
        (D.comparison (idealPowerModule I n)).app M ≫
          DerivedCategory.Q.map (factorThruImage (idealPowerMultiplication M I n))) =
    ((symmetry.hom.app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (idealPowerModule I n))).app (DerivedCategory.Q.obj P) ≫
        (D.comparison (idealPowerModule I n)).app P ≫
          DerivedCategory.Q.map (factorThruImage (idealPowerMultiplication P I n))) ≫
      DerivedCategory.Q.map (idealPowerComplexMap p I n)
  rw [NatTrans.naturality_assoc]
  simp only [Category.assoc]
  have h := (D.comparison (idealPowerModule I n)).naturality p
  change (D.tensor.map (DerivedCategory.Q.map p)).app
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (idealPowerModule I n)) ≫
      (D.comparison (idealPowerModule I n)).app M =
    (D.comparison (idealPowerModule I n)).app P ≫
      DerivedCategory.Q.map (tensorIdealPowerMap p I n) at h
  erw [reassoc_of% h]
  erw [← DerivedCategory.Q.map_comp, ← factorThruImage_idealPowerComplexMap,
    DerivedCategory.Q.map_comp]

private lemma strictlyBounded_of_isZero_outside
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (h : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i → IsZero (M.X i)) :
    ∃ a b : ℤ, M.IsStrictlyGE a ∧ M.IsStrictlyLE b := by
  obtain ⟨a, b, _, h⟩ := h
  refine ⟨a, b, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyGE_iff]
    exact fun i hi => h i (Or.inl hi)
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => h i (Or.inr hi)

/-- The canonical transition on the images `Iⁿ⁺¹M → IⁿM`. -/
private def idealPowerComplexTransition (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : Ideal A) (n : ℕ) : idealPowerComplex M I (n + 1) ⟶ idealPowerComplex M I n :=
  image.lift
    { I := image (idealPowerMultiplication M I n)
      m := image.ι (idealPowerMultiplication M I n)
      e := tensorIdealPowerTransition M I n ≫
        factorThruImage (idealPowerMultiplication M I n)
      fac := by rw [Category.assoc, image.fac, tensorIdealPowerTransition_multiplication] }

private lemma idealPowerComplexTransition_comp (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (I : Ideal A) (n : ℕ) :
    idealPowerComplexTransition M I n ≫ image.ι (idealPowerMultiplication M I n) =
      image.ι (idealPowerMultiplication M I (n + 1)) :=
  image.lift_fac _

set_option backward.isDefEq.respectTransparency false in
/-- The canonical comparisons form a morphism of inverse sequences. -/
private def derivedToIdealPowerNatTrans
    (D : DerivedTensorData.DerivedTensorProduct A) (symmetry : D.tensor ≅ D.tensor.flip)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) :
    derivedTensorIdealSystem D symmetry M I ⟶
      idealPowerSystem M I (idealPowerComplexTransition M I) :=
  NatTrans.ofOpSequence (derivedToIdealPowerMap D symmetry M I)
    (fun n => by
      convert Stacks.AdicSystem.IdealPowerTensorComparison.derivedToIdealPowerMap_naturality D
        symmetry M I n
        (idealPowerComplexTransition M I n) (idealPowerComplexTransition_comp M I n)
        using 1
      simp [derivedTensorIdealSystem, idealPowerSystem])

private lemma derivedToIdealPowerNatTrans_app
    (D : DerivedTensorData.DerivedTensorProduct A) (symmetry : D.tensor ≅ D.tensor.flip)
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) (n : ℕ) :
    (derivedToIdealPowerNatTrans D symmetry M I).app (op n) =
      derivedToIdealPowerMap D symmetry M I n := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma idealPowerComplexMap_transition
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (I : Ideal A) (n : ℕ) :
    idealPowerComplexTransition P I n ≫ idealPowerComplexMap p I n =
      idealPowerComplexMap p I (n + 1) ≫ idealPowerComplexTransition M I n := by
  apply (cancel_mono (image.ι (idealPowerMultiplication M I n))).1
  erw [Category.assoc, idealPowerComplexMap_comp, ← Category.assoc,
    idealPowerComplexTransition_comp, Category.assoc, idealPowerComplexTransition_comp,
    idealPowerComplexMap_comp]

set_option backward.isDefEq.respectTransparency false in
/-- A map of complexes acts naturally on the systems of ideal-power images. -/
private def idealPowerSystemMap
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (I : Ideal A) :
    idealPowerSystem P I (idealPowerComplexTransition P I) ⟶
      idealPowerSystem M I (idealPowerComplexTransition M I) :=
  NatTrans.ofOpSequence (fun n => DerivedCategory.Q.map (idealPowerComplexMap p I n))
    (fun n => by
      simpa only [idealPowerSystem, Functor.ofOpSequence_map_homOfLE_succ,
        Functor.map_comp] using
        congrArg DerivedCategory.Q.map (idealPowerComplexMap_transition p I n))

private lemma idealPowerSystemMap_app
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (I : Ideal A) (n : ℕ) :
    (idealPowerSystemMap p I).app (op n) =
      DerivedCategory.Q.map (idealPowerComplexMap p I n) := rfl

set_option backward.isDefEq.respectTransparency false in
private def derivedTensorIdealSystemMap
    (D : DerivedTensorData.DerivedTensorProduct A) (symmetry : D.tensor ≅ D.tensor.flip)
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (I : Ideal A) :
    derivedTensorIdealSystem D symmetry P I ⟶ derivedTensorIdealSystem D symmetry M I :=
  NatTrans.ofOpSequence
    (fun n => (D.tensor.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (idealPowerModule I n))).map (DerivedCategory.Q.map p))
    (fun n => by
      let β := symmetry.hom.app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (idealPowerModule I (n + 1))) ≫
        derivedTensorModuleMap D (idealPowerModuleTransition I n) ≫
        symmetry.inv.app
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (idealPowerModule I n))
      simpa only [derivedTensorIdealSystem, Functor.ofOpSequence_map_homOfLE_succ,
        NatTrans.comp_app, Iso.app_hom, Iso.app_inv, β, Category.assoc] using
        (β.naturality (DerivedCategory.Q.map p)).symm)

private lemma derivedToIdealPowerNatTrans_naturality
    (D : DerivedTensorData.DerivedTensorProduct A) (symmetry : D.tensor ≅ D.tensor.flip)
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (I : Ideal A) :
    derivedTensorIdealSystemMap D symmetry p I ≫ derivedToIdealPowerNatTrans D symmetry M I =
      derivedToIdealPowerNatTrans D symmetry P I ≫ idealPowerSystemMap p I := by
  ext n
  exact derivedToIdealPowerMap_naturality_complex D symmetry p I n.unop

/-- Levelwise isomorphisms have pro-inverses without changing the index. -/
private lemma proInverse_of_isIso_app
    {C : Type*} [Category C] {X Y : ℕᵒᵖ ⥤ C} (e : X ⟶ Y)
    (he : ∀ n : ℕ, IsIso (e.app (op n))) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
      (s : Y.obj (op m) ⟶ X.obj (op n)),
      e.app (op m) ≫ s = X.map (homOfLE h).op ∧
        s ≫ e.app (op n) = Y.map (homOfLE h).op := by
  intro n
  let := he n
  refine ⟨n, le_rfl, inv (e.app (op n)), ?_, ?_⟩ <;> simp

/-- Composition of pro-isomorphisms of inverse sequences. -/
private lemma proInverse_comp
    {C : Type*} [Category C] {X Y Z : ℕᵒᵖ ⥤ C}
    (e : X ⟶ Y) (f : Y ⟶ Z)
    (he : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
      (s : Y.obj (op m) ⟶ X.obj (op n)),
      e.app (op m) ≫ s = X.map (homOfLE h).op ∧
        s ≫ e.app (op n) = Y.map (homOfLE h).op)
    (hf : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
      (s : Z.obj (op m) ⟶ Y.obj (op n)),
      f.app (op m) ≫ s = Y.map (homOfLE h).op ∧
        s ≫ f.app (op n) = Z.map (homOfLE h).op) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
      (s : Z.obj (op m) ⟶ X.obj (op n)),
      (e ≫ f).app (op m) ≫ s = X.map (homOfLE h).op ∧
        s ≫ (e ≫ f).app (op n) = Z.map (homOfLE h).op := by
  rw [← DerivedReductionProIso.hasProInverse_iff_nat] at he hf ⊢
  exact he.comp hf

/-- A pro-isomorphism can be cancelled on the left. -/
private lemma proInverse_leftCancel
    {C : Type*} [Category C] {X Y Z : ℕᵒᵖ ⥤ C}
    (e : X ⟶ Y) (f : Y ⟶ Z)
    (he : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
      (s : Y.obj (op m) ⟶ X.obj (op n)),
      e.app (op m) ≫ s = X.map (homOfLE h).op ∧
        s ≫ e.app (op n) = Y.map (homOfLE h).op)
    (hef : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
      (s : Z.obj (op m) ⟶ X.obj (op n)),
      (e ≫ f).app (op m) ≫ s = X.map (homOfLE h).op ∧
        s ≫ (e ≫ f).app (op n) = Z.map (homOfLE h).op) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
      (s : Z.obj (op m) ⟶ Y.obj (op n)),
      f.app (op m) ≫ s = Y.map (homOfLE h).op ∧
        s ≫ f.app (op n) = Z.map (homOfLE h).op := by
  rw [← DerivedReductionProIso.hasProInverse_iff_nat] at he hef ⊢
  exact DerivedReductionProIso.proInverse_of_common_source e (e ≫ f) f rfl he hef

section Triangles

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ]
  [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

private lemma yoneda_exact₁ {T : Triangle C} (hT : T ∈ distTriang C) {X : C}
    (f : T.obj₁ ⟶ X) (hf : T.mor₃ ≫ f⟦(1 : ℤ)⟧' = 0) : ∃ g : T.obj₂ ⟶ X, f = T.mor₁ ≫ g := by
  have hrot : Triangle.mk T.mor₂ T.mor₃ (-(T.mor₁⟦(1 : ℤ)⟧')) ∈ distTriang C :=
    rot_of_distTriang _ hT
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₃ _ hrot (f⟦(1 : ℤ)⟧') hf
  refine ⟨(shiftFunctor C (1 : ℤ)).preimage (-g), (shiftFunctor C (1 : ℤ)).map_injective ?_⟩
  rw [Functor.map_comp, Functor.map_preimage, hg]
  simp only [Triangle.mk_mor₃, Preadditive.comp_neg, Preadditive.neg_comp]

private lemma triangle_hom₁_comp_eq_zero {T U V : Triangle C}
    (hU : U ∈ distTriang C) (f : T ⟶ U) (g : U ⟶ V)
    (hf : f.hom₂ = 0) (hg : g.hom₃ = 0) : f.hom₁ ≫ g.hom₁ = 0 := by
  obtain ⟨s, hs⟩ := yoneda_exact₁ hU g.hom₁ (by rw [g.comm₃, hg, zero_comp])
  rw [hs, ← Category.assoc, ← f.comm₁, hf, comp_zero, zero_comp]

private lemma triangle_hom₁_sub_comp_sub_eq_zero {T U V : Triangle C}
    (hU : U ∈ distTriang C) (f f' : T ⟶ U) (g g' : U ⟶ V)
    (hf : f.hom₂ = f'.hom₂) (hg : g.hom₃ = g'.hom₃) :
    (f.hom₁ - f'.hom₁) ≫ (g.hom₁ - g'.hom₁) = 0 := by
  exact triangle_hom₁_comp_eq_zero hU (f - f') (g - g')
    (by change f.hom₂ - f'.hom₂ = 0; rw [hf, sub_self])
    (by change g.hom₃ - g'.hom₃ = 0; rw [hg, sub_self])

private lemma exists_triangle_proInverse_mod_hom₁
    {T U : ℕᵒᵖ ⥤ Triangle C} (f : T ⟶ U)
    (hT : ∀ n, T.obj (op n) ∈ distTriang C) (hU : ∀ n, U.obj (op n) ∈ distTriang C)
    (h₂ : ∀ n, IsIso (f.app (op n)).hom₂)
    {n m : ℕ} (h : n ≤ m)
    (s : (U.obj (op m)).obj₃ ⟶ (T.obj (op n)).obj₃)
    (hs : (f.app (op m)).hom₃ ≫ s = (T.map (homOfLE h).op).hom₃)
    (hs' : s ≫ (f.app (op n)).hom₃ = (U.map (homOfLE h).op).hom₃) :
    ∃ t : U.obj (op m) ⟶ T.obj (op n),
      (f.app (op m) ≫ t).hom₂ = (T.map (homOfLE h).op).hom₂ ∧
      (f.app (op m) ≫ t).hom₃ = (T.map (homOfLE h).op).hom₃ ∧
      (t ≫ f.app (op n)).hom₂ = (U.map (homOfLE h).op).hom₂ ∧
      (t ≫ f.app (op n)).hom₃ = (U.map (homOfLE h).op).hom₃ := by
  let := h₂ n
  let := h₂ m
  let b := (U.map (homOfLE h).op).hom₂ ≫ inv (f.app (op n)).hom₂
  have hb : (f.app (op m)).hom₂ ≫ b = (T.map (homOfLE h).op).hom₂ := by
    have hh := congrArg (fun g => g.hom₂) (f.naturality (homOfLE h).op)
    change (T.map (homOfLE h).op).hom₂ ≫ (f.app (op n)).hom₂ =
      (f.app (op m)).hom₂ ≫ (U.map (homOfLE h).op).hom₂ at hh
    dsimp [b]
    rw [← Category.assoc, ← hh, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hw : (U.obj (op m)).mor₂ ≫ s = b ≫ (T.obj (op n)).mor₂ := by
    apply (cancel_epi (f.app (op m)).hom₂).1
    rw [← Category.assoc, ← (f.app (op m)).comm₂, Category.assoc, hs,
      (T.map (homOfLE h).op).comm₂, ← Category.assoc, hb]
  obtain ⟨a, ha, hc⟩ := complete_distinguished_triangle_morphism₁ _ _ (hU m) (hT n) b s hw
  refine ⟨{ hom₁ := a, hom₂ := b, hom₃ := s, comm₁ := ha, comm₂ := hw, comm₃ := hc },
    hb, hs, ?_, hs'⟩
  change ((U.map (homOfLE h).op).hom₂ ≫ inv (f.app (op n)).hom₂) ≫ _ = _
  simp

private lemma exists_proInverse_hom₁_of_isIso_hom₂_of_proInverse_hom₃
    {T U : ℕᵒᵖ ⥤ Triangle C} (f : T ⟶ U)
    (hT : ∀ n, T.obj (op n) ∈ distTriang C) (hU : ∀ n, U.obj (op n) ∈ distTriang C)
    (h₂ : ∀ n, IsIso (f.app (op n)).hom₂)
    (h₃ : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
      (s : (U.obj (op m)).obj₃ ⟶ (T.obj (op n)).obj₃),
      (f.app (op m)).hom₃ ≫ s = (T.map (homOfLE h).op).hom₃ ∧
      s ≫ (f.app (op n)).hom₃ = (U.map (homOfLE h).op).hom₃) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
      (s : (U.obj (op m)).obj₁ ⟶ (T.obj (op n)).obj₁),
      (f.app (op m)).hom₁ ≫ s = (T.map (homOfLE h).op).hom₁ ∧
      s ≫ (f.app (op n)).hom₁ = (U.map (homOfLE h).op).hom₁ := by
  intro n
  obtain ⟨m, hnm, s₃, hs₃, hs₃'⟩ := h₃ n
  obtain ⟨s, hs₂, hs₃, hs₂', hs₃'⟩ :=
    exists_triangle_proInverse_mod_hom₁ f hT hU h₂ hnm s₃ hs₃ hs₃'
  obtain ⟨k, hmk, t₃, ht₃, ht₃'⟩ := h₃ m
  obtain ⟨t, ht₂, ht₃, ht₂', ht₃'⟩ :=
    exists_triangle_proInverse_mod_hom₁ f hT hU h₂ hmk t₃ ht₃ ht₃'
  let x := T.map (homOfLE hnm).op
  let x' := T.map (homOfLE hmk).op
  let y := U.map (homOfLE hnm).op
  let y' := U.map (homOfLE hmk).op
  have hf₁ : (f.app (op k)).hom₁ ≫ y'.hom₁ = x'.hom₁ ≫ (f.app (op m)).hom₁ := by
    exact (congrArg (fun g => g.hom₁) (f.naturality (homOfLE hmk).op)).symm
  have hf₂ : x.hom₁ ≫ (f.app (op n)).hom₁ = (f.app (op m)).hom₁ ≫ y.hom₁ := by
    exact congrArg (fun g => g.hom₁) (f.naturality (homOfLE hnm).op)
  have hx : (T.map (homOfLE (hnm.trans hmk)).op).hom₁ = x'.hom₁ ≫ x.hom₁ := by
    change (T.map ((homOfLE hmk).op ≫ (homOfLE hnm).op)).hom₁ = _
    rw [T.map_comp]
    rfl
  have hy : (U.map (homOfLE (hnm.trans hmk)).op).hom₁ = y'.hom₁ ≫ y.hom₁ := by
    change (U.map ((homOfLE hmk).op ≫ (homOfLE hnm).op)).hom₁ = _
    rw [U.map_comp]
    rfl
  have he₁ := triangle_hom₁_sub_comp_sub_eq_zero (hT m)
    (f.app (op k) ≫ t) x' (f.app (op m) ≫ s) x ht₂ hs₃
  have he₂ := triangle_hom₁_sub_comp_sub_eq_zero (hU m)
    (t ≫ f.app (op m)) y' (s ≫ f.app (op n)) y ht₂' hs₃'
  refine ⟨k, hnm.trans hmk,
    y'.hom₁ ≫ s.hom₁ + t.hom₁ ≫ x.hom₁ - t.hom₁ ≫ (f.app (op m)).hom₁ ≫ s.hom₁,
    ?_, ?_⟩
  · change ((f.app (op k)).hom₁ ≫ t.hom₁ - x'.hom₁) ≫
      ((f.app (op m)).hom₁ ≫ s.hom₁ - x.hom₁) = 0 at he₁
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc] at he₁
    rw [hx]
    simp only [Preadditive.comp_sub, Preadditive.comp_add, ← Category.assoc]
    rw [hf₁]
    simp only [Category.assoc]
    apply sub_eq_zero.mp
    convert congrArg Neg.neg he₁ using 1 <;> abel
  · change (t.hom₁ ≫ (f.app (op m)).hom₁ - y'.hom₁) ≫
      (s.hom₁ ≫ (f.app (op n)).hom₁ - y.hom₁) = 0 at he₂
    simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc] at he₂
    rw [hy]
    simp only [Preadditive.sub_comp, Preadditive.add_comp, Category.assoc]
    rw [hf₂]
    apply sub_eq_zero.mp
    convert congrArg Neg.neg he₂ using 1 <;> abel

end Triangles

private def reductionProjection (M : CochainComplex (ModuleCat.{u} A) ℤ) (J : Ideal A) :
    M ⟶ (reduceComplex J).obj M where
  f i := ModuleCat.ofHom (J • (⊤ : Submodule A (M.X i))).mkQ
  comm' i j _ := by ext x; rfl

private lemma reductionProjection_naturality
    {M N : CochainComplex (ModuleCat.{u} A) ℤ} (f : M ⟶ N) (J : Ideal A) :
    f ≫ reductionProjection N J = reductionProjection M J ≫ (reduceComplex J).map f := by
  ext i x
  rfl

set_option backward.isDefEq.respectTransparency false in
private lemma range_idealPowerMultiplication_f
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) (n : ℕ) (i : ℤ) :
    LinearMap.range ((idealPowerMultiplication M I n).f i).hom =
      I ^ (n + 1) • (⊤ : Submodule A (M.X i)) := by
  apply le_antisymm
  · rintro x ⟨t, rfl⟩
    induction t using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul x r => exact Submodule.smul_mem_smul r.property (Submodule.mem_top)
    | add x y hx hy => simpa only [_root_.map_add] using Submodule.add_mem _ hx hy
  · refine Submodule.smul_le.mpr fun r hr x _ => ?_
    exact ⟨x ⊗ₜ[A] ⟨r, hr⟩, rfl⟩

private lemma idealPowerMultiplication_reductionProjection
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) (n : ℕ) :
    idealPowerMultiplication M I n ≫ reductionProjection M (I ^ (n + 1)) = 0 := by
  ext i : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (I ^ (n + 1) • (⊤ : Submodule A (M.X i))).mkQ
    (((idealPowerMultiplication M I n).f i).hom x) = 0
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
    ← range_idealPowerMultiplication_f]
  exact LinearMap.mem_range_self _ x

private lemma image_ι_reductionProjection
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) (n : ℕ) :
    image.ι (idealPowerMultiplication M I n) ≫ reductionProjection M (I ^ (n + 1)) = 0 := by
  apply (cancel_epi (factorThruImage (idealPowerMultiplication M I n))).1
  rw [← Category.assoc, image.fac, idealPowerMultiplication_reductionProjection, comp_zero]

private def idealPowerShortComplex
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) (n : ℕ) :
    ShortComplex (CochainComplex (ModuleCat.{u} A) ℤ) :=
  ShortComplex.mk (image.ι (idealPowerMultiplication M I n))
    (reductionProjection M (I ^ (n + 1))) (image_ι_reductionProjection M I n)

private lemma idealPowerShortComplex_shortExact
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) (n : ℕ) :
    (idealPowerShortComplex M I n).ShortExact := by
  have he : Epi (reductionProjection M (I ^ (n + 1))) := by
    apply HomologicalComplex.epi_of_epi_f
    intro i
    rw [ModuleCat.epi_iff_surjective]
    exact Submodule.mkQ_surjective _
  refine { exact := ?_, mono_f := ?_, epi_g := he }
  rotate_left
  · change Mono (image.ι (idealPowerMultiplication M I n))
    infer_instance
  let S := ShortComplex.mk (idealPowerMultiplication M I n)
    (reductionProjection M (I ^ (n + 1))) (idealPowerMultiplication_reductionProjection M I n)
  have hS : S.Exact := by
    apply HomologicalComplex.exact_of_degreewise_exact
    intro i
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range ((idealPowerMultiplication M I n).f i).hom =
      LinearMap.ker (I ^ (n + 1) • (⊤ : Submodule A (M.X i))).mkQ
    rw [range_idealPowerMultiplication_f, Submodule.ker_mkQ]
  let f : S ⟶ idealPowerShortComplex M I n :=
    { τ₁ := factorThruImage (idealPowerMultiplication M I n)
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, idealPowerShortComplex] }
  have : Epi f.τ₁ := by
    change Epi (factorThruImage (idealPowerMultiplication M I n))
    infer_instance
  have : IsIso f.τ₂ := by change IsIso (𝟙 M); infer_instance
  have : Mono f.τ₃ := by change Mono (𝟙 ((reduceComplex (I ^ (n + 1))).obj M)); infer_instance
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono f).1 hS

private abbrev reductionComplexTransition
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) {n m : ℕ} (h : n ≤ m) :
    (reduceComplex (I ^ (m + 1))).obj M ⟶ (reduceComplex (I ^ (n + 1))).obj M :=
  ((Stacks.AdicSystem.DerivedReductionProIso.reductionNatTrans (Ideal.pow_le_pow_right (I := I)
    (Nat.add_le_add_right h 1))).mapHomologicalComplex (ComplexShape.up ℤ)).app M

private lemma epi_reductionProjection
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (J : Ideal A) :
    Epi (reductionProjection M J) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  rw [ModuleCat.epi_iff_surjective]
  exact Submodule.mkQ_surjective _

private lemma reductionProjection_transition
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) {n m : ℕ} (h : n ≤ m) :
    reductionProjection M (I ^ (m + 1)) ≫ reductionComplexTransition M I h =
      reductionProjection M (I ^ (n + 1)) := by
  ext i x
  rfl

private def reductionComplexSystem
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ where
  obj n := (reduceComplex (I ^ (n.unop + 1))).obj M
  map f := reductionComplexTransition M I (leOfHom f.unop)
  map_id n := by
    have := epi_reductionProjection M (I ^ (n.unop + 1))
    apply (cancel_epi (reductionProjection M (I ^ (n.unop + 1)))).1
    rw [reductionProjection_transition, Category.comp_id]
  map_comp {n m k} f g := by
    have := epi_reductionProjection M (I ^ (n.unop + 1))
    apply (cancel_epi (reductionProjection M (I ^ (n.unop + 1)))).1
    rw [reductionProjection_transition, ← Category.assoc, reductionProjection_transition,
      reductionProjection_transition]

set_option backward.isDefEq.respectTransparency false in
private def idealPowerShortComplexTransition
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) (n : ℕ) :
    idealPowerShortComplex M I (n + 1) ⟶ idealPowerShortComplex M I n where
  τ₁ := idealPowerComplexTransition M I n
  τ₂ := 𝟙 M
  τ₃ := reductionComplexTransition M I (Nat.le_succ n)
  comm₁₂ := by simpa [idealPowerShortComplex] using idealPowerComplexTransition_comp M I n
  comm₂₃ := by ext i x; rfl

private def idealPowerShortComplexMap
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (I : Ideal A) (n : ℕ) :
    idealPowerShortComplex P I n ⟶ idealPowerShortComplex M I n where
  τ₁ := idealPowerComplexMap p I n
  τ₂ := p
  τ₃ := (reduceComplex (I ^ (n + 1))).map p
  comm₁₂ := idealPowerComplexMap_comp p I n
  comm₂₃ := reductionProjection_naturality p _

private def idealPowerTriangleSystem
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) :
    ℕᵒᵖ ⥤ Triangle (DerivedCategory (ModuleCat.{u} A)) :=
  Functor.ofOpSequence
    (X := fun n => DerivedCategory.triangleOfSES (idealPowerShortComplex_shortExact M I n))
    (fun n => DerivedCategory.triangleOfSES.map
    (idealPowerShortComplex_shortExact M I (n + 1)) (idealPowerShortComplex_shortExact M I n)
    (idealPowerShortComplexTransition M I n))

set_option backward.isDefEq.respectTransparency false in
private def idealPowerTriangleSystemMap
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M) (I : Ideal A) :
    idealPowerTriangleSystem P I ⟶ idealPowerTriangleSystem M I :=
  NatTrans.ofOpSequence (fun n => DerivedCategory.triangleOfSES.map
    (idealPowerShortComplex_shortExact P I n) (idealPowerShortComplex_shortExact M I n)
    (idealPowerShortComplexMap p I n))
    (fun n => by
      simp only [idealPowerTriangleSystem, Functor.ofOpSequence_map_homOfLE_succ]
      apply Triangle.hom_ext
      · change DerivedCategory.Q.map (idealPowerComplexTransition P I n) ≫
            DerivedCategory.Q.map (idealPowerComplexMap p I n) =
          DerivedCategory.Q.map (idealPowerComplexMap p I (n + 1)) ≫
            DerivedCategory.Q.map (idealPowerComplexTransition M I n)
        rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp,
          idealPowerComplexMap_transition]
      · change DerivedCategory.Q.map (𝟙 P) ≫ DerivedCategory.Q.map p =
          DerivedCategory.Q.map p ≫ DerivedCategory.Q.map (𝟙 M)
        simp
      · change DerivedCategory.Q.map (reductionComplexTransition P I (Nat.le_succ n)) ≫
            DerivedCategory.Q.map ((reduceComplex (I ^ (n + 1))).map p) =
          DerivedCategory.Q.map ((reduceComplex (I ^ (n + 1 + 1))).map p) ≫
            DerivedCategory.Q.map (reductionComplexTransition M I (Nat.le_succ n))
        rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
        congr 1
        exact (((Stacks.AdicSystem.DerivedReductionProIso.reductionNatTrans
          (Ideal.pow_le_pow_right (Nat.add_le_add_right (Nat.le_succ n) 1))).mapHomologicalComplex
            (ComplexShape.up ℤ)).naturality p).symm)

set_option backward.isDefEq.respectTransparency false in
private lemma idealPowerTriangleSystem_map_hom₁
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) {n m : ℕ} (h : n ≤ m) :
    ((idealPowerTriangleSystem M I).map (homOfLE h).op).hom₁ =
      (idealPowerSystem M I (idealPowerComplexTransition M I)).map (homOfLE h).op := by
  let e : idealPowerTriangleSystem M I ⋙ Triangle.π₁ ⟶
      idealPowerSystem M I (idealPowerComplexTransition M I) :=
    NatTrans.ofOpSequence (fun _ => 𝟙 _) (fun n => by
      simp [idealPowerTriangleSystem, idealPowerSystem, DerivedCategory.triangleOfSES.map,
        idealPowerShortComplexTransition, Triangle.π₁])
  simpa [e] using e.naturality (homOfLE h).op

set_option backward.isDefEq.respectTransparency false in
private lemma idealPowerTriangleSystem_map_hom₃
    (M : CochainComplex (ModuleCat.{u} A) ℤ) (I : Ideal A) {n m : ℕ} (h : n ≤ m) :
    ((idealPowerTriangleSystem M I).map (homOfLE h).op).hom₃ =
      Stacks.AdicSystem.DerivedReductionProIso.adicReductionTransition I M h := by
  let e : idealPowerTriangleSystem M I ⋙ Triangle.π₃ ⟶
      reductionComplexSystem M I ⋙ DerivedCategory.Q :=
    NatTrans.ofOpSequence (fun _ => 𝟙 _) (fun n => by
      simp [idealPowerTriangleSystem, reductionComplexSystem, DerivedCategory.triangleOfSES.map,
        idealPowerShortComplexTransition, Triangle.π₃])
  simpa [e, Stacks.AdicSystem.DerivedReductionProIso.adicReductionTransition,
    reductionComplexSystem] using
    e.naturality (homOfLE h).op

private lemma proInverse_idealPowerSystemMap_of_reduction
    {P M : CochainComplex (ModuleCat.{u} A) ℤ} (p : P ⟶ M)
    [IsIso (DerivedCategory.Q.map p)] (I : Ideal A)
    (hp : ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
      (s : DerivedCategory.Q.obj ((reduceComplex (I ^ (m + 1))).obj M) ⟶
        DerivedCategory.Q.obj ((reduceComplex (I ^ (n + 1))).obj P)),
      Stacks.AdicSystem.DerivedReductionProIso.adicReductionComparison I p m ≫ s =
        Stacks.AdicSystem.DerivedReductionProIso.adicReductionTransition I P h ∧
      s ≫ Stacks.AdicSystem.DerivedReductionProIso.adicReductionComparison I p n =
        Stacks.AdicSystem.DerivedReductionProIso.adicReductionTransition I M h) :
    ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
      (s : (idealPowerSystem M I (idealPowerComplexTransition M I)).obj (op m) ⟶
        (idealPowerSystem P I (idealPowerComplexTransition P I)).obj (op n)),
      (idealPowerSystemMap p I).app (op m) ≫ s =
        (idealPowerSystem P I (idealPowerComplexTransition P I)).map (homOfLE h).op ∧
      s ≫ (idealPowerSystemMap p I).app (op n) =
        (idealPowerSystem M I (idealPowerComplexTransition M I)).map (homOfLE h).op := by
  have h := exists_proInverse_hom₁_of_isIso_hom₂_of_proInverse_hom₃
    (idealPowerTriangleSystemMap p I)
    (fun n => DerivedCategory.triangleOfSES_distinguished (idealPowerShortComplex_shortExact P I n))
    (fun n => DerivedCategory.triangleOfSES_distinguished (idealPowerShortComplex_shortExact M I n))
    (fun n => by change IsIso (DerivedCategory.Q.map p); infer_instance)
    (fun n => by
      obtain ⟨m, h, s, hs, hs'⟩ := hp n
      refine ⟨m, h, s, ?_, ?_⟩
      · rw [idealPowerTriangleSystem_map_hom₃]
        exact hs
      · rw [idealPowerTriangleSystem_map_hom₃]
        exact hs')
  intro n
  obtain ⟨m, h, s, hs, hs'⟩ := h n
  exact ⟨m, h, s, hs.trans (idealPowerTriangleSystem_map_hom₁ P I h),
    hs'.trans (idealPowerTriangleSystem_map_hom₁ M I h)⟩

/-- For a bounded complex of finite modules over a Noetherian ring, the inverse system of maps
`Iⁿ ⊗ᴸ M → Iⁿ M` formed from any derived tensor product bundle is an isomorphism of pro-objects
in the derived category. The displayed identities are the two-sided inverse identities after
cofinal refinement.

This is the form general in the bundle; the canonical derived tensor product is substituted in
`derivedTensor_idealPowers_proIsomorphic`. -/
public theorem derivedTensor_idealPowers_proIsomorphic_of_data
    [IsNoetherianRing A] (D : DerivedTensorData.DerivedTensorProduct A)
    (symmetry : D.tensor ≅ D.tensor.flip)
    (I : Ideal A) (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i → IsZero (M.X i))
    (hfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    ∃ (t : ∀ n, idealPowerComplex M I (n + 1) ⟶ idealPowerComplex M I n)
      (_ht : ∀ n, t n ≫ image.ι (idealPowerMultiplication M I n) =
        image.ι (idealPowerMultiplication M I (n + 1)))
      (α : derivedTensorIdealSystem D symmetry M I ⟶ idealPowerSystem M I t),
      (∀ n, α.app (op n) = derivedToIdealPowerMap D symmetry M I n) ∧
      ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
        (s : (idealPowerSystem M I t).obj (op m) ⟶
          (derivedTensorIdealSystem D symmetry M I).obj (op n)),
        α.app (op m) ≫ s = (derivedTensorIdealSystem D symmetry M I).map (homOfLE h).op ∧
          s ≫ α.app (op n) = (idealPowerSystem M I t).map (homOfLE h).op := by
  obtain ⟨P, p, hPbounded, hPfinite, hp, _, hpred⟩ :=
    Stacks.AdicSystem.DerivedReductionProIso.derivedReduction_proIsomorphic_adicReduction I M
      (strictlyBounded_of_isZero_outside M hbounded) hfinite
  obtain ⟨b, hb⟩ := hPbounded
  let := hb
  let := hp
  have (i : ℤ) : Module.Free A (P.X i) := (hPfinite i).2
  have (i : ℤ) : Projective (P.X i) := inferInstance
  have (i : ℤ) : Module.Flat A (P.X i) := inferInstance
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  let α := derivedToIdealPowerNatTrans D symmetry M I
  let β := derivedToIdealPowerNatTrans D symmetry P I
  let e := derivedTensorIdealSystemMap D symmetry p I
  refine ⟨idealPowerComplexTransition M I, idealPowerComplexTransition_comp M I,
    α, fun _ => rfl, ?_⟩
  apply proInverse_leftCancel e α
  · apply proInverse_of_isIso_app
    intro n
    change IsIso ((D.tensor.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (idealPowerModule I n))).map (DerivedCategory.Q.map p))
    infer_instance
  · change ∀ n : ℕ, ∃ (m : ℕ) (h : n ≤ m)
        (s : (idealPowerSystem M I (idealPowerComplexTransition M I)).obj (op m) ⟶
          (derivedTensorIdealSystem D symmetry P I).obj (op n)),
      (derivedTensorIdealSystemMap D symmetry p I ≫
        derivedToIdealPowerNatTrans D symmetry M I).app (op m) ≫ s =
          (derivedTensorIdealSystem D symmetry P I).map (homOfLE h).op ∧
      s ≫ (derivedTensorIdealSystemMap D symmetry p I ≫
        derivedToIdealPowerNatTrans D symmetry M I).app (op n) =
          (idealPowerSystem M I (idealPowerComplexTransition M I)).map (homOfLE h).op
    rw [derivedToIdealPowerNatTrans_naturality]
    apply proInverse_comp β (idealPowerSystemMap p I)
    · apply proInverse_of_isIso_app
      intro n
      exact isIso_derivedToIdealPowerMap D symmetry P I n
    · exact proInverse_idealPowerSystemMap_of_reduction p I hpred


end Stacks.AdicSystem.IdealPowerTensorComparison

end

/-! ## Tag 0928 -/

noncomputable section

namespace Stacks.AdicSystem.IdealPowerDerivedTensor

open CategoryTheory CategoryTheory.Limits Opposite

universe v

attribute [local instance] HasDerivedCategory.standard

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- For a finite module over a Noetherian ring, the inclusion of some positive ideal power
factors through the canonical map from the derived tensor product with the ideal, formed from any
derived tensor product bundle. The index `n` represents the positive exponent `n + 1`.

This is the form general in the bundle; the canonical derived tensor product is substituted in
`idealPowerInclusion_factors_through_derivedTensor`. -/
public theorem idealPowerInclusion_factors_through_derivedTensor_of_data
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (D : DerivedTensorData.DerivedTensorProduct A) (symmetry : D.tensor ≅ D.tensor.flip)
    (I : Ideal A) (M : ModuleCat.{v} A) [Module.Finite A M] :
    letI := Module.Finite.small.{u} A M
    let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
      (ModuleCat.of A (Shrink.{u} M))
    ∃ n : ℕ,
      ∃ f : DerivedCategory.Q.obj (Stacks.AdicSystem.IdealPowerTensorComparison.idealPowerComplex K
        I n) ⟶
          (Stacks.AdicSystem.IdealPowerTensorComparison.derivedTensorIdealSystem D symmetry K I).obj
            (op 0),
        f ≫
            (Stacks.AdicSystem.IdealPowerTensorComparison.derivedToIdealPowerMap D symmetry K I 0 ≫
              DerivedCategory.Q.map
                (image.ι (Stacks.AdicSystem.IdealPowerTensorComparison.idealPowerMultiplication K I
                  0))) =
          DerivedCategory.Q.map
            (image.ι (Stacks.AdicSystem.IdealPowerTensorComparison.idealPowerMultiplication K I n))
              := by
  let := Module.Finite.small.{u} A M
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj
    (ModuleCat.of A (Shrink.{u} M))
  have hbounded : ∃ a b : ℤ, a ≤ b ∧
      ∀ i : ℤ, i < a ∨ b < i → IsZero (K.X i) := by
    refine ⟨0, 0, le_refl _, fun i hi => ?_⟩
    exact HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)
  have hfinite : ∀ i : ℤ, Module.Finite A (K.X i) := by
    intro i
    by_cases hi : i = 0
    · subst i
      change Module.Finite A (Shrink.{u} M)
      infer_instance
    · let : Subsingleton (K.X i) := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0
          (ModuleCat.of A (Shrink.{u} M)) i hi)
      infer_instance
  obtain ⟨t, ht, α, hα, hinv⟩ :=
    Stacks.AdicSystem.IdealPowerTensorComparison.derivedTensor_idealPowers_proIsomorphic_of_data D
      symmetry
      I K hbounded hfinite
  obtain ⟨n, hn, f, _, hf⟩ := hinv 0
  let ι : Stacks.AdicSystem.IdealPowerTensorComparison.idealPowerSystem K I t ⟶
      (Functor.const ℕᵒᵖ).obj (DerivedCategory.Q.obj K) :=
    NatTrans.ofOpSequence
      (fun n => DerivedCategory.Q.map
        (image.ι (Stacks.AdicSystem.IdealPowerTensorComparison.idealPowerMultiplication K I n))) (by
      intro n
      simp only [Stacks.AdicSystem.IdealPowerTensorComparison.idealPowerSystem,
        Functor.ofOpSequence_map_homOfLE_succ,
        Functor.const_obj_map, Functor.const_obj_obj, Category.comp_id,
        ← DerivedCategory.Q.map_comp, ht])
  refine ⟨n, f, ?_⟩
  change f ≫ (Stacks.AdicSystem.IdealPowerTensorComparison.derivedToIdealPowerMap D symmetry K I 0 ≫
    _) = _
  rw [← hα 0, ← Category.assoc, hf]
  simpa only [Functor.const_obj_map, Functor.const_obj_obj, Category.comp_id,
    ι, NatTrans.ofOpSequence_app] using ι.naturality (homOfLE hn).op

end Stacks.AdicSystem.IdealPowerDerivedTensor

end

end
