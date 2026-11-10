module

public import StacksFrontier.Deformation.ToposThickening.FlatRepresentative
import StacksCore.Tactic.StacksAttribute

/-!
# Existence and comparison of the flat lifts computing the curvature class

Let `f : O ⟶ O₀` be a locally surjective morphism of sheaves of commutative rings on a site.
Tag 0DIU attaches to a bounded above complex `K₀` of `O₀`-modules a canonical map
`ω(K₀) : K₀ ⟶ (K₀ ⊗^L_{O₀} I)[2]`, built from a bounded above flat lift of `K₀` across `f`.
`StacksFrontier.Deformation.ToposThickening.CurvatureClass` constructs that map from a lift and
proves it natural along a morphism of lifts; this file supplies the three existence and
comparison statements the construction needs in order to be about `K₀` alone:

* a flat lift exists for every complex whose cohomology vanishes in high degrees, hence for
  every object of `D⁻(O₀)`;
* a map `K₀ ⟶ L₀` of complexes is covered by a morphism of flat lifts out of any prescribed
  lift of `K₀`;
* any two flat lifts of one complex both map to a third one over the identity.

Each is Stacks 0DIT (`Stacks.SheafOfModules.ComplexLifting.exists_liftedComplex`) applied to a
different prescribed graded family: the zero family, the first lift, and the direct sum of the
two lifts. They are the first, second and third paragraphs of the proof of Tag 0DIU.

## Main definitions

* `Deformation.ComplexLift.zeroGraded`, `Deformation.ComplexLift.zeroBaseChange`: the empty
  input to Stacks 0DIT.
* `Deformation.ComplexLift.baseChangePostcomp`: a base-change datum read against a new target
  complex.
* `Deformation.ComplexLift.FlatLiftHom.ofHom`: a morphism of flat lifts assembled from a map
  of the lifted graded families; the map of reductions is produced by the universal property
  of extension of scalars, not chosen.
* `Deformation.ComplexLift.pairGraded`, `Deformation.ComplexLift.pairReduction`,
  `Deformation.ComplexLift.pairBaseChange`: the direct sum of two flat lifts of one complex,
  as an input to Stacks 0DIT.

## Main results

* `Deformation.ComplexLift.exists_flatLift`: **Tag 0DIU**, a bounded above flat lift exists.
* `Deformation.ComplexLift.exists_flatLift_of_isLE`,
  `Deformation.ComplexLift.exists_flatLift_of_minus`: **Tag 0DIU**, the same for an object of
  the derived category with bounded above cohomology.
* `Deformation.ComplexLift.exists_flatLiftHom`: **Tag 0DIU**, a map of complexes lifts to a
  morphism of flat lifts.
* `Deformation.ComplexLift.exists_flatLiftHom_pair`: **Tag 0DIU**, two flat lifts of one
  complex map to a common flat lift.
* `Deformation.ComplexLift.obstructionMap_eq_of_common_lift`,
  `Deformation.ComplexLift.obstructionMap_eq_of_coherentKernels`: **Tag 0DIU**, `ω(K₀)` does
  not depend on the flat lift used to compute it.

## Implementation notes

The module universe is `max u v w` throughout: Stacks 0DIT builds its flat covers from sums of
extensions by zero indexed by the objects and sections of the sheaf being covered, so its
ambient module universe is the maximum of the site and ring universes and the module universe
one starts from, while the tensor product of sheaves of modules used by the curvature class
needs the module and ring universes to agree. Taking `max u v w` for both satisfies the two
constraints at once; the site universes stay independent.

The direct sum of two lifts is formed with the coproduct `pairObj` of
`StacksFrontier.CategoryTheory.Sites.Modules.FlatResolution.BaseChange`, whose flatness and
compatibility with extension of scalars are already available there. The summands, their
inclusions and the morphisms out of them are given names (`inlG`, `descG`, `inlR`, `descR`)
typed by `(pairGraded L L').X n` and `(pairReduction L L').X n` rather than by the underlying
coproduct: every rewrite in this file then matches syntactically, with no unfolding of a
coproduct during elaboration.

The kernel identification `Deformation.ComplexLift.IdealKernel` is data in the interface of
`CurvatureClass`, and its compatibility with a morphism of lifts is the hypothesis `hemb` of
the naturality results there. Accordingly `obstructionMap_eq_of_coherentKernels` takes that
compatibility as a hypothesis — it is the statement that the chosen identifications are the
canonical ones — and supplies the comparison of lifts that the independence argument needs.

## References

* [Stacks Project, Tag 0DIU](https://stacks.math.columbia.edu/tag/0DIU)
* [Stacks Project, Tag 0DIT](https://stacks.math.columbia.edu/tag/0DIT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
open Stacks.Sheaves.ChangeOfRings (ringSheafMap)
open Stacks.SheafOfModules.ComplexLifting (GradedDifferential BaseChangeTo
  IsExtensionOfScalars LiftedComplex pairObj pairInl pairInr pairDesc pairInl_desc
  pairInr_desc pair_hom_ext pair_isFlat)

universe v u w d

namespace Deformation.ComplexLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  {O O₀ : Sheaf J CommRingCat.{max u v w}} {f : O ⟶ O₀}

section Zero

/-- The zero graded family of `O`-modules: the input to Stacks 0DIT that prescribes nothing. -/
def zeroGraded : GradedDifferential (SheafMod O) where
  X _ := 0
  d _ := 0

/-- The zero complex of `O₀`-modules, the reduction of `zeroGraded`. -/
def zeroComplex : CochainComplex (SheafMod O₀) ℤ :=
  CochainComplex.of (fun _ => (0 : SheafMod O₀)) (fun _ => 0) (by simp)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify J AddCommGrpCat.{max u v w}] in
/-- The zero module is the extension of scalars of the zero module. -/
lemma isExtensionOfScalars_zero :
    IsExtensionOfScalars f (0 : SheafMod O) (0 : SheafMod O₀) 0 := by
  intro N
  constructor
  · intro a b _
    exact (isZero_zero (SheafMod O₀)).eq_of_src a b
  · intro k
    exact ⟨0, (isZero_zero (SheafMod O)).eq_of_src _ _⟩

/-- The zero graded family reduces to the zero complex, mapping to any complex by zero. -/
def zeroBaseChange (K₀ : CochainComplex (SheafMod O₀) ℤ) :
    BaseChangeTo f (zeroGraded (O := O)) K₀ (fun _ => 0) where
  complex := zeroComplex
  unit _ := 0
  isExtension _ := isExtensionOfScalars_zero
  differential _ := by simp
  map := 0
  map_unit _ := by simp

/-- **Stacks 0DIU, existence of a flat lift.** A complex of `O₀`-modules whose cohomology
vanishes in sufficiently high degrees admits a bounded above flat lift across a locally
surjective `f : O ⟶ O₀`. -/
@[stacks 0DIU "variant: existence of a flat lift of a bounded above complex, a step of the proof;
the tag is Deformation.ComplexLift.tensorOmegaMinus"]
theorem exists_flatLift (hf : Sheaf.IsLocallySurjective f)
    (K₀ : CochainComplex (SheafMod O₀) ℤ)
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n)) :
    Nonempty (FlatLift f K₀) := by
  obtain ⟨T⟩ := Stacks.SheafOfModules.ComplexLifting.exists_liftedComplex f hf
    (zeroGraded (O := O)) K₀ (fun _ => 0)
    (fun _ => flatModules_of_isZero O _ (isZero_zero _))
    ⟨0, fun _ _ => isZero_zero _⟩ hK (zeroBaseChange K₀)
  exact ⟨FlatLift.ofLiftedComplex T⟩

end Zero

section Comparison

variable {K₀ L₀ : CochainComplex (SheafMod O₀) ℤ}

/-- Composing the target of a base-change datum with a map of complexes. -/
def baseChangePostcomp {G : GradedDifferential (SheafMod O)}
    {g : ∀ n, G.X n ⟶ (restrict f).obj (K₀.X n)}
    (B : BaseChangeTo f G K₀ g) (φ : K₀ ⟶ L₀) :
    BaseChangeTo f G L₀ (fun n => g n ≫ (restrict f).map (φ.f n)) where
  complex := B.complex
  unit := B.unit
  isExtension := B.isExtension
  differential := B.differential
  map := B.map ≫ φ
  map_unit n := by
    rw [HomologicalComplex.comp_f, Functor.map_comp, ← Category.assoc, B.map_unit]

/-- A map of the lifted graded families compatible with the maps in consecutive degrees and
with the maps to the targets is a morphism of flat lifts: the map of reductions is obtained
from the universal property of extension of scalars, not chosen. -/
def FlatLiftHom.ofHom (L : FlatLift f K₀) (M : FlatLift f L₀) (φ : K₀ ⟶ L₀)
    (hom : ∀ n, L.F.X n ⟶ M.F.X n)
    (hom_d : ∀ n, L.F.d n ≫ hom (n + 1) = hom n ≫ M.F.d n)
    (hcompat : ∀ n, hom n ≫ M.toTarget n = L.toTarget n ≫ (restrict f).map (φ.f n)) :
    FlatLiftHom L M φ where
  hom := hom
  hom_d := hom_d
  red :=
    { f := fun n => IsExtensionOfScalars.desc f (L.baseChange.isExtension n)
        (hom n ≫ M.baseChange.unit n)
      comm' := by
        intro i j hij
        obtain rfl : j = i + 1 := by simpa using hij.symm
        refine (L.baseChange.isExtension i _).injective ?_
        calc L.baseChange.unit i ≫ (restrict f).map
                (IsExtensionOfScalars.desc f (L.baseChange.isExtension i)
                  (hom i ≫ M.baseChange.unit i) ≫ M.baseChange.complex.d i (i + 1))
            = (hom i ≫ M.baseChange.unit i) ≫
                (restrict f).map (M.baseChange.complex.d i (i + 1)) := by
              rw [Functor.map_comp, ← Category.assoc, IsExtensionOfScalars.desc_spec]
          _ = (hom i ≫ M.F.d i) ≫ M.baseChange.unit (i + 1) := by
              rw [Category.assoc, ← M.baseChange.differential i, ← Category.assoc]
          _ = L.F.d i ≫ hom (i + 1) ≫ M.baseChange.unit (i + 1) := by
              rw [← hom_d i, Category.assoc]
          _ = L.baseChange.unit i ≫ (restrict f).map
                (L.baseChange.complex.d i (i + 1) ≫
                  IsExtensionOfScalars.desc f (L.baseChange.isExtension (i + 1))
                    (hom (i + 1) ≫ M.baseChange.unit (i + 1))) := by
              conv_rhs =>
                rw [Functor.map_comp, ← Category.assoc, ← L.baseChange.differential i,
                  Category.assoc, IsExtensionOfScalars.desc_spec] }
  unit_red n := (IsExtensionOfScalars.desc_spec f (L.baseChange.isExtension n) _).symm
  red_map := by
    refine HomologicalComplex.hom_ext _ _ fun n => ?_
    refine (L.baseChange.isExtension n _).injective ?_
    calc L.baseChange.unit n ≫ (restrict f).map
            (IsExtensionOfScalars.desc f (L.baseChange.isExtension n)
              (hom n ≫ M.baseChange.unit n) ≫ M.baseChange.map.f n)
        = hom n ≫ M.baseChange.unit n ≫ (restrict f).map (M.baseChange.map.f n) := by
          rw [Functor.map_comp, ← Category.assoc, IsExtensionOfScalars.desc_spec,
            Category.assoc]
      _ = L.toTarget n ≫ (restrict f).map (φ.f n) := by
          rw [M.baseChange.map_unit n, hcompat n]
      _ = L.baseChange.unit n ≫ (restrict f).map
            ((L.baseChange.map ≫ φ).f n) := by
          conv_rhs =>
            rw [HomologicalComplex.comp_f, Functor.map_comp, ← Category.assoc,
              L.baseChange.map_unit n]

/-- **Stacks 0DIU, lifting a map of complexes.** A map `φ : K₀ ⟶ L₀` of complexes of
`O₀`-modules, with the cohomology of `L₀` vanishing in sufficiently high degrees, is covered by
a morphism of flat lifts out of any given bounded above flat lift of `K₀`. -/
@[stacks 0DIU "variant: lifting a map of complexes to the flat lifts, a step of the proof; the tag
is Deformation.ComplexLift.tensorOmegaMinus_natural"]
theorem exists_flatLiftHom (hf : Sheaf.IsLocallySurjective f)
    (L : FlatLift f K₀) (φ : K₀ ⟶ L₀)
    (hL₀ : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (L₀.homology n)) :
    ∃ M : FlatLift f L₀, Nonempty (FlatLiftHom L M φ) := by
  obtain ⟨T⟩ := Stacks.SheafOfModules.ComplexLifting.exists_liftedComplex f hf
    L.F L₀ (fun n => L.toTarget n ≫ (restrict f).map (φ.f n)) L.flat L.boundedAbove hL₀
    (baseChangePostcomp L.baseChange φ)
  exact ⟨FlatLift.ofLiftedComplex T,
    ⟨FlatLiftHom.ofHom L _ φ T.fromG T.fromG_d T.fromG_toTarget⟩⟩

end Comparison

section Pair

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- A direct sum of two zero sheaves of modules is zero. -/
lemma isZero_pairObj {M N : SheafMod O} (hM : IsZero M) (hN : IsZero N) :
    IsZero (pairObj M N) := by
  rw [IsZero.iff_id_eq_zero]
  refine pair_hom_ext ?_ ?_
  · rw [Category.comp_id, comp_zero]; exact hM.eq_of_src _ _
  · rw [Category.comp_id, comp_zero]; exact hN.eq_of_src _ _

variable {K₀ : CochainComplex (SheafMod O₀) ℤ} (L L' : FlatLift f K₀)

/-- The direct sum of the lifted graded families of two flat lifts of the same complex. -/
def pairGraded : GradedDifferential (SheafMod O) where
  X n := pairObj (L.F.X n) (L'.F.X n)
  d n := pairDesc (L.F.d n ≫ pairInl (L.F.X (n + 1)) (L'.F.X (n + 1)))
    (L'.F.d n ≫ pairInr (L.F.X (n + 1)) (L'.F.X (n + 1)))

/-- The inclusion of the first lifted family into the direct sum. -/
def inlG (n : ℤ) : L.F.X n ⟶ (pairGraded L L').X n := pairInl _ _

/-- The inclusion of the second lifted family into the direct sum. -/
def inrG (n : ℤ) : L'.F.X n ⟶ (pairGraded L L').X n := pairInr _ _

/-- A morphism out of the direct sum of the lifted families. -/
def descG {P : SheafMod O} {n : ℤ} (a : L.F.X n ⟶ P) (b : L'.F.X n ⟶ P) :
    (pairGraded L L').X n ⟶ P := pairDesc a b

/-- The first inclusion followed by `descG L L' a b` is `a`. -/
@[simp]
lemma inlG_descG {P : SheafMod O} {n : ℤ} (a : L.F.X n ⟶ P) (b : L'.F.X n ⟶ P) :
    inlG L L' n ≫ descG L L' a b = a := pairInl_desc a b

/-- The second inclusion followed by `descG L L' a b` is `b`. -/
@[simp]
lemma inrG_descG {P : SheafMod O} {n : ℤ} (a : L.F.X n ⟶ P) (b : L'.F.X n ⟶ P) :
    inrG L L' n ≫ descG L L' a b = b := pairInr_desc a b

/-- Two morphisms out of a term of `pairGraded L L'` agreeing on both inclusions are equal. -/
lemma pairGraded_hom_ext {P : SheafMod O} {n : ℤ} {x y : (pairGraded L L').X n ⟶ P}
    (h₁ : inlG L L' n ≫ x = inlG L L' n ≫ y) (h₂ : inrG L L' n ≫ x = inrG L L' n ≫ y) :
    x = y := pair_hom_ext h₁ h₂

/-- The differential of `pairGraded L L'` restricted to the first family is the differential
of `L.F` followed by the first inclusion. -/
@[simp]
lemma inlG_comp_pairGraded_d (n : ℤ) :
    inlG L L' n ≫ (pairGraded L L').d n = L.F.d n ≫ inlG L L' (n + 1) := pairInl_desc _ _

/-- The differential of `pairGraded L L'` restricted to the second family is the differential
of `L'.F` followed by the second inclusion. -/
@[simp]
lemma inrG_comp_pairGraded_d (n : ℤ) :
    inrG L L' n ≫ (pairGraded L L').d n = L'.F.d n ≫ inrG L L' (n + 1) := pairInr_desc _ _

/-- The direct sum of the reductions of two flat lifts of the same complex. -/
def pairReduction : CochainComplex (SheafMod O₀) ℤ where
  X n := pairObj (L.baseChange.complex.X n) (L'.baseChange.complex.X n)
  d i j := if i + 1 = j then
      pairDesc
        (L.baseChange.complex.d i j ≫
          pairInl (L.baseChange.complex.X j) (L'.baseChange.complex.X j))
        (L'.baseChange.complex.d i j ≫
          pairInr (L.baseChange.complex.X j) (L'.baseChange.complex.X j))
    else 0
  shape _ _ h := ite_eq_right h
  d_comp_d' i j k hij hjk := by
    have hij' : i + 1 = j := hij
    have hjk' : j + 1 = k := hjk
    rw [ite_eq_left hij', ite_eq_left hjk']
    refine pair_hom_ext ?_ ?_
    · rw [comp_zero, ← Category.assoc, pairInl_desc, Category.assoc, pairInl_desc,
        ← Category.assoc, HomologicalComplex.d_comp_d, zero_comp]
    · rw [comp_zero, ← Category.assoc, pairInr_desc, Category.assoc, pairInr_desc,
        ← Category.assoc, HomologicalComplex.d_comp_d, zero_comp]

/-- The inclusion of the first reduction into the direct sum. -/
def inlR (n : ℤ) : L.baseChange.complex.X n ⟶ (pairReduction L L').X n := pairInl _ _

/-- The inclusion of the second reduction into the direct sum. -/
def inrR (n : ℤ) : L'.baseChange.complex.X n ⟶ (pairReduction L L').X n := pairInr _ _

/-- A morphism out of the direct sum of the reductions. -/
def descR {P : SheafMod O₀} {n : ℤ} (a : L.baseChange.complex.X n ⟶ P)
    (b : L'.baseChange.complex.X n ⟶ P) : (pairReduction L L').X n ⟶ P := pairDesc a b

/-- The first inclusion followed by `descR L L' a b` is `a`. -/
@[simp]
lemma inlR_descR {P : SheafMod O₀} {n : ℤ} (a : L.baseChange.complex.X n ⟶ P)
    (b : L'.baseChange.complex.X n ⟶ P) : inlR L L' n ≫ descR L L' a b = a := pairInl_desc a b

/-- The second inclusion followed by `descR L L' a b` is `b`. -/
@[simp]
lemma inrR_descR {P : SheafMod O₀} {n : ℤ} (a : L.baseChange.complex.X n ⟶ P)
    (b : L'.baseChange.complex.X n ⟶ P) : inrR L L' n ≫ descR L L' a b = b := pairInr_desc a b

/-- Two morphisms out of a term of `pairReduction L L'` agreeing on both inclusions are
equal. -/
lemma pairReduction_hom_ext {P : SheafMod O₀} {n : ℤ} {x y : (pairReduction L L').X n ⟶ P}
    (h₁ : inlR L L' n ≫ x = inlR L L' n ≫ y) (h₂ : inrR L L' n ≫ x = inrR L L' n ≫ y) :
    x = y := pair_hom_ext h₁ h₂

/-- The differential of `pairReduction L L'` from degree `n` to `n + 1` is the sum of the
differentials of the two reductions. -/
lemma pairReduction_d (n : ℤ) :
    (pairReduction L L').d n (n + 1) =
      descR L L' (L.baseChange.complex.d n (n + 1) ≫ inlR L L' (n + 1))
        (L'.baseChange.complex.d n (n + 1) ≫ inrR L L' (n + 1)) :=
  ite_eq_left rfl

/-- The differential of `pairReduction L L'` restricted to the first reduction is the
differential of `L.baseChange.complex` followed by the first inclusion. -/
@[simp]
lemma inlR_comp_pairReduction_d (n : ℤ) :
    inlR L L' n ≫ (pairReduction L L').d n (n + 1) =
      L.baseChange.complex.d n (n + 1) ≫ inlR L L' (n + 1) := by
  rw [pairReduction_d, inlR_descR]

/-- The differential of `pairReduction L L'` restricted to the second reduction is the
differential of `L'.baseChange.complex` followed by the second inclusion. -/
@[simp]
lemma inrR_comp_pairReduction_d (n : ℤ) :
    inrR L L' n ≫ (pairReduction L L').d n (n + 1) =
      L'.baseChange.complex.d n (n + 1) ≫ inrR L L' (n + 1) := by
  rw [pairReduction_d, inrR_descR]

/-- The reduction map of the direct sum of two flat lifts. -/
def pairUnit (n : ℤ) :
    (pairGraded L L').X n ⟶ (restrict f).obj ((pairReduction L L').X n) :=
  descG L L' (L.baseChange.unit n ≫ (restrict f).map (inlR L L' n))
    (L'.baseChange.unit n ≫ (restrict f).map (inrR L L' n))

/-- On the first lifted family, `pairUnit L L'` is the reduction map of `L` followed by the
first inclusion. -/
@[simp]
lemma inlG_comp_pairUnit (n : ℤ) :
    inlG L L' n ≫ pairUnit L L' n =
      L.baseChange.unit n ≫ (restrict f).map (inlR L L' n) := inlG_descG L L' _ _

/-- On the second lifted family, `pairUnit L L'` is the reduction map of `L'` followed by the
second inclusion. -/
@[simp]
lemma inrG_comp_pairUnit (n : ℤ) :
    inrG L L' n ≫ pairUnit L L' n =
      L'.baseChange.unit n ≫ (restrict f).map (inrR L L' n) := inrG_descG L L' _ _

/-- The direct sum of two flat lifts of the same complex, as data for Stacks 0DIT: a bounded
above flat graded family whose reduction maps to the complex by the two reductions. -/
def pairBaseChange :
    BaseChangeTo f (pairGraded L L') K₀
      (fun n => descG L L' (L.toTarget n) (L'.toTarget n)) where
  complex := pairReduction L L'
  unit := pairUnit L L'
  isExtension n :=
    IsExtensionOfScalars.pair f (L.baseChange.isExtension n) (L'.baseChange.isExtension n)
  differential n := by
    refine pairGraded_hom_ext L L' ?_ ?_
    · conv_rhs =>
        rw [← Category.assoc, inlG_comp_pairUnit, Category.assoc, ← Functor.map_comp,
          inlR_comp_pairReduction_d, Functor.map_comp, ← Category.assoc,
          ← L.baseChange.differential n]
      rw [← Category.assoc, inlG_comp_pairGraded_d, Category.assoc, inlG_comp_pairUnit,
        ← Category.assoc]
    · conv_rhs =>
        rw [← Category.assoc, inrG_comp_pairUnit, Category.assoc, ← Functor.map_comp,
          inrR_comp_pairReduction_d, Functor.map_comp, ← Category.assoc,
          ← L'.baseChange.differential n]
      rw [← Category.assoc, inrG_comp_pairGraded_d, Category.assoc, inrG_comp_pairUnit,
        ← Category.assoc]
  map :=
    { f := fun n => descR L L' (L.baseChange.map.f n) (L'.baseChange.map.f n)
      comm' := by
        intro i j hij
        obtain rfl : j = i + 1 := by simpa using hij.symm
        refine pairReduction_hom_ext L L' ?_ ?_
        · rw [← Category.assoc, inlR_descR, ← Category.assoc, inlR_comp_pairReduction_d,
            Category.assoc, inlR_descR]
          exact L.baseChange.map.comm i (i + 1)
        · rw [← Category.assoc, inrR_descR, ← Category.assoc, inrR_comp_pairReduction_d,
            Category.assoc, inrR_descR]
          exact L'.baseChange.map.comm i (i + 1) }
  map_unit n := by
    refine pairGraded_hom_ext L L' ?_ ?_
    · rw [← Category.assoc, inlG_comp_pairUnit, Category.assoc, ← Functor.map_comp,
        inlR_descR, L.baseChange.map_unit n, inlG_descG]
    · rw [← Category.assoc, inrG_comp_pairUnit, Category.assoc, ← Functor.map_comp,
        inrR_descR, L'.baseChange.map_unit n, inrG_descG]

/-- The direct sum of two bounded above flat lifts is bounded above. -/
lemma pairGraded_boundedAbove :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero ((pairGraded L L').X n) := by
  obtain ⟨N, hN⟩ := L.boundedAbove
  obtain ⟨N', hN'⟩ := L'.boundedAbove
  exact ⟨max N N', fun n hn => isZero_pairObj (hN n ((le_max_left N N').trans hn))
    (hN' n ((le_max_right N N').trans hn))⟩

/-- **Stacks 0DIU, a common enlargement of two flat lifts.** Two bounded above flat lifts of
the same complex both map to a third one, over the identity. This is the comparison that the
well-definedness of the canonical class rests on; it is Stacks 0DIT applied to the direct sum
of the two lifted families. -/
@[stacks 0DIU "variant: two flat lifts of a complex map to a common flat lift, a step of the proof;
the tag is Deformation.ComplexLift.tensorOmegaMinus"]
theorem exists_flatLiftHom_pair (hf : Sheaf.IsLocallySurjective f)
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n)) :
    ∃ M : FlatLift f K₀,
      Nonempty (FlatLiftHom L M (𝟙 K₀)) ∧ Nonempty (FlatLiftHom L' M (𝟙 K₀)) := by
  obtain ⟨T⟩ := Stacks.SheafOfModules.ComplexLifting.exists_liftedComplex f hf
    (pairGraded L L') K₀ (fun n => descG L L' (L.toTarget n) (L'.toTarget n))
    (fun n => pair_isFlat (L.flat n) (L'.flat n)) (pairGraded_boundedAbove L L') hK
    (pairBaseChange L L')
  refine ⟨FlatLift.ofLiftedComplex T,
    ⟨FlatLiftHom.ofHom L _ (𝟙 K₀) (fun n => inlG L L' n ≫ T.fromG n) ?_ ?_⟩,
    ⟨FlatLiftHom.ofHom L' _ (𝟙 K₀) (fun n => inrG L L' n ≫ T.fromG n) ?_ ?_⟩⟩
  · intro n
    change L.F.d n ≫ inlG L L' (n + 1) ≫ T.fromG (n + 1) = (inlG L L' n ≫ T.fromG n) ≫ T.F.d n
    rw [← Category.assoc, ← inlG_comp_pairGraded_d, Category.assoc, T.fromG_d,
      ← Category.assoc]
  · intro n
    change (inlG L L' n ≫ T.fromG n) ≫ T.toTarget n =
      L.toTarget n ≫ (restrict f).map (𝟙 (K₀.X n))
    rw [Category.assoc, T.fromG_toTarget n, inlG_descG, CategoryTheory.Functor.map_id,
      Category.comp_id]
  · intro n
    change L'.F.d n ≫ inrG L L' (n + 1) ≫ T.fromG (n + 1) = (inrG L L' n ≫ T.fromG n) ≫ T.F.d n
    rw [← Category.assoc, ← inrG_comp_pairGraded_d, Category.assoc, T.fromG_d,
      ← Category.assoc]
  · intro n
    change (inrG L L' n ≫ T.fromG n) ≫ T.toTarget n =
      L'.toTarget n ≫ (restrict f).map (𝟙 (K₀.X n))
    rw [Category.assoc, T.fromG_toTarget n, inrG_descG, CategoryTheory.Functor.map_id,
      Category.comp_id]

end Pair

section Derived

omit [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})] in
/-- A complex vanishing in degrees above `b` has vanishing cohomology above `b`. -/
lemma homology_boundedAbove (M : CochainComplex (SheafMod O₀) ℤ) (b : ℤ) [M.IsStrictlyLE b] :
    ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (M.homology n) :=
  ⟨b + 1, fun n hn => (HomologicalComplex.ExactAt.of_isZero
    (M.isZero_of_isStrictlyLE b n (by omega))).isZero_homology⟩

variable [HasDerivedCategory.{d} (SheafMod O₀)]

/-- **Stacks 0DIU, a flat lift for an object of the derived category.** An object of `D(O₀)`
with no cohomology above `b` is represented by a complex of `O₀`-modules carrying a bounded
above flat lift across a locally surjective `f : O ⟶ O₀`. -/
@[stacks 0DIU "variant: a flat lift of a derived object with bounded above cohomology, a step of
the proof; the tag is Deformation.ComplexLift.tensorOmegaMinus"]
theorem exists_flatLift_of_isLE (hf : Sheaf.IsLocallySurjective f) (b : ℤ)
    (E : DerivedCategory (SheafMod O₀)) [E.IsLE b] :
    ∃ K₀ : CochainComplex (SheafMod O₀) ℤ,
      Nonempty (DerivedCategory.Q.obj K₀ ≅ E) ∧ Nonempty (FlatLift f K₀) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := E.exists_iso_Q_obj_of_isLE b
  have : M.IsStrictlyLE b := hM
  exact ⟨M, ⟨e.symm⟩, exists_flatLift hf M (homology_boundedAbove M b)⟩

/-- **Stacks 0DIU, a flat lift for a bounded above object.** Every object of `D⁻(O₀)` is
represented by a complex carrying a bounded above flat lift. -/
@[stacks 0DIU "variant: a flat lift of a bounded above derived object, a step of the proof; the tag
is Deformation.ComplexLift.tensorOmegaMinus"]
theorem exists_flatLift_of_minus (hf : Sheaf.IsLocallySurjective f)
    (E : DerivedCategory.Minus (SheafMod O₀)) :
    ∃ K₀ : CochainComplex (SheafMod O₀) ℤ,
      Nonempty (DerivedCategory.Q.obj K₀ ≅ E.obj) ∧ Nonempty (FlatLift f K₀) := by
  obtain ⟨b, hb⟩ := E.property
  have : E.obj.IsLE b := hb
  exact exists_flatLift_of_isLE hf b E.obj

end Derived

section Canonical

variable {I : SheafMod O₀} [(((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I)).Additive]
  [HasDerivedCategory.{d} (SheafMod O₀)] {S : SquareZeroIdeal f I}
  (D : DerivedIdealTensor I) {K₀ : CochainComplex (SheafMod O₀) ℤ}

/-- **Stacks 0DIU, independence of the flat lift.** Two flat lifts of the same complex that
both map to a third one, compatibly with the kernel identifications, give the same canonical
map `ω(K₀)`. -/
@[stacks 0DIU "variant: independence of ω of the flat lift through a common enlargement at a
supplied derived ideal tensor datum D; the tag is Deformation.ComplexLift.tensorOmegaMinus"]
theorem obstructionMap_eq_of_common_lift {L L' M : FlatLift f K₀}
    (h : FlatLiftHom L M (𝟙 K₀)) (h' : FlatLiftHom L' M (𝟙 K₀))
    (TL : IdealKernel S L) (TL' : IdealKernel S L') (TM : IdealKernel S M)
    (hemb : ∀ n : ℤ, (restrict f).map (((idealTensorFunctor O₀ I).map h.red).f n) ≫ TM.emb n =
      TL.emb n ≫ h.hom n)
    (hemb' : ∀ n : ℤ, (restrict f).map (((idealTensorFunctor O₀ I).map h'.red).f n) ≫ TM.emb n =
      TL'.emb n ≫ h'.hom n) :
    obstructionMap D TL = obstructionMap D TL' := by
  rw [obstructionMap_eq_of_hom D h TL TM hemb, obstructionMap_eq_of_hom D h' TL' TM hemb']

/-- **Stacks 0DIU, the canonical map does not depend on the flat lift.** Suppose every bounded
above flat lift of `K₀` carries a kernel identification, and that these are carried to one
another by every morphism of flat lifts over the identity -- which is the assertion that the
identifications are the canonical ones, normalized by the pure-tensor formula of
`Deformation.ComplexLift.IdealKernel.emb_tmul`. Then the map `ω(K₀)` computed from any two
flat lifts of `K₀` is the same, so `ω(K₀)` depends on `K₀` alone.

The common enlargement that forces the agreement is `exists_flatLiftHom_pair`, Stacks 0DIT
applied to the direct sum of the two lifted families. -/
@[stacks 0DIU "variant: ω depends only on the complex at a supplied derived ideal tensor datum D;
the tag is Deformation.ComplexLift.tensorOmegaMinus"]
theorem obstructionMap_eq_of_coherentKernels (hf : Sheaf.IsLocallySurjective f)
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    (kern : ∀ M : FlatLift f K₀, IdealKernel S M)
    (hcoh : ∀ {A B : FlatLift f K₀} (h : FlatLiftHom A B (𝟙 K₀)) (n : ℤ),
      (restrict f).map (((idealTensorFunctor O₀ I).map h.red).f n) ≫ (kern B).emb n =
        (kern A).emb n ≫ h.hom n)
    (L L' : FlatLift f K₀) :
    obstructionMap D (kern L) = obstructionMap D (kern L') := by
  obtain ⟨M, ⟨h⟩, ⟨h'⟩⟩ := exists_flatLiftHom_pair L L' hf hK
  exact obstructionMap_eq_of_common_lift D h h' (kern L) (kern L') (kern M)
    (fun n => hcoh h n) (fun n => hcoh h' n)

end Canonical

end Deformation.ComplexLift

end
