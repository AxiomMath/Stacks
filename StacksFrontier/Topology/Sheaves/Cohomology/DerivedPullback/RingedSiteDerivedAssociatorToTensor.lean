module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedAssociatorToTensor
import all StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedAssociatorToTensor

/-!
# The associativity constraint of `D(𝒪)` against the canonical map to the total tensor complex

Let `R` be a sheaf of commutative rings on a small site, and write
`t_{A,B} : QA ⊗^L QB ⟶ Q(Tot(A ⊗ B))` for the canonical map of Stacks 06YU from the derived
tensor product `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor R` to the total tensor
complex. For arbitrary complexes `A`, `B`, `D` of `R`-modules

`(t_{A,B} ▷ QD) ≫ t_{A ⊗ B, D} ≫ Q(α_{A,B,D}) = α_{QA,QB,QD} ≫ (QA ◁ t_{B,D}) ≫ t_{A, B ⊗ D}`,

where `α_{QA,QB,QD}` is the associativity constraint of
`Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedMonoidal` (Tag 0FPB), the one Tag 0FP4 is
stated with (`Stacks.Cohomology.DerivedRelativeCupProduct.derivedAssociator` is it, at the
structure sheaf of a ringed space).

As a consequence, a multiplication `m : K ⊗ K ⟶ K` on a complex which is associative on the
nose induces an associative multiplication `QK ⊗^L QK ⟶ Q(K ⊗ K) ⟶ QK` in the monoidal derived
category, `Stacks.SheafOfModules.DerivedMonoidal.derivedMul_assoc`.

## Main results

* `Stacks.SheafOfModules.DerivedMonoidal.canonicalAssociator_toTensor`: the identity above, for
  arbitrary complexes `A`, `B`, `D`.
* `Stacks.SheafOfModules.DerivedMonoidal.derivedMul_assoc`: the derived multiplication of an
  associative multiplication on a complex is associative.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe d u

namespace Stacks.SheafOfModules.DerivedMonoidal

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

attribute [local instance 10000] CochainComplex.symmetricCategory
  SheafOfModules.monoidalCategorySheafTensor

/-- The monoidal structure on `Complexes R`, as a top-priority local instance. -/
local instance (priority := 100000) monoidalCategoryStructComplexesAT :
    MonoidalCategoryStruct (Complexes R) := inferInstance

/-- **The canonical map of Stacks 06YU** from the derived tensor product to the total tensor
complex, at the `⊗` spelling of its target. -/
def toTensorHom (A B : Complexes R) :
    ((derivedTensorBifunctorOfSite R).obj (DerivedCategory.Q.obj A)).obj
        (DerivedCategory.Q.obj B) ⟶
      DerivedCategory.Q.obj ((A ⊗ B : Complexes R)) :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).toTensor A B

/-- On two K-flat complexes the canonical map is the K-flat comparison. -/
theorem toTensorHom_eq_canonicalComparisonHom (A B : Complexes R)
    (hA : Stacks.SheafOfModules.KFlat R A) (hB : Stacks.SheafOfModules.KFlat R B) :
    toTensorHom R A B = canonicalComparisonHom R A B hA hB := by
  rw [toTensorHom, canonicalComparisonHom,
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).toTensor_eq_comparisonRight
      A B hB,
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).comparisonRight_eq_comparison
      A B hA hB]
  rfl

/-- The canonical map is natural in both complexes. -/
theorem toTensorHom_naturality {A A' B B' : Complexes R} (f : A ⟶ A') (g : B ⟶ B') :
    canonicalWhiskerRight R (DerivedCategory.Q.map f) (DerivedCategory.Q.obj B) ≫
        canonicalWhiskerLeft R (DerivedCategory.Q.obj A') (DerivedCategory.Q.map g) ≫
        toTensorHom R A' B' =
      toTensorHom R A B ≫ DerivedCategory.Q.map (f ⊗ₘ g) :=
  (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct R).toTensor_naturality f g

/-- The associator of total tensor complexes, read in `D(Mod(O))`, is natural in all three
complexes. -/
theorem complexAssociatorHom_naturality {A A' B B' D D' : Complexes R}
    (a : A' ⟶ A) (b : B' ⟶ B) (d : D' ⟶ D) :
    DerivedCategory.Q.map ((a ⊗ₘ b) ⊗ₘ d) ≫ complexAssociatorHom R A B D =
      complexAssociatorHom R A' B' D' ≫ DerivedCategory.Q.map (a ⊗ₘ (b ⊗ₘ d)) := by
  rw [complexAssociatorHom, complexAssociatorHom, ← Functor.map_comp, ← Functor.map_comp,
    associator_naturality a b d]

/-- The associativity constraint of `canonicalDerivedMonoidal` is natural in all three variables,
in the bifunctor spelling of `canonicalAssociatorHom`. -/
theorem canonicalAssociatorHom_naturality' {A A' B B' D D' : DerivedModules R}
    (a : A' ⟶ A) (b : B' ⟶ B) (d : D' ⟶ D) :
    canonicalWhiskerRight R (canonicalWhiskerRight R a B' ≫ canonicalWhiskerLeft R A b) D' ≫
        canonicalWhiskerLeft R _ d ≫ canonicalAssociatorHom R A B D =
      canonicalAssociatorHom R A' B' D' ≫ canonicalWhiskerRight R a _ ≫
        canonicalWhiskerLeft R A (canonicalWhiskerRight R b D' ≫ canonicalWhiskerLeft R B d) := by
  let := canonicalDerivedMonoidal R
  have h := associator_naturality a b d
  rwa [tensorHom_def, tensorHom_def, tensorHom_def, tensorHom_def, Category.assoc] at h

/-- **The associativity constraint of `D(Mod(O))` against the canonical map to the total tensor
complex**: for arbitrary complexes `A`, `B`, `D` of `R`-modules,

`(t_{A,B} ▷ QD) ≫ t_{A ⊗ B, D} ≫ Q(α_{A,B,D}) = α_{QA,QB,QD} ≫ (QA ◁ t_{B,D}) ≫ t_{A, B ⊗ D}`. -/
theorem canonicalAssociator_toTensor (A B D : Complexes R) :
    canonicalWhiskerRight R (toTensorHom R A B) (DerivedCategory.Q.obj D) ≫
        toTensorHom R (A ⊗ B) D ≫ complexAssociatorHom R A B D =
      canonicalAssociatorHom R (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj B)
          (DerivedCategory.Q.obj D) ≫
        canonicalWhiskerLeft R (DerivedCategory.Q.obj A) (toTensorHom R B D) ≫
          toTensorHom R A (B ⊗ D) := by
  obtain ⟨A', a, hA', _⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso R A
  obtain ⟨B', b, hB', _⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso R B
  obtain ⟨D', d, hD', _⟩ := Stacks.DerivedTensor.RingedSite.exists_kFlat_quasiIso R D
  have hq := complexAssociatorHom_naturality R a b d
  have h' := canonicalComparison_associator R A' B' D' hA' hB' hD'
  unfold CanonicalComparisonAssociator at h'
  rw [← toTensorHom_eq_canonicalComparisonHom R A' B' hA' hB',
    ← toTensorHom_eq_canonicalComparisonHom R B' D' hB' hD',
    ← toTensorHom_eq_canonicalComparisonHom R (A' ⊗ B') D' (kFlat_tensor_complexes R hA' hB') hD',
    ← toTensorHom_eq_canonicalComparisonHom R A' (B' ⊗ D') hA' (kFlat_tensor_complexes R hB' hD')]
    at h'
  exact assoc_descent (derivedTensorBifunctorOfSite R) (DerivedCategory.Q.map a)
    (DerivedCategory.Q.map b) (DerivedCategory.Q.map d) (toTensorHom R A B) (toTensorHom R A' B')
    (DerivedCategory.Q.map (a ⊗ₘ b)) (toTensorHom_naturality R a b)
    (toTensorHom R B D) (toTensorHom R B' D')
    (DerivedCategory.Q.map (b ⊗ₘ d)) (toTensorHom_naturality R b d)
    (toTensorHom R (A ⊗ B) D) (toTensorHom R (A' ⊗ B') D')
    (DerivedCategory.Q.map ((a ⊗ₘ b) ⊗ₘ d)) (toTensorHom_naturality R (a ⊗ₘ b) d)
    (toTensorHom R A (B ⊗ D)) (toTensorHom R A' (B' ⊗ D'))
    (DerivedCategory.Q.map (a ⊗ₘ (b ⊗ₘ d))) (toTensorHom_naturality R a (b ⊗ₘ d))
    (complexAssociatorHom R A B D) (complexAssociatorHom R A' B' D') hq
    (canonicalAssociatorHom R _ _ _) (canonicalAssociatorHom R _ _ _)
    (canonicalAssociatorHom_naturality' R _ _ _) h'

/-- Whiskering on the right by an object is a functor. -/
theorem canonicalWhiskerRight_comp {X Y Z : DerivedModules R} (f : X ⟶ Y) (g : Y ⟶ Z)
    (W : DerivedModules R) :
    canonicalWhiskerRight R (f ≫ g) W =
      canonicalWhiskerRight R f W ≫ canonicalWhiskerRight R g W := by
  rw [canonicalWhiskerRight, canonicalWhiskerRight, canonicalWhiskerRight, Functor.map_comp,
    NatTrans.comp_app]

/-- Whiskering on the left by an object is a functor. -/
theorem canonicalWhiskerLeft_comp (W : DerivedModules R) {X Y Z : DerivedModules R} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    canonicalWhiskerLeft R W (f ≫ g) = canonicalWhiskerLeft R W f ≫ canonicalWhiskerLeft R W g :=
  Functor.map_comp _ _ _

/-- The canonical map is natural in the first complex. -/
theorem toTensorHom_naturality_left {A A' : Complexes R} (f : A ⟶ A') (B : Complexes R) :
    canonicalWhiskerRight R (DerivedCategory.Q.map f) (DerivedCategory.Q.obj B) ≫
        toTensorHom R A' B =
      toTensorHom R A B ≫ DerivedCategory.Q.map (f ⊗ₘ 𝟙 B) := by
  have h := toTensorHom_naturality R f (𝟙 B)
  rwa [canonicalWhiskerLeft, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    Category.id_comp] at h

/-- The canonical map is natural in the second complex. -/
theorem toTensorHom_naturality_right (A : Complexes R) {B B' : Complexes R} (g : B ⟶ B') :
    canonicalWhiskerLeft R (DerivedCategory.Q.obj A) (DerivedCategory.Q.map g) ≫
        toTensorHom R A B' =
      toTensorHom R A B ≫ DerivedCategory.Q.map (𝟙 A ⊗ₘ g) := by
  have h := toTensorHom_naturality R (𝟙 A) g
  rwa [canonicalWhiskerRight, CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
    NatTrans.id_app, Category.id_comp] at h

/-- **The derived multiplication** `QK ⊗^𝐋 QK ⟶ Q(K ⊗ K) ⟶ QK` of a multiplication
`m : K ⊗ K ⟶ K` on a complex of `R`-modules: the canonical map of Stacks 06YU followed by `m`. -/
def derivedMul {K : Complexes R} (m : (K ⊗ K : Complexes R) ⟶ K) :
    ((derivedTensorBifunctorOfSite R).obj (DerivedCategory.Q.obj K)).obj
        (DerivedCategory.Q.obj K) ⟶ DerivedCategory.Q.obj K :=
  toTensorHom R K K ≫ DerivedCategory.Q.map m

/-- Associativity of a multiplication built as `t ≫ qm`: if the whiskerings `wRm` and `wLm`
commute with `t` up to `qm1` and `q1m`, and the associativity squares `hW` (for `t`) and `hA`
(for `qm`) commute, then so does the associativity square of the composite. -/
theorem mul_assoc_of_squares {C : Type*} [Category* C]
    {D0 D1 D2 D3 L0 R0 R1 W0 W1 : C}
    (wRt : D0 ⟶ D1) (wRm : D1 ⟶ D2) (t : D2 ⟶ D3) (qm : D3 ⟶ W0) (t' : D1 ⟶ L0)
    (qm1 : L0 ⟶ D3) (qα : L0 ⟶ R0) (q1m : R0 ⟶ D3) (aD : D0 ⟶ W1) (wLt : W1 ⟶ R1)
    (t'' : R1 ⟶ R0) (wLm : R1 ⟶ D2)
    (hR : wRm ≫ t = t' ≫ qm1) (hL : wLm ≫ t = t'' ≫ q1m)
    (hW : wRt ≫ t' ≫ qα = aD ≫ wLt ≫ t'') (hA : qm1 ≫ qm = qα ≫ q1m ≫ qm) :
    (wRt ≫ wRm) ≫ t ≫ qm = aD ≫ (wLt ≫ wLm) ≫ t ≫ qm := by
  rw [Category.assoc, reassoc_of% hR, hA, reassoc_of% hW, Category.assoc, reassoc_of% hL]

/-- **A multiplication on a complex which is associative on the nose induces an associative
multiplication in the derived category**: if `(m ⊗ 𝟙) ≫ m = α ≫ (𝟙 ⊗ m) ≫ m` on `K`, then the
derived multiplication `μ = derivedMul R m` satisfies `(μ ▷ QK) ≫ μ = α ≫ (QK ◁ μ) ≫ μ` for the
associativity constraint of `canonicalDerivedMonoidal` (Tag 0FPB). -/
theorem derivedMul_assoc {K : Complexes R} (m : (K ⊗ K : Complexes R) ⟶ K)
    (hm : (m ⊗ₘ 𝟙 K) ≫ m = (α_ K K K).hom ≫ (𝟙 K ⊗ₘ m) ≫ m) :
    canonicalWhiskerRight R (derivedMul R m) (DerivedCategory.Q.obj K) ≫ derivedMul R m =
      canonicalAssociatorHom R (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj K)
          (DerivedCategory.Q.obj K) ≫
        canonicalWhiskerLeft R (DerivedCategory.Q.obj K) (derivedMul R m) ≫ derivedMul R m := by
  have hA : DerivedCategory.Q.map (m ⊗ₘ 𝟙 K) ≫ DerivedCategory.Q.map m =
      complexAssociatorHom R K K K ≫ DerivedCategory.Q.map (𝟙 K ⊗ₘ m) ≫
        DerivedCategory.Q.map m := by
    rw [complexAssociatorHom, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, hm]
  rw [derivedMul, canonicalWhiskerRight_comp, canonicalWhiskerLeft_comp]
  exact mul_assoc_of_squares _ _ _ _ _ _ _ _ _ _ _ _ (toTensorHom_naturality_left R m K)
    (toTensorHom_naturality_right R K m) (canonicalAssociator_toTensor R K K K) hA

end Stacks.SheafOfModules.DerivedMonoidal

end
