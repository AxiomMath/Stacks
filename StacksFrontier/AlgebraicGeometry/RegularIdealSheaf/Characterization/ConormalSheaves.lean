module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Multilinear.Basic
public import Mathlib.RingTheory.Ideal.Cotangent
public import StacksFrontier.AlgebraicGeometry.QuasiRegular.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiRegular.StalkGenerators
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Basic
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.Topology.Sheaves.Modules.SupportedSectionsSheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Quasi-regular ideal sheaves: the conormal sheaves

The sectionwise graded pieces and symmetric powers of an ideal, their functoriality, the
presheaves and sheaves `O_X/J`, `Jⁿ/Jⁿ⁺¹`, `J/J²`, `Symⁿ(J/J²)` with the canonical map between
the last two, and the comparison in degrees zero and one.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RingTheory.QuasiRegular
open scoped BigOperators
universe u v

/- The structure sheaf of a `RingedSpace` is packaged as a `TopCat.Sheaf`, while every
sheafification and every `sheafCompose` below speaks of
`Sheaf (Opens.grothendieckTopology _)`.  The two are the same definition, so unification is
allowed to see through these abbreviations. -/
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local implicit_reducible] SheafOfModules.toSheaf PresheafOfModules.presheaf

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf

/-- A section generating an ideal sheaf over `U` is a section of that ideal sheaf. -/
theorem mem_of_isGeneratedByOn (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op U)) (h : IsGeneratedByOn X J U f) (i : Fin r) :
    f i ∈ J.obj (op U) := by
  rw [h U le_rfl]
  exact mem_generatedIdealOn X U f i

end Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal
namespace Construction
variable {R : Type u} [CommRing R] (I : Ideal R)

/-- The degree-`n` graded piece `Iⁿ/Iⁿ⁺¹` of the `I`-adic filtration of `R`. -/
@[ega "0 15.2.1" "special case",
  ega "IV 16.1.2" "special case",
  sga "1 II 4.14" "partial",
  sga "1 III 6.9"]
abbrev GradedPiece (n : ℕ) := ↥(I ^ n) ⧸ (Submodule.comap (I ^ n).subtype (I ^ (n + 1)))

/-- The ideal `I` annihilates `Iⁿ/Iⁿ⁺¹`. -/
lemma gradedPiece_torsion (n : ℕ) : Module.IsTorsionBySet R (GradedPiece I n) (I : Set R) := by
  rw [Module.isTorsionBySet_quotient_iff]
  intro x r hr
  show r * (x : R) ∈ I ^ (n + 1)
  rw [pow_succ']
  exact Ideal.mul_mem_mul hr x.property

/-- The `R/I`-module structure on `Iⁿ/Iⁿ⁺¹`. -/
noncomputable instance (n : ℕ) : Module (R ⧸ I) (GradedPiece I n) :=
  (gradedPiece_torsion I n).module
/-- Scalars act on `Iⁿ/Iⁿ⁺¹` through `R/I`. -/
instance (n : ℕ) : IsScalarTower R (R ⧸ I) (GradedPiece I n) :=
  (gradedPiece_torsion I n).isScalarTower

/-- Formal `R`-linear combinations of `n`-letter words in elements of `I`. -/
abbrev Words (n : ℕ) := (Fin n → I) →₀ R
/-- The word with letters `a` and coefficient one. -/
noncomputable def word {n : ℕ} (a : Fin n → I) : Words I n := Finsupp.single a 1

/-- The usual presentation of `Symⁿ_(R/I)(I/I²)`: multilinearity, symmetry,
reduction of coefficients modulo `I`, and reduction of factors modulo `I²`. -/
inductive SymmetricRelation (n : ℕ) : Words I n → Prop
  | add (a : Fin n → I) (i : Fin n) (x y : I) :
      SymmetricRelation n (word I (Function.update a i (x + y)) -
        word I (Function.update a i x) - word I (Function.update a i y))
  | smul (a : Fin n → I) (i : Fin n) (r : R) (x : I) :
      SymmetricRelation n (word I (Function.update a i (r • x)) -
        r • word I (Function.update a i x))
  | perm (a : Fin n → I) (σ : Equiv.Perm (Fin n)) :
      SymmetricRelation n (word I (a ∘ σ) - word I a)
  | coeff (a : Fin n → I) (r : R) (hr : r ∈ I) :
      SymmetricRelation n (r • word I a)
  | square (a : Fin n → I) (i : Fin n) (hi : (a i : R) ∈ I ^ 2) :
      SymmetricRelation n (word I a)

/-- The submodule of words spanned by the symmetric-power relations. -/
noncomputable def relations (n : ℕ) : Submodule R (Words I n) :=
  Submodule.span R {z | SymmetricRelation I n z}

/-- `Symⁿ_(R/I)(I/I²)`, presented by words modulo the symmetric relations. -/
abbrev SymmetricPower (n : ℕ) := Words I n ⧸ relations I n

/-- The ideal `I` annihilates `Symⁿ_(R/I)(I/I²)`. -/
lemma symmetricPower_torsion (n : ℕ) :
    Module.IsTorsionBySet R (SymmetricPower I n) (I : Set R) := by
  rw [Module.isTorsionBySet_quotient_iff]
  intro x r hr
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simpa only [smul_add] using (relations I n).add_mem hx hy
  | single a s =>
    have h : r • word I a ∈ relations I n :=
      Submodule.subset_span (SymmetricRelation.coeff (I := I) a r hr)
    have h' := (relations I n).smul_mem s h
    simpa [word, smul_smul, mul_comm, Finsupp.smul_single] using h'

/-- The `R/I`-module structure on `Symⁿ_(R/I)(I/I²)`. -/
noncomputable instance (n : ℕ) : Module (R ⧸ I) (SymmetricPower I n) :=
  (symmetricPower_torsion I n).module
/-- Scalars act on `Symⁿ_(R/I)(I/I²)` through `R/I`. -/
instance (n : ℕ) : IsScalarTower R (R ⧸ I) (SymmetricPower I n) :=
  (symmetricPower_torsion I n).isScalarTower

/-- The product of `n` elements of `I`, as an element of `Iⁿ`. -/
noncomputable def product (n : ℕ) : MultilinearMap R (fun _ : Fin n => I) ↥(I ^ n) :=
  ((MultilinearMap.mkPiAlgebra R (Fin n) R).compLinearMap (fun _ => I.subtype)).codRestrict
    (I ^ n) (fun a => by
      change (∏ i, (a i : R)) ∈ I ^ n
      simpa using (show (∏ i, (a i : R)) ∈ ∏ _i : Fin n, I from
        Ideal.prod_mem_prod (fun i _ => (a i).property)))

/-- The product of `n` elements of `I`, read modulo `Iⁿ⁺¹`. -/
noncomputable def productClass (n : ℕ) :
    MultilinearMap R (fun _ : Fin n => I) (GradedPiece I n) :=
  (Submodule.mkQ _).compMultilinearMap (product I n)

/-- The `R`-linear extension of the product of letters to all words. -/
noncomputable def productMap (n : ℕ) : Words I n →ₗ[R] GradedPiece I n :=
  Finsupp.linearCombination R (productClass I n)

/-- The product map on a word is the product of its letters. -/
@[simp] lemma productMap_word {n : ℕ} (a : Fin n → I) :
    productMap I n (word I a) = productClass I n a := by
  simp [productMap, word]

/-- The product of letters annihilates the symmetric-power relations. -/
lemma relations_le_ker_productMap (n : ℕ) : relations I n ≤ (productMap I n).ker := by
  rw [relations, Submodule.span_le]
  intro z hz
  show productMap I n z = 0
  cases hz with
  | add a i x y => simp [MultilinearMap.map_update_add]
  | smul a i r x => simp [MultilinearMap.map_update_smul]
  | perm a σ =>
    simp only [map_sub, productMap_word, sub_eq_zero]
    apply congrArg (Submodule.mkQ _)
    apply Subtype.ext
    exact Equiv.prod_comp σ (fun i => (a i : R))
  | coeff a r hr =>
    simp only [map_smul, productMap_word]
    exact gradedPiece_torsion I n (a := ⟨r, hr⟩)
  | square a i hi =>
    simp only [productMap_word]
    apply (Submodule.Quotient.mk_eq_zero _).2
    show (∏ j, (a j : R)) ∈ I ^ (n + 1)
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    have hrest : (∏ j ∈ Finset.univ.erase i, (a j : R)) ∈
        I ^ (Finset.univ.erase i).card := by
      simpa using (show (∏ j ∈ Finset.univ.erase i, (a j : R)) ∈
        ∏ _j ∈ Finset.univ.erase i, I from Ideal.prod_mem_prod (fun j _ => (a j).property))
    have h := Ideal.mul_mem_mul hi hrest
    rw [← pow_add] at h
    have hc : 2 + (Finset.univ.erase i).card = n + 1 := by
      simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      have := i.isLt
      omega
    rwa [hc] at h

/-- The canonical map `Symⁿ_(R/I)(I/I²) → Iⁿ/Iⁿ⁺¹`, the product of the letters. -/
noncomputable def canonicalMap (n : ℕ) : SymmetricPower I n →ₗ[R] GradedPiece I n :=
  (relations I n).liftQ (productMap I n) (relations_le_ker_productMap I n)

end Construction
end Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal.Construction
variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]
variable (I : Ideal R) (K : Ideal S) (φ : R →+* S) (h : I ≤ K.comap φ)

include h in
/-- A ring map carrying `I` into `K` carries `Iⁿ` into `Kⁿ`. -/
lemma map_pow_mem {n : ℕ} {x : R} (hx : x ∈ I ^ n) : φ x ∈ K ^ n :=
  (Ideal.map_le_iff_le_comap.mp (by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr h) n)) hx

/-- The restriction of `φ` to a semilinear map `I → K`. -/
noncomputable def idealMap : I →ₛₗ[φ] K :=
  φ.toSemilinearMap.restrict (fun _ hx => h hx)

/-- The restriction of `φ` to a semilinear map `Iⁿ → Kⁿ`. -/
noncomputable def powerMap (n : ℕ) : ↥(I ^ n) →ₛₗ[φ] ↥(K ^ n) :=
  φ.toSemilinearMap.restrict (fun _ hx => map_pow_mem I K φ h hx)

/-- The semilinear map `Iⁿ/Iⁿ⁺¹ → Kⁿ/Kⁿ⁺¹` induced by `φ`. -/
noncomputable def gradedMap (n : ℕ) : GradedPiece I n →ₛₗ[φ] GradedPiece K n :=
  Submodule.mapQ _ _ (powerMap I K φ h n) (by
    intro x hx
    change φ (x : R) ∈ K ^ (n + 1)
    exact map_pow_mem I K φ h hx)

/-- The semilinear map on words induced by `φ`, letter by letter. -/
noncomputable def wordsMap (n : ℕ) : Words I n →ₛₗ[φ] Words K n :=
  (Finsupp.lmapDomain S S (fun a i => idealMap I K φ h (a i))).comp
    (Finsupp.mapRange.linearMap φ.toSemilinearMap)

/-- The transport of a word is the word of the transported letters. -/
@[simp] lemma wordsMap_word {n : ℕ} (a : Fin n → I) :
    wordsMap I K φ h n (word I a) = word K (fun i => idealMap I K φ h (a i)) := by
  simp [wordsMap, word]

/-- Transporting letters commutes with updating one letter. -/
lemma map_update {n : ℕ} (a : Fin n → I) (i : Fin n) (x : I) :
    (fun j => idealMap I K φ h (Function.update a i x j)) =
      Function.update (fun j => idealMap I K φ h (a j)) i (idealMap I K φ h x) := by
  funext j
  by_cases hj : j = i <;> simp [hj]

/-- Transporting words carries the symmetric relations into the symmetric relations. -/
lemma relations_map (n : ℕ) :
    relations I n ≤ (relations K n).comap (wordsMap I K φ h n) := by
  rw [relations, Submodule.span_le]
  intro z hz
  show wordsMap I K φ h n z ∈ relations K n
  cases hz with
  | add a i x y =>
    simp only [map_sub, wordsMap_word, map_update, map_add]
    exact Submodule.subset_span (SymmetricRelation.add _ _ _ _)
  | smul a i r x =>
    simp only [map_sub, map_smulₛₗ, wordsMap_word, map_update]
    exact Submodule.subset_span (SymmetricRelation.smul _ _ _ _)
  | perm a σ =>
    simp only [map_sub, wordsMap_word]
    exact Submodule.subset_span (SymmetricRelation.perm _ σ)
  | coeff a r hr =>
    simp only [map_smulₛₗ, wordsMap_word]
    exact Submodule.subset_span (SymmetricRelation.coeff _ _ (h hr))
  | square a i hi =>
    simp only [wordsMap_word]
    exact Submodule.subset_span (SymmetricRelation.square _ i (map_pow_mem I K φ h hi))

/-- The semilinear map `Symⁿ(I/I²) → Symⁿ(K/K²)` induced by `φ`. -/
noncomputable def symmetricMap (n : ℕ) : SymmetricPower I n →ₛₗ[φ] SymmetricPower K n :=
  Submodule.mapQ _ _ (wordsMap I K φ h n) (relations_map I K φ h n)

/-- The induced graded map, computed on the class of an element of `Iⁿ`. -/
@[simp] lemma gradedMap_mk {n : ℕ} (a : ↥(I ^ n)) :
    gradedMap I K φ h n (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (powerMap I K φ h n a) := rfl

/-- The induced symmetric-power map, computed on the class of a word. -/
@[simp] lemma symmetricMap_mk {n : ℕ} (a : Words I n) :
    symmetricMap I K φ h n (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (wordsMap I K φ h n a) := rfl

/-- Induction on `Symⁿ_(R/I)(I/I²)`: it is additively spanned by `r • [word a]`. -/
private lemma symmetricPower_induction {n : ℕ} {P : SymmetricPower I n → Prop}
    (z : SymmetricPower I n) (zero : P 0) (add : ∀ x y, P x → P y → P (x + y))
    (smul_word : ∀ (r : R) (a : Fin n → I), P (r • Submodule.Quotient.mk (word I a))) : P z := by
  induction z using Submodule.Quotient.induction_on with | _ z =>
  induction z using Finsupp.induction_linear with
  | zero => exact zero
  | add a b ha hb => exact add _ _ ha hb
  | single a r =>
    have hw : Finsupp.single a r = r • word I a := by simp [word]
    rw [hw, Submodule.Quotient.mk_smul]
    exact smul_word r a

/-- The canonical map is natural in the pair of a ring and an ideal. -/
lemma canonicalMap_naturality (n : ℕ) (z : SymmetricPower I n) :
    canonicalMap K n (symmetricMap I K φ h n z) =
      gradedMap I K φ h n (canonicalMap I n z) := by
  induction z using symmetricPower_induction with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul_word r a =>
    simp only [map_smulₛₗ]
    congr 1
    show productMap K n (wordsMap I K φ h n (word I a)) =
      gradedMap I K φ h n (productMap I n (word I a))
    simp only [wordsMap_word, productMap_word]
    apply congrArg (Submodule.Quotient.mk)
    apply Subtype.ext
    exact (map_prod φ (fun i : Fin n => (a i : R)) Finset.univ).symm

/-- Regard a semilinear map annihilated by the ideals as semilinear over the quotient rings. -/
noncomputable def quotientSemilinearMap
    {M : Type*} [AddCommGroup M] [Module R M] [Module (R ⧸ I) M]
    [IsScalarTower R (R ⧸ I) M]
    {N : Type*} [AddCommGroup N] [Module S N] [Module (S ⧸ K) N]
    [IsScalarTower S (S ⧸ K) N] (f : M →ₛₗ[φ] N) :
    M →ₛₗ[Ideal.quotientMap K φ h] N where
  toFun := f
  map_add' := f.map_add
  map_smul' r m := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
    change f (algebraMap R (R ⧸ I) r • m) = algebraMap S (S ⧸ K) (φ r) • f m
    simpa only [algebraMap_smul] using f.map_smulₛₗ r m
end Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal.Construction

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal
variable (X : RingedSpace.{u})
  (J : (Stacks.RingedSpace.structureSheafModule X).Submodule)
/-- The ideal of sections of `J` over an open set. -/
noncomputable abbrev sectionIdeal (U : (Opens X)ᵒᵖ) : Ideal (X.presheaf.obj U) := J.obj U
/-- Restriction of sections carries `J(U)` into `J(V)`. -/
lemma sectionIdeal_map {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    sectionIdeal X J U ≤ (sectionIdeal X J V).comap (X.presheaf.map f).hom := by
  intro a ha
  exact J.toSubmodule.map_mem f ha

/-- The presheaf of rings `U ↦ O_X(U)/J(U)`. -/
noncomputable def quotientPresheaf : (Opens X)ᵒᵖ ⥤ RingCat.{u} where
  obj U := RingCat.of (X.presheaf.obj U ⧸ sectionIdeal X J U)
  map f := RingCat.ofHom (Ideal.quotientMap _ (X.presheaf.map f).hom (sectionIdeal_map X J f))
  map_id U := by
    ext a
    simp
  map_comp f g := by
    ext a
    simp

/-- The ring sheaf `O_X/J`, obtained by sheafifying the sectionwise quotients. -/
noncomputable def quotientSheaf : Sheaf (Opens.grothendieckTopology X) RingCat.{u} :=
  (presheafToSheaf (Opens.grothendieckTopology X) RingCat.{u}).obj (quotientPresheaf X J)

/-- The presheaf of `O_X/J`-modules `U ↦ J(U)ⁿ/J(U)ⁿ⁺¹`. -/
noncomputable def gradedPresheaf (n : ℕ) : PresheafOfModules.{u} (quotientPresheaf X J) where
  obj U := ModuleCat.of (X.presheaf.obj U ⧸ sectionIdeal X J U)
    (Construction.GradedPiece (sectionIdeal X J U) n)
  map f := ModuleCat.semilinearMapAddEquiv _ _ _
    (Construction.quotientSemilinearMap _ _ _ (sectionIdeal_map X J f)
      (Construction.gradedMap _ _ _ (sectionIdeal_map X J f) n))
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    induction a using Submodule.Quotient.induction_on with | _ a =>
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (X.presheaf.map_id U) a.val
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    induction a using Submodule.Quotient.induction_on with | _ a =>
    apply congrArg Submodule.Quotient.mk
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (X.presheaf.map_comp f g) a.val
end Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal

/- Everything downstream names `quotientSheaf X J` where the sheafification machinery
produces `(presheafToSheaf _ _).obj (quotientPresheaf X J)`, and names `gradedPresheaf X J n`
where it produces that functor's components. Mathlib's own links in those chains --
`sheafify`, `toSheafify`, `Sheaf.over`, `overPullback` -- are all `abbrev`, so they already
unfold at `implicit` transparency; these three definitions of ours were the only semireducible
steps left, which is why unification could not see through them without raising transparency
wholesale. Naming them here is what makes the three local constructions as transparent as the
Mathlib abbreviations they expand into. -/
open Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal in
attribute [local implicit_reducible] quotientPresheaf quotientSheaf gradedPresheaf
/- The remaining chain runs through Mathlib's free-module and sheaf-pullback machinery:
`PresheafOfModules.freeObj F` has `obj V := (ModuleCat.free (R.obj V)).obj (F.obj V)`, and
`Sheaf.over`/`overPullback` bottom out in `Functor.sheafPushforwardContinuous`. Those three are
the only `def`s in it -- every other step is already an `abbrev` -- so naming them lets
unification reach the `Finsupp` module structure that the free presheaf of modules is built
from, and the sections functor that `Sheaf.over` is. -/
attribute [local implicit_reducible] PresheafOfModules.freeObj ModuleCat.free
  CategoryTheory.Functor.sheafPushforwardContinuous

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal
variable (X : RingedSpace.{u})
  (J : (Stacks.RingedSpace.structureSheafModule X).Submodule)

/-- The presheaf of `O_X/J`-modules `U ↦ Symⁿ_(O_X(U)/J(U))(J(U)/J(U)²)`. -/
noncomputable def symmetricPresheaf (n : ℕ) : PresheafOfModules.{u} (quotientPresheaf X J) where
  obj U := ModuleCat.of (X.presheaf.obj U ⧸ sectionIdeal X J U)
    (Construction.SymmetricPower (sectionIdeal X J U) n)
  map f := ModuleCat.semilinearMapAddEquiv _ _ _
    (Construction.quotientSemilinearMap _ _ _ (sectionIdeal_map X J f)
      (Construction.symmetricMap _ _ _ (sectionIdeal_map X J f) n))
  map_id U := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    induction a using Submodule.Quotient.induction_on with | _ a =>
    apply congrArg Submodule.Quotient.mk
    simp only [Construction.wordsMap]
    have hm : (fun (a : Fin n → sectionIdeal X J U) i =>
        Construction.idealMap _ _ (X.presheaf.map (𝟙 U)).hom (sectionIdeal_map X J (𝟙 U))
          (a i)) = id := by
      funext a i
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (X.presheaf.map_id U) (a i).val
    rw [hm]
    simp
  map_comp f g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    induction a using Submodule.Quotient.induction_on with | _ a =>
    apply congrArg Submodule.Quotient.mk
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb
    | single a r =>
      simp only [Construction.wordsMap, Construction.idealMap, LinearMap.coe_comp,
        Function.comp_apply, Finsupp.mapRange.linearMap_apply, RingHom.coe_toSemilinearMap,
        X.presheaf.map_comp, CommRingCat.hom_comp, RingHom.coe_comp,
        Finsupp.mapRange_single, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
      congr 1
      funext i
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (X.presheaf.map_comp f g) (a i).val

/-- The sectionwise canonical map `Symⁿ(J/J²) ⟶ Jⁿ/Jⁿ⁺¹` of presheaves of modules. -/
noncomputable def canonicalPresheafMap (n : ℕ) :
    symmetricPresheaf X J n ⟶ gradedPresheaf X J n where
  app U := ModuleCat.ofHom
    { toFun := Construction.canonicalMap (sectionIdeal X J U) n
      map_add' := map_add _
      map_smul' r m := by
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        change Construction.canonicalMap _ n (algebraMap _ _ r • m) =
          algebraMap _ _ r • Construction.canonicalMap _ n m
        simpa only [algebraMap_smul] using
          (Construction.canonicalMap (sectionIdeal X J U) n).map_smul r m }
  naturality f := by
    ext a
    exact Construction.canonicalMap_naturality _ _ _ (sectionIdeal_map X J f) n a

/-- Sheafification of presheaves of modules over the quotient presheaf of rings. -/
noncomputable def quotientSheafification :
    PresheafOfModules.{u} (quotientPresheaf X J) ⥤ SheafOfModules.{u} (quotientSheaf X J) := by
  let T := Opens.grothendieckTopology X
  letI : Limits.HasColimitsOfSize.{u, u} RingCat.{u} :=
    Limits.hasColimitsOfSizeShrink RingCat.{u}
  letI : ∀ U : Opens X, Limits.HasColimitsOfShape (T.Cover U)ᵒᵖ RingCat.{u} := fun U =>
    Limits.HasColimitsOfShape.of_small (C := RingCat.{u}) ((T.Cover U)ᵒᵖ)
  letI : Limits.PreservesFilteredColimitsOfSize.{u, u} (forget RingCat.{u}) :=
    Limits.preservesFilteredColimitsOfSize_shrink _
  letI : T.PreservesSheafification (forget RingCat.{u}) :=
    GrothendieckTopology.instPreservesSheafification T (forget RingCat.{u})
  letI : ConcreteCategory.{u} RingCat
      (fun A B : RingCat.{u} => A →+* B) := inferInstance
  letI : T.WEqualsLocallyBijective RingCat.{u} := inferInstance
  letI : Presheaf.IsLocallyInjective T
      (CategoryTheory.toSheafify T (quotientPresheaf X J)) := inferInstance
  letI : Presheaf.IsLocallySurjective T
      (CategoryTheory.toSheafify T (quotientPresheaf X J)) := inferInstance
  exact PresheafOfModules.sheafification (J := T)
    (CategoryTheory.toSheafify T (quotientPresheaf X J))

/-- The degree `n` associated graded sheaf `Jⁿ/Jⁿ⁺¹`, as an `O_X/J`-module. -/
noncomputable def associatedGradedPiece (n : ℕ) : SheafOfModules.{u} (quotientSheaf X J) :=
  (quotientSheafification X J).obj (gradedPresheaf X J n)

/-- The conormal sheaf `J/J²`, with its natural `O_X/J`-module structure. -/
noncomputable abbrev conormalSheaf : SheafOfModules.{u} (quotientSheaf X J) :=
  associatedGradedPiece X J 1

/-- The `n`th symmetric power over `O_X/J` of the conormal sheaf. It is the
sheafification of the symmetric multilinear presentation on local ideal sections. -/
noncomputable def conormalSymmetricPower (n : ℕ) : SheafOfModules.{u} (quotientSheaf X J) :=
  (quotientSheafification X J).obj (symmetricPresheaf X J n)

/-- The canonical morphism `Symⁿ_(O_X/J)(J/J²) ⟶ Jⁿ/Jⁿ⁺¹`, sending a symmetric
product of local ideal sections to their product modulo `Jⁿ⁺¹`. -/
@[ega "0 19.5.2" "more general", ega "IV 16.9.3" "partial", ega "IV 17.12.1" "partial"]
noncomputable def conormalSymmetricToGradedMap (n : ℕ) :
    conormalSymmetricPower X J n ⟶ associatedGradedPiece X J n :=
  (quotientSheafification X J).map (canonicalPresheafMap X J n)

end Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal

namespace Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal

namespace Construction
variable {R : Type u} [CommRing R] (I : Ideal R)

/-- `canonicalMap` is bijective if `g` inverts it, `g` being the identity on products of letters. -/
private lemma canonicalMap_bijective_of_inverse (n : ℕ)
    (g : GradedPiece I n →ₗ[R] SymmetricPower I n)
    (hg : ∀ a, g (productClass I n a) = Submodule.Quotient.mk (word I a))
    (hg' : ∀ x, canonicalMap I n (g x) = x) : Function.Bijective (canonicalMap I n) := by
  refine ⟨Function.LeftInverse.injective (g := g) fun x => ?_,
    Function.RightInverse.surjective hg'⟩
  induction x using symmetricPower_induction with
  | zero => simp
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | smul_word r a =>
    rw [map_smul, map_smul]
    congr 1
    show g (productMap I n (word I a)) = _
    rw [productMap_word]
    exact hg a

private lemma word_update_one (a : Fin 1 → I) (x : I) :
    Function.update a 0 x = fun _ => x := by
  funext i
  fin_cases i
  simp

private noncomputable def degreeOneWord : I →ₗ[R] SymmetricPower I 1 where
  toFun x := Submodule.Quotient.mk (word I (fun _ => x))
  map_add' x y := by
    have h := (Submodule.Quotient.mk_eq_zero (relations I 1)).2
      (Submodule.subset_span (SymmetricRelation.add (I := I) (fun _ => x) 0 x y))
    simpa only [word_update_one, Submodule.Quotient.mk_sub, sub_eq_zero,
      sub_eq_iff_eq_add, zero_add, add_comm] using h
  map_smul' r x := by
    have h := (Submodule.Quotient.mk_eq_zero (relations I 1)).2
      (Submodule.subset_span (SymmetricRelation.smul (I := I) (fun _ => x) 0 r x))
    simpa only [word_update_one, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      sub_eq_zero, RingHom.id_apply] using h

private noncomputable def degreeOneInverse : GradedPiece I 1 →ₗ[R] SymmetricPower I 1 :=
  (Submodule.comap (I ^ 1).subtype (I ^ (1 + 1))).liftQ
    ((degreeOneWord I).comp (Submodule.inclusion (show I ^ 1 ≤ I by simp))) (by
      intro x hx
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact Submodule.subset_span (SymmetricRelation.square (I := I)
        (fun _ => ⟨(x : R), by simpa using x.property⟩) 0 hx))

private lemma degreeOneInverse_productClass (a : Fin 1 → I) :
    degreeOneInverse I (productClass I 1 a) = Submodule.Quotient.mk (word I a) := by
  show Submodule.Quotient.mk (word I (fun _ => _)) = _
  congr 2
  funext i
  apply Subtype.ext
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  simp [product, MultilinearMap.mkPiAlgebra_apply]

private lemma canonicalMap_degreeOneInverse (x : GradedPiece I 1) :
    canonicalMap I 1 (degreeOneInverse I x) = x := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
  show productMap I 1 (word I (fun _ => _)) = Submodule.Quotient.mk x
  rw [productMap_word]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simp [product, MultilinearMap.mkPiAlgebra_apply]

private lemma canonicalMap_bijective_one : Function.Bijective (canonicalMap I 1) :=
  canonicalMap_bijective_of_inverse I 1 (degreeOneInverse I) (degreeOneInverse_productClass I)
    (canonicalMap_degreeOneInverse I)

private lemma productMap_eq (n : ℕ) :
    productMap I n = (Submodule.mkQ _).comp (Finsupp.linearCombination R (product I n)) := by
  ext a
  simp [productMap, productClass]

lemma canonicalMap_surjective (n : ℕ) : Function.Surjective (canonicalMap I n) := by
  let p : Words I n →ₗ[R] R :=
    (I ^ n).subtype.comp (Finsupp.linearCombination R (product I n))
  have hr : I ^ n ≤ LinearMap.range p := by
    rw [Submodule.pow_eq_span_pow_set]
    apply Submodule.span_le.mpr
    intro a ha
    obtain ⟨f, hf, rfl⟩ := Set.mem_pow_iff_prod.mp ha
    refine ⟨word I (fun i => ⟨f i, hf i⟩), ?_⟩
    simp [p, word, product, MultilinearMap.mkPiAlgebra_apply]
  intro x
  induction x using Submodule.Quotient.induction_on with | _ x =>
  obtain ⟨w, hw⟩ := hr x.property
  refine ⟨Submodule.Quotient.mk w, ?_⟩
  show productMap I n w = Submodule.Quotient.mk x
  rw [productMap_eq]
  apply congrArg Submodule.Quotient.mk
  exact Subtype.ext hw

private noncomputable def degreeZeroWord : R →ₗ[R] SymmetricPower I 0 :=
  LinearMap.toSpanSingleton R _ (Submodule.Quotient.mk (word I Fin.elim0))

private noncomputable def degreeZeroInverse : GradedPiece I 0 →ₗ[R] SymmetricPower I 0 :=
  (Submodule.comap (I ^ 0).subtype (I ^ (0 + 1))).liftQ
    ((degreeZeroWord I).comp (I ^ 0).subtype) (by
      intro x hx
      change (x : R) • (Submodule.Quotient.mk (word I Fin.elim0) : SymmetricPower I 0) = 0
      rw [← Submodule.Quotient.mk_smul]
      apply (Submodule.Quotient.mk_eq_zero _).2
      exact Submodule.subset_span (SymmetricRelation.coeff (I := I) Fin.elim0 x
        (by simpa using hx)))

private lemma degreeZeroInverse_productClass (a : Fin 0 → I) :
    degreeZeroInverse I (productClass I 0 a) = Submodule.Quotient.mk (word I a) := by
  have ha : a = Fin.elim0 := funext (fun i => i.elim0)
  subst a
  show (∏ i : Fin 0, (Fin.elim0 i : I).val) •
    (Submodule.Quotient.mk (word I Fin.elim0) : SymmetricPower I 0) = _
  simp

private lemma canonicalMap_degreeZeroInverse (x : GradedPiece I 0) :
    canonicalMap I 0 (degreeZeroInverse I x) = x := by
  induction x using Submodule.Quotient.induction_on with | _ x =>
  show canonicalMap I 0 ((x : R) • Submodule.Quotient.mk (word I Fin.elim0)) = _
  rw [map_smul]
  show (x : R) • productMap I 0 (word I Fin.elim0) = _
  rw [productMap_word]
  show (x : R) • Submodule.Quotient.mk (product I 0 Fin.elim0) = _
  rw [← Submodule.Quotient.mk_smul]
  apply congrArg Submodule.Quotient.mk
  apply Subtype.ext
  simp [product, MultilinearMap.mkPiAlgebra_apply]

private lemma canonicalMap_bijective_zero : Function.Bijective (canonicalMap I 0) :=
  canonicalMap_bijective_of_inverse I 0 (degreeZeroInverse I) (degreeZeroInverse_productClass I)
    (canonicalMap_degreeZeroInverse I)

end Construction

private lemma canonicalPresheafMap_epi (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (n : ℕ) :
    Epi (canonicalPresheafMap X J n) := by
  apply PresheafOfModules.epi_of_surjective
  intro U
  exact Construction.canonicalMap_surjective (sectionIdeal X J U) n

private lemma canonicalPresheafMap_isIso_of_bijective (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (n : ℕ)
    (h : ∀ U, Function.Bijective (Construction.canonicalMap (sectionIdeal X J U) n)) :
    IsIso (canonicalPresheafMap X J n) := by
  have := canonicalPresheafMap_epi X J n
  have : Mono (canonicalPresheafMap X J n) :=
    PresheafOfModules.mono_of_injective fun U => (h U).1
  exact isIso_of_mono_of_epi _

private lemma canonicalPresheafMap_isIso_one (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) :
    IsIso (canonicalPresheafMap X J 1) :=
  canonicalPresheafMap_isIso_of_bijective X J 1 fun U =>
    Construction.canonicalMap_bijective_one (sectionIdeal X J U)

private lemma conormalSymmetricToGradedMap_isIso_one (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) :
    IsIso (conormalSymmetricToGradedMap X J 1) := by
  have := canonicalPresheafMap_isIso_one X J
  exact Functor.map_isIso (quotientSheafification X J) (canonicalPresheafMap X J 1)

private lemma canonicalPresheafMap_isIso_zero (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) :
    IsIso (canonicalPresheafMap X J 0) :=
  canonicalPresheafMap_isIso_of_bijective X J 0 fun U =>
    Construction.canonicalMap_bijective_zero (sectionIdeal X J U)

private lemma conormalSymmetricToGradedMap_isIso_zero (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) :
    IsIso (conormalSymmetricToGradedMap X J 0) := by
  have := canonicalPresheafMap_isIso_zero X J
  exact Functor.map_isIso (quotientSheafification X J) (canonicalPresheafMap X J 0)

@[ega "0 19.5.2" "more general", ega "IV 16.9.3" "partial"]
private lemma conormalSymmetricToGradedMap_epi (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (n : ℕ) :
    Epi (conormalSymmetricToGradedMap X J n) := by
  have := canonicalPresheafMap_epi X J n
  have hB : Epi ((PresheafOfModules.toPresheaf (quotientPresheaf X J)).map
    (canonicalPresheafMap X J n)) := inferInstance
  apply (SheafOfModules.toSheaf _).epi_of_epi_map
  show Epi ((presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
    ((PresheafOfModules.toPresheaf _).map (canonicalPresheafMap X J n)))
  infer_instance

lemma quasiRegularMap_isIso_iff (X : RingedSpace.{u}) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op (⊤ : Opens X))) :
    IsIso (QuasiRegular.quasiRegularMap X f).hom ↔
      ∀ x : X, Function.Bijective
        (associatedGradedMap (QuasiRegular.germSequence X f x)) := by
  rw [TopCat.Presheaf.isIso_iff_stalkFunctor_map_iso]
  apply forall_congr'
  intro x
  let D := QuasiRegular.quasiRegularMap X f
  let k := (TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map D.hom.hom
  have hleft := ConcreteCategory.bijective_of_isIso (D.associatedGradedStalkIso x).hom
  have hright := ConcreteCategory.bijective_of_isIso (D.polynomialStalkIso x).hom
  have heq : (fun p => (D.associatedGradedStalkIso x).hom p) ∘ (fun p => k p) =
      (fun p => associatedGradedMap
        (QuasiRegular.germSequence X f x) p) ∘ (fun p => (D.polynomialStalkIso x).hom p) :=
    funext (D.stalk_map x)
  constructor
  · intro hk
    have hk' := ConcreteCategory.bijective_of_isIso k
    have h := hleft.comp hk'
    rw [heq] at h
    exact (Function.Bijective.of_comp_iff _ hright).mp h
  · intro hp
    have h := hp.comp hright
    rw [← heq] at h
    have hk := (Function.Bijective.of_comp_iff' hleft _).mp h
    have : IsIso ((forget CommRingCat.{u}).map k) := (isIso_iff_bijective _).mpr hk
    exact isIso_of_reflects_iso k (forget CommRingCat.{u})

noncomputable def gradedPieceOneEquivCotangent {R : Type u} [CommRing R]
    (I : Ideal R) : Construction.GradedPiece I 1 ≃ₗ[R] I.Cotangent := by
  have h : Submodule.comap I.subtype (I ^ 2) = I • (⊤ : Submodule R I) := by
    rw [← I.map_toCotangent_ker,
      Submodule.comap_map_eq_of_injective (Submodule.injective_subtype I)]
    change (I • (⊤ : Submodule R I)).mkQ.ker = _
    exact Submodule.ker_mkQ _
  change (↥(I ^ 1) ⧸ Submodule.comap (I ^ 1).subtype (I ^ 2)) ≃ₗ[R]
    (I ⧸ (I • (⊤ : Submodule R I)))
  rw [pow_one, h]

private noncomputable def kernelIdeal (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule)
    {N : SheafOfModules.{u} _} (φ : J.toSheafOfModules ⟶ N) :
    (Stacks.RingedSpace.structureSheafModule X).Submodule where
  obj V := ((φ.val.app V).hom.ker).map (J.obj V).subtype
  map {V W} i := by
    rintro s ⟨t, ht, rfl⟩
    refine ⟨J.toSheafOfModules.val.map i t, ?_, rfl⟩
    change φ.val.app W (J.toSheafOfModules.val.map i t) = 0
    have ht0 : (φ.val.app V).hom t = 0 := ht
    exact (PresheafOfModules.naturality_apply φ.val i t).trans
      ((congrArg (fun z => N.val.map i z) ht0).trans (map_zero _))
  isSheaf {V} s hs := by
    have hJ : s ∈ J.obj V := by
      apply J.isSheaf s
      refine (Opens.grothendieckTopology X).superset_covering (fun W i hi => ?_) hs
      obtain ⟨t, ht, heq⟩ := hi
      change (Stacks.RingedSpace.structureSheafModule X).val.map i.op s ∈ J.obj (op W)
      change (t : (Stacks.RingedSpace.structureSheafModule X).val.obj (op W)) =
        (Stacks.RingedSpace.structureSheafModule X).val.map i.op s at heq
      exact heq ▸ t.property
    refine ⟨⟨s, hJ⟩, ?_, rfl⟩
    change φ.val.app V ⟨s, hJ⟩ = 0
    apply N.isSheaf.isSeparated _ _ hs
    intro W i hi
    obtain ⟨t, ht, heq⟩ := hi
    change N.val.map i.op (φ.val.app V ⟨s, hJ⟩) = N.val.map i.op 0
    have he : J.toSheafOfModules.val.map i.op (⟨s, hJ⟩ : J.obj V) = t :=
      Subtype.ext heq.symm
    have ht0 : (φ.val.app (op W)).hom t = 0 := ht
    refine Eq.trans
      (PresheafOfModules.naturality_apply φ.val i.op (⟨s, hJ⟩ : J.obj V)).symm ?_
    exact ((congrArg (fun z => φ.val.app (op W) z) he).trans ht0).trans (map_zero _).symm

/-- Restriction along a morphism of an over-category, composed with the structure map. Stated
for an abstract presheaf of modules: at a concrete one the `rw` below has an ill-typed
motive. -/
private lemma map_over_hom_apply {C : Type v} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) {U : C} {V W : (Over U)ᵒᵖ} (i : V ⟶ W)
    (s : M.obj (op U)) :
    M.map i.unop.left.op (M.map V.unop.hom.op s) = M.map W.unop.hom.op s := by
  rw [← PresheafOfModules.map_comp_apply, ← op_comp, Over.w]

noncomputable def sectionOver (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X)
    (s : J.obj (op U)) : (J.toSheafOfModules.over U).sections :=
  PresheafOfModules.sectionsMk
    (fun V => J.toSheafOfModules.val.map V.unop.hom.op s) (by
      intro V W i
      exact map_over_hom_apply J.toSheafOfModules.val i s)

lemma hom_eq_zero_of_generators (X : RingedSpace.{u})
    (J : (Stacks.RingedSpace.structureSheafModule X).Submodule) (U : Opens X) {r : ℕ}
    (f : Fin r → X.presheaf.obj (op U))
    (hgen : IsGeneratedByOn X J U f)
    {N : SheafOfModules.{u} _} (φ : J.toSheafOfModules.over U ⟶ N)
    (hf : ∀ i V, φ.val.app V
      ((sectionOver X J U ⟨f i, mem_of_isGeneratedByOn X J U f hgen i⟩).val V) = 0) :
    φ = 0 := by
  let adj := SheafOfModules.overPushforwardOverAdj
    (R := (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) U
  let τ := (adj.homEquiv J.toSheafOfModules N) φ
  have hle : generatedIdealOn X U f ≤ kernelIdeal X J τ := by
    apply generatedIdealOn_le
    intro i
    refine ⟨⟨f i, mem_of_isGeneratedByOn X J U f hgen i⟩, ?_, rfl⟩
    show τ.val.app (op U) _ = 0
    exact hf i (op ((Over.star U).obj U))
  have hτ : τ.over U = 0 := by
    ext V s
    have hs : s.val ∈ (kernelIdeal X J τ).obj (op V.unop.left) := by
      apply hle (op V.unop.left)
      rw [← hgen V.unop.left (leOfHom V.unop.hom)]
      exact s.property
    obtain ⟨t, ht, heq⟩ := hs
    have he : t = s := Subtype.ext heq
    subst t
    exact ht
  have he := (adj.homEquiv J.toSheafOfModules N).symm_apply_apply φ
  rw [Adjunction.homEquiv_counit] at he
  change τ.over U ≫ _ = φ at he
  rw [hτ] at he
  exact he.symm.trans Limits.zero_comp

end Stacks.AlgebraicGeometry.RegularIdealSheaf.Conormal

end
