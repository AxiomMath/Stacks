module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Noetherian.Basic
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIsoShift

/-!
# Finiteness and vanishing for the total complex of a double complex

Two pieces of homological algebra feed the finiteness of the hypercohomology of a bounded complex
with coherent terms.

* Over a Noetherian ring `A` the finite `A`-modules form a Serre class of `ModuleCat A`, and so
  do the `B`-modules which are finite over `A` along a ring map `A →+* B`. A weak Serre class
  containing the column cohomology of a double complex contains the cohomology of its total
  complex (`Stacks.DeRhamDirectImage.weakSerre_homology_total`), so this is what makes the total
  complex of a Čech double complex finite in every degree.
* A double complex `B^{p,q}` whose columns are supported in `a ≤ p ≤ b`, vanish in negative
  second degree and have no cohomology in second degrees `> m` has a total complex without
  cohomology in degrees `> b + m`: the columns may be replaced by their canonical truncations
  `τ_{≤ m}`, which changes the total complex by a quasi-isomorphism (acyclic assembly), and the
  total complex of the truncated double complex vanishes termwise above `b + m`.

## Main results

* `AlgebraicGeometry.DeRhamTypeComplex.isSerreClass_moduleFinite`: finite modules over a
  Noetherian ring form a Serre class.
* `AlgebraicGeometry.DeRhamTypeComplex.isSerreClass_finiteOver`: so do the modules which are finite
  over a Noetherian ring after restriction of scalars.
* `AlgebraicGeometry.DeRhamTypeComplex.isZero_homology_total_of_exactAt`: the vanishing of the
  cohomology of the total complex above `b + m`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape

universe v u

namespace AlgebraicGeometry.DeRhamTypeComplex

/-! ### Finite modules -/

section Finite

variable (A : Type u) [CommRing A]

/-- The property of an `A`-module of being finitely generated. -/
def moduleFinite : ObjectProperty (ModuleCat.{v} A) := fun M => Module.Finite A M

/-- **Finitely generated modules over a Noetherian ring form a Serre class**: submodules of
finite modules are finite because the ring is Noetherian, quotients of finite modules are
finite, and an extension of finite modules is finite. -/
instance isSerreClass_moduleFinite [IsNoetherianRing A] :
    (moduleFinite.{v} A).IsSerreClass where
  exists_zero := ⟨ModuleCat.of A PUnit, ModuleCat.isZero_of_subsingleton _,
    (inferInstance : Module.Finite A PUnit)⟩
  prop_of_mono {M N} f hf hN := by
    have : Module.Finite A N := hN
    have hinj : Function.Injective f.hom := (ModuleCat.mono_iff_injective f).1 hf
    exact Module.Finite.of_injective f.hom hinj
  prop_of_epi {M N} f hf hM := by
    have : Module.Finite A M := hM
    have hsurj : Function.Surjective f.hom := (ModuleCat.epi_iff_surjective f).1 hf
    exact Module.Finite.of_surjective f.hom hsurj
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have : Module.Finite A S.X₁ := h₁
    have : Module.Finite A S.X₃ := h₃
    have hex : Function.Exact S.f.hom S.g.hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
    exact Module.Finite.of_exact (f := S.f.hom) (g := S.g.hom) hex hS.moduleCat_surjective_g

variable {A} {B : Type u} [Ring B] (φ : A →+* B)

/-- The property of a `B`-module of being finite over `A` along `φ : A →+* B`. -/
def finiteOver : ObjectProperty (ModuleCat.{v} B) :=
  (moduleFinite.{v} A).inverseImage (ModuleCat.restrictScalars.{v} φ)

/-- A `B`-module `M` is finite over `A` along `φ` if and only if its restriction of scalars along
`φ` is a finite `A`-module. -/
lemma finiteOver_iff (M : ModuleCat.{v} B) :
    finiteOver φ M ↔ Module.Finite A ((ModuleCat.restrictScalars.{v} φ).obj M) :=
  Iff.rfl

/-- **The `B`-modules finite over a Noetherian ring `A` form a Serre class**: restriction of
scalars is exact and faithful on underlying groups, so the closure properties of finite
`A`-modules pull back. -/
instance isSerreClass_finiteOver [IsNoetherianRing A] : (finiteOver.{v} φ).IsSerreClass where
  exists_zero := ⟨ModuleCat.of B PUnit, ModuleCat.isZero_of_subsingleton _,
    (inferInstance : Module.Finite A PUnit)⟩
  prop_of_mono {M N} f hf hN := by
    have : Module.Finite A ((ModuleCat.restrictScalars.{v} φ).obj N) := hN
    exact Module.Finite.of_injective ((ModuleCat.restrictScalars.{v} φ).map f).hom
      ((ModuleCat.mono_iff_injective f).1 hf)
  prop_of_epi {M N} f hf hM := by
    have : Module.Finite A ((ModuleCat.restrictScalars.{v} φ).obj M) := hM
    exact Module.Finite.of_surjective ((ModuleCat.restrictScalars.{v} φ).map f).hom
      ((ModuleCat.epi_iff_surjective f).1 hf)
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have : Module.Finite A ((ModuleCat.restrictScalars.{v} φ).obj S.X₁) := h₁
    have : Module.Finite A ((ModuleCat.restrictScalars.{v} φ).obj S.X₃) := h₃
    have hex : Function.Exact S.f.hom S.g.hom :=
      (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
    exact Module.Finite.of_exact (f := ((ModuleCat.restrictScalars.{v} φ).map S.f).hom)
      (g := ((ModuleCat.restrictScalars.{v} φ).map S.g).hom) hex hS.moduleCat_surjective_g

end Finite

/-! ### Canonical truncation of the columns of a double complex -/

section Truncation

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The canonical truncation `τ_{≤ m}` of cochain complexes preserves zero morphisms: the
truncation of a map is determined by its composite with the inclusion into the complex. -/
instance preservesZeroMorphisms_truncLEFunctor (m : ℤ) :
    ((embeddingUpIntLE m).truncLEFunctor C).PreservesZeroMorphisms where
  map_zero K L := by
    change HomologicalComplex.truncLEMap (0 : K ⟶ L) (embeddingUpIntLE m) = 0
    rw [← cancel_mono (L.ιTruncLE (embeddingUpIntLE m)), HomologicalComplex.ιTruncLE_naturality,
      comp_zero, zero_comp]

/-- **The total complex has no cohomology above `b + m`.** Let `B^{p,q}` be a double complex
whose columns `B^{p,•}` vanish for `p < a` and `p > b`, vanish in negative second degree, and
are exact in second degrees `> m`. Then `H^j(Tot B) = 0` for `j > b + m`. -/
theorem isZero_homology_total_of_exactAt
    (B : HomologicalComplex₂ C (up ℤ) (up ℤ)) [B.HasTotal (up ℤ)] (a b m : ℤ)
    (hpa : ∀ p, p < a → IsZero (B.X p)) (hpb : ∀ p, b < p → IsZero (B.X p))
    (hq : ∀ p q, q < 0 → IsZero ((B.X p).X q))
    (hex : ∀ p q, m < q → (B.X p).ExactAt q) (j : ℤ) (hj : b + m < j) :
    IsZero ((B.total (up ℤ)).homology j) := by
  let T : HomologicalComplex₂ C (up ℤ) (up ℤ) :=
    (((embeddingUpIntLE m).truncLEFunctor C).mapHomologicalComplex (up ℤ)).obj B
  let ι : T ⟶ B :=
    (NatTrans.mapHomologicalComplex ((embeddingUpIntLE m).ιTruncLENatTrans C) (up ℤ)).app B
  have hTX (p : ℤ) : T.X p = CochainComplex.truncLE (B.X p) m := rfl
  have hTzero (p : ℤ) (h : IsZero (B.X p)) : IsZero (T.X p) :=
    ((embeddingUpIntLE m).truncLEFunctor C).map_isZero h
  have hTq (p q : ℤ) (hq0 : q < 0) : IsZero ((T.X p).X q) := by
    rw [hTX]
    by_cases hqm : q ≤ m
    · exact IsZero.of_mono (HomologicalComplex.ιTruncLE (B.X p) (embeddingUpIntLE m) |>.f q)
        (hq p q hq0)
    · exact CochainComplex.isZero_of_isStrictlyLE _ m q (by lia)
  have : T.HasTotal (up ℤ) :=
    StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded T a hTq
      (fun p hp => hTzero p (hpa p hp))
  have hcol (p : ℤ) : QuasiIso (ι.f p) := by
    have : CochainComplex.IsLE (B.X p) m :=
      (CochainComplex.isLE_iff (B.X p) m).2 (fun i hi => hex p i hi)
    exact (CochainComplex.quasiIso_ιTruncLE_iff (B.X p) m).2 this
  have hqi : QuasiIso (HomologicalComplex₂.total.map ι (up ℤ)) :=
    StacksDraft.TotalComplexQuasiIso.quasiIso_total_map_of_lowerBound ι a 0 hTq
      (fun p hp => hTzero p (hpa p hp)) hq hpa hcol
  have hzero : IsZero ((T.total (up ℤ)).X j) := by
    refine StacksDraft.TotalComplexQuasiIso.isZero_cofan_pt _
      (T.toGradedObject.isColimitCofanMapObj _ j) (fun i => ?_)
    obtain ⟨⟨p, q⟩, hpq⟩ := i
    have hpq' : p + q = j := hpq
    by_cases hp : b < p
    · exact Functor.map_isZero (HomologicalComplex.eval C (up ℤ) q) (hTzero p (hpb p hp))
    · show IsZero ((CochainComplex.truncLE (B.X p) m).X q)
      exact CochainComplex.isZero_of_isStrictlyLE _ m q (by lia)
  exact (StacksDraft.TotalComplexQuasiIso.isZero_homology_of_isZero_X j hzero).of_iso
    (asIso (HomologicalComplex.homologyMap (HomologicalComplex₂.total.map ι (up ℤ)) j)).symm

end Truncation

end AlgebraicGeometry.DeRhamTypeComplex

end
