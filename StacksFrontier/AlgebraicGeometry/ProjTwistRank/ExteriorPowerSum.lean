module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerDegreeOne
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorProductRightExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafUnitSections
public import StacksFrontier.AlgebraicGeometry.ProjInvertibleLocus.Basic
public import StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.LocallyFree
public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TwistPowers

/-!
# The exterior powers of a finite direct sum of line bundles

Let `X` be a scheme and let `L₀, …, L_N` be sheaves of modules on it. The Künneth decomposition
of an exterior power of a direct sum identifies `⋀ⁿ(L₀ ⊕ ⋯ ⊕ L_N)` with
`⨁_{p + q = n} (⋀ᵖ L₀ ⊗ ⋀^q (L₁ ⊕ ⋯ ⊕ L_N))`, so an induction on the number of summands
decomposes an exterior power of a finite direct sum into tensor products of exterior powers of
the individual summands. When each `Lᵢ` is a line bundle only the exterior powers of degree `0`
and `1` survive — all higher ones vanish, a line bundle having rank one — and the decomposition
collapses to the two-term *Pascal recursion*

`⋀^{q+1}(L₀ ⊕ M) ≅ ⋀^{q+1} M ⊕ (L₀ ⊗ ⋀^q M)`,     `M = L₁ ⊕ ⋯ ⊕ L_N`,

whose solution for `N + 1` copies of one line bundle `L` is `binom(N + 1, p)` copies of `L^{⊗p}`.

This file proves the recursion. On `ℙⁿ_R = Proj R[T₀, …, Tₙ]` with `L = 𝒪(-1)` the three
remaining ingredients of the closed form are also proved here: the tensor product of two Serre
twists is their sum, `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)`; the structure sheaf is a unit for the tensor
product; and tensoring with a fixed sheaf distributes over a finite direct sum. Composing them
into `⋀^p(𝒪(-1)^{⊕(n+1)}) ≅ 𝒪(-p)^{⊕binom(n+1,p)}` is *not* done here.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistRank.coproductIsoBinaryOfIsZero`: a coproduct at most two of
  whose summands are nonzero is the binary biproduct of those two.
* `Stacks.AlgebraicGeometry.ProjTwistRank.biprodFinIso`: `a` copies of an object and `b` copies of
  it make `a + b` copies.
* `Stacks.AlgebraicGeometry.ProjTwistRank.tailIncl` and `tailProj`: the splitting of a finite
  biproduct `⨁_{i : Fin (N+1)} gᵢ` into its zeroth summand and the biproduct of the rest.
* `Stacks.AlgebraicGeometry.ProjTwistRank.exteriorPowerPeelIso`: the Künneth decomposition of
  `⋀ⁿ(⨁_{i : Fin (N+1)} gᵢ)` along that splitting.
* `Stacks.AlgebraicGeometry.ProjTwistRank.exteriorPowerSplitIso`: **the Pascal recursion.** If all
  exterior powers of the zeroth summand above degree one vanish, then
  `⋀^{q+1}(⨁_{i : Fin (N+1)} gᵢ) ≅ ⋀^{q+1}(⨁_{j : Fin N} g_{j+1}) ⊞ (g₀ ⊗ ⋀^q(⨁_{j} g_{j+1}))`.
* `Stacks.AlgebraicGeometry.ProjTwistRank.tensorBiproductIso`: tensoring with a fixed sheaf of
  modules distributes over a finite biproduct.
* `Stacks.AlgebraicGeometry.ProjTwistRank.tensorTwistingSheafIso`: `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` on
  `ℙⁿ_R`, at the tensor-product spelling the Künneth decomposition uses.
* `Stacks.AlgebraicGeometry.ProjTwistRank.unitTensorModuleIso`: `𝒪 ⊗ M ≅ M` at the same spelling.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistRank.tail_total`: the two projections and the two inclusions
  of the splitting add up to the identity, which is the hypothesis the Künneth comparison of
  `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf` consumes.
* `Stacks.AlgebraicGeometry.ProjTwistRank.isZero_tensorSheaf_of_isZero_left`: a tensor product
  with a zero left factor is zero.
* `Stacks.AlgebraicGeometry.ProjTwistRank.antidiagonalCases`: a pair of naturals summing to
  `q + 1` whose first entry is at most one is `(0, q + 1)` or `(1, q)`. This is what makes the
  Künneth sum collapse to two terms once the higher exterior powers of the zeroth summand vanish.

## Implementation notes

The ambient category is written
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)` throughout, rather than
`AlgebraicGeometry.Scheme.Modules Y`. That is the canonical description of the structure sheaf of
`Y` as a sheaf of rings, and it is the one `Stacks.SheafOfModules.Tensor.sheafTensor`,
`AlgebraicGeometry.SheafOfModules.algebras` and
`Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight` are stated over, so the exterior
powers, the Künneth summands and the distributivity isomorphism are all objects of one and the
same category.

`Stacks.SheafOfModules.Tensor.ringSheaf` is a plain definition, so instance search does not see
through it to the instances the library carries at other descriptions of the same sheaf of rings.
The three instances this file needs are therefore named at the canonical spelling, as the theorems
`hasFiniteBiproducts_ringSheaf`, `hasBinaryBiproducts_ringSheaf` and
`hasColimitsOfShape_discrete_ringSheaf` below, and declared local instances: the first two are the
finite and binary biproducts of an additive category with the corresponding products, and the
third is `Stacks.SheafOfModules.FlatCoproduct.hasColimitsOfShape_discrete`, which is what the
coproduct over the antidiagonal index set of the Künneth decomposition needs. The library's
universally quantified biproduct and colimit instances cannot be used in their place: they are
stated for `SheafOfModules.{max u v}`, and `max ?u ?v =?= u` is not a constraint the universe
unifier solves, so instance search never applies them to a category of sheaves of modules in a
single universe.

Two uses are not served by those local instances and pass what they need explicitly instead. The
exterior powers of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerProdSheaf` are
valued in the `CategoryTheory.Sheaf.toRingCat` description of the same sheaf of rings, so an
expression whose ambient category is read off one of them lands at that description and the
instances above do not reach it. A type ascription on the object does not help: the ambient
category of an application is taken from the *inferred* type of the argument, not from the
ascription. So the binary biproduct of `exteriorPowerSplitIso` names its category and supplies its
`CategoryTheory.Limits.HasBinaryBiproduct` as a term, and the two biproducts of
`tensorBiproductIso` name their category as `CategoryTheory.Limits.biproduct (C := ...)`, where it
is otherwise fixed by the functor the biproduct is fed to.

`Stacks.AlgebraicGeometry.ProjTwistRank.tail_total` is proved with `simp only` and not with
`rw`: the identity `𝟙 (⨁ g)` on the right makes `rw [Category.comp_id]` attempt
`biproduct.π g 0 ≫ biproduct.ι g 0 =?= 𝟙 ?X`, and that unification exhausts the heartbeat budget
in this category, whereas `simp only` discriminates on the head symbol and never tries it.

## References

* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01MT](https://stacks.math.columbia.edu/tag/01MT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.AlgebraicGeometry.ProjTwistRank

open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization
open AlgebraicGeometry.ProjectiveSpectrum.Proj

/-! ### The instances of the ambient category -/

/-- Finite biproducts in the category of sheaves of modules on a scheme, at the canonical
`Stacks.SheafOfModules.Tensor.ringSheaf` spelling of its structure sheaf: a category of sheaves of
modules is additive and has finite products. -/
theorem hasFiniteBiproducts_ringSheaf (Y : Scheme.{u}) :
    HasFiniteBiproducts (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Binary biproducts in the same category, for the same reason. -/
theorem hasBinaryBiproducts_ringSheaf (Y : Scheme.{u}) :
    HasBinaryBiproducts (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) :=
  HasBinaryBiproducts.of_hasBinaryProducts

attribute [local instance] hasFiniteBiproducts_ringSheaf

/-- Coproducts indexed by a type in the universe of the space, in the same category. The index set
of the Künneth decomposition is an antidiagonal lifted into that universe, so the coproduct over it
needs this and not just finite biproducts. -/
theorem hasColimitsOfShape_discrete_ringSheaf (Y : Scheme.{u}) (ι : Type u) :
    HasColimitsOfShape (Discrete ι) (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) :=
  Stacks.SheafOfModules.FlatCoproduct.hasColimitsOfShape_discrete
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) ι

/-! ### Coproducts with at most two nonzero summands -/

section Coproducts

variable {C : Type*} [Category C] [HasZeroMorphisms C]

/-- **A coproduct at most two of whose summands are nonzero is the binary biproduct of those
two.** The comparison is the pair of the two inclusions; its inverse sends the two distinguished
summands to the two legs of the biproduct and every other summand to zero. -/
def coproductIsoBinaryOfIsZero {I : Type*} [DecidableEq I] (g : I → C) (i₀ i₁ : I)
    (hne : i₀ ≠ i₁) (hz : ∀ i, i ≠ i₀ → i ≠ i₁ → IsZero (g i))
    [HasCoproduct g] [HasBinaryBiproduct (g i₀) (g i₁)] :
    (g i₀ ⊞ g i₁) ≅ ∐ g where
  hom := biprod.desc (Sigma.ι g i₀) (Sigma.ι g i₁)
  inv := Sigma.desc fun i =>
    if h : i = i₀ then eqToHom (congrArg g h) ≫ biprod.inl
    else if h' : i = i₁ then eqToHom (congrArg g h') ≫ biprod.inr else 0
  hom_inv_id := by
    refine biprod.hom_ext' _ _ ?_ ?_
    · rw [biprod.inl_desc_assoc, Sigma.ι_comp_desc, dite_eq_left_of_eq_true (eq_true rfl),
        eqToHom_refl, Category.id_comp, Category.comp_id]
    · rw [biprod.inr_desc_assoc, Sigma.ι_comp_desc,
        dite_eq_right_of_eq_false (eq_false (Ne.symm hne)),
        dite_eq_left_of_eq_true (eq_true rfl), eqToHom_refl, Category.id_comp,
        Category.comp_id]
  inv_hom_id := by
    refine Sigma.hom_ext _ _ fun i => ?_
    by_cases h : i = i₀
    · subst h
      rw [Sigma.ι_comp_desc_assoc, Category.comp_id, dite_eq_left_of_eq_true (eq_true rfl),
        Category.assoc, biprod.inl_desc, eqToHom_refl, Category.id_comp]
    · by_cases h' : i = i₁
      · subst h'
        rw [Sigma.ι_comp_desc_assoc, Category.comp_id, dite_eq_right_of_eq_false (eq_false h),
          dite_eq_left_of_eq_true (eq_true rfl), Category.assoc, biprod.inr_desc, eqToHom_refl,
          Category.id_comp]
      · rw [Sigma.ι_comp_desc_assoc, Category.comp_id, dite_eq_right_of_eq_false (eq_false h),
          dite_eq_right_of_eq_false (eq_false h'), zero_comp]
        exact ((hz i h h').eq_of_src _ _).symm

end Coproducts

/-! ### Biproducts of a constant family -/

section ConstantFamilies

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasFiniteBiproducts C]
  [HasBinaryBiproducts C]

/-- **`a` copies of an object together with `b` copies of it make `a + b` copies**: the
biproduct of the two blocks, indexed by `Fin a` and `Fin b`, is the biproduct indexed by
`Fin (a + b)`, the two blocks sitting in the two halves of `Fin.addCases`. -/
def biprodFinIso (L : C) (a b : ℕ) :
    ((⨁ fun _ : Fin a => L) ⊞ ⨁ fun _ : Fin b => L) ≅ ⨁ fun _ : Fin (a + b) => L where
  hom := biprod.desc
    (biproduct.desc fun i => biproduct.ι (fun _ : Fin (a + b) => L) (Fin.castAdd b i))
    (biproduct.desc fun j => biproduct.ι (fun _ : Fin (a + b) => L) (Fin.natAdd a j))
  inv := biproduct.desc fun k => Fin.addCases
    (fun i => biproduct.ι (fun _ : Fin a => L) i ≫ biprod.inl)
    (fun j => biproduct.ι (fun _ : Fin b => L) j ≫ biprod.inr) k
  hom_inv_id := by
    refine biprod.hom_ext' _ _ (biproduct.hom_ext' _ _ fun i => ?_)
      (biproduct.hom_ext' _ _ fun j => ?_)
    · simp only [biprod.inl_desc_assoc, biproduct.ι_desc_assoc, biproduct.ι_desc,
        Fin.addCases_left, Category.comp_id]
    · simp only [biprod.inr_desc_assoc, biproduct.ι_desc_assoc, biproduct.ι_desc,
        Fin.addCases_right, Category.comp_id]
  inv_hom_id := by
    refine biproduct.hom_ext' _ _ fun k => ?_
    induction k using Fin.addCases with
    | left i =>
      simp only [Category.assoc, biproduct.ι_desc_assoc, Fin.addCases_left, Category.comp_id,
        biprod.inl_desc, biproduct.ι_desc]
    | right j =>
      simp only [Category.assoc, biproduct.ι_desc_assoc, Fin.addCases_right, Category.comp_id,
        biprod.inr_desc, biproduct.ι_desc]

end ConstantFamilies

/-! ### Peeling the zeroth summand off a finite direct sum -/

section Splitting

variable {Y : Scheme.{u}} {N : ℕ}
  (g : Fin (N + 1) → SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))

/-- The direct sum of all but the zeroth member of a family of `N + 1` sheaves of modules. -/
abbrev tailSum : SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf) := ⨁ fun j : Fin N => g j.succ

/-- The inclusion `⨁_{j : Fin N} g_{j+1} ⟶ ⨁_{i : Fin (N+1)} gᵢ` of the tail. -/
def tailIncl : tailSum g ⟶ ⨁ g := biproduct.desc fun j => biproduct.ι g j.succ

/-- The projection `⨁_{i : Fin (N+1)} gᵢ ⟶ ⨁_{j : Fin N} g_{j+1}` onto the tail. -/
def tailProj : (⨁ g) ⟶ tailSum g := biproduct.lift fun j => biproduct.π g j.succ

/-- The tail projection sends the `(j+1)`-st summand to the `j`-th summand of the tail. -/
private theorem succ_comp_tailProj (j : Fin N) :
    biproduct.ι g j.succ ≫ tailProj g = biproduct.ι (fun j : Fin N => g j.succ) j := by
  refine biproduct.hom_ext _ _ fun j' => ?_
  simp [tailProj, biproduct.ι_π, Fin.succ_inj]

/-- The tail inclusion is split by the tail projection. -/
theorem tailIncl_tailProj : tailIncl g ≫ tailProj g = 𝟙 _ := by
  refine biproduct.hom_ext' _ _ fun j => ?_
  simp [tailIncl, succ_comp_tailProj]

/-- The zeroth summand is annihilated by the tail projection. -/
theorem head_tailProj : biproduct.ι g 0 ≫ tailProj g = 0 := by
  refine biproduct.hom_ext _ _ fun j => ?_
  simp [tailProj, (Fin.succ_ne_zero j).symm]

/-- The tail is annihilated by the projection onto the zeroth summand. -/
theorem tailIncl_head : tailIncl g ≫ biproduct.π g 0 = 0 := by
  refine biproduct.hom_ext' _ _ fun j => ?_
  simp [tailIncl, Fin.succ_ne_zero j]

/-- **The zeroth summand and the tail exhaust `⨁_{i : Fin (N+1)} gᵢ`**: the two composites
`project then include` add up to the identity. With the three preceding lemmas this is the
splitting datum the Künneth decomposition of an exterior power consumes. -/
theorem tail_total :
    biproduct.π g 0 ≫ biproduct.ι g 0 + tailProj g ≫ tailIncl g = 𝟙 (⨁ g) := by
  refine biproduct.hom_ext' _ _ fun i => ?_
  induction i using Fin.cases with
  | zero =>
    simp only [Preadditive.comp_add, Category.comp_id, ← Category.assoc, biproduct.ι_π_self,
      Category.id_comp, head_tailProj, zero_comp, add_zero]
  | succ j =>
    simp only [Preadditive.comp_add, Category.comp_id, ← Category.assoc,
      biproduct.ι_π_ne g (Fin.succ_ne_zero j), succ_comp_tailProj, zero_comp, zero_add, tailIncl,
      biproduct.ι_desc]

end Splitting

/-! ### The Künneth decomposition along the splitting -/

section Kunneth

attribute [local instance] hasColimitsOfShape_discrete_ringSheaf

variable {Y : Scheme.{u}} {N : ℕ}
  (g : Fin (N + 1) → SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))

/-- **The Künneth decomposition of `⋀ⁿ(⨁_{i : Fin (N+1)} gᵢ)` along the splitting into the zeroth
summand and the tail**: `⨁_{p + q = n} (⋀ᵖ g₀ ⊗ ⋀^q (⨁_{j} g_{j+1})) ≅ ⋀ⁿ(⨁_i gᵢ)`. -/
def exteriorPowerPeelIso (p : ℕ) :
    (∐ SheafOfModules.exteriorPowerProdSummand (SheafOfModules.algebras _ (g 0))
        (SheafOfModules.algebras _ (tailSum g)) p) ≅
      (SheafOfModules.algebras _ (⨁ g)).exteriorPower p :=
  @asIso _ _ _ _
    (SheafOfModules.exteriorPowerProdHom (SheafOfModules.algebras _ (g 0))
      (SheafOfModules.algebras _ (tailSum g)) (SheafOfModules.algebras _ (⨁ g))
      (biproduct.ι g 0) (tailIncl g) p)
    (SheafOfModules.isIso_exteriorPowerProdHom (SheafOfModules.algebras _ (g 0))
      (SheafOfModules.algebras _ (tailSum g)) (SheafOfModules.algebras _ (⨁ g))
      (biproduct.ι g 0) (biproduct.π g 0) (tailIncl g) (tailProj g)
      (biproduct.ι_π_self g 0) (tailIncl_tailProj g) (head_tailProj g) (tailIncl_head g)
      (tail_total g) p)

end Kunneth

/-! ### The summands that vanish -/

/-- **A tensor product of sheaves of modules with a zero left factor is zero**: tensoring with a
fixed right factor preserves zero morphisms, hence zero objects. -/
theorem isZero_tensorSheaf_of_isZero_left {Y : Scheme.{u}}
    {A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)}
    (h : IsZero A) :
    IsZero (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj A).obj B) := by
  have := Stacks.SheafOfModules.TensorLocalProperties.preservesZeroMorphisms_tensorSheafLeft
    (Opens.grothendieckTopology ↥Y) Y.sheaf B
  exact (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafLeft
    (Opens.grothendieckTopology ↥Y) Y.sheaf B).map_isZero h

/-- **A pair of naturals summing to `q + 1` whose first entry is at most one is `(0, q + 1)` or
`(1, q)`.** The index set of the Künneth decomposition in degree `q + 1` is this antidiagonal,
lifted into the universe of the space, so once the exterior powers of the zeroth summand above
degree one vanish only these two summands remain. -/
theorem antidiagonalCases (q : ℕ) (i : ULift.{u} {pq : ℕ × ℕ // pq.1 + pq.2 = q + 1})
    (h : i.down.1.1 ≤ 1) :
    i = ULift.up ⟨(0, q + 1), Nat.zero_add _⟩ ∨
      i = ULift.up ⟨(1, q), Nat.add_comm 1 q⟩ := by
  obtain ⟨⟨⟨a, b⟩, hab⟩⟩ := i
  simp only at h hab
  interval_cases a
  · have hb : b = q + 1 := by omega
    subst hb
    exact Or.inl rfl
  · have hb : b = q := by omega
    subst hb
    exact Or.inr rfl

/-! ### The Pascal recursion -/

section PascalStep

attribute [local instance] hasColimitsOfShape_discrete_ringSheaf
  hasBinaryBiproducts_ringSheaf

variable {Y : Scheme.{u}} {N : ℕ}
  (g : Fin (N + 1) → SheafOfModules.{u}
    (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))

/-- The `(0, q + 1)` summand of the Künneth decomposition is `⋀^{q+1}` of the tail: the zeroth
exterior power of the zeroth summand is the structure sheaf, which is a unit for the tensor
product. -/
def peelSummandZeroIso (q : ℕ) :
    SheafOfModules.exteriorPowerProdSummand (SheafOfModules.algebras _ (g 0))
        (SheafOfModules.algebras _ (tailSum g)) (q + 1)
        (ULift.up ⟨(0, q + 1), Nat.zero_add _⟩) ≅
      (SheafOfModules.algebras _ (tailSum g)).exteriorPower (q + 1) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).mapIso
      (SheafOfModules.algebras _ (g 0)).exteriorPieceZeroIsoUnit).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj _).mapIso
        (Iso.refl _)) ≪≫
    AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso Y.toRingedSpace _

/-- The `(1, q)` summand of the Künneth decomposition is `g₀ ⊗ ⋀^q` of the tail: nothing is
divided out of an exterior algebra in degree one, so `⋀¹ g₀` is `g₀`. -/
def peelSummandOneIso (q : ℕ) :
    SheafOfModules.exteriorPowerProdSummand (SheafOfModules.algebras _ (g 0))
        (SheafOfModules.algebras _ (tailSum g)) (q + 1)
        (ULift.up ⟨(1, q), Nat.add_comm 1 q⟩) ≅
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj (g 0)).obj
        ((SheafOfModules.algebras _ (tailSum g)).exteriorPower q) :=
  (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).mapIso
      (SheafOfModules.algebras _ (g 0)).exteriorPowerOneIso).app _ ≪≫
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj _).mapIso
        (Iso.refl _))

/-- **The Pascal recursion for the exterior powers of a finite direct sum.** If every exterior
power of the zeroth summand above degree one vanishes — as it does when that summand is a line
bundle — then the Künneth sum over the antidiagonal of `q + 1` has only the two terms `(0, q + 1)`
and `(1, q)`, and

`⋀^{q+1}(⨁_{i : Fin (N+1)} gᵢ) ≅ ⋀^{q+1}(⨁_{j : Fin N} g_{j+1}) ⊞ (g₀ ⊗ ⋀^q(⨁_j g_{j+1}))`. -/
def exteriorPowerSplitIso
    (hg : ∀ q : ℕ, 1 < q → IsZero ((SheafOfModules.algebras _ (g 0)).exteriorPower q)) (q : ℕ) :
    (@biprod (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) _ _
        ((SheafOfModules.algebras _ (tailSum g)).exteriorPower (q + 1))
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj (g 0)).obj
          ((SheafOfModules.algebras _ (tailSum g)).exteriorPower q))
        (HasBinaryBiproducts.has_binary_biproduct _ _)) ≅
      (SheafOfModules.algebras _ (⨁ g)).exteriorPower (q + 1) :=
  @biprod.mapIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) _ _
      _ _ _ _ (HasBinaryBiproducts.has_binary_biproduct _ _)
      (HasBinaryBiproducts.has_binary_biproduct _ _)
      (peelSummandZeroIso g q).symm (peelSummandOneIso g q).symm ≪≫
    coproductIsoBinaryOfIsZero
      (SheafOfModules.exteriorPowerProdSummand (SheafOfModules.algebras _ (g 0))
        (SheafOfModules.algebras _ (tailSum g)) (q + 1))
      (ULift.up ⟨(0, q + 1), Nat.zero_add _⟩) (ULift.up ⟨(1, q), Nat.add_comm 1 q⟩)
      (fun h => Nat.zero_ne_one
        (congrArg (fun i : ULift.{u} {pq : ℕ × ℕ // pq.1 + pq.2 = q + 1} => i.down.1.1) h))
      (fun i h0 h1 => by
        rcases Nat.lt_or_ge 1 i.down.1.1 with hlt | hle
        · exact isZero_tensorSheaf_of_isZero_left (hg _ hlt)
        · rcases antidiagonalCases q i hle with rfl | rfl
          · exact absurd rfl h0
          · exact absurd rfl h1) ≪≫
    exteriorPowerPeelIso g (q + 1)

end PascalStep

/-! ### Collapsing the surviving summands -/

section Distrib

variable {Y : Scheme.{u}}

/-- **Tensoring with a fixed sheaf of modules distributes over a finite direct sum**:
`F ⊗ ⨁_i gᵢ ≅ ⨁_i (F ⊗ gᵢ)`, because the tensor product preserves colimits in each variable. -/
def tensorBiproductIso
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) {k : ℕ}
    (g : Fin k → SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj F).obj
        (biproduct (C := SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf)) g) ≅
      biproduct (C := SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
        fun i =>
          ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj F).obj (g i) :=
  haveI := Stacks.SheafOfModules.TensorLocalProperties.preservesColimits_tensorSheafRight
    (Opens.grothendieckTopology ↥Y) Y.sheaf F
  haveI : PreservesColimitsOfSize.{0, 0}
      (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
        (Opens.grothendieckTopology ↥Y) Y.sheaf F) :=
    preservesColimitsOfSize_shrink.{0, u, 0, u} _
  (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
      (Opens.grothendieckTopology ↥Y) Y.sheaf F).mapIso (biproduct.isoCoproduct g) ≪≫
    PreservesCoproduct.iso (Stacks.SheafOfModules.TensorLocalProperties.tensorSheafRight
      (Opens.grothendieckTopology ↥Y) Y.sheaf F) g ≪≫
    (biproduct.isoCoproduct (C := SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.sheaf))
      fun i =>
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.sheaf).obj F).obj (g i)).symm

end Distrib

section Twists

variable (R : Type u) [CommRing R] (n : ℕ)

/-- **`𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` on `ℙⁿ_R`**, at the tensor product the Künneth summands are
written with. Multiplication of twists is an isomorphism because `R[T₀, …, Tₙ]` is generated in
degree one over `R`. -/
def tensorTwistingSheafIso (a b : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ((_root_.AlgebraicGeometry.Proj (polyGrading R
      n)).sheaf)).obj (twistingSheaf (polyGrading R n) a)).obj (twistingSheaf (polyGrading R n) b) ≅
      twistingSheaf (polyGrading R n) (a + b) :=
  @asIso _ _ _ _ (Stacks.AlgebraicGeometry.ProjInvertibleLocus.twistMultiplicationMap
      (polyGrading R n) a b)
    (Stacks.AlgebraicGeometry.ProjRepresentsF1.isIso_twistMultiplicationMap_of_adjoin
      (polyGrading R n)
      (Stacks.AlgebraicGeometry.ProjKoszulComplex.adjoin_degree_one_polyGrading R n) a b)

/-- **`𝒪 ⊗ M ≅ M` on `ℙⁿ_R`**, at the tensor product the Künneth summands are written with: the
structure sheaf is a unit for the tensor product of sheaves of modules. -/
def unitTensorModuleIso (M : (_root_.AlgebraicGeometry.Proj (polyGrading R n)).Modules) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ((_root_.AlgebraicGeometry.Proj (polyGrading R
      n)).sheaf)).obj (_root_.SheafOfModules.unit
          (_root_.AlgebraicGeometry.Proj (polyGrading R n)).ringCatSheaf)).obj M ≅ M :=
  AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso
    (_root_.AlgebraicGeometry.Proj (polyGrading R n)).toRingedSpace M

end Twists

end Stacks.AlgebraicGeometry.ProjTwistRank

end
