module

public import StacksFrontier.Deformation.Examples.Linear.SquareZeroFirstOrderPart
public import StacksFrontier.RingTheory.GradedAlgebra.WeightedHomogeneousPresentation

/-!
# The first-order class of a graded deformation in the cokernel of the Jacobian

Let `P` be a graded `k`-algebra with grading `𝒜`, let

`k[X_i] ⟶ P`,  `X_i ↦ x_i ∈ 𝒜 (d i)`,  relations `F_j` of degree `e j`

be a weighted-homogeneous presentation of it, and let `W` be the cokernel of the graded Jacobian
of that presentation. Let `A` be a square-zero thickening of `k` — a `k`-algebra with a
retraction `A → k` whose kernel `I` is square zero — identified with a `k`-module `V` through
`I ≃ₗ[k] V`, and let `Q` be a *deformation* of `P` over `A`: a graded `A`-algebra, degreewise
flat, whose reduction along the retraction is `P` degree by degree.

Lifting the generators `x_i` to homogeneous elements `y_i` of `Q` of the same degree, the
relations no longer vanish: `F_j(y)` is only known to reduce to `F_j(x) = 0`, so it is an
element of the kernel of `Q_{e j} → P_{e j}`. Its first-order part is therefore an element of
`I ⊗[k] 𝒜 (e j)`, and reading `I` as `V` and collecting over `j` gives an element of `W ⊗[k] V`:
the *first-order class of the lifted presentation*.

This file constructs that class and proves it compatible with morphisms of deformations: a map
of deformations over a map of thickenings carries the class of a lifted presentation to the
class of the image lifted presentation. All of the work is in
`StacksFrontier.Deformation.Examples.Linear.SquareZeroFirstOrderPart`; what is added here is that
the value of a relation at lifted generators is homogeneous of the right degree and does lie in
the kernel, and the `k`-linear comparison of the receptacle `I ⊗[k] 𝒜 (e j)` of one relation
with `W ⊗[k] V`.

## Main definitions

* `GradedDeformation.gradedPiece`: the degreewise reduction `Q_d → P_d` of a deformation.
* `GradedDeformation.relationFirstOrderPart`: the first-order part of the value of one relation
  at lifted generators, an element of `I ⊗[k] 𝒜 (e j)`.
* `GradedDeformation.relationComponent`: the `k`-linear comparison of that receptacle with
  `W ⊗[k] V`.
* `GradedDeformation.firstOrderClass`: the first-order class of a lifted presentation, an
  element of `W ⊗[k] V`.

## Main results

* `GradedDeformation.map_algebraMap`: the reduction of a deformation is a `k`-algebra map. This
  is what makes a polynomial identity over `k` transportable between `Q` and `P`, and it is
  available only because the base is a `k`-algebra — the retraction is what provides the
  `k`-algebra structure on `Q`.
* `GradedDeformation.aeval_relation_mem` and `GradedDeformation.gradedPiece_aeval_relation`: the
  value of a relation at lifted generators is homogeneous of the degree of the relation and is
  killed by the reduction.
* `GradedDeformation.relationComponent_rTensor`: the comparison with `W ⊗[k] V` is natural in
  the thickening.
* `GradedDeformation.firstOrderClass_map`: a morphism of deformations over a morphism of
  thickenings carries the first-order class of a lifted presentation to that of its image.

## Implementation notes

A deformation is not bundled into a structure: it is a list of instance binders (`Algebra A Q`,
`GradedAlgebra 𝒬`, degreewise `Module.Flat`) together with the reduction `Q →+* P` and its three
properties as explicit hypotheses. Every module structure occurring in a statement — the
`k`-module structures on `Q_d`, on `P_d`, on `I` and on the kernels, and the `A`-module
structure on `P_d` — is then found by instance search, and no statement needs a `letI` prefix.
A caller holding a deformation as a structure supplies the binders once and uses the statements
as they stand.

The homogeneity of the value of a relation is proved against the grading
`fun d ↦ (𝒬 d).restrictScalars k` rather than `𝒬` itself: the relations are polynomials over
`k`, so `MvPolynomial.aeval_mem_of_isWeightedHomogeneous` is applied with `k` as the base ring,
and the two gradings have the same members.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public section

open MvPolynomial TensorProduct

namespace GradedDeformation

universe w u u₂ v v₁ v₂ t t₂ x y

/-! ### The degreewise reduction of a deformation -/

section Deformation

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {P : Type v} [CommRing P] [Algebra k P] [Module A P] [IsScalarTower A k P]
  {𝒜 : ℕ → Submodule k P}
  {Q : Type t} [CommRing Q] [Algebra A Q] [Algebra k Q] [IsScalarTower k A Q]
  {𝒬 : ℕ → Submodule A Q}
  (red : Q →+* P)

/-- The reduction of a deformation, restricted to the `d`-th graded piece. -/
def gradedPiece (hsmul : ∀ (a : A) (q : Q), red (a • q) = algebraMap A k a • red q)
    (hmem : ∀ (d : ℕ) (q : Q), q ∈ 𝒬 d → red q ∈ 𝒜 d) (d : ℕ) :
    ↥(𝒬 d) →ₗ[A] ↥(𝒜 d) where
  toFun q := ⟨red (q : Q), hmem d (q : Q) q.2⟩
  map_add' x z := Subtype.ext (map_add red (x : Q) (z : Q))
  map_smul' a q := by
    apply Subtype.ext
    change red (a • (q : Q)) = a • (red (q : Q))
    rw [hsmul, IsScalarTower.algebraMap_smul]

omit [Algebra k A] [Algebra k Q] [IsScalarTower k A Q] in
/-- The degreewise reduction is the reduction. -/
@[simp]
theorem coe_gradedPiece
    (hsmul : ∀ (a : A) (q : Q), red (a • q) = algebraMap A k a • red q)
    (hmem : ∀ (d : ℕ) (q : Q), q ∈ 𝒬 d → red q ∈ 𝒜 d) (d : ℕ) (q : ↥(𝒬 d)) :
    (gradedPiece red hsmul hmem d q : P) = red (q : Q) := rfl

/-- The image of `r : k` in `Q` is `r` acting through `A` on `1`. -/
private theorem algebraMap_eq_algebraMap_smul_one {k A Q : Type*} [CommRing k] [CommRing A]
    [CommRing Q] [Algebra k A] [Algebra A Q] [Algebra k Q] [IsScalarTower k A Q] (r : k) :
    algebraMap k Q r = algebraMap k A r • (1 : Q) := by
  rw [algebraMap_smul, Algebra.algebraMap_eq_smul_one]

omit [Module A P] [IsScalarTower A k P] in
/-- The reduction of a deformation over a square-zero thickening retracting onto `k` is a
`k`-algebra map: the `k`-algebra structure of the base is what makes a polynomial identity over
`k` transportable between a deformation and its special fibre. -/
theorem map_algebraMap (hsmul : ∀ (a : A) (q : Q), red (a • q) = algebraMap A k a • red q)
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r) (r : k) :
    red (algebraMap k Q r) = algebraMap k P r := by
  rw [algebraMap_eq_algebraMap_smul_one (A := A), hsmul, map_one, hret, Algebra.smul_def, mul_one]

/-- The reduction of a deformation as a `k`-algebra map. -/
def mapAlgHom (hsmul : ∀ (a : A) (q : Q), red (a • q) = algebraMap A k a • red q)
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r) : Q →ₐ[k] P :=
  { red with commutes' := map_algebraMap red hsmul hret }

omit [Module A P] [IsScalarTower A k P] in
/-- The reduction as a `k`-algebra map is the reduction. -/
@[simp]
theorem mapAlgHom_apply
    (hsmul : ∀ (a : A) (q : Q), red (a • q) = algebraMap A k a • red q)
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r) (q : Q) :
    mapAlgHom red hsmul hret q = red q := rfl

omit [Algebra A k] in
/-- The graded pieces of a graded algebra over `A`, as a grading by `k`-submodules. This is the
grading against which a polynomial with coefficients in `k` is evaluated. -/
theorem gradedMonoid_restrictScalars (𝒬 : ℕ → Submodule A Q) [SetLike.GradedMonoid 𝒬] :
    SetLike.GradedMonoid fun d ↦ (𝒬 d).restrictScalars k where
  one_mem := SetLike.one_mem_graded 𝒬
  mul_mem {_ _ _ _} hx hz := SetLike.mul_mem_graded (A := 𝒬) hx hz

end Deformation

/-! ### The first-order part of a relation at lifted generators -/

section Relation

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {P : Type v} [CommRing P] [Algebra k P] [Module A P] [IsScalarTower A k P]
  {𝒜 : ℕ → Submodule k P} [GradedAlgebra 𝒜]
  {Q : Type t} [CommRing Q] [Algebra A Q] [Algebra k Q] [IsScalarTower k A Q]
  {𝒬 : ℕ → Submodule A Q} [GradedAlgebra 𝒬] [∀ d, Module.Flat A ↥(𝒬 d)]
  {red : Q →+* P}
  {hsmul : ∀ (a : A) (q : Q), red (a • q) = algebraMap A k a • red q}
  {hmem : ∀ (d : ℕ) (q : Q), q ∈ 𝒬 d → red q ∈ 𝒜 d}
  {ι : Type x} {σ : Type y}
  (pres : Algebra.WeightedHomogeneousPresentation k P 𝒜 ι σ)
  {yl : ι → Q}

omit [Algebra A k] [Module A P] [IsScalarTower A k P] [GradedAlgebra 𝒜]
  [∀ d, Module.Flat A ↥(𝒬 d)] in
/-- The value of a relation at homogeneous lifts of the chosen generators is homogeneous of the
degree of the relation. -/
theorem aeval_relation_mem (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (j : σ) :
    aeval yl (pres.relation j) ∈ 𝒬 (pres.relDegree j) := by
  have := gradedMonoid_restrictScalars (k := k) 𝒬
  exact aeval_mem_of_isWeightedHomogeneous (fun d ↦ (𝒬 d).restrictScalars k) yl
    pres.varDegree hyd (pres.relation_isWeightedHomogeneous j)

omit [GradedAlgebra 𝒜] [∀ d, Module.Flat A ↥(𝒬 d)] in
/-- The value of a relation at lifts of the chosen generators is killed by the reduction: it
reduces to the value of the relation at the generators themselves, which is zero. -/
theorem gradedPiece_aeval_relation
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i) (j : σ) :
    gradedPiece red hsmul hmem (pres.relDegree j)
        ⟨aeval yl (pres.relation j), aeval_relation_mem pres hyd j⟩ = 0 := by
  apply Subtype.ext
  have hcomp : mapAlgHom red hsmul hret (aeval yl (pres.relation j)) =
      aeval (fun i ↦ mapAlgHom red hsmul hret (yl i)) (pres.relation j) :=
    comp_aeval_apply (f := yl) (mapAlgHom red hsmul hret) (pres.relation j)
  have hval : (fun i ↦ mapAlgHom red hsmul hret (yl i)) = pres.val := funext hy
  change mapAlgHom red hsmul hret (aeval yl (pres.relation j)) = 0
  rw [hcomp, hval, pres.aeval_val_relation j]

/-- The first-order part of the value of one relation at lifted generators: the element of
`I ⊗[k] 𝒜 (e j)` whose image in `Q` is the discrepancy `F_j(y)`. -/
noncomputable def relationFirstOrderPart
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d))
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i) (j : σ) :
    ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 (pres.relDegree j)) :=
  SquareZeroRetraction.firstOrderPart hret hsq (hbc (pres.relDegree j))
    (gradedPiece_aeval_relation pres hret hyd hy j)

end Relation

/-! ### The receptacle: the cokernel of the Jacobian, tensored with the thickening module -/

section Receptacle

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {B : Type u₂} [CommRing B] [Algebra k B] [Algebra B k]
  {P : Type v} [CommRing P] [Algebra k P]
  {𝒜 : ℕ → Submodule k P} [GradedAlgebra 𝒜]
  {V : Type t} [AddCommGroup V] [Module k V]
  {V' : Type t₂} [AddCommGroup V'] [Module k V']
  {ι : Type x} [Fintype ι] {σ : Type y} [DecidableEq σ]
  (pres : Algebra.WeightedHomogeneousPresentation k P 𝒜 ι σ)

/-- The comparison of the receptacle of one relation with the cokernel of the Jacobian tensored
with the thickening module: read the square-zero ideal as `V`, place the graded piece in the
`j`-th coordinate of the target of the Jacobian, and pass to the cokernel.

The cokernel is what makes the class independent of the chosen lifts: changing the lifts changes
the collected first-order parts by the Jacobian of the perturbation. -/
noncomputable def relationComponent
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V) (j : σ) :
    ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 (pres.relDegree j)) →ₗ[k]
      pres.jacobianCokernel ⊗[k] V :=
  LinearMap.rTensor V (LinearMap.range pres.jacobian).mkQ ∘ₗ
    LinearMap.rTensor V (LinearMap.single k (fun j ↦ ↥(𝒜 (pres.relDegree j))) j) ∘ₗ
      (TensorProduct.congr (LinearEquiv.refl k ↥(𝒜 (pres.relDegree j))) eV).toLinearMap ∘ₗ
        (TensorProduct.comm k ↥(RingHom.ker (algebraMap A k))
          ↥(𝒜 (pres.relDegree j))).toLinearMap

/-- The comparison on a generator. -/
@[simp]
theorem relationComponent_tmul (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V) (j : σ)
    (i : ↥(RingHom.ker (algebraMap A k))) (p : ↥(𝒜 (pres.relDegree j))) :
    relationComponent pres eV j (i ⊗ₜ[k] p) =
      (LinearMap.range pres.jacobian).mkQ
        (LinearMap.single k (fun j ↦ ↥(𝒜 (pres.relDegree j))) j p) ⊗ₜ[k] eV i := rfl

/-- The comparison with the cokernel of the Jacobian is natural in the thickening: a map of
square-zero ideals compatible with the two identifications with `V` and `V'` commutes with
it. -/
theorem relationComponent_rTensor
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V)
    (eV' : ↥(RingHom.ker (algebraMap B k)) ≃ₗ[k] V')
    (φ : A →ₐ[k] B) (hφ : ∀ a : A, algebraMap B k (φ a) = algebraMap A k a)
    (f : V →ₗ[k] V')
    (hf : ∀ i, eV' (SquareZeroRetraction.kerMap φ hφ i) = f (eV i)) (j : σ)
    (t : ↥(RingHom.ker (algebraMap A k)) ⊗[k] ↥(𝒜 (pres.relDegree j))) :
    relationComponent pres eV' j
        (LinearMap.rTensor ↥(𝒜 (pres.relDegree j)) (SquareZeroRetraction.kerMap φ hφ) t) =
      LinearMap.lTensor pres.jacobianCokernel f (relationComponent pres eV j t) := by
  induction t using TensorProduct.inductionOn with
  | tmul i p =>
      rw [LinearMap.rTensor_tmul, relationComponent_tmul, relationComponent_tmul,
        LinearMap.lTensor_tmul, hf]
  | add z z' hz hz' => simp only [map_add, hz, hz']

end Receptacle

/-! ### The first-order class of a lifted presentation -/

section Class

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {B : Type u₂} [CommRing B] [Algebra k B] [Algebra B k]
  {P : Type v} [CommRing P] [Algebra k P] [Module A P] [IsScalarTower A k P]
  {𝒜 : ℕ → Submodule k P} [GradedAlgebra 𝒜]
  {Q : Type t} [CommRing Q] [Algebra A Q] [Algebra k Q] [IsScalarTower k A Q]
  {𝒬 : ℕ → Submodule A Q} [GradedAlgebra 𝒬] [∀ d, Module.Flat A ↥(𝒬 d)]
  {V : Type t₂} [AddCommGroup V] [Module k V]
  {red : Q →+* P}
  {hsmul : ∀ (a : A) (q : Q), red (a • q) = algebraMap A k a • red q}
  {hmem : ∀ (d : ℕ) (q : Q), q ∈ 𝒬 d → red q ∈ 𝒜 d}
  {ι : Type x} [Fintype ι] {σ : Type y} [Fintype σ] [DecidableEq σ]
  (pres : Algebra.WeightedHomogeneousPresentation k P 𝒜 ι σ)
  {yl : ι → Q}

/-- **The first-order class of a lifted presentation.** Lifting the chosen generators of a
presentation of `P` to homogeneous elements of a deformation `Q` of the same degrees, the
relations take values in the kernel of the reduction; their first-order parts, read through
`I ≃ₗ[k] V` and collected in the cokernel of the graded Jacobian, give an element of
`W ⊗[k] V`. -/
noncomputable def firstOrderClass
    (hret : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsq : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d))
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V)
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i) :
    pres.jacobianCokernel ⊗[k] V :=
  ∑ j, relationComponent pres eV j
    (relationFirstOrderPart pres hret hsq hbc hyd hy j)

end Class

/-! ### Transport along a morphism of deformations -/

section Transport

variable {k : Type w} [CommRing k]
  {A : Type u} [CommRing A] [Algebra k A] [Algebra A k]
  {B : Type u₂} [CommRing B] [Algebra k B] [Algebra B k]
  {P : Type v} [CommRing P] [Algebra k P] [Module A P] [IsScalarTower A k P]
    [Module B P] [IsScalarTower B k P]
  {𝒜 : ℕ → Submodule k P} [GradedAlgebra 𝒜]
  {Q : Type t} [CommRing Q] [Algebra A Q] [Algebra k Q] [IsScalarTower k A Q]
  {𝒬 : ℕ → Submodule A Q} [GradedAlgebra 𝒬] [∀ d, Module.Flat A ↥(𝒬 d)]
  {Q' : Type t₂} [CommRing Q'] [Algebra B Q'] [Algebra k Q'] [IsScalarTower k B Q']
  {𝒬' : ℕ → Submodule B Q'} [GradedAlgebra 𝒬'] [∀ d, Module.Flat B ↥(𝒬' d)]
  {V : Type v₁} [AddCommGroup V] [Module k V]
  {V' : Type v₂} [AddCommGroup V'] [Module k V']
  {red : Q →+* P}
  {hsmul : ∀ (a : A) (q : Q), red (a • q) = algebraMap A k a • red q}
  {hmem : ∀ (d : ℕ) (q : Q), q ∈ 𝒬 d → red q ∈ 𝒜 d}
  {red' : Q' →+* P}
  {hsmul' : ∀ (b : B) (q : Q'), red' (b • q) = algebraMap B k b • red' q}
  {hmem' : ∀ (d : ℕ) (q : Q'), q ∈ 𝒬' d → red' q ∈ 𝒜 d}
  {ι : Type x} [Fintype ι] {σ : Type y} [Fintype σ] [DecidableEq σ]
  (pres : Algebra.WeightedHomogeneousPresentation k P 𝒜 ι σ)
  {yl : ι → Q} {φ : A →ₐ[k] B} {g : Q →+* Q'}

/-- A morphism of deformations, restricted to the `d`-th graded piece. -/
def mapGradedPiece (g : Q →+* Q') (hgmem : ∀ (d : ℕ) (q : Q), q ∈ 𝒬 d → g q ∈ 𝒬' d) (d : ℕ) :
    ↥(𝒬 d) →+ ↥(𝒬' d) where
  toFun q := ⟨g (q : Q), hgmem d (q : Q) q.2⟩
  map_zero' := Subtype.ext (map_zero g)
  map_add' x z := Subtype.ext (map_add g (x : Q) (z : Q))

omit [Algebra A k] [Algebra B k] in
/-- A morphism of deformations semilinear over a `k`-algebra map of the bases is a `k`-algebra
map. -/
theorem map_map_algebraMap (hg : ∀ (a : A) (q : Q), g (a • q) = φ a • g q) (r : k) :
    g (algebraMap k Q r) = algebraMap k Q' r := by
  rw [algebraMap_eq_algebraMap_smul_one (A := A), hg, map_one, φ.commutes, Algebra.smul_def,
    mul_one, ← IsScalarTower.algebraMap_apply]

/-- A morphism of deformations semilinear over a `k`-algebra map of the bases, as a `k`-algebra
map. -/
def mapAlgHomOfSemilinear (hg : ∀ (a : A) (q : Q), g (a • q) = φ a • g q) : Q →ₐ[k] Q' :=
  { g with commutes' := map_map_algebraMap (φ := φ) hg }

omit [GradedAlgebra 𝒜] [Fintype ι] [Fintype σ] [DecidableEq σ] in
/-- **The first-order part of a relation is carried along a morphism of deformations.** -/
theorem relationFirstOrderPart_map
    (hretA : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsqA : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hretB : ∀ r : k, algebraMap B k (algebraMap k B r) = r)
    (hsqB : RingHom.ker (algebraMap B k) * RingHom.ker (algebraMap B k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d))
    (hbc' : ∀ d, IsBaseChange k (gradedPiece red' hsmul' hmem' d))
    (hφ : ∀ a : A, algebraMap B k (φ a) = algebraMap A k a)
    (hg : ∀ (a : A) (q : Q), g (a • q) = φ a • g q)
    (hgmem : ∀ (d : ℕ) (q : Q), q ∈ 𝒬 d → g q ∈ 𝒬' d)
    (hgcomm : ∀ q : Q, red' (g q) = red q)
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i)
    (hyd' : ∀ i, g (yl i) ∈ 𝒬' (pres.varDegree i))
    (hy' : ∀ i, red' (g (yl i)) = pres.val i) (j : σ) :
    relationFirstOrderPart (yl := fun i ↦ g (yl i)) pres hretB hsqB hbc' hyd' hy' j =
      LinearMap.rTensor ↥(𝒜 (pres.relDegree j)) (SquareZeroRetraction.kerMap φ hφ)
        (relationFirstOrderPart pres hretA hsqA hbc hyd hy j) := by
  have hzeq : mapGradedPiece g hgmem (pres.relDegree j)
        ⟨aeval yl (pres.relation j), aeval_relation_mem pres hyd j⟩ =
      (⟨aeval (fun i ↦ g (yl i)) (pres.relation j), aeval_relation_mem pres hyd' j⟩ :
        ↥(𝒬' (pres.relDegree j))) :=
    Subtype.ext <| comp_aeval_apply (f := yl) (mapAlgHomOfSemilinear (φ := φ) hg) (pres.relation j)
  have hgsm : ∀ (a : A) (x : ↥(𝒬 (pres.relDegree j))),
      mapGradedPiece g hgmem (pres.relDegree j) (a • x) =
        φ a • mapGradedPiece g hgmem (pres.relDegree j) x :=
    fun a x ↦ Subtype.ext (hg a (x : Q))
  have hgc : ∀ x : ↥(𝒬 (pres.relDegree j)),
      gradedPiece red' hsmul' hmem' (pres.relDegree j)
          (mapGradedPiece g hgmem (pres.relDegree j) x) =
        gradedPiece red hsmul hmem (pres.relDegree j) x :=
    fun x ↦ Subtype.ext (hgcomm (x : Q))
  have hkey : ((SquareZeroRetraction.kerEquiv hretA hsqA (hbc (pres.relDegree j))
        (relationFirstOrderPart pres hretA hsqA hbc hyd hy j) :
          ↥(LinearMap.ker (gradedPiece red hsmul hmem (pres.relDegree j)))) :
        ↥(𝒬 (pres.relDegree j))) =
      ⟨aeval yl (pres.relation j), aeval_relation_mem pres hyd j⟩ :=
    SquareZeroRetraction.kerEquiv_firstOrderPart hretA hsqA (hbc (pres.relDegree j))
      (gradedPiece_aeval_relation pres hretA hyd hy j)
  apply SquareZeroRetraction.firstOrderPart_eq_of_coe_kerEquiv_eq
  rw [SquareZeroRetraction.coe_kerEquiv_map hretA hsqA hretB hsqB (hbc (pres.relDegree j))
      (hbc' (pres.relDegree j)) φ hφ (mapGradedPiece g hgmem (pres.relDegree j)) hgsm hgc,
    hkey]
  exact hzeq

/-- **The first-order class is carried along a morphism of deformations.** A morphism of
deformations semilinear over a `k`-algebra map of square-zero thickenings carries the
first-order class of a lifted presentation to the class of the image lifted presentation,
through the map of thickening modules induced on the square-zero ideals.

With `B = A` and `φ` the identity this is the invariance of the class under an isomorphism of
deformations over the special fibre; with `g` a pushforward it is the naturality of the class in
the thickening module. -/
theorem firstOrderClass_map
    (hretA : ∀ r : k, algebraMap A k (algebraMap k A r) = r)
    (hsqA : RingHom.ker (algebraMap A k) * RingHom.ker (algebraMap A k) = ⊥)
    (hretB : ∀ r : k, algebraMap B k (algebraMap k B r) = r)
    (hsqB : RingHom.ker (algebraMap B k) * RingHom.ker (algebraMap B k) = ⊥)
    (hbc : ∀ d, IsBaseChange k (gradedPiece red hsmul hmem d))
    (hbc' : ∀ d, IsBaseChange k (gradedPiece red' hsmul' hmem' d))
    (eV : ↥(RingHom.ker (algebraMap A k)) ≃ₗ[k] V)
    (eV' : ↥(RingHom.ker (algebraMap B k)) ≃ₗ[k] V')
    (hφ : ∀ a : A, algebraMap B k (φ a) = algebraMap A k a)
    (hg : ∀ (a : A) (q : Q), g (a • q) = φ a • g q)
    (hgmem : ∀ (d : ℕ) (q : Q), q ∈ 𝒬 d → g q ∈ 𝒬' d)
    (hgcomm : ∀ q : Q, red' (g q) = red q)
    (hyd : ∀ i, yl i ∈ 𝒬 (pres.varDegree i)) (hy : ∀ i, red (yl i) = pres.val i)
    (hyd' : ∀ i, g (yl i) ∈ 𝒬' (pres.varDegree i))
    (hy' : ∀ i, red' (g (yl i)) = pres.val i)
    (f : V →ₗ[k] V')
    (hf : ∀ i, eV' (SquareZeroRetraction.kerMap φ hφ i) = f (eV i)) :
    firstOrderClass (yl := fun i ↦ g (yl i)) pres hretB hsqB hbc' eV' hyd' hy' =
      LinearMap.lTensor pres.jacobianCokernel f
        (firstOrderClass pres hretA hsqA hbc eV hyd hy) := by
  change ∑ j, relationComponent pres eV' j
      (relationFirstOrderPart (yl := fun i ↦ g (yl i)) pres hretB hsqB hbc' hyd' hy' j) =
    LinearMap.lTensor pres.jacobianCokernel f
      (∑ j, relationComponent pres eV j (relationFirstOrderPart pres hretA hsqA hbc hyd hy j))
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [relationFirstOrderPart_map pres hretA hsqA hretB hsqB hbc hbc' hφ hg hgmem hgcomm
      hyd hy hyd' hy' j,
    relationComponent_rTensor pres eV eV' φ hφ f hf j]

end Transport

end GradedDeformation

end
