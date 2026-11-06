module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.Algebra.FreeAbelianGroup.Finsupp
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AlternatingCech.DiagonalComplement
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Etale
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal

/-!
# Anti-invariant sections and the sign twist of the complement of the diagonals

Let `f : U → X` be an étale and separated morphism of algebraic spaces over a scheme `S`, let
`W_p` be the complement of all the diagonals in the `(p+1)`-fold self-product of `U` over `X`,
and let `K^p = ∧^{p+1} j_{U!} ℤ`.  The canonical map `ℤ(sign) ⟶ K^p` from the sign twist of
`W_p` is an isomorphism, and consequently the canonical map from `Hom(K^p, ℱ)` to the
`S_{p+1}`-anti-invariant sections of `ℱ` over `W_p` is bijective for every abelian sheaf `ℱ` on
the spaces-étale site of `X`.  Together with the freeness of the action of `S_{p+1}` on `W_p`
this is Stacks 0726.

## Main definitions

* `AlgebraicGeometry.Space.SpacesEtale.pairMk` is the morphism `(a, b) : V ⟶ U ×_X U` attached
  to a pair of morphisms `V ⟶ U`, and
  `AlgebraicGeometry.Space.SpacesEtale.collisionSet` is the set of points of `V` at which two
  morphisms `V ⟶ U` agree.
* `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementComponents` is the tuple of
  components `V ⟶ U` of a morphism from `V` into the complement of the diagonals.
* `AlgebraicGeometry.Space.SpacesEtale.koszulHomSignSectionsEquiv` is the identification of
  `Hom(K^p, ℱ)` with the anti-invariant sections, as an isomorphism of abelian groups.
* `exteriorPower.detFunctional` is the functional on an exterior power attached to a tuple of
  linear forms, the determinant of the matrix of their values.

## Main results

* `AlgebraicGeometry.Space.SpacesEtale.eq_of_collisionSet_eq_univ`: two morphisms `V ⟶ U` of
  the spaces-étale site agreeing at every point of `V` are equal.
* `AlgebraicGeometry.Space.SpacesEtale.exists_mem_topology_collisionSet_dichotomy`: a finite
  family of morphisms `V ⟶ U` is separated by a covering of `V`, on each member of which any
  two members of the family either agree or have no point in common.
* `FreeAbelianGroup.eq_zero_of_wedge_eq_zero`: the sign relations are all the relations among
  the wedges of a family of injective tuples.
* `AlgebraicGeometry.Space.SpacesEtale.isLocallySurjective_signTwistToExteriorPower` and
  `AlgebraicGeometry.Space.SpacesEtale.isLocallyInjective_signTwistToExteriorPower`: the map
  from the sign-twisted presheaf on `W_p` to the objectwise exterior power of the free abelian
  presheaf on `U` is locally surjective and locally injective.
* `AlgebraicGeometry.Space.SpacesEtale.isIso_signTwistToKoszul`,
  `AlgebraicGeometry.Space.SpacesEtale.bijective_koszulHomToSignSections` and
  `AlgebraicGeometry.Space.SpacesEtale.freeAction_and_bijective_koszulHomToSignSections` are
  **Stacks 0726**: the canonical map `ℤ(sign) ⟶ K^p` is an isomorphism, the induced map on
  `Hom(K^p, ℱ)` is bijective, and the full conclusion of the tag.

## Implementation notes

The isomorphism `ℤ(sign) ≅ K^p` is proved at the level of the presentations, not on stalks:
both sheaves are sheafifications of explicit presheaves, and a morphism of presheaves whose
sheafification is an isomorphism is exactly one which is locally injective and locally
surjective (`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`).  This is what makes the proof
insensitive to the fact that `K^p` is the sheafification of the `(p+1)`-st exterior power of
the *free abelian presheaf* on `U` rather than of the sheaf `j_{U!} ℤ`: everything happens
before sheafification, where the free abelian presheaf has an honest basis.

Local surjectivity is where the geometry sits.  A section of the exterior power over `V` is a
sum of wedges `φ_0 ∧ ⋯ ∧ φ_p` of morphisms `V ⟶ U`, and the locus where two of them agree is
open because the diagonal of `U ×_X U` is étale and closed because `f` is separated.  The
finitely many such loci therefore cut `V` into open and closed pieces covering it, on each of
which every pair either agrees — so that the wedge vanishes — or avoids the diagonal
everywhere, so that the tuple factors through `W_p`.  The factorization is the universal
property `AlgebraicGeometry.Space.SpacesEtale.diagonalComplementLift`.  That two pointwise
equal morphisms `V ⟶ U` are equal uses that the diagonal of `U ×_X U` is an open immersion,
which is part (1) of Stacks 05W1 for the unramified morphism `f`, and that an open immersion
surjective on points is an isomorphism.

Local injectivity needs no covering at all: over an object with a point the map is injective,
and an object with no points is covered by the empty sieve.  Injectivity over an object with a
point is a statement about free abelian groups, isolated as
`FreeAbelianGroup.eq_zero_of_wedge_eq_zero`: the components of a morphism into `W_p` are
pairwise distinct, morphisms with the same set of components differ by a permutation of the
factors, and the determinant of the coefficients at a chosen such set distinguishes the sets
and computes the signs.  Separatedness of `f` is not used for this half.

Surjectivity of `f`, which Stacks 0726 also assumes, is not used anywhere: it is what makes the
Koszul complex a resolution.

## References

* [Stacks Project, Tag 0726](https://stacks.math.columbia.edu/tag/0726)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

/-! ### Generation and functionals on exterior powers -/

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- An additive subgroup of the `n`-th exterior power over the integers containing the wedges
of the elements of a generating set of the module is everything. -/
theorem eq_top_of_ιMulti_mem (n : ℕ) {M : Type*} [AddCommGroup M]
    (N : AddSubgroup (⋀[ℤ]^n M)) (s : Set M) (hs : Submodule.span ℤ s = ⊤)
    (h : ∀ m : Fin n → M, (∀ i, m i ∈ s) → ιMulti ℤ n m ∈ N) : N = ⊤ := by
  have key : ∀ (t : Finset (Fin n)) (m : Fin n → M), (∀ i, i ∉ t → m i ∈ s) →
      ιMulti ℤ n m ∈ N := by
    intro t
    induction t using Finset.induction with
    | empty => exact fun m hm => h m fun i => hm i (Finset.notMem_empty i)
    | @insert i t hi ih =>
        intro m hm
        have hmem : m i ∈ Submodule.span ℤ s := by rw [hs]; exact Submodule.mem_top
        have hupd : ∀ x : M, x ∈ Submodule.span ℤ s →
            ιMulti ℤ n (Function.update m i x) ∈ N := by
          intro x hx
          induction hx using Submodule.span_induction with
          | mem y hy =>
              refine ih _ fun j hj => ?_
              by_cases hji : j = i
              · subst hji
                rw [Function.update_self]
                exact hy
              · rw [Function.update_of_ne hji]
                exact hm j fun hjt => hj (by
                  rcases Finset.mem_insert.1 hjt with h' | h'
                  · exact absurd h' hji
                  · exact h')
          | zero =>
              have hz : ιMulti ℤ n (Function.update m i (0 : M)) = 0 := by
                simp
              rw [hz]
              exact N.zero_mem
          | add y z _ _ hy hz =>
              have hadd : ιMulti ℤ n (Function.update m i (y + z)) =
                  ιMulti ℤ n (Function.update m i y) +
                    ιMulti ℤ n (Function.update m i z) := by
                simp
              rw [hadd]
              exact N.add_mem hy hz
          | smul r y _ hy =>
              have hsm : ιMulti ℤ n (Function.update m i (r • y)) =
                  r • ιMulti ℤ n (Function.update m i y) := by
                simp
              rw [hsm]
              exact N.zsmul_mem hy r
        have := hupd (m i) hmem
        rwa [Function.update_eq_self] at this
  refine le_antisymm le_top ?_
  intro x hxtop
  clear hxtop
  have hx : x ∈ Submodule.span ℤ (Set.range (ιMulti ℤ n (M := M))) := by
    rw [ιMulti_span]
    exact Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      exact key Finset.univ m fun i hi => absurd (Finset.mem_univ i) hi
  | zero => exact N.zero_mem
  | add y z _ _ hy hz => exact N.add_mem hy hz
  | smul r y _ hy => exact N.zsmul_mem hy r

/-- The linear functional on the `n`-th exterior power attached to an `n`-tuple of linear
forms: the determinant of the matrix of their values. -/
def detFunctional (n : ℕ) (c : Fin n → Module.Dual R M) : ⋀[R]^n M →ₗ[R] R :=
  alternatingMapLinearEquiv (Matrix.detRowAlternating.compLinearMap (LinearMap.pi c))

/-- The functional attached to an `n`-tuple of linear forms sends a wedge of `n` vectors to
the determinant of the matrix of the values of the forms at the vectors. -/
theorem detFunctional_ιMulti (n : ℕ) (c : Fin n → Module.Dual R M) (m : Fin n → M) :
    detFunctional n c (ιMulti R n m) = Matrix.det (Matrix.of fun i j => c j (m i)) :=
  alternatingMapLinearEquiv_apply_ιMulti _ m

end exteriorPower

/-! ### Free abelian groups and determinants of incidence matrices -/

namespace FreeAbelianGroup

/-- The free abelian group on a type is spanned over `ℤ` by its generators. -/
theorem span_range_of (α : Type*) :
    Submodule.span ℤ (Set.range (FreeAbelianGroup.of : α → FreeAbelianGroup α)) = ⊤ := by
  refine le_antisymm le_top ?_
  intro x hx
  clear hx
  induction x using FreeAbelianGroup.induction_on with
  | zero => exact Submodule.zero_mem _
  | of a => exact Submodule.subset_span ⟨a, rfl⟩
  | neg y hy => exact Submodule.neg_mem _ hy
  | add y z hy hz => exact Submodule.add_mem _ hy hz

/-- A generator has multiplicity one in itself. -/
@[simp]
theorem coeff_of_self {α : Type*} (a : α) : coeff a (of a) = 1 := by
  change (toFinsupp (of a)) a = 1
  rw [toFinsupp_of, Finsupp.single_eq_same]

/-- A generator has multiplicity zero in a different generator. -/
theorem coeff_of_of_ne {α : Type*} {a b : α} (h : b ≠ a) : coeff a (of b) = 0 := by
  change (toFinsupp (of b)) a = 0
  rw [toFinsupp_of, Finsupp.single_eq_of_ne' h]

/-- An additive map out of a free abelian group is the sum, over the support, of the
coefficients acting on the values at the generators. -/
theorem map_eq_sum_support {α M : Type*} [AddCommGroup M] (f : FreeAbelianGroup α →+ M)
    (z : FreeAbelianGroup α) : f z = ∑ a ∈ z.support, coeff a z • f (of a) := by
  conv_lhs => rw [eq_sum_support_coeff_smul_of z]
  rw [map_sum]
  exact Finset.sum_congr rfl fun a _ => map_zsmul _ _ _

end FreeAbelianGroup

namespace Function

/-- Two injective tuples of the same finite length, the range of the second contained in the
range of the first, differ by a permutation of the index set. -/
theorem exists_perm_comp_of_range_subset {A : Type*} {n : ℕ} {f g : Fin n → A}
    (hg : Function.Injective g) (h : Set.range g ⊆ Set.range f) :
    ∃ σ : Equiv.Perm (Fin n), g = f ∘ σ := by
  have hex : ∀ i : Fin n, ∃ j : Fin n, f j = g i := fun i => h ⟨i, rfl⟩
  choose s hs using hex
  have hsinj : Function.Injective s := fun i j hij =>
    hg ((hs i).symm.trans ((congrArg f hij).trans (hs j)))
  exact ⟨Equiv.ofBijective s (Finite.injective_iff_bijective.1 hsinj), funext fun i => (hs i).symm⟩

end Function

namespace Matrix

/-- A square matrix over the integers whose rows are the rows of the identity matrix permuted
by `σ` has determinant the sign of `σ`. -/
theorem det_eq_sign_of_entries {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} (σ : Equiv.Perm (Fin n))
    (h : ∀ i j, M i j = (1 : Matrix (Fin n) (Fin n) ℤ) (σ i) j) :
    M.det = (Equiv.Perm.sign σ : ℤ) := by
  have hM : M = (1 : Matrix (Fin n) (Fin n) ℤ).submatrix σ id := by
    funext i j
    rw [h i j, Matrix.submatrix_apply, id_eq]
  rw [hM, Matrix.det_permute, Matrix.det_one, mul_one, Int.cast_id]

end Matrix

/-! ### A relation among sign-twisted generators whose wedges vanish -/

namespace FreeAbelianGroup

/-- **The sign relations are all the relations among wedges of injective tuples.** Let a family
of injective `n`-tuples in a type `A` be indexed by `α`, let `q` be an additive map out of the
free abelian group on `α` which turns a permutation of the tuple of an index into the sign of
that permutation, and let `w` send the generator at an index to the wedge of the generators of
its tuple.  Then every element killed by `w` is killed by `q`.

Grouping the indices occurring in an element by the *set* of members of their tuples, the
tuples of one group are permutations of one another, so the values of `q` on that group differ
by signs, and the determinant of the coefficients at a chosen group kills the wedges of all the
other groups and computes those signs on the chosen one.  Hence the signed coefficients of each
group sum to zero. -/
theorem eq_zero_of_wedge_eq_zero {α A : Type*} {n : ℕ} (cmp : α → Fin n → A)
    (hinj : ∀ a, Function.Injective (cmp a)) {Q : Type*} [AddCommGroup Q]
    (q : FreeAbelianGroup α →+ Q)
    (hq : ∀ (a b : α) (σ : Equiv.Perm (Fin n)), cmp a = cmp b ∘ σ →
      q (of a) = (Equiv.Perm.sign σ : ℤ) • q (of b))
    (w : FreeAbelianGroup α →+ ⋀[ℤ]^n (FreeAbelianGroup A))
    (hw : ∀ a, w (of a) = exteriorPower.ιMulti ℤ n fun i => of (cmp a i))
    (z : FreeAbelianGroup α) (hz : w z = 0) : q z = 0 := by
  classical
  rw [map_eq_sum_support q z, ← Finset.sum_fiberwise_of_maps_to
    (g := fun a => Set.range (cmp a)) (t := z.support.image fun a => Set.range (cmp a))
    (fun a ha => Finset.mem_image_of_mem _ ha)]
  refine Finset.sum_eq_zero fun T hT => ?_
  obtain ⟨a₀, -, rfl⟩ := Finset.mem_image.1 hT
  have hperm : ∀ a : α, ∃ σ : Equiv.Perm (Fin n),
      Set.range (cmp a) = Set.range (cmp a₀) → cmp a = cmp a₀ ∘ σ := by
    intro a
    by_cases hcase : Set.range (cmp a) = Set.range (cmp a₀)
    · obtain ⟨σ, hσ⟩ := Function.exists_perm_comp_of_range_subset (hinj a) hcase.le
      exact ⟨σ, fun _ => hσ⟩
    · exact ⟨1, fun h => absurd h hcase⟩
  choose sg hsg using hperm
  have hdet : ∀ a : α, Set.range (cmp a) = Set.range (cmp a₀) →
      exteriorPower.detFunctional n
          (fun j => (coeff (cmp a₀ j)).toIntLinearMap) (w (of a)) =
        (Equiv.Perm.sign (sg a) : ℤ) := by
    intro a ha
    rw [hw, exteriorPower.detFunctional_ιMulti]
    refine Matrix.det_eq_sign_of_entries (sg a) fun i j => ?_
    change coeff (cmp a₀ j) (of (cmp a i)) = (1 : Matrix (Fin n) (Fin n) ℤ) (sg a i) j
    rw [congrFun (hsg a ha) i, Function.comp_apply]
    by_cases hij : sg a i = j
    · rw [hij, coeff_of_self, Matrix.one_apply_eq]
    · rw [coeff_of_of_ne fun hc => hij (hinj a₀ hc), Matrix.one_apply_ne hij]
  have hdet0 : ∀ a : α, Set.range (cmp a) ≠ Set.range (cmp a₀) →
      exteriorPower.detFunctional n
        (fun j => (coeff (cmp a₀ j)).toIntLinearMap) (w (of a)) = 0 := by
    intro a ha
    obtain ⟨j₀, hj₀⟩ : ∃ j₀ : Fin n, cmp a₀ j₀ ∉ Set.range (cmp a) := by
      by_contra hall
      refine ha ?_
      have hsubset : Set.range (cmp a₀) ⊆ Set.range (cmp a) := by
        rintro v ⟨j, rfl⟩
        exact not_not.1 fun hc => hall ⟨j, hc⟩
      obtain ⟨τ, hτ⟩ := Function.exists_perm_comp_of_range_subset (hinj a₀) hsubset
      rw [hτ, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
    rw [hw, exteriorPower.detFunctional_ιMulti]
    refine Matrix.det_eq_zero_of_column_eq_zero j₀ fun i => ?_
    change coeff (cmp a₀ j₀) (of (cmp a i)) = 0
    exact coeff_of_of_ne fun hc => hj₀ ⟨i, hc⟩
  have hzerosum : ∑ a ∈ z.support.filter (fun a => Set.range (cmp a) = Set.range (cmp a₀)),
      coeff a z * (Equiv.Perm.sign (sg a) : ℤ) = 0 := by
    have h1 : ∑ a ∈ z.support, coeff a z * exteriorPower.detFunctional n
        (fun j => (coeff (cmp a₀ j)).toIntLinearMap) (w (of a)) = 0 := by
      have h2 := map_eq_sum_support
        ((exteriorPower.detFunctional n
          (fun j => (coeff (cmp a₀ j)).toIntLinearMap)).toAddMonoidHom.comp w) z
      rw [show ((exteriorPower.detFunctional n
            (fun j => (coeff (cmp a₀ j)).toIntLinearMap)).toAddMonoidHom.comp w) z = 0 from by
          rw [AddMonoidHom.comp_apply, hz]
          exact map_zero _] at h2
      refine Eq.trans (Finset.sum_congr rfl fun a _ => ?_) h2.symm
      rw [zsmul_eq_mul, Int.cast_id]
      rfl
    rw [← Finset.sum_filter_of_ne
      (p := fun a => Set.range (cmp a) = Set.range (cmp a₀)) fun a _ hne => by
        by_contra hc
        exact hne (by rw [hdet0 a hc, mul_zero])] at h1
    refine Eq.trans (Finset.sum_congr rfl fun a ha => ?_) h1
    rw [hdet a (Finset.mem_filter.1 ha).2]
  calc ∑ a ∈ z.support.filter (fun a => Set.range (cmp a) = Set.range (cmp a₀)),
        coeff a z • q (of a)
      = ∑ a ∈ z.support.filter (fun a => Set.range (cmp a) = Set.range (cmp a₀)),
          (coeff a z * (Equiv.Perm.sign (sg a) : ℤ)) • q (of a₀) :=
        Finset.sum_congr rfl fun a ha => by
          rw [hq a a₀ (sg a) (hsg a (Finset.mem_filter.1 ha).2), smul_smul]
    _ = (∑ a ∈ z.support.filter (fun a => Set.range (cmp a) = Set.range (cmp a₀)),
            coeff a z * (Equiv.Perm.sign (sg a) : ℤ)) • q (of a₀) :=
        Finset.sum_smul.symm
    _ = 0 := by rw [hzerosum, zero_smul]

end FreeAbelianGroup

/-! ### The locus where two morphisms into `U` agree -/

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

namespace SpacesEtale

/-- The morphism `(a, b) : V ⟶ U ×_X U` attached to a pair of morphisms `V ⟶ U` of the
spaces-étale site of `X`. -/
def pairMk (U : SpacesEtale B S hS X) {V : SpacesEtale B S hS X} (a b : V ⟶ U) :
    V ⟶ prodTwo B S hS X U :=
  pullback.lift a b ((final_isTerminal B S hS X).hom_ext _ _)

/-- The first projection of `pairMk U a b` is `a`. -/
@[simp]
theorem pairMk_comp_fst (U : SpacesEtale B S hS X) {V : SpacesEtale B S hS X} (a b : V ⟶ U) :
    pairMk B S hS X U a b ≫ pullback.fst (toFinal B S hS U) (toFinal B S hS U) = a :=
  pullback.lift_fst _ _ _

/-- The second projection of `pairMk U a b` is `b`. -/
@[simp]
theorem pairMk_comp_snd (U : SpacesEtale B S hS X) {V : SpacesEtale B S hS X} (a b : V ⟶ U) :
    pairMk B S hS X U a b ≫ pullback.snd (toFinal B S hS U) (toFinal B S hS U) = b :=
  pullback.lift_snd _ _ _

/-- Precomposition distributes over the pair of two morphisms. -/
theorem comp_pairMk (U : SpacesEtale B S hS X) {V V' : SpacesEtale B S hS X} (g : V' ⟶ V)
    (a b : V ⟶ U) :
    g ≫ pairMk B S hS X U a b = pairMk B S hS X U (g ≫ a) (g ≫ b) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, pairMk_comp_fst, pairMk_comp_fst]
  · rw [Category.assoc, pairMk_comp_snd, pairMk_comp_snd]

/-- The pair of a morphism with itself factors through the diagonal. -/
theorem pairMk_self (U : SpacesEtale B S hS X) {V : SpacesEtale B S hS X} (a : V ⟶ U) :
    pairMk B S hS X U a a = a ≫ diagTwo B S hS X U := by
  refine pullback.hom_ext ?_ ?_
  · rw [pairMk_comp_fst, Category.assoc, diagTwo_comp_fst, Category.comp_id]
  · rw [pairMk_comp_snd, Category.assoc, diagTwo_comp_snd, Category.comp_id]

/-- The pair of projections of `U^n` composed with a morphism into `U^n` is the pair of the
corresponding two components. -/
theorem comp_projPair_eq_pairMk (U : SpacesEtale B S hS X) (n : ℕ)
    {V : SpacesEtale B S hS X} (ψ : V ⟶ selfProd B S hS X U n) (i j : Fin n) :
    ψ ≫ projPair B S hS X U n i j =
      pairMk B S hS X U (ψ ≫ Pi.π (fun _ : Fin n => U) i)
        (ψ ≫ Pi.π (fun _ : Fin n => U) j) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, projPair_comp_fst, pairMk_comp_fst]
  · rw [Category.assoc, projPair_comp_snd, pairMk_comp_snd]

/-- The set of points of `V` at which two morphisms `V ⟶ U` agree: the preimage, under the
pair they form, of the point set of the diagonal of `U ×_X U`. -/
def collisionSet (U : SpacesEtale B S hS X) {V : SpacesEtale B S hS X} (a b : V ⟶ U) :
    Set (points B S hS (underlying B S hS X V).1) :=
  pointsMap B S hS (underlying B S hS X V).1
      ((toSpaces B S hS X).map (pairMk B S hS X U a b)).hom ⁻¹'
    Set.range (pointsMap B S hS (underlying B S hS X U).1
      ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom)

/-- The locus where two morphisms into `U` agree is open: the point set of the diagonal of
`U ×_X U` is open because the diagonal is a morphism of the spaces-étale site, hence étale. -/
theorem isOpen_collisionSet (U : SpacesEtale B S hS X) {V : SpacesEtale B S hS X}
    (a b : V ⟶ U) : IsOpen (collisionSet B S hS X U a b) :=
  (isOpen_range_pointsMap_diagTwo B S hS X U).preimage (continuous_pointsMap B S hS _)

/-- The locus where two morphisms into `U` agree is closed when the structure morphism of `U`
is separated. -/
theorem isClosed_collisionSet (U : SpacesEtale B S hS X)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X} (a b : V ⟶ U) :
    IsClosed (collisionSet B S hS X U a b) :=
  (isClosed_range_pointsMap_diagTwo B S hS X U hsep).preimage (continuous_pointsMap B S hS _)

/-- A point of `V'` lies in the locus where two restricted morphisms agree exactly when its
image in `V` lies in the locus where the two morphisms agree. -/
theorem mem_collisionSet_comp_iff (U : SpacesEtale B S hS X)
    {V V' : SpacesEtale B S hS X} (g : V' ⟶ V) (a b : V ⟶ U)
    (y : points B S hS (underlying B S hS X V').1) :
    y ∈ collisionSet B S hS X U (g ≫ a) (g ≫ b) ↔
      pointsMap B S hS (underlying B S hS X V').1
          ((toSpaces B S hS X).map g).hom y ∈ collisionSet B S hS X U a b := by
  rw [collisionSet, collisionSet, Set.mem_preimage, Set.mem_preimage,
    ← comp_pairMk B S hS X U g a b, pointsMap_toSpaces_map_comp]

/-- The locus where a morphism agrees with itself is everything. -/
theorem collisionSet_self (U : SpacesEtale B S hS X) {V : SpacesEtale B S hS X} (a : V ⟶ U) :
    collisionSet B S hS X U a a = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  rw [collisionSet, Set.mem_preimage, pairMk_self, pointsMap_toSpaces_map_comp]
  exact ⟨_, rfl⟩

/-! ### Two morphisms agreeing at every point are equal -/

/-- **Stacks 05W1 for the diagonal of `U ×_X U`.** The diagonal of `U ×_X U`, read on
presheaves, is an open immersion: it is the relative diagonal of the structure morphism of
`U`, which is étale hence unramified, transported along the comparison of the two fibre
squares. -/
theorem isOpenImmersion_hom_toSpaces_map_diagTwo (U : SpacesEtale B S hS X) :
    IsOpenImmersion B S hS ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom := by
  have hdiag : IsOpenImmersion B S hS (pullback.diagonal U.1.hom.hom) :=
    isOpenImmersion_diagonal_of_isUnramified B S hS (underlying B S hS X U).2 X.2 _
      (isUnramified_of_isEtale B S hS U.property)
  have hiso : IsIso (fibreSquareIso B S hS X U).hom.hom :=
    (ObjectProperty.isIso_hom_iff (fibreSquareIso B S hS X U).hom).2 inferInstance
  have hcomp : ((toSpaces B S hS X).map (diagTwo B S hS X U)).hom =
      pullback.diagonal U.1.hom.hom ≫ (fibreSquareIso B S hS X U).hom.hom :=
    congrArg (fun k => k.hom) (toSpaces_map_diagTwo B S hS X U)
  rw [hcomp]
  exact MorphismProperty.RespectsIso.postcomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)))
    (fibreSquareIso B S hS X U).hom.hom _ hdiag

/-- Two morphisms `V ⟶ U` of the spaces-étale site of `X` which agree at every point of `V`
are equal.

The fibre product of the pair they form with the diagonal of `U ×_X U` projects to `V` by a
base change of that diagonal, hence by an open immersion, and the hypothesis makes that
projection surjective on points; an open immersion surjective on points is an isomorphism, and
inverting it factors the pair through the diagonal. -/
theorem eq_of_collisionSet_eq_univ (U : SpacesEtale B S hS X) {V : SpacesEtale B S hS X}
    (a b : V ⟶ U) (h : collisionSet B S hS X U a b = Set.univ) : a = b := by
  set f := (toSpaces B S hS X).map (pairMk B S hS X U a b) with hf
  set i := (toSpaces B S hS X).map (diagTwo B S hS X U) with hi
  have sq : IsPullback
      (ObjectProperty.homMk (pullback.fst f.hom i.hom) :
        AlgebraicSpaces.fiberProduct B S hS f i ⟶ underlying B S hS X V)
      (ObjectProperty.homMk (pullback.snd f.hom i.hom) :
        AlgebraicSpaces.fiberProduct B S hS f i ⟶ underlying B S hS X U) f i :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f i
  set p := (ObjectProperty.homMk (pullback.fst f.hom i.hom) :
    AlgebraicSpaces.fiberProduct B S hS f i ⟶ underlying B S hS X V) with hp
  set q := (ObjectProperty.homMk (pullback.snd f.hom i.hom) :
    AlgebraicSpaces.fiberProduct B S hS f i ⟶ underlying B S hS X U) with hq
  have hpOI : IsOpenImmersion B S hS p.hom :=
    isOpenImmersion_of_isPullback B S hS sq.flip
      (isOpenImmersion_hom_toSpaces_map_diagTwo B S hS X U)
  have hsurj : Function.Surjective
      (pointsMap B S hS (AlgebraicSpaces.fiberProduct B S hS f i).1 p.hom) := by
    intro y
    obtain ⟨x, hx⟩ : pointsMap B S hS (underlying B S hS X V).1 f.hom y ∈
        Set.range (pointsMap B S hS (underlying B S hS X U).1 i.hom) :=
      (h ▸ Set.mem_univ y : y ∈ collisionSet B S hS X U a b)
    obtain ⟨w, hw, -⟩ := exists_point_of_isPullback B S hS sq y x hx.symm
    exact ⟨w, hw⟩
  have hisoHom : IsIso p.hom :=
    isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS p.hom hpOI
      ((surjective_iff_pointsMap_surjective_of_representable B S hS p.hom hpOI.rep).2 hsurj)
  have _ : IsIso p := (ObjectProperty.isIso_hom_iff p).1 hisoHom
  have hfac : f = inv p ≫ q ≫ i := by
    rw [← sq.w, IsIso.inv_hom_id_assoc]
  have key : ∀ (m : prodTwo B S hS X U ⟶ U) (c : V ⟶ U), diagTwo B S hS X U ≫ m = 𝟙 _ →
      pairMk B S hS X U a b ≫ m = c → (toSpaces B S hS X).map c = inv p ≫ q := by
    intro m c hm hc
    have him : i ≫ (toSpaces B S hS X).map m = 𝟙 _ := by
      rw [hi, ← Functor.map_comp, hm, CategoryTheory.Functor.map_id]
    rw [← hc, Functor.map_comp, ← hf]
    exact (congrArg (· ≫ (toSpaces B S hS X).map m) hfac).trans
      (by rw [Category.assoc, Category.assoc, him, Category.comp_id])
  refine (toSpaces B S hS X).map_injective ?_
  rw [key _ a (diagTwo_comp_fst B S hS X U) (pairMk_comp_fst B S hS X U a b),
    key _ b (diagTwo_comp_snd B S hS X U) (pairMk_comp_snd B S hS X U a b)]

/-! ### Separating a finite family of morphisms by a covering -/

/-- The point set of an open subspace of an object of the spaces-étale site of `X`, read as the
image of the points of that subspace read as an object of the site. -/
theorem range_pointsMap_openSubspaceInclusion (V : SpacesEtale B S hS X)
    (T : Set (points B S hS (underlying B S hS X V).1))
    (hT : IsOpenSubspace B S hS (openSubspaceOfPoints B S hS (underlying B S hS X V).1 T)) :
    Set.range (pointsMap B S hS
        (underlying B S hS X (openSubspaceObject B S hS X V ⟨_, hT⟩)).1
        ((toSpaces B S hS X).map (openSubspaceInclusion B S hS X V ⟨_, hT⟩)).hom) = T :=
  range_pointsMap_ι_openSubspaceOfPoints B S hS T

/-- **The separating covering of a finite family of morphisms into `U`.** For a finite family
of morphisms `V ⟶ U` with `U` separated over `X` there is a covering of `V` on which any two
members of the family either agree or have no point in common: the complementary loci where
they agree are open and closed, so the finitely many conditions cut `V` into open and closed
pieces that cover it. -/
theorem exists_mem_topology_collisionSet_dichotomy (U : SpacesEtale B S hS X)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X} {ι : Type}
    [Finite ι] (a : ι → (V ⟶ U)) :
    ∃ R : Sieve V, R ∈ topology B S hS X V ∧
      ∀ ⦃V' : SpacesEtale B S hS X⦄ (g : V' ⟶ V), R g → ∀ p q : ι,
        g ≫ a p = g ≫ a q ∨ collisionSet B S hS X U (g ≫ a p) (g ≫ a q) = ∅ := by
  classical
  set C : ι × ι → Set (points B S hS (underlying B S hS X V).1) :=
    fun pq => collisionSet B S hS X U (a pq.1) (a pq.2) with hC
  set T : Set (ι × ι) → Set (points B S hS (underlying B S hS X V).1) :=
    fun ε => (⋂ pq ∈ ε, C pq) ∩ ⋂ pq ∈ εᶜ, (C pq)ᶜ with hT
  have hopen : ∀ ε, IsOpen (T ε) := fun ε =>
    ((Set.toFinite ε).isOpen_biInter fun pq _ => isOpen_collisionSet B S hS X U _ _).inter
      ((Set.toFinite εᶜ).isOpen_biInter fun pq _ =>
        (isClosed_collisionSet B S hS X U hsep _ _).isOpen_compl)
  have hsub : ∀ ε, IsOpenSubspace B S hS
      (openSubspaceOfPoints B S hS (underlying B S hS X V).1 (T ε)) := fun ε =>
    isOpenSubspace_openSubspaceOfPoints B S hS (underlying B S hS X V).2 _ (hopen ε)
  set W : Set (ι × ι) → SpacesEtale B S hS X := fun ε =>
    openSubspaceObject B S hS X V ⟨_, hsub ε⟩ with hW
  set incl : ∀ ε, W ε ⟶ V := fun ε => openSubspaceInclusion B S hS X V ⟨_, hsub ε⟩ with hincl
  have hrange : ∀ ε, Set.range (pointsMap B S hS (underlying B S hS X (W ε)).1
      ((toSpaces B S hS X).map (incl ε)).hom) = T ε := fun ε =>
    range_pointsMap_openSubspaceInclusion B S hS X V (T ε) (hsub ε)
  set E : PreZeroHypercover.{u + 1} V :=
    ⟨ULift.{u + 1} (Set (ι × ι)), fun e => W e.down, fun e => incl e.down⟩ with hE
  have hcov : IsCovering B S hS X ⟨V, E⟩ := by
    intro x
    refine ⟨ULift.up {pq | x ∈ C pq}, ?_⟩
    have hx : x ∈ T {pq | x ∈ C pq} :=
      ⟨Set.mem_biInter fun pq hpq => hpq, Set.mem_biInter fun pq hpq => hpq⟩
    obtain ⟨y, hy⟩ := (hrange {pq | x ∈ C pq}).ge hx
    exact ⟨y, hy⟩
  refine ⟨Sieve.generate E.presieve₀, ?_, ?_⟩
  · rw [Precoverage.mem_toGrothendieck_iff]
    exact Precoverage.Saturate.of V E.presieve₀ ((mem_precoverage_iff B S hS X).2 ⟨E, rfl, hcov⟩)
  · rintro V' g ⟨Z, h, b, hb, rfl⟩ p q
    obtain ⟨e⟩ := hb
    have hpt : ∀ y : points B S hS (underlying B S hS X V').1,
        pointsMap B S hS (underlying B S hS X V').1
          ((toSpaces B S hS X).map (h ≫ E.f e)).hom y ∈ T e.down := by
      intro y
      rw [pointsMap_toSpaces_map_comp]
      exact (hrange e.down).le ⟨_, rfl⟩
    by_cases hε : (p, q) ∈ e.down
    · refine Or.inl (eq_of_collisionSet_eq_univ B S hS X U _ _ (Set.eq_univ_of_forall fun y => ?_))
      rw [mem_collisionSet_comp_iff]
      exact Set.mem_iInter₂.1 (hpt y).1 (p, q) hε
    · refine Or.inr (Set.eq_empty_of_forall_notMem fun y hy => ?_)
      rw [mem_collisionSet_comp_iff] at hy
      exact Set.mem_iInter₂.1 (hpt y).2 (p, q) hε hy

/-! ### Local surjectivity of the map to the exterior power -/

/-- Restriction in the exterior power of the free abelian presheaf on `U` carries the wedge of
the generators at a tuple of morphisms to the wedge of the generators at the restricted
tuple. -/
theorem presheafExteriorPower_map_ιMulti_of (U : SpacesEtale B S hS X) (n : ℕ)
    {V V' : SpacesEtale B S hS X} (g : V' ⟶ V) (a : Fin n → (V ⟶ U)) :
    (AddCommGrpCat.presheafExteriorPower (freeAbelianRepresentablePresheaf B S hS X U) n).map
        g.op (exteriorPower.ιMulti ℤ n fun i => FreeAbelianGroup.of (a i)) =
      exteriorPower.ιMulti ℤ n fun i => FreeAbelianGroup.of (g ≫ a i) := by
  change exteriorPower.map n
      ((freeAbelianRepresentablePresheaf B S hS X U).map g.op).hom.toIntLinearMap
      (exteriorPower.ιMulti ℤ n fun i => FreeAbelianGroup.of (a i)) = _
  refine Eq.trans (exteriorPower.map_apply_ιMulti _ _) ?_
  congr 1

/-- The map from the sign-twisted presheaf to the exterior power sends the class of a morphism
`V ⟶ W` to the wedge of the generators at its components. -/
theorem signTwistToExteriorPower_app_twistedGenerator (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X}
    (ψ : V ⟶ diagonalComplement B S hS X U n hsep) :
    (signTwistToExteriorPower B S hS X U n hsep).app (op V)
        (twistedGenerator (diagonalComplement B S hS X U n hsep)
          (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign ψ) =
      exteriorPower.ιMulti ℤ n fun i => FreeAbelianGroup.of
        (ψ ≫ diagonalComplementι B S hS X U n hsep ≫ Pi.π (fun _ : Fin n => U) i) :=
  signTwistToExteriorPowerApp_twistedGenerator B S hS X U n hsep (op V) ψ

/-- A point of `V` is sent into the locus of `U^n` where two factors agree exactly when the two
corresponding components of the morphism agree at it. -/
private theorem pointsMap_mem_collisionPoints_iff (U : SpacesEtale B S hS X) (n : ℕ)
    {V : SpacesEtale B S hS X} (ψ : V ⟶ selfProd B S hS X U n) (i j : Fin n)
    (y : points B S hS (underlying B S hS X V).1) :
    pointsMap B S hS (underlying B S hS X V).1 ((toSpaces B S hS X).map ψ).hom y ∈
        collisionPoints B S hS X U n i j ↔
      y ∈ collisionSet B S hS X U (ψ ≫ Pi.π (fun _ : Fin n => U) i)
        (ψ ≫ Pi.π (fun _ : Fin n => U) j) := by
  rw [collisionPoints, collisionSet, Set.mem_preimage, Set.mem_preimage,
    ← pointsMap_toSpaces_map_comp, comp_projPair_eq_pairMk]

/-- A tuple of morphisms `V ⟶ U` no two distinct members of which have a point in common
factors through the complement of the diagonals; these are the points of its factorization. -/
theorem mem_diagonalComplementPoints_pointsMap_lift (U : SpacesEtale B S hS X) (n : ℕ)
    {V : SpacesEtale B S hS X} (a : Fin n → (V ⟶ U))
    (hempty : ∀ i j : Fin n, i ≠ j → collisionSet B S hS X U (a i) (a j) = ∅)
    (y : points B S hS (underlying B S hS X V).1) :
    pointsMap B S hS (underlying B S hS X V).1
        ((toSpaces B S hS X).map (Pi.lift a)).hom y ∈
      diagonalComplementPoints B S hS X U n := by
  rw [mem_diagonalComplementPoints_iff]
  intro i j hij hmem
  rw [pointsMap_mem_collisionPoints_iff, Pi.lift_comp_π, Pi.lift_comp_π] at hmem
  exact Set.eq_empty_iff_forall_notMem.1 (hempty i j hij) y hmem

/-- **Stacks 0726, local surjectivity.** Every section of the `n`-th exterior power of the free
abelian presheaf on `U` is locally the image of the class of a morphism into the complement of
the diagonals: a covering separates the finitely many morphisms involved, and on each member
either two of them agree, so that the wedge vanishes, or the tuple avoids all the diagonals and
hence factors through that complement. -/
theorem isLocallySurjective_signTwistToExteriorPower (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    Presheaf.IsLocallySurjective (topology B S hS X)
      (signTwistToExteriorPower B S hS X U n hsep) := by
  classical
  constructor
  intro V s
  have hgen : ∀ a : Fin n → (V ⟶ U),
      Presheaf.imageSieve (signTwistToExteriorPower B S hS X U n hsep)
        (exteriorPower.ιMulti ℤ n fun i => FreeAbelianGroup.of (a i)) ∈
          topology B S hS X V := by
    intro a
    obtain ⟨R, hR, hdich⟩ := exists_mem_topology_collisionSet_dichotomy B S hS X U hsep a
    refine (topology B S hS X).superset_covering ?_ hR
    intro V' g hg
    by_cases hex : ∃ i j : Fin n, i ≠ j ∧ g ≫ a i = g ≫ a j
    · obtain ⟨i, j, hij, hgij⟩ := hex
      have hz : (exteriorPower.ιMulti ℤ n fun k => FreeAbelianGroup.of (g ≫ a k)) = 0 :=
        (exteriorPower.ιMulti ℤ n).map_eq_zero_of_eq _
          (congrArg FreeAbelianGroup.of hgij) hij
      refine ⟨0, ?_⟩
      rw [presheafExteriorPower_map_ιMulti_of, hz]
      exact map_zero _
    · have hempty : ∀ i j : Fin n, i ≠ j →
          collisionSet B S hS X U (g ≫ a i) (g ≫ a j) = ∅ := by
        intro i j hij
        rcases hdich g hg i j with heq | hemp
        · exact absurd ⟨i, j, hij, heq⟩ hex
        · exact hemp
      refine ⟨twistedGenerator (diagonalComplement B S hS X U n hsep)
        (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign
        (diagonalComplementLift B S hS X U n hsep (Pi.lift fun i => g ≫ a i)
          (mem_diagonalComplementPoints_pointsMap_lift B S hS X U n _ hempty)), ?_⟩
      have hcomp : ∀ i : Fin n,
          diagonalComplementLift B S hS X U n hsep (Pi.lift fun k => g ≫ a k)
              (mem_diagonalComplementPoints_pointsMap_lift B S hS X U n _ hempty) ≫
            diagonalComplementι B S hS X U n hsep ≫ Pi.π (fun _ : Fin n => U) i =
          g ≫ a i := by
        intro i
        rw [← Category.assoc, diagonalComplementLift_ι, Pi.lift_comp_π]
      rw [signTwistToExteriorPower_app_twistedGenerator,
        presheafExteriorPower_map_ιMulti_of]
      exact congrArg (fun k => exteriorPower.ιMulti ℤ n k)
        (funext fun i => congrArg FreeAbelianGroup.of (hcomp i))
  let N : AddSubgroup (⋀[ℤ]^n (FreeAbelianGroup (V ⟶ U))) :=
    { carrier := {t | Presheaf.imageSieve (signTwistToExteriorPower B S hS X U n hsep) t ∈
        topology B S hS X V}
      zero_mem' := by
        refine (topology B S hS X).superset_covering ?_ ((topology B S hS X).top_mem V)
        intro V' g _
        refine ⟨0, ?_⟩
        rw [map_zero]
        exact (map_zero _).symm
      add_mem' := fun {x y} hx hy => by
        refine (topology B S hS X).superset_covering ?_
          ((topology B S hS X).intersection_covering hx hy)
        rintro V' g ⟨⟨t₁, h₁⟩, t₂, h₂⟩
        refine ⟨t₁ + t₂, ?_⟩
        rw [map_add, h₁, h₂]
        exact (map_add _ x y).symm
      neg_mem' := fun {x} hx => by
        refine (topology B S hS X).superset_covering ?_ hx
        rintro V' g ⟨t, h⟩
        refine ⟨-t, ?_⟩
        rw [map_neg, h]
        exact (map_neg _ x).symm }
  have hN : N = ⊤ := by
    refine exteriorPower.eq_top_of_ιMulti_mem n N _
      (FreeAbelianGroup.span_range_of (V ⟶ U)) ?_
    intro m hm
    choose a ha using hm
    have hmeq : m = fun i => FreeAbelianGroup.of (a i) := funext fun i => (ha i).symm
    rw [hmeq]
    exact hgen a
  have hsN : s ∈ N := by rw [hN]; exact AddSubgroup.mem_top s
  exact hsN

/-! ### Local injectivity of the map to the exterior power -/

/-- The `n` components `V ⟶ U` of a morphism from `V` into the complement of the diagonals in
the `n`-fold self-product of `U`. -/
def diagonalComplementComponents (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X}
    (ψ : V ⟶ diagonalComplement B S hS X U n hsep) (i : Fin n) : V ⟶ U :=
  ψ ≫ diagonalComplementι B S hS X U n hsep ≫ Pi.π (fun _ : Fin n => U) i

/-- A morphism into the complement of the diagonals is determined by its components. -/
theorem eq_of_diagonalComplementComponents_eq (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X}
    {ψ ψ' : V ⟶ diagonalComplement B S hS X U n hsep}
    (h : diagonalComplementComponents B S hS X U n hsep ψ =
      diagonalComplementComponents B S hS X U n hsep ψ') : ψ = ψ' := by
  refine diagonalComplement_hom_ext B S hS X U n hsep (Pi.hom_ext _ _ fun i => ?_)
  rw [Category.assoc, Category.assoc]
  exact congrFun h i

/-- Translating a morphism into the complement of the diagonals by a permutation permutes its
components. -/
theorem diagonalComplementComponents_comp_aut (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X}
    (ψ : V ⟶ diagonalComplement B S hS X U n hsep) (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    diagonalComplementComponents B S hS X U n hsep
        (ψ ≫ (diagonalComplementAut B S hS X U n hsep σ).asIso.hom) i =
      diagonalComplementComponents B S hS X U n hsep ψ (σ⁻¹ i) :=
  comp_diagonalComplementAut_comp_π B S hS X U n hsep ψ σ i

/-- **The components of a morphism into the complement of the diagonals are distinct.** If the
source has a point, no two components can agree, since at such a point the image would lie on
a diagonal of `U^n`. -/
theorem injective_diagonalComplementComponents (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) {V : SpacesEtale B S hS X}
    (y : points B S hS (underlying B S hS X V).1)
    (ψ : V ⟶ diagonalComplement B S hS X U n hsep) :
    Function.Injective (diagonalComplementComponents B S hS X U n hsep ψ) := by
  intro i j hij
  by_contra hne
  have hij2 : ψ ≫ diagonalComplementι B S hS X U n hsep ≫ Pi.π (fun _ : Fin n => U) i =
      ψ ≫ diagonalComplementι B S hS X U n hsep ≫ Pi.π (fun _ : Fin n => U) j := hij
  have hmem : pointsMap B S hS (underlying B S hS X V).1
      ((toSpaces B S hS X).map (ψ ≫ diagonalComplementι B S hS X U n hsep)).hom y ∈
      diagonalComplementPoints B S hS X U n := by
    rw [pointsMap_toSpaces_map_comp]
    exact mem_diagonalComplementPoints_pointsMap_diagonalComplementι B S hS X U n hsep _
  refine (mem_diagonalComplementPoints_iff B S hS X U n _).1 hmem i j hne ?_
  rw [pointsMap_mem_collisionPoints_iff, Category.assoc, Category.assoc, hij2]
  exact (collisionSet_self B S hS X U _).symm ▸ Set.mem_univ y

/-- **Stacks 0726, injectivity on sections over an object with a point.** A relation between
classes of morphisms into the complement of the diagonals whose wedge of components vanishes is
already a relation imposed by the sign character.

This is the algebraic statement that the sign relations are all the relations among wedges of
injective tuples, applied to the components of the morphisms into the complement of the
diagonals: those components are injective because the source has a point, a morphism into that
complement is determined by its components, and translating by a permutation permutes them. -/
theorem quotient_mk_eq_zero_of_signTwistToExteriorPower_app_eq_zero (U : SpacesEtale B S hS X)
    (n : ℕ) (hsep : IsSeparated B S hS U.1.hom.hom) (V : (SpacesEtale B S hS X)ᵒᵖ)
    (y : points B S hS (underlying B S hS X V.unop).1)
    (z : FreeAbelianGroup (V.unop ⟶ diagonalComplement B S hS X U n hsep))
    (hz : (signTwistToExteriorPower B S hS X U n hsep).app V (QuotientAddGroup.mk z) = 0) :
    (QuotientAddGroup.mk z : (signTwistPresheaf B S hS X U n hsep).obj V) = 0 := by
  refine FreeAbelianGroup.eq_zero_of_wedge_eq_zero
    (diagonalComplementComponents B S hS X U n hsep)
    (injective_diagonalComplementComponents B S hS X U n hsep y)
    (QuotientAddGroup.mk' (characterRelations (diagonalComplement B S hS X U n hsep)
      (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign V.unop)) ?_
    ((ConcreteCategory.hom ((signTwistToExteriorPower B S hS X U n hsep).app V)).comp
      (QuotientAddGroup.mk' (characterRelations (diagonalComplement B S hS X U n hsep)
        (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign V.unop))) ?_ z hz
  · intro a b σ hab
    have hcomp : a = b ≫ (diagonalComplementAut B S hS X U n hsep σ⁻¹).asIso.hom := by
      refine eq_of_diagonalComplementComponents_eq B S hS X U n hsep (funext fun i => ?_)
      rw [diagonalComplementComponents_comp_aut, inv_inv]
      exact congrFun hab i
    have hgen := twistedGenerator_act (diagonalComplement B S hS X U n hsep)
      (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign b σ⁻¹
    rw [Equiv.Perm.sign_inv] at hgen
    rwa [hcomp]
  · intro a
    exact signTwistToExteriorPower_app_twistedGenerator B S hS X U n hsep a

/-- **Stacks 0726, local injectivity.** The map from the sign-twisted presheaf on the
complement of the diagonals to the exterior power of the free abelian presheaf on `U` is
locally injective: over an object with a point it is injective, and an object with no points is
covered by the empty sieve. -/
theorem isLocallyInjective_signTwistToExteriorPower (U : SpacesEtale B S hS X) (n : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    Presheaf.IsLocallyInjective (topology B S hS X)
      (signTwistToExteriorPower B S hS X U n hsep) := by
  constructor
  intro V x₁ x₂ hx
  by_cases hpt : Nonempty (points B S hS (underlying B S hS X V.unop).1)
  · obtain ⟨y⟩ := hpt
    obtain ⟨z₁, rfl⟩ := QuotientAddGroup.mk_surjective x₁
    obtain ⟨z₂, rfl⟩ := QuotientAddGroup.mk_surjective x₂
    have e0 : (QuotientAddGroup.mk (z₁ - z₂) :
        ToType ((signTwistPresheaf B S hS X U n hsep).obj V)) =
        QuotientAddGroup.mk z₁ - QuotientAddGroup.mk z₂ :=
      map_sub (QuotientAddGroup.mk' (characterRelations
        (diagonalComplement B S hS X U n hsep)
        (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign V.unop)) z₁ z₂
    have e1 : (signTwistToExteriorPower B S hS X U n hsep).app V
          (QuotientAddGroup.mk (z₁ - z₂)) =
        (signTwistToExteriorPower B S hS X U n hsep).app V (QuotientAddGroup.mk z₁) -
          (signTwistToExteriorPower B S hS X U n hsep).app V (QuotientAddGroup.mk z₂) :=
      map_sub ((ConcreteCategory.hom
        ((signTwistToExteriorPower B S hS X U n hsep).app V)).comp
          (QuotientAddGroup.mk' (characterRelations
            (diagonalComplement B S hS X U n hsep)
            (diagonalComplementAut B S hS X U n hsep) Equiv.Perm.sign V.unop))) z₁ z₂
    have hzero : (signTwistToExteriorPower B S hS X U n hsep).app V
        (QuotientAddGroup.mk (z₁ - z₂)) = 0 := by
      rw [e1, hx, sub_self]
    have hsub := quotient_mk_eq_zero_of_signTwistToExteriorPower_app_eq_zero
      B S hS X U n hsep V y (z₁ - z₂) hzero
    rw [e0, sub_eq_zero] at hsub
    refine (topology B S hS X).superset_covering ?_ ((topology B S hS X).top_mem V.unop)
    exact le_of_eq ((Presheaf.equalizerSieve_eq_top_iff _ _).2 hsub).symm
  · refine (topology B S hS X).superset_covering bot_le ?_
    exact bot_mem_topology_of_isEmpty_points B S hS X V.unop (not_nonempty_iff.1 hpt)

/-! ### The canonical map is an isomorphism and the Hom-identification is bijective -/

/-- **Stacks 0726.** The canonical map `ℤ(sign) ⟶ K^p` from the sign twist of `W_p` to the
`(p+1)`-st exterior power of the extension by zero of `ℤ` from `U` is an isomorphism: it is the
sheafification of a map of presheaves which is both locally injective and locally
surjective. -/
@[stacks 0726 "the canonical map ℤ(sign) ⟶ K^p is an isomorphism"]
theorem isIso_signTwistToKoszul (U : SpacesEtale B S hS X) (p : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    IsIso (signTwistToKoszul B S hS X U p hsep) := by
  have hi : Sheaf.IsLocallyInjective (signTwistToKoszul B S hS X U p hsep) :=
    (Presheaf.isLocallyInjective_presheafToSheaf_map_iff (topology B S hS X)
        (signTwistToExteriorPower B S hS X U (p + 1) hsep)).2
      (isLocallyInjective_signTwistToExteriorPower B S hS X U (p + 1) hsep)
  have hs : Sheaf.IsLocallySurjective (signTwistToKoszul B S hS X U p hsep) :=
    (Presheaf.isLocallySurjective_presheafToSheaf_map_iff (topology B S hS X)
        (signTwistToExteriorPower B S hS X U (p + 1) hsep)).2
      (isLocallySurjective_signTwistToExteriorPower B S hS X U (p + 1) hsep)
  exact (Sheaf.isLocallyBijective_iff_isIso _).1 ⟨hi, hs⟩

/-- **Stacks 0726.** The canonical map from `Hom(K^p, ℱ)` to the `S_{p+1}`-anti-invariant
sections of `ℱ` over `W_p` is bijective: it is precomposition with the isomorphism
`ℤ(sign) ⟶ K^p` followed by the identification of maps out of `ℤ(sign)` with anti-invariant
sections. -/
@[stacks 0726 "bijectivity of the map Hom(K^p, F) ⟶ anti-invariant sections"]
theorem bijective_koszulHomToSignSections (U : SpacesEtale B S hS X) (p : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    Function.Bijective (koszulHomToSignSections B S hS X U p hsep F).hom := by
  have _ := isIso_signTwistToKoszul B S hS X U p hsep
  have hpre : Function.Bijective
      (fun g : (koszulComplex B S hS X U).X p ⟶ F =>
        signTwistToKoszul B S hS X U p hsep ≫ g) := by
    refine ⟨fun g₁ g₂ h => (cancel_epi (signTwistToKoszul B S hS X U p hsep)).1 h, fun h => ?_⟩
    exact ⟨inv (signTwistToKoszul B S hS X U p hsep) ≫ h,
      IsIso.hom_inv_id_assoc (signTwistToKoszul B S hS X U p hsep) h⟩
  exact (characterTwistHomEquiv (diagonalComplement B S hS X U (p + 1) hsep)
    (diagonalComplementAut B S hS X U (p + 1) hsep) Equiv.Perm.sign
    (topology B S hS X) F).bijective.comp hpre

/-- **Stacks 0726.** The identification of `Hom(K^p, ℱ)` with the group of
`S_{p+1}`-anti-invariant sections of `ℱ` over `W_p`, as an isomorphism of abelian groups. -/
@[stacks 0726 "the map Hom(K^p, F) ⟶ anti-invariant sections is an isomorphism of groups"]
def koszulHomSignSectionsEquiv (U : SpacesEtale B S hS X) (p : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom)
    (F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) :
    ((koszulComplex B S hS X U).X p ⟶ F) ≃+
      characterSections (diagonalComplement B S hS X U (p + 1) hsep)
        (diagonalComplementAut B S hS X U (p + 1) hsep) Equiv.Perm.sign F.obj :=
  AddEquiv.ofBijective (koszulHomToSignSections B S hS X U p hsep F).hom
    (bijective_koszulHomToSignSections B S hS X U p hsep F)

/-- **Stacks 0726.** For `U` étale and separated over `X` the space
`W_p = U ×_X ⋯ ×_X U ∖ (all diagonals)` with `p + 1` factors carries a free action of the
symmetric group on `p + 1` letters over `X`, and for every abelian sheaf `ℱ` on the
spaces-étale site of `X` the canonical map from `Hom(K^p, ℱ)` to the `S_{p+1}`-anti-invariant
sections of `ℱ` over `W_p` is bijective, functorially in `ℱ`.

Freeness is stated in the shape a site asks for: a morphism `φ : V ⟶ W_p` fixed by `σ` forces
`σ = 1` unless the empty sieve covers `V`.  Surjectivity of `U ⟶ X`, which Stacks 0726 also
assumes, is not used: it is what makes the Koszul complex a resolution. -/
@[stacks 0726]
theorem freeAction_and_bijective_koszulHomToSignSections (U : SpacesEtale B S hS X) (p : ℕ)
    (hsep : IsSeparated B S hS U.1.hom.hom) :
    (∀ (V : SpacesEtale B S hS X) (φ : V ⟶ diagonalComplement B S hS X U (p + 1) hsep)
        (σ : Equiv.Perm (Fin (p + 1))),
        φ ≫ (diagonalComplementAut B S hS X U (p + 1) hsep σ).asIso.hom = φ →
          (⊥ : Sieve V) ∈ topology B S hS X V ∨ σ = 1) ∧
      (∀ F : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1},
        Function.Bijective (koszulHomToSignSections B S hS X U p hsep F).hom) ∧
      (∀ (F F' : Sheaf (topology B S hS X) AddCommGrpCat.{u + 1}) (k : F ⟶ F')
        (g : (koszulComplex B S hS X U).X p ⟶ F),
        (((koszulHomToSignSections B S hS X U p hsep F').hom (g ≫ k)).1 :
            F'.obj.obj (op (diagonalComplement B S hS X U (p + 1) hsep))) =
          k.hom.app (op (diagonalComplement B S hS X U (p + 1) hsep))
            (((koszulHomToSignSections B S hS X U p hsep F).hom g).1)) :=
  ⟨fun _ φ σ h => eq_one_of_comp_diagonalComplementAut B S hS X U (p + 1) hsep φ σ h,
    fun F => bijective_koszulHomToSignSections B S hS X U p hsep F,
    fun _ _ k g => koszulHomToSignSections_naturality B S hS X U p hsep k g⟩

end SpacesEtale

end AlgebraicGeometry.Space

end
