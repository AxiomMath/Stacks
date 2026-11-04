module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.SplitNode
public import StacksFrontier.AlgebraicGeometry.Curves.NodeQuadraticAlgebra.SeparableTower
public import StacksFrontier.AlgebraicGeometry.Curves.NormalizationClosedFibre
import all StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra

/-!
# The quadratic relation of a node, and its splitting, after an extension of the residue field

Let `A` be the local ring of a node and let `A → B` be a local homomorphism which *extends the
maximal ideal*, that is, `𝔪_A B = 𝔪_B`. The local ring of the base change of a curve along a
field extension at a point above the node is of this shape (Stacks Tag 0C50), and so is the
local ring of an étale neighbourhood. Then the nodal quadratic relation of Stacks Tag 0C49 at
`A` is carried to one at `B` with the *same* coefficients, read in the residue field of `B`:
lifts of a cotangent basis generate `𝔪_A`, hence their images generate `𝔪_B`, hence — the
cotangent space of `B` being two-dimensional — they are lifts of a cotangent basis of `B`, and
the relation itself is the image of the relation downstairs.

This is the base change of the quadratic relation, and it is what makes the reduction of Stacks
Tag 0CBY to a split node work. The quadratic algebra of a node is the quadratic polynomial
algebra `κ[T]/(a T² + b T + c)` of its relation
(`Stacks.Curves.quadraticAlgebra_equiv_adjoinRoot`, Stacks Tag 0CBT); since the coefficients are
unchanged, the quadratic algebra at a point of the base change is the *same* polynomial algebra
read over the larger residue field, so it splits as soon as that residue field contains a root
of `a T² + b T + c`. No base change of the normalization is needed, and the degree-two algebra
upstairs is thereby identified with `κ' ⊗_κ κ_B` without the tensor product being formed.

## Main results

* `Stacks.Curves.exists_nodalQuadraticRelation_map_of_map_maximalIdeal_eq` — the quadratic
  relation of Stacks Tag 0C49 transports, with its coefficients, along a local homomorphism
  which extends the maximal ideal.
* `Stacks.Curves.nonempty_quadraticAlgebra_algEquiv_adjoinRoot_map_of_map_maximalIdeal_eq` — the
  quadratic algebra upstairs is the quadratic polynomial algebra of the *same* coefficients.
* `Stacks.Curves.nonempty_quadraticAlgebra_algEquiv_prod_of_map_maximalIdeal_eq_of_isRoot` —
  the quadratic algebra upstairs splits when the residue field upstairs contains a root of the
  quadratic polynomial downstairs.
* `Stacks.Curves.nonempty_quadraticAlgebra_algEquiv_prod_of_map_maximalIdeal_eq_of_ringHom` — the
  same with the root replaced by a `κ`-algebra map out of the quadratic algebra, which is what it
  amounts to.
* `Stacks.Curves.exists_finiteSeparable_algHom_of_isMaximal` — a maximal ideal of a finite
  separable algebra over a field has a quotient which is a finite separable field extension.
* `Stacks.Curves.exists_finiteSeparable_algHom_quadraticAlgebra` — such a `κ`-algebra map exists
  into a finite separable extension of `κ`, namely the residue field of a maximal ideal of the
  quadratic algebra. This is the choice of `κ(v)` in the reduction of Stacks Tag 0CBY to a split
  node, made without the case distinction of the source.
* `Stacks.Curves.exists_finiteSeparable_algHom_quadraticAlgebra_over_base` — the same read over
  the ground field, which is the shape Stacks Tag 02LF consumes.

## Implementation notes

Two-dimensionality of the cotangent space of `B` is a hypothesis rather than a consequence: it
is what flatness of `A → B` would buy, and at the use site it comes instead from `B` being the
local ring of a node, which is known independently by the invariance of the node condition under
extension of the ground field (Stacks Tag 0C56). Taking it as a hypothesis keeps this file free
of any flatness theory.

The coefficients are carried as elements of `A` and their images under `algebraMap A B`, not as
residues; `IsLocalRing.ResidueField.map` of a local homomorphism is a homomorphism of fields and
hence injective, which is how nondegeneracy of the discriminant survives.

## References

* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
* [Stacks Project, Tag 0CBT](https://stacks.math.columbia.edu/tag/0CBT)
* [Stacks Project, Tag 0CBU](https://stacks.math.columbia.edu/tag/0CBU)
* [Stacks Project, Tag 0CBY](https://stacks.math.columbia.edu/tag/0CBY)
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

universe u v w

namespace Stacks.Curves

section ResidueFieldExtension

variable {A : Type w} {B : Type v} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  [CommRing B] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B]
  [IsLocalHom (algebraMap A B)]

omit [IsLocalHom (algebraMap A B)] in
/-- **The nodal quadratic relation transports along a local homomorphism which extends the
maximal ideal**, with its coefficients carried along `algebraMap A B`.

Lifts `x, y` of a cotangent basis generate `𝔪_A`, so their images generate
`𝔪_A B = 𝔪_B`; the cotangent space of `B` being two-dimensional, the images are therefore
lifts of a cotangent basis of `B`, and the relation upstairs is the image of the relation
downstairs. -/
theorem exists_nodalQuadraticRelation_map_of_map_maximalIdeal_eq
    (hmax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    (hfin : Module.finrank (ResidueField B) (CotangentSpace B) = 2)
    (x y : maximalIdeal A)
    (e : Module.Basis (BinaryIndex (ResidueField A)) (ResidueField A) (CotangentSpace A))
    (hx : e ⟨0⟩ = (maximalIdeal A).toCotangent x)
    (hy : e ⟨1⟩ = (maximalIdeal A).toCotangent y)
    (a b c : A)
    (hrel : a * (x : A) ^ 2 + b * (x : A) * (y : A) + c * (y : A) ^ 2 ∈ maximalIdeal A ^ 3) :
    ∃ (x' y' : maximalIdeal B)
      (e' : Module.Basis (BinaryIndex (ResidueField B)) (ResidueField B) (CotangentSpace B)),
      (x' : B) = algebraMap A B (x : A) ∧ (y' : B) = algebraMap A B (y : A) ∧
        e' ⟨0⟩ = (maximalIdeal B).toCotangent x' ∧
          e' ⟨1⟩ = (maximalIdeal B).toCotangent y' ∧
            algebraMap A B a * (x' : B) ^ 2 +
                algebraMap A B b * (x' : B) * (y' : B) +
                  algebraMap A B c * (y' : B) ^ 2 ∈ maximalIdeal B ^ 3 := by
  have hmemx : algebraMap A B (x : A) ∈ maximalIdeal B :=
    hmax ▸ Ideal.mem_map_of_mem (algebraMap A B) x.2
  have hmemy : algebraMap A B (y : A) ∈ maximalIdeal B :=
    hmax ▸ Ideal.mem_map_of_mem (algebraMap A B) y.2
  have hspanB : Ideal.span ({algebraMap A B (x : A), algebraMap A B (y : A)} : Set B) =
      maximalIdeal B := by
    have hspan : Ideal.map (algebraMap A B) (Ideal.span ({(x : A), (y : A)} : Set A)) =
        Ideal.span ({algebraMap A B (x : A), algebraMap A B (y : A)} : Set B) := by
      rw [Ideal.map_span, Set.image_pair]
    rw [← hspan, ← maximalIdeal_eq_span_of_cotangent_basis x y e hx hy, hmax]
  obtain ⟨e', he₀, he₁⟩ := exists_cotangent_basis_of_pair_generators_and_finrank_two B
    ⟨_, hmemx⟩ ⟨_, hmemy⟩ hspanB hfin
  refine ⟨⟨_, hmemx⟩, ⟨_, hmemy⟩, e', rfl, rfl, he₀, he₁, ?_⟩
  have hmap : algebraMap A B a * algebraMap A B (x : A) ^ 2 +
        algebraMap A B b * algebraMap A B (x : A) * algebraMap A B (y : A) +
          algebraMap A B c * algebraMap A B (y : A) ^ 2 =
      algebraMap A B (a * (x : A) ^ 2 + b * (x : A) * (y : A) + c * (y : A) ^ 2) := by
    simp only [map_add, map_mul, map_pow]
  rw [show ((⟨_, hmemx⟩ : maximalIdeal B) : B) = algebraMap A B (x : A) from rfl,
    show ((⟨_, hmemy⟩ : maximalIdeal B) : B) = algebraMap A B (y : A) from rfl, hmap, ← hmax,
    ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hrel

omit [IsNoetherianRing A] [IsNoetherianRing B] in
/-- The leading coefficient of the transported relation is the image of the leading
coefficient, hence still nonzero. -/
private theorem residue_leadingCoeff_map_ne_zero (a : A) (ha : residue A a ≠ 0) :
    residue B (algebraMap A B a) ≠ 0 := by
  rw [← ResidueField.map_residue (algebraMap A B)]
  exact fun h => ha ((RingHom.injective (ResidueField.map (algebraMap A B)))
    (h.trans (map_zero _).symm))

omit [IsNoetherianRing A] [IsNoetherianRing B] in
/-- The discriminant of the transported relation is the image of the discriminant, hence still
nonzero: a homomorphism of residue fields is injective. -/
private theorem residue_discriminant_map_ne_zero (a b c : A)
    (hdisc : residue A (4 * a * c - b ^ 2) ≠ 0) :
    residue B (4 * algebraMap A B a * algebraMap A B c - algebraMap A B b ^ 2) ≠ 0 := by
  simpa only [map_sub, map_mul, map_pow, map_ofNat] using
    residue_leadingCoeff_map_ne_zero (B := B) _ hdisc

/-- **The quadratic algebra of a node is the same quadratic polynomial algebra after a local
homomorphism which extends the maximal ideal.** The coefficients of the quadratic polynomial of
Stacks Tag 0CBT are the residues of the coefficients of the quadratic relation of Stacks Tag
0C49, and those transport with the relation, so the polynomial upstairs is the polynomial
downstairs read over the larger residue field. -/
theorem nonempty_quadraticAlgebra_algEquiv_adjoinRoot_map_of_map_maximalIdeal_eq
    (K : Type u) [Field K] [Algebra K B] (hB : IsNodalAlgebra K B)
    (hmax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    (x y : maximalIdeal A)
    (e : Module.Basis (BinaryIndex (ResidueField A)) (ResidueField A) (CotangentSpace A))
    (hx : e ⟨0⟩ = (maximalIdeal A).toCotangent x)
    (hy : e ⟨1⟩ = (maximalIdeal A).toCotangent y)
    (a b c : A) (ha : residue A a ≠ 0)
    (hdisc : residue A (4 * a * c - b ^ 2) ≠ 0)
    (hrel : a * (x : A) ^ 2 + b * (x : A) * (y : A) + c * (y : A) ^ 2 ∈ maximalIdeal A ^ 3) :
    Nonempty (quadraticAlgebra B ≃ₐ[ResidueField B]
      AdjoinRoot (C (residue B (algebraMap A B a)) * X ^ 2 +
        C (residue B (algebraMap A B b)) * X + C (residue B (algebraMap A B c)))) := by
  have hfin : Module.finrank (ResidueField B) (CotangentSpace B) = 2 :=
    finrank_cotangentSpace_eq_two_of_hasNodalQuadraticRelation hB.2.2
  obtain ⟨x', y', e', -, -, hx', hy', hrel'⟩ :=
    exists_nodalQuadraticRelation_map_of_map_maximalIdeal_eq hmax hfin x y e hx hy a b c hrel
  exact quadraticAlgebra_equiv_adjoinRoot K B hB x' y' e' hx' hy'
    (algebraMap A B a) (algebraMap A B b) (algebraMap A B c)
    (residue_leadingCoeff_map_ne_zero a ha) (residue_discriminant_map_ne_zero a b c hdisc) hrel'

/-- **The quadratic algebra of a node splits after a local homomorphism which extends the
maximal ideal, as soon as the residue field upstairs contains a root of the quadratic polynomial
of the node.** This is the base change of the quadratic relation of Stacks Tag 0C49 followed by
the splitting criterion for a quadratic polynomial with a root; it is the step by which Stacks
Tag 0CBY reduces to a split node. -/
theorem nonempty_quadraticAlgebra_algEquiv_prod_of_map_maximalIdeal_eq_of_isRoot
    (K : Type u) [Field K] [Algebra K B] (hB : IsNodalAlgebra K B)
    (hmax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    (x y : maximalIdeal A)
    (e : Module.Basis (BinaryIndex (ResidueField A)) (ResidueField A) (CotangentSpace A))
    (hx : e ⟨0⟩ = (maximalIdeal A).toCotangent x)
    (hy : e ⟨1⟩ = (maximalIdeal A).toCotangent y)
    (a b c : A) (ha : residue A a ≠ 0)
    (hdisc : residue A (4 * a * c - b ^ 2) ≠ 0)
    (hrel : a * (x : A) ^ 2 + b * (x : A) * (y : A) + c * (y : A) ^ 2 ∈ maximalIdeal A ^ 3)
    (r : ResidueField B)
    (hroot : ResidueField.map (algebraMap A B) (residue A a) * r ^ 2 +
      ResidueField.map (algebraMap A B) (residue A b) * r +
        ResidueField.map (algebraMap A B) (residue A c) = 0) :
    Nonempty (quadraticAlgebra B ≃ₐ[ResidueField B] (ResidueField B × ResidueField B)) := by
  obtain ⟨e₁⟩ := nonempty_quadraticAlgebra_algEquiv_adjoinRoot_map_of_map_maximalIdeal_eq
    K hB hmax x y e hx hy a b c ha hdisc hrel
  have hdisc' : 4 * residue B (algebraMap A B a) * residue B (algebraMap A B c) -
      residue B (algebraMap A B b) ^ 2 ≠ 0 := by
    simpa only [map_sub, map_mul, map_pow, map_ofNat] using
      residue_discriminant_map_ne_zero (B := B) a b c hdisc
  rw [ResidueField.map_residue, ResidueField.map_residue, ResidueField.map_residue] at hroot
  obtain ⟨e₂⟩ := nonempty_adjoinRoot_algEquiv_prod_of_isRoot (ResidueField B)
    (residue B (algebraMap A B a)) (residue B (algebraMap A B b))
    (residue B (algebraMap A B c)) (residue_leadingCoeff_map_ne_zero a ha) hdisc' r hroot
  exact ⟨e₁.trans e₂⟩

/-- **A `κ`-algebra map from the quadratic algebra of a node to the residue field upstairs makes
the node split upstairs.** This is the basis-free form of the previous result: the quadratic
algebra `κ'` is `κ[T]/(a T² + b T + c)`, so a `κ`-algebra map `κ' → κ_B` is exactly a root of
that polynomial in `κ_B`, and the polynomial upstairs is the same one. Equivalently, it says that
`κ' ⊗_κ κ_B` splits — the tensor product never being formed.

The `κ`-algebra map is carried as a ring homomorphism together with its commutation with the two
structure maps, so that no algebra structure on `ResidueField B` over `ResidueField A` need be
installed. -/
theorem nonempty_quadraticAlgebra_algEquiv_prod_of_map_maximalIdeal_eq_of_ringHom
    (k K : Type u) [Field k] [Field K] [Algebra k A] [Algebra K B]
    (hA : IsNodalAlgebra k A) (hB : IsNodalAlgebra K B)
    (hmax : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B)
    (ψ : quadraticAlgebra A →+* ResidueField B)
    (hψ : ∀ z : ResidueField A,
      ψ (algebraMap (ResidueField A) (quadraticAlgebra A) z) =
        ResidueField.map (algebraMap A B) z) :
    Nonempty (quadraticAlgebra B ≃ₐ[ResidueField B] (ResidueField B × ResidueField B)) := by
  obtain ⟨x, y, e, a, b, c, hx, hy, ha, hdisc, hrel⟩ :=
    exists_nodalQuadraticRelation_nonzero k A hA
  obtain ⟨eA⟩ := quadraticAlgebra_equiv_adjoinRoot k A hA x y e hx hy a b c ha hdisc hrel
  have hχof : (ψ.comp eA.symm.toAlgHom.toRingHom).comp
        (AdjoinRoot.of (C (residue A a) * X ^ 2 + C (residue A b) * X + C (residue A c))) =
      ResidueField.map (algebraMap A B) := by
    refine RingHom.ext fun z => ?_
    show ψ (eA.symm (AdjoinRoot.of _ z)) = _
    rw [show AdjoinRoot.of
          (C (residue A a) * X ^ 2 + C (residue A b) * X + C (residue A c)) z =
        algebraMap (ResidueField A) (AdjoinRoot
          (C (residue A a) * X ^ 2 + C (residue A b) * X + C (residue A c))) z from rfl,
      AlgEquiv.commutes]
    exact hψ z
  have hroot0 : (C (residue A a) * X ^ 2 + C (residue A b) * X +
        C (residue A c)).eval₂ (ResidueField.map (algebraMap A B))
      ((ψ.comp eA.symm.toAlgHom.toRingHom) (AdjoinRoot.root
        (C (residue A a) * X ^ 2 + C (residue A b) * X + C (residue A c)))) = 0 := by
    rw [← hχof, ← hom_eval₂, AdjoinRoot.eval₂_root, map_zero]
  refine nonempty_quadraticAlgebra_algEquiv_prod_of_map_maximalIdeal_eq_of_isRoot K hB hmax
    x y e hx hy a b c ha hdisc hrel
    ((ψ.comp eA.symm.toAlgHom.toRingHom) (AdjoinRoot.root
      (C (residue A a) * X ^ 2 + C (residue A b) * X + C (residue A c)))) ?_
  simpa only [eval₂_add, eval₂_mul, eval₂_C, eval₂_X_pow, eval₂_X] using hroot0

end ResidueFieldExtension

/-! ### The finite separable extension of the residue field that splits the node -/

section SplittingField

/-- **At a maximal ideal of a finite separable algebra over a field the quotient is a finite
separable field extension of the base**, receiving the quotient map.

Stated at an abstract algebra and an abstract ideal, and only then instantiated at the quadratic
algebra: applied directly to a maximal ideal of `Stacks.Curves.quadraticAlgebra A`, whose term
carries the whole description of the normalization, instance synthesis for the module structure
on the quotient exhausts the default budget. The same device is used in
`Stacks.Curves.isSeparableExtension_residueField_integralClosure_fractionRing`. -/
theorem exists_finiteSeparable_algHom_of_isMaximal (κ : Type u) (T : Type v) [Field κ]
    [CommRing T] [Algebra κ T] [Module.Finite κ T] [Algebra.IsSeparable κ T]
    (m : Ideal T) (hm : m.IsMaximal) :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra κ L) (_ : Module.Finite κ L)
      (_ : Algebra.IsSeparable κ L), Nonempty (T →ₐ[κ] L) := by
  let : m.IsMaximal := hm
  let : Field (T ⧸ m) := Ideal.Quotient.field m
  exact ⟨T ⧸ m, ‹Field (T ⧸ m)›, inferInstance,
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ κ m).toLinearMap Ideal.Quotient.mk_surjective,
    isSeparable_quotient κ m, ⟨Ideal.Quotient.mkₐ κ m⟩⟩

/-- **The quadratic algebra of a node acquires a rational point over a finite separable extension
of the residue field.** The quadratic algebra is a separable algebra of degree two over `κ`
(Stacks Tag 0CBT), so the residue field `L` of any of its maximal ideals is a finite separable
extension of `κ` receiving a `κ`-algebra map from it.

This is the choice of the residue field `κ(v)` in the reduction of Stacks Tag 0CBY to a split
node: the source distinguishes the case where the quadratic algebra is `κ × κ`, where `κ(v)`
realizes `κ(x)/κ(s)`, from the case where it is a field, where `κ(v)` realizes `κ'/κ(s)`; taking
the residue field of a maximal ideal covers both without a case distinction. -/
theorem exists_finiteSeparable_algHom_quadraticAlgebra (k : Type u) (A : Type v) [Field k]
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A] (hA : IsNodalAlgebra k A) :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra (ResidueField A) L)
      (_ : Module.Finite (ResidueField A) L)
      (_ : Algebra.IsSeparable (ResidueField A) L),
      Nonempty (quadraticAlgebra A →ₐ[ResidueField A] L) := by
  have hfinite : Module.Finite (ResidueField A) (quadraticAlgebra A) :=
    finite_quadraticAlgebra_of_isNodalAlgebra k A hA
  have hsep : Algebra.IsSeparable (ResidueField A) (quadraticAlgebra A) :=
    isSeparable_quadraticAlgebra_of_isNodalAlgebra k A hA
  have hnt : Nontrivial (quadraticAlgebra A) := by
    refine Module.nontrivial_of_finrank_pos (R := ResidueField A) ?_
    rw [finrank_quadraticAlgebra_of_isNodalAlgebra k A hA]
    norm_num
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (quadraticAlgebra A)
  exact exists_finiteSeparable_algHom_of_isMaximal (ResidueField A) (quadraticAlgebra A) m hm

/-- **The residue field that splits the node is a finite separable extension of the ground
field.** Composing the two steps of the tower `k ⊆ κ ⊆ L` turns
`Stacks.Curves.exists_finiteSeparable_algHom_quadraticAlgebra` into the shape that Stacks Tag
02LF consumes, so that `L` is realized as the residue field of an étale neighbourhood of the
base point.

Finiteness of `κ/k` is a hypothesis: nodality alone gives only separability of `κ/k`, and
finiteness comes at the use site from `x` being a closed point of a scheme locally of finite
type over `k`. -/
theorem exists_finiteSeparable_algHom_quadraticAlgebra_over_base (k : Type u) (A : Type v)
    [Field k] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra k A]
    (hA : IsNodalAlgebra k A) (hfin : Module.Finite k (ResidueField A)) :
    ∃ (L : Type v) (_ : Field L) (_ : Algebra (ResidueField A) L) (_ : Algebra k L)
      (_ : IsScalarTower k (ResidueField A) L) (_ : Module.Finite k L)
      (_ : Algebra.IsSeparableExtension k L),
      Nonempty (quadraticAlgebra A →ₐ[ResidueField A] L) := by
  obtain ⟨L, hfld, halg, hfinL, hsepL, ⟨ψ⟩⟩ :=
    exists_finiteSeparable_algHom_quadraticAlgebra k A hA
  let : Field L := hfld
  let : Algebra (ResidueField A) L := halg
  let : Module.Finite (ResidueField A) L := hfinL
  let : Algebra.IsSeparable (ResidueField A) L := hsepL
  let : Algebra k L :=
    ((algebraMap (ResidueField A) L).comp (algebraMap k (ResidueField A))).toAlgebra
  let : IsScalarTower k (ResidueField A) L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : Algebra.IsSeparableExtension k (ResidueField A) := hA.1
  exact ⟨L, hfld, halg, ‹Algebra k L›, ‹IsScalarTower k (ResidueField A) L›,
    Module.Finite.trans (ResidueField A) L,
    Algebra.IsSeparableExtension.trans_of_isSeparable k (ResidueField A) L, ⟨ψ⟩⟩

end SplittingField

end Stacks.Curves

end
