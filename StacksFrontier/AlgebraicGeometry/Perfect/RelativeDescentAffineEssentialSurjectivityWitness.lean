module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibres

/-!
# A closed instance of the affine case of the essential-surjectivity half of Stacks 0DI8

`AlgebraicGeometry.AffinePerfectDescent.exists_isPerfectRelativeTo_stage`
(`StacksFrontier/AlgebraicGeometry/Perfect/RelativeDescentAffineEssentialSurjectivity.lean`) carries
the affine case of the essential-surjectivity half of Stacks 0DI8 at a filtered diagram of rings:
for a filtered diagram `i ↦ Rᵢ` of `R₀`-algebras with colimit `R` and a flat `R₀`-algebra `A₀` of
finite presentation, every object of `D(𝒪_{Spec(R ⊗_{R₀} A₀)})` perfect relative to `Spec R` is
the derived pullback of an object perfect relative to `Spec Rᵢ` at some stage.

This file instantiates **every one of its binders at once, by closed terms**, so that the theorem
is exhibited as non-vacuous: the index category is `ℕ`, the diagram is the tower of polynomial
rings `R₀[x₀, …, x_{n-1}]` over `R₀ = ℤ[t]`, the cocone is the colimit cocone of that tower, and
`A₀ = R₀[y]`. The object is the structure sheaf of the limit, in degree zero, and its relative
perfectness is
`AlgebraicGeometry.AffinePerfectDescent.isPerfectRelativeTo_single_self`, which assumes nothing.

## Main definitions

* `AlgebraicGeometry.AffinePerfectDescent.polynomialTower`: the tower `n ↦ R₀[x₀, …, x_{n-1}]`,
  a filtered diagram in `CommAlgCat R₀` whose transition maps are the variable inclusions.
* `AlgebraicGeometry.AffinePerfectDescent.towerCocone`: its colimit cocone.
* `AlgebraicGeometry.AffinePerfectDescent.towerObject`: the structure sheaf of
  `Spec(R ⊗_{R₀} A₀)` in degree zero.

## Main results

* `AlgebraicGeometry.AffinePerfectDescent.exists_isPerfectRelativeTo_stage_polynomialTower`: the
  conclusion of `exists_isPerfectRelativeTo_stage` at that data, with no hypotheses.
* `AlgebraicGeometry.AffinePerfectDescent.not_surjective_polynomialTower_map`: the tower is not
  eventually constant — already the transition from stage `0` to stage `1` fails to be surjective.

## Implementation notes

**What this certifies and what it does not.** It certifies that the hypotheses of
`exists_isPerfectRelativeTo_stage` are *simultaneously satisfiable by closed terms* at a system
which is not degenerate in any of its binders: the index category is infinite and filtered, the
diagram is not eventually constant (`not_surjective_polynomialTower_map`), its colimit
`ℤ[t][x₀, x₁, …]` is not Noetherian and is not any stage, `A₀` is of relative dimension one over
`R₀`, and the object is the nonzero structure sheaf rather than a zero object. It does **not**
certify that the theorem does non-trivial descent work on this instance: the structure sheaf is
already defined at stage `0`, so the existential is witnessed there. Exhibiting an object which
exists only at a positive stage would need relative perfectness of a complex other than a single
free module, and the only unconditional producer in the tree is
`isPerfectRelativeTo_single_self`.

**Why the base ring is `ℤ[t]` and not `ℤ` or `ULift ℤ`.** The statement tensors the colimit over
the base, and for `R₀ = ℤ` the module structure on `↑c.pt` that `⊗[ℤ]` elaborates is the one from
`AddCommGroup.toIntModule`, not `Algebra.toModule` of `CommAlgCat.algebra`, so
`Algebra.TensorProduct.instCommRing` does not apply and even `Semiring (↑c.pt ⊗[ℤ] A₀)` fails to
synthesize. For `R₀ = ULift ℤ` the same happens through `ULift.module`. Any base ring with no
generic `Module R₀ _` instance works; a polynomial ring is the cheapest, and it also makes the
system less degenerate than `ℤ` would.

**No `@[stacks]` attribute.** These are statements about one particular system of rings, not
clauses of Stacks 0DI8; the tag's registration stays where it is, on
`exists_isPerfectRelativeTo_stage`.

## References

* [Stacks Project, Lemma 36.35.9 (Tag 0DI8)](https://stacks.math.columbia.edu/tag/0DI8)
* [Stacks Project, Situation 36.35.7 (Tag 0DI6)](https://stacks.math.columbia.edu/tag/0DI6)
* [Stacks Project, Lemma 15.85.7 (Tag 0DHX)](https://stacks.math.columbia.edu/tag/0DHX)
* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry StrictlyPerfect
open scoped TensorProduct
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.AffinePerfectDescent

open AlgebraicGeometry.AffineRelativeTorAmplitude

/-- The base ring `R₀ = ℤ[t]` of the witness system; see the implementation notes for why it is
not `ℤ`. -/
abbrev towerBase : Type := MvPolynomial (Fin 1) ℤ

/-- The tower `n ↦ R₀[x₀, …, x_{n-1}]` of polynomial rings over `R₀ = ℤ[t]`, a filtered diagram
in `CommAlgCat R₀` whose transition maps are the inclusions of variables. -/
def polynomialTower : ℕ ⥤ CommAlgCat.{0} towerBase where
  obj n := CommAlgCat.of towerBase (MvPolynomial (Fin n) towerBase)
  map h := CommAlgCat.ofHom (MvPolynomial.rename (Fin.castLE (leOfHom h)))
  map_id n := by
    ext x
    simp [MvPolynomial.rename_id]
  map_comp f g := by
    ext x
    simp

/-- The colimit cocone of the tower; its vertex is the polynomial ring on countably many
variables over `R₀`. -/
def towerCocone : Cocone polynomialTower := colimit.cocone polynomialTower

/-- The flat `R₀`-algebra of finite presentation the tower is tensored with: `A₀ = R₀[y]`. -/
abbrev towerFibre : Type := MvPolynomial (Fin 1) towerBase

/-- The limit algebra `A = R ⊗_{R₀} A₀` of the witness system. -/
abbrev towerLimitAlgebra : Type := (towerCocone.pt : Type) ⊗[towerBase] towerFibre

/-- The object of `D(𝒪_{Spec A})` the witness is taken at: the structure sheaf, in degree zero.
It is nonzero. -/
abbrev towerObject : DerivedCategory (OXMod.{0, 0}
    (Spec (CommRingCat.of towerLimitAlgebra)).toRingedSpace) :=
  tildeObj towerLimitAlgebra
    ((CochainComplex.singleFunctor (ModuleCat.{0} towerLimitAlgebra) 0).obj
      (ModuleCat.of _ towerLimitAlgebra))

/-- **The affine case of the essential-surjectivity half of Stacks 0DI8, with every binder
instantiated by a closed term.** For the tower `n ↦ ℤ[t][x₀, …, x_{n-1}]`, its colimit cocone and
`A₀ = ℤ[t][y]`, the structure sheaf of `Spec(R ⊗_{R₀} A₀)` in degree zero is, at some stage `i`,
the derived pullback of an object of `D(𝒪_{Spec(Rᵢ ⊗_{R₀} A₀)})` perfect relative to `Spec Rᵢ`.

The colimit hypothesis is `PseudoCoherence.isColimit_mapCocone_commAlgCat_uliftFunctor` applied
to `CategoryTheory.Limits.colimit.isColimit`, and the relative perfectness of the object is
`isPerfectRelativeTo_single_self`; neither assumes anything. See the implementation notes for
what this does and does not certify. -/
theorem exists_isPerfectRelativeTo_stage_polynomialTower :
    ∃ (i : ℕ) (Ei : DerivedCategory (OXMod.{0, 0}
        (Spec (CommRingCat.of
          (PseudoCoherence.stageAlgebra polynomialTower towerFibre i))).toRingedSpace)),
      (specMap (polynomialTower.obj i)
            (PseudoCoherence.stageAlgebra polynomialTower towerFibre i)).IsPerfectRelativeTo
          (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) Ei ∧
        Nonempty ((derivedPullback (Spec.map (CommRingCat.ofHom
          (PseudoCoherence.stageToLimitMap towerCocone towerFibre i))).toLRSHom.toShHom).obj Ei ≅
            towerObject) :=
  exists_isPerfectRelativeTo_stage polynomialTower towerCocone
    (PseudoCoherence.isColimit_mapCocone_commAlgCat_uliftFunctor
      (colimit.isColimit polynomialTower))
    towerFibre towerObject (isPerfectRelativeTo_single_self _ _)

/-- **The witness system is not degenerate in its index**: already the transition from stage `0`
to stage `1` of the tower is not surjective, so the tower is not eventually constant and no stage
is its colimit. A polynomial over no variables is a constant, constants are carried to constants
by `MvPolynomial.rename`, and `x₀` is not a constant. -/
theorem not_surjective_polynomialTower_map :
    ¬ Function.Surjective (polynomialTower.map (homOfLE (Nat.zero_le 1))).hom := by
  intro hsurj
  obtain ⟨p, hp⟩ := hsurj (MvPolynomial.X (0 : Fin 1))
  rw [p.eq_C_of_isEmpty] at hp
  have h := congrArg MvPolynomial.totalDegree ((MvPolynomial.rename_C _ _).symm.trans hp)
  rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X] at h
  exact zero_ne_one h

end AlgebraicGeometry.AffinePerfectDescent

end
