module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import StacksCore.Tactic.StacksAttribute

/-!
# Projective space

Projective `n`-space over the integers is `Proj ℤ[T₀, …, Tₙ]` for the grading by total degree.
Projective `n`-space over a scheme `S`, or over a commutative ring `R`, is its base change from
the integers: the terminal scheme is `Spec ℤ`, so a pullback over the terminal object expresses
exactly that base change, and the structure morphism of `ℙⁿ_S` is the first projection.

A base scheme in universe `u` forces its integral model into universe `u` as well, so the
coefficient ring of the model used for the base change is the canonical universe copy
`ULift.{u} ℤ`. At universe zero that model is canonically identified with the literal
`Proj ℤ[T₀, …, Tₙ]` by `projectiveSpaceIntegralIso`, which is `Proj` applied to the graded ring
isomorphism induced by `ULift.ringEquiv`.

## Main definitions

* `AlgebraicGeometry.projectiveSpace`: projective `n`-space over the integers.
* `AlgebraicGeometry.projectiveSpaceAtUniverse`: its canonical universe copy.
* `AlgebraicGeometry.projectiveSpaceIntegralIso`: the comparison of the two integral models.
* `AlgebraicGeometry.projectiveSpaceOver`: projective `n`-space over a scheme.
* `AlgebraicGeometry.projectiveSpaceOverRing`: projective `n`-space over a ring.

## Implementation notes

The grading is by total degree, with the variables indexed by `Fin (n + 1)`; the required
`GradedAlgebra` instance on `MvPolynomial.homogeneousSubmodule` is `MvPolynomial.gradedAlgebra`,
supplied locally at each use because it is not a global instance.

The comparison of integral models is built from `AlgebraicGeometry.Proj.map`, which needs the
irrelevant ideal of the target to be contained in the image of the irrelevant ideal of the
source; for a graded ring isomorphism that containment holds for both directions at once, which
is why it is proved once as a statement universally quantified over the coefficient rings.

`projectiveSpaceOver` and `projectiveSpaceOverRing` are abbreviations, so that the pullback API
applies to them directly; the structure morphism is recorded as a `CanonicallyOver` instance
rather than as a separate definition.

## References

* [Stacks Project, Tag 01NF](https://stacks.math.columbia.edu/tag/01NF)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits

namespace AlgebraicGeometry

universe u

/-- Projective `n`-space over the integers. -/
@[stacks 01NF "projective space over the integers"]
public noncomputable def projectiveSpace (n : ℕ) : Scheme.{0} := by
  let : GradedAlgebra
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℤ) :=
    MvPolynomial.gradedAlgebra
  exact AlgebraicGeometry.Proj
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℤ)

/-- The integral model of projective space in the universe of the base scheme. -/
public noncomputable def projectiveSpaceAtUniverse (n : ℕ) : Scheme.{u} := by
  let : GradedAlgebra
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) :=
    MvPolynomial.gradedAlgebra
  exact AlgebraicGeometry.Proj
    (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))

/-- The canonical comparison between the literal integral model and its universe-zero copy. -/
@[stacks 01NF "canonical comparison of integral models"]
public noncomputable def projectiveSpaceIntegralIso (n : ℕ) :
    projectiveSpace n ≅ projectiveSpaceAtUniverse.{0} n := by
  let gradedPolynomialMap {R S : Type} [CommRing R] [CommRing S]
      (e : R ≃+* S) :
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R →+*ᵍ
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S :=
    { toRingHom := (MvPolynomial.mapEquiv (Fin (n + 1)) e).toRingHom
      map_mem := by
        intro i x hx
        exact hx.map e.toRingHom }
  have irrelevant_le_map_gradedPolynomialMap :
      ∀ {R S : Type} [CommRing R] [CommRing S] (e : R ≃+* S),
        let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) :=
          MvPolynomial.gradedAlgebra
        let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S) :=
          MvPolynomial.gradedAlgebra
        HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S) ≤
          (HomogeneousIdeal.irrelevant
            (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)).map
            (gradedPolynomialMap e) := by
    intro R S _ _ e
    let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) :=
      MvPolynomial.gradedAlgebra
    let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) S) :=
      MvPolynomial.gradedAlgebra
    apply (HomogeneousIdeal.irrelevant_le _).2
    intro i hi x hx
    let y : MvPolynomial (Fin (n + 1)) R :=
      (MvPolynomial.mapEquiv (Fin (n + 1)) e).symm x
    have hy : y ∈ MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R i := by
      exact hx.map e.symm.toRingHom
    have hxy : gradedPolynomialMap e y = x := by
      exact (MvPolynomial.mapEquiv (Fin (n + 1)) e).apply_symm_apply x
    rw [← hxy]
    exact Ideal.mem_map_of_mem (gradedPolynomialMap e)
      (HomogeneousIdeal.mem_irrelevant_of_mem _ hi hy)
  let : GradedAlgebra (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℤ) :=
    MvPolynomial.gradedAlgebra
  let : GradedAlgebra
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)) :=
    MvPolynomial.gradedAlgebra
  let e : ℤ ≃+* ULift.{0} ℤ := ULift.ringEquiv.symm
  let f := gradedPolynomialMap e
  let g := gradedPolynomialMap e.symm
  have hf := irrelevant_le_map_gradedPolynomialMap e
  have hg := irrelevant_le_map_gradedPolynomialMap e.symm
  refine ⟨AlgebraicGeometry.Proj.map g hg, AlgebraicGeometry.Proj.map f hf, ?_, ?_⟩
  · have h : g.comp f = GradedRingHom.id
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) ℤ) :=
      GradedRingHom.ext fun x => (MvPolynomial.mapEquiv (Fin (n + 1)) e).symm_apply_apply x
    exact (AlgebraicGeometry.Proj.map_comp f g hf hg).symm.trans (by
      simp only [h, AlgebraicGeometry.Proj.map_id, projectiveSpace])
  · have h : f.comp g = GradedRingHom.id
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{0} ℤ)) :=
      GradedRingHom.ext fun x => (MvPolynomial.mapEquiv (Fin (n + 1)) e).apply_symm_apply x
    exact (AlgebraicGeometry.Proj.map_comp g f hg hf).symm.trans (by
      simp only [h, AlgebraicGeometry.Proj.map_id, projectiveSpaceAtUniverse])

/-- Projective `n`-space over `S`, by base change from the integers. -/
@[stacks 01NF "projective space over a scheme"]
public noncomputable abbrev projectiveSpaceOver (n : ℕ) (S : Scheme.{u}) : Scheme.{u} :=
  pullback (terminal.from S) (terminal.from (projectiveSpaceAtUniverse.{u} n))

namespace projectiveSpaceOver

/-- The canonical structure morphism of projective space over `S`. -/
public noncomputable instance over (n : ℕ) (S : Scheme.{u}) :
    (projectiveSpaceOver n S).CanonicallyOver S where
  hom := pullback.fst _ _

/-- The projection to the integral model in the universe of `S`. -/
public noncomputable abbrev toIntegralAtUniverse (n : ℕ) (S : Scheme.{u}) :
    projectiveSpaceOver n S ⟶ projectiveSpaceAtUniverse.{u} n :=
  pullback.snd _ _

/-- The projection to the literal integral model at universe zero. -/
public noncomputable def toIntegral (n : ℕ) (S : Scheme.{0}) :
    projectiveSpaceOver n S ⟶ projectiveSpace n :=
  toIntegralAtUniverse n S ≫ (projectiveSpaceIntegralIso n).inv

/-- The universal lift from an `S`-scheme with a map to the literal integral model. -/
public noncomputable def lift {X S : Scheme.{0}} (n : ℕ) (f : X ⟶ S)
    (g : X ⟶ projectiveSpace n) : X ⟶ projectiveSpaceOver n S :=
  pullback.lift f (g ≫ (projectiveSpaceIntegralIso n).hom) (by simp)

/-- The lift `lift n f g` composed with the structure projection to `S` is `f`. -/
@[simp] public theorem lift_fst {X S : Scheme.{0}} (n : ℕ) (f : X ⟶ S)
    (g : X ⟶ projectiveSpace n) :
    lift n f g ≫ pullback.fst _ _ = f :=
  pullback.lift_fst _ _ _

/-- The lift `lift n f g` composed with `toIntegral n S` is `g`. -/
@[simp] public theorem lift_toIntegral {X S : Scheme.{0}} (n : ℕ) (f : X ⟶ S)
    (g : X ⟶ projectiveSpace n) :
    lift n f g ≫ toIntegral n S = g := by
  dsimp [lift, toIntegral, toIntegralAtUniverse]
  rw [← Category.assoc, pullback.lift_snd, Category.assoc]
  simp

end projectiveSpaceOver

/-- Projective `n`-space over a commutative ring `R`. -/
@[stacks 01NF "projective space over a ring"]
public noncomputable abbrev projectiveSpaceOverRing (n : ℕ) (R : CommRingCat.{u}) : Scheme.{u} :=
  projectiveSpaceOver n (Spec R)

end AlgebraicGeometry
