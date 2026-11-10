module

public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.FieldTheory.FinTrdeg
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Formula

/-!
# The dimension of a fibre at a point

Let `f : X ⟶ S` be locally of finite type and let `x` be a point of `X`. The dimension of the
scheme-theoretic fibre `X_{f(x)}` at `x` is the Krull dimension of the local ring of the fibre
at `x` plus the transcendence degree of `κ(x)` over `κ(f(x))`.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk_add_trdeg` is the
  dimension formula for a scheme-theoretic fibre at a point.

## Implementation notes

The point of the fibre determined by `x` is `AlgebraicGeometry.Scheme.Hom.asFiber`, and the
residue field extension is the one induced by `AlgebraicGeometry.Scheme.Hom.residueFieldMap`,
supplied by a `letI` inside the statement. Since transcendence degree is cardinal-valued while
dimensions take values in `WithBot ℕ∞`, it is compared through `Cardinal.toENat`.

## References

* [Stacks Project, Tag 02FX](https://stacks.math.columbia.edu/tag/02FX)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Evaluation at a point of the spectrum of a residue field is bijective. -/
private theorem bijective_specResidueField_Γevaluation {X : Scheme.{u}} (x : X)
    (y : Spec (X.residueField x)) :
    Function.Bijective ((Scheme.ΓSpecIso (X.residueField x)).inv ≫
      (Spec (X.residueField x)).Γevaluation y).hom := by
  have hp : y.asIdeal.IsPrime := y.isPrime
  have hmax : y.asIdeal.IsMaximal := by
    simpa [y.asIdeal.eq_bot_of_prime] using
      (Ideal.bot_isMaximal : (⊥ : Ideal (X.residueField x)).IsMaximal)
  have hcat : (Scheme.ΓSpecIso (X.residueField x)).inv ≫
      (Spec (X.residueField x)).Γevaluation y =
      CommRingCat.ofHom (algebraMap (X.residueField x) y.asIdeal.ResidueField) ≫
        (Scheme.Spec.residueFieldIso (X.residueField x) y).inv := by
    rw [Scheme.Spec.algebraMap_residueFieldIso_inv]
    rfl
  rw [hcat]
  change Function.Bijective
    ((Scheme.Spec.residueFieldIso (X.residueField x) y).inv.hom.comp
      (algebraMap (X.residueField x) y.asIdeal.ResidueField))
  rw [RingHom.coe_comp]
  refine Function.Bijective.comp ?_ ?_
  · exact (Scheme.Spec.residueFieldIso (X.residueField x)
      y).symm.commRingCatIsoToRingEquiv.bijective
  · exact ⟨(algebraMap (X.residueField x) y.asIdeal.ResidueField).injective,
      y.asIdeal.algebraMap_residueField_surjective⟩

/-- Evaluation at the unique point identifies the residue field of `Spec κ(x)` with `κ(x)`
itself, so it leaves the transcendence degree over a base field `k` unchanged. The two
`k`-algebra structures involved are read off a ring map `φ` and a morphism `ψ` of spectra which
induces `φ` on global sections. -/
private theorem trdeg_spec_residueField (k : Type u) [Field k] {X : Scheme.{u}} (x : X)
    (φ : CommRingCat.of k ⟶ X.residueField x) (y : Spec (X.residueField x))
    (ψ : Spec (X.residueField x) ⟶ Spec (CommRingCat.of k))
    (hψ : φ ≫ (Scheme.ΓSpecIso (X.residueField x)).inv =
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ ψ.appTop) :
    letI := φ.hom.toAlgebra
    letI := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ ψ.appTop ≫
      (Spec (X.residueField x)).Γevaluation y).hom.toAlgebra
    Algebra.trdeg k ((Spec (X.residueField x)).residueField y) =
      Algebra.trdeg k (X.residueField x) := by
  let _ := φ.hom.toAlgebra
  let _ := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ ψ.appTop ≫
    (Spec (X.residueField x)).Γevaluation y).hom.toAlgebra
  refine (AlgEquiv.ofRingEquiv
    (f := RingEquiv.ofBijective _ (bijective_specResidueField_Γevaluation x y)) ?_).trdeg_eq.symm
  intro a
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (by rw [← Category.assoc, hψ, Category.assoc] :
      φ ≫ (Scheme.ΓSpecIso (X.residueField x)).inv ≫
          (Spec (X.residueField x)).Γevaluation y =
        (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ ψ.appTop ≫
          (Spec (X.residueField x)).Γevaluation y)) a

/-- For a morphism locally of finite type, the dimension of the fibre at a point is the Krull
dimension of the local ring of the fibre there plus the transcendence degree of the residue field
extension. -/
@[stacks 02FX, ega "IV 17.15.8" "more general", sga "1 II 5.8" "n = p + trdeg_k κ(x)"]
theorem topologicalKrullDimAt_fiber_eq_ringKrullDim_stalk_add_trdeg
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X) :
    letI := (f.residueFieldMap x).hom.toAlgebra
    topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) =
      ringKrullDim ((f.fiber (f x)).presheaf.stalk (f.asFiber x)) +
        (Cardinal.toENat (Algebra.trdeg (S.residueField (f x)) (X.residueField x)) :
          WithBot ℕ∞) := by
  have hft : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField, Scheme.Hom.fiber]; infer_instance
  have h0 := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk (S.residueField (f x))
    (f.fiber (f x)) (f.fiberToSpecResidueField (f x)) ((f.asFiberHom x) default)
  have h1 := trdeg_residueField_of_surjectiveOnStalks (S.residueField (f x))
    (f.fiberToSpecResidueField (f x)) (f.asFiberHom x) default
  have h2 := trdeg_spec_residueField (S.residueField (f x)) x
    (f.residueFieldMap x) default (f.asFiberHom x ≫ f.fiberToSpecResidueField (f x))
    (by rw [f.asFiberHom_fiberToSpecResidueField x, Scheme.ΓSpecIso_inv_naturality])
  rw [← f.asFiberHom_apply x default, h0, h1, h2, add_comm]

end AlgebraicGeometry

end
