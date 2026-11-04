module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.GradedAlgebra.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebraDerivations
public import StacksFrontier.RingTheory.GradedAlgebra.WeightedHomogeneousPresentation

/-!
# Finite-dimensional infinitesimal automorphisms of a graded algebra (Stacks 0DVZ)

Let `P` be a graded `k`-algebra which is of finite type over the field `k` and
finite-dimensional in each degree. This file shows that the infinitesimal automorphism
group of its deformation category, at an arbitrary dual-number lift, carries the structure
of a finite-dimensional `k`-vector space whose addition is composition of automorphisms.

The group is identified with the degree-preserving derivations of `P` by
`ProjectiveGradedAlgebra.infinitesimalAutomorphismGroupEquivDegreeZeroDerivations`, so the
content is that `degreeZeroDerivations grading` is a finite-dimensional `k`-vector space.
A degree-preserving derivation is determined by its values on algebra generators, and such an
algebra has a finite generating family of homogeneous elements by
`GradedAlgebra.exists_fin_homogeneous_adjoin_eq_top`. Evaluation at that finite family is
therefore an injective `k`-linear map from the degree-preserving derivations into a finite
product of the finite-dimensional graded pieces.

## Main results

* `gradedAlgebra_infinitesimalAutomorphisms_finiteDimensional`, in the namespace
  `Deformation.Examples.ProjectiveGradedAlgebra`: **Stacks 0DVZ**, the
  finite-dimensionality part.

## Implementation notes

`degreeZeroDerivations` is an `AddSubgroup` of the derivations; since the derivations are a
`k`-module and the degree-preserving condition is stable under scalars, it is upgraded here
to a `Submodule` and the two are identified by an additive equivalence, which transports the
`k`-module structure onto the `AddSubgroup`. The infinitesimal automorphism group is a
multiplicative group, so its vector-space structure is obtained through `Additive`, which is
why `a + b = a * b` holds by `rfl`.

## References

* [Stacks Project, Tag 0DVZ](https://stacks.math.columbia.edu/tag/0DVZ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Deformation.Examples

universe u w m

/-- The degree-preserving derivations of a graded algebra, as a `k`-submodule of all
`k`-derivations of `P`. -/
private def degreeZeroDerivationSubmodule {k : Type w} {P : Type (max w m)}
    [Field k] [CommRing P] [Algebra k P] (grading : ℕ → Submodule k P) :
    Submodule k (Derivation k P P) where
  carrier := (degreeZeroDerivations grading).carrier
  zero_mem' := (degreeZeroDerivations grading).zero_mem
  add_mem' := (degreeZeroDerivations grading).add_mem
  smul_mem' := by
    intro r D hD d x hx
    rw [Derivation.smul_apply]
    exact (grading d).smul_mem r (hD d x hx)

/-- The degree-preserving derivations as an `AddSubgroup` and as a `Submodule` have the same
elements. -/
private def degreeZeroDerivationsAddEquivSubmodule {k : Type w} {P : Type (max w m)}
    [Field k] [CommRing P] [Algebra k P] (grading : ℕ → Submodule k P) :
    degreeZeroDerivations grading ≃+ degreeZeroDerivationSubmodule grading where
  toFun D := ⟨D.1, D.2⟩
  invFun D := ⟨D.1, D.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- For a graded algebra of finite type over a field whose graded pieces are
finite-dimensional, the degree-preserving derivations form a finite-dimensional vector
space. -/
private theorem degreeZeroDerivations_finiteDimensional
    {k : Type w} {P : Type (max w m)} [Field k] [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)] [Algebra.FiniteType k P] :
    letI : Module k (degreeZeroDerivations grading) :=
      (degreeZeroDerivationsAddEquivSubmodule grading).module k
    FiniteDimensional k (degreeZeroDerivations grading) := by
  classical
  let : Module k (degreeZeroDerivations grading) :=
    (degreeZeroDerivationsAddEquivSubmodule grading).module k
  obtain ⟨n, v, d, v_mem, hgen⟩ :=
    GradedAlgebra.exists_fin_homogeneous_adjoin_eq_top grading
  let E : degreeZeroDerivationSubmodule grading →ₗ[k] ((i : Fin n) → grading (d i)) :=
    { toFun D i := ⟨D.1 (v i), D.2 (d i) (v i) (v_mem i)⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have Einj : Function.Injective E := fun D D' h =>
    Subtype.ext <| Derivation.ext_of_adjoin_eq_top (D1 := D.1) (D2 := D'.1) (Set.range v)
      hgen <| by
        rintro _ ⟨i, rfl⟩
        exact congrArg Subtype.val (congrFun h i)
  let e : degreeZeroDerivations grading ≃ₗ[k] degreeZeroDerivationSubmodule grading :=
    (degreeZeroDerivationsAddEquivSubmodule grading).linearEquiv k
  exact FiniteDimensional.of_injective (E.comp e.toLinearMap) (Einj.comp e.injective)

namespace ProjectiveGradedAlgebra

/-- **Stacks 0DVZ.** The infinitesimal automorphisms of the deformation category of a graded
algebra of finite type over a field, with finite-dimensional graded pieces, form a
finite-dimensional vector space whose addition is composition of automorphisms. -/
@[stacks 0DVZ "graded_inf_finite"]
public theorem gradedAlgebra_infinitesimalAutomorphisms_finiteDimensional
    {Λ : Type u} {k : Type w} [CommRing Λ] [IsNoetherianRing Λ]
    [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)] [Algebra.FiniteType k P] :
    let p := objectsOverFunctor
      (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)
    let hp := (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation
    ∀ {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
      {x₀ : p.Fiber (residueFieldObject.{u, w, w} Λ k)}
      {xε : p.Fiber Aε}
      (g : residueFieldObject.{u, w, w} Λ k ⟶ Aε)
      (e : Aε ⟶ residueFieldObject.{u, w, w} Λ k)
      (hpair : IsCanonicalDualNumberPair g e)
      (i : x₀.1 ⟶ xε.1) (hi : p.IsHomLift g i),
      let G := infinitesimalAutomorphismGroup hp g e hpair i hi
      ∃ hA : AddCommGroup G,
        letI := hA
        ∃ hM : Module k G,
          letI := hM
          (∀ a b : G, a + b = a * b) ∧ FiniteDimensional k G := by
  dsimp only
  intro Aε x₀ xε g e hpair i hi
  let G := infinitesimalAutomorphismGroup
    (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation
    g e hpair i hi
  let H := degreeZeroDerivations grading
  let : Module k H := (degreeZeroDerivationsAddEquivSubmodule (k := k) (P := P) grading).module k
  let F := infinitesimalAutomorphismGroupEquivDegreeZeroDerivations
    (Λ := Λ) P grading g e hpair i hi
  let E : Additive G ≃+ H := F.toAdditiveLeft
  let : CommGroup G :=
    { (inferInstance : Group G) with
      mul_comm a b := F.injective <| by rw [map_mul, map_mul, mul_comm] }
  let hA : AddCommGroup G := inferInstanceAs (AddCommGroup (Additive G))
  let : AddCommGroup G := hA
  let : Module k (Additive G) := E.module k
  let hM : Module k G := inferInstanceAs (Module k (Additive G))
  let : Module k G := hM
  have : FiniteDimensional k H :=
    degreeZeroDerivations_finiteDimensional (k := k) (P := P) grading
  exact ⟨hA, hM, fun _ _ => rfl,
    FiniteDimensional.of_injective (E.linearEquiv k).toLinearMap E.injective⟩

end ProjectiveGradedAlgebra

end Deformation.Examples

end
