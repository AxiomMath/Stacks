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
group of its deformation category, at an arbitrary dual-number lift, is finite-dimensional for
its natural `k`-vector-space structure: addition is composition of automorphisms and a scalar
`c` acts by pushforward along the rescaling `ε ↦ cε` of the dual numbers.

The group is identified with the degree-preserving derivations of `P`, compatibly with these
rescalings, by
`ProjectiveGradedAlgebra.exists_infinitesimalAutomorphismGroupMulEquiv_pushforward_eq_smul`,
so the content is that `degreeZeroDerivations grading` is a finite-dimensional `k`-vector space.
A degree-preserving derivation is determined by its values on algebra generators, and such an
algebra has a finite generating family of homogeneous elements by
`GradedAlgebra.exists_fin_homogeneous_adjoin_eq_top`. Evaluation at that finite family is
therefore an injective `k`-linear map from the degree-preserving derivations into a finite
product of the finite-dimensional graded pieces.

## Main results

* `exists_module_finiteDimensional_infinitesimalAutomorphismGroup`, in the namespace
  `Deformation.Examples.ProjectiveGradedAlgebra`: **Stacks 0DVZ**, the finite-dimensionality of
  `Inf(Def_P)` for its natural vector-space structure, in which `c` acts by pushforward along
  `ε ↦ cε`; the structure is carried from the degree-preserving derivations along the
  identification `id + εD ↦ D`, which
  `ProjectiveGradedAlgebra.exists_infinitesimalAutomorphismGroupMulEquiv_pushforward_eq_smul`
  shows to be compatible with these rescalings.
* `gradedAlgebra_infinitesimalAutomorphisms_finiteDimensional`: the weaker statement that some
  finite-dimensional structure with addition composition exists.

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

/-- The infinitesimal automorphisms of the deformation category of a graded algebra of finite
type over a field, with finite-dimensional graded pieces, carry some finite-dimensional
`k`-vector-space structure whose addition is composition of automorphisms. The scalar action is
not tied to the natural one here; the finite-dimensionality part of Stacks 0DVZ, for the natural
structure in which `c` acts by pushforward along `ε ↦ cε`, is
`exists_module_finiteDimensional_infinitesimalAutomorphismGroup`. -/
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

/-- **Stacks 0DVZ, the infinitesimal automorphisms.** Let `P` be a graded algebra of finite type
over the field `k`, finite-dimensional in each degree. Then `Inf(Def_P)` is a finite-dimensional
`k`-vector space: at every lift `i : x₀ ⟶ xε` of the special fibre along a canonical dual-number
pair `k → Aε → k`, the infinitesimal automorphism group carries a `k`-vector-space structure

* whose addition is composition of infinitesimal automorphisms, and
* in which a scalar `c` acts by pushforward along `ε ↦ cε`: for every endomorphism `s` of `Aε`
  which is `ε ↦ cε` in a dual-number coordinate of `Aε` compatible with its residue field, and
  every arrow `j : xε ⟶ xε` over `s` fixing `i`, `c • a` is the pushforward of `a` along `j`,

which is the natural structure of Stacks 06JV / 06JX, and this vector space is finite
dimensional. -/
@[stacks 0DVZ "graded_inf_finite: for P of finite type over k, Inf(Def_P) with its natural \
vector space structure (addition is composition; c acts by pushforward along eps -> c eps) is \
finite dimensional over k, at every lift x0 -> x_eps along a canonical dual-number pair"]
public theorem exists_module_finiteDimensional_infinitesimalAutomorphismGroup
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (P : Type (max w m)) [CommRing P] [Algebra k P]
    (grading : ℕ → Submodule k P) [GradedAlgebra grading]
    [∀ d, Module.Finite k (grading d)] [Algebra.FiniteType k P]
    {Aε : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x₀ : (objectsOverFunctor
      (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)).Fiber (residueFieldObject.{u, w, w} Λ k)}
    {xε : (objectsOverFunctor
      (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)).Fiber Aε}
    (g : residueFieldObject.{u, w, w} Λ k ⟶ Aε)
    (e : Aε ⟶ residueFieldObject.{u, w, w} Λ k)
    (hpair : IsCanonicalDualNumberPair g e)
    (i : x₀.1 ⟶ xε.1)
    (hi : (objectsOverFunctor
      (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
      (specialFiber (Λ := Λ) P grading)).IsHomLift g i) :
    ∃ hA : AddCommGroup (infinitesimalAutomorphismGroup
        (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation
        g e hpair i hi),
      letI := hA
      ∃ hM : Module k (infinitesimalAutomorphismGroup
          (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation
          g e hpair i hi),
        letI := hM
        (∀ a b : infinitesimalAutomorphismGroup
          (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation
          g e hpair i hi, a + b = a * b) ∧
        (∀ (c : k) (s : Aε ⟶ Aε),
          (∃ φ : Aε ≃ₐ[Λ] DualNumber k,
            (∀ t : Aε, (φ t).1 = Aε.residueEquiv (IsLocalRing.residue Aε t)) ∧
            (∀ t : k, φ (s.hom (φ.symm (TrivSqZeroExt.inl t))) = TrivSqZeroExt.inl t) ∧
            φ (s.hom (φ.symm DualNumber.eps)) = c • DualNumber.eps) →
          ∀ (j : xε.1 ⟶ xε.1) (hj : (objectsOverFunctor
              (ProjectiveGradedAlgebra.projection.{u, w, w, max w m} (Λ := Λ) (k := k))
              (specialFiber (Λ := Λ) P grading)).IsHomLift s j),
            i ≫ j = i →
            ∀ a : infinitesimalAutomorphismGroup
                (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation
                g e hpair i hi,
              ∃ b : infinitesimalAutomorphismGroup
                  (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation
                  g e hpair i hi,
                b.val = pushforwardAutomorphismHom
                  (isDeformationCategory_deformationCategory (Λ := Λ) P
                    grading).predeformation.cofibered s j hj a.val ∧ c • a = b) ∧
        FiniteDimensional k (infinitesimalAutomorphismGroup
          (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation
          g e hpair i hi) := by
  obtain ⟨Φ, hΦ⟩ := exists_infinitesimalAutomorphismGroupMulEquiv_pushforward_eq_smul
    (Λ := Λ) P grading g e hpair i hi
  let H := degreeZeroDerivations grading
  let : Module k H := (degreeZeroDerivationsAddEquivSubmodule (k := k) (P := P) grading).module k
  have : FiniteDimensional k H :=
    degreeZeroDerivations_finiteDimensional (k := k) (P := P) grading
  let eD : infinitesimalAutomorphismGroup
      (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation
      g e hpair i hi ≃ H :=
    Φ.toEquiv.trans Multiplicative.toAdd
  let hA : AddCommGroup (infinitesimalAutomorphismGroup
      (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation
      g e hpair i hi) := eD.addCommGroup
  let hM : Module k (infinitesimalAutomorphismGroup
      (isDeformationCategory_deformationCategory (Λ := Λ) P grading).predeformation
      g e hpair i hi) := eD.addEquiv.module k
  refine ⟨hA, hM, fun a b => ?_, fun c s hs j hj hij a => ?_, ?_⟩
  · have h : eD (a * b) = eD a + eD b := by
      change Multiplicative.toAdd (Φ (a * b)) =
        Multiplicative.toAdd (Φ a) + Multiplicative.toAdd (Φ b)
      rw [map_mul]
      rfl
    rw [Equiv.add_def, ← h, Equiv.symm_apply_apply]
  · obtain ⟨b, hb, hΦb⟩ := hΦ c s hs j hj hij a
    refine ⟨b, hb, ?_⟩
    change eD.symm (c • eD a) = b
    rw [Equiv.symm_apply_eq]
    exact Subtype.ext hΦb.symm
  · exact Module.Finite.equiv (eD.addEquiv.linearEquiv k).symm

end ProjectiveGradedAlgebra

end Deformation.Examples

end
