module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.Exactness
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.UniformBoundAnyModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.Pushforward
public import StacksFrontier.AlgebraicGeometry.FunctorsAndMorphisms.IntegralTransformQcoh.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineHom
public import StacksFrontier.AlgebraicGeometry.ModuleSpecGammaAdditive
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EilenbergWattsGeometricFactor

/-!
# The base field acts on derived direct image and on the duality isomorphism

Let `k` be a field and let `f : X ⟶ Spec(k)` be a morphism of schemes. The category of
`𝒪_X`-modules is `k`-linear by `AlgebraicGeometry.modulesLinear`, the scalar `a` acting by
multiplication by its image under `k ≅ Γ(Spec(k), 𝒪) ⟶ Γ(X, 𝒪_X)`, and `Mathlib` propagates that
linearity to the cochain complexes, to the homotopy category and to the unbounded derived
category. This file carries it the remaining distance, to the objects that Serre duality on a
curve is stated with:

* derived direct image `Rf_* : D(𝒪_X) ⥤ D(𝒪_{Spec(k)})` and its restriction to the complexes
  with quasi-coherent cohomology;
* the duality isomorphism `Hom_X(K, f^×ω) ≃ Hom_{Spec(k)}(Rf_*K, ω)` of [Stacks, Tag 0AWP];
* morphisms of quasi-coherent modules on `Spec(k)`, which are the `k`-linear maps on global
  sections.

A `k`-linear identification is what Serre duality needs: an additive bijection of Hom-groups
says nothing about dimensions over an infinite field, so every step of the chain computing
`dim_k H^0(X, ω_X)` has to be linear.

## Main results

* `AlgebraicGeometry.CurveDuality.linear_pushforward` — direct image along `f` is `k`-linear.
* `AlgebraicGeometry.CurveDuality.linear_derivedPushforward` — `Rf_*` is `k`-linear.
* `AlgebraicGeometry.CurveDuality.additive_quasiCoherentDerivedPushforward` and
  `AlgebraicGeometry.CurveDuality.linear_quasiCoherentDerivedPushforward` — the restriction of
  `Rf_*` to `D_QCoh` is additive and `k`-linear.
* `AlgebraicGeometry.CurveDuality.dualityLinearEquiv` — the duality isomorphism of
  [Stacks, Tag 0AWP] is `k`-linear.
* `AlgebraicGeometry.CurveDuality.moduleSpecΓHomLinearEquiv` — morphisms of quasi-coherent
  modules on `Spec(k)` are the `k`-linear maps on global sections.

## Implementation notes

The `k`-linear structures cannot be global instances: they depend on the structure morphism `f`,
which instance search cannot recover from `X`. They are therefore installed with `letI` both in
the statements and in the proofs, as `AlgebraicGeometry.globalSectionsOver_linear` and
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.linear_moduleSpecΓFunctor` already do. On the base
the structure is taken at `Stacks.AlgebraicGeometry.TopDegreeBaseChange.specBase`, which is
`Spec(k)` with its identity structure morphism, so that the existing linearity of
`AlgebraicGeometry.moduleSpecΓFunctor` applies verbatim.

Linearity of `Rf_*` is not an instance of linearity of a right derived functor of a linear
functor: `Rf_*` is a *total* right derived functor along the quasi-isomorphisms of the homotopy
category, not `Functor.rightDerived`. It is
`Stacks.SemilinearFunctor.map_smul_id_rightDerived`, the transfer of a central scalar across the
universal property of a right derived functor, applied to the comparison
`Stacks.Duality.derivedPushforwardUnit`; the underived input is
`AlgebraicGeometry.over_pushforward_linear`.

Additivity of the restricted functor is not found by instance search even though
`CategoryTheory.Functor.IsTriangulated` supplies additivity of the ambient `Rf_*`, so it is
proved here: morphisms of `D_QCoh` are a one-field structure over those of `D`
(`CategoryTheory.InducedCategory.Hom`) whose addition is the ambient one.

## References

* [Stacks Project, Tag 0AWP](https://stacks.math.columbia.edu/tag/0AWP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.CurveDuality

open Stacks.AlgebraicGeometry.TopDegreeBaseChange (specBase)

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Direct image along a morphism to `Spec(k)` is `k`-linear.** The scalar is pulled back from
the base on both sides, so this is `AlgebraicGeometry.over_pushforward_linear` for the morphism
of `k`-schemes `f`. -/
theorem linear_pushforward :
    letI : Linear k X.Modules := modulesLinear k (Over.mk f)
    letI : Linear k (Spec (CommRingCat.of k)).Modules := modulesLinear k (specBase k)
    (Scheme.Modules.pushforward f).Linear k := by
  let : Linear k X.Modules := modulesLinear k (Over.mk f)
  let : Linear k (Spec (CommRingCat.of k)).Modules := modulesLinear k (specBase k)
  exact over_pushforward_linear k (X := Over.mk f) (Y := specBase k) (Over.homMk f (by simp))

/-- **Derived direct image along a morphism to `Spec(k)` is `k`-linear.** Multiplication by a
base scalar is a central endomorphism, and the universal property of a right derived functor
carries the identity `f_*(a · id) = a · id` of `AlgebraicGeometry.over_pushforward_linear` to
`Rf_*`. -/
theorem linear_derivedPushforward [HasDerivedCategory.{w} X.Modules]
    [HasDerivedCategory.{w} (Spec (CommRingCat.of k)).Modules] :
    letI : Linear k X.Modules := modulesLinear k (Over.mk f)
    letI : Linear k (Spec (CommRingCat.of k)).Modules := modulesLinear k (specBase k)
    Functor.Linear k (Stacks.Duality.derivedPushforward.{w} f) := by
  let : Linear k X.Modules := modulesLinear k (Over.mk f)
  let : Linear k (Spec (CommRingCat.of k)).Modules := modulesLinear k (specBase k)
  have hu : (Scheme.Modules.pushforward f).Linear k := linear_pushforward k f
  rw [Functor.linear_iff]
  intro K r
  exact Stacks.SemilinearFunctor.map_smul_id_rightDerived
    (G := Stacks.Duality.homotopyPushforward.{w} f) (L := DerivedCategory.Qh)
    (Stacks.Duality.derivedPushforward.{w} f) (Stacks.Duality.derivedPushforwardUnit.{w} f)
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)) r r
    (fun M => Stacks.SemilinearFunctor.map_smul_id_comp
      ((Scheme.Modules.pushforward f).mapHomotopyCategory (ComplexShape.up ℤ))
      DerivedCategory.Qh r r
      (fun N => Stacks.SemilinearFunctor.map_smul_id_mapHomotopyCategory
        (Scheme.Modules.pushforward f) r r
        (fun M' => by rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id])
        (ComplexShape.up ℤ) N) M) K

variable [HasDerivedCategory.{w} X.Modules]
  [HasDerivedCategory.{w} (Spec (CommRingCat.of k)).Modules]
  (hpush : ∀ (K : Stacks.Duality.quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor (Spec (CommRingCat.of k)).Modules i).obj
      ((Stacks.Duality.derivedPushforward f).obj K.obj)).IsQuasicoherent)

include f hpush in
/-- **The restriction of `Rf_*` to complexes with quasi-coherent cohomology is additive.** The
ambient `Rf_*` is additive because it is triangulated, and addition of morphisms of `D_QCoh` is
addition of the underlying morphisms of `D`. -/
theorem additive_quasiCoherentDerivedPushforward :
    (Stacks.Duality.quasiCoherentDerivedPushforward.{w} f hpush).Additive := by
  have : (Stacks.Duality.derivedPushforward.{w} f).Additive := inferInstance
  exact ⟨fun {A B} g h => ObjectProperty.hom_ext _ <|
    (Stacks.Duality.derivedPushforward f).map_add (f := g.hom) (g := h.hom)⟩

include f hpush in
/-- **The restriction of `Rf_*` to complexes with quasi-coherent cohomology is `k`-linear.** The
scalar action on `D_QCoh` is the ambient one, where `Rf_*` is `k`-linear by
`AlgebraicGeometry.CurveDuality.linear_derivedPushforward`. -/
theorem linear_quasiCoherentDerivedPushforward :
    letI : Linear k X.Modules := modulesLinear k (Over.mk f)
    letI : Linear k (Spec (CommRingCat.of k)).Modules := modulesLinear k (specBase k)
    Functor.Linear k (Stacks.Duality.quasiCoherentDerivedPushforward.{w} f hpush) := by
  let : Linear k X.Modules := modulesLinear k (Over.mk f)
  let : Linear k (Spec (CommRingCat.of k)).Modules := modulesLinear k (specBase k)
  have hRf : Functor.Linear k (Stacks.Duality.derivedPushforward.{w} f) :=
    linear_derivedPushforward k f
  rw [Functor.linear_iff]
  intro K r
  refine ObjectProperty.hom_ext _ ?_
  change (Stacks.Duality.derivedPushforward f).map (r • 𝟙 K.obj) = r • 𝟙 _
  rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
  rfl

include f hpush in
/-- **The duality isomorphism of [Stacks, Tag 0AWP] is `k`-linear.** It sends a map into the
relative dualizing complex to its derived direct image followed by the trace, and both
operations are `k`-linear. -/
def dualityLinearEquiv [(Stacks.Duality.quasiCoherentDerivedPushforward.{w} f hpush).IsLeftAdjoint]
    (ωY : Stacks.Duality.quasiCoherentDerivedCategory (Spec (CommRingCat.of k)))
    (K : Stacks.Duality.quasiCoherentDerivedCategory X) :
    letI : Linear k X.Modules := modulesLinear k (Over.mk f)
    letI : Linear k (Spec (CommRingCat.of k)).Modules := modulesLinear k (specBase k)
    (K ⟶ Stacks.Duality.relativeDualizingComplex f hpush ωY) ≃ₗ[k]
      ((Stacks.Duality.quasiCoherentDerivedPushforward f hpush).obj K ⟶ ωY) := by
  letI : Linear k X.Modules := modulesLinear k (Over.mk f)
  letI : Linear k (Spec (CommRingCat.of k)).Modules := modulesLinear k (specBase k)
  haveI := additive_quasiCoherentDerivedPushforward k f hpush
  haveI := linear_quasiCoherentDerivedPushforward k f hpush
  exact
    { toFun := Stacks.Duality.relativeDualizingComplexHomEquiv f hpush ωY K
      invFun := (Stacks.Duality.relativeDualizingComplexHomEquiv f hpush ωY K).symm
      left_inv := (Stacks.Duality.relativeDualizingComplexHomEquiv f hpush ωY K).left_inv
      right_inv := (Stacks.Duality.relativeDualizingComplexHomEquiv f hpush ωY K).right_inv
      map_add' := fun u v => by
        simp only [Stacks.Duality.relativeDualizingComplexHomEquiv_apply, Functor.map_add,
          Preadditive.add_comp]
      map_smul' := fun r u => by
        simp only [RingHom.id_apply, Stacks.Duality.relativeDualizingComplexHomEquiv_apply,
          Functor.Linear.map_smul, Linear.smul_comp] }

/-- **Morphisms of quasi-coherent modules on `Spec(k)` are the `k`-linear maps on global
sections.** Faithfulness is
`Stacks.AlgebraicGeometry.ModuleLimits.moduleSpec_hom_ext` and fullness is
`Stacks.AlgebraicGeometry.ModuleLimits.moduleSpec_exists_hom`; `k`-linearity of the comparison is
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.linear_moduleSpecΓFunctor`. -/
def moduleSpecΓHomLinearEquiv (A B : (Spec (CommRingCat.of k)).Modules)
    [hA : A.IsQuasicoherent] [hB : B.IsQuasicoherent] :
    letI : Linear k (Spec (CommRingCat.of k)).Modules := modulesLinear k (specBase k)
    (A ⟶ B) ≃ₗ[k] (moduleSpecΓFunctor.obj A ⟶ moduleSpecΓFunctor.obj B) := by
  letI : Linear k (Spec (CommRingCat.of k)).Modules := modulesLinear k (specBase k)
  haveI := Stacks.AlgebraicGeometry.TopDegreeBaseChange.linear_moduleSpecΓFunctor k
  haveI := AlgebraicGeometry.moduleSpecΓFunctor_additive (CommRingCat.of k)
  refine LinearEquiv.ofBijective
    ((moduleSpecΓFunctor (R := CommRingCat.of k)).mapLinearMap k) ⟨?_, ?_⟩
  · intro ψ ψ' hψ
    refine Stacks.AlgebraicGeometry.ModuleLimits.moduleSpec_hom_ext (fun a => ?_)
    exact congrArg (fun (t : moduleSpecΓFunctor.obj A ⟶ moduleSpecΓFunctor.obj B) => t.hom a) hψ
  · intro v
    obtain ⟨ψ, hψ⟩ := Stacks.AlgebraicGeometry.ModuleLimits.moduleSpec_exists_hom
      (A := A) (B := B) v.hom
    exact ⟨ψ, ModuleCat.hom_ext (LinearMap.ext hψ)⟩

end AlgebraicGeometry.CurveDuality

end
