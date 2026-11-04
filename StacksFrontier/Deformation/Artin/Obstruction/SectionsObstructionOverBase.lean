module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsBaseChangeTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen

/-!
# The obstruction element in the obstruction module over the base

For a deformation situation `A' → A` with kernel `I`, the boundary map of the sheaf-level sequence
on `W_{A'}` produces an obstruction element in `H¹(W_{A'}, 𝓕_{A'} ⊗_{A'} I)`. This module
identifies that group with the obstruction module `𝒪_x(I) = H¹(W_A, 𝓕_A ⊗_A I)`, with scalars
restricted along `A' → A`, and so places the obstruction element in `𝒪_x(I)`.

## Main definitions

* `Deformation.Artin.SectionsSheaf.cohomologyRestrictIso`: the `R`-linear cohomology
  `Hⁿ(X, -)` of `cohomologyDeltaFunctor` is the `Γ(X, 𝒪_X)`-linear one with scalars restricted
  along `R → Γ(X, 𝒪_X)`.
* `Deformation.Artin.SectionsSheaf.obstructionBaseChangeIso` and
  `Deformation.Artin.SectionsSheaf.obstructionBaseChangeIsoOf`: the obstruction module over `A'`
  at an `A`-module is the obstruction module over `A`,
  `Hⁿ(W_{A'}, 𝓕_{A'} ⊗_{A'} M) ≅ Hⁿ(W_A, 𝓕_A ⊗_A M)`, with scalars restricted along `A' → A`.
* `Deformation.Artin.SectionsSheaf.obstructionClassOverBase`: the obstruction element `o_x(A')` in
  `𝒪_x(I)`.

## Main results

* `Deformation.Artin.SectionsSheaf.baseHomCompat`: the base scalars `A' → Γ(W_{A'}, 𝒪)` and
  `A → Γ(W_A, 𝒪)` are compatible with the base-change immersion.
* `Deformation.Artin.SectionsSheaf.iso_hom_eq_zero_iff`: an isomorphism of modules carries an
  element to zero exactly when the element is zero.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open Stacks.Cohomology.AffineBase

universe u

namespace Deformation.Artin.SectionsSheaf

section OverBase

variable {S : Scheme.{u}} {A' A : CommRingCat.{u}} (φ : A' ⟶ A) (t : Spec A' ⟶ S)
  {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- The base scalars are compatible with the base-change immersion: the two composites
`A' → Γ(W_{A'}, 𝒪) → Γ(W_A, 𝒪)` and `A' → A → Γ(W_A, 𝒪)` agree. -/
theorem baseHomCompat :
    (((Scheme.ΓSpecIso A').inv ≫ (pullback.fst (Over.mk t).hom q).appTop) ≫
        (baseChangeMap q (quotHom φ t)).appTop) =
      φ ≫ ((Scheme.ΓSpecIso A).inv ≫ (pullback.fst (quotOver φ t).hom q).appTop) := by
  have hw : baseChangeMap q (quotHom φ t) ≫ (pullback.fst (Over.mk t).hom q) =
      (pullback.fst (quotOver φ t).hom q) ≫ Spec.map φ :=
    baseChangeMap_comp_fst q (quotHom φ t)
  rw [Category.assoc, ← Scheme.Hom.comp_appTop, hw, Scheme.Hom.comp_appTop, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc]

/-- Restricting scalars to `A'` through `Γ(W_{A'}, 𝒪)` and then along the immersion is
restricting them through `A`. -/
theorem restrictScalars_baseHom_compat
    (N : ModuleCat.{u} ↑Γ(pullback (quotOver φ t).hom q, ⊤)) :
    (ModuleCat.restrictScalars (baseHom (pullback.fst (Over.mk t).hom q))).obj
        ((ModuleCat.restrictScalars
          (baseChangeMap q (quotHom φ t)).appTop.hom).obj N) =
      (ModuleCat.restrictScalars φ.hom).obj
        ((ModuleCat.restrictScalars (baseHom (pullback.fst (quotOver φ t).hom q))).obj N) := by
  have hf : RingHom.comp ((baseChangeMap q (quotHom φ t)).appTop.hom)
        (baseHom (pullback.fst (Over.mk t).hom q)) =
      RingHom.comp (baseHom (pullback.fst (quotOver φ t).hom q)) φ.hom := by
    ext x
    exact congrArg (fun m ↦ CommRingCat.Hom.hom m x) (baseHomCompat φ t q)
  exact congrArg (fun f ↦ (ModuleCat.restrictScalars f).obj N) hf

end OverBase

section Cohomology

attribute [local instance] HasDerivedCategory.standard

/-- The `R`-linear cohomology is the `Γ(X, 𝒪_X)`-linear cohomology with scalars restricted along
`R → Γ(X, 𝒪_X)`. -/
def cohomologyRestrictIso {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R) (n : ℕ) :
    (moduleGlobalSections X).rightDerived n ⋙ ModuleCat.restrictScalars (baseHom π) ≅
      (cohomologyDeltaFunctor π).functor n :=
  have h1 : (ModuleCat.restrictScalars.{u} (baseHom π)).Additive := ⟨by intros; rfl⟩
  have h2 : PreservesFiniteLimits (ModuleCat.restrictScalars.{u} (baseHom π)) :=
    ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩
  have h3 : PreservesFiniteColimits (ModuleCat.restrictScalars.{u} (baseHom π)) :=
    ⟨fun _ _ _ ↦ ⟨fun {_} ↦ inferInstance⟩⟩
  have h4 : (ModuleCat.restrictScalars.{u} (baseHom π)).PreservesHomology :=
    Functor.preservesHomologyOfExact _
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (moduleGlobalSections X)
    (ModuleCat.restrictScalars.{u} (baseHom π))
    (moduleGlobalSections X ⋙ ModuleCat.restrictScalars.{u} (baseHom π)) (Iso.refl _) n

variable {S : Scheme.{u}} {A' A : CommRingCat.{u}} (φ : A' ⟶ A) (t : Spec A' ⟶ S)
  {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- The obstruction module over `A'` at an `A`-module is the obstruction module over `A`:
```
Hⁿ(W_{A'}, 𝓕_{A'} ⊗_{A'} M) ≅ Hⁿ(W_A, 𝓕_A ⊗_A M),
```
with scalars restricted along `A' → A`. -/
def obstructionBaseChangeIso
    (hi : IsClosedImmersion (baseChangeMap q (quotHom φ t))) (n : ℕ) (M : ModuleCat.{u} A) :
    ((cohomologyDeltaFunctor (pullback.fst (Over.mk t).hom q)).functor n).obj
        ((tensorSheafFunctor (pullback.fst (Over.mk t).hom q)
          ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)).obj
            ((ModuleCat.restrictScalars φ.hom).obj M)) ≅
      (ModuleCat.restrictScalars φ.hom).obj
        (((cohomologyDeltaFunctor (pullback.fst (quotOver φ t).hom q)).functor n).obj
          ((tensorSheafFunctor (pullback.fst (quotOver φ t).hom q)
            ((Scheme.Modules.pullback (pullback.snd (quotOver φ t).hom q)).obj 𝓕)).obj M)) :=
  letI := hi
  (cohomologyRestrictIso (pullback.fst (Over.mk t).hom q) n).symm.app _ ≪≫
    (ModuleCat.restrictScalars (baseHom (pullback.fst (Over.mk t).hom q))).mapIso
      (((moduleGlobalSections (pullback (Over.mk t).hom q)).rightDerived n).mapIso
          (Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso φ t q 𝓕 hi M) ≪≫
        baseChangeCohomologyObjIso q (quotHom φ t) hi
          ((tensorSheafFunctor (pullback.fst (quotOver φ t).hom q)
            ((Scheme.Modules.pullback (pullback.snd (quotOver φ t).hom q)).obj 𝓕)).obj M) n) ≪≫
    eqToIso (restrictScalars_baseHom_compat φ t q _) ≪≫
    (ModuleCat.restrictScalars φ.hom).mapIso
      ((cohomologyRestrictIso (pullback.fst (quotOver φ t).hom q) n).app _)

/-- The isomorphism `obstructionBaseChangeIso` at an `A'`-module `M'` equal to the restriction of
scalars of `M` along `A' → A`. -/
def obstructionBaseChangeIsoOf
    (hi : IsClosedImmersion (baseChangeMap q (quotHom φ t))) (n : ℕ) (M : ModuleCat.{u} A)
    (M' : ModuleCat.{u} A') (hM : M' = (ModuleCat.restrictScalars φ.hom).obj M) :
    ((cohomologyDeltaFunctor (pullback.fst (Over.mk t).hom q)).functor n).obj
        ((tensorSheafFunctor (pullback.fst (Over.mk t).hom q)
          ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)).obj M') ≅
      (ModuleCat.restrictScalars φ.hom).obj
        (((cohomologyDeltaFunctor (pullback.fst (quotOver φ t).hom q)).functor n).obj
          ((tensorSheafFunctor (pullback.fst (quotOver φ t).hom q)
            ((Scheme.Modules.pullback (pullback.snd (quotOver φ t).hom q)).obj 𝓕)).obj M)) :=
  eqToIso (congrArg (fun N ↦
      ((cohomologyDeltaFunctor (pullback.fst (Over.mk t).hom q)).functor n).obj
        ((tensorSheafFunctor (pullback.fst (Over.mk t).hom q)
          ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)).obj N)) hM) ≪≫
    obstructionBaseChangeIso φ t q 𝓕 hi n M

variable {M : ModuleCat.{u} A} {Y₂ Y₃ : ModuleCat.{u} A'}

/-- An isomorphism of modules carries an element to zero exactly when the element is zero. -/
theorem iso_hom_eq_zero_iff {R : Type u} [Ring R] {P N : ModuleCat.{u} R} (e : P ≅ N)
    (y : (P : Type u)) : e.hom y = 0 ↔ y = 0 :=
  ⟨fun h ↦ by simpa using congrArg e.inv h, fun h ↦ by simp [h]⟩

/-- The obstruction element `o_x(A')` in the obstruction module over `A`. For a short exact
sequence of `A'`-modules whose first term is an `A`-module — the sequence `0 → I → A' → A → 0` of a
deformation situation — this is the obstruction element of a section, computed on `W_{A'}`, carried
by `obstructionBaseChangeIso` into `𝒪_x(M) = H¹(W_A, 𝓕_A ⊗_A M)`. -/
def obstructionClassOverBase
    (hF : AlgebraicGeometry.IsFlatOver (pullback.fst (Over.mk t).hom q).toLRSHom.toShHom
      ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕))
    (hi : IsClosedImmersion (baseChangeMap q (quotHom φ t)))
    {f : (ModuleCat.restrictScalars φ.hom).obj M ⟶ Y₂} {g : Y₂ ⟶ Y₃} {zero : f ≫ g = 0}
    (hSq : (ShortComplex.mk f g zero).ShortExact)
    (x : (((cohomologyDeltaFunctor (pullback.fst (Over.mk t).hom q)).functor 0).obj
      ((tensorSheafFunctor (pullback.fst (Over.mk t).hom q)
        ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)).obj Y₃) :
      Type u)) :=
  letI := hi
  (obstructionBaseChangeIsoOf φ t q 𝓕 hi 1 M (ShortComplex.mk f g zero).X₁ rfl).hom
    (obstructionClass (pullback.fst (Over.mk t).hom q)
      ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕) hF hSq x)

end Cohomology

end Deformation.Artin.SectionsSheaf

end
