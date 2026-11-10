module

public import StacksFrontier.AlgebraicGeometry.Perfect.ExtProjectionAssembly
public import StacksFrontier.AlgebraicGeometry.Perfect.ExtProjectionModelBridge
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.FlatPullbackTensorDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.CanonicalDeltaFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 0A1F]: a projection formula for cohomology, with boundary maps

Let `S` be a Noetherian scheme, `f : X ⟶ S` locally of finite type, `E` a perfect object of
`D(𝒪_X)`, `𝒢` a bounded complex of coherent `𝒪_X`-modules flat over `S` with support proper over
`S`, and `K = Rf_*(E ⊗^𝐋 𝒢)`.  [Stacks, Tag 0A1F] asserts functorial isomorphisms
`H^i(S, K ⊗^𝐋 ℱ) ≅ H^i(X, E ⊗^𝐋 (𝒢 ⊗ f^*ℱ))` for quasi-coherent `ℱ`, compatible with boundary maps.

This file supplies the last inputs of
`Stacks.Cohomology.ExtProjectionAssembly.exists_isos_of_model` and states the tag.

## Main definitions

* `modelR`: the descent `R : D(𝒪_S) ⥤ D(𝒪_X)` of `M ↦ Tot(f^*M ⊗ 𝒢)` with its shift structure;
  `modelμ : R ≅ 𝒢 ⊗^𝐋 Lf^*(-)`; `modelν : R(ℱ[0]) ≅ 𝒢 ⊗ f^*ℱ`, natural in `ℱ`.

## Main results

* `shortExact_Ψ`: `0 → 𝒢 ⊗ f^*ℱ₁ → 𝒢 ⊗ f^*ℱ₂ → 𝒢 ⊗ f^*ℱ₃ → 0` is short exact.
* `modelTri`: `R` carries the triangle of a short exact sequence of modules to the triangle of
  that sequence of complexes, with `modelν` as components.
* `Stacks.Cohomology.ExtProjectionFormulaBoundary.extCohomologyIso_qcoh_boundary`:
  **[Stacks, Tag 0A1F]**, unconditionally.

## Implementation notes

The base declaration `Stacks.Cohomology.ExtProjectionFormula.extCohomologyIso` registers the tag
conditionally (it carries the projection formula and the flat identification as structure fields
and omits the boundary maps); the theorem here supersedes it and carries no such input.  The
objects are written at the spelling of the derived tensor product (`DT`, `ModS`), which is the
category of `𝒪`-modules up to definitional equality; at that spelling instance search finds the
shift structures of the functors whose connecting morphisms the statement uses.

## References

* [Stacks Project, Tag 0A1F](https://stacks.math.columbia.edu/tag/0A1F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Pretriangulated StrictlyPerfect
open Stacks.Cohomology.ExtProjectionDegreeIso
open Stacks.Cohomology.ExtProjectionAssembly (ModS qcModules Ψ)

universe u

namespace Stacks.Cohomology.ExtProjectionFormulaBoundary

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local implicit_reducible] structureSheafRing
  StrictlyPerfect.structureSheafOfRings CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

variable {X S : Scheme.{u}} (f : X ⟶ S) (E : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
  (G : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ)

/-- The functor `ℱ ↦ 𝒢 ⊗ f^*ℱ` from `𝒪_S`-modules to complexes of `𝒪_X`-modules is additive. -/
instance Ψ_additive : (Ψ f G).Additive :=
  Stacks.Cohomology.ExtProjectionFlatExact.pullbackTensorModuleComplex_additive f G

variable [LocallyOfFiniteType f] (hG : PerfectPushforward.FlatProperSupportComplex f G)

/-- `R : M ↦ Tot(f^*M ⊗ 𝒢)` descended to `D(𝒪_S) ⥤ D(𝒪_X)`
(`Stacks.Cohomology.FlatPullbackTensor.derivedFunctor`), at the spelling of the derived tensor
product. -/
def modelR : DT S ⥤ DT X :=
  Stacks.Cohomology.FlatPullbackTensor.derivedFunctor f.toLRSHom.toShHom G hG.isFlatOver hG.bounded

/-- The commutation of `modelR` with shifts, that of the descended functor. -/
instance modelR_commShift : (modelR f G hG).CommShift ℤ :=
  inferInstanceAs ((Stacks.Cohomology.FlatPullbackTensor.derivedFunctor f.toLRSHom.toShHom G
    hG.isFlatOver hG.bounded).CommShift ℤ)

/-- `R ≅ 𝒢 ⊗^𝐋 Lf^*(-)` on all of `D(𝒪_S)`. -/
def modelμ : modelR f G hG ≅ pullbackTensorG f G :=
  (Stacks.Cohomology.FlatPullbackTensor.derivedPullbackTensorLeftIso f.toLRSHom.toShHom G
    hG.isFlatOver hG.bounded).symm

/-- The factorization `Q ⋙ R ≅ Tot(f^*(-) ⊗ 𝒢) ⋙ Q`. -/
abbrev modelFactors :=
  Stacks.Cohomology.FlatPullbackTensor.derivedFunctorFactors f.toLRSHom.toShHom G hG.isFlatOver
    hG.bounded

/-- **`R(ℱ[0]) ≅ 𝒢 ⊗ f^*ℱ`**, naturally in the `𝒪_S`-module `ℱ`: `Q ⋙ R ≅ Tot(f^*(-) ⊗ 𝒢) ⋙ Q`
at `ℱ[0]`, followed by `Tot(f^*ℱ[0] ⊗ 𝒢) ≅ 𝒢 ⊗ f^*ℱ`. -/
def modelν : DerivedCategory.singleFunctor (ModS S) 0 ⋙ modelR f G hG ≅ Ψ f G ⋙ DerivedCategory.Q :=
  NatIso.ofComponents
    (fun F => ((modelFactors f G hG).app
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)).symm ≪≫
      DerivedCategory.Q.mapIso
        (Stacks.Cohomology.ExtProjectionModelBridge.singleIso f.toLRSHom.toShHom G F))
    (fun {F F'} φ => by
      have h₁ := (modelFactors f G hG).inv.naturality
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ)
      have h₂ := (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map
        (Stacks.Cohomology.ExtProjectionModelBridge.singleIso_hom_naturality f.toLRSHom.toShHom G
          φ)).trans (DerivedCategory.Q.map_comp _ _))
      exact ((reassoc_of% h₁) _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm))

include hG in
/-- **Short exactness of `𝒢 ⊗ f^*(-)`** on a short exact sequence of `𝒪_S`-modules. -/
theorem shortExact_Ψ (T : ShortComplex (ModS S)) (hT : T.ShortExact) :
    (T.map (Ψ f G)).ShortExact :=
  Stacks.Cohomology.ExtProjectionFlatExact.shortExact_map_pullbackTensor f G hG.isFlatOver T hT

/-- The short exact sequence `Tot(f^*ℱ_•[0] ⊗ 𝒢)` is isomorphic to `𝒢 ⊗ f^*ℱ_•`. -/
def sesIso (T : ShortComplex (ModS S)) :
    (T.map (HomologicalComplex.single _ (ComplexShape.up ℤ) 0)).map
        (Stacks.Cohomology.FlatPullbackTensor.complexFunctor f.toLRSHom.toShHom G) ≅
      T.map (Ψ f G) :=
  ShortComplex.isoMk
    (Stacks.Cohomology.ExtProjectionModelBridge.singleIso f.toLRSHom.toShHom G T.X₁)
    (Stacks.Cohomology.ExtProjectionModelBridge.singleIso f.toLRSHom.toShHom G T.X₂)
    (Stacks.Cohomology.ExtProjectionModelBridge.singleIso f.toLRSHom.toShHom G T.X₃)
    (Stacks.Cohomology.ExtProjectionModelBridge.singleIso_hom_naturality f.toLRSHom.toShHom G
      T.f).symm
    (Stacks.Cohomology.ExtProjectionModelBridge.singleIso_hom_naturality f.toLRSHom.toShHom G
      T.g).symm

/-- **The image under `R` of the distinguished triangle of a short exact sequence of modules maps
to the distinguished triangle of `0 → 𝒢 ⊗ f^*ℱ₁ → 𝒢 ⊗ f^*ℱ₂ → 𝒢 ⊗ f^*ℱ₃ → 0`**, with the
components of `modelν` as first and third components. -/
theorem modelTri (T : ShortComplex (ModS S)) (hT : T.ShortExact) :
    ∃ φ : (modelR f G hG).mapTriangle.obj hT.singleTriangle ⟶
        DerivedCategory.triangleOfSES (shortExact_Ψ f G hG T hT),
      φ.hom₁ = (modelν f G hG).hom.app T.X₁ ∧ φ.hom₃ = (modelν f G hG).hom.app T.X₃ := by
  have hS' := hT.map_of_exact (HomologicalComplex.single (ModS S) (ComplexShape.up ℤ) 0)
  have hΨS' := ShortComplex.shortExact_of_iso (sesIso f G T).symm (shortExact_Ψ f G hG T hT)
  refine ⟨(modelR f G hG).mapTriangle.map hT.singleTriangleIso.hom ≫
    Stacks.Cohomology.FlatPullbackTensor.mapTriangleOfSESHom f.toLRSHom.toShHom G hG.isFlatOver
      hG.bounded hS' hΨS' ≫
    triangleMorphismOfSESHom hΨS' (shortExact_Ψ f G hG T hT) (sesIso f G T).hom,
    ?_, ?_⟩ <;>
  · refine (congrArg (· ≫ _) ((modelR f G hG).map_id _)).trans ((Category.id_comp _).trans ?_)
    rfl

omit [LocallyOfFiniteType f] in
/-- **[Stacks, Tag 0A1F].**  Let `S` be a Noetherian scheme, `f : X ⟶ S` a morphism locally of
finite type, `E ∈ D(𝒪_X)` perfect and `𝒢` a bounded complex of coherent `𝒪_X`-modules, flat over
`S`, whose support is contained in a closed subset proper over `S` (the assumptions of
[Stacks, Tag 0DJQ]), and let `K = Rf_*(E ⊗^𝐋_{𝒪_X} 𝒢)`.  Then there are isomorphisms

`H^i(S, K ⊗^𝐋_{𝒪_S} ℱ) ≅ H^i(X, E ⊗^𝐋_{𝒪_X} (𝒢 ⊗_{𝒪_X} f^*ℱ))`,

functorial in the quasi-coherent `𝒪_S`-module `ℱ` (a natural isomorphism of functors on the full
subcategory of quasi-coherent modules, for every `i`), and compatible with boundary maps: for a
short exact sequence `0 → ℱ₁ → ℱ₂ → ℱ₃ → 0` of quasi-coherent `𝒪_S`-modules the square formed
with the connecting morphisms commutes, where on the left the connecting morphism is that of
`H^*(S, -)` at the distinguished triangle `K ⊗^𝐋 ℱ₁ → K ⊗^𝐋 ℱ₂ → K ⊗^𝐋 ℱ₃ → (K ⊗^𝐋 ℱ₁)[1]`,
and on the right that of `H^*(X, E ⊗^𝐋 -)` at the distinguished triangle of the short exact
sequence of complexes `0 → 𝒢 ⊗ f^*ℱ₁ → 𝒢 ⊗ f^*ℱ₂ → 𝒢 ⊗ f^*ℱ₃ → 0`.

Here `H^i(S, -)` is the `i`-th cohomology of unbounded derived global sections, valued in
`Γ(S, 𝒪_S)`-modules, `H^i(X, -)` is read as a `Γ(S, 𝒪_S)`-module by restriction along `f^♯`, the
connecting morphisms are `CategoryTheory.Functor.homologySequenceδ` of the homological functor
`H^0` at the image triangles, and `𝒢 ⊗ f^*ℱ` is the complex with terms `𝒢^p ⊗ f^*ℱ`
(`Stacks.Cohomology.ExtProjectionFormula.tensorModuleComplex`); its short exactness is
`shortExact_Ψ`, proved from flatness of the `𝒢^p` over `S`.

Every step of the source's proof is proved: the projection formula ([Stacks, Tag 08EU]) through a
quasi-compact open neighbourhood of the support (`f` need not be quasi-compact), associativity,
Leray ([Stacks, Tag 0D5W]) and the flat identification `𝒢 ⊗^𝐋 Lf^*ℱ ≅ 𝒢 ⊗ f^*ℱ`
([Stacks, Tag 08DE] with flatness over `S`); the isomorphisms in degree `i` are obtained from a
degree-zero comparison evaluated at `ℱ[i]`, which is what makes them compatible with the
connecting morphisms. -/
@[stacks 0A1F "the functorial isomorphisms on quasi-coherent F for every i, and their \
compatibility with the boundary maps of every short exact sequence of quasi-coherent modules; \
H^i(S, -) = H^i of unbounded RΓ(S, -), H^i(X, -) as a Γ(S, O_S)-module along f^♯, boundary maps \
the connecting morphisms of H^0 at the image under RΓ(S, -) of K ⊗^L (triangle of the sequence) \
and at the image under RΓ(X, E ⊗^L -) of the triangle of 0 → G ⊗ f^*F₁ → G ⊗ f^*F₂ → G ⊗ f^*F₃ \
→ 0; \
no hypothesis beyond those of Tag 0DJQ"]
theorem extCohomologyIso_qcoh_boundary [IsNoetherian S] [LocallyOfFiniteType f]
    (hE : RingedSpace.IsPerfect (X := X.toRingedSpace) E)
    (hG : PerfectPushforward.FlatProperSupportComplex f G) :
    ∃ Φ : ∀ i : ℤ, (qcModules S).ι ⋙ DerivedCategory.singleFunctor (ModS S) 0 ⋙
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor S.toRingedSpace.sheaf).obj
            (Kobj f E G) ⋙
          Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsOverOpen S.toRingedSpace ⊤ ⋙
          DerivedCategory.homologyFunctor _ i ≅
        (qcModules S).ι ⋙ Ψ f G ⋙ DerivedCategory.Q ⋙
          (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.toRingedSpace.sheaf).obj
            E ⋙
          Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections f.toLRSHom.toShHom ⊤ ⋙
          DerivedCategory.homologyFunctor _ i,
      ∀ (T : ShortComplex (ModS S)) (hT : T.ShortExact) (h₁ : qcModules S T.X₁)
        (h₃ : qcModules S T.X₃) (i : ℤ),
        (Φ i).hom.app ⟨T.X₃, h₃⟩ ≫
          (H0 (S := S)).homologySequenceδ
            ((sourceSections f E).mapTriangle.obj
              (DerivedCategory.triangleOfSES (shortExact_Ψ f G hG T hT))) i (i + 1) rfl =
        (H0 (S := S)).homologySequenceδ
            ((sectionsS (S := S)).mapTriangle.obj
              ((tensorK f E G).mapTriangle.obj hT.singleTriangle)) i (i + 1) rfl ≫
          (Φ (i + 1)).hom.app ⟨T.X₁, h₁⟩ :=
  Stacks.Cohomology.ExtProjectionAssembly.exists_isos_of_model f E G hE hG (modelR f G hG)
    (modelμ f G hG) (shortExact_Ψ f G hG) (modelν f G hG) (modelTri f G hG)

end Stacks.Cohomology.ExtProjectionFormulaBoundary

end
