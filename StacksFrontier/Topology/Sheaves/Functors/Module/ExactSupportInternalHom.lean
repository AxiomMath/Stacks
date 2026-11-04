module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorHomAdjunction
public import StacksFrontier.AlgebraicGeometry.ProjectionFormula.Basic
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupport

/-!
# Sheaf Hom out of a direct image along a closed quotient morphism

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces — a homeomorphism onto a closed
subset whose comorphism of structure sheaves is surjective — and write `ℰom(𝒪_Z, -)` for sheaf
Hom with exact support, the right adjoint of `i_*` of [Stacks, Tag 0A75].  For a sheaf of
`𝒪_Z`-modules `N` there is a canonical isomorphism of sheaves of `𝒪_X`-modules

`SheafHom_{𝒪_X}(i_* N, F) ≅ i_* SheafHom_{𝒪_Z}(N, ℰom(𝒪_Z, F))`,

natural in the `𝒪_X`-module `F` and in `N`.  This is the underived form of [Stacks, Tag 0E2I].

Both sides are right adjoints in the variable `F`.  The left-hand side is right adjoint to
`C ↦ (i_* N) ⊗_{𝒪_X} C` by the sheaf clause of [Stacks, Tag 03EO].  The right-hand side is a
composite of three right adjoints — `ℰom(𝒪_Z, -)`, then `SheafHom_{𝒪_Z}(N, -)`, then `i_*` —
hence right adjoint to the composite of their left adjoints, `C ↦ i_*(N ⊗_{𝒪_Z} i^* C)`.  The
projection formula for a closed quotient morphism identifies the two left adjoints, and the
isomorphism of the right adjoints follows.

## Main definitions

* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.tensorPushforwardAdjunction`,
  `tensorPushforwardExactSupportAdjunction` and `pushforwardTensorPullbackAdjunction`: the two
  adjunctions whose right adjoints are the two sides of the isomorphism, and the intermediate
  composite out of which the second is built.
* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.projectionFormulaLeftAdjointIso`
  is the projection formula as an isomorphism of those two left adjoints.
* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardMap` and
  `pushforwardSheafHomExactSupportMap`: the maps induced on the two sides by a morphism of
  `𝒪_Z`-modules, as conjugates of the maps induced on the left adjoints.

## Main results

* `Stacks.AffineProjectionFormula.sheafTensor_obj_map_eq` and `sheafTensor_map_app_eq`: the
  curried tensor product of sheaves of modules on a ringed space, read as the tensor bifunctor
  of the projection formula with one argument frozen.
* `Stacks.AffineProjectionFormula.projectionFormulaMap_natural_second` and
  `projectionFormulaMap_natural_first`: the two naturality statements of the
  projection-formula map, read for the curried tensor product.
* `CategoryTheory.rightAdjointUniq_ofNatIsoLeft_hom`: transporting an adjunction along an
  isomorphism of left adjoints and then comparing right adjoints is conjugation along that
  isomorphism.
* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardNatIso`:
  **the underived form of [Stacks, Tag 0E2I]**, as an isomorphism of functors of the
  `𝒪_X`-module variable, so that naturality in that variable is part of the statement.
* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.sheafHomPushforwardNatIso_hom`
  identifies its forward map as the conjugate of the projection formula, which is what pins it
  down, and `sheafHomPushforwardNatIso_natural` is its naturality in `N`.

## Implementation notes

The proof is by uniqueness of right adjoints: nothing is constructed on sections, and the only
input beyond the three adjunctions is an isomorphism of the two left adjoints.  That
isomorphism is the projection formula for a closed quotient morphism,
`Stacks.AffineProjectionFormula.projectionFormulaIso`, assembled into an isomorphism of
functors of the `𝒪_X`-module variable by its naturality.  So the projection formula is what
identifies the two left adjoints, and uniqueness of right adjoints does the rest; in
particular no quasi-coherence hypothesis appears, the projection formula being available here
without one.

Uniqueness of right adjoints is applied in the form `Adjunction.ofNatIsoLeft` followed by
`Adjunction.rightAdjointUniq`.  For the naturality in `N` the same morphism is needed in the
equivalent form `CategoryTheory.conjugateEquiv`, whose compatibility with composition
(`CategoryTheory.conjugateEquiv_comp`) turns the naturality square of the left adjoints into
the naturality square of the right adjoints; `rightAdjointUniq_ofNatIsoLeft_hom` is the
identification of the two forms.

Two spellings of the tensor product of sheaves of modules meet here and are definitionally
equal: `Stacks.SheafOfModules.Tensor.sheafTensor`, the curried bifunctor the
tensor--internal-Hom adjunction of [Stacks, Tag 03EO] is stated over, and
the uncurried canonical sheaf tensor, the bifunctor the projection formula is stated
over.  They agree on objects by `rfl`; on morphisms the two freeze one argument differently,
one by whiskering and one by tensoring with an identity, and `sheafTensor_obj_map_eq` and
`sheafTensor_map_app_eq` record that these agree.  No comparison isomorphism is involved.  The
two naturality lemmas are stated and proved in the spelling of the projection formula, with
the sheaf of rings written as `Stacks.RingedSpace.structureRingSheaf`, so that every rewriting
step happens in a single spelling; crossing to the spelling of the tensor--internal-Hom
adjunction is then one definitional step, taken by `exact` at the point of use.

The threefold composite on the right-hand side is written `(ℰom(𝒪_Z, -) ⋙ SheafHom_{𝒪_Z}(N, -))
⋙ i_*`, with explicit parentheses.  This is the association that `Adjunction.comp` produces,
and it is the same functor as `ℰom(𝒪_Z, -) ⋙ SheafHom_{𝒪_Z}(N, -) ⋙ i_*` by
`CategoryTheory.Functor.assoc`, which holds by `rfl`.  Declaring the other association costs a
definitional unfolding of `Functor.comp` inside every field of an `Adjunction` and of an
`Iso` of functors, which exhausts the kernel's budget at these universes; nothing is gained by
it, so the association of the construction is kept.

The module universe is the universe of the two spaces, as everywhere in this development: the
site of opens of a space in `Type u` has objects and morphisms in `Type u`, so the ring and
module universes of the tensor--internal-Hom adjunction both collapse to `u`, and that is the
universe `RingedSpaceModuleAdjunction.modulePullback` is available in.

## References

* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.RingedSpace
open Stacks.AffineProjectionFormula
open Stacks.SheafOfModules.InternalHom
open scoped CategoryTheory.Prod

noncomputable section

universe v₁ v₂ u₁ u₂ u

namespace Stacks.AffineProjectionFormula

/-- **The curried tensor product with its left argument frozen.**  Tensoring on the left by a
fixed sheaf of modules on a ringed space, as the curried bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor` gives it, acts on a morphism exactly as the tensor
bifunctor's uncurried form acts on that morphism paired with an identity. -/
theorem sheafTensor_obj_map_eq (X : RingedSpace.{u, u})
    (M : SheafOfModules.{u} (structureRingSheaf X))
    {N N' : SheafOfModules.{u} (structureRingSheaf X)} (ψ : N ⟶ N') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj M).map ψ =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
        (𝟙 M ×ₘ ψ) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map ⟨X.presheaf, X.IsSheaf⟩ (𝟙 M) ψ).symm

/-- **The curried tensor product with its right argument frozen.**  The action of the curried
bifunctor `Stacks.SheafOfModules.Tensor.sheafTensor` on a morphism, read at a fixed sheaf of
modules, is the action of its uncurried form on that morphism paired with an
identity. -/
theorem sheafTensor_map_app_eq (X : RingedSpace.{u, u})
    {M M' : SheafOfModules.{u} (structureRingSheaf X)} (φ : M ⟶ M')
    (N : SheafOfModules.{u} (structureRingSheaf X)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).map φ).app N =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩)).map
        (φ ×ₘ 𝟙 N) :=
  (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map ⟨X.presheaf, X.IsSheaf⟩ φ (𝟙 N)).symm

variable {Z X : RingedSpace.{u, u}} (f : Z ⟶ X)

/-- **Naturality of the projection-formula map in the module on the target**, read for the
curried tensor product: the map `f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)` commutes with the maps
induced by a morphism `ℋ ⟶ ℋ'`. -/
theorem projectionFormulaMap_natural_second (G : SheafOfModules.{u} (structureRingSheaf Z))
    {H H' : SheafOfModules.{u} (structureRingSheaf X)} (k : H ⟶ H') :
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).obj
          ((pushforwardFunctor f).obj G)).map k ≫ projectionFormulaMap f G H' =
      projectionFormulaMap f G H ≫ (pushforwardFunctor f).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩).obj G).map
          ((pullbackFunctor f).map k)) := by
  rw [sheafTensor_obj_map_eq X _ k, sheafTensor_obj_map_eq Z G,
    ← (pushforwardFunctor f).map_id G]
  exact projectionFormulaMap_natural f (𝟙 G) k

/-- **Naturality of the projection-formula map in the module on the source**, read for the
curried tensor product: the map `f_*𝒢 ⊗_{𝒪_X} ℋ ⟶ f_*(𝒢 ⊗_{𝒪_Z} f^*ℋ)` commutes with the maps
induced by a morphism `𝒢 ⟶ 𝒢'`. -/
theorem projectionFormulaMap_natural_first
    {G G' : SheafOfModules.{u} (structureRingSheaf Z)} (g : G ⟶ G')
    (H : SheafOfModules.{u} (structureRingSheaf X)) :
    projectionFormulaMap f G H ≫ (pushforwardFunctor f).map
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨Z.presheaf, Z.IsSheaf⟩).map g).app
          ((pullbackFunctor f).obj H)) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.presheaf, X.IsSheaf⟩).map
          ((pushforwardFunctor f).map g)).app H ≫ projectionFormulaMap f G' H := by
  rw [sheafTensor_map_app_eq Z g, sheafTensor_map_app_eq X _ H,
    ← (pullbackFunctor f).map_id H]
  exact (projectionFormulaMap_natural f g (𝟙 H)).symm

end Stacks.AffineProjectionFormula

namespace CategoryTheory

/-- **Transporting an adjunction along an isomorphism of left adjoints, then comparing right
adjoints, is conjugation along that isomorphism.**  For adjunctions `L₁ ⊣ R₁` and `L₂ ⊣ R₂` and
an isomorphism `e : L₁ ≅ L₂`, the forward map of the comparison of `R₁` with `R₂` obtained from
`Adjunction.ofNatIsoLeft` and `Adjunction.rightAdjointUniq` is the conjugate of `e.inv`. -/
theorem rightAdjointUniq_ofNatIsoLeft_hom {C : Type u₁} {D : Type u₂} [Category.{v₁} C]
    [Category.{v₂} D] {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : L₁ ≅ L₂) :
    (Adjunction.rightAdjointUniq adj₁ (Adjunction.ofNatIsoLeft adj₂ e.symm)).hom =
      conjugateEquiv adj₁ adj₂ e.inv := by
  ext F
  simp [Adjunction.rightAdjointUniq]

end CategoryTheory

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- The site of opens of the ambient ringed space `X`, with its open-cover topology. -/
abbrev siteX : GrothendieckTopology (Opens S.X.carrier) :=
  _root_.Opens.grothendieckTopology S.X.carrier

/-- The site of opens of the closed ringed subspace `Z`, with its open-cover topology. -/
abbrev siteZ : GrothendieckTopology (Opens S.Z.carrier) :=
  _root_.Opens.grothendieckTopology S.Z.carrier

/-- **The adjunction whose right adjoint is the left-hand side of Stacks 0E2I.**  Tensoring by
the direct image `i_* N` is left adjoint to sheaf Hom out of `i_* N`.  This is the sheaf clause
of [Stacks, Tag 03EO] on the site of opens of `X`. -/
def tensorPushforwardAdjunction (N : SheafOfModules.{u} (structureSheafRing S.Z)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf, S.X.IsSheaf⟩).obj
        ((modulePushforward S.i).obj N) ⊣
      internalHomSecondFunctor.{u, u, u, u} S.siteX ⟨S.X.presheaf, S.X.IsSheaf⟩
        ((modulePushforward S.i).obj N) :=
  sheafTensorHomAdjunction ⟨S.X.presheaf, S.X.IsSheaf⟩ ((modulePushforward S.i).obj N)

/-- **Tensoring on `Z` and pushing forward is left adjoint to sheaf Hom with exact support
followed by sheaf Hom out of `N`.**  This is the sheaf clause of [Stacks, Tag 03EO] on the site
of opens of `Z` composed with the exact-support adjunction of [Stacks, Tag 0A75]. -/
def tensorPushforwardExactSupportAdjunction (N : SheafOfModules.{u} (structureSheafRing S.Z)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.Z.presheaf, S.Z.IsSheaf⟩).obj N ⋙
        modulePushforward S.i ⊣
      S.sheafHomExactSupport ⋙
        internalHomSecondFunctor.{u, u, u, u} S.siteZ ⟨S.Z.presheaf, S.Z.IsSheaf⟩ N :=
  (sheafTensorHomAdjunction ⟨S.Z.presheaf, S.Z.IsSheaf⟩ N).comp
    S.modulePushforwardSheafHomExactSupportAdjunction

/-- **The adjunction whose right adjoint is the right-hand side of Stacks 0E2I.**  The functor
`C ↦ i_*(N ⊗_{𝒪_Z} i^* C)` is left adjoint to `ℰom(𝒪_Z, -)` followed by sheaf Hom out of `N`
followed by `i_*`: it is the composite of the left adjoints of those three functors, namely the
pullback-pushforward adjunction of [Stacks, Tag 0096], the sheaf clause of [Stacks, Tag 03EO]
on the site of opens of `Z`, and the exact-support adjunction of [Stacks, Tag 0A75]. -/
def pushforwardTensorPullbackAdjunction (N : SheafOfModules.{u} (structureSheafRing S.Z)) :
    modulePullback S.i ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.Z.presheaf, S.Z.IsSheaf⟩).obj N ⋙
          modulePushforward S.i ⊣
      (S.sheafHomExactSupport ⋙
          internalHomSecondFunctor.{u, u, u, u} S.siteZ ⟨S.Z.presheaf, S.Z.IsSheaf⟩ N) ⋙
        modulePushforward S.i :=
  (modulePullbackPushforwardAdjunction S.i).comp
    (S.tensorPushforwardExactSupportAdjunction N)

/-- **The projection formula as an isomorphism of the two left adjoints.**  The functors
`C ↦ (i_* N) ⊗_{𝒪_X} C` and `C ↦ i_*(N ⊗_{𝒪_Z} i^* C)` are isomorphic, by the projection
formula for a closed quotient morphism of ringed spaces together with its naturality in the
module on the target. -/
def projectionFormulaLeftAdjointIso (N : SheafOfModules.{u} (structureSheafRing S.Z)) :
    (Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf, S.X.IsSheaf⟩).obj
        ((modulePushforward S.i).obj N) ≅
      modulePullback S.i ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.Z.presheaf, S.Z.IsSheaf⟩).obj N ⋙
          modulePushforward S.i :=
  NatIso.ofComponents (fun F ↦ projectionFormulaIso S N F)
    (fun f ↦ projectionFormulaMap_natural_second S.i N f)

/-- The component of the isomorphism of left adjoints is the canonical projection-formula map,
rather than an unspecified isomorphism of objects. -/
theorem projectionFormulaLeftAdjointIso_hom_app (N : SheafOfModules.{u} (structureSheafRing S.Z))
    (F : SheafOfModules.{u} (structureSheafRing S.X)) :
    (S.projectionFormulaLeftAdjointIso N).hom.app F = projectionFormulaMap S.i N F :=
  rfl

/-- **The isomorphism of left adjoints is natural in `N`.**  A morphism `ν : N ⟶ N'` of
`𝒪_Z`-modules induces `i_* ν ⊗_{𝒪_X} -` on the one left adjoint and `i_*(ν ⊗_{𝒪_Z} i^* -)` on
the other, and the projection formula carries the first to the second. -/
theorem projectionFormulaLeftAdjointIso_natural
    {N N' : SheafOfModules.{u} (structureSheafRing S.Z)} (ν : N ⟶ N') :
    (S.projectionFormulaLeftAdjointIso N).hom ≫
        Functor.whiskerLeft (modulePullback S.i)
          (Functor.whiskerRight
            ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.Z.presheaf, S.Z.IsSheaf⟩).map ν)
            (modulePushforward S.i)) =
      (Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf, S.X.IsSheaf⟩).map
          ((modulePushforward S.i).map ν) ≫
        (S.projectionFormulaLeftAdjointIso N').hom :=
  NatTrans.ext (funext fun F ↦ projectionFormulaMap_natural_first S.i ν F)

/-- **Stacks 0E2I, underived form.**  For a sheaf of `𝒪_Z`-modules `N` there is a canonical
isomorphism of functors of the `𝒪_X`-module variable

`SheafHom_{𝒪_X}(i_* N, -) ≅ i_* SheafHom_{𝒪_Z}(N, ℰom(𝒪_Z, -))`,

whose naturality is the functoriality of the isomorphism in that variable.  Both sides are
right adjoint to the same functor, the two left adjoints being identified by the projection
formula for a closed quotient morphism. -/
def sheafHomPushforwardNatIso (N : SheafOfModules.{u} (structureSheafRing S.Z)) :
    internalHomSecondFunctor.{u, u, u, u} S.siteX ⟨S.X.presheaf, S.X.IsSheaf⟩
        ((modulePushforward S.i).obj N) ≅
      (S.sheafHomExactSupport ⋙
          internalHomSecondFunctor.{u, u, u, u} S.siteZ ⟨S.Z.presheaf, S.Z.IsSheaf⟩ N) ⋙
        modulePushforward S.i :=
  Adjunction.rightAdjointUniq (S.tensorPushforwardAdjunction N)
    (Adjunction.ofNatIsoLeft (S.pushforwardTensorPullbackAdjunction N)
      (S.projectionFormulaLeftAdjointIso N).symm)

/-- **The forward map of the underived Stacks 0E2I isomorphism is the conjugate of the
projection formula.**  This pins the isomorphism down: it is not an unspecified comparison of
two right adjoints but the one determined by the projection-formula isomorphism of the left
adjoints. -/
theorem sheafHomPushforwardNatIso_hom (N : SheafOfModules.{u} (structureSheafRing S.Z)) :
    (S.sheafHomPushforwardNatIso N).hom =
      conjugateEquiv (S.tensorPushforwardAdjunction N)
        (S.pushforwardTensorPullbackAdjunction N)
        (S.projectionFormulaLeftAdjointIso N).inv :=
  rightAdjointUniq_ofNatIsoLeft_hom _ _ _

/-- **The map induced in `N` on the left-hand side of the underived Stacks 0E2I isomorphism.**
A morphism `ν : N ⟶ N'` of `𝒪_Z`-modules induces `i_* ν ⊗_{𝒪_X} -` on the left adjoints, and
this is the conjugate natural transformation
`SheafHom_{𝒪_X}(i_* N', -) ⟶ SheafHom_{𝒪_X}(i_* N, -)`. -/
def sheafHomPushforwardMap {N N' : SheafOfModules.{u} (structureSheafRing S.Z)} (ν : N ⟶ N') :
    internalHomSecondFunctor.{u, u, u, u} S.siteX ⟨S.X.presheaf, S.X.IsSheaf⟩
        ((modulePushforward S.i).obj N') ⟶
      internalHomSecondFunctor.{u, u, u, u} S.siteX ⟨S.X.presheaf, S.X.IsSheaf⟩
        ((modulePushforward S.i).obj N) :=
  conjugateEquiv (S.tensorPushforwardAdjunction N') (S.tensorPushforwardAdjunction N)
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf, S.X.IsSheaf⟩).map
      ((modulePushforward S.i).map ν))

/-- **The map induced in `N` on the right-hand side of the underived Stacks 0E2I
isomorphism.**  A morphism `ν : N ⟶ N'` of `𝒪_Z`-modules induces `i_*(ν ⊗_{𝒪_Z} i^* -)` on the
left adjoints, and this is the conjugate natural transformation
`i_* SheafHom_{𝒪_Z}(N', ℰom(𝒪_Z, -)) ⟶ i_* SheafHom_{𝒪_Z}(N, ℰom(𝒪_Z, -))`. -/
def pushforwardSheafHomExactSupportMap {N N' : SheafOfModules.{u} (structureSheafRing S.Z)}
    (ν : N ⟶ N') :
    (S.sheafHomExactSupport ⋙
          internalHomSecondFunctor.{u, u, u, u} S.siteZ ⟨S.Z.presheaf, S.Z.IsSheaf⟩ N') ⋙
        modulePushforward S.i ⟶
      (S.sheafHomExactSupport ⋙
          internalHomSecondFunctor.{u, u, u, u} S.siteZ ⟨S.Z.presheaf, S.Z.IsSheaf⟩ N) ⋙
        modulePushforward S.i :=
  conjugateEquiv (S.pushforwardTensorPullbackAdjunction N')
    (S.pushforwardTensorPullbackAdjunction N)
    (Functor.whiskerLeft (modulePullback S.i)
      (Functor.whiskerRight
        ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.Z.presheaf, S.Z.IsSheaf⟩).map ν)
        (modulePushforward S.i)))

/-- **The underived Stacks 0E2I isomorphism is natural in `N`.**  For a morphism `ν : N ⟶ N'`
of `𝒪_Z`-modules the square formed by the isomorphisms at `N` and at `N'` and the two maps
induced by `ν` commutes.  It commutes because the corresponding square of left adjoints
commutes, which is the naturality of the projection formula in the module on the source, and
conjugation along an adjunction turns composites into composites. -/
theorem sheafHomPushforwardNatIso_natural {N N' : SheafOfModules.{u} (structureSheafRing S.Z)}
    (ν : N ⟶ N') :
    (S.sheafHomPushforwardNatIso N').hom ≫ S.pushforwardSheafHomExactSupportMap ν =
      S.sheafHomPushforwardMap ν ≫ (S.sheafHomPushforwardNatIso N).hom := by
  have hsq : Functor.whiskerLeft (modulePullback S.i)
          (Functor.whiskerRight
            ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.Z.presheaf, S.Z.IsSheaf⟩).map ν)
            (modulePushforward S.i)) ≫
        (S.projectionFormulaLeftAdjointIso N').inv =
      (S.projectionFormulaLeftAdjointIso N).inv ≫
        (Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf, S.X.IsSheaf⟩).map
          ((modulePushforward S.i).map ν) :=
    (Iso.eq_inv_comp (S.projectionFormulaLeftAdjointIso N)).mpr
      ((Category.assoc _ _ _).symm.trans
        ((Iso.comp_inv_eq (S.projectionFormulaLeftAdjointIso N')).mpr
          (S.projectionFormulaLeftAdjointIso_natural ν)))
  rw [sheafHomPushforwardNatIso_hom, sheafHomPushforwardNatIso_hom, sheafHomPushforwardMap,
    pushforwardSheafHomExactSupportMap]
  refine (conjugateEquiv_comp (S.tensorPushforwardAdjunction N')
    (S.pushforwardTensorPullbackAdjunction N') (S.pushforwardTensorPullbackAdjunction N)
    (S.projectionFormulaLeftAdjointIso N').inv _).trans ?_
  refine Eq.trans ?_ (conjugateEquiv_comp (S.tensorPushforwardAdjunction N')
    (S.tensorPushforwardAdjunction N) (S.pushforwardTensorPullbackAdjunction N) _
    (S.projectionFormulaLeftAdjointIso N).inv).symm
  exact congrArg
    (fun α ↦ conjugateEquiv (S.tensorPushforwardAdjunction N')
      (S.pushforwardTensorPullbackAdjunction N) α) hsq

end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end

end
