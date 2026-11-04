module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModuleHomMk
public import StacksCore.Tactic.StacksAttribute

/-!
# The functor from quasi-coherent modules on an algebraic space to the groupoid

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces, let `X` be an algebraic space and let
`φ : U ⟶ X` be a morphism with `t ≫ φ = s ≫ φ`.  Every quasi-coherent `𝒪_X`-module `ℱ`
gives a quasi-coherent module `(φ^*ℱ, α)` on the groupoid, by
`AlgebraicGeometry.Space.quasicoherentModuleOfSpaceBase`; this file assembles that assignment
into a functor `QCoh(𝒪_X) ⥤ QCoh(U, R, s, t, c)`, the functor underlying the equivalence of
[Stacks, Tag 03M3] for a target which is an algebraic space.

## Main definitions

* `AlgebraicGeometry.Space.spaceBaseObj` is the quasi-coherent module `(φ^*ℱ, α)` on the
  groupoid attached to a quasi-coherent `𝒪_X`-module, the object map of the functor.
* `AlgebraicGeometry.Space.spaceBasePullbackMap` is the inverse image along `φ` of a morphism of
  quasi-coherent `𝒪_X`-modules, read as a morphism of the underlying modules of the two
  quasi-coherent modules on the groupoid, and `AlgebraicGeometry.Space.spaceBaseHom` is the
  resulting morphism of quasi-coherent modules on the groupoid.
* `AlgebraicGeometry.Space.quasicoherentFromSpaceBase` is the functor
  `QCoh(𝒪_X) ⥤ QCoh(U, R, s, t, c)`.

## Main results

* `AlgebraicGeometry.Space.spaceBasePullbackMap_compatible`: the inverse image of a morphism is
  compatible with the two canonical transition morphisms.
* `AlgebraicGeometry.Space.spaceBaseHom_id` and
  `AlgebraicGeometry.Space.spaceBaseHom_comp`: the inverse image of a morphism respects
  identities and composition.
* `AlgebraicGeometry.Space.spaceBaseObj_F_obj` and
  `AlgebraicGeometry.Space.spaceBaseObj_alpha`: the two fields of the object map.
* `AlgebraicGeometry.Space.quasicoherentFromSpaceBase_obj` and
  `AlgebraicGeometry.Space.quasicoherentFromSpaceBase_map`: the object map and the morphism
  map of the functor.

## Implementation notes

The compatibility condition of `AlgebraicGeometry.Space.QuasicoherentModule.Hom` and the term
`M.obj` for a quasi-coherent sheaf `M` are very large once written out at these types, and a
declaration whose type spells either out exhausts the kernel's budget. So every morphism is built
with `AlgebraicGeometry.Space.QuasicoherentModule.homMk` from the named
`AlgebraicGeometry.Space.spaceBasePullbackMap` and its compatibility
`AlgebraicGeometry.Space.spaceBasePullbackMap_compatible`, and the object map is the named
`AlgebraicGeometry.Space.spaceBaseObj`; inlining any of them is a kernel timeout.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS} (φ : G.objects ⟶ X)
  (hφ : G.target ≫ φ = G.source ≫ φ)

/-- **The quasi-coherent module on the groupoid attached to a quasi-coherent `𝒪_X`-module**:
`AlgebraicGeometry.Space.quasicoherentModuleOfSpaceBase` applied to the underlying module and
its quasi-coherence. -/
def spaceBaseObj (M : QuasicoherentSheaves.{u, u} B S hS X.obj X.property) :
    QuasicoherentModule B S hS G :=
  quasicoherentModuleOfSpaceBase B S hS G φ hφ M.obj M.property

/-- The underlying module of `AlgebraicGeometry.Space.spaceBaseObj` is the inverse image of the
underlying module of the given quasi-coherent sheaf. -/
@[simp]
theorem spaceBaseObj_F_obj (M : QuasicoherentSheaves.{u, u} B S hS X.obj X.property) :
    (spaceBaseObj B S hS G φ hφ M).F.obj = (modulePullback B S hS φ).obj M.obj := by
  unfold spaceBaseObj
  exact quasicoherentModuleOfSpaceBase_F_obj B S hS G φ hφ M.obj M.property

/-- The transition morphism of `AlgebraicGeometry.Space.spaceBaseObj` is the canonical one. -/
@[simp]
theorem spaceBaseObj_alpha (M : QuasicoherentSheaves.{u, u} B S hS X.obj X.property) :
    (spaceBaseObj B S hS G φ hφ M).alpha = spaceBaseDescent B S hS G φ hφ M.obj := by
  unfold spaceBaseObj
  exact quasicoherentModuleOfSpaceBase_alpha B S hS G φ hφ M.obj M.property

/-- **The inverse image along `φ` of a morphism of quasi-coherent `𝒪_X`-modules**, read as a
morphism of the underlying modules of the two attached quasi-coherent modules on the groupoid:
`(AlgebraicGeometry.Space.modulePullback _ _ _ φ).map ψ.hom`. -/
def spaceBasePullbackMap
    {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (ψ : M ⟶ N) :
    (spaceBaseObj B S hS G φ hφ M).F.obj ⟶ (spaceBaseObj B S hS G φ hφ N).F.obj :=
  (modulePullback B S hS φ).map ψ.hom

/-- `AlgebraicGeometry.Space.spaceBasePullbackMap` is the inverse image of the underlying
morphism of modules. -/
theorem spaceBasePullbackMap_eq
    {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (ψ : M ⟶ N) :
    spaceBasePullbackMap B S hS G φ hφ ψ = (modulePullback B S hS φ).map ψ.hom :=
  rfl

/-- **The inverse image of a morphism is compatible with the canonical transition
morphisms.** -/
theorem spaceBasePullbackMap_compatible
    {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (ψ : M ⟶ N) :
    QuasicoherentModule.Compatible (spaceBasePullbackMap B S hS G φ hφ ψ) := by
  unfold QuasicoherentModule.Compatible
  rw [spaceBasePullbackMap_eq, spaceBaseObj_alpha, spaceBaseObj_alpha]
  exact spaceBaseDescent_naturality B S hS G φ hφ (M := M.obj) (N := N.obj) ψ.hom

/-- The inverse image of an identity is an identity. -/
theorem spaceBasePullbackMap_id (M : QuasicoherentSheaves.{u, u} B S hS X.obj X.property) :
    spaceBasePullbackMap B S hS G φ hφ (𝟙 M) =
      𝟙 (spaceBaseObj B S hS G φ hφ M).F.obj := by
  rw [spaceBasePullbackMap_eq]
  exact (modulePullback B S hS φ).map_id M.obj

/-- The inverse image of a composite is the composite of the inverse images. -/
theorem spaceBasePullbackMap_comp
    {M N P : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (ψ : M ⟶ N) (χ : N ⟶ P) :
    spaceBasePullbackMap B S hS G φ hφ (ψ ≫ χ) =
      spaceBasePullbackMap B S hS G φ hφ ψ ≫
        spaceBasePullbackMap B S hS G φ hφ χ := by
  rw [spaceBasePullbackMap_eq, spaceBasePullbackMap_eq, spaceBasePullbackMap_eq]
  exact (modulePullback B S hS φ).map_comp ψ.hom χ.hom

/-- **The inverse image along `φ` of a morphism of quasi-coherent `𝒪_X`-modules, as a morphism
of quasi-coherent modules on the groupoid.** -/
def spaceBaseHom {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (ψ : M ⟶ N) :
    spaceBaseObj B S hS G φ hφ M ⟶ spaceBaseObj B S hS G φ hφ N :=
  QuasicoherentModule.homMk (spaceBasePullbackMap B S hS G φ hφ ψ)
    (spaceBasePullbackMap_compatible B S hS G φ hφ ψ)

/-- The underlying morphism of modules of `AlgebraicGeometry.Space.spaceBaseHom` is
`AlgebraicGeometry.Space.spaceBasePullbackMap`. -/
@[simp]
theorem spaceBaseHom_hom
    {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (ψ : M ⟶ N) :
    (spaceBaseHom B S hS G φ hφ ψ).hom = spaceBasePullbackMap B S hS G φ hφ ψ :=
  rfl

/-- The inverse image of an identity is an identity. -/
theorem spaceBaseHom_id (M : QuasicoherentSheaves.{u, u} B S hS X.obj X.property) :
    spaceBaseHom B S hS G φ hφ (𝟙 M) = 𝟙 (spaceBaseObj B S hS G φ hφ M) := by
  refine QuasicoherentModule.Hom.ext ?_
  rw [spaceBaseHom_hom, QuasicoherentModule.id_hom]
  exact spaceBasePullbackMap_id B S hS G φ hφ M

/-- The inverse image of a composite is the composite of the inverse images. -/
theorem spaceBaseHom_comp
    {M N P : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (ψ : M ⟶ N) (χ : N ⟶ P) :
    spaceBaseHom B S hS G φ hφ (ψ ≫ χ) =
      spaceBaseHom B S hS G φ hφ ψ ≫ spaceBaseHom B S hS G φ hφ χ := by
  refine QuasicoherentModule.Hom.ext ?_
  rw [spaceBaseHom_hom, QuasicoherentModule.comp_hom, spaceBaseHom_hom, spaceBaseHom_hom]
  exact spaceBasePullbackMap_comp B S hS G φ hφ ψ χ

/-- **The functor `QCoh(𝒪_X) ⥤ QCoh(U, R, s, t, c)` attached to an étale `φ : U ⟶ X` with
`t ≫ φ = s ≫ φ`**: it sends a quasi-coherent `𝒪_X`-module `ℱ` to `φ^*ℱ` with its canonical
transition morphism, and a morphism to its inverse image along `φ`. -/
@[stacks 03M3 "the functor QCoh(𝒪_X) ⥤ QCoh(U, R, s, t, c) of the equivalence, for a target \
which is an algebraic space; this declaration is the functor itself, that it is an equivalence \
being proved in QuasicoherentFromSpaceBaseEquivalence.lean"]
def quasicoherentFromSpaceBase :
    QuasicoherentSheaves.{u, u} B S hS X.obj X.property ⥤ QuasicoherentModule B S hS G where
  obj M := spaceBaseObj B S hS G φ hφ M
  map ψ := spaceBaseHom B S hS G φ hφ ψ
  map_id M := spaceBaseHom_id B S hS G φ hφ M
  map_comp ψ χ := spaceBaseHom_comp B S hS G φ hφ ψ χ

/-- The object map of the functor is `AlgebraicGeometry.Space.spaceBaseObj`, that is,
`AlgebraicGeometry.Space.quasicoherentModuleOfSpaceBase`. -/
@[simp]
theorem quasicoherentFromSpaceBase_obj
    (M : QuasicoherentSheaves.{u, u} B S hS X.obj X.property) :
    (quasicoherentFromSpaceBase B S hS G φ hφ).obj M = spaceBaseObj B S hS G φ hφ M :=
  rfl

/-- The morphism map of the functor is the inverse image along `φ` of the underlying morphism of
modules. -/
@[simp]
theorem quasicoherentFromSpaceBase_map
    {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (ψ : M ⟶ N) :
    (quasicoherentFromSpaceBase B S hS G φ hφ).map ψ = spaceBaseHom B S hS G φ hφ ψ :=
  rfl

end AlgebraicGeometry.Space

end
