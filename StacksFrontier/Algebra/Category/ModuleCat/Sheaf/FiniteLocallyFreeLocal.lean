module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactnessSheafify
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Finite local freeness is local on the base

Let `R` be a sheaf of rings on a site `(C, J)` and let `M` be a sheaf of `R`-modules. If the
members of a covering family of the terminal object all have finite locally free restrictions of
`M`, then `M` itself is finite locally free.

`Stacks.SheafOfModules.LocalKernel.bindLocalGeneratorsData` already glues local generators of the
restrictions `M.over (Xc i)` into local generators of `M`, and
`Stacks.SheafOfModules.LocalKernel.isFiniteType_of_coversTop` uses that gluing to make being of
finite type local on the base. What is added here is the *locally free* half: the transport of a
family of generating sections from an iterated slice down to the base object, which the gluing
performs, carries a family whose canonical map out of the free module is an isomorphism to another
such family. So the glued local generators are locally free data as soon as all the given ones
are, and finite local freeness descends along the same gluing.

## Main results

* `Stacks.SheafOfModules.LocalKernel.isIso_generatingSectionsIteratedSlice_π`: the transport of a
  family of generating sections from an iterated slice down to the base object preserves being a
  basis.
* `Stacks.SheafOfModules.LocalKernel.bindLocalGeneratorsData_isLocallyFreeData` and
  `Stacks.SheafOfModules.LocalKernel.shrink_isLocallyFreeData`: the two steps of the gluing
  preserve local freeness of the data.
* `Stacks.SheafOfModules.LocalKernel.isFiniteLocallyFree_of_coversTop`: **finite local freeness is
  local on the base**, for an arbitrary sheaf of rings on an arbitrary site.
* `Stacks.SheafOfModules.LocalKernel.isFiniteLocallyFree_of_isOpenCover`: the same statement on the
  site of opens of a topological space, where the covering family is an open covering and the
  four sheafification hypotheses are automatic.

## Implementation notes

`AlgebraicGeometry.SheafOfModules.LocalGeneratorsData.IsLocallyFreeData` asks that the canonical
map `π` out of the free module on the index type be an isomorphism, so everything here is a
statement about `π` of a transported family of generating sections.  The two transports used by
`bindLocalGeneratorsData` are `SheafOfModules.GeneratingSections.ofEpi`, whose effect on `π` is
`SheafOfModules.GeneratingSections.ofEpi_π`, and `SheafOfModules.GeneratingSections.map`, for which
pinned Mathlib records no `π` lemma; `isIso_map_π` reads it off from `Equiv.symm_apply_apply`. The
canonical map of the image family and the image of the original canonical map, precomposed with
`SheafOfModules.mapFreeIso`, are literally the same term after one application of
`Equiv.symm_apply_apply`, because
`SheafOfModules.GeneratingSections.map` stores its sections as the image under
`SheafOfModules.freeHomEquiv` of exactly the morphism the right-hand side names.

The hypotheses are those of the gluing, not of the conclusion: besides the slice sheafification
hypotheses that `SheafOfModules.LocalGeneratorsData` itself carries, the *twice* iterated slices
appear, because a local datum for `M.over (Xc i)` lives over an object of `Over (Xc i)`. They are
not extra assumptions in the cases of interest —
`Stacks.SheafOfModules.SliceFinite.hasSheafify_iteratedSlice` derives them from the once iterated
ones — but they are kept as hypotheses rather than derived inside, because they occur in the
*statement* of the hypothesis `h` and so must be available when it is elaborated.

No Stacks tag is claimed here. Stacks Tag 01C6, which defines finite local freeness, is attached
to `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree`; this file proves a locality property of
that definition which the tag does not state.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules

universe u v₁ u₁

namespace Stacks.SheafOfModules.LocalKernel

section Free

variable {C : Type u₁} [Category.{v₁} C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Pushing a family of generating sections along an isomorphism preserves being a basis: the
canonical map out of the free module gets composed with that isomorphism. -/
lemma isIso_ofEpi_π {M N : _root_.SheafOfModules.{u} R} (σ : M.GeneratingSections) (p : M ⟶ N)
    [Epi p] (hσ : IsIso σ.π) (hp : IsIso p) : IsIso (σ.ofEpi p).π := by
  rw [GeneratingSections.ofEpi_π]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hσ hp

variable {C' : Type u₁} [Category.{v₁} C'] {J' : GrothendieckTopology C'}
  {S : Sheaf J' RingCat.{u}}
  [HasSheafify J' AddCommGrpCat.{u}] [J'.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Taking the image of a family of generating sections under a colimit-preserving functor
preserves being a basis. -/
lemma isIso_map_π {M : _root_.SheafOfModules.{u} R} (σ : M.GeneratingSections)
    (F : _root_.SheafOfModules.{u} R ⥤ _root_.SheafOfModules.{u} S)
    [PreservesColimitsOfSize.{u, u} F]
    (η : _root_.SheafOfModules.unit S ≅ F.obj (_root_.SheafOfModules.unit R))
    (hσ : IsIso σ.π) : IsIso (σ.map F η).π := by
  rw [show (σ.map F η).π = (mapFreeIso F σ.I η).hom ≫ F.map σ.π from Equiv.symm_apply_apply _ _]
  have : IsIso σ.π := hσ
  have h₁ : IsIso (F.map σ.π) := inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Iso.isIso_hom _) h₁

end Free

section Bind

variable {C : Type u₁} [Category.{v₁} C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Z : Over X), HasSheafify ((J.over X).over Z) AddCommGrpCat.{u}]
  [∀ (X : C) (Z : Over X), ((J.over X).over Z).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Reading a basis of `(M.over W).over Z` as a basis of `M.over Z.left`.** The transport of
`Stacks.SheafOfModules.LocalKernel.generatingSectionsIteratedSlice` is the image under the inverse
of an equivalence followed by pushing along an isomorphism, and both steps preserve being a
basis. -/
lemma isIso_generatingSectionsIteratedSlice_π {M : _root_.SheafOfModules.{u} R} {W : C}
    (Z : Over W) (s : ((M.over W).over Z).GeneratingSections) (hs : IsIso s.π) :
    IsIso (generatingSectionsIteratedSlice Z s).π :=
  isIso_ofEpi_π _ _ (isIso_map_π _ _ _ hs) (Iso.isIso_hom _)

/-- Gluing locally free local generators of the restrictions of `M` to the members of a covering
family gives locally free local generators of `M`. -/
instance bindLocalGeneratorsData_isLocallyFreeData (M : _root_.SheafOfModules.{u} R)
    {I : Type u₁} (Xc : I → C) (hX : J.CoversTop Xc)
    (D : Π i, (M.over (Xc i)).LocalGeneratorsData.{max u₁ v₁})
    [hD : ∀ i, (D i).IsLocallyFreeData] :
    (bindLocalGeneratorsData M Xc hX D).IsLocallyFreeData where
  isIso ij := isIso_generatingSectionsIteratedSlice_π _ _ ((hD ij.1).isIso ij.2)

/-- Shrinking the indexing type of local generators data preserves local freeness, since the
shrunk data reuses the original generating families. -/
instance shrink_isLocallyFreeData {M : _root_.SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData.{max u₁ v₁}) [hq : q.IsLocallyFreeData] :
    q.shrink.IsLocallyFreeData where
  isIso _ := hq.isIso _

/-- **Being finite locally free is local on the base.** If the members of a covering family of the
terminal object all have finite locally free restrictions of `M`, then `M` is finite locally free.

This is the finite-locally-free analogue of
`Stacks.SheafOfModules.LocalKernel.isFiniteType_of_coversTop`, and is proved by the same gluing:
`bindLocalGeneratorsData` assembles the local data, and the two instances above say that the
assembly keeps both the finiteness and the local freeness of the pieces. -/
theorem isFiniteLocallyFree_of_coversTop (M : _root_.SheafOfModules.{u} R) {I : Type u₁}
    (Xc : I → C) (hX : J.CoversTop Xc)
    (h : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree (M.over (Xc i))) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree M := by
  choose D hD using fun i ↦ (h i).exists_isFiniteLocallyFreeData
  have h₁ : ∀ i, (D i).IsLocallyFreeData := fun i ↦ (hD i).1
  have h₂ : ∀ i, (D i).IsFiniteType := fun i ↦ (hD i).2
  exact ⟨(bindLocalGeneratorsData M Xc hX D).shrink, inferInstance, inferInstance⟩

end Bind

section Space

open TopologicalSpace

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- **Being finite locally free is local on a topological space.** If the restriction of `M` to
each member of an open covering is finite locally free, then `M` is finite locally free.

This is `Stacks.SheafOfModules.LocalKernel.isFiniteLocallyFree_of_coversTop` on the site of opens,
where `TopologicalSpace.Opens.coversTop_iff` turns an open covering into a covering family of the
terminal object and all four sheafification hypotheses of that theorem are instances. -/
theorem isFiniteLocallyFree_of_isOpenCover (M : _root_.SheafOfModules.{u} R) {I : Type u}
    (U : I → Opens X) (hU : IsOpenCover U)
    (h : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (M.over (U i))) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
  isFiniteLocallyFree_of_coversTop M U ((Opens.coversTop_iff X U).mpr hU) h

end Space

end Stacks.SheafOfModules.LocalKernel

end
