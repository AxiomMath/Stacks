module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleStalkConservative
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseAcyclic

/-!
# Geometric stalks of the formal glueing kernel

Stacks 0AF0 says that the functor of Stacks 0AEW is an equivalence, and the source proves it by
checking that the unit and the counit of the adjunction of Stacks 0AEY are isomorphisms "by
looking at stalks".  This file supplies the stalk apparatus for that check, **on the module side
and at the universe `u` of the module sections**, which is where the three maps to be inverted
already live: the functors of Stacks 0AEW and Stacks 0AEX, and the adjunction between them, are
all stated for `AlgebraicGeometry.Space.Modules` and
`AlgebraicGeometry.Space.QuasicoherentSheaves` at `.{u, u}`.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isIso_geometricModuleStalk_quasicoherent`: a map of
  quasi-coherent `𝒪_X`-modules whose geometric module stalks are all invertible is invertible.
* `AlgebraicGeometry.Space.geometricModuleStalkKernelIso`: the geometric module stalk of a kernel
  is the kernel of the geometric module stalks.
* `AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_glueingKernel_app`: the
  `𝒪_X`-module of Stacks 0AEX is, at each glueing triple, the pullback of the two canonical maps.
* `AlgebraicGeometry.Space.FormalGlueingSituation.geometricModuleStalkGlueingKernelIso`: the
  geometric module stalk of the `𝒪_X`-module of Stacks 0AEX, at a glueing triple, is the kernel
  of the stalk of the map whose kernel that module is.

## Implementation notes

**Why the stalks are taken module-side.**  The geometric stalk of an *abelian* sheaf on the small
étale site, `AlgebraicGeometry.Space.smallEtaleAbelianStalk`, is the colimit over the
neighbourhood category, which is a `CategoryTheory.Category.{u, u + 1}`; that colimit exists in
`AddCommGrpCat.{u + 1}` and not in `AddCommGrpCat.{u}`, so the abelian stalk is pinned one
universe above the module sections.  Stacks 0AER is stated there.  The module stalk is a
different construction — the fibre at the point of the site of Stacks 04K0 — and it is available
at `u` itself; `isIso_of_isIso_geometricModuleStalk` is the matching conservativity.  Working
module-side therefore needs no universe lift and no transport of Stacks 0AER across one, which is
why the kernel computation below is phrased for `AlgebraicGeometry.Space.Modules` throughout.

The kernel clause is `CategoryTheory.Limits.PreservesKernel.iso` for the stalk functor, which
preserves kernels because `Stacks.sheafModuleFiber` preserves homology.  The quasi-coherent
clause is the conservativity composed with the reflection of isomorphisms by a fully faithful
inclusion: `AlgebraicGeometry.Space.QuasicoherentSheaves` is a full subcategory of the
`𝒪_X`-modules, so a map of quasi-coherent modules is invertible as soon as it is invertible as a
map of modules.

## References

* [Stacks Project, Tag 0AF0](https://stacks.math.columbia.edu/tag/0AF0)
* [Stacks Project, Tag 0AEX](https://stacks.math.columbia.edu/tag/0AEX)
* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

/-- The structure sheaf of the small étale ringed site of `X`, as a sheaf of rings, which is the
sheaf of rings the `𝒪_X`-modules of this development are modules over. -/
abbrev structureRingSheafOfSite : Sheaf (SmallEtale.topology B S hS X) RingCat.{u} :=
  Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O

/-- **Geometric module stalks detect isomorphisms of quasi-coherent modules.**  A map of
quasi-coherent `𝒪_X`-modules which is invertible on the geometric module stalk at every
geometric point of `X` is invertible.

This is `AlgebraicGeometry.Space.isIso_of_isIso_geometricModuleStalk` — the module form of the
"enough points" consequence of Stacks 04K5 — carried across the fully faithful inclusion of the
quasi-coherent modules into all `𝒪_X`-modules, which reflects isomorphisms.  It is the first
step of the source's stalkwise proof of Stacks 0AF0. -/
theorem isIso_of_isIso_geometricModuleStalk_quasicoherent
    {M N : QuasicoherentSheaves.{u, u} B S hS X hX} (φ : M ⟶ N)
    (hφ : ∀ x : GeometricPoint B S hS X,
      IsIso ((geometricModuleStalkFunctor B S hS X hX (structureRingSheafOfSite B S hS X hX) x).map
        ((ObjectProperty.ι _).map φ))) :
    IsIso φ :=
  have : IsIso ((ObjectProperty.ι _).map φ) :=
    isIso_of_isIso_geometricModuleStalk B S hS X hX
      (structureRingSheafOfSite B S hS X hX) ((ObjectProperty.ι _).map φ) hφ
  isIso_of_reflects_iso φ (ObjectProperty.ι _)

/-- **The geometric module stalk of a kernel is the kernel of the geometric module stalks.**

The stalk functor preserves kernels because `Stacks.sheafModuleFiber` preserves homology; this
names the resulting comparison as an isomorphism. -/
def geometricModuleStalkKernelIso (x : GeometricPoint B S hS X)
    {F G : Modules.{u, u} B S hS X hX} (φ : F ⟶ G) :
    (geometricModuleStalkFunctor B S hS X hX
          (structureRingSheafOfSite B S hS X hX) x).obj (kernel φ) ≅
      kernel ((geometricModuleStalkFunctor B S hS X hX
        (structureRingSheafOfSite B S hS X hX) x).map φ) :=
  PreservesKernel.iso
    (geometricModuleStalkFunctor B S hS X hX (structureRingSheafOfSite B S hS X hX) x) φ

namespace FormalGlueingSituation

variable {B S hS}

/-- **The `𝒪_X`-module of Stacks 0AEX is a pullback at each glueing triple.**  The functor-level
square `AlgebraicGeometry.Space.FormalGlueingSituation.isPullback_glueingKernel`, read at a
single glueing triple `t`: that module, with its two projections, is the pullback of the two
canonical maps at `t`.

Limits in a functor category are computed objectwise, so evaluation at `t` carries the square
across.  This is the form the stalkwise argument for Stacks 0AF0 consumes, because a stalk
functor is applied to one `𝒪_X`-module at a time rather than to the diagram; and it is the
pullback presentation, rather than the kernel-of-a-difference presentation, that keeps the
biproduct instances of the ambient module category out of the computation — the same reason the
adjunction of Stacks 0AEY is assembled from the pullback square. -/
theorem isPullback_glueingKernel_app (D : FormalGlueingSituation B S hS)
    (t : D.moduleGlueingComma) :
    IsPullback (D.glueingKernelFst.app t) (D.glueingKernelSnd.app t)
      (D.restrictionOverlapMap.app t) (D.ambientOverlapMap.app t) :=
  D.isPullback_glueingKernel.map ((evaluation _ _).obj t)

/-- **The geometric module stalk of the `𝒪_X`-module of Stacks 0AEX.**  At a glueing triple `t`,
the stalk of `Ker(j_*ℋ ⊕ f_*𝒢 ⟶ (f ∘ j')_*𝒢|_V)` at a geometric point `x̄` of `X` is the kernel
of the stalk at `x̄` of the map of Stacks 0AEX evaluated at `t`.

This composes the objectwise description
`AlgebraicGeometry.Space.FormalGlueingSituation.glueingKernelDiagramObjIso` of the module of
Stacks 0AEX with `AlgebraicGeometry.Space.geometricModuleStalkKernelIso`.  It is the half of the
source's stalk computation for Stacks 0AF0 which says that taking the stalk commutes with forming
the kernel; the remaining half, that the resulting kernel of stalks is
`Ker(j_*ℋ_x̄ ⊕ 𝒢_ȳ ⟶ j'_*𝒢_ȳ)`, is the diagram chase the source omits. -/
def geometricModuleStalkGlueingKernelIso (D : FormalGlueingSituation B S hS)
    (x : GeometricPoint B S hS D.spaceX.1) (t : D.moduleGlueingComma) :
    (geometricModuleStalkFunctor B S hS D.spaceX.1 D.spaceX.2
        (structureRingSheafOfSite B S hS D.spaceX.1 D.spaceX.2) x).obj
        (D.glueingKernelDiagram.obj t) ≅
      kernel ((geometricModuleStalkFunctor B S hS D.spaceX.1 D.spaceX.2
        (structureRingSheafOfSite B S hS D.spaceX.1 D.spaceX.2) x).map
        (D.glueingKernelMap.app t)) :=
  (geometricModuleStalkFunctor B S hS D.spaceX.1 D.spaceX.2
        (structureRingSheafOfSite B S hS D.spaceX.1 D.spaceX.2) x).mapIso
      (D.glueingKernelDiagramObjIso t) ≪≫
    geometricModuleStalkKernelIso B S hS D.spaceX.1 D.spaceX.2 x (D.glueingKernelMap.app t)

end FormalGlueingSituation

end AlgebraicGeometry.Space

end
