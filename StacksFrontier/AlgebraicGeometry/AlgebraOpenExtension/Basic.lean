module

public import StacksFrontier.AlgebraicGeometry.RelativeSpecBaseChange.Adjunction

/-!
# Extending a sheaf of algebras across an open immersion: the fibre product

Let `j : U ⟶ X` be an open immersion of schemes, `A` a sheaf of commutative `𝒪_X`-algebras,
`G` a sheaf of commutative `𝒪_U`-algebras and `φ : G ⟶ A|_U` a morphism of `𝒪_U`-algebras.
The *extension algebra* of `φ` is the fibre product

```
A ×_{j_*(A|_U)} j_* G
```

taken in `Stacks.RelativeSpec.AlgebraSheaf X`, the first leg being the unit of the adjunction
`Stacks.AffineAlgebraEquivalence.algebraPullbackPushforwardAdjunction` and the second the direct
image of `φ`. It is the algebra-level analogue of the construction behind
[Stacks, Tag 01PE], whose module-level form is the kernel
`Ker(F ⊕ j_*G ⟶ j_*j^*F)` of
`StacksFrontier/AlgebraicGeometry/ResolutionsAndBounds/QuasiCoherentExtension.lean`; a fibre
product replaces the kernel because `Stacks.RelativeSpec.AlgebraSheaf X` is not additive.

## Main definitions

* `Stacks.AlgebraicGeometry.AlgebraOpenExtension.extensionAlgebra` is the fibre product, and
  `extensionProjection`, `extensionDirectImageLeg` its two legs.

## Main results

* `Stacks.AlgebraicGeometry.AlgebraOpenExtension.isPullback_extensionAlgebra`: the defining
  cartesian square.
* `Stacks.AlgebraicGeometry.AlgebraOpenExtension.mono_extensionProjection`: the projection to
  `A` is a monomorphism as soon as `φ` is, so the extension is a *subalgebra* of `A` exactly
  when `G` is a subalgebra of `A|_U`.
* `Stacks.AlgebraicGeometry.AlgebraOpenExtension.isPullback_extensionAlgebra_right`: the
  underlying sheaf of rings of the extension is the fibre product of the underlying sheaves of
  rings, and `extensionAlgebra_sections` reads that off on sections: a section of the extension
  over `V` is a pair consisting of a section of `A` over `V` and a section of `G` over
  `j⁻¹V` agreeing in `(A|_U)(j⁻¹V)`.
Part (1) of [Stacks, Tag 01PE] at the level of modules — the direct image being the extension —
is `AlgebraicGeometry.exists_quasicoherent_restrict_iso`, in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionCriteria/OpenExtension.lean`.

## What is not done, and no stacks attribute for the algebra-level statement

**No `@[stacks]` attribute is attached to anything in this file, and none could be.** Tag 01PE
has exactly three labels — `extend_quasicoherent`, `extend_quasicoherent_morphism`,
`extend_quasicoherent_subsheaf` — and all three of its tagged assertions are about
`AlgebraicGeometry.Scheme.Modules`, i.e. about sheaves of *modules*. There is no algebra-level
assertion under that tag, so the algebra analogue below is infrastructure for Tag 05JT and Tag
0817 and carries no tag of its own. (Part (1) of the tag is proved, at module level, in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionCriteria/OpenExtension.lean`.)

The algebra-level Tag 01PE — "`A ×_{j_*(A|_U)} j_*G` is a quasi-coherent subalgebra of `A`
restricting to `G` on `U`" — is **not** proved here. What is proved is everything that is formal:
the fibre product exists, its underlying sheaf of rings and its sections are the expected fibre
products, and the projection to `A` is a monomorphism when `φ` is. The two remaining assertions
and what each needs:

* **`(algebraPullback j).obj (extensionAlgebra j A G φ) ≅ G`.** The module-level proof
  (`AlgebraicGeometry.graphKernelPullbackIso`) gets this from exactness of restriction together
  with `CategoryTheory.Adjunction.counit_isIso_of_R_fully_faithful`. At the level of algebras
  the corresponding inputs are both absent. First, full faithfulness of
  `TopCat.Sheaf.pushforward CommRingCat j.base` for an open embedding: the repository has this
  shape only for a *closed* subset inclusion
  (`Stacks.Topology.Sheaves.ClosedImmersion`, `StacksFrontier/Topology/Sheaves/ClosedImmersion/PushforwardAlgStruct.lean:157`), and pinned
  Mathlib's `Mathlib/Topology/Sheaves/Functors.lean` states no fullness or faithfulness for
  `Topology.IsOpenEmbedding`. Second, `IsIso (inverseImageStructureMap j)` — the identification
  `j⁻¹𝒪_X ≅ 𝒪_U` that makes `algebraPullback j` the plain inverse image rather than a pushout
  along it: there is no `IsIso`, `Epi` or `Mono` statement about
  `Stacks.AffineAlgebraEquivalence.inverseImageStructureMap` anywhere in either tree.
* **Quasi-coherence of the fibre product.** `AlgebraSheaf.IsQuasicoherent` is quasi-coherence of
  `AlgebraSheaf.underlyingModule`, so this needs two bridges that do not exist: that
  `AlgebraSheaf.underlyingModuleFunctor` carries the fibre product above to the fibre product of
  underlying modules, and that it carries `algebraPushforward j` to
  `AlgebraicGeometry.Scheme.Modules.pushforward j`. Granted both, the module-level work is
  already available and needs nothing new — `graphKernel_isQuasicoherent` for the fibre product and
  `Stacks.AlgebraicGeometry.RelativeMayerVietoris.pushforward_isQuasicoherent` (Tag 01LC) for
  the direct image.

## Implementation notes

**No pushforward functor is constructed here, because one already exists.**
`Stacks.AffineAlgebraEquivalence.algebraPushforward`
(`StacksFrontier/AlgebraicGeometry/RelativeSpecBaseChange/Adjunction.lean`) is stated for an
*arbitrary* morphism of schemes `g : T ⟶ S`, so `j_*` for sheaves of algebras along an open
immersion is the instantiation `algebraPushforward j`, and its right-adjointness to restriction
is `algebraPullbackPushforwardAdjunction j`. Nothing about open immersions is used to build it.

Everything else here is free from the ambient `Under`-category structure, which is the point:
`Stacks.RelativeSpec.AlgebraSheaf X` is `CategoryTheory.Under X.sheaf`, and
`CategoryTheory.Under.createsLimitsOfSize` says `CategoryTheory.Under.forget` *creates* limits.
So the fibre product of algebra sheaves exists whenever sheaves of commutative rings have
fibre products, its underlying sheaf of rings is the fibre product of the underlying sheaves of
rings, and the structure morphism from `𝒪_X` is induced; none of it has to be built by hand, and
the algebra structure on the extension is not separate data.

The one instance that must be spelled out is `HasPullbacks` for sheaves of commutative rings:
`TopCat.Sheaf CommRingCat X` is reducibly `CategoryTheory.Sheaf (Opens.grothendieckTopology X)
CommRingCat`, but instance search does not see through the former, exactly as
`Stacks.AffineAlgebraEquivalence.hasPushouts_topCatSheafCommRingCat` records for pushouts.

## References

* [Stacks Project, Tag 01PE](https://stacks.math.columbia.edu/tag/01PE)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence Stacks.RelativeSpec

universe u

namespace Stacks.AlgebraicGeometry.AlgebraOpenExtension

/-! ### Fibre products of algebra sheaves -/

/-- Fibre products exist in the category of sheaves of commutative rings on a topological
space: `TopCat.Sheaf C X` is by definition the category of `C`-valued sheaves for the
Grothendieck topology on the opens of `X`, which has every limit that `C` has. -/
public instance hasPullbacks_topCatSheafCommRingCat (X : TopCat.{u}) :
    HasPullbacks (TopCat.Sheaf CommRingCat.{u} X) :=
  inferInstanceAs
    (HasPullbacks (Sheaf (_root_.Opens.grothendieckTopology X) CommRingCat.{u}))

/-- Fibre products exist in the category of sheaves of commutative `𝒪_X`-algebras: limits in an
`Under` category are created by the forgetful functor. -/
public instance hasPullbacks_algebraSheaf (X : Scheme.{u}) :
    HasPullbacks (AlgebraSheaf X) :=
  inferInstanceAs (HasPullbacks (Under X.sheaf))

variable {U X : Scheme.{u}} (j : U ⟶ X) (A : AlgebraSheaf X) (G : AlgebraSheaf U)
  (φ : G ⟶ (algebraPullback j).obj A)

/-- The unit `A ⟶ j_*(A|_U)` of the restriction–direct image adjunction for algebra sheaves. -/
public def extensionUnit : A ⟶ (algebraPushforward j).obj ((algebraPullback j).obj A) :=
  (algebraPullbackPushforwardAdjunction j).unit.app A

/-- The extension algebra of `φ : G ⟶ A|_U`: the fibre product `A ×_{j_*(A|_U)} j_*G` of
sheaves of commutative `𝒪_X`-algebras. -/
public def extensionAlgebra : AlgebraSheaf X :=
  pullback (extensionUnit j A) ((algebraPushforward j).map φ)

/-- The projection `A ×_{j_*(A|_U)} j_*G ⟶ A` of the extension algebra to `A`. -/
public def extensionProjection : extensionAlgebra j A G φ ⟶ A :=
  pullback.fst (extensionUnit j A) ((algebraPushforward j).map φ)

/-- The projection `A ×_{j_*(A|_U)} j_*G ⟶ j_*G` of the extension algebra to the direct image
of `G`. -/
public def extensionDirectImageLeg :
    extensionAlgebra j A G φ ⟶ (algebraPushforward j).obj G :=
  pullback.snd (extensionUnit j A) ((algebraPushforward j).map φ)

/-- **The defining cartesian square of the extension algebra.** -/
public theorem isPullback_extensionAlgebra :
    IsPullback (extensionProjection j A G φ) (extensionDirectImageLeg j A G φ)
      (extensionUnit j A) ((algebraPushforward j).map φ) :=
  IsPullback.of_hasPullback _ _

/-! ### The extension is a subalgebra exactly when `G` is -/

/-- The direct image of algebra sheaves preserves monomorphisms, being a right adjoint. -/
public instance preservesMonomorphisms_algebraPushforward :
    (algebraPushforward j).PreservesMonomorphisms :=
  haveI : (algebraPushforward j).IsRightAdjoint :=
    (algebraPullbackPushforwardAdjunction j).isRightAdjoint
  inferInstance

/-- **The extension algebra is a subalgebra of `A` whenever `G` is a subalgebra of `A|_U`.**
The projection to `A` is the pullback of the monomorphism `j_*φ`. -/
public instance mono_extensionProjection [Mono φ] :
    Mono (extensionProjection j A G φ) :=
  inferInstanceAs (Mono (pullback.fst (extensionUnit j A) ((algebraPushforward j).map φ)))

/-! ### The underlying sheaf of rings, and sections -/

/-- **The underlying sheaf of rings of the extension algebra is the fibre product of the
underlying sheaves of rings.** This is `CategoryTheory.Under.forget` creating limits; it is why
the algebra structure on the extension costs nothing. -/
public theorem isPullback_extensionAlgebra_right :
    IsPullback (extensionProjection j A G φ).right (extensionDirectImageLeg j A G φ).right
      (extensionUnit j A).right ((algebraPushforward j).map φ).right :=
  (isPullback_extensionAlgebra j A G φ).map (Under.forget X.sheaf)

omit φ in
/-- Sections over a fixed open, as a functor on sheaves of commutative rings. Limits of
sheaves are computed in presheaves and presheaf limits are pointwise, so this functor
preserves limits. -/
public def sectionsFunctor (V : X.Opens) :
    TopCat.Sheaf CommRingCat.{u} X.toPresheafedSpace.carrier ⥤ CommRingCat.{u} :=
  sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op V)

omit φ in
/-- Sections over an open preserve finite limits: `sheafToPresheaf` creates them and limits of
presheaves are pointwise. -/
public instance preservesFiniteLimits_sectionsFunctor (V : X.Opens) :
    PreservesFiniteLimits (sectionsFunctor (X := X) V) :=
  inferInstanceAs (PreservesFiniteLimits
    (sheafToPresheaf (_root_.Opens.grothendieckTopology _) CommRingCat.{u} ⋙
      (evaluation _ _).obj (op V)))

/-- **A section of the extension algebra over `V` is a pair of a section of `A` over `V` and a
section of `j_*G` over `V`, agreeing in `j_*(A|_U)`.** -/
public theorem isPullback_extensionAlgebra_sections (V : X.Opens) :
    IsPullback
      ((sectionsFunctor V).map (extensionProjection j A G φ).right)
      ((sectionsFunctor V).map (extensionDirectImageLeg j A G φ).right)
      ((sectionsFunctor V).map (extensionUnit j A).right)
      ((sectionsFunctor V).map ((algebraPushforward j).map φ).right) :=
  (isPullback_extensionAlgebra_right j A G φ).map (sectionsFunctor V)

end Stacks.AlgebraicGeometry.AlgebraOpenExtension

end
