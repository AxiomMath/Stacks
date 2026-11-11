module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceCokernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentExtensionLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite

/-!
# Kernels, images and cokernels of 03DL(8)-coherent modules on the fppf site of a stack

Let `𝒳` be an algebraic stack and `φ : ℱ ⟶ 𝒢` a map of `𝒪_𝒳`-modules on the big fppf ringed site
of `𝒳` which are coherent in the sectionwise sense of **Stacks 03DL(8)**,
`SheafOfModules.IsCoherentOnSite`.  This file proves, for that notion, the closure properties of
**Stacks 01BY** (stated there for a ringed space) on the fppf site of `𝒳`: `Ker(φ)`, `Coker(φ)`
and `Im(φ)`, computed in `Mod(𝒪_𝒳)`, are coherent, and the full subcategory `CohOnSite` of such
modules is abelian.  The content is `Stacks.SheafOfModules.isCoherentOnSite_kernel` and
`Stacks.SheafOfModules.isCoherentOnSite_cokernel`, which hold over an arbitrary ringed site.

These are **not** Stacks 0GR9.  That lemma is about coherence in the sense of Stacks 0GR6, under
which `Ker(φ)` may fail to be coherent and the image computed in `Mod(𝒪_𝒳)` can fail to be
coherent (`AlgebraicGeometry.Stack.exists_not_isCoherent_image_of_isCoherent`), whereas here both
are coherent.  Stacks 0GR9 is formalized for `AlgebraicGeometry.Stack.IsCoherent` in
`StacksFrontier.AlgebraicGeometry.Stacks.CoherentAbelianLocallyNoetherian`,
`StacksFrontier.AlgebraicGeometry.Stacks.CoherentCokernelLocallyNoetherian` and
`StacksFrontier.AlgebraicGeometry.Stacks.CoherentKernelLocallyQuasicoherentFlatBaseChange`.

## Main definitions

* `AlgebraicGeometry.Stack.coherentOnSiteModules`: the object property cutting out the
  `𝒪_𝒳`-modules coherent in the sense of Stacks 03DL(8), and
  `AlgebraicGeometry.Stack.CohOnSite` the full subcategory it defines.

## Main results

* `AlgebraicGeometry.Stack.isCoherentOnSite_cokernel`: the cokernel is coherent.
* `AlgebraicGeometry.Stack.isCoherentOnSite_kernel`: the kernel is coherent.
* `AlgebraicGeometry.Stack.isCoherentOnSite_image` and
  `AlgebraicGeometry.Stack.isCoherentOnSite_imageSubobject`: the abelian image and the
  categorical image are coherent.
* `AlgebraicGeometry.Stack.nonempty_abelian_cohOnSite`: `CohOnSite` is abelian.

## Implementation notes

**The two notions of coherence.**  `SheafOfModules.IsCoherentOnSite` is a different predicate
from `AlgebraicGeometry.Stack.IsCoherent`, the reading of Stacks 0GR6 as conditions (1) and (2) of
Stacks 0GR5.  On a locally Noetherian algebraic stack the first implies the second
(`AlgebraicGeometry.Stack.isCoherent_of_isCoherentOnSite`); the converse is not in this library.

**Local Noetherianity is a hypothesis of the statements here and is used by none of them**:
the closure properties hold over an arbitrary ringed site.  It is kept so that these statements
sit beside the extension clause `AlgebraicGeometry.Stack.isCoherentOnSite_X₂_of_shortExact`, which
also carries it.

**The module universe is the universe `u` of the schemes, and `𝒳` is assumed essentially small
there.**  Coherence of a cokernel, `Stacks.SheafOfModules.isCoherentOnSite_cokernel`, needs the
category of `𝒪_𝒳`-modules to have cokernels at all, hence sheafification of presheaves of
abelian groups with sections in the universe of the coefficient rings; on the fppf site of `𝒳`,
whose objects lie one universe above its schemes, that is supplied by
`AlgebraicGeometry.Stack.hasSheafifyAddCommGrpCat_associatedTopology`, which holds because the
site is essentially small in `u`.  Coherence of a kernel needs none of it and is proved at an
arbitrary module universe by `Stacks.SheafOfModules.isCoherentOnSite_kernel`; it is stated here
at `u` only so that it can feed the abelian structure.

**The abelian structure is not registered as an instance.**  It is the structure a full
subcategory of an abelian category closed under kernels, cokernels and finite products carries,
and is exhibited as the inhabitant of a `Nonempty` so that no choice principle enters a
statement.  Closure under finite products comes from closure under extensions, through
`AlgebraicGeometry.Stack.isCoherentOnSite_X₂_of_shortExact`: a binary coproduct in an additive
category is a biproduct, hence an extension of one summand by the other.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
* [Stacks Project, Tag 0GR9](https://stacks.math.columbia.edu/tag/0GR9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u t

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : AlgebraicStacks.{u, t} B S hS) [EssentiallySmall.{u} 𝒳.val.val.obj]

/-- The object property cutting out the `𝒪_𝒳`-modules that are coherent in the sense of
Stacks 03DL(8), on the big fppf ringed site of an algebraic stack `𝒳`.

This is not `AlgebraicGeometry.Stack.coherentModules`, which carries the conjunction of
conditions (1) and (2) of Stacks 0GR5; on a locally Noetherian stack this property implies that
one (`AlgebraicGeometry.Stack.isCoherent_of_isCoherentOnSite`), and the converse is not in this
library, so this one carries no tag. -/
def coherentOnSiteModules :
    ObjectProperty (SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) :=
  fun M ↦ SheafOfModules.IsCoherentOnSite M

/-- The full subcategory of `Mod(𝒪_𝒳)` of modules coherent in the sense of Stacks 03DL(8). -/
abbrev CohOnSite := (coherentOnSiteModules.{u, t} B S hS 𝒳).FullSubcategory

omit [EssentiallySmall.{u} 𝒳.val.val.obj] in
/-- An object of `AlgebraicGeometry.Stack.CohOnSite` is coherent. -/
theorem isCoherentOnSite_of_mem_cohOnSite (M : CohOnSite.{u, t} B S hS 𝒳) :
    SheafOfModules.IsCoherentOnSite M.obj :=
  M.property

/-- Let `𝒳` be a locally Noetherian algebraic stack and `φ : ℱ ⟶ 𝒢` a map of `𝒪_𝒳`-modules
coherent in the sense of Stacks 03DL(8).  The cokernel of `φ` computed in `Mod(𝒪_𝒳)` is
coherent in that sense.

Coherence is the sectionwise condition of Stacks 03DL(8) on the big fppf ringed site of `𝒳`, and
the content is Stacks 01BY (3) there: the cokernel projection is locally surjective and the
image of `φ` is of finite type, which bounds both the generators and the relations of the
quotient.  Local Noetherianity is not used. -/
theorem isCoherentOnSite_cokernel
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (hF : SheafOfModules.IsCoherentOnSite F) (hG : SheafOfModules.IsCoherentOnSite G)
    (φ : F ⟶ G) :
    SheafOfModules.IsCoherentOnSite (cokernel φ) :=
  _root_.Stacks.SheafOfModules.isCoherentOnSite_cokernel φ hF hG

omit [EssentiallySmall.{u} 𝒳.val.val.obj] in
/-- Let `𝒳` be a locally Noetherian algebraic stack and `φ : ℱ ⟶ 𝒢` a map of `𝒪_𝒳`-modules
coherent in the sense of Stacks 03DL(8).  The kernel of `φ` computed in `Mod(𝒪_𝒳)` is coherent
in that sense, hence is already the kernel of `φ` inside those modules.

Coherence is the sectionwise condition of Stacks 03DL(8) on the big fppf ringed site of `𝒳`, and
the content is Stacks 01BY (3) there: the kernel is of finite type by Stacks 01BY (2) and is a
subsheaf of the coherent source, so Stacks 01BY (1) applies.  This is not Stacks 0GR9 (3),
where coherence is that of Stacks 0GR6, the kernel may fail to be coherent and the coherator is
needed (`AlgebraicGeometry.Stack.kernel_mem_lqcohFbc_and_isCoherent_coherator_kernel`).  Local
Noetherianity is not used. -/
theorem isCoherentOnSite_kernel
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (hF : SheafOfModules.IsCoherentOnSite F) (hG : SheafOfModules.IsCoherentOnSite G)
    (φ : F ⟶ G) :
    SheafOfModules.IsCoherentOnSite (kernel φ) :=
  _root_.Stacks.SheafOfModules.isCoherentOnSite_kernel hF hG φ

/-- Let `𝒳` be a locally Noetherian algebraic stack and `φ : ℱ ⟶ 𝒢` a map of `𝒪_𝒳`-modules
coherent in the sense of Stacks 03DL(8).  The image of `φ` computed in `Mod(𝒪_𝒳)` is coherent in
that sense.

The abelian image is the kernel of the projection onto the cokernel, so this is the kernel
clause applied to `𝒢 ⟶ Coker(φ)`, whose target is coherent by the cokernel clause.  For
coherence in the sense of Stacks 0GR6 the image computed in `Mod(𝒪_𝒳)` need not be coherent
(`AlgebraicGeometry.Stack.exists_not_isCoherent_image_of_isCoherent`), so this is not
Stacks 0GR9 (2).  Local Noetherianity is not used. -/
theorem isCoherentOnSite_image
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (hF : SheafOfModules.IsCoherentOnSite F) (hG : SheafOfModules.IsCoherentOnSite G)
    (φ : F ⟶ G) :
    SheafOfModules.IsCoherentOnSite (Abelian.image φ) :=
  _root_.Stacks.SheafOfModules.isCoherentOnSite_kernel hG
    (isCoherentOnSite_cokernel B S hS 𝒳 _h𝒳 hF hG φ) (cokernel.π φ)

/-- The image of a map of `𝒪_𝒳`-modules coherent in the sense of Stacks 03DL(8), formed as
`CategoryTheory.Limits.image`, is coherent in that sense, being isomorphic to the abelian
image. -/
@[sga "6 I 3.4" "special case"]
theorem isCoherentOnSite_imageSubobject
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (hF : SheafOfModules.IsCoherentOnSite F) (hG : SheafOfModules.IsCoherentOnSite G)
    (φ : F ⟶ G) :
    SheafOfModules.IsCoherentOnSite (image φ) :=
  _root_.Stacks.SheafOfModules.isCoherentOnSite_of_iso (Abelian.imageIsoImage φ)
    (isCoherentOnSite_image B S hS 𝒳 _h𝒳 hF hG φ)

section Closure

/-- The coherent `𝒪_𝒳`-modules contain a zero object: a zero sheaf of modules is coherent over
any site. -/
theorem coherentOnSiteModules_containsZero :
    (coherentOnSiteModules.{u, t} B S hS 𝒳).ContainsZero where
  exists_zero :=
    ⟨HasZeroObject.zero.choose, HasZeroObject.zero.choose_spec,
      _root_.Stacks.SheafOfModules.isCoherentOnSite_zero HasZeroObject.zero.choose_spec⟩

omit [EssentiallySmall.{u} 𝒳.val.val.obj] in
/-- The coherent `𝒪_𝒳`-modules are closed under isomorphism. -/
theorem coherentOnSiteModules_isClosedUnderIsomorphisms :
    (coherentOnSiteModules.{u, t} B S hS 𝒳).IsClosedUnderIsomorphisms where
  of_iso e hM := _root_.Stacks.SheafOfModules.isCoherentOnSite_of_iso e hM

omit [EssentiallySmall.{u} 𝒳.val.val.obj] in
/-- The `𝒪_𝒳`-modules coherent in the sense of Stacks 03DL(8) are closed under kernels. -/
theorem coherentOnSiteModules_isClosedUnderKernels
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳) :
    (coherentOnSiteModules.{u, t} B S hS 𝒳).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact _root_.Stacks.SheafOfModules.isCoherentOnSite_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel φ) hk)
      (isCoherentOnSite_kernel B S hS 𝒳 h𝒳 hF hG φ)

/-- The `𝒪_𝒳`-modules coherent in the sense of Stacks 03DL(8) are closed under cokernels. -/
theorem coherentOnSiteModules_isClosedUnderCokernels
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳) :
    (coherentOnSiteModules.{u, t} B S hS 𝒳).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact _root_.Stacks.SheafOfModules.isCoherentOnSite_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel φ) hk)
      (isCoherentOnSite_cokernel B S hS 𝒳 h𝒳 hF hG φ)

/-- The `𝒪_𝒳`-modules coherent in the sense of Stacks 03DL(8) are closed under extensions, by
`AlgebraicGeometry.Stack.isCoherentOnSite_X₂_of_shortExact`. -/
theorem coherentOnSiteModules_isClosedUnderExtensions
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳) :
    (coherentOnSiteModules.{u, t} B S hS 𝒳).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hT h₁ h₃ :=
    isCoherentOnSite_X₂_of_shortExact B S hS 𝒳 h𝒳 hT h₁ h₃

/-- The coherent `𝒪_𝒳`-modules are closed under binary coproducts: a binary coproduct in an
additive category is a biproduct, hence an extension of one summand by the other. -/
theorem coherentOnSiteModules_isClosedUnderBinaryCoproducts
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳) :
    (coherentOnSiteModules.{u, t} B S hS 𝒳).IsClosedUnderBinaryCoproducts := by
  have := coherentOnSiteModules_isClosedUnderIsomorphisms.{u, t} B S hS 𝒳
  have := coherentOnSiteModules_isClosedUnderExtensions.{u, t} B S hS 𝒳 h𝒳
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨D, hD⟩
  exact (coherentOnSiteModules.{u, t} B S hS 𝒳).prop_of_iso
    ((biprod.isoCoprod (D.obj ⟨WalkingPair.left⟩) (D.obj ⟨WalkingPair.right⟩)).trans
      (HasColimit.isoOfNatIso (diagramIsoPair D)).symm)
    ((coherentOnSiteModules.{u, t} B S hS 𝒳).prop_biprod (hD ⟨WalkingPair.left⟩)
      (hD ⟨WalkingPair.right⟩))

/-- The coherent `𝒪_𝒳`-modules are closed under finite coproducts: the empty coproduct is a
zero module and the binary case is closure under extensions. -/
theorem coherentOnSiteModules_isClosedUnderFiniteCoproducts
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳) :
    (coherentOnSiteModules.{u, t} B S hS 𝒳).IsClosedUnderFiniteCoproducts :=
  have := coherentOnSiteModules_containsZero.{u, t} B S hS 𝒳
  have := coherentOnSiteModules_isClosedUnderIsomorphisms.{u, t} B S hS 𝒳
  have := coherentOnSiteModules_isClosedUnderBinaryCoproducts.{u, t} B S hS 𝒳 h𝒳
  have : HasFiniteBiproducts (SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) := Abelian.hasFiniteBiproducts
  have : HasFiniteCoproducts (SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) := hasFiniteCoproducts_of_hasFiniteBiproducts _
  ObjectProperty.IsClosedUnderFiniteCoproducts.mk'

/-- The category `CohOnSite` of `𝒪_𝒳`-modules coherent in the sense of Stacks 03DL(8), on a
locally Noetherian algebraic stack, is abelian.

The structure is the one a full subcategory of an abelian category closed under kernels,
cokernels and finite products carries; the kernel and cokernel closure are proved above and the
product closure comes from closure under extensions.  This is not the abelian clause of
Stacks 0GR9, which is about `AlgebraicGeometry.Stack.Coh`
(`AlgebraicGeometry.Stack.nonempty_abelian_coh`).  Local Noetherianity is not used. -/
theorem nonempty_abelian_cohOnSite
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳) :
    Nonempty (Abelian (CohOnSite.{u, t} B S hS 𝒳)) := by
  have := coherentOnSiteModules_containsZero.{u, t} B S hS 𝒳
  have := coherentOnSiteModules_isClosedUnderIsomorphisms.{u, t} B S hS 𝒳
  have := coherentOnSiteModules_isClosedUnderKernels.{u, t} B S hS 𝒳 h𝒳
  have := coherentOnSiteModules_isClosedUnderCokernels.{u, t} B S hS 𝒳 h𝒳
  have := coherentOnSiteModules_isClosedUnderFiniteCoproducts.{u, t} B S hS 𝒳 h𝒳
  have := ObjectProperty.IsClosedUnderFiniteProducts.of_isClosedUnderFiniteCoproducts
    (coherentOnSiteModules.{u, t} B S hS 𝒳)
  exact ⟨inferInstance⟩

end Closure

end AlgebraicGeometry.Stack

end
