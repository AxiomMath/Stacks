module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceCokernels
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceFiniteFamilies
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentExtensionLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentModules
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriek
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite

/-!
# Kernels, images and cokernels of maps of coherent modules on a locally Noetherian stack

Let `𝒳` be a locally Noetherian algebraic stack and `φ : ℱ ⟶ 𝒢` a map of coherent
`𝒪_𝒳`-modules.  **Stacks 0GR9** asserts that `Coh(𝒪_𝒳)` is abelian and that

1. `Coker(φ)` computed in `Mod(𝒪_𝒳)` is coherent,
2. `Im(φ)` computed in `Mod(𝒪_𝒳)` is coherent, and
3. `Ker(φ)` computed in `Mod(𝒪_𝒳)` *may fail* to be coherent, but lies in `LQCoh^fbc(𝒪_𝒳)`, and
   `Q(Ker(φ))` is coherent and is the kernel of `φ` in `Coh(𝒪_𝒳)`.

All four are proved here with coherence read as the sectionwise condition of **Stacks 03DL(8)**,
`SheafOfModules.IsCoherentOnSite`, on the big fppf ringed site of `𝒳`.  Under that reading the
three closure properties hold over an arbitrary ringed site, by **Stacks 01BY (3)**, so clause
(3) needs no coherator: the kernel formed in `Mod(𝒪_𝒳)` is itself coherent and is therefore
already the kernel inside the subcategory.

## Main definitions

* `AlgebraicGeometry.Stack.coherentOnSiteModules`: the object property cutting out the
  `𝒪_𝒳`-modules coherent in the sense of Stacks 03DL(8), and
  `AlgebraicGeometry.Stack.CohOnSite` the full subcategory it defines.

## Main results

* `AlgebraicGeometry.Stack.isCoherentOnSite_cokernel`: **Stacks 0GR9** part (1).
* `AlgebraicGeometry.Stack.isCoherentOnSite_image` and
  `AlgebraicGeometry.Stack.isCoherentOnSite_imageSubobject`: **Stacks 0GR9** part (2), for the
  abelian image and for the categorical image.
* `AlgebraicGeometry.Stack.isCoherentOnSite_kernel`: **Stacks 0GR9** part (3).
* `AlgebraicGeometry.Stack.nonempty_abelian_cohOnSite`: **Stacks 0GR9**, the abelian-category
  clause.

## Implementation notes

**Which reading of "coherent" is used.**  Stacks 0GR6 calls an `𝒪_𝒳`-module coherent when it
satisfies the four equivalent conditions of Stacks 0GR5, and that equivalence is not available
in this library: `StacksFrontier.AlgebraicGeometry.Stacks.CoherenceConditions` proves only the
implication (2) ⟹ (1) and records that conditions (3) and (4) cannot be stated at all, the
restriction of a module on the big fppf site of `𝒳` to the small étale site of an algebraic
space (Stacks 073M) being absent.  Everything below therefore reads coherence as Stacks
03DL(8), as `StacksFrontier.AlgebraicGeometry.Stacks.CoherentExtensionLocallyNoetherian` does for
the extension clause Stacks 0GRA and
`StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian` for the algebraic-spaces analogue
Stacks 07UC.  **This is a different predicate from `AlgebraicGeometry.Stack.IsCoherent`**, the
reading of Stacks 0GR5(2) that Stacks 0GR7 and 0GR8 are stated for, and the two are compared
nowhere in this library.

**What that costs at clause (3), and why it is not a contradiction.**  The source's warning that
`Ker(φ)` may fail to be coherent is about coherence in the sense of Stacks 0GR6, and it is what
forces the coherator `Q` of Stacks 0778 into the source's formulation.  Stacks 03DL(8)-coherence
is a strictly sectionwise condition and is closed under kernels over any ringed site, so under
that reading the kernel formed in `Mod(𝒪_𝒳)` is coherent and the two remaining assertions of
clause (3) — that `Ker(φ)` lies in `LQCoh^fbc(𝒪_𝒳)`, which is Stacks 0771 part (2), and that
`Q(Ker(φ))` is coherent — are not needed to exhibit the kernel of `φ` inside the subcategory.
Neither is proved here: the first is not in the library, and the second is the one place where
local Noetherianity of `𝒳` carries weight in the source, through conditions (3) and (4) of
Stacks 0GR5.  The source's own clause (3) for Stacks 0GR6-coherence is therefore **not**
delivered.

**Local Noetherianity is a hypothesis of every statement here and is used by none of them**, as
it is throughout the family of files around Stacks 0GR5, 0GR7, 0GR8 and 0GRA: Stacks 01BY (3)
holds over an arbitrary ringed site.  It is kept because the source has it, and because it is
what makes "coherent" well defined there.

**The module universe is the universe `u` of the schemes, and `𝒳` is assumed essentially small
there.**  Coherence of a cokernel, `Stacks.SheafOfModules.isCoherentOnSite_cokernel`, needs the
category of `𝒪_𝒳`-modules to have cokernels at all, hence sheafification of presheaves of
abelian groups with sections in the universe of the coefficient rings; on the fppf site of `𝒳`,
whose objects lie one universe above its schemes, that is supplied by
`AlgebraicGeometry.Stack.hasSheafifyAddCommGrpCat_associatedTopology`, which holds because the
site is essentially small in `u`.  This is the same size hypothesis under which the
invertible-module clause of Stacks 0GR7 is stated in
`StacksFrontier.AlgebraicGeometry.Stacks.InvertibleCoherent`.  Coherence of a kernel needs none of
it and is proved at an arbitrary module universe by
`Stacks.SheafOfModules.isCoherentOnSite_kernel`; it is stated here at `u` only so that it can
feed the abelian structure.

**The abelian structure is not registered as an instance.**  It is the structure a full
subcategory of an abelian category closed under kernels, cokernels and finite products carries,
and is exhibited as the inhabitant of a `Nonempty` so that no choice principle enters a
statement.  Closure under finite products is not an independent input: a binary coproduct in an
additive category is a biproduct, hence an extension of one summand by the other, and the
extension clause is Stacks 0GRA at
`AlgebraicGeometry.Stack.isCoherentOnSite_X₂_of_shortExact`.

## References

* [Stacks Project, Tag 0GR9](https://stacks.math.columbia.edu/tag/0GR9)
* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
* [Stacks Project, Tag 0GRA](https://stacks.math.columbia.edu/tag/0GRA)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 07UC](https://stacks.math.columbia.edu/tag/07UC)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
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
conditions (1) and (2) of Stacks 0GR5; the two predicates are compared nowhere in this library,
so this one carries no tag. -/
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

/-- **Stacks 0GR9, part (1).**  Let `𝒳` be a locally Noetherian algebraic stack and
`φ : ℱ ⟶ 𝒢` a map of coherent `𝒪_𝒳`-modules.  The cokernel of `φ` computed in `Mod(𝒪_𝒳)` is
coherent.

Coherence is the sectionwise condition of Stacks 03DL(8) on the big fppf ringed site of `𝒳`, and
the content is Stacks 01BY (3) there: the cokernel projection is locally surjective and the
image of `φ` is of finite type, which bounds both the generators and the relations of the
quotient.  Local Noetherianity is the hypothesis of the source and is not used. -/
@[stacks 0GR9 "part (1), the cokernel, with coherence read as the sectionwise condition of \
  Stacks 03DL(8) rather than as Stacks 0GR6, whose four conditions this library does not \
  identify"]
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
/-- **Stacks 0GR9, part (3).**  Let `𝒳` be a locally Noetherian algebraic stack and
`φ : ℱ ⟶ 𝒢` a map of coherent `𝒪_𝒳`-modules.  The kernel of `φ` computed in `Mod(𝒪_𝒳)` is
coherent, hence is already the kernel of `φ` inside the coherent modules.

Coherence is the sectionwise condition of Stacks 03DL(8) on the big fppf ringed site of `𝒳`, and
the content is Stacks 01BY (3) there: the kernel is of finite type by Stacks 01BY (2) and is a
subsheaf of the coherent source, so Stacks 01BY (1) applies.  The source states the clause for
coherence in the sense of Stacks 0GR6, where the kernel may fail to be coherent and the
coherator of Stacks 0778 is needed; see the module documentation.  Local Noetherianity is the
hypothesis of the source and is not used. -/
@[stacks 0GR9 "part (3), the kernel, with coherence read as the sectionwise condition of \
  Stacks 03DL(8): under that reading Ker(φ) is itself coherent and is the kernel inside the \
  coherent modules, so the coherator Q of the source's formulation is not needed — the \
  source's own clause for Stacks 0GR6-coherence, that Ker(φ) lies in LQCoh^fbc and that \
  Q(Ker(φ)) is coherent, is not proved here"]
theorem isCoherentOnSite_kernel
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    {F G : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)}
    (hF : SheafOfModules.IsCoherentOnSite F) (hG : SheafOfModules.IsCoherentOnSite G)
    (φ : F ⟶ G) :
    SheafOfModules.IsCoherentOnSite (kernel φ) :=
  _root_.Stacks.SheafOfModules.isCoherentOnSite_kernel hF hG φ

/-- **Stacks 0GR9, part (2).**  Let `𝒳` be a locally Noetherian algebraic stack and
`φ : ℱ ⟶ 𝒢` a map of coherent `𝒪_𝒳`-modules.  The image of `φ` computed in `Mod(𝒪_𝒳)` is
coherent.

The abelian image is the kernel of the projection onto the cokernel, so this is the kernel
clause applied to `𝒢 ⟶ Coker(φ)`, whose target is coherent by the cokernel clause.  Local
Noetherianity is the hypothesis of the source and is not used. -/
@[stacks 0GR9 "part (2), the image, with coherence read as the sectionwise condition of \
  Stacks 03DL(8) rather than as Stacks 0GR6, whose four conditions this library does not \
  identify"]
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

/-- **Stacks 0GR9, part (2), for the categorical image.**  The image of a map of coherent
`𝒪_𝒳`-modules formed as `CategoryTheory.Limits.image` is coherent, being isomorphic to the
abelian image. -/
@[stacks 0GR9 "part (2) for the categorical image, with coherence read as the sectionwise \
  condition of Stacks 03DL(8) rather than as Stacks 0GR6", sga "6 I 3.4" "special case"]
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
/-- The coherent `𝒪_𝒳`-modules are closed under kernels; this is Stacks 0GR9 part (3) as a
closure property. -/
theorem coherentOnSiteModules_isClosedUnderKernels
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳) :
    (coherentOnSiteModules.{u, t} B S hS 𝒳).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact _root_.Stacks.SheafOfModules.isCoherentOnSite_of_iso
      (IsLimit.conePointUniqueUpToIso (kernelIsKernel φ) hk)
      (isCoherentOnSite_kernel B S hS 𝒳 h𝒳 hF hG φ)

/-- The coherent `𝒪_𝒳`-modules are closed under cokernels; this is Stacks 0GR9 part (1) as a
closure property. -/
theorem coherentOnSiteModules_isClosedUnderCokernels
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳) :
    (coherentOnSiteModules.{u, t} B S hS 𝒳).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨φ, k, hk, hF, hG⟩
    exact _root_.Stacks.SheafOfModules.isCoherentOnSite_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel φ) hk)
      (isCoherentOnSite_cokernel B S hS 𝒳 h𝒳 hF hG φ)

/-- The coherent `𝒪_𝒳`-modules are closed under extensions; this is Stacks 0GRA, through
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

/-- **Stacks 0GR9, the abelian-category clause.**  The category of coherent `𝒪_𝒳`-modules on a
locally Noetherian algebraic stack is abelian.

The structure is the one a full subcategory of an abelian category closed under kernels,
cokernels and finite products carries; the kernel and cokernel closure are parts (3) and (1)
above and the product closure comes from the extension clause Stacks 0GRA.  Coherence is the
sectionwise condition of Stacks 03DL(8); local Noetherianity is the hypothesis of the source and
is not used. -/
@[stacks 0GR9 "the abelian-category clause, with coherence read as the sectionwise condition of \
  Stacks 03DL(8) rather than as Stacks 0GR6, whose four conditions this library does not \
  identify"]
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
