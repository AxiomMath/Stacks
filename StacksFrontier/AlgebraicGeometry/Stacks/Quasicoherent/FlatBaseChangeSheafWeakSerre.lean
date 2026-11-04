module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSchemeFlatPullbackExact
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeSheafColimits

/-!
# The flat base change property is a weak Serre condition on étale sheaves (Stacks 0764 (2))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. **Stacks 0764** part (2) says
that the étale sheaves of `𝒪_𝒳`-modules with the flat base change property of **Stacks 0762**
form a weak Serre subcategory of `Mod(𝒳_étale, 𝒪_𝒳)`. By **Stacks 0754** that asks for a strictly
full subcategory containing a zero object and closed under kernels, cokernels and extensions.

`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeSheafColimits.lean` proves, for
the source's reading of the property
(`AlgebraicGeometry.Stack.HasFlatBaseChangePropertySheafUnivLE`, with `a_{small}^*` the inverse
image of sheaves of modules), strict fullness, the zero object, the cokernels and the extensions.
This file supplies the missing clause, **kernels**, and assembles the whole of part (2).

The kernel clause is the source's argument. For an arrow `φ : x ⟶ y` of `𝒳` over a flat
morphism of schemes `a : U ⟶ V`, the comparison `c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` is the
component of a natural transformation between two functors of `F`. Both are left exact: the
restrictions to the small étale sites are, by
`AlgebraicGeometry.Stack.preservesFiniteLimits_restrictSheafToSmallEtale`, and `a_{small}^*` is
left exact because `a` is flat — this is the input the source reads off flatness, and it is
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_pullback_smallEtaleStructureMapRing`, carried
to the spelling of the comparison by `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso`.
A natural transformation of left exact functors which is an isomorphism at the source and the
target of a morphism is an isomorphism at its kernel, `CategoryTheory.NatTrans.isIso_app_limit`.

## Main results

* `AlgebraicGeometry.Stack.preservesFiniteLimits_sheafifiedPullbackComparison`: the inverse
  image `a_{small}^*` of sheaves of modules below an arrow of `𝒳` lying over a flat morphism of
  schemes is left exact.
* `AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_kernel`: the comparison map
  `c_φ` at the kernel of a morphism is an isomorphism when it is one at the source and the
  target.
* `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_kernel`: the kernel clause of
  **Stacks 0764** part (2), as the source states it.
* `AlgebraicGeometry.Stack.isWeakSerreClass_flatBaseChangeEtaleModules`: **Stacks 0764**,
  part (2), as the source states it — the étale sheaves of `𝒪_𝒳`-modules with the flat base
  change property form a weak Serre subcategory of `Mod(𝒳_étale, 𝒪_𝒳)`.

## Implementation notes

`CategoryTheory.ObjectProperty.IsWeakSerreClass` is stated over an abelian category, and the
abelian structure on the étale sheaves of `𝒪_𝒳`-modules is Mathlib's, which needs étale
sheafification of abelian presheaves on `𝒳`. Those two instances are not hypotheses: they are
supplied, for any `B`, `S` and `p`, by
`AlgebraicGeometry.Stack.hasSheafify_etaleAssociatedTopology` and
`AlgebraicGeometry.Stack.wEqualsLocallyBijective_etaleAssociatedTopology`, and the statement
introduces them, and Mathlib's abelian structure `CategoryTheory.SheafOfModules.instAbelian` built
from them, with `letI` in its type. The abelian structure is named rather than found by instance
search, which otherwise tries the module universe as a metavariable and gets stuck.

## References

* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **`a_{small}^*` is left exact along a flat morphism.** The inverse image of sheaves of
modules below an arrow `φ : x ⟶ y` of `𝒳`, lying over a flat morphism of schemes, preserves
finite limits.

It is the pullback of sheaves of modules along the morphism of small étale ringed sites `ε_a` of
Stacks 070R (2), by `AlgebraicGeometry.Stack.sheafifiedPullbackComparisonIso`, and that pullback
is left exact for a flat `a` by
`AlgebraicGeometry.SmallEtale.preservesFiniteLimits_pullback_smallEtaleStructureMapRing`. -/
@[sga "4 IV 13.7" "special case"]
theorem preservesFiniteLimits_sheafifiedPullbackComparison
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) {x y : 𝒳} (φ : x ⟶ y)
    (hflat : Flat (B.inclusion.map (p.map φ).left)) :
    PreservesFiniteLimits (sheafifiedPullbackComparison B E h S hS p hp τ hτ φ) :=
  have : PreservesFiniteLimits (SheafOfModules.pullback.{u} (SmallEtale.smallEtaleStructureMapRing E
      (smallEtaleBaseMorphism B E h S hS p φ))) :=
    SmallEtale.preservesFiniteLimits_pullback_smallEtaleStructureMapRing E
      (smallEtaleBaseMorphism B E h S hS p φ) hflat
  preservesFiniteLimits_of_natIso (sheafifiedPullbackComparisonIso B E h S hS p hp τ hτ φ).symm

/-- The comparison map `c_φ^{sh}` below an arrow `φ` of `𝒳` lying over a flat morphism of schemes
is an isomorphism at the kernel of a morphism of étale sheaves of modules as soon as it is one at
the source and at the target of the morphism, provided `a_{small}^*` is left exact; at section
universe `u` it is, by
`AlgebraicGeometry.Stack.preservesFiniteLimits_sheafifiedPullbackComparison`.

`c_φ^{sh}` is the component of
`AlgebraicGeometry.Stack.restrictSheafPullbackComparisonNatTrans`, whose source is the restriction
at `y` followed by `a_{small}^*` and whose target is the restriction at `x`; both are left exact,
by `AlgebraicGeometry.Stack.preservesFiniteLimits_restrictSheafToSmallEtale` and
`AlgebraicGeometry.Stack.preservesFiniteLimits_sheafifiedPullbackComparison`, so the kernel, the
limit of the parallel pair of the morphism and zero, is carried to an isomorphism by
`CategoryTheory.NatTrans.isIso_app_limit`. -/
theorem isIso_restrictSheafPullbackComparison_kernel [UnivLE.{u, m}] {x y : 𝒳} (φ : x ⟶ y)
    [PreservesFiniteLimits (sheafifiedPullbackComparisonUnivLE.{u, v, w, m} B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) φ)]
    {F G : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} (α : F ⟶ G)
    (hF : IsIso (restrictSheafPullbackComparison B E h S hS p hp φ F))
    (hG : IsIso (restrictSheafPullbackComparison B E h S hS p hp φ G)) :
    IsIso (restrictSheafPullbackComparison B E h S hS p hp φ (kernel α)) := by
  have : PreservesFiniteLimits (restrictSheafToSmallEtale.{u, v, w, m} B E h S hS p hp y ⋙
      sheafifiedPullbackComparisonUnivLE.{u, v, w, m} B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) φ) :=
    comp_preservesFiniteLimits _ _
  exact NatTrans.isIso_app_limit (restrictSheafPullbackComparisonNatTrans B E h S hS p hp φ)
    (parallelPair α 0) (by rintro (_ | _) <;> assumption)

/-- **Stacks 0764, part (2), as the source states it, the kernel clause.** The kernel of a
morphism of étale sheaves of `𝒪_𝒳`-modules with the flat base change property of
**Stacks 0762** has the flat base change property. This is the closure under kernels asked for
by **Stacks 0754**, with the kernel the kernel of `Mod(𝒳_étale, 𝒪_𝒳)`.

At each arrow lying over a flat morphism of schemes this is
`AlgebraicGeometry.Stack.isIso_restrictSheafPullbackComparison_kernel`. -/
theorem hasFlatBaseChangePropertySheaf_kernel [UnivLE.{u, m}]
    (hlex : ∀ {x y : 𝒳} (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
      PreservesFiniteLimits (sheafifiedPullbackComparisonUnivLE.{u, v, w, m} B E h S hS p hp
        (etaleTopology B) (etaleTopology_le_topology B) φ))
    {F G : SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))} (α : F ⟶ G)
    (hF : HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp F)
    (hG : HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp G) :
    HasFlatBaseChangePropertySheafUnivLE B E h S hS p hp (kernel α) := fun φ hflat =>
  have := hlex φ hflat
  isIso_restrictSheafPullbackComparison_kernel B E h S hS p hp φ α (hF φ hflat) (hG φ hflat)

/-- **The étale sheaves of modules with the flat base change property form a weak Serre
subcategory, at any section universe at which `a_{small}^*` is left exact along flat morphisms.**
This is the argument of **Stacks 0764**, part (2), at section universe `m`, in the form
**Stacks 0754** gives: a strictly full subcategory containing a zero object and closed under
kernels, cokernels and extensions. Only the kernel clause uses the left exactness `hlex`, which
at section universe `u` is
`AlgebraicGeometry.Stack.preservesFiniteLimits_sheafifiedPullbackComparison`. -/
theorem isWeakSerreClass_flatBaseChangeEtaleModules_of_preservesFiniteLimits [UnivLE.{u, m}]
    [HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{m}]
    [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{m}]
    (hlex : ∀ {x y : 𝒳} (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
      PreservesFiniteLimits (sheafifiedPullbackComparisonUnivLE.{u, v, w, m} B E h S hS p hp
        (etaleTopology B) (etaleTopology_le_topology B) φ)) :
    letI : Abelian (SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :=
      SheafOfModules.instAbelian (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B))
    (flatBaseChangeEtaleModules.{u, v, w, m} B E h S hS p hp).IsWeakSerreClass := by
  let : Abelian (SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :=
    SheafOfModules.instAbelian (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))
  have : (flatBaseChangeEtaleModules.{u, v, w, m} B E h S hS p hp).ContainsZero := by
    obtain ⟨Z, hZ⟩ := (inferInstance :
      HasZeroObject (SheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)))).zero
    exact ⟨⟨Z, hZ, hasFlatBaseChangePropertySheaf_initial B E h S hS p hp hZ.isInitial⟩⟩
  have : ObjectProperty.IsClosedUnderKernels
      (flatBaseChangeEtaleModules.{u, v, w, m} B E h S hS p hp) := by
    constructor
    rintro K ⟨f, k, hk, hF, hG⟩
    exact hasFlatBaseChangePropertySheafUnivLE_of_iso B E h S hS p hp
      (IsLimit.conePointUniqueUpToIso hk (kernelIsKernel f)).symm
      (hasFlatBaseChangePropertySheaf_kernel B E h S hS p hp hlex f hF hG)
  have : ObjectProperty.IsClosedUnderCokernels
      (flatBaseChangeEtaleModules.{u, v, w, m} B E h S hS p hp) := by
    constructor
    rintro Q ⟨f, k, hk, hF, hG⟩
    exact hasFlatBaseChangePropertySheafUnivLE_of_iso B E h S hS p hp
      (IsColimit.coconePointUniqueUpToIso hk (cokernelIsCokernel f)).symm
      (hasFlatBaseChangePropertySheaf_cokernel B E h S hS p hp f hF hG)
  have : ObjectProperty.IsClosedUnderExtensions
      (flatBaseChangeEtaleModules.{u, v, w, m} B E h S hS p hp) :=
    ⟨fun hT h₁ h₃ => hasFlatBaseChangePropertySheaf_of_shortExact B E h S hS p hp hT h₁ h₃⟩
  exact {}

/-- **Stacks 0764, part (2), as the source states it.** The étale sheaves of `𝒪_𝒳`-modules with
the flat base change property of **Stacks 0762** form a weak Serre subcategory of
`Mod(𝒳_étale, 𝒪_𝒳)`, in the form **Stacks 0754** gives: a strictly full subcategory containing a
zero object and closed under kernels, cokernels and extensions.

Strict fullness is
`AlgebraicGeometry.Stack.isClosedUnderIsomorphisms_flatBaseChangeEtaleModules`, the zero object
is `AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_initial`, the cokernels are
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_cokernel`, the extensions are
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_of_shortExact`, and the kernels are
`AlgebraicGeometry.Stack.hasFlatBaseChangePropertySheaf_kernel`, the last with the left exactness
`AlgebraicGeometry.Stack.preservesFiniteLimits_sheafifiedPullbackComparison`: this is
`AlgebraicGeometry.Stack.isWeakSerreClass_flatBaseChangeEtaleModules_of_preservesFiniteLimits`
at section universe `u`.

The abelian structure on `Mod(𝒳_étale, 𝒪_𝒳)` is the one coming from étale sheafification of
abelian presheaves on `𝒳`, whose two instances are supplied in the statement by
`AlgebraicGeometry.Stack.hasSheafify_etaleAssociatedTopology` and
`AlgebraicGeometry.Stack.wEqualsLocallyBijective_etaleAssociatedTopology`; they are not
hypotheses. -/
@[stacks 0764 "part (2): the étale sheaves of O_X-modules with the flat base change property \
  form a weak Serre subcategory of Mod(X_etale, O_X), in the form of Stacks 0754 -- strictly \
  full, with a zero object, and closed under kernels, cokernels and extensions. The whole of \
  part (2), in the source's ambient category, with a_small^* the inverse image of sheaves of \
  modules, and with no hypothesis beyond the source's"]
theorem isWeakSerreClass_flatBaseChangeEtaleModules :
    letI := hasSheafify_etaleAssociatedTopology B S hS p hp
    letI := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
    letI : Abelian (SheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B))) :=
      SheafOfModules.instAbelian (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B))
    (flatBaseChangeEtaleModules.{u, v, w} B E h S hS p hp).IsWeakSerreClass := by
  let := hasSheafify_etaleAssociatedTopology B S hS p hp
  let := wEqualsLocallyBijective_etaleAssociatedTopology B S hS p hp
  exact isWeakSerreClass_flatBaseChangeEtaleModules_of_preservesFiniteLimits B E h S hS p hp
    fun φ hflat => preservesFiniteLimits_sheafifiedPullbackComparison B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) φ hflat

end AlgebraicGeometry.Stack

end
