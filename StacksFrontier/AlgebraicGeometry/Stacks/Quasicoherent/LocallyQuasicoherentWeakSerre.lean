module

public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExactCocontinuous
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeExtensions
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentTensor
public import
  StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentWeakSerre

/-!
# Locally quasi-coherent modules form a weak Serre subcategory (Stacks 06WM, parts (2) and (3))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. **Stacks 06WJ** calls a sheaf of
`𝒪_𝒳`-modules on the associated étale site *locally quasi-coherent* when its restriction to the
small étale site of the scheme below every object of `𝒳` is quasi-coherent there. Part (2) of
**Stacks 06WM** says that the resulting category `LQCoh(𝒪_𝒳)` is abelian with kernels and
cokernels computed in `Mod(𝒳_ét, 𝒪_𝒳)` — equivalently that the inclusion is exact — and part (3)
that in a short exact sequence of `Mod(𝒳_ét, 𝒪_𝒳)` whose two of three terms are locally
quasi-coherent, so is the third. Both are proved here.

The argument is the source's, in two halves.

*Restriction to a small étale site is exact.* The restriction functor of **Stacks 06W1** is
continuous *and* cocontinuous for the small étale topology and the associated étale topology
(`AlgebraicGeometry.Stack.isContinuous_and_isCocontinuous_restrictToSmallEtale`), so it is the
direct image along a morphism of ringed sites whose underlying functor is cocontinuous. Such a
direct image is exact: left exactness because it is a right adjoint, right exactness because a
cocontinuous functor is almost cocontinuous and the direct image then preserves epimorphisms.
That is **Stacks 04BD** part (2), proved as
`SheafOfModules.exactFunctor_pushforward_of_isCocontinuous`; the two halves are read off here as
`AlgebraicGeometry.Stack.preservesFiniteLimits_restrictModuleToSmallEtaleSheafFunctor` and
`AlgebraicGeometry.Stack.preservesFiniteColimits_restrictModuleToSmallEtaleSheafFunctor`.

*Quasi-coherence on the small étale site of a scheme is a weak Serre class.* Its closure under
kernels, under cokernels and under extensions are
`AlgebraicGeometry.SmallEtale.isClosedUnderKernels_isQuasicoherentOnSite`,
`AlgebraicGeometry.SmallEtale.isClosedUnderCokernels_isQuasicoherentOnSite` and
`AlgebraicGeometry.SmallEtale.isClosedUnderExtensions_isQuasicoherentOnSite`.

Local quasi-coherence is the conjunction, over the objects of `𝒳`, of quasi-coherence of the
restrictions, so an exact functor carrying each clause to its scheme-level counterpart turns the
three scheme-level closure properties into the three closure properties of `LQCoh(𝒪_𝒳)`, and
`CategoryTheory.ObjectProperty.IsWeakSerreClass` collects them. Parts (2) and (3) are then the
"moreover" of **Stacks 0754** and **Stacks 02MO** (2) respectively.

## Main definitions

* `AlgebraicGeometry.Stack.smallEtaleStructureRestrictionHom`: the comparison of structure
  sheaves below it, which makes it a morphism of ringed sites.
* `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleSheafFunctor`: restriction to the small
  étale site of the scheme below an object, as a functor on *sheaves* of modules.
* `AlgebraicGeometry.Stack.locallyQuasicoherent`: local quasi-coherence as an object property of
  the sheaves of `𝒪_𝒳`-modules on the associated étale site, the property whose full subcategory
  is `AlgebraicGeometry.Stack.locallyQuasicoherentModules`.

## Main results

* `AlgebraicGeometry.Stack.preservesFiniteLimits_restrictModuleToSmallEtaleSheafFunctor` and
  `AlgebraicGeometry.Stack.preservesFiniteColimits_restrictModuleToSmallEtaleSheafFunctor`:
  restriction to a small étale site is exact on sheaves of modules.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_iff_restrictModule`: a sheaf of modules is
  locally quasi-coherent exactly when each of its restrictions is quasi-coherent on its small étale
  site.
* `AlgebraicGeometry.Stack.isClosedUnderKernels_locallyQuasicoherent`,
  `AlgebraicGeometry.Stack.isClosedUnderCokernels_locallyQuasicoherent` and
  `AlgebraicGeometry.Stack.isClosedUnderExtensions_locallyQuasicoherent`: the three closure
  clauses, and `AlgebraicGeometry.Stack.isWeakSerreClass_locallyQuasicoherent` their collection.
* `AlgebraicGeometry.Stack.abelian_and_exact_ι_locallyQuasicoherentModules`:
  **Stacks 06WM part (2)**.
* `AlgebraicGeometry.Stack.isLocallyQuasicoherent_two_out_of_three`:
  **Stacks 06WM part (3)**.

## Implementation notes

The restriction functor on sheaves of modules is `SheafOfModules.pushforward` along the
morphism of ringed sites assembled here, so every statement about it is read off the generic
statements about that direct image rather than proved again. Its action on the underlying
presheaf is the restriction of **Stacks 06WJ** on the nose, which is
`AlgebraicGeometry.Stack.restrictModuleToSmallEtaleSheafFunctor_obj_val`.

Each of the three pieces — the functor of sites, the comparison of structure sheaves, the
functor on sheaves of modules — is given a name of its own and the generic statements are
applied to the named terms. That is not cosmetic: `AlgebraicGeometry.Stack.structureSheaf` and
its ring form `AlgebraicGeometry.Stack.ringStructureSheafCore` are built by tactic blocks, so
leaving the identification of a spelling to unification makes `whnf` unfold a tactic-generated
term and costs several times the default heartbeat budget, as the implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/LocallyQuasicoherentTensor.lean` record.

The statements in the `WeakSerre` section carry two instance hypotheses on the associated étale
site, `CategoryTheory.HasSheafify` and
`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` for abelian groups. They are not
hypotheses of the source: they are what makes `Mod(𝒳_ét, 𝒪_𝒳)` abelian at all, so that there are
cokernels to speak of, and they are conditions on the ambient site rather than on the modules.
On an essentially small fibred category both hold with no hypothesis, by
`AlgebraicGeometry.FibredSite.hasWeakSheafify_associatedTopology` and its companion, and
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_tensorSheaf` — part (4) of the same tag — carries
them for the same reason. On the small étale site of a scheme, which is always essentially small,
the corresponding instances are `AlgebraicGeometry.smallEtale_hasSheafify` and
`AlgebraicGeometry.smallEtale_wEqualsLocallyBijective` and are found by instance search.

The module sections live in the universe `u` of the schemes, which is the universe at which the
closure properties of quasi-coherence on the small étale site of a scheme are stated.

Part (1) of **Stacks 06WM**, the colimits, is not here: its formal half is
`AlgebraicGeometry.Stack.hasColimits_locallyQuasicoherentModules` and the closure of local
quasi-coherence under colimits of arbitrary shape that it consumes asks for arbitrary direct
sums of quasi-coherent modules on the small étale site, clause (1) of **Stacks 0GNB**, which the
library has in the finite case. Part (4), the tensor products, is
`AlgebraicGeometry.Stack.isLocallyQuasicoherent_tensorSheaf`. Part (5), the internal homs, asks
for the internal-hom clause of **Stacks 0GNB** on the small étale site.

## References

* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 04BD](https://stacks.math.columbia.edu/tag/04BD)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- The restriction functor of **Stacks 06W1** is continuous. -/
theorem isContinuous_smallEtaleRestrictionSiteFunctor (x : 𝒳) :
    (smallEtaleRestrictionSiteFunctor B E h S hS p hp x).IsContinuous
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      (associatedTopology B S hS p (etaleTopology B)) :=
  (isContinuous_and_isCocontinuous_restrictToSmallEtale B E h S hS p hp x).1

/-- The restriction functor of **Stacks 06W1** is cocontinuous. -/
theorem isCocontinuous_smallEtaleRestrictionSiteFunctor (x : 𝒳) :
    (smallEtaleRestrictionSiteFunctor B E h S hS p hp x).IsCocontinuous
      (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      (associatedTopology B S hS p (etaleTopology B)) :=
  (isContinuous_and_isCocontinuous_restrictToSmallEtale B E h S hS p hp x).2

/-- The comparison of structure sheaves below the restriction functor. -/
def smallEtaleStructureRestrictionHom (x : 𝒳) :
    letI := isContinuous_smallEtaleRestrictionSiteFunctor B E h S hS p hp x
    SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x) ⟶
      ((smallEtaleRestrictionSiteFunctor B E h S hS p hp x).sheafPushforwardContinuous
          RingCat.{u} (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
          (associatedTopology B S hS p (etaleTopology B))).obj
        (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)) :=
  letI := isContinuous_smallEtaleRestrictionSiteFunctor B E h S hS p hp x
  ⟨(localStructurePresheafIso B E h S hS p hp x (etaleTopology B)
    (etaleTopology_le_topology B)).hom⟩

/-- Restriction to the small étale site as a functor on sheaves of modules. -/
def restrictModuleToSmallEtaleSheafFunctor (x : 𝒳) :
    SheafOfModules.{u}
        (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)) ⥤
      SheafOfModules.{u}
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)) :=
  letI := isContinuous_smallEtaleRestrictionSiteFunctor B E h S hS p hp x
  SheafOfModules.pushforward.{u} (smallEtaleStructureRestrictionHom B E h S hS p hp x)

/-- The underlying presheaf of the restriction is the restriction of Stacks 06WJ. -/
theorem restrictModuleToSmallEtaleSheafFunctor_obj_val (x : 𝒳)
    (M : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x).obj M).val =
      restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) M.val :=
  rfl

/-- Restriction to the small étale site is an additive functor. -/
instance additive_restrictModuleToSmallEtaleSheafFunctor (x : 𝒳) :
    (restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x).Additive :=
  letI := isContinuous_smallEtaleRestrictionSiteFunctor B E h S hS p hp x
  Stacks.SheafOfModules.PushforwardRightExact.additive_pushforward
    (smallEtaleRestrictionSiteFunctor B E h S hS p hp x)
    (smallEtaleStructureRestrictionHom B E h S hS p hp x)

/-- Restriction to the small étale site is left exact. -/
theorem preservesFiniteLimits_restrictModuleToSmallEtaleSheafFunctor (x : 𝒳) :
    PreservesFiniteLimits (restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x) :=
  let := isContinuous_smallEtaleRestrictionSiteFunctor B E h S hS p hp x
  SheafOfModules.preservesFiniteLimits_pushforward.{u}
    (smallEtaleStructureRestrictionHom B E h S hS p hp x)

open Stacks.SheafOfModules.PushforwardRightExact in
/-- Restriction to the small étale site is right exact. -/
theorem preservesFiniteColimits_restrictModuleToSmallEtaleSheafFunctor
    [HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
    [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (x : 𝒳) :
    PreservesFiniteColimits (restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x) :=
  let := isContinuous_smallEtaleRestrictionSiteFunctor B E h S hS p hp x
  let := isCocontinuous_smallEtaleRestrictionSiteFunctor B E h S hS p hp x
  preservesFiniteColimits_pushforward_of_isAlmostCocontinuous
    (smallEtaleRestrictionSiteFunctor B E h S hS p hp x)
    (smallEtaleStructureRestrictionHom B E h S hS p hp x)
    (isAlmostCocontinuous_of_isCocontinuous _ _ _)

/-! ### `LQCoh(𝒪_𝒳)` through the restriction functor -/

/-- Local quasi-coherence of a *sheaf* of modules on the associated étale site, read through the
restriction functor on sheaves of modules: a sheaf of modules is locally quasi-coherent exactly
when each of its restrictions to a small étale site is quasi-coherent there.

The étale sheaf condition, the first clause of
`AlgebraicGeometry.Stack.IsLocallyQuasicoherent`, is part of being a sheaf of modules, and the
sheaf condition on each restriction is supplied by continuity of the restriction functor. -/
theorem isLocallyQuasicoherent_iff_restrictModule
    (M : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :
    IsLocallyQuasicoherent B E h S hS p hp M.val ↔
      ∀ x : 𝒳,
        ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x).obj M).IsQuasicoherentOnSite :=
  ⟨fun hM x => (hM.2 x).choose_spec,
    fun hM => ⟨M.isSheaf, fun x =>
      ⟨((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x).obj M).isSheaf, hM x⟩⟩⟩

/-- `LQCoh(𝒪_𝒳)`, the local quasi-coherence of **Stacks 06WJ**, as an object property of the
sheaves of `𝒪_𝒳`-modules on the associated étale site.  Its full subcategory is
`AlgebraicGeometry.Stack.locallyQuasicoherentModules`. -/
abbrev locallyQuasicoherent :
    ObjectProperty (SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))) :=
  fun M => IsLocallyQuasicoherent B E h S hS p hp M.val

/-- Local quasi-coherence is closed under isomorphism: an isomorphism of sheaves of modules
restricts to an isomorphism on every small étale site, and quasi-coherence there is closed
under isomorphism. -/
instance isClosedUnderIsomorphisms_locallyQuasicoherent :
    (locallyQuasicoherent B E h S hS p hp).IsClosedUnderIsomorphisms where
  of_iso {M N} e hM :=
    (isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp N).2 fun x =>
      SheafOfModules.IsQuasicoherentOnSite.of_iso
        ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x).mapIso e)
        ((isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp M).1 hM x)

/-- A zero sheaf of modules is locally quasi-coherent: the restriction functor is additive, so
each restriction is a zero module, and a zero module is quasi-coherent. -/
theorem isLocallyQuasicoherent_of_isZero
    {M : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))}
    (hM : IsZero M) : IsLocallyQuasicoherent B E h S hS p hp M.val :=
  (isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp M).2 fun x =>
    SheafOfModules.IsQuasicoherentOnSite.of_isZero
      ((restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x).map_isZero hM)

/-- The category `LQCoh(𝒪_𝒳)` of **Stacks 06WJ** is the full subcategory cut out by the object
property `AlgebraicGeometry.Stack.locallyQuasicoherent`. -/
theorem locallyQuasicoherentModules_eq :
    locallyQuasicoherentModules.{u, v, w, u} B E h S hS p hp =
      (locallyQuasicoherent B E h S hS p hp).FullSubcategory :=
  rfl

section WeakSerre

variable [HasSheafify (associatedTopology B S hS p (etaleTopology B)) AddCommGrpCat.{u}]
  [(associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- `LQCoh(𝒪_𝒳)` contains a zero object. -/
instance containsZero_locallyQuasicoherent :
    (locallyQuasicoherent B E h S hS p hp).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)))
    exact ⟨Z, hZ, isLocallyQuasicoherent_of_isZero B E h S hS p hp hZ⟩

/-- **The kernel clause of Stacks 06WM part (2).**  The kernel, formed in
`Mod(𝒳_ét, 𝒪_𝒳)`, of a morphism of locally quasi-coherent sheaves of modules is locally
quasi-coherent.

Restriction to a small étale site is left exact, so it carries the kernel to the kernel of the
restricted morphism, and quasi-coherence on the small étale site of a scheme is closed under
kernels. -/
instance isClosedUnderKernels_locallyQuasicoherent :
    (locallyQuasicoherent B E h S hS p hp).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    refine (isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp _).2 fun x => ?_
    have := preservesFiniteLimits_restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x
    exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_of_isLimit_kernelFork
      (k.mapIsLimit hk (restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x))
      ((isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp _).1 hM x)
      ((isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp _).1 hN x)

/-- **The cokernel clause of Stacks 06WM part (2).**  The cokernel, formed in
`Mod(𝒳_ét, 𝒪_𝒳)`, of a morphism of locally quasi-coherent sheaves of modules is locally
quasi-coherent.

Restriction to a small étale site is right exact — the restriction functor of **Stacks 06W1**
is cocontinuous, so it commutes with étale sheafification — and quasi-coherence on the small
étale site of a scheme is closed under cokernels. -/
instance isClosedUnderCokernels_locallyQuasicoherent :
    (locallyQuasicoherent B E h S hS p hp).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, hM, hN⟩
    refine (isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp _).2 fun x => ?_
    have := preservesFiniteColimits_restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x
    exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _)
      |>.prop_of_isColimit_cokernelCofork
      (k.mapIsColimit hk (restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x))
      ((isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp _).1 hM x)
      ((isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp _).1 hN x)

/-- **The extension clause of Stacks 06WM part (2).**  The middle term of a short exact sequence
of `Mod(𝒳_ét, 𝒪_𝒳)` whose outer terms are locally quasi-coherent is locally quasi-coherent.

Restriction to a small étale site is exact, so it carries the short exact sequence to a short
exact sequence there, and quasi-coherence on the small étale site of a scheme is closed under
extensions. -/
instance isClosedUnderExtensions_locallyQuasicoherent :
    (locallyQuasicoherent B E h S hS p hp).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {T} hT h₁ h₃ := by
    refine (isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp _).2 fun x => ?_
    have := preservesFiniteLimits_restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x
    have := preservesFiniteColimits_restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x
    have := hT.mono_f
    have := hT.epi_g
    exact (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u} _).prop_X₂_of_shortExact
      (hT.map (restrictModuleToSmallEtaleSheafFunctor B E h S hS p hp x))
      ((isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp _).1 h₁ x)
      ((isLocallyQuasicoherent_iff_restrictModule B E h S hS p hp _).1 h₃ x)

/-- **Stacks 06WM part (2), as a weak Serre class.**  Local quasi-coherence is a weak Serre
class in the sense of **Stacks 0754** inside `Mod(𝒳_ét, 𝒪_𝒳)`. -/
instance isWeakSerreClass_locallyQuasicoherent :
    (locallyQuasicoherent B E h S hS p hp).IsWeakSerreClass where

/-! ### Stacks 06WM, parts (2) and (3) -/

/-- `LQCoh(𝒪_𝒳)` is abelian with exact inclusion.  The category `LQCoh(𝒪_𝒳)` of locally
quasi-coherent sheaves of modules is abelian, and its inclusion into `Mod(𝒳_ét, 𝒪_𝒳)` is exact;
equivalently, kernels and cokernels in `LQCoh(𝒪_𝒳)` are the ones computed in `Mod(𝒳_ét, 𝒪_𝒳)`.

Local quasi-coherence is a weak Serre class — it contains a zero object, is closed under
isomorphism, under kernels, under cokernels and under extensions — and a weak Serre class is
abelian with exact inclusion by the "moreover" of **Stacks 0754**. -/
theorem abelian_and_exact_ι_locallyQuasicoherentModules :
    Nonempty (Abelian (locallyQuasicoherentModules.{u, v, w, u} B E h S hS p hp)) ∧
      PreservesFiniteLimits (locallyQuasicoherent B E h S hS p hp).ι ∧
      PreservesFiniteColimits (locallyQuasicoherent B E h S hS p hp).ι :=
  ⟨(locallyQuasicoherent B E h S hS p hp).abelian_of_isWeakSerreClass,
    (locallyQuasicoherent B E h S hS p hp).preservesFiniteLimits_ι_of_isWeakSerreClass,
    (locallyQuasicoherent B E h S hS p hp).preservesFiniteColimits_ι_of_isWeakSerreClass⟩

/-- Two out of three for local quasi-coherence. Given a short exact sequence `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0`
of `Mod(𝒳_ét, 𝒪_𝒳)`, if two of the three terms are locally quasi-coherent then so is the third.

The three cases are the three closure properties of the weak Serre class: `ℱ₃` is the cokernel
of `ℱ₁ ⟶ ℱ₂`, `ℱ₁` is the kernel of `ℱ₂ ⟶ ℱ₃`, and `ℱ₂` is an extension of `ℱ₃` by `ℱ₁`. -/
theorem isLocallyQuasicoherent_two_out_of_three
    (T : ShortComplex (SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B))))
    (hT : T.ShortExact) :
    (locallyQuasicoherent B E h S hS p hp T.X₁ → locallyQuasicoherent B E h S hS p hp T.X₂ →
        locallyQuasicoherent B E h S hS p hp T.X₃) ∧
      (locallyQuasicoherent B E h S hS p hp T.X₁ → locallyQuasicoherent B E h S hS p hp T.X₃ →
        locallyQuasicoherent B E h S hS p hp T.X₂) ∧
      (locallyQuasicoherent B E h S hS p hp T.X₂ → locallyQuasicoherent B E h S hS p hp T.X₃ →
        locallyQuasicoherent B E h S hS p hp T.X₁) :=
  ⟨fun h₁ h₂ => (locallyQuasicoherent B E h S hS p hp).prop_of_isColimit_cokernelCofork
      hT.gIsCokernel h₁ h₂,
    fun h₁ h₃ => (locallyQuasicoherent B E h S hS p hp).prop_X₂_of_shortExact hT h₁ h₃,
    fun h₂ h₃ => (locallyQuasicoherent B E h S hS p hp).prop_of_isLimit_kernelFork
      hT.fIsKernel h₂ h₃⟩

end WeakSerre

end AlgebraicGeometry.Stack

end
