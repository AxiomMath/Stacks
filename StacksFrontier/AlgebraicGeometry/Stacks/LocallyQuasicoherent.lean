module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalizationPullback
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalizationStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf

/-!
# Locally quasi-coherent modules on a fibred category (Stacks 06WJ)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `F` be a presheaf of
`O_𝒳`-modules. Following Stacks 06WJ, `F` is *locally quasi-coherent* when it is a sheaf for
the étale topology and, for every object `x` of `𝒳` lying over a scheme `U`, the restriction
`x^*F|_{U_étale}` is a quasi-coherent sheaf on the small étale site of `U`.

The restriction is the localization of Stacks 06W1 followed by a change of scalars: the
localized module is a module over the pullback of the structure presheaf of `𝒳`, and
`localStructurePresheafIso` identifies that pullback with the small étale structure sheaf of
Stacks 03DU. Quasi-coherence is then the local-presentation predicate of Stacks 03DL(6).

The restriction itself, `AlgebraicGeometry.Stack.restrictModuleToSmallEtale`, the scalar
identification `AlgebraicGeometry.Stack.localStructurePresheafIso` it is built from, and the
predicate `AlgebraicGeometry.Stack.IsLocallyQuasicoherent` are in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherent`, which this module
imports.

## Main definitions

* `AlgebraicGeometry.Stack.locallyQuasicoherentModules` is the category `LQCoh(O_𝒳)` of locally
  quasi-coherent modules, the full subcategory cut out by that predicate.

## Main results

* `AlgebraicGeometry.Stack.hasColimits_locallyQuasicoherentModules`: `LQCoh(O_𝒳)` has colimits,
  given that local quasi-coherence is closed under them.
* `AlgebraicGeometry.Stack.preservesColimits_locallyQuasicoherentInclusion`: and the inclusion of
  `LQCoh(O_𝒳)` into all étale sheaves of modules preserves them, under the same hypothesis.

## Implementation notes

The localization functor is the composite of the small étale inclusion, the inverse of the
canonical equivalence of Stacks 06W0, and the slice forgetful functor. The canonical
isomorphism of scalar presheaves comes from the counit of that equivalence together with
Stacks 06W9. Restriction of scalars along it makes the localized module a module over the
existing small étale structure sheaf. The small étale and big fppf sites are required to have
the same size cutoff, as in Stacks 06W1.

As elsewhere in this area the two auxiliary constructions are stated for a general topology
`τ : GrothendieckTopology B.Schemes` with `hτ : τ ≤ B.topology` rather than for one of the
five named topologies; see the "Generality of `τ`" section of
`StacksFrontier/AlgebraicGeometry/Stacks/StructureSheaf.lean`. Neither uses which topology was
chosen, since the underlying presheaf of the structure sheaf does not depend on it. The
predicate `IsLocallyQuasicoherent` itself is stated at the big étale topology, which is where
the source states it: its first clause is the étale sheaf condition.

Module sections have an independent universe `m`; restriction retains that universe and does
not tie it to the universe of the schemes. `locallyQuasicoherentModules` keeps `m` free for the
same reason, so that it can be read at any universe of sections.

`locallyQuasicoherentModules` carries no `@[stacks]` attribute. It is the *category* that
Stacks 06WM is about, not one of that lemma's five assertions, and the source introduces it in
Stacks 06WJ rather than proving anything about it there. The five assertions of Stacks 06WM —
colimits, the abelian structure with kernels and cokernels computed in the ambient module
category, two-out-of-three for short exact sequences, and closure under tensor products and
internal homs — are proved at the module universe of the schemes in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentClosure`,
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentTensor` and
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentInternalHom`. Each
reduces, object by object through `restrictModuleToSmallEtale`, to the corresponding closure
property of quasi-coherent modules on the small étale site of a *scheme*, which is Descent,
Lemma 0GNB.

The two results below are the *formal* half of the colimits assertion at a free module
universe: once local quasi-coherence is known to be closed under colimits of a given shape, both
the existence of those colimits in `LQCoh(O_𝒳)` and their agreement with the colimits of the
ambient category of étale sheaves of modules follow, because a full subcategory closed under
colimits inherits them and its inclusion creates them. The closure property is a hypothesis
here; it is a theorem at the module universe of the schemes, which is the universe Stacks 06WM
is stated at.

What makes them available without any smallness hypothesis on `𝒳` is the free module universe.
The ambient colimits come from sheafification of `AddCommGrpCat`-valued presheaves on the
associated étale site, which `CategoryTheory.hasSheafifyEssentiallySmallSite` supplies at any
universe containing an essentially small model of the site. At section universe `max u v w m`
such a model exists for any `𝒳 : Type v` with `Category.{w} 𝒳`, so nothing has to be assumed;
at a section universe not containing `max v w` — for instance the `u` of
`AlgebraicGeometry.FibredSite.hasColimits_sheafOfModules`, where essential smallness of `𝒳` is
a hypothesis — it does not. That is why the module universe is kept free here.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06WM](https://stacks.math.columbia.edu/tag/06WM)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w m

namespace AlgebraicGeometry.Stack

/-- The category `LQCoh(O_𝒳)` of *locally quasi-coherent modules* on a category fibred in
groupoids: the full subcategory of the étale sheaves of `O_𝒳`-modules whose underlying presheaf
is locally quasi-coherent in the sense of `IsLocallyQuasicoherent` (**Stacks 06WJ**). This is
the category Stacks 06WM is about. -/
noncomputable abbrev locallyQuasicoherentModules
    (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) :=
  ObjectProperty.FullSubcategory
    (fun F : SheafOfModules.{m}
        (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)) =>
      IsLocallyQuasicoherent B E h S hS p hp F.val)

/-- The category `LQCoh(O_𝒳)` of locally quasi-coherent modules has colimits, provided local
quasi-coherence is closed under them. This is the formal half of the colimits assertion of
Stacks 06WM at a free module universe; the hypothesis is the closure property, which is
Descent, Lemma 0GNB(2) transported object by object through `restrictModuleToSmallEtale`. No
smallness of `𝒳` is assumed: the ambient colimits are available at the section universe
`max u v w m` for any `𝒳`. -/
theorem hasColimits_locallyQuasicoherentModules
    (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (hclosed : ∀ (K : Type (max u v w m)) [Category.{max u v w m} K],
      ObjectProperty.IsClosedUnderColimitsOfShape
        (fun F : SheafOfModules.{max u v w m}
            (ringStructureSheafCore B S hS p hp (etaleTopology B)
              (etaleTopology_le_topology B)) =>
          IsLocallyQuasicoherent B E h S hS p hp F.val) K) :
    Limits.HasColimits (locallyQuasicoherentModules.{u, v, w, max u v w m} B E h S hS p hp) := by
  have : EssentiallySmall.{max u v w m} 𝒳 := inferInstance
  have : HasSheafify (associatedTopology B S hS p (etaleTopology B))
      AddCommGrpCat.{max u v w m} := hasSheafifyEssentiallySmallSite _ _
  have : (associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective
      AddCommGrpCat.{max u v w m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  constructor
  intro K _
  have := hclosed K
  infer_instance

/-- The inclusion of `LQCoh(O_𝒳)` into all étale sheaves of `O_𝒳`-modules preserves colimits,
provided local quasi-coherence is closed under them: the agreement of colimits of the colimits
assertion of Stacks 06WM at a free module universe, again with the closure property as the
hypothesis. -/
theorem preservesColimits_locallyQuasicoherentInclusion
    (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
    (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (hclosed : ∀ (K : Type (max u v w m)) [Category.{max u v w m} K],
      ObjectProperty.IsClosedUnderColimitsOfShape
        (fun F : SheafOfModules.{max u v w m}
            (ringStructureSheafCore B S hS p hp (etaleTopology B)
              (etaleTopology_le_topology B)) =>
          IsLocallyQuasicoherent B E h S hS p hp F.val) K) :
    Limits.PreservesColimits
      (ObjectProperty.ι (fun F : SheafOfModules.{max u v w m}
        (ringStructureSheafCore B S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B)) =>
        IsLocallyQuasicoherent B E h S hS p hp F.val)) := by
  have : EssentiallySmall.{max u v w m} 𝒳 := inferInstance
  have : HasSheafify (associatedTopology B S hS p (etaleTopology B))
      AddCommGrpCat.{max u v w m} := hasSheafifyEssentiallySmallSite _ _
  have : (associatedTopology B S hS p (etaleTopology B)).WEqualsLocallyBijective
      AddCommGrpCat.{max u v w m} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _
  have : CreatesColimitsOfSize.{max u v w m, max u v w m}
      (ObjectProperty.ι (fun F : SheafOfModules.{max u v w m}
        (ringStructureSheafCore B S hS p hp (etaleTopology B)
          (etaleTopology_le_topology B)) =>
        IsLocallyQuasicoherent B E h S hS p hp F.val)) := by
    constructor
    intro K _
    have := hclosed K
    infer_instance
  exact preservesColimits_of_createsColimits_and_hasColimits _

end AlgebraicGeometry.Stack

end
