module

public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleExactAssociatedModule
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleQuasicoherentAbelian
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleQuasicoherentClosure

/-!
# Transporting the closure properties of quasi-coherent modules to the small étale site

Stacks 0GNB lists six closure properties of `QCoh(S_étale, 𝒪)`, and proves all six by
transporting the corresponding property of `QCoh(𝒪_S)` along the equivalence of Stacks 03DX (2).
**This file carries out that transport for clauses (1), (2), (3) and two of the three cases of
clause (4).**

The transport is run through the counit of the associated-module adjunction rather than through
the equivalence of categories, which avoids lifting a diagram into a full subcategory.  Write
`ε_*` for `AlgebraicGeometry.SmallEtale.restrictModule`, the right adjoint of `𝓕 ↦ 𝓕^a`.  For a
quasi-coherent `𝒢` on
`S_étale` the restriction `ε_*𝒢` is a quasi-coherent `𝒪_S`-module
(`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`) and the counit
`(ε_*𝒢)^a ⟶ 𝒢` is an isomorphism
(`AlgebraicGeometry.SmallEtale.isIso_counit`), both with no hypothesis.  So every diagram of
quasi-coherent modules on `S_étale` is canonically and naturally isomorphic to the image under
`𝓕 ↦ 𝓕^a` of a diagram of quasi-coherent `𝒪_S`-modules; `𝓕 ↦ 𝓕^a` is a left adjoint, hence
preserves colimits (Stacks 06VE (2), (3)), and it is left exact (Stacks 06VE (5)), so colimits
and kernels of the first diagram are the images of those of the second, which are quasi-coherent
by Schemes, Section 01LA.  Stacks 03DV (2) carries them back.

## Main results

* `AlgebraicGeometry.SmallEtale.counitIso`: the counit `(ε_*𝒢)^a ≅ 𝒢` at a quasi-coherent `𝒢`,
  with no hypothesis.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isColimit'`: the point of a colimit
  cocone of quasi-coherent modules on `S_étale` is quasi-coherent, for a shape whose colimits
  exist in both categories.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isColimit`: **Stacks 0GNB (2)** — a
  colimit of quasi-coherent modules on `S_étale` is quasi-coherent.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isColimit_cofan`: **Stacks 0GNB (1)** —
  a direct sum of quasi-coherent modules on `S_étale` is quasi-coherent.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isColimit_cokernelCofork` and
  `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_of_isLimit_kernelFork`: **Stacks
  0GNB (3)** — the cokernel and the kernel of a morphism of quasi-coherent modules on `S_étale`
  are quasi-coherent.  The `IsClosedUnderCokernels` and `IsClosedUnderKernels` instances are
  `AlgebraicGeometry.SmallEtale.isClosedUnderCokernels_isQuasicoherentOnSite` and
  `AlgebraicGeometry.SmallEtale.isClosedUnderKernels_isQuasicoherentOnSite`, imported.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_shortExact_X₁` and
  `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_shortExact_X₃`: **two of the three cases
  of Stacks 0GNB (4)**, the ones the source itself derives from clause (3).
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_iff_essImage_associatedModuleQcoh`:
  quasi-coherence on `S_étale` is exactly membership in the essential image of `𝓕 ↦ 𝓕^a`, with no
  hypothesis — the two halves of Stacks 03DX (2) and 03DV (2) read as one equivalence.
* `AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_shortExact_X₂_of_essImageExtension` and
  `isClosedUnderExtensions_isQuasicoherentOnSite_of_essImageExtension`:
  the third case of Stacks 0GNB (4) *reduced to Stacks 06VE (10)*, which is carried as a
  hypothesis.  By the equivalence above the hypothesis and the conclusion are the same statement,
  so nothing is lost and nothing is smuggled in; neither carries a `stacks` attribute.

## Implementation notes

The index universe of the colimits is the universe `u` of the scheme, as in
`AlgebraicGeometry.SmallEtale.preservesColimitsOfSize_associatedModuleQcoh`, which states
Stacks 06VE (3) at the same size.  A direct sum is the special case of a discrete shape and a
cokernel the special case of a parallel pair, so clauses (1) and the cokernel half of (3) are
instances of the colimit statement, stated separately because the source states them separately
and because their shapes live in different universes.

The third case of clause (4) — an extension of two quasi-coherent modules is quasi-coherent — is
**not proved** here.  The source derives it not from clause (3) but from Stacks 06VE (10), which
asserts that a module sitting in a short exact sequence between two associated modules is itself
an associated module.  What is here is the reduction to it,
`isQuasicoherentOnSite_shortExact_X₂_of_essImageExtension`, carrying it as a hypothesis, together
with the equivalence that shows the two statements coincide on this site.

That hypothesis is **no longer missing**: 06VE (10) at `τ = étale` is
`AlgebraicGeometry.SmallEtale.essImage_X₂_of_shortExact` and the third case of 0GNB (4) itself is
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_shortExact_X₂`, both in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRestrictionRightExact.lean`,
which also supplies the `ObjectProperty.IsClosedUnderExtensions` instance for
`SheafOfModules.isQuasicoherentOnSite (structureSheaf B S hS)` unconditionally.  The two
statements in *this* file keep their hypothesis and keep carrying no attribute.

Clauses (5) and (6) are also not here.  (5) is
`AlgebraicGeometry.SmallEtale.tensorSheaf_isQuasicoherentOnSite`
(`StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleQuasicoherentTensor`).  (6) is
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_internalHomSheaf`
(`StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleInternalHomFinitePresentation`), at the
source hypothesis the clause states — finite presentation in the sense of Stacks 03DL (7) — and
with no hypothesis of its own.  So all six clauses of the tag are theorems.

## References

* [Stacks Project, Tag 0GNB](https://stacks.math.columbia.edu/tag/0GNB)
* [Stacks Project, Tag 03DV](https://stacks.math.columbia.edu/tag/03DV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06VE](https://stacks.math.columbia.edu/tag/06VE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The counit at a quasi-coherent module -/

/-- **The counit of the associated-module adjunction of `S_étale` is an isomorphism at every
quasi-coherent module, with no hypothesis.**  Its second hypothesis in
`AlgebraicGeometry.SmallEtale.isIso_counit` is discharged by
`AlgebraicGeometry.SmallEtale.isQuasicoherent_restrictModule`. -/
public theorem isIso_counit' (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hG : G.IsQuasicoherentOnSite) :
    IsIso ((associatedModuleAdjunction B S hS).counit.app G) :=
  isIso_counit B S hS G hG (isQuasicoherent_restrictModule B S hS G hG)

/-- A quasi-coherent module on `S_étale` is the associated module of its own restriction to the
small Zariski site of `S`, by the counit. -/
public noncomputable def counitIso (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hG : G.IsQuasicoherentOnSite) :
    (associatedModule B S hS).obj ((restrictModule B S hS).obj G) ≅ G :=
  haveI := isIso_counit' B S hS G hG
  asIso ((associatedModuleAdjunction B S hS).counit.app G)

/-- The forward map of `counitIso` is the counit of the associated-module adjunction at `G`. -/
@[simp]
public theorem counitIso_hom (G : SheafOfModules.{u} (structureSheaf B S hS))
    (hG : G.IsQuasicoherentOnSite) :
    (counitIso B S hS G hG).hom = (associatedModuleAdjunction B S hS).counit.app G :=
  rfl

/-- A module on `S_étale` isomorphic to the associated module of a quasi-coherent `𝒪_S`-module is
quasi-coherent. -/
private theorem isQuasicoherentOnSite_of_iso_associatedModule {F : S.Modules}
    (hF : SheafOfModules.IsQuasicoherent (R := S.ringCatSheaf) F)
    {G : SheafOfModules.{u} (structureSheaf B S hS)} (e : (associatedModule B S hS).obj F ≅ G) :
    G.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_associatedModule_of_isQuasicoherent B S hS F hF).of_iso e

/-! ### Colimits -/

section Colimits

/-- The point of a colimit cocone of quasi-coherent modules on the small étale site of `S` is
quasi-coherent, for any shape whose colimits exist in the modules on `S` and on `S_étale`. -/
public theorem isQuasicoherentOnSite_of_isColimit' {K : Type w} [Category.{w'} K]
    [∀ R : CommRingCat.{u}, HasColimitsOfShape K (ModuleCat.{u} R)]
    [HasColimitsOfShape K S.Modules]
    [HasColimitsOfShape K (SheafOfModules.{u} (structureSheaf B S hS))]
    {D : K ⥤ SheafOfModules.{u} (structureSheaf B S hS)}
    (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) {c : Cocone D} (hc : IsColimit c) :
    c.pt.IsQuasicoherentOnSite := by
  have : PreservesColimitsOfShape K (associatedModule B S hS) :=
    (associatedModuleAdjunction B S hS).leftAdjoint_preservesColimits.preservesColimitsOfShape
  let D' := D ⋙ restrictModule B S hS
  let e : D' ⋙ associatedModule B S hS ≅ D :=
    NatIso.ofComponents (fun k => counitIso B S hS (D.obj k) (hD k))
      (fun f => (associatedModuleAdjunction B S hS).counit.naturality (D.map f))
  exact isQuasicoherentOnSite_of_iso_associatedModule B S hS
    (Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isColimit (D := D')
      (fun k => isQuasicoherent_restrictModule B S hS (D.obj k) (hD k))
      (colimit.isColimit D'))
    (preservesColimitIso (associatedModule B S hS) D' ≪≫ HasColimit.isoOfNatIso e ≪≫
      (colimit.isColimit D).coconePointUniqueUpToIso hc)

end Colimits

/-- **Stacks 0GNB (2).**  A colimit of quasi-coherent `𝒪`-modules on the small étale site of a
scheme is quasi-coherent; the shape is indexed at the size of the scheme, as in Stacks 06VE (3)
on the same site. -/
@[stacks 0GNB "part (2): colimits"]
public theorem isQuasicoherentOnSite_of_isColimit {K : Type u} [SmallCategory K]
    {D : K ⥤ SheafOfModules.{u} (structureSheaf B S hS)}
    (hD : ∀ k, (D.obj k).IsQuasicoherentOnSite) {c : Cocone D} (hc : IsColimit c) :
    c.pt.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isColimit' B S hS hD hc

/-- **Stacks 0GNB (1).**  A direct sum of quasi-coherent `𝒪`-modules on the small étale site of
a scheme is quasi-coherent. -/
@[stacks 0GNB "part (1): direct sums"]
public theorem isQuasicoherentOnSite_of_isColimit_cofan {I : Type u}
    {F : I → SheafOfModules.{u} (structureSheaf B S hS)}
    (hF : ∀ i, (F i).IsQuasicoherentOnSite)
    {c : Cocone (Discrete.functor F)} (hc : IsColimit c) :
    c.pt.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isColimit' B S hS (fun i => hF i.as) hc

/-! ### Kernels and cokernels -/

/-- **Stacks 0GNB (3), the cokernel half.**  A cokernel of a morphism of quasi-coherent
`𝒪`-modules on the small étale site of a scheme is quasi-coherent. -/
@[stacks 0GNB "part (3): cokernels"]
public theorem isQuasicoherentOnSite_of_isColimit_cokernelCofork
    {M N : SheafOfModules.{u} (structureSheaf B S hS)} (f : M ⟶ N)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    {c : CokernelCofork f} (hc : IsColimit c) : c.pt.IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_of_isColimit' B S hS
    (D := parallelPair f 0) (fun k => by cases k <;> assumption) hc

/-- **Stacks 0GNB (3), the kernel half.**  A kernel of a morphism of quasi-coherent
`𝒪`-modules on the small étale site of a scheme is quasi-coherent. -/
@[stacks 0GNB "part (3): kernels"]
public theorem isQuasicoherentOnSite_of_isLimit_kernelFork
    {M N : SheafOfModules.{u} (structureSheaf B S hS)} (f : M ⟶ N)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    {c : KernelFork f} (hc : IsLimit c) : c.pt.IsQuasicoherentOnSite := by
  have : PreservesFiniteLimits (associatedModule B S hS) :=
    preservesFiniteLimits_associatedModule B S hS
  let g := (restrictModule B S hS).map f
  have := isQuasicoherent_restrictModule B S hS M hM
  have := isQuasicoherent_restrictModule B S hS N hN
  exact isQuasicoherentOnSite_of_iso_associatedModule B S hS
    (Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel g)
    (PreservesKernel.iso (associatedModule B S hS) g ≪≫
      kernel.mapIso _ f (counitIso B S hS M hM) (counitIso B S hS N hN)
        ((associatedModuleAdjunction B S hS).counit.naturality f) ≪≫
      (kernelIsKernel f).conePointUniqueUpToIso hc)

/-! ### Two of the three cases of the two-out-of-three clause -/

/-- **Stacks 0GNB (4), the case in which the quotient and the middle term are quasi-coherent.**
The kernel term of a short exact sequence of `𝒪`-modules on the small étale site of a scheme is
quasi-coherent when the other two are. -/
@[stacks 0GNB "part (4): the case of the sub, from the kernel clause"]
public theorem isQuasicoherentOnSite_shortExact_X₁
    {T : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hT : T.ShortExact)
    (h₂ : T.X₂.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite) :
    T.X₁.IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_shortExact_X₁ hT h₂ h₃

/-- **Stacks 0GNB (4), the case in which the sub and the middle term are quasi-coherent.**
The quotient term of a short exact sequence of `𝒪`-modules on the small étale site of a scheme
is quasi-coherent when the other two are. -/
@[stacks 0GNB "part (4): the case of the quotient, from the cokernel clause"]
public theorem isQuasicoherentOnSite_shortExact_X₃
    {T : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (h₂ : T.X₂.IsQuasicoherentOnSite) :
    T.X₃.IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_shortExact_X₃ hT h₁ h₂

/-! ### The third case, and what it is still missing -/

/-- **On the small étale site of a scheme, quasi-coherence is exactly membership in the
essential image of `𝓕 ↦ 𝓕^a`**, with no hypothesis.

The two directions are the two halves of Stacks 03DX (2) and 03DV (2) at `τ = étale`, both
proved unconditionally: essential surjectivity is
`AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule` and quasi-coherence of an
associated module is
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_associatedModule_of_isQuasicoherent`.

The point of recording the two as one equivalence is that it identifies the two predicates a
closure clause can be stated about.  In particular the third case of Stacks 0GNB (4) — an
extension of two quasi-coherent modules — and Stacks 06VE (10) at `τ = étale` — a module in a
short exact sequence between two associated modules is an associated module — are, on this site,
*the same statement*; see
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_shortExact_X₂_of_essImageExtension`. -/
public theorem isQuasicoherentOnSite_iff_essImage_associatedModuleQcoh
    (G : SheafOfModules.{u} (structureSheaf B S hS)) :
    G.IsQuasicoherentOnSite ↔ (associatedModuleQcoh B S hS).essImage G := by
  refine ⟨fun hG => quasicoherentIsEssImageAssociatedModule B S hS G hG, fun hG => ?_⟩
  obtain ⟨𝓕, ⟨e⟩⟩ := hG
  exact isQuasicoherentOnSite_of_iso_associatedModule B S hS 𝓕.property e

/-- **The third case of Stacks 0GNB (4), reduced to Stacks 06VE (10) at `τ = étale`.**  The
middle term of a short exact sequence of `𝒪`-modules on the small étale site of a scheme is
quasi-coherent when the outer two are, given that the essential image of `𝓕 ↦ 𝓕^a` is closed
under extensions.

The hypothesis `h` is Stacks 06VE (10) at `τ = étale`, stated as the source states it.  It is
**proved** in this library, as `AlgebraicGeometry.SmallEtale.essImage_X₂_of_shortExact`, so this
statement is a reading of that clause rather than a gap.  By
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_iff_essImage_associatedModuleQcoh` the
hypothesis and the conclusion are the same statement read through the equivalence of Stacks
03DX (2), so this reduction neither weakens 06VE (10) nor smuggles anything in: the two are
equivalent.

**No `@[stacks 0GNB]` attribute is carried**, a hypothesis being part of a citation.  All three
cases of the clause are registered on unconditional statements: the first two on
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_shortExact_X₁` and `…_X₃` below, and the
third — which, as the source itself notes, does not follow from clause (3) — on
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_shortExact_X₂` in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleRestrictionRightExact.lean`. -/
public theorem isQuasicoherentOnSite_shortExact_X₂_of_essImageExtension
    (h : ∀ T : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS)), T.ShortExact →
      (associatedModuleQcoh B S hS).essImage T.X₁ →
      (associatedModuleQcoh B S hS).essImage T.X₃ →
      (associatedModuleQcoh B S hS).essImage T.X₂)
    {T : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS))} (hT : T.ShortExact)
    (h₁ : T.X₁.IsQuasicoherentOnSite) (h₃ : T.X₃.IsQuasicoherentOnSite) :
    T.X₂.IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_essImage_associatedModuleQcoh B S hS T.X₂).2
    (h T hT ((isQuasicoherentOnSite_iff_essImage_associatedModuleQcoh B S hS T.X₁).1 h₁)
      ((isQuasicoherentOnSite_iff_essImage_associatedModuleQcoh B S hS T.X₃).1 h₃))

/-- Quasi-coherence of modules on the small étale site of a scheme is closed under extensions,
given Stacks 06VE (10) at `τ = étale`.  This is the shape in which
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedEquivalence` consumes
the third case of Stacks 0GNB (4): supplying `h` turns its
`[(qcohOnSite B S hS).IsClosedUnderExtensions` binder into an instance. -/
public theorem isClosedUnderExtensions_isQuasicoherentOnSite_of_essImageExtension
    (h : ∀ T : ShortComplex (SheafOfModules.{u} (structureSheaf B S hS)), T.ShortExact →
      (associatedModuleQcoh B S hS).essImage T.X₁ →
      (associatedModuleQcoh B S hS).essImage T.X₃ →
      (associatedModuleQcoh B S hS).essImage T.X₂) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (structureSheaf B S hS)).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hT h₁ h₃ :=
    isQuasicoherentOnSite_shortExact_X₂_of_essImageExtension B S hS h hT h₁ h₃

end AlgebraicGeometry.SmallEtale

end
