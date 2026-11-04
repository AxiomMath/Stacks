module

public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Sites.Over
public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Zariski.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites

/-!
# Adequate sheaves of modules on a big site

A sheaf of modules on one of the five big `τ`-sites of a scheme `S` is *adequate* when, after a
`τ`-covering of `S` by affine schemes `Spec Aᵢ`, each of the induced functors on the category of
`Aᵢ`-algebras belonging to the site is an adequate module-valued functor in the sense of
[Stacks, Tag 06UT].

## Main definitions

* `Stacks.Adequate.BigSite` packages one of the five chosen big sites: its cutoff, its
  topology, the sheaf condition for the structure presheaf, and a witness that the topology is
  the one of the corresponding accepted big-site construction.
* `Stacks.Adequate.affineSectionFunctor` is the canonical functor of affine sections.
* `Stacks.Adequate.IsAdequate` is adequacy of a sheaf of modules.
* `Stacks.Adequate.adequate` is the category `Adeq(𝒪)` of adequate `𝒪`-modules, namely the
  strictly full subcategory of the sheaves of modules on the site cut out by adequacy.

## Main results

The scalar identification `Stacks.Adequate.affineRingMap` is an isomorphism. The simp lemmas
`Stacks.Adequate.affineSectionFunctor_obj` and `Stacks.Adequate.affineSectionFunctor_map`
identify evaluation and restriction with the original sheaf of modules.

## Implementation notes

The site's containment predicate is fixed by its cutoff, rather than supplied independently.
The canonical affine-section functor is available for any affine scheme over the base belonging
to the site, before a covering is chosen. The functor's evaluation and restriction lemmas are
the direct interface for local adequacy and descent statements.

`AlgebraicGeometry.CoveringTopology`, the list of the five topologies with standard affine
coverings, and `AlgebraicGeometry.coveringMorphismProperty`, the property each member of a
covering family must have, are in
`StacksFrontier/AlgebraicGeometry/Topologies/StandardCoverings.lean`, which this module imports.

* `CoveringTopology` is the `Topology` of [Stacks, Tag 03X9], which that tag itself leaves
  untagged (the tag belongs to `IsStandardCovering`).
* `coveringMorphismProperty` is the `coveringMorphismProperty` of [Stacks, Tag 03X8]; that tag
  also covers `AlgebraicGeometry.Scheme.precoverage` and
  `AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff`.

`AlgebraicGeometry.BigZariskiOver` — the big Zariski category over `S`, with its covering
families and Grothendieck topology — is in
`StacksFrontier/AlgebraicGeometry/Topologies/ZariskiTopology/Sites.lean`, which this module
imports. The four other big sites over `S` are likewise already in the library and are used
from there.

**There is no unconditional constructor of a `BigSite` for any of the five topologies**, so the
five constructions `BigSite.{zariski, etale, fppf, smooth, syntomic}` of [Stacks, Tag 06VG] are
not reproduced here. Such a constructor would have to supply the `isSheaf` field from the
corresponding sheaf condition of Tag 03DU, and none of those five sheaf conditions is proved
here, so an unconditional constructor would make every object of `BigSite` rest on an unproved
statement. What is available instead is `BigSite.ofZariski` and its four companions, which
take the Tag 03DU sheaf condition for their topology as an explicit argument; a proof of
that condition substituted into one of them gives the unconditional constructor, which is the
constructor of Tag 06VG.

`Stacks.Adequate.adequate` carries only its closure under isomorphisms. The remaining
properties making `Adeq(𝒪)` an abelian subcategory — containing the zero sheaf and closure
under kernels and cokernels, which for module-valued functors on algebras are
`AdequateFunctor.adequate_containsZero`, `AdequateFunctor.adequate_isClosedUnderKernels` and
`AdequateFunctor.adequate_isClosedUnderCokernels` — are not asserted here: they need the
affine-section functors of a kernel or cokernel of sheaves of modules to be the kernel or
cokernel of the affine-section functors, which is not available.

## References

* [Stacks Project, Tag 06VG](https://stacks.math.columbia.edu/tag/06VG)
* [Stacks Project, Tag 07AH](https://stacks.math.columbia.edu/tag/07AH)
* [Stacks Project, Tag 06UT](https://stacks.math.columbia.edu/tag/06UT)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u m

namespace Stacks.Adequate

/-! ### A chosen big site -/

/-- A chosen big site over `S` with the cutoff and topology of one of the
five standard big sites. -/
public structure BigSite (τ : CoveringTopology) (S : Scheme.{u}) where
  /-- The cardinal cutoff defining the underlying category of schemes. -/
  cutoff : Cardinal.{u}
  /-- The base scheme belongs to the chosen category of schemes. -/
  base_mem : schemeSizeBelow cutoff S
  /-- The Grothendieck topology on the slice at the base scheme. -/
  topology : GrothendieckTopology (Over (⟨S, base_mem⟩ : SchemeBelow cutoff))
  /-- The structure presheaf of global functions is a sheaf for that topology. -/
  isSheaf : Presheaf.IsSheaf topology
    (Stacks.Sites.structurePresheaf S
      (Over.post (ObjectProperty.ι (schemeSizeBelow cutoff))))
  /-- The topology is the one of the corresponding accepted big-site construction. -/
  chosen :
    (τ = .zariski ∧ ∃ B : BigZariskiSite.{u},
      ∃ hS : B.Contains S, ∃ _e : B.schemeCardinal = cutoff,
        HEq topology (BigZariskiOver.topology B S hS)) ∨
    (τ = .etale ∧ ∃ B : BigEtaleSite.{u},
      ∃ hS : B.Contains S, ∃ _e : B.cutoff = cutoff,
        HEq topology (BigEtaleOver.topology B S hS)) ∨
    (τ = .fppf ∧ ∃ B : BigFppfSite.{u},
      ∃ hS : B.Contains S, ∃ _e : B.cutoff = cutoff,
        HEq topology (BigFppfOver.topology B S hS)) ∨
    (τ = .smooth ∧ ∃ B : BigSmoothSite.{u},
      ∃ hS : S.size < B.cutoff, ∃ _e : B.cutoff = cutoff,
        HEq topology (BigSmoothOver.topology B S hS)) ∨
    (τ = .syntomic ∧ ∃ B : BigSyntomicSite.{u},
      ∃ hS : B.Contains S, ∃ _e : B.cutoff = cutoff,
        HEq topology (BigSyntomicOver.topology B S hS))

/-- The underlying category of a chosen big site. -/
public abbrev BigSite.category {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) := Over (⟨S, B.base_mem⟩ : SchemeBelow B.cutoff)

/-- The canonical functor from a chosen big site to the schemes over `S`. -/
public abbrev BigSite.toOver {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) : B.category ⥤ Over S :=
  Over.post (ObjectProperty.ι (schemeSizeBelow B.cutoff))

/-- The structure sheaf of rings of a chosen big site. -/
public noncomputable abbrev BigSite.structureSheaf {τ : CoveringTopology} {S : Scheme.{u}}
    (B : BigSite τ S) : Sheaf B.topology RingCat.{u} :=
  ⟨Stacks.Sites.structurePresheaf S B.toOver, B.isSheaf⟩

/-! ### Building a chosen big site from an accepted one -/

/-- The chosen big Zariski site as a big site for adequate sheaves, given the sheaf condition
of [Stacks, Tag 03DU]. -/
public def BigSite.ofZariski (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (h : Presheaf.IsSheaf (BigZariskiOver.topology B S hS)
      (Stacks.Sites.structurePresheaf S
        (Over.post (ObjectProperty.ι (schemeSizeBelow B.schemeCardinal))))) :
    BigSite .zariski S where
  cutoff := B.schemeCardinal
  base_mem := hS
  topology := BigZariskiOver.topology B S hS
  isSheaf := h
  chosen := Or.inl ⟨rfl, B, hS, rfl, HEq.rfl⟩

/-- The chosen big étale site as a big site for adequate sheaves, given the sheaf condition
of [Stacks, Tag 03DU]. -/
public def BigSite.ofEtale (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (h : Presheaf.IsSheaf (BigEtaleOver.topology B S hS)
      (Stacks.Sites.structurePresheaf S
        (Over.post (ObjectProperty.ι (schemeSizeBelow B.cutoff))))) :
    BigSite .etale S where
  cutoff := B.cutoff
  base_mem := hS
  topology := BigEtaleOver.topology B S hS
  isSheaf := h
  chosen := Or.inr (Or.inl ⟨rfl, B, hS, rfl, HEq.rfl⟩)

/-- The chosen big fppf site as a big site for adequate sheaves, given the sheaf condition
of [Stacks, Tag 03DU]. -/
public def BigSite.ofFppf (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (h : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (Stacks.Sites.structurePresheaf S
        (Over.post (ObjectProperty.ι (schemeSizeBelow B.cutoff))))) :
    BigSite .fppf S where
  cutoff := B.cutoff
  base_mem := hS
  topology := BigFppfOver.topology B S hS
  isSheaf := h
  chosen := Or.inr (Or.inr (Or.inl ⟨rfl, B, hS, rfl, HEq.rfl⟩))

/-- The chosen big smooth site as a big site for adequate sheaves, given the sheaf condition
of [Stacks, Tag 03DU]. -/
public def BigSite.ofSmooth (B : BigSmoothSite.{u})
    (S : Scheme.{u}) (hS : S.size < B.cutoff)
    (h : Presheaf.IsSheaf (BigSmoothOver.topology B S hS)
      (Stacks.Sites.structurePresheaf S
        (Over.post (ObjectProperty.ι (schemeSizeBelow B.cutoff))))) :
    BigSite .smooth S where
  cutoff := B.cutoff
  base_mem := hS
  topology := BigSmoothOver.topology B S hS
  isSheaf := h
  chosen := Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, B, hS, rfl, HEq.rfl⟩)))

/-- The chosen big syntomic site as a big site for adequate sheaves, given the sheaf condition
of [Stacks, Tag 03DU]. -/
public def BigSite.ofSyntomic (B : BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    (h : Presheaf.IsSheaf (BigSyntomicOver.topology B S hS)
      (Stacks.Sites.structurePresheaf S
        (Over.post (ObjectProperty.ι (schemeSizeBelow B.cutoff))))) :
    BigSite .syntomic S where
  cutoff := B.cutoff
  base_mem := hS
  topology := BigSyntomicOver.topology B S hS
  isSheaf := h
  chosen := Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, B, hS, rfl, HEq.rfl⟩)))

/-! ### Affine sections -/

/-- The canonical restriction of `Spec` to algebras whose spectra lie in the big site. -/
@[implicit_reducible] public noncomputable def affineSpecOver
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S) :
    (AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖ ⥤
      B.category := by
  let ι := AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)
  let G : (AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖ ⥤
      Over S :=
    ι.op ⋙ algSpec A ⋙ Over.map f
  refine {
    obj := fun X => Over.mk (ObjectProperty.homMk (G.obj X).hom :
      (⟨(G.obj X).left, X.unop.property⟩ : SchemeBelow B.cutoff) ⟶
        ⟨S, B.base_mem⟩)
    map := fun {X Y} g => Over.homMk
      (ObjectProperty.homMk (G.map g).left) ?_
    map_id := ?_
    map_comp := ?_ }
  · apply ObjectProperty.hom_ext
    exact (G.map g).w
  · intro X
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    simp
  · intro X Y Z g h
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    simp

/-- The canonical scalar-ring map from each algebra to functions on its spectrum. -/
public noncomputable def affineRingMap
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S) :
    AdequateFunctor.algebraRingDiagramOn
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) ⟶
    (affineSpecOver B A f).op ⋙ B.structureSheaf.obj := by
  let ι := AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)
  refine { app := fun X => ?_, naturality := ?_ }
  · exact (forget₂ CommRingCat RingCat).map
      (Scheme.ΓSpecIso (CommRingCat.of (ι.obj X.unop.unop))).inv
  · intro X Y g
    let h := CommRingCat.ofHom ((ι.map g.unop.unop).hom.toRingHom)
    change (forget₂ CommRingCat RingCat).map h ≫
        (forget₂ CommRingCat RingCat).map
          (Scheme.ΓSpecIso (CommRingCat.of (ι.obj Y.unop.unop))).inv =
      (forget₂ CommRingCat RingCat).map
          (Scheme.ΓSpecIso (CommRingCat.of (ι.obj X.unop.unop))).inv ≫
        (forget₂ CommRingCat RingCat).map (Spec.map h).appTop
    simpa only [Functor.map_comp] using
      congrArg (forget₂ CommRingCat RingCat).map
        (Scheme.ΓSpecIso_inv_naturality h)

/-- The scalar identification with functions on an affine spectrum is an isomorphism. -/
public instance affineRingMap_isIso
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S) :
    IsIso (affineRingMap B A f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  change IsIso ((forget₂ CommRingCat RingCat).map
    (Scheme.ΓSpecIso (CommRingCat.of
      ((AdequateFunctor.siteAlgebraInclusion A
        (schemeSizeBelow B.cutoff)).obj X.unop.unop))).inv)
  infer_instance

/-- The canonical module-valued functor of affine sections. -/
@[implicit_reducible] public noncomputable def affineSectionFunctor
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (F : SheafOfModules.{m} B.structureSheaf)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S) :
    AdequateFunctor.ModuleValuedFunctorOn
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)) :=
  (PresheafOfModules.pushforward (affineRingMap B A f)).obj F.val

/-- The affine-section functor evaluates to sections on the spectrum. -/
@[simp] public theorem affineSectionFunctor_obj
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (F : SheafOfModules.{m} B.structureSheaf)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (X : (AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖᵒᵖ) :
    (((affineSectionFunctor B F A f).obj X) : Type m) =
      ((F.val.obj ((affineSpecOver B A f).op.obj X)) : Type m) := rfl

/-- Restriction of affine sections is the restriction map of the sheaf. -/
@[simp] public theorem affineSectionFunctor_map
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (F : SheafOfModules.{m} B.structureSheaf)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    {X Y : (AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖᵒᵖ}
    (g : X ⟶ Y) (x : (affineSectionFunctor B F A f).obj X) :
    (affineSectionFunctor B F A f).map g x =
      F.val.map ((affineSpecOver B A f).op.map g) x := rfl

/-- Adequacy of a sheaf of modules on the selected big site. -/
@[stacks 06VG] public abbrev IsAdequate
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)
    (F : SheafOfModules.{m} B.structureSheaf) : Prop :=
  ∃ (I : Type (u + 1)) (A : I → CommRingCat.{u})
      (f : ∀ i, Spec (A i) ⟶ S),
    (∀ i, coveringMorphismProperty τ (f i)) ∧
    ((⋃ i, Set.range (f i)) = Set.univ) ∧
    (∀ i, schemeSizeBelow B.cutoff (Spec (A i)) ∧
      AdequateFunctor.IsAdequate
        (AdequateFunctor.siteAlgebraInclusion (A i) (schemeSizeBelow B.cutoff))
        (affineSectionFunctor B F (A i) (f i)))

/-! ### The category of adequate modules -/

/-- The category `Adeq(𝒪)` of adequate `𝒪`-modules on the selected big site: the strictly full
subcategory of the sheaves of modules on the site cut out by adequacy. -/
@[stacks 07AH] public abbrev adequate
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S) :
    ObjectProperty (SheafOfModules.{m} B.structureSheaf) :=
  fun F ↦ IsAdequate B F

/-- Adequacy is invariant under isomorphism of sheaves of modules, because the affine-section
functors of isomorphic sheaves are isomorphic. -/
public instance adequate_isClosedUnderIsomorphisms
    {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S) :
    (adequate.{u, m} B).IsClosedUnderIsomorphisms where
  of_iso e hF := by
    obtain ⟨I, A, f, hcovering, hsurjective, h⟩ := hF
    exact ⟨I, A, f, hcovering, hsurjective, fun i ↦ ⟨(h i).1,
      AdequateFunctor.IsAdequate.of_iso (h i).2
        ((PresheafOfModules.pushforward (affineRingMap B (A i) (f i))).mapIso
          ((SheafOfModules.forget B.structureSheaf).mapIso e.symm))⟩⟩

end Stacks.Adequate

add_to_stacks 06VF "Section 46.5: a sheaf of 𝒪-modules on (Sch/S)_τ is adequate when its
affine-section functors are adequate over the members of a τ-covering of S by affines"
  Stacks.Adequate.IsAdequate

end
