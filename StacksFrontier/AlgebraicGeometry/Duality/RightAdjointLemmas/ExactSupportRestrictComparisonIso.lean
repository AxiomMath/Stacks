module

public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedPushforwardConservative
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportRestrictComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportEquiv

/-!
# Invertibility of the restriction comparison for sheaf Hom with exact support

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces and let `U ⊆ X` be open. The
comparisons

`ℰom(𝒪_Z, F)|_{i⁻¹U} ⟶ ℰom(𝒪_{Z|_{i⁻¹U}}, F|_U)` and
`(R ℰom(𝒪_Z, K))|_{i⁻¹U} ⟶ R ℰom(𝒪_{Z|_{i⁻¹U}}, K|_U)`

are `ClosedQuotientMorphismOfRingedSpaces.sheafHomExactSupportRestrictComparison` and
`ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportRestrictComparison`, the mates
of the base-change square of pushforward and restriction. This file supplies the **opening move
of the proof that they are invertible**: the restriction `i|_{i⁻¹U}` is again a closed quotient
morphism, so its pushforward is exact and fully faithful by [Stacks, Tag 08KS] and therefore
reflects isomorphisms on sheaves of modules, and the functor it induces on unbounded derived
categories reflects isomorphisms too, being exact and conservative on cohomology objects.
Invertibility of either comparison may consequently be checked after applying `(i|_{i⁻¹U})_*`,
respectively `R(i|_{i⁻¹U})_*`.

The derived reflection does *not* come from full faithfulness of
`(modulePushforward (i|_{i⁻¹U})).mapDerivedCategory`, which fails as soon as the kernel ideal of
the comorphism is nonzero: `Ext¹` of the residue field of a closed point of a curve with itself
is one-dimensional on the curve and zero on the point, so the derived pushforward is not full
and the unit of [Stacks, Tag 0A76] is not invertible. Only the underived `i_*` is fully
faithful.

## Main results

All names below are in the namespace `ClosedQuotientMorphismOfRingedSpaces`.

* `isIso_sheafHomExactSupportRestrictComparison_app_of_map` and
  `isIso_derivedSheafHomExactSupportRestrictComparison_app_of_map`: **"it suffices after
  `(i|_{i⁻¹U})_*`"**, pointwise.
* `isIso_sheafHomExactSupportRestrictComparison_of_map` and
  `isIso_derivedSheafHomExactSupportRestrictComparison_of_map`: the same for the whole 2-square,
  which is invertible as soon as each of its components is.
* `isIso_sheafHomExactSupportRestrictComparison_app_iff` and
  `isIso_derivedSheafHomExactSupportRestrictComparison_app_iff`: the same as an equivalence, so
  the reduction loses nothing.
* `reflectsIsomorphisms_modulePushforward_restrictedMorphism` and its derived counterpart: the
  two reflection instances at the written-out spelling
  `Stacks.Cohomology.HigherDirectImage.restrictedMorphism` of the restricted morphism.
* `isIso_sheafHomExactSupportRestrictComparison`: **the underived comparison is an
  isomorphism.**

## The comparisons are isomorphisms

The underived comparison **is** an isomorphism:
`ClosedQuotientMorphismOfRingedSpaces.isIso_sheafHomExactSupportRestrictComparison`. After the
reduction to `(i|_{i⁻¹U})_*`, the counit equation of the comparison identifies its composite
with evaluation at one with the restriction to `U` of evaluation at one for `i`; evaluation at
one is injective on sections with image the sections locally annihilated by the kernel ideal
([Stacks, Tag 0A75] read on sections, `sectionsSheafHomExactSupportEquiv`), and the kernel ideal
of `i|_{i⁻¹U}` is the restriction of that of `i`, so the comparison is bijective on sections.
This avoids the internal-Hom identifications of [Stacks, Tag 08DL] and [Stacks, Tag 0E8H].

On derived categories,
`ClosedQuotientMorphismOfRingedSpaces.nonempty_derivedSheafHomExactSupport_restrict_iso` gives
`(R ℰom(𝒪_Z, K))|_{i⁻¹U} ≅ R ℰom(𝒪_{Z|_{i⁻¹U}}, K|_U)` at any chosen models, through a
K-injective resolution. It is not proved that this isomorphism is the derived comparison
`derivedSheafHomExactSupportRestrictComparison`.

## Implementation notes

The reflection instances hold for a bundled closed quotient morphism
(`ClosedQuotientMorphismOfRingedSpaces.reflectsIsomorphisms_modulePushforward` and its derived
counterpart), and `ClosedQuotientMorphismOfRingedSpaces.restrict` presents `i|_{i⁻¹U}` as one.
They are restated here at the spelling `Stacks.Cohomology.HigherDirectImage.restrictedMorphism`
used by the comparison, because instance search cannot discover the bundled morphism from the
written-out one: unifying `modulePushforward ?S.i` with
`modulePushforward (restrictedMorphism S.i U)` means solving for `?S` under a projection, which
it does not do. Supplying `S.restrict U` by hand is enough — the two spellings are the same term
by `ClosedQuotientMorphismOfRingedSpaces.restrict_i`, and `restrict` is reducible, so the
instances transfer.

## References

* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
* [Stacks Project, Tag 0A76](https://stacks.math.columbia.edu/tag/0A76)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
* [Stacks Project, Tag 0E8H](https://stacks.math.columbia.edu/tag/0E8H)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage

attribute [local instance] HasDerivedCategory.standard

universe u

namespace RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u}) (U : Opens S.X)

/-! ### Reflection of isomorphisms by the pushforward of the restricted situation -/

/-- **Pushforward along the restriction of a closed quotient morphism reflects
isomorphisms.** The restriction `i|_{i⁻¹U}` is again a closed quotient morphism, so this is
`ClosedQuotientMorphismOfRingedSpaces.reflectsIsomorphisms_modulePushforward` for it, read at
the written-out restriction `Stacks.Cohomology.HigherDirectImage.restrictedMorphism`. -/
instance reflectsIsomorphisms_modulePushforward_restrictedMorphism :
    (modulePushforward (restrictedMorphism S.i U)).ReflectsIsomorphisms :=
  (S.restrict U).reflectsIsomorphisms_modulePushforward

/-- **Derived pushforward along the restriction of a closed quotient morphism reflects
isomorphisms**, read at the written-out restriction. -/
instance reflectsIsomorphisms_mapDerivedCategory_modulePushforward_restrictedMorphism :
    (modulePushforward (restrictedMorphism S.i U)).mapDerivedCategory.ReflectsIsomorphisms :=
  (S.restrict U).reflectsIsomorphisms_mapDerivedCategory_modulePushforward

/-! ### The reduction for the underived comparison -/

/-- **"It suffices after `(i|_{i⁻¹U})_*`" for the underived comparison.** If the image of the
component of `ClosedQuotientMorphismOfRingedSpaces.sheafHomExactSupportRestrictComparison` at an
`𝒪_X`-module `F` under pushforward along the restricted morphism is invertible, then that
component is invertible. -/
theorem isIso_sheafHomExactSupportRestrictComparison_app_of_map
    (F : SheafOfModules.{u} (structureSheafRing S.X))
    (h : IsIso ((modulePushforward (restrictedMorphism S.i U)).map
      ((S.sheafHomExactSupportRestrictComparison U).app F))) :
    IsIso ((S.sheafHomExactSupportRestrictComparison U).app F) :=
  isIso_of_reflects_iso _ (modulePushforward (restrictedMorphism S.i U))

/-- **"It suffices after `(i|_{i⁻¹U})_*`" for the underived comparison, as a 2-square.** A
natural transformation is invertible as soon as each of its components is, so the whole
comparison is invertible once its pushforward is invertible at every `𝒪_X`-module. -/
theorem isIso_sheafHomExactSupportRestrictComparison_of_map
    (h : ∀ F : SheafOfModules.{u} (structureSheafRing S.X),
      IsIso ((modulePushforward (restrictedMorphism S.i U)).map
        ((S.sheafHomExactSupportRestrictComparison U).app F))) :
    IsIso (S.sheafHomExactSupportRestrictComparison U) := by
  have := fun F => S.isIso_sheafHomExactSupportRestrictComparison_app_of_map U F (h F)
  exact NatIso.isIso_of_isIso_app _

/-- **The reduction loses nothing.** A component of the underived comparison is invertible
exactly when its pushforward along the restricted morphism is: pushforward is a functor, so the
converse of
`ClosedQuotientMorphismOfRingedSpaces.isIso_sheafHomExactSupportRestrictComparison_app_of_map`
is automatic. -/
theorem isIso_sheafHomExactSupportRestrictComparison_app_iff
    (F : SheafOfModules.{u} (structureSheafRing S.X)) :
    IsIso ((modulePushforward (restrictedMorphism S.i U)).map
        ((S.sheafHomExactSupportRestrictComparison U).app F)) ↔
      IsIso ((S.sheafHomExactSupportRestrictComparison U).app F) :=
  isIso_iff_of_reflects_iso _ (modulePushforward (restrictedMorphism S.i U))

/-! ### The reduction for the comparison on derived categories -/

/-- **"It suffices after `R(i|_{i⁻¹U})_*`" for the comparison on derived categories.** If the
image of the component of
`ClosedQuotientMorphismOfRingedSpaces.derivedSheafHomExactSupportRestrictComparison` at `K` in
`D(𝒪_X)` under derived pushforward along the restricted morphism is invertible, then that
component is invertible. -/
theorem isIso_derivedSheafHomExactSupportRestrictComparison_app_of_map
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)))
    (h : IsIso ((modulePushforward (restrictedMorphism S.i U)).mapDerivedCategory.map
      ((S.derivedSheafHomExactSupportRestrictComparison U).app K))) :
    IsIso ((S.derivedSheafHomExactSupportRestrictComparison U).app K) :=
  isIso_of_reflects_iso _ (modulePushforward (restrictedMorphism S.i U)).mapDerivedCategory

/-- **"It suffices after `R(i|_{i⁻¹U})_*`", as a 2-square.** -/
theorem isIso_derivedSheafHomExactSupportRestrictComparison_of_map
    (h : ∀ K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X)),
      IsIso ((modulePushforward (restrictedMorphism S.i U)).mapDerivedCategory.map
        ((S.derivedSheafHomExactSupportRestrictComparison U).app K))) :
    IsIso (S.derivedSheafHomExactSupportRestrictComparison U) := by
  have := fun K => S.isIso_derivedSheafHomExactSupportRestrictComparison_app_of_map U K (h K)
  exact NatIso.isIso_of_isIso_app _

/-- **The reduction loses nothing**, on derived categories. -/
theorem isIso_derivedSheafHomExactSupportRestrictComparison_app_iff
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing S.X))) :
    IsIso ((modulePushforward (restrictedMorphism S.i U)).mapDerivedCategory.map
        ((S.derivedSheafHomExactSupportRestrictComparison U).app K)) ↔
      IsIso ((S.derivedSheafHomExactSupportRestrictComparison U).app K) :=
  isIso_iff_of_reflects_iso _ (modulePushforward (restrictedMorphism S.i U)).mapDerivedCategory

/-! ### The underived comparison is an isomorphism -/


/-- **The kernel ideal of the restricted situation is the restriction of the kernel ideal.** A
function on an open `W` of `U` is killed by the comorphism of `i|_{i⁻¹U}` exactly when, read on
the corresponding open of `X`, it is killed by the comorphism of `i`. -/
theorem restrict_mem_kernelIdeal_iff (W : Opens (S.restrict U).X)
    (a : (S.restrict U).X.presheaf.obj (op W)) :
    a ∈ (S.restrict U).kernelIdeal W ↔
      (a : S.X.presheaf.obj (op ((jFun (asRingSheafedSpace S.X) U).obj W))) ∈
        S.kernelIdeal ((jFun (asRingSheafedSpace S.X) U).obj W) := by
  change (ConcreteCategory.hom ((restrictedMorphism S.i U).hom.c.app (op W))) a = 0 ↔
    (ConcreteCategory.hom (S.i.hom.c.app (op ((jFun (asRingSheafedSpace S.X) U).obj W)))) a = 0
  rw [restrictedMorphism_c_app_apply]
  exact (ConcreteCategory.bijective_of_isIso _).1.eq_iff' (map_zero _)

/-- **Local annihilation by the kernel ideal can be read in `U` or in `X`.** A section of `F|_U`
over an open `W` of `U` is locally annihilated by the kernel ideal of the restricted situation
exactly when, as a section of `F` over the corresponding open of `X`, it is locally annihilated
by the kernel ideal of `i`. -/
theorem restrict_mem_sectionsLocallyAnnihilated_iff
    (F : SheafOfModules.{u} (structureSheafRing S.X)) (W : Opens (S.restrict U).X)
    (s : ((moduleRestriction S.X U).obj F).val.obj (op W)) :
    s ∈ (S.restrict U).sectionsLocallyAnnihilatedByKernelIdeal
        ((moduleRestriction S.X U).obj F) W ↔
      (s : F.val.obj (op ((jFun (asRingSheafedSpace S.X) U).obj W))) ∈
        S.sectionsLocallyAnnihilatedByKernelIdeal F ((jFun (asRingSheafedSpace S.X) U).obj W) := by
  constructor
  · intro hs W'' hW'' a ha
    have hle : W'' ≤ U := hW''.trans
      (((jFun (asRingSheafedSpace S.X) U).monotone le_top).trans
        (Opens.isOpenEmbedding_obj_top U).le)
    have he : (jFun (asRingSheafedSpace S.X) U).obj ((Opens.map U.inclusion').obj W'') = W'' :=
      (Opens.functor_map_eq_inf U W'').trans (inf_eq_left.2 hle)
    have hW''' : (Opens.map U.inclusion').obj W'' ≤ W :=
      ((Opens.map U.inclusion').monotone hW'').trans (Opens.map_functor_eq W).le
    obtain ⟨V, hV, rfl⟩ : ∃ V, V ≤ W ∧ (jFun (asRingSheafedSpace S.X) U).obj V = W'' :=
      ⟨_, hW''', he⟩
    exact hs V hV a ((S.restrict_mem_kernelIdeal_iff U V a).2 ha)
  · intro hs W''' hW''' a ha
    exact hs _ ((jFun (asRingSheafedSpace S.X) U).monotone hW''') a
      ((S.restrict_mem_kernelIdeal_iff U W''' a).1 ha)


/-- **Evaluation at one is injective on sections**: the counit `i_* ℰom(𝒪_Z, F) ⟶ F` of
[Stacks, Tag 0A75] is injective over every open. -/
theorem counit_app_injective (F : SheafOfModules.{u} (structureSheafRing S.X)) (W : Opens S.X) :
    Function.Injective
      ((S.modulePushforwardSheafHomExactSupportAdjunction.counit.app F).val.app (op W)) := by
  intro s t hst
  apply (S.sectionsSheafHomExactSupportEquiv F W _ rfl).injective
  apply Subtype.ext
  rwa [S.sectionsSheafHomExactSupportEquiv_apply F W _ rfl s,
    S.sectionsSheafHomExactSupportEquiv_apply F W _ rfl t]

/-- The image of evaluation at one consists of sections locally annihilated by the kernel
ideal. -/
theorem counit_app_mem (F : SheafOfModules.{u} (structureSheafRing S.X)) (W : Opens S.X)
    (s : ((modulePushforward S.i).obj (S.sheafHomExactSupport.obj F)).val.obj (op W)) :
    (S.modulePushforwardSheafHomExactSupportAdjunction.counit.app F).val.app (op W) s ∈
      S.sectionsLocallyAnnihilatedByKernelIdeal F W := by
  have hp := (S.sectionsSheafHomExactSupportEquiv F W _ rfl s).prop
  rwa [S.sectionsSheafHomExactSupportEquiv_apply F W _ rfl s] at hp

/-- Every section locally annihilated by the kernel ideal is in the image of evaluation at
one. -/
theorem exists_counit_app_eq (F : SheafOfModules.{u} (structureSheafRing S.X)) (W : Opens S.X)
    (e : F.val.obj (op W)) (he : e ∈ S.sectionsLocallyAnnihilatedByKernelIdeal F W) :
    ∃ s, (S.modulePushforwardSheafHomExactSupportAdjunction.counit.app F).val.app (op W) s = e := by
  obtain ⟨t, ht⟩ := (S.sectionsSheafHomExactSupportEquiv F W _ rfl).surjective ⟨e, he⟩
  exact ⟨t, (S.sectionsSheafHomExactSupportEquiv_apply F W _ rfl t).symm.trans
    (congrArg Subtype.val ht)⟩

/-- **The pushed-forward underived comparison is an isomorphism.** By the counit equation
`sheafHomExactSupportRestrictComparison_counit`, after `(i|_{i⁻¹U})_*` and evaluation at one the
comparison becomes the inclusion of the sections of `F|_U` locally annihilated by the kernel
ideal of `i`, read in `X`, into those locally annihilated by the kernel ideal of the restricted
situation; the two sets agree (`restrict_mem_sectionsLocallyAnnihilated_iff`) and evaluation at
one is injective, so the comparison is bijective on sections. -/
theorem isIso_pushforward_sheafHomExactSupportRestrictComparison_app
    (F : SheafOfModules.{u} (structureSheafRing S.X)) :
    IsIso ((modulePushforward (restrictedMorphism S.i U)).map
      ((S.sheafHomExactSupportRestrictComparison U).app F)) := by
  have hc := S.sheafHomExactSupportRestrictComparison_counit U F
  set c := (modulePushforward (restrictedMorphism S.i U)).map
      ((S.sheafHomExactSupportRestrictComparison U).app F)
  set ε' := (S.restrictPushforwardSheafHomExactSupportAdjunction U).counit.app
          ((moduleRestriction S.X U).obj F)
  set sq := (S.pushforwardRestrictSquare U).app (S.sheafHomExactSupport.obj F)
  set ε := S.modulePushforwardSheafHomExactSupportAdjunction.counit.app F
  have hsq : IsIso sq := by
    change IsIso ((modulePushforwardRestrictIso S.i U).hom.app _)
    infer_instance
  refine Stacks.SheafOfModules.isIso_of_bijective_app c fun W => ?_
  have key : ∀ x, ε'.val.app W (c.val.app W x) =
      ((moduleRestriction S.X U).map ε).val.app W (sq.val.app W x) := fun x =>
    congrArg (fun φ => φ.val.app W x) hc
  have hε' : Function.Injective (ε'.val.app W) := (S.restrict U).counit_app_injective _ W.unop
  have hε : Function.Injective (((moduleRestriction S.X U).map ε).val.app W) :=
    S.counit_app_injective F _
  have hsqb : Function.Bijective (sq.val.app W) :=
    ConcreteCategory.bijective_of_isIso ((SheafOfModules.evaluation _ W).map sq)
  refine ⟨fun x y hxy => hsqb.1 (hε (by rw [← key, ← key, hxy])), fun t => ?_⟩
  have hm := (S.restrict U).counit_app_mem _ W.unop t
  rw [S.restrict_mem_sectionsLocallyAnnihilated_iff] at hm
  obtain ⟨s, hs⟩ := S.exists_counit_app_eq F _ _ hm
  obtain ⟨x, rfl⟩ := hsqb.2 s
  exact ⟨x, hε' ((key x).trans hs)⟩

/-- **Sheaf Hom with exact support commutes with restriction to an open subspace**:
`ℰom(𝒪_Z, F)|_{i⁻¹U} ⟶ ℰom(𝒪_{Z|_{i⁻¹U}}, F|_U)` is an isomorphism. -/
instance isIso_sheafHomExactSupportRestrictComparison_app
    (F : SheafOfModules.{u} (structureSheafRing S.X)) :
    IsIso ((S.sheafHomExactSupportRestrictComparison U).app F) :=
  S.isIso_sheafHomExactSupportRestrictComparison_app_of_map U F
    (S.isIso_pushforward_sheafHomExactSupportRestrictComparison_app U F)

/-- The underived comparison is an isomorphism of functors. -/
instance isIso_sheafHomExactSupportRestrictComparison :
    IsIso (S.sheafHomExactSupportRestrictComparison U) :=
  S.isIso_sheafHomExactSupportRestrictComparison_of_map U
    (S.isIso_pushforward_sheafHomExactSupportRestrictComparison_app U)


end RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces

end
