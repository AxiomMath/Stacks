module

import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import Mathlib.CategoryTheory.Sites.CoverLifting
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HigherDirectImage.CompositeRightDerivedFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyInvertible
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ExtensionByZeroExact
public import StacksFrontier.Topology.Sheaves.Stalk.Restrict

/-!
# Excision for the local cohomology of sheaves of abelian groups

Let `T` be a subset of a topological space `X`, let `U ⊆ X` be an open subset and let
`j : U → X` be its inclusion.  Local cohomology with supports in `T` is local on `X`:

`ℋ ⁿ_T(F)|_U ≅ ℋ ⁿ_{j⁻¹T}(F|_U)`,

naturally in the sheaf of abelian groups `F`.  That is
`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologyRestrictNatIso`, and
`Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafRestrictNatIso` is the same
statement for the local cohomology *sheaves* of [Stacks, Tag 0G74], read on the ambient space
as their direct image from the closed support.

The library had this only for sheaves of **modules**, as
`Stacks.Perfect.LocalCohomologyExcision.localCohomologyRestrictNatIso`; every excision in it was
`𝒪`-linear.  The abelian statement is what a merely additive endomorphism of the coefficients —
a de Rham differential, which is `𝒪_X`-linear for no `X` — can be transported along, and it is
not a formal consequence of the module statement, an abelian sheaf not being a sheaf of modules
over anything.

This file is the abelian twin of
`StacksFrontier/AlgebraicGeometry/Perfect/SupportClosedSubset/LocalCohomologyExcision.lean` and is
built in the same three steps: excision in degree zero, the homological properties of
restriction to an open subset, and the two generic derived-functor comparisons.

## Main definitions and results

* `Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRestrictIso`: **excision in
  degree zero at one sheaf** — the subsheaf of sections of `F` supported on `T`, restricted to
  `U`, is the subsheaf of `F|_U` of sections supported on `j⁻¹T`.  Both are subgroups of the
  same group of sections over each open of `U`, and the two membership conditions agree because
  the germ of a section of `F|_U` at a point of `U` is the germ of that section in `F`:
  `Stacks.Cohomology.SupportedComplexes.mem_supportedSections_restrict_iff`.
* `Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRestrictNatIso`: **excision in
  degree zero**, as a natural isomorphism of functors.
* `Stacks.Cohomology.SupportedComplexes.sheafRestrict_additive`,
  `Stacks.Cohomology.SupportedComplexes.sheafRestrict_preservesFiniteLimits`,
  `Stacks.Cohomology.SupportedComplexes.sheafRestrict_preservesFiniteColimits` and
  `Stacks.Cohomology.SupportedComplexes.sheafRestrict_preservesInjectiveObjects`:
  **restriction of abelian sheaves to an open subset is exact and preserves injective
  objects** ([Stacks, Tag 01E1] for abelian sheaves).  Exactness is read off two adjunctions:
  `ExtensionByZero.jExtAdjunction` makes restriction a right adjoint, and
  `CategoryTheory.Functor.sheafAdjunctionCocontinuous` for the functor of images of opens — which
  is cocontinuous, being a left adjoint whose right adjoint preserves covers — makes it a left
  adjoint.  Preservation of injectives is then the general adjunction criterion applied to
  `ExtensionByZero.jExtAdjunction`, extension by zero being exact ([Stacks, Tag 01AK]).
* `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologyRestrictNatIso`: **excision for
  abelian local cohomology in every degree**, for the right derived functors of the
  supported-sections endofunctor.
* `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafPushforwardIso`: the right
  derived functors of the supported-sections endofunctor **are** the local cohomology sheaves of
  `ClosedImmersionSheaves.localCohomologySheafFunctor`, pushed forward from the closed support.
  This is the abelian analogue of
  `Stacks.Perfect.LocalCohomologyExcision.localCohomologyOnIso`, and it is what entitles the
  previous item to be read as excision for the local cohomology sheaves themselves.
* `Stacks.Cohomology.SupportedComplexes.abelianLocalCohomologySheafRestrictNatIso`: **excision
  for the abelian local cohomology sheaves of [Stacks, Tag 0G74], in the spelling
  `Stacks.Perfect.GysinAbelianSquare.abelianLocalCohomologyPushforward`** — the functor
  `F ↦ i_*ℋ ⁿ_T(F)` the abelian action of [Stacks, Tag 0G74] part (2) is a conjugation of.

## Implementation notes

**Why degree zero is an isomorphism of subobjects and nothing more.**  Over an open `V` of `U`
both sides are subgroups of the one group `F(j(V))`: the first by definition of restriction
along the functor of images of opens, the second because the sections of `F|_U` over `V` are
*literally* the sections of `F` over `j(V)`.  So the comparison is the identity on underlying
sections, and all that has to be checked is that the two support conditions cut out the same
subgroup.  That is `mem_supportedSections_restrict_iff`, which is
`TopCat.Presheaf.stalkRestrictIso_germ` — the germ at `u ∈ U` of a section of the naive
restriction is the germ at `j(u)` of the same section — together with the fact that a point of
`j(V)` is `j(u)` for a unique `u ∈ V`.

**The two adjunctions for restriction.**  Restriction to an open subset is a right adjoint and a
left adjoint, and both are needed: left exactness comes from the first, right exactness from the
second.  Mathlib's `TopologicalSpace.Opens.sheafRestrict` is the direct image along the functor
`V ↦ j(V)` on opens, so `CategoryTheory.Functor.sheafAdjunctionCocontinuous` applies to it once
that functor is known to be cocontinuous; cocontinuity is
`CategoryTheory.Adjunction.isCocontinuous_iff_coverPreserving` for the image-preimage
adjunction, the preimage functor being cover-preserving.  The instances are stated for
`TopologicalSpace.Opens.sheafRestrict` and found by `show` rather than by instance search,
because that definition is not reducible and its instance argument for continuity is the one
generated inside it.

No declaration here carries a Stacks tag.  Excision for local cohomology is not a numbered
result of the source; the tagged statements this supports are elsewhere, and the generic
homological algebra it uses is tagged where it is proved ([Stacks, Tag 015Z] and
[Stacks, Tag 01E1] for modules).

## References

* [Stacks Project, Lemma 20.34.8 (Tag 0G74)](https://stacks.math.columbia.edu/tag/0G74)
* [Stacks Project, Tag 0G6N](https://stacks.math.columbia.edu/tag/0G6N)
* [Stacks Project, Tag 01AK](https://stacks.math.columbia.edu/tag/01AK)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 015Z](https://stacks.math.columbia.edu/tag/015Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AlgebraicGeometry.SheafOfModules (supportedSections supportedSectionsSheaf
  supportedSectionsSheafι)

universe u

namespace Stacks.Cohomology.SupportedComplexes

variable {X : TopCat.{u}}

/-- **The preimage of a subset in an open subset**, with the ambient space of the result spelled
as the open subset viewed as a topological space.  Pinning that spelling is what lets the
instances for the supported-sections endofunctor on the open subset be found; `↥U` and
`↑((Opens.toTopCat X).obj U)` are definitionally equal but are different keys for instance
search. -/
abbrev preimageSubset (U : Opens X) (T : Set X) : Set ((Opens.toTopCat X).obj U) :=
  U.inclusion' ⁻¹' T

/-- **Restriction of abelian sheaves to an open subset**, with its target spelled as abelian
sheaves on the open subset viewed as a topological space.  This is Mathlib's
`TopologicalSpace.Opens.sheafRestrict`; only the spelling of the target category differs, and the
spelling is what the instances below are keyed on. -/
abbrev abelianRestrictOpen (U : Opens X) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{u} :=
  U.sheafRestrict

/-! ### Restriction of abelian sheaves to an open subset is exact -/

section Restrict

variable (U : Opens X)

/-- Restriction of abelian sheaves to an open subset is additive: on sections it is the identity,
a section over an open `V` of `U` being a section over its image in `X`. -/
instance sheafRestrict_additive : (abelianRestrictOpen U).Additive where
  map_add := by intros; rfl

/-- **Restriction of abelian sheaves to an open subset is left exact.**  It is the right adjoint
of extension by zero, `ExtensionByZero.jExtAdjunction`, so it preserves all limits. -/
instance sheafRestrict_preservesFiniteLimits :
    PreservesFiniteLimits (abelianRestrictOpen U) := by
  have := (ExtensionByZero.jExtAdjunction U).rightAdjoint_preservesLimits
  exact inferInstanceAs (PreservesFiniteLimits (ExtensionByZero.restrict U))

/-- Extension by zero is left exact, as part of [Stacks, Tag 01AK]. -/
instance jExt_preservesFiniteLimits : PreservesFiniteLimits (ExtensionByZero.jExt U) :=
  (ExtensionByZero.jExt_exactFunctor U).1

/-- Extension by zero preserves monomorphisms, being left exact. -/
instance jExt_preservesMonomorphisms : (ExtensionByZero.jExt U).PreservesMonomorphisms :=
  preservesMonomorphisms_of_preservesLimitsOfShape _

/-- **[Stacks, Tag 01E1] for abelian sheaves: restriction to an open subset preserves injective
objects.**  Restriction is the right adjoint of extension by zero, and extension by zero
preserves monomorphisms — indeed it is exact, [Stacks, Tag 01AK] — so the general adjunction
criterion applies. -/
instance sheafRestrict_preservesInjectiveObjects :
    (abelianRestrictOpen U).PreservesInjectiveObjects :=
  @Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms _ _ _ _ _ _
    (ExtensionByZero.jExtAdjunction U) (jExt_preservesMonomorphisms U)

/-- The functor `V ↦ j(V)` of images of opens along the inclusion of an open subset is
cocontinuous for the topologies of opens.  It is a left adjoint, its right adjoint being the
preimage functor, and that functor is cover-preserving. -/
instance imF_isCocontinuous : (TopCat.Presheaf.imF U).IsCocontinuous
    (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) (Opens.grothendieckTopology X) := by
  rw [(IsOpenMap.adjunction U.isOpenEmbedding.isOpenMap).isCocontinuous_iff_coverPreserving]
  exact coverPreserving_opens_map U.inclusion'

/-- **Restriction of abelian sheaves to an open subset is right exact.**  It is the direct image
along the functor of images of opens, which is both continuous and cocontinuous, so it is the
*left* adjoint of `CategoryTheory.Functor.sheafAdjunctionCocontinuous` and preserves all
colimits. -/
instance sheafRestrict_preservesFiniteColimits :
    PreservesFiniteColimits (abelianRestrictOpen U) := by
  have hc : (TopCat.Presheaf.imF U).IsContinuous
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      (Opens.grothendieckTopology X) := U.isOpenEmbedding.functor_isContinuous
  have := ((TopCat.Presheaf.imF U).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
    (Opens.grothendieckTopology X)).leftAdjoint_preservesColimits
  change PreservesFiniteColimits ((TopCat.Presheaf.imF U).sheafPushforwardContinuous
    AddCommGrpCat.{u} (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
    (Opens.grothendieckTopology X))
  infer_instance

/-- Restriction of abelian sheaves to an open subset preserves homology, being exact. -/
instance sheafRestrict_preservesHomology :
    (abelianRestrictOpen U).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- The composite of restriction with the supported-sections endofunctor of the preimage is
additive.  It is stated by hand because the generic instance for a composite is not found at this
spelling of the intermediate category. -/
instance sheafRestrict_comp_abelianSupportedSections_additive (T : Set X) :
    (abelianRestrictOpen U ⋙ abelianSupportedSections (preimageSubset U T)).Additive where
  map_add := by intros; rfl

end Restrict

/-! ### Excision in degree zero -/

section DegreeZero

variable (T : Set X) (U : Opens X)

/-- **The two support conditions on a section over an open of `U` agree.**  A section of `F` over
the image `j(V)` of an open `V` of `U` is supported on `j⁻¹T` as a section of `F|_U` exactly when
it is supported on `T` as a section of `F`: a point of `j(V)` is `j(u)` for a `u ∈ V`, and the
germ at `u` of a section of the naive restriction is the germ at `j(u)` of that section, by
`TopCat.Presheaf.stalkRestrictIso_germ`. -/
theorem mem_supportedSections_restrict_iff (F : X.Sheaf AddCommGrpCat.{u})
    (V : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ)
    (s : F.presheaf.obj (op ((TopCat.Presheaf.imF U).obj V.unop))) :
    s ∈ supportedSections (preimageSubset U T) ((abelianRestrictOpen U).obj F) V ↔
      s ∈ supportedSections T F (op ((TopCat.Presheaf.imF U).obj V.unop)) := by
  have key : ∀ (u : (Opens.toTopCat X).obj U) (hu : u ∈ V.unop),
      TopCat.Presheaf.germ ((TopCat.Presheaf.imF U).op ⋙ F.presheaf) V.unop u hu s = 0 ↔
        F.presheaf.germ ((TopCat.Presheaf.imF U).obj V.unop) (U.inclusion' u)
          ⟨u, hu, rfl⟩ s = 0 := by
    intro u hu
    have happ : (TopCat.Presheaf.stalkRestrictIso U F.presheaf u).hom
        (TopCat.Presheaf.germ ((TopCat.Presheaf.imF U).op ⋙ F.presheaf) V.unop u hu s) =
        F.presheaf.germ ((TopCat.Presheaf.imF U).obj V.unop) (U.inclusion' u) ⟨u, hu, rfl⟩ s :=
      ConcreteCategory.congr_hom
        (TopCat.Presheaf.stalkRestrictIso_germ U F.presheaf V.unop u hu) s
    rw [← happ]
    refine ⟨fun h => by rw [h]; exact map_zero _, fun h => ?_⟩
    exact (AddCommGrpCat.mono_iff_injective
      (TopCat.Presheaf.stalkRestrictIso U F.presheaf u).hom).mp inferInstance
      (h.trans (map_zero _).symm)
  refine ⟨fun hs y hy hyT => ?_, fun hs u huV huT => ?_⟩
  · obtain ⟨u, huV, rfl⟩ := hy
    exact (key u huV).1 (hs u huV hyT)
  · exact (key u huV).2 (hs _ ⟨u, huV, rfl⟩ huT)

/-- Excision in degree zero at one sheaf, in the direction out of the restriction: a section of
`F` over `j(V)` supported on `T` is a section of `F|_U` over `V` supported on `j⁻¹T`. -/
def supportedSectionsToRestrict (F : X.Sheaf AddCommGrpCat.{u}) :
    (abelianRestrictOpen U).obj (supportedSectionsSheaf T F) ⟶
      supportedSectionsSheaf (preimageSubset U T) ((abelianRestrictOpen U).obj F) :=
  ⟨{ app := fun V => AddCommGrpCat.ofHom <| AddMonoidHom.mk'
       (fun s => ⟨s.1, (mem_supportedSections_restrict_iff T U F V s.1).2 s.2⟩)
       (by intro a b; apply Subtype.ext; rfl)
     naturality := by
       intro V W i
       apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
       intro s; apply Subtype.ext; rfl }⟩

/-- Excision in degree zero at one sheaf, in the direction into the restriction. -/
def supportedSectionsFromRestrict (F : X.Sheaf AddCommGrpCat.{u}) :
    supportedSectionsSheaf (preimageSubset U T) ((abelianRestrictOpen U).obj F) ⟶
      (abelianRestrictOpen U).obj (supportedSectionsSheaf T F) :=
  ⟨{ app := fun V => AddCommGrpCat.ofHom <| AddMonoidHom.mk'
       (fun s => ⟨s.1, (mem_supportedSections_restrict_iff T U F V s.1).1 s.2⟩)
       (by intro a b; apply Subtype.ext; rfl)
     naturality := by
       intro V W i
       apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
       intro s; apply Subtype.ext; rfl }⟩

/-- **Excision in degree zero, at one abelian sheaf.**  The subsheaf of sections of `F` supported
on `T`, restricted to the open subset `U`, is the subsheaf of `F|_U` of sections supported on
`j⁻¹T`.  Both are subgroups of the same group of sections over each open of `U` and the
isomorphism is the identity on sections; the content is
`mem_supportedSections_restrict_iff`. -/
def abelianSupportedSectionsRestrictIso (F : X.Sheaf AddCommGrpCat.{u}) :
    (abelianRestrictOpen U).obj (supportedSectionsSheaf T F) ≅
      supportedSectionsSheaf (preimageSubset U T) ((abelianRestrictOpen U).obj F) where
  hom := supportedSectionsToRestrict T U F
  inv := supportedSectionsFromRestrict T U F
  hom_inv_id := by
    apply CategoryTheory.Sheaf.hom_ext; apply NatTrans.ext; funext V
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    intro s; apply Subtype.ext; rfl
  inv_hom_id := by
    apply CategoryTheory.Sheaf.hom_ext; apply NatTrans.ext; funext V
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    intro s; apply Subtype.ext; rfl

/-- The comparison of degree zero is compatible with the two inclusions into `F|_U`: it is the
identity on sections, so composing it with the inclusion of the subsheaf of sections supported on
`j⁻¹T` is the restriction of the inclusion of the subsheaf of sections supported on `T`. -/
theorem abelianSupportedSectionsRestrictIso_hom_ι (F : X.Sheaf AddCommGrpCat.{u}) :
    (abelianSupportedSectionsRestrictIso T U F).hom ≫
        supportedSectionsSheafι (preimageSubset U T) ((abelianRestrictOpen U).obj F) =
      (abelianRestrictOpen U).map (supportedSectionsSheafι T F) := by
  apply CategoryTheory.Sheaf.hom_ext; apply NatTrans.ext; funext V
  apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
  intro s; rfl

/-- **Excision in degree zero for abelian sheaves**, as a natural isomorphism

`H_T(-)|_U ≅ H_{j⁻¹T}((-)|_U)`

of functors from abelian sheaves on `X` to abelian sheaves on `U`.  Naturality holds because the
comparison is the identity on sections and both functors act on a morphism by its action on the
ambient sections. -/
def abelianSupportedSectionsRestrictNatIso :
    abelianSupportedSections T ⋙ abelianRestrictOpen U ≅
      abelianRestrictOpen U ⋙ abelianSupportedSections (preimageSubset U T) :=
  NatIso.ofComponents (fun F => abelianSupportedSectionsRestrictIso T U F) (by
    intro F G f
    apply CategoryTheory.Sheaf.hom_ext; apply NatTrans.ext; funext V
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    intro s; apply Subtype.ext; rfl)

end DegreeZero

/-! ### Excision in every degree -/

section Derived

variable (T : Set X) (U : Opens X)

/-- **Excision for abelian local cohomology, in every degree.**  For a subset `T` of a
topological space `X`, an open subset `U ⊆ X` and a degree `n`, the right derived functors of the
subsheaf of sections supported on `T` satisfy

`ℋ ⁿ_T(F)|_U ≅ ℋ ⁿ_{j⁻¹T}(F|_U)`,

naturally in the abelian sheaf `F`.  No closedness assumption on `T` is needed.

The proof is the standard one: `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` moves the
restriction out of the derived functor, using only that restriction is exact, and
`Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso` ([Stacks, Tag 015Z]) moves it
back in, using that restriction is exact and preserves injective objects.  The mathematical
content is therefore the degree-zero statement
`abelianSupportedSectionsRestrictNatIso` together with
`sheafRestrict_preservesInjectiveObjects`. -/
def abelianLocalCohomologyRestrictNatIso (n : ℕ) :
    (abelianSupportedSections T).rightDerived n ⋙ abelianRestrictOpen U ≅
      abelianRestrictOpen U ⋙ (abelianSupportedSections (preimageSubset U T)).rightDerived n :=
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso (abelianSupportedSections T)
      (abelianRestrictOpen U)
      (abelianRestrictOpen U ⋙ abelianSupportedSections (preimageSubset U T))
      (abelianSupportedSectionsRestrictNatIso T U) n ≪≫
    Stacks.Cohomology.CompositeRightDerived.compRightDerivedNatIso
      (abelianRestrictOpen U) (abelianSupportedSections (preimageSubset U T)) n

end Derived

/-! ### This is excision for the local cohomology sheaves of Tag 0G74 -/

section Sheaves

variable (T : Set X) (U : Opens X)

/-- Pushforward of abelian sheaves along the inclusion of a closed subset is exact
([Stacks, Tag 00AG]). -/
theorem abelianClosedPushforward_preservesFiniteLimits (hT : IsClosed T) :
    PreservesFiniteLimits (abelianClosedPushforward T) :=
  Stacks.ClosedImmersion.preservesFiniteLimits_closedInclusionPushforward
    (ClosedImmersionSheaves.closedSubsetInclusion T) hT.isClosedEmbedding_subtypeVal

/-- Pushforward of abelian sheaves along the inclusion of a closed subset is right exact. -/
theorem abelianClosedPushforward_preservesFiniteColimits (hT : IsClosed T) :
    PreservesFiniteColimits (abelianClosedPushforward T) :=
  Stacks.ClosedImmersion.preservesFiniteColimits_closedInclusionPushforward
    (ClosedImmersionSheaves.closedSubsetInclusion T) hT.isClosedEmbedding_subtypeVal

/-- Pushforward of abelian sheaves along the inclusion of a closed subset preserves homology,
being exact. -/
theorem abelianClosedPushforward_preservesHomology (hT : IsClosed T) :
    (abelianClosedPushforward T).PreservesHomology :=
  let _ := abelianClosedPushforward_preservesFiniteLimits T hT
  let _ := abelianClosedPushforward_preservesFiniteColimits T hT
  Functor.preservesHomologyOfExact _

/-- **The right derived functors of the supported-sections endofunctor are the abelian local
cohomology sheaves of [Stacks, Tag 0G74], pushed forward from the closed support.**  For a closed
`T`, deriving the subsheaf of sections supported on `T` is deriving the local cohomology sheaf on
`T` and pushing it forward to `X`: the two degree-zero functors agree by
`Stacks.Cohomology.SupportedComplexes.abelianSupportedSectionsRealizedCompPushforwardIso`, and
the direct image along the inclusion of a closed subset is exact, so it commutes with right
derived functors.

This is the abelian analogue of `Stacks.Perfect.LocalCohomologyExcision.localCohomologyOnIso`,
and it is what entitles `abelianLocalCohomologyRestrictNatIso` to be read as excision for the
local cohomology sheaves themselves rather than for a functor that merely agrees with them in
degree zero. -/
def abelianLocalCohomologySheafPushforwardIso (hT : IsClosed T) (n : ℕ) :
    ClosedImmersionSheaves.localCohomologySheafFunctor T hT n ⋙ abelianClosedPushforward T ≅
      (abelianSupportedSections T).rightDerived n :=
  letI := abelianClosedPushforward_preservesFiniteLimits T hT
  letI := abelianClosedPushforward_preservesFiniteColimits T hT
  letI := abelianClosedPushforward_preservesHomology T hT
  Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
    (abelianSupportedSectionsRealized T hT) (abelianClosedPushforward T)
    (abelianSupportedSections T) (abelianSupportedSectionsRealizedCompPushforwardIso T hT) n

/-- **Excision for the abelian local cohomology sheaves of [Stacks, Tag 0G74].**  In the spelling
`Stacks.Perfect.GysinAbelianSquare.abelianLocalCohomologyPushforward` — the local cohomology sheaf
on the closed subset, pushed forward to the ambient space, which is the functor the abelian action
of [Stacks, Tag 0G74] part (2) is a conjugation of — local cohomology with supports in a closed
`T` is local on `X`:

`(i_*ℋ ⁿ_T(F))|_U ≅ i'_*ℋ ⁿ_{j⁻¹T}(F|_U)`,

naturally in the abelian sheaf `F`.  It is `abelianLocalCohomologyRestrictNatIso` conjugated by
`abelianLocalCohomologySheafPushforwardIso` on `X` and on `U`. -/
def abelianLocalCohomologySheafRestrictNatIso (hT : IsClosed T)
    (hTU : IsClosed (preimageSubset U T)) (n : ℕ) :
    (ClosedImmersionSheaves.localCohomologySheafFunctor T hT n ⋙
          abelianClosedPushforward T) ⋙ abelianRestrictOpen U ≅
      abelianRestrictOpen U ⋙
        (ClosedImmersionSheaves.localCohomologySheafFunctor (preimageSubset U T) hTU n ⋙
          abelianClosedPushforward (preimageSubset U T)) :=
  Functor.isoWhiskerRight (abelianLocalCohomologySheafPushforwardIso T hT n)
      (abelianRestrictOpen U) ≪≫
    abelianLocalCohomologyRestrictNatIso T U n ≪≫
      Functor.isoWhiskerLeft (abelianRestrictOpen U)
        (abelianLocalCohomologySheafPushforwardIso (preimageSubset U T) hTU n).symm

end Sheaves

end Stacks.Cohomology.SupportedComplexes

end
