module

public import StacksFrontier.AlgebraicGeometry.Quot.HilbertFunctorClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.HilbertPresheafCanonicalModel
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientPullbackLeLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceIdealQuasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A closed immersion induces a closed immersion of Hilbert functors (Stacks 0DPF)

Let `π : X ⟶ Y` be a closed immersion of algebraic spaces over an algebraic space `A`, with
`Y ⟶ A` of finite presentation. The induced monomorphism `Hilb_{X/A} ⟶ Hilb_{Y/A}`
(`AlgebraicGeometry.Space.hilbertModelMapOfClosed`), whose image consists of the families
`Z ⊆ Y_T` contained in `X_T`, is a closed immersion.

## The argument

For a family `Z ⊆ Y_T` over a scheme `T`, let `𝓘_{X_T}` be the ideal sheaf of `X_T ⊆ Y_T` and
`𝒪_{Y_T} ⟶ 𝒪_Z` the quotient the family determines (Stacks 0D00). After a base change
`T' ⟶ T` the family lands in `X_{T'}` exactly when `𝓘_{X_{T'}} ⊆ 𝓘_{Z_{T'}}` (Stacks 03MB);
both ideal sheaves are the images of the pulled-back ideal sheaves (Stacks 04CQ, as in the
naturality of Stacks 0D00), so this is the vanishing of the pullback of the composite
`𝓘_{X_T} ⟶ 𝒪_{Y_T} ⟶ 𝒪_Z`, and by Stacks 083M the locus of that vanishing is a closed subspace
of `T`, because `𝒪_Z` is of finite presentation, flat over `T` and has support proper over `T`.
This is `AlgebraicGeometry.Space.QuotSituation.exists_isClosedSubspace_quotientPullback_le`
applied to the defining ideal of `X_T` and the kernel of the quotient of the family.
Equivalently, one may argue through Stacks 0DP5, for the surjection `𝒪_Y ⟶ π_*𝒪_X`.

## Main results

* `AlgebraicGeometry.Space.exists_isClosedSubspace_baseChange_le_range_iff`: the locus of `T`
  over which a family of `Y/A` lands in `X` is a closed subspace of `T`.
* `AlgebraicGeometry.Space.isClosedImmersion_hilbertModelMapOfClosed`: **Stacks 0DPF**, read in
  any models of the two Hilbert functors.
* `AlgebraicGeometry.Space.isClosedImmersion_hilbertModelMapOfClosed_canonical`: **Stacks 0DPF**,
  read in the canonical models `AlgebraicGeometry.Space.HilbertPresheafModel.canonical`, which
  exist for every morphism of algebraic spaces.

## Implementation notes

**Hypotheses.** The source assumes `X` and `Y` separated and of finite presentation over `A`.
Only finite presentation of `Y ⟶ A` is used: it is the standing assumption of the Quot functor
of `𝒪_Y/Y/A` through which Stacks 0D00 and Stacks 083M are applied. The remaining assumptions are
what makes the two Hilbert functors algebraic spaces (Stacks 0D01), that is what guarantees the
existence of models of them in the universe of the site. The statement here is made for
arbitrary models (`AlgebraicGeometry.Space.HilbertPresheafModel`), so it does not need them; it
implies the source's statement for the models of Stacks 0D01, and it is also stated for the
canonical models, which exist for every morphism with nothing assumed.

## References

* [Stacks Project, Tag 0DPF](https://stacks.math.columbia.edu/tag/0DPF)
* [Stacks Project, Tag 0D00](https://stacks.math.columbia.edu/tag/0D00)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 083M](https://stacks.math.columbia.edu/tag/083M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

-- Left in place, this instance is selected ahead of `SheafOfModules.instAbelian` and leaves the
-- module universe of every subobject and cokernel below unsolved.
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Comparing the subobjects cut out by two closed subspaces -/

section DefiningIdeal

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsFinitePresentation B S hS f.hom)
  (T : SchemesOverPresheaf B S hS Y)

/-- **Stacks 03MB, read in the module of the Quot situation.** The subobject of `F_T` cut out by
a closed subspace of `X_T` is contained in the one cut out by a second closed subspace exactly
when the second closed subspace is contained in the first. -/
theorem definingIdealSubobject_le_iff
    (Z₁ Z₂ : ClosedSubspaces B S hS (baseChangeSpace f (structureSheafTestScheme T)).1) :
    definingIdealSubobject f hf T Z₁ ≤ definingIdealSubobject f hf T Z₂ ↔ Z₂.1 ≤ Z₁.1 := by
  have m₁ := mono_definingIdealArrow f hf T Z₁
  have m₂ := mono_definingIdealArrow f hf T Z₂
  constructor
  · intro h
    have hcomp := @Subobject.ofMkLEMk_comp _ _ _ _ _ _ _ m₁ m₂ h
    have hmono : Mono (baseChangeModuleIsoStructureSheaf f hf T).inv :=
      @IsIso.mono_of_iso _ _ _ _ (baseChangeModuleIsoStructureSheaf f hf T).inv
        (Iso.isIso_inv (baseChangeModuleIsoStructureSheaf f hf T))
    have hι : @Subobject.ofMkLEMk _ _ _ _ _ _ _ m₁ m₂ h ≫
        (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T)) Z₂).ι =
        (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T)) Z₁).ι := by
      refine (cancel_mono (baseChangeModuleIsoStructureSheaf f hf T).inv).1 ?_
      exact (Category.assoc _ _ _).trans hcomp
    exact le_of_definingIdealSheaf_le B S hS _ Z₂ Z₁
      (Stacks.SheafOfModules.ImageSubsheaf.submodule_le_of_subobject_mk_ι_le
        (Subobject.mk_le_mk_of_comm _ hι))
  · intro h
    have hI := definingIdealSheaf_antitone B S hS _ Z₂ Z₁ h
    refine @Subobject.mk_le_mk_of_comm _ _ _ _ _ _ _ m₁ m₂
      (⟨PresheafOfModules.Submodule.homOfLE (SheafOfModules.Submodule.le_iff.mp hI)⟩ :
        (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T))
          Z₁).toSheafOfModules ⟶
        (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T))
          Z₂).toSheafOfModules) ?_
    exact (Category.assoc _
      (definingIdealSheaf B S hS (baseChangeSpace f (structureSheafTestScheme T)) Z₂).ι
      (baseChangeModuleIsoStructureSheaf f hf T).inv).symm.trans
      (congrArg (· ≫ (baseChangeModuleIsoStructureSheaf f hf T).inv) rfl)

/-- The subobject of `F_T` cut out by a closed subspace of `X_T` is quasi-coherent, being
isomorphic to the defining ideal sheaf of the closed subspace (Stacks 03MB). -/
theorem isQuasicoherentOnSite_definingIdealSubobject
    (Z : ClosedSubspaces B S hS (baseChangeSpace f (structureSheafTestScheme T)).1) :
    SheafOfModules.IsQuasicoherentOnSite
      ((definingIdealSubobject f hf T Z : Modules.{u, u} B S hS
        ((structureSheafQuotSituation f hf).space (structureSheafTestScheme T)).1
        ((structureSheafQuotSituation f hf).space (structureSheafTestScheme T)).2)) :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (@Subobject.underlyingIso _ _ _ _ (definingIdealArrow f hf T Z)
      (mono_definingIdealArrow f hf T Z)).symm
    (isQuasicoherentOnSite_definingIdealSheaf B S hS _ Z)

end DefiningIdeal

/-! ### The locus over which a family lands in the closed subspace -/

variable {X Y A : AlgebraicSpaces B S hS} {π : X ⟶ Y} {bX : X ⟶ A} {bY : Y ⟶ A}

section Locus

variable (hπ : π ≫ bY = bX) (hclosed : IsClosedImmersion B S hS π.hom)

include hπ hclosed

/-- The range of the base change of `π`, as a closed subspace of `Y_T` spelled as the Quot
situation of `𝒪_Y/Y/A` spells the base change. -/
abbrev rangeClosedSubspace (T : SchemesOverPresheaf B S hS A) :
    ClosedSubspaces B S hS (baseChangeSpace bY (structureSheafTestScheme T)).1 :=
  ⟨Subfunctor.range (schemeBaseChangeOfMap hπ T),
    isClosedSubspace_range_schemeBaseChangeOfMap hπ hclosed T⟩

/-- The inverse image of the range of the base change of `π` along a transition map of base
changes is the range of the base change of `π` to the new test scheme. -/
theorem preimageSubspace_rangeClosedSubspace {T T' : SchemesOverPresheaf B S hS A} (g : T' ⟶ T) :
    preimageSubspace B S hS (baseChangeMap bY (structureSheafTestSchemeMap g))
        (rangeClosedSubspace hπ hclosed T) =
      rangeClosedSubspace hπ hclosed T' := by
  refine Subtype.ext ?_
  show (Subfunctor.range (schemeBaseChangeOfMap hπ T)).preimage
      (baseChangeMap bY (structureSheafTestSchemeMap g)).hom =
    Subfunctor.range (schemeBaseChangeOfMap hπ T')
  rw [relativeMap_structureSheafTestSchemeMap bY g]
  exact (Subfunctor.range_eq_preimage_of_isPullback
    (isPullback_schemeBaseChangeOfMap_comm hπ g).flip).symm

/-- **The locus over which a family of `Y/A` lands in `X` is a closed subspace of the test
scheme.** For a family `Z ⊆ Y_T` over a scheme `T` lying over `A`, the morphisms `t : T' ⟶ T`
after which the family is contained in `X_{T'}` are exactly those factoring through a closed
subspace of `T` (Stacks 083M, for the composite `𝓘_{X_T} ⟶ 𝒪_{Y_T} ⟶ 𝒪_Z`). -/
@[sga "3 XI 6.1" "partial"]
theorem exists_isClosedSubspace_baseChange_le_range_iff
    (hfp : IsFinitePresentation B S hS bY.hom) {T : BigFppfOver B S hS}
    (toBase : yoneda.obj T ⟶ A.obj) (z : HilbertFamily bY (CostructuredArrow.mk toBase)) :
    ∃ W : Subfunctor (yoneda.obj T), IsClosedSubspace B S hS W ∧
      ∀ (T' : BigFppfOver B S hS) (t : T' ⟶ T),
        (z.baseChange (HilbertFamilyOver.restrict t toBase)).Z ≤
            Subfunctor.range (schemeBaseChangeOfMap hπ
              (CostructuredArrow.mk (yoneda.map t ≫ toBase))) ↔
          ∃ k : yoneda.obj T' ⟶ W.toFunctor, k ≫ W.ι = yoneda.map t := by
  obtain ⟨W, hW, hloc⟩ :=
    (structureSheafQuotSituation bY hfp).exists_isClosedSubspace_quotientPullback_le
      (T := structureSheafTestScheme (CostructuredArrow.mk toBase))
      (isQuasicoherentOnSite_definingIdealSubobject bY hfp (CostructuredArrow.mk toBase)
        (rangeClosedSubspace hπ hclosed (CostructuredArrow.mk toBase)))
      (hilbertFamilySubobject_mem bY hfp (CostructuredArrow.mk toBase) z)
  refine ⟨W, hW, fun T' t => ?_⟩
  rw [← hloc T' t]
  have e₁ := quotientPullback_subobject_definingIdealSheaf bY hfp
    (structureSheafTestSchemeMap (HilbertFamilyOver.restrict t toBase))
    (rangeClosedSubspace hπ hclosed (CostructuredArrow.mk toBase))
  have e₂ := quotientPullback_hilbertFamilySubobject bY hfp
    (HilbertFamilyOver.restrict t toBase) z
  rw [preimageSubspace_rangeClosedSubspace hπ hclosed] at e₁
  have key : definingIdealSubobject bY hfp (CostructuredArrow.mk (yoneda.map t ≫ toBase))
        (rangeClosedSubspace hπ hclosed (CostructuredArrow.mk (yoneda.map t ≫ toBase))) ≤
      hilbertFamilySubobject bY hfp (CostructuredArrow.mk (yoneda.map t ≫ toBase))
        (z.baseChange (HilbertFamilyOver.restrict t toBase)) ↔
      (z.baseChange (HilbertFamilyOver.restrict t toBase)).Z ≤
        Subfunctor.range (schemeBaseChangeOfMap hπ
          (CostructuredArrow.mk (yoneda.map t ≫ toBase))) := by
    rw [hilbertFamilySubobject_eq_definingIdealSubobject]
    exact definingIdealSubobject_le_iff bY hfp _ _ _
  rw [← e₁, ← e₂] at key
  exact key.symm

end Locus

/-! ### Stacks 0DPF -/

section Model

variable (hπ : π ≫ bY = bX) (hclosed : IsClosedImmersion B S hS π.hom)

include hπ hclosed

/-- Let `π : X ⟶ Y` be a closed immersion of algebraic spaces over an algebraic space `A`, with
`Y` of finite presentation over `A`. Then the morphism of Hilbert functors
`Hilb_{X/A} ⟶ Hilb_{Y/A}` that `π` induces is a closed immersion, read in any models of the two
Hilbert functors. -/
@[stacks 0DPF "the induced morphism is a closed immersion"]
theorem isClosedImmersion_hilbertModelMapOfClosed (hfp : IsFinitePresentation B S hS bY.hom)
    (MX : HilbertPresheafModel bX) (MY : HilbertPresheafModel bY) :
    IsClosedImmersion B S hS (hilbertModelMapOfClosed hπ hclosed MX MY) := by
  have := mono_hilbertModelMapOfClosed hπ hclosed MX MY
  apply isClosedImmersion_of_isClosedImmersion_range_preimage
  intro T q
  set Z := MY.familyEquiv T (yonedaEquiv q) with hZ
  obtain ⟨W, hW, hloc⟩ :=
    exists_isClosedSubspace_baseChange_le_range_iff hπ hclosed hfp Z.toBase Z.family
  have hEq : (Subfunctor.range (hilbertModelMapOfClosed hπ hclosed MX MY)).preimage q = W := by
    ext U g
    have hqg : q.app U g = MY.presheaf.map (Quiver.Hom.op g) (yonedaEquiv q) := by
      simpa [yonedaEquiv_apply] using NatTrans.naturality_apply q (Quiver.Hom.op g) (𝟙 T)
    show q.app U g ∈ Set.range ((hilbertModelMapOfClosed hπ hclosed MX MY).app U) ↔
      g ∈ W.obj U
    rw [hqg, mem_range_hilbertModelMapOfClosed_iff, HilbertPresheafModel.familyEquiv_map,
      Subfunctor.mem_yoneda_iff]
    exact hloc U.unop g
  exact hEq ▸ hW.2

/-- Let `π : X ⟶ Y` be a closed immersion of algebraic spaces over an algebraic space `A`, with
`Y` of finite presentation over `A`. Then `π` induces a closed immersion
`Hilb_{X/A} ⟶ Hilb_{Y/A}` of Hilbert functors: the morphism
`AlgebraicGeometry.Space.hilbertPresheafMapOfClosed`, sending a family `Z ⊆ X_T` to its image in
`Y_T`, read in the canonical models `AlgebraicGeometry.Space.HilbertPresheafModel.canonical` of
the two Hilbert functors, is a closed immersion. -/
@[stacks 0DPF "the induced morphism of the canonical Hilbert functors is a closed immersion"]
theorem isClosedImmersion_hilbertModelMapOfClosed_canonical
    (hfp : IsFinitePresentation B S hS bY.hom) :
    IsClosedImmersion B S hS (hilbertModelMapOfClosed hπ hclosed
      (HilbertPresheafModel.canonical bX) (HilbertPresheafModel.canonical bY)) :=
  isClosedImmersion_hilbertModelMapOfClosed hπ hclosed hfp _ _

end Model

end AlgebraicGeometry.Space

end
