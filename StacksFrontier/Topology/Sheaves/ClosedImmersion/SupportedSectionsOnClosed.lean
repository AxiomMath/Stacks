module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianPushforwardExact
public import StacksFrontier.Topology.Sheaves.Modules.Support
import StacksCore.Tactic.StacksAttribute

/-!
# Sections supported on a closed subset, as a sheaf on that subset

Let `Z` be a closed subset of a topological space `X` and let `i : Z → X` be the inclusion.
For an abelian sheaf `F` on `X`, the subsheaf of sections supported on `Z` is pushed forward
from `Z`: pushforward along a closed inclusion is fully faithful, and its essential image is
exactly the sheaves whose support lies in `Z` (Stacks 01AX), which the supported-sections
subsheaf satisfies by construction. Choosing a preimage functorially realizes supported
sections as a functor into abelian sheaves on `Z`, and that functor is left exact.

The realization is moreover right adjoint to pushforward, so pushforward along a closed
inclusion preserves all colimits.

## Main definitions

* `ClosedImmersionSheaves.supportedSectionsFunctor`: the supported-sections endofunctor on
  abelian sheaves on `X`.
* `ClosedImmersionSheaves.factorToSupportedSections`: the factorisation of a morphism into
  `F` whose germs vanish off `Z` through the supported-sections subsheaf.
* `ClosedImmersionSheaves.supportedSectionsOnClosedFunctor`: its realization as a functor
  into abelian sheaves on the closed subset `Z`.

## Main results

* `ClosedImmersionSheaves.supportedSectionsSheaf_mem_closedInclusionPushforward_essImage`:
  the supported-sections sheaf lies in the essential image of pushforward from `Z`.
* `ClosedImmersionSheaves.supportedSectionsSheaf_maximal`: the supported-sections sheaf is
  the largest abelian subsheaf of `F` whose support is contained in `Z`.
* `ClosedImmersionSheaves.supportedSectionsOnClosedFunctor_comp_pushforward_iso`: pushing the
  realization forward recovers the supported-sections functor.
* `ClosedImmersionSheaves.supportedSectionsOnClosedFunctor_leftExact`: the realization is
  left exact.
* `ClosedImmersionSheaves.closedInclusionPushforward_supportedSectionsOnClosedFunctor_adjunction`:
  pushforward from `Z` is left adjoint to the realization.
* `ClosedImmersionSheaves.closedInclusionPushforward_preservesColimits`: consequently
  pushforward along a closed inclusion preserves arbitrary colimits.

## Implementation notes

The realization on `Z` is not an equality but a choice: it is obtained by factoring the
supported-sections functor through the essential image of the fully faithful pushforward,
using Mathlib's `CategoryTheory.Functor.essImage.liftFunctor`. Its defining property is
therefore recorded by the natural isomorphism
`supportedSectionsOnClosedFunctor_comp_pushforward_iso` after pushforward, not by an equation
between chosen objects; everything downstream is stated through that isomorphism. Left
exactness is deduced from left exactness of the supported-sections endofunctor by reflection
along pushforward, which is exact and fully faithful.

The adjunction is built from its hom-set bijection rather than from a unit and a counit. The
left adjoint is fully faithful, so a map `P A ⟶ B` is determined by a map `A ⟶ R B`; the
bijection factors a map out of `P A` through the supported-sections subsheaf, which is
possible because the stalks of `P A` vanish off `Z`, and then transports along the
realization isomorphism.

Stacks 01AY is covered by several declarations, here and elsewhere: that `H_Z(F)` is an
abelian subsheaf of `F` is `AlgebraicGeometry.SheafOfModules.supportedSectionsSubsheaf`,
while its maximality among abelian subsheaves supported in `Z`, its realization as an
abelian sheaf on `Z`, and the left exactness of that realization are the declarations tagged
`01AY` below.

## References

* [Stacks Project, Remark 17.5.4 (Tag 01AY)](https://stacks.math.columbia.edu/tag/01AY)
* [Stacks Project, Lemma 17.5.6 (Tag 01AZ)](https://stacks.math.columbia.edu/tag/01AZ)
* [Stacks Project, Tag 01AX](https://stacks.math.columbia.edu/tag/01AX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace
open AlgebraicGeometry.SheafOfModules (supportedSectionsSheaf supportedSectionsSheafι
  supportedSectionsSheafι_app mem_supportedSections_iff)

universe u

namespace ClosedImmersionSheaves

/-- The inclusion of a closed subset, as a morphism of topological spaces. -/
noncomputable abbrev closedSubsetInclusion {X : TopCat.{u}} (Z : Set X) :
    TopCat.of Z ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- If a monomorphism of sheaves sends a section to one with vanishing germ at `x`, the germ of
the section at `x` already vanishes. -/
private theorem germ_eq_zero_of_germ_app_eq_zero {X : TopCat.{u}}
    {A F : X.Sheaf AddCommGrpCat.{u}} (f : A ⟶ F) [Mono f] {U : (Opens X)ᵒᵖ}
    (s : A.presheaf.obj U) {x : X} (hx : x ∈ unop U)
    (h : F.presheaf.germ (unop U) x hx (f.hom.app U s) = 0) :
    A.presheaf.germ (unop U) x hx s = 0 := by
  apply (AddCommGrpCat.mono_iff_injective _).mp (Presheaf.stalk_mono_of_mono f x)
  rw [Presheaf.stalkFunctor_map_germ_apply, h]
  exact (map_zero _).symm

/-- **Stacks 01AY.** For a closed subset `Z`, the sheaf of sections supported on `Z` is, up
to isomorphism, pushed forward from an abelian sheaf on `Z`. -/
@[stacks 01AY "realization on Z"]
theorem supportedSectionsSheaf_mem_closedInclusionPushforward_essImage
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z) (F : X.Sheaf AddCommGrpCat.{u}) :
    (closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z)).essImage
      (supportedSectionsSheaf Z F) := by
  apply (Stacks.ClosedImmersion.essImage_closedInclusionPushforward_iff_support_subset
    (closedSubsetInclusion Z) hZ.isClosedEmbedding_subtypeVal
    (supportedSectionsSheaf Z F)).2
  intro x hx
  by_contra hxZ
  apply hx
  apply AddCommGrpCat.isZero_of_iff_subsingleton.mpr
  refine subsingleton_of_forall_eq 0 fun t ↦ ?_
  rcases (supportedSectionsSheaf Z F).presheaf.exists_germ_eq t with ⟨U, hxU, s, rfl⟩
  refine germ_eq_zero_of_germ_app_eq_zero (supportedSectionsSheafι Z F) s hxU ?_
  simpa [supportedSectionsSheafι_app] using
    (mem_supportedSections_iff Z F (op U) s.val).mp s.property x hxU
      (fun h => hxZ ⟨⟨x, h⟩, rfl⟩)

/-- Taking sections supported on `Z`, functorially in an abelian sheaf. -/
@[implicit_reducible]
noncomputable def supportedSectionsFunctor {X : TopCat.{u}} (Z : Set X) :
    X.Sheaf AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u} where
  obj F := supportedSectionsSheaf Z F
  map {F G} f := ⟨{
    app := fun U ↦ AddCommGrpCat.ofHom <| AddMonoidHom.mk'
      (fun s ↦ ⟨f.hom.app U s.1, by
        intro x hx hxZ
        rw [← Presheaf.stalkFunctor_map_germ_apply, s.2 x hx hxZ]
        exact map_zero _⟩)
      (fun _ _ ↦ by ext; simp)
    naturality := fun _ _ i ↦ by
      ext s
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (f.hom.naturality i) s.1 }⟩
  map_id F := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    rfl
  map_comp f g := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    rfl

/-- The functor of sections supported on `Z` sends `F` to `supportedSectionsSheaf Z F`. -/
@[simp]
theorem supportedSectionsFunctor_obj {X : TopCat.{u}} (Z : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) :
    (supportedSectionsFunctor Z).obj F = supportedSectionsSheaf Z F :=
  rfl

private theorem supportedSectionsFunctor_additive {X : TopCat.{u}} (Z : Set X) :
    (supportedSectionsFunctor Z).Additive where
  map_add := by
    intro F G f g
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    rfl

/-- A morphism into `F` whose composites with every germ outside `Z` vanish factors through
the supported-sections subsheaf. -/
noncomputable def factorToSupportedSections {X : TopCat.{u}} (Z : Set X)
    {A F : X.Sheaf AddCommGrpCat.{u}} (f : A ⟶ F)
    (hf : ∀ (U : (Opens X)ᵒᵖ) (s : A.presheaf.obj U) (x : X)
      (hx : x ∈ unop U), x ∉ Z →
        F.presheaf.germ (unop U) x hx (f.hom.app U s) = 0) :
    A ⟶ supportedSectionsSheaf Z F := by
  refine ⟨{
    app := fun U ↦ AddCommGrpCat.ofHom <| AddMonoidHom.mk'
      (fun s ↦ ⟨f.hom.app U s, hf U s⟩)
      (fun _ _ ↦ by ext; simp)
    naturality := fun _ _ i ↦ by
      ext s
      apply Subtype.ext
      exact ConcreteCategory.congr_hom (f.hom.naturality i) s }⟩

/-- **Stacks 01AY.** The sheaf of sections supported on `Z` is the largest abelian subsheaf
of `F` whose support is contained in `Z`: every abelian subsheaf of `F` supported in `Z`
factors through it, and the factorisation is unique. -/
@[stacks 01AY "largest abelian subsheaf supported in Z"]
theorem supportedSectionsSheaf_maximal {X : TopCat.{u}} (Z : Set X)
    {A F : X.Sheaf AddCommGrpCat.{u}} (f : A ⟶ F) [Mono f]
    (hA : Stacks.AbelianSheaf.support A ⊆ Z) :
    ∃! g : A ⟶ supportedSectionsSheaf Z F, g ≫ supportedSectionsSheafι Z F = f := by
  have hf : ∀ (U : (Opens X)ᵒᵖ) (s : A.presheaf.obj U) (x : X)
      (hx : x ∈ unop U), x ∉ Z →
        F.presheaf.germ (unop U) x hx (f.hom.app U s) = 0 := by
    intro U s x hx hxZ
    have hzero : IsZero (A.presheaf.stalk x) := by
      by_contra hne
      exact hxZ (hA hne)
    have hs : A.presheaf.germ (unop U) x hx s = 0 :=
      (AddCommGrpCat.isZero_iff_subsingleton.mp hzero).elim _ _
    rw [← Presheaf.stalkFunctor_map_germ_apply (unop U) x hx f.hom s, hs]
    exact map_zero _
  have hfac : factorToSupportedSections Z f hf ≫ supportedSectionsSheafι Z F = f := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    rfl
  exact ⟨factorToSupportedSections Z f hf, hfac,
    fun _ hg ↦ (cancel_mono (supportedSectionsSheafι Z F)).mp (hg.trans hfac.symm)⟩

private theorem supportedSectionsSheafι_naturality {X : TopCat.{u}} (Z : Set X)
    {F G : X.Sheaf AddCommGrpCat.{u}} (f : F ⟶ G) :
    (supportedSectionsFunctor Z).map f ≫ supportedSectionsSheafι Z G =
      supportedSectionsSheafι Z F ≫ f := by
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  rfl

@[sga "4 V 6.3" "special case"]
private theorem supportedSectionsFunctor_leftExact {X : TopCat.{u}} (Z : Set X) :
    leftExactFunctor (X.Sheaf AddCommGrpCat.{u}) (X.Sheaf AddCommGrpCat.{u})
      (supportedSectionsFunctor Z) := by
  rw [leftExactFunctor_iff]
  have := supportedSectionsFunctor_additive Z
  apply ((Functor.preservesFiniteLimits_tfae (supportedSectionsFunctor Z)).out 2 4).mp
  intro S hS
  have : Mono S.f := hS.2
  let hker := hS.1.fIsKernel
  have hkcomp {A : X.Sheaf AddCommGrpCat.{u}}
      (k : A ⟶ supportedSectionsSheaf Z S.X₂)
      (hk : k ≫ (supportedSectionsFunctor Z).map S.g = 0) :
      (k ≫ supportedSectionsSheafι Z S.X₂) ≫ S.g = 0 := by
    rw [Category.assoc, ← supportedSectionsSheafι_naturality Z S.g,
      ← Category.assoc, hk, zero_comp]
  have hfac {A : X.Sheaf AddCommGrpCat.{u}}
      (k : A ⟶ supportedSectionsSheaf Z S.X₂)
      (hk : k ≫ (supportedSectionsFunctor Z).map S.g = 0) :
      (hker.lift (KernelFork.ofι (k ≫ supportedSectionsSheafι Z S.X₂)
        (hkcomp k hk))) ≫ S.f = k ≫ supportedSectionsSheafι Z S.X₂ := by
    simpa [Fork.ι] using hker.fac
      (KernelFork.ofι (k ≫ supportedSectionsSheafι Z S.X₂) (hkcomp k hk))
      WalkingParallelPair.zero
  let hliftData {A : X.Sheaf AddCommGrpCat.{u}}
      (k : A ⟶ supportedSectionsSheaf Z S.X₂)
      (hk : k ≫ (supportedSectionsFunctor Z).map S.g = 0) :
      {q : A ⟶ supportedSectionsSheaf Z S.X₁ //
        q ≫ supportedSectionsSheafι Z S.X₁ =
          hker.lift (KernelFork.ofι (k ≫ supportedSectionsSheafι Z S.X₂)
            (hkcomp k hk))} := by
    let l : A ⟶ S.X₁ := hker.lift (KernelFork.ofι (k ≫ supportedSectionsSheafι Z S.X₂)
      (hkcomp k hk))
    have hf : ∀ (U : (Opens X)ᵒᵖ) (s : A.presheaf.obj U) (x : X)
        (hx : x ∈ unop U), x ∉ Z →
          S.X₁.presheaf.germ (unop U) x hx (l.hom.app U s) = 0 := by
      intro U s x hx hxZ
      have heq : S.f.hom.app U (l.hom.app U s) = (k.hom.app U s).val := by
        have hl' : l.hom ≫ S.f.hom = k.hom ≫ (supportedSectionsSheafι Z S.X₂).hom :=
          congrArg (fun q => q.hom) (hfac k hk)
        simpa [supportedSectionsSheafι_app] using
          ConcreteCategory.congr_hom (NatTrans.congr_app hl' U) s
      refine germ_eq_zero_of_germ_app_eq_zero S.f _ hx ?_
      rw [heq]
      exact (k.hom.app U s).property x hx hxZ
    exact ⟨factorToSupportedSections Z l hf, by
      apply CategoryTheory.Sheaf.hom_ext
      ext U s
      rfl⟩
  have hlim : IsLimit (KernelFork.ofι
      ((supportedSectionsFunctor Z).map S.f)
      (show ((supportedSectionsFunctor Z).map S.f) ≫
        ((supportedSectionsFunctor Z).map S.g) = 0 by
          rw [← Functor.map_comp, S.zero, Functor.map_zero])) := by
    apply KernelFork.IsLimit.ofι
      ((supportedSectionsFunctor Z).map S.f) _
      (fun {A} k hk ↦ (hliftData k hk).1)
      (fun {A} k hk ↦ by
        beta_reduce
        apply (cancel_mono (supportedSectionsSheafι Z S.X₂)).mp
        rw [Category.assoc, supportedSectionsSheafι_naturality Z S.f, ← Category.assoc,
          (hliftData k hk).2, hfac k hk])
      (fun {A} k hk m hm ↦ by
        beta_reduce
        apply (cancel_mono (supportedSectionsSheafι Z S.X₁)).mp
        apply (cancel_mono S.f).mp
        rw [(hliftData k hk).2, hfac k hk, Category.assoc,
          ← supportedSectionsSheafι_naturality Z S.f, ← Category.assoc, hm])
  exact ⟨ShortComplex.exact_of_f_is_kernel _ hlim, Fork.IsLimit.mono hlim⟩

/-- The supported-sections functor, regarded as taking values in abelian sheaves on the
closed subspace `Z`. -/
@[implicit_reducible, stacks 01AY "realization on Z"]
noncomputable def supportedSectionsOnClosedFunctor {X : TopCat.{u}}
    (Z : Set X) (hZ : IsClosed Z) :
    X.Sheaf AddCommGrpCat.{u} ⥤ (TopCat.of Z).Sheaf AddCommGrpCat.{u} := by
  letI : (closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z)).Full :=
    closedInclusion_pushforward_full _ _ _ hZ.isClosedEmbedding_subtypeVal
  letI : (closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z)).Faithful :=
    closedInclusion_pushforward_faithful _ _ _ hZ.isClosedEmbedding_subtypeVal
  exact Functor.essImage.liftFunctor (supportedSectionsFunctor Z)
    (closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z))
    (supportedSectionsSheaf_mem_closedInclusionPushforward_essImage Z hZ)

/-- Pushforward of the realization on the closed subspace is naturally isomorphic to the
sheaf of supported sections. -/
@[stacks 01AY "realization on Z"]
noncomputable def supportedSectionsOnClosedFunctor_comp_pushforward_iso
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z) :
    supportedSectionsOnClosedFunctor Z hZ ⋙
        closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z) ≅
      supportedSectionsFunctor Z := by
  letI : (closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z)).Full :=
    closedInclusion_pushforward_full _ _ _ hZ.isClosedEmbedding_subtypeVal
  letI : (closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z)).Faithful :=
    closedInclusion_pushforward_faithful _ _ _ hZ.isClosedEmbedding_subtypeVal
  exact Functor.essImage.liftFunctorCompIso
    (G := supportedSectionsFunctor Z)
    (F := closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z))
    (supportedSectionsSheaf_mem_closedInclusionPushforward_essImage Z hZ)

/-- **Stacks 01AY.** Taking sections supported on a closed subset, viewed as an abelian sheaf
on that subset, is left exact. -/
@[stacks 01AY "left exact functor Ab(X) → Ab(Z)", sga "4 V 6.3" "special case"]
theorem supportedSectionsOnClosedFunctor_leftExact {X : TopCat.{u}}
    (Z : Set X) (hZ : IsClosed Z) :
    leftExactFunctor (X.Sheaf AddCommGrpCat.{u})
      ((TopCat.of Z).Sheaf AddCommGrpCat.{u})
      (supportedSectionsOnClosedFunctor Z hZ) := by
  rw [leftExactFunctor_iff]
  let F := closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z)
  let G := supportedSectionsOnClosedFunctor Z hZ
  have hF : exactFunctor ((TopCat.of Z).Sheaf AddCommGrpCat.{u})
      (X.Sheaf AddCommGrpCat.{u}) F :=
    Stacks.ClosedImmersion.exactFunctor_closedInclusionPushforward _
      hZ.isClosedEmbedding_subtypeVal
  have : PreservesFiniteLimits F := hF.1
  have : F.Full := closedInclusion_pushforward_full _ _ _ hZ.isClosedEmbedding_subtypeVal
  have : F.Faithful := closedInclusion_pushforward_faithful _ _ _ hZ.isClosedEmbedding_subtypeVal
  have : F.ReflectsIsomorphisms :=
    Functor.FullyFaithful.reflectsIsomorphisms (Functor.FullyFaithful.ofFullyFaithful F)
  have : PreservesFiniteLimits (supportedSectionsFunctor Z) :=
    supportedSectionsFunctor_leftExact Z
  have : PreservesFiniteLimits (G ⋙ F) :=
    preservesFiniteLimits_of_natIso
      (supportedSectionsOnClosedFunctor_comp_pushforward_iso Z hZ).symm
  exact preservesFiniteLimits_of_reflects_of_preserves G F

/-- **Stacks 01AZ, adjunction.** Pushforward from a closed subset is left adjoint to the
functor of sections supported on that subset. -/
@[stacks 01AZ "adjunction"]
noncomputable def closedInclusionPushforward_supportedSectionsOnClosedFunctor_adjunction
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z) :
    closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z) ⊣
      supportedSectionsOnClosedFunctor Z hZ := by
  let P := closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z)
  let R := supportedSectionsOnClosedFunctor Z hZ
  let S := supportedSectionsFunctor Z
  let ρ := supportedSectionsOnClosedFunctor_comp_pushforward_iso Z hZ
  letI : P.Full := closedInclusion_pushforward_full _ _ _ hZ.isClosedEmbedding_subtypeVal
  letI : P.Faithful := closedInclusion_pushforward_faithful _ _ _ hZ.isClosedEmbedding_subtypeVal
  let ff := Functor.FullyFaithful.ofFullyFaithful P
  let factor {A : (TopCat.of Z).Sheaf AddCommGrpCat.{u}} {B : X.Sheaf AddCommGrpCat.{u}}
      (f : P.obj A ⟶ B) : P.obj A ⟶ supportedSectionsSheaf Z B :=
    factorToSupportedSections Z f fun U s x hx hxZ ↦ by
      have hs : (P.obj A).presheaf.germ (unop U) x hx s = 0 :=
        (AddCommGrpCat.isZero_iff_subsingleton.mp
          (closedInclusion_pushforward_stalk_isZero_of_not_mem_range
            (TopCat.of Z) X (closedSubsetInclusion Z)
            hZ.isClosedEmbedding_subtypeVal A x (by simpa using hxZ))).elim _ _
      rw [← Presheaf.stalkFunctor_map_germ_apply (unop U) x hx f.hom s, hs]
      exact map_zero _
  have factor_comp {A B} (f : P.obj A ⟶ B) : factor f ≫ supportedSectionsSheafι Z B = f := by
    apply CategoryTheory.Sheaf.hom_ext
    ext U s
    rfl
  let homEquiv (A : (TopCat.of Z).Sheaf AddCommGrpCat.{u}) (B : X.Sheaf AddCommGrpCat.{u}) :
      (P.obj A ⟶ B) ≃ (A ⟶ R.obj B) := {
    toFun := fun f => ff.preimage (factor f ≫ (ρ.app B).inv)
    invFun := fun g => P.map g ≫ (ρ.app B).hom ≫ supportedSectionsSheafι Z B
    left_inv f := by
      change P.map (ff.preimage (factor f ≫ (ρ.app B).inv)) ≫
        (ρ.app B).hom ≫ supportedSectionsSheafι Z B = f
      rw [ff.map_preimage]
      simpa [Category.assoc] using factor_comp f
    right_inv g := by
      have hfactor : factor (P.map g ≫ (ρ.app B).hom ≫ supportedSectionsSheafι Z B) =
          P.map g ≫ (ρ.app B).hom := by
        apply (cancel_mono (supportedSectionsSheafι Z B)).1
        simpa [Category.assoc] using factor_comp
          (P.map g ≫ (ρ.app B).hom ≫ supportedSectionsSheafι Z B)
      apply P.map_injective
      rw [ff.map_preimage, hfactor, Category.assoc, Iso.hom_inv_id, Category.comp_id] }
  refine Adjunction.mkOfHomEquiv (F := P) (G := R) {
    homEquiv := homEquiv
    homEquiv_naturality_left_symm := by
      intro A' A B f g
      dsimp only [homEquiv, Equiv.coe_fn_mk]
      simp [Category.assoc]
    homEquiv_naturality_right := by
      intro A B B' f g
      dsimp only [homEquiv, Equiv.coe_fn_mk]
      apply P.map_injective
      rw [ff.map_preimage]
      have hnat : factor (f ≫ g) = factor f ≫ S.map g := by
        apply CategoryTheory.Sheaf.hom_ext
        ext U s
        rfl
      rw [hnat]
      simp only [Functor.map_comp, Category.assoc]
      rw [ff.map_preimage]
      have h := ρ.inv.naturality g
      change S.map g ≫ (ρ.app B').inv = (ρ.app B).inv ≫ P.map (R.map g) at h
      simpa only [Category.assoc] using congrArg (fun k => factor f ≫ k) h }

/-- **Stacks 01AZ, colimits.** Pushforward of abelian sheaves along a closed inclusion
preserves arbitrary colimits. -/
@[stacks 01AZ "colimits"]
theorem closedInclusionPushforward_preservesColimits
    {X : TopCat.{u}} (Z : Set X) (hZ : IsClosed Z) :
    PreservesColimits
      (closedInclusionPushforward (TopCat.of Z) X (closedSubsetInclusion Z)) :=
  (closedInclusionPushforward_supportedSectionsOnClosedFunctor_adjunction
    Z hZ).leftAdjoint_preservesColimits

end ClosedImmersionSheaves

end
