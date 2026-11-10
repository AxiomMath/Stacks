module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLiftFunctor
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedCategoryBTransport
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.NatIsoSquare
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentInterface
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherentCohomologyUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleRingedToposHomComp
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleAssociatedModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleSpaceSiteOfFppfSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleModuleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSmallQuasiIsoSubcomplex

/-!
# The small étale and the spaces-étale derived categories of modules

Let `X` be an algebraic space over a scheme `S`. Modules on the small étale site of `X` have
sections in `Type u` (`AlgebraicGeometry.Space.derivedModules`, on which the derived pullback
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` lives), while modules on the spaces-étale
site of `X` have sections in `Type (u + 1)` (the setting of Stacks 0DHF, in
`AlgebraicGeometry.Space` the theorem
`SimplicialSpacesEtaleSite.isWeakSerreClass_and_derivedPullback_equivalence`). This file
compares the two derived categories through the transport
`ι = AlgebraicGeometry.Space.toSpacesEtaleModules` of Stacks 03G1, which lifts the module sections
one universe and extends along the comparison of sites, and compares the two derived pullbacks
along it.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedFunctor`: the derived functor
  `Φ_X : D(𝒪_X) ⥤ D(𝒪_{X, spaces-étale})` of the exact functor `ι`.
* `AlgebraicGeometry.Space.smallEtaleSpacesEtaleDerivedPullComparison`: the comparison
  `ε'_f : Φ_Y ⋙ Lf_{spaces}^* ⟶ Lf^* ⋙ Φ_X` of the two derived pullbacks, from the universal
  property of the left derived functor `Lf^* ⋙ Φ_X`.
* `AlgebraicGeometry.Space.spacesEtalePullbackToSpacesEtaleModulesHom`: the intertwining
  `f_{spaces}^* ∘ ι_Y ⟶ ι_X ∘ f^*` of the underived pullbacks, as the mate of the intertwining of
  the direct images.
* `AlgebraicGeometry.Space.SpacesEtaleSmallQuasiIsoSubcomplex`: the sheaf-site Löwenheim–Skolem
  statement (Stacks 0GYY for the spaces-étale topology) through which the full faithfulness and
  the essential image of `Φ` are reached; it holds,
  `AlgebraicGeometry.Space.spacesEtaleSmallQuasiIsoSubcomplex`.

## Main results

* `AlgebraicGeometry.Space.preservesFiniteLimits_toSpacesEtaleModules` and
  `AlgebraicGeometry.Space.preservesFiniteColimits_toSpacesEtaleModules`: `ι` is exact.
* `AlgebraicGeometry.Space.nonempty_smallEtaleSpacesEtaleDerivedFunctor_shift_iso` and
  `AlgebraicGeometry.Space.derivedCategoryB_smallEtaleSpacesEtaleDerivedFunctor_obj`: `Φ_X`
  commutes with the shifts and carries pseudo-coherent objects to complexes with quasi-coherent
  cohomology.
* `AlgebraicGeometry.Space.isIso_smallEtaleSpacesEtaleDerivedPullComparison_of_isFlat`: along a
  flat morphism `ε'_f` is an isomorphism.
* `AlgebraicGeometry.Space.spacesEtalePullbackToSpacesEtaleModulesHom_comp_app'`: the
  intertwining of the underived pullbacks is compatible with the composition comparisons.

## Implementation notes

The derived categories are the standard models `CategoryTheory.HasDerivedCategory.standard`,
which is the model `AlgebraicGeometry.Space.derivedModules` and the derived pullback of
`Stacks.Cohomology.DerivedPullbackOfToposHom` are built in. It is supplied explicitly or by
local instances for these specific categories at the default priority.

The comparison of the pullbacks is stated for the algebraic spaces of an arbitrary big étale
site of algebraic spaces `T`, with `B = T.fppfSite`, the form in which the comparisons of
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleModulePullbackComparison` are proved;
the transport `ι` is read with its target over the ringed topos of the spaces-étale site
(`AlgebraicGeometry.Space.toSpacesEtaleRingedToposModules`), the form the morphisms of
spaces-étale ringed topoi are stated over.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 08JL](https://stacks.math.columbia.edu/tag/08JL)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 0DHF](https://stacks.math.columbia.edu/tag/0DHF)
* [Stacks Project, Tag 0GYY](https://stacks.math.columbia.edu/tag/0GYY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

/-! ### The universe lift over the lifted structure sheaf is exact -/

namespace Stacks.SheafOfModules.CoherentLift

universe u v w

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})

attribute [local implicit_reducible] liftRingedSite CategoryTheory.sheafCompose

/-- The universe lift of sheaves of modules, read on the underlying sheaves of abelian groups, is
the universe lift of abelian sheaves. -/
theorem liftModuleFunctor_comp_toSheaf :
    liftModuleFunctor.{u, v, w} X ⋙ _root_.SheafOfModules.toSheaf.{max u v w}
        (Stacks.SheafOfModules.Tensor.ringSheaf (liftRingedSite.{u, v, w} X).O) =
      _root_.SheafOfModules.toSheaf.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        sheafCompose X.J AddCommGrpCat.uliftFunctor.{max u v, w} :=
  rfl

/-- **The universe lift of sheaves of modules over the lifted structure sheaf is left exact.**
Finite limits of sheaves of modules are computed on the underlying presheaves of abelian groups,
where the lift is postcomposition with `AddCommGrpCat.uliftFunctor`. -/
theorem preservesFiniteLimits_liftModuleFunctor :
    PreservesFiniteLimits (liftModuleFunctor.{u, v, w} X) := by
  let G := _root_.SheafOfModules.forget.{max u v w}
      (Stacks.SheafOfModules.Tensor.ringSheaf (liftRingedSite.{u, v, w} X).O) ⋙
    PresheafOfModules.toPresheaf _
  have : PreservesFiniteLimits (liftModuleFunctor.{u, v, w} X ⋙ G) := by
    change PreservesFiniteLimits
      ((_root_.SheafOfModules.forget.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
          PresheafOfModules.toPresheaf _) ⋙
        (Functor.whiskeringRight _ AddCommGrpCat.{w} AddCommGrpCat.{max u v w}).obj
          AddCommGrpCat.uliftFunctor.{max u v, w})
    infer_instance
  exact preservesFiniteLimits_of_reflects_of_preserves _ G

/-- **The universe lift of sheaves of modules over the lifted structure sheaf is right exact.**
Read through `SheafOfModules.toSheaf`, which preserves and reflects finite colimits, it is the
universe lift of abelian sheaves, which commutes with sheafification. -/
theorem preservesFiniteColimits_liftModuleFunctor
    [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify X.J AddCommGrpCat.{max u v w}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] :
    PreservesFiniteColimits (liftModuleFunctor.{u, v, w} X) := by
  have : HasSheafify (liftRingedSite.{u, v, w} X).J AddCommGrpCat.{max u v w} :=
    ‹HasSheafify X.J AddCommGrpCat.{max u v w}›
  have : (liftRingedSite.{u, v, w} X).J.WEqualsLocallyBijective AddCommGrpCat.{max u v w} :=
    ‹X.J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}›
  let G := _root_.SheafOfModules.toSheaf.{max u v w}
    (Stacks.SheafOfModules.Tensor.ringSheaf (liftRingedSite.{u, v, w} X).O)
  have : PreservesFiniteColimits (liftModuleFunctor.{u, v, w} X ⋙ G) := by
    rw [liftModuleFunctor_comp_toSheaf]
    have := Stacks.SheafOfModules.toSheaf_preservesFiniteColimits.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
    have : PreservesColimitsOfSize.{w, w}
        (sheafCompose X.J AddCommGrpCat.uliftFunctor.{max u v, w}) :=
      Stacks.Sheaves.UniverseLift.sheafCompose_uliftFunctor_preservesColimits
    have : PreservesColimitsOfSize.{0, 0}
        (sheafCompose X.J AddCommGrpCat.uliftFunctor.{max u v, w}) :=
      preservesSmallestColimits_of_preservesColimits _
    infer_instance
  have := Stacks.SheafOfModules.toSheaf_reflectsFiniteColimits.{max u v w}
    (Stacks.SheafOfModules.Tensor.ringSheaf (liftRingedSite.{u, v, w} X).O)
  exact preservesFiniteColimits_of_reflects_of_preserves _ G

end Stacks.SheafOfModules.CoherentLift

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The transport `ι` is exact -/

/-- **`ι` is left exact**: the universe lift is, and the second step is an equivalence. -/
theorem preservesFiniteLimits_toSpacesEtaleModules (X : AlgebraicSpaces B S hS) :
    PreservesFiniteLimits (toSpacesEtaleModules B S hS X) := by
  have := Stacks.SheafOfModules.CoherentLift.preservesFiniteLimits_liftModuleFunctor.{u + 1, u, u}
    (smallEtaleRingedSite B S hS X.1 X.2)
  unfold toSpacesEtaleModules
  infer_instance

/-- **`ι` is right exact**: the universe lift is, and the second step is an equivalence. -/
theorem preservesFiniteColimits_toSpacesEtaleModules (X : AlgebraicSpaces B S hS) :
    PreservesFiniteColimits (toSpacesEtaleModules B S hS X) := by
  have := Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp.{u + 1, u, u + 1}
    (J := (smallEtaleRingedSite B S hS X.1 X.2).J)
  have := Stacks.Cohomology.SiteModules.site_wEqualsLocallyBijective_addCommGrp.{u + 1, u, u + 1}
    (J := (smallEtaleRingedSite B S hS X.1 X.2).J)
  have := Stacks.SheafOfModules.CoherentLift.preservesFiniteColimits_liftModuleFunctor.{u + 1, u, u}
    (smallEtaleRingedSite B S hS X.1 X.2)
  unfold toSpacesEtaleModules
  infer_instance

/-- The transport `ι` of Stacks 03G1, with its target read over the ringed topos
`AlgebraicGeometry.Space.spacesEtaleRingedTopos` rather than the ringed site
`AlgebraicGeometry.Space.spacesEtaleRingedSite` (the two have the same underlying data). The
morphisms of spaces-étale ringed topoi of Stacks 0DE7 and their pullbacks and derived pullbacks
are stated over the ringed topos, so this is the form in which `ι` is composed with them. -/
abbrev toSpacesEtaleRingedToposModules (X : AlgebraicSpaces B S hS) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O) :=
  toSpacesEtaleModules B S hS X

/-! ### The derived functor `Φ_X` -/

/-- **The comparison `Φ_X : D(𝒪_X) ⥤ D(𝒪_{X, spaces-étale})`**: the derived functor of the exact
transport `ι = AlgebraicGeometry.Space.toSpacesEtaleModules` of Stacks 03G1, from the derived
category of modules on the small étale site of `X` with sections in `Type u` to that of modules
on the spaces-étale site of `X` with sections in `Type (u + 1)`. -/
def smallEtaleSpacesEtaleDerivedFunctor (X : AlgebraicSpaces B S hS) :
    derivedModules B S hS X ⥤ spacesEtaleDerivedModules B S hS X :=
  letI : HasDerivedCategory (Modules.{u, u} B S hS X.1 X.2) := HasDerivedCategory.standard _
  letI : HasDerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O)) :=
    HasDerivedCategory.standard _
  haveI := preservesFiniteLimits_toSpacesEtaleModules B S hS X
  haveI := preservesFiniteColimits_toSpacesEtaleModules B S hS X
  (toSpacesEtaleRingedToposModules B S hS X).mapDerivedCategory

/-- **`Φ_X` commutes with the shifts**: `Φ_X(K⟦i⟧) ≅ Φ_X(K)⟦i⟧`. -/
theorem nonempty_smallEtaleSpacesEtaleDerivedFunctor_shift_iso (X : AlgebraicSpaces B S hS)
    (K : derivedModules B S hS X) (i : ℤ) :
    Nonempty ((smallEtaleSpacesEtaleDerivedFunctor B S hS X).obj (K⟦i⟧) ≅
      ((smallEtaleSpacesEtaleDerivedFunctor B S hS X).obj K)⟦i⟧) := by
  let : HasDerivedCategory (Modules.{u, u} B S hS X.1 X.2) := HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O)) :=
    HasDerivedCategory.standard _
  have := preservesFiniteLimits_toSpacesEtaleModules B S hS X
  have := preservesFiniteColimits_toSpacesEtaleModules B S hS X
  exact ⟨((toSpacesEtaleRingedToposModules B S hS X).mapDerivedCategory.commShiftIso i).app K⟩

/-- **`Φ_X` carries a pseudo-coherent object to a complex with quasi-coherent cohomology**: a
pseudo-coherent object of `D(𝒪_X)` has quasi-coherent cohomology sheaves (Stacks 08JL), `ι`
preserves quasi-coherence, and the cohomology of `Φ_X(K)` is `ι` of that of `K`. -/
theorem derivedCategoryB_smallEtaleSpacesEtaleDerivedFunctor_obj (X : AlgebraicSpaces B S hS)
    (K : derivedModules B S hS X)
    (hK : letI : HasDerivedCategory (Modules.{u, u} B S hS X.1 X.2) :=
        HasDerivedCategory.standard _
      (smallEtaleRingedSite B S hS X.1 X.2).IsPseudoCoherent K) :
    @DerivedCategoryB.derivedCategoryB _ _ _ (HasDerivedCategory.standard _)
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O))
      ((smallEtaleSpacesEtaleDerivedFunctor B S hS X).obj K) := by
  let : HasDerivedCategory (Modules.{u, u} B S hS X.1 X.2) := HasDerivedCategory.standard _
  let : HasDerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS X).O)) :=
    HasDerivedCategory.standard _
  have := preservesFiniteLimits_toSpacesEtaleModules B S hS X
  have := preservesFiniteColimits_toSpacesEtaleModules B S hS X
  exact DerivedCategoryB.derivedCategoryB_mapDerivedCategory_obj
    (toSpacesEtaleRingedToposModules B S hS X)
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) _
    (fun M hM => by
      have : M.IsQuasicoherentOnSite := hM
      exact isQuasicoherentOnSite_toSpacesEtaleModules B S hS X M)
    (derivedCategoryB_of_isPseudoCoherent_unconditional B S hS X.1 X.2 K hK)

/-! ### The sheaf-site Löwenheim–Skolem statement -/

/-- **Small quasi-isomorphic subcomplexes on the spaces-étale sites** (Stacks 0GYY for the
spaces-étale topology): every complex of modules on the spaces-étale site of
an algebraic space, with sections in `Type (u + 1)`, whose cohomology sheaves have `u`-small
sections, receives a quasi-isomorphism from a complex all of whose terms have `u`-small sections.
By `AlgebraicGeometry.Space.toSpacesEtaleModules_full_faithful_essImage` the terms of such a
complex are in the essential image of `ι`; this is the input for the full faithfulness and the
essential image of `Φ`. -/
def SpacesEtaleSmallQuasiIsoSubcomplex : Prop :=
  ∀ (X : AlgebraicSpaces B S hS)
    (M : CochainComplex (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)) ℤ),
    (∀ (n : ℤ) (V : (SpacesEtale B S hS X)ᵒᵖ), Small.{u} ((M.homology n).val.obj V)) →
    ∃ (M' : CochainComplex (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedSite B S hS X).O)) ℤ)
      (i : M' ⟶ M), QuasiIso i ∧
      ∀ (n : ℤ) (V : (SpacesEtale B S hS X)ᵒᵖ), Small.{u} ((M'.X n).val.obj V)

/-- **Small quasi-isomorphic subcomplexes on the spaces-étale sites hold**: this is
`AlgebraicGeometry.Space.spacesEtale_exists_small_quasiIso_subcomplex`. -/
theorem spacesEtaleSmallQuasiIsoSubcomplex : SpacesEtaleSmallQuasiIsoSubcomplex B S hS :=
  fun X M h => spacesEtale_exists_small_quasiIso_subcomplex B S hS X M h

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

universe u

variable {S : Scheme.{u}} {T : BigEtaleSpaceSite S}

/-! ### The two pullbacks along a morphism of spaces-étale ringed topoi -/

section Bridge


/-- The morphism of ringed sites underlying the morphism of spaces-étale ringed topoi of a
morphism of algebraic spaces: base change of the spaces-étale sites, with the pullback of global
regular functions along the projections. -/
abbrev spacesEtaleRingedSiteHomOfHom {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) :
    RingedSite.Hom (spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X).toRingedSite
      (spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y).toRingedSite :=
  RingedSite.Hom.ofRingedToposSiteHom
    (BigEtaleSpaceSite.smallEtaleRingedSiteHom (T) f)
    (spacesBaseChange_isMorphismOfSites T.fppfSite S T.fppf_mem f)

/-- The morphism of spaces-étale ringed topoi of Stacks 0DE7 is the morphism of ringed topoi of
`spacesEtaleRingedSiteHomOfHom`, on the nose. -/
theorem spacesEtaleRingedToposHom_eq_ringedToposHom {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) :
    SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f =
      (spacesEtaleRingedSiteHomOfHom f).ringedToposHom :=
  rfl

/-- **The pullback of modules along the morphism of spaces-étale ringed topoi of Stacks 0DE7 is
the pullback along the site-presented morphism** `f_{small}` of
`AlgebraicGeometry.BigEtaleSpaceSite.smallEtaleRingedSiteHom`: both are left adjoints of the
same pushforward (`AlgebraicGeometry.RingedSite.Hom.pullbackModulesToposIso`). -/
def spacesEtalePullbackModulesIsoPullbackTopos {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) :
    (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f).toModulesHom.pullbackModules ≅
      (BigEtaleSpaceSite.smallEtaleRingedSiteHom (T) f).pullbackTopos :=
  eqToIso (congrArg (fun φ => φ.pullbackModules)
      (RingedToposHom.toModulesHom_eq_toRingedToposModulesHom
        (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f))) ≪≫
    (spacesEtaleRingedSiteHomOfHom f).pullbackModulesToposIso

end Bridge

/-! ### The composition comparisons of the spaces-étale pullbacks -/

section Composition

/-- The comparison of the left adjoints `L₂ ≅ L₁` of two isomorphic right adjoints `R₂ ≅ R₁`, the
first adjunction being transported along the isomorphism, has the inverse of that isomorphism
as its conjugate.  This is `Stacks.Mates.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom` with
the two adjunctions in the other order. -/
theorem conjugateEquiv_leftAdjointUniq_ofNatIsoRight_left_hom {C₀ C₁ : Type*} [Category C₀]
    [Category C₁] {L₁ L₂ : C₀ ⥤ C₁} {R₁ R₂ : C₁ ⥤ C₀} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (e : R₂ ≅ R₁) :
    conjugateEquiv adj₁ adj₂ (Adjunction.leftAdjointUniq (adj₂.ofNatIsoRight e) adj₁).hom =
      e.inv := by
  have hY := Stacks.Mates.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom adj₁ adj₂ e
  have hXY : (Adjunction.leftAdjointUniq (adj₂.ofNatIsoRight e) adj₁).hom =
      (Adjunction.leftAdjointUniq adj₁ (adj₂.ofNatIsoRight e)).inv := by
    rw [← Iso.comp_hom_eq_id, Adjunction.leftAdjointUniq_trans, Adjunction.leftAdjointUniq_refl]
  rw [hXY]
  have h := conjugateEquiv_comp adj₁ adj₂ adj₁
    (Adjunction.leftAdjointUniq adj₁ (adj₂.ofNatIsoRight e)).inv
    (Adjunction.leftAdjointUniq adj₁ (adj₂.ofNatIsoRight e)).hom
  rw [Iso.hom_inv_id, conjugateEquiv_id, hY] at h
  rw [← Iso.comp_hom_eq_id e]
  exact h

/-- The conjugate of a composite of two comparisons of left adjoints of the kind of
`conjugateEquiv_leftAdjointUniq_ofNatIsoRight_left_hom`. -/
theorem conjugateEquiv_leftAdjointUniq_ofNatIsoRight_comp_hom {C₀ C₁ : Type*} [Category C₀]
    [Category C₁] {L₁ L₂ L₃ : C₀ ⥤ C₁} {R₁ R₂ R₃ : C₁ ⥤ C₀} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₃ : L₃ ⊣ R₃) (e : R₃ ≅ R₂) (e' : R₂ ≅ R₁) :
    conjugateEquiv adj₁ adj₃ ((Adjunction.leftAdjointUniq (adj₃.ofNatIsoRight e) adj₂).hom ≫
        (Adjunction.leftAdjointUniq (adj₂.ofNatIsoRight e') adj₁).hom) = e'.inv ≫ e.inv := by
  rw [← conjugateEquiv_comp adj₁ adj₂ adj₃, conjugateEquiv_leftAdjointUniq_ofNatIsoRight_left_hom,
    conjugateEquiv_leftAdjointUniq_ofNatIsoRight_left_hom]


/-- The direct image `f_{spaces,*}` of modules along the morphism of spaces-étale ringed topoi of
a morphism of algebraic spaces. -/
abbrev spacesEtalePushforward {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) :
    SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X).O) ⥤
      SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y).O) :=
  RingedToposHom.pushforwardModules (X := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
    (Y := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
    (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)

/-- The adjunction `f_{spaces}^* ⊣ f_{spaces,*}` of a morphism of algebraic spaces. -/
abbrev spacesEtalePullbackAdjunction {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) :
    (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f).toModulesHom.pullbackModules ⊣
      spacesEtalePushforward f :=
  RingedToposHom.pullbackAdjPushforwardModules
    (X := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
    (Y := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
    (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)

/-- The composition comparison `f_{spaces,*} ⋙ g_{spaces,*} ≅ (f ≫ g)_{spaces,*}` of direct
images of modules on the spaces-étale sites: the composition of direct images along morphisms of
ringed topoi, followed by the 2-isomorphism of Stacks 0DE7. -/
def spacesEtalePushforwardModulesCompIso {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    spacesEtalePushforward f ⋙ spacesEtalePushforward g ≅ spacesEtalePushforward (f ≫ g) :=
  (RingedToposHom.pushforwardModulesCompIso (X := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
      (Y := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
      (Z := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
      (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)
      (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom g)).symm ≪≫
    (spacesEtaleRingedToposHomCompTwoIsoSpacesEtaleRingedToposHomComp f
      g).pushforwardModulesIso.symm

/-- **The composition comparison of the spaces-étale pullbacks is the comparison of left
adjoints induced by that of the direct images**: the underived compositor of the derived
pullback of Stacks 0D6D on the spaces-étale sites is
`CategoryTheory.Adjunction.leftAdjointCompIso` of `spacesEtalePushforwardModulesCompIso`. -/
theorem spacesEtalePullbackCompIso_eq_leftAdjointCompIso
    {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (RingedToposHom.pullbackModulesCompIso (X := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
        (Y := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
        (Z := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
        (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)
        (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom g)).symm ≪≫
        spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp f g =
      Adjunction.leftAdjointCompIso (spacesEtalePullbackAdjunction g)
        (spacesEtalePullbackAdjunction f) (spacesEtalePullbackAdjunction (f ≫ g))
        (spacesEtalePushforwardModulesCompIso f g) := by
  refine Iso.ext ((Iso.inv_eq_inv _ _).1 ?_)
  apply (conjugateEquiv ((spacesEtalePullbackAdjunction g).comp (spacesEtalePullbackAdjunction f))
    (spacesEtalePullbackAdjunction (f ≫ g))).injective
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv]
  simp only [Iso.trans_inv, Iso.symm_inv,
    spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp,
    spacesEtalePushforwardModulesCompIso, Iso.trans_hom, Iso.symm_hom]
  unfold RingedToposHom.pullbackModulesCompIso RingedToposHom.TwoIso.pullbackModulesIso
  exact conjugateEquiv_leftAdjointUniq_ofNatIsoRight_comp_hom _ _ _ _ _

end Composition

/-! ### The intertwining of the pullbacks as a mate, and its composition law -/

section Mate


/-- The comparison `f_{spaces,*} ≅ f_{small,*}` of the two presentations of the direct image of
modules along the morphism of spaces-étale ringed topoi of a morphism of algebraic spaces. -/
abbrev spacesEtalePushforwardIsoPushforwardTopos {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) :
    spacesEtalePushforward f ≅
      (BigEtaleSpaceSite.smallEtaleRingedSiteHom (T) f).pushforwardTopos :=
  (spacesEtaleRingedSiteHomOfHom f).pushforwardToposIso

/-- **`ι` intertwines the direct images**, in the presentation of the morphism of spaces-étale
ringed topoi of Stacks 0DE7: `ι_Y ∘ f_* ≅ f_{spaces,*} ∘ ι_X`. -/
def spacesEtalePushforwardToSpacesEtaleModulesIso {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) :
    modulePushforward T.fppfSite S T.fppf_mem f ⋙
      toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem Y ≅
      toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem X ⋙ spacesEtalePushforward f :=
  BigEtaleSpaceSite.toSpacesEtaleModulesPushforwardIso (T) f ≪≫
    Functor.isoWhiskerLeft _ (spacesEtalePushforwardIsoPushforwardTopos f).symm

/-- **The intertwining of the inverse images**, `f_{spaces}^*(ι_Y M) ⟶ ι_X(f^*M)`: the mate of
`spacesEtalePushforwardToSpacesEtaleModulesIso`. -/
def spacesEtalePullbackToSpacesEtaleModulesHom {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) :
    toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem Y ⋙
        (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f).toModulesHom.pullbackModules ⟶
      modulePullback T.fppfSite S T.fppf_mem f ⋙
        toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem X :=
  Adjunction.mateOfRightIso (modulePullbackAdjunction T.fppfSite S T.fppf_mem f)
    (spacesEtalePullbackAdjunction f)
    (spacesEtalePushforwardToSpacesEtaleModulesIso f)

/-- **The intertwining of the inverse images is an isomorphism**: `ι` is fully faithful and
`f_{spaces}^*(ι_Y M)`, isomorphic to `f_{small}^*(ι_Y M)`, is in its essential image. -/
instance isIso_spacesEtalePullbackToSpacesEtaleModulesHom
    {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) : IsIso (spacesEtalePullbackToSpacesEtaleModulesHom f) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro F
  exact Adjunction.isIso_mateOfRightIso_app_of_mem_essImage _ _ _
    (fullyFaithfulToSpacesEtaleModules T.fppfSite S T.fppf_mem Y)
    (fullyFaithfulToSpacesEtaleModules T.fppfSite S T.fppf_mem X)
    ((toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem X).essImage.prop_of_iso
      ((spacesEtalePullbackModulesIsoPullbackTopos f).app _).symm
      (BigEtaleSpaceSite.mem_essImage_pullbackTopos_toSpacesEtaleModules
        (T) f F))

/-- The comparisons of the two presentations of the direct images are compatible with the two
composition comparisons. -/
theorem spacesEtalePushforwardIsoPushforwardTopos_comp
    {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X).O)) :
    (BigEtaleSpaceSite.smallEtaleRingedSiteHomPushforwardCompIso (T) f
        g).hom.app N ≫ (spacesEtalePushforwardIsoPushforwardTopos (f ≫ g)).inv.app N =
      (spacesEtalePushforwardIsoPushforwardTopos g).inv.app
          ((BigEtaleSpaceSite.smallEtaleRingedSiteHom (T) f).pushforwardTopos.obj N) ≫
        (spacesEtalePushforward g).map ((spacesEtalePushforwardIsoPushforwardTopos f).inv.app N) ≫
        (spacesEtalePushforwardModulesCompIso f g).hom.app N := by
  ext V x
  rfl

/-- **The intertwining of the direct images is compatible with composition**: the composition
comparison of Stacks 03LU transported through `ι`, followed by the intertwining for `f ≫ g`, is
the intertwinings for `g` and `f` followed by the composition comparison of the spaces-étale
direct images. -/
theorem spacesEtalePushforwardToSpacesEtaleModulesIso_comp_hom_app
    {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) (g : Y ⟶ Z) (M : Modules.{u, u} T.fppfSite S T.fppf_mem X.1 X.2) :
    (toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem Z).map
    ((modulePushforwardCompIso T.fppfSite S T.fppf_mem f g).hom.app M) ≫
        (spacesEtalePushforwardToSpacesEtaleModulesIso (f ≫ g)).hom.app M =
      (spacesEtalePushforwardToSpacesEtaleModulesIso g).hom.app
          ((modulePushforward T.fppfSite S T.fppf_mem f).obj M) ≫
        (spacesEtalePushforward g).map
          ((spacesEtalePushforwardToSpacesEtaleModulesIso f).hom.app M) ≫
        (spacesEtalePushforwardModulesCompIso f g).hom.app
          ((toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem X).obj M) := by
  have hs := BigEtaleSpaceSite.toSpacesEtaleModulesPushforwardIso_comp_hom_app T f g M
  have hP := spacesEtalePushforwardIsoPushforwardTopos_comp f g
    ((toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem X).obj M)
  have hn := (spacesEtalePushforwardIsoPushforwardTopos g).inv.naturality
    ((BigEtaleSpaceSite.toSpacesEtaleModulesPushforwardIso T f).hom.app M)
  have e : ∀ {A B : AlgebraicSpaces T.fppfSite S T.fppf_mem} (k : A ⟶ B)
      (M : Modules.{u, u} T.fppfSite S T.fppf_mem A.1 A.2),
      (spacesEtalePushforwardToSpacesEtaleModulesIso k).hom.app M =
        (BigEtaleSpaceSite.toSpacesEtaleModulesPushforwardIso T k).hom.app M ≫
          (spacesEtalePushforwardIsoPushforwardTopos k).inv.app
            ((toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem A).obj M) :=
    fun _ _ => rfl
  dsimp only [Functor.comp_obj] at hn
  rw [e (f ≫ g) M, e g, e f M, Functor.map_comp, ← Category.assoc, hs, Category.assoc,
    Category.assoc, hP, reassoc_of% hn]
  simp only [Category.assoc]

/-- The underived composition comparison `g_{spaces}^* ⋙ f_{spaces}^* ≅ (f ≫ g)_{spaces}^*` of
the spaces-étale pullbacks, the one the derived comparison of Stacks 0D6D is built from. -/
abbrev spacesEtalePullbackModulesCompIso {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom g).toModulesHom.pullbackModules ⋙
        (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f).toModulesHom.pullbackModules ≅
      (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom (f ≫ g)).toModulesHom.pullbackModules :=
  (RingedToposHom.pullbackModulesCompIso (X := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
      (Y := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
      (Z := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Z)
      (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)
      (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom g)).symm ≪≫
    spacesEtalePullbackModulesCompIsoSpacesEtaleRingedToposHomComp f g

/-- **The intertwining of the inverse images is compatible with composition**, in the form of
`CategoryTheory.Adjunction.leftAdjointCompIso_hom_app_comp_mateOfRightIso_app`: for
`f : X ⟶ Y`, `g : Y ⟶ Z` and an `𝒪_Z`-module `N`, the composition comparison of the spaces-étale
pullbacks induced by that of the direct images, followed by the intertwining for `f ≫ g`, is
`f_{spaces}^*` of the intertwining for `g`, then the intertwining for `f`, then `ι` of the
composition comparison of Stacks 03LU. -/
theorem spacesEtalePullbackToSpacesEtaleModulesHom_comp_app'
    {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) (g : Y ⟶ Z)
    (N : Modules.{u, u} T.fppfSite S T.fppf_mem Z.1 Z.2) :
    (Adjunction.leftAdjointCompIso (spacesEtalePullbackAdjunction g)
        (spacesEtalePullbackAdjunction f) (spacesEtalePullbackAdjunction (f ≫ g))
        (spacesEtalePushforwardModulesCompIso f g)).hom.app
          ((toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem Z).obj N) ≫
        (Adjunction.mateOfRightIso (modulePullbackAdjunction T.fppfSite S T.fppf_mem (f ≫ g))
          (spacesEtalePullbackAdjunction (f ≫ g))
          (spacesEtalePushforwardToSpacesEtaleModulesIso (f ≫ g))).app N =
      (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.map
          ((Adjunction.mateOfRightIso (modulePullbackAdjunction T.fppfSite S T.fppf_mem g)
            (spacesEtalePullbackAdjunction g)
            (spacesEtalePushforwardToSpacesEtaleModulesIso g)).app N) ≫
        (Adjunction.mateOfRightIso (modulePullbackAdjunction T.fppfSite S T.fppf_mem f)
          (spacesEtalePullbackAdjunction f) (spacesEtalePushforwardToSpacesEtaleModulesIso f)).app
            ((modulePullback T.fppfSite S T.fppf_mem g).obj N) ≫
        (toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem X).map
          ((modulePullbackCompIso T.fppfSite S T.fppf_mem f g).hom.app N) :=
  Adjunction.leftAdjointCompIso_hom_app_comp_mateOfRightIso_app
    (modulePullbackAdjunction T.fppfSite S T.fppf_mem g)
    (modulePullbackAdjunction T.fppfSite S T.fppf_mem f)
    (modulePullbackAdjunction T.fppfSite S T.fppf_mem (f ≫ g)) (spacesEtalePullbackAdjunction g)
    (spacesEtalePullbackAdjunction f) (spacesEtalePullbackAdjunction (f ≫ g))
    (spacesEtalePushforwardToSpacesEtaleModulesIso g)
    (spacesEtalePushforwardToSpacesEtaleModulesIso f)
    (spacesEtalePushforwardToSpacesEtaleModulesIso (f ≫ g))
    (modulePushforwardCompIso T.fppfSite S T.fppf_mem f g)
    (spacesEtalePushforwardModulesCompIso f g)
    (spacesEtalePushforwardToSpacesEtaleModulesIso_comp_hom_app f g)
    (modulePullbackCompIso T.fppfSite S T.fppf_mem f g)
    (modulePullbackCompIso_eq_leftAdjointCompIso T.fppfSite S T.fppf_mem f g) N

/-- The pullbacks of `AlgebraicGeometry.Space.modulePullbackDataTopos` are the inverse images of
`𝒪`-modules of Stacks 03LU, as functors between the categories of modules on the small étale
sites. -/
theorem modulePullbackDataTopos_pull_eq_modulePullback
    {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) :
    (modulePullbackDataTopos T.fppfSite S T.fppf_mem).pull f =
      modulePullback T.fppfSite S T.fppf_mem f :=
  toModulesHom_pullbackModules_eq_modulePullback T.fppfSite S T.fppf_mem f

/-- **The transport `ι` intertwines the two inverse images**: for `f : X ⟶ Y`,
`f_{spaces}^*(ι_Y M) ≅ ι_X(f^*M)`, the pullback on the left being that of the morphism of
spaces-étale ringed topoi of Stacks 0DE7 and the one on the right that of the morphism of small
étale ringed topoi (Stacks 03LU), which the derived pullback
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData` derives. It is the mate
`AlgebraicGeometry.Space.spacesEtalePullbackToSpacesEtaleModulesHom`, read in the spelling of the
pullbacks of `AlgebraicGeometry.Space.modulePullbackDataTopos`. -/
def spacesEtalePullbackToSpacesEtaleModulesIso {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) :
    toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem Y ⋙
        (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f).toModulesHom.pullbackModules ≅
      (modulePullbackDataTopos T.fppfSite S T.fppf_mem).pull f ⋙
        toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem X :=
  asIso (spacesEtalePullbackToSpacesEtaleModulesHom f) ≪≫
    Functor.isoWhiskerRight (eqToIso (modulePullbackDataTopos_pull_eq_modulePullback f).symm)
      (toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem X)

/-- `spacesEtalePullbackToSpacesEtaleModulesIso` is the mate of
`AlgebraicGeometry.Space.spacesEtalePushforwardToSpacesEtaleModulesIso` (that is,
`AlgebraicGeometry.Space.spacesEtalePullbackToSpacesEtaleModulesHom`), followed by `ι` of the
transport between the two spellings of the pullback. -/
theorem spacesEtalePullbackToSpacesEtaleModulesIso_hom
    {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) :
    (spacesEtalePullbackToSpacesEtaleModulesIso f).hom =
      Adjunction.mateOfRightIso (modulePullbackAdjunction T.fppfSite S T.fppf_mem f)
          (spacesEtalePullbackAdjunction f) (spacesEtalePushforwardToSpacesEtaleModulesIso f) ≫
        Functor.whiskerRight (eqToHom (modulePullbackDataTopos_pull_eq_modulePullback f).symm)
          (toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem X) :=
  rfl

/-- The composition comparison of `AlgebraicGeometry.Space.modulePullbackDataTopos` is that of
Stacks 03LU, transported along the two spellings of the pullbacks. -/
theorem modulePullbackDataTopos_compIso_eq {X Y Z : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (modulePullbackDataTopos T.fppfSite S T.fppf_mem).compIso f g =
      eqToIso (modulePullbackDataTopos_pull_eq_modulePullback (f ≫ g)) ≪≫
        (modulePullbackCompIso T.fppfSite S T.fppf_mem f g).symm ≪≫
        eqToIso (by rw [modulePullbackDataTopos_pull_eq_modulePullback f,
          modulePullbackDataTopos_pull_eq_modulePullback g]) :=
  rfl

end Mate

/-! ### The comparison of the derived pullbacks -/

section Derived

open Stacks.Cohomology.DerivedPullbackOfToposHom


attribute [local instance] preservesFiniteLimits_toSpacesEtaleModules
  preservesFiniteColimits_toSpacesEtaleModules

/-- The standard model of the derived category of modules on the small étale site, the model
`AlgebraicGeometry.Space.derivedModules` is built in. -/
local instance hasDerivedCategory_smallEtaleModules (X : AlgebraicSpaces T.fppfSite S T.fppf_mem) :
    HasDerivedCategory (Modules.{u, u} T.fppfSite S T.fppf_mem X.1 X.2) :=
  HasDerivedCategory.standard _

/-- The standard model of the derived category of modules on the spaces-étale site, the model
the derived pullback of `Stacks.Cohomology.DerivedPullbackOfToposHom` is built in. -/
local instance hasDerivedCategory_spacesEtaleModules (X : AlgebraicSpaces T.fppfSite S T.fppf_mem) :
    HasDerivedCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X).O)) :=
  HasDerivedCategory.standard _

/-- The pullback of modules along a morphism of spaces-étale ringed topoi is additive. -/
local instance additive_spacesEtalePullbackModules {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) :
    (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f).toModulesHom.pullbackModules.Additive :=
  RingedToposHom.pullbackModules_additive (X := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
    (Y := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
    (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)

/-- The adjunction `f_{spaces}^* ⊣ f_{spaces,*}`. -/
abbrev spacesEtalePullbackAdjunctionOfHom {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) :=
  RingedToposHom.pullbackAdjPushforwardModules
    (X := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem X)
    (Y := spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y)
    (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)

/-- `spacesEtalePullbackToSpacesEtaleModulesIso` on the homotopy categories. -/
def spacesEtaleMapHomotopyPullbackIso {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y) :
    (toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem Y).mapHomotopyCategory
    (ComplexShape.up ℤ) ⋙
        (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom
          f).toModulesHom.pullbackModules.mapHomotopyCategory
          (ComplexShape.up ℤ) ≅
      ((modulePullbackDataTopos T.fppfSite S T.fppf_mem).pull f).mapHomotopyCategory
      (ComplexShape.up ℤ) ⋙
        (toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem X).mapHomotopyCategory
        (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (spacesEtalePullbackToSpacesEtaleModulesIso f) _ ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) _).symm

/-- The comparison of `Lf^* ⋙ Φ_X` with the underived functor: the comparison of Stacks 06YY on
the small étale sites, followed by `Φ_X`. -/
abbrev smallEtaleSpacesEtaleDerivedPullCounit {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) :
    DerivedCategory.Qh ⋙ ((smallEtaleDerivedPullbackData T.fppfSite S T.fppf_mem).pull f ⋙
        smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem X) ⟶
      (((modulePullbackDataTopos T.fppfSite S T.fppf_mem).pull f).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙ smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem X :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).α f)
      (smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem X)

/-- **`Lf^* ⋙ Φ_X` is a left derived functor** of degreewise pullback followed by `Φ_X`, with
the comparison `smallEtaleSpacesEtaleDerivedPullCounit`: `Lf^*` is computed on K-flat
complexes, so it stays a left derived functor after composition with any functor. -/
instance isLeftDerivedFunctor_smallEtaleSpacesEtaleDerivedPull
    {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) :
    ((smallEtaleDerivedPullbackData T.fppfSite S T.fppf_mem).pull f ⋙
        smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem X).IsLeftDerivedFunctor
      (smallEtaleSpacesEtaleDerivedPullCounit f) (HomotopyCategory.quasiIso _ _) :=
  haveI : ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).Q Y).IsLocalization
      (HomotopyCategory.quasiIso _ _) :=
    (derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).isLocalization Y
  haveI : ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).L f).IsLeftDerivedFunctor
      ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).α f)
      (HomotopyCategory.quasiIso _ _) :=
    (derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).isLeftDerivedFunctor f
  LeftDerivedByResolutions.isLeftDerivedFunctor_postcomp_of_resolutions
    (HomotopyCategory.quasiIso _ _) ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).R Y)
    ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).resolves Y) _
    ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).inverts f)
    ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).Q Y)
    ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).L f)
    ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).α f)
    (smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem X)

/-- The comparison of `Φ_Y ⋙ Lf_{spaces}^*` with the same underived functor: `Φ_Y` on complexes,
the comparison of Stacks 06YY on the spaces-étale sites, the underived intertwining
`spacesEtalePullbackToSpacesEtaleModulesIso`, and `Φ_X` on complexes. -/
def spacesEtaleSmallEtaleDerivedPullCounit {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) :
    DerivedCategory.Qh ⋙
      (smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem Y ⋙
      spacesEtaleDerivedPull T.fppfSite S T.fppf_mem f) ⟶
      (((modulePullbackDataTopos T.fppfSite S T.fppf_mem).pull f).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh) ⋙ smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem X :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      (toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem Y).mapDerivedCategoryFactorsh.hom _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _ (derivedPullbackComparison
      (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (spacesEtaleMapHomotopyPullbackIso f).hom DerivedCategory.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft _
      (toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem X).mapDerivedCategoryFactorsh.inv ≫
    (Functor.associator _ _ _).inv

/-- The component of `spacesEtaleSmallEtaleDerivedPullCounit f` at a complex `P` is the
composite of the components of its four constituent comparisons. -/
theorem spacesEtaleSmallEtaleDerivedPullCounit_app {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y)
    (P : HomotopyCategory (Modules.{u, u} T.fppfSite S T.fppf_mem Y.1 Y.2) (ComplexShape.up ℤ)) :
    (spacesEtaleSmallEtaleDerivedPullCounit f).app P =
      𝟙 _ ≫ (spacesEtaleDerivedPull T.fppfSite S T.fppf_mem f).map
          ((toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem
            Y).mapDerivedCategoryFactorsh.hom.app P) ≫ 𝟙 _ ≫
        (derivedPullbackComparison (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)).app
          (((toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem Y).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj P) ≫
        𝟙 _ ≫ DerivedCategory.Qh.map ((spacesEtaleMapHomotopyPullbackIso f).hom.app P) ≫ 𝟙 _ ≫
        (toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem
          X).mapDerivedCategoryFactorsh.inv.app
          ((((modulePullbackDataTopos T.fppfSite S T.fppf_mem).pull f).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj P) ≫ 𝟙 _ :=
  rfl

/-- **The comparison `ε'_f : Φ_Y ⋙ Lf_{spaces}^* ⟶ Lf^* ⋙ Φ_X` of the two derived pullbacks**,
induced by the universal property of the left derived functor `Lf^* ⋙ Φ_X` from the comparison
`spacesEtaleSmallEtaleDerivedPullCounit`. -/
def smallEtaleSpacesEtaleDerivedPullComparison {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y) :
    smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem Y ⋙
      spacesEtaleDerivedPull T.fppfSite S T.fppf_mem f ⟶
      (smallEtaleDerivedPullbackData T.fppfSite S T.fppf_mem).pull f ⋙
        smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem X :=
  ((smallEtaleDerivedPullbackData T.fppfSite S T.fppf_mem).pull f ⋙
      smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem X).leftDerivedLift
    (smallEtaleSpacesEtaleDerivedPullCounit f) (HomotopyCategory.quasiIso _ _) _
    (spacesEtaleSmallEtaleDerivedPullCounit f)

/-- The comparison `smallEtaleSpacesEtaleDerivedPullComparison f`, evaluated at the image of a
complex `P` in the derived category and followed by the component of
`smallEtaleSpacesEtaleDerivedPullCounit f` at `P`, is the component of
`spacesEtaleSmallEtaleDerivedPullCounit f` at `P`. -/
theorem smallEtaleSpacesEtaleDerivedPullComparison_fac_app
    {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y)
    (P : HomotopyCategory (Modules.{u, u} T.fppfSite S T.fppf_mem Y.1 Y.2) (ComplexShape.up ℤ)) :
    (smallEtaleSpacesEtaleDerivedPullComparison f).app (DerivedCategory.Qh.obj P) ≫
        (smallEtaleSpacesEtaleDerivedPullCounit f).app P =
      (spacesEtaleSmallEtaleDerivedPullCounit f).app P :=
  Functor.leftDerived_fac_app _ _ _ _ _ P

/-- The comparison `spacesEtaleSmallEtaleDerivedPullCounit` is invertible at a complex `P` at
which the comparison of Stacks 06YY on the spaces-étale sites is invertible at `ι(P)`. -/
theorem isIso_spacesEtaleSmallEtaleDerivedPullCounit_app
    {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y)
    (P : HomotopyCategory (Modules.{u, u} T.fppfSite S T.fppf_mem Y.1 Y.2) (ComplexShape.up ℤ))
    (h : IsIso ((derivedPullbackComparison
        (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)).app
          (((toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem Y).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj P))) :
    IsIso ((spacesEtaleSmallEtaleDerivedPullCounit f).app P) := by
  have h2 := h
  have h1 : IsIso ((spacesEtaleDerivedPull T.fppfSite S T.fppf_mem f).map
      ((toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem
        Y).mapDerivedCategoryFactorsh.hom.app P)) := inferInstance
  have h3 : IsIso (DerivedCategory.Qh.map ((spacesEtaleMapHomotopyPullbackIso f).hom.app P)) :=
    inferInstance
  have h4 : IsIso ((toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem
        X).mapDerivedCategoryFactorsh.inv.app
      ((((modulePullbackDataTopos T.fppfSite S T.fppf_mem).pull f).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj P)) := inferInstance
  rw [spacesEtaleSmallEtaleDerivedPullCounit_app]
  exact IsIso.comp_isIso' (IsIso.id _) (IsIso.comp_isIso' h1 (IsIso.comp_isIso' (IsIso.id _)
    (IsIso.comp_isIso' h2 (IsIso.comp_isIso' (IsIso.id _) (IsIso.comp_isIso' h3
      (IsIso.comp_isIso' (IsIso.id _) (IsIso.comp_isIso' h4 (IsIso.id _))))))))

/-- **The comparison of the two derived pullbacks is invertible** as soon as the comparison of
Stacks 06YY on the spaces-étale sites is invertible at the transport `ι(P)` of every K-flat
complex `P` with flat terms: `Φ_Y ⋙ Lf_{spaces}^*` is then a second left derived functor of the
same underived functor. -/
theorem isIso_smallEtaleSpacesEtaleDerivedPullComparison_of_isIso
    {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem}
    (f : X ⟶ Y)
    (h : ∀ P :
      HomotopyCategory (Modules.{u, u} T.fppfSite S T.fppf_mem Y.1 Y.2) (ComplexShape.up ℤ),
      (derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).R Y P →
        IsIso ((derivedPullbackComparison
          (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)).app
            (((toSpacesEtaleRingedToposModules T.fppfSite S T.fppf_mem Y).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj P))) :
    IsIso (smallEtaleSpacesEtaleDerivedPullComparison f) := by
  have hF : ∀ {M N : HomotopyCategory (Modules.{u, u} T.fppfSite S T.fppf_mem Y.1 Y.2)
      (ComplexShape.up ℤ)} (s : M ⟶ N), HomotopyCategory.quasiIso _ _ s →
        (derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).R Y M →
        (derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).R Y N →
        IsIso (((((modulePullbackDataTopos T.fppfSite S T.fppf_mem).pull f).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙
            smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem X).map s) := by
    intro M N s hs hM hN
    have : IsIso ((((modulePullbackDataTopos T.fppfSite S T.fppf_mem).pull f).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map s) :=
      (derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).inverts f s hs hM hN
    exact (inferInstance : IsIso
      ((smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem X).map
      ((((modulePullbackDataTopos T.fppfSite S T.fppf_mem).pull f).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map s)))
  have : (smallEtaleSpacesEtaleDerivedFunctor T.fppfSite S T.fppf_mem Y ⋙
      spacesEtaleDerivedPull T.fppfSite S T.fppf_mem f).IsLeftDerivedFunctor
        (spacesEtaleSmallEtaleDerivedPullCounit f)
        (HomotopyCategory.quasiIso _ _) :=
    LeftDerivedByResolutions.isLeftDerivedFunctor_of_isIso_on_resolutions
      (HomotopyCategory.quasiIso _ _)
      ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).R Y)
      ((derivedModulePullbackLeftDerived T.fppfSite S T.fppf_mem).resolves Y) _ hF
        DerivedCategory.Qh _ _
      (fun P hP => isIso_spacesEtaleSmallEtaleDerivedPullCounit_app f P (h P hP))
  exact (Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift _
    (smallEtaleSpacesEtaleDerivedPullCounit f) (HomotopyCategory.quasiIso _ _) _
    (spacesEtaleSmallEtaleDerivedPullCounit f)).1 inferInstance

/-- **Along a flat morphism the derived pullback on the spaces-étale sites is computed
degreewise**: the pullback of modules is then exact (Stacks 05V5 on stalks), so degreewise pullback
inverts every quasi-isomorphism and every complex resolves itself. -/
theorem isIso_derivedPullbackComparison_spacesEtaleRingedToposHom_of_isFlat
    {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y)
    (hf : IsFlat T.fppfSite S T.fppf_mem f.hom) :
    IsIso (derivedPullbackComparison (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)) := by
  have := (
  preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact
    f hf)
  have : PreservesFiniteColimits
      (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f).toModulesHom.pullbackModules :=
    have := (spacesEtalePullbackAdjunctionOfHom f).leftAdjoint_preservesColimits
    inferInstance
  have hF : ∀ {M N : HomotopyCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos T.fppfSite S T.fppf_mem Y).O))
        (ComplexShape.up ℤ)} (s : M ⟶ N), HomotopyCategory.quasiIso _ _ s →
        (⊤ : ObjectProperty _) M → (⊤ : ObjectProperty _) N →
        IsIso ((pullbackOnHomotopy
          (SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom f)).map s) := by
    intro M N s hs _ _
    have : IsIso (DerivedCategory.Qh.map s) := Localization.inverts DerivedCategory.Qh _ s hs
    exact (NatIso.isIso_map_iff ((SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom
      f).toModulesHom.pullbackModules.mapDerivedCategoryFactorsh) s).1
        (inferInstance : IsIso (((SimplicialSpacesEtaleSite.spacesEtaleRingedToposHom
          f).toModulesHom.pullbackModules.mapDerivedCategory).map (DerivedCategory.Qh.map s)))
  rw [NatTrans.isIso_iff_isIso_app]
  intro P
  exact LeftDerivedByResolutions.isIso_app_of_resolutions (HomotopyCategory.quasiIso _ _) ⊤
    (fun M => ⟨M, trivial, 𝟙 M, (HomotopyCategory.quasiIso _ _).id_mem M⟩) _ hF
    DerivedCategory.Qh _ _ P trivial

/-- **Along a flat morphism the two derived pullbacks are intertwined by `Φ`**: the comparison
`ε'_f` is invertible. -/
theorem isIso_smallEtaleSpacesEtaleDerivedPullComparison_of_isFlat
    {X Y : AlgebraicSpaces T.fppfSite S T.fppf_mem} (f : X ⟶ Y)
    (hf : IsFlat T.fppfSite S T.fppf_mem f.hom) :
    IsIso (smallEtaleSpacesEtaleDerivedPullComparison f) :=
  have := isIso_derivedPullbackComparison_spacesEtaleRingedToposHom_of_isFlat f hf
  isIso_smallEtaleSpacesEtaleDerivedPullComparison_of_isIso f fun _ _ => inferInstance

end Derived

end AlgebraicGeometry.Space

end
