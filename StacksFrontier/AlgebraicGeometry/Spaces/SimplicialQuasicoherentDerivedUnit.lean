module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.OverSimplicialObjectHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialBigFppfModuleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialBigFppfTotalAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleRightAcyclic
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleUnitTopos
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.RelativeLeraySpectralSequence
public import StacksFrontier.Homology.CompositeCollapseSquare

/-!
# Cohomological descent of quasi-coherent modules along an fppf hypercovering

Let `a : U → X` be an fppf hypercovering of an algebraic space `X` by a simplicial algebraic
space, and `a : (Sh(U_{étale}), 𝒪_U) ⟶ (Sh(X_{étale}), 𝒪_X)` the morphism of ringed topoi of
Stacks 0DE7. For a quasi-coherent `𝒪_X`-module `F` the map `F ⟶ Ra_*(a^*F)` is an isomorphism
(Stacks 0DHE): the unit `F ⟶ a_*a^*F` is invertible (Stacks 0DHD) and `Rⁿa_*(a^*F) = 0` for
`n > 0`.

The vanishing follows the source's computation around the square of Stacks 0DHC,
`a ∘ h ≅ h_{-1} ∘ a_{fppf}`. Put `G = a^*F` and `M = h^*G`. Then `G = h_*M` (Stacks 0DH0) and `M`
is `h_*`-acyclic (Stacks 0DH1 with 0DGP in each degree); `M = a_{fppf}^*E` with `E = h_{-1}^*F`,
which is `a_{fppf,*}`-acyclic (Stacks 0DAC) with `a_{fppf,*}M = E` (Stacks 0DAB); and `E` is
`h_{-1,*}`-acyclic (Stacks 0DGP). Direct images of injective modules are acyclic for further
direct images (Stacks 072Z, 0731), so the Grothendieck spectral sequences of `a_* ∘ h_*` and
`h_{-1,*} ∘ a_{fppf,*}` collapse at `M`, and `Rⁿa_*(G) ≅ Rⁿh_{-1,*}(E) = 0`.

## Main results

All in the namespace `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`:

* `isZero_rightDerived_bigFppfAugmentation_pushforwardModules_pullbackModules`:
  Stacks 0DAC for `a_{fppf}`.
* `isZero_rightDerived_augmentationRingedToposHom_pushforwardModules_pullbackModules`:
  `Rⁿa_*(a^*F) = 0` for `n > 0`.
* `isIso_unit_and_isZero_rightDerived_of_isHypercoveringAugmentation`: the unit
  `F ⟶ a_*a^*F` is an isomorphism and `Rⁿa_*(a^*F) = 0` for `n > 0` (**Stacks 0DHE**).

## References

* [Stacks Project, Tag 0DHE](https://stacks.math.columbia.edu/tag/0DHE)
* [Stacks Project, Tag 0DHC](https://stacks.math.columbia.edu/tag/0DHC)
* [Stacks Project, Tag 0DAC](https://stacks.math.columbia.edu/tag/0DAC)
* [Stacks Project, Tag 0DGP](https://stacks.math.columbia.edu/tag/0DGP)
* [Stacks Project, Tag 072Z](https://stacks.math.columbia.edu/tag/072Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CategoryTheory.Hypercovering

universe w u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.RingedToposHom

variable {X Y Z : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [Z.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Z.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [IsGrothendieckAbelian.{w} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))]

omit [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [IsGrothendieckAbelian.{w}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- **The direct image of an injective module is acyclic for a further direct image** (Stacks
072Z with Stacks 0731 (4)), in Mathlib's `ℕ`-indexed right derived functors. -/
theorem isZero_rightDerived_pushforwardModules_obj_pushforwardModules_of_injective
    (f : RingedToposHom X Y) (g : RingedToposHom Y Z)
    (I : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hI : Injective I)
    (n : ℕ) (hn : 0 < n) :
    IsZero (((pushforwardModules g).rightDerived n).obj ((pushforwardModules f).obj I)) := by
  let := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
  let := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  let := Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian.{w}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))
  have := (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules
    g.toModulesHom).right_adjoint_additive
  have : (Stacks.Sheaves.RingedToposModules.pushforwardModules g.toModulesHom).IsRightAdjoint :=
    (Stacks.Sheaves.RingedToposModules.pullbackAdjPushforwardModules g.toModulesHom).isRightAdjoint
  have h₁ := Stacks.Cohomology.Leray.rightAcyclic_pushforwardModules_pushforward_of_injective
    f.toModulesHom g.toModulesHom I hI
  have h₂ := (Stacks.RightDerivedComp.rightAcyclic_iff_acyclic _ _).1 h₁ n hn
  exact h₂.of_iso (((Functor.rightDerivedIsoOfIso g.toModulesPushforwardIso n).app _).symm ≪≫
    ((Stacks.Sheaves.RingedToposModules.pushforwardModules g.toModulesHom).rightDerived n).mapIso
      (f.toModulesPushforwardIso.app I).symm)

end AlgebraicGeometry.RingedToposHom

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S} {U : SimplicialObject T.Spaces} {X : T.Spaces}
  {a : U ⟶ (SimplicialObject.const T.Spaces).obj X}

variable (a) in
/-- Sheaves of modules on `(Spaces/U)_{fppf,total}` have enough injectives. -/
local instance enoughInjectives_bigFppfTotalRingedToposModules :
    EnoughInjectives (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (bigFppfTotalRingedTopos a).O)) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

variable (a) in
/-- Sheaves of modules on `(Spaces/U)_{fppf,total}` form an abelian category, read at the
universes of the ringed topos of its ringed site. -/
noncomputable local instance abelian_bigFppfTotalRingedSiteModules :
    Abelian (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfTotalRingedSite a)).O)) :=
  inferInstance

variable (a) in
/-- Sheaves of modules on `(Spaces/U)_{fppf,total}` have enough injectives, read at the
universes of the ringed topos of its ringed site. -/
local instance enoughInjectives_bigFppfTotalRingedSiteModules :
    EnoughInjectives (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (bigFppfTotalRingedSite a)).O)) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

variable (U) in
/-- Sheaves of modules on `U_{spaces,étale}` have enough injectives. -/
local instance enoughInjectives_ringedToposModules :
    EnoughInjectives (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O)) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

variable (T X) in
/-- Sheaves of modules on `(Spaces/X)_fppf` have enough injectives. -/
local instance enoughInjectives_bigFppfRingedToposModules :
    EnoughInjectives (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfSpaceSite.bigFppfRingedTopos T X).O)) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

variable (T X) in
/-- Sheaves of modules on `X_{spaces,étale}` have enough injectives. -/
local instance enoughInjectives_spacesEtaleRingedToposModules :
    EnoughInjectives (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (spacesEtaleRingedTopos T.schemeSite S T.scheme_mem X).O)) :=
  IsGrothendieckAbelian.enoughInjectives.{u + 1}

variable (T X) in
/-- Sheaves of modules on the spaces-étale ringed topos of `X` form an abelian category, read at
the universes of its ringed topos. -/
noncomputable local instance abelian_spacesEtaleRingedSiteModules :
    Abelian (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1}
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X)).O)) :=
  inferInstance

variable (T X) in
/-- Sheaves of modules on the big fppf ringed site of `X` form an abelian category, read at the
universes of its ringed topos. -/
noncomputable local instance abelian_bigFppfRingedSiteModules :
    Abelian (SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{u + 1, u + 1, u + 1} (BigFppfSpaceSite.bigFppfRingedSite T X)).O)) :=
  inferInstance

variable (T X) in
/-- **Stacks 0DGP in `ℕ`-indexed form**: for a quasi-coherent `𝒪_X`-module `F`,
`Rⁿa_{X,*}(a_X^*F) = 0` for `n > 0`, for the morphism of ringed topoi
`a_X : (Sh((Spaces/X)_fppf), 𝒪_{big}) ⟶ (Sh(X_{spaces,étale}), 𝒪_X)`. -/
theorem isZero_rightDerived_fppfToSpacesEtaleRingedHom_pushforwardModules_pullbackModules
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (SpacesEtale.topology T.schemeSite S T.scheme_mem X))
      (SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X)))
    [F.IsQuasicoherentOnSite] (n : ℕ) (hn : 0 < n) :
    haveI := RingedToposHom.pushforwardModules_additive
      (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X)
    IsZero (((RingedToposHom.pushforwardModules
        (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X)).rightDerived n).obj
      ((BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X).toModulesHom.pullbackModules.obj F)) := by
  have := RingedToposHom.pushforwardModules_additive
    (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X)
  have := RingedToposHom.pushforwardModules_additive
    (BigFppfSpaceSite.fppfToSpacesEtaleRingedSiteHom T X).ringedToposHom
  have := RingedToposSiteHom.pushforwardTopos_additive.{u + 1}
    (BigFppfSpaceSite.fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom
  have : (BigFppfSpaceSite.fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom
      |>.pushforwardTopos.IsRightAdjoint :=
    (BigFppfSpaceSite.fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom
      |>.pullbackPushforwardAdjunctionTopos.isRightAdjoint
  have h₁ := BigFppfSpaceSite.rightAcyclic_pushforward_pullback F
  have h₂ := (@Stacks.RightDerivedComp.rightAcyclic_iff_acyclic _ _ _ _ _ _ _ _ _ _
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) _).1 h₁ n hn
  let eP := Adjunction.leftAdjointUniq
    (Adjunction.ofNatIsoRight
      ((BigFppfSpaceSite.fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom
        |>.pullbackPushforwardAdjunctionTopos)
      (BigFppfSpaceSite.fppfToSpacesEtaleRingedSiteHom T X).pushforwardToposIso.symm)
    (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X).pullbackAdjPushforwardModules
  exact h₂.of_iso (((Functor.rightDerivedIsoOfIso
      (BigFppfSpaceSite.fppfToSpacesEtaleRingedSiteHom T X).pushforwardToposIso n).app _) ≪≫
    ((BigFppfSpaceSite.fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom
      |>.pushforwardTopos.rightDerived n).mapIso (eP.app F).symm)

/-- The direct image of sheaves of modules along a morphism of ringed topoi is a right adjoint. -/
private theorem isRightAdjoint_pushforwardModules {A B : RingedTopos.{u + 1, u + 1, u + 1}}
    [A.J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [B.J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
    [A.J.HasSheafCompose (forget RingCat.{u + 1})] [B.J.HasSheafCompose (forget RingCat.{u + 1})]
    (f : RingedToposHom A B) : (RingedToposHom.pushforwardModules f).IsRightAdjoint :=
  (RingedToposHom.pullbackAdjPushforwardModules f).isRightAdjoint

section

variable (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a)

include h

/-- **Stacks 0DAC for `a_{fppf}`.** For an fppf hypercovering `a : U → X` and an
`𝒪_{big}`-module `E` on `(Spaces/X)_fppf`, `Rⁿa_{fppf,*}(a_{fppf}^*E) = 0` for `n > 0`. -/
theorem isZero_rightDerived_bigFppfAugmentation_pushforwardModules_pullbackModules
    (E : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (BigFppfSpaceSite.bigFppfRingedTopos T X).O))
    (n : ℕ) (hn : 0 < n) :
    haveI := RingedToposHom.pushforwardModules_additive (bigFppfAugmentationRingedHom a)
    IsZero (((RingedToposHom.pushforwardModules (bigFppfAugmentationRingedHom a)).rightDerived
      n).obj ((bigFppfAugmentationRingedHom a).toModulesHom.pullbackModules.obj E)) := by
  open SimplicialOver in
  exact isZero_rightDerived_pushforwardModules_pullbackModules_overSimplicialObjectHigherDirectImage
    T.pretopologyBigFppfPretopology
    T.toGrothendieck_pretopology_bigFppfPretopology h (bigFppfAugmentationRingedHom a)
    (hf := isIso_bigFppfAugmentationRingedHom_fSharpInverseImage a)
    (eqToIso (bigFppfAugmentationRingedHom_inverseImage a)) E n hn

/-- **`Rⁿa_*(a^*F) = 0` for `n > 0`** for a quasi-coherent `𝒪_X`-module `F` and an fppf
hypercovering `a : U → X`, the morphism of ringed topoi being the one of Stacks 0DE7. With
`G = a^*F`, `M = h^*G` and `E = a_X^*F`, the two composites around the square of Stacks 0DHC
have collapsing spectral sequences at `M`, so `Rⁿa_*(G) = Rⁿa_*(h_*M) ≅ Rⁿa_{X,*}(a_{fppf,*}M) =
Rⁿa_{X,*}(E)`, which vanishes by Stacks 0DGP. -/
theorem isZero_rightDerived_augmentationRingedToposHom_pushforwardModules_pullbackModules
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (SpacesEtale.topology T.schemeSite S T.scheme_mem X))
      (SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X)))
    [F.IsQuasicoherentOnSite] (n : ℕ) (hn : 0 < n) :
    haveI := RingedToposHom.pushforwardModules_additive (augmentationRingedToposHom a)
    IsZero (((RingedToposHom.pushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        (augmentationRingedToposHom a)).rightDerived n).obj
      ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
        u + 1, u + 1, u + 1} (augmentationRingedToposHom a).toModulesHom).obj F)) := by
  have := RingedToposHom.pushforwardModules_additive (augmentationRingedToposHom a)
  have := RingedToposHom.pushforwardModules_additive (bigFppfTotalRingedHom a)
  have := RingedToposHom.pushforwardModules_additive (bigFppfAugmentationRingedHom a)
  have := RingedToposHom.pushforwardModules_additive
    (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X)
  have := isRightAdjoint_pushforwardModules (augmentationRingedToposHom a)
  have := isRightAdjoint_pushforwardModules (bigFppfTotalRingedHom a)
  have := isRightAdjoint_pushforwardModules (bigFppfAugmentationRingedHom a)
  have := isRightAdjoint_pushforwardModules (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X)
  have := RingedToposHom.pushforwardModules_additive (bigFppfTotalRingedSiteHom a).ringedToposHom
  have := RingedToposSiteHom.pushforwardTopos_additive.{u + 1}
    (bigFppfTotalRingedSiteHom a).toRingedToposSiteHom
  have hA := isQuasicoherentOnSite_augmentationRingedToposHom_pullbackModules_obj a F
  have := @isIso_bigFppfTotalRingedHom_unit_app _ _ _ _ a _ hA
  have := isIso_bigFppfAugmentation_unit h
  -- `M = h^*a^*F ≅ a_{fppf}^*a_X^*F` around the square of Stacks 0DHC
  let eM := ((RingedToposHom.pullbackModulesCompIso (bigFppfTotalRingedHom a)
      (augmentationRingedToposHom a)).app F).symm ≪≫
    (bigFppfAugmentationSquareTwoIso a).pullbackModulesIso.app F ≪≫
    (RingedToposHom.pullbackModulesCompIso (bigFppfAugmentationRingedHom a)
      (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X)).app F
  refine Stacks.RightDerivedComp.isZero_rightDerived_of_square_compositeCollapseSquare
    (RingedToposHom.pushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (bigFppfTotalRingedHom a))
    (RingedToposHom.pushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (augmentationRingedToposHom a))
    (RingedToposHom.pushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (bigFppfAugmentationRingedHom a))
    (RingedToposHom.pushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
      (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X))
    (ih := RingedToposHom.pushforwardModules_additive (bigFppfTotalRingedHom a))
    (ia := RingedToposHom.pushforwardModules_additive (augmentationRingedToposHom a))
    (if' := RingedToposHom.pushforwardModules_additive (bigFppfAugmentationRingedHom a))
    (ix := RingedToposHom.pushforwardModules_additive
      (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X))
    ((RingedToposHom.pushforwardModulesCompIso (bigFppfTotalRingedHom a)
        (augmentationRingedToposHom a)).symm ≪≫
      (bigFppfAugmentationSquareTwoIso a).pushforwardModulesIso ≪≫
      RingedToposHom.pushforwardModulesCompIso (bigFppfAugmentationRingedHom a)
        (BigFppfSpaceSite.fppfToSpacesEtaleRingedHom T X))
    (fun Z hZ ↦
      RingedToposHom.isZero_rightDerived_pushforwardModules_obj_pushforwardModules_of_injective
        _ _ Z hZ)
    (fun Z hZ ↦
      RingedToposHom.isZero_rightDerived_pushforwardModules_obj_pushforwardModules_of_injective
        _ _ Z hZ)
    (fun m hm ↦ (@isZero_rightDerived_bigFppfTotal_pushforward_pullbackModules _ _ _ _ a _ hA m
      hm).of_iso
      ((Functor.rightDerivedIsoOfIso
        (RingedSite.Hom.pushforwardToposIso (bigFppfTotalRingedSiteHom a)) m).app _))
    (fun m hm ↦ (isZero_rightDerived_bigFppfAugmentation_pushforwardModules_pullbackModules h
      _ m hm).of_iso
        (((RingedToposHom.pushforwardModules (bigFppfAugmentationRingedHom a)).rightDerived
          m).mapIso eM))
    (@asIso _ _ _ _
      ((RingedToposHom.pullbackAdjPushforwardModules (bigFppfTotalRingedHom a)).unit.app _)
      (@isIso_bigFppfTotalRingedHom_unit_app _ _ _ _ a _ hA))
    ((RingedToposHom.pushforwardModules (bigFppfAugmentationRingedHom a)).mapIso eM ≪≫
      (asIso ((RingedToposHom.pullbackAdjPushforwardModules
        (bigFppfAugmentationRingedHom a)).unit.app _)).symm)
    (isZero_rightDerived_fppfToSpacesEtaleRingedHom_pushforwardModules_pullbackModules T X F) n hn

/-- **Stacks 0DHE.** Let `S` be a scheme, `X` an algebraic space over `S`, `U` a simplicial
algebraic space over `S` and `a : U → X` an augmentation which is an fppf hypercovering of `X`,
with `a : (Sh(U_{étale}), 𝒪_U) ⟶ (Sh(X_{étale}), 𝒪_X)` the morphism of ringed topoi of
Stacks 0DE7. For a quasi-coherent `𝒪_X`-module `F` the map `F ⟶ Ra_*(a^*F)` is an
isomorphism: the unit `F ⟶ a_*a^*F` is invertible and `Rⁿa_*(a^*F) = 0` for `n > 0`. -/
theorem isIso_unit_and_isZero_rightDerived_of_isHypercoveringAugmentation
    (F : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1}
      (J := (SpacesEtale.topology T.schemeSite S T.scheme_mem X))
      (SpacesEtale.structureSheaf T.schemeSite S T.scheme_mem X)))
    [F.IsQuasicoherentOnSite] :
    haveI := RingedToposHom.pushforwardModules_additive (augmentationRingedToposHom a)
    IsIso ((RingedToposHom.pullbackAdjPushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
        (augmentationRingedToposHom a)).unit.app F) ∧
      ∀ n : ℕ, 0 < n →
        IsZero (((RingedToposHom.pushforwardModules.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
          (augmentationRingedToposHom a)).rightDerived n).obj
          ((Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
            u + 1, u + 1, u + 1} (augmentationRingedToposHom a).toModulesHom).obj F)) :=
  ⟨isIso_augmentationRingedToposHom_unit_app h F,
    isZero_rightDerived_augmentationRingedToposHom_pushforwardModules_pullbackModules h F⟩

end

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
