module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfModuleRightAcyclic

/-!
# The canonical map `π_X^*𝓕 ⟶ ε_{X,*}(a_X^*𝓕)` is an isomorphism

Let `X` be an algebraic space and `𝓕` a quasi-coherent `𝒪_X`-module. The map
`π_X^*𝓕 ⟶ Rε_{X,*}(a_X^*𝓕)` of Stacks 0DGP is the unit `π_X^*𝓕 ⟶ ε_{X,*}ε_X^*π_X^*𝓕` of
`ε_X^* ⊣ ε_{X,*}` followed by the direct image of the identification `ε_X^*π_X^* ≅ a_X^*` coming
from `a_X = π_X ∘ ε_X` (Stacks 0DGM), and then by `ε_{X,*} ⟶ Rε_{X,*}`. This file constructs the
underived map and proves it is an isomorphism, `a_X^*𝓕` being right acyclic for `ε_{X,*}`.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.pullbackToposIsoCompBigEtale`: `a_X^* ≅ ε_X^* ∘ π_X^*`,
  the pseudofunctoriality isomorphism of `a_X = π_X ∘ ε_X`.
* `AlgebraicGeometry.BigFppfSpaceSite.bigEtalePullbackToPushforwardPullback`: the canonical map
  `π_X^*𝓕 ⟶ ε_{X,*}(a_X^*𝓕)`.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isIso_bigEtalePullbackToPushforwardPullback`: Stacks 0DGP.

## References

* [Stacks Project, Tag 0DGP](https://stacks.math.columbia.edu/tag/0DGP)
* [Stacks Project, Tag 0DGM](https://stacks.math.columbia.edu/tag/0DGM)
* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry.RingedToposSiteHom

variable {X Y Z : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The pseudofunctoriality isomorphism `k^* ≅ f^* ∘ g^*` of pullbacks of sheaves of modules
along a morphism `k` written as a composite `g ∘ f` (Stacks 03D6). -/
noncomputable def pullbackToposIsoOfCompEq (g : RingedToposSiteHom Y Z)
    (f : RingedToposSiteHom X Y) (k : RingedToposSiteHom X Z) (hk : g.comp f = k) :
    k.pullbackTopos ≅ g.pullbackTopos ⋙ f.pullbackTopos := by
  subst hk
  exact (pullbackToposComp g f).symm

end AlgebraicGeometry.RingedToposSiteHom

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite) (X : T.Spaces)

/-- **`a_X^* ≅ ε_X^* ∘ π_X^*`**: the comparison of pullbacks along the factorization
`a_X = π_X ∘ ε_X` of Stacks 0DGM, the spaces-étale site of `X` being read on the big étale site
through `toEtaleSpaceModules`. Once the fppf site of schemes of `E` is identified with that of
`T` along `h`, the composite `π_X ∘ ε_X` is `a_X` and this is the pseudofunctoriality
isomorphism of pullbacks. -/
noncomputable def pullbackToposIsoCompBigEtale :
    (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos ≅
      toEtaleSpaceModules T E h X ⋙
        (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
          (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos ⋙
        (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pullbackTopos := by
  cases E with
  | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
      eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
    change T.schemeSite = eFppfSite at h
    cases h
    let E' : BigEtaleSpaceSite S := ⟨eSchemeSite, eSchemeMem, T.schemeSite, eFppfMem, eInitial,
      eInitialSmall, eInitialEtale, eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite,
      eRepresentative⟩
    have hcomp : (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E'
        (etaleSpace T E' rfl X)).toRingedToposSiteHom.comp
        (fppfToBigEtaleRingedHom T E' rfl X).toRingedToposSiteHom =
        (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom := by
      refine RingedToposSiteHom.ext_of_heq _ _ rfl (heq_of_eq ?_)
      apply ObjectProperty.hom_ext
      apply NatTrans.ext
      funext U
      ext x
      rfl
    refine (RingedToposSiteHom.pullbackToposIsoOfCompEq.{u + 1}
        (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E'
          (etaleSpace T E' rfl X)).toRingedToposSiteHom
        (fppfToBigEtaleRingedHom T E' rfl X).toRingedToposSiteHom
        (fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom hcomp).trans ?_
    exact Functor.isoWhiskerRight (Iso.refl _) _ ≪≫ (Functor.leftUnitor _).symm

/-- **The canonical map `π_X^*𝓕 ⟶ ε_{X,*}(a_X^*𝓕)`** of Stacks 0DGP: the unit of
`ε_X^* ⊣ ε_{X,*}` at `π_X^*𝓕`, followed by the direct image of the identification
`ε_X^*π_X^*𝓕 ≅ a_X^*𝓕` of `a_X = π_X ∘ ε_X`. -/
noncomputable def bigEtalePullbackToPushforwardPullback
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O)) :
    (BigEtaleSpaceSite.spacesEtaleRestrictionRingedSiteHom E
        (etaleSpace T E h X)).toRingedToposSiteHom.pullbackTopos.obj
          ((toEtaleSpaceModules T E h X).obj F) ⟶
      (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos.obj
        ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F) :=
  (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.unit.app
      _ ≫
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos.map
      ((pullbackToposIsoCompBigEtale T E h X).inv.app F)

attribute [local instance] HasDerivedCategory.standard enoughInjectives_bigFppfModules
  abelian_bigEtaleRingedToposModules

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- **Stacks 0DGP: the map `π_X^*𝓕 ⟶ Rε_{X,*}(a_X^*𝓕)` is an isomorphism** for a quasi-coherent
`𝒪_X`-module `𝓕`: the canonical map `π_X^*𝓕 ⟶ ε_{X,*}(a_X^*𝓕)` is an isomorphism (Stacks 0DGN
(6)) and `a_X^*𝓕` is right acyclic for `ε_{X,*}` (Stacks 0DGN (7)), so that the canonical map
`ε_{X,*}(a_X^*𝓕) ⟶ Rε_{X,*}(a_X^*𝓕)` is an isomorphism too. -/
@[stacks 0DGP "(1) the canonical map π_X^*𝓕 ⟶ ε_{X,*}a_X^*𝓕 (unit of ε_X^* ⊣ ε_{X,*} and \
a_X = π_X ∘ ε_X) is an isomorphism, and ε_{X,*}a_X^*𝓕 ⟶ Rε_{X,*}a_X^*𝓕 is an isomorphism"]
theorem isIso_bigEtalePullbackToPushforwardPullback
    (F : SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.spacesEtaleRingedSite T.schemeSite S T.scheme_mem X).O))
    [hF : F.IsQuasicoherentOnSite] :
    IsIso (bigEtalePullbackToPushforwardPullback T E h X F) ∧
      Functor.rightAcyclic.{u + 2, u + 2}
        (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pushforwardTopos
        ((fppfToSpacesEtaleRingedSiteHom T X).toRingedToposSiteHom.pullbackTopos.obj F) := by
  have : ((toEtaleSpaceModules T E h X).obj F).IsQuasicoherentOnSite := by
    cases E
    cases h
    exact hF
  have := isIso_fppfToBigEtale_unit_app_pullback T E h X ((toEtaleSpaceModules T E h X).obj F)
  exact ⟨inferInstanceAs (IsIso (_ ≫ _)), rightAcyclic_fppfToBigEtale_pushforward_pullback E h F⟩

end AlgebraicGeometry.BigFppfSpaceSite
