module

public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveQcoh.EtaleAcyclicity
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineMorphismCohomologyIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.LimitSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ImageSystemProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactEtaleOverArtinian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpBaseChange

/-!
# Artinian direct images are acyclic on quasi-compact quasi-separated étale spaces

Let `X` be a quasi-separated algebraic space over a scheme `S`, let `g : U ⟶ X` be étale with `U`
quasi-compact and quasi-separated, and let `ℱ = (Z ⟶ X)_*𝒢` be the direct image of a coherent
module `𝒢` on the spectrum `Z` of an Artinian ring.  This file proves

```
H^p(U, ℱ|_U) = 0   for p > 0,
```

which is the step of the proof of Stacks 09TL, part (1), about the terms `ℱ_i` of the Artinian
presentation of Stacks 09TJ.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_iso_schemeSpace`: a
  quasi-coherent module on an algebraic space isomorphic to an affine scheme of the site has no
  higher cohomology.
* `AlgebraicGeometry.Space.isZero_etaleRestrictionCohomology_of_isArtinianPushforward`: the
  vanishing above.
* `AlgebraicGeometry.Space.isZeroEtaleRestrictionCohomologyOfArtinian`: the same, in the form of
  the hypothesis `hartin` of the conditional Stacks 09TL, part (1),
  `AlgebraicGeometry.Space.IsZeroEtaleRestrictionCohomologyOfArtinian`.

## Implementation notes

The argument is the source's.  The morphism `Z ⟶ X` is affine by Stacks 09TF
(`AlgebraicGeometry.Space.isAffineHom_of_isLocallyArtinian`), hence so is its base change
`Z ×_X U ⟶ U` by Stacks 03WI, and by étale base change, Stacks 03LX
(`AlgebraicGeometry.Space.modulePushforwardEtaleBaseChangeIso`),
`ℱ|_U = (Z ×_X U ⟶ U)_*𝒢'` with `𝒢'` the restriction of `𝒢`, which is quasi-coherent.  The Leray
collapse along the affine morphism, Stacks 0D2U
(`AlgebraicGeometry.Space.cohomologyIsoOfIsAffineHom`), identifies `H^p(U, ℱ|_U)` with
`H^p(Z ×_X U, 𝒢')`.  Finally `Z ×_X U` is affine — this is the source's "since `Z_i ×_X U` is
affine": it is quasi-compact and quasi-separated, being affine over `U`, and étale over the
spectrum of an Artinian ring, so it is affine by
`AlgebraicGeometry.Space.exists_iso_yoneda_isAffine_of_etale_over_isLocallyArtinian` — and a
quasi-coherent module has no higher cohomology on an affine.

The cohomology groups are module-valued; the comparison of Stacks 0D2U is an isomorphism of the
underlying abelian groups, which is enough because a module is zero exactly when its underlying
abelian group is.

## References

* [Stacks Project, Tag 09TL](https://stacks.math.columbia.edu/tag/09TL)
* [Stacks Project, Tag 09TF](https://stacks.math.columbia.edu/tag/09TF)
* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 03LX](https://stacks.math.columbia.edu/tag/03LX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteModules

attribute [local instance 5000] SheafOfModules.instAbelian

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A module is zero as soon as its underlying abelian group is. -/
theorem isZero_of_isZero_forget₂_addCommGrpCat {R : Type*} [Ring R] {M : ModuleCat.{u + 1} R}
    (h : IsZero ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj M)) : IsZero M :=
  ModuleCat.isZero_iff_subsingleton.2 (AddCommGrpCat.isZero_iff_subsingleton.1 h)

/-- An affine object of the site whose ring of global functions is Artinian is a locally
Artinian scheme. -/
theorem isLocallyArtinian_of_isArtinianRing_globalSections (Z : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    [IsArtinianRing Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)] :
    IsLocallyArtinian ((BigFppfOver.toScheme B S hS).obj Z) :=
  have : IsLocallyArtinian (Spec Γ((BigFppfOver.toScheme B S hS).obj Z, ⊤)) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  .of_isImmersion ((BigFppfOver.toScheme B S hS).obj Z).isoSpec.hom

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules in
/-- **A quasi-coherent module on an algebraic space isomorphic to an affine scheme of the site
has no higher cohomology** on the small étale site.

The isomorphism `P ≅ h_T` is an affine morphism, so Stacks 0D2U
(`AlgebraicGeometry.Space.cohomologyIsoOfIsAffineHom`) identifies the cohomology of `𝓜` with
that of its direct image to `h_T`, which is quasi-coherent by Stacks 07U8 and has no higher
cohomology on the affine `T` by
`AlgebraicGeometry.Space.isZero_rightDerived_globalSectionsFunctor_of_isAffine`. -/
theorem isZero_rightDerived_globalSectionsFunctor_of_iso_schemeSpace
    {P : AlgebraicSpaces B S hS} (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (ε : P ≅ schemeSpace T)
    (M : Modules.{u, u} B S hS P.1 P.2) (hM : M.IsQuasicoherentOnSite) (n : ℕ) (hn : 0 < n) :
    IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS P.1 P.2).O)).rightDerived
        n).obj M) := by
  have : IsIso ε.hom.hom := (ObjectProperty.ι _).map_isIso ε.hom
  have hε : IsAffineHom B S hS ε.hom.hom := isAffineHom_of_isIso ε.hom.hom
  refine isZero_of_isZero_forget₂_addCommGrpCat ?_
  refine IsZero.of_iso ?_ (cohomologyIsoOfIsAffineHom B S hS ε.hom hε M hM n)
  exact (forget₂ _ AddCommGrpCat.{u + 1}).map_isZero
    (isZero_rightDerived_globalSectionsFunctor_of_isAffine B S hS T hT _
      (isQuasicoherentOnSite_modulePushforward_isAffineHom B S hS ε.hom hε M hM) n hn)

attribute [local instance] hasInjectiveResolutions_modules enoughInjectives_modules in
/-- **The Artinian case of the proof of Stacks 09TL, part (1).**  Let `X` be a quasi-separated
algebraic space, `g : U ⟶ X` an étale morphism from a quasi-compact and quasi-separated algebraic
space and `ℱ` a quasi-coherent `𝒪_X`-module of the form `(Z ⟶ X)_*𝒢` with `Z` the spectrum of
an Artinian ring and `𝒢` coherent.  Then `H^p(U, ℱ|_U) = 0` for `p > 0`. -/
theorem isZero_etaleRestrictionCohomology_of_isArtinianPushforward
    (hZ : B.Contains (⊤_ Scheme.{u})) {X U : AlgebraicSpaces B S hS}
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (g : U ⟶ X) (hg : IsEtale B S hS g.hom)
    (hUqc : IsQuasiCompactSpace B S hS U.1) (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1)
    (p : ℕ) (hp : 0 < p) (M : QuasicoherentSheaves.{u, u} B S hS X.1 X.2)
    (hM : IsArtinianPushforward B S hS X M.obj) :
    IsZero ((etaleRestrictionCohomology B S hS g hg p).obj M) := by
  obtain ⟨Z, hZaff, hZart, gZ, G, hG, ⟨e⟩⟩ := hM
  have := isLocallyArtinian_of_isArtinianRing_globalSections B S hS Z
  -- the base change `P = Z ×_X U`, with its two projections
  let P := AlgebraicSpaces.fiberProduct B S hS gZ g
  have sq := AlgebraicSpaces.isPullback_fiberProduct B S hS gZ g
  let fst : P ⟶ schemeSpace Z := ObjectProperty.homMk (pullback.fst gZ.hom g.hom)
  let snd : P ⟶ U := ObjectProperty.homMk (pullback.snd gZ.hom g.hom)
  have hfst : IsEtale B S hS fst.hom := isEtale_of_isPullback B S hS snd fst g gZ sq.flip hg
  have hgZ : IsAffineHom B S hS gZ.hom :=
    isAffineHom_of_isLocallyArtinian B S hS hZ X.2 hXqs Z gZ.hom
  have hsnd : IsAffineHom B S hS snd.hom :=
    IsAffineHom.of_isPullback (AlgebraicSpaces.isPullback_hom B S hS sq) hgZ
  -- `P` is quasi-compact and quasi-separated, being affine over `U`
  have hPqc : IsQuasiCompactSpace B S hS P.1 :=
    isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 U.1) snd.hom))
      (isQuasiCompact_of_isAffineHom' B S hS snd.hom P.2 U.2 hsnd U.1 U.2 hUqc (𝟙 U.1))
  have hPqs : IsAbsolutelyQuasiSeparated B S hS hZ P.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ P.2 hUqs
      (isQuasiSeparated_of_isAffineHom B S hS snd.hom P.2 U.2 hsnd)
  -- hence affine, being étale over the spectrum of an Artinian ring
  obtain ⟨T, eT, hT⟩ := exists_iso_yoneda_isAffine_of_etale_over_isLocallyArtinian B S hS hZ
    P.2 fst.hom hfst hPqc hPqs
  let ε : P ≅ schemeSpace T := (ObjectProperty.fullyFaithfulι _).preimageIso eT
  -- the restriction of `𝒢` to `P` is quasi-coherent
  have hG' : ((etaleModulePullback B S hS fst hfst).obj G).IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_etaleModulePullback B S hS fst hfst G hG.toIsQuasicoherentOnSite
  -- étale base change identifies `ℱ|_U` with the direct image of that restriction
  let b : (etaleModulePullback B S hS g hg).obj M.obj ≅
      (modulePushforward B S hS snd).obj ((etaleModulePullback B S hS fst hfst).obj G) :=
    (etaleModulePullback B S hS g hg).mapIso e.symm ≪≫
      ((modulePushforwardEtaleBaseChangeIso B S hS fst snd gZ g sq hg).app G).symm
  refine IsZero.of_iso ?_ (((globalSectionsFunctor.{u + 1, u, u, u}
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS U.1 U.2).O)).rightDerived p).mapIso b)
  refine isZero_of_isZero_forget₂_addCommGrpCat ?_
  refine IsZero.of_iso ?_ (cohomologyIsoOfIsAffineHom B S hS snd hsnd _ hG' p).symm
  exact (forget₂ _ AddCommGrpCat.{u + 1}).map_isZero
    (isZero_rightDerived_globalSectionsFunctor_of_iso_schemeSpace B S hS T hT ε _ hG' p hp)

/-- **The hypothesis `hartin` of the conditional Stacks 09TL, part (1), discharged**, for a
quasi-separated `X` and a quasi-compact and quasi-separated `U` étale over it. -/
theorem isZeroEtaleRestrictionCohomologyOfArtinian
    (hZ : B.Contains (⊤_ Scheme.{u})) {X U : AlgebraicSpaces B S hS}
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (g : U ⟶ X) (hg : IsEtale B S hS g.hom)
    (hUqc : IsQuasiCompactSpace B S hS U.1) (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1)
    (p : ℕ) : IsZeroEtaleRestrictionCohomologyOfArtinian B S hS g hg p :=
  fun hp M hM =>
    isZero_etaleRestrictionCohomology_of_isArtinianPushforward B S hS hZ hXqs g hg hUqc hUqs p hp
      M hM

end AlgebraicGeometry.Space

end

end
