module

public import Mathlib.Tactic.TFAE
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.QuasiCoherentModulesAndAffines

/-!
# Stacks 0EM8 with nothing carried

`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SiteEquivalence` states the three clauses of
Stacks 0EM8 as `AlgebraicGeometry.FibredSite.IsQuasicoherentClause`, for a category `𝒳` fibred
in groupoids over the big fppf category of schemes over `S` and a presheaf of modules `𝓕` on
`𝒳`, and proves their equivalence `AlgebraicGeometry.FibredSite.tfae_isQuasicoherentClause` over
two inputs at the Zariski and at the étale topology,
`AlgebraicGeometry.FibredSite.IsSheafFppfOfQuasicoherentOnSite` and
`AlgebraicGeometry.FibredSite.QuasicoherentOnSiteOfLeFppf`.  This file **proves both inputs at
every one of the five topologies** and so obtains Stacks 0EM8 with no hypothesis.

## Main results

* `AlgebraicGeometry.Stack.AffineCategory.isCocontinuous_inclusion_siteKind`: the cocontinuity
  half of Stacks 0H0B, in the indexed form.
* `AlgebraicGeometry.FibredSite.isSheafFppfOfQuasicoherentOnSite_siteKind` and
  `AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_siteKind`: **the two inputs, at every
  one of the five topologies and with no hypothesis**, together with their instances at the
  Zariski and the étale topology,
  `AlgebraicGeometry.FibredSite.isSheafFppfOfQuasicoherentOnSite_zariski`,
  `AlgebraicGeometry.FibredSite.isSheafFppfOfQuasicoherentOnSite_etale`,
  `AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_zariski` and
  `AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_etale`.
* `AlgebraicGeometry.FibredSite.tfae_isQuasicoherentClause'`: **the three-way equivalence of
  Stacks 0EM8**, for a category fibred in groupoids over the big fppf category of schemes over
  `S` and a presheaf of modules on it, with nothing carried.

## How the two inputs are proved

The route is the affine subcategory `𝒳_affine` of Stacks 0H0A, not the slices `𝒳/x` of the
source's proof, and it rests on three results of the library.

The affine inclusion `𝒳_affine ⥤ 𝒳` is a dense subsite inclusion for each of the five
topologies — Stacks 0H0B,
`AlgebraicGeometry.Stack.AffineCategory.isDenseSubsite_inclusion_siteKind` — so restriction along
it is an equivalence on sheaves of abelian groups and on sheaves of modules, which is
Stacks 0H0C:
`AlgebraicGeometry.Stack.AffineCategory.isEquivalence_sheafPushforwardContinuous_addCommGrpCat`
and `AlgebraicGeometry.Stack.AffineCategory.isEquivalence_moduleRestriction`.  A quasi-coherent
sheaf of modules on `𝒳_{affine, τ}` is *cartesian*, that is all its base-change comparisons
`𝒪(x) ⊗_{𝒪(x')} 𝓕(x') ⟶ 𝓕(x)` are isomorphisms:
`AlgebraicGeometry.Stack.AffineCategory.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`.
That implication is the content of Descent, Proposition 03DX which the source's proof of
Stacks 0EM8 uses, and it is where the appeal to that proposition sits in this library.
Conversely a cartesian presheaf of modules on `𝒳_affine` is a sheaf for every one of the five
topologies and quasi-coherent for each of them —
`AlgebraicGeometry.Stack.AffineCategory.isSheaf_of_cartesian` and
`Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso`.  The two implications
together are Stacks 0H0E.  Being cartesian mentions no topology, and that is exactly why it
carries a clause of Stacks 0EM8 from one topology to another.

For the first input: given a `τ`-sheaf of modules `𝓕` on `𝒳` which is quasi-coherent on
`(𝒳_τ, 𝒪_𝒳)`, its restriction to `𝒳_{affine, τ}` is quasi-coherent
(`Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite`), hence cartesian, hence
a sheaf for the affine *fppf* topology.  Restriction being an equivalence for the fppf topology,
there is a sheaf for the inherited fppf topology on `𝒳` with that restriction; restriction being
an equivalence for `τ` as well and `𝓕` being a `τ`-sheaf, that sheaf is isomorphic to `𝓕`
itself.  So `𝓕` is a sheaf for the inherited fppf topology.  This is the library's form of the
source's appeal to Descent, Lemma 03DT: the fppf sheaf condition is produced on the affine
subcategory by faithfully flat descent, Stacks 023M inside
`AlgebraicGeometry.Stack.AffineCategory.isSheaf_of_cartesian`, rather than read off an `𝓗^a`.

For the second input: a global presentation is a cokernel taken in the category of *sheaves* of
modules, so quasi-coherence depends on the topology, and nothing formal carries it from a finer
topology to a coarser one.  The cartesian condition is what crosses that gap: the restriction to
`𝒳_affine` of a module quasi-coherent on `(𝒳_fppf, 𝒪_𝒳)` is cartesian, hence quasi-coherent for
the affine `τ`-topology, and quasi-coherence of the restriction implies quasi-coherence on `𝒳`
by `AlgebraicGeometry.Stack.AffineCategory.isQuasicoherentOnSite_of_moduleRestriction`.

## References

* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 0H0A](https://stacks.math.columbia.edu/tag/0H0A)
* [Stacks Project, Tag 0H0B](https://stacks.math.columbia.edu/tag/0H0B)
* [Stacks Project, Tag 0H0C](https://stacks.math.columbia.edu/tag/0H0C)
* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Stack.AffineCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)

/-- **The cocontinuity half of Stacks 0H0B, in the indexed form.**  For each of the five
topologies the inclusion of the affine subcategory of a category fibred in groupoids is
cocontinuous from the associated affine site of Stacks 0H0A to the associated site of
Stacks 06TP.

`AlgebraicGeometry.Stack.AffineCategory.isDenseSubsite_inclusion_siteKind` is the other half, and
the five instances of `AlgebraicGeometry.Stack.AffineCategory.IsSpecialCocontinuous` they are
taken from are the ones named there.  Both halves are needed to restrict a quasi-coherent module
along the inclusion, and this one is stated here because the proofs of the two inputs of
Stacks 0EM8 below are its only consumer. -/
public theorem isCocontinuous_inclusion_siteKind (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    (inclusion B S hS p).IsCocontinuous
      (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS τ))
      (BigFppfOver.associatedTopology B S hS p τ) := by
  cases τ with
  | zariski =>
    have h := inclusion_isSpecialCocontinuous_zariski B S hS p hp
    rw [B.bigZariskiOver_topology_toBigZariskiSite S hS] at h
    exact h.1
  | etale =>
    have h := inclusion_isSpecialCocontinuous_etale B S hS p hp
    rw [B.bigEtaleOver_topology_toBigEtaleSite S hS] at h
    exact h.1
  | smooth =>
    have h := inclusion_isSpecialCocontinuous_smooth B S hS p hp
    rw [B.bigSmoothOver_topology_toBigSmoothSite S hS] at h
    exact h.1
  | syntomic =>
    have h := inclusion_isSpecialCocontinuous_syntomic B S hS p hp
    rw [B.bigSyntomicOver_topology_toBigSyntomicSite S hS] at h
    exact h.1
  | fppf => exact (inclusion_isSpecialCocontinuous_fppf B S hS p hp).1

end AlgebraicGeometry.Stack.AffineCategory

namespace AlgebraicGeometry.FibredSite

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids)

section Affine

open Stack Stack.AffineCategory

/-- A quasi-coherent sheaf of modules on the associated `τ`-site has cartesian restriction to the
affine subcategory. -/
private theorem isIso_restrictionBaseChange_moduleRestriction (τ : SiteKind)
    [(inclusion B S hS p).IsCocontinuous
      (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS τ))
      (BigFppfOver.associatedTopology B S hS p τ)]
    [(inclusion B S hS p).IsDenseSubsite
      (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS τ))
      (BigFppfOver.associatedTopology B S hS p τ)]
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ)) (hM : M.IsQuasicoherentOnSite)
    {X Y : (AffineCategory B S hS p)ᵒᵖ} (f : X ⟶ Y) :
    IsIso (Stacks.PresheafOfModules.restrictionBaseChange
      (R := (toScheme B S hS p).op ⋙ Scheme.Γ)
      ((Stacks.DenseSubsiteModules.moduleRestriction
        (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS τ))
        (BigFppfOver.associatedTopology B S hS p τ) (inclusion B S hS p)
        (ringStructureSheafCore B S hS p hp τ)).obj M).val f) := by
  exact isIso_restrictionBaseChange_of_isQuasicoherentOnSite B S hS p _ rfl hp τ _ _
    (Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite
      (J := associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS τ))
      (K := BigFppfOver.associatedTopology B S hS p τ)
      (inclusion B S hS p) (ringStructureSheafCore B S hS p hp τ) M hM) f

/-- **The first input of Stacks 0EM8, at every one of the five topologies and with no
hypothesis.**  A sheaf of modules on the associated `τ`-site of a category fibred in groupoids
which is quasi-coherent on `(𝒳_τ, 𝒪_𝒳)` is a sheaf for the inherited fppf topology.

Its restriction to the affine subcategory `𝒳_{affine, τ}` of Stacks 0H0A is quasi-coherent, the
affine inclusion being a cocontinuous dense subsite inclusion at `τ` by Stacks 0H0B; a
quasi-coherent module on `𝒳_{affine, τ}` is cartesian, which is the content of Descent,
Proposition 03DX used in the source's proof; and a cartesian presheaf of modules on
`𝒳_affine` is a sheaf for the affine fppf topology, by faithfully flat descent.  Restriction
along the affine inclusion is an equivalence of sheaf topoi for each of the five topologies
(Stacks 0H0C), so the affine fppf sheaf so obtained extends to a sheaf for the inherited fppf
topology on `𝒳`, and the equivalence at `τ` identifies that extension with the `τ`-sheaf `𝓕`
one started from. -/
public theorem isSheafFppfOfQuasicoherentOnSite_siteKind (τ : SiteKind) :
    IsSheafFppfOfQuasicoherentOnSite B S hS p hp τ := by
  intro M hM
  have dτ := isDenseSubsite_inclusion_siteKind B S hS p hp τ
  have cτ := isCocontinuous_inclusion_siteKind B S hS p hp τ
  have df := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  have hcart := fun {X Y} (f : X ⟶ Y) =>
    isIso_restrictionBaseChange_moduleRestriction B S hS p hp τ M hM f
  have hsh : Presheaf.IsSheaf
      (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .fppf))
      ((inclusion B S hS p).op ⋙ M.val.presheaf) :=
    isSheaf_of_cartesian B S hS p _ rfl hp .fppf _ hcart
  have ef := isEquivalence_sheafPushforwardContinuous_addCommGrpCat B S hS p hp
    (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .fppf))
    (BigFppfOver.associatedTopology B S hS p .fppf)
  have et := isEquivalence_sheafPushforwardContinuous_addCommGrpCat B S hS p hp
    (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS τ))
    (BigFppfOver.associatedTopology B S hS p τ)
  set Φf := (inclusion B S hS p).sheafPushforwardContinuous AddCommGrpCat.{u}
    (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS .fppf))
    (BigFppfOver.associatedTopology B S hS p .fppf)
  set Φt := (inclusion B S hS p).sheafPushforwardContinuous AddCommGrpCat.{u}
    (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS τ))
    (BigFppfOver.associatedTopology B S hS p τ)
  set Z := Φf.objPreimage ⟨(inclusion B S hS p).op ⋙ M.val.presheaf, hsh⟩
  have eZ : Φf.obj Z ≅ ⟨(inclusion B S hS p).op ⋙ M.val.presheaf, hsh⟩ :=
    Φf.objObjPreimageIso _
  have nat : (inclusion B S hS p).op ⋙ Z.obj ≅ (inclusion B S hS p).op ⋙ M.val.presheaf :=
    (sheafToPresheaf _ _).mapIso eZ
  have e : (⟨Z.obj, Z.property.of_le (BigFppfOver.associatedTopology_le_fppf B S hS p τ)⟩ :
      Sheaf (BigFppfOver.associatedTopology B S hS p τ) AddCommGrpCat.{u}) ≅
      ⟨M.val.presheaf, M.isSheaf⟩ :=
    Φt.preimageIso ((sheafToPresheaf _ _).preimageIso nat)
  exact (Presheaf.isSheaf_of_iso_iff ((sheafToPresheaf _ _).mapIso e)).mp Z.property

/-- **The second input of Stacks 0EM8, at every one of the five topologies and with no
hypothesis.**  A sheaf of modules on the inherited fppf site of a category fibred in groupoids
which is quasi-coherent there stays quasi-coherent when read for a coarser associated topology.

Its restriction to `𝒳_{affine, fppf}` is quasi-coherent, hence cartesian by Descent,
Proposition 03DX in the form Stacks 0H0E uses it; being cartesian names no topology, so the same
restriction is quasi-coherent on `𝒳_{affine, τ}`; and a sheaf of modules on `𝒳` whose
restriction to the affine subcategory is quasi-coherent is quasi-coherent, by Stacks 0H0C. -/
public theorem quasicoherentOnSiteOfLeFppf_siteKind (τ : SiteKind) :
    QuasicoherentOnSiteOfLeFppf B S hS p hp τ := by
  intro M hM
  have dτ := isDenseSubsite_inclusion_siteKind B S hS p hp τ
  have df := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
  have cf := isCocontinuous_inclusion_siteKind B S hS p hp .fppf
  refine isQuasicoherentOnSite_of_moduleRestriction B S hS p
    (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS τ))
    (BigFppfOver.associatedTopology B S hS p τ) hp _ _ ?_
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso
    (siteKindRingedSite B S hS p hp τ) _ (fun _ _ f =>
      isIso_restrictionBaseChange_moduleRestriction B S hS p hp .fppf M hM f.op)

end Affine

/-- **`h₁z`: the first input of Stacks 0EM8 at the Zariski topology.**  A Zariski sheaf of
modules which is quasi-coherent on `(𝒳_Zar, 𝒪_𝒳)` is a sheaf for the inherited fppf topology. -/
public theorem isSheafFppfOfQuasicoherentOnSite_zariski :
    IsSheafFppfOfQuasicoherentOnSite B S hS p hp .zariski :=
  isSheafFppfOfQuasicoherentOnSite_siteKind B S hS p hp .zariski

/-- **`h₁e`: the first input of Stacks 0EM8 at the étale topology.**  An étale sheaf of modules
which is quasi-coherent on `(𝒳_ét, 𝒪_𝒳)` is a sheaf for the inherited fppf topology. -/
public theorem isSheafFppfOfQuasicoherentOnSite_etale :
    IsSheafFppfOfQuasicoherentOnSite B S hS p hp .etale :=
  isSheafFppfOfQuasicoherentOnSite_siteKind B S hS p hp .etale

/-- **`h₂z`: the second input of Stacks 0EM8 at the Zariski topology.**  Quasi-coherence on the
inherited fppf site survives being read for the inherited Zariski topology. -/
public theorem quasicoherentOnSiteOfLeFppf_zariski :
    QuasicoherentOnSiteOfLeFppf B S hS p hp .zariski :=
  quasicoherentOnSiteOfLeFppf_siteKind B S hS p hp .zariski

/-- **`h₂e`: the second input of Stacks 0EM8 at the étale topology.**  Quasi-coherence on the
inherited fppf site survives being read for the inherited étale topology. -/
public theorem quasicoherentOnSiteOfLeFppf_etale :
    QuasicoherentOnSiteOfLeFppf B S hS p hp .etale :=
  quasicoherentOnSiteOfLeFppf_siteKind B S hS p hp .etale

/-- **Stacks 0EM8.**  For a category `𝒳` fibred in groupoids over the big fppf category of
schemes over `S` and a presheaf of modules `𝓕` on `𝒳`, the three conditions

1. `𝓕` is an object of `Mod(𝒳_Zar, 𝒪_𝒳)` and is quasi-coherent on `(𝒳_Zar, 𝒪_𝒳)`,
2. `𝓕` is an object of `Mod(𝒳_ét, 𝒪_𝒳)` and is quasi-coherent on `(𝒳_ét, 𝒪_𝒳)`,
3. `𝓕` is a quasi-coherent module on `𝒳` in the sense of Stacks 06WG, that is on
   `(𝒳_fppf, 𝒪_𝒳)`,

are equivalent.

This is `AlgebraicGeometry.FibredSite.tfae_isQuasicoherentClause` with its four hypotheses
discharged by `AlgebraicGeometry.FibredSite.isSheafFppfOfQuasicoherentOnSite_zariski`,
`AlgebraicGeometry.FibredSite.isSheafFppfOfQuasicoherentOnSite_etale`,
`AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_zariski` and
`AlgebraicGeometry.FibredSite.quasicoherentOnSiteOfLeFppf_etale`. -/
@[stacks 0EM8 "the three-way equivalence of the conditions at the Zariski, étale and fppf \
topologies (a sheaf for the inherited topology and quasi-coherent on that ringed site), for any \
category fibred in groupoids over (Sch/S)_fppf and any presheaf of modules on it; the inputs are \
proved by isSheafFppfOfQuasicoherentOnSite_siteKind and quasicoherentOnSiteOfLeFppf_siteKind"]
public theorem tfae_isQuasicoherentClause'
    (𝓕 : PresheafOfModules.{u} (structureRingPresheaf B S hS p hp)) :
    [IsQuasicoherentClause B S hS p hp .zariski 𝓕,
      IsQuasicoherentClause B S hS p hp .etale 𝓕,
      IsQuasicoherentClause B S hS p hp .fppf 𝓕].TFAE :=
  tfae_isQuasicoherentClause B S hS p hp
    (isSheafFppfOfQuasicoherentOnSite_zariski B S hS p hp)
    (isSheafFppfOfQuasicoherentOnSite_etale B S hS p hp)
    (quasicoherentOnSiteOfLeFppf_zariski B S hS p hp)
    (quasicoherentOnSiteOfLeFppf_etale B S hS p hp) 𝓕

end AlgebraicGeometry.FibredSite

end
