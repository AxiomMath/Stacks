module

public import Mathlib.Tactic.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.InternalHom
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineModuleExtension
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineRingedToposTopologies
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteCartesianModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.AffineSiteEtaleSmooth

/-!
# Quasi-coherent modules and affines, for a category fibred in groupoids

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. Its affine subcategory
`𝒳_{affine}` of Stacks 0H0A carries, for each of the five standard topologies on the affine
schemes over `S`, an inherited topology, and the restriction `𝒪` of the structure sheaf of
Stacks 06TV along the inclusion `𝒳_{affine} ⥤ 𝒳`. For a sheaf of modules `𝓕` on such a ringed
site and an arrow `x ⟶ x'` of `𝒳_{affine}`, extension of scalars along `𝒪(x') ⟶ 𝒪(x)` produces
a base-change map `𝓕(x') ⊗_{𝒪(x')} 𝒪(x) ⟶ 𝓕(x)`.

This file proves Stacks 0H0E: the base-change maps of an `𝒪`-module `𝓕` on `𝒳_{affine}` are all
isomorphisms exactly when `𝓕` is quasi-coherent on the chaotic affine site of Stacks 0H09,
exactly when it is a quasi-coherent sheaf for any one of the five topologies, and exactly when it
corresponds to a quasi-coherent module on `𝒳` under the equivalence of Stacks 0H0C.

## Main definitions

* `AlgebraicGeometry.Stack.AffineCategory.siteKindRingedSite`: the ringed site
  `(𝒳_{affine, τ}, 𝒪)` for each of the five topologies `τ`; its chaotic reading is the ringed
  site `(𝒳_{affine}, 𝒪)` of Stacks 0H0D.
* `AlgebraicGeometry.Stack.AffineCategory.ringedSite`: the same for an arbitrary topology on the
  affine schemes over `S` for which the affine inclusion is continuous.

## Main results

* `AlgebraicGeometry.Stack.AffineCategory.tfae_isQuasicoherent`: **Stacks 0H0E**, the
  equivalence of the eight conditions.
* `AlgebraicGeometry.Stack.AffineCategory.isQuasicoherentOnSite_chaotic_iff_canonicalMap_isIso`:
  the equivalence of conditions (1) and (2), by Stacks 0GZN.

## Implementation notes

The proof follows the source. Conditions (1) and (2) are equivalent by Stacks 0GZN. Condition
(1) implies that `𝓕` is a sheaf for each of the five topologies by faithfully flat descent,
Stacks 023M, because every covering of `𝒳_{affine, τ}` is refined by a finite flat covering of
affine schemes (`AlgebraicGeometry.Stack.AffineCategory.isSheaf_of_cartesian`), and that it is
quasi-coherent there because it is on the chaotic site. Conversely a quasi-coherent sheaf on
`𝒳_{affine, τ}` satisfies condition (1)
(`AlgebraicGeometry.Stack.AffineCategory.isIso_restrictionBaseChange_of_isQuasicoherentOnSite`),
which is the content of Descent, Proposition 03DX used in the source through Stacks 0GZV. For
condition (8), restriction along the affine inclusion is the inverse image of the equivalence of
ringed topoi of Stacks 0H0C; on sheaves of modules with sections in the universe of the schemes
it is an equivalence (`AlgebraicGeometry.Stack.AffineCategory.isEquivalence_moduleRestriction`),
and quasi-coherence is carried by it in both directions, which is the intrinsic nature of
quasi-coherence, Stacks 03DM.

Condition (8) is stated for the fppf topology on `𝒳`, the topology with which the modules on a
category fibred in groupoids over `(Sch/S)_{fppf}` are defined in the source, and whose affine
version is condition (7), as in the source's proof.

## References

* [Stacks Project, Tag 0H0E](https://stacks.math.columbia.edu/tag/0H0E)
* [Stacks Project, Tag 0GZN](https://stacks.math.columbia.edu/tag/0GZN)
* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0H0C](https://stacks.math.columbia.edu/tag/0H0C)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack.AffineCategory

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (τ : SiteKind)
  (J : GrothendieckTopology (BigAffineFppf B S hS))

section

variable [(inclusion B S hS p).IsContinuous (associatedAffineTopology B S hS p J)
  (BigFppfOver.associatedTopology B S hS p τ)]

/-- **The ringed site `(𝒳_{affine}, 𝒪)` of Stacks 0H0E.** The affine subcategory of Stacks 0H0A
with an inherited topology, carrying the restriction along the affine inclusion of the
structure sheaf of Stacks 06TV. -/
noncomputable abbrev ringedSite : RingedSite.{v, w, u} :=
  affineRingedSite (associatedAffineTopology B S hS p J)
    (BigFppfOver.associatedTopology B S hS p τ) (inclusion B S hS p)
    (FibredSite.structureSheaf B S hS p hp τ)

/-- The chaotic reading of the affine ringed site carries exactly the associated affine chaotic
topology of Stacks 0H09, so the quasi-coherence it measures is the one of condition (2) of
Stacks 0H0E. -/
theorem chaotic_ringedSite_J :
    (ringedSite B S hS p hp τ J).chaotic.J = associatedAffineChaoticTopology B S hS p :=
  rfl

/-- **The equivalence of conditions (1) and (2) of Stacks 0H0E**, by Stacks 0GZN. A module on
the affine subcategory of a category fibred in groupoids, carrying the chaotic topology of
Stacks 0H09, is quasi-coherent in the sense of Stacks 03DL(6) exactly when every base-change
map `𝓕(x') ⊗_{𝒪(x')} 𝒪(x) ⟶ 𝓕(x)` is an isomorphism. -/
theorem isQuasicoherentOnSite_chaotic_iff_canonicalMap_isIso
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS p hp τ J).chaotic.O)) :
    F.IsQuasicoherentOnSite ↔
      ∀ ⦃x y : AffineCategory B S hS p⦄ (f : x ⟶ y),
        IsIso (Stacks.SheafOfModules.canonicalMap
          (ringedSite B S hS p hp τ J).chaotic F f) :=
  Stacks.SheafOfModules.isQuasicoherent_iff_canonicalMap_isIso _ F rfl

/-- **The quasi-coherence half of the passage from condition (1) to conditions (3)–(7) of
Stacks 0H0E.** A sheaf of modules on the affine subcategory of a category fibred in groupoids,
for an inherited topology, all of whose base-change maps `𝓕(x') ⊗_{𝒪(x')} 𝒪(x) ⟶ 𝓕(x)` are
isomorphisms, is quasi-coherent on the ringed site `(𝒳_{affine}, 𝒪)`. -/
theorem isQuasicoherentOnSite_of_canonicalMap_isIso
    (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS p hp τ J).O))
    (h : ∀ ⦃x y : AffineCategory B S hS p⦄ (f : x ⟶ y),
      IsIso (Stacks.SheafOfModules.canonicalMap (ringedSite B S hS p hp τ J) F f)) :
    F.IsQuasicoherentOnSite :=
  Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso _ F h

end

/-- **The passage from condition (8) to condition (7) of Stacks 0H0E, for the module itself.**
The restriction to the affine subcategory of a quasi-coherent module on the ringed site
`(𝒳, 𝒪_𝒳)` is quasi-coherent on `(𝒳_{affine}, 𝒪)`.

Restriction along the affine inclusion is the inverse image of the equivalence of ringed topoi
of Stacks 0H0C. -/
theorem isQuasicoherentOnSite_restriction
    (hbase : (BigAffineFppf.inclusion B S hS).IsDenseSubsite J
      (BigFppfOver.baseOverTopology B S hS τ))
    (M : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp τ))
    (hM : M.IsQuasicoherentOnSite) :
    letI := (inclusion_isSpecialCocontinuous B S hS p hp J
      (BigFppfOver.baseOverTopology B S hS τ) hbase).2
    ((SheafOfModules.pushforward.{u} (F := inclusion B S hS p)
      (R := FibredSite.ringStructureSheafCore B S hS p hp τ)
      (S := (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite B S hS p hp τ J).O)) (𝟙 _)).obj
        M).IsQuasicoherentOnSite :=
  let := (inclusion_isSpecialCocontinuous B S hS p hp J
    (BigFppfOver.baseOverTopology B S hS τ) hbase).2
  Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite _ _ M hM

/-! ### The five associated affine sites and Stacks 0H0E -/

/-- **Stacks 0H0B, in the indexed form.** For each of the five topologies, the inclusion of the
affine subcategory of a category fibred in groupoids is a dense subsite inclusion of the
associated affine site of Stacks 0H0A into the associated site of Stacks 06TP. -/
theorem isDenseSubsite_inclusion_siteKind (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    (inclusion B S hS p).IsDenseSubsite
      (associatedAffineTopology B S hS p (BigAffineFppf.siteKindTopology B S hS τ))
      (BigFppfOver.associatedTopology B S hS p τ) := by
  cases τ with
  | zariski => exact isDenseSubsite_affineInclusion_zariski B S hS p hp
  | etale => exact isDenseSubsite_affineInclusion_etale B S hS p hp
  | smooth => exact isDenseSubsite_affineInclusion_smooth B S hS p hp
  | syntomic => exact isDenseSubsite_affineInclusion_syntomic B S hS p hp
  | fppf => exact isDenseSubsite_affineInclusion_fppf B S hS p hp

/-- **The ringed site `(𝒳_{affine, τ}, 𝒪)` of Stacks 0H0D**, for each of the five topologies of
Stacks 0H0A: the associated affine site carrying the restriction of the structure sheaf of
Stacks 06TV. -/
noncomputable abbrev siteKindRingedSite (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    RingedSite.{v, w, u} :=
  haveI := isDenseSubsite_inclusion_siteKind B S hS p hp τ
  ringedSite B S hS p hp τ (BigAffineFppf.siteKindTopology B S hS τ)

/-- The chaotic reading of `siteKindRingedSite` carries exactly the associated affine chaotic
topology of Stacks 0H09. -/
theorem siteKindRingedSite_chaotic_J (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    (siteKindRingedSite B S hS p hp τ).chaotic.J = associatedAffineChaoticTopology B S hS p :=
  rfl

/-- The ring of sections of `𝒪` at an object of `𝒳_{affine}` is the ring of global functions on
the affine scheme it lies over. -/
theorem siteKindRingedSite_O_obj (hp : p.IsFiberedInGroupoids) (τ : SiteKind) :
    (siteKindRingedSite B S hS p hp τ).O.obj = (toScheme B S hS p).op ⋙ Scheme.Γ :=
  rfl

/-- **Stacks 0H0E.** Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `𝓕`
be an `𝒪`-module on `𝒳_{affine}`, that is, a sheaf of modules on the chaotic ringed site
`(𝒳_{affine}, 𝒪)` of Stacks 0H09 and 0H0D. The following are equivalent:

1. for every morphism `x ⟶ x'` of `𝒳_{affine}` the map
   `𝓕(x') ⊗_{𝒪(x')} 𝒪(x) ⟶ 𝓕(x)` is an isomorphism;
2. `𝓕` is a quasi-coherent module on `(𝒳_{affine}, 𝒪)` in the sense of Stacks 03DL;
3. `𝓕` is a sheaf for the Zariski topology on `𝒳_{affine}` and a quasi-coherent module on
   `(𝒳_{affine, Zar}, 𝒪)`;
4. the same for the étale topology;
5. the same for the smooth topology;
6. the same for the syntomic topology;
7. the same for the fppf topology;
8. `𝓕` corresponds to a quasi-coherent module on `𝒳` via the equivalence of Stacks 0H0C: it is a
   sheaf for the fppf topology, and as such it is isomorphic to the restriction to
   `𝒳_{affine, fppf}` of a quasi-coherent module on `(𝒳_{fppf}, 𝒪_𝒳)`.

The equivalence of Stacks 0H0C is restriction along the affine inclusion, which on sheaves of
modules with sections in the universe of the schemes is an equivalence by
`AlgebraicGeometry.Stack.AffineCategory.isEquivalence_moduleRestriction`; condition (8) asks
that `𝓕` lie in its image of the quasi-coherent modules. -/
@[stacks 0H0E]
theorem tfae_isQuasicoherent (hp : p.IsFiberedInGroupoids)
    (F : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (siteKindRingedSite B S hS p hp .fppf).chaotic.O)) :
    [∀ ⦃x x' : AffineCategory B S hS p⦄ (f : x ⟶ x'),
        IsIso (Stacks.SheafOfModules.canonicalMap
          (siteKindRingedSite B S hS p hp .fppf).chaotic F f),
      F.IsQuasicoherentOnSite,
      ∃ h : Presheaf.IsSheaf (siteKindRingedSite B S hS p hp .zariski).J F.val.presheaf,
        (⟨F.val, h⟩ : SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (siteKindRingedSite B S hS p hp .zariski).O)).IsQuasicoherentOnSite,
      ∃ h : Presheaf.IsSheaf (siteKindRingedSite B S hS p hp .etale).J F.val.presheaf,
        (⟨F.val, h⟩ : SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (siteKindRingedSite B S hS p hp .etale).O)).IsQuasicoherentOnSite,
      ∃ h : Presheaf.IsSheaf (siteKindRingedSite B S hS p hp .smooth).J F.val.presheaf,
        (⟨F.val, h⟩ : SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (siteKindRingedSite B S hS p hp .smooth).O)).IsQuasicoherentOnSite,
      ∃ h : Presheaf.IsSheaf (siteKindRingedSite B S hS p hp .syntomic).J F.val.presheaf,
        (⟨F.val, h⟩ : SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (siteKindRingedSite B S hS p hp .syntomic).O)).IsQuasicoherentOnSite,
      ∃ h : Presheaf.IsSheaf (siteKindRingedSite B S hS p hp .fppf).J F.val.presheaf,
        (⟨F.val, h⟩ : SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (siteKindRingedSite B S hS p hp .fppf).O)).IsQuasicoherentOnSite,
      ∃ h : Presheaf.IsSheaf (siteKindRingedSite B S hS p hp .fppf).J F.val.presheaf,
        letI := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
        ∃ G : SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf),
          G.IsQuasicoherentOnSite ∧
            Nonempty ((Stacks.DenseSubsiteModules.moduleRestriction
              (siteKindRingedSite B S hS p hp .fppf).J
              (BigFppfOver.associatedTopology B S hS p .fppf) (inclusion B S hS p)
              (FibredSite.ringStructureSheafCore B S hS p hp .fppf)).obj G ≅
              (⟨F.val, h⟩ : SheafOfModules.{u}
                (Stacks.SheafOfModules.Tensor.ringSheaf
                  (siteKindRingedSite B S hS p hp .fppf).O)))].TFAE := by
  let R : (AffineCategory B S hS p)ᵒᵖ ⥤ CommRingCat.{u} := (toScheme B S hS p).op ⋙ Scheme.Γ
  -- condition (1) is the cartesian condition on the underlying presheaf of modules
  have hcan : (∀ ⦃x x' : AffineCategory B S hS p⦄ (f : x ⟶ x'),
      IsIso (Stacks.SheafOfModules.canonicalMap
        (siteKindRingedSite B S hS p hp .fppf).chaotic F f)) ↔
      ∀ {X Y : (AffineCategory B S hS p)ᵒᵖ} (f : X ⟶ Y),
        IsIso (Stacks.PresheafOfModules.restrictionBaseChange.{v, w, u, u} (R := R) F.val f) :=
    ⟨fun h _ _ f => h f.unop, fun h _ _ f => h f.op⟩
  -- condition (1) is each of conditions (3)–(7)
  have key : ∀ τ : SiteKind, (∀ ⦃x x' : AffineCategory B S hS p⦄ (f : x ⟶ x'),
      IsIso (Stacks.SheafOfModules.canonicalMap
        (siteKindRingedSite B S hS p hp .fppf).chaotic F f)) ↔
      ∃ h : Presheaf.IsSheaf (siteKindRingedSite B S hS p hp τ).J F.val.presheaf,
        (⟨F.val, h⟩ : SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            (siteKindRingedSite B S hS p hp τ).O)).IsQuasicoherentOnSite := by
    intro τ
    constructor
    · intro h
      have hs : Presheaf.IsSheaf (siteKindRingedSite B S hS p hp τ).J F.val.presheaf :=
        isSheaf_of_cartesian.{u, v, w, u} B S hS p R rfl hp τ F.val (hcan.mp h)
      exact ⟨hs, Stacks.SheafOfModules.isQuasicoherentOnSite_of_canonicalMap_isIso
        (siteKindRingedSite B S hS p hp τ) ⟨F.val, hs⟩ fun _ _ f => h f⟩
    · rintro ⟨h, hq⟩
      exact hcan.mpr fun f => isIso_restrictionBaseChange_of_isQuasicoherentOnSite
        B S hS p R rfl hp τ
        (Stacks.SheafOfModules.Tensor.ringSheaf (siteKindRingedSite B S hS p hp τ).O).property
        ⟨F.val, h⟩ hq f
  tfae_have 1 ↔ 2 :=
    (Stacks.SheafOfModules.isQuasicoherent_iff_canonicalMap_isIso _ F rfl).symm
  tfae_have 1 ↔ 3 := key .zariski
  tfae_have 1 ↔ 4 := key .etale
  tfae_have 1 ↔ 5 := key .smooth
  tfae_have 1 ↔ 6 := key .syntomic
  tfae_have 1 ↔ 7 := key .fppf
  tfae_have 7 → 8 := by
    rintro ⟨h, hq⟩
    let := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
    have := isEquivalence_moduleRestriction B S hS p hp
      (siteKindRingedSite B S hS p hp .fppf).J (BigFppfOver.associatedTopology B S hS p .fppf)
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf)
    let Res := Stacks.DenseSubsiteModules.moduleRestriction
      (siteKindRingedSite B S hS p hp .fppf).J (BigFppfOver.associatedTopology B S hS p .fppf)
      (inclusion B S hS p) (FibredSite.ringStructureSheafCore B S hS p hp .fppf)
    let N : SheafOfModules.{u} (Stacks.DenseSubsiteModules.ringRestriction
        (siteKindRingedSite B S hS p hp .fppf).J (BigFppfOver.associatedTopology B S hS p .fppf)
        (inclusion B S hS p) (FibredSite.ringStructureSheafCore B S hS p hp .fppf)) :=
      ⟨F.val, h⟩
    refine ⟨h, Res.objPreimage N, ?_, ⟨Res.objObjPreimageIso N⟩⟩
    exact isQuasicoherentOnSite_of_moduleRestriction B S hS p _ _ hp _ _
      (SheafOfModules.IsQuasicoherentOnSite.of_iso (Res.objObjPreimageIso N).symm hq)
  tfae_have 8 → 7 := by
    rintro ⟨h, G, hG, ⟨e⟩⟩
    let := isDenseSubsite_inclusion_siteKind B S hS p hp .fppf
    have := (inclusion_isSpecialCocontinuous B S hS p hp (BigAffineFppf.topology B S hS)
      (BigFppfOver.topology B S hS) (bigAffineFppfInclusion_isDenseSubsite B S hS)).1
    exact ⟨h, (Stacks.SheafOfModules.isQuasicoherentOnSite_restrictionAlongSubsite
      (inclusion B S hS p) (FibredSite.ringStructureSheafCore B S hS p hp .fppf) G hG).of_iso e⟩
  tfae_finish

end AlgebraicGeometry.Stack.AffineCategory

end
