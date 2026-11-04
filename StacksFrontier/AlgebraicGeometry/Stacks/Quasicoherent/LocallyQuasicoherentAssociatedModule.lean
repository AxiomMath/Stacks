module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherent

/-!
# The quasi-coherent module below a locally quasi-coherent module (Stacks 076T, first step)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `F` be a presheaf of
modules over the structure sheaf of **Stacks 06TV** which is locally quasi-coherent
(**Stacks 06WJ**). The proof of **Stacks 076T** opens with "the restriction
`𝒢 = F|_{U_ét}` is quasi-coherent" and closes with "the sheaf condition for `𝒢^a` on
`(Sch/U)_{fppf}` … holds by Descent, Lemma 35.8.1". Between those two sentences the letter `𝒢`
changes meaning: local quasi-coherence makes `F|_{U_ét}` quasi-coherent *on the small étale
site* (**Stacks 03DL**(6)), while `𝒢^a` is formed from a quasi-coherent `𝒪_U`-module.

This file supplies that passage and the sheaf condition which follows it, with no hypothesis:

* the module `F|_{U_ét}` is `𝓕^a` for an honest quasi-coherent `𝒪_U`-module `𝓕`, because
  `𝓕 ↦ 𝓕^a` is essentially surjective onto the quasi-coherent modules of the small étale site —
  **Stacks 03DX**(2) at `τ = étale`, which this repository proves unconditionally as
  `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`;
* the pullback-sections presheaf of that `𝓕` on the big fppf site of `U` is an fppf sheaf —
  Descent, **Stacks 03DT**, which this repository also proves unconditionally as
  `AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology`.

So both named inputs of the source's proof are available at every object of `𝒳`, and what the
step carried by
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FppfSheafFromFlatBaseChange.lean` still
needs is only the identification of the two sheaf conditions — the word "equivalent" in the
source's proof — and not either of the two results it rests on.

## Main results

* `AlgebraicGeometry.Stack.exists_associatedModule_iso_restrictModuleToSmallEtale`: **the
  restriction of a locally quasi-coherent module to the small étale site of the scheme below an
  object is `𝓕^a` for a quasi-coherent module `𝓕` on that scheme.**
* `AlgebraicGeometry.Stack.exists_isSheaf_sectionsPresheafOfModules_of_isLocallyQuasicoherent`:
  **the `𝒢^a` of the source's proof of Stacks 076T exists and is a sheaf for the fppf topology
  of `(Sch/U)_{fppf}`.**

## Implementation notes

The quasi-coherent module is produced as an object of the full subcategory
`SheafOfModules.isQuasicoherent U.ringCatSheaf`, which is where
`AlgebraicGeometry.SmallEtale.associatedModuleQcoh` takes its argument and where
`CategoryTheory.Functor.essImage` therefore places it. The second statement reads it back as a
`AlgebraicGeometry.Scheme.Modules` together with its quasi-coherence, so that
`AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules` applies; the instance argument of that
definition is passed explicitly, since inside an existential there is no instance to find.

The module universe is the universe `u` of the schemes. It is forced on both sides: local
quasi-coherence is read through `SheafOfModules.IsQuasicoherentOnSite` at the universes of the
small étale site, and the essential surjectivity of Stacks 03DX(2) is stated at those same
universes.

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **The first step of the proof of Stacks 076T.** For a locally quasi-coherent presheaf of
modules `F` and an object `x` of `𝒳` lying over a scheme `U`, the restriction `F|_{U_ét}` of
**Stacks 06WJ** is the module `𝓕^a` associated with a quasi-coherent `𝒪_U`-module `𝓕`.

Local quasi-coherence gives the restriction as a sheaf of modules on the small étale site of `U`
which is quasi-coherent there, in the sense of **Stacks 03DL**(6); `𝓕 ↦ 𝓕^a` is essentially
surjective onto those by **Stacks 03DX**(2) at `τ = étale`. -/
theorem exists_associatedModule_iso_restrictModuleToSmallEtale
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F) (x : 𝒳) :
    ∃ (hM : Presheaf.IsSheaf
          (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
          (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
            (etaleTopology_le_topology B) F).presheaf)
        (𝓕 : (SheafOfModules.isQuasicoherent
          ((p.obj x).left.1).ringCatSheaf).FullSubcategory),
      Nonempty ((SmallEtale.associatedModuleQcoh E (p.obj x).left.1
            (contains_base B E h S hS p x)).obj 𝓕 ≅
        (⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B) F, hM⟩ :
          SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
            (contains_base B E h S hS p x)))) := by
  obtain ⟨hM, hqc⟩ := hlqc.2 x
  obtain ⟨𝓕, e⟩ := SmallEtale.quasicoherentIsEssImageAssociatedModule E (p.obj x).left.1
    (contains_base B E h S hS p x) _ hqc
  exact ⟨hM, 𝓕, e⟩

/-- **The two named inputs of the proof of Stacks 076T, at one object, with no hypothesis.** For
a locally quasi-coherent presheaf of modules `F` and an object `x` of `𝒳` lying over a scheme
`U` there is a quasi-coherent `𝒪_U`-module `𝓕` whose associated module on the small étale site
of `U` is `F|_{U_ét}` and whose pullback-sections presheaf `𝓕^a` on `(Sch/U)_{fppf}` is a sheaf
for the fppf topology.

The first clause is
`AlgebraicGeometry.Stack.exists_associatedModule_iso_restrictModuleToSmallEtale`, the second is
Descent, **Stacks 03DT** through
`AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology`. Together
they are the two results the source's proof cites; the step still carried by
`AlgebraicGeometry.Stack.IsSheafForLiftedFppfFamily` is the identification of the sheaf
condition for `F` along a family lying over an fppf covering with the sheaf condition for this
`𝓕^a` along the covering downstairs. -/
theorem exists_isSheaf_sectionsPresheafOfModules_of_isLocallyQuasicoherent
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F) (x : 𝒳) :
    ∃ (𝓕 : ((p.obj x).left.1).Modules) (h𝓕 : 𝓕.IsQuasicoherent),
      Presheaf.IsSheaf
          (BigFppfOver.baseOverTopology B (p.obj x).left.1 (p.obj x).left.2 .fppf)
          (@BigFppfOver.sectionsPresheafOfModules B (p.obj x).left.1 (p.obj x).left.2
            𝓕 h𝓕).presheaf ∧
        ∃ hM : Presheaf.IsSheaf
            (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
            (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
              (etaleTopology_le_topology B) F).presheaf,
          Nonempty ((SmallEtale.associatedModule E (p.obj x).left.1
                (contains_base B E h S hS p x)).obj 𝓕 ≅
            (⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
              (etaleTopology_le_topology B) F, hM⟩ :
              SheafOfModules.{u} (SmallEtale.structureSheaf E (p.obj x).left.1
                (contains_base B E h S hS p x)))) := by
  obtain ⟨hM, 𝓕, e⟩ :=
    exists_associatedModule_iso_restrictModuleToSmallEtale B E h S hS p hp F hlqc x
  refine ⟨𝓕.obj, 𝓕.property, ?_, hM, e⟩
  have : SheafOfModules.IsQuasicoherent 𝓕.obj := 𝓕.property
  exact BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology B (p.obj x).left.1
    (p.obj x).left.2 .fppf 𝓕.obj

end AlgebraicGeometry.Stack

end
