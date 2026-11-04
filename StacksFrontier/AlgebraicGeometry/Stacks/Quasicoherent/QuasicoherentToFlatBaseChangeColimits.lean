module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.EffectiveGlueAgreementTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Coherator
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Descent.FibredSiteColimits
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatBaseChangeSummary

/-!
# The inclusion `QCoh(𝒪_𝒳) ⊆ LQCoh^fbc(𝒪_𝒳)` preserves colimits

Let `p : 𝒳 ⥤ (Sch/S)_fppf` be an essentially small category fibred in groupoids, as for an
algebraic stack. The coherator of **Stacks 0778**,
`AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator`, is built by the special adjoint functor
theorem over a hypothesis `hpres`: that the inclusion
`i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)`, `AlgebraicGeometry.Stack.quasicoherentToFlatBaseChange`,
preserves colimits. The same hypothesis appears as `hpresX` in the statements of **Stacks 0GQX**
in `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ColimitsOfQuasicoherentDirectImage.lean`.
It is proved here, for every choice of the containment `hinc` the inclusion is built over.

## Main results

* `AlgebraicGeometry.Stack.preservesColimitsOfSize_quasicoherentToFlatBaseChange`: the inclusion
  `i` preserves all colimits indexed in the universe of the site.

## Proof

A colimit of quasi-coherent modules is computed in `Mod(𝒪_𝒳)` on the fppf site (the colimit
clause of **Stacks 06WN** (1), available with no hypothesis by
`AlgebraicGeometry.FibredSite.colimits_quasicoherentModules_of_surjective` together with
**Stacks 03DX** (1) at `τ = fppf`). To see that it is still a colimit in `LQCoh^fbc(𝒪_𝒳)`, take
a cocone with vertex `G` in `LQCoh^fbc(𝒪_𝒳)`. By **Stacks 0771** part (1),
`AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherentWithFlatBaseChange`, the étale
sheaf `G` is already an fppf sheaf, so the cocone is a cocone in `Mod(𝒪_𝒳)`, where the colimit
property applies. Restricting from the fppf to the étale site changes neither presheaves of
modules nor the maps between them, so the induced map and its uniqueness carry back.

So no colimit is ever computed in `Mod(𝒳_étale, 𝒪_𝒳)`: only test objects of `LQCoh^fbc` are
needed, and they are fppf sheaves.

## Implementation notes

The source does not state this as a lemma of its own; it is part of what the proof of
**Stacks 0779** part (3) uses, and the agreement of colimits of `LQCoh^fbc(𝒪_𝒳)` with those of
the ambient categories is **Stacks 0771** part (5), which is a different and stronger statement
about all of `LQCoh^fbc`. So no `stacks` attribute is recorded. (The docstrings of
`ColimitsOfQuasicoherentDirectImage.lean` and `Coherator.lean` call this property "Stacks 07AQ
part (2)"; Stacks 07AQ part (2) is in fact the flat, locally finitely presented descent of
membership in `LQCoh^fbc`, an unrelated statement.)

## References

* [Stacks Project, Tag 0778](https://stacks.math.columbia.edu/tag/0778)
* [Stacks Project, Tag 0779](https://stacks.math.columbia.edu/tag/0779)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type (u + 1)} [Category.{u} 𝒳] [EssentiallySmall.{u} 𝒳]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (hinc : ∀ F : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS p hp,
    IsLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp
      ((FibredSite.toSiteModules.{u, u + 1, u, u} B S hS p hp .etale).obj F).val)

/-- A member of `LQCoh^fbc(𝒪_𝒳)` read as a module on the associated fppf site, with the same
presheaf of modules: it is an fppf sheaf by **Stacks 0771** part (1). This is
`AlgebraicGeometry.Stack.fppfModuleOfLocallyQuasicoherentWithFlatBaseChange` for an arbitrary
category fibred in groupoids rather than an algebraic stack, read on an object of the
subcategory. -/
def flatBaseChangeToFppfModule
    (G : locallyQuasicoherentFlatBaseChangeModules.{u, u + 1, u} B E h S hS p hp) :
    SheafOfModules.{u} (FibredSite.ringStructureSheafCore B S hS p hp .fppf) where
  val := G.obj.val
  isSheaf := isSheaf_fppf_of_isLocallyQuasicoherentWithFlatBaseChange B E h S hS p hp
    G.obj.val G.property

include hinc in
/-- **The inclusion `i : QCoh(𝒪_𝒳) ⥤ LQCoh^fbc(𝒪_𝒳)` of Stacks 0778 preserves colimits**, with
no hypothesis: this is the input `hpres` of the coherator
`AlgebraicGeometry.Stack.flatBaseChangeQuasicoherator`. A colimit of quasi-coherent modules is
computed in `Mod(𝒪_𝒳)` (Stacks 06WN (1)), and every test object of `LQCoh^fbc(𝒪_𝒳)` is an fppf
sheaf (Stacks 0771 (1)), so the colimit property in `Mod(𝒪_𝒳)` is the one needed. -/
theorem preservesColimitsOfSize_quasicoherentToFlatBaseChange :
    PreservesColimitsOfSize.{u, u} (quasicoherentToFlatBaseChange B E h S hS p hp hinc) := by
  have := (FibredSite.colimits_quasicoherentModules_of_surjective B S hS p hp
    (fun T hT => BigFppfOver.quasicoherentIsEssImageAssociatedModule' B T hT)).2
  refine ⟨fun {K} _ => ⟨fun {F} => ⟨fun {c} hc => ⟨?_⟩⟩⟩⟩
  have hc' := isColimitOfPreserves
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (FibredSite.ringStructureSheafCore B S hS p hp .fppf)).ι hc
  let lift (s : Cocone (F ⋙ quasicoherentToFlatBaseChange B E h S hS p hp hinc)) :
      Cocone (F ⋙ (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (FibredSite.ringStructureSheafCore B S hS p hp .fppf)).ι) :=
    { pt := flatBaseChangeToFppfModule B E h S hS p hp s.pt
      ι := { app := fun j => ⟨(s.ι.app j).hom.val⟩
             naturality := fun j j' g => by
               ext1
               exact congrArg (fun φ => φ.hom.val) (s.ι.naturality g) } }
  exact
    { desc := fun s => ObjectProperty.homMk ⟨(hc'.desc (lift s)).val⟩
      fac := fun s j => by
        have := congrArg SheafOfModules.Hom.val (hc'.fac (lift s) j)
        ext1
        ext1
        exact this
      uniq := fun s m hm => by
        have := hc'.uniq (lift s) ⟨m.hom.val⟩ fun j => by
          have := congrArg (fun φ => φ.hom.val) (hm j)
          ext1
          exact this
        have := congrArg SheafOfModules.Hom.val this
        ext1
        ext1
        exact this }

end AlgebraicGeometry.Stack

end
