module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.RestrictScalarsCoextension
public import StacksFrontier.Topology.Sheaves.Functors.Module.ExactSupportSections
public import StacksFrontier.Topology.Sheaves.Functors.Module.HomSheaf
public import StacksFrontier.Topology.Sheaves.Sheaf.Module
import StacksCore.Tactic.StacksAttribute

/-!
# Sheaf Hom with exact support along a closed quotient of ringed spaces

Let `i : Z ⟶ X` be a closed quotient morphism of ringed spaces, with kernel ideal
`ℐ = ker(𝒪_X ⟶ i_* 𝒪_Z)`.  The functor taking an `𝒪_X`-module `F` to the `𝒪_Z`-module whose
sections over `V ⊆ Z` are the sections of `F` over an open `U ⊆ X` with `U ∩ Z = V` which are
annihilated by `ℐ` is right adjoint to pushforward.

## Main definitions

* `RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.sheafHomExactSupport` is the
  sheaf Hom functor with exact support.
* `ClosedQuotientMorphismOfRingedSpaces.sectionsLocallyAnnihilatedByKernelIdeal` is the
  additive subgroup of sections whose restriction to every smaller open is killed by the kernel
  ideal there.

## Main results

* `ClosedQuotientMorphismOfRingedSpaces.modulePushforwardSheafHomExactSupportAdjunction` gives
  the adjunction with pushforward.

## Implementation notes

The functor is the internal Hom `SheafHom_{𝒪_X}(i_* 𝒪_Z, -)`, which is a module over
`i_* 𝒪_Z`, followed by the descent equivalence of
`ClosedQuotientMorphismOfRingedSpaces.moduleDescend`.  The adjunction is then the composite of
`RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction` — the adjunction of Tag 0A6F, which
lives in `StacksFrontier.Topology.Sheaves.Functors.Module.HomSheaf` — with
`ClosedQuotientMorphismOfRingedSpaces.moduleDescendAdjunction`, using that pushforward of
modules along `i` is pushforward over `i_* 𝒪_Z` followed by restriction of scalars.

Annihilation by the kernel ideal is sheaf-local: it is required after restriction to every
smaller open, not merely for the global sections of the ideal on `U`.

`sectionsLocallyAnnihilatedByKernelIdeal` is reserved for the section-level description of
`sheafHomExactSupport` — that its sections over `V` are the sections of `F` over `i_! V` killed
by `ℐ` — and has **no consumer yet**: the declarations identifying the two are not available, so
nothing here ties `sheafHomExactSupport` to the exact-support condition.  A consequence is that
`ClosedQuotientMorphismOfRingedSpaces.isLocallySurjective`, one of the two defining fields of a
closed quotient morphism, is used by nothing in the library; the adjunction below needs only
the closed-embedding field.

## References

* [Stacks Project, Tag 0A75](https://stacks.math.columbia.edu/tag/0A75)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace RingedSpaceModuleAdjunction

namespace ClosedQuotientMorphismOfRingedSpaces

variable (S : ClosedQuotientMorphismOfRingedSpaces.{u})

/-- The additive subgroup of sections of an `𝒪_X`-module on `U` which are annihilated
sheaf-locally by the kernel ideal of a closed quotient morphism.  Thus the condition is
required for every restriction of the section to an open `W ⊆ U`. -/
def sectionsLocallyAnnihilatedByKernelIdeal
    (F : SheafOfModules.{u} (structureSheafRing S.X)) (U : Opens S.X) :
    AddSubgroup (F.val.obj (op U)) where
  carrier := { s |
    ∀ (W : Opens S.X) (hWU : W ≤ U)
      (a : (structureSheafRing S.X).obj.obj (op W)), a ∈ S.kernelIdeal W →
        a • F.val.map (homOfLE hWU).op s = 0 }
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy W hWU a ha
    simp only [map_add, smul_add, hx W hWU a ha, hy W hWU a ha, add_zero]
  neg_mem' := by
    intro x hx W hWU a ha
    simp only [map_neg, smul_neg, hx W hWU a ha, neg_zero]

/-- **Stacks Project, Tag 0A75 (the functor).** The sheaf Hom from `𝒪_Z` with exact support,
regarded as a functor from `𝒪_X`-modules to `𝒪_Z`-modules.  It is the internal Hom
`SheafHom_{𝒪_X}(i_* 𝒪_Z, -)`, which is annihilated by the kernel ideal and therefore descends
to `Z`. -/
@[stacks 0A75 "the functor"]
noncomputable def sheafHomExactSupport :
    SheafOfModules.{u} (structureSheafRing S.X) ⥤ SheafOfModules.{u} (structureSheafRing S.Z) :=
  homSheaf (structureSheafHom S.i) ⋙ S.moduleDescend

/-- **Stacks Project, Tag 0A75 (the internal Hom identification).** After pushforward to `X`,
sheaf Hom with exact support is naturally the internal Hom `SheafHom_{𝒪_X}(i_* 𝒪_Z, -)`,
regarded as an `𝒪_X`-module. -/
@[stacks 0A75 "the internal Hom identification"]
noncomputable def modulePushforwardSheafHomExactSupportIsoHomSheaf :
    S.sheafHomExactSupport ⋙ modulePushforward S.i ≅
      homSheaf (structureSheafHom S.i) ⋙
        SheafOfModules.restrictScalars (structureSheafHom S.i) :=
  Functor.isoWhiskerLeft (homSheaf (structureSheafHom S.i))
    (Functor.isoWhiskerRight S.moduleDescendCompPushforwardIso
      (SheafOfModules.restrictScalars (structureSheafHom S.i)))

/-- **Stacks Project, Tag 0A75 (adjunction).** Pushforward from a closed quotient ringed
subspace is left adjoint to sheaf Hom with exact support. -/
@[stacks 0A75 "the adjunction"]
noncomputable def modulePushforwardSheafHomExactSupportAdjunction :
    modulePushforward S.i ⊣ S.sheafHomExactSupport :=
  S.moduleDescendAdjunction.comp (restrictScalarsHomAdjunction (structureSheafHom S.i))

/-- The counit of the exact-support adjunction is, under the internal Hom identification,
evaluation of a local homomorphism at the section `1`. -/
@[stacks 0A75 "the counit is evaluation at one"]
theorem modulePushforwardSheafHomExactSupportAdjunction_counit_app
    (F : SheafOfModules.{u} (structureSheafRing S.X)) (U : Opens S.X)
    (s : ((modulePushforward S.i).obj (S.sheafHomExactSupport.obj F)).val.obj (op U)) :
    (S.modulePushforwardSheafHomExactSupportAdjunction.counit.app F).val.app (op U) s =
      Stacks.PresheafOfModules.CoextendScalars.invSecVal (structureSheafHom S.i).hom F.val (op U)
        ((S.modulePushforwardSheafHomExactSupportIsoHomSheaf.hom.app F).val.app (op U) s) :=
  rfl

end ClosedQuotientMorphismOfRingedSpaces

end RingedSpaceModuleAdjunction

end
