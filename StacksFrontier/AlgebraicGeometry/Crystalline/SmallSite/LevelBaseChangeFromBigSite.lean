module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FirstOrderBaseChangeBridge
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelReductionAssembly

/-!
# The base-change input of [Stacks, Lemma 60.17.3, Tag 07JG] from the big site

Fix a global crystalline situation `(p, (S, I, γ), X)` and a system of levels
`L : ...SmallSite.LevelScalars07JG S D` of the small crystalline site `Cris(X/S)`.  The record
`...SmallSite.LevelBaseChangeData` carries two inputs of the reduction of
[Stacks, Lemma 60.17.3, Tag 07JG], and the second of them,

`bijective_extensionSectionsMap : ∀ (F : QuasiCoherentCrystal S) (e : ℕ),
  Function.Bijective (L.levelExtensionSectionsMap F e)`,

is bijectivity of the base change of sections along `p₀` of [Stacks, Tag 07J2] over each level,
for the crystal `F` on the **small** site.  The chain that reduces that bijectivity to the affine
statement of [Stacks, Tag 07J6] is written in
`StacksFrontier/AlgebraicGeometry/Crystalline/FirstOrderIdealAffine.lean` for the base change
`Crystalline.GlobalCrystallineSituation.extensionSectionsMap` of a sheaf of modules on the
**big** site `CRIS(X/S)`.  This file reduces the field to that big-site statement.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `bijective_levelExtensionSectionsMap_of_sectionsEquiv`: **one instance of the field from the
  sections alone**: a sheaf of modules on `CRIS(X/S)` whose sections agree with those of the
  crystal over the level and over its first-order thickening, compatibly with the two
  restrictions along `p₀`, transports its big-site bijectivity to the level.
* `bijective_levelExtensionSectionsMap_of_exists_restrictIso`: **the whole field from the
  big-site statement**: if every crystal and every level admit a sheaf of modules on `CRIS(X/S)`
  restricting to the crystal and with bijective big-site base change over that level, then the
  field holds.
* `LevelBaseChangeData.ofBigSite`: the record of [Stacks, Tag 07JG], assembled from its
  differentials input and that big-site statement.

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07IJ](https://stacks.math.columbia.edu/tag/07IJ)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u uI

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} {A : Type u} [CommRing A]
  {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {ι : Type uI}

/-! ### One instance of the field, from the sections over the level -/

/-- **The base change of sections over a level is bijective as soon as a sheaf of modules on
`CRIS(X/S)` with the same sections over the level has bijective big-site base change.**

The identifications asked for are of the sections of the crystal over the level `T_e` and over
its first-order thickening `T'_e`, each linear over the section ring of that object, and
compatible with the two restrictions along `p₀`. -/
theorem bijective_levelExtensionSectionsMap_of_sectionsEquiv (L : LevelScalars07JG S D)
    (F : QuasiCoherentCrystal S) (e : ℕ)
    {N : SheafOfModules.{u} (crystallineStructureSheaf S)}
    (φ₀ : F.obj.val.obj (op (L.levelSystem.obj e))
      ≃ₗ[crysSheafRing S (L.levelSystem.obj e).obj] N.val.obj (op (L.levelSystem.obj e).obj))
    (φ₁ : F.obj.val.obj (op (firstOrderThickeningCrysObject S (L.levelSystem.obj e)))
      ≃ₗ[crysSheafRing S (firstOrderThickeningObject S (L.levelSystem.obj e).obj)]
      N.val.obj (op (firstOrderThickeningObject S (L.levelSystem.obj e).obj)))
    (hcomm : ∀ s : F.obj.val.obj (op (L.levelSystem.obj e)),
      φ₁ (crysSectionsP₀ F.obj (L.levelSystem.obj e) s) =
        moduleSiteRestrict N (firstOrderThickeningSiteP₀ S (L.levelSystem.obj e).obj) (φ₀ s))
    (h : Function.Bijective (extensionSectionsMap N (L.levelSystem.obj e).obj)) :
    Function.Bijective (L.levelExtensionSectionsMap F e) :=
  bijective_crysExtensionSectionsMap_of_sectionsEquiv (L.levelSystem.obj e) φ₀ φ₁ hcomm h

/-! ### The whole field, from the big-site statement -/

/-- **The base-change input of [Stacks, Lemma 60.17.3, Tag 07JG], reduced to the big site.**

If every crystal in quasi-coherent `𝒪_{X/S}`-modules and every level of the system admit a sheaf
of `𝒪_{X/S}`-modules on `CRIS(X/S)` whose restriction to `Cris(X/S)` is isomorphic to the crystal
and whose big-site base change of sections along `p₀` over that level is bijective, then the base
change of sections over every level is bijective — which is the field
`...SmallSite.LevelBaseChangeData.bijective_extensionSectionsMap`. -/
theorem bijective_levelExtensionSectionsMap_of_exists_restrictIso (L : LevelScalars07JG S D)
    (h : ∀ (F : QuasiCoherentCrystal S) (e : ℕ),
      ∃ N : SheafOfModules.{u} (crystallineStructureSheaf S),
        ∃ _ : restrictSheafOfModules N ≅ F.obj,
          Function.Bijective (extensionSectionsMap N (L.levelSystem.obj e).obj))
    (F : QuasiCoherentCrystal S) (e : ℕ) :
    Function.Bijective (L.levelExtensionSectionsMap F e) :=
  let ⟨_, α, hN⟩ := h F e
  bijective_crysExtensionSectionsMap_of_restrictIso α (L.levelSystem.obj e) hN

/-- **The record of [Stacks, Lemma 60.17.3, Tag 07JG] over a system of levels, with its
base-change input taken from the big site.**

The differentials input, a basis of the differentials of each level which is the image of the
chosen basis of `Ω`, is passed through unchanged, and the bijectivity input is
`bijective_levelExtensionSectionsMap_of_exists_restrictIso`. -/
def LevelBaseChangeData.ofBigSite {L : LevelScalars07JG S D}
    (R : LevelForms07JG S A D g Omega d L) (b : Module.Basis ι (D : Type u) Omega)
    (omegaBasis : ∀ e : ℕ, Module.Basis ι (crysSheafRing S (L.levelSystem.obj e).obj)
      (crysDiffSections (L.levelSystem.obj e).obj))
    (omegaBasis_apply : ∀ (e : ℕ) (i : ι), omegaBasis e i = R.omegaMap e (b i))
    (h : ∀ (F : QuasiCoherentCrystal S) (e : ℕ),
      ∃ N : SheafOfModules.{u} (crystallineStructureSheaf S),
        ∃ _ : restrictSheafOfModules N ≅ F.obj,
          Function.Bijective (extensionSectionsMap N (L.levelSystem.obj e).obj)) :
    LevelBaseChangeData R b where
  omegaBasis := omegaBasis
  omegaBasis_apply := omegaBasis_apply
  bijective_extensionSectionsMap :=
    bijective_levelExtensionSectionsMap_of_exists_restrictIso L h

end Crystalline.GlobalCrystallineSituation.SmallSite

end
