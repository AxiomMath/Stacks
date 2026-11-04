module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrysFirstOrderAffineBaseChange
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemFirstOrder

/-!
# The base-change input of [Stacks, Lemma 60.17.3, Tag 07JG] over affine levels

Fix a global crystalline situation `(p, (S, I, γ), X)` and a system of levels
`L : ...SmallSite.LevelScalars07JG S D` of the small crystalline site `Cris(X/S)`.  The record
`...SmallSite.LevelBaseChangeData` carries two inputs of the reduction of
[Stacks, Lemma 60.17.3, Tag 07JG], and the second of them,

`bijective_extensionSectionsMap : ∀ (F : QuasiCoherentCrystal S) (e : ℕ),
  Function.Bijective (L.levelExtensionSectionsMap F e)`,

is bijectivity of the base change of sections along `p₀` of [Stacks, Tag 07J2] over each level.
**This module discharges that field** whenever each level has affine ambient scheme, with no
hypothesis on the crystal beyond its being one and no lift to the big site `CRIS(X/S)`.

## What replaces the big-site lift

`SmallSite/LevelBaseChangeFromBigSite.lean` reduces the field to the big-site statement of
[Stacks, Tag 07J6] *for a sheaf of modules on `CRIS(X/S)` restricting to the crystal*, and carries
the existence of that sheaf as a hypothesis — essential surjectivity of
`...SmallSite.restrictSheafOfModules` on crystals, which the tree does not have and which cannot
be had from `i_*` or `i_!` at the module universe the base-change maps are written at; see the
module documentation of `SmallSite/CrysFirstOrderAffineBaseChange.lean`.

That reduction is not used here.  `...SmallSite.bijective_crysExtensionSectionsMap` proves the
affine statement of [Stacks, Tag 07J6] **on the small site directly**, so the field follows from
affineness of the levels alone and the hypothesis is removed rather than moved.  The levels of the
source's own system `(X, T(n)_e, δ(n))` are affine by
`...SmallSite.isAffine_target_wholeSpaceSystem`, so over that system the field is discharged
outright.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `bijective_levelExtensionSectionsMap_of_isAffine` — **the field at one crystal and one level**
  whose ambient scheme is affine.
* `bijective_levelExtensionSectionsMap_of_affineLevels` — the field, for a system all of whose
  levels have affine ambient scheme.
* `LevelBaseChangeData.ofAffineLevels` — **the record of [Stacks, Tag 07JG] over such a system**,
  assembled from its differentials input alone.
* `bijective_levelExtensionSectionsMap_wholeSpace` — the field over the source's own system of
  levels, with **no** hypothesis.
* `LevelBaseChangeData.ofWholeSpaceSystem` — the record over the source's own system, from its
  differentials input alone.

**No `@[stacks]` attribute is placed and no tag is proved**: this is one input of the reduction of
[Stacks, Tag 07JG].

## References

* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct

universe u uI

namespace Crystalline.GlobalCrystallineSituation.SmallSite

section Generic

variable {S : GlobalCrystallineSituation.{u}} {A : Type u} [CommRing A]
  {D : DividedPowerRing.{u}} {g : A →+* D} {Omega : Type u} [AddCommGroup Omega]
  [Module D Omega] [Module Dᵐᵒᵖ Omega] [IsCentralScalar D Omega]
  {d : DividedPowerDerivation A D g Omega} {ι : Type uI}

/-! ### The field at one level with affine ambient scheme -/

/-- **The base change of sections over a level whose ambient scheme is affine is bijective**, for
a crystal in quasi-coherent `𝒪_{X/S}`-modules on `Cris(X/S)`.

`...SmallSite.LevelScalars07JG.levelExtensionSectionsMap` is the small-site base-change map
`...SmallSite.crysExtensionSectionsMap` at the ambient object of the level, and that map is
bijective by `...SmallSite.bijective_crysExtensionSectionsMap_of_isQuasicoherentOnSite`: the
crystal condition and the quasi-coherence of `ℱ_{T_e}` are both read off [Stacks, Tag 07IT] from
quasi-coherence of the crystal on the site. -/
theorem bijective_levelExtensionSectionsMap_of_isAffine (L : LevelScalars07JG S D)
    (F : QuasiCoherentCrystal S) (e : ℕ)
    [IsAffine (L.levelSystem.obj e).obj.thickening.target.scheme] :
    Function.Bijective (L.levelExtensionSectionsMap F e) :=
  bijective_crysExtensionSectionsMap_of_isQuasicoherentOnSite F.obj (L.levelSystem.obj e)
    F.property.1

/-- **The base-change input of [Stacks, Lemma 60.17.3, Tag 07JG] over a system of levels with
affine ambient schemes.**  This is the field
`...SmallSite.LevelBaseChangeData.bijective_extensionSectionsMap`, with affineness of the levels
as its only hypothesis. -/
theorem bijective_levelExtensionSectionsMap_of_affineLevels (L : LevelScalars07JG S D)
    (haff : ∀ e : ℕ, IsAffine (L.levelSystem.obj e).obj.thickening.target.scheme)
    (F : QuasiCoherentCrystal S) (e : ℕ) :
    Function.Bijective (L.levelExtensionSectionsMap F e) :=
  have := haff e
  bijective_levelExtensionSectionsMap_of_isAffine L F e

/-! ### The record of [Stacks, Tag 07JG] over affine levels -/

/-- **The record of [Stacks, Lemma 60.17.3, Tag 07JG] over a system of levels with affine ambient
schemes**, assembled from its differentials input alone.

The differentials input — a basis of the differentials of each level which is the image of the
chosen basis of `Ω`, so that the differentials of the level are the base change of `Ω` — is passed
through unchanged, and the bijectivity input is now a theorem,
`bijective_levelExtensionSectionsMap_of_affineLevels`.  Nothing is carried.

**No `@[stacks]` attribute is placed and no tag is proved**: this is one of the two inputs of the
reduction of [Stacks, Tag 07JG]. -/
def LevelBaseChangeData.ofAffineLevels {L : LevelScalars07JG S D}
    (R : LevelForms07JG S A D g Omega d L) (b : Module.Basis ι (D : Type u) Omega)
    (omegaBasis : ∀ e : ℕ, Module.Basis ι (crysSheafRing S (L.levelSystem.obj e).obj)
      (crysDiffSections (L.levelSystem.obj e).obj))
    (omegaBasis_apply : ∀ (e : ℕ) (i : ι), omegaBasis e i = R.omegaMap e (b i))
    (haff : ∀ e : ℕ, IsAffine (L.levelSystem.obj e).obj.thickening.target.scheme) :
    LevelBaseChangeData R b where
  omegaBasis := omegaBasis
  omegaBasis_apply := omegaBasis_apply
  bijective_extensionSectionsMap :=
    bijective_levelExtensionSectionsMap_of_affineLevels L haff

end Generic

/-! ### The source's own system of levels -/

section WholeSpace

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) {n : ℕ} {A : Type u} [CommRing A]
  {g : A →+* (wholeSpaceSystemEnvelope hp n).ring} {Omega : Type u} [AddCommGroup Omega]
  [Module (wholeSpaceSystemEnvelope hp n).ring Omega]
  [Module ((wholeSpaceSystemEnvelope hp n).ring)ᵐᵒᵖ Omega]
  [IsCentralScalar (wholeSpaceSystemEnvelope hp n).ring Omega]
  {d : DividedPowerDerivation A (wholeSpaceSystemEnvelope hp n).ring g Omega} {ι : Type uI}

/-- **The base change of sections over the levels of the source's own system
`(X, T(n)_e, δ(n))` is bijective**, with no hypothesis: the ambient divided power scheme of every
object of that system is affine, by `...SmallSite.isAffine_target_wholeSpaceSystem`.

This is the field `...SmallSite.LevelBaseChangeData.bijective_extensionSectionsMap` over the
system of [Stacks, Proposition 60.20.1, Tag 07JN], and it replaces
`...SmallSite.bijective_levelExtensionSectionsMap_wholeSpace_of_exists_bigCrystal`, whose
hypothesis — a big-site lift of each crystal — is no longer needed. -/
theorem bijective_levelExtensionSectionsMap_wholeSpace (F : QuasiCoherentCrystal S) (e : ℕ) :
    Function.Bijective ((wholeSpaceLevelScalars hp n).levelExtensionSectionsMap F e) :=
  bijective_levelExtensionSectionsMap_of_affineLevels (wholeSpaceLevelScalars hp n)
    (fun e ↦ isAffine_target_wholeSpaceSystem hp n e) F e

/-- **The record of [Stacks, Lemma 60.17.3, Tag 07JG] over the source's own system of levels**,
assembled from its differentials input alone. -/
def LevelBaseChangeData.ofWholeSpaceSystem
    (R : LevelForms07JG S A (wholeSpaceSystemEnvelope hp n).ring g Omega d
      (wholeSpaceLevelScalars hp n))
    (b : Module.Basis ι ((wholeSpaceSystemEnvelope hp n).ring : Type u) Omega)
    (omegaBasis : ∀ e : ℕ, Module.Basis ι
      (crysSheafRing S ((wholeSpaceLevelScalars hp n).levelSystem.obj e).obj)
      (crysDiffSections ((wholeSpaceLevelScalars hp n).levelSystem.obj e).obj))
    (omegaBasis_apply : ∀ (e : ℕ) (i : ι), omegaBasis e i = R.omegaMap e (b i)) :
    LevelBaseChangeData R b :=
  LevelBaseChangeData.ofAffineLevels R b omegaBasis omegaBasis_apply
    (fun e ↦ isAffine_target_wholeSpaceSystem hp n e)

end WholeSpace

end Crystalline.GlobalCrystallineSituation.SmallSite

end
