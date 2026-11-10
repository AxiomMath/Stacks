module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SecondOrderIdealAffineIntegrable
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelBaseChangeFromBigSite
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceLevelScalars
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.WholeSpaceSystemAffine

/-!
# The affine first-order and second-order results at the cosimplicial system of [Stacks, Tag 07JN]

`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/WholeSpaceSystemAffine.lean` shows that
every object of the cosimplicial system `(X, T(n)_e, δ(n))` of [Stacks, Proposition 60.20.1, Tag
07JN] has affine ambient divided power scheme.  That is the one hypothesis beyond the source's own
under which the affine results about a crystal are stated:

* `Crystalline.GlobalCrystallineSituation.bijective_extensionSectionsMap` — the sections of a
  crystal over the first-order universal thickening `(U, T', δ')` of [Stacks, Tag 07J2] are the
  base change of its sections over the object;
* `Crystalline.GlobalCrystallineSituation.firstOrderIdealBaseChangeOfIsSheafCrystal` — the
  degree-one identification `Ω ⊗_D M ≅ ker(F(U, T', δ') ⟶ M)` of [Stacks, Tag 07J6], obtained
  from the crystal condition rather than assumed;
* `...SecondOrderAffine.crystalConnectionTensor_comp_self_eq_zero_of_isSheafCrystal` —
  integrability of the resulting connection, clause [Stacks, Tag 07JD].

This module reads all three at the objects of that system, so that the affineness side condition
is discharged once and for all and does not have to be carried by anything downstream of
[Stacks, Proposition 60.21.3, Tag 07LG].

## What remains, exactly

The three results above are stated for a sheaf of modules on the **big** crystalline site
`CRIS(X/S)`, and the coefficient sheaf of [Stacks, Tag 07LG] is a sheaf of modules on the
**small** site `Cris(X/S)`.  The two base-change maps are literally the same map for a restricted
sheaf, which is
`...SmallSite.bijective_crysExtensionSectionsMap_restrictSheafOfModules_iff` of
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/FirstOrderBaseChangeBridge.lean`, so what
stands between the two sides is a **lift**: a sheaf of modules on `CRIS(X/S)` whose restriction
to `Cris(X/S)` is isomorphic to the given crystal.  That is essential surjectivity of
`...SmallSite.restrictSheafOfModules` on crystals, which the tree does not have.

`bijective_levelExtensionSectionsMap_wholeSpace_of_exists_bigCrystal` below is the exact
remaining statement.  Compared with
`...SmallSite.bijective_levelExtensionSectionsMap_of_exists_restrictIso`, whose hypothesis asks
for a lift **together with** bijectivity of its big-site base change, the hypothesis here asks
only for a lift which is a crystal with quasi-coherent ambient module: the bijectivity is now a
theorem, by affineness of the objects of the system.  The quasi-coherence of the ambient module
`F_T` is the instance `[(ambientSchemeModules N A).IsQuasicoherent]` the affine chain is stated
under; it is the ambient-scheme reading of the source's own quasi-coherence clause, and nothing
in the tree produces it from `SheafOfModules.IsQuasicoherentOnSite`.

## Main results

Everything is in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `bijective_extensionSectionsMap_wholeSpaceSystem` — **the base change of sections along `p₀` is
  bijective at every object of the system**, for a big-site crystal with quasi-coherent ambient
  module.
* `firstOrderIdealBaseChangeWholeSpaceSystem` — **the degree-one datum of [Stacks, Tag 07J6] at
  every object of the system**, built from the crystal condition.
* `crystalConnectionTensor_comp_self_eq_zero_wholeSpaceSystem` — **integrability of the canonical
  connection at every object of the system.**
* `bijective_levelExtensionSectionsMap_wholeSpace_of_exists_bigCrystal` — the base-change input
  of [Stacks, Lemma 60.17.3, Tag 07JG] over the system, from the big-site lift alone.

## What is and is not proved

**No `@[stacks]` attribute is placed and no tag is proved here.**  Each statement below is one of
the affine results cited above read at a particular object; the affineness hypothesis they carry
is not a hypothesis of any tag, and it is discharged here rather than assumed, but the big-site
restriction on the coefficient sheaf is still carried and no statement of [Stacks, Tag 07J6] or
[Stacks, Tag 07JG] is claimed.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Proposition 60.20.1, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Lemma 60.15.1, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite Simplicial
open scoped TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  (M : SheafOfModules.{u} (crystallineStructureSheaf S))

/-- **The base change of sections along `p₀` is bijective at every object of the cosimplicial
system of [Stacks, Proposition 60.20.1, Tag 07JN]**, for a crystal on `CRIS(X/S)` whose ambient
module over the object is quasi-coherent.

This is `Crystalline.GlobalCrystallineSituation.bijective_extensionSectionsMap`, whose affineness
instance is supplied by `isAffine_target_wholeSpaceSystem`. -/
theorem bijective_extensionSectionsMap_wholeSpaceSystem (n e : ℕ)
    [(ambientSchemeModules M
      (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e).obj).IsQuasicoherent]
    (hM : GlobalCrystallineSituation.IsSheafCrystal M) :
    Function.Bijective
      (extensionSectionsMap M (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e).obj) :=
  have := isAffine_target_wholeSpaceSystem hp n e
  bijective_extensionSectionsMap M _ hM

/-- **The canonical map of [Stacks, Tag 07J6] on global sections is bijective at every object of
the cosimplicial system of [Stacks, Proposition 60.20.1, Tag 07JN]**, for a crystal on
`CRIS(X/S)` with quasi-coherent ambient module over the object. -/
theorem bijective_firstOrderSectionsMap_wholeSpaceSystem (n e : ℕ)
    [(ambientSchemeModules M
      (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e).obj).IsQuasicoherent]
    (hM : GlobalCrystallineSituation.IsSheafCrystal M) :
    Function.Bijective
      (firstOrderSectionsMap M (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e).obj) :=
  have := isAffine_target_wholeSpaceSystem hp n e
  bijective_firstOrderSectionsMap_of_isSheafCrystal M _ hM

/-- **The degree-one datum of [Stacks, Tag 07J6] at every object of the cosimplicial system of
[Stacks, Proposition 60.20.1, Tag 07JN]**, for a crystal on `CRIS(X/S)` with quasi-coherent
ambient module over the object.

This is the datum `Crystalline.GlobalCrystallineSituation.FirstOrderIdealBaseChange` that the
connection of [Stacks, Tag 07J6] is built from, obtained from the crystal condition and not
assumed. -/
def firstOrderIdealBaseChangeWholeSpaceSystem (n e : ℕ)
    [(ambientSchemeModules M
      (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e).obj).IsQuasicoherent]
    (hM : GlobalCrystallineSituation.IsSheafCrystal M) :
    FirstOrderIdealBaseChange M (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e).obj :=
  haveI := isAffine_target_wholeSpaceSystem hp n e
  firstOrderIdealBaseChangeOfIsSheafCrystal M _ hM

/-- **Integrability of the canonical connection of [Stacks, Tag 07J6] at every object of the
cosimplicial system of [Stacks, Proposition 60.20.1, Tag 07JN]**, for a crystal on `CRIS(X/S)`
with quasi-coherent ambient module over the object: the connection composes with its own
degree-one extension to zero.

This is clause [Stacks, Tag 07JD] at the objects of the system, and it is the reason the square
of the de Rham differential of the double complex of [Stacks, Proposition 60.21.3, Tag 07LG] need
not be assumed at an affine object. -/
theorem crystalConnectionTensor_comp_self_eq_zero_wholeSpaceSystem (n e : ℕ)
    [(ambientSchemeModules M
      (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e).obj).IsQuasicoherent]
    (hM : GlobalCrystallineSituation.IsSheafCrystal M)
    (s : M.val.obj (op (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e).obj)) :
    extendedConnectionTensor M (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e).obj
        (firstOrderIdealBaseChangeWholeSpaceSystem hp M n e hM)
        (crystalConnectionTensor M (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e).obj
          (firstOrderIdealBaseChangeWholeSpaceSystem hp M n e hM) s) = 0 :=
  have := isAffine_target_wholeSpaceSystem hp n e
  SecondOrderAffine.crystalConnectionTensor_comp_self_eq_zero_of_isSheafCrystal M _ hM s

/-! ### The base-change input of [Stacks, Tag 07JG] over the system -/

/-- **The base change of sections over the levels of `(X, T(n)_e, δ(n))` is bijective as soon as
every crystal admits a big-site lift which is a crystal with quasi-coherent ambient module.**

This is the field `...SmallSite.LevelBaseChangeData.bijective_extensionSectionsMap` at the
source's own system of levels, with the affineness side condition **discharged**: the hypothesis
of `...SmallSite.bijective_levelExtensionSectionsMap_of_exists_restrictIso` asks for a lift
together with bijectivity of its big-site base change, and bijectivity is here a theorem by
`bijective_extensionSectionsMap_wholeSpaceSystem`.

What is still carried is the lift itself, together with the quasi-coherence of its ambient module
over each level.  Producing the lift is essential surjectivity of
`...SmallSite.restrictSheafOfModules` on crystals, which the tree does not have. -/
theorem bijective_levelExtensionSectionsMap_wholeSpace_of_exists_bigCrystal (n : ℕ)
    (h : ∀ (F : QuasiCoherentCrystal S) (e : ℕ),
      ∃ N : SheafOfModules.{u} (crystallineStructureSheaf S),
        ∃ _ : restrictSheafOfModules N ≅ F.obj,
          ∃ _ : (ambientSchemeModules N
              (((wholeSpaceSystem S hp).obj (op ⦋n⦌)).obj e).obj).IsQuasicoherent,
            GlobalCrystallineSituation.IsSheafCrystal N)
    (F : QuasiCoherentCrystal S) (e : ℕ) :
    Function.Bijective ((wholeSpaceLevelScalars hp n).levelExtensionSectionsMap F e) := by
  refine bijective_levelExtensionSectionsMap_of_exists_restrictIso
    (wholeSpaceLevelScalars hp n) (fun F e ↦ ?_) F e
  obtain ⟨N, α, hqc, hN⟩ := h F e
  exact ⟨N, α, bijective_extensionSectionsMap_wholeSpaceSystem hp N n e hN⟩

end Crystalline.GlobalCrystallineSituation.SmallSite

end
