module

public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineObjectDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.DiffSectionsFunctoriality
public import StacksFrontier.AlgebraicGeometry.Crystalline.DifferentialsAffineSections

/-!
# The differentials of an affine object of `CRIS(X/S)`, on global sections, algebraically

`Crystalline.GlobalCrystallineSituation.crysDiffSections` is the module
`Γ(T, Ω_{T/S,δ})` in which the connection of [Stacks, Tag 07J6] takes its values, and it is the
*sheaf* of divided power differentials evaluated on the whole ambient scheme.  Two other objects
in the tree compute the same thing:

* `...GlobalCrystallineSituation.crysDifferentialsObj`, the sections of the *presheaf*, which
  `...GlobalCrystallineSituation.affineCrysDifferentialsIso` — [Stacks, Tag 07J0] — identifies
  with the algebraic divided power differentials of the section ring when the ambient scheme is
  affine over an affine open of the base;
* the algebraic `Crystalline.dividedPowerDifferentials` themselves, which
  `Crystalline.affineSectionsEquiv` — [Stacks, Tag 07IY] clause (2) — identifies with the
  sections of the *sheaf* over an affine open, carrying the universal divided power derivation to
  the universal divided power differential.

The second of those is exactly what the reduction datum of [Stacks, Lemma 60.17.3, Tag 07JG]
needs — its field `...SmallSite.LevelBaseChangeData.omegaBasis` asks for a basis of
`crysDiffSections` of a level over the level's section ring, and a basis of the *algebraic*
differentials is what a presentation of the ring supplies — and the tree had it only in the
general `(T, Y, f, W, V)` form, never read at an object of `CRIS(X/S)` on the top open.  **This
module reads it there**, and records that it carries
`...GlobalCrystallineSituation.crysDerivation` to the universal divided power differential.

## Main definitions

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation`.

* `affineCrysDiffSectionsEquiv` — **`Γ(T, Ω_{T/S,δ}) ≅ Ω_{Γ(T,𝒪_T)/Γ(V,𝒪_S),δ}` for an object
  with affine ambient scheme lying over an affine open of the base.**

## Main results

* `affineCrysDiffSectionsEquiv_crysDerivation` — **it carries `d_{T/S,δ} b` to the universal
  divided power differential of `b`.**
* `affineCrysDiffSectionsEquiv_symm_dpd` — and back.
* `crysDiffSectionsBasisOfAlgebraic` — hence a basis of the algebraic divided power differentials
  of the section ring is a basis of `crysDiffSections`.

## What is and is not proved

**No `@[stacks]` attribute is placed in this module and no tag is proved.**  Both
[Stacks, Tag 07IY] and [Stacks, Tag 07J0] are registered where they are proved,
`StacksFrontier/AlgebraicGeometry/Crystalline/DifferentialsAffineSections.lean` and
`StacksFrontier/AlgebraicGeometry/Crystalline/AffineObjectDifferentials.lean`; this is their
instance at an object of `CRIS(X/S)` on the top open.

## References

* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
* [Stacks Project, Tag 07J0](https://stacks.math.columbia.edu/tag/07J0)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u uI

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} (A : Thickening S)
  [IsAffine A.thickening.target.scheme] {V : S.S.scheme.Opens}
  (hVA : (⊤ : A.thickening.target.scheme.Opens) ≤ A.toBase.hom ⁻¹ᵁ V) (hV : IsAffineOpen V)

/-- **The differentials of an object of `CRIS(X/S)` with affine ambient scheme, on global
sections, are the algebraic divided power differentials of its section ring.**

This is `Crystalline.affineSectionsEquiv` — [Stacks, Tag 07IY] clause (2) — at the top open of
the ambient scheme, which is affine, over an affine open `V` of the base through which the
structure morphism factors.  The target is
`...GlobalCrystallineSituation.affineCrysDifferentialsObj`, the module
`Ω_{Γ(T,𝒪_T)/Γ(V,𝒪_S),δ}` of [Stacks, Tag 07J0]. -/
def affineCrysDiffSectionsEquiv :
    crysDiffSections A ≃ₗ[Γ(A.thickening.target.scheme, ⊤)]
      (affineCrysDifferentialsObj S A hVA : Type u) :=
  _root_.Crystalline.affineSectionsEquiv A.thickening.target S.S.scheme A.toBase.hom
    (isAffineOpen_top A.thickening.target.scheme) hVA hV

/-- **The identification carries the universal divided power derivation of the object to the
universal divided power differential of its section ring**, which is
`Crystalline.affineSectionsEquiv_apply`. -/
theorem affineCrysDiffSectionsEquiv_crysDerivation (b : Γ(A.thickening.target.scheme, ⊤)) :
    affineCrysDiffSectionsEquiv A hVA hV (crysDerivation A b) =
      _root_.Crystalline.dpd (f := affineBaseAppLE S A hVA) (crysDividedPowers S A) b :=
  _root_.Crystalline.affineSectionsEquiv_apply A.thickening.target S.S.scheme A.toBase.hom
    (isAffineOpen_top A.thickening.target.scheme) hVA hV b

/-- The identification read backwards on a universal divided power differential. -/
theorem affineCrysDiffSectionsEquiv_symm_dpd (b : Γ(A.thickening.target.scheme, ⊤)) :
    (affineCrysDiffSectionsEquiv A hVA hV).symm
        (_root_.Crystalline.dpd (f := affineBaseAppLE S A hVA) (crysDividedPowers S A) b) =
      crysDerivation A b :=
  _root_.Crystalline.affineSectionsEquiv_symm_dpd A.thickening.target S.S.scheme A.toBase.hom
    (isAffineOpen_top A.thickening.target.scheme) hVA hV b

/-- **A basis of the algebraic divided power differentials of the section ring is a basis of the
differentials on global sections.**

A basis of `Ω_{Γ(T,𝒪_T)/Γ(V,𝒪_S),δ}` over `Γ(T,𝒪_T)` is transported along
`affineCrysDiffSectionsEquiv` to a basis of `crysDiffSections` over the section ring. -/
def crysDiffSectionsBasisOfAlgebraic {ι : Type uI}
    (c : Module.Basis ι Γ(A.thickening.target.scheme, ⊤)
      (affineCrysDifferentialsObj S A hVA : Type u)) :
    Module.Basis ι (crysSheafRing S A) (crysDiffSections A) :=
  c.map (affineCrysDiffSectionsEquiv A hVA hV).symm

/-- The `i`-th vector of `crysDiffSectionsBasisOfAlgebraic c` is the image of `c i` under the
inverse of `affineCrysDiffSectionsEquiv`. -/
@[simp] theorem crysDiffSectionsBasisOfAlgebraic_apply {ι : Type uI}
    (c : Module.Basis ι Γ(A.thickening.target.scheme, ⊤)
      (affineCrysDifferentialsObj S A hVA : Type u))
    (i : ι) :
    crysDiffSectionsBasisOfAlgebraic A hVA hV c i =
      (affineCrysDiffSectionsEquiv A hVA hV).symm (c i) :=
  rfl

end Crystalline.GlobalCrystallineSituation

end
