module

public import StacksFrontier.AlgebraicGeometry.Blowup.IsoOffCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The blowup square of a quasi-coherent ideal of finite type

Let `X` be a scheme and `I` a quasi-coherent ideal sheaf on `X`, cutting out `Z ⊆ X`. The
blowup square
```
E --j--> X'
|π       |b
v        v
Z --i--> X
```
has upper-right corner the blowup `X' = Bl_I(X)`, upper-left corner the exceptional divisor
`E = b⁻¹(Z)`, and is cartesian. This file collects what the Mayer–Vietoris results for étale
cohomology of such a square (Stacks 0EW5, 0EW3, 0EW6) need about it:

* it is cartesian, for any `I`;
* over the open complement `U = X \ Z` the blowup morphism is an isomorphism, which is recorded
  as a cartesian square whose top arrow over `U` is invertible;
* if `I` is of finite type, then `b` is proper, so cohomology of torsion sheaves commutes with
  base change along `b` (the proper base change theorem, Stacks 0A3U/095T).

## Main definitions

* `AlgebraicGeometry.exceptionalDivisorToCenter`: the morphism `π : E ⟶ Z`.

## Main results

* `AlgebraicGeometry.isPullback_exceptionalDivisor`: the blowup square is cartesian.
* `AlgebraicGeometry.range_subschemeι_compl_eq`: the complement of the centre is the image of
  the open immersion `Scheme.Opens.ι I.support.compl`.
* `AlgebraicGeometry.isPullback_blowUpToBase_restrict_compl_support`: the restriction of the
  blowup morphism over the complement of the centre, as a cartesian square.
* `AlgebraicGeometry.cohomologyCommutesWithBaseChange_blowUpToBase_of_fg`: for an ideal of finite
  type, étale cohomology of torsion sheaves commutes with base change along the blowup morphism.

## References

* [Stacks Project, Tag 0EV5](https://stacks.math.columbia.edu/tag/0EV5)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 0A3U](https://stacks.math.columbia.edu/tag/0A3U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The morphism `π : E ⟶ Z` from the exceptional divisor of the blowup of `X` in `I` to the
closed subscheme `Z` cut out by `I`: the exceptional divisor is the inverse image of `Z`, hence
the fibre product of the blowup morphism and the inclusion of `Z`, and `π` is the second
projection. -/
@[sga "7 XVIII 2.1"]
public def exceptionalDivisorToCenter : exceptionalDivisor I ⟶ I.subscheme :=
  (I.comapIso (blowUpToBase I)).hom ≫ pullback.snd (blowUpToBase I) I.subschemeι

/-- **The blowup square is cartesian.** For any quasi-coherent ideal sheaf `I` on `X` the square
```
E ⟶ X'
↓    ↓ b
Z ⟶ X
```
formed by the exceptional divisor, the blowup, the centre and `X` commutes and is cartesian. -/
@[sga "6 VII 3.7" "more general"]
public theorem isPullback_exceptionalDivisor :
    IsPullback (exceptionalIdeal I).subschemeι (exceptionalDivisorToCenter I) (blowUpToBase I)
      I.subschemeι := by
  refine IsPullback.of_iso_pullback ⟨?_⟩ (I.comapIso (blowUpToBase I))
    (Scheme.IdealSheafData.comapIso_hom_fst _ _) rfl
  show _ = ((I.comapIso (blowUpToBase I)).hom ≫
    pullback.snd (blowUpToBase I) I.subschemeι) ≫ I.subschemeι
  rw [Category.assoc, ← pullback.condition, ← Category.assoc,
    Scheme.IdealSheafData.comapIso_hom_fst]

/-- The open complement of the centre is the image of its open immersion. -/
public theorem range_subschemeι_compl_eq :
    Set.range (Scheme.Opens.ι I.support.compl).base = (Set.range I.subschemeι.base)ᶜ := by
  rw [Scheme.Opens.range_ι, Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- **The blowup morphism over the complement of the centre.** The restriction of the blowup
morphism over `X \ Z` sits in a cartesian square with the blowup morphism and the two open
immersions; by Stacks 02OS its top arrow is an isomorphism
(`AlgebraicGeometry.isIso_blowUpToBase_restrict_compl_support`). -/
public theorem isPullback_blowUpToBase_restrict_compl_support :
    IsPullback (blowUpToBase I ⁻¹ᵁ I.support.compl).ι (blowUpToBase I ∣_ I.support.compl)
      (blowUpToBase I) (Scheme.Opens.ι I.support.compl) :=
  (isPullback_morphismRestrict (blowUpToBase I) I.support.compl).flip

/-- **Proper base change for the blowup in an ideal of finite type.** If `I` is finitely
generated on every affine open, the blowup morphism is proper, so higher direct images of torsion
abelian sheaves along it commute with arbitrary base change (Stacks 0A3U). -/
public theorem cohomologyCommutesWithBaseChange_blowUpToBase_of_fg
    (hI : ∀ U : X.affineOpens, (I.ideal U).FG) :
    Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} (blowUpToBase I) :=
  have := isProper_blowUpToBase_of_fg I hI
  Stacks.EtaleCohomology.cohomologyCommutesWithBaseChange_of_isProper _

end AlgebraicGeometry

end
