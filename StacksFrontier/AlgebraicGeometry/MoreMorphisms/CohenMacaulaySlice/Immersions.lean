module

public import StacksFrontier.AlgebraicGeometry.RegularImmersion.BaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CohenMacaulaySlice.FiberSequence
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion

/-!
# Restricting and base changing the closed subscheme of an ideal sheaf

The closed subscheme of an ideal sheaf pulled back along an open immersion is the restriction of
the closed subscheme, so it inherits regularity of the immersion and flatness over a base.  And
the closed subscheme of a relative quasi-regular immersion stays a regular immersion after an
arbitrary change of base.

## Main results

* `Stacks.AlgebraicGeometry.isRegularImmersion_comap_of_isOpenImmersion`: the pullback of a
  regular ideal sheaf along an open immersion is a regular immersion.
* `Stacks.AlgebraicGeometry.flat_comap_of_isOpenImmersion`: the pullback keeps its flatness over
  the base.
* `Stacks.AlgebraicGeometry.isRegularImmersion_pullback_snd_of_isRelativeQuasiRegular`: the base
  change of a relative quasi-regular immersion is a regular immersion, in the orientation in
  which Stacks tag 06LI states it.
* `Stacks.AlgebraicGeometry.germ_comp_of_lift`: the germ condition of Stacks tag 06LI transports
  along a morphism of open subschemes.

## Implementation notes

`AlgebraicGeometry.Scheme.IdealSheafData.comapIso` identifies the subscheme of the pullback
ideal sheaf with the fibred product, which turns both statements about the pullback into
statements about a cartesian square;  regularity is then
`Stacks.AlgebraicGeometry.isRegularImmersion_of_isPullback_of_flat` (Stacks tag 067P) and
flatness is a rewriting of the composite.

The base-changed immersion of Stacks tag 063U is `pullback.fst (pullback.snd g f) i`, while
Stacks tag 06LI needs `pullback.snd i (pullback.fst f g)`;  the two are related by the pullback
symmetry, and the comparison is again a cartesian square whose base change is an isomorphism,
hence flat.

## References

* [Stacks Project, Lemma 37.24.1 (Tag 06LI)](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Lemma 31.20.4 (Tag 067P)](https://stacks.math.columbia.edu/tag/067P)
* [Stacks Project, Lemma 31.22.4 (Tag 063U)](https://stacks.math.columbia.edu/tag/063U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry

open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}}

/-- The subscheme of an ideal sheaf pulled back along an open immersion sits in a cartesian
square over the subscheme of the ideal sheaf itself. -/
theorem isPullback_subschemeι_comap (I : X.IdealSheafData) (j : Y ⟶ X) :
    IsPullback (I.comap j).subschemeι ((I.comapIso j).hom ≫ pullback.snd j I.subschemeι) j
      I.subschemeι :=
  (IsPullback.of_hasPullback j I.subschemeι).of_iso' (I.comapIso j) (Iso.refl _) (Iso.refl _)
    (Iso.refl _) (by simp) (by simp) (by simp) (by simp)

/-- **Restricting a regular immersion to an open subscheme.**  If the closed subscheme of `I` is
a regular immersion, so is the closed subscheme of the pullback of `I` along an open
immersion. -/
theorem isRegularImmersion_comap_of_isOpenImmersion (I : X.IdealSheafData) (j : Y ⟶ X)
    [IsOpenImmersion j] (hI : IsRegularImmersion I.subschemeι) :
    IsRegularImmersion (I.comap j).subschemeι :=
  isRegularImmersion_of_isPullback_of_flat (isPullback_subschemeι_comap I j) hI

/-- **Restricting a flat closed subscheme to an open subscheme.**  If the closed subscheme of `I`
is flat over `S`, so is the closed subscheme of the pullback of `I` along an open immersion. -/
theorem flat_comap_of_isOpenImmersion (I : X.IdealSheafData) (f : X ⟶ S) (j : Y ⟶ X)
    [IsOpenImmersion j] [Flat (I.subschemeι ≫ f)] : Flat ((I.comap j).subschemeι ≫ j ≫ f) := by
  have he : (I.comap j).subschemeι ≫ j ≫ f =
      (I.comapIso j).hom ≫ pullback.snd j I.subschemeι ≫ (I.subschemeι ≫ f) := by
    simp [← Category.assoc]
  rw [he]
  infer_instance

/-- **The base change of a relative quasi-regular immersion is a regular immersion**, in the
orientation used by Stacks tag 06LI.  This is Stacks tag 063U transported along the pullback
symmetry. -/
theorem isRegularImmersion_pullback_snd_of_isRelativeQuasiRegular {Z S' : Scheme.{u}}
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f] (i : Z ⟶ X) [IsImmersion i]
    (hi : IsRelativeQuasiRegularImmersion f i) (g : S' ⟶ S) :
    IsRegularImmersion (pullback.snd i (pullback.fst f g)) := by
  let j := pullback.fst (pullback.snd g f) i
  let b : pullback i (pullback.fst f g) ⟶ pullback (pullback.snd g f) i :=
    pullback.lift (pullback.snd i (pullback.fst f g) ≫ (pullbackSymmetry f g).hom)
      (pullback.fst i (pullback.fst f g)) (by simp [pullback.condition])
  have hbsnd : b ≫ pullback.snd (pullback.snd g f) i = pullback.fst i (pullback.fst f g) :=
    pullback.lift_snd _ _ _
  have houter : IsPullback (b ≫ pullback.snd (pullback.snd g f) i)
      (pullback.snd i (pullback.fst f g)) i ((pullbackSymmetry f g).hom ≫ pullback.snd g f) := by
    rw [hbsnd, pullbackSymmetry_hom_comp_snd]
    exact IsPullback.of_hasPullback i (pullback.fst f g)
  have hbfst : b ≫ j = pullback.snd i (pullback.fst f g) ≫ (pullbackSymmetry f g).hom :=
    pullback.lift_fst _ _ _
  have hsq : IsPullback (pullback.snd i (pullback.fst f g)) b (pullbackSymmetry f g).hom j :=
    (houter.of_right hbfst (IsPullback.of_hasPullback (pullback.snd g f) i).flip).flip
  exact isRegularImmersion_of_isPullback_of_flat hsq
    (isRegularImmersion_baseChange_of_isRelativeQuasiRegularImmersion f i hi g)

/-- **Transport of the germ condition along a morphism of open subschemes.**  If the germ of an
element of `𝒪_{X, i y}` on `Y` is the germ of a global section `a`, then its germ on `Z` is the
germ of the restriction of `a`. -/
theorem germ_comp_of_lift {Z : Scheme.{u}} (i : Y ⟶ X) (j : Z ⟶ Y) (z : Z)
    (h : X.presheaf.stalk (i (j z))) (a : Γ(Y, ⊤))
    (ha : (i.stalkMap (j z)).hom h = Y.presheaf.germ ⊤ (j z) trivial a) :
    ((j ≫ i).stalkMap z).hom h = Z.presheaf.germ ⊤ z trivial (j.appTop a) := by
  rw [Scheme.Hom.stalkMap_comp]
  show (j.stalkMap z).hom ((i.stalkMap (j z)).hom h) = _
  rw [ha]
  exact (congrArg (fun k : Γ(Y, ⊤) ⟶ Z.presheaf.stalk z => k.hom a)
    (appTop_comp_germ_top j z)).symm

/-- **The germ condition along a factorisation, with the points named.**  The form of
`germ_comp_of_lift` in which the composite `j ≫ i` and the images of `z` are given by
equations, as they are when `j` is the inclusion of a smaller open subscheme. -/
theorem germ_comp_of_lift_of_eq {Z : Scheme.{u}} (i : Y ⟶ X) (j : Z ⟶ Y) (q : Z ⟶ X)
    (hq : j ≫ i = q) (z : Z) {y : Y} (hy : j z = y) {x : X} (hx : i y = x)
    (h : X.presheaf.stalk x) (a : Γ(Y, ⊤))
    (ha : (i.stalkMap y).hom (hx.symm ▸ h) = Y.presheaf.germ ⊤ y trivial a) :
    (q.stalkMap z).hom ((show q z = x by rw [← hq]; exact (congrArg i hy).trans hx).symm ▸ h) =
      Z.presheaf.germ ⊤ z trivial (j.appTop a) := by
  subst hq hy hx
  exact germ_comp_of_lift i j z h a ha

end Stacks.AlgebraicGeometry

end
