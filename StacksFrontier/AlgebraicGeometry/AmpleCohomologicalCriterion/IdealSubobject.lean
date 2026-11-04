module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Quasi-coherent ideal sheaves as subobjects of `𝒪_X`

The cohomological criterion for ampleness, [Stacks, Tag 0B5P], hypothesises a vanishing
`H¹(X, I ⊗ L^{⊗ n}) = 0` for **every quasi-coherent sheaf of ideals** `I ⊆ 𝒪_X`, and its proof
consumes that hypothesis at the two ideal sheaves cutting out the reduced closed subschemes on
`Z = X ∖ U` and on `Z' = Z ∪ {x}` ([Stacks, Tag 01J3]). To consume it at all one needs those two
ideal sheaves *as subobjects of the unit of `X.Modules`*, which is the spelling the hypothesis is
quantified over, and that spelling did not exist: Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData` is a family of ideals indexed by the affine opens and
carries no module structure — its own implementation notes say so — while the repository's
module-level ideal sheaf
`Stacks.ClosedImmersion.idealSheaf` is a bare `SheafOfModules` with a monomorphism into the unit.

This file supplies the bridge. For a morphism of schemes `i : W ⟶ X` the kernel of
`𝒪_X ⟶ i_* 𝒪_W` is a subobject of `𝒪_X`, quasi-coherent as soon as `i` is quasi-compact by
[Stacks, Tag 01R8] part (1); applying this to `i = I.subschemeι` turns every
`I : X.IdealSheafData` into a quasi-coherent subobject of `𝒪_X`, and applying *that* to the
vanishing ideal sheaf of a closed set gives the two inputs the proof of Tag 0B5P needs, in the
right inclusion order.

## Main definitions

* `Stacks.AmpleCohomologicalCriterion.kerSubobject i`: the kernel of `𝒪_X ⟶ i_* 𝒪_W`, as a
  subobject of `𝒪_X`.
* `Stacks.AmpleCohomologicalCriterion.idealSubobject I`: the ideal sheaf of `I : X.IdealSheafData`,
  as a subobject of `𝒪_X`. This is `kerSubobject` of the closed immersion of the subscheme `I` cuts
  out.
* `Stacks.AmpleCohomologicalCriterion.closedIdealSubobject Z`: the ideal sheaf of the reduced
  closed subscheme supported on a closed set `Z`, as a subobject of `𝒪_X`.

## Main results

* `Stacks.AmpleCohomologicalCriterion.isQuasicoherent_kerSubobject`,
  `isQuasicoherent_idealSubobject` and `isQuasicoherent_closedIdealSubobject`: all three are
  quasi-coherent, in the exact shape `(Subobject.underlying.obj _).IsQuasicoherent` that the
  hypothesis of Tag 0B5P quantifies over.
* `Stacks.AmpleCohomologicalCriterion.idealSubobject_mono`: `I ≤ J` gives
  `idealSubobject I ≤ idealSubobject J`.
* `Stacks.AmpleCohomologicalCriterion.closedIdealSubobject_antitone`: `Z ≤ Z'` gives
  `closedIdealSubobject Z' ≤ closedIdealSubobject Z`. **This is the inclusion `I' ⊆ I` of the
  proof of Tag 0B5P**, for `Z ⊆ Z'`.

## Implementation notes

`Stacks.AmpleCohomologicalCriterion.unitToPushforwardObjUnit_comp` repeats a `private` lemma of
`StacksFrontier/AlgebraicGeometry/Morphisms/Closure/ImageQuasicoherent.lean`, which is not visible
here; both are `ext U; rfl`. It is a deduplication target if that one is ever made public.

Two rewrites in `Stacks.AmpleCohomologicalCriterion.kerSubobject_le_comp` would fail.
`Scheme.Modules` is a non-reducible abbreviation for `SheafOfModules X.ringCatSheaf`, so the goal
there is not type-correct at `implicit` transparency and neither `Category.assoc` nor `zero_comp`
can be used as a rewrite — the reassociation is supplied as the term `(Category.assoc _ _ _).symm`
and the final step as the term `zero_comp`, both of which elaborate at default transparency. Only
`kernel.condition`, whose pattern is a bare composition of two named morphisms, rewrites
normally.

Monotonicity is transported along an equality of *morphisms of schemes*,
`AlgebraicGeometry.Scheme.IdealSheafData.inclusion_subschemeι`, rather than of modules. That is
why `kerSubobject` is stated for an arbitrary morphism into `X` instead of only for
`I.subschemeι`: both sides of that equality are morphisms out of `J.subscheme`, so `congrArg`
applies to the function `kerSubobject` directly and no dependent rewrite arises.

## References

* [Stacks Project, Tag 0B5P](https://stacks.math.columbia.edu/tag/0B5P)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.AmpleCohomologicalCriterion

variable {X : Scheme.{u}}

/-- The canonical map `𝒪_X ⟶ (f ≫ g)_* 𝒪_W` factors through `𝒪_X ⟶ g_* 𝒪_V`. -/
theorem unitToPushforwardObjUnit_comp {W V Y : Scheme.{u}} (f : W ⟶ V) (g : V ⟶ Y) :
    SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
        (Scheme.Modules.pushforward g).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
        (Scheme.Modules.pushforwardComp f g).hom.app
          (SheafOfModules.unit W.ringCatSheaf) := by
  ext U
  rfl

/-- **The ideal sheaf of a morphism of schemes, as a subobject of `𝒪_X`**: the kernel of the
canonical map `𝒪_X ⟶ i_* 𝒪_W`. For `i` a closed immersion this is the ideal sheaf of the closed
subscheme it presents, and for `i` merely quasi-compact it is the ideal sheaf of the
scheme-theoretic image of `i`. -/
noncomputable def kerSubobject {W : Scheme.{u}} (i : W ⟶ X) :
    Subobject (SheafOfModules.unit X.ringCatSheaf) :=
  Subobject.mk (kernel.ι (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom))

/-- The underlying module of `Stacks.AmpleCohomologicalCriterion.kerSubobject i` is the kernel
itself. -/
noncomputable def underlyingKerSubobjectIso {W : Scheme.{u}} (i : W ⟶ X) :
    Subobject.underlying.obj (kerSubobject i) ≅
      kernel (SheafOfModules.unitToPushforwardObjUnit i.toRingCatSheafHom) :=
  Subobject.underlyingIso _

/-- **The ideal sheaf of a quasi-compact morphism is quasi-coherent**, in the subobject spelling.
This is [Stacks, Tag 01R8] part (1), transported along
`Stacks.AmpleCohomologicalCriterion.underlyingKerSubobjectIso`. -/
theorem isQuasicoherent_kerSubobject {W : Scheme.{u}} (i : W ⟶ X) [QuasiCompact i] :
    (Subobject.underlying.obj (kerSubobject i)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (underlyingKerSubobjectIso i).symm
    (AlgebraicGeometry.isQuasicoherent_kernel_unitToPushforwardObjUnit i)

/-- **Factoring the morphism enlarges the ideal sheaf.** If `i` factors as `f ≫ g` then the
kernel of `𝒪_X ⟶ g_* 𝒪_V` is contained in the kernel of `𝒪_X ⟶ i_* 𝒪_W`, because the latter map
factors through the former. -/
theorem kerSubobject_le_comp {W V : Scheme.{u}} (f : W ⟶ V) (g : V ⟶ X) :
    kerSubobject g ≤ kerSubobject (f ≫ g) := by
  refine Subobject.mk_le_mk_of_comm (kernel.lift _ (kernel.ι _) ?_) (kernel.lift_ι _ _ _)
  rw [unitToPushforwardObjUnit_comp]
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [kernel.condition]
  exact zero_comp

/-- **The ideal sheaf of `I : X.IdealSheafData`, as a subobject of `𝒪_X`**: the kernel of
`𝒪_X ⟶ i_* 𝒪_Z` for `i : Z ⟶ X` the closed immersion of the subscheme that `I` cuts out. -/
noncomputable def idealSubobject (I : X.IdealSheafData) :
    Subobject (SheafOfModules.unit X.ringCatSheaf) :=
  kerSubobject I.subschemeι

/-- **The ideal sheaf of an ideal sheaf datum is quasi-coherent**, in the shape that the
hypothesis of [Stacks, Tag 0B5P] quantifies over. -/
theorem isQuasicoherent_idealSubobject (I : X.IdealSheafData) :
    (Subobject.underlying.obj (idealSubobject I)).IsQuasicoherent :=
  isQuasicoherent_kerSubobject I.subschemeι

/-- **`Stacks.AmpleCohomologicalCriterion.idealSubobject` is monotone.** A larger ideal sheaf datum
gives a larger subobject of `𝒪_X`: the inclusion of subschemes `J.subscheme ⟶ I.subscheme` factors
`J.subschemeι` through `I.subschemeι`. -/
theorem idealSubobject_mono {I J : X.IdealSheafData} (h : I ≤ J) :
    idealSubobject I ≤ idealSubobject J :=
  (kerSubobject_le_comp (Scheme.IdealSheafData.inclusion h) I.subschemeι).trans_eq
    (congrArg kerSubobject (Scheme.IdealSheafData.inclusion_subschemeι h))

/-- **The ideal sheaf of a closed subset, as a subobject of `𝒪_X`**: the ideal sheaf of the
reduced closed subscheme supported on `Z`, which is the vanishing ideal sheaf of
[Stacks, Tag 01J3]. -/
noncomputable def closedIdealSubobject (Z : Closeds X) :
    Subobject (SheafOfModules.unit X.ringCatSheaf) :=
  idealSubobject (Scheme.IdealSheafData.vanishingIdeal Z)

/-- **The ideal sheaf of a closed subset is quasi-coherent.** This is what makes the hypothesis
of [Stacks, Tag 0B5P] applicable to the two closed sets its proof forms. -/
theorem isQuasicoherent_closedIdealSubobject (Z : Closeds X) :
    (Subobject.underlying.obj (closedIdealSubobject Z)).IsQuasicoherent :=
  isQuasicoherent_idealSubobject _

/-- **A larger closed set has a smaller ideal sheaf.** For `Z ⊆ Z'` this is the inclusion
`I' ⊆ I` with which the proof of [Stacks, Tag 0B5P] forms its short exact sequence. -/
theorem closedIdealSubobject_antitone {Z Z' : Closeds X} (h : Z ≤ Z') :
    closedIdealSubobject Z' ≤ closedIdealSubobject Z :=
  idealSubobject_mono (Scheme.IdealSheafData.vanishingIdeal_antimono h)

end Stacks.AmpleCohomologicalCriterion

end
