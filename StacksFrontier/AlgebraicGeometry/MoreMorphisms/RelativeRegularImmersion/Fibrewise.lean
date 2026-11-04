module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.ClosedBridge
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.Chart
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# The fibrewise criterion of Stacks tag 063W

The closing sentence of Stacks tag 063W is a criterion with no point in it:  if `T` is a closed
subscheme of a scheme `X` flat and locally of finite presentation over `S`, if `T` is itself flat
and locally of finite presentation over `S`, and if every fibre `T_s ⊆ X_s` is a quasi-regular
immersion, then `T → X` is a relative quasi-regular immersion over `S`.

## Main results

* `Stacks.AlgebraicGeometry.isQuasiRegularImmersion_comap_of_flat`: a quasi-regular closed
  subscheme pulls back to a quasi-regular closed subscheme along a flat morphism.
* `Stacks.AlgebraicGeometry.isRelativeQuasiRegularImmersion_subschemeι_of_forall_fiber`: the
  fibrewise criterion.

## Implementation notes

Both conjuncts of the conclusion are local on `X`, and the affine chart of the tag
(`Stacks.AlgebraicGeometry.exists_affineOpen_isWeaklyRegular_ideal_of_fibre`) produces, at every
point of the support, an affine open carrying a weakly regular family generating the ideal of `T`.
That is exactly a witness for the affine criterion of Stacks tag 063G, so no gluing is needed
beyond the one that criterion already performs.

The chart asks for the fibre hypothesis on an open neighbourhood of the point in the fibre and for
flatness over the base at the point;  the first comes from the global hypothesis on the fibre by
restricting along the inclusion of the whole fibre, which is the flat base change
`isQuasiRegularImmersion_comap_of_flat`, and the second from global flatness of `T` over `S`.

Finite presentation of `T → X` — which is what the chart consumes — is not assumed:  it is Stacks
tag 02FV applied to `T → X → S`, the composite being locally of finite presentation by hypothesis
and `X → S` locally of finite type.

## References

* [Stacks Project, Lemma 31.22.8 (Tag 063W)](https://stacks.math.columbia.edu/tag/063W)
* [Stacks Project, Lemma 31.20.2 (Tag 063G)](https://stacks.math.columbia.edu/tag/063G)
* [Stacks Project, Lemma 29.21.11 (Tag 02FV)](https://stacks.math.columbia.edu/tag/02FV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry RingTheory.Sequence
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace Stacks.AlgebraicGeometry

universe u

variable {X S : Scheme.{u}}

/-- **A quasi-regular closed subscheme stays quasi-regular after a flat base change.**  If the
closed subscheme cut out by an ideal sheaf `I` on `Y` is a quasi-regular immersion and `g` is
flat, then the closed subscheme cut out by `I.comap g` is a quasi-regular immersion. -/
@[ega "IV 19.1.5" "(ii), special case"]
theorem isQuasiRegularImmersion_comap_of_flat {Y Y' : Scheme.{u}} (I : Y.IdealSheafData)
    (g : Y' ⟶ Y) [Flat g] (hI : IsQuasiRegularImmersion I.subschemeι) :
    IsQuasiRegularImmersion (I.comap g).subschemeι := by
  have hpb : IsPullback (Scheme.IdealSheafData.subschemeMap _ _ g (I.le_map_comap g))
      (I.comap g).subschemeι I.subschemeι g :=
    (AlgebraicGeometry.isPullback_of_isClosedImmersion (I.comap g).subschemeι I.subschemeι
      (Scheme.IdealSheafData.subschemeMap _ _ g (I.le_map_comap g)) g (by simp)
      (by simp [Scheme.IdealSheafData.ker_subschemeι])).flip
  refine isQuasiRegularImmersion_of_isQuasiRegularIdealSheaf _
    ((isQuasiRegularIdealSheaf_iff_kerGeneratedBy (I.comap g).subschemeι).mpr ?_)
  refine kerGeneratedBy_of_isPullback isQuasiRegular_of_ringHomFlat hpb ?_
  exact (isQuasiRegularIdealSheaf_iff_kerGeneratedBy I.subschemeι).mp
    (isQuasiRegularIdealSheaf_of_isQuasiRegularImmersion I.subschemeι hI)

/-- **The fibrewise criterion of Stacks tag 063W.**  Let `f : X ⟶ S` be flat and locally of finite
presentation and let `T` be a closed subscheme of `X` which is flat and locally of finite
presentation over `S`.  If every fibre of `T` is a quasi-regular closed subscheme of the
corresponding fibre of `X`, then `T` is a relative quasi-regular immersion over `S`. -/
@[stacks 063W "fibrewise criterion"]
theorem isRelativeQuasiRegularImmersion_subschemeι_of_forall_fiber (f : X ⟶ S) [Flat f]
    [LocallyOfFinitePresentation f] (T : X.IdealSheafData) [Flat (T.subschemeι ≫ f)]
    [LocallyOfFinitePresentation (T.subschemeι ≫ f)]
    (hfib : ∀ s : S, IsQuasiRegularImmersion (T.comap (f.fiberι s)).subschemeι) :
    IsRelativeQuasiRegularImmersion f T.subschemeι := by
  have _ : LocallyOfFinitePresentation T.subschemeι :=
    AlgebraicGeometry.locallyOfFinitePresentation_of_comp T.subschemeι f
  refine ⟨inferInstance, isQuasiRegularImmersion_of_isQuasiRegularIdealSheaf _ ?_⟩
  refine (isQuasiRegularIdealSheaf_iff_exists_affine_generators X _).mpr fun x hxq => ?_
  rw [definingIdealQuotient_support_eq_range, T.range_subschemeι] at hxq
  have hx : x ∈ T.support := hxq
  have hflat : ((T.subschemeι ≫ f).stalkMap (⟨x, hx⟩ : T.subscheme)).hom.Flat :=
    (Flat.iff_flat_stalkMap (T.subschemeι ≫ f)).mp inferInstance _
  have hfibx : ∃ V : (f.fiber (f x)).Opens, f.asFiber x ∈ V ∧ IsQuasiRegularImmersion
      (((T.comap (f.fiberι (f x))).comap V.ι).subschemeι) :=
    ⟨⊤, trivial, isQuasiRegularImmersion_comap_of_flat _ (⊤ : (f.fiber (f x)).Opens).ι
      (hfib (f x))⟩
  obtain ⟨V, hV, hxV, -, r, c, hgen, hwr⟩ :=
    exists_affineOpen_isWeaklyRegular_ideal_of_fibre f T x hx hfibx hflat ⊤ trivial
  exact ⟨⟨V, hV⟩, hxV, r, c, isGeneratedByOn_definingIdealOfHom_of_ker_app_eq_span _ hV c
    ((T.ker_subschemeι_app ⟨V, hV⟩).trans hgen), isQuasiRegular_of_isWeaklyRegular _ hwr⟩

end Stacks.AlgebraicGeometry

end
