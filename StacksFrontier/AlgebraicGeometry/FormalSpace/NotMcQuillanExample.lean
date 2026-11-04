module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.SectionsDoNotSeparatePoints
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SectionsIndependentOfPresentation
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout

/-!
# An affine formal algebraic space which is not McQuillan

The affine formal algebraic space of Stacks 0CBD is a directed colimit `X = colim Spec(A_s)` of
affine thickenings whose inverse limit of section rings `lim Γ(Spec(A_s), 𝒪)` is a field, while
the stage indexed by the empty set has infinitely many points. A field cannot surject onto the
ring of a stage with more than one point, so no presentation of `X` has surjective section
projections and `X` fails McQuillan's criterion, condition (4) of Stacks 0AIC.

## Main results

* `exists_isAffineFormalAlgebraicSpace_not_hasSomeSurjectivePresentation`: **Stacks 0CBC.**
  There is an affine formal algebraic space which is not McQuillan.
* `exists_isAffineFormalAlgebraicSpace_not_hasAllSurjectivePresentations`: the same example
  also fails condition (5) of Stacks 0AIC.

## Implementation notes

McQuillan's criterion is a condition on *some* presentation, whereas the example of Stacks 0CBD
comes with a distinguished one, so the argument must transport the computation of the section
limit between presentations; that is
`AlgebraicGeometry.FormalSpace.sectionsRingEquivOfPresentations`, which makes the section limit
of a competing presentation a field as well. The infinitude of points is transported in the
other direction: a stage of the given presentation factors through a stage of the competing one
by `AlgebraicGeometry.FormalSpace.exists_factor_to_affine_stage`, that factorisation is a
thickening by `AlgebraicGeometry.FormalSpace.isThickening_of_factor_stage`, and a thickening is
a homeomorphism on points. Finally a surjection of rings induces an injection of prime spectra,
so a stage receiving a surjection from a field has at most one point, and its underlying space
is the spectrum of its ring because the stage is affine.

## References

* [Stacks Project, Tag 0CBC](https://stacks.math.columbia.edu/tag/0CBC)
* [Stacks Project, Tag 0CBD](https://stacks.math.columbia.edu/tag/0CBD)
* [Stacks Project, Tag 0AIC](https://stacks.math.columbia.edu/tag/0AIC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FormalSpace

universe u

/-- **Stacks 0CBC.** There exists an affine formal algebraic space which is not McQuillan: the
example of Stacks 0CBD admits no presentation by affine thickenings whose section-ring
projections are all surjective. -/
@[stacks 0CBC]
public theorem exists_isAffineFormalAlgebraicSpace_not_hasSomeSurjectivePresentation :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS),
      IsAffineFormalAlgebraicSpace B S hS X ∧ ¬ HasSomeSurjectivePresentation B S hS X := by
  classical
  obtain ⟨B, S, hS, X, hAff, I₀, pre₀, hne₀, hdir₀, D₀, hD₀, ⟨e₀⟩, hfield, i₀, hinf⟩ :=
    exists_isAffineFormalAlgebraicSpace_sections_isField_infinite_stage.{u}
  refine ⟨B, S, hS, X, hAff, ?_⟩
  rintro ⟨-, I₁, pre₁, hne₁, hdir₁, D₁, hD₁, ⟨e₁⟩, hsurj⟩
  let : Preorder I₀ := pre₀
  let : Preorder I₁ := pre₁
  have : Nonempty I₀ := hne₀
  have : IsDirected I₀ (· ≤ ·) := hdir₀
  have : Nonempty I₁ := hne₁
  have : IsDirected I₁ (· ≤ ·) := hdir₁
  have := hinf
  -- The section limit does not depend on the presentation, so it is a field for `D₁` too.
  let : Field (sectionDiagram B S hS D₁ ⋙ forget CommRingCat.{u}).sections :=
    (MulEquiv.isField hfield
      (sectionsRingEquivOfPresentations B S hS X I₀ D₀ hD₀ e₀ I₁ D₁ hD₁ e₁).symm.toMulEquiv).toField
  -- The infinite stage of `D₀` factors through a stage of `D₁` by a thickening.
  obtain ⟨k, g, hg⟩ := exists_factor_to_affine_stage B S hS X I₁ D₁ hD₁ e₁ (D₀.obj i₀)
    (colimit.ι (D₀ ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) i₀ ≫ e₀.inv)
  have : Infinite ((BigAffineFppf.toScheme B S hS).obj (D₁.obj k)) :=
    Infinite.of_injective _ (isThickening_of_factor_stage B S hS X I₀ D₀ hD₀ e₀ I₁ D₁ hD₁ e₁ i₀ k g
      hg).homeomorph.injective
  -- The projection of the section limit to the stage `k` is a surjective ring homomorphism.
  let π : (sectionDiagram B S hS D₁ ⋙ forget CommRingCat.{u}).sections →+*
      Γ((BigAffineFppf.toScheme B S hS).obj (D₁.obj k), ⊤) :=
    (Pi.evalRingHom (fun j ↦ ((sectionDiagram B S hS D₁).obj j : Type u)) (op k)).comp
      (RingCat.sectionsSubring
        (sectionDiagram B S hS D₁ ⋙ forget₂ CommRingCat RingCat.{u})).subtype
  -- A surjection out of a field leaves the stage at most one prime, hence at most one point.
  have : Subsingleton (Spec Γ((BigAffineFppf.toScheme B S hS).obj (D₁.obj k), ⊤)) :=
    (PrimeSpectrum.comap_injective_of_surjective π fun y ↦ hsurj k y).subsingleton
  have hspace : Subsingleton ((BigAffineFppf.toScheme B S hS).obj (D₁.obj k) : Type u) :=
    (Scheme.homeoOfIso
      ((BigAffineFppf.toScheme B S hS).obj (D₁.obj k)).isoSpec).injective.subsingleton
  exact not_subsingleton _ hspace

/-- The same example refutes condition (5) of Stacks 0AIC: there is an affine formal algebraic
space one of whose presentations by affine thickenings has a section-ring projection which is
not surjective. -/
public theorem exists_isAffineFormalAlgebraicSpace_not_hasAllSurjectivePresentations :
    ∃ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : FppfSheaf B S hS),
      IsAffineFormalAlgebraicSpace B S hS X ∧ ¬ HasAllSurjectivePresentations B S hS X := by
  obtain ⟨B, S, hS, X, hAff, hX⟩ :=
    exists_isAffineFormalAlgebraicSpace_not_hasSomeSurjectivePresentation.{u}
  exact ⟨B, S, hS, X, hAff, fun h ↦ hX h.hasSomeSurjectivePresentation⟩

end AlgebraicGeometry.FormalSpace

end
