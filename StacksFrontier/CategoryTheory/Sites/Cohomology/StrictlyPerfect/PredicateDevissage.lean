module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedComplexInduction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes

/-!
# The dévissage of a strictly perfect complex, for an arbitrary property

Let `(C, O)` be a ringed site and let `Pr` be a property of the objects of `D(O)` which is

* invariant under isomorphism,
* satisfied by the zero objects,
* inherited by a split retract,
* satisfied by a finite direct sum of objects satisfying it, and
* satisfied at the middle vertex of a distinguished triangle whose outer two vertices
  satisfy it.

Then `Pr` holds at every strictly perfect complex of `O`-modules ([Stacks, Tag 08FL]) whose
terms' degrees it already covers, in the sense that it holds at the structure sheaf placed in
each degree in which the complex is nonzero.

The dévissage is the one of [Stacks, Tag 08FL]: a strictly perfect complex is bounded, so it is
built from its terms by finitely many extensions, and each term is a direct summand of a finite
free `O`-module, hence a retract of a finite direct sum of copies of `O`.

## Main results

* `StrictlyPerfectDevissage.property_singleFunctor_of_isDirectSummandOfFiniteFree`: the term
  step — a direct summand of a finite free `O`-module, placed in a degree, satisfies `Pr` as soon
  as the structure sheaf placed in that degree does.
* `StrictlyPerfectDevissage.property_of_isStrictlyPerfect`: the induction.

## Implementation notes

*Why a predicate and not a natural transformation.*
`Stacks.Cohomology.ProjectionFormulaPerfectDevissage.isIso_app_of_isStrictlyPerfect` runs this
same dévissage on an arbitrary ringed site, but only for the property "a fixed natural
transformation `α` is invertible here". That property is not a priori stable under the shift, so
it has to be carried at every shift at once, and its extension step is the five lemma applied to
the images of a distinguished triangle under two exact functors, which is why that statement
carries a `CategoryTheory.Functor.CommShift` and a `CategoryTheory.Functor.IsTriangulated` for
each of the two functors. A general predicate needs none of that: the extension step is
`hobj₂` directly, at the distinguished triangle `DerivedCategory.triangleOfSES` of the short
exact sequence of complexes that the stupid truncations produce, and no shift is quantified
over. The two statements have no common generalisation that is worth stating, since the
natural-transformation version's conclusion is at all shifts and its hypotheses are about
functors rather than about objects.

*The closure properties asked for are exactly those the Tor amplitude of a derived tensor
product has.* With `Pr E` read as "`E ⊗^𝐋_O M` has Tor amplitude in `[a, b]`", `hiso` is
`Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitude.of_iso`, `hretract` is
`…hasTorAmplitude_of_retract` ([Stacks, Tag 08G3]), `hbiproduct` is
`…hasTorAmplitude_biproduct`, and `hobj₂` is `…hasTorAmplitude_obj₂` ([Stacks, Tag 08G2] (2)).
The binders of the hypotheses below are chosen to match those declarations, so that each is
supplied by applying the corresponding one to the derived tensor product datum.

*Why the base case is restricted to the degrees in which the complex is nonzero.* A caller
whose property depends on the degree — Tor amplitude in a fixed interval does, since
`O[i] ⊗^𝐋_O M ≅ M⟦-i⟧` — cannot satisfy `Pr (O[i])` for every `i : ℤ` at once, but needs only
the finitely many degrees that `K` occupies. In the remaining degrees the term `K.X i` is a zero
object, so `hzero` closes that case and nothing about `O[i]` is used. Phrasing `hunit`
conditionally rather than over an interval keeps the statement free of a choice of bounds for
`K`, which `IsStrictlyPerfect.bounded` provides only as the finiteness of the support.

*No `@[stacks]` attribute is attached.* This is one step of the second assertion of
[Stacks, Tag 0DKS] (and of [Stacks, Tag 0DI4]) and not that assertion; it is consumed by
`hasTorAmplitude_restrictScalars_tensor_of_isStrictlyPerfect` in the namespace
`Stacks.SheafOfModules.DerivedTensorProduct`, and the assertion is registered in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativelyPerfectDerivedTensor`. Nothing below
mentions a morphism of sites, a tensor product or a Tor dimension.

*The finite biproducts of the `O`-modules are not installed as an instance here.* The category
of sheaves of modules is abelian, hence has finite products, hence has finite biproducts; but
that step is not an instance, and both
`Stacks.SheafOfModules.Tensor.isDirectSummandOfFiniteFree_iff_retract_biproduct`, whose
statement names the direct sum of `n` copies of `O`, and this file's use of it must agree on
which one. So that file's own witness is named explicitly in the proof below rather than
reproduced, and the direct sums in the derived category are the ones a pretriangulated category
has.

## References

* [Stacks Project, Tag 08FL](https://stacks.math.columbia.edu/tag/08FL)
* [Stacks Project, Tag 08G2](https://stacks.math.columbia.edu/tag/08G2)
* [Stacks Project, Tag 08G3](https://stacks.math.columbia.edu/tag/08G3)
* [Stacks Project, Tag 0DKS](https://stacks.math.columbia.edu/tag/0DKS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.Cohomology.StrictlyPerfectDevissage

universe u v w d

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J CommRingCat.{w})
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
  (Pr : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) → Prop)

/-- **The term step of the dévissage of a strictly perfect complex.** A direct summand `F` of a
finite free `O`-module, placed in degree `i` of `D(O)`, satisfies a property which is invariant
under isomorphism, inherited by split retracts and satisfied by finite direct sums, as soon as
the structure sheaf placed in degree `i` satisfies it.

A direct summand of a finite free `O`-module is a retract of a direct sum of finitely many
copies of `O` ([Stacks, Tag 08FL]); the single functor in degree `i` is additive, so it carries
that direct sum to the direct sum of the copies of `O[i]` and that retraction to a
retraction. -/
theorem property_singleFunctor_of_isDirectSummandOfFiniteFree
    (hiso : ∀ (A B : DerivedCategory (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O))), (A ≅ B) → Pr A → Pr B)
    (hretract : ∀ (A B : DerivedCategory (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O))) (i : A ⟶ B) (r : B ⟶ A),
      i ≫ r = 𝟙 A → Pr B → Pr A)
    (hbiproduct : ∀ {ι : Type} [Finite ι] (f : ι → DerivedCategory (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O))) [HasBiproduct f],
      (∀ j, Pr (f j)) → Pr (⨁ f))
    (i : ℤ)
    (hunit : Pr ((DerivedCategory.singleFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) i).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O))))
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hF : IsDirectSummandOfFiniteFree (Stacks.SheafOfModules.Tensor.ringSheaf O) F) :
    Pr ((DerivedCategory.singleFunctor
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) i).obj F) := by
  let : HasFiniteBiproducts
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    Stacks.SheafOfModules.Tensor.hasFiniteBiproducts_sheafOfModules O
  obtain ⟨m, ⟨ret⟩⟩ :=
    (Stacks.SheafOfModules.Tensor.isDirectSummandOfFiniteFree_iff_retract_biproduct O F).mp hF
  have hmap := ret.map (DerivedCategory.singleFunctor
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) i)
  refine hretract _ _ hmap.i hmap.r hmap.retract ?_
  refine hiso _ _ ((DerivedCategory.singleFunctor
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) i).mapBiproduct
      (fun _ : Fin m => SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf O))).symm ?_
  exact hbiproduct _ fun _ => hunit

/-- **The dévissage of a strictly perfect complex, for an arbitrary property of the objects of
`D(O)`.** Let `(C, O)` be a ringed site and let `Pr` be a property of the objects of `D(O)`
which is invariant under isomorphism, holds at the zero objects, is inherited by split retracts,
holds at a finite direct sum of objects at which it holds, and holds at the middle vertex of a
distinguished triangle whose first and third vertices it holds at. If `Pr` holds at the
structure sheaf placed in every degree in which a strictly perfect complex `K` of `O`-modules is
nonzero, then `Pr` holds at `K` ([Stacks, Tag 08FL]).

The induction is on the stupid truncations of `K`, which is bounded: the truncation `K ≥ p` is
an extension of the term `K^p` placed in degree `p` by `K ≥ p+1`, and that extension is a short
exact sequence of complexes, whose image in `D(O)` is a distinguished triangle. Each term of `K`
is a direct summand of a finite free `O`-module, so the term step is
`property_singleFunctor_of_isDirectSummandOfFiniteFree`. -/
theorem property_of_isStrictlyPerfect
    (hiso : ∀ (A B : DerivedCategory (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O))), (A ≅ B) → Pr A → Pr B)
    (hzero : ∀ (A : DerivedCategory (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O))), IsZero A → Pr A)
    (hretract : ∀ (A B : DerivedCategory (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O))) (i : A ⟶ B) (r : B ⟶ A),
      i ≫ r = 𝟙 A → Pr B → Pr A)
    (hbiproduct : ∀ {ι : Type} [Finite ι] (f : ι → DerivedCategory (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O))) [HasBiproduct f],
      (∀ j, Pr (f j)) → Pr (⨁ f))
    (hobj₂ : ∀ (tri : Triangle (DerivedCategory (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf O)))), tri ∈ distinguishedTriangles →
      Pr tri.obj₁ → Pr tri.obj₃ → Pr tri.obj₂)
    (K : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    (hK : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf O) K)
    (hunit : ∀ i : ℤ, ¬ IsZero (K.X i) →
      Pr ((DerivedCategory.singleFunctor
        (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) i).obj
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf O)))) :
    Pr (DerivedCategory.Q.obj K) := by
  refine Stacks.DerivedCategory.BoundedInduction.property_of_bounded_complex Pr
    (fun {A B} e h => hiso A B e h) hzero ?_ K hK.bounded ?_
  · intro S hS h₁ h₃
    exact hobj₂ (DerivedCategory.triangleOfSES hS)
      (DerivedCategory.triangleOfSES_distinguished hS) h₁ h₃
  · intro i
    by_cases hKi : IsZero (K.X i)
    · exact hzero _ (Functor.map_isZero _ hKi)
    · exact property_singleFunctor_of_isDirectSummandOfFiniteFree O Pr hiso hretract
        hbiproduct i (hunit i hKi) (K.X i) (hK.termDirectSummand i)

end Stacks.Cohomology.StrictlyPerfectDevissage

end
