module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationFunctorial

/-!
# Local surjectivity of the ungraded realization

Let `f : A ⟶ B` be a unital homomorphism of graded algebras of presheaves of modules on a site.
This file proves that if every homogeneous component `f i : A i ⟶ B i` is locally surjective then
so is the induced morphism of the ungraded realizations — as presheaves of rings, as sheaves of
rings, and, on a scheme, as the algebra sheaves of [Stacks, Tag 01LM] that a relative spectrum
consumes.

The last of these is the hypothesis of
`Stacks.RelativeSpecClosedImmersion.isClosedImmersion_relativeSpecMapOfAlgebraHom`, which turns a
locally surjective morphism of quasi-coherent algebra sheaves into a closed immersion of relative
spectra with no further hypotheses. Degreewise local surjectivity is what one has in practice —
for instance the comparison `f^* B̃ ⟶ ⨁ₙ ℐⁿ` of
`Stacks.Cohomology.FormalFunctions.baseReesPullbackHom` is surjective on affine charts in every
nonnegative degree and is *not* an isomorphism — so this is the bridge between the two.

## Main results

* `Stacks.GradedAlgebra.isLocallySurjective_totalPresheafMap`: the presheaf statement, and
  `Stacks.GradedAlgebra.imageSieve_totalPresheafMap_mem` the sieve of local lifts it is proved
  from.
* `Stacks.GradedAlgebra.isLocallySurjective_totalSheafMap` and
  `SheafOfModules.GradedAlgebra.isLocallySurjective_ungradedSheafMap`: the sheaf statement.
* `Stacks.RelativeSpec.isLocallySurjective_gradedAlgebraSheafMap`: **the morphism of algebra
  sheaves on a scheme induced by a degreewise locally surjective homomorphism of sheaves of
  graded algebras is locally surjective.**

## Implementation notes

The presheaf statement is where the work is, and it is an induction over
`Stacks.GradedAlgebra.incl_induction`: a section of `Stacks.GradedAlgebra.Total` over an object of
the site is a *finite* sum of homogeneous sections, so the three cases are that `0` lifts
everywhere, that a homogeneous section of degree `i` lifts wherever the degree-`i` component lifts
it (`GrothendieckTopology.superset_covering`), and that a sum lifts on the intersection of two
covering sieves (`GrothendieckTopology.intersection_covering`). This is exactly the local
induction that the functoriality lemmas of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UngradedRealizationFunctorial` avoid by using the
universal property; here it cannot be avoided, because local surjectivity is a statement about
sections.

Passing to the sheafification is then formal:
`CategoryTheory.Presheaf.isLocallySurjective_of_isLocallySurjective_fac` applied to
`Stacks.GradedAlgebra.toTotalSheaf_totalSheafMap`.

The elements of the image sieve of a morphism of presheaves of modules are typed through
`CategoryTheory.ConcreteCategory.ToType` of the presheaf of abelian groups, which is the module's
section type but not syntactically so; the proof names the section at its module type once
(`x'`) so that the rewrites by `Stacks.GradedAlgebra.totalPresheafMap_app_incl` and
`Stacks.GradedAlgebra.totalRestrict_incl` apply.

No `@[stacks]` attribute is attached: local surjectivity of the ungraded realization is not the
assertion of a tag, it is the input [Stacks, Tag 01LM]'s relative spectrum needs.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace

universe v u w

namespace Stacks.GradedAlgebra

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}} {ι : Type} [DecidableEq ι]
  [AddMonoid ι] {P Q : ι → PresheafOfModules.{w} R} {A : GradedAlgebra P} {B : GradedAlgebra Q}
  (J : GrothendieckTopology C)

/-- **Every section of the ungraded realization of the target is locally in the image**, as soon
as every homogeneous piece of the homomorphism is locally surjective: the sieve of local lifts of
a section is a covering sieve.

The induction is `Stacks.GradedAlgebra.incl_induction`: a section of the *presheaf* ungraded
realization is a finite sum of homogeneous ones, a homogeneous section of degree `i` lifts
wherever the degree-`i` component does, and a sum lifts on the intersection of two covering
sieves. No sheaf condition and no sheafification is involved. -/
theorem imageSieve_totalPresheafMap_mem (f : UnitalHom A B)
    (hf : ∀ i : ι, Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R).map (f.app i)))
    {U : C} (s : B.Total (op U)) :
    Presheaf.imageSieve (totalPresheafMap f) s ∈ J U := by
  induction s using B.incl_induction with
  | zero =>
      have h0 : (0 : B.Total (op U)) = (totalPresheafMap f).app (op U) 0 :=
        (map_zero ((totalPresheafMap f).app (op U)).hom).symm
      rw [h0, Presheaf.imageSieve_app]
      exact J.top_mem U
  | incl i y =>
      refine J.superset_covering ?_ ((hf i).imageSieve_mem (U := U) y)
      intro V g hg
      obtain ⟨x, hx⟩ := hg
      let x' : ↥((P i).obj (op V)) := x
      have hx' : PresheafOfModules.Hom.app (f.app i) (op V) x' =
          sectionRestrict (Q i) g.op y := hx
      refine ⟨A.incl i x', ?_⟩
      change (totalPresheafMap f).app (op V) (A.incl i x') =
        B.totalRestrict g.op (B.incl i y)
      rw [totalPresheafMap_app_incl, B.totalRestrict_incl]
      exact congrArg (B.incl i) hx'
  | add s s' hs hs' =>
      refine J.superset_covering ?_ (J.intersection_covering hs hs')
      rintro V g ⟨⟨t, ht⟩, ⟨t', ht'⟩⟩
      refine ⟨t + t', ?_⟩
      change (totalPresheafMap f).app (op V) (t + t') =
        B.totalRestrict g.op (s + s')
      rw [map_add, map_add]
      exact congrArg₂ (· + ·) ht ht'

/-- **A homomorphism of graded algebras whose homogeneous pieces are locally surjective induces
a locally surjective morphism of the ungraded realizations as presheaves of rings.** -/
theorem isLocallySurjective_totalPresheafMap (f : UnitalHom A B)
    (hf : ∀ i : ι,
      Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R).map (f.app i))) :
    Presheaf.IsLocallySurjective J (totalPresheafMap f) :=
  ⟨imageSieve_totalPresheafMap_mem J f hf⟩

/-- **The same after sheafification**: the morphism of the ungraded realizations as *sheaves* of
rings is locally surjective.

This is not the sheafification of the presheaf statement as a functor: the morphism of sheaves is
obtained from the universal property, and what identifies it is
`Stacks.GradedAlgebra.toTotalSheaf_totalSheafMap`. Composed with the sheafification unit of the
source it becomes the presheaf morphism followed by the sheafification unit of the target, both of
which are locally surjective, and local surjectivity of a composite passes to its second
factor. -/
theorem isLocallySurjective_totalSheafMap [HasSheafify J RingCat.{w}]
    [J.WEqualsLocallyBijective RingCat.{w}] (f : UnitalHom A B)
    (hf : ∀ i : ι,
      Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf R).map (f.app i))) :
    Presheaf.IsLocallySurjective J (totalSheafMap J f).hom :=
  have := isLocallySurjective_totalPresheafMap J f hf
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac J (toTotalSheaf_totalSheafMap J f)

end Stacks.GradedAlgebra

namespace SheafOfModules.GradedAlgebra

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J RingCat.{u}] [J.WEqualsLocallyBijective RingCat.{u}]
  [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})]

omit [J.HasSheafCompose (CategoryTheory.forget RingCat.{u})] in
/-- **A unital homomorphism of sheaves of graded algebras with locally surjective homogeneous
components induces a locally surjective morphism of the ungraded realizations.** -/
theorem isLocallySurjective_ungradedSheafMap {A B : GradedAlgebra.{u, u} R}
    (f : UnitalHom A B)
    (hf : ∀ i : ℤ, Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (f.app i).val)) :
    Sheaf.IsLocallySurjective (ungradedSheafMap f) :=
  Stacks.GradedAlgebra.isLocallySurjective_totalSheafMap J f.toPresheafGradedAlgebraHom hf

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The same between the commutative lifts.** `Stacks.CommRingSheaf.sheaf` keeps the carrier
and the ring operations, so the sieve of local lifts of a section is literally the sieve of local
lifts of that same section of the underlying sheaf of rings. -/
theorem isLocallySurjective_ungradedCommSheafMap {A B : GradedAlgebra.{u, u} R}
    (f : UnitalHom A B)
    (hcA : ∀ (i j : ℤ) (W : Cᵒᵖ) (a : (A.piece i).val.obj W) (b : (A.piece j).val.obj W),
      HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (hcB : ∀ (i j : ℤ) (W : Cᵒᵖ) (a : (B.piece i).val.obj W) (b : (B.piece j).val.obj W),
      HEq ((B.mul i j).app W a b) ((B.mul j i).app W b a))
    (hf : ∀ i : ℤ, Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map (f.app i).val)) :
    Sheaf.IsLocallySurjective (ungradedCommSheafMap f hcA hcB) :=
  have := isLocallySurjective_ungradedSheafMap f hf
  ⟨fun {U} s => Presheaf.imageSieve_mem J (ungradedSheafMap f).hom
    (U := op U) (show ↥(B.ungradedSheaf.obj.obj (op U)) from s)⟩

end SheafOfModules.GradedAlgebra

namespace Stacks.RelativeSpec

open _root_.AlgebraicGeometry

/-- **A unital homomorphism of sheaves of graded algebras on a scheme whose homogeneous
components are locally surjective induces a locally surjective morphism of the algebra sheaves**
of [Stacks, Tag 01LM].

This is the hypothesis that
`Stacks.RelativeSpecClosedImmersion.isClosedImmersion_relativeSpecMapOfAlgebraHom` consumes: the
relative spectrum of a locally surjective morphism of quasi-coherent algebra sheaves is a closed
immersion, and local surjectivity of the ungraded realization of a graded homomorphism is what
had to be supplied to feed it. -/
theorem isLocallySurjective_gradedAlgebraSheafMap (X : Scheme.{u})
    {A B : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
    (f : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (hcA : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (hcB : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (B.piece i).val.obj W)
      (b : (B.piece j).val.obj W), HEq ((B.mul i j).app W a b) ((B.mul j i).app W b a))
    (hf : ∀ i : ℤ, Presheaf.IsLocallySurjective (Opens.grothendieckTopology (X : TopCat))
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (f.app i).val)) :
    Sheaf.IsLocallySurjective (gradedAlgebraSheafMap X f hcA hcB).right :=
  SheafOfModules.GradedAlgebra.isLocallySurjective_ungradedCommSheafMap f hcA hcB hf

/-- `Stacks.RelativeSpec.isLocallySurjective_gradedAlgebraSheafMap` with its hypothesis in the
spelling a morphism of sheaves of modules carries it: local surjectivity of the underlying
morphism of sheaves of abelian groups. -/
theorem isLocallySurjective_gradedAlgebraSheafMap' (X : Scheme.{u})
    {A B : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
    (f : SheafOfModules.GradedAlgebra.UnitalHom A B)
    (hcA : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (A.piece i).val.obj W)
      (b : (A.piece j).val.obj W), HEq ((A.mul i j).app W a b) ((A.mul j i).app W b a))
    (hcB : ∀ (i j : ℤ) (W : (Opens ↥X)ᵒᵖ) (a : (B.piece i).val.obj W)
      (b : (B.piece j).val.obj W), HEq ((B.mul i j).app W a b) ((B.mul j i).app W b a))
    (hf : ∀ i : ℤ,
      Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf X.ringCatSheaf).map (f.app i))) :
    Sheaf.IsLocallySurjective (gradedAlgebraSheafMap X f hcA hcB).right :=
  isLocallySurjective_gradedAlgebraSheafMap X f hcA hcB hf

end Stacks.RelativeSpec
end
