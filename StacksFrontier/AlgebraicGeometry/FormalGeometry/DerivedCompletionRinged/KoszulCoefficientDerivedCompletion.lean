module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GlobalSectionsKoszulDerivedLimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PrincipalQuotientTowerDerivedCompletion
public import StacksFrontier.Homology.DerivedComplete.AdicDerivedCompletionKoszul
public import StacksFrontier.Homology.DerivedComplete.CechReflection

/-!
# The coefficient Koszul tower of a complex of modules has the derived completion as its
derived limit

Let `A` be a commutative ring, let `a_1, …, a_r ∈ A` and let `E` be a cochain complex of
`A`-modules. This file proves

`(-)^∧ (E) = R lim_n Hom•_A(Kos(a^{n+1}), E)`,

where the right-hand tower is `KoszulCoefficientTower.coefficientKoszulTower a` applied to `E`
and the left-hand side is `DerivedCompletion.derivedCompletionFunctor A a`, the reflector of
[Stacks, Tag 0G3E] into the objects of `D(A)` that are derived complete for
`Ideal.span (Set.range a)`.

This is **the module side of the identity `RΓ(𝒞, ℱ)^∧ = RΓ(𝒞, ℱ^∧)` of [Stacks, Tag 0BLX]**, in
exactly the model in which the sheaf side
`AlgebraicGeometry.RingedSite.isDerivedLimit_derivedGlobalSections_derivedSheafHomSystem` of
`GlobalSectionsKoszulDerivedLimit.lean` leaves it: an inverse system of *cochain complexes* of
`A`-modules indexed by `ℕᵒᵖ`, with no boundedness, no nilpotence and no finiteness hypothesis on
`E`, and with the existence of the reflector discharged rather than assumed.

## Main results

* `CategoryTheory.ObjectProperty.isoOfReflection`: **two reflections into one class of objects
  agree.** Stated for a pair of functors with units satisfying the reflection bijection, rather
  than for a pair of adjunctions, because that is the form the library's two constructions of
  derived completion come in.
* `KoszulCompletion.completionFunctor_isDerivedComplete` and
  `KoszulCompletion.completionUnit_hom_bijective`: the Koszul construction
  `KoszulCompletion.completionFunctor` of `StacksFrontier/Homology/DerivedComplete/AdicKoszulCompletion.lean` *is* a reflection into the
  derived-complete objects. Both were available only as `private` declarations of
  `StacksFrontier/Homology/DerivedComplete/NoetherianCompletePrincipalIdeal.lean`; they are re-proved here from the public inputs
  `koszulPowerCompletion_complete`, `canonicalCompletion_criterion`,
  `canonicalCompletion_map_unit_isIso` and
  `AdicKoszulAdjunction.completion_hom_bijective`, so nothing has to be re-exported.
* `KoszulCompletion.completionFunctorIsoDerivedCompletion`: the Koszul completion and the Čech
  completion of [Stacks, Tag 0G3E] agree.
* `KoszulCompletion.isDerivedLimit_coefficientKoszulTower_derivedCompletion`: **the displayed
  formula.**

## The argument

`KoszulCompletion.coefficientCompletionComplex a` is by definition
`KoszulCoefficientTower.coefficientKoszulTower a ⋙ CountableMilnorTower.countableMilnorFunctor`,
so the Milnor mapping cocone of the tower is the strict completion of `E`. By
`Stacks.Algebraization.PrincipalQuotientTowerCompletion.isDerivedLimit_milnorTriangle_obj₁` that
cocone is a derived limit of the tower — the two spellings `1 - shift` of
`CompletionSequences.complexDifference` and `CountableMilnorTower.oneMinusShift` are the same
`Pi.lift`, so no transport is needed. `KoszulCompletion.completionLocalIso` identifies its image
in `D(A)` with `KoszulCompletion.completionFunctor a` applied to `E`, and
`completionFunctorIsoDerivedCompletion` identifies that with the derived completion. Transporting
the derived limit along the composite is
`CategoryTheory.Pretriangulated.IsDerivedLimit.of_isoObj`.

## What this leaves for the identity of [Stacks, Tag 0BLX]

The isomorphism of functors `ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{u} A) ℤ` that this file used to
name as the one thing missing, namely

`(n ↦ Γ_A(𝒞, SheafHom•_𝒪(K^n, J))) ≅ (coefficientKoszulTower a).obj (Γ_A(𝒞, J))`

for `f_i = ρ (a_i)`, is now proved, unconditionally and for an arbitrary complex `J` of
`𝒪`-modules: it is
`AlgebraicGeometry.RingedSite.globalSectionsKoszulSheafHomComplexSystemIso` of
`KoszulGlobalHomCochain.lean`, with the left-hand tower written as `Γ_A(𝒞, -)` applied to
`AlgebraicGeometry.RingedSite.koszulSheafHomComplexSystem`, and
`AlgebraicGeometry.RingedSite.koszulHomComplexSystemIso` with it written in the Hom-cochain form
of [Stacks, Tag 0A8Z]. Its degreewise half is
`AlgebraicGeometry.RingedSite.koszulHomComplexIso`, twisted by
`AlgebraicGeometry.RingedSite.koszulTwist` `= (-1)^{#S(#S-1)/2}` because
`CochainComplex.HomComplex.δ` and `KoszulCoefficientTower.coefficientKoszulDifferential` differ
by `(-1)^{#S}` on the contraction term; the transitions need no twist.

What remains is to pass from that tower of complexes to the tower in `D(A)` whose derived limit
is `RΓ(𝒞, ℱ^∧)`, which is the single statement
`AlgebraicGeometry.RingedSite.DerivedKoszulHomTowerComparison` of that file. With it,
`CategoryTheory.Pretriangulated.nonempty_iso_of_isDerivedLimit` applied to the formula above and
to the sheaf side finishes the identity.

## References

* [Stacks Project, Tag 0920](https://stacks.math.columbia.edu/tag/0920)
* [Stacks Project, Tag 0G3E](https://stacks.math.columbia.edu/tag/0G3E)
* [Stacks Project, Tag 0BKG](https://stacks.math.columbia.edu/tag/0BKG)
* [Stacks Project, Tag 0BLX](https://stacks.math.columbia.edu/tag/0BLX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe v u

/-! ## Two reflections into one class of objects agree -/

namespace CategoryTheory.ObjectProperty

/-- **Two reflections into one class of objects agree.** If `L` and `L'` both take values in the
class `P` and their units `η`, `η'` both have the reflection property — composing with the unit
is a bijection onto the maps into any object of `P` — then `L.obj X ≅ L'.obj X`.

The isomorphism is the unique map under the unit of `L` carrying `η.app X` to `η'.app X`, and its
inverse is the map in the other direction; both triangles are checked by the injectivity half of
the reflection property. This is the uniqueness of a left adjoint, stated for units rather than
for adjunctions, because the library's two constructions of derived completion come in that
form. -/
def isoOfReflection {C : Type u} [Category.{v} C] (P : ObjectProperty C) {L L' : C ⥤ C}
    (η : 𝟭 C ⟶ L) (η' : 𝟭 C ⟶ L') (hL : ∀ X, P (L.obj X)) (hL' : ∀ X, P (L'.obj X))
    (hη : ∀ X Y, P Y → Function.Bijective fun g : L.obj X ⟶ Y ↦ η.app X ≫ g)
    (hη' : ∀ X Y, P Y → Function.Bijective fun g : L'.obj X ⟶ Y ↦ η'.app X ≫ g)
    (X : C) : L.obj X ≅ L'.obj X where
  hom := ((hη X (L'.obj X) (hL' X)).surjective (η'.app X)).choose
  inv := ((hη' X (L.obj X) (hL X)).surjective (η.app X)).choose
  hom_inv_id := by
    have h1 := ((hη X (L'.obj X) (hL' X)).surjective (η'.app X)).choose_spec
    have h2 := ((hη' X (L.obj X) (hL X)).surjective (η.app X)).choose_spec
    refine (hη X (L.obj X) (hL X)).injective ?_
    rw [← Category.assoc, h1, h2, Category.comp_id]
  inv_hom_id := by
    have h1 := ((hη X (L'.obj X) (hL' X)).surjective (η'.app X)).choose_spec
    have h2 := ((hη' X (L.obj X) (hL X)).surjective (η.app X)).choose_spec
    refine (hη' X (L'.obj X) (hL' X)).injective ?_
    rw [← Category.assoc, h2, h1, Category.comp_id]

end CategoryTheory.ObjectProperty

/-! ## The Koszul completion is the derived completion -/

namespace KoszulCompletion

variable {A : Type u} [CommRing A]

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] derivedCountableProducts

/-- The class of objects of `D(A)` that are derived complete for the ideal generated by `f`. -/
abbrev IsComplete {r : ℕ} (f : Fin r → A) :
    ObjectProperty (DerivedCategory (ModuleCat.{u} A)) :=
  fun K ↦ IsDerivedComplete (Ideal.span (Set.range f)) K

/-- **The Koszul completion of an object of `D(A)` is derived complete.** This is
`koszulPowerCompletion_complete` at the canonical derived tensor product and at the
localization-of-the-strict-construction completion data `KoszulCompletion.completionData`.

The same statement is a `private` declaration of `StacksFrontier/Homology/DerivedComplete/NoetherianCompletePrincipalIdeal.lean`; all of
its inputs are public, so it is re-proved rather than re-exported. -/
theorem completionFunctor_isDerivedComplete {r : ℕ} (f : Fin r → A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    IsDerivedComplete (Ideal.span (Set.range f)) ((completionFunctor f).obj K) :=
  koszulPowerCompletion_complete A f
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A))
    (completionData f
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A))) K

/-- **The universal property of the Koszul completion unit.** Composition with
`KoszulCompletion.completionUnit` is a bijection from the maps out of the completion of `K` to
the maps out of `K`, whenever the target is derived complete.

The two hypotheses of `AdicKoszulAdjunction.completion_hom_bijective` are discharged by
`canonicalCompletion_criterion`, which says that a derived-complete object has an invertible
unit, and by `canonicalCompletion_map_unit_isIso`, which is the idempotence of the
construction. -/
theorem completionUnit_hom_bijective {r : ℕ} (f : Fin r → A)
    (K E : DerivedCategory (ModuleCat.{u} A))
    (hE : IsDerivedComplete (Ideal.span (Set.range f)) E) :
    Function.Bijective
      (fun g : (completionFunctor f).obj K ⟶ E ↦ (completionUnit f).app K ≫ g) := by
  have : IsIso ((completionUnit f).app E) :=
    (canonicalCompletion_criterion f
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A)) E).mp hE
  have : IsIso ((completionFunctor f).map ((completionUnit f).app K)) :=
    canonicalCompletion_map_unit_isIso f
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (ULift.{u} A)) K
  exact AdicKoszulAdjunction.completion_hom_bijective (completionFunctor f) (completionUnit f) K E

/-- **The Koszul completion is the derived completion of [Stacks, Tag 0G3E].** Both are
reflections of `D(A)` into the objects that are derived complete for `Ideal.span (Set.range f)`,
so `CategoryTheory.ObjectProperty.isoOfReflection` identifies them. -/
def completionFunctorIsoDerivedCompletion {r : ℕ} (f : Fin r → A)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    (completionFunctor f).obj K ≅ (DerivedCompletion.derivedCompletionFunctor A f).obj K :=
  ObjectProperty.isoOfReflection (IsComplete f) (completionUnit f)
    (DerivedCompletion.derivedCompletionUnit A f) (completionFunctor_isDerivedComplete f)
    (DerivedCompletion.derivedCompletion_isReflection A f).1
    (completionUnit_hom_bijective f) (DerivedCompletion.derivedCompletion_isReflection A f).2 K

/-- **`E^∧ = R lim_n Hom•_A(Kos(a^{n+1}), E)`: the module side of the identity of
[Stacks, Tag 0BLX].** For a commutative ring `A`, a finite family `f_1, …, f_r ∈ A` and an
arbitrary cochain complex `E` of `A`-modules, the derived completion of `E` along
`Ideal.span (Set.range f)` — the reflector of [Stacks, Tag 0G3E] — is a derived limit in `D(A)`
of the coefficient Koszul tower `KoszulCoefficientTower.coefficientKoszulTower f` of `E`, whose
`n`-th stage is the `A`-linear Hom complex out of the Koszul complex on `f_1^{n+1}, …, f_r^{n+1}`
and whose transitions multiply the factor indexed by `S` by `∏_{i ∈ S} f_i^{m - n}`.

There is no boundedness, nilpotence or finiteness hypothesis, and the reflector is not carried as
an `IsRightAdjoint` hypothesis: it is the named functor
`DerivedCompletion.derivedCompletionFunctor`, whose reflection property is [Stacks, Tag 0G3E].

This carries no `@[stacks 0BLX]` attribute: it is the module half of that tag's identity, and the
identity itself needs in addition the comparison of this tower with the tower of global sections
of the sheaf-level Koszul Hom complexes. -/
theorem isDerivedLimit_coefficientKoszulTower_derivedCompletion {r : ℕ} (f : Fin r → A)
    (E : CochainComplex (ModuleCat.{u} A) ℤ) :
    IsDerivedLimit ((KoszulCoefficientTower.coefficientKoszulTower f).obj E ⋙ DerivedCategory.Q)
      ((DerivedCompletion.derivedCompletionFunctor A f).obj (DerivedCategory.Q.obj E)) :=
  IsDerivedLimit.of_isoObj
    (((completionLocalIso f).app E).symm.trans
      (completionFunctorIsoDerivedCompletion f (DerivedCategory.Q.obj E)))
    (Stacks.Algebraization.PrincipalQuotientTowerCompletion.isDerivedLimit_milnorTriangle_obj₁ A
      ((KoszulCoefficientTower.coefficientKoszulTower f).obj E))

end KoszulCompletion

end
