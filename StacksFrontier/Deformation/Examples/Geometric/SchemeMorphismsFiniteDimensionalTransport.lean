module

public import StacksFrontier.Deformation.Artin.FiniteDimensional.ChangeOfFieldsDescent
public import StacksFrontier.Deformation.Applications.InfinitesimalAutomorphismTransfer

/-!
# Finite dimensionality of `Inf` and `T` of a deformation category, at any point

`Deformation.IsFiniteDimensionalDeformationCategory p` asks the tangent space
`tangentSpaceArtinian` of the deformation category `p` and its infinitesimal automorphisms at
*every* point over the residue-field object `residueFieldObject Λ k` (with carrier `ULift k`), at
every choice of pushforwards, to be finite dimensional. The geometric examples are built over a
different spelling of the residue field, `Deformation.Examples.residueFieldBase` (carrier `k`),
and the natural data — the trivial deformation and its chosen pushforwards — live there.

This file transports finite dimensionality between such points. The input is the canonical
`k`-linear identification of [Stacks Project, Tag 06JV] (2)
(`Deformation.canonicalLocalizedTangentAutomorphismLinearEquiv`), which compares the tangent
spaces at the identity of the automorphism functors at the two ends of any arrow whose target
lies over the residue-field object, and the existence of such arrows: in a predeformation
category every object over a field isomorphic to `k` has an arrow to every object over `k`
(pushforward along the isomorphism, then the unique isomorphism of the special fibre).

## Main results

* `Deformation.nonempty_hom_of_hom_residueFieldObject`: the arrows into the special fibre.
* `Deformation.finiteDimensional_localizedAutomorphismFunctorTangent_of_isFiniteDimensional`:
  condition (4) gives finite dimensionality of the infinitesimal automorphisms at any point with
  an arrow to the residue-field object.
* `Deformation.isFiniteDimensionalDeformationCategory_of_localized_of_tangentModuleAt`: and
  conversely, condition (4) follows from finite dimensionality of the tangent module at
  `ULift k` and of the infinitesimal automorphisms at one such point.
* `Deformation.finiteDimensional_tangentModuleAt_of_isFiniteDimensional`: condition (4) gives
  finite dimensionality of the tangent module at `ULift k`.

## References

* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 07W6](https://stacks.math.columbia.edu/tag/07W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Deformation

universe u w u₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{w} F] {p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k}

/-- Pushing `x` forward along a map to the residue-field object gives an arrow to an object over
the residue-field object. -/
private theorem exists_hom_of_hom_residueFieldObject (hp : IsPredeformationCategory p) {x : F}
    (g : p.obj x ⟶ residueFieldObject.{u, w, w} Λ k) :
    ∃ (y : F) (_ : x ⟶ y), p.obj y = residueFieldObject.{u, w, w} Λ k := by
  obtain ⟨y, ψ, hψ⟩ := exists_pushforward hp.cofibered g x rfl
  exact ⟨y, ψ, IsHomLift.codomain_eq p g ψ⟩

/-- **Arrows into the special fibre.** In a predeformation category, an object `x` lying over an
object of `𝒞_Λ` with a map to the residue-field object `k` has an arrow to every object `y` over
`k`: push `x` forward along that map, then compose with the unique isomorphism of the special
fibre. -/
theorem nonempty_hom_of_hom_residueFieldObject (hp : IsPredeformationCategory p) {x : F}
    (g : p.obj x ⟶ residueFieldObject.{u, w, w} Λ k) (y : F)
    (hy : p.obj y = residueFieldObject.{u, w, w} Λ k) : Nonempty (x ⟶ y) := by
  obtain ⟨y', ψ, hy'⟩ := exists_hom_of_hom_residueFieldObject hp g
  obtain ⟨i, -⟩ := existsUnique_pointIso hp ⟨y', hy'⟩ ⟨y, hy⟩
  exact ⟨ψ ≫ i.hom.1⟩

/-- **Finite dimensionality of the infinitesimal automorphisms spreads from one point to all
points over the residue field.** If the tangent space at the identity of the automorphism
functor is finite dimensional at one point `x` with an arrow `p x → k`, then it is at every point
over `k` and every choice of pushforwards there ([Stacks Project, Tag 06JV] (2)). -/
theorem finiteDimensional_localizedAutomorphismFunctorTangent_of_hom_residueFieldObject
    (hp : IsDeformationCategory p) {x : F} (g : p.obj x ⟶ residueFieldObject.{u, w, w} Λ k)
    (P : ChosenPushforwardsAt p x)
    (hfin :
      letI := naturalLocalizedTangentAddCommGroup P hp.satisfiesRS
      letI := naturalLocalizedTangentModule P hp.satisfiesRS
      FiniteDimensional k (localizedAutomorphismFunctorTangent P))
    (y : F) (hy : p.obj y = residueFieldObject.{u, w, w} Λ k) (Q : ChosenPushforwardsAt p y) :
    letI := naturalLocalizedTangentAddCommGroup Q hp.satisfiesRS
    letI := naturalLocalizedTangentModule Q hp.satisfiesRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent Q) := by
  let := naturalLocalizedTangentAddCommGroup P hp.satisfiesRS
  let := naturalLocalizedTangentModule P hp.satisfiesRS
  let := naturalLocalizedTangentAddCommGroup Q hp.satisfiesRS
  let := naturalLocalizedTangentModule Q hp.satisfiesRS
  obtain ⟨j⟩ := nonempty_hom_of_hom_residueFieldObject hp.predeformation g y hy
  have := hfin
  exact Module.Finite.equiv
    (canonicalLocalizedTangentAutomorphismLinearEquiv hp.satisfiesRS j hy P Q)

/-- **Condition (4) gives finite dimensionality of the infinitesimal automorphisms at any point
with an arrow to the residue-field object**, at every choice of pushforwards there: push the
point forward to the special fibre, where condition (4) applies, and compare the two tangent
spaces at the identity by [Stacks Project, Tag 06JV] (2). -/
theorem finiteDimensional_localizedAutomorphismFunctorTangent_of_isFiniteDimensional
    (h : IsFiniteDimensionalDeformationCategory p) (hRS : SatisfiesRS p) {x : F}
    (g : p.obj x ⟶ residueFieldObject.{u, w, w} Λ k) (P : ChosenPushforwardsAt p x) :
    letI := naturalLocalizedTangentAddCommGroup P hRS
    letI := naturalLocalizedTangentModule P hRS
    FiniteDimensional k (localizedAutomorphismFunctorTangent P) := by
  obtain ⟨hp, -, hinf⟩ := h
  obtain ⟨y, ψ, hy⟩ := exists_hom_of_hom_residueFieldObject hp.predeformation g
  let Q := chosenPushforwardsAt hp.predeformation.cofibered y
  let := naturalLocalizedTangentAddCommGroup P hRS
  let := naturalLocalizedTangentModule P hRS
  let := naturalLocalizedTangentAddCommGroup Q hRS
  let := naturalLocalizedTangentModule Q hRS
  have := hinf y hy Q
  have : FiniteDimensional k (localizedAutomorphismFunctorTangent Q) :=
    Module.Finite.equiv (tangentCarrierLinearEquiv Q hRS)
  exact Module.Finite.equiv
    (canonicalLocalizedTangentAutomorphismLinearEquiv hRS ψ hy P Q).symm

/-- **Condition (4) gives finite dimensionality of the tangent module at `ULift k`**: that module
is `tangentSpaceArtinian` up to the canonical identification. -/
theorem finiteDimensional_tangentModuleAt_of_isFiniteDimensional
    (h : IsFiniteDimensionalDeformationCategory p) (hp : IsDeformationCategory p) :
    FiniteDimensional k ↥(tangentModuleAt.{u, w, w} (BasedCategory.ofFunctor p) hp
      (FGModuleCat.of k (ULift.{w} k))) := by
  obtain ⟨hp', htan, -⟩ := h
  dsimp only at htan
  let : Fact (IsPredeformationCategory (BasedCategory.ofFunctor p).p) := ⟨hp.predeformation⟩
  let : Fact (SchlessingerConditionS2 (CategoryOfElements.π
    (isomorphismClasses (BasedCategory.ofFunctor p) hp.predeformation.cofibered))) :=
    ⟨tangentConditionS2.{u, w, w} hp⟩
  have := htan
  exact (associatedTangentSpaceCarrierLinearEquiv.{u, w, w} (BasedCategory.ofFunctor p)
    hp.predeformation (tangentConditionS2.{u, w, w} hp)).symm.finiteDimensional

/-- **Condition (4) from one point.** A deformation category whose tangent module at `ULift k`
is finite dimensional, and whose infinitesimal automorphisms are finite dimensional at one point
`x` with an arrow `p x → k`, satisfies condition (4): its tangent space and its infinitesimal
automorphisms at every point over `k` are finite dimensional. -/
theorem isFiniteDimensionalDeformationCategory_of_localized_of_tangentModuleAt
    (hp : IsDeformationCategory p) {x : F} (g : p.obj x ⟶ residueFieldObject.{u, w, w} Λ k)
    (P : ChosenPushforwardsAt p x)
    (hinf :
      letI := naturalLocalizedTangentAddCommGroup P hp.satisfiesRS
      letI := naturalLocalizedTangentModule P hp.satisfiesRS
      FiniteDimensional k (localizedAutomorphismFunctorTangent P))
    (htan : FiniteDimensional k ↥(tangentModuleAt.{u, w, w} (BasedCategory.ofFunctor p) hp
      (FGModuleCat.of k (ULift.{w} k)))) :
    IsFiniteDimensionalDeformationCategory p := by
  refine ⟨hp, finiteDimensional_tangentSpaceArtinian_of_tangentModuleAt hp htan, ?_⟩
  intro y hy Q
  have := finiteDimensional_localizedAutomorphismFunctorTangent_of_hom_residueFieldObject hp g P
    hinf y hy Q
  exact finiteDimensional_infinitesimalAutomorphismLinearLift_of_localized hp.satisfiesRS Q this

end Deformation

end
