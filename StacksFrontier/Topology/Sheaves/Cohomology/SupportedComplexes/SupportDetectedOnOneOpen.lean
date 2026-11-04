module

public import StacksFrontier.Homology.DerivedCategory.ShiftSummandApproximation
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ExactFunctorDerivedHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.PushforwardAndRestriction
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness

/-!
# Cohomological support: biproducts, shifts, and detection on one open

Let `(X, 𝒪)` be a space with a sheaf of rings and `T ⊆ X`. An object of `D(𝒪)` is
*cohomologically supported on `T`* when every cohomology sheaf has vanishing stalks off `T`,
which is `Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn`. This file adds three
closure properties of that condition — two of them one-line stalk computations, the third a
three-line appeal to a distinguished triangle — all consumed by the proof of
[Stacks, Tag 08EK].

## Main results

* `Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_biprod`: a biproduct of two
  objects supported on `T` is supported on `T`.
* `Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_shift`: a shift of an object
  supported on `T` is supported on `T`.
* `Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_compl_subset`:
  **support is detected on a single open containing the complement of `T`.** If `Tᶜ ⊆ U` and
  the restriction of `E` to `U` is supported on the preimage of `T`, then `E` is supported
  on `T`.

## Why these three

[Stacks, Tag 08EK] lifts a perfect object `F` of `D(𝒪_U)` supported on `T ∩ U`, for `U` a
quasi-compact open of an affine `X`, to a perfect object of `D(𝒪_X)` supported on `T` whose
restriction is `F ⊕ F[1]`. Taking `W = U ∪ (X ∖ T)`, the subset `T ∩ W` is closed in `W` *and*
contained in the copy of `U` inside `W`, so `F` pushes forward to a perfect object `G` of
`D(𝒪_W)` supported on `T ∩ W` ([Stacks, Tag 08DP]); [Stacks, Tag 08EI] then lifts `G` to a
perfect object `P` of `D(𝒪_X)` with `P|_W ≅ G ⊕ G[1]`.

The support clause of the conclusion is what the three lemmas below supply: `G ⊕ G[1]` is
supported on `T ∩ W` by the first two, and `P` is then supported on `T` by the third, whose
hypothesis `Tᶜ ⊆ W` holds by the construction of `W`. No quasi-compactness and no perfectness
enter; the third lemma is the reason the support clause costs nothing once `W` is chosen this
way, where the source's own proof instead tracks support through an iteration of cones on
multiplication by the equations of `T`.

## Implementation notes

`AlgebraicGeometry.CohomologySupportedOn` of [Stacks, Tag 08DA] and
`Stacks.Cohomology.PushforwardRestriction.CohomologySupportedOn` are character-for-character the
same abbreviation in two namespaces, with the same signature. Being reducible, they cross by
`exact` in both directions, and the biproduct lemma below is proved by a result stated at the
first while itself being stated at the second. So this instance of the parallel-presentations
genus is benign.

`Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iSup_eq_top` is not the third
lemma: a covering of `X` would have to include an open on which the support condition is known,
and here the single open `W` carries it while `X ∖ W ⊆ T` carries nothing. What makes the one-open
statement work is that the condition is stalkwise and only ever tested at points off `T`, all of
which lie in `W`.

The statements are at the `Sheaf (Opens.grothendieckTopology X) RingCat` spelling of the structure
sheaf, with the derived-category model a variable, as the rest of
`Stacks.Cohomology.PushforwardRestriction` is; `AlgebraicGeometry.CohomologySupportedOn` of
[Stacks, Tag 08DA] is the same abbreviation in another namespace, so these apply to it too once
the ring-sheaf spellings agree.

## References

* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
* [Stacks Project, Tag 08DP](https://stacks.math.columbia.edu/tag/08DP)
* [Stacks Project, Tag 08EI](https://stacks.math.columbia.edu/tag/08EI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace ZeroObject
open ExtensionByZeroModules
open Stacks.Cohomology.SupportedComplexes (exactFunctorDerivedHomologyIso)

universe u

namespace Stacks.Cohomology.PushforwardRestriction

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

section Closure

variable [HasDerivedCategory (SheafOfModules.{u} O)]

/-- **A shift of an object supported on `T` is supported on `T`.** The `i`-th cohomology sheaf of
`E⟦n⟧` is the `(i + n)`-th cohomology sheaf of `E`. -/
theorem cohomologySupportedOn_shift (T : Set X) (n : ℤ)
    {E : DerivedCategory (SheafOfModules.{u} O)} (hE : CohomologySupportedOn O T E) :
    CohomologySupportedOn O T (E⟦n⟧) := by
  intro i x hx
  refine (hE (i + n) x hx).of_iso ?_
  exact (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).mapIso ((toAb O).mapIso
    ((DerivedCategory.homologyShiftIsoAdd n i (i + n) rfl).app E))

end Closure

section StandardModel

attribute [local instance] HasDerivedCategory.standard

/-- **A biproduct of two objects supported on `T` is supported on `T`.** The biproduct is the
second vertex of the split distinguished triangle `E ⟶ E ⊞ F ⟶ F ⟶ E⟦1⟧`, and support is a
two-out-of-three property for a distinguished triangle.

Unlike the other two statements in this file this one is at the **standard** derived-category
model, `CategoryTheory.HasDerivedCategory.standard`, because
`AlgebraicGeometry.cohomologySupportedOn_obj₂_of_distinguished` is; that is also the model
[Stacks, Tag 08EI] and `Stacks.DerivedQCoh.SupportedDerivedModules` are stated at, so it is the
model the assembly of [Stacks, Tag 08EK] runs in.

Going through the triangle is what makes this free. The direct route — the stalk of a biproduct
of sheaves of modules is the biproduct of the stalks — needs the composite
`Hⁱ ⋙ toAb ⋙ stalk` to be additive, and `TopCat.Presheaf AddCommGrpCat X` carries neither
`Preadditive` nor the additivity of `ExtensionByZeroModules.toAb` as an instance; supplying both
by `inferInstanceAs` against `(Opens X)ᵒᵖ ⥤ AddCommGrpCat` works for `toAb` but leaves the stalk
functor's additivity still owed. None of that is needed. -/
theorem cohomologySupportedOn_biprod (T : Set X)
    (E F : DerivedCategory (SheafOfModules.{u} O))
    (hE : CohomologySupportedOn O T E) (hF : CohomologySupportedOn O T F) :
    CohomologySupportedOn O T (E ⊞ F) :=
  AlgebraicGeometry.cohomologySupportedOn_obj₂_of_distinguished O T
    (CategoryTheory.Pretriangulated.binaryBiproductTriangle E F)
    (CategoryTheory.Pretriangulated.binaryBiproductTriangle_distinguished E F) hE hF

end StandardModel

/-- **Cohomological support is detected on a single open containing the complement.** If
`Tᶜ ⊆ U` and the restriction of `E` to `U` is supported on the preimage of `T`, then `E` is
supported on `T`.

Unlike `Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iSup_eq_top` this needs
no covering of `X`: the condition is stalkwise and is only ever tested at points off `T`, and
those all lie in `U`, where restriction leaves the stalks of the cohomology sheaves unchanged. -/
theorem cohomologySupportedOn_of_compl_subset [HasDerivedCategory (SheafOfModules.{u} O)]
    (U : Opens X) [HasDerivedCategory (SheafOfModules.{u} (resRing U O))]
    (T : Set X) (hT : Tᶜ ⊆ (U : Set X)) (E : DerivedCategory (SheafOfModules.{u} O))
    (hE : CohomologySupportedOn (resRing U O) (Subtype.val ⁻¹' T)
      ((jStar U O).mapDerivedCategory.obj E)) :
    CohomologySupportedOn O T E := by
  intro i x hx
  have hxU : x ∈ U := hT hx
  set y : Usp U := ⟨x, hxU⟩ with hy
  refine (hE i y hx).of_iso ?_
  exact ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} y).mapIso
      ((toAb (resRing U O)).mapIso
        ((exactFunctorDerivedHomologyIso (jStar U O) i).app E)) ≪≫
    TopCat.Presheaf.stalkRestrictIso U
      (((DerivedCategory.homologyFunctor (SheafOfModules.{u} O) i).obj E).val.presheaf) y).symm

end Stacks.Cohomology.PushforwardRestriction

end
