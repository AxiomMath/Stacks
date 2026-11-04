module

public import StacksFrontier.AlgebraicGeometry.DerivedCoherent.Modules
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.RegularBoundedCoherentPerfect
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory
public import StacksCore.Tactic.StacksAttribute

/-!
# Sibling functors between bounded coherent derived categories of schemes

Let `X` and `Y` be schemes. Two exact functors `D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)` are *siblings* if
they are siblings in the sense of [Stacks, Tag 0FZT] for the abelian category `Coh(𝒪_X)`, read
through the identification `D^b(Coh(𝒪_X)) = D^b_Coh(𝒪_X)` of [Stacks, Tag 0FDB]. Since the
relation of [Stacks, Tag 0FZT] is a relation between exact functors out of the bounded derived
category of an abelian category, and `D^b_Coh(𝒪_X)` is not that category but the full subcategory
of `D(𝒪_X)` identified with it, the definition is the restriction of the two functors along the
comparison functor `D^b(Coh(𝒪_X)) ⥤ D^b_Coh(𝒪_X)` of [Stacks, Tag 0FDB]. This is
[Stacks, Tag 0FZZ].

On a regular scheme the perfect objects of `D(𝒪_X)` are exactly the objects of `D^b_Coh(𝒪_X)`, by
[Stacks, Tag 0FDC], and the tag applies the same terminology to exact functors
`D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`. That reading is `AlgebraicGeometry.AreSiblingsPerfect`, obtained by
transporting such a pair of functors along the two inclusions coming from that identification.

## Main definitions

* `AlgebraicGeometry.boundedCoherentSingleFunctor`: the inclusion `Coh(𝒪_X) ⥤ D^b_Coh(𝒪_X)` of the
  coherent modules placed in degree zero.
* `AlgebraicGeometry.AreSiblingsCoherent`: **[Stacks, Tag 0FZZ]**, the relation of being sibling
  exact functors `D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)`.
* `AlgebraicGeometry.perfectInModules`: perfectness, read as a property of objects of `D(𝒪_X)` in
  the spelling of `Mod(𝒪_X)` used by [Stacks, Tag 0FDB]; the full subcategory it cuts out is
  `D_perf(𝒪_X)`.
* `AlgebraicGeometry.AreSiblingsPerfect`: **[Stacks, Tag 0FZZ], the regular case**, the same
  relation for exact functors `D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` on quasi-compact regular schemes.

## Main results

* `AlgebraicGeometry.AreSiblingsCoherent.restrictionIso` and
  `AlgebraicGeometry.AreSiblingsCoherent.objIso`: the two conditions of [Stacks, Tag 0FZT], read
  on the coherent modules and on all of `D^b_Coh(𝒪_X)`.
* `AlgebraicGeometry.areSiblingsCoherent_of` and `AlgebraicGeometry.areSiblingsCoherent_iff`: the
  same two conditions suffice, so on a Noetherian scheme being siblings is exactly having
  naturally isomorphic restrictions to `Coh(𝒪_X)` and isomorphic values at every object of
  `D^b_Coh(𝒪_X)`.
* `AlgebraicGeometry.perfectInModules_eq_derivedCategoryBBounded`: **[Stacks, Tag 0FDC]** as an
  equality of properties of objects of `D(𝒪_X)`, which is what identifies `D_perf(𝒪_X)` with
  `D^b_Coh(𝒪_X)` for a quasi-compact regular scheme.
* `CategoryTheory.ObjectProperty.isTriangulated_ιOfLE`: the inclusion of a triangulated
  subcategory into a larger one is exact.
* `AlgebraicGeometry.isTriangulated_coherentToModulesDerivedBounded`: the comparison functor of
  [Stacks, Tag 0FDB] is exact.

## Implementation notes

*The spellings.* `Coh(𝒪_X)` is `AlgebraicGeometry.SheafOfModules.CoherentModules X.ringCatSheaf`,
`D^b(Coh(𝒪_X))` is its bounded derived category, and `D^b_Coh(𝒪_X)` is the full subcategory of
`D(𝒪_X)` cut out by `AlgebraicGeometry.coherentInModules`, exactly as in the file proving
[Stacks, Tag 0FDB], whose local instance `CategoryTheory.HasDerivedCategory.standard` is
installed here too so that the two readings of the derived categories agree syntactically.

*The exactness of the comparison functor.* [Stacks, Tag 0FDB] is formalized as the functor
`AlgebraicGeometry.coherentToModulesDerivedBounded` together with the statement that it is an
equivalence on a Noetherian scheme. Composing it with the two functors of the definition requires
knowing that it is exact, which is not recorded there; it is proved here from the identity
`AlgebraicGeometry.coherentToModulesDerivedBounded_comp_ι`, which exhibits the comparison functor
followed by the fully faithful inclusion of `D^b_Coh(𝒪_X)` as the derived functor of the exact
inclusion `Coh(𝒪_X) ⥤ Mod(𝒪_X)` restricted to the bounded complexes.

*The hypotheses of the source that are not assumed.* The source states the definition for `X` and
`Y` of finite type over a field `k` and for `k`-linear exact functors. The sibling condition of
[Stacks, Tag 0FZT] refers only to the exact structure of the two functors, so neither the base
field nor `k`-linearity enters its expression, and neither is assumed here; the definition applies
verbatim to the source's situation. Noetherianity is likewise not needed to state the condition.
It is what makes the comparison functor of [Stacks, Tag 0FDB] an equivalence, hence what makes
restricting along it lose nothing, and it is assumed exactly where that is used:
`AlgebraicGeometry.AreSiblingsCoherent.objIso` and `AlgebraicGeometry.areSiblingsCoherent_iff`. A
scheme of finite type over a field is Noetherian, so it is in force in the source's situation.

*The regular case.* [Stacks, Tag 0FDC] is available as the pointwise equivalence
`Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_iff_isBoundedCoherent_of_isRegular`, for a
regular scheme with `CompactSpace`; `AlgebraicGeometry.perfectInModules_eq_derivedCategoryBBounded`
turns it into an equality of properties of objects, and the two functors
`CategoryTheory.ObjectProperty.ιOfLE` it produces move a pair of exact functors
`D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)` to a pair `D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)`. Those inclusions are exact
by `CategoryTheory.ObjectProperty.isTriangulated_ιOfLE`, proved here in general.

## References

* [Stacks Project, Tag 0FZZ](https://stacks.math.columbia.edu/tag/0FZZ)
* [Stacks Project, Tag 0FZT](https://stacks.math.columbia.edu/tag/0FZT)
* [Stacks Project, Tag 0FDB](https://stacks.math.columbia.edu/tag/0FDB)
* [Stacks Project, Tag 0FDC](https://stacks.math.columbia.edu/tag/0FDC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  {P Q : ObjectProperty C} [P.IsTriangulated] [Q.IsTriangulated]

/-- The inclusion of a triangulated subcategory into a larger one commutes with the shift: it
does so after composition with the fully faithful inclusion of the larger subcategory, where it
becomes the inclusion of the smaller one. -/
noncomputable instance commShift_ιOfLE (h : P ≤ Q) : (ιOfLE h).CommShift ℤ :=
  Functor.CommShift.ofComp (ιOfLECompιIso h) ℤ

/-- The identification of the inclusion of a triangulated subcategory into a larger one, followed
by the inclusion of that larger one, with the inclusion of the smaller one is compatible with the
shift. -/
instance natTransCommShift_ιOfLECompιIso (h : P ≤ Q) :
    NatTrans.CommShift (ιOfLECompιIso h).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

/-- The inclusion of a triangulated subcategory into a larger one is exact: a triangle of the
smaller subcategory is distinguished exactly when its image in the ambient category is, and that
image is unchanged by the inclusion. -/
instance isTriangulated_ιOfLE (h : P ≤ Q) : (ιOfLE h).IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (ιOfLECompιIso h)).2 inferInstance

end CategoryTheory.ObjectProperty

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

section Comparison

variable (X : Scheme.{u})

/-- The comparison functor `D^b(Coh(𝒪_X)) ⥤ D^b_Coh(𝒪_X)` of [Stacks, Tag 0FDB], followed by the
inclusion of `D^b_Coh(𝒪_X)` into `D(𝒪_X)`, is the derived functor of the inclusion
`Coh(𝒪_X) ⥤ Mod(𝒪_X)` restricted to the bounded complexes: the isomorphism form of
`AlgebraicGeometry.coherentToModulesDerivedBounded_comp_ι`. -/
def coherentToModulesDerivedBoundedCompιIso :
    coherentToModulesDerivedBounded X ⋙
        (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).ι ≅
      DerivedCategory.Bounded.ι ⋙ (coherentInModules X).ι.mapDerivedCategory :=
  eqToIso (coherentToModulesDerivedBounded_comp_ι X)

/-- The comparison functor of [Stacks, Tag 0FDB] commutes with the shift, because it does so
after composition with the fully faithful inclusion of `D^b_Coh(𝒪_X)` into `D(𝒪_X)`. -/
noncomputable instance commShift_coherentToModulesDerivedBounded :
    (coherentToModulesDerivedBounded X).CommShift ℤ :=
  Functor.CommShift.ofComp (coherentToModulesDerivedBoundedCompιIso X) ℤ

/-- The identification of the comparison functor of [Stacks, Tag 0FDB], followed by the inclusion
of `D^b_Coh(𝒪_X)`, with the derived functor of `Coh(𝒪_X) ⥤ Mod(𝒪_X)` is compatible with the
shift. -/
instance natTransCommShift_coherentToModulesDerivedBoundedCompιIso :
    NatTrans.CommShift (coherentToModulesDerivedBoundedCompιIso X).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

/-- **The comparison functor of [Stacks, Tag 0FDB] is exact.** Composed with the fully faithful
inclusion of `D^b_Coh(𝒪_X)` into `D(𝒪_X)` it is the derived functor of an exact functor,
restricted to the bounded complexes, and a functor into a triangulated subcategory is exact as
soon as it is after composition with the inclusion of that subcategory. -/
instance isTriangulated_coherentToModulesDerivedBounded :
    (coherentToModulesDerivedBounded X).IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right (coherentToModulesDerivedBoundedCompιIso X)).2
    inferInstance

/-- The inclusion of the coherent `𝒪_X`-modules into `D^b_Coh(𝒪_X)`, sending a coherent module to
the complex concentrated in degree zero: the degree-zero inclusion
`Coh(𝒪_X) ⥤ D^b(Coh(𝒪_X))` of `AlgebraicGeometry.boundedSingleFunctor` followed by the comparison
functor of [Stacks, Tag 0FDB]. -/
def boundedCoherentSingleFunctor :
    SheafOfModules.CoherentModules X.ringCatSheaf ⥤
      (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).FullSubcategory :=
  boundedSingleFunctor _ ⋙ coherentToModulesDerivedBounded X

end Comparison

section Siblings

variable {X Y : Scheme.{u}}
  (F F' : (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).FullSubcategory ⥤
    (DerivedCategoryB.derivedCategoryBBounded (coherentInModules Y)).FullSubcategory)
  [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]

/-- **Stacks Project, Tag 0FZZ.** Two exact functors `D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)` are
**siblings**, or `F'` is a **sibling** of `F`, if they are siblings in the sense of
[Stacks, Tag 0FZT] for the abelian category `Coh(𝒪_X)`: their restrictions along the comparison
functor `D^b(Coh(𝒪_X)) ⥤ D^b_Coh(𝒪_X)` of the identification `D^b_Coh(𝒪_X) = D^b(Coh(𝒪_X))` of
[Stacks, Tag 0FDB] are siblings, that is, they agree up to natural isomorphism on the coherent
modules and up to isomorphism at each object. -/
@[stacks 0FZZ "siblings of exact functors between the bounded coherent derived categories"]
def AreSiblingsCoherent : Prop :=
  AreSiblings (coherentToModulesDerivedBounded X ⋙ F) (coherentToModulesDerivedBounded X ⋙ F')

/-- The restrictions of two sibling exact functors `D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)` to the coherent
modules are naturally isomorphic. -/
theorem AreSiblingsCoherent.restrictionIso (h : AreSiblingsCoherent F F') :
    Nonempty (boundedCoherentSingleFunctor X ⋙ F ≅ boundedCoherentSingleFunctor X ⋙ F') :=
  AreSiblings.restrictionIso h

/-- **The values of two sibling exact functors are isomorphic at every object of
`D^b_Coh(𝒪_X)`.** The definition asks for this only at the objects coming from
`D^b(Coh(𝒪_X))`; on a Noetherian scheme the comparison functor of [Stacks, Tag 0FDB] is an
equivalence, in particular essentially surjective, so every object is such an object up to
isomorphism. -/
theorem AreSiblingsCoherent.objIso [IsNoetherian X] (h : AreSiblingsCoherent F F')
    (K : (DerivedCategoryB.derivedCategoryBBounded (coherentInModules X)).FullSubcategory) :
    Nonempty (F.obj K ≅ F'.obj K) := by
  obtain ⟨e⟩ := AreSiblings.objIso h ((coherentToModulesDerivedBounded X).objPreimage K)
  exact ⟨(F.mapIso ((coherentToModulesDerivedBounded X).objObjPreimageIso K)).symm ≪≫ e ≪≫
    F'.mapIso ((coherentToModulesDerivedBounded X).objObjPreimageIso K)⟩

/-- **Two exact functors `D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)` are siblings as soon as their
restrictions to the coherent modules are naturally isomorphic and their values at every object
are isomorphic.** No Noetherian hypothesis is needed in this direction: the objects of
`D^b_Coh(𝒪_X)` coming from `D^b(Coh(𝒪_X))` are among the objects of `D^b_Coh(𝒪_X)`. -/
theorem areSiblingsCoherent_of
    (h₁ : Nonempty (boundedCoherentSingleFunctor X ⋙ F ≅ boundedCoherentSingleFunctor X ⋙ F'))
    (h₂ : ∀ K, Nonempty (F.obj K ≅ F'.obj K)) :
    AreSiblingsCoherent F F' where
  restrictionIso := h₁
  objIso _ := h₂ _

/-- **Being siblings, spelled out on a Noetherian scheme**: two exact functors
`D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)` are siblings exactly when their restrictions to the coherent
modules are naturally isomorphic and their values at every object of `D^b_Coh(𝒪_X)` are
isomorphic. -/
theorem areSiblingsCoherent_iff [IsNoetherian X] :
    AreSiblingsCoherent F F' ↔
      Nonempty (boundedCoherentSingleFunctor X ⋙ F ≅ boundedCoherentSingleFunctor X ⋙ F') ∧
        ∀ K, Nonempty (F.obj K ≅ F'.obj K) :=
  ⟨fun h => ⟨h.restrictionIso, h.objIso⟩, fun h => areSiblingsCoherent_of F F' h.1 h.2⟩

end Siblings

section Perfect

/-- Perfectness, read as a property of objects of `D(𝒪_X)` in the spelling
`Mod(𝒪_X) = SheafOfModules X.ringCatSheaf` of [Stacks, Tag 0FDB]. The full subcategory it cuts
out is `D_perf(𝒪_X)`. -/
abbrev perfectInModules (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :=
  Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)

/-- **The perfect objects form a triangulated subcategory of `D(𝒪_X)`**, in the spelling
`AlgebraicGeometry.perfectInModules`: the instance of
`Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect`, restated at the
abbreviation, which instance search does not see through. Everything the triangulated structure
of `D_perf(𝒪_X)` needs is found from this. -/
instance isTriangulated_perfectInModules (X : Scheme.{u}) :
    (perfectInModules X).IsTriangulated :=
  inferInstanceAs (ObjectProperty.IsTriangulated
    (Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) :
      ObjectProperty (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))))

/-- **[Stacks, Tag 0FDC] as an equality of properties of objects of `D(𝒪_X)`.** On a quasi-compact
regular scheme the perfect objects are exactly the objects which are bounded with coherent
cohomology, so `D_perf(𝒪_X)` and `D^b_Coh(𝒪_X)` are cut out by the same property. -/
theorem perfectInModules_eq_derivedCategoryBBounded (X : Scheme.{u}) (hX : IsRegular X)
    [CompactSpace X] :
    perfectInModules X = DerivedCategoryB.derivedCategoryBBounded (coherentInModules X) := by
  funext K
  exact propext
    (Stacks.AlgebraicGeometry.PerfectCohomology.isPerfect_iff_isBoundedCoherent_of_isRegular
      hX K)

variable {X Y : Scheme.{u}} (hX : IsRegular X) (hY : IsRegular Y) [CompactSpace X]
  [CompactSpace Y]
  (F F' : (perfectInModules X).FullSubcategory ⥤ (perfectInModules Y).FullSubcategory)
  [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]

/-- **Stacks Project, Tag 0FZZ, the regular case.** On quasi-compact regular schemes
`D_perf(𝒪_X) = D^b_Coh(𝒪_X)` by [Stacks, Tag 0FDC], and the same terminology is used for exact
functors `D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`: two of them are **siblings** if they are siblings as exact
functors `D^b_Coh(𝒪_X) ⥤ D^b_Coh(𝒪_Y)` after being moved there along that identification, which
on each of the two schemes is the inclusion of one of the two subcategories into the other. -/
@[stacks 0FZZ "the regular case: siblings of exact functors between the perfect derived \
categories of quasi-compact regular schemes"]
def AreSiblingsPerfect : Prop :=
  AreSiblingsCoherent
    (ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge ⋙ F ⋙
      ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded Y hY).le)
    (ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded X hX).ge ⋙ F' ⋙
      ObjectProperty.ιOfLE (perfectInModules_eq_derivedCategoryBBounded Y hY).le)

end Perfect

end AlgebraicGeometry

end
