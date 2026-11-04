module

public import StacksFrontier.AlgebraicGeometry.FullyFaithful.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.Basic

/-!
# Base change near finitely many closed points is faithful

Let `D` be a `FinitePresentationAwayPointsSituation`: a scheme `S` with finitely many pairwise
distinct closed points `s i` whose open complement `U` is quasi-compact. Base change to the
spectra of the local rings `S_i = Spec 𝒪_{S, s i}` is the functor
`AlgebraicGeometry.finitePresentationAwayPointsBaseChange` of [Stacks, Tag 0BFU], from the
category of finitely presented morphisms to `S` that are isomorphisms over `U` to the product
of the corresponding local categories.

[Stacks, Tag 0BFV] asserts that this functor is an equivalence, and that is proved in
`BaseChangeEquivalence.lean`, which carries the tag. This file proves the **faithfulness**
constituent on its own, from nothing beyond fpqc descent for the covering family consisting of
`U ⟶ S` together with the morphisms `S_i ⟶ S`.

## Main results

* `AlgebraicGeometry.BaseChangeFunctor.faithful`: any functor carrying the canonical
  identifications with base change to the spectra of the local rings — in particular the one of
  [Stacks, Tag 0BFU] — is faithful.
* `AlgebraicGeometry.finitePresentationAwayPointsBaseChange_faithful`: the base-change functor
  of [Stacks, Tag 0BFU] is faithful.

## Implementation notes

The descent statement used is `AlgebraicGeometry.LocalSchemesCover.over_hom_ext_of_baseChange`:
a morphism of schemes over `S` is determined by its base changes to the open complement and to
the local schemes at the distinguished points. Of the two kinds of component it asks for, only
the local ones carry information here. The component over the open complement is free: an object
of the source category restricts over `U` to an isomorphism, hence to a terminal object of the
over-category of `U`, so any two morphisms into it already agree.

The index type of `AlgebraicGeometry.LocalSchemesCover` lives in the universe of the scheme,
while a `FinitePresentationAwayPointsSituation` indexes its points by `Fin n`; the family of
points is therefore transported along `ULift` before the descent statement is applied, and the
resulting open complement is identified with the one of the situation.

The local components are read off from the structure field
`AlgebraicGeometry.BaseChangeFunctor.pullbackIso`, whose naturality square turns an equality of
images under the functor into an equality of base changes along `S_i ⟶ S`. This is why the
result is about the canonical base-change functor rather than about some functor of the same
type.

## References

* [Stacks Project, Tag 0BFV](https://stacks.math.columbia.edu/tag/0BFV)
* [Stacks Project, Tag 0BFU](https://stacks.math.columbia.edu/tag/0BFU)
* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe v u

namespace AlgebraicGeometry

/-- An object of an over-category whose structure morphism is invertible is terminal, so any two
morphisms into it agree. -/
private theorem over_hom_ext_of_isIso_hom {C : Type u} [Category.{v} C] {T : C} {X Y : Over T}
    (hY : IsIso Y.hom) (f g : X ⟶ Y) : f = g := by
  have : IsIso Y.hom := hY
  exact CostructuredArrow.hom_ext _ _ ((cancel_mono Y.hom).mp (by rw [Over.w f, Over.w g]))

namespace FinitePresentationAwayPointsSituation

variable (D : FinitePresentationAwayPointsSituation.{u})

/-- The index type of the distinguished points, lifted to the universe of the scheme. -/
private abbrev Index := ULift.{u} (Fin D.n)

/-- The distinguished points, reindexed by a type in the universe of the scheme. -/
private def indexedPoints : D.Index → D.S := fun i ↦ D.points i.down

/-- The reindexed family of distinguished points consists of closed points. -/
private theorem indexedPoints_mem_closedPoints :
    ∀ i : D.Index, D.indexedPoints i ∈ closedPoints D.S :=
  fun i ↦ mem_closedPoints_iff.mpr (D.points_closed i.down)

/-- The open complement formed from the reindexed family is the open complement of the
situation. -/
private theorem complementOfClosedPoints_indexedPoints :
    complementOfClosedPoints D.indexedPoints D.indexedPoints_mem_closedPoints = D.complement := by
  ext x
  show x ∈ (⋂ i : D.Index, ({D.points i.down} : Set D.S)ᶜ) ↔ x ∈ (Set.range D.points)ᶜ
  simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_range]
  exact ⟨fun h ⟨i, hi⟩ ↦ h ⟨i⟩ hi.symm, fun h i hi ↦ h ⟨i.down, hi.symm⟩⟩

/-- The open complement formed from the reindexed family has quasi-compact inclusion. -/
private theorem quasiCompact_complementOfClosedPoints_indexedPoints :
    QuasiCompact
      (complementOfClosedPoints D.indexedPoints D.indexedPoints_mem_closedPoints).ι := by
  have : QuasiCompact D.complement.ι := D.complement_quasiCompact
  rw [← Scheme.isoOfEq_hom_ι D.S D.complementOfClosedPoints_indexedPoints]
  infer_instance

end FinitePresentationAwayPointsSituation

/-- The faithfulness constituent of the equivalence of [Stacks, Tag 0BFV]. Any functor
carrying the canonical identifications with base change to the spectra of the local rings — in
particular the one of [Stacks, Tag 0BFU] — is faithful.

A morphism of the source category is determined by its base changes to the open complement and
to the spectra of the local rings, by fpqc descent for the covering family of
`AlgebraicGeometry.LocalSchemesCover.presieve₀_mem_fpqcPrecoverage`. The base change to the open
complement carries no information, because the target restricts there to an isomorphism; the
base changes to the local schemes are the components of the image of the morphism.

The other two constituents, fullness and essential surjectivity, are proved in
`BaseChangeEquivalence.lean`, so the equivalence Tag 0BFV asserts is available in full there and
the tag is carried by `AlgebraicGeometry.finitePresentationAwayPointsBaseChange_isEquivalence`:
essential surjectivity is deduced from [Stacks, Tag 0B3X], and full faithfulness, whose proof the
source of Tag 0BFV omits, from the full faithfulness of the canonical restriction functor of
[Stacks, Tag 0E8Q]. -/
theorem BaseChangeFunctor.faithful {D : FinitePresentationAwayPointsSituation.{u}}
    (B : BaseChangeFunctor D) : B.functor.Faithful where
  map_injective := by
    intro X Y f₁ f₂ h
    refine (ObjectProperty.ι (IsFinitePresentationAway D.complement)).map_injective
      (LocalSchemesCover.over_hom_ext_of_baseChange D.indexedPoints
        D.indexedPoints_mem_closedPoints
        D.quasiCompact_complementOfClosedPoints_indexedPoints _ _ ?_)
    rintro (_ | i)
    · -- Over the open complement the target is terminal, so the two base changes agree.
      have key : ∀ (V : D.S.Opens), V = D.complement →
          ∀ g₁ g₂ : (ObjectProperty.ι (IsFinitePresentationAway D.complement)).obj X ⟶
            (ObjectProperty.ι (IsFinitePresentationAway D.complement)).obj Y,
            (Over.pullback V.ι).map g₁ = (Over.pullback V.ι).map g₂ := by
        intro V hV g₁ g₂
        subst hV
        exact over_hom_ext_of_isIso_hom Y.property.2 _ _
      exact key _ D.complementOfClosedPoints_indexedPoints _ _
    · -- Over the `i`th local scheme the base change is the `i`th component of the image.
      show (ObjectProperty.ι (IsFinitePresentationAway D.complement) ⋙
          Over.pullback (D.S.fromSpecStalk (D.points i.down))).map f₁ =
        (ObjectProperty.ι (IsFinitePresentationAway D.complement) ⋙
          Over.pullback (D.S.fromSpecStalk (D.points i.down))).map f₂
      have hcomp : (B.functor ⋙ Pi.eval (fun i ↦ D.localCategory i) i.down ⋙
            ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i.down))).map f₁ =
          (B.functor ⋙ Pi.eval (fun i ↦ D.localCategory i) i.down ⋙
            ObjectProperty.ι (IsFinitePresentationAway
              (D.puncturedLocalScheme i.down))).map f₂ :=
        congrArg (fun m ↦ (ObjectProperty.ι (IsFinitePresentationAway
          (D.puncturedLocalScheme i.down))).map m) (congrFun h i.down)
      refine (cancel_epi ((B.pullbackIso i.down).hom.app X)).mp ?_
      rw [← (B.pullbackIso i.down).hom.naturality f₁,
        ← (B.pullbackIso i.down).hom.naturality f₂, hcomp]

/-- The faithfulness constituent of the equivalence of [Stacks, Tag 0BFV]. Base change from
finitely presented modifications supported at finitely many closed points to the corresponding
local modifications is faithful.

The equivalence itself, which carries the tag, is
`AlgebraicGeometry.finitePresentationAwayPointsBaseChange_isEquivalence`. -/
@[stacks 0BFV "faithful"]
theorem finitePresentationAwayPointsBaseChange_faithful
    (D : FinitePresentationAwayPointsSituation.{u}) :
    (finitePresentationAwayPointsBaseChange D).functor.Faithful :=
  (finitePresentationAwayPointsBaseChange D).faithful

end AlgebraicGeometry

end
