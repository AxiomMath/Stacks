module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Pi.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationPoint
public import StacksCore.Tactic.StacksAttribute

/-!
# Base change near finitely many closed points

Let `S` be a scheme and let `s i` be finitely many distinct closed points whose open complement
is quasi-compact. This file defines the categories of finitely presented morphisms which are
isomorphisms away from those points, and records the canonical functor obtained by base change
to the spectra of the local rings at the points.

## Main definitions

* `AlgebraicGeometry.rangeComplementOfClosedPoints` is the open complement of a finite family
  of closed points.
* `AlgebraicGeometry.FinitePresentationAwayPointsSituation` is the standing data: a scheme,
  finitely many distinct closed points, and quasi-compactness of the inclusion of their open
  complement.
* `AlgebraicGeometry.FinitePresentationAway` is the category of finitely presented morphisms
  which become isomorphisms over a specified open subscheme.
* `AlgebraicGeometry.BaseChangeFunctor` is a functor to the product of the local categories
  together with identifications of its components with base change.
* `AlgebraicGeometry.finitePresentationAwayPointsBaseChange` is the base-change functor,
  together with its canonical identification after forgetting the defining properties.

## Implementation notes

The finite product in the source is represented by the dependent product category indexed by
`Fin n`. To retain that the displayed functor is the canonical base-change functor rather than
an arbitrary functor of the same type, it is bundled with natural isomorphisms identifying each
component, after passage to the ambient over-category, with `Over.pullback` along the canonical
morphism from the spectrum of the corresponding local ring.

The open complement is formed here as the complement of the range of the family. This is a
different presentation from `AlgebraicGeometry.complementOfClosedPoints`, which intersects the
complements of the individual points and indexes by an arbitrary finite type; the two opens
agree, but the interfaces do not.

## References

* [Stacks Project, Tag 0BFU](https://stacks.math.columbia.edu/tag/0BFU)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The open complement of a finite family of closed points. -/
def rangeComplementOfClosedPoints {S : Scheme.{u}} {n : ℕ} (s : Fin n → S)
    (hs : ∀ i, IsClosed ({s i} : Set S)) : S.Opens :=
  ⟨(Set.range s)ᶜ, by
    rw [Set.range_eq_iUnion]
    exact (isClosed_iUnion_of_finite hs).isOpen_compl⟩

/-- The standing scheme, closed points, and quasi-compactness hypothesis for Stacks Tag
`0BFU`. -/
structure FinitePresentationAwayPointsSituation where
  /-- The base scheme. -/
  S : Scheme.{u}
  /-- The number of distinguished closed points. -/
  n : ℕ
  /-- The distinguished points. -/
  points : Fin n → S
  /-- The distinguished points are pairwise distinct. -/
  points_injective : Function.Injective points
  /-- Every distinguished point is closed. -/
  points_closed : ∀ i, IsClosed ({points i} : Set S)
  /-- The inclusion of their open complement is quasi-compact. -/
  complement_quasiCompact :
    QuasiCompact (rangeComplementOfClosedPoints points points_closed).ι

/-- The property of a morphism to `S` that it is of finite presentation and becomes an
isomorphism after base change to `U`. -/
abbrev IsFinitePresentationAway {S : Scheme.{u}} (U : S.Opens) :
    ObjectProperty (Over S) := fun X ↦
  FinitePresentation X.hom ∧ IsIso ((Over.pullback U.ι).obj X).hom

/-- The category of finitely presented morphisms to `S` which are isomorphisms over `U`. -/
abbrev FinitePresentationAway {S : Scheme.{u}} (U : S.Opens) :=
  (IsFinitePresentationAway U).FullSubcategory

namespace FinitePresentationAwayPointsSituation

/-- The open complement of the distinguished points. -/
abbrev complement (D : FinitePresentationAwayPointsSituation.{u}) : D.S.Opens :=
  rangeComplementOfClosedPoints D.points D.points_closed

/-- The spectrum of the local ring at the `i`th distinguished point. -/
noncomputable abbrev localScheme (D : FinitePresentationAwayPointsSituation.{u})
    (i : Fin D.n) : Scheme.{u} := Spec (.of (D.S.presheaf.stalk (D.points i)))

/-- The complement of the closed point in the spectrum of the `i`th local ring. -/
def puncturedLocalScheme (D : FinitePresentationAwayPointsSituation.{u})
    (i : Fin D.n) : (D.localScheme i).Opens :=
  ⟨{IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))}ᶜ,
    (IsLocalRing.isClosed_singleton_closedPoint _).isOpen_compl⟩

/-- The source category in the displayed equation of Stacks Tag `0BFU`. -/
abbrev globalCategory (D : FinitePresentationAwayPointsSituation.{u}) :=
  FinitePresentationAway D.complement

/-- The `i`th factor of the target category in the displayed equation of Stacks Tag `0BFU`. -/
abbrev localCategory (D : FinitePresentationAwayPointsSituation.{u}) (i : Fin D.n) :=
  FinitePresentationAway (D.puncturedLocalScheme i)

end FinitePresentationAwayPointsSituation

/-- A functor in the displayed equation, equipped with the data asserting that every component
is canonically base change along `Spec(𝒪_{S,s_i}) ⟶ S`. -/
structure BaseChangeFunctor (D : FinitePresentationAwayPointsSituation.{u}) where
  /-- The functor to the product of the local categories. -/
  functor : D.globalCategory ⥤ (∀ i, D.localCategory i)
  /-- After forgetting the finiteness and isomorphism-away conditions, each component is the
  usual pullback functor. -/
  pullbackIso : ∀ i,
    functor ⋙ Pi.eval (fun i ↦ D.localCategory i) i ⋙
        ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i)) ≅
      ObjectProperty.ι (IsFinitePresentationAway D.complement) ⋙
        Over.pullback (D.S.fromSpecStalk (D.points i))

/-- **Stacks Project, Tag 0BFU.** Base change to the spectra of the local rings defines a
functor from finitely presented modifications of `S` supported at the distinguished points to
the product of the corresponding local categories. -/
@[stacks 0BFU]
noncomputable def finitePresentationAwayPointsBaseChange
    (D : FinitePresentationAwayPointsSituation.{u}) : BaseChangeFunctor D := by
  have hG : ∀ i X, IsFinitePresentationAway (D.puncturedLocalScheme i)
      (((IsFinitePresentationAway D.complement).ι ⋙
        Over.pullback (D.S.fromSpecStalk (D.points i))).obj X) := by
    intro i X
    let : MorphismProperty.IsStableUnderBaseChangeAlong
        (@LocallyOfFinitePresentation) (D.S.fromSpecStalk (D.points i)) :=
      ⟨fun sq h =>
        AlgebraicGeometry.locallyOfFinitePresentation_isStableUnderBaseChange.of_isPullback sq h⟩
    let : MorphismProperty.IsStableUnderBaseChangeAlong
        (@QuasiCompact) (D.S.fromSpecStalk (D.points i)) :=
      ⟨fun sq h => AlgebraicGeometry.quasiCompact_isStableUnderBaseChange.of_isPullback sq h⟩
    let : MorphismProperty.IsStableUnderBaseChangeAlong
        (@QuasiSeparated) (D.S.fromSpecStalk (D.points i)) :=
      ⟨fun sq h => AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange.of_isPullback sq h⟩
    constructor
    · rcases X.property.1 with ⟨hlfp, hqc, hqs⟩
      exact ⟨MorphismProperty.pullback_snd _ _ hlfp,
        MorphismProperty.pullback_snd _ _ hqc,
        MorphismProperty.pullback_snd _ _ hqs⟩
    · let g := D.S.fromSpecStalk (D.points i)
      let V := D.puncturedLocalScheme i
      have hV : V ≤ g ⁻¹ᵁ D.complement := by
        intro x hx
        change g x ∉ Set.range D.points
        rintro ⟨j, hj⟩
        have hspec : g x ⤳ D.points i := by
          have hr : g x ∈ Set.range (D.S.fromSpecStalk (D.points i)) := ⟨x, rfl⟩
          rw [Scheme.range_fromSpecStalk] at hr
          simpa [g] using hr
        have hspec' : D.points j ⤳ D.points i := by simpa [hj] using hspec
        have hmem : D.points i ∈ ({D.points j} : Set D.S) :=
          specializes_iff_forall_closed.mp hspec' _ (D.points_closed j) (by simp)
        have hji : j = i := D.points_injective (by simpa using hmem.symm)
        subst j
        have hmap : g x = g (IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))) :=
          hj.symm.trans (Scheme.fromSpecStalk_closedPoint (x := D.points i)).symm
        exact hx (g.isEmbedding.injective hmap)
      let q := g.resLE D.complement V hV
      have hcomp : q ≫ D.complement.ι = V.ι ≫ g := by dsimp [q]; simp
      let Y := (IsFinitePresentationAway D.complement).ι.obj X
      let A := (Over.pullback D.complement.ι).obj Y
      have : IsIso A.hom := X.property.2
      let B := (Over.pullback q).obj A
      have : IsIso B.hom := by
        change IsIso (Limits.pullback.snd A.hom q)
        infer_instance
      let iso₁ : (Over.pullback (q ≫ D.complement.ι)).obj Y ≅
          ((Over.pullback D.complement.ι ⋙ Over.pullback q).obj Y) :=
        (Over.pullbackComp q D.complement.ι).app Y
      let iso₂ : (Over.pullback (V.ι ≫ g)).obj Y ≅
          ((Over.pullback g ⋙ Over.pullback V.ι).obj Y) :=
        (Over.pullbackComp V.ι g).app Y
      let iso₂' : (Over.pullback (q ≫ D.complement.ι)).obj Y ≅
          ((Over.pullback g ⋙ Over.pullback V.ι).obj Y) :=
        (eqToIso (congrArg (fun f => Over.pullback f) hcomp)).app Y ≪≫ iso₂
      let iso : B ≅ ((Over.pullback V.ι).obj ((Over.pullback g).obj Y)) :=
        iso₁.symm ≪≫ iso₂'
      have : IsIso iso.hom.left := inferInstanceAs (IsIso ((Over.forget _).map iso.hom))
      have : IsIso (iso.hom.left ≫ ((Over.pullback V.ι).obj
          ((Over.pullback g).obj Y)).hom) := by
        rw [Over.w iso.hom]
        infer_instance
      exact IsIso.of_isIso_comp_left iso.hom.left
        (((Over.pullback V.ι).obj ((Over.pullback g).obj Y)).hom)
  let G : ∀ i, D.globalCategory ⥤ D.localCategory i := fun i =>
    ObjectProperty.lift _
      ((IsFinitePresentationAway D.complement).ι ⋙
        Over.pullback (D.S.fromSpecStalk (D.points i))) (hG i)
  let F : D.globalCategory ⥤ ∀ i, D.localCategory i := Functor.pi' G
  exact
    { functor := F
      pullbackIso := fun i =>
        Functor.isoWhiskerRight (Functor.pi'CompEval G i)
          (ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i))) ≪≫
          ObjectProperty.liftCompιIso _ _ (hG i) }

end AlgebraicGeometry
