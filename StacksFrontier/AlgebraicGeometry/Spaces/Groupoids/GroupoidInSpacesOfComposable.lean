module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.PointwiseComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-!
# Building a groupoid in algebraic spaces from a composition law on composable pairs

A `AlgebraicGeometry.GroupoidInAlgebraicSpaces` (Stacks 043W) asks for its composition as a
morphism out of the *chosen* fibre product `AlgebraicGeometry.AlgebraicSpaces.fiberProduct` of the
source and target maps, while the object it is naturally defined on is the presheaf
`Deformation.composableArrows` of composable pairs of arrows, which is the pointwise fibre
product. The two are compared by `AlgebraicGeometry.composableToPullback`, and the structure's
pointwise groupoid condition is stated through that comparison. So a composition law given on
composable pairs cannot be fed to the structure without knowing that the comparison is invertible.

This file supplies what is missing, and then the resulting constructor.

* The presheaf of composable pairs, with its two projections, *is* a fibre product
  (`AlgebraicGeometry.isLimitComposablePullbackCone`), so `composableToPullback` is an isomorphism.
* Hence a composition law `c` on composable pairs determines a morphism
  `AlgebraicGeometry.compOfComposable` out of the chosen fibre product whose composite with the
  comparison is `c` again.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.ofComposable` then builds a groupoid in algebraic
  spaces over the **final** algebraic space `AlgebraicGeometry.Space.terminalSpace`, where the two
  structure morphisms to the base and the three conditions that they are respected are unique and
  hence free.

A groupoid in algebraic spaces over the final algebraic space is what Stacks 04T4 parts (4) and
(5) build out of the self-intersection of an algebraic-space-valued point of an algebraic stack:
its spaces of objects and arrows are prescribed, so `objects` and `arrows` have to come out
*equal* — not merely isomorphic — to the given ones, which is why the constructor takes them as
arguments and makes them structure fields rather than producing them.

## Main definitions

* `AlgebraicGeometry.composableFst` and `AlgebraicGeometry.composableSnd`: the two projections of
  the presheaf of composable pairs of arrows.
* `AlgebraicGeometry.composableArrowsIsoPullback`: the comparison of the presheaf of composable
  pairs with the chosen fibre product, as an isomorphism.
* `AlgebraicGeometry.compOfComposable`: the morphism out of the chosen fibre product determined by
  a composition law on composable pairs.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.ofComposable`: **the** constructor of a groupoid in
  algebraic spaces over the final algebraic space.
* `Deformation.PointwiseGroupoid.ofIndexing`: a pointwise groupoid from an indexing of the
  objects by a groupoid together with an identification of arrows.

## Main results

* `AlgebraicGeometry.isLimitComposablePullbackCone`: the presheaf of composable pairs of arrows is
  a fibre product of the source and target maps.
* `AlgebraicGeometry.composableToPullback_comp_compOfComposable`: the composition law is recovered
  from the morphism it determines, which is what makes the pointwise groupoid condition of the
  structure say what it is expected to say.
* `AlgebraicGeometry.toGroupoidInFunctors_ofComposable_comp`: the underlying groupoid in
  presheaves of the constructed groupoid has the given composition law.
* `Deformation.PointwiseGroupoid.isPullback_comp_snd`: for a pointwise groupoid, composition and
  the second projection out of the composable pairs form a cartesian square of sets with two
  copies of the source map.
* `AlgebraicGeometry.Space.isPullback_comp_source`: **Stacks 043Z**, the lower right square of
  the composition diagram of a groupoid in algebraic spaces is cartesian.
* `AlgebraicGeometry.Space.isPullback_fst_comp`: **Stacks 043Z**, the triangle on top of the
  composition diagram of a groupoid in algebraic spaces, read as a square, is cartesian.

## Implementation notes

The groupoid structure produced by `Deformation.PointwiseGroupoid.ofIndexing` is the category
induced on the object set by the indexing map, written out rather than taken from Mathlib's
`CategoryTheory.InducedCategory`: the field `Deformation.PointwiseGroupoid.arrowEquiv` is about
the morphisms of the groupoid being constructed, and with the induced category the elaborator does
not reduce those to the morphisms of the indexing groupoid, so the identification cannot be
supplied. Written out, the `Hom` field *is* `index x ⟶ index y` and the identification goes in
directly. Everything else is inherited from the indexing groupoid, so nothing beyond the
identification is chosen.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 043Z](https://stacks.math.columbia.edu/tag/043Z)
* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Deformation.PointwiseGroupoid

universe w u'

/-- A pointwise groupoid built from an indexing of the objects by a groupoid. Given a map
`index` of the object set into a groupoid `D`, an identification of the arrows from `x` to `y`
with the morphisms `index x ⟶ index y`, and compatibility of that identification with
composition, the object set becomes a groupoid in the sense of `Deformation.PointwiseGroupoid`.

The groupoid structure is the one induced by `index`, so nothing beyond the identification of
arrows is chosen. -/
def ofIndexing {X Y : Type w} {D : Type u'} [Groupoid.{w} D] (index : X → D)
    (source target : Y → X) (comp : { p : Y × Y // source p.1 = target p.2 } → Y)
    (arrowEquiv : ∀ x y : X,
      (index x ⟶ index y) ≃ { a : Y // source a = x ∧ target a = y })
    (comp_eq : ∀ (x y z : X) (g : index x ⟶ index y) (f : index y ⟶ index z),
      (arrowEquiv x z (g ≫ f)).1 =
        comp ⟨((arrowEquiv y z f).1, (arrowEquiv x y g).1),
          (arrowEquiv y z f).2.1.trans (arrowEquiv x y g).2.2.symm⟩) :
    Deformation.PointwiseGroupoid source target comp where
  groupoid :=
    { toCategory :=
        { Hom x y := index x ⟶ index y
          id x := 𝟙 (index x)
          comp f g := f ≫ g
          id_comp f := Category.id_comp f
          comp_id f := Category.comp_id f
          assoc f g h := Category.assoc f g h }
      inv f := Groupoid.inv f
      inv_comp f := Groupoid.inv_comp f
      comp_inv f := Groupoid.comp_inv f }
  arrowEquiv := arrowEquiv
  comp_eq g f := comp_eq _ _ _ g f

variable {U R : Type w} {source target : R → U}
  {comp : { p : R × R // source p.1 = target p.2 } → R}

/-- Composition and the second projection out of the set of composable pairs form a cartesian
square with two copies of the source map: a composable pair is determined by its second arrow
together with its composite, and every pair of an arrow and a composite with matching sources
arises from one — the first arrow being the composite followed by the inverse of the second. -/
@[sga "3 V 1.2" "(2)"]
theorem isPullback_comp_snd (H : PointwiseGroupoid source target comp) :
    IsPullback (C := Type w) (TypeCat.ofHom comp)
      (TypeCat.ofHom fun p : { p : R × R // source p.1 = target p.2 } => p.1.2)
      (TypeCat.ofHom source) (TypeCat.ofHom source) := by
  classical
  let _inst := H.groupoid
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext p
    exact H.source_comp p.1.1 p.1.2 p.2
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ ⟨hcomp, hsnd⟩
    change b = b' at hsnd
    subst hsnd
    change comp ⟨(a, b), hab⟩ = comp ⟨(a', b), hab'⟩ at hcomp
    have ht : target a = target a' :=
      (H.target_comp a b hab).symm.trans ((congrArg target hcomp).trans (H.target_comp a' b hab'))
    let β : source b ⟶ target b := (H.arrowEquiv (source b) (target b)).symm ⟨b, rfl, rfl⟩
    let α : target b ⟶ target a := (H.arrowEquiv (target b) (target a)).symm ⟨a, hab, rfl⟩
    let α' : target b ⟶ target a := (H.arrowEquiv (target b) (target a)).symm ⟨a', hab', ht.symm⟩
    have hcat : β ≫ α = β ≫ α' := by
      apply (H.arrowEquiv (source b) (target a)).injective
      apply Subtype.ext
      calc (H.arrowEquiv (source b) (target a) (β ≫ α)).1 = comp ⟨(a, b), hab⟩ := by
            simpa [α, β] using H.comp_eq β α
        _ = comp ⟨(a', b), hab'⟩ := hcomp
        _ = (H.arrowEquiv (source b) (target a) (β ≫ α')).1 := by
            simpa [α', β] using (H.comp_eq β α').symm
    have ha : a = a' := by
      simpa [α, α'] using
        congrArg (fun f => (H.arrowEquiv (target b) (target a) f).1) ((cancel_epi β).1 hcat)
    exact Subtype.ext (Prod.ext ha rfl)
  · intro d b hdb
    change source d = source b at hdb
    let β : source b ⟶ target b := (H.arrowEquiv (source b) (target b)).symm ⟨b, rfl, rfl⟩
    let γ : source b ⟶ target d := (H.arrowEquiv (source b) (target d)).symm ⟨d, hdb, rfl⟩
    let α : target b ⟶ target d := Groupoid.inv β ≫ γ
    refine ⟨⟨((H.arrowEquiv (target b) (target d) α).1, b),
      (H.arrowEquiv (target b) (target d) α).2.1⟩, ?_, rfl⟩
    calc comp ⟨((H.arrowEquiv (target b) (target d) α).1, b), _⟩
          = (H.arrowEquiv (source b) (target d) (β ≫ α)).1 := by
            simpa [β] using (H.comp_eq β α).symm
      _ = (H.arrowEquiv (source b) (target d) γ).1 :=
            congrArg (fun f => (H.arrowEquiv (source b) (target d) f).1)
              (by simp [α, ← Category.assoc])
      _ = d := by simp [γ]

end Deformation.PointwiseGroupoid

namespace AlgebraicGeometry

universe u

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}

/-- Two equal morphisms of set-valued presheaves agree at every point. -/
theorem natTrans_app_congr {F G : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {a b : F ⟶ G}
    (h : a = b) (T : (BigFppfOver C S hS)ᵒᵖ) (x : F.obj T) : a.app T x = b.app T x := by
  subst h
  rfl

section Composable

variable {U R : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (s t : R ⟶ U)

/-- The first projection of the presheaf of composable pairs of arrows. -/
def composableFst : Deformation.composableArrows U R s t ⟶ R where
  app _ := ↾ fun p => p.1.1
  naturality := by intros; rfl

/-- The second projection of the presheaf of composable pairs of arrows. -/
def composableSnd : Deformation.composableArrows U R s t ⟶ R where
  app _ := ↾ fun p => p.1.2
  naturality := by intros; rfl

/-- The first projection sends a composable pair to its first arrow. -/
@[simp]
theorem composableFst_app (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows U R s t).obj T) :
    (composableFst s t).app T p = p.1.1 := rfl

/-- The second projection sends a composable pair to its second arrow. -/
@[simp]
theorem composableSnd_app (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows U R s t).obj T) :
    (composableSnd s t).app T p = p.1.2 := rfl

/-- The first arrow of the restriction of a composable pair is the restriction of its first
arrow. -/
@[simp]
theorem composableArrows_map_fst {T T' : (BigFppfOver C S hS)ᵒᵖ} (g : T ⟶ T')
    (p : (Deformation.composableArrows U R s t).obj T) :
    (((Deformation.composableArrows U R s t).map g) p).1.1 = R.map g p.1.1 := rfl

/-- The second arrow of the restriction of a composable pair is the restriction of its second
arrow. -/
@[simp]
theorem composableArrows_map_snd {T T' : (BigFppfOver C S hS)ᵒᵖ} (g : T ⟶ T')
    (p : (Deformation.composableArrows U R s t).obj T) :
    (((Deformation.composableArrows U R s t).map g) p).1.2 = R.map g p.1.2 := rfl

/-- The two projections of the presheaf of composable pairs equalize source and target. -/
theorem composableFst_comp_source :
    composableFst s t ≫ s = composableSnd s t ≫ t := by
  ext T p
  exact p.2

/-- The presheaf of composable pairs of arrows, with its two projections, is a fibre product of
the source and target maps. Limits of set-valued presheaves are computed pointwise and a
composable pair is by definition a pair of arrows whose source and target agree. -/
noncomputable def isLimitComposablePullbackCone :
    IsLimit (PullbackCone.mk (composableFst s t) (composableSnd s t)
      (composableFst_comp_source s t)) :=
  PullbackCone.IsLimit.mk _
    (fun c =>
      { app := fun T => ↾ fun w =>
          ⟨(c.fst.app T w, c.snd.app T w), by
            simpa using natTrans_app_congr c.condition T w⟩
        naturality := by
          intro T T' g
          ext w
          refine Subtype.ext (Prod.ext ?_ ?_) <;> simp })
    (fun c => by ext T w; rfl)
    (fun c => by ext T w; rfl)
    (fun c m h₁ h₂ => by
      ext T w
      refine Subtype.ext (Prod.ext ?_ ?_)
      · simpa using natTrans_app_congr h₁ T w
      · simpa using natTrans_app_congr h₂ T w)

/-- The comparison `AlgebraicGeometry.composableToPullback` followed by the first projection of
the chosen fibre product is the first projection of the presheaf of composable pairs. -/
@[simp]
theorem composableToPullback_comp_pullbackFst :
    composableToPullback s t ≫ pullback.fst s t = composableFst s t :=
  pullback.lift_fst _ _ _

/-- The comparison `AlgebraicGeometry.composableToPullback` followed by the second projection of
the chosen fibre product is the second projection of the presheaf of composable pairs. -/
@[simp]
theorem composableToPullback_comp_pullbackSnd :
    composableToPullback s t ≫ pullback.snd s t = composableSnd s t :=
  pullback.lift_snd _ _ _

/-- The comparison of the chosen fibre product of the source and target maps with the presheaf of
composable pairs of arrows, in the direction opposite to
`AlgebraicGeometry.composableToPullback`. -/
noncomputable def pullbackToComposable :
    pullback s t ⟶ Deformation.composableArrows U R s t :=
  PullbackCone.IsLimit.lift (isLimitComposablePullbackCone s t)
    (pullback.fst s t) (pullback.snd s t) pullback.condition

/-- The comparison `AlgebraicGeometry.pullbackToComposable` followed by the first projection of
the presheaf of composable pairs is the first projection of the chosen fibre product. -/
@[simp]
theorem pullbackToComposable_comp_composableFst :
    pullbackToComposable s t ≫ composableFst s t = pullback.fst s t :=
  PullbackCone.IsLimit.lift_fst _ _ _ _

/-- The comparison `AlgebraicGeometry.pullbackToComposable` followed by the second projection of
the presheaf of composable pairs is the second projection of the chosen fibre product. -/
@[simp]
theorem pullbackToComposable_comp_composableSnd :
    pullbackToComposable s t ≫ composableSnd s t = pullback.snd s t :=
  PullbackCone.IsLimit.lift_snd _ _ _ _

/-- `AlgebraicGeometry.pullbackToComposable` is a left inverse of
`AlgebraicGeometry.composableToPullback`. -/
@[simp]
theorem composableToPullback_comp_pullbackToComposable :
    composableToPullback s t ≫ pullbackToComposable s t = 𝟙 _ := by
  refine PullbackCone.IsLimit.hom_ext (isLimitComposablePullbackCone s t) ?_ ?_
  · show (composableToPullback s t ≫ pullbackToComposable s t) ≫ composableFst s t =
      𝟙 _ ≫ composableFst s t
    rw [Category.assoc, pullbackToComposable_comp_composableFst,
      composableToPullback_comp_pullbackFst, Category.id_comp]
  · show (composableToPullback s t ≫ pullbackToComposable s t) ≫ composableSnd s t =
      𝟙 _ ≫ composableSnd s t
    rw [Category.assoc, pullbackToComposable_comp_composableSnd,
      composableToPullback_comp_pullbackSnd, Category.id_comp]

/-- `AlgebraicGeometry.pullbackToComposable` is a right inverse of
`AlgebraicGeometry.composableToPullback`. -/
@[simp]
theorem pullbackToComposable_comp_composableToPullback :
    pullbackToComposable s t ≫ composableToPullback s t = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_ <;> simp

/-- The presheaf of composable pairs of arrows is isomorphic to the chosen fibre product of the
source and target maps, by the canonical comparison. -/
noncomputable def composableArrowsIsoPullback :
    Deformation.composableArrows U R s t ≅ pullback s t where
  hom := composableToPullback s t
  inv := pullbackToComposable s t

/-- The comparison of the presheaf of composable pairs with the chosen fibre product is an
isomorphism. -/
instance isIso_composableToPullback : IsIso (composableToPullback s t) :=
  (composableArrowsIsoPullback s t).isIso_hom

/-- The first projection of the chosen fibre product sends the image of a composable pair under
the comparison to its first arrow. -/
@[simp]
theorem pullbackFst_app_composableToPullback (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows U R s t).obj T) :
    (pullback.fst s t).app T ((composableToPullback s t).app T p) = p.1.1 :=
  natTrans_app_congr (composableToPullback_comp_pullbackFst s t) T p

/-- The second projection of the chosen fibre product sends the image of a composable pair under
the comparison to its second arrow. -/
@[simp]
theorem pullbackSnd_app_composableToPullback (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows U R s t).obj T) :
    (pullback.snd s t).app T ((composableToPullback s t).app T p) = p.1.2 :=
  natTrans_app_congr (composableToPullback_comp_pullbackSnd s t) T p

/-- The morphism out of the chosen fibre product of the source and target maps determined by a
composition law on composable pairs of arrows. -/
noncomputable def compOfComposable (c : Deformation.composableArrows U R s t ⟶ R) :
    pullback s t ⟶ R :=
  pullbackToComposable s t ≫ c

/-- The comparison `AlgebraicGeometry.composableToPullback` followed by
`AlgebraicGeometry.compOfComposable` of a composition law `c` is `c`. -/
@[simp]
theorem composableToPullback_comp_compOfComposable
    (c : Deformation.composableArrows U R s t ⟶ R) :
    composableToPullback s t ≫ compOfComposable s t c = c := by
  rw [compOfComposable, ← Category.assoc, composableToPullback_comp_pullbackToComposable,
    Category.id_comp]

/-- At the image of a composable pair under the comparison, `AlgebraicGeometry.compOfComposable`
of a composition law `c` takes the value of `c` at that pair. -/
@[simp]
theorem compOfComposable_app_composableToPullback
    (c : Deformation.composableArrows U R s t ⟶ R) (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows U R s t).obj T) :
    (compOfComposable s t c).app T ((composableToPullback s t).app T p) = c.app T p :=
  natTrans_app_congr (composableToPullback_comp_compOfComposable s t c) T p

end Composable

namespace GroupoidInAlgebraicSpaces

/-- A groupoid in algebraic spaces over the final algebraic space, from the spaces of objects and
of arrows, the source and target maps, a composition law on composable pairs of arrows, and the
pointwise groupoid condition for that composition law.

The two structure morphisms to the base and the three conditions that the source, target and
composition respect them are free, the base being final
(`AlgebraicGeometry.Space.terminalSpace_isTerminal`). The spaces of objects and of arrows are
structure fields, so they come out equal to the given ones. -/
@[sga "3 V 1.2"]
noncomputable def ofComposable (U R : AlgebraicSpaces C S hS) (s t : R ⟶ U)
    (c : Deformation.composableArrows U.obj R.obj s.hom t.hom ⟶ R.obj)
    (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid (s.hom.app T) (t.hom.app T)
      (fun p => c.app T p))) :
    GroupoidInAlgebraicSpaces C S hS (Space.terminalSpace C S hS) where
  objects := U
  arrows := R
  objectsToBase := (Space.terminalSpace_isTerminal C S hS).from U
  arrowsToBase := (Space.terminalSpace_isTerminal C S hS).from R
  source := s
  target := t
  source_over := (Space.terminalSpace_isTerminal C S hS).hom_ext _ _
  target_over := (Space.terminalSpace_isTerminal C S hS).hom_ext _ _
  comp := ObjectProperty.homMk (compOfComposable s.hom t.hom c)
  comp_over := (Space.terminalSpace_isTerminal C S hS).hom_ext _ _
  pointwiseGroupoid T := by
    refine Nonempty.map (fun G => ?_) (hG T)
    exact (funext fun p =>
      (compOfComposable_app_composableToPullback s.hom t.hom c T p).symm) ▸ G

/-- The space of objects of `ofComposable U R s t c hG` is `U`. -/
@[simp]
theorem ofComposable_objects (U R : AlgebraicSpaces C S hS) (s t : R ⟶ U)
    (c : Deformation.composableArrows U.obj R.obj s.hom t.hom ⟶ R.obj)
    (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid (s.hom.app T) (t.hom.app T)
      (fun p => c.app T p))) :
    (ofComposable U R s t c hG).objects = U := rfl

/-- The space of arrows of `ofComposable U R s t c hG` is `R`. -/
@[simp]
theorem ofComposable_arrows (U R : AlgebraicSpaces C S hS) (s t : R ⟶ U)
    (c : Deformation.composableArrows U.obj R.obj s.hom t.hom ⟶ R.obj)
    (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid (s.hom.app T) (t.hom.app T)
      (fun p => c.app T p))) :
    (ofComposable U R s t c hG).arrows = R := rfl

/-- The source map of `ofComposable U R s t c hG` is `s`. -/
@[simp]
theorem ofComposable_source (U R : AlgebraicSpaces C S hS) (s t : R ⟶ U)
    (c : Deformation.composableArrows U.obj R.obj s.hom t.hom ⟶ R.obj)
    (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid (s.hom.app T) (t.hom.app T)
      (fun p => c.app T p))) :
    (ofComposable U R s t c hG).source = s := rfl

/-- The target map of `ofComposable U R s t c hG` is `t`. -/
@[simp]
theorem ofComposable_target (U R : AlgebraicSpaces C S hS) (s t : R ⟶ U)
    (c : Deformation.composableArrows U.obj R.obj s.hom t.hom ⟶ R.obj)
    (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid (s.hom.app T) (t.hom.app T)
      (fun p => c.app T p))) :
    (ofComposable U R s t c hG).target = t := rfl

end GroupoidInAlgebraicSpaces

/-- The underlying groupoid in presheaves of a groupoid in algebraic spaces built from a
composition law on composable pairs of arrows has that composition law. -/
theorem toGroupoidInFunctors_ofComposable_comp (U R : AlgebraicSpaces C S hS) (s t : R ⟶ U)
    (c : Deformation.composableArrows U.obj R.obj s.hom t.hom ⟶ R.obj)
    (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid (s.hom.app T) (t.hom.app T)
      (fun p => c.app T p))) :
    (GroupoidInAlgebraicSpaces.ofComposable U R s t c hG).toGroupoidInFunctors.comp = c :=
  composableToPullback_comp_compOfComposable s.hom t.hom c

/-- The composite of two composable arrows of a groupoid in algebraic spaces built from a
composition law on composable pairs of arrows is the value of that law at the pair. -/
theorem compose_ofComposable (U R : AlgebraicSpaces C S hS) (s t : R ⟶ U)
    (c : Deformation.composableArrows U.obj R.obj s.hom t.hom ⟶ R.obj)
    (hG : ∀ T, Nonempty (Deformation.PointwiseGroupoid (s.hom.app T) (t.hom.app T)
      (fun p => c.app T p)))
    (T : (BigFppfOver C S hS)ᵒᵖ) (a b : R.obj.obj T)
    (h : s.hom.app T a = t.hom.app T b) :
    (GroupoidInAlgebraicSpaces.ofComposable U R s t c hG).toGroupoidInFunctors.compose T a b h =
      c.app T ⟨(a, b), h⟩ :=
  natTrans_app_congr (toGroupoidInFunctors_ofComposable_comp U R s t c hG) T ⟨(a, b), h⟩

namespace Space

/-- A square in a space-valued category is cartesian if its underlying square of presheaves is. -/
private theorem isPullback_of_hom {X Y Z W : AlgebraicSpaces C S hS} {f : X ⟶ Y} {g : X ⟶ Z}
    {h : Y ⟶ W} {i : Z ⟶ W} (H : IsPullback f.hom g.hom h.hom i.hom) : IsPullback f g h i :=
  IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ H.w) H

add_to_stacks 043Z "lower_left" AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct

/-- For a groupoid in algebraic spaces, composition and the second projection out of the space of
composable pairs of arrows form a cartesian square with two copies of the source map: a
composable pair is determined by its second arrow together with its composite, and every arrow
and composite with matching sources arise from one, the first arrow of the pair being the
composite preceded by the inverse of the second. -/
@[stacks 043Z "lower_right"]
theorem isPullback_comp_source {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsPullback G.comp
      (ObjectProperty.homMk (pullback.snd G.source.hom G.target.hom) :
        AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows)
      G.source G.source := by
  have hcomposable : IsPullback
      (composableToPullback G.source.hom G.target.hom ≫ G.comp.hom)
      (composableSnd G.source.hom G.target.hom) G.source.hom G.source.hom :=
    IsPullback.of_forall_isPullback_app fun T =>
      (Classical.choice (G.pointwiseGroupoid T)).isPullback_comp_snd
  have hunderlying : IsPullback G.comp.hom
      (pullback.snd G.source.hom G.target.hom) G.source.hom G.source.hom :=
    hcomposable.of_iso (composableArrowsIsoPullback G.source.hom G.target.hom)
      (Iso.refl _) (Iso.refl _) (Iso.refl _) (Category.comp_id _)
      ((Category.comp_id _).trans
        (composableToPullback_comp_pullbackSnd G.source.hom G.target.hom).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  exact isPullback_of_hom hunderlying

/-- For a groupoid in algebraic spaces, the first projection out of the space of composable pairs
of arrows and composition form a cartesian square with two copies of the target map: a
composable pair is determined by its first arrow together with its composite, and every arrow
and composite with matching targets arise from one, the second arrow of the pair being the
composite preceded by the inverse of the first. -/
@[stacks 043Z "top_square"]
theorem isPullback_fst_comp {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B) :
    IsPullback
      (ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom) :
        AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows)
      G.comp G.target G.target := by
  have hcomposable : IsPullback (composableFst G.source.hom G.target.hom)
      (composableToPullback G.source.hom G.target.hom ≫ G.comp.hom)
      G.target.hom G.target.hom :=
    IsPullback.of_forall_isPullback_app fun T =>
      (Classical.choice (G.pointwiseGroupoid T)).isPullback_comp_fst
  have hunderlying : IsPullback (pullback.fst G.source.hom G.target.hom)
      G.comp.hom G.target.hom G.target.hom :=
    hcomposable.of_iso (composableArrowsIsoPullback G.source.hom G.target.hom)
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      ((Category.comp_id _).trans
        (composableToPullback_comp_pullbackFst G.source.hom G.target.hom).symm)
      (Category.comp_id _)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)
  exact isPullback_of_hom hunderlying

end Space

end AlgebraicGeometry

end
