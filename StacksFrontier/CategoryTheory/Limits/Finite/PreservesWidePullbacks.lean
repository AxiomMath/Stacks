module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
public import Mathlib.Data.Fintype.Option
public import StacksFrontier.CategoryTheory.Limits.Finite.Connected

/-!
# Finite wide pullbacks are preserved by a functor preserving binary pullbacks

A functor which commutes with binary fibre products commutes with all *finite* iterated fibre
products: if `F : C ⥤ D` preserves limits of shape `WalkingCospan` and `C` has pullbacks, then
`F` preserves limits of shape `WidePullbackShape α` for every finite index type `α`.

Two hypotheses and no more are needed. On `F`, preservation of binary pullbacks alone: every
wide pullback shape is connected, so gluing the legs on one at a time only ever asks for a
binary pullback, and neither a terminal object nor a product is ever formed. On `C`, the
existence of pullbacks: the proof realises the limit over `Option α` as a pullback of the limit
over `α`, and that intermediate wide pullback has to exist in `C` to be mapped anywhere. By
`CategoryTheory.Limits.hasFiniteWidePullbacks_of_hasPullbacks` this is again only binary
pullbacks.

The argument is the preservation counterpart of that existence statement. The index type is
built up by `Finite.induction_empty_option`; over the empty index type the shape has `none` as
an initial object, so every functor preserves limits of that shape, and the step from `α` to
`Option α` glues on the leg at `none` with a single pullback square.

## Main definitions

* `CategoryTheory.Functor.mapWidePullbackCone`: the image under a functor of a wide pullback
  cone, read as a wide pullback cone on the family of images.
* `CategoryTheory.Limits.WidePullbackCone.glueOption`: the wide pullback cone over `Option α`
  assembled from a wide pullback cone over `α` and a pullback square gluing on the leg
  at `none`.
* `CategoryTheory.Limits.WidePullbackShape.isInitialNone`: over an empty index type, `none` is
  an initial object of the wide pullback shape.

## Main results

* `CategoryTheory.Limits.WidePullbackCone.isLimitGlueOption`: the assembled cone is limiting as
  soon as both of its ingredients are. An iterated fibre product is a fibre product of one fewer
  of its factors with the remaining one, and this is that statement at the level of cones, so it
  can be read in the source category and in the target category alike.
* `CategoryTheory.Limits.preservesLimitsOfShape_of_isInitial`: a functor preserves limits of any
  shape having an initial object, such a limit being the value of the diagram at that object.
* `CategoryTheory.Limits.preservesLimitsOfShape_widePullbackShape`: the main statement.
-/

@[expose] public section

namespace CategoryTheory

open CategoryTheory.Limits

universe t v v' u u'

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

namespace Functor

variable (F : C ⥤ D) {ι : Type t} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X}

/-- The image under `F` of a wide pullback cone on a family `f`, read as a wide pullback cone on
the family of images `F.map (f i)`. It has the same components as `F.mapCone`; only the diagram
it is a cone over is spelled as a wide cospan rather than as a wide cospan composed with `F`. -/
@[simps! pt]
def mapWidePullbackCone (s : WidePullbackCone f) : WidePullbackCone (fun i ↦ F.map (f i)) :=
  WidePullbackCone.mk (F.map s.base) (fun i ↦ F.map (s.π i))
    (fun i ↦ by rw [← F.map_comp, s.condition])

/-- The base of `F.mapWidePullbackCone s` is the image under `F` of the base of `s`. -/
@[simp]
lemma mapWidePullbackCone_base (s : WidePullbackCone f) :
    (F.mapWidePullbackCone s).base = F.map s.base := rfl

/-- The leg at `i` of `F.mapWidePullbackCone s` is the image under `F` of the leg of `s` at `i`. -/
@[simp]
lemma mapWidePullbackCone_π (s : WidePullbackCone f) (i : ι) :
    (F.mapWidePullbackCone s).π i = F.map (s.π i) := rfl

end Functor

namespace Limits

/-! ### Reading the image of a wide pullback cone -/

namespace WidePullbackCone

variable (F : C ⥤ D) {ι : Type t} {X : C} {Y : ι → C} {f : ∀ i, Y i ⟶ X}

/-- A cone over the composite of a wide cospan with `F`, read as a wide pullback cone on the
family of images. -/
def ofMapCone (t : Cone (WidePullbackShape.wideCospan X Y f ⋙ F)) :
    WidePullbackCone (fun i ↦ F.map (f i)) :=
  WidePullbackCone.mk (t.π.app none) (fun i ↦ t.π.app (some i))
    (fun i ↦ by simpa using (t.π.naturality (WidePullbackShape.Hom.term i)).symm)

/-- If `F.mapCone s` is a limit cone then so is its reading as a wide pullback cone on the
family of images. -/
def isLimitMapOfIsLimitMapCone {s : WidePullbackCone f} (h : IsLimit (F.mapCone s)) :
    IsLimit (F.mapWidePullbackCone s) :=
  WidePullbackCone.IsLimit.mk _
    (fun t ↦ h.lift (WidePullbackShape.mkCone t.base t.π (fun j ↦ t.condition j)))
    (fun _ ↦ h.fac _ none) (fun _ i ↦ h.fac _ (some i))
    (fun t m hb hπ ↦ h.uniq (WidePullbackShape.mkCone t.base t.π (fun j ↦ t.condition j)) m
      (by rintro (_ | j); exacts [hb, hπ j]))

/-- The converse reading: if the image of `s` is a limiting wide pullback cone on the family of
images, then `F.mapCone s` is a limit cone. -/
def isLimitMapConeOfIsLimitMap {s : WidePullbackCone f}
    (h : IsLimit (F.mapWidePullbackCone s)) : IsLimit (F.mapCone s) where
  lift t := h.lift (ofMapCone F t)
  fac t j := by rcases j with _ | i; exacts [h.fac _ none, h.fac _ (some i)]
  uniq t m hm := h.uniq (ofMapCone F t) m (by rintro (_ | i); exacts [hm none, hm (some i)])

end WidePullbackCone

/-! ### Gluing on one more leg -/

namespace WidePullbackCone

variable {α : Type t} {B : C} {objs : Option α → C} {arrows : ∀ j, objs j ⟶ B}
  (s : WidePullbackCone (fun a : α ↦ arrows (some a))) (p : PullbackCone s.base (arrows none))

/-- The wide pullback cone over `Option α` glued from a wide pullback cone `s` over `α` and a
pullback square `p` of the base map of `s` against the remaining arrow `arrows none`. Its leg at
`none` is the second projection of `p`, and its leg at `some a` is the first projection of `p`
followed by the leg of `s` at `a`. -/
def glueOption : WidePullbackCone arrows :=
  WidePullbackCone.mk (p.snd ≫ arrows none)
    (fun j ↦ Option.rec (motive := fun j ↦ p.pt ⟶ objs j) p.snd (fun a ↦ p.fst ≫ s.π a) j)
    (by rintro (_ | a)
        · rfl
        · rw [Category.assoc, s.condition a, p.condition])

/-- The base of `glueOption s p` is the second projection of `p` followed by `arrows none`. -/
@[simp]
lemma glueOption_base : (glueOption s p).base = p.snd ≫ arrows none := rfl

/-- The leg of `glueOption s p` at `none` is the second projection of `p`. -/
@[simp]
lemma glueOption_π_none : (glueOption s p).π none = p.snd := rfl

/-- The leg of `glueOption s p` at `some a` is the first projection of `p` followed by the leg
of `s` at `a`. -/
@[simp]
lemma glueOption_π_some (a : α) : (glueOption s p).π (some a) = p.fst ≫ s.π a := rfl

/-- **An iterated fibre product is a fibre product.** If `s` is a limiting wide pullback cone
over `α` and `p` is a limiting pullback square of its base map against the arrow at `none`, then
the glued cone is a limiting wide pullback cone over `Option α`.

Only the universal properties of `s` and of `p` are used, so this applies verbatim to the images
of `s` and `p` under a functor preserving both. -/
def isLimitGlueOption (hs : IsLimit s) (hp : IsLimit p) : IsLimit (glueOption s p) := by
  refine WidePullbackCone.IsLimit.mk _
    (fun t ↦ PullbackCone.IsLimit.lift hp
      (WidePullbackCone.IsLimit.lift hs t.base (fun a ↦ t.π (some a))
        (fun a ↦ t.condition (some a)))
      (t.π none)
      ((WidePullbackCone.IsLimit.lift_base hs _ _ _).trans (t.condition none).symm))
    (fun t ↦ ?_) (fun t ↦ ?_) (fun t m hbase hπ ↦ ?_)
  · change _ ≫ p.snd ≫ arrows none = _
    rw [← Category.assoc, PullbackCone.IsLimit.lift_snd]
    exact t.condition none
  · rintro (_ | a)
    · exact PullbackCone.IsLimit.lift_snd hp _ _ _
    · change _ ≫ p.fst ≫ s.π a = _
      rw [← Category.assoc, PullbackCone.IsLimit.lift_fst]
      exact WidePullbackCone.IsLimit.lift_π hs _ _ _ a
  · refine PullbackCone.IsLimit.hom_ext hp ?_ ?_
    · rw [PullbackCone.IsLimit.lift_fst]
      refine WidePullbackCone.IsLimit.hom_ext hs ?_ (fun a ↦ ?_)
      · exact (Category.assoc m p.fst s.base).trans
          (((congrArg (fun x ↦ m ≫ x) p.condition).trans hbase).trans
            (WidePullbackCone.IsLimit.lift_base hs _ _ _).symm)
      · refine (Category.assoc m p.fst (s.π a)).trans ((hπ (some a)).trans ?_)
        exact (WidePullbackCone.IsLimit.lift_π hs t.base (fun a ↦ t.π (some a))
          (fun a ↦ t.condition (some a)) a).symm
    · rw [PullbackCone.IsLimit.lift_snd]
      exact hπ none

end WidePullbackCone

/-! ### Shapes with an initial object -/

/-- A diagram over a shape with an initial object `X` has its value at `X` as a limit, with legs
the images of the unique arrows out of `X`. Those legs are produced by the diagram itself, so
every functor carries this limit cone to a limit cone. -/
lemma preservesLimit_of_isInitial {J : Type*} [Category J] {X : J} (hX : IsInitial X)
    (K : J ⥤ C) (F : C ⥤ D) : PreservesLimit K F :=
  preservesLimit_of_preserves_limit_cone (limitOfDiagramInitial hX K)
    (IsLimit.ofIsoLimit (limitOfDiagramInitial hX (K ⋙ F)) (Cone.ext (Iso.refl _) (by simp)))

/-- Every functor preserves limits of a shape having an initial object. -/
lemma preservesLimitsOfShape_of_isInitial {J : Type*} [Category J] {X : J} (hX : IsInitial X)
    (F : C ⥤ D) : PreservesLimitsOfShape J F :=
  ⟨fun {K} ↦ preservesLimit_of_isInitial hX K F⟩

/-- Over an empty index type the wide pullback shape has the single object `none`, which is
therefore initial. -/
def WidePullbackShape.isInitialNone (J : Type t) [IsEmpty J] :
    IsInitial (C := WidePullbackShape J) none :=
  IsInitial.ofUnique _ (h := fun Y ↦ by
    rcases Y with _ | j
    · exact ⟨⟨𝟙 _⟩, fun a ↦ Subsingleton.elim _ _⟩
    · exact (IsEmpty.false j).elim)

/-! ### Binary pullbacks give finite wide pullbacks -/

/-- The inductive step: a functor preserving binary pullbacks and the wide pullbacks over `α`
preserves the wide pullbacks over `Option α`, by gluing on the leg at `none`. -/
private lemma preservesLimitsOfShape_widePullbackShape_option (F : C ⥤ D)
    [HasFiniteWidePullbacks C] [PreservesLimitsOfShape WalkingCospan F] {α : Type} [Finite α]
    (h : PreservesLimitsOfShape (WidePullbackShape α) F) :
    PreservesLimitsOfShape (WidePullbackShape (Option α)) F := by
  have := h
  have key : ∀ (B : C) (objs : Option α → C) (arrows : ∀ j, objs j ⟶ B),
      PreservesLimit (WidePullbackShape.wideCospan B objs arrows) F := by
    intro B objs arrows
    let sC : WidePullbackCone (fun a : α ↦ arrows (some a)) :=
      limit.cone (WidePullbackShape.wideCospan B (fun a : α ↦ objs (some a))
        (fun a ↦ arrows (some a)))
    have hsC : IsLimit sC := limit.isLimit _
    have hpC : IsLimit (PullbackCone.mk (pullback.fst sC.base (arrows none))
        (pullback.snd sC.base (arrows none)) pullback.condition) := pullbackIsPullback _ _
    refine preservesLimit_of_preserves_limit_cone
      (WidePullbackCone.isLimitGlueOption sC _ hsC hpC) ?_
    refine WidePullbackCone.isLimitMapConeOfIsLimitMap F ?_
    refine IsLimit.ofIsoLimit (WidePullbackCone.isLimitGlueOption
      (objs := fun j ↦ F.obj (objs j)) (arrows := fun j ↦ F.map (arrows j))
      (F.mapWidePullbackCone sC) _
      (WidePullbackCone.isLimitMapOfIsLimitMapCone F (isLimitOfPreserves F hsC))
      (isLimitOfHasPullbackOfPreservesLimit F sC.base (arrows none)))
      (WidePullbackCone.ext (Iso.refl _) ((Category.id_comp _).trans (F.map_comp _ _))
        (fun i ↦ ?_))
    rcases i with _ | a
    · exact Category.id_comp _
    · exact (Category.id_comp _).trans (F.map_comp _ _)
  constructor
  intro K
  have := key (K.obj none) (fun j ↦ K.obj (some j)) (fun j ↦ K.map (WidePullbackShape.Hom.term j))
  exact preservesLimit_of_iso_diagram F (WidePullbackShape.diagramIsoWideCospan K).symm

/-- **A functor preserving binary fibre products preserves finite iterated fibre products.**
If `C` has pullbacks and `F : C ⥤ D` preserves limits of shape `WalkingCospan`, then `F`
preserves limits of shape `WidePullbackShape α` for every finite index type `α`.

The index type is built up by `Finite.induction_empty_option`. Over the empty index type the
shape has an initial object, and the step from `α` to `Option α` is one application of
`CategoryTheory.Limits.WidePullbackCone.isLimitGlueOption`, read once in `C` and once in `D`. -/
theorem preservesLimitsOfShape_widePullbackShape (F : C ⥤ D) [HasPullbacks C]
    [PreservesLimitsOfShape WalkingCospan F] (α : Type) [Finite α] :
    PreservesLimitsOfShape (WidePullbackShape α) F := by
  have : HasFiniteWidePullbacks C := hasFiniteWidePullbacks_of_hasPullbacks C
  refine Finite.induction_empty_option
    (P := fun α ↦ PreservesLimitsOfShape (WidePullbackShape α) F) ?_ ?_ ?_ α
  · intro β γ e h
    exact preservesLimitsOfShape_of_equiv (WidePullbackShape.equivalenceOfEquiv _ e) F
  · exact preservesLimitsOfShape_of_isInitial (WidePullbackShape.isInitialNone PEmpty) F
  · intro β _ h
    exact preservesLimitsOfShape_widePullbackShape_option F h

end Limits

end CategoryTheory
