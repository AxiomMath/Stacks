module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.GroupoidQuotient.MinimalAutoequivalence

/-!
# Groupoids in functors and functors to groupoids

A groupoid in functors on a category `C` is the same data as a functor `C ⥤ Grpd`, and a
morphism of groupoids in functors is the same data as a morphism of the associated functors.

## Main definitions

* `Deformation.GroupoidInFunctors.evaluationGrpdFunctor`: the functor from groupoids in
  functors on `C` to functors `C ⥤ Grpd` assembled from the evaluations.
* `Deformation.GroupoidInFunctors.ofGrpdFunctor`: the groupoid in functors determined by a
  functor `C ⥤ Grpd`.

## Main results

* `Deformation.GroupoidInFunctors.evaluationEquivalence`: `evaluationGrpdFunctor` is an
  equivalence of categories.

## References

* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
* [Stacks Project, Tag 06K4](https://stacks.math.columbia.edu/tag/06K4)
* [Stacks Project, Tag 06KB](https://stacks.math.columbia.edu/tag/06KB)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory

universe u v w

namespace GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

/-! ### Arrows of an evaluated groupoid and elements of the arrow functor -/

/-- The arrow of an evaluated groupoid with prescribed endpoints represented by an element of
the arrow functor. -/
noncomputable def arrowOfElem (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (x y : G.Evaluation T) (a : G.arrows.obj T)
    (hx : G.source.app T a = x) (hy : G.target.app T a = y) : x ⟶ y :=
  (G.evaluationArrowEquiv T x y).symm ⟨a, hx, hy⟩

/-- The element of the arrow functor represented by `arrowOfElem` is the given element. -/
@[simp]
theorem evaluationArrowEquiv_arrowOfElem (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (x y : G.Evaluation T) (a : G.arrows.obj T)
    (hx : G.source.app T a = x) (hy : G.target.app T a = y) :
    (G.evaluationArrowEquiv T x y (G.arrowOfElem T x y a hx hy)).1 = a :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- An arrow of an evaluated groupoid is the arrow represented by the element of the arrow
functor it determines. -/
theorem arrowOfElem_evaluationArrowEquiv (G : GroupoidInFunctors.{u, v, w} C) (T : C)
    (x y : G.Evaluation T) (b : x ⟶ y)
    (hx : G.source.app T (G.evaluationArrowEquiv T x y b).1 = x)
    (hy : G.target.app T (G.evaluationArrowEquiv T x y b).1 = y) :
    G.arrowOfElem T x y (G.evaluationArrowEquiv T x y b).1 hx hy = b := by
  have h : (⟨(G.evaluationArrowEquiv T x y b).1, hx, hy⟩ :
      { a : G.arrows.obj T // G.source.app T a = x ∧ G.target.app T a = y }) =
      G.evaluationArrowEquiv T x y b := Subtype.ext rfl
  rw [arrowOfElem, h, Equiv.symm_apply_apply]

/-! ### The functor to functors to groupoids -/

/-- Evaluation as a functor from groupoids in functors on `C` to functors `C ⥤ Grpd`. -/
noncomputable def evaluationGrpdFunctor :
    GroupoidInFunctors.{u, v, w} C ⥤ (C ⥤ Grpd.{w, w}) where
  obj G := AlgebraicGeometry.Stack.evaluationGroupoidFunctor G
  map F := evaluationNatTrans F
  map_id G := NatTrans.ext (funext fun T => Hom.evaluation_id G T)
  map_comp F₁ F₂ := NatTrans.ext (funext fun T => Hom.evaluation_comp F₁ F₂ T)

/-- The component at `T` of the image of a morphism under `evaluationGrpdFunctor` is its
evaluation at `T`. -/
@[simp]
theorem evaluationGrpdFunctor_map_app {G H : GroupoidInFunctors.{u, v, w} C} (F : G ⟶ H)
    (T : C) : (evaluationGrpdFunctor.map F).app T = F.evaluation T := rfl

/-- A morphism of groupoids in functors is determined by the induced morphism of the
associated functors to groupoids. -/
theorem hom_eq_of_evaluation_eq {G H : GroupoidInFunctors.{u, v, w} C} {F F' : G ⟶ H}
    (h : ∀ T : C, F.evaluation T = F'.evaluation T) : F = F' := by
  refine Hom.ext ?_ ?_
  · ext T x
    exact Functor.congr_obj (h T) x
  · ext T a
    have key : ∀ F'' : G ⟶ H, F''.mapArrows.app T a =
        (H.evaluationArrowEquiv T _ _
          ((F''.evaluation T).map (G.arrowOfElem T _ _ a rfl rfl))).1 := by
      intro F''
      rw [Hom.evaluation_map_arrow, evaluationArrowEquiv_arrowOfElem]
    change F.mapArrows.app T a = F'.mapArrows.app T a
    rw [key F, key F', h T]

/-- The functor `evaluationGrpdFunctor` is faithful. -/
instance evaluationGrpdFunctor_faithful :
    (evaluationGrpdFunctor :
      GroupoidInFunctors.{u, v, w} C ⥤ (C ⥤ Grpd.{w, w})).Faithful where
  map_injective h := hom_eq_of_evaluation_eq fun T => congrFun (congrArg NatTrans.app h) T

/-! ### Recovering a morphism of groupoids in functors -/

/-- Equal functors between evaluated groupoids send an arrow to arrows representing the same
element of the arrow functor. -/
private theorem evaluationArrowEquiv_map_congr {K L : GroupoidInFunctors.{u, v, w} C}
    {T S : C} {F F' : K.Evaluation T ⥤ L.Evaluation S} (h : F = F')
    {x y : K.Evaluation T} (b : x ⟶ y) :
    (L.evaluationArrowEquiv S (F.obj x) (F.obj y) (F.map b)).1 =
      (L.evaluationArrowEquiv S (F'.obj x) (F'.obj y) (F'.map b)).1 := by
  cases h
  rfl

section

variable {G H : GroupoidInFunctors.{u, v, w} C}
  (α : AlgebraicGeometry.Stack.evaluationGroupoidFunctor G ⟶
    AlgebraicGeometry.Stack.evaluationGroupoidFunctor H)

/-- The component of `α` at an object of the base, as a functor between the evaluated
groupoids. -/
noncomputable def natTransFunctor (T : C) : G.Evaluation T ⥤ H.Evaluation T := α.app T

/-- The element of the arrow functor of `H` representing the image under `α` of the arrow of
an evaluated groupoid of `G` represented by an element of its arrow functor. -/
noncomputable def natTransArrows (T : C) (a : G.arrows.obj T) : H.arrows.obj T :=
  (H.evaluationArrowEquiv T _ _ ((natTransFunctor α T).map (G.arrowOfElem T _ _ a rfl rfl))).1

/-- `natTransArrows α T a` is the element representing the image under `α` of the arrow
represented by `a`, for any choice of its endpoints. -/
theorem natTransArrows_eq (T : C) (x y : G.Evaluation T) (a : G.arrows.obj T)
    (hx : G.source.app T a = x) (hy : G.target.app T a = y) :
    natTransArrows α T a =
      (H.evaluationArrowEquiv T ((natTransFunctor α T).obj x) ((natTransFunctor α T).obj y)
        ((natTransFunctor α T).map (G.arrowOfElem T x y a hx hy))).1 := by
  cases hx
  cases hy
  rfl

/-- On the element representing an arrow `b`, `natTransArrows α T` gives the element
representing the image of `b` under `α`. -/
theorem natTransArrows_evaluationArrowEquiv (T : C) (x y : G.Evaluation T) (b : x ⟶ y) :
    natTransArrows α T (G.evaluationArrowEquiv T x y b).1 =
      (H.evaluationArrowEquiv T ((natTransFunctor α T).obj x) ((natTransFunctor α T).obj y)
        ((natTransFunctor α T).map b)).1 := by
  rw [natTransArrows_eq α T x y _ (G.evaluationArrowEquiv T x y b).2.1
    (G.evaluationArrowEquiv T x y b).2.2, arrowOfElem_evaluationArrowEquiv]

/-- Transport along the base category commutes with the morphism of evaluated groupoids. -/
theorem natTransArrows_naturality_aux {T S : C} (f : T ⟶ S) (x y : G.Evaluation T)
    (b : x ⟶ y) :
    (H.evaluationArrowEquiv S ((natTransFunctor α S).obj ((evaluationMap G f).obj x))
        ((natTransFunctor α S).obj ((evaluationMap G f).obj y))
        ((natTransFunctor α S).map ((evaluationMap G f).map b))).1 =
      H.arrows.map f (H.evaluationArrowEquiv T ((natTransFunctor α T).obj x)
        ((natTransFunctor α T).obj y) ((natTransFunctor α T).map b)).1 := by
  have hfun : evaluationMap G f ⋙ natTransFunctor α S =
      natTransFunctor α T ⋙ evaluationMap H f := α.naturality f
  exact (evaluationArrowEquiv_map_congr hfun b).trans
    (evaluationMap_map_arrow H f ((natTransFunctor α T).map b))

/-- The map on object functors underlying the morphism of groupoids in functors that `α`
determines. -/
noncomputable def natTransObjects : G.objects ⟶ H.objects where
  app T := ↾ fun x => (natTransFunctor α T).obj x
  naturality := by
    intro T S f
    ext x
    exact Functor.congr_obj (α.naturality f) x

/-- The map `natTransObjects α` at `T` sends an object to its image under the component of
`α` at `T`. -/
@[simp]
theorem natTransObjects_app_apply (T : C) (x : G.Evaluation T) :
    (natTransObjects α).app T x = (natTransFunctor α T).obj x := rfl

/-- The map on arrow functors underlying the morphism of groupoids in functors that `α`
determines. -/
noncomputable def natTransArrowsHom : G.arrows ⟶ H.arrows where
  app T := ↾ fun a => natTransArrows α T a
  naturality := by
    intro T S f
    ext a
    have hδ : (G.evaluationArrowEquiv S _ _
        ((evaluationMap G f).map (G.arrowOfElem T _ _ a rfl rfl))).1 = G.arrows.map f a :=
      (evaluationMap_map_arrow G f (G.arrowOfElem T _ _ a rfl rfl)).trans
        (congrArg (G.arrows.map f) (G.evaluationArrowEquiv_arrowOfElem T _ _ a rfl rfl))
    change natTransArrows α S (G.arrows.map f a) = H.arrows.map f (natTransArrows α T a)
    calc natTransArrows α S (G.arrows.map f a)
        = natTransArrows α S (G.evaluationArrowEquiv S _ _
            ((evaluationMap G f).map (G.arrowOfElem T _ _ a rfl rfl))).1 := by rw [hδ]
      _ = (H.evaluationArrowEquiv S _ _ ((natTransFunctor α S).map
            ((evaluationMap G f).map (G.arrowOfElem T _ _ a rfl rfl)))).1 :=
          natTransArrows_evaluationArrowEquiv α S _ _ _
      _ = H.arrows.map f (natTransArrows α T a) :=
          natTransArrows_naturality_aux α f _ _ (G.arrowOfElem T _ _ a rfl rfl)

/-- The map `natTransArrowsHom α` at `T` is `natTransArrows α T`. -/
@[simp]
theorem natTransArrowsHom_app_apply (T : C) (a : G.arrows.obj T) :
    (natTransArrowsHom α).app T a = natTransArrows α T a := rfl

/-- The identity arrow is preserved by the map `α` induces on arrows. -/
theorem natTransArrows_identity (T : C) (x : G.Evaluation T) :
    natTransArrows α T (G.identity T x) = H.identity T ((natTransFunctor α T).obj x) := by
  refine (natTransArrows_evaluationArrowEquiv α T x x (𝟙 x)).trans ?_
  rw [CategoryTheory.Functor.map_id]
  exact H.evaluationArrowEquiv_id T _

/-- Composition in the arrow functor is preserved by the map `α` induces on arrows. -/
theorem natTransArrows_compose (T : C) (a b : G.arrows.obj T)
    (h : G.source.app T a = G.target.app T b)
    (h' : H.source.app T (natTransArrows α T a) = H.target.app T (natTransArrows α T b)) :
    H.compose T (natTransArrows α T a) (natTransArrows α T b) h' =
      natTransArrows α T (G.compose T a b h) := by
  have hsrc : G.source.app T (G.compose T a b h) = G.source.app T b :=
    (G.pointwiseData T).source_comp a b h
  have htgt : G.target.app T (G.compose T a b h) = G.target.app T a :=
    (G.pointwiseData T).target_comp a b h
  have harrow : G.arrowOfElem T _ _ (G.compose T a b h) hsrc htgt =
      G.arrowOfElem T _ _ b rfl rfl ≫ G.arrowOfElem T _ _ a h rfl := by
    refine (G.evaluationArrowEquiv T _ _).injective (Subtype.ext ?_)
    rw [evaluationArrowEquiv_arrowOfElem, G.evaluationArrowEquiv_comp]
    exact (compose_congr G T _ _ (evaluationArrowEquiv_arrowOfElem G T _ _ a h rfl)
      (evaluationArrowEquiv_arrowOfElem G T _ _ b rfl rfl)).symm
  have hβ : (natTransFunctor α T).map (G.arrowOfElem T _ _ (G.compose T a b h) hsrc htgt) =
      (natTransFunctor α T).map (G.arrowOfElem T _ _ b rfl rfl) ≫
        (natTransFunctor α T).map (G.arrowOfElem T _ _ a h rfl) := by
    rw [harrow, CategoryTheory.Functor.map_comp]
  rw [natTransArrows_eq α T _ _ (G.compose T a b h) hsrc htgt, hβ,
    H.evaluationArrowEquiv_comp]
  exact compose_congr H T _ _ (natTransArrows_eq α T _ _ a h rfl)
    (natTransArrows_eq α T _ _ b rfl rfl)

/-- The morphism of groupoids in functors inducing a given morphism of the associated
functors to groupoids. -/
noncomputable def homOfNatTrans : G ⟶ H where
  mapObjects := natTransObjects α
  mapArrows := natTransArrowsHom α
  map_source T _a := (H.evaluationArrowEquiv T _ _ _).2.1
  map_target T _a := (H.evaluationArrowEquiv T _ _ _).2.2
  map_id T x := natTransArrows_identity α T x
  map_comp T a b h := natTransArrows_compose α T a b h _

/-- The morphism of functors to groupoids induced by `homOfNatTrans α` is `α`. -/
theorem evaluationNatTrans_homOfNatTrans : evaluationNatTrans (homOfNatTrans α) = α := by
  refine NatTrans.ext (funext fun T => ?_)
  change Hom.evaluation (homOfNatTrans α) T = natTransFunctor α T
  refine CategoryTheory.Functor.ext (fun x => rfl) fun x y b =>
    hom_eq_transport H T rfl rfl _ _ ?_
  rw [Hom.evaluation_map_arrow]
  change natTransArrows α T (G.evaluationArrowEquiv T x y b).1 = _
  exact natTransArrows_evaluationArrowEquiv α T x y b

end

/-- The functor `evaluationGrpdFunctor` is full. -/
instance evaluationGrpdFunctor_full :
    (evaluationGrpdFunctor :
      GroupoidInFunctors.{u, v, w} C ⥤ (C ⥤ Grpd.{w, w})).Full where
  map_surjective α := ⟨homOfNatTrans α, evaluationNatTrans_homOfNatTrans α⟩

/-! ### The groupoid in functors determined by a functor to groupoids -/

section

variable (𝒢 : C ⥤ Grpd.{w, w})

/-- The functor of objects of the groupoid in functors that a functor to groupoids
determines. -/
@[implicit_reducible]
def grpdObjects : C ⥤ Type w where
  obj T := ↥(𝒢.obj T)
  map f := ↾ fun x => (𝒢.map f).obj x
  map_id T := ConcreteCategory.hom_ext _ _ fun x => Functor.congr_obj (𝒢.map_id T) x
  map_comp f g := ConcreteCategory.hom_ext _ _ fun x => Functor.congr_obj (𝒢.map_comp f g) x

/-- The functor of arrows of the groupoid in functors that a functor to groupoids
determines. -/
@[implicit_reducible]
def grpdArrows : C ⥤ Type w where
  obj T := Σ x : ↥(𝒢.obj T), Σ y : ↥(𝒢.obj T), (x ⟶ y)
  map f := ↾ fun a => ⟨(𝒢.map f).obj a.1, (𝒢.map f).obj a.2.1, (𝒢.map f).map a.2.2⟩
  map_id T := ConcreteCategory.hom_ext _ _ fun a =>
    congrArg (fun F : 𝒢.obj T ⟶ 𝒢.obj T =>
      (⟨F.obj a.1, F.obj a.2.1, F.map a.2.2⟩ :
        Σ x : ↥(𝒢.obj T), Σ y : ↥(𝒢.obj T), (x ⟶ y))) (𝒢.map_id T)
  map_comp {X _Y Z} f g := ConcreteCategory.hom_ext _ _ fun a =>
    congrArg (fun F : 𝒢.obj X ⟶ 𝒢.obj Z =>
      (⟨F.obj a.1, F.obj a.2.1, F.map a.2.2⟩ :
        Σ x : ↥(𝒢.obj Z), Σ y : ↥(𝒢.obj Z), (x ⟶ y))) (𝒢.map_comp f g)

/-- The source of an arrow of a functor to groupoids. -/
def grpdSource : grpdArrows 𝒢 ⟶ grpdObjects 𝒢 where
  app _T := ↾ fun a => a.1
  naturality _ _ _ := rfl

/-- The target of an arrow of a functor to groupoids. -/
def grpdTarget : grpdArrows 𝒢 ⟶ grpdObjects 𝒢 where
  app _T := ↾ fun a => a.2.1
  naturality _ _ _ := rfl

/-- The composability condition on a pair of arrows of a functor to groupoids. -/
theorem grpdComposable {T : C}
    (p : (composableArrows (grpdObjects 𝒢) (grpdArrows 𝒢) (grpdSource 𝒢)
      (grpdTarget 𝒢)).obj T) : p.1.2.2.1 = p.1.1.1 := p.2.symm

/-- Composition of composable arrows of a functor to groupoids. -/
noncomputable def grpdComp :
    composableArrows (grpdObjects 𝒢) (grpdArrows 𝒢) (grpdSource 𝒢) (grpdTarget 𝒢) ⟶
      grpdArrows 𝒢 where
  app T := ↾ fun p => ⟨p.1.2.1, p.1.1.2.1,
    p.1.2.2.2 ≫ eqToHom (grpdComposable 𝒢 p) ≫ p.1.1.2.2⟩
  naturality {T S} f := by
    refine ConcreteCategory.hom_ext _ _ fun p => ?_
    have h : (𝒢.map f).map (p.1.2.2.2 ≫ eqToHom (grpdComposable 𝒢 p) ≫ p.1.1.2.2) =
        (𝒢.map f).map p.1.2.2.2 ≫
          eqToHom (congrArg (𝒢.map f).obj (grpdComposable 𝒢 p)) ≫
          (𝒢.map f).map p.1.1.2.2 := by
      rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, eqToHom_map]
    exact congrArg (fun b : (𝒢.map f).obj p.1.2.1 ⟶ (𝒢.map f).obj p.1.1.2.1 =>
      (⟨(𝒢.map f).obj p.1.2.1, (𝒢.map f).obj p.1.1.2.1, b⟩ :
        Σ x : ↥(𝒢.obj S), Σ y : ↥(𝒢.obj S), (x ⟶ y))) h.symm

/-- Arrows of a value of a functor to groupoids are the triples of two objects and an arrow
between them with the prescribed endpoints. -/
def grpdArrowEquiv (T : C) (x y : ↥(𝒢.obj T)) :
    (x ⟶ y) ≃ { a : (grpdArrows 𝒢).obj T //
      (grpdSource 𝒢).app T a = x ∧ (grpdTarget 𝒢).app T a = y } where
  toFun b := ⟨⟨x, y, b⟩, rfl, rfl⟩
  invFun a := eqToHom a.2.1.symm ≫ a.1.2.2 ≫ eqToHom a.2.2
  left_inv b := (Category.id_comp (b ≫ 𝟙 y)).trans (Category.comp_id b)
  right_inv a := by
    obtain ⟨⟨x', y', b'⟩, hx, hy⟩ := a
    cases hx
    cases hy
    exact Subtype.ext (congrArg (fun c : x' ⟶ y' =>
      (⟨x', y', c⟩ : Σ a : ↥(𝒢.obj T), Σ b : ↥(𝒢.obj T), (a ⟶ b)))
      ((Category.id_comp (b' ≫ 𝟙 y')).trans (Category.comp_id b')))

/-- Composition of arrows of a functor to groupoids, read on the arrow functor. -/
theorem grpdComp_app (T : C) (x y z : ↥(𝒢.obj T)) (g : x ⟶ y) (f : y ⟶ z) :
    (grpdComp 𝒢).app T ⟨((grpdArrowEquiv 𝒢 T y z f).1, (grpdArrowEquiv 𝒢 T x y g).1),
        (grpdArrowEquiv 𝒢 T y z f).2.1.trans (grpdArrowEquiv 𝒢 T x y g).2.2.symm⟩ =
      (grpdArrowEquiv 𝒢 T x z (g ≫ f)).1 :=
  congrArg (fun c : x ⟶ z =>
    (⟨x, z, c⟩ : Σ a : ↥(𝒢.obj T), Σ b : ↥(𝒢.obj T), (a ⟶ b)))
    (congrArg (fun c : y ⟶ z => g ≫ c) (Category.id_comp f))

/-- The pointwise groupoid structure of the groupoid in functors that a functor to groupoids
determines. -/
noncomputable def grpdPointwiseGroupoid (T : C) :
    PointwiseGroupoid ((grpdSource 𝒢).app T) ((grpdTarget 𝒢).app T)
      (fun p => (grpdComp 𝒢).app T p) where
  groupoid := Grpd.str' (𝒢.obj T)
  arrowEquiv := grpdArrowEquiv 𝒢 T
  comp_eq g f := (grpdComp_app 𝒢 T _ _ _ g f).symm

/-- The groupoid in functors determined by a functor to groupoids. -/
noncomputable def ofGrpdFunctor : GroupoidInFunctors.{u, v, w} C where
  objects := grpdObjects 𝒢
  arrows := grpdArrows 𝒢
  source := grpdSource 𝒢
  target := grpdTarget 𝒢
  comp := grpdComp 𝒢
  pointwiseGroupoid T := ⟨grpdPointwiseGroupoid 𝒢 T⟩

end

/-! ### The functor to groupoids is recovered up to isomorphism -/

section

variable (𝒢 : C ⥤ Grpd.{w, w})

/-- An idempotent arrow of a groupoid is an identity. -/
private theorem eq_id_of_comp_self {X : Type w} [Groupoid.{w} X] {x : X} (α : x ⟶ x)
    (h : α ≫ α = α) : α = 𝟙 x :=
  (cancel_epi α).1 (h.trans (Category.comp_id α).symm)

/-- Arrows of the evaluated groupoid of the groupoid in functors built from a functor to
groupoids. -/
abbrev GrpdEvalHom (T : C) (x y : ↥(𝒢.obj T)) :=
  @Quiver.Hom ((ofGrpdFunctor 𝒢).Evaluation T)
    ((ofGrpdFunctor 𝒢).evaluationGroupoid T).toCategory.toQuiver x y

/-- The identity arrow of the evaluated groupoid of `ofGrpdFunctor 𝒢`. -/
noncomputable def grpdEvalId (T : C) (x : ↥(𝒢.obj T)) : GrpdEvalHom 𝒢 T x x :=
  @CategoryStruct.id ((ofGrpdFunctor 𝒢).Evaluation T)
    ((ofGrpdFunctor 𝒢).evaluationGroupoid T).toCategory.toCategoryStruct x

/-- An arrow of an evaluated groupoid of `ofGrpdFunctor 𝒢`, read as an arrow of `𝒢`. -/
noncomputable def grpdEvalHom (T : C) (x y : ↥(𝒢.obj T)) (b : GrpdEvalHom 𝒢 T x y) : x ⟶ y :=
  (grpdArrowEquiv 𝒢 T x y).symm ((ofGrpdFunctor 𝒢).evaluationArrowEquiv T x y b)

/-- An arrow of `𝒢`, read as an arrow of an evaluated groupoid of `ofGrpdFunctor 𝒢`. -/
noncomputable def grpdEvalInv (T : C) (x y : ↥(𝒢.obj T)) (b : x ⟶ y) : GrpdEvalHom 𝒢 T x y :=
  ((ofGrpdFunctor 𝒢).evaluationArrowEquiv T x y).symm (grpdArrowEquiv 𝒢 T x y b)

/-- An arrow of an evaluated groupoid of `ofGrpdFunctor 𝒢` and its reading `grpdEvalHom` as
an arrow of `𝒢` represent the same element of the arrow functor. -/
theorem grpdArrowEquiv_grpdEvalHom (T : C) (x y : ↥(𝒢.obj T)) (b : GrpdEvalHom 𝒢 T x y) :
    (grpdArrowEquiv 𝒢 T x y (grpdEvalHom 𝒢 T x y b)).1 =
      ((ofGrpdFunctor 𝒢).evaluationArrowEquiv T x y b).1 :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- An arrow of `𝒢` and its reading `grpdEvalInv` as an arrow of an evaluated groupoid of
`ofGrpdFunctor 𝒢` represent the same element of the arrow functor. -/
theorem evaluationArrowEquiv_grpdEvalInv (T : C) (x y : ↥(𝒢.obj T)) (b : x ⟶ y) :
    ((ofGrpdFunctor 𝒢).evaluationArrowEquiv T x y (grpdEvalInv 𝒢 T x y b)).1 =
      (grpdArrowEquiv 𝒢 T x y b).1 :=
  congrArg Subtype.val (Equiv.apply_symm_apply _ _)

/-- `grpdEvalInv` is a left inverse of `grpdEvalHom`. -/
theorem grpdEvalInv_grpdEvalHom (T : C) (x y : ↥(𝒢.obj T)) (b : GrpdEvalHom 𝒢 T x y) :
    grpdEvalInv 𝒢 T x y (grpdEvalHom 𝒢 T x y b) = b :=
  (congrArg (fun a => ((ofGrpdFunctor 𝒢).evaluationArrowEquiv T x y).symm a)
      (Equiv.apply_symm_apply (grpdArrowEquiv 𝒢 T x y)
        ((ofGrpdFunctor 𝒢).evaluationArrowEquiv T x y b))).trans
    (Equiv.symm_apply_apply ((ofGrpdFunctor 𝒢).evaluationArrowEquiv T x y) b)

/-- `grpdEvalHom` is a left inverse of `grpdEvalInv`. -/
theorem grpdEvalHom_grpdEvalInv (T : C) (x y : ↥(𝒢.obj T)) (b : x ⟶ y) :
    grpdEvalHom 𝒢 T x y (grpdEvalInv 𝒢 T x y b) = b :=
  (congrArg (fun a => (grpdArrowEquiv 𝒢 T x y).symm a)
      (Equiv.apply_symm_apply ((ofGrpdFunctor 𝒢).evaluationArrowEquiv T x y)
        (grpdArrowEquiv 𝒢 T x y b))).trans
    (Equiv.symm_apply_apply (grpdArrowEquiv 𝒢 T x y) b)

/-- `grpdEvalHom` preserves composition. -/
theorem grpdEvalHom_comp (T : C) (x y z : ↥(𝒢.obj T)) (g : GrpdEvalHom 𝒢 T x y)
    (f : GrpdEvalHom 𝒢 T y z) :
    grpdEvalHom 𝒢 T x z (g ≫ f) = grpdEvalHom 𝒢 T x y g ≫ grpdEvalHom 𝒢 T y z f := by
  refine (grpdArrowEquiv 𝒢 T x z).injective (Subtype.ext ?_)
  refine Eq.trans (grpdArrowEquiv_grpdEvalHom 𝒢 T x z (g ≫ f)) ?_
  refine Eq.trans ((ofGrpdFunctor 𝒢).evaluationArrowEquiv_comp T g f) ?_
  refine Eq.trans ?_ (grpdComp_app 𝒢 T x y z (grpdEvalHom 𝒢 T x y g)
    (grpdEvalHom 𝒢 T y z f))
  exact congrArg ((grpdComp 𝒢).app T) (Subtype.ext (Prod.ext
    (grpdArrowEquiv_grpdEvalHom 𝒢 T y z f).symm
    (grpdArrowEquiv_grpdEvalHom 𝒢 T x y g).symm))

/-- `grpdEvalInv` preserves composition. -/
theorem grpdEvalInv_comp (T : C) (x y z : ↥(𝒢.obj T)) (g : x ⟶ y) (f : y ⟶ z) :
    grpdEvalInv 𝒢 T x z (g ≫ f) = grpdEvalInv 𝒢 T x y g ≫ grpdEvalInv 𝒢 T y z f := by
  refine ((ofGrpdFunctor 𝒢).evaluationArrowEquiv T x z).injective (Subtype.ext ?_)
  refine Eq.trans (evaluationArrowEquiv_grpdEvalInv 𝒢 T x z (g ≫ f)) ?_
  refine Eq.trans (grpdComp_app 𝒢 T x y z g f).symm ?_
  refine Eq.trans ?_ ((ofGrpdFunctor 𝒢).evaluationArrowEquiv_comp T
    (grpdEvalInv 𝒢 T x y g) (grpdEvalInv 𝒢 T y z f)).symm
  exact congrArg ((grpdComp 𝒢).app T) (Subtype.ext (Prod.ext
    (evaluationArrowEquiv_grpdEvalInv 𝒢 T y z f).symm
    (evaluationArrowEquiv_grpdEvalInv 𝒢 T x y g).symm))

/-- `grpdEvalHom` preserves identities. -/
theorem grpdEvalHom_id (T : C) (x : ↥(𝒢.obj T)) :
    grpdEvalHom 𝒢 T x x (grpdEvalId 𝒢 T x) = 𝟙 x := by
  refine eq_id_of_comp_self (X := ↥(𝒢.obj T)) _ ?_
  refine Eq.trans (grpdEvalHom_comp 𝒢 T x x x (grpdEvalId 𝒢 T x) (grpdEvalId 𝒢 T x)).symm ?_
  exact congrArg (grpdEvalHom 𝒢 T x x) (Category.id_comp (grpdEvalId 𝒢 T x))

/-- `grpdEvalInv` preserves identities. -/
theorem grpdEvalInv_id (T : C) (x : ↥(𝒢.obj T)) :
    grpdEvalInv 𝒢 T x x (𝟙 x) = grpdEvalId 𝒢 T x := by
  refine eq_id_of_comp_self (X := (ofGrpdFunctor 𝒢).Evaluation T) _ ?_
  refine Eq.trans (grpdEvalInv_comp 𝒢 T x x x (𝟙 x) (𝟙 x)).symm ?_
  exact congrArg (grpdEvalInv 𝒢 T x x) (Category.id_comp (𝟙 x))

/-- The evaluated groupoid of `ofGrpdFunctor 𝒢` mapped to the value of `𝒢`. -/
noncomputable def evalToGrpd (T : C) : (ofGrpdFunctor 𝒢).Evaluation T ⥤ ↥(𝒢.obj T) where
  obj x := x
  map {x y} b := grpdEvalHom 𝒢 T x y b
  map_id x := grpdEvalHom_id 𝒢 T x
  map_comp f g := grpdEvalHom_comp 𝒢 T _ _ _ f g

/-- The value of `𝒢` mapped to the evaluated groupoid of `ofGrpdFunctor 𝒢`. -/
noncomputable def grpdToEval (T : C) : ↥(𝒢.obj T) ⥤ (ofGrpdFunctor 𝒢).Evaluation T where
  obj x := x
  map {x y} b := grpdEvalInv 𝒢 T x y b
  map_id x := grpdEvalInv_id 𝒢 T x
  map_comp f g := grpdEvalInv_comp 𝒢 T _ _ _ f g

/-- `grpdToEval 𝒢 T` is a right inverse of `evalToGrpd 𝒢 T`. -/
theorem evalToGrpd_comp_grpdToEval (T : C) :
    evalToGrpd 𝒢 T ⋙ grpdToEval 𝒢 T =
      CategoryTheory.Functor.id ((ofGrpdFunctor 𝒢).Evaluation T) := by
  refine CategoryTheory.Functor.ext (fun x => rfl) fun x y b => ?_
  exact (grpdEvalInv_grpdEvalHom 𝒢 T x y b).trans
    ((Category.id_comp (b ≫ 𝟙 y)).trans (Category.comp_id b)).symm

/-- `evalToGrpd 𝒢 T` is a right inverse of `grpdToEval 𝒢 T`. -/
theorem grpdToEval_comp_evalToGrpd (T : C) :
    grpdToEval 𝒢 T ⋙ evalToGrpd 𝒢 T = CategoryTheory.Functor.id ↥(𝒢.obj T) := by
  refine CategoryTheory.Functor.ext (fun x => rfl) fun x y b => ?_
  exact (grpdEvalHom_grpdEvalInv 𝒢 T x y b).trans
    ((Category.id_comp (b ≫ 𝟙 y)).trans (Category.comp_id b)).symm

/-- The evaluated groupoid of `ofGrpdFunctor 𝒢` is isomorphic to the value of `𝒢`. -/
noncomputable def evaluationIsoApp (T : C) :
    Grpd.of ((ofGrpdFunctor 𝒢).Evaluation T) ≅ 𝒢.obj T where
  hom := evalToGrpd 𝒢 T
  inv := grpdToEval 𝒢 T
  hom_inv_id := evalToGrpd_comp_grpdToEval 𝒢 T
  inv_hom_id := grpdToEval_comp_evalToGrpd 𝒢 T

/-- `grpdEvalHom` intertwines transport along `f` in `ofGrpdFunctor 𝒢` with `𝒢.map f`. -/
theorem grpdEvalHom_evaluationMap {T S : C} (f : T ⟶ S) (x y : ↥(𝒢.obj T))
    (b : GrpdEvalHom 𝒢 T x y) :
    grpdEvalHom 𝒢 S ((grpdObjects 𝒢).map f x) ((grpdObjects 𝒢).map f y)
        ((evaluationMap (ofGrpdFunctor 𝒢) f).map b) =
      (𝒢.map f).map (grpdEvalHom 𝒢 T x y b) := by
  refine (grpdArrowEquiv 𝒢 S _ _).injective (Subtype.ext ?_)
  refine Eq.trans (grpdArrowEquiv_grpdEvalHom 𝒢 S _ _ _) ?_
  refine Eq.trans (evaluationMap_map_arrow (ofGrpdFunctor 𝒢) f b) ?_
  exact congrArg (fun a => (grpdArrows 𝒢).map f a)
    (grpdArrowEquiv_grpdEvalHom 𝒢 T x y b).symm

/-- The functors `evalToGrpd 𝒢 T` are natural in `T`. -/
theorem evalToGrpd_naturality {T S : C} (f : T ⟶ S) :
    evaluationMap (ofGrpdFunctor 𝒢) f ⋙ evalToGrpd 𝒢 S = evalToGrpd 𝒢 T ⋙ 𝒢.map f := by
  refine CategoryTheory.Functor.ext (fun x => rfl) fun x y b => ?_
  refine Eq.trans (grpdEvalHom_evaluationMap 𝒢 f x y b) ?_
  exact ((Category.id_comp ((𝒢.map f).map (grpdEvalHom 𝒢 T x y b) ≫
    𝟙 ((𝒢.map f).obj y))).trans (Category.comp_id _)).symm

/-- The functor to groupoids built from `ofGrpdFunctor 𝒢` is isomorphic to `𝒢`. -/
noncomputable def evaluationIso :
    AlgebraicGeometry.Stack.evaluationGroupoidFunctor (ofGrpdFunctor 𝒢) ≅ 𝒢 :=
  NatIso.ofComponents (evaluationIsoApp 𝒢) fun f => evalToGrpd_naturality 𝒢 f

end

/-- The functor `evaluationGrpdFunctor` is essentially surjective. -/
instance evaluationGrpdFunctor_essSurj :
    (evaluationGrpdFunctor :
      GroupoidInFunctors.{u, v, w} C ⥤ (C ⥤ Grpd.{w, w})).EssSurj where
  mem_essImage 𝒢 := ⟨ofGrpdFunctor 𝒢, ⟨evaluationIso 𝒢⟩⟩

/-- The functor `evaluationGrpdFunctor` is an equivalence of categories. -/
instance evaluationGrpdFunctor_isEquivalence :
    (evaluationGrpdFunctor :
      GroupoidInFunctors.{u, v, w} C ⥤ (C ⥤ Grpd.{w, w})).IsEquivalence where

/-- A groupoid in functors on `C` is the same data as a functor `C ⥤ Grpd`, and a morphism of
groupoids in functors is the same data as a morphism of the associated functors: evaluation is
an equivalence of categories. -/
@[stacks 06K4]
noncomputable def evaluationEquivalence :
    GroupoidInFunctors.{u, v, w} C ≌ (C ⥤ Grpd.{w, w}) :=
  (evaluationGrpdFunctor : GroupoidInFunctors.{u, v, w} C ⥤ (C ⥤ Grpd.{w, w})).asEquivalence

end GroupoidInFunctors


end

end Deformation
