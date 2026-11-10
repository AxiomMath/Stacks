module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Submersive
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.SubmersiveAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjective

/-!
# Testing a relative topological property on all base changes (Stacks 0CHX, 0CI1, 0CI6)

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S` representable by algebraic spaces,
and let `P` be one of submersiveness, injectivity, or being a homeomorphism, read on the
topological spaces of points of Tags 04XG and 04XL. Then `f` is universally `P` in the relative
sense of Tag 04XB — every algebraic space representing a base change of `f` along a scheme-valued
point of `𝒴` has universally `P` structural morphism — exactly when, for every algebraic stack
`𝒵` over `𝒴`, the map `|𝒵 ×_𝒴 𝒳| → |𝒵|` is `P`.

## Main definitions

* `AlgebraicGeometry.Stack.PointMapProperty`: a property of maps between the point spaces of this
  library, all of which live in `Type (u + 1)`.
* `AlgebraicGeometry.Stack.IsConjInvariant` and `AlgebraicGeometry.Stack.IsDescendable`: the two
  closure conditions on such a property that the equivalence needs.
* `AlgebraicGeometry.Stack.RelativeUniversally`: the relative property of Tag 04XB at
  universally `Q`, in the unrolled shape of Tag 03YK.

## Main results

* `AlgebraicGeometry.Stack.relative_iff_forall_pointsMap_fst`: the equivalence, for an abstract
  `Q` satisfying the two closure conditions.
* `AlgebraicGeometry.Stack.isConjInvariant_quotientMapProperty` and its five siblings:
  submersiveness, injectivity and being a homeomorphism satisfy both closure conditions.

## Implementation notes

Submersiveness, injectivity and being a homeomorphism are the three cases needed for Tags 0CHX,
0CI1 and 0CI6, which are proved from this file in
`StacksFrontier.AlgebraicGeometry.Stacks.UniversallySubmersiveCriterion`,
`StacksFrontier.AlgebraicGeometry.Stacks.UniversallyInjectiveCriterion` and
`StacksFrontier.AlgebraicGeometry.Stacks.UniversalHomeomorphismCriterion`.

The route is the one of **Stacks 0512**, the universally closed member of the same family: the
forward direction uses the chart of a presentation of `𝒵` read on the slice of the site
(`AlgebraicGeometry.Stack.exists_sliceChart_isOpenMap_surjective`), the first-factor cancellation
of Tag 02XD, and Tag 04XH for surjectivity onto the topological fibre product; the converse uses
that a morphism of algebraic spaces to `h_U` is induced by a 1-morphism out of the category of
elements (Tag 04SW) and Tag 04SD for the representing presheaf of an iterated 2-fibre product.

The relative side is stated in the unrolled form of Tag 04XB, as
`AlgebraicGeometry.Stack.UniversallyClosed` is: `AlgebraicGeometry.Stack.HasRelativeProperty`
carries an fppf-locality instance argument for the tested property, which is Tag 0421 for
universal closedness and is not in the library for any of the three properties here.

## References

* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04XG](https://stacks.math.columbia.edu/tag/04XG)
* [Stacks Project, Tag 04XH](https://stacks.math.columbia.edu/tag/04XH)
* [Stacks Project, Tag 04XL](https://stacks.math.columbia.edu/tag/04XL)
* [Stacks Project, Tag 0512](https://stacks.math.columbia.edu/tag/0512)
* [Stacks Project, Tag 0CHX](https://stacks.math.columbia.edu/tag/0CHX)
* [Stacks Project, Tag 0CI1](https://stacks.math.columbia.edu/tag/0CI1)
* [Stacks Project, Tag 0CI6](https://stacks.math.columbia.edu/tag/0CI6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u w

namespace AlgebraicGeometry.Stack

/-! ### Topological preliminaries -/

section Topology

variable {A A' C C' : Type*} [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace C]
  [TopologicalSpace C']

/-- Each map of a commutative square whose horizontal maps are homeomorphisms is the conjugate of
the other by them. -/
private theorem eq_comp_comp_of_isHomeomorph {p : A → C} {q : A' → C'} {σ : A → A'}
    {τ : C → C'} (hσ : IsHomeomorph σ) (hτ : IsHomeomorph τ) (hcomm : ∀ x, τ (p x) = q (σ x)) :
    p = (IsHomeomorph.homeomorph τ hτ).symm ∘ q ∘ σ ∧
      q = τ ∘ p ∘ (IsHomeomorph.homeomorph σ hσ).symm := by
  constructor
  · funext x
    have h : (IsHomeomorph.homeomorph τ hτ).symm ((IsHomeomorph.homeomorph τ hτ) (p x)) =
        (IsHomeomorph.homeomorph τ hτ).symm (q (σ x)) := congrArg _ (hcomm x)
    rwa [(IsHomeomorph.homeomorph τ hτ).symm_apply_apply] at h
  · funext y
    have h := hcomm ((IsHomeomorph.homeomorph σ hσ).symm y)
    rw [show σ _ = y from (IsHomeomorph.homeomorph σ hσ).apply_symm_apply y] at h
    exact h.symm

/-- Injectivity transfers across a commutative square whose two horizontal maps are
homeomorphisms. -/
private theorem injective_iff_of_isHomeomorph {p : A → C} {q : A' → C'} {σ : A → A'} {τ : C → C'}
    (hσ : IsHomeomorph σ) (hτ : IsHomeomorph τ) (hcomm : ∀ x, τ (p x) = q (σ x)) :
    Function.Injective p ↔ Function.Injective q := by
  constructor
  · intro hp
    rw [(eq_comp_comp_of_isHomeomorph hσ hτ hcomm).2]
    exact hτ.injective.comp (hp.comp (IsHomeomorph.homeomorph σ hσ).symm.injective)
  · intro hq
    rw [(eq_comp_comp_of_isHomeomorph hσ hτ hcomm).1]
    exact (IsHomeomorph.homeomorph τ hτ).symm.injective.comp (hq.comp hσ.injective)

/-- The quotient-map condition transfers across a commutative square whose two horizontal maps
are homeomorphisms. -/
private theorem isQuotientMap_iff_of_isHomeomorph {p : A → C} {q : A' → C'} {σ : A → A'}
    {τ : C → C'} (hσ : IsHomeomorph σ) (hτ : IsHomeomorph τ) (hcomm : ∀ x, τ (p x) = q (σ x)) :
    Topology.IsQuotientMap p ↔ Topology.IsQuotientMap q := by
  constructor
  · intro hp
    rw [(eq_comp_comp_of_isHomeomorph hσ hτ hcomm).2]
    exact (IsHomeomorph.homeomorph τ hτ).isQuotientMap.comp
      (hp.comp (IsHomeomorph.homeomorph σ hσ).symm.isQuotientMap)
  · intro hq
    rw [(eq_comp_comp_of_isHomeomorph hσ hτ hcomm).1]
    exact (IsHomeomorph.homeomorph τ hτ).symm.isQuotientMap.comp
      (hq.comp (IsHomeomorph.homeomorph σ hσ).isQuotientMap)

/-- Being a homeomorphism transfers across a commutative square whose two horizontal maps are
homeomorphisms. -/
private theorem isHomeomorph_iff_of_isHomeomorph {p : A → C} {q : A' → C'} {σ : A → A'}
    {τ : C → C'} (hσ : IsHomeomorph σ) (hτ : IsHomeomorph τ) (hcomm : ∀ x, τ (p x) = q (σ x)) :
    IsHomeomorph p ↔ IsHomeomorph q := by
  constructor
  · intro hp
    rw [(eq_comp_comp_of_isHomeomorph hσ hτ hcomm).2]
    exact hτ.comp (hp.comp (IsHomeomorph.homeomorph σ hσ).symm.isHomeomorph)
  · intro hq
    rw [(eq_comp_comp_of_isHomeomorph hσ hτ hcomm).1]
    exact (IsHomeomorph.homeomorph τ hτ).symm.isHomeomorph.comp (hq.comp hσ)

omit [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace C] [TopologicalSpace C'] in
/-- Surjectivity descends along a surjection of the targets: in a commutative square
`b ∘ p = q ∘ a` with `b` surjective, `q` is surjective as soon as `p` is. -/
private theorem surjective_of_surjective_comm_of_surjective {p : A → A'} {a : A → C}
    {q : C → C'} {b : A' → C'} (hcomm : ∀ x, b (p x) = q (a x)) (hbsurj : Function.Surjective b)
    (hp : Function.Surjective p) : Function.Surjective q := by
  intro d
  obtain ⟨y, hy⟩ := hbsurj d
  obtain ⟨x, hx⟩ := hp y
  exact ⟨a x, by rw [← hcomm x, hx, hy]⟩

omit [TopologicalSpace A] [TopologicalSpace A'] [TopologicalSpace C] [TopologicalSpace C'] in
/-- Injectivity descends along a surjection of the targets: in a commutative square
`b ∘ p = q ∘ a` with `b` surjective and the canonical map `A → A' ×_{C'} C` surjective, `q` is
injective as soon as `p` is. -/
private theorem injective_of_injective_comm_of_surjective {p : A → A'} {a : A → C} {q : C → C'}
    {b : A' → C'} (_hcomm : ∀ x, b (p x) = q (a x)) (hbsurj : Function.Surjective b)
    (hsurj : ∀ (y : A') (c : C), b y = q c → ∃ x, p x = y ∧ a x = c)
    (hp : Function.Injective p) : Function.Injective q := by
  intro c₁ c₂ h
  obtain ⟨y, hy⟩ := hbsurj (q c₁)
  obtain ⟨x₁, hx₁p, hx₁a⟩ := hsurj y c₁ hy
  obtain ⟨x₂, hx₂p, hx₂a⟩ := hsurj y c₂ (hy.trans h)
  rw [← hx₁a, ← hx₂a, hp (hx₁p.trans hx₂p.symm)]

/-- The quotient-map condition descends along an open continuous surjection of the targets: in a
commutative square `b ∘ p = q ∘ a` with `b` open, continuous and surjective, `a` continuous and
`q` continuous, `q` is a quotient map as soon as `p` is. -/
private theorem isQuotientMap_of_isQuotientMap_comm_of_isOpenMap_surjective {p : A → A'}
    {a : A → C} {q : C → C'} {b : A' → C'} (hcomm : ∀ x, b (p x) = q (a x)) (hb : IsOpenMap b)
    (hbsurj : Function.Surjective b) (hbcont : Continuous b) (ha : Continuous a)
    (hq : Continuous q) (hp : Topology.IsQuotientMap p) : Topology.IsQuotientMap q := by
  refine Topology.IsQuotientMap.of_comp ha hq ?_
  rw [show q ∘ a = b ∘ p from funext fun x => (hcomm x).symm]
  exact (hb.isQuotientMap hbcont hbsurj).comp hp

/-- Being a homeomorphism descends along an open continuous surjection of the targets: in a
commutative square `b ∘ p = q ∘ a` with `b` open, continuous and surjective, `a` continuous,
`q` continuous and the canonical map `A → A' ×_{C'} C` surjective, `q` is a homeomorphism as
soon as `p` is. -/
private theorem isHomeomorph_of_isHomeomorph_comm_of_isOpenMap_surjective {p : A → A'}
    {a : A → C} {q : C → C'} {b : A' → C'} (hcomm : ∀ x, b (p x) = q (a x)) (hb : IsOpenMap b)
    (hbsurj : Function.Surjective b) (ha : Continuous a) (hq : Continuous q)
    (hsurj : ∀ (y : A') (c : C), b y = q c → ∃ x, p x = y ∧ a x = c) (hp : IsHomeomorph p) :
    IsHomeomorph q :=
  ⟨hq, isOpenMap_of_isOpenMap_comm_of_isOpenMap_surjective hcomm hb hbsurj ha hsurj hp.isOpenMap,
    injective_of_injective_comm_of_surjective hcomm hbsurj hsurj hp.injective,
    surjective_of_surjective_comm_of_surjective hcomm hbsurj hp.surjective⟩

end Topology

/-! ### An abstract property of maps on point spaces -/

section Abstract

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for pullbacks of presheaves on the big fppf site times out otherwise
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_UniversalTopologicalProperties :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

local instance (priority := high) hasPullback_presheaf_UniversalTopologicalProperties
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- A property of maps between the point spaces of this library, which all live in
`Type (u + 1)`. -/
abbrev PointMapProperty : Type (u + 2) :=
  ∀ X Y : Type (u + 1), TopologicalSpace X → TopologicalSpace Y → (X → Y) → Prop

/-- Invariance of a property of maps on point spaces under conjugating by homeomorphisms. -/
abbrev IsConjInvariant (Q : PointMapProperty.{u}) : Prop :=
  ∀ (A C A' C' : Type (u + 1)) (tA : TopologicalSpace A) (tC : TopologicalSpace C)
    (tA' : TopologicalSpace A') (tC' : TopologicalSpace C') (p : A → C) (q : A' → C')
    (σ : A → A') (τ : C → C'), @IsHomeomorph _ _ tA tA' σ → @IsHomeomorph _ _ tC tC' τ →
    (∀ x, τ (p x) = q (σ x)) → (Q A C tA tC p ↔ Q A' C' tA' tC' q)

/-- Descent of a property of maps on point spaces along an open continuous surjection of the
targets, across a commutative square whose canonical map to the topological fibre product is
surjective. -/
abbrev IsDescendable (Q : PointMapProperty.{u}) : Prop :=
  ∀ (A A' C C' : Type (u + 1)) (tA : TopologicalSpace A) (tA' : TopologicalSpace A')
    (tC : TopologicalSpace C) (tC' : TopologicalSpace C') (p : A → A') (a : A → C) (q : C → C')
    (b : A' → C'), (∀ x, b (p x) = q (a x)) → @IsOpenMap _ _ tA' tC' b →
    Function.Surjective b → @Continuous _ _ tA' tC' b → @Continuous _ _ tA tC a →
    @Continuous _ _ tC tC' q → (∀ (y : A') (c : C), b y = q c → ∃ x, p x = y ∧ a x = c) →
    Q A A' tA tA' p → Q C C' tC tC' q

/-- The underlying isomorphism of presheaves of an isomorphism of algebraic spaces over `S`. -/
private def isoObj {X Y : AlgebraicSpaces B S hS} (e : X ≅ Y) : X.obj ≅ Y.obj where
  hom := e.hom.hom
  inv := e.inv.hom
  hom_inv_id := congrArg (fun k : X ⟶ X => k.hom) e.hom_inv_id
  inv_hom_id := congrArg (fun k : Y ⟶ Y => k.hom) e.inv_hom_id

/-- The property of a morphism of algebraic spaces over `S` that its map on the points of
Tag 03BX has `Q`. -/
abbrev pointMapProperty (Q : PointMapProperty.{u}) :
    MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _X _Y a => Q (Space.points B S hS _X.obj) (Space.points B S hS _Y.obj)
    (Space.pointTopology B S hS _X.obj) (Space.pointTopology B S hS _Y.obj)
    (Space.pointsMap B S hS _X.obj a.hom)

/-- A conjugation-invariant property of maps on point spaces gives a property of morphisms of
algebraic spaces over `S` which respects isomorphisms, the map on points of an isomorphism being
a homeomorphism. -/
theorem respectsIso_pointMapProperty (Q : PointMapProperty.{u})
    (hQ : IsConjInvariant.{u} Q) :
    MorphismProperty.RespectsIso (pointMapProperty B S hS Q) := by
  refine MorphismProperty.RespectsIso.mk _ ?_ ?_
  · intro X Y Z e f hf
    exact (hQ _ _ _ _ _ _ _ _ (Space.pointsMap B S hS X.obj (e.hom ≫ f).hom)
      (Space.pointsMap B S hS Y.obj f.hom)
      (Space.pointsMap B S hS X.obj e.hom.hom) id
      (Space.pointsHomeomorphOfIso B S hS (isoObj B S hS e)).isHomeomorph
      (@IsHomeomorph.id (Space.points B S hS Z.obj) (Space.pointTopology B S hS Z.obj))
      (fun x => congrFun (Space.pointsMap_comp B S hS X.obj e.hom.hom f.hom) x)).mpr hf
  · intro X Y Z e f hf
    exact (hQ _ _ _ _ _ _ _ _ (Space.pointsMap B S hS X.obj f.hom)
      (Space.pointsMap B S hS X.obj (f ≫ e.hom).hom) id
      (Space.pointsMap B S hS Y.obj e.hom.hom)
      (@IsHomeomorph.id (Space.points B S hS X.obj) (Space.pointTopology B S hS X.obj))
      (Space.pointsHomeomorphOfIso B S hS (isoObj B S hS e)).isHomeomorph
      (fun x => (congrFun (Space.pointsMap_comp B S hS X.obj f.hom e.hom.hom) x).symm)).mp hf

/-- **A property holds after every base change exactly when it holds for the chosen fibre
products.** The chosen fibre product of Tag 02X2 realises each of the base changes that an
algebraic-space base change tests, and the comparison isomorphism of two cartesian squares on one
cospan carries a property respecting isomorphisms between them. -/
theorem universally_iff_forall_space_baseChange
    (𝓅 : MorphismProperty (AlgebraicSpaces B S hS)) [𝓅.RespectsIso]
    {X T : AlgebraicSpaces B S hS} (g : X ⟶ T) :
    𝓅.universally g ↔
      ∀ (Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hZ : IsAlgebraicSpace B S hS Z) (k : Z ⟶ T.obj),
        𝓅 (ObjectProperty.homMk (pullback.fst k g.hom) :
          AlgebraicSpaces.fiberProduct B S hS
              (ObjectProperty.homMk (X := (⟨Z, hZ⟩ : AlgebraicSpaces B S hS)) k) g ⟶
            (⟨Z, hZ⟩ : AlgebraicSpaces B S hS)) := by
  refine ⟨fun hg Z hZ k => hg _ _ _ (AlgebraicSpaces.isPullback_fiberProduct B S hS
    (ObjectProperty.homMk (X := (⟨Z, hZ⟩ : AlgebraicSpaces B S hS)) k) g), ?_⟩
  · intro hg Y' T' i₁ i₂ k sq
    have hcan : 𝓅 (ObjectProperty.homMk (pullback.fst i₂.hom g.hom) :
        AlgebraicSpaces.fiberProduct B S hS i₂ g ⟶ T') := hg T'.obj T'.property i₂.hom
    refine (𝓅.arrow_mk_iso_iff
      (Arrow.isoMk (f := Arrow.mk (ObjectProperty.homMk (pullback.fst i₂.hom g.hom)))
        (g := Arrow.mk k)
        ((AlgebraicSpaces.isPullback_fiberProduct B S hS i₂ g).isoIsPullback T' X sq)
        (Iso.refl _) ?_)).mp hcan
    exact (AlgebraicSpaces.isPullback_fiberProduct B S hS i₂ g).isoIsPullback_hom_fst T' X sq

/-- **The relative property of Tag 04XB, read on the lower-shriek extension.** The definition
tests the structural morphism of Tag 04SG of each algebraic space representing a base change
along a scheme-valued point of the target; this reads the test on
`CategoryTheory.OverShriek.relocalizeToYoneda`, which is the explicit form of that morphism. -/
private theorem relative_iff_forall_relocalize
    (𝓅 : MorphismProperty (AlgebraicSpaces B S hS)) [𝓅.RespectsIso]
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) :
    (∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hT : IsAlgebraicSpace B U.left.1 U.left.2 T),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (T ⋙ typeToCat)).p) →
        𝓅 (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨T, hT⟩))) ↔
      ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
        (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
        (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hT : IsAlgebraicSpace B U.left.1 U.left.2 T),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor f))
          (presheafOfCategories (T ⋙ typeToCat)).p) →
        𝓅 (ObjectProperty.homMk (OverShriek.relocalizeToYoneda U.hom T) :
          (⟨(OverShriek.relocalizePresheafFunctor U.hom).obj T,
              isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT⟩ :
            AlgebraicSpaces B S hS) ⟶
          (schemeSpace U : AlgebraicSpaces B S hS)) := by
  constructor <;> intro H U y hy T hT he
  · exact (prop_algebraicSpaceMap_iff B S hS 𝓅 U T hT).mp (H U y hy T hT he)
  · exact (prop_algebraicSpaceMap_iff B S hS 𝓅 U T hT).mpr (H U y hy T hT he)

/-- **The property on points of a 1-morphism of represented stacks is the property on points of
the induced morphism of representing presheaves.** Both ends are represented by algebraic spaces,
so the canonical maps on points of the two representing charts are homeomorphisms and they
identify the two maps. -/
private theorem pointMapProperty_representingMap_iff (Q : PointMapProperty.{u})
    (hQ : IsConjInvariant.{u} Q)
    (𝒜 𝒞 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (eF : StacksRepresentableCFG.EquivalenceOver
      𝒜.val.p (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver
      𝒞.val.p (presheafOfCategories (G ⋙ typeToCat)).p)
    (a : 𝒜 ⟶ 𝒞) :
    Q (Space.points B S hS F) (Space.points B S hS G) (Space.pointTopology B S hS F)
        (Space.pointTopology B S hS G)
        (Space.pointsMap B S hS F (representingMap B S hS 𝒜 𝒞 F G eF eG a)) ↔
      Q (points B S hS 𝒜.val 𝒜.property) (points B S hS 𝒞.val 𝒞.property)
        (pointTopology B S hS 𝒜) (pointTopology B S hS 𝒞)
        (pointsMap B S hS 𝒜.val 𝒜.property 𝒞.property a.hom) :=
  hQ _ _ _ _ _ _ _ _ _ _
    (spacePointMap B S hS F 𝒜 (representingEquivalence B S hS F 𝒜 eF).functor)
    (spacePointMap B S hS G 𝒞 (representingEquivalence B S hS G 𝒞 eG).functor)
    (isHomeomorph_spacePointMap_representing B S hS F hF 𝒜 eF)
    (isHomeomorph_spacePointMap_representing B S hS G hG 𝒞 eG)
    (spacePointMap_representing_naturality B S hS F G 𝒜 𝒞 eF eG a)

/-- **The property on points of the first projection is a property of the cospan.** Any two
2-fibre products of one cospan of categories fibred in groupoids over the big fppf site of `S`
have first projections with the property together: the comparison 1-morphism is a homeomorphism
on points for the topology of Tag 04XL, and it identifies the two projections. -/
theorem pointMapProperty_fst_congr (Q : PointMapProperty.{u})
    (hQ : IsConjInvariant.{u} Q)
    {𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    {g : 𝒵 ⟶ 𝒴} {f : 𝒳 ⟶ 𝒴} (P R : Bicategory.TwoCommSq g f)
    (hP : Bicategory.IsTwoFibreProduct P) (hR : Bicategory.IsTwoFibreProduct R)
    (h : Q (points B S hS P.pt.val P.pt.property) (points B S hS 𝒵.val 𝒵.property)
      (pointTopology B S hS P.pt) (pointTopology B S hS 𝒵)
      (pointsMap B S hS P.pt.val P.pt.property 𝒵.property P.fst.hom)) :
    Q (points B S hS R.pt.val R.pt.property) (points B S hS 𝒵.val 𝒵.property)
      (pointTopology B S hS R.pt) (pointTopology B S hS 𝒵)
      (pointsMap B S hS R.pt.val R.pt.property 𝒵.property R.fst.hom) := by
  let a := Quotient.out (hP.from R)
  exact (hQ _ _ _ _ _ _ _ _
    (pointsMap B S hS R.pt.val R.pt.property 𝒵.property R.fst.hom)
    (pointsMap B S hS P.pt.val P.pt.property 𝒵.property P.fst.hom)
    (pointsMap B S hS R.pt.val R.pt.property P.pt.property a.hom.hom) id
    (isHomeomorph_pointsMap_of_isEquivalence B S hS R.pt P.pt a.hom.hom
      (Bicategory.isEquivalence_of_isTwoFibreProduct hR hP a))
    (@IsHomeomorph.id _ (pointTopology B S hS 𝒵))
    (fun x => congrFun (pointsMap_fst_comp_eq B S hS a) x)).mpr h

/-! ### The shared core -/

/-- **First-factor cancellation preserves the property on points of the first projection.** If the
first projection of `𝒰 ×_𝒴 𝒳` has the property, so has that of the exchanged iterated 2-fibre
product `(𝒵 ×_𝒴 𝒳) ×_𝒵 𝒰` of Tag 02XD. -/
private theorem pointMapProperty_fst_cancelFst (Q : PointMapProperty.{u})
    (hQ : IsConjInvariant.{u} Q)
    {𝒰 𝒵 𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
    (g : 𝒵 ⟶ 𝒴) (f : 𝒳 ⟶ 𝒴) (c : 𝒰 ⟶ 𝒵) (G : 𝒰 ⟶ 𝒴) (θ : c ≫ g ≅ G)
    (h : Q (points B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          G f).pt.val (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
          G f).pt.property) (points B S hS 𝒰.val 𝒰.property)
      (pointTopology B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        G f).pt) (pointTopology B S hS 𝒰)
      (pointsMap B S hS (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        G f).pt.val (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
        G f).pt.property 𝒰.property
        (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} G f).fst.hom)) :
    Q (points B S hS (CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1}
          g f c G θ).swap.pt.val (CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1}
          g f c G θ).swap.pt.property) (points B S hS 𝒰.val 𝒰.property)
      (pointTopology B S hS (CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1}
        g f c G θ).swap.pt) (pointTopology B S hS 𝒰)
      (pointsMap B S hS (CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1}
        g f c G θ).swap.pt.val (CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1}
        g f c G θ).swap.pt.property 𝒰.property
        (CatFiberedInGroupoids.cancelFstSquare.{u, u, u + 1, u + 1} g f c G θ).swap.fst.hom) :=
  pointMapProperty_fst_congr B S hS Q hQ _ _
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} G f)
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_cancelFstSquare.{u, u, u + 1, u + 1}
        g f c G θ)) h

/-- The relative property of Tag 04XB at `Q`, in the shape of Tag 03YK: every algebraic space
representing a base change of `f` along a scheme-valued point of the target has structural
morphism with `Q` after every further algebraic-space base change. -/
abbrev RelativeUniversally (Q : PointMapProperty.{u})
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)} (f : 𝒳 ⟶ 𝒴) :
    Prop :=
  ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (T : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hT : IsAlgebraicSpace B U.left.1 U.left.2 T),
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
        (CatFiberedInGroupoids.homFunctor f))
      (presheafOfCategories (T ⋙ typeToCat)).p) →
    (pointMapProperty B S hS Q).universally (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨T, hT⟩))

/-- **The forward implication of the shared core.** Take a chart of `𝒵` by the slice of the site
over a scheme `U`, open and surjective on points. The relative property at the scheme-valued
point of `𝒴` the chart names says the structural morphism of the presheaf representing the base
change has `Q`; reading that on points and moving it along the first-factor cancellation of
Tag 02XD gives `Q` for the first projection of `U ×_𝒵 (𝒵 ×_𝒴 𝒳)`; and the open surjection
`|U| → |𝒵|` descends it to `𝒵 ×_𝒴 𝒳`, the hypothesis on the canonical map to the topological
fibre product being Tag 04XH. -/
private theorem pointMapProperty_fst_of_relativeUniversally (Q : PointMapProperty.{u})
    (hQconj : IsConjInvariant.{u} Q) (hQdesc : IsDescendable.{u} Q)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (H : RelativeUniversally B S hS Q f.hom)
    (𝒵 : AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴) :
    Q (points B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.val
        (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.property)
      (points B S hS 𝒵.val.val 𝒵.val.property)
      (pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val)
      (pointTopology B S hS 𝒵.val)
      (pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.val
        (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.property 𝒵.val.property
        (twoFibreProductSquareAlgebraicStacks B S hS g f).fst.hom.hom) := by
  classical
  obtain ⟨U, c, hcsurj, hcopen⟩ := exists_sliceChart_isOpenMap_surjective B S hS 𝒵
  let cMor : schemeSlice B S hS U ⟶ 𝒵.val := Bicategory.InducedBicategory.mkHom c
  let y := CatFiberedInGroupoids.homFunctor (cMor ≫ g.hom)
  have hy : y ⋙ 𝒴.val.val.p = Over.map U.hom :=
    CatFiberedInGroupoids.homFunctor_comp_p (cMor ≫ g.hom)
  let Sq := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (schemeSliceMap B S hS U y hy) f.hom
  let Pb := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} g.hom f.hom
  let V := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Pb.fst cMor
  obtain ⟨T, hT, ⟨eT⟩⟩ := hf U y hy
  have hUC := (relative_iff_forall_relocalize B S hS
    ((pointMapProperty B S hS Q).universally) f.hom).mp H U y hy T hT ⟨eT⟩
  have hCM := MorphismProperty.universally_le (pointMapProperty B S hS Q) _ hUC
  have hSq : Q (points B S hS Sq.pt.val Sq.pt.property)
      (points B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property)
      (pointTopology B S hS Sq.pt) (pointTopology B S hS (schemeSlice B S hS U))
      (pointsMap B S hS Sq.pt.val Sq.pt.property (schemeSlice B S hS U).property
        Sq.fst.hom) := by
    refine (pointMapProperty_representingMap_iff B S hS Q hQconj Sq.pt
      (schemeSlice B S hS U) ((OverShriek.relocalizePresheafFunctor U.hom).obj T)
      (yoneda.obj U) (isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT)
      (isAlgebraicSpace_yoneda B S hS U)
      (relocalizeFibreEquivalence B S hS U f.hom y T eT)
      (schemeSliceEquivalenceOver B S hS U) Sq.fst).mp ?_
    rwa [representingMap_relocalizeFibre B S hS U f.hom y T eT hy]
  have hRest := pointMapProperty_fst_cancelFst B S hS Q hQconj g.hom f.hom cMor
    (schemeSliceMap B S hS U y hy) (Iso.refl _) hSq
  refine hQdesc
    (points B S hS V.pt.val V.pt.property)
    (points B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property)
    (points B S hS Pb.pt.val Pb.pt.property)
    (points B S hS 𝒵.val.val 𝒵.val.property)
    (pointTopology B S hS V.pt)
    (pointTopology B S hS (schemeSlice B S hS U))
    (pointTopology B S hS Pb.pt)
    (pointTopology B S hS 𝒵.val)
    (pointsMap B S hS V.pt.val V.pt.property (schemeSlice B S hS U).property V.snd.hom)
    (pointsMap B S hS V.pt.val V.pt.property Pb.pt.property V.fst.hom)
    (pointsMap B S hS Pb.pt.val Pb.pt.property 𝒵.val.property Pb.fst.hom)
    (pointsMap B S hS (schemeSlice B S hS U).val (schemeSlice B S hS U).property
      𝒵.val.property c)
    (fun x => ?_) hcopen hcsurj
    (continuous_pointsMap B S hS (schemeSlice B S hS U) 𝒵.val c)
    (continuous_pointsMap B S hS V.pt Pb.pt V.fst.hom)
    (continuous_pointsMap B S hS Pb.pt 𝒵.val Pb.fst.hom)
    (fun v cc h => ?_) hRest
  · exact ((pointsMap_comp B S hS _ _ (schemeSlice B S hS U).property 𝒵.val.property
        V.snd.hom cMor.hom x).trans
      (congrFun (pointsMap_eq_of_basedNatTrans B S hS _ _ 𝒵.val.property
        V.iso.inv.hom) x)).trans
      (pointsMap_comp B S hS _ _ _ 𝒵.val.property V.fst.hom Pb.fst.hom x).symm
  · obtain ⟨r, hr1, hr2⟩ := exists_point_of_isTwoFibreProduct B S hS V
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        Pb.fst cMor) cc v h.symm
    exact ⟨r, hr2, hr1⟩

/-- **The converse implication of the shared core.** It is enough to see that the structural
morphism `Λ_U T ⟶ h_U` of the lower-shriek extension of a presheaf representing a base change
along a scheme-valued point has `Q` after every algebraic-space base change. The morphism
`k : Z ⟶ h_U` comes from a 1-morphism out of the category of elements of `Z` (Tag 04SW, onto);
the hypothesis at that algebraic stack, moved by two first-factor cancellations of Tag 02XD, is
`Q` on points of the first projection of `Z ×_U (U ×_𝒴 𝒳)`; and Tag 04SD identifies the
representing presheaf of that apex with `Z ×_{h_U} Λ_U T`. -/
private theorem relativeUniversally_of_pointMapProperty_fst (Q : PointMapProperty.{u})
    (hQconj : IsConjInvariant.{u} Q)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (Hpts : ∀ (𝒵 : AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴),
      Q (points B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.val
          (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.property)
        (points B S hS 𝒵.val.val 𝒵.val.property)
        (pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val)
        (pointTopology B S hS 𝒵.val)
        (pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.val
          (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.property 𝒵.val.property
          (twoFibreProductSquareAlgebraicStacks B S hS g f).fst.hom.hom)) :
    RelativeUniversally B S hS Q f.hom := by
  classical
  have := respectsIso_pointMapProperty B S hS Q hQconj
  refine (relative_iff_forall_relocalize B S hS
    ((pointMapProperty B S hS Q).universally) f.hom).mpr ?_
  rintro U y hy T hT ⟨eT⟩
  refine (universally_iff_forall_space_baseChange B S hS (pointMapProperty B S hS Q) _).mpr ?_
  intro Z hZ k
  -- the two represented algebraic stacks and the 1-morphism inducing `k`
  let Ualg : AlgebraicStacks.{u, w} B S hS :=
    ⟨schemeSlice B S hS U, isAlgebraicStack_of_isRepresentableByAlgebraicSpace.{u, w} B S hS
      (schemeSlice B S hS U) (isRepresentableByAlgebraicSpace_schemeSlice B S hS U)⟩
  let Zalg : AlgebraicStacks.{u, w} B S hS :=
    ⟨fibredCategory B S hS Z, isAlgebraicStack_fibredCategory.{u, w} B S hS Z hZ⟩
  obtain ⟨hZU, hk⟩ := exists_oneMorphism_representingMap_eq B S hS
    (𝒳 := Zalg) (𝒴 := Ualg) Z (yoneda.obj U)
    (spaceEquivalenceOver B S hS Z) (schemeSliceEquivalenceOver B S hS U) k
  let Sq := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1}
    (schemeSliceMap B S hS U y hy) f.hom
  let gZ := hZU ≫ Bicategory.InducedBicategory.mkHom (schemeSliceMap B S hS U y hy)
  let R := CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} hZU.hom Sq.fst
  have hQrep := isRepresentableByAlgebraicSpaces_baseChange.{u, u, u} B S hS 𝒳.val 𝒴.val
    (schemeSlice B S hS U) f.hom (schemeSliceMap B S hS U y hy) Sq
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      (schemeSliceMap B S hS U y hy) f.hom) hf
  have h1 := pointMapProperty_fst_cancelFst B S hS Q hQconj (schemeSliceMap B S hS U y hy) f.hom
    hZU.hom gZ.hom (Iso.refl _) (Hpts Zalg gZ)
  have h2 := pointMapProperty_fst_congr B S hS Q hQconj
    (CatFiberedInGroupoids.twoFibreProductSquare.{u, u, u + 1, u + 1} Sq.fst hZU.hom).swap R
    (Bicategory.isTwoFibreProduct_swap
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
        Sq.fst hZU.hom))
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} hZU.hom
      Sq.fst) h1
  obtain ⟨W, hW, ⟨eW⟩⟩ := isRepresentableByAlgebraicSpace_of_isTwoFibreProduct.{u, u, u} B S hS
    Sq.pt (schemeSlice B S hS U) (fibredCategory B S hS Z) Sq.fst hZU.hom R
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1}
      hZU.hom Sq.fst) hQrep (isRepresentableByAlgebraicSpace_fibredCategory B S hS Z hZ)
  have h3 := (pointMapProperty_representingMap_iff B S hS Q hQconj R.pt
    (fibredCategory B S hS Z) W Z hW hZ eW (spaceEquivalenceOver B S hS Z) R.fst).mpr h2
  change Q (Space.points B S hS (pullback k (OverShriek.relocalizeToYoneda U.hom T)))
      (Space.points B S hS Z)
      (Space.pointTopology B S hS (pullback k (OverShriek.relocalizeToYoneda U.hom T)))
      (Space.pointTopology B S hS Z)
      (Space.pointsMap B S hS (pullback k (OverShriek.relocalizeToYoneda U.hom T))
        (pullback.fst k (OverShriek.relocalizeToYoneda U.hom T)))
  rw [← hk, ← representingMap_relocalizeFibre B S hS U f.hom y T eT hy]
  let _inst : (twoFibreProductStructureFunctor B S hS (fibredCategory B S hS Z) Sq.pt
      (schemeSlice B S hS U) hZU.hom Sq.fst).IsFibered :=
    R.pt.property.isFibered
  have hA := fibreProductIsoRepresenting_hom_comp_representingMap_fst B S hS
    (fibredCategory B S hS Z) Sq.pt (schemeSlice B S hS U) Z
    ((OverShriek.relocalizePresheafFunctor U.hom).obj T) (yoneda.obj U)
    (spaceEquivalenceOver B S hS Z) (relocalizeFibreEquivalence B S hS U f.hom y T eT)
    (schemeSliceEquivalenceOver B S hS U) hZU.hom Sq.fst W eW
  have hiso : Arrow.mk (ObjectProperty.homMk (pullback.fst
        (representingMap B S hS (fibredCategory B S hS Z) (schemeSlice B S hS U) Z
          (yoneda.obj U) (spaceEquivalenceOver B S hS Z)
          (schemeSliceEquivalenceOver B S hS U) hZU.hom)
        (representingMap B S hS Sq.pt (schemeSlice B S hS U)
          ((OverShriek.relocalizePresheafFunctor U.hom).obj T) (yoneda.obj U)
          (relocalizeFibreEquivalence B S hS U f.hom y T eT)
          (schemeSliceEquivalenceOver B S hS U) Sq.fst)) :
      (⟨pullback (representingMap B S hS (fibredCategory B S hS Z) (schemeSlice B S hS U) Z
          (yoneda.obj U) (spaceEquivalenceOver B S hS Z)
          (schemeSliceEquivalenceOver B S hS U) hZU.hom)
          (representingMap B S hS Sq.pt (schemeSlice B S hS U)
          ((OverShriek.relocalizePresheafFunctor U.hom).obj T) (yoneda.obj U)
          (relocalizeFibreEquivalence B S hS U f.hom y T eT)
          (schemeSliceEquivalenceOver B S hS U) Sq.fst),
        isAlgebraicSpace_pullback B S hS _ _ hZ
          (isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom T hT)
          (isAlgebraicSpace_yoneda B S hS U)⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Z, hZ⟩ : AlgebraicSpaces B S hS)) ≅
      Arrow.mk (ObjectProperty.homMk (representingMap B S hS R.pt (fibredCategory B S hS Z) W Z
          eW (spaceEquivalenceOver B S hS Z) R.fst) :
        (⟨W, hW⟩ : AlgebraicSpaces B S hS) ⟶ (⟨Z, hZ⟩ : AlgebraicSpaces B S hS)) := by
    refine Arrow.isoMk (ObjectProperty.isoMk _
      ((Presheaf.fibreProductIsoPullback _ _).symm ≪≫
        fibreProductIsoRepresenting B S hS (fibredCategory B S hS Z) Sq.pt
          (schemeSlice B S hS U) Z ((OverShriek.relocalizePresheafFunctor U.hom).obj T)
          (yoneda.obj U) (spaceEquivalenceOver B S hS Z)
          (relocalizeFibreEquivalence B S hS U f.hom y T eT)
          (schemeSliceEquivalenceOver B S hS U) hZU.hom Sq.fst W eW)) (Iso.refl _) ?_
    apply ObjectProperty.hom_ext
    change ((Presheaf.fibreProductIsoPullback _ _).symm ≪≫
        fibreProductIsoRepresenting B S hS (fibredCategory B S hS Z) Sq.pt
          (schemeSlice B S hS U) Z ((OverShriek.relocalizePresheafFunctor U.hom).obj T)
          (yoneda.obj U) (spaceEquivalenceOver B S hS Z)
          (relocalizeFibreEquivalence B S hS U f.hom y T eT)
          (schemeSliceEquivalenceOver B S hS U) hZU.hom Sq.fst W eW).hom ≫
        (representingMap B S hS R.pt (fibredCategory B S hS Z) W Z eW
          (spaceEquivalenceOver B S hS Z) R.fst) =
      pullback.fst (representingMap B S hS (fibredCategory B S hS Z) (schemeSlice B S hS U) Z
          (yoneda.obj U) (spaceEquivalenceOver B S hS Z)
          (schemeSliceEquivalenceOver B S hS U) hZU.hom)
        (representingMap B S hS Sq.pt (schemeSlice B S hS U)
          ((OverShriek.relocalizePresheafFunctor U.hom).obj T) (yoneda.obj U)
          (relocalizeFibreEquivalence B S hS U f.hom y T eT)
          (schemeSliceEquivalenceOver B S hS U) Sq.fst) ≫ 𝟙 _
    rw [Category.comp_id, Iso.trans_hom, Category.assoc, hA, Iso.symm_hom]
    exact (Presheaf.isPullback_fibreProduct _ _).isoPullback_inv_fst
  exact ((pointMapProperty B S hS Q).arrow_mk_iso_iff hiso).mpr h3

/-- **The shared core of Stacks 0CHX, 0CI1 and 0CI6.** A 1-morphism of algebraic stacks over `S`
representable by algebraic spaces has the relative property of Tag 04XB at universally `Q`
exactly when, for every algebraic stack `𝒵` over `𝒴`, the map `|𝒵 ×_𝒴 𝒳| → |𝒵|` on the points of
Tag 04XG for the topology of Tag 04XL has `Q`. -/
theorem relative_iff_forall_pointsMap_fst (Q : PointMapProperty.{u})
    (hQconj : IsConjInvariant.{u} Q) (hQdesc : IsDescendable.{u} Q)
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ 𝒴)
    (hf : IsRepresentableByAlgebraicSpaces B S hS f.hom.hom) :
    RelativeUniversally B S hS Q f.hom ↔
      ∀ (𝒵 : AlgebraicStacks.{u, w} B S hS) (g : 𝒵 ⟶ 𝒴),
        Q (points B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.val
            (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.property)
          (points B S hS 𝒵.val.val 𝒵.val.property)
          (pointTopology B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val)
          (pointTopology B S hS 𝒵.val)
          (pointsMap B S hS (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.val
            (twoFibreProductSquareAlgebraicStacks B S hS g f).pt.val.property 𝒵.val.property
            (twoFibreProductSquareAlgebraicStacks B S hS g f).fst.hom.hom) :=
  ⟨fun H 𝒵 g => pointMapProperty_fst_of_relativeUniversally B S hS Q hQconj hQdesc f hf H 𝒵 g,
    relativeUniversally_of_pointMapProperty_fst B S hS Q hQconj f hf⟩

end Abstract

/-! ### The three properties this is used at -/

section Properties

/-- Submersiveness, as a property of maps between the point spaces of this library. -/
abbrev quotientMapProperty : PointMapProperty.{u} :=
  fun _ _ tX tY h => @Topology.IsQuotientMap _ _ tX tY h

/-- Injectivity, as a property of maps between the point spaces of this library. -/
abbrev injectiveProperty : PointMapProperty.{u} := fun _ _ _ _ h => Function.Injective h

/-- Being a homeomorphism, as a property of maps between the point spaces of this library. -/
abbrev homeomorphProperty : PointMapProperty.{u} :=
  fun _ _ tX tY h => @IsHomeomorph _ _ tX tY h

/-- Submersiveness is invariant under conjugating by homeomorphisms. -/
theorem isConjInvariant_quotientMapProperty : IsConjInvariant.{u} quotientMapProperty :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hσ hτ hcomm => isQuotientMap_iff_of_isHomeomorph hσ hτ hcomm

/-- Injectivity is invariant under conjugating by homeomorphisms. -/
theorem isConjInvariant_injectiveProperty : IsConjInvariant.{u} injectiveProperty :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hσ hτ hcomm => injective_iff_of_isHomeomorph hσ hτ hcomm

/-- Being a homeomorphism is invariant under conjugating by homeomorphisms. -/
theorem isConjInvariant_homeomorphProperty : IsConjInvariant.{u} homeomorphProperty :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hσ hτ hcomm => isHomeomorph_iff_of_isHomeomorph hσ hτ hcomm

/-- Submersiveness descends along an open continuous surjection of the targets. -/
theorem isDescendable_quotientMapProperty : IsDescendable.{u} quotientMapProperty :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hcomm hb hbsurj hbcont ha hq _ hp =>
    isQuotientMap_of_isQuotientMap_comm_of_isOpenMap_surjective hcomm hb hbsurj hbcont ha hq hp

/-- Injectivity descends along a surjection of the targets, across a square whose canonical map
to the topological fibre product is surjective. -/
theorem isDescendable_injectiveProperty : IsDescendable.{u} injectiveProperty :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hcomm _hb hbsurj _ _ _ hsurj hp =>
    injective_of_injective_comm_of_surjective hcomm hbsurj hsurj hp

/-- Being a homeomorphism descends along an open surjection of the targets, across a square whose
canonical map to the topological fibre product is surjective. -/
theorem isDescendable_homeomorphProperty : IsDescendable.{u} homeomorphProperty :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hcomm hb hbsurj _ ha hq hsurj hp =>
    isHomeomorph_of_isHomeomorph_comm_of_isOpenMap_surjective hcomm hb hbsurj ha hq hsurj hp

end Properties

end AlgebraicGeometry.Stack

end
