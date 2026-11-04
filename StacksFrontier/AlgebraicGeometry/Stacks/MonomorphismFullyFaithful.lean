module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Monomorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.EssentiallySmallSite
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsInjective
public import StacksFrontier.AlgebraicGeometry.Stacks.ResidualGerbe
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective

/-!
# Monomorphisms of fibred groupoids are fully faithful, and are injective on points

Let `S` be a scheme contained in a big fppf site and let `j : 𝒳 ⟶ 𝒴` be a 1-morphism of
categories fibred in groupoids over `(Sch/S)_fppf` which is representable by algebraic spaces.
**Stacks 05UK** says that if every algebraic space representing a base change of `j` along a
scheme-valued point of `𝒴` has *monomorphism* structural morphism, then the functor induced by
`j` on each fibre category is fully faithful; with **Stacks 003Z** that makes `j` itself fully
faithful, which is the implication (1) ⟹ (2) of **Stacks 04ZZ**.

Combined with **Stacks 0500** this is what makes a monomorphism injective on points, and hence —
since a closed immersion of algebraic spaces is an immersion and an immersion is a monomorphism
(**Stacks 042R**) — what makes a *closed immersion of algebraic stacks* injective on points. That
last statement is the input `StacksFrontier.AlgebraicGeometry.Stacks.ThickeningComposition` records
as missing for the converse half of **Stacks 0CJ9** part (2).

## Main results

* `AlgebraicGeometry.Stack.full_and_faithful_homFunctor_of_mono_representingMaps`: **Stacks
  05UK** together with Stacks 003Z, i.e. the implication (1) ⟹ (2) of **Stacks 04ZZ**.
* `AlgebraicGeometry.Stack.AlgebraicStacks.full_and_faithful_homFunctor_of_isMonomorphism`: the
  same implication (1) ⟹ (2) of **Stacks 04ZZ** read for a monomorphism of algebraic stacks in
  the sense of **Stacks 04ZW**.
* `AlgebraicGeometry.Stack.full_and_faithful_homFunctor_of_isClosedImmersion` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.full_and_faithful_homFunctor_of_isClosedImmersion`:
  the same for a closed immersion, at the two levels of the 2-category tower.
* `AlgebraicGeometry.Stack.AlgebraicStacks.injective_pointsMap_of_isClosedImmersion`: a closed
  immersion of algebraic stacks is injective on points.
* `AlgebraicGeometry.Stack.AlgebraicStacks.bijective_pointsMap_of_isEquivalence`: a 1-morphism
  of algebraic stacks whose underlying functor is an equivalence is bijective on points. This
  complements `AlgebraicGeometry.Stack.AlgebraicStacks.bijective_pointsMap_preHom`, which
  compares two models of *one* cospan: this one compares models of two *different* cospans whose
  apexes happen to be equivalent, which is the situation
  `CategoryTheory.TwoFibreProductOver.isEquivalence_mapBase` produces when the target of a cospan
  is enlarged along a fully faithful 1-morphism.

The consequence for thickenings is in
`StacksFrontier.AlgebraicGeometry.Stacks.ThickeningSurjective`, which needs Stacks 0BPP and so
cannot be imported here.

## Implementation notes

The monomorphism hypothesis is stated in the **longhand** form of Stacks 04XB — a quantifier over
every algebraic space representing a base change, with `Mono` of the structural morphism of
presheaves as the conclusion — rather than as
`AlgebraicGeometry.Stack.HasRelativeProperty` at `MorphismProperty.monomorphisms`. That is
deliberate, and it is the idiom of
`AlgebraicGeometry.Stack.prop_baseChange_of_isTwoFibreProduct`:
`AlgebraicGeometry.Stack.HasRelativeProperty` carries locality of the property at the target for
the fppf precoverage, which for monomorphisms is Stacks 042D, a result this library does not have.
The proof does not use it, so requiring it would make the statement unavailable for no reason.
`AlgebraicGeometry.Stack.IsClosedImmersion` is written in the same longhand, so the two match up
directly.

The conclusion is the conjunction `Full ∧ Faithful` rather than two instance arguments, as in
`CategoryTheory.Limits.CategoricalPullback.isEquivalence_relativeDiagonal_of_fullyFaithful`, so
that it can be supplied by a term; the faithful half is already
`AlgebraicGeometry.Stack.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces` (Stacks 04Y5)
and is only repeated here for the convenience of consumers that need both.

The fibre functor of Stacks 003Z (1) is `CategoryTheory.Functor.Fiber.mapOfComp` while the
criterion of Stacks 02ZY states its faithfulness clause with
`CategoryTheory.Stacks.RepresentableMorphism.inducedFiberFunctor`. These are the same term under
two names — both are `CategoryTheory.Functor.Fiber.inducedFunctor` at `fiberInclusion ⋙ j` — so
no bridge is needed, exactly as in
`StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable`. Both are semireducible, which is
why `CategoryTheory.Functor.Fiber` and `CategoryTheory.Functor.Fiber.fiberInclusion` are made
locally implicit-reducible here.

The fullness argument is the source's. Fix `U`, objects `a`, `b` of the fibre `𝒳_U` and a
morphism `f : j(a) ⟶ j(b)` of `𝒴_U`. Take `y = j(a)`, let `G` be the 1-morphism
`(Sch/U)_fppf ⟶ 𝒴` that 2-Yoneda attaches to `y`, and let `F` be an algebraic space representing
`(Sch/U)_fppf ×_𝒴 𝒳`. The identity of `U` is a section of `F` over the terminal object of
`(Sch/U)_fppf`, and the structural morphism of `F` is injective on sections because it is a
monomorphism; so `F` has *at most one* section there. The pair `(a, 𝟙)` and the pair `(b, f)` are
two objects of the fibre of `(Sch/U)_fppf ×_𝒴 𝒳` over that terminal object, hence isomorphic, and
the `𝒳`-component of the isomorphism is the preimage of `f` sought.

## References

* [Stacks Project, Tag 003Z](https://stacks.math.columbia.edu/tag/003Z)
* [Stacks Project, Tag 02ZY](https://stacks.math.columbia.edu/tag/02ZY)
* [Stacks Project, Tag 042R](https://stacks.math.columbia.edu/tag/042R)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YL](https://stacks.math.columbia.edu/tag/04YL)
* [Stacks Project, Tag 04ZZ](https://stacks.math.columbia.edu/tag/04ZZ)
* [Stacks Project, Tag 0500](https://stacks.math.columbia.edu/tag/0500)
* [Stacks Project, Tag 05UK](https://stacks.math.columbia.edu/tag/05UK)
* [Stacks Project, Tag 0BPP](https://stacks.math.columbia.edu/tag/0BPP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite

namespace AlgebraicGeometry.Stack

universe u v w

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

/-- The fibre of the category fibred in discrete groupoids attached to a presheaf is a
subsingleton over an object at which the presheaf is one: an object of that fibre is a section
over the object itself, read as an object of a discrete category. -/
private theorem subsingleton_presheafOfCategories_fiber
    {C : Type*} [Category C] (F : Cᵒᵖ ⥤ Type*) (U : C) [Subsingleton (F.obj (op U))] :
    Subsingleton ((presheafOfCategories (F ⋙ typeToCat)).p.Fiber U) := by
  constructor
  rintro ⟨⟨V, x⟩, hx⟩ ⟨⟨W, y⟩, hy⟩
  obtain rfl : V = U := hx
  obtain rfl : W = V := hy
  obtain rfl : x = y := Discrete.ext (Subsingleton.elim _ _)
  rfl

/-- Any two objects of a fibre of a category fibred in groupoids *represented* by a presheaf which
is a subsingleton over that object are connected by a morphism: downstairs the fibre of the
presheaf's category of discrete groupoids is a subsingleton, and the representing equivalence is
fully faithful, so the resulting equality of objects lifts to a morphism over the identity. -/
private theorem nonempty_fiber_hom_of_equivalenceOver
    {C D : Type*} [Category C] [Category D] {p : D ⥤ C} (F : Cᵒᵖ ⥤ Type*)
    (e : StacksRepresentableCFG.EquivalenceOver p (presheafOfCategories (F ⋙ typeToCat)).p)
    (U : C) [Subsingleton (F.obj (op U))] (a b : p.Fiber U) : Nonempty (a ⟶ b) := by
  let q := (presheafOfCategories (F ⋙ typeToCat)).p
  let H := Stacks.RepresentableMorphism.inducedFiberFunctor p q e.hom.functor e.hom.w U
  have _ := subsingleton_presheafOfCategories_fiber F U
  let f : H.obj a ⟶ H.obj b := eqToHom (Subsingleton.elim _ _)
  let ff := e.toEquivalence.fullyFaithfulFunctor
  let g := ff.preimage (Fiber.fiberInclusion.map f)
  have hg : p.IsHomLift (𝟙 U) g := by
    apply (isHomLift_map_iff_of_comp_eq p q e.hom.functor e.hom.w (𝟙 U) g).mp
    rw [show e.hom.functor.map g = Fiber.fiberInclusion.map f from ff.map_preimage _]
    exact f.2
  exact ⟨⟨g, hg⟩⟩

/-- An algebraic space over `U` whose structural morphism is a monomorphism has at most one
section over the terminal object of `(Sch/U)_fppf`. -/
theorem subsingleton_obj_of_mono_algebraicSpaceMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (U : BigFppfOver B S hS)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (hm : Mono (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom) :
    Subsingleton (F.obj (op (Over.mk (𝟙 U.left) : BigFppfOver B U.left.1 U.left.2))) := by
  let m := algebraicSpaceMap B S hS U
    ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)
  have hinj : Function.Injective (m.hom.app (op U)) :=
    (mono_iff_injective _).mp ((NatTrans.mono_iff_mono_app _).mp hm (op U))
  let secRel (s : F.obj (op (Over.mk (𝟙 U.left) : BigFppfOver B U.left.1 U.left.2))) :
      ((OverShriek.relocalizePresheafFunctor U.hom).obj F).obj (op U) := by
    show {z // _}
    exact ⟨⟨𝟙 U.left, s⟩, by
      show 𝟙 U.left ≫ U.hom = U.hom
      exact Category.id_comp _⟩
  let iSpace := (spacesOverSmallerBaseFunctorForgetIso B U.left.1 S U.left.2 hS U.hom).app ⟨F, hF⟩
  have hmap (s) : m.hom.app (op U) (iSpace.inv.app (op U) (secRel s)) = 𝟙 U :=
    (spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app B U.left.1 S U.left.2 hS U.hom
      ⟨F, hF⟩ (op U) (secRel s)).trans (Over.OverMorphism.ext rfl)
  refine ⟨fun s₁ s₂ => ?_⟩
  have h : secRel s₁ = secRel s₂ := by
    simpa using congrArg (iSpace.hom.app (op U)) (hinj ((hmap s₁).trans (hmap s₂).symm))
  exact eq_of_heq (Sigma.mk.inj (congrArg Subtype.val h)).2

private theorem map_hom_obj_mk_id (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS) :
    (Over.map U.hom).obj (Over.mk (𝟙 U.left) : BigFppfOver B U.left.1 U.left.2) = U := by
  show Over.mk (𝟙 U.left ≫ U.hom) = U
  simp only [Category.id_comp]
  rfl

private theorem isHomLift_id_map_iteratedSliceBackward (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (U : BigFppfOver B S hS) (c : 𝒴.val.p.ChoiceOfPullbacks) (y : 𝒴.val.p.Fiber U) :
    𝒴.val.p.IsHomLift (𝟙 U) (c.map (U.iteratedSliceBackward.obj
      (Over.mk (𝟙 U.left) : BigFppfOver B U.left.1 U.left.2)).hom y) := by
  let f₀ := (U.iteratedSliceBackward.obj
    (Over.mk (𝟙 U.left) : BigFppfOver B U.left.1 U.left.2)).hom
  have hf₀ : f₀ = eqToHom (map_hom_obj_mk_id B S hS U) := by
    apply Over.OverMorphism.ext
    simp [f₀, Over.iteratedSliceBackward, Over.eqToHom_left]
  have _ : 𝒴.val.p.IsHomLift f₀ (c.map f₀ y) := inferInstance
  have h : 𝒴.val.p.IsHomLift (eqToHom (map_hom_obj_mk_id B S hS U).symm ≫ f₀) (c.map f₀ y) :=
    IsHomLift.lift_eqToHom_comp 𝒴.val.p f₀ (c.map f₀ y) (map_hom_obj_mk_id B S hS U).symm
  simpa [hf₀] using h

/-- **The fullness half of Stacks 05UK.** If every algebraic space representing a base change of
`j` along a scheme-valued point of `𝒴` has monomorphism structural morphism, then the functor
induced by `j` on the fibre over `U` is full. -/
theorem full_fiber_mapOfComp_of_mono_representingMaps
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (j : 𝒳 ⟶ 𝒴)
    (hj : IsRepresentableByAlgebraicSpaces B S hS j.hom)
    (hmono : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor j))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Mono (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom)
    (U : BigFppfOver B S hS) :
    (Fiber.mapOfComp 𝒳.val.p 𝒴.val.p (CatFiberedInGroupoids.homFunctor j)
      (CatFiberedInGroupoids.homFunctor_comp_p j) U).Full := by
  have _ : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let c : 𝒴.val.p.ChoiceOfPullbacks := Functor.chosenPullbacks 𝒴.val.p
  refine ⟨fun {a b} f => ?_⟩
  let Fg := CatFiberedInGroupoids.homFunctor j
  let y : 𝒴.val.p.Fiber U :=
    ⟨Fg.obj (Fiber.fiberInclusion.obj a),
      (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p j)
        (Fiber.fiberInclusion.obj a)).trans a.2⟩
  let G := U.iteratedSliceBackward ⋙ c.sliceFunctor y
  have hG : G ⋙ 𝒴.val.p = Over.map U.hom := by
    dsimp only [G]
    rw [Functor.assoc, c.sliceFunctor_comp y, Over.iteratedSliceBackward_forget]
  obtain ⟨Fspace, hspace, ⟨e⟩⟩ := hj U G hG
  have := subsingleton_obj_of_mono_algebraicSpaceMap B S hS U Fspace hspace
    (hmono U G hG Fspace hspace ⟨e⟩)
  let v₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  let f₀ : Over U := U.iteratedSliceBackward.obj v₀
  let φ₁ : (c.obj f₀.hom y).1 ⟶ Fg.obj (Fiber.fiberInclusion.obj a) := c.map f₀.hom y
  have hφ₁ : 𝒴.val.p.IsHomLift (𝟙 U) φ₁ := isHomLift_id_map_iteratedSliceBackward B S hS U c y
  let φ₂ : (c.obj f₀.hom y).1 ⟶ Fg.obj (Fiber.fiberInclusion.obj b) :=
    φ₁ ≫ Fiber.fiberInclusion.map f
  have hφ₂ : 𝒴.val.p.IsHomLift (𝟙 U) φ₂ := @IsHomLift.comp_lift_id_right _ _ _ _ 𝒴.val.p _ _ _
    U U (𝟙 U) φ₁ hφ₁ (Fiber.fiberInclusion.map f) f.2
  let Fst := TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p G Fg
  let mkObj (z : 𝒳.val.p.Fiber U) (φ : (c.obj f₀.hom y).1 ⟶ Fg.obj (Fiber.fiberInclusion.obj z))
      (hφ : 𝒴.val.p.IsHomLift (𝟙 U) φ) : Fst.Fiber v₀ :=
    ⟨{ base := U, x := v₀, y := z.1, hx := map_hom_obj_mk_id B S hS U, hy := z.2,
       iso := @asIso _ _ _ _ φ (𝒴.isFiberedInGroupoids.isIso_of_isHomLift_id φ hφ),
       vertical := hφ }, rfl⟩
  let A := mkObj a φ₁ hφ₁
  let D := mkObj b φ₂ hφ₂
  obtain ⟨k⟩ := nonempty_fiber_hom_of_equivalenceOver Fspace e v₀ A D
  have hk : k.1.a = 𝟙 v₀ := by
    have _ := k.2
    have h : k.1.a = 𝟙 v₀ ≫ 𝟙 v₀ ≫ 𝟙 v₀ := IsHomLift.fac' Fst (𝟙 v₀) k.1
    simpa only [Category.id_comp] using h
  have hbase : k.1.hbase = 𝟙 U := by
    rw [TwoFibreProductOver.Hom.hbase_eq, hk]
    simp [A, D, mkObj]
  have := 𝒴.isFiberedInGroupoids.isIso_of_isHomLift_id φ₁ hφ₁
  refine ⟨⟨k.1.b, hbase ▸ k.1.hb⟩, Fiber.hom_ext ((cancel_epi φ₁).1 ?_)⟩
  have hw := k.1.w
  rw [hk, G.map_id, Category.id_comp] at hw
  change φ₂ = φ₁ ≫ Fg.map k.1.b at hw
  exact hw.symm

/-- **Stacks 05UK, with Stacks 003Z: the implication (1) ⟹ (2) of Stacks 04ZZ.** A 1-morphism
`j : 𝒳 ⟶ 𝒴` of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces and all of whose representing structural morphisms are
monomorphisms has fully faithful underlying functor.

Faithfulness is Stacks 04Y5 and uses only representability. For fullness: a morphism of the fibre
`𝒴_U` out of `j(a)` makes a second object of the fibre of `(Sch/U)_fppf ×_𝒴 𝒳` over the terminal
object of `(Sch/U)_fppf`, next to the one given by `a` itself; the representing algebraic space
has at most one section there because its structural morphism is injective on sections, so the two
objects are isomorphic and the `𝒳`-component of the isomorphism is the preimage sought. -/
@[stacks 05UK]
theorem full_and_faithful_homFunctor_of_mono_representingMaps
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (j : 𝒳 ⟶ 𝒴)
    (hj : IsRepresentableByAlgebraicSpaces B S hS j.hom)
    (hmono : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
      (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
      (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
            (CatFiberedInGroupoids.homFunctor j))
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        Mono (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom) :
    (CatFiberedInGroupoids.homFunctor j).Full ∧
      (CatFiberedInGroupoids.homFunctor j).Faithful := by
  have _ : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  have hcriterion := (AlgebraicGeometry.isRepresentableByAlgebraicSpaces_iff_associatedMap
    B S hS j (Functor.chosenPullbacks 𝒴.val.p)).mp hj
  exact (Functor.IsFiberedInGroupoids.full_and_faithful_iff_forall_fiber 𝒳.val.p 𝒴.val.p
    𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor j)
    (CatFiberedInGroupoids.homFunctor_comp_p j)).mpr fun U =>
      ⟨full_fiber_mapOfComp_of_mono_representingMaps B S hS j hj hmono U, hcriterion.1 U⟩

/-- **A closed immersion of categories fibred in groupoids is fully faithful.** A closed immersion
of algebraic spaces is an immersion, and an immersion is a monomorphism (**Stacks 042R**), so the
representing structural morphisms of a closed immersion in the sense of Stacks 04XB are
monomorphisms and `AlgebraicGeometry.Stack.full_and_faithful_homFunctor_of_mono_representingMaps`
applies. -/
theorem full_and_faithful_homFunctor_of_isClosedImmersion
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)} (j : 𝒳 ⟶ 𝒴)
    (hj : IsRepresentableByAlgebraicSpaces B S hS j.hom)
    (hci : IsClosedImmersion B S hS j) :
    (CatFiberedInGroupoids.homFunctor j).Full ∧
      (CatFiberedInGroupoids.homFunctor j).Faithful :=
  full_and_faithful_homFunctor_of_mono_representingMaps B S hS j hj
    fun U y hy F hF he =>
      Space.mono_of_isImmersion B S hS
        (Space.isImmersion_of_isClosedImmersion B S hS (hci U y hy F hF he))

namespace AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **The implication (1) ⟹ (2) of Stacks 04ZZ: a monomorphism of algebraic stacks is fully
faithful.** A 1-morphism of algebraic stacks over `S` which is a monomorphism in the sense of
**Stacks 04ZW** has fully faithful underlying functor.

This is `AlgebraicGeometry.Stack.full_and_faithful_homFunctor_of_mono_representingMaps`
(**Stacks 05UK** with Stacks 003Z) read in the 2-category of algebraic stacks of Stacks 03YP. The
representability witness is the first conjunct of Stacks 04ZW, and its second conjunct gives the
monomorphy of each representing structural morphism in the category of algebraic spaces over `S`,
which **Stacks 042M** turns into monomorphy of the underlying morphism of presheaves. -/
@[stacks 04ZZ "the implication (1) ⟹ (2): a monomorphism of algebraic stacks is fully faithful"]
theorem full_and_faithful_homFunctor_of_isMonomorphism (f : 𝒳 ⟶ 𝒴)
    (hf : IsMonomorphism B S hS f) :
    (CatFiberedInGroupoids.homFunctor f.hom).Full ∧
      (CatFiberedInGroupoids.homFunctor f.hom).Faithful :=
  Stack.full_and_faithful_homFunctor_of_mono_representingMaps B S hS f.hom hf.1
    fun U z hz H hH he => (Space.mono_hom_iff_mono B S hS _).2 (hf.2 U z hz H hH he)

/-- **A closed immersion of algebraic stacks is fully faithful**, i.e. is a monomorphism in the
sense of Stacks 04ZZ part (2). This is
`AlgebraicGeometry.Stack.full_and_faithful_homFunctor_of_isClosedImmersion` read in the
2-category of algebraic stacks of Stacks 03YP, where the representability witness is the first
conjunct of **Stacks 04YL** part (2). -/
theorem full_and_faithful_homFunctor_of_isClosedImmersion (f : 𝒳 ⟶ 𝒴)
    (hf : IsClosedImmersion B S hS f) :
    (CatFiberedInGroupoids.homFunctor f.hom).Full ∧
      (CatFiberedInGroupoids.homFunctor f.hom).Faithful :=
  Stack.full_and_faithful_homFunctor_of_isClosedImmersion B S hS f.hom hf.1 hf.2

/-- **A closed immersion of algebraic stacks is injective on points.** It is fully faithful, and
a fully faithful 1-morphism is injective on points by **Stacks 0500**.

This is the input that `StacksFrontier.AlgebraicGeometry.Stacks.ThickeningComposition` records as
missing for the converse half of Stacks 0CJ9 part (2). -/
theorem injective_pointsMap_of_isClosedImmersion (f : 𝒳 ⟶ 𝒴)
    (hf : IsClosedImmersion B S hS f) :
    Function.Injective (AlgebraicStacks.pointsMap B S hS f) := by
  obtain ⟨_, _⟩ := full_and_faithful_homFunctor_of_isClosedImmersion B S hS f hf
  exact Stack.pointsMap_injective_of_fullyFaithful B S hS f

/-- **A 1-morphism of algebraic stacks whose underlying functor is an equivalence is bijective on
points.**

Injectivity is **Stacks 0500**, since an equivalence is fully faithful. For surjectivity, a
field-valued point `P` of the target is hit up to isomorphism by an object `x₀` of the source,
by essential surjectivity; but `x₀` need not lie over the *recorded* base of `P`, only over one
isomorphic to it, so it is transported along that isomorphism with
`CategoryTheory.Functor.IsFiberedInGroupoids.exists_obj_eq_of_iso` to an object `y` lying over
`P.base` on the nose. The field-valued point built on `y` then maps to the class of `P`, the
common refinement being its own image together with the composite of the transport isomorphism
and the essential-surjectivity isomorphism.

This is what makes a comparison of 2-fibre products *over different cospans* usable on points:
`AlgebraicGeometry.Stack.AlgebraicStacks.bijective_pointsMap_preHom` compares two models of one
cospan, and this compares two cospans whose apexes are equivalent — for instance the two models
`𝒵 ×_𝒴 𝒳` and `𝒵 ×_{𝒴'} 𝒳` identified by
`CategoryTheory.TwoFibreProductOver.isEquivalence_mapBase` when `𝒴 ⟶ 𝒴'` is fully faithful. -/
theorem bijective_pointsMap_of_isEquivalence (f : 𝒳 ⟶ 𝒴)
    [Functor.IsEquivalence (CatFiberedInGroupoids.homFunctor f.hom)] :
    Function.Bijective (AlgebraicStacks.pointsMap B S hS f) := by
  refine ⟨Stack.pointsMap_injective_of_fullyFaithful B S hS f, ?_⟩
  intro q
  obtain ⟨P, hP⟩ := Quotient.exists_rep q
  let G := CatFiberedInGroupoids.homFunctor f.hom
  have hG : G ⋙ 𝒴.val.val.p = 𝒳.val.val.p := CatFiberedInGroupoids.homFunctor_comp_p f.hom
  have hX : 𝒳.val.val.p.IsFiberedInGroupoids := Classical.choose 𝒳.property
  let x₀ := G.objPreimage P.obj
  let e : G.obj x₀ ≅ P.obj := G.objObjPreimageIso P.obj
  have hbase : 𝒴.val.val.p.obj (G.obj x₀) = 𝒳.val.val.p.obj x₀ := Functor.congr_obj hG x₀
  let c : P.base ≅ 𝒳.val.val.p.obj x₀ :=
    (eqToIso P.over).symm ≪≫ (𝒴.val.val.p.mapIso e).symm ≪≫ eqToIso hbase
  obtain ⟨y, hy, ⟨ey⟩⟩ := hX.exists_obj_eq_of_iso c
  -- `over` is a syntax token once the fppf topologies are in scope, so the field name of
  -- `AlgebraicGeometry.Stack.FieldValuedPoint` has to be escaped here, unlike in
  -- `StacksFrontier.AlgebraicGeometry.Stacks.PointsInjective`, which does not import them.
  let Q : FieldValuedPoint B S hS 𝒳.val.val :=
    { carrier := P.carrier
      field := P.field
      base := P.base
      isSpec := P.isSpec
      obj := y
      «over» := hy }
  refine ⟨pointClass B S hS 𝒳.val.val hX Q, ?_⟩
  rw [← hP]
  exact Quotient.sound
    ⟨fieldValuedPointMap B S hS 𝒳.val.val f.hom.hom Q, ⟨𝟙 _⟩, ⟨G.map ey.hom ≫ e.hom⟩⟩

end AlgebraicStacks

end AlgebraicGeometry.Stack

end
