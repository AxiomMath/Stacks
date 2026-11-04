module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Quotient.PresentedObjectCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackProjection
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase
public import StacksFrontier.CategoryTheory.TwoYoneda.Basic

/-!
# Points of a quotient stack from a presentation by a scheme

Let `G = (U, R, s, t, c)` be a groupoid in algebraic spaces over an algebraic space `B` over a
scheme `S` of a big fppf site and let `f : 𝒮_W ⟶ [U/R]` be a 1-morphism from the category of a
scheme of the site, representable by algebraic spaces. An object of `[U/R]` over a test object `T`
is, locally on `T`, in the image of the `W`-points of `[U/R]` as soon as the structural morphism
of every algebraic space representing a base change of `f` is a surjection of fppf sheaves.

## Main definitions

* `AlgebraicGeometry.Stack.schemePointFiber`: the object of a fibre of `𝒳` named by a point of the
  scheme a 1-morphism `𝒮_W ⟶ 𝒳` is defined on.
* `AlgebraicGeometry.Stack.presentedSchemeMap`: the 1-morphism `𝒮_V ⟶ [U/R]` presented by a point
  of the object space over `V`.

## Main results

* `AlgebraicGeometry.Stack.exists_local_point_of_locallySurjective_fiber`: a local point of `W`
  with the prescribed image, from local surjectivity of the structural morphism of a
  representation of the base change.
* `AlgebraicGeometry.Stack.presentedSchemeMapIso`: the 1-morphism presented by a point of the
  object space which presents the pullback of a `W`-point of `[U/R]` along `b : V ⟶ W` is
  2-isomorphic to `b` followed by that point.

## Implementation notes

A `W`-point of a category `𝒳` over the site is a 1-morphism out of the category of the slice over
`W`, and the 2-Yoneda lemma of Stacks 04SS identifies those with the objects of the fibre of `𝒳`
over `W`; `schemePointFiber` is the object the point of the slice `𝟙 : W ⟶ W` names, and
`schemePointPullbackIso` is the cartesian comparison which says that the object named by
`V ⟶ W` is its pullback. The identification is used in the form
`CategoryTheory.Functor.twoYonedaEvaluation`, which is an equivalence for a category fibred in
groupoids, so an isomorphism of the two fibre objects is an isomorphism of the two points.

## References

* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 044V](https://stacks.math.columbia.edu/tag/044V)
* [Stacks Project, Tag 044X](https://stacks.math.columbia.edu/tag/044X)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 04SS](https://stacks.math.columbia.edu/tag/04SS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

/- The category of a based category is reached through a projection, so the universe of the
morphisms of a 2-fibre product over one is not computed at implicit transparency; naming the
construction is what lets the instances for those 2-fibre products be found. -/
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

universe u w u₀ v₀ u₁ v₁ w₁ u₂ v₂

/-- The object of the fibre of `𝒳` over the base of a point of `W` that a 1-morphism
`𝒮_W ⟶ 𝒳` names at that point. -/
noncomputable def schemePointFiber
    {D : Type u₀} [Category.{v₀} D] {X : BasedCategory.{v₁, w₁} D} {W : D}
    (f : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ X) (V : Over W) :
    X.p.Fiber V.left := ⟨f.obj V, f.w_obj V⟩

/-- **Stacks 04SS.** The object a 1-morphism `𝒮_W ⟶ 𝒳` names at a point `V ⟶ W` is the chosen
pullback along it of the object named at the identity of `W`. -/
noncomputable def schemePointPullbackIso
    {D : Type u₀} [Category.{v₀} D] {X : BasedCategory.{v₁, w₁} D}
    [X.p.IsFibered] (hX : X.p.IsFiberedInGroupoids) {W : D}
    (f : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ X) (V : Over W) :
    Functor.pullbackFiber X.p (schemePointFiber f (Over.mk (𝟙 W))) V.hom ≅
      schemePointFiber f V := by
  let f' : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ BasedCategory.ofFunctor X.p :=
    ⟨f.toFunctor, f.w⟩
  haveI hc : X.p.IsStronglyCartesian V.hom (f.map (Over.mkIdTerminal.from V)) :=
    Functor.TwoYoneda.isStronglyCartesian_map_from_mkIdTerminal X.p hX W f' V
  exact Functor.fiberIsoOfCartesian V.hom
    (Functor.IsPreFibered.pullbackMap (schemePointFiber f (Over.mk (𝟙 W))).2 V.hom)
    (f.map (Over.mkIdTerminal.from V)) inferInstance
    (Functor.IsStronglyCartesian.isCartesian_of_isStronglyCartesian X.p V.hom
      (f.map (Over.mkIdTerminal.from V)))

/-- **Stacks 04SS.** Two 1-morphisms `𝒮_W ⟶ 𝒳` naming isomorphic objects of the fibre over `W`
are 2-isomorphic, the 2-Yoneda evaluation being an equivalence. -/
noncomputable def schemePointIsoOfFiberIso
    {D : Type u₀} [Category.{v₀} D] {X : BasedCategory.{v₁, w₁} D}
    (hX : X.p.IsFiberedInGroupoids) {W : D}
    (f g : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ X)
    (e : schemePointFiber f (Over.mk (𝟙 W)) ≅
      schemePointFiber g (Over.mk (𝟙 W))) : f ≅ g := by
  letI := Functor.twoYonedaEvaluation_isEquivalence X.p hX W
  exact (Functor.twoYonedaEvaluation X.p W).preimageIso e

/-- A point of the object space presenting the pullback of an object of `[U/R]` along `b` presents,
after restriction along `k`, the pullback of that object along `k ≫ b`. -/
theorem presented_refinement_pullback_iso
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {W V : BigFppfOver C S hS}
    (x : (quotientStack G).p.Fiber W) (b : V ⟶ W)
    (a : G.objects.obj.obj (op V))
    (ha : (pointwiseToQuotientStackFiber G V).obj a ≅
      Functor.pullbackFiber (quotientStack G).p x b)
    {T : BigFppfOver C S hS} (k : T ⟶ V) :
    Nonempty ((pointwiseToQuotientStackFiber G T).obj
        ((yonedaEquiv.symm a).app (op T) k) ≅
      Functor.pullbackFiber (quotientStack G).p x (k ≫ b)) :=
  ⟨(presentedPullbackIso G V a _ rfl (Over.mk k)).symm ≪≫
    Functor.pullbackFiberIso ha k ≪≫ Functor.pullbackFiberCompIso x b k⟩

/-- A point of the 2-fibre product of two scheme-valued points of `𝒳` is a morphism to the second
scheme together with an isomorphism of the two objects it names. -/
private theorem point_of_fiber_product
    {D : Type u₀} [Category.{v₀} D]
    {X : BasedCategory.{v₁, w₁} D} {W T : D}
    (f : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ X)
    (y : BasedCategory.ofFunctor (Over.forget T) ⥤ᵇ X)
    (r : TwoFibreProductOver (Over.forget T) (Over.forget W) X.p
      y.toFunctor f.toFunctor) :
    ∃ k : r.x.left ⟶ W, Nonempty
      (schemePointFiber f (Over.mk k) ≅ schemePointFiber y r.x) := by
  rcases r with ⟨V, A, ⟨L, ⟨⟨⟩⟩, k⟩, hA, hL, α, hα⟩
  change A.left = V at hA
  change L = V at hL
  subst V L
  exact ⟨k, ⟨{ hom := Functor.Fiber.homMk X.p A.left α.inv
               inv := Functor.Fiber.homMk X.p A.left α.hom
               hom_inv_id := Functor.Fiber.hom_ext α.inv_hom_id
               inv_hom_id := Functor.Fiber.hom_ext α.hom_inv_id }⟩⟩

/-- A section of an algebraic space representing the 2-fibre product of two scheme-valued points
of `𝒳` gives such a morphism and isomorphism. -/
private theorem exists_point_of_represented_fiber
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {X : BasedCategory.{v₁, w₁} (BigFppfOver C S hS)}
    {W T : BigFppfOver C S hS}
    (f : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ X)
    (y : BasedCategory.ofFunctor (Over.forget T) ⥤ᵇ X)
    (F : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map T.hom) (Over.forget W) X.p
        ((Over.iteratedSliceBackward T) ⋙ y.toFunctor) f.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (A : BigFppfOver C T.left.1 T.left.2) (a : F.obj (op A)) :
    ∃ k : (Over.map T.hom).obj A ⟶ W,
      Nonempty (schemePointFiber f (Over.mk k) ≅
        schemePointFiber y ((Over.iteratedSliceBackward T).obj A)) := by
  let r := e.inv.functor.obj ⟨A, Discrete.mk a⟩
  have hr : r.x = A := Functor.congr_obj e.inv.w ⟨A, Discrete.mk a⟩
  let r' : TwoFibreProductOver (Over.forget T) (Over.forget W) X.p
      y.toFunctor f.toFunctor :=
    ⟨r.base, (Over.iteratedSliceBackward T).obj r.x, r.y, r.hx, r.hy, r.iso,
      r.vertical⟩
  have h := point_of_fiber_product f y r'
  change ∃ k : (Over.map T.hom).obj r.x ⟶ W,
    Nonempty (schemePointFiber f (Over.mk k) ≅
      schemePointFiber y ((Over.iteratedSliceBackward T).obj r.x)) at h
  rwa [hr] at h

/-- If the structural morphism of an algebraic space representing the 2-fibre product of two
scheme-valued points of `𝒳` is a surjection of fppf sheaves, then the object named by the first
point is, locally on its test object, named by a point of the second scheme. -/
theorem exists_local_point_of_locallySurjective_fiber
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {X : BasedCategory.{v₁, w₁} (BigFppfOver C S hS)}
    {W T : BigFppfOver C S hS}
    (f : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ X)
    (y : BasedCategory.ofFunctor (Over.forget T) ⥤ᵇ X)
    (F : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace C T.left.1 T.left.2 F)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map T.hom) (Over.forget W) X.p
        ((Over.iteratedSliceBackward T) ⋙ y.toFunctor) f.toFunctor)
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (h : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
      (algebraicSpaceMap C S hS T
        ((spacesOverSmallerBaseFunctor C T.left.1 S T.left.2 hS T.hom).obj
          ⟨F, hF⟩)).hom) :
    ∃ R ∈ BigFppfOver.topology C S hS T,
      ∀ ⦃V⦄ (b : V ⟶ T), R b → ∃ k : V ⟶ W,
        Nonempty (schemePointFiber f (Over.mk k) ≅ schemePointFiber y (Over.mk b)) := by
  let A : AlgebraicSpaces C T.left.1 T.left.2 := ⟨F, hF⟩
  let p := (algebraicSpaceMap C S hS T
    ((spacesOverSmallerBaseFunctor C T.left.1 S T.left.2 hS T.hom).obj A)).hom
  let q := (spacesOverSmallerBaseFunctorForgetIso C T.left.1 S T.left.2 hS T.hom).inv.app A ≫ p
  let _ : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) p := h
  have hq : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) q :=
    inferInstance
  refine ⟨Presheaf.imageSieve q (𝟙 T), hq.1 (𝟙 T), ?_⟩
  rintro ⟨L, ⟨⟨⟩⟩, v⟩ b hb
  obtain ⟨⟨⟨ψ, a⟩, hψ⟩, hb⟩ := hb
  change L ⟶ T.left at ψ
  change F.obj (op (Over.mk ψ)) at a
  change L ⟶ C.obj hS at v
  change ψ ≫ T.hom = v at hψ
  subst v
  let s : ((OverShriek.relocalizePresheafFunctor T.hom).obj F).obj
      (op (Over.mk (ψ ≫ T.hom))) := ⟨⟨ψ, a⟩, rfl⟩
  obtain rfl : (Over.homMk ψ : Over.mk (ψ ≫ T.hom) ⟶ T) = b :=
    (spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app
      C T.left.1 S T.left.2 hS T.hom A (op (Over.mk (ψ ≫ T.hom))) s).symm.trans hb
  exact exists_point_of_represented_fiber C S hS f y F e (Over.mk ψ) a

/-- The object a 1-morphism `𝒮_W ⟶ 𝒳` names at a composite `T ⟶ V ⟶ W` is the pullback along
`T ⟶ V` of the object it names at `V ⟶ W`. -/
noncomputable def schemePointPullbackCompIso
    {D : Type u₀} [Category.{v₀} D] {X : BasedCategory.{v₁, w₁} D}
    [X.p.IsFibered] (hX : X.p.IsFiberedInGroupoids) {W V T : D}
    (f : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ X) (k : V ⟶ W) (b : T ⟶ V) :
    Functor.pullbackFiber X.p (schemePointFiber f (Over.mk k)) b ≅
      schemePointFiber f (Over.mk (b ≫ k)) :=
  Functor.pullbackFiberIso (schemePointPullbackIso hX f (Over.mk k)).symm b ≪≫
    Functor.pullbackFiberCompIso (schemePointFiber f (Over.mk (𝟙 W))) k b ≪≫
    schemePointPullbackIso hX f (Over.mk (b ≫ k))

/-- The 1-morphism from the category of the slice over `V` to the category of a presheaf induced
by a section of that presheaf over `V`: a point of the slice is sent to the restriction of the
section along it. -/
def presheafSectionFunctor
    {D : Type u₀} [Category.{v₀} D] {V : D} {F : Dᵒᵖ ⥤ Type v₀}
    (a : yoneda.obj V ⟶ F) :
    BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ
      presheafOfCategories (F ⋙ typeToCat) where
  toFunctor := {
    obj T := ⟨T.left, Discrete.mk (a.app (op T.left) T.hom)⟩
    map k := {
      base := k.left
      fiber := eqToHom (by
        apply Discrete.ext
        change a.app (op _) _ = F.map k.left.op (a.app (op _) _)
        rw [← NatTrans.naturality_apply]
        change a.app (op _) _ = a.app (op _) (k.left ≫ _)
        rw [Over.w]) }
    map_id T := by
      refine Pseudofunctor.CoGrothendieck.Hom.ext
        (F := (F ⋙ typeToCat).toPseudofunctor') _ _ ?_ ?_
      · rfl
      · exact Discrete.hom_eq
    map_comp k l := by
      refine Pseudofunctor.CoGrothendieck.Hom.ext
        (F := (F ⋙ typeToCat).toPseudofunctor') _ _ ?_ ?_
      · rfl
      · exact Discrete.hom_eq }
  w := rfl

/-- The inverse 1-morphism of the identification of the category of the presheaf represented by
`V` with the category of the slice over `V`. -/
private def presheafYonedaInverse
    {D : Type u₀} [Category.{v₀} D] (V : D) :
    presheafOfCategories (yoneda.obj V ⋙ typeToCat) ⥤ᵇ
      BasedCategory.ofFunctor (Over.forget V) where
  toFunctor := {
    obj x := Over.mk (Discrete.as x.fiber)
    map {x y} k := Over.homMk k.base (by
      exact (@Discrete.eq_of_hom (x.base ⟶ V) x.fiber
        (Discrete.mk (k.base ≫ Discrete.as y.fiber)) k.fiber).symm)
    map_id x := rfl
    map_comp k l := rfl }
  w := rfl

attribute [local implicit_reducible] presheafSectionFunctor presheafYonedaInverse

/-- **Stacks 025Z.** The category of the slice over `V` is the category of the presheaf
represented by `V`, by an equivalence over the site. -/
private def presheafYonedaEquivalence
    {D : Type u₀} [Category.{v₀} D] (V : D) :
    StacksRepresentableCFG.EquivalenceOver (Over.forget V)
      (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p where
  hom := ⟨(presheafSectionFunctor (𝟙 (yoneda.obj V))).toFunctor, rfl⟩
  inv := ⟨(presheafYonedaInverse V).toFunctor, rfl⟩
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro x y k
    simp only [Iso.refl_hom, Functor.id_map]
    refine Pseudofunctor.CoGrothendieck.Hom.ext
      (F := (yoneda.obj V ⋙ typeToCat).toPseudofunctor') _ _ ?_ ?_
    · change k.base ≫ 𝟙 _ = 𝟙 _ ≫ k.base
      simp
    · exact Discrete.hom_eq)
  unit_over := by
    ext x
    simp
  counit_over := by
    ext x
    exact (presheafOfCategories (yoneda.obj V ⋙ typeToCat)).p.map_id x

/-- The 1-morphism induced by the identity section of a representable presheaf is an
equivalence. -/
private theorem presheafSectionFunctor_id_isEquivalence
    {D : Type u₀} [Category.{v₀} D] (V : D) :
    (presheafSectionFunctor (𝟙 (yoneda.obj V))).toFunctor.IsEquivalence :=
  (presheafYonedaEquivalence V).toEquivalence.isEquivalence_functor

/-- **Stacks 044R.** The 1-morphism `𝒮_V ⟶ [U/R]` presented by a point of the object space over
`V`: the point, followed by the canonical projection of the quotient stack. -/
noncomputable def presentedSchemeMap
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {V : BigFppfOver C S hS} (a : yoneda.obj V ⟶ G.objects.obj) :
    BasedCategory.ofFunctor (Over.forget V) ⥤ᵇ quotientStack G :=
  BasedFunctor.comp (presheafSectionFunctor a) (quotientStackProjection G)

/-- The object of `[U/R]` that the 1-morphism presented by a point of the object space names at a
point of the slice is the object presented by the restricted point. -/
noncomputable def presentedSchemeMapFiberIso
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {V : BigFppfOver C S hS} (a : yoneda.obj V ⟶ G.objects.obj)
    (T : Over V) :
    schemePointFiber (presentedSchemeMap G a) T ≅
      (pointwiseToQuotientStackFiber G T.left).obj
        (a.app (op T.left) T.hom) :=
  eqToIso (Subtype.ext (quotientStackProjection_obj G _))

/-- A point of the object space over `V` presenting the pullback along `b : V ⟶ W` of the object
named by a 1-morphism `𝒮_W ⟶ [U/R]` presents the 1-morphism `𝒮_V ⟶ [U/R]` that `b` induces from
it. -/
noncomputable def presentedSchemeMapIso
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {V W : BigFppfOver C S hS}
    (f : BasedCategory.ofFunctor (Over.forget W) ⥤ᵇ quotientStack G)
    (b : V ⟶ W) (a : G.objects.obj.obj (op V))
    (e : (pointwiseToQuotientStackFiber G V).obj a ≅
      Functor.pullbackFiber (quotientStack G).p
        (schemePointFiber f (Over.mk (𝟙 W))) b) :
    presentedSchemeMap G (yonedaEquiv.symm a) ≅
      BasedFunctor.comp ⟨Over.map b, rfl⟩ f := by
  apply schemePointIsoOfFiberIso (isFiberedInGroupoids_quotientStack G)
  refine presentedSchemeMapFiberIso G _ (Over.mk (𝟙 V)) ≪≫ ?_ ≪≫ e ≪≫
    schemePointPullbackIso (isFiberedInGroupoids_quotientStack G)
      f (Over.mk b) ≪≫ ?_
  · exact eqToIso (by simp [yonedaEquiv])
  · exact eqToIso (by
      change schemePointFiber f (Over.mk b) =
        schemePointFiber f (Over.mk (𝟙 V ≫ b))
      rw [Category.id_comp])

/-- Every object of a fibre of `[U/R]` over a test object is, locally on that test object,
isomorphic to the object named by a point of `W` through a 1-morphism `𝒮_W ⟶ [U/R]` whose base
changes to algebraic spaces are surjective, flat and locally of finite presentation. -/
theorem exists_local_schemePoint_of_atlas
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B : AlgebraicSpaces C S hS} (G : GroupoidInAlgebraicSpaces C S hS B)
    (W : BigFppfOver C S hS)
    (f : (schemeFibredCategory C S hS W).val ⥤ᵇ quotientStack G)
    (hf : IsRepresentableByAlgebraicSpaces C S hS f)
    (hatlas : ∀ (T : BigFppfOver C S hS)
      (y : BigFppfOver C T.left.1 T.left.2 ⥤ (quotientStack G).obj)
      (_hy : y ⋙ (quotientStack G).p = Over.map T.hom)
      (F : (BigFppfOver C T.left.1 T.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace C T.left.1 T.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map T.hom)
          (schemeFibredCategory C S hS W).val.p (quotientStack G).p y f.toFunctor)
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS)
        (algebraicSpaceMap C S hS T
          ((spacesOverSmallerBaseFunctor C T.left.1 S T.left.2 hS T.hom).obj ⟨F, hF⟩)).hom)
    (T : BigFppfOver C S hS) (z : (quotientStack G).p.Fiber T) :
    ∃ R ∈ BigFppfOver.topology C S hS T,
      ∀ ⦃A⦄ (d : A ⟶ T), R d → ∃ k : A ⟶ W,
        Nonempty (schemePointFiber f (Over.mk k) ≅
          Functor.pullbackFiber (quotientStack G).p z d) := by
  have hFibered := isFiberedInGroupoids_quotientStack G
  let p := (quotientStack G).p
  let y₀ := Functor.TwoYoneda.liftBased p hFibered T z
  let y : BasedCategory.ofFunctor (Over.forget T) ⥤ᵇ quotientStack G := ⟨y₀.toFunctor, y₀.w⟩
  let y' := Over.iteratedSliceBackward T ⋙ y.toFunctor
  have hy' : y' ⋙ p = Over.map T.hom := by
    rw [Functor.assoc, y.w]
    rfl
  obtain ⟨F, hF, ⟨e⟩⟩ := hf T y' hy'
  obtain ⟨R, hR, hlocal⟩ := exists_local_point_of_locallySurjective_fiber C S hS f y F hF e
    (hatlas T y' hy' F hF ⟨e⟩)
  let c := Functor.TwoYoneda.chosenLift p hFibered T z (Over.mk (𝟙 T))
  have hlift : p.IsHomLift (𝟙 T) c.φ := c.isStronglyCartesian.toIsHomLift
  let m : schemePointFiber y (Over.mk (𝟙 T)) ⟶ z := Functor.Fiber.homMk p T c.φ
  have : IsIso m := (hFibered.fiber_isGroupoid T).all_isIso m
  refine ⟨R, hR, fun A d hd => ?_⟩
  obtain ⟨k, ⟨ek⟩⟩ := hlocal d hd
  exact ⟨k, ⟨ek ≪≫ (schemePointPullbackIso hFibered y (Over.mk d)).symm ≪≫
    Functor.pullbackFiberIso (asIso m) d⟩⟩

end AlgebraicGeometry.Stack

end
