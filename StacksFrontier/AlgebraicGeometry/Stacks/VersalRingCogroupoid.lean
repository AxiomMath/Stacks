module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalRing
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.Deformation.Completed.Pushout
public import StacksFrontier.Deformation.Groupoid.Basic
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.GroupoidQuotient.MinimalAutoequivalence
public import StacksFrontier.Deformation.Presentation

/-!
# Cogroupoids of complete local algebras (Stacks 0DR3)

**Stacks 0DR3** represents the deformation category `𝓕_{𝒳,k,x₀}` of a field-valued point of an
algebraic stack by a *cogroupoid* `(A, B, s, t, c)` of Noetherian complete local `Λ`-algebras with
residue field `k`: two such algebras `A`, `B`, two morphisms `s, t : A ⟶ B` and a
*comultiplication* `c : B ⟶ B ⊗̂_{s, A, t} B` for which the resulting source, target and
composition operations make the `T`-points of `B` a groupoid on the `T`-points of `A`, for every
complete local test algebra `T`.

This file supplies that comultiplication. The data `(A, B, s, t)` together with the composition
law is already in the library, as `Deformation.RepresentablePresentation` of
**Stacks 06K6** — there the composition law is recorded in its Yoneda-dual form, as a natural
transformation of the two corepresented functors. What is added here is the morphism `c` itself,
together with the identification of the composition law as "compose with `c`" and the cogroupoid
axioms in that form.

## Main definitions

* `Deformation.IsCogroupoid`: the cogroupoid law for `(A, B, s, t, c)` — on the points of every
  test object, source, target and the composition induced by `c` form a groupoid.
* `Deformation.RepresentablePresentation.comultiplication`: **Stacks 0DR3**, the morphism
  `c : B ⟶ B ⊗̂_{s, A, t} B` of a representable presentation. The completed tensor product is the
  pushout `B ⊗̂_{s, A, t} B` of `s` and `t`, which exists in the category of Noetherian complete
  local `Λ`-algebras by **Stacks 06SB**.

## Main results

* `Deformation.RepresentablePresentation.comp_app_down`: the composition law of a representable
  presentation is composition with `c` followed by the universal map out of the pushout. This is
  what makes `c` *the* comultiplication rather than some morphism to the pushout.
* `Deformation.RepresentablePresentation.isCogroupoid_comultiplication`: **Stacks 0DR3**, that
  `(A, B, s, t, c)` is a cogroupoid.
* `Deformation.RepresentablePresentation.source_comp_comultiplication` and
  `target_comp_comultiplication`: the two cogroupoid identities relating `c` to the two pushout
  inclusions, dual to "the source of a composite is the source of its second factor" and "the
  target of a composite is the target of its first factor".
* `Deformation.exists_cogroupoid_presentation`: **Stacks 0DR3**, the unwinding — a presentation
  of a category cofibered in groupoids over `𝒞_Λ` by a prorepresentable groupoid in functors is
  an equivalence `[A|_{𝒞_Λ} / B|_{𝒞_Λ}] ⟶ 𝓕` over `𝒞_Λ` for a cogroupoid `(A, B, s, t, c)` of
  Noetherian complete local `Λ`-algebras with residue field `k`.
* `AlgebraicGeometry.Stack.isVersalRingAt_base`: **Stacks 0DR3**, the last clause of the remark —
  the base of a versal formal object of `𝓕_{𝒳,k,x₀}` is a versal ring to `𝒳` at `x₀`.

## Implementation notes

`c` is read off the composition law at the pushout itself: the pair of pushout inclusions
`(inl, inr)` is a composable pair there, by the pushout condition, and `c` is its composite.
Naturality of the composition law in the test object then recovers the whole law from `c`, which
is `comp_app_down`; the two are therefore interchangeable, and the cogroupoid axioms transport
between them with no further input.

The functors of points in `Deformation.RepresentablePresentation` are universe-lifted
(`CategoryTheory.uliftCoyoneda`), so that they may take values in a universe larger than the
hom-universe of the ambient category. `Deformation.IsCogroupoid` is stated in that same lifted
form, so that it is literally the pointwise groupoid law carried by a representable presentation
with the composition law rewritten through `c`.

The statements about `c` are made for an arbitrary category, since nothing in them uses the
algebras: the case of the remark is `C = Deformation.CompleteLocalAlgCat Λ k`, where the pushout
required by `Deformation.RepresentablePresentation` is the completed tensor product supplied by
`Deformation.CompleteLocalAlgCat.hasPushouts`.

The unwinding is exactly the two existentials of prorepresentability (**Stacks 06KD**) and of
representability (**Stacks 06K6**) read in sequence, so the work in it is transporting the
presentation along the resulting isomorphism of groupoids in functors. That transport is
`Deformation.GroupoidInFunctors.presentationOfIso`, which rests on
`Deformation.GroupoidInFunctors.restrictIso` — restriction along a functor of base categories
carries an isomorphism of groupoids in functors to one of the restrictions — and on
`Deformation.GroupoidInFunctors.quotientEquivalenceOver`, which turns such an isomorphism into an
equivalence of the quotient categories over the base. The latter is strict: the induced functors
on quotients compose to the identity on the nose, by `Deformation.quotientMap_comp` and
`Deformation.quotientMap_id`, so the unit and counit are `eqToIso` and their verticality is
`CategoryTheory.IsHomLift.eqToHom_domain_lift_id`.

## References

* [Stacks Project, Tag 06K6](https://stacks.math.columbia.edu/tag/06K6)
* [Stacks Project, Tag 06SB](https://stacks.math.columbia.edu/tag/06SB)
* [Stacks Project, Tag 0DQV](https://stacks.math.columbia.edu/tag/0DQV)
* [Stacks Project, Tag 0DR3](https://stacks.math.columbia.edu/tag/0DR3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Deformation

universe u v w

section Cogroupoid

variable {C : Type u} [Category.{v} C]

/-- `(A, B, s, t, c)` is a *cogroupoid* when, for every test object `T`, the maps
`a ↦ s ≫ a` and `a ↦ t ≫ a` from the `T`-points of `B` to the `T`-points of `A`, together with
the composition `(a, b) ↦ c ≫ (a, b)` given by `c` and the universal property of the pushout,
make the `T`-points of `A` and `B` a groupoid. -/
def IsCogroupoid {A B : C} (s t : A ⟶ B) [HasPushout s t] (c : B ⟶ pushout s t) : Prop :=
  ∀ T : C, Nonempty (PointwiseGroupoid.{max w v}
    (fun a : ULift.{w} (B ⟶ T) => (ULift.up (s ≫ a.down) : ULift.{w} (A ⟶ T)))
    (fun a : ULift.{w} (B ⟶ T) => (ULift.up (t ≫ a.down) : ULift.{w} (A ⟶ T)))
    (fun q => ULift.up (c ≫ pushout.desc q.1.1.down q.1.2.down
      (show s ≫ q.1.1.down = t ≫ q.1.2.down from congrArg ULift.down q.2))))

end Cogroupoid

namespace RepresentablePresentation

variable {C : Type u} [Category.{v} C]

attribute [local instance] hasPushout

/-- The pair of pushout inclusions, as a composable pair of points of the arrow object over the
pushout itself. -/
def pushoutPair (P : RepresentablePresentation.{u, v, w} C) :
    (composableArrows (uliftCoyoneda.{w}.obj (op P.objects))
        (uliftCoyoneda.{w}.obj (op P.arrows))
        (uliftCoyoneda.{w}.map P.source.op)
        (uliftCoyoneda.{w}.map P.target.op)).obj (pushout P.source P.target) :=
  ⟨(ULift.up (pushout.inl P.source P.target), ULift.up (pushout.inr P.source P.target)),
    show ULift.up (P.source ≫ pushout.inl P.source P.target) =
        ULift.up (P.target ≫ pushout.inr P.source P.target) from
      congrArg ULift.up pushout.condition⟩

/-- **Stacks 0DR3.** The comultiplication `c : B ⟶ B ⊗̂_{s, A, t} B` of a representable
presentation `(A, B, s, t)`: the composite of the two pushout inclusions under the presentation's
composition law. -/
@[stacks 0DR3 "the comultiplication c : B ⟶ B ⊗̂_{s,A,t} B of the cogroupoid (A,B,s,t,c)"]
def comultiplication (P : RepresentablePresentation.{u, v, w} C) :
    P.arrows ⟶ pushout P.source P.target :=
  (P.comp.app (pushout P.source P.target) P.pushoutPair).down

/-- The composition law of a representable presentation is composition with the comultiplication
followed by the universal map out of the pushout. -/
theorem comp_app_down (P : RepresentablePresentation.{u, v, w} C) {T : C}
    (q : (composableArrows (uliftCoyoneda.{w}.obj (op P.objects))
        (uliftCoyoneda.{w}.obj (op P.arrows))
        (uliftCoyoneda.{w}.map P.source.op)
        (uliftCoyoneda.{w}.map P.target.op)).obj T) :
    (P.comp.app T q).down =
      P.comultiplication ≫ pushout.desc q.1.1.down q.1.2.down
        (show P.source ≫ q.1.1.down = P.target ≫ q.1.2.down from
          congrArg ULift.down q.2) := by
  have hq : P.source ≫ q.1.1.down = P.target ≫ q.1.2.down := congrArg ULift.down q.2
  have hpair : (composableArrows (uliftCoyoneda.{w}.obj (op P.objects))
      (uliftCoyoneda.{w}.obj (op P.arrows))
      (uliftCoyoneda.{w}.map P.source.op)
      (uliftCoyoneda.{w}.map P.target.op)).map
      (pushout.desc q.1.1.down q.1.2.down hq) P.pushoutPair = q := by
    apply Subtype.ext
    change (ULift.up (pushout.inl P.source P.target ≫
          pushout.desc q.1.1.down q.1.2.down hq),
        ULift.up (pushout.inr P.source P.target ≫
          pushout.desc q.1.1.down q.1.2.down hq)) = q.1
    rw [pushout.inl_desc, pushout.inr_desc]
    rfl
  have hnat := NatTrans.naturality_apply P.comp
    (pushout.desc q.1.1.down q.1.2.down hq) P.pushoutPair
  rw [hpair] at hnat
  rw [hnat]
  rfl

/-- **Stacks 0DR3.** A representable presentation `(A, B, s, t)` and its comultiplication `c` form
a cogroupoid. -/
@[stacks 0DR3 "(A,B,s,t,c) is a cogroupoid of complete local algebras"]
theorem isCogroupoid_comultiplication (P : RepresentablePresentation.{u, v, w} C) :
    IsCogroupoid.{u, v, w} P.source P.target P.comultiplication := by
  intro T
  obtain ⟨H⟩ := P.pointwiseGroupoid T
  exact ⟨{
    groupoid := H.groupoid
    arrowEquiv := H.arrowEquiv
    comp_eq := by
      intro x y z g f
      exact (H.comp_eq g f).trans (congrArg ULift.up (P.comp_app_down _)) }⟩

/-- The source of a composite is the source of its second factor: the cogroupoid identity
`s ≫ c = s ≫ inr`. -/
theorem source_comp_comultiplication (P : RepresentablePresentation.{u, v, w} C) :
    P.source ≫ P.comultiplication =
      P.source ≫ pushout.inr P.source P.target := by
  obtain ⟨H⟩ := P.pointwiseGroupoid (pushout P.source P.target)
  exact congrArg ULift.down (H.source_comp _ _ P.pushoutPair.2)

/-- The target of a composite is the target of its first factor: the cogroupoid identity
`t ≫ c = t ≫ inl`. -/
theorem target_comp_comultiplication (P : RepresentablePresentation.{u, v, w} C) :
    P.target ≫ P.comultiplication =
      P.target ≫ pushout.inl P.source P.target := by
  obtain ⟨H⟩ := P.pointwiseGroupoid (pushout P.source P.target)
  exact congrArg ULift.down (H.target_comp _ _ P.pushoutPair.2)

end RepresentablePresentation

namespace GroupoidInFunctors

universe u₁ v₁ y

/-- Restriction of a morphism of groupoids in functors along a functor of source categories. -/
def restrictMap {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    {G H : GroupoidInFunctors.{u₁, v₁, y} D} (α : G ⟶ H) (F : C ⥤ D) :
    G.restrict F ⟶ H.restrict F where
  mapObjects := Functor.whiskerLeft F α.mapObjects
  mapArrows := Functor.whiskerLeft F α.mapArrows
  map_source T a := α.map_source (F.obj T) a
  map_target T a := α.map_target (F.obj T) a
  map_id T x := α.map_id (F.obj T) x
  map_comp T a b h := α.map_comp (F.obj T) a b h

/-- Restricting the identity morphism of a groupoid in functors gives the identity. -/
theorem restrictMap_id {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    (G : GroupoidInFunctors.{u₁, v₁, y} D) (F : C ⥤ D) :
    restrictMap (𝟙 G) F = 𝟙 (G.restrict F) :=
  Hom.ext rfl rfl

/-- Restriction along a functor commutes with composition of morphisms of groupoids in functors. -/
theorem restrictMap_comp {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    {G H K : GroupoidInFunctors.{u₁, v₁, y} D} (α : G ⟶ H) (β : H ⟶ K) (F : C ⥤ D) :
    restrictMap (α ≫ β) F = restrictMap α F ≫ restrictMap β F :=
  Hom.ext rfl rfl

/-- An isomorphism of groupoids in functors restricts to an isomorphism of their
restrictions. -/
def restrictIso {C : Type u} {D : Type u₁} [Category.{v} C] [Category.{v₁} D]
    {G H : GroupoidInFunctors.{u₁, v₁, y} D} (e : G ≅ H) (F : C ⥤ D) :
    G.restrict F ≅ H.restrict F where
  hom := restrictMap e.hom F
  inv := restrictMap e.inv F
  hom_inv_id := by rw [← restrictMap_comp, e.hom_inv_id, restrictMap_id]
  inv_hom_id := by rw [← restrictMap_comp, e.inv_hom_id, restrictMap_id]

/-- An isomorphism of groupoids in functors induces an equivalence of their quotient categories
over the base category. -/
def quotientEquivalenceOver {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (e : G ≅ H) :
    StacksRepresentableCFG.EquivalenceOver
      (Grothendieck.forget (evaluationFunctor G))
      (Grothendieck.forget (evaluationFunctor H)) :=
  have h₁ : quotientMap e.hom ⋙ quotientMap e.inv =
      Functor.id (Grothendieck (evaluationFunctor G)) := by
    rw [← quotientMap_comp]
    have h : Hom.comp e.hom e.inv = Hom.id G := e.hom_inv_id
    rw [h, quotientMap_id]
  have h₂ : quotientMap e.inv ⋙ quotientMap e.hom =
      Functor.id (Grothendieck (evaluationFunctor H)) := by
    rw [← quotientMap_comp]
    have h : Hom.comp e.inv e.hom = Hom.id H := e.inv_hom_id
    rw [h, quotientMap_id]
  { hom := ⟨quotientMap e.hom, quotientMap_over e.hom⟩
    inv := ⟨quotientMap e.inv, quotientMap_over e.inv⟩
    unitIso := eqToIso h₁.symm
    counitIso := eqToIso h₂
    unit_over := by
      refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ ?_
      intro x
      simp only [eqToIso.hom, eqToHom_app]
      exact IsHomLift.eqToHom_domain_lift_id _ rfl
    counit_over := by
      refine StacksRepresentableCFG.whiskerRight_eq_eqToHom _ _ _ ?_
      intro x
      simp only [eqToIso.hom, eqToHom_app]
      exact IsHomLift.eqToHom_domain_lift_id _ rfl }

/-- A presentation of a category cofibered in groupoids by a groupoid in functors is a
presentation by any isomorphic groupoid in functors. -/
def presentationOfIso {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (e : G ≅ H)
    {F : Type u₁} [Category.{v₁} F] {p : F ⥤ C} (E : Presentation G p) :
    Presentation H p :=
  (quotientEquivalenceOver e.symm).trans E

end GroupoidInFunctors

section Unwinding

universe uΛ uk uz uF vF

variable {Λ : Type uΛ} {k : Type uk} [CommRing Λ] [Field k] [Algebra Λ k]

/-- **Stacks 0DR3.** Unwinding a presentation of a category cofibered in groupoids over `𝒞_Λ` by
a prorepresentable groupoid in functors: there are a cogroupoid `(A, B, s, t, c)` of Noetherian
complete local `Λ`-algebras with residue field `k` and an equivalence
`[A|_{𝒞_Λ} / B|_{𝒞_Λ}] ⟶ 𝓕` of groupoids cofibered over `𝒞_Λ`. -/
@[stacks 0DR3 "the equivalence [A/B] → 𝓕 of groupoids cofibred over 𝒞_Λ"]
theorem exists_cogroupoid_presentation
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{uΛ, v, uk} Λ k)
    {G : GroupoidInFunctors.{_, v, max v uz} (ArtinianLocalAlgCat.{uΛ, v, uk} Λ k)}
    (hG : GroupoidInFunctors.IsProrepresentable G) (E : Presentation G p) :
    ∃ P : RepresentablePresentation.{_, v, uz} (CompleteLocalAlgCat.{uΛ, v, uk} Λ k),
      IsCogroupoid.{_, v, uz} P.source P.target P.comultiplication ∧
        Nonempty (Presentation
          (GroupoidInFunctors.restrict P.groupoidInFunctors artinianToComplete) p) := by
  obtain ⟨H, hH, ⟨eGH⟩⟩ := hG
  obtain ⟨P, ⟨eHP⟩⟩ := hH
  exact ⟨P, P.isCogroupoid_comultiplication,
    ⟨GroupoidInFunctors.presentationOfIso
      (eGH ≪≫ GroupoidInFunctors.restrictIso eHP artinianToComplete) E⟩⟩

end Unwinding

end Deformation

namespace AlgebraicGeometry.Stack

open AlgebraicGeometry

universe u w

/-- **Stacks 0DR3**, last clause. The base of a versal formal object of the deformation category
of a field-valued point of `𝒳` is a versal ring to `𝒳` at that point. -/
@[stacks 0DR3 "A is a versal ring to 𝒳 at x₀"]
theorem isVersalRingAt_base
    (D : AlgebraicGeometry.Stack.VersalSituation.{u, w})
    {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (iΛ : Spec (.of Λ) ⟶ D.S) (hiΛ : _root_.AlgebraicGeometry.IsOpenImmersion iΛ)
    (x₀ : D.𝒳.val.val.obj)
    (hx₀ : (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion).obj x₀ =
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ))
    (hfinite : _root_.AlgebraicGeometry.LocallyOfFiniteType
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ) ∧
      _root_.AlgebraicGeometry.QuasiCompact
        (Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ iΛ)) :
    let C := Deformation.Artin.predeformationCategory iΛ
      (D.𝒳.val.val.p ⋙ Over.post D.B.inclusion) x₀ hx₀
    letI : Category C.carrier := C.category
    ∀ ξ : Deformation.FormalObject C.projection,
      Deformation.IsVersal
          (Deformation.Artin.predeformationCategory_isPredeformationCategory
            D.B D.hS iΛ D.𝒳.val.val.p x₀ hx₀ D.𝒳.val.property).cofibered ξ →
        IsVersalRingAt D iΛ hiΛ x₀ hx₀ hfinite ξ.base := by
  intro C ξ hξ
  exact ⟨ξ, rfl, hξ⟩

end AlgebraicGeometry.Stack

end
