module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaQuotientStackSquareFibred
public import StacksFrontier.AlgebraicGeometry.Stacks.IntegralAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductSquareAlgebraicStack
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFirstFactor
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality

/-!
# The stabilizer as the inertia of a presentation, in the 2-category of algebraic stacks

Let `𝒳` be an algebraic stack over `S` and let `[U/R] ⟶ 𝒳` be a presentation. Let `G/U` be the
stabilizer group algebraic space associated to the presenting groupoid `(U, R, s, t, c)`. Then

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
ℐ_𝒳  ------>  𝒳
```

is a fibre product diagram in the 2-category `AlgebraicGeometry.Stack.AlgebraicStacks` of
algebraic stacks over `S`, the lower horizontal arrow being the composite `𝒮_U ⟶ [U/R] ⟶ 𝒳`.

## Main definitions

* `AlgebraicGeometry.Stack.presentationStabilizerAlgebraicStack` and
  `AlgebraicGeometry.Stack.presentationObjectAlgebraicStack`: the stabilizer group algebraic space
  `G` and the object space `U` of the presenting groupoid, read as algebraic stacks over `S`
  through `AlgebraicGeometry.Stack.algebraicSpaceStack`.
* `AlgebraicGeometry.Stack.presentationObjectMorphismAlgebraicStacks`: the lower horizontal
  1-morphism `𝒮_U ⟶ 𝒳`, the projection of Stacks 044R followed by the presenting 1-morphism.
* `AlgebraicGeometry.Stack.presentationStabilizerToInertiaAlgebraicStacks`: the left vertical
  1-morphism `𝒮_G ⟶ ℐ_𝒳`, the left arrow of the diagram of Stacks 06PC followed by the
  functoriality of the inertia along the presenting 1-morphism.
* `AlgebraicGeometry.Stack.inertiaPresentationSquareAlgebraicStacks`: the diagram above, as a
  2-commutative square of algebraic stacks.

## Main results

* `CategoryTheory.Functor.isEquivalence_of_comp_eq_comp₄`: a functor is an equivalence as soon as
  composing it with an equivalence produces a composite of four equivalences.
* `CategoryTheory.RelativeInertia.faithful_functoriality` and
  `CategoryTheory.RelativeInertia.full_functoriality`: the functoriality of the inertia along a
  faithful, respectively fully faithful, functor is faithful, respectively full.
* `CategoryTheory.RelativeInertia.isEquivalence_functoriality`: the functoriality 1-morphism
  `ℐ_𝒳 ⟶ ℐ_𝒴` of the inertia along a 1-morphism over the base whose underlying functor is an
  equivalence is again an equivalence.
* `AlgebraicGeometry.Stack.isTwoFibreProduct_inertiaPresentationSquareAlgebraicStacks` and
  `AlgebraicGeometry.Stack.nonempty_isTwoFibreProduct_inertiaPresentationSquareAlgebraicStacks`:
  the diagram above is a 2-fibre product in the 2-category of algebraic stacks.

## References

* [Stacks Project, Tag 0448](https://stacks.math.columbia.edu/tag/0448)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 03YP](https://stacks.math.columbia.edu/tag/03YP)
* [Stacks Project, Tag 04TI](https://stacks.math.columbia.edu/tag/04TI)
* [Stacks Project, Tag 06PB](https://stacks.math.columbia.edu/tag/06PB)
* [Stacks Project, Tag 06PC](https://stacks.math.columbia.edu/tag/06PC)
* [Stacks Project, Tag 06PR](https://stacks.math.columbia.edu/tag/06PR)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

universe v₀ v₁ v₂ v₃ v₄ v₅ u₀ u₁ u₂ u₃ u₄ u₅

/-- A functor `F` is an equivalence as soon as its composite `F ⋙ G` with an equivalence `G` is
equal to a composite of four equivalences. -/
theorem isEquivalence_of_comp_eq_comp₄ {A₀ : Type u₀} [Category.{v₀} A₀] {A₁ : Type u₁}
    [Category.{v₁} A₁] {A₂ : Type u₂} [Category.{v₂} A₂] {A₃ : Type u₃} [Category.{v₃} A₃]
    {A₄ : Type u₄} [Category.{v₄} A₄] {A₅ : Type u₅} [Category.{v₅} A₅]
    (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₂) (H₁ : A₀ ⥤ A₃) (H₂ : A₃ ⥤ A₄) (H₃ : A₄ ⥤ A₅) (H₄ : A₅ ⥤ A₂)
    (hG : G.IsEquivalence) (h₁ : H₁.IsEquivalence) (h₂ : H₂.IsEquivalence)
    (h₃ : H₃.IsEquivalence) (h₄ : H₄.IsEquivalence) (h : F ⋙ G = H₁ ⋙ H₂ ⋙ H₃ ⋙ H₄) :
    F.IsEquivalence := by
  have : (F ⋙ G).IsEquivalence := by rw [h]; infer_instance
  exact Functor.isEquivalence_of_comp_right F G

end CategoryTheory.Functor

namespace CategoryTheory.RelativeInertia

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] {S : Type u₂} [Category.{v₂} S]
  {S' : Type u₃} [Category.{v₃} S']

/-- The functoriality 1-morphism `I_F : I_S ⥤ I_{S'}` of the inertia is faithful as soon as `F`
is. -/
theorem faithful_functoriality (p : S ⥤ C) (p' : S' ⥤ C) (F : S ⥤ S') (hF : F ⋙ p' = p)
    [F.Faithful] : (functoriality p p' F hF).Faithful where
  map_injective {_ _} _ _ h :=
    RelativeInertiaHom.ext (F.map_injective (congrArg RelativeInertiaHom.hom h))

/-- The functoriality 1-morphism `I_F : I_S ⥤ I_{S'}` of the inertia is full as soon as `F` is
fully faithful. -/
theorem full_functoriality (p : S ⥤ C) (p' : S' ⥤ C) (F : S ⥤ S') (hF : F ⋙ p' = p)
    [F.Full] [F.Faithful] : (functoriality p p' F hF).Full where
  map_surjective {A B} ψ := by
    obtain ⟨φ, hφ⟩ := F.map_surjective ψ.hom
    refine ⟨⟨φ, F.map_injective ?_⟩, RelativeInertiaHom.ext hφ⟩
    rw [F.map_comp, F.map_comp, hφ]
    exact ψ.comm

/-- Let `p : S ⥤ C` and `p' : S' ⥤ C` be categories over `C` and let `F : S ⥤ S'` be a 1-morphism
over `C` whose underlying functor is an equivalence of categories. Then
`CategoryTheory.RelativeInertia.functoriality`, `(x, α) ↦ (F x, F α)`, is an equivalence
`I_S ⥤ I_{S'}`. -/
theorem isEquivalence_functoriality (p : S ⥤ C) (p' : S' ⥤ C) (F : S ⥤ S') (hF : F ⋙ p' = p)
    [F.IsEquivalence] : (functoriality p p' F hF).IsEquivalence := by
  subst hF
  have := faithful_functoriality (F ⋙ p') p' F rfl
  have := full_functoriality (F ⋙ p') p' F rfl
  have : (functoriality (F ⋙ p') p' F rfl).EssSurj := by
    refine ⟨fun Bq ↦ ?_⟩
    let ff := Functor.FullyFaithful.ofFullyFaithful F
    let x := F.objPreimage Bq.obj
    let e : F.obj x ≅ Bq.obj := F.objObjPreimageIso Bq.obj
    let α : Aut x := .of (ff.preimageIso (e ≪≫ Bq.auto.asIso ≪≫ e.symm))
    have hmap : F.map α.asIso.hom = e.hom ≫ Bq.auto.asIso.hom ≫ e.inv := ff.map_preimage _
    refine ⟨⟨x, α, ?_⟩, ⟨?_⟩⟩
    · show p'.map (F.map α.asIso.hom) = 𝟙 _
      rw [hmap]
      simp [← p'.map_comp, Bq.cond]
    · refine ⟨⟨e.hom, ?_⟩, ⟨e.inv, ?_⟩, ?_, ?_⟩
      · show e.hom ≫ Bq.auto.asIso.hom = F.map α.asIso.hom ≫ e.hom
        simp [hmap]
      · show e.inv ≫ F.map α.asIso.hom = Bq.auto.asIso.hom ≫ e.inv
        simp [hmap]
      · exact RelativeInertiaHom.ext e.hom_inv_id
      · exact RelativeInertiaHom.ext e.inv_hom_id
  exact Functor.IsEquivalence.mk

end CategoryTheory.RelativeInertia

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : AlgebraicStacks.{u, w} B S hS} (P : GroupoidPresentation B S hS 𝒳.val.val)

/-- The functoriality `ℐ_{[U/R]} ⟶ ℐ_𝒳`, `(x, α) ↦ (f x, f α)`, of the inertia along the
presenting 1-morphism `f : [U/R] ⟶ 𝒳` of a presentation, as a functor over the big fppf site. -/
noncomputable def inertiaPresentationFunctoriality :
    (inertia.{u, u + 1, u + 1} B S hS (quotientStackCFG B S hS P.groupoid)).val ⥤ᵇ
      (inertia.{u, u, u + 1} B S hS 𝒳.val).val where
  toFunctor := RelativeInertia.functoriality (quotientStack P.groupoid).p 𝒳.val.val.p
    P.basedFunctor.toFunctor P.basedFunctor.w
  w := RelativeInertia.functoriality_comp_toBase _ _ _ _

/-- The stabilizer group algebraic space `G/U` of Stacks 0448 of the presenting groupoid of a
presentation, read as an algebraic stack over `S`. -/
noncomputable abbrev presentationStabilizerAlgebraicStack : AlgebraicStacks.{u, w} B S hS :=
  algebraicSpaceStack.{u, w} B S hS
    (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid).obj
    (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid).property

/-- The object space `U` of the presenting groupoid of a presentation, read as an algebraic stack
over `S`. -/
noncomputable abbrev presentationObjectAlgebraicStack : AlgebraicStacks.{u, w} B S hS :=
  algebraicSpaceStack.{u, w} B S hS P.groupoid.objects.obj P.groupoid.objects.property

/-- The 1-morphism `𝒮_U ⟶ 𝒳`: the projection
`𝒮_U ⟶ [U/R]` of Stacks 044R followed by the presenting 1-morphism `[U/R] ⟶ 𝒳`, read in the
2-category of algebraic stacks over `S`. -/
noncomputable def presentationObjectMorphismAlgebraicStacks :
    presentationObjectAlgebraicStack B S hS P ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp (quotientStackProjection P.groupoid) P.basedFunctor))

/-- The 1-morphism `𝒮_G ⟶ 𝒮_U` induced by the structure morphism `G ⟶ U` of the stabilizer, the
object map of the forgetful morphism of the inertia groupoid of Stacks 06PB. -/
noncomputable def presentationStabilizerProjectionAlgebraicStacks :
    presentationStabilizerAlgebraicStack B S hS P ⟶ presentationObjectAlgebraicStack B S hS P :=
  Bicategory.InducedBicategory.mkHom
    (associatedMap B S hS
      (GroupoidInAlgebraicSpaces.inertiaForgetful P.groupoid).objectsMap.hom).1

/-- The 1-morphism `𝒮_G ⟶ ℐ_𝒳`: the universe lift
`𝒮_G ⟶ 𝒮_G'`, followed by the left arrow `𝒮_G' ⟶ ℐ_{[U/R]}` of the diagram of Stacks 06PC — the
projection of Stacks 044R for the inertia groupoid of Stacks 06PB composed with the comparison of
the second assertion of Stacks 06PB — followed by the functoriality of the inertia along the
presenting 1-morphism. -/
noncomputable def presentationStabilizerToInertiaAlgebraicStacks :
    presentationStabilizerAlgebraicStack B S hS P ⟶ inertiaAlgebraicStack B S hS 𝒳 :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    (BasedFunctor.comp
      (liftedFibredCategoryUp (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid))
      (BasedFunctor.comp (quotientStackInertiaSquare P.groupoid).fst.hom
        (inertiaPresentationFunctoriality B S hS P))))

/-- For an algebraic stack
`𝒳` over `S` with a presentation `[U/R] ⟶ 𝒳` whose presenting groupoid is `(U, R, s, t, c)` and
whose stabilizer group algebraic space is `G/U` (Stacks 0448), the 2-commutative square

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
ℐ_𝒳  ------>  𝒳
```

of algebraic stacks over `S`, whose 2-cell is that of the diagram of Stacks 06PC read through the
presenting 1-morphism. -/
noncomputable def inertiaPresentationSquareAlgebraicStacks :
    Bicategory.TwoCommSq (inertiaProjectionAlgebraicStacks B S hS 𝒳)
      (presentationObjectMorphismAlgebraicStacks B S hS P) where
  pt := presentationStabilizerAlgebraicStack B S hS P
  fst := presentationStabilizerToInertiaAlgebraicStacks B S hS P
  snd := presentationStabilizerProjectionAlgebraicStacks B S hS P
  iso := Bicategory.InducedBicategory.isoMk (Bicategory.InducedBicategory.isoMk
    (BasedNatIso.mkNatIso
      (Functor.isoWhiskerLeft
          (liftedFibredCategoryUp
            (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid)).toFunctor
        (Functor.isoWhiskerRight
          (CatFiberedInGroupoids.underlyingIso (quotientStackInertiaSquare P.groupoid).iso)
          P.basedFunctor.toFunctor))
      (fun a ↦ by
        have : (quotientStack P.groupoid).p.IsHomLift
            (𝟙 ((presentationStabilizerAlgebraicStack B S hS P).val.val.p.obj a))
            ((CatFiberedInGroupoids.underlyingIso
              (quotientStackInertiaSquare P.groupoid).iso).hom.app
                ((liftedFibredCategoryUp
                  (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid)).toFunctor.obj a)) :=
          (quotientStackInertiaSquare P.groupoid).iso.hom.hom.isHomLift' _
        exact Functor.isHomLift_map_of_comp_eq P.basedFunctor.w _ _)))

/-- The apex of `AlgebraicGeometry.Stack.inertiaPresentationSquareAlgebraicStacks` is the algebraic
stack of the stabilizer group algebraic space `G/U` of Stacks 0448. -/
theorem inertiaPresentationSquareAlgebraicStacks_pt :
    (inertiaPresentationSquareAlgebraicStacks B S hS P).pt =
      presentationStabilizerAlgebraicStack B S hS P := rfl

/-- The first leg of `AlgebraicGeometry.Stack.inertiaPresentationSquareAlgebraicStacks` is the
1-morphism `𝒮_G ⟶ ℐ_𝒳`. -/
theorem inertiaPresentationSquareAlgebraicStacks_fst :
    (inertiaPresentationSquareAlgebraicStacks B S hS P).fst =
      presentationStabilizerToInertiaAlgebraicStacks B S hS P := rfl

/-- The second leg of `AlgebraicGeometry.Stack.inertiaPresentationSquareAlgebraicStacks` is the
1-morphism `𝒮_G ⟶ 𝒮_U` induced by the structure morphism `G ⟶ U` of the stabilizer. -/
theorem inertiaPresentationSquareAlgebraicStacks_snd :
    (inertiaPresentationSquareAlgebraicStacks B S hS P).snd =
      presentationStabilizerProjectionAlgebraicStacks B S hS P := rfl

/-- The canonical comparison `𝒮_G ⟶ ℐ_𝒳 ×_𝒳 𝒮_U` of
`AlgebraicGeometry.Stack.inertiaPresentationSquareAlgebraicStacks` with the 2-fibre product of
its cospan is an equivalence of categories. -/
theorem isEquivalence_lift_inertiaPresentationSquareAlgebraicStacks :
    Functor.IsEquivalence
      (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1}
        (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom
        (presentationObjectMorphismAlgebraicStacks B S hS P).hom
        (inertiaPresentationSquareAlgebraicStacks B S hS P).underlying).hom.toFunctor :=
  @Functor.isEquivalence_of_comp_eq_comp₄ _ _ _ TwoFibreProductOver.instCategory
    _ TwoFibreProductOver.instCategory _ _ _ TwoFibreProductOver.instCategory
    _ TwoFibreProductOver.instCategory
    (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u, u + 1, u + 1}
      (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom
      (presentationObjectMorphismAlgebraicStacks B S hS P).hom
      (inertiaPresentationSquareAlgebraicStacks B S hS P).underlying).hom.toFunctor
    (TwoFibreProductOver.precomposeSnd
      (pT := (inertia.{u, u, u + 1} B S hS 𝒳.val).val.p) (pℬ := 𝒳.val.val.p)
      (p𝒜' := (fibredCategory B S hS P.groupoid.objects.obj).val.p)
      (p𝒜 := (liftedSpaceStack P.groupoid.objects).val.p)
      (RelativeInertia.π 𝒳.val.val.p)
      ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
      (liftedFibredCategoryUp P.groupoid.objects).toFunctor rfl)
    (liftedFibredCategoryUp
      (GroupoidInAlgebraicSpaces.stabilizerOverBase P.groupoid)).toFunctor
    (CatFiberedInGroupoids.liftTwoFibreProductSquare.{u, u + 1, u + 1, u + 1}
      (inertiaCatProjection B S hS (quotientStackCFG B S hS P.groupoid))
      (Bicategory.InducedBicategory.mkHom (liftedQuotientStackProjection P.groupoid) :
        liftedSpaceStack P.groupoid.objects ⟶ quotientStackCFG B S hS P.groupoid)
      (quotientStackInertiaSquare P.groupoid)).hom.toFunctor
    (TwoFibreProductOver.mapBase
      (pT := (inertia.{u, u + 1, u + 1} B S hS
        (quotientStackCFG B S hS P.groupoid)).val.p)
      (p𝒜 := (liftedSpaceStack P.groupoid.objects).val.p)
      (RelativeInertia.π (quotientStack P.groupoid).p)
      (liftedQuotientStackProjection P.groupoid).toFunctor
      P.basedFunctor.toFunctor P.basedFunctor.w)
    (TwoFibreProductOver.precomposeFst
      (inertia.{u, u + 1, u + 1} B S hS (quotientStackCFG B S hS P.groupoid)).val.p
      (inertia.{u, u, u + 1} B S hS 𝒳.val).val.p
      (liftedSpaceStack P.groupoid.objects).val.p 𝒳.val.val.p
      (RelativeInertia.π 𝒳.val.val.p)
      ((liftedQuotientStackProjection P.groupoid).toFunctor ⋙ P.basedFunctor.toFunctor)
      (RelativeInertia.functoriality (quotientStack P.groupoid).p 𝒳.val.val.p
        P.basedFunctor.toFunctor P.basedFunctor.w)
      (RelativeInertia.functoriality_comp_toBase _ _ _ _))
    (TwoFibreProductOver.isEquivalence_precomposeSnd
      (inertia.{u, u, u + 1} B S hS 𝒳.val).isFiberedInGroupoids
      (fibredCategory B S hS P.groupoid.objects.obj).isFiberedInGroupoids
      (liftedSpaceStack P.groupoid.objects).isFiberedInGroupoids rfl
      (BasedFunctor.comp (liftedQuotientStackProjection P.groupoid) P.basedFunctor).w)
    (isEquivalence_liftedFibredCategoryUp _)
    (Bicategory.isEquivalence_of_isTwoFibreProduct
      (isTwoFibreProduct_quotientStackInertiaSquare P.groupoid)
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _)
      (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u + 1, u + 1, u + 1} _ _
        (quotientStackInertiaSquare P.groupoid)))
    (TwoFibreProductOver.isEquivalence_mapBase P.basedFunctor.w)
    (TwoFibreProductOver.isEquivalence_precomposeFst _ _ _ _ _ _ _ _
      (liftedSpaceStack P.groupoid.objects).isFiberedInGroupoids
      (inertia.{u, u + 1, u + 1} B S hS
        (quotientStackCFG B S hS P.groupoid)).isFiberedInGroupoids
      (inertia.{u, u, u + 1} B S hS 𝒳.val).isFiberedInGroupoids
      (RelativeInertia.isEquivalence_functoriality _ _ _ _) rfl)
    rfl

/-- Let `𝒳` be an algebraic stack over `S` and let `[U/R] ⟶ 𝒳` be a presentation. Let `G/U` be
the stabilizer group algebraic space associated to the presenting groupoid `(U, R, s, t, c)`.
Then

```
𝒮_G  ------>  𝒮_U
 |             |
 v             v
ℐ_𝒳  ------>  𝒳
```

is a 2-fibre product diagram in the 2-category of algebraic stacks over `S`. -/
@[stacks 06PR "the diagram is 2-cartesian in the 2-category of algebraic stacks"]
noncomputable def isTwoFibreProduct_inertiaPresentationSquareAlgebraicStacks :
    Bicategory.IsTwoFibreProduct (inertiaPresentationSquareAlgebraicStacks B S hS P) :=
  Bicategory.isTwoFibreProduct_of_underlying
    (Bicategory.isTwoFibreProduct_of_isEquivalence_to
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ _)
      (CatFiberedInGroupoids.preHomTwoFibreProductSquare.{u, u, u + 1, u + 1} _ _
        (inertiaPresentationSquareAlgebraicStacks B S hS P).underlying)
      (isEquivalence_lift_inertiaPresentationSquareAlgebraicStacks B S hS P))

/-- For an algebraic stack `𝒳` over `S` with a
presentation `[U/R] ⟶ 𝒳`, the diagram of the algebraic stack of the stabilizer, the algebraic
stack of the object space, the inertia of `𝒳` and `𝒳` is a fibre product diagram in the
2-category of algebraic stacks over `S`. -/
@[stacks 06PR "the diagram is a fibre product diagram of algebraic stacks"]
theorem nonempty_isTwoFibreProduct_inertiaPresentationSquareAlgebraicStacks :
    Nonempty (Bicategory.IsTwoFibreProduct
      (inertiaPresentationSquareAlgebraicStacks B S hS P)) :=
  ⟨isTwoFibreProduct_inertiaPresentationSquareAlgebraicStacks B S hS P⟩

end AlgebraicGeometry.Stack

end
