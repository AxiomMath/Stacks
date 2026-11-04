module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Quot.NumericalSubstackFlatClosed
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatClosedLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyClosedLocus
public import StacksFrontier.AlgebraicGeometry.Stacks.ObjectPropertyOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStackHomUniverse
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.EssentialImageFibered
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Fibrewise
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.RestrictMorPresheaf

/-!
# Substacks of `Coh_{X/Y}` cut out by conditions on the test schemes

Let `f : X ⟶ Y` be a morphism of algebraic spaces of finite presentation, the standing data of
Stacks 08KB, and let `Q` be a condition on the objects `(T, 𝓕)` of `Coh_{X/Y}` which is inherited
along the morphisms of `Coh_{X/Y}`.  The full subcategory `Coh^Q_{X/Y}` of the objects satisfying
`Q` is again a category fibred in groupoids over `(Sch/S)_{fppf}`, and its inclusion
`Coh^Q_{X/Y} ⟶ Coh_{X/Y}` is a 1-morphism of categories fibred in groupoids.

Suppose that on every object `A = (T, 𝓕)` the condition is cut out by a subset `Z ⊆ |T|`: a
morphism `A' ⟶ A` lying over `h : T' ⟶ T` has `Q A'` exactly when `h` maps `|T'|` into `Z`.

* If every such `Z` is closed and stable under generalization, the flat closed subscheme of `T`
  with support `Z` (Stacks 04PW) represents the 2-fibre product `T ×_{Coh_{X/Y}} Coh^Q_{X/Y}`, so
  the inclusion is representable by algebraic spaces and is a flat closed immersion in the sense of
  Stacks 04XB.
* If every such `Z` is open and closed, the inclusion is moreover an open immersion: `Coh^Q_{X/Y}`
  is an open and closed substack.

This is the shape of Stacks 0DND for the substack `Coh^P_{X/B}` of Situation 0DNC, whose
condition is cut out by the locus where the locally constant functions `χ_i` take the values
`P(i)`.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.fullSubcategory`: the full subcategory of a category
  fibred in groupoids cut out by a property of objects inherited along morphisms, as a category
  fibred in groupoids, and `CategoryTheory.CatFiberedInGroupoids.fullSubcategoryι` its inclusion.
* `AlgebraicGeometry.Stack.IsFlat`: a 1-morphism of categories fibred in groupoids over the big
  fppf site is *flat* in the sense of Stacks 04XB.
* `AlgebraicGeometry.Space.CoherentSituation.conditionCFG`: the substack `Coh^Q_{X/Y}`, and
  `AlgebraicGeometry.Space.CoherentSituation.conditionι` its inclusion into `Coh_{X/Y}`.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.isFiberedInGroupoids_fullSubcategoryBased`: the full
  subcategory cut out by a property inherited along morphisms is fibred in groupoids.
* `AlgebraicGeometry.Stack.isFlat_of_flatClosedLocus`: a fully faithful 1-morphism whose image is
  cut out on every scheme-valued point of the target by a flat closed subscheme is flat.
* `AlgebraicGeometry.Space.CoherentSituation.exists_flatClosedLocus_conditionι`: on a
  scheme-valued point of `Coh_{X/Y}`, the flat closed subscheme with support the locus cutting out
  `Q` represents the 2-fibre product with `Coh^Q_{X/Y}`.
* `AlgebraicGeometry.Space.CoherentSituation.conditionι_isFlatClosedImmersion`: the inclusion of
  `Coh^Q_{X/Y}` is representable by algebraic spaces and a flat closed immersion when `Q` is cut
  out by closed subsets stable under generalization.
* `AlgebraicGeometry.Space.CoherentSituation.conditionι_isOpenAndClosedImmersion`: it is
  representable by algebraic spaces, an open immersion and a closed immersion when `Q` is cut out
  by open and closed subsets.
* `AlgebraicGeometry.Space.CoherentSituation.isAlgebraicStack_conditionCFG`: `Coh^Q_{X/Y}` is an
  algebraic stack when `Coh_{X/Y}` is and `Q` is a flat closed condition (Stacks 05UM).
* In `AlgebraicGeometry.Space.NumericalSituation`,
  `conditionι_hasNumericalInvariants_isFlatClosedImmersion`,
  `…_isOpenAndClosedImmersion_of_finite` and `…_isOpenAndClosedImmersion_of_noetherianDescent`:
  for the substack `Coh^P_{X/B}` of Situation 0DNC, the inclusion is a flat closed immersion, and
  an open and closed immersion for finite `I` or over a Noetherian descent, as soon as the
  functions `χ_i` are compatible with pullback and locally constant.

## Implementation notes

The flatness predicate `AlgebraicGeometry.Stack.IsFlat` is the condition of Stacks 04XB for
`AlgebraicGeometry.Space.IsFlat` written out, exactly as `AlgebraicGeometry.Stack.IsOpenImmersion`
and `AlgebraicGeometry.Stack.IsClosedImmersion` are for open and closed immersions: every algebraic
space representing a base change along a scheme-valued point of the target has flat structural
morphism.

Algebraicity of `Coh^Q_{X/Y}` from that of `Coh_{X/Y}` uses Stacks 05UM in the form
`AlgebraicGeometry.Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_homUniverse`,
because the morphisms of `Coh_{X/Y}` lie in universe `u + 1`.

## References

* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04PW](https://stacks.math.columbia.edu/tag/04PW)
* [Stacks Project, Tag 04TU](https://stacks.math.columbia.edu/tag/04TU)
* [Stacks Project, Tag 05UM](https://stacks.math.columbia.edu/tag/05UM)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w v₁ u₁ v₂ u₂

/-! ### Full subcategories of categories fibred in groupoids -/

namespace CategoryTheory.CatFiberedInGroupoids

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- **The full subcategory cut out by a property inherited along morphisms is fibred in
groupoids.**  Condition (1) of Stacks 04TU holds on the nose, so the restriction of the structure
functor is fibred; its fibres are groupoids because they embed fully faithfully into those of the
ambient category. -/
theorem isFiberedInGroupoids_fullSubcategoryBased (𝒳 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞)
    {P : ObjectProperty 𝒳.val.obj} (hP : ∀ {a b : 𝒳.val.obj}, (a ⟶ b) → P b → P a) :
    (fullSubcategoryBased 𝒳 P).p.IsFiberedInGroupoids := by
  set p := 𝒳.val.p
  have : p.IsFibered := 𝒳.property.isFibered
  have hclosed : Functor.ClosedUnderStronglyCartesian p P := fun _ φ _ hx =>
    Functor.isoOverId_of_prop (hP φ hx)
  have hGroups : ∀ U : 𝒞, IsGroupoid ((P.ι ⋙ p).Fiber U) := by
    intro U
    have hrfl : P.ι ⋙ p = P.ι ⋙ p := rfl
    set L := Functor.Fiber.mapOfComp (P.ι ⋙ p) p P.ι hrfl U
    have : P.ι.Full := ObjectProperty.full_ι P
    have : P.ι.Faithful := ObjectProperty.faithful_ι P
    have : L.Full := Functor.Fiber.full_mapOfComp hrfl U
    have : L.Faithful := Functor.Fiber.faithful_mapOfComp hrfl U
    have hAmbient : IsGroupoid (p.Fiber U) := 𝒳.property.fiber_isGroupoid U
    refine { all_isIso := ?_ }
    intro a b f
    have : IsIso (L.map f) := hAmbient.all_isIso (L.map f)
    exact isIso_of_fully_faithful L f
  exact Functor.IsFiberedInGroupoids.iff_isFibered_and_fiber_isGroupoid.mpr
    ⟨Functor.isFibered_restrict_of_closed p P hclosed, hGroups⟩

/-- **The full subcategory of a category fibred in groupoids cut out by a property of its objects
inherited along morphisms**, as a category fibred in groupoids. -/
def fullSubcategory (𝒳 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞) (P : ObjectProperty 𝒳.val.obj)
    (hP : ∀ {a b : 𝒳.val.obj}, (a ⟶ b) → P b → P a) : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞 :=
  CatFiberedInGroupoids.mk (fullSubcategoryBased 𝒳 P)
    (isFiberedInGroupoids_fullSubcategoryBased 𝒳 hP)

/-- The inclusion of the full subcategory cut out by a property inherited along morphisms, as a
1-morphism of categories fibred in groupoids. -/
def fullSubcategoryι (𝒳 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞) (P : ObjectProperty 𝒳.val.obj)
    (hP : ∀ {a b : 𝒳.val.obj}, (a ⟶ b) → P b → P a) : fullSubcategory 𝒳 P hP ⟶ 𝒳 :=
  Bicategory.InducedBicategory.mkHom (fullSubcategoryBasedι 𝒳 P)

/-- The underlying functor of the inclusion of a full subcategory is the inclusion `P.ι`. -/
theorem homFunctor_fullSubcategoryι (𝒳 : CatFiberedInGroupoids.{v₁, v₂, u₁, u₂} 𝒞)
    (P : ObjectProperty 𝒳.val.obj) (hP : ∀ {a b : 𝒳.val.obj}, (a ⟶ b) → P b → P a) :
    homFunctor (fullSubcategoryι 𝒳 P hP) = P.ι :=
  rfl

end CategoryTheory.CatFiberedInGroupoids

/-! ### Flat 1-morphisms of categories fibred in groupoids -/

namespace AlgebraicGeometry.Stack

section FiberedInGroupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- A 1-morphism of categories fibred in groupoids over the big fppf site of `S` which is
representable by algebraic spaces *is flat* when every algebraic space representing its base
change along a scheme-valued point of the target has flat structural morphism, read as a morphism
of algebraic spaces over `S`.  This is the notion of Stacks 04XB for
`AlgebraicGeometry.Space.IsFlat`. -/
abbrev IsFlat (f : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj)
    (_hy : y ⋙ 𝒴.val.p = Over.map U.hom)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
          (CatFiberedInGroupoids.homFunctor f))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      Space.IsFlat B S hS
        (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom

end FiberedInGroupoids

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space over `U` isomorphic to a flat subscheme of `U` has flat structural
morphism over `S`.**  This is the structural morphism of Stacks 04SG, the one the flatness
condition of Stacks 04XB tests. -/
theorem isFlat_algebraicSpaceMap_of_iso_yoneda (U : BigFppfOver B S hS)
    (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hP : IsAlgebraicSpace B U.left.1 U.left.2 P)
    (V : BigFppfOver B U.left.1 U.left.2) (e : P ≅ yoneda.obj V)
    (hV : Flat V.hom.hom) :
    Space.IsFlat B S hS
      (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨P, hP⟩)).hom := by
  have : (Space.flatProperty B S hS).RespectsIso :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine (prop_algebraicSpaceMap_iff B S hS (Space.flatProperty B S hS) U P hP).mpr ?_
  let k : (Over.map U.hom).obj V ⟶ Over.mk U.hom := Over.homMk V.hom rfl
  let j : (OverShriek.relocalizePresheafFunctor U.hom).obj P ≅
      yoneda.obj ((Over.map U.hom).obj V) :=
    (OverShriek.relocalizePresheafFunctor U.hom).mapIso e ≪≫
      (OverShriek.relocalizeYonedaIso U.hom).app V
  have hj : j.hom ≫ yoneda.map k = OverShriek.relocalizeToYoneda U.hom P := by
    dsimp only [j, Iso.trans_hom, Functor.mapIso_hom]
    rw [Category.assoc, relocalizeToYoneda_yoneda, relocalizeToYoneda_comp_map]
  let jA : (⟨(OverShriek.relocalizePresheafFunctor U.hom).obj P,
      isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom P hP⟩ : AlgebraicSpaces B S hS) ≅
      ⟨yoneda.obj ((Over.map U.hom).obj V), isAlgebraicSpace_yoneda B S hS _⟩ :=
    ObjectProperty.isoMk _ j
  show Space.IsFlat B S hS (OverShriek.relocalizeToYoneda U.hom P)
  rw [← hj]
  exact ((Space.flatProperty B S hS).cancel_left_of_respectsIso jA.hom
    (ObjectProperty.homMk (yoneda.map k) :
      (⟨yoneda.obj ((Over.map U.hom).obj V), isAlgebraicSpace_yoneda B S hS _⟩ :
        AlgebraicSpaces B S hS) ⟶ ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)).mpr
    (Space.isFlat_yoneda_map B S hS k hV)

section Locus

variable {B S hS} {𝒞 : BasedCategory.{v₁, u₁} (BigFppfOver B S hS)}
  {𝒟 : BasedCategory.{v₂, u₂} (BigFppfOver B S hS)}

variable (B S hS) in
/-- **An algebraic space representing a base change of a fully faithful 1-morphism is any closed
subscheme of the base cutting out its image.**  Both presheaves take subsingleton values and have
the same support. -/
theorem nonempty_iso_yoneda_of_equivalenceOver_of_locus (G : 𝒞 ⥤ᵇ 𝒟)
    (hfull : G.toFunctor.Full) (hfaithful : G.toFunctor.Faithful) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒟.obj) (hy : y ⋙ 𝒟.p = Over.map U.hom)
    (V : BigFppfOver B U.left.1 U.left.2)
    (hV : _root_.AlgebraicGeometry.IsClosedImmersion V.hom.hom)
    (hVlocus : ∀ T : BigFppfOver B U.left.1 U.left.2,
      Nonempty (T ⟶ V) ↔
        ∃ a, (TwoFibreProductOver.fst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor).obj a = T)
    (P : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (e : StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor)
      (presheafOfCategories (P ⋙ typeToCat)).p) :
    Nonempty (P ≅ yoneda.obj V) := by
  have hfst := (fullyFaithfulTwoFibreProductFst (Over.map U.hom) 𝒞.p 𝒟.p y G.toFunctor hy G.w
    (Functor.FullyFaithful.ofFullyFaithful G.toFunctor)).full
  obtain ⟨hrange, hfullP⟩ := range_obj_eq_and_full_of_equivalenceOver e hfst
  have hsubP : ∀ X, Subsingleton (P.obj X) := by
    refine fun X => ⟨fun a b => ?_⟩
    let A' : (presheafOfCategories (P ⋙ typeToCat)).obj := ⟨X.unop, Discrete.mk a⟩
    let D' : (presheafOfCategories (P ⋙ typeToCat)).obj := ⟨X.unop, Discrete.mk b⟩
    obtain ⟨m, hm⟩ := (presheafOfCategories (P ⋙ typeToCat)).p.map_surjective
      (X := A') (Y := D') (𝟙 X.unop)
    have he : a = P.map m.base.op b := Discrete.eq_of_hom m.fiber
    change m.base = 𝟙 X.unop at hm
    rw [hm] at he
    change a = P.map (𝟙 X) b at he
    simpa only [P.map_id, types_id_apply] using he
  refine nonempty_iso_of_subsingleton P (yoneda.obj V) hsubP
    (fun T ↦ subsingleton_hom_of_isClosedImmersion B S hS U V hV T.unop) ?_
  intro T
  have h1 := congrArg (T.unop ∈ ·) (range_elementsProjection_obj P)
  have h2 := congrArg (T.unop ∈ ·) hrange
  simp only [eq_iff_iff] at h1 h2
  exact h1.symm.trans (h2.symm.trans (hVlocus T.unop).symm)

variable (B S hS) in
/-- **Flatness from a flat closed locus.**  A fully faithful 1-morphism of categories fibred in
groupoids whose image is cut out, on the base of every scheme-valued point of the target, by a
flat closed subscheme is flat in the sense of Stacks 04XB: every algebraic space representing one
of its base changes is that flat closed subscheme. -/
theorem isFlat_of_flatClosedLocus
    {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
    (f : 𝒳 ⟶ 𝒴)
    (hfull : (CatFiberedInGroupoids.homFunctor f).Full)
    (hfaithful : (CatFiberedInGroupoids.homFunctor f).Faithful)
    (hlocus : ∀ (U : BigFppfOver B S hS) (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒴.val.obj),
      y ⋙ 𝒴.val.p = Over.map U.hom →
      ∃ V : BigFppfOver B U.left.1 U.left.2,
        _root_.AlgebraicGeometry.IsClosedImmersion V.hom.hom ∧ Flat V.hom.hom ∧
        ∀ T : BigFppfOver B U.left.1 U.left.2,
          Nonempty (T ⟶ V) ↔
            ∃ a, (TwoFibreProductOver.fst (Over.map U.hom) 𝒳.val.p 𝒴.val.p y
              (CatFiberedInGroupoids.homFunctor f)).obj a = T) :
    IsFlat B S hS f := by
  intro U y hy P hP ⟨e⟩
  obtain ⟨V, hVcl, hVfl, hV⟩ := hlocus U y hy
  obtain ⟨i⟩ := nonempty_iso_yoneda_of_equivalenceOver_of_locus B S hS f.hom hfull hfaithful U y
    hy V hVcl hV P e
  exact isFlat_algebraicSpaceMap_of_iso_yoneda B S hS U P hP V i hVfl

end Locus

end AlgebraicGeometry.Stack

/-! ### Substacks of `Coh_{X/Y}` -/

namespace AlgebraicGeometry.Space.CoherentSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (D : CoherentSituation B S hS)

/-- **The substack `Coh^Q_{X/Y} ⊆ Coh_{X/Y}`** cut out by a condition `Q` on the objects which is
inherited along the morphisms of `Coh_{X/Y}`: the full subcategory of the objects satisfying `Q`,
as a category fibred in groupoids over the big fppf site of `S`. -/
def conditionCFG (Q : CoherentObject D → Prop)
    (hQ : ∀ {A' A : CoherentObject D}, CoherentHom A' A → Q A → Q A') :
    CatFiberedInGroupoids.{u, u + 1, u + 1, u + 1} (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.fullSubcategory (coherentCFG D) Q (fun φ h => hQ φ h)

/-- **The inclusion `Coh^Q_{X/Y} ⟶ Coh_{X/Y}`**, a 1-morphism of categories fibred in
groupoids. -/
def conditionι (Q : CoherentObject D → Prop)
    (hQ : ∀ {A' A : CoherentObject D}, CoherentHom A' A → Q A → Q A') :
    D.conditionCFG Q hQ ⟶ coherentCFG D :=
  CatFiberedInGroupoids.fullSubcategoryι (coherentCFG D) Q (fun φ h => hQ φ h)

variable {D} {Q : CoherentObject D → Prop}
  (hQ : ∀ {A' A : CoherentObject D}, CoherentHom A' A → Q A → Q A')

/-- The inclusion of `Coh^Q_{X/Y}` is fully faithful. -/
theorem conditionι_full : (CatFiberedInGroupoids.homFunctor (D.conditionι Q hQ)).Full :=
  ObjectProperty.full_ι (C := (coherentCFG D).val.obj) Q

/-- The inclusion of `Coh^Q_{X/Y}` is faithful. -/
theorem conditionι_faithful : (CatFiberedInGroupoids.homFunctor (D.conditionι Q hQ)).Faithful :=
  ObjectProperty.faithful_ι (C := (coherentCFG D).val.obj) Q

/-- **The image of the 2-fibre product with `Coh^Q_{X/Y}`.**  For a scheme-valued point `y` of
`Coh_{X/Y}` over `U`, an object `T` of the big fppf site of `U` is in the image of the first
projection of `(Sch/U)_{fppf} ×_{y, Coh_{X/Y}} Coh^Q_{X/Y}` exactly when `y(T)` satisfies `Q`. -/
theorem exists_twoFibreProductFst_conditionι_iff (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ (coherentCFG D).val.obj)
    (hy : y ⋙ (coherentCFG D).val.p = Over.map U.hom) (T : BigFppfOver B U.left.1 U.left.2) :
    (∃ a, (TwoFibreProductOver.fst (Over.map U.hom) (D.conditionCFG Q hQ).val.p
        (coherentCFG D).val.p y (CatFiberedInGroupoids.homFunctor (D.conditionι Q hQ))).obj a =
          T) ↔ Q (y.obj T) := by
  constructor
  · rintro ⟨a, rfl⟩
    exact hQ a.iso.hom a.y.property
  · intro hT
    exact ⟨{ base := (coherentCFG D).val.p.obj (y.obj T)
             x := T
             y := ⟨y.obj T, hT⟩
             hx := (Functor.congr_obj hy T).symm
             hy := rfl
             iso := Iso.refl _
             vertical := IsHomLift.id rfl }, rfl⟩

/-- **The locus of `Coh^Q_{X/Y}` on a scheme-valued point.**  If `Q` is cut out on the test
schemes by subsets with property `p`, then for every scheme-valued point `y` of `Coh_{X/Y}` over
`U` there is a subset `Z ⊆ |U|` with property `p` (read on the test scheme of `y(U)`) such that an
object `T ⟶ U` of the big fppf site of `U` has `Q (y T)` exactly when `T ⟶ U` maps into `Z`. -/
theorem exists_locus_of_isCutOutOnTestSchemes
    {p : ∀ A : CoherentObject D, Set A.testScheme → Prop}
    (hcut : IsCutOutOnTestSchemes D Q p) (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ (coherentCFG D).val.obj)
    (hy : y ⋙ (coherentCFG D).val.p = Over.map U.hom) :
    ∃ (A : CoherentObject D) (hA : A.T.left = (Over.map U.hom).obj (Over.mk (𝟙 _)))
      (Z : Set A.testScheme), p A Z ∧
      ∀ (T : BigFppfOver B U.left.1 U.left.2) (hT : (y.obj T).T.left = (Over.map U.hom).obj T),
        Q (y.obj T) ↔
          Set.range ((BigFppfOver.toScheme B S hS).map (eqToHom hT ≫
            (Over.map U.hom).map (Over.homMk T.hom (Category.comp_id _)) ≫ eqToHom hA.symm)) ⊆
            Z := by
  let U₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 _)
  let A : CoherentObject D := y.obj U₀
  have hA : A.T.left = (Over.map U.hom).obj U₀ := Functor.congr_obj hy U₀
  obtain ⟨Z, hpZ, hZ⟩ := hcut A
  refine ⟨A, hA, Z, hpZ, fun T hT => ?_⟩
  let t : T ⟶ U₀ := Over.homMk T.hom (Category.comp_id _)
  let m : CoherentHom (y.obj T) A := y.map t
  have hm : m.base.left = eqToHom hT ≫ (Over.map U.hom).map t ≫ eqToHom hA.symm :=
    Functor.congr_hom hy t
  rw [hZ (y.obj T) m]
  show Set.range ((BigFppfOver.toScheme B S hS).map m.base.left) ⊆ Z ↔ _
  rw [hm]

/-- **The flat closed subscheme cutting out `Coh^Q_{X/Y}` on a scheme-valued point.**  If on the
scheme-valued point `y` of `Coh_{X/Y}` over `U` the condition `Q (y T)` is cut out by a closed
subset `Z ⊆ |U|` stable under generalization, then the flat closed subscheme of `U` with support
`Z` (Stacks 04PW) is a locus of the inclusion of `Coh^Q_{X/Y}` over `y`; it is an open subscheme
when `Z` is open. -/
theorem exists_flatClosedLocus_conditionι (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ (coherentCFG D).val.obj)
    (hy : y ⋙ (coherentCFG D).val.p = Over.map U.hom) (A : CoherentObject D)
    (hA : A.T.left = (Over.map U.hom).obj (Over.mk (𝟙 _))) (Z : Set A.testScheme)
    (hZ : IsClosed Z) (hgen : StableUnderGeneralization Z)
    (hQZ : ∀ (T : BigFppfOver B U.left.1 U.left.2)
      (hT : (y.obj T).T.left = (Over.map U.hom).obj T),
      Q (y.obj T) ↔
        Set.range ((BigFppfOver.toScheme B S hS).map (eqToHom hT ≫
          (Over.map U.hom).map (Over.homMk T.hom (Category.comp_id _)) ≫ eqToHom hA.symm)) ⊆
          Z) :
    ∃ V : BigFppfOver B U.left.1 U.left.2,
      _root_.AlgebraicGeometry.IsClosedImmersion V.hom.hom ∧ Flat V.hom.hom ∧
      (IsOpen Z → _root_.AlgebraicGeometry.IsOpenImmersion V.hom.hom) ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2,
        Nonempty (T ⟶ V) ↔
          ∃ a, (TwoFibreProductOver.fst (Over.map U.hom) (D.conditionCFG Q hQ).val.p
            (coherentCFG D).val.p y (CatFiberedInGroupoids.homFunctor (D.conditionι Q hQ))).obj a =
              T := by
  obtain ⟨V₀, s, hscl, hsfl, hsop, hfac⟩ :=
    Space.exists_flat_closedImmersion_factors_iff B S hS A.T.left Z hZ hgen
  let s' : V₀ ⟶ (Over.map U.hom).obj (Over.mk (𝟙 _)) := s ≫ eqToHom hA
  have hs' : (BigFppfOver.toScheme B S hS).map s' =
      (BigFppfOver.toScheme B S hS).map s ≫ (BigFppfOver.toScheme B S hS).map (eqToHom hA) :=
    Functor.map_comp _ _ _
  refine ⟨Over.mk s'.left, ?_, ?_, fun hop => ?_, fun T => ?_⟩
  · show _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map s')
    rw [hs']
    infer_instance
  · show Flat ((BigFppfOver.toScheme B S hS).map s')
    rw [hs']
    infer_instance
  · have := hsop hop
    show _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map s')
    rw [hs']
    infer_instance
  · have hT : (y.obj T).T.left = (Over.map U.hom).obj T := Functor.congr_obj hy T
    rw [nonempty_hom_overMk_iff s' T, exists_twoFibreProductFst_conditionι_iff hQ U y hy T,
      hQZ T hT, ← hfac]
    exact (exists_comp_eq_iff_of_iso (eqToIso hT) (eqToIso hA.symm) s _).symm

/-- The inclusion of `Coh^Q_{X/Y}` is flat, closed and representable when `Q` is cut out by closed
subsets stable under generalization, and an open immersion if these subsets are open. -/
private theorem conditionι_isFlatClosedImmersion_of_isCutOutOnTestSchemes
    {p : ∀ A : CoherentObject D, Set A.testScheme → Prop}
    (hcut : IsCutOutOnTestSchemes D Q p)
    (hpZ : ∀ A Z, p A Z → IsClosed Z ∧ StableUnderGeneralization Z) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS (D.conditionι Q hQ).hom ∧
      Stack.IsClosedImmersion B S hS (D.conditionι Q hQ) ∧
      Stack.IsFlat B S hS (D.conditionι Q hQ) ∧
      ((∀ A Z, p A Z → IsOpen Z) → Stack.IsOpenImmersion B S hS (D.conditionι Q hQ)) := by
  have hlocus : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ (coherentCFG D).val.obj),
      y ⋙ (coherentCFG D).val.p = Over.map U.hom →
      ∃ V : BigFppfOver B U.left.1 U.left.2,
        _root_.AlgebraicGeometry.IsClosedImmersion V.hom.hom ∧ Flat V.hom.hom ∧
        ((∀ A Z, p A Z → IsOpen Z) → _root_.AlgebraicGeometry.IsOpenImmersion V.hom.hom) ∧
        ∀ T : BigFppfOver B U.left.1 U.left.2,
          Nonempty (T ⟶ V) ↔
            ∃ a, (TwoFibreProductOver.fst (Over.map U.hom) (D.conditionCFG Q hQ).val.p
              (coherentCFG D).val.p y
                (CatFiberedInGroupoids.homFunctor (D.conditionι Q hQ))).obj a = T := by
    intro U y hy
    obtain ⟨A, hA, Z, hZ, hQZ⟩ := exists_locus_of_isCutOutOnTestSchemes hcut U y hy
    obtain ⟨V, h₁, h₂, h₃, h₄⟩ := exists_flatClosedLocus_conditionι hQ U y hy A hA Z
      (hpZ A Z hZ).1 (hpZ A Z hZ).2 hQZ
    exact ⟨V, h₁, h₂, fun hop => h₃ (hop A Z hZ), h₄⟩
  obtain ⟨hcl, hrep⟩ :=
    Stack.isClosedImmersion_and_isRepresentableByAlgebraicSpaces_of_hasClosedLocus
      B S hS (D.conditionι Q hQ) (conditionι_full hQ) (conditionι_faithful hQ)
      (fun U y hy => (hlocus U y hy).imp fun _ hV => ⟨hV.1, hV.2.2.2⟩)
  refine ⟨hrep, hcl, Stack.isFlat_of_flatClosedLocus B S hS (D.conditionι Q hQ)
    (conditionι_full hQ) (conditionι_faithful hQ) fun U y hy =>
      (hlocus U y hy).imp fun _ hV => ⟨hV.1, hV.2.1, hV.2.2.2⟩, fun hop => ?_⟩
  exact (Stack.isOpenImmersion_and_isRepresentableByAlgebraicSpaces_of_hasOpenLocus
    B S hS (D.conditionι Q hQ) (conditionι_full hQ) (conditionι_faithful hQ)
    (fun U y hy => (hlocus U y hy).imp fun _ hV => ⟨hV.2.2.1 hop, hV.2.2.2⟩)).1

/-- **A flat closed condition cuts out a flat closed substack.**  If `Q` is a flat closed
condition — on every object `(T, 𝓕)` it is cut out by a flat closed subscheme of `T`, equivalently
(Stacks 04PW) by a closed subset of `|T|` stable under generalization — then the inclusion
`Coh^Q_{X/Y} ⟶ Coh_{X/Y}` is representable by algebraic spaces, a closed immersion and flat. -/
theorem conditionι_isFlatClosedImmersion (h : IsFlatClosedCondition D Q) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS (D.conditionι Q hQ).hom ∧
      Stack.IsClosedImmersion B S hS (D.conditionι Q hQ) ∧
      Stack.IsFlat B S hS (D.conditionι Q hQ) := by
  obtain ⟨hrep, hcl, hfl, -⟩ := conditionι_isFlatClosedImmersion_of_isCutOutOnTestSchemes hQ
    (isFlatClosedCondition_iff_isCutOutOnTestSchemes.1 h) fun _ _ => id
  exact ⟨hrep, hcl, hfl⟩

/-- **An open and closed condition cuts out an open and closed substack.**  If `Q` is an open and
closed condition — on every object `(T, 𝓕)` it is cut out by an open subscheme of `T` whose
underlying set is closed — then the inclusion `Coh^Q_{X/Y} ⟶ Coh_{X/Y}` is representable by
algebraic spaces, an open immersion and a closed immersion. -/
theorem conditionι_isOpenAndClosedImmersion (h : IsOpenAndClosedCondition D Q) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS (D.conditionι Q hQ).hom ∧
      Stack.IsOpenImmersion B S hS (D.conditionι Q hQ) ∧
      Stack.IsClosedImmersion B S hS (D.conditionι Q hQ) := by
  obtain ⟨hrep, hcl, -, hop⟩ := conditionι_isFlatClosedImmersion_of_isCutOutOnTestSchemes hQ
    (isOpenAndClosedCondition_iff_isCutOutOnTestSchemes.1 h)
    fun _ _ hZ => ⟨hZ.isClosed, hZ.isOpen.stableUnderGeneralization⟩
  exact ⟨hrep, hop fun _ _ hZ => hZ.isOpen, hcl⟩

/-- **`Coh^Q_{X/Y}` is algebraic when `Coh_{X/Y}` is**, for a flat closed condition `Q`: its
inclusion is representable by algebraic spaces, so Stacks 05UM applies, in the form for
categories fibred in groupoids whose morphisms lie in an arbitrary universe. -/
theorem isAlgebraicStack_conditionCFG (h : IsFlatClosedCondition D Q)
    (hcoh : Stack.IsAlgebraicStack.{u, w} B S hS (coherentCFG D).val) :
    Stack.IsAlgebraicStack.{u, w} B S hS (D.conditionCFG Q hQ).val :=
  Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces_homUniverse B S hS
    (D.conditionι Q hQ) (conditionι_isFlatClosedImmersion hQ h).1 hcoh

end AlgebraicGeometry.Space.CoherentSituation

/-! ### The substack `Coh^P_{X/B}` of Situation 0DNC -/

namespace AlgebraicGeometry.Space.NumericalSituation

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {D : CoherentSituation B S hS} (N : NumericalSituation.{u, v, u} B S hS D)
  (hQ : ∀ {A' A : CoherentObject D}, CoherentHom A' A →
    N.HasNumericalInvariants A → N.HasNumericalInvariants A')

/-- **`Coh^P_{X/B} ⟶ Coh_{X/B}` is a flat closed immersion**, as soon as the functions `χ_i` of
Situation 0DNC are compatible with pullback along the morphisms of `Coh_{X/B}` and locally
constant: the inclusion of the substack cut out by `χ_i = P(i)` is representable by algebraic
spaces, a closed immersion and flat. -/
theorem conditionι_hasNumericalInvariants_isFlatClosedImmersion
    (hbc : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : N.I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      N.numericalEuler A' i t =
        N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i)) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS (D.conditionι N.HasNumericalInvariants hQ).hom ∧
      Stack.IsClosedImmersion B S hS (D.conditionι N.HasNumericalInvariants hQ) ∧
      Stack.IsFlat B S hS (D.conditionι N.HasNumericalInvariants hQ) :=
  CoherentSituation.conditionι_isFlatClosedImmersion hQ
    (N.isFlatClosedCondition_hasNumericalInvariants hbc hlc)

/-- **`Coh^P_{X/B}` is algebraic when `Coh_{X/B}` is**, as soon as the functions `χ_i` of
Situation 0DNC are compatible with pullback and locally constant. -/
theorem isAlgebraicStack_conditionCFG_hasNumericalInvariants
    (hbc : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : N.I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      N.numericalEuler A' i t =
        N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i))
    (hcoh : Stack.IsAlgebraicStack.{u, w} B S hS (coherentCFG D).val) :
    Stack.IsAlgebraicStack.{u, w} B S hS (D.conditionCFG N.HasNumericalInvariants hQ).val :=
  CoherentSituation.isAlgebraicStack_conditionCFG hQ
    (N.isFlatClosedCondition_hasNumericalInvariants hbc hlc) hcoh

/-- **For finite `I`, `Coh^P_{X/B}` is an open and closed substack of `Coh_{X/B}`**, as soon as
the functions `χ_i` of Situation 0DNC are compatible with pullback and locally constant. -/
theorem conditionι_hasNumericalInvariants_isOpenAndClosedImmersion_of_finite [Finite N.I]
    (hbc : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : N.I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      N.numericalEuler A' i t =
        N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i)) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS (D.conditionι N.HasNumericalInvariants hQ).hom ∧
      Stack.IsOpenImmersion B S hS (D.conditionι N.HasNumericalInvariants hQ) ∧
      Stack.IsClosedImmersion B S hS (D.conditionι N.HasNumericalInvariants hQ) :=
  CoherentSituation.conditionι_isOpenAndClosedImmersion hQ
    (N.isOpenAndClosedCondition_hasNumericalInvariants hbc hlc)

/-- **`Coh^P_{X/B}` is an open and closed substack of `Coh_{X/B}` over a Noetherian descent**:
for any index set, as soon as the functions `χ_i` are compatible with pullback and locally
constant and every object of `Coh_{X/B}` is, near every point of its test scheme, pulled back from
an object over a locally Noetherian test scheme.  This is the form in which the source concludes
for `B` locally Noetherian. -/
theorem conditionι_hasNumericalInvariants_isOpenAndClosedImmersion_of_noetherianDescent
    (hbc : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : N.I)
      (t : points B S hS (yoneda.obj A'.T.left)),
      N.numericalEuler A' i t =
        N.numericalEuler A i (pointsMap B S hS _ (yoneda.map φ.base.left) t))
    (hlc : ∀ A i, IsLocallyConstant (N.numericalEuler A i))
    (hloc : ∀ (A : CoherentObject D) (t : A.testScheme), ∃ (A' A₀ : CoherentObject D)
      (p : CoherentHom A' A) (_ : CoherentHom A' A₀) (t' : A'.testScheme),
        p.baseScheme t' = t ∧ IsOpenMap p.baseScheme ∧ IsLocallyNoetherian A₀.testScheme) :
    Stack.IsRepresentableByAlgebraicSpaces B S hS (D.conditionι N.HasNumericalInvariants hQ).hom ∧
      Stack.IsOpenImmersion B S hS (D.conditionι N.HasNumericalInvariants hQ) ∧
      Stack.IsClosedImmersion B S hS (D.conditionι N.HasNumericalInvariants hQ) :=
  CoherentSituation.conditionι_isOpenAndClosedImmersion hQ
    (N.isOpenAndClosedCondition_hasNumericalInvariants_of_noetherianDescent hbc hlc hloc)

end AlgebraicGeometry.Space.NumericalSituation

end
