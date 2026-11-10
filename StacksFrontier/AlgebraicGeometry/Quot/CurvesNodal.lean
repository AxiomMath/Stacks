module

public import Mathlib.CategoryTheory.Groupoid.Discrete
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesFibered
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.NodalOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Stacks.Algebraic.RepresentableBySpace.Characterization
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentableMorphismAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Substack
public import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids
public import StacksFrontier.CategoryTheory.FiberedCategory.OfPresheaf
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.Criterion
public import StacksFrontier.CategoryTheory.Sites.Localization.Relocalize

/-!
# The open substack of at-worst-nodal curves (Stacks 0DSY, part (1))

Stacks 0DSY produces the open substack `Curves^{nodal} ⊂ Curves` of families of curves whose
structure morphism is at-worst-nodal of relative dimension one. Part (1) of the source is proved
here: the condition cuts a strictly full subcategory out of the category of families of curves,
that subcategory is an algebraic stack, its inclusion is an open immersion, and the classifying
morphism of a family factors through it exactly when the family is at-worst-nodal of relative
dimension one.

The locus in the base of a family over which the family is at-worst-nodal of relative dimension
one is produced from the maximal at-worst-nodal open subspace of the total space of
**Stacks 0DSH**: the complement of that open subspace is closed, the family is proper, so the
image of the complement is closed, and the locus is the complement of that image. The two
properties of Stacks 0DSH — maximality and compatibility with base change — turn membership of
the locus into the condition that the family pulled back to a scheme over the base be
at-worst-nodal of relative dimension one. Representing the locus by an object of the site makes
the presheaf of objects of the subcategory lying over a scheme-valued point of the stack
representable, hence an algebraic space, which is what makes the inclusion of the subcategory
representable by algebraic spaces and an open immersion.

## Main definitions

* `AlgebraicGeometry.nodalCurvesOpenSubstack`: **Stacks 0DSY**, part (1) — the open substack
  `Curves^{nodal}`, together with the characterisation of its objects on every family of curves.

## Main results

* `AlgebraicGeometry.classifying_factors_nodalCurvesOpenSubstack_iff`: **Stacks 0DSY**, part (1)
  — the classifying object of a family of curves lifts through the inclusion of the nodal open
  substack exactly when the family is at-worst-nodal of relative dimension one.

## Implementation notes

The algebraic stack of curves is not constructed in this library (Stacks 0D5A is not proved
here), so the substack is formed inside an arbitrary algebraic stack `𝒳` presented as being
equivalent, over the big fppf site of the integers, to the category of families of curves; the
equivalence `E` and the compatibility `hE` of `E` with the two projections to the site are
hypotheses. Membership of the substack is the condition of Stacks 0DSE on the family which the
inverse equivalence attaches to an object, which is invariant under isomorphism because it is
stable under base change along a morphism of families (Stacks 0DSF), so the subcategory is
strictly full.

The open substack is algebraic by the algebraic-stack clause of **Stacks 05UN**,
`AlgebraicGeometry.Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces`, applied
to its inclusion, which is representable by algebraic spaces.

Clause (2) of the source, the characterisation for a proper scheme over a field, is **not**
asserted here: it needs the criterion of Stacks 0C4E for at-worst-nodal singularities and the
family of curves of Stacks 0E0G attached to a proper scheme over a field, neither of which is
available.

The base change of the locus of Stacks 0DSH is stated for the chosen fibre product of presheaves,
while the cartesian square of a morphism of families of curves is an arbitrary one; the two are
joined by transporting the point set of the locus along the comparison isomorphism of fibre
products, which is `AlgebraicGeometry.nodalPointSet_comp_iso` below. Representability of the
presheaf of objects of the subcategory is read off through the category of elements of
`AlgebraicGeometry.propertyPresheaf`, the presheaf of proofs of the condition, which is
subsingleton-valued and therefore isomorphic to the presheaf represented by the object of the
site representing the locus.

## References

* [Stacks Project, Tag 0DSY](https://stacks.math.columbia.edu/tag/0DSY)
* [Stacks Project, Tag 0DSH](https://stacks.math.columbia.edu/tag/0DSH)
* [Stacks Project, Tag 0DSE](https://stacks.math.columbia.edu/tag/0DSE)
* [Stacks Project, Tag 0DSF](https://stacks.math.columbia.edu/tag/0DSF)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 05UN](https://stacks.math.columbia.edu/tag/05UN)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 0D4Z](https://stacks.math.columbia.edu/tag/0D4Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry

attribute [local instance] Space.pointTopology

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-! ### Strictly full subcategories of a fibred category -/

/-- The restriction of a functor fibred in groupoids to the full subcategory selected by a
property of objects which is inherited along morphisms is again fibred in groupoids. -/
private theorem fullSubcategory_isFiberedInGroupoids
    {C D : Type*} [Category C] [Category D] (p : D ⥤ C)
    (hp : p.IsFiberedInGroupoids) (P : ObjectProperty D)
    (hP : ∀ {x y : D}, (x ⟶ y) → P y → P x) :
    (P.ι ⋙ p).IsFiberedInGroupoids where
  exists_lift f x hx := by
    obtain ⟨y, φ, hφ⟩ := hp.exists_lift f x.obj hx
    refine ⟨⟨y, hP φ x.property⟩, ObjectProperty.homMk φ, ?_⟩
    cases hφ
    exact Functor.IsHomLift.map _
  unique_lift φ ψ f h := by
    obtain ⟨χ, hχ, huniq⟩ := hp.unique_lift φ.hom ψ.hom f h
    refine ⟨ObjectProperty.homMk χ, ⟨hχ.1, ?_⟩, ?_⟩
    · ext
      exact hχ.2
    · intro χ' hχ'
      ext
      exact huniq χ'.hom ⟨hχ'.1, congrArg (fun a => a.hom) hχ'.2⟩

/-- The base change of the inclusion of a strictly full subcategory along a functor over the
base is the inclusion of the full subcategory selected by the transported property. -/
private def fullSubcategoryBaseChangeEquivalence
    {C D A : Type*} [Category C] [Category D] [Category A]
    (p : D ⥤ C) (q : A ⥤ C) (y : A ⥤ D) (hy : y ⋙ p = q)
    (P : ObjectProperty D) (hP : ∀ {x z}, (x ⟶ z) → P z → P x) :
    StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst q (P.ι ⋙ p) p y P.ι)
      ((show ObjectProperty A from fun a => P (y.obj a)).ι) := by
  let Q : ObjectProperty A := fun a => P (y.obj a)
  let F : TwoFibreProductOver q (P.ι ⋙ p) p y P.ι ⥤ Q.FullSubcategory :=
    { obj := fun z => ⟨z.x, hP z.iso.hom z.y.property⟩
      map := fun f => ObjectProperty.homMk f.a }
  have hoy (a : A) : p.obj (y.obj a) = q.obj a := Functor.congr_obj hy a
  let G : Q.FullSubcategory ⥤ TwoFibreProductOver q (P.ι ⋙ p) p y P.ι :=
    { obj := fun z =>
        { base := q.obj z.obj
          x := z.obj
          y := ⟨y.obj z.obj, z.property⟩
          hx := rfl
          hy := hoy z.obj
          iso := Iso.refl _
          vertical := by
            change p.IsHomLift (𝟙 _) (𝟙 _)
            apply IsHomLift.of_fac' p _ _ (hoy z.obj) (hoy z.obj)
            simp }
      map := fun {z z'} f =>
        { hbase := q.map f.hom
          a := f.hom
          b := ObjectProperty.homMk (y.map f.hom)
          ha := Functor.IsHomLift.map _
          hb := IsHomLift.of_fac' (P.ι ⋙ p) (q.map f.hom)
            (ObjectProperty.homMk (X := ⟨y.obj z.obj, z.property⟩)
              (Y := ⟨y.obj z'.obj, z'.property⟩) (y.map f.hom))
            (hoy z.obj) (hoy z'.obj) (CategoryTheory.Functor.congr_hom hy f.hom)
          w := by simp }
      map_id := by
        intro z
        apply TwoFibreProductOver.Hom.ext'
        · rfl
        · apply ObjectProperty.hom_ext
          exact y.map_id z.obj
      map_comp := by
        intro z z' z'' f g
        apply TwoFibreProductOver.Hom.ext'
        · rfl
        · apply ObjectProperty.hom_ext
          exact y.map_comp f.hom g.hom }
  have hGF : G ⋙ F = 𝟭 _ := by
    refine CategoryTheory.Functor.ext (fun z => rfl) ?_
    intro z z' f
    simp only [F, G, CategoryTheory.Functor.comp_map, CategoryTheory.Functor.id_map,
      eqToHom_refl, Category.id_comp, Category.comp_id]
    apply ObjectProperty.hom_ext
    rfl
  have hb (z : TwoFibreProductOver q (P.ι ⋙ p) p y P.ι) :
      p.IsHomLift (𝟙 (q.obj z.x)) z.iso.inv := by
    have := z.vertical
    have : p.IsHomLift (𝟙 z.base) z.iso.inv := by infer_instance
    rwa [z.hx]
  let η : 𝟭 _ ≅ F ⋙ G := NatIso.ofComponents (fun z =>
    { hom :=
        { hbase := eqToHom z.hx.symm
          a := 𝟙 _
          b := ObjectProperty.homMk z.iso.inv
          ha := by
            apply IsHomLift.of_fac' q _ _ z.hx rfl
            simp
          hb := IsHomLift.of_fac' (P.ι ⋙ p) _ _ z.hy (hoy z.x) (by
            have := z.vertical
            change p.map z.iso.inv = _
            rw [IsHomLift.fac' p (𝟙 z.base) z.iso.inv]
            simp)
          w := by simp [F, G] }
      inv :=
        { hbase := eqToHom z.hx
          a := 𝟙 _
          b := ObjectProperty.homMk z.iso.hom
          ha := by
            apply IsHomLift.of_fac' q _ _ rfl z.hx
            simp
          hb := IsHomLift.of_fac' (P.ι ⋙ p) _ _ (hoy z.x) z.hy (by
            have := z.vertical
            change p.map z.iso.hom = _
            rw [IsHomLift.fac' p (𝟙 z.base) z.iso.hom]
            simp)
          w := by simp [F, G] }
      hom_inv_id := by
        apply TwoFibreProductOver.Hom.ext'
        · exact Category.id_comp _
        · apply ObjectProperty.hom_ext
          exact z.iso.inv_hom_id
      inv_hom_id := by
        apply TwoFibreProductOver.Hom.ext'
        · exact Category.id_comp _
        · apply ObjectProperty.hom_ext
          exact z.iso.hom_inv_id }) (by
        intro z z' f
        apply TwoFibreProductOver.Hom.ext'
        · simp [F, G]
        · apply ObjectProperty.hom_ext
          change f.b.hom ≫ z'.iso.inv = z.iso.inv ≫ y.map f.a
          have hw : y.map f.a ≫ z'.iso.hom = z.iso.hom ≫ f.b.hom := f.w
          rw [Iso.comp_inv_eq, Category.assoc, hw]
          simp)
  refine ⟨⟨F, rfl⟩, ⟨G, rfl⟩, η, eqToIso hGF, ?_, ?_⟩
  · ext z
    rfl
  · ext z
    simp

/-- The presheaf of proofs of a property of objects which is inherited along morphisms: its
value on an object is the (subsingleton) type of proofs that the object has the property. -/
private def propertyPresheaf {C : Type*} [Category C] (P : ObjectProperty C)
    (hP : ∀ {x y}, (x ⟶ y) → P y → P x) : Cᵒᵖ ⥤ Type u where
  obj T := ULift.{u} (PLift (P T.unop))
  map f := ↾fun t => ⟨⟨hP f.unop t.down.down⟩⟩
  map_id _ := by
    ext x
    rfl
  map_comp _ _ := by
    ext x
    rfl

/-- The inclusion of the full subcategory selected by a property of objects is the category of
elements of the presheaf of proofs of that property. -/
private def propertyPresheafEquivalence {C : Type*} [Category C]
    (P : ObjectProperty C) (hP : ∀ {x y}, (x ⟶ y) → P y → P x) :
    StacksRepresentableCFG.EquivalenceOver P.ι
      (presheafOfCategories (propertyPresheaf.{u} P hP ⋙ typeToCat)).p := by
  let R := propertyPresheaf.{u} P hP
  letI (T : Cᵒᵖ) : Subsingleton (R.obj T) := by
    dsimp [R, propertyPresheaf]
    infer_instance
  let F : P.FullSubcategory ⥤ (presheafOfCategories (R ⋙ typeToCat)).obj :=
    { obj := fun x => ⟨x.obj, ⟨⟨⟨x.property⟩⟩⟩⟩
      map := fun f => ⟨f.hom, eqToHom (by apply Discrete.ext; exact Subsingleton.elim _ _)⟩
      map_id := by
        intro x
        apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl
        apply Discrete.hom_eq
      map_comp := by
        intro x y z f g
        apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ rfl
        apply Discrete.hom_eq }
  let G : (presheafOfCategories (R ⋙ typeToCat)).obj ⥤ P.FullSubcategory :=
    { obj := fun x => ⟨x.base, x.fiber.as.down.down⟩
      map := fun f => ObjectProperty.homMk f.base }
  have hFG : F ⋙ G = 𝟭 _ := by
    refine CategoryTheory.Functor.ext (fun x => rfl) ?_
    intro x y f
    apply ObjectProperty.hom_ext
    simp [F, G]
  have hGF : G ⋙ F = 𝟭 _ := by
    refine CategoryTheory.Functor.ext (fun x => rfl) ?_
    intro x y f
    refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ ?_ ?_
    · change f.base = (𝟙 x ≫ f ≫ 𝟙 y).base
      simp
    · apply Discrete.hom_eq
  refine ⟨⟨F, rfl⟩, ⟨G, rfl⟩, eqToIso hFG.symm, eqToIso hGF, ?_, ?_⟩ <;> ext x <;>
    simp only [CategoryTheory.Functor.whiskerRight_app, eqToIso.hom, eqToHom_app, eqToHom_map]

/-- The base change of the inclusion of a strictly full subcategory along a functor over the
base is the category of elements of the presheaf of proofs of the transported property. -/
private def fullSubcategoryBaseChangePresheafEquivalence
    {C D A : Type*} [Category C] [Category D] [Category A]
    (p : D ⥤ C) (q : A ⥤ C) (y : A ⥤ D) (hy : y ⋙ p = q)
    (P : ObjectProperty D) (hP : ∀ {x z}, (x ⟶ z) → P z → P x) :
    StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst q (P.ι ⋙ p) p y P.ι)
      (presheafOfCategories (propertyPresheaf.{u}
        (fun a => P (y.obj a)) (fun f => hP (y.map f)) ⋙ typeToCat)).p :=
  (fullSubcategoryBaseChangeEquivalence p q y hy P hP).trans
    (propertyPresheafEquivalence _ _)

/-- A strictly full subcategory of an algebraic stack over `S` all of whose presheaves of proofs
over a scheme-valued point of the stack are algebraic spaces is an algebraic stack.

This is the algebraic-stack clause of Stacks 05UN applied to the inclusion, which the hypothesis
makes representable by algebraic spaces. -/
private theorem fullSubcategory_isAlgebraicStack_of_local_representability
    (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (P : ObjectProperty 𝒳.val.val.obj)
    (hP : ∀ {x z}, (x ⟶ z) → P z → P x)
    (hlocal : ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
      (_hy : y ⋙ 𝒳.val.val.p = Over.map U.hom),
      IsAlgebraicSpace B U.left.1 U.left.2
        (propertyPresheaf.{u} (fun a => P (y.obj a)) (fun f => hP (y.map f)))) :
    Stack.IsAlgebraicStack.{u, w} B S hS (Stack.fullSubcategoryBased 𝒳 P) := by
  let hfib := fullSubcategory_isFiberedInGroupoids 𝒳.val.val.p 𝒳.val.property P hP
  let Y := CatFiberedInGroupoids.mk (Stack.fullSubcategoryBased 𝒳 P) hfib
  let i : Y ⟶ 𝒳.val := Bicategory.InducedBicategory.mkHom
    (Stack.fullSubcategoryBasedInclusion 𝒳 P)
  refine Stack.isAlgebraicStack_source_of_isRepresentableByAlgebraicSpaces B S hS i ?_
    𝒳.property
  intro U
  dsimp only
  intro y hy
  refine ⟨_, hlocal U y hy, ⟨?_⟩⟩
  exact fullSubcategoryBaseChangePresheafEquivalence 𝒳.val.val.p (Over.map U.hom) y hy P hP

/-- Two presentations of a fibred category in groupoids as the category of elements of a presheaf
of sets identify the two presheaves: both are the presheaf of isomorphism classes of objects of
the fibres. -/
private def presheafIsoOfEquivalenceOver
    {C : Type (u + 1)} [Category.{u} C] {D : Type (u + 1)} [Category.{u} D] {p : D ⥤ C}
    (hp : p.IsFiberedInGroupoids) (F G : Cᵒᵖ ⥤ Type u)
    (eF : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (F ⋙ typeToCat)).p)
    (eG : StacksRepresentableCFG.EquivalenceOver p
      (presheafOfCategories (G ⋙ typeToCat)).p) : F ≅ G := by
  letI : p.IsFibered := hp.isFibered
  refine NatIso.ofComponents (fun T =>
    ((PresheafOfCategories.elementsIsoClassEquiv F eF T.unop).symm.trans
      (PresheafOfCategories.elementsIsoClassEquiv G eG T.unop)).toIso) ?_
  intro T T' f
  ext a
  let qF := PresheafOfCategories.elementsIsoClassEquiv F eF T.unop
  let qF' := PresheafOfCategories.elementsIsoClassEquiv F eF T'.unop
  let qG := PresheafOfCategories.elementsIsoClassEquiv G eG T.unop
  let qG' := PresheafOfCategories.elementsIsoClassEquiv G eG T'.unop
  let c := qF.symm a
  have hc : qF'.symm (F.map f a) = p.isoClassPresheaf.map f c := by
    apply qF'.injective
    rw [qF'.apply_symm_apply]
    simpa only [c, qF, qF', Quiver.Hom.op_unop, Equiv.apply_symm_apply] using
      (PresheafOfCategories.elementsIsoClassEquiv_naturality hp F eF f.unop c).symm
  change qG' (qF'.symm (F.map f a)) = G.map f (qG (qF.symm a))
  rw [hc]
  exact PresheafOfCategories.elementsIsoClassEquiv_naturality hp G eG f.unop c

/-- A presheaf of proofs which is representable is represented by the object it is tested
against: the values are subsingletons, so a proof of the property names a morphism and
conversely. -/
private def propertyPresheafIsoYoneda
    {C : Type*} [Category C] (P : ObjectProperty C)
    (hP : ∀ {x y : C}, (x ⟶ y) → P y → P x)
    (V : C) (h : ∀ T : C, P T ↔ Nonempty (T ⟶ V))
    (hsub : ∀ T : C, Subsingleton (T ⟶ V)) :
    propertyPresheaf.{u} P hP ≅ yoneda.obj V := by
  letI (T : C) : Subsingleton (T ⟶ V) := hsub T
  letI (T : Cᵒᵖ) : Subsingleton ((propertyPresheaf.{u} P hP).obj T) := by
    dsimp [propertyPresheaf]
    infer_instance
  refine NatIso.ofComponents (fun T => ?_) ?_
  · let e : (propertyPresheaf.{u} P hP).obj T ≃ (yoneda.obj V).obj T := {
      toFun q := Classical.choice ((h T.unop).mp q.down.down)
      invFun k := ⟨⟨(h T.unop).mpr ⟨k⟩⟩⟩
      left_inv q := Subsingleton.elim _ _
      right_inv k := Subsingleton.elim _ _ }
    exact e.toIso
  · intro T T' f
    ext q
    apply Subsingleton.elim

/-- There is at most one morphism of the site into an object whose structure morphism is an open
immersion: an open immersion is a monomorphism. -/
private theorem subsingleton_hom_of_openOver
    (S : Scheme.{u}) (hS : B.Contains S)
    (V : BigFppfOver B S hS)
    (hV : IsOpenImmersion (B.inclusion.map V.hom))
    (T : BigFppfOver B S hS) :
    Subsingleton (T ⟶ V) := by
  have : Mono (B.inclusion.map V.hom) := hV.mono
  constructor
  intro f g
  apply Over.OverMorphism.ext
  apply B.inclusion.map_injective
  apply (cancel_mono (B.inclusion.map V.hom)).mp
  rw [← Functor.map_comp, ← Functor.map_comp, Over.w f, Over.w g]

/-! ### The point set of the maximal at-worst-nodal open subspace -/

/-- Precomposing an at-worst-nodal morphism of relative dimension one of algebraic spaces over
`S` with an isomorphism leaves it at-worst-nodal of relative dimension one: the property is
stable under base change by Stacks 0DSF, hence invariant under isomorphism. -/
private theorem nodal_precomp_iso (S : Scheme.{u}) (hS : B.Contains S)
    {X X' Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hY : IsAlgebraicSpace B S hS Y) (i : X' ⟶ X) (hi : IsIso i) (f : X ⟶ Y)
    (hf : Space.IsAtWorstNodalOfRelativeDimensionOne B S hS f) :
    Space.IsAtWorstNodalOfRelativeDimensionOne B S hS (i ≫ f) := by
  let P : MorphismProperty (AlgebraicSpaces B S hS) := fun ⦃_ _⦄ g =>
    Space.IsAtWorstNodalOfRelativeDimensionOne B S hS g.hom
  have : P.RespectsIso :=
    (Space.isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange B S hS).respectsIso
  let i' : (⟨X', hX'⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩ := ObjectProperty.homMk i
  let f' : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩ := ObjectProperty.homMk f
  have : IsIso i' := (ObjectProperty.isIso_hom_iff i').mp hi
  exact MorphismProperty.RespectsIso.precomp P i' f' hf

/-- An open subspace on which a morphism is at-worst-nodal of relative dimension one stays one
after transport along an isomorphism of the source. -/
private theorem isNodalOpen_preimage_of_iso (S : Scheme.{u}) (hS : B.Contains S)
    {X X₀ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX₀ : IsAlgebraicSpace B S hS X₀)
    (hY : IsAlgebraicSpace B S hS Y) (e : X ≅ X₀) (q : X₀ ⟶ Y)
    {W : Subfunctor X} (hW : Space.IsNodalOpen B S hS (e.hom ≫ q) W) :
    Space.IsNodalOpen B S hS q (W.preimage e.inv) := by
  have hopen : Space.IsOpenSubspace B S hS (W.preimage e.inv) :=
    Space.isOpenSubspace_preimage B S hS e.inv W hX hX₀ hW.1
  have hiso : IsIso (W.fromPreimage e.inv) :=
    (Subfunctor.isPullback_preimage e.inv W).isIso_fst_of_isIso
  refine ⟨hopen, ?_⟩
  have hfac : (W.preimage e.inv).ι ≫ q = W.fromPreimage e.inv ≫ W.ι ≫ e.hom ≫ q :=
    calc (W.preimage e.inv).ι ≫ q
        = (W.preimage e.inv).ι ≫ e.inv ≫ e.hom ≫ q := by rw [Iso.inv_hom_id_assoc]
      _ = ((W.preimage e.inv).ι ≫ e.inv) ≫ e.hom ≫ q := (Category.assoc _ _ _).symm
      _ = (W.fromPreimage e.inv ≫ W.ι) ≫ e.hom ≫ q := by rw [Subfunctor.fromPreimage_ι]
      _ = W.fromPreimage e.inv ≫ W.ι ≫ e.hom ≫ q := Category.assoc _ _ _
  rw [hfac]
  exact nodal_precomp_iso B S hS hW.1.1 hopen.1 hY (W.fromPreimage e.inv) hiso
    (W.ι ≫ e.hom ≫ q) hW.2

/-- The point set of the locus of Stacks 0DSH is carried to the point set of the locus of the
transported morphism by an isomorphism of the source. -/
private theorem nodalPointSet_subset_of_iso (S : Scheme.{u}) (hS : B.Contains S)
    {X X₀ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX₀ : IsAlgebraicSpace B S hS X₀)
    (hY : IsAlgebraicSpace B S hS Y) (e : X ≅ X₀) (q : X₀ ⟶ Y) :
    Space.nodalPointSet B S hS (e.hom ≫ q) ⊆
      Space.pointsMap B S hS X e.hom ⁻¹' Space.nodalPointSet B S hS q := by
  intro x hx
  obtain ⟨W, hxW⟩ := Set.mem_iUnion.mp hx
  have hiso : IsIso (W.1.fromPreimage e.inv) :=
    (Subfunctor.isPullback_preimage e.inv W.1).isIso_fst_of_isIso
  have hW' : Space.IsNodalOpen B S hS q (W.1.preimage e.inv) :=
    isNodalOpen_preimage_of_iso B S hS hX hX₀ hY e q W.2
  obtain ⟨wx, hwx⟩ := hxW
  have hphi : Space.pointsMap B S hS (W.1.preimage e.inv).toFunctor
      (W.1.fromPreimage e.inv)
      (Space.pointsMap B S hS W.1.toFunctor (inv (W.1.fromPreimage e.inv)) wx) = wx := by
    rw [← Space.pointsMap_comp_apply, IsIso.inv_hom_id, Space.pointsMap_id, id_eq]
  have hkey : Space.pointsMap B S hS (W.1.preimage e.inv).toFunctor
      ((W.1.preimage e.inv).ι ≫ e.inv)
      (Space.pointsMap B S hS W.1.toFunctor (inv (W.1.fromPreimage e.inv)) wx) = x := by
    rw [← Subfunctor.fromPreimage_ι W.1 e.inv, Space.pointsMap_comp_apply, hphi]
    exact hwx
  have hcomp : ((W.1.preimage e.inv).ι ≫ e.inv) ≫ e.hom = (W.1.preimage e.inv).ι := by
    rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  refine Set.mem_iUnion.mpr ⟨⟨W.1.preimage e.inv, hW'⟩, ?_⟩
  refine ⟨Space.pointsMap B S hS W.1.toFunctor (inv (W.1.fromPreimage e.inv)) wx, ?_⟩
  change Space.pointsMap B S hS (W.1.preimage e.inv).toFunctor (W.1.preimage e.inv).ι
      (Space.pointsMap B S hS W.1.toFunctor (inv (W.1.fromPreimage e.inv)) wx) =
    Space.pointsMap B S hS X e.hom x
  rw [← hcomp, Space.pointsMap_comp_apply, hkey]

/-- **The point set of the locus of Stacks 0DSH is invariant under isomorphism of the source.**
For an isomorphism `e : X ≅ X₀` of algebraic spaces over `S` and a morphism `q : X₀ ⟶ Y`, the
point set of the locus of `e.hom ≫ q` is the inverse image of the point set of the locus of
`q`. -/
private theorem nodalPointSet_comp_iso (S : Scheme.{u}) (hS : B.Contains S)
    {X X₀ Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX₀ : IsAlgebraicSpace B S hS X₀)
    (hY : IsAlgebraicSpace B S hS Y) (e : X ≅ X₀) (q : X₀ ⟶ Y) :
    Space.nodalPointSet B S hS (e.hom ≫ q) =
      Space.pointsMap B S hS X e.hom ⁻¹' Space.nodalPointSet B S hS q := by
  refine subset_antisymm (nodalPointSet_subset_of_iso B S hS hX hX₀ hY e q) ?_
  intro x hx
  have hback := nodalPointSet_subset_of_iso B S hS hX₀ hX hY e.symm (e.hom ≫ q)
  rw [show e.symm.hom ≫ e.hom ≫ q = q by simp] at hback
  have h := hback hx
  rw [Set.mem_preimage, ← Space.pointsMap_comp_apply] at h
  simpa only [Iso.symm_hom, e.hom_inv_id, Space.pointsMap_id, id_eq] using h

/-- **The point set of the locus of Stacks 0DSH commutes with arbitrary base change.** For a
cartesian square over a flat morphism of finite presentation, the point set of the locus of the
base change is the inverse image of the point set of the locus.

This is the base change of Stacks 0DSH for the chosen fibre product of presheaves, transported
along the comparison isomorphism of the arbitrary cartesian square with it. -/
private theorem nodalPointSet_of_isPullback (S : Scheme.{u}) (hS : B.Contains S)
    {X Y X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hX' : IsAlgebraicSpace B S hS X') (hY' : IsAlgebraicSpace B S hS Y')
    (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hsq : IsPullback p f' f g)
    (hflat : Space.IsFlat B S hS f)
    (hfp : Space.IsLocallyOfFinitePresentation B S hS f) :
    Space.nodalPointSet B S hS f' =
      Space.pointsMap B S hS X' p ⁻¹' Space.nodalPointSet B S hS f := by
  have hP : IsAlgebraicSpace B S hS (pullback f g) :=
    isAlgebraicSpace_pullback B S hS f g hX hY' hY
  have hpts : Space.nodalPointSet B S hS (pullback.snd f g) =
      Space.pointsMap B S hS (pullback f g) (pullback.fst f g) ⁻¹'
        Space.nodalPointSet B S hS f := by
    rw [← Space.range_pointsMap_nodalOpenSubspace B S hS (pullback.snd f g),
      Space.nodalOpenSubspace_baseChange B S hS hX hY hY' f g hflat hfp,
      Space.range_pointsMap_preimage_ι, Space.range_pointsMap_nodalOpenSubspace]
  have hf' : f' = hsq.isoPullback.hom ≫ pullback.snd f g := hsq.isoPullback_hom_snd.symm
  calc Space.nodalPointSet B S hS f'
      = Space.nodalPointSet B S hS (hsq.isoPullback.hom ≫ pullback.snd f g) :=
        congrArg (fun k => Space.nodalPointSet B S hS k) hf'
    _ = Space.pointsMap B S hS X' hsq.isoPullback.hom ⁻¹'
          Space.nodalPointSet B S hS (pullback.snd f g) :=
        nodalPointSet_comp_iso B S hS hX' hP hY' hsq.isoPullback (pullback.snd f g)
    _ = Space.pointsMap B S hS X' hsq.isoPullback.hom ⁻¹'
          (Space.pointsMap B S hS (pullback f g) (pullback.fst f g) ⁻¹'
            Space.nodalPointSet B S hS f) := by rw [hpts]
    _ = Space.pointsMap B S hS X' (hsq.isoPullback.hom ≫ pullback.fst f g) ⁻¹'
          Space.nodalPointSet B S hS f := by rw [Space.pointsMap_comp, Set.preimage_comp]
    _ = Space.pointsMap B S hS X' p ⁻¹' Space.nodalPointSet B S hS f := by
        rw [hsq.isoPullback_hom_fst]

/-! ### The locus in the base of a family -/

/-- A morphism of algebraic spaces over `S` being at-worst-nodal of relative dimension one is the
same as the locus of Stacks 0DSH being the whole source. -/
private theorem nodal_iff_nodalOpenSubspace_eq_top
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    Space.IsAtWorstNodalOfRelativeDimensionOne B S hS f ↔
      Space.nodalOpenSubspace B S hS f = ⊤ := by
  let T : Subfunctor X := ⊤
  have hTiso : IsIso T.ι := (Subfunctor.eq_top_iff_isIso T).mp rfl
  have hTopen : Space.IsOpenSubspace B S hS T := by
    refine ⟨isAlgebraicSpace_of_iso B S hS (asIso T.ι) hX, ?_⟩
    exact (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isIso T.ι
  constructor
  · intro hn
    refine top_unique (Space.le_nodalOpenSubspace B S hS hX f ⟨hTopen, ?_⟩)
    exact nodal_precomp_iso B S hS hX hTopen.1 hY T.ι hTiso f hn
  · intro hN
    have hn := Space.isAtWorstNodalOfRelativeDimensionOne_nodalOpenSubspace B S hS hX f
    rw [hN] at hn
    have h2 := nodal_precomp_iso B S hS hTopen.1 hX hY (inv T.ι) inferInstance
      (T.ι ≫ f) hn
    rwa [← Category.assoc, IsIso.inv_hom_id, Category.id_comp] at h2

/-- An open subspace of an algebraic space over `S` is the whole space exactly when its point set
is: this is part (1) of Stacks 03BZ read on the one open subspace. -/
private theorem openSubspace_eq_top_iff_points
    (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (N : Subfunctor X) (hN : Space.IsOpenSubspace B S hS N) :
    N = ⊤ ↔ Set.range (Space.pointsMap B S hS N.toFunctor N.ι) = Set.univ := by
  constructor
  · intro h
    have : IsIso N.ι := (Subfunctor.eq_top_iff_isIso N).mp h
    refine Set.eq_univ_of_forall fun x => ⟨Space.pointsMap B S hS X (inv N.ι) x, ?_⟩
    rw [← Space.pointsMap_comp_apply, IsIso.inv_hom_id, Space.pointsMap_id, id_eq]
  · intro h
    obtain ⟨g, hg⟩ := (Space.factorsThrough_openSubspace_iff_points B S hS hX hX N hN
      (𝟙 X)).mpr (by simp [h])
    refine top_unique fun U x _ => ?_
    have hx := congrArg (fun t : X ⟶ X => t.app U x) hg
    change (g.app U x).val = x at hx
    rw [← hx]
    exact (g.app U x).property

/-- A morphism of algebraic spaces over `S` is at-worst-nodal of relative dimension one exactly
when the point set of the locus of Stacks 0DSH is everything. -/
private theorem nodal_iff_nodalPointSet_eq_univ
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    Space.IsAtWorstNodalOfRelativeDimensionOne B S hS f ↔
      Space.nodalPointSet B S hS f = Set.univ := by
  rw [nodal_iff_nodalOpenSubspace_eq_top B S hS hX hY f,
    openSubspace_eq_top_iff_points B S hS hX _
      (Space.isOpenSubspace_nodalOpenSubspace B S hS hX f),
    Space.range_pointsMap_nodalOpenSubspace]

/-- The complement of the image under a universally closed morphism of the complement of an open
set of points is the point set of an open subspace of the target, by part (1) of
Stacks 03BZ. -/
private theorem exists_open_complement_image
    (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : Space.UniversallyClosed B S hS f) (N : Set (Space.points B S hS X))
    (hN : IsOpen N) :
    ∃ W : Subfunctor Y, Space.IsOpenSubspace B S hS W ∧
      Set.range (Space.pointsMap B S hS W.toFunctor W.ι) =
        (Space.pointsMap B S hS X f '' Nᶜ)ᶜ :=
  have hclosed : IsClosed (Space.pointsMap B S hS X f '' Nᶜ) :=
    Space.isClosed_of_universallyClosed B S hS hY f hf _ hN.isClosed_compl
  ⟨Space.openSubspaceOfPoints B S hS Y _,
    Space.isOpenSubspace_openSubspaceOfPoints B S hS hY _ hclosed.isOpen_compl,
    Space.range_pointsMap_ι_openSubspaceOfPoints B S hS _⟩

/-- A set is the whole source of a map exactly when the range of a second map into the common
target misses the image of its complement, provided the two maps are the two projections of a
square which is cartesian on the underlying sets. -/
private theorem range_subset_compl_image_iff
    {A A' C C' : Type*} (f : A → C) (g : C' → C) (p : A' → A) (q : A' → C')
    (h : ∀ a c, f a = g c → ∃ z, p z = a ∧ q z = c)
    (hw : ∀ z, f (p z) = g (q z)) (N : Set A) :
    Set.range g ⊆ (f '' Nᶜ)ᶜ ↔ p ⁻¹' N = Set.univ := by
  constructor
  · intro hg
    refine Set.eq_univ_of_forall fun z => ?_
    by_contra hn
    exact hg ⟨q z, rfl⟩ ⟨p z, hn, hw z⟩
  · intro hp c hc ⟨a, ha, he⟩
    obtain ⟨c', rfl⟩ := hc
    obtain ⟨z, rfl, _⟩ := h a c' he
    exact ha (Set.eq_univ_iff_forall.mp hp z)

/-- A family of curves mapping to a family of curves is at-worst-nodal of relative dimension one
exactly when the morphism of base schemes factors through the open subspace of the base of the
target cut out by the complement of the image of the complement of the locus of Stacks 0DSH. -/
private theorem nodal_curveFamily_iff_factors_baseOpen
    (F G : CurveFamily B hZ) (a : F ⟶ G)
    (W : Subfunctor (schemeSpace G.base).obj)
    (hW : Space.IsOpenSubspace B integerBase hZ W)
    (hWp : Set.range (Space.pointsMap B integerBase hZ W.toFunctor W.ι) =
      (Space.pointsMap B integerBase hZ G.total.obj G.toBase.hom ''
        (Space.nodalPointSet B integerBase hZ G.toBase.hom)ᶜ)ᶜ) :
    Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom ↔
      ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
        t ≫ W.ι = (schemeSpaceMap a.baseMap).hom := by
  rw [Space.factorsThrough_openSubspace_iff_points B integerBase hZ
    (schemeSpace G.base).property (schemeSpace F.base).property W hW, hWp,
    nodal_iff_nodalPointSet_eq_univ B integerBase hZ F.total.property
      (schemeSpace F.base).property F.toBase.hom]
  let : CreatesLimit (cospan G.toBase (schemeSpaceMap a.baseMap))
      (ObjectProperty.ι (fun T => IsAlgebraicSpace B integerBase hZ T)) :=
    Limits.createsLimitFullSubcategoryInclusion _ (isAlgebraicSpace_of_iso B integerBase hZ
      (HasLimit.isoOfNatIso (cospanCompIso
        (ObjectProperty.ι (fun T => IsAlgebraicSpace B integerBase hZ T))
        G.toBase (schemeSpaceMap a.baseMap)))
      (isAlgebraicSpace_pullback B integerBase hZ
        G.toBase.hom (schemeSpaceMap a.baseMap).hom
        G.total.property (schemeSpace F.base).property (schemeSpace G.base).property))
  have hpb := a.cartesian.map (ObjectProperty.ι
    (fun T => IsAlgebraicSpace B integerBase hZ T))
  rw [nodalPointSet_of_isPullback B integerBase hZ G.total.property
    (schemeSpace G.base).property F.total.property (schemeSpace F.base).property
    a.totalMap.hom F.toBase.hom G.toBase.hom (schemeSpaceMap a.baseMap).hom hpb
    G.flat G.finitePresentation.1]
  symm
  apply range_subset_compl_image_iff
  · exact Space.exists_point_of_isPullback B integerBase hZ a.cartesian
  · intro z
    have h := congrArg (fun t => Space.pointsMap B integerBase hZ F.total.obj t z)
      (congrArg (fun t => t.hom) a.cartesian.w)
    simpa only [ObjectProperty.FullSubcategory.comp_hom, Space.pointsMap_comp,
      Function.comp_apply] using h

/-- **The open locus in the base of a family of curves.** For a family of curves there is an open
subspace of the base through which the morphism of base schemes of a second family mapping to it
factors exactly when the second family is at-worst-nodal of relative dimension one.

The locus is the complement of the image of the complement of the maximal at-worst-nodal open
subspace of Stacks 0DSH of the total space, which is open because the family is proper. -/
private theorem exists_nodal_baseOpen (G : CurveFamily B hZ) :
    ∃ W : Subfunctor (schemeSpace G.base).obj,
      Space.IsOpenSubspace B integerBase hZ W ∧
      ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
        Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom ↔
          ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
            t ≫ W.ι = (schemeSpaceMap a.baseMap).hom := by
  obtain ⟨W, hW, hWp⟩ := exists_open_complement_image B integerBase hZ
    (schemeSpace G.base).property G.toBase.hom G.proper.universallyClosed
    (Space.nodalPointSet B integerBase hZ G.toBase.hom)
    (Space.isOpen_nodalPointSet B integerBase hZ G.toBase.hom)
  exact ⟨W, hW, fun F a => nodal_curveFamily_iff_factors_baseOpen B hZ F G a W hW hWp⟩

/-- A family of curves mapping to a family of curves which is at-worst-nodal of relative
dimension one is itself at-worst-nodal of relative dimension one: it is a base change of it, and
the condition is stable under base change by Stacks 0DSF. -/
private theorem nodal_of_curveFamily_hom {F G : CurveFamily B hZ} (a : F ⟶ G)
    (hG : Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ G.toBase.hom) :
    Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom :=
  have h : MorphismProperty.IsStableUnderBaseChange
      (fun ⦃X Y : AlgebraicSpaces B integerBase hZ⦄ (f : X ⟶ Y) =>
        Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ f.hom) :=
    Space.isAtWorstNodalOfRelativeDimensionOne_isStableUnderBaseChange B integerBase hZ
  h.of_isPullback a.cartesian hG

/-- Being at-worst-nodal of relative dimension one is invariant under isomorphism of families of
curves: an isomorphism is in particular a morphism in both directions. -/
private theorem nodal_iff_of_curveFamily_iso {F G : CurveFamily B hZ} (e : F ≅ G) :
    Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom ↔
      Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ G.toBase.hom :=
  ⟨nodal_of_curveFamily_hom B hZ e.inv, nodal_of_curveFamily_hom B hZ e.hom⟩

/-! ### The locus over a scheme-valued point of the stack -/

/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance (priority := high) hasPullbacks_presheaf_curvesNodal
    {B' : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B'.Contains S} :
    HasPullbacks ((BigFppfOver B' S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_curvesNodal
    {B' : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B'.Contains S}
    {X Y Z : (BigFppfOver B' S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_curvesNodal (B' := B') (S := S) (hS := hS)).has_limit _

local instance (priority := high) hasLimitsOfShape_discrete_presheaf_curvesNodal
    {B' : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B'.Contains S} (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B' S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

/-- An open subspace of the algebraic space of a scheme of the site is represented by a scheme of
the site with an open immersion to it, by part (1) of Stacks 03BZ. -/
private theorem openSubspace_yoneda_representation
    (S : Scheme.{u}) (hS : B.Contains S)
    (U : BigFppfOver B S hS)
    (W : Subfunctor (yoneda.obj U))
    (hW : Space.IsOpenSubspace B S hS W) :
    ∃ (V : BigFppfOver B S hS) (j : V ⟶ U),
      IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j) ∧
      ∃ e : yoneda.obj V ≅ W.toFunctor, e.hom ≫ W.ι = yoneda.map j := by
  let h := hW.2.rep.isPullback (𝟙 (yoneda.obj U))
  let V := hW.2.rep.pullback (𝟙 (yoneda.obj U))
  let j := hW.2.rep.snd (𝟙 (yoneda.obj U))
  let eMap := hW.2.rep.fst (𝟙 (yoneda.obj U))
  have : IsIso eMap := h.isIso_fst_of_isIso
  refine ⟨V, j, hW.2.property_snd (𝟙 (yoneda.obj U)), asIso eMap, ?_⟩
  simpa [eMap, j] using h.w

/-- The base scheme of the family of curves attached to an object of the stack, identified with
the object of the site the structure functor sends it to. -/
private def curveFamilyBaseIso
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)
    (x : 𝒳.val.val.obj) :
    (E.inverse.obj x).base ≅ 𝒳.val.val.p.obj x :=
  have h : 𝒳.val.val.p.obj (E.functor.obj (E.inverse.obj x)) = (E.inverse.obj x).base :=
    Functor.congr_obj hE (E.inverse.obj x)
  eqToIso h.symm ≪≫ 𝒳.val.val.p.mapIso (E.counitIso.app x)

/-- The identification of `AlgebraicGeometry.curveFamilyBaseIso` at the identity point of a
scheme-valued point of the stack. -/
private def curveFamilyBaseIsoAt
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom) :
    (E.inverse.obj (y.obj (Over.mk (𝟙 U.left)))).base ≅ U :=
  let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  have h₁ : 𝒳.val.val.p.obj (y.obj T₀) = (Over.map U.hom).obj T₀ :=
    Functor.congr_obj hy T₀
  have h₂ : (Over.map U.hom).obj T₀ = U := by
    cases U
    congr 1
  curveFamilyBaseIso B hZ 𝒳 E hE (y.obj T₀) ≪≫ eqToIso h₁ ≪≫ eqToIso h₂

/-- `AlgebraicGeometry.curveFamilyBaseIso` is natural. -/
private theorem curveFamilyBaseIso_naturality
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)
    {x z : 𝒳.val.val.obj} (φ : x ⟶ z) :
    (E.inverse.map φ).baseMap ≫ (curveFamilyBaseIso B hZ 𝒳 E hE z).hom =
      (curveFamilyBaseIso B hZ 𝒳 E hE x).hom ≫ 𝒳.val.val.p.map φ := by
  simp only [curveFamilyBaseIso, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, Category.assoc]
  have hm := CategoryTheory.Functor.congr_hom hE.symm (E.inverse.map φ)
  have hc := E.counitIso.hom.naturality φ
  simp only [Functor.comp_map, curvesProjectionOver] at hm
  simp only [Functor.comp_map, Functor.id_map] at hc
  change E.functor.map (E.inverse.map φ) ≫ (E.counitIso.app z).hom =
    (E.counitIso.app x).hom ≫ φ at hc
  have hp := congrArg (fun ψ => 𝒳.val.val.p.map ψ) hc
  have hx : 𝒳.val.val.p.obj (E.functor.obj (E.inverse.obj x)) =
      (E.inverse.obj x).base := Functor.congr_obj hE (E.inverse.obj x)
  have hz : 𝒳.val.val.p.obj (E.functor.obj (E.inverse.obj z)) =
      (E.inverse.obj z).base := Functor.congr_obj hE (E.inverse.obj z)
  have hm' : (E.inverse.map φ).baseMap =
      eqToHom hx.symm ≫ 𝒳.val.val.p.map (E.functor.map (E.inverse.map φ)) ≫
        eqToHom hz := hm
  have hbase : (E.inverse.map φ).baseMap ≫ eqToHom hz.symm =
      eqToHom hx.symm ≫ 𝒳.val.val.p.map (E.functor.map (E.inverse.map φ)) := by
    rw [hm']
    simp [Category.assoc]
  change (E.inverse.map φ).baseMap ≫ eqToHom hz.symm ≫
      𝒳.val.val.p.map (E.counitIso.app z).hom =
    eqToHom hx.symm ≫ 𝒳.val.val.p.map (E.counitIso.app x).hom ≫ 𝒳.val.val.p.map φ
  rw [← Category.assoc, hbase]
  rw [Category.assoc, ← Functor.map_comp, hp, Functor.map_comp]

/-- The morphism of base schemes attached to the structure morphism of an object of a
scheme-valued point of the stack is the structure morphism of the object of the site. -/
private theorem curveFamilyBaseMap_toTerminal
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom)
    (T : BigFppfOver B U.left.1 U.left.2) :
    let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
    let t : T ⟶ T₀ := Over.homMk T.hom rfl
    (E.inverse.map (y.map t)).baseMap ≫ (curveFamilyBaseIsoAt B hZ 𝒳 E hE U y hy).hom =
    (curveFamilyBaseIso B hZ 𝒳 E hE (y.obj T)).hom ≫
      eqToHom (Functor.congr_obj hy T) ≫
      (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by
  dsimp only
  let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  let t : T ⟶ T₀ := Over.homMk T.hom rfl
  have hnat := curveFamilyBaseIso_naturality B hZ 𝒳 E hE (y.map t)
  have hhy := Functor.congr_hom hy t
  have hT : 𝒳.val.val.p.obj (y.obj T) = (Over.map U.hom).obj T :=
    Functor.congr_obj hy T
  have h₁ : 𝒳.val.val.p.obj (y.obj T₀) = (Over.map U.hom).obj T₀ :=
    Functor.congr_obj hy T₀
  have h₂ : (Over.map U.hom).obj T₀ = U := by
    cases U
    congr 1
  have hhy' : 𝒳.val.val.p.map (y.map t) =
      eqToHom hT ≫ (Over.map U.hom).map t ≫ eqToHom h₁.symm := by
    simpa only [Functor.comp_map] using hhy
  have hcanon : (Over.map U.hom).map t ≫ eqToHom h₂ =
      (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by
    cases U
    rfl
  change (E.inverse.map (y.map t)).baseMap ≫
      (curveFamilyBaseIso B hZ 𝒳 E hE (y.obj T₀)).hom ≫ eqToHom h₁ ≫ eqToHom h₂ =
    (curveFamilyBaseIso B hZ 𝒳 E hE (y.obj T)).hom ≫
      eqToHom hT ≫ (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U)
  rw [← Category.assoc, ← Category.assoc, hnat, hhy']
  simp [Category.assoc, hcanon]

/-- Factorizations through a fixed object are carried across isomorphisms of the two ends of a
commuting square. -/
private theorem factorization_iff_of_iso
    {C : Type*} [Category C] {A A' D D' V : C}
    (a : A ⟶ D) (b : A' ⟶ D') (j : V ⟶ D)
    (α : A ≅ A') (β : D ≅ D')
    (h : a ≫ β.hom = α.hom ≫ b) :
    (∃ k : A ⟶ V, k ≫ j = a) ↔ ∃ k : A' ⟶ V, k ≫ (j ≫ β.hom) = b := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨α.inv ≫ k, by rw [Category.assoc, reassoc_of% hk, h, Iso.inv_hom_id_assoc]⟩
  · rintro ⟨k, hk⟩
    refine ⟨α.hom ≫ k, ?_⟩
    apply (cancel_mono β.hom).mp
    simp only [Category.assoc] at hk ⊢
    rw [hk, ← h]

/-- Factoring a morphism of representable presheaves through an open subspace which is itself
represented is factoring the morphism of the representing objects. -/
private theorem factor_openSubspace_iff
    {C : Type*} [Category C] {U V A : C}
    (W : Subfunctor (yoneda.obj U)) (j : V ⟶ U)
    (e : yoneda.obj V ≅ W.toFunctor)
    (he : e.hom ≫ W.ι = yoneda.map j) (a : A ⟶ U) :
    (∃ t : yoneda.obj A ⟶ W.toFunctor, t ≫ W.ι = yoneda.map a) ↔
      ∃ k : A ⟶ V, k ≫ j = a := by
  have he' : e.inv ≫ yoneda.map j = W.ι := by
    rw [← he, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  constructor
  · rintro ⟨t, ht⟩
    exact ⟨yoneda.preimage (t ≫ e.inv), yoneda.map_injective <| by
      rw [Functor.map_comp, yoneda.map_preimage, Category.assoc, he', ht]⟩
  · rintro ⟨k, hk⟩
    refine ⟨yoneda.map k ≫ e.hom, ?_⟩
    rw [Category.assoc, he, ← Functor.map_comp, hk]

/-- Factoring the structure morphism of an object of the site over a scheme through an object
over that scheme is a morphism in the category over the scheme. -/
private theorem factor_to_over_iff
    (S : Scheme.{u}) (hS : B.Contains S)
    (U V : BigFppfOver B S hS) (j : V ⟶ U)
    (T : BigFppfOver B U.left.1 U.left.2) :
    (∃ k : (Over.map U.hom).obj T ⟶ V,
      k ≫ j = (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U)) ↔
      Nonempty (T ⟶ (Over.mk j.left : BigFppfOver B U.left.1 U.left.2)) := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨Over.homMk k.left (congrArg (fun f : (Over.map U.hom).obj T ⟶ U => f.left) hk)⟩
  · rintro ⟨k⟩
    let l : (Over.map U.hom).obj T ⟶ V := Over.homMk k.left (by
      calc
        k.left ≫ V.hom = k.left ≫ j.left ≫ U.hom := by rw [Over.w j]
        _ = T.hom ≫ U.hom := by
          have hk : k.left ≫ j.left = T.hom := k.w
          simpa [Category.assoc] using congrArg (fun f => f ≫ U.hom) hk)
    exact ⟨l, Over.OverMorphism.ext (Over.w k)⟩

/-- The family of curves attached to an object of a scheme-valued point of the stack is
at-worst-nodal of relative dimension one exactly when the object of the site maps to the open
subobject representing the locus in the base. -/
private theorem nodal_y_iff_overFactor
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom) :
    let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
    let G := E.inverse.obj (y.obj T₀)
    ∀ (W : Subfunctor (yoneda.obj G.base))
      (_hWchar : ∀ (F : CurveFamily B hZ) (a : F ⟶ G),
        Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom ↔
          ∃ t : (schemeSpace F.base).obj ⟶ W.toFunctor,
            t ≫ W.ι = (schemeSpaceMap a.baseMap).hom)
      (V : BigFppfOver B integerBase hZ)
      (j : V ⟶ G.base) (eW : yoneda.obj V ≅ W.toFunctor)
      (_heW : eW.hom ≫ W.ι = yoneda.map j)
      (T : BigFppfOver B U.left.1 U.left.2),
      Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ
        (E.inverse.obj (y.obj T)).toBase.hom ↔
        Nonempty (T ⟶ (Over.mk (j ≫ (curveFamilyBaseIsoAt B hZ 𝒳 E hE U y hy).hom).left :
          BigFppfOver B U.left.1 U.left.2)) := by
  dsimp only
  intro W hWchar V j e he T
  let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  let t : T ⟶ T₀ := Over.homMk T.hom rfl
  let F := E.inverse.obj (y.obj T)
  let G := E.inverse.obj (y.obj T₀)
  let a : F ⟶ G := E.inverse.map (y.map t)
  let β := curveFamilyBaseIsoAt B hZ 𝒳 E hE U y hy
  have hT : 𝒳.val.val.p.obj (y.obj T) = (Over.map U.hom).obj T :=
    Functor.congr_obj hy T
  let α : F.base ≅ (Over.map U.hom).obj T :=
    curveFamilyBaseIso B hZ 𝒳 E hE (y.obj T) ≪≫ eqToIso hT
  have hcomm : a.baseMap ≫ β.hom =
      α.hom ≫ (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) := by
    simpa only [α, Iso.trans_hom, eqToIso.hom, Category.assoc] using
      curveFamilyBaseMap_toTerminal B hZ 𝒳 E hE U y hy T
  exact (hWchar F a).trans <|
    (factor_openSubspace_iff W j e he a.baseMap).trans <|
    (factorization_iff_of_iso a.baseMap
      (Over.homMk T.hom : (Over.map U.hom).obj T ⟶ U) j α β hcomm).trans <|
    factor_to_over_iff B integerBase hZ U V (j ≫ β.hom) T

/-- **The locus over a scheme-valued point of the stack is represented by an open subobject.**
Over a scheme-valued point `y` of the stack there is an object of the site over the base scheme
whose structure morphism is an open immersion and which receives a morphism from an object of the
site exactly when the family of curves there is at-worst-nodal of relative dimension one. -/
private theorem exists_nodal_open_over
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)
    (U : BigFppfOver B integerBase hZ)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
    (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom) :
    ∃ V : BigFppfOver B U.left.1 U.left.2,
      IsOpenImmersion (B.inclusion.map V.hom) ∧
      ∀ T : BigFppfOver B U.left.1 U.left.2,
        Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ
          (E.inverse.obj (y.obj T)).toBase.hom ↔ Nonempty (T ⟶ V) := by
  classical
  let T₀ : BigFppfOver B U.left.1 U.left.2 := Over.mk (𝟙 U.left)
  let G := E.inverse.obj (y.obj T₀)
  obtain ⟨W, hW, hWchar⟩ := exists_nodal_baseOpen B hZ G
  obtain ⟨V, j, hj, e, he⟩ := openSubspace_yoneda_representation B
    integerBase hZ G.base W hW
  let β := curveFamilyBaseIsoAt B hZ 𝒳 E hE U y hy
  let j' : V ⟶ U := j ≫ β.hom
  let V' : BigFppfOver B U.left.1 U.left.2 := Over.mk j'.left
  have hj' : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j') := by
    change IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map (j ≫ β.hom))
    rw [Functor.map_comp]
    have : IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map j) := hj
    infer_instance
  exact ⟨V', hj', nodal_y_iff_overFactor B hZ 𝒳 E hE U y hy W hWchar V j e he⟩

/-! ### Representability of the presheaf of proofs by an open subobject -/

/-- Relocalizing the presheaf represented by an object over a scheme of the site along a morphism
of the site is the presheaf represented by the composite structure morphism, pointwise. -/
private def relocalizeYonedaEquivAt
    {C : Type (u + 1)} [Category.{u} C] {V U : C} (f : V ⟶ U)
    (A : Over V) (T : Over U) :
    ((OverShriek.relocalizePresheafFunctor f).obj (yoneda.obj A)).obj (Opposite.op T) ≃
      (yoneda.obj (Over.mk (A.hom ≫ f))).obj (Opposite.op T) := by
  let e : (yoneda.obj (Over.mk (A.hom ≫ f))).obj (Opposite.op T) ≃
      ((OverShriek.relocalizePresheafFunctor f).obj (yoneda.obj A)).obj (Opposite.op T) := by
    dsimp [OverShriek.relocalizePresheafFunctor, OverShriek.presheafFunctorToOver,
      OverShriek.presheaf, OverShriek.fiberFunctor, OverShriek.fiber,
      OverShriek.presheafToYoneda]
    change (T ⟶ Over.mk (A.hom ≫ f)) ≃
      {p : Σ ψ : T.left ⟶ V, (yoneda.obj A).obj (Opposite.op (Over.mk ψ)) //
        p.1 ≫ f = T.hom}
    refine
      { toFun := fun q => ⟨⟨q.left ≫ A.hom, Over.homMk q.left (by simp)⟩, by
          calc
            (q.left ≫ A.hom) ≫ f = q.left ≫ (A.hom ≫ f) := Category.assoc _ _ _
            _ = T.hom := q.w⟩
        invFun := fun x => Over.homMk x.1.2.left (by
          calc
            x.1.2.left ≫ A.hom ≫ f = (x.1.2.left ≫ A.hom) ≫ f :=
              (Category.assoc _ _ _).symm
            _ = x.1.1 ≫ f := congrArg (fun t => t ≫ f) x.1.2.w
            _ = T.hom := x.2)
        left_inv := fun q => by ext; rfl
        right_inv := by
          rintro ⟨⟨ψ, g⟩, hψ⟩
          apply Subtype.ext
          have h := OverShriek.sigmaMk_eq (yoneda.obj A) (𝟙 A)
            (Over.homMk (U := Over.mk (g.left ≫ A.hom)) (V := A) g.left rfl) g rfl
          change (⟨g.left ≫ A.hom,
            (Over.homMk g.left rfl : Over.mk (g.left ≫ A.hom) ⟶ A) ≫ 𝟙 A⟩ :
            Σ χ : T.left ⟶ V, Over.mk χ ⟶ A) = ⟨ψ, g ≫ 𝟙 A⟩ at h
          change (⟨g.left ≫ A.hom,
            (Over.homMk g.left rfl : Over.mk (g.left ≫ A.hom) ⟶ A)⟩ :
            Σ χ : T.left ⟶ V, Over.mk χ ⟶ A) = ⟨ψ, g⟩
          simpa only [Category.comp_id] using h }
  exact e.symm

/-- Relocalizing the presheaf represented by an object over a scheme of the site along a morphism
of the site is the presheaf represented by the composite structure morphism. -/
private def relocalizeYonedaIsoOver
    {C : Type (u + 1)} [Category.{u} C] {V U : C} (f : V ⟶ U) (A : Over V) :
    (OverShriek.relocalizePresheafFunctor f).obj (yoneda.obj A) ≅
      yoneda.obj (Over.mk (A.hom ≫ f)) :=
  NatIso.ofComponents (fun T => (relocalizeYonedaEquivAt f A T.unop).toIso)
    (by
      intro T T' g
      ext q
      apply Over.OverMorphism.ext
      rfl)

/-- An algebraic space over a scheme of the site which is represented by an object whose
structure morphism is an open immersion has open structure morphism as an algebraic space over
the base of the site, through the equivalence of Stacks 04SG. -/
private theorem algebraicSpaceMap_open_of_yonedaIso
    (U : BigFppfOver B integerBase hZ)
    (F : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B U.left.1 U.left.2 F)
    (V : BigFppfOver B U.left.1 U.left.2)
    (hV : IsOpenImmersion (B.inclusion.map V.hom))
    (e : F ≅ yoneda.obj V) :
    Space.IsOpenImmersion B integerBase hZ
      (algebraicSpaceMap B integerBase hZ U
        ((spacesOverSmallerBaseFunctor B U.left.1 integerBase U.left.2 hZ U.hom).obj
          ⟨F, hF⟩)).hom := by
  classical
  let i := spacesOverSmallerBaseFunctorForgetIso B U.left.1 integerBase U.left.2 hZ U.hom
  let K := spacesOverSmallerBaseFunctor B U.left.1 integerBase U.left.2 hZ U.hom
  let V' : BigFppfOver B integerBase hZ := Over.mk (V.hom ≫ U.hom)
  let j' : V' ⟶ Over.mk U.hom := Over.homMk V.hom rfl
  let d : (K.obj ⟨F, hF⟩).1.left ≅ yoneda.obj V' :=
    i.app ⟨F, hF⟩ ≪≫
      (OverShriek.relocalizePresheafFunctor U.hom).mapIso e ≪≫
      relocalizeYonedaIsoOver U.hom V
  have hd : (K.obj ⟨F, hF⟩).1.hom = d.hom ≫ yoneda.map j' := by
    ext W x
    let s := (i.hom.app ⟨F, hF⟩).app W x
    have hx : (i.inv.app ⟨F, hF⟩).app W s = x :=
      congrArg (fun t => t.app W x) (i.app ⟨F, hF⟩).hom_inv_id
    have hs := spacesOverSmallerBaseFunctor_hom_app_forgetIso_inv_app
      B U.left.1 integerBase U.left.2 hZ U.hom ⟨F, hF⟩ W s
    rw [hx] at hs
    apply Over.OverMorphism.ext
    change (((K.obj ⟨F, hF⟩).1.hom).app W x).left = (d.hom.app W x).left ≫ V.hom
    rw [hs]
    change s.1.1 = (d.hom.app W x).left ≫ V.hom
    exact (Over.w (e.hom.app (Opposite.op (Over.mk s.1.1)) s.1.2)).symm
  have hj : Space.IsOpenImmersion B integerBase hZ (yoneda.map j') := by
    let Tf := BigFppfOver.toScheme B integerBase hZ
    let P₀ := MorphismProperty.inverseImage
      (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}) Tf
    let : P₀.IsStableUnderBaseChange := ⟨by
      intro X Y Y' R f g f' g' h hg
      exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (P := @AlgebraicGeometry.IsOpenImmersion) (h.map Tf) hg⟩
    apply MorphismProperty.relative_map (P := P₀)
    exact hV
  let P : MorphismProperty ((BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u) :=
    MorphismProperty.presheaf
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B integerBase hZ))
  have : P.RespectsIso := inferInstance
  change P ((K.obj ⟨F, hF⟩).1.hom)
  rw [hd]
  exact MorphismProperty.RespectsIso.precomp P d.hom (yoneda.map j') hj

/-! ### Stacks 0DSY, part (1) -/

/-- **Stacks 0DSY, part (1).** The open substack `Curves^{nodal}` of families of curves which are
at-worst-nodal of relative dimension one, together with the characterisation of its objects: an
object of the stack belongs to it exactly when the family of curves it classifies is
at-worst-nodal of relative dimension one.

The algebraic stack of curves is a hypothesis: `𝒳` is any algebraic stack over the big fppf site
of the integers whose objects are identified with families of curves by an equivalence `E` over
that site.

Part (2) of the source, the characterisation for a proper scheme over a field, is not asserted
here.

The definition carries `@[no_expose]`: its body names the private helpers that build the
substack, so it may not be exposed. Nothing downstream needs to unfold it — the
characterisation of its objects is the second component of the subtype. -/
@[stacks 0DSY "the open substack and part (1): the characterisation on every family of curves, \
given a presentation of the algebraic stack of curves. Part (2), \
the characterisation for a proper scheme over a field, is NOT asserted here",
  no_expose]
def nodalCurvesOpenSubstack
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ) :
    {U : Stack.OpenSubstack 𝒳 //
      ∀ F : CurveFamily B hZ,
        U.property (E.functor.obj F) ↔
          Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom} := by
  classical
  let P : ObjectProperty 𝒳.val.val.obj := fun x =>
    Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ (E.inverse.obj x).toBase.hom
  have hpre : ∀ {x y : 𝒳.val.val.obj}, (x ⟶ y) → P y → P x := fun f hy =>
    nodal_of_curveFamily_hom B hZ (E.inverse.map f) hy
  have hstrict : P.IsClosedUnderIsomorphisms := ⟨fun e hx => hpre e.inv hx⟩
  have hOpen :
      ∃ hP : Stack.IsAlgebraicStack.{u, w} B integerBase hZ
          (Stack.fullSubcategoryBased 𝒳 P),
        Stack.AlgebraicStacks.IsOpenImmersion B integerBase hZ
          (Stack.fullSubcategoryInclusion 𝒳 P hP) := by
    have hlocal : ∀ (U : BigFppfOver B integerBase hZ)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.val.val.obj)
        (hy : y ⋙ 𝒳.val.val.p = Over.map U.hom),
        IsAlgebraicSpace B U.left.1 U.left.2
          (propertyPresheaf.{u} (fun T => P (y.obj T)) (fun f => hpre (y.map f))) := by
      intro U y hy
      obtain ⟨V, hV, hchar⟩ := exists_nodal_open_over B hZ 𝒳 E hE U y hy
      let e := propertyPresheafIsoYoneda.{u} (fun T => P (y.obj T))
        (fun f => hpre (y.map f)) V hchar
        (subsingleton_hom_of_openOver B U.left.1 U.left.2 V hV)
      exact isAlgebraicSpace_of_iso B U.left.1 U.left.2 e
        (isAlgebraicSpace_yoneda B U.left.1 U.left.2 V)
    let hP := fullSubcategory_isAlgebraicStack_of_local_representability
      B integerBase hZ 𝒳 P hpre hlocal
    refine ⟨hP, ?_⟩
    constructor
    · intro U
      dsimp only
      intro y hy
      exact ⟨propertyPresheaf.{u} (fun T => P (y.obj T)) (fun f => hpre (y.map f)),
        hlocal U y hy,
        ⟨fullSubcategoryBaseChangePresheafEquivalence
          𝒳.val.val.p (Over.map U.hom) y hy P hpre⟩⟩
    · intro U y hy F hF heF
      obtain ⟨V, hV, hchar⟩ := exists_nodal_open_over B hZ 𝒳 E hE U y hy
      let Q := propertyPresheaf.{u} (fun T => P (y.obj T)) (fun f => hpre (y.map f))
      let eQ := fullSubcategoryBaseChangePresheafEquivalence
        𝒳.val.val.p (Over.map U.hom) y hy P hpre
      have hp : (TwoFibreProductOver.fst (Over.map U.hom)
          (P.ι ⋙ 𝒳.val.val.p) 𝒳.val.val.p y P.ι).IsFiberedInGroupoids :=
        StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver eQ
          (elementsProjection_isFiberedInSetoids Q).isFiberedInGroupoids
      let e : F ≅ Q := presheafIsoOfEquivalenceOver hp F Q (Classical.choice heF) eQ
      let eV := propertyPresheafIsoYoneda.{u} (fun T => P (y.obj T))
        (fun f => hpre (y.map f)) V hchar
        (subsingleton_hom_of_openOver B U.left.1 U.left.2 V hV)
      exact algebraicSpaceMap_open_of_yonedaIso B hZ U F hF V hV (e ≪≫ eV)
  exact ⟨⟨P, hstrict, hOpen.choose, hOpen.choose_spec⟩,
    fun F => (nodal_iff_of_curveFamily_iso B hZ (E.unitIso.app F)).symm⟩

/-- **Stacks 0DSY, part (1).** The classifying object of a family of curves lifts through the
inclusion of the nodal open substack exactly when the family is at-worst-nodal of relative
dimension one.

As for `AlgebraicGeometry.nodalCurvesOpenSubstack`, the algebraic stack of curves and its
identification with families of curves are hypotheses. -/
@[stacks 0DSY "part (1): the classifying morphism of a family factors through the nodal open \
substack iff the family is at-worst-nodal of relative dimension one, given a presentation of \
the algebraic stack of curves. Part (2), the \
characterisation for a proper scheme over a field, is NOT asserted here"]
theorem classifying_factors_nodalCurvesOpenSubstack_iff
    (𝒳 : Stack.AlgebraicStacks.{u, w} B integerBase hZ)
    (E : CurveFamily B hZ ≌ 𝒳.val.val.obj)
    (hE : E.functor ⋙ 𝒳.val.val.p = curvesProjectionOver B hZ)
    (F : CurveFamily B hZ) :
    (∃ Y : (nodalCurvesOpenSubstack B hZ 𝒳 E hE).1.property.FullSubcategory,
      Y.obj = E.functor.obj F) ↔
      Space.IsAtWorstNodalOfRelativeDimensionOne B integerBase hZ F.toBase.hom := by
  have hchar := (nodalCurvesOpenSubstack B hZ 𝒳 E hE).2 F
  constructor
  · rintro ⟨Y, hY⟩
    exact hchar.mp (hY ▸ Y.property)
  · intro hN
    exact ⟨⟨E.functor.obj F, hchar.mpr hN⟩, rfl⟩

end AlgebraicGeometry

end
