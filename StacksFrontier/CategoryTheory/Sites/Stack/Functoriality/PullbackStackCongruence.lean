module

public import Mathlib.CategoryTheory.Localization.Equivalence
public import StacksFrontier.CategoryTheory.FiberedCategory.Amelioration
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStack
public import StacksFrontier.CategoryTheory.Sites.Stack.Functoriality.PullbackStackification
public import StacksFrontier.CategoryTheory.Sites.Stackification.Stackification
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalPropertyUniqueness

/-!
# Equivalent fibred categories have equivalent pullbacks along a morphism of sites

Let `f : (𝒟, K) ⟶ (𝒞, J)` be the morphism of sites attached to a continuous left exact functor
`u : 𝒞 ⥤ 𝒟`, and let `p : 𝒮 ⥤ 𝒞`, `q : 𝒯 ⥤ 𝒞` be fibred categories which are equivalent over `𝒞`.
This file shows that `f⁻¹𝒮` and `f⁻¹𝒯` are then equivalent over `𝒟`, where the pullback is taken
in the explicit form of Stacks 04WJ: the three-stage stackification of the fibred category `u_p`
of Stacks 04WG.

Two independent steps. First, an equivalence over `𝒞` induces an equivalence `u_p 𝒮 ⥤ u_p 𝒯`:
the functor `Ψ` of Stacks 04WR is the localization of the evident functor on comma categories, and
the unit and counit of the given equivalence localize to a unit and counit for it. Second, a
stackification of equivalent fibred categories is equivalent: both stackifications satisfy the
universal property of Stacks 04W9 against each other, so the two 1-morphisms into them correspond
to each other and the comparison is an equivalence.

## Main definitions

* `CategoryTheory.Functor.FibredMor.ofEquivalenceOver` and
  `CategoryTheory.Functor.FibredMor.ofEquivalenceOverSymm`: the two 1-morphisms of an equivalence
  over the base, read as 1-morphisms of fibred categories.
* `CategoryTheory.Functor.equivalenceOverOfUniversalMorphisms`: the comparison of two
  stackifications of one fibred category.
* `CategoryTheory.Functor.stageThreeCongr`: equivalent fibred categories have equivalent
  three-stage stackifications.

## Main results

* `CategoryTheory.Functor.restrictMor_toStageThree_isEquivalence`: Stacks 04W9 for the explicit
  stackification of Stacks 02ZN.
* `CategoryTheory.Comma.pullbackLocalizationMap_isEquivalence`: the functor `Ψ` of Stacks 04WR
  attached to an equivalence over the base is an equivalence.
* `CategoryTheory.Comma.nonempty_equivalenceOver_stageThreeProj_pullbackProj`: equivalent fibred
  categories have equivalent pullbacks along the morphism of sites.

## Implementation notes

An equivalence over the base is a `StacksRepresentableCFG.EquivalenceOver`, whose 1-morphisms are
functors commuting strictly with the structure functors but are not asked to preserve strongly
cartesian morphisms. They do, by `CategoryTheory.Equivalence.isStronglyCartesian_map_functor`, so
each of them is a `CategoryTheory.Functor.FibredMor`; that upgrade is what lets the universal
property of Stacks 04W9, which is stated for 1-morphisms of fibred categories, be applied to them.

`CategoryTheory.Functor.equivalenceOverOfUniversalMorphisms` is stated for two 1-morphisms out of
one fibred category, each of which is a stackification in the sense that restriction along it is
an equivalence of morphism categories against both targets. That is weaker than asking for the two
clauses of Stacks 02ZN and is all the comparison needs, so the same statement serves both for
comparing a stackification with a stack it is equivalent to and for comparing the stackifications
of two equivalent fibred categories.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 04W9](https://stacks.math.columbia.edu/tag/04W9)
* [Stacks Project, Tag 04WG](https://stacks.math.columbia.edu/tag/04WG)
* [Stacks Project, Tag 04WJ](https://stacks.math.columbia.edu/tag/04WJ)
* [Stacks Project, Tag 04WR](https://stacks.math.columbia.edu/tag/04WR)
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe uc ux uy uz vc vx vy vz

section FibredMor

variable {C : Type uc} [Category.{vc} C] {X : Type ux} [Category.{vx} X]
  {Y : Type uy} [Category.{vy} Y] {Z : Type uz} [Category.{vz} Z]

/-- The identity 1-morphism of fibred categories. -/
abbrev Functor.fibredMorId (p : X ⥤ C) : Functor.FibredMor p p :=
  ⟨𝟭 X, Functor.IsFibredOneMorphism.id p⟩

/-- The composite of two 1-morphisms of fibred categories. -/
abbrev Functor.fibredMorComp {p : X ⥤ C} {q : Y ⥤ C} {r : Z ⥤ C}
    (F : Functor.FibredMor p q) (G : Functor.FibredMor q r) : Functor.FibredMor p r :=
  ⟨F.functor ⋙ G.functor, F.isFibredOneMorphism.comp G.isFibredOneMorphism⟩

/-- Post-composition with a 1-morphism of fibred categories, as a functor of morphism
categories. -/
abbrev Functor.fibredMorPostcomp {p : X ⥤ C} {q : Y ⥤ C} {r : Z ⥤ C}
    (G : Functor.FibredMor q r) : Functor.FibredMor p q ⥤ Functor.FibredMor p r where
  obj F := Functor.fibredMorComp F G
  map α :=
    { trans := Functor.whiskerRight α.trans G.functor
      isHomLift x := by
        have := α.isHomLift x
        exact G.isFibredOneMorphism.map_isHomLift _ _ }
  map_id _ := Functor.FibredMor.Hom.ext' (by ext; simp [Functor.fibredMorComp])
  map_comp _ _ := Functor.FibredMor.Hom.ext' (by ext; simp [Functor.fibredMorComp])

/-- An isomorphism of 1-morphisms of fibred categories, read as an isomorphism of the underlying
functors. -/
abbrev Functor.fibredMorNatIso {p : X ⥤ C} {q : Y ⥤ C} {F G : Functor.FibredMor p q}
    (e : F ≅ G) : F.functor ≅ G.functor where
  hom := e.hom.trans
  inv := e.inv.trans
  hom_inv_id := congrArg Functor.FibredMor.Hom.trans e.hom_inv_id
  inv_hom_id := congrArg Functor.FibredMor.Hom.trans e.inv_hom_id

/-- An equivalence over the base assembled from two 1-morphisms of fibred categories and a unit
and counit in the morphism categories. -/
def Functor.equivalenceOverOfFibredMor {p : X ⥤ C} {q : Y ⥤ C}
    (F : Functor.FibredMor p q) (G : Functor.FibredMor q p)
    (η : Functor.fibredMorId p ≅ Functor.fibredMorComp F G)
    (ε : Functor.fibredMorComp G F ≅ Functor.fibredMorId q) :
    StacksRepresentableCFG.EquivalenceOver p q where
  hom := ⟨F.functor, F.isFibredOneMorphism.comp_eq⟩
  inv := ⟨G.functor, G.isFibredOneMorphism.comp_eq⟩
  unitIso := Functor.fibredMorNatIso η
  counitIso := Functor.fibredMorNatIso ε
  unit_over := by
    ext x
    have := η.hom.isHomLift x
    simpa [Functor.fibredMorNatIso, Functor.fibredMorId, Functor.fibredMorComp] using
      IsHomLift.fac' p (𝟙 (p.obj x)) (η.hom.trans.app x)
  counit_over := by
    ext y
    have := ε.hom.isHomLift y
    simpa [Functor.fibredMorNatIso, Functor.fibredMorId, Functor.fibredMorComp] using
      IsHomLift.fac' q (𝟙 (q.obj y)) (ε.hom.trans.app y)

/-- The forward 1-morphism of an equivalence over the base, as a 1-morphism of fibred
categories. -/
abbrev Functor.FibredMor.ofEquivalenceOver {p : X ⥤ C} {q : Y ⥤ C}
    (e : StacksRepresentableCFG.EquivalenceOver p q) : Functor.FibredMor p q :=
  ⟨e.hom.functor, ⟨e.hom.w, by
    intro R T f a b g hg
    exact e.toEquivalence.isStronglyCartesian_map_functor q e.hom.w f g hg⟩⟩

/-- The backward 1-morphism of an equivalence over the base, as a 1-morphism of fibred
categories. -/
abbrev Functor.FibredMor.ofEquivalenceOverSymm {p : X ⥤ C} {q : Y ⥤ C}
    (e : StacksRepresentableCFG.EquivalenceOver p q) : Functor.FibredMor q p :=
  ⟨e.inv.functor, ⟨e.inv.w, by
    intro R T f a b g hg
    exact e.toEquivalence.symm.isStronglyCartesian_map_functor p e.inv.w f g hg⟩⟩

/-- The unit of an equivalence over the base, in the category of 1-morphisms of fibred
categories. -/
def Functor.FibredMor.unitIsoOfEquivalenceOver {p : X ⥤ C} {q : Y ⥤ C}
    (e : StacksRepresentableCFG.EquivalenceOver p q) :
    Functor.fibredMorId p ≅ Functor.fibredMorComp (Functor.FibredMor.ofEquivalenceOver e)
      (Functor.FibredMor.ofEquivalenceOverSymm e) :=
  Functor.FibredMor.isoMk e.unitIso e.isHomLift_unitIso_hom_app

/-- The counit of an equivalence over the base, in the category of 1-morphisms of fibred
categories. -/
def Functor.FibredMor.counitIsoOfEquivalenceOver {p : X ⥤ C} {q : Y ⥤ C}
    (e : StacksRepresentableCFG.EquivalenceOver p q) :
    Functor.fibredMorComp (Functor.FibredMor.ofEquivalenceOverSymm e)
      (Functor.FibredMor.ofEquivalenceOver e) ≅ Functor.fibredMorId q :=
  Functor.FibredMor.isoMk e.counitIso e.isHomLift_counitIso_hom_app

/-- The unit of the equivalence of morphism categories induced by an equivalence over the base. -/
private def restrictMorUnitIso {p : X ⥤ C} {q : Y ⥤ C} (r : Z ⥤ C)
    (e : StacksRepresentableCFG.EquivalenceOver p q) :
    𝟭 _ ≅ Functor.restrictMor (q := r) (Functor.FibredMor.ofEquivalenceOver e).isFibredOneMorphism ⋙
      Functor.restrictMor (q := r)
        (Functor.FibredMor.ofEquivalenceOverSymm e).isFibredOneMorphism :=
  NatIso.ofComponents (fun H =>
    Functor.FibredMor.isoMk (Functor.isoWhiskerRight e.counitIso.symm H.functor) (by
      intro x
      have h₁ : q.IsHomLift (𝟙 (q.obj x)) (e.counitIso.app x).hom :=
        e.isHomLift_counitIso_hom_app x
      have h₂ : q.IsHomLift (𝟙 (q.obj x)) (e.counitIso.inv.app x) :=
        IsHomLift.lift_id_inv q (q.obj x) (e.counitIso.app x)
      exact H.isFibredOneMorphism.map_isHomLift (𝟙 (q.obj x)) (e.counitIso.inv.app x))) (by
        intro H H' α
        apply Functor.FibredMor.Hom.ext'
        ext x
        simp [Functor.restrictMor, Functor.FibredMor.isoMk])

/-- **Restriction along an equivalence over the base is an equivalence of morphism categories.**
Pre-composition with the forward 1-morphism of an equivalence over the base is an equivalence from
the 1-morphisms out of its target into any fixed category over the base onto the 1-morphisms out
of its source. -/
theorem Functor.restrictMor_isEquivalence_of_equivalenceOver {p : X ⥤ C} {q : Y ⥤ C} (r : Z ⥤ C)
    (e : StacksRepresentableCFG.EquivalenceOver p q) :
    (Functor.restrictMor (q := r)
      (Functor.FibredMor.ofEquivalenceOver e).isFibredOneMorphism).IsEquivalence :=
  (Equivalence.mk _ _ (restrictMorUnitIso r e)
    (restrictMorUnitIso r e.symm).symm).isEquivalence_functor

/-- **Two stackifications of one fibred category are equivalent over the base.** If restriction
along each of two 1-morphisms `A : p ⟶ q` and `B : p ⟶ r` of fibred categories is an equivalence
of morphism categories into both targets, then `q` and `r` are equivalent over the base. -/
noncomputable def Functor.equivalenceOverOfUniversalMorphisms {p : X ⥤ C} {q : Y ⥤ C} {r : Z ⥤ C}
    (A : Functor.FibredMor p q) (B : Functor.FibredMor p r)
    [(Functor.restrictMor (q := r) A.isFibredOneMorphism).IsEquivalence]
    [(Functor.restrictMor (q := q) A.isFibredOneMorphism).IsEquivalence]
    [(Functor.restrictMor (q := q) B.isFibredOneMorphism).IsEquivalence]
    [(Functor.restrictMor (q := r) B.isFibredOneMorphism).IsEquivalence] :
    StacksRepresentableCFG.EquivalenceOver q r := by
  let RA := Functor.restrictMor (q := r) A.isFibredOneMorphism
  let RB := Functor.restrictMor (q := q) B.isFibredOneMorphism
  let F := RA.objPreimage B
  let G := RB.objPreimage A
  let α : Functor.fibredMorComp A F ≅ B := RA.objObjPreimageIso B
  let β : Functor.fibredMorComp B G ≅ A := RB.objObjPreimageIso A
  let η₀ : Functor.fibredMorComp A (Functor.fibredMorComp F G) ≅
      Functor.fibredMorComp A (Functor.fibredMorId q) :=
    (Functor.fibredMorPostcomp G).mapIso α ≪≫ β
  let ε₀ : Functor.fibredMorComp B (Functor.fibredMorComp G F) ≅
      Functor.fibredMorComp B (Functor.fibredMorId r) :=
    (Functor.fibredMorPostcomp F).mapIso β ≪≫ α
  exact Functor.equivalenceOverOfFibredMor F G
    ((Functor.restrictMor (q := q) A.isFibredOneMorphism).preimageIso η₀).symm
    ((Functor.restrictMor (q := r) B.isFibredOneMorphism).preimageIso ε₀)

end FibredMor

section StageThree

universe w t₁ t₂ t₃ vb

variable {C : Type t₁} [Category.{vb} C] {X : Type t₂} [Category.{max t₁ t₂ w vb} X]
  {Y : Type t₃} [Category.{max t₁ t₂ w vb} Y]

/-- **Stacks 04W9 for the explicit stackification of Stacks 02ZN.** Restriction along the
canonical 1-morphism of a fibred category into its three-stage stackification is an equivalence of
morphism categories into any stack over the site. -/
theorem Functor.restrictMor_toStageThree_isEquivalence (p : X ⥤ C) [p.IsFibered]
    (J : GrothendieckTopology C) {t : Y ⥤ C} (ht : t.IsStack J) :
    (Functor.restrictMor (q := t) (Functor.isFibredOneMorphism_toStageThree p J)).IsEquivalence :=
  have := ht.isFibered
  Functor.Stackification.restrict_isEquivalence
    (Functor.isFibredOneMorphism_toStageThree p J)
    (Functor.isLocallyBijective_morPresheafMap_toStageThree p J) ht.isMorSheaf
    (Functor.essImage_pullbackFiber_toStageThree p J) ht.hasEffectiveDescent

/-- **A fibred category equivalent over the site to a stack is equivalent over the site to its own
three-stage stackification.** -/
noncomputable def Functor.stageThreeEquivalenceOfEquivalence {p : X ⥤ C} {q : Y ⥤ C}
    [p.IsFibered] (J : GrothendieckTopology C) (hq : q.IsStack J)
    (e : StacksRepresentableCFG.EquivalenceOver p q) :
    StacksRepresentableCFG.EquivalenceOver (p.stageThreeProj J) q := by
  let A : Functor.FibredMor p (p.stageThreeProj J) :=
    ⟨p.toStageThree J, Functor.isFibredOneMorphism_toStageThree p J⟩
  let B := Functor.FibredMor.ofEquivalenceOver e
  have hP := Functor.isStack_stageThreeProj p J
  have h₁ := Functor.restrictMor_toStageThree_isEquivalence p J hq
  have h₂ := Functor.restrictMor_toStageThree_isEquivalence p J hP
  have h₃ := Functor.restrictMor_isEquivalence_of_equivalenceOver q e
  have h₄ := Functor.restrictMor_isEquivalence_of_equivalenceOver (p.stageThreeProj J) e
  exact Functor.equivalenceOverOfUniversalMorphisms A B

end StageThree

section StageThreeCongr

universe w t₁ t₂ t₃ vb

variable {C : Type t₁} [Category.{vb} C] {X : Type t₂} [Category.{max t₁ t₂ w vb} X]
  {Y : Type t₂} [Category.{max t₁ t₂ w vb} Y]

/-- **Equivalent fibred categories have equivalent three-stage stackifications.** -/
noncomputable def Functor.stageThreeCongr {p : X ⥤ C} {q : Y ⥤ C} [p.IsFibered] [q.IsFibered]
    (J : GrothendieckTopology C) (e : StacksRepresentableCFG.EquivalenceOver p q) :
    StacksRepresentableCFG.EquivalenceOver (p.stageThreeProj J) (q.stageThreeProj J) := by
  let A : Functor.FibredMor p (p.stageThreeProj J) :=
    ⟨p.toStageThree J, Functor.isFibredOneMorphism_toStageThree p J⟩
  let Q : Functor.FibredMor q (q.stageThreeProj J) :=
    ⟨q.toStageThree J, Functor.isFibredOneMorphism_toStageThree q J⟩
  let B := Functor.fibredMorComp (Functor.FibredMor.ofEquivalenceOver e) Q
  have hP := Functor.isStack_stageThreeProj p J
  have hQ := Functor.isStack_stageThreeProj q J
  have h₁ := Functor.restrictMor_toStageThree_isEquivalence p J hP
  have h₂ := Functor.restrictMor_toStageThree_isEquivalence p J hQ
  have h₃ : (Functor.restrictMor (q := p.stageThreeProj J)
      B.isFibredOneMorphism).IsEquivalence := by
    have hq₁ := Functor.restrictMor_toStageThree_isEquivalence q J hP
    have hq₂ := Functor.restrictMor_isEquivalence_of_equivalenceOver (p.stageThreeProj J) e
    change (Functor.restrictMor (q := p.stageThreeProj J) Q.isFibredOneMorphism ⋙
      Functor.restrictMor (q := p.stageThreeProj J)
        (Functor.FibredMor.ofEquivalenceOver e).isFibredOneMorphism).IsEquivalence
    infer_instance
  have h₄ : (Functor.restrictMor (q := q.stageThreeProj J)
      B.isFibredOneMorphism).IsEquivalence := by
    have hq₁ := Functor.restrictMor_toStageThree_isEquivalence q J hQ
    have hq₂ := Functor.restrictMor_isEquivalence_of_equivalenceOver (q.stageThreeProj J) e
    change (Functor.restrictMor (q := q.stageThreeProj J) Q.isFibredOneMorphism ⋙
      Functor.restrictMor (q := q.stageThreeProj J)
        (Functor.FibredMor.ofEquivalenceOver e).isFibredOneMorphism).IsEquivalence
    infer_instance
  exact Functor.equivalenceOverOfUniversalMorphisms A B

end StageThreeCongr

section Pullback

universe t₁ t₂ t₃ t₄ vb vt vt'

variable {C : Type t₁} [Category.{vb} C] {X : Type t₂} [Category.{vt} X]
  {Y : Type t₃} [Category.{vt'} Y] {Z : Type t₄} [Category.{vb} Z]

/-- **An equivalence over the base lifts to an equivalence over the base of the identity functor
on the comma categories of Stacks 04WF.** -/
noncomputable def Comma.commaUnitIsoOfEquivalenceOver {p : X ⥤ C} {q : Y ⥤ C} (i : C ⥤ Z)
    (e : StacksRepresentableCFG.EquivalenceOver p q) :
    𝟭 (Comma (𝟭 Z) (p ⋙ i)) ≅ commaMapOver i e.hom.w ⋙ commaMapOver i e.inv.w :=
  NatIso.ofComponents (fun x => Comma.isoMk (Iso.refl _) (e.unitIso.app x.right) (by
    have he := congrArg (fun α => α.app x.right) e.unit_over
    dsimp at he
    simp [commaMapOver, he, eqToHom_map])) (by
      intro x y f
      apply Comma.hom_ext
      · simp
      · exact e.unitIso.hom.naturality f.right)

/-- **The functor `Ψ` of Stacks 04WR attached to an equivalence over the base is an
equivalence.** -/
theorem Comma.pullbackLocalizationMap_isEquivalence {p : X ⥤ C} {q : Y ⥤ C} (i : C ⥤ Z)
    (e : StacksRepresentableCFG.EquivalenceOver p q) :
    (pullbackLocalizationMap i
      (Functor.FibredMor.ofEquivalenceOver e).isFibredOneMorphism).IsEquivalence := by
  let A := Comma.idBaseStronglyCartesian p i
  let B := Comma.idBaseStronglyCartesian q i
  let M := commaMapOver i e.hom.w
  let N := commaMapOver i e.inv.w
  let P := pullbackLocalizationMap i
    (Functor.FibredMor.ofEquivalenceOver e).isFibredOneMorphism
  let Q := pullbackLocalizationMap i
    (Functor.FibredMor.ofEquivalenceOverSymm e).isFibredOneMorphism
  have liftP : Localization.Lifting A.Q A (M ⋙ B.Q) P :=
    ⟨eqToIso (pullbackLocalizationMap_fac i
      (Functor.FibredMor.ofEquivalenceOver e).isFibredOneMorphism)⟩
  have liftQ : Localization.Lifting B.Q B (N ⋙ A.Q) Q :=
    ⟨eqToIso (pullbackLocalizationMap_fac i
      (Functor.FibredMor.ofEquivalenceOverSymm e).isFibredOneMorphism)⟩
  apply Localization.isEquivalence A.Q A B.Q B (M ⋙ B.Q) P (N ⋙ A.Q) Q
  · exact Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft M
        (eqToIso (pullbackLocalizationMap_fac i
          (Functor.FibredMor.ofEquivalenceOverSymm e).isFibredOneMorphism)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Comma.commaUnitIsoOfEquivalenceOver i e).symm A.Q ≪≫
      Functor.leftUnitor _
  · exact Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft N
        (eqToIso (pullbackLocalizationMap_fac i
          (Functor.FibredMor.ofEquivalenceOver e).isFibredOneMorphism)) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Comma.commaUnitIsoOfEquivalenceOver i e.symm).symm B.Q ≪≫
      Functor.leftUnitor _

/-- **A functor over the base which is an equivalence of categories is an equivalence over the
base**, when its source is fibred. -/
theorem Functor.nonempty_equivalenceOver_of_isEquivalence {p : X ⥤ C} {q : Y ⥤ C}
    (hp : p.IsFibered) (F : X ⥤ Y) (hFe : F.IsEquivalence) (hF : F ⋙ q = p) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver p q) := by
  classical
  subst hF
  have hsurj : ∀ y : Y, ∃ (x : X) (e : F.obj x ≅ y),
      q.IsHomLift (𝟙 (q.obj y)) e.hom := by
    intro y
    let x := F.objPreimage y
    let ε := F.objObjPreimageIso y
    let f := (q.mapIso ε).inv
    let g := Functor.IsPreFibered.pullbackMap (p := F ⋙ q) (a := x) rfl f
    have hiso : IsIso g := Functor.IsStronglyCartesian.isIso_of_base_isIso (p := F ⋙ q) f g
    let k := F.mapIso (asIso g) ≪≫ ε
    refine ⟨_, k, ?_⟩
    have hlift : q.IsHomLift f (F.map g) :=
      Functor.isHomLift_map_of_comp_eq rfl f g
    have hc : q.IsHomLift (f ≫ q.map ε.hom) (F.map g ≫ ε.hom) := inferInstance
    simpa [f, k] using hc
  obtain ⟨I, hI, η, hη, ε, hε⟩ :=
    (Functor.isFibredEquivalenceOver_of_fullyFaithful F hsurj).exists_inverse
  exact ⟨Functor.equivalenceOverOfFibredMor
    ⟨F, Functor.IsFibredOneMorphism.of_fullyFaithful F hsurj⟩ ⟨I, hI⟩
    (Functor.FibredMor.isoMk η hη) (Functor.FibredMor.isoMk ε hε)⟩

end Pullback

section PullbackCongr

universe c₁ c₂ c₄ wb wx

variable {C : Type c₁} [Category.{wb} C] {Z : Type c₄} [Category.{wb} Z]
  {X : Type c₂} [Category.{wx} X] {Y : Type c₂} [Category.{wx} Y]

/-- **Equivalent fibred categories have equivalent pullbacks along a morphism of sites.** The
pullback is taken in the explicit form of Stacks 04WJ: the three-stage stackification of the
fibred category `u_p` of Stacks 04WG.

Every hypothesis is an explicit argument. The two sides of a change of big site are the same
category under two different names, so an instance supplied under one name is invisible to a goal
phrased under the other; passing the witnesses explicitly makes the statement usable from either
spelling. -/
theorem Comma.nonempty_equivalenceOver_stageThreeProj_pullbackProj
    (p : X ⥤ C) (q : Y ⥤ C) (i : C ⥤ Z) (K : GrothendieckTopology Z)
    (hp : p.IsFibered) (hq : q.IsFibered) (hC : HasFiniteLimits C)
    (hi : PreservesFiniteLimits i) (hpi : (Comma.pullbackProj p i).IsFibered)
    (hqi : (Comma.pullbackProj q i).IsFibered)
    (e : StacksRepresentableCFG.EquivalenceOver p q) :
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (letI := hpi; (Comma.pullbackProj p i).stageThreeProj K)
      (letI := hqi; (Comma.pullbackProj q i).stageThreeProj K)) := by
  have hp' := hp
  have hq' := hq
  have hC' := hC
  have hi' := hi
  obtain ⟨E⟩ := Functor.nonempty_equivalenceOver_of_isEquivalence hpi
    (pullbackLocalizationMap i
      (Functor.FibredMor.ofEquivalenceOver e).isFibredOneMorphism)
    (Comma.pullbackLocalizationMap_isEquivalence i e)
    (pullbackLocalizationMap_comp_pullbackProj i
      (Functor.FibredMor.ofEquivalenceOver e).isFibredOneMorphism)
  exact ⟨Functor.stageThreeCongr K E⟩

end PullbackCongr

end CategoryTheory

end
