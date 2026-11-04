module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.Stabilizer.ActionGroupoid
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.TransitionReindexComp

/-!
# Equivariant quasi-coherent modules and modules on the action groupoid

Let `G` be a group algebraic space over an algebraic space `B` acting on an algebraic space `X`
over `B`.  The action makes `(X, G ×_B X, pr₁, a, m)` a groupoid in algebraic spaces, the action
groupoid of Stacks 0444: its source is the projection `pr₁ : G ×_B X ⟶ X` and its target is the
action `a : G ×_B X ⟶ X`, so a transition morphism `α : t^*ℱ ⟶ s^*ℱ` on the groupoid is
literally a transition morphism `α : a^*ℱ ⟶ pr₁^*ℱ` for the action.  The rule `(ℱ, α) ↦ (ℱ, α)`
therefore carries `G`-equivariant quasi-coherent `𝒪_X`-modules to quasi-coherent modules on the
action groupoid, and it is an equivalence of categories.  This is Stacks 0445.

## Main definitions

* `AlgebraicGeometry.Space.actionGroupoid`: the action groupoid `(X, G ×_B X, pr₁, a, m)` of an
  action of a group algebraic space.
* `AlgebraicGeometry.Space.ActionGroupoidModulesComparison`: a functor from the `G`-equivariant
  quasi-coherent `𝒪_X`-modules to the quasi-coherent modules on a groupoid which leaves the
  underlying module, the transition morphism and the morphisms unchanged, and is fully faithful
  and essentially surjective.

## Main results

* `AlgebraicGeometry.Space.unit_of_transitionUnit` and
  `AlgebraicGeometry.Space.groupoidPullbackTransition_identityArrow_eq_pullbackTransport`: the
  unit condition of Stacks 0441 on a transition morphism of a quasi-coherent module on a
  groupoid in algebraic spaces is `AlgebraicGeometry.Space.TransitionUnit` at the unit arrow,
  and it suffices to have it at any morphism equal to the unit arrow.
* `AlgebraicGeometry.Space.groupoidPullbackTransition_comp_eq_groupoidTransitionComposite`: the
  cocycle condition of Stacks 0441 is `AlgebraicGeometry.Space.TransitionCocycle` at any triple
  of morphisms of the arrow space equal to the two projections and the composition.
* `AlgebraicGeometry.Space.QuasicoherentModule.transitionUnit` and
  `AlgebraicGeometry.Space.QuasicoherentModule.transitionCocycle`: the transition morphism of a
  quasi-coherent module on a groupoid satisfies `AlgebraicGeometry.Space.TransitionUnit` at the
  unit arrow and `AlgebraicGeometry.Space.TransitionCocycle` at the two projections of the space
  of composable pairs of arrows and the composition.
* `AlgebraicGeometry.Space.actionGroupoidModulesComparison`: the rule `(ℱ, α) ↦ (ℱ, α)` is a
  fully faithful and essentially surjective functor from the `G`-equivariant quasi-coherent
  `𝒪_X`-modules to the quasi-coherent modules on the action groupoid, leaving the underlying
  module, the transition morphism and the morphisms unchanged.
* `AlgebraicGeometry.Space.actionGroupoidModulesEquivalence`: the same result read as an
  equivalence of categories.

## References

* [Stacks Project, Tag 0445](https://stacks.math.columbia.edu/tag/0445)
* [Stacks Project, Tag 0444](https://stacks.math.columbia.edu/tag/0444)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 043H](https://stacks.math.columbia.edu/tag/043H)
* [Stacks Project, Tag 043T](https://stacks.math.columbia.edu/tag/043T)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}

/-! ### The action groupoid of an action -/

/-- The action groupoid `(X, G ×_B X, pr₁, a, m)` of an action `A` of a group algebraic space `G`
over `B` on an algebraic space `X` over `B`, with the projection as its source and the action
morphism as its target. -/
@[stacks 0444 "the action groupoid itself",
  stacks 06DZ "the groupoid `(Spec k, G, p, p, m)` of a group over a field, at the trivial"]
noncomputable abbrev actionGroupoid (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (A : ModObj G.obj.X X) :
    GroupoidInAlgebraicSpaces 𝒞 S hS ⟨B, hB⟩ :=
  letI : GrpObj G.obj.X := G.obj.grp
  letI : ModObj G.obj.X X := A
  (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX).groupoid

/-! ### The unit law of Stacks 0441 as an instance of the abstract unit condition -/

/-- The unit condition of Stacks 0441 on a transition morphism `α : t^*ℱ ⟶ s^*ℱ` is
`AlgebraicGeometry.Space.TransitionUnit` at the unit arrow of the groupoid. -/
theorem unit_of_transitionUnit {A : AlgebraicSpaces 𝒞 S hS}
    (H : GroupoidInAlgebraicSpaces 𝒞 S hS A)
    (F : Modules.{u, u} 𝒞 S hS H.objects.1 H.objects.2)
    (α : (modulePullback 𝒞 S hS H.target).obj F ⟶ (modulePullback 𝒞 S hS H.source).obj F)
    (h : TransitionUnit 𝒞 S hS (U := H.objects) (V := H.arrows)
      (a := H.target) (b := H.source) F α (identityArrow H)) :
    groupoidPullbackTransition 𝒞 S hS H F α (identityArrow H) =
      pullbackTransport F
        ((identityArrow_comp_target H).trans (identityArrow_comp_source H).symm) := by
  rw [groupoidPullbackTransition_eq_transitionReindex]
  exact h _

section Reindex

variable (𝒞 S hS)

/-- The cocycle condition of Stacks 0441 holds as soon as the cocycle law holds at some triple
of morphisms of the arrow space equal to the two projections of the space of composable pairs
of arrows and to the composition. -/
theorem groupoidPullbackTransition_comp_eq_groupoidTransitionComposite
    {Y : AlgebraicSpaces 𝒞 S hS} (H : GroupoidInAlgebraicSpaces 𝒞 S hS Y)
    (F : Modules.{u, u} 𝒞 S hS H.objects.1 H.objects.2)
    (α : (modulePullback 𝒞 S hS H.target).obj F ⟶ (modulePullback 𝒞 S hS H.source).obj F)
    (p q r : AlgebraicSpaces.fiberProduct 𝒞 S hS H.source H.target ⟶ H.arrows)
    (hp : p = firstArrow H) (hq : q = secondArrow H) (hr : r = H.comp)
    (hcocycle : TransitionCocycle 𝒞 S hS (U := H.objects) (V := H.arrows)
      (a := H.target) (b := H.source) F α p q r) :
    groupoidPullbackTransition 𝒞 S hS H F α H.comp =
      groupoidTransitionComposite 𝒞 S hS H F α := by
  subst hp hq hr
  rw [groupoidPullbackTransition_eq_transitionReindex, groupoidTransitionComposite_eq]
  exact hcocycle (comp_comp_target H) (firstArrow_comp_source H) (comp_comp_source H)

/-- The unit condition of Stacks 0441 holds as soon as the unit law holds at some morphism of
the arrow space equal to the unit arrow of the groupoid. -/
theorem groupoidPullbackTransition_identityArrow_eq_pullbackTransport
    {Y : AlgebraicSpaces 𝒞 S hS} (H : GroupoidInAlgebraicSpaces 𝒞 S hS Y)
    (F : Modules.{u, u} 𝒞 S hS H.objects.1 H.objects.2)
    (α : (modulePullback 𝒞 S hS H.target).obj F ⟶ (modulePullback 𝒞 S hS H.source).obj F)
    (k : H.objects ⟶ H.arrows) (hk : identityArrow H = k)
    (hunit : TransitionUnit 𝒞 S hS (U := H.objects) (V := H.arrows)
      (a := H.target) (b := H.source) F α k) :
    groupoidPullbackTransition 𝒞 S hS H F α (identityArrow H) =
      pullbackTransport F
        ((identityArrow_comp_target H).trans (identityArrow_comp_source H).symm) := by
  subst hk
  exact unit_of_transitionUnit H F α hunit

end Reindex

/-! ### The laws of Stacks 0441 as instances of the abstract conditions -/

/-- The transition morphism of a quasi-coherent module on a groupoid in algebraic spaces
satisfies the abstract unit condition at the unit arrow. -/
theorem QuasicoherentModule.transitionUnit {A : AlgebraicSpaces 𝒞 S hS}
    (H : GroupoidInAlgebraicSpaces 𝒞 S hS A) (N : QuasicoherentModule 𝒞 S hS H) :
    TransitionUnit 𝒞 S hS (U := H.objects) (V := H.arrows) (a := H.target) (b := H.source)
      N.F.obj N.alpha (identityArrow H) :=
  fun _ =>
    (groupoidPullbackTransition_eq_transitionReindex 𝒞 S hS H N.F.obj N.alpha _).symm.trans
      N.unit

/-- The transition morphism of a quasi-coherent module on a groupoid in algebraic spaces
satisfies the abstract cocycle condition at the two projections of the space of composable
pairs of arrows and the composition. -/
theorem QuasicoherentModule.transitionCocycle {A : AlgebraicSpaces 𝒞 S hS}
    (H : GroupoidInAlgebraicSpaces 𝒞 S hS A) (N : QuasicoherentModule 𝒞 S hS H) :
    TransitionCocycle 𝒞 S hS (U := H.objects) (V := H.arrows) (a := H.target) (b := H.source)
      N.F.obj N.alpha (firstArrow H) (secondArrow H) H.comp :=
  fun _ _ _ =>
    ((groupoidPullbackTransition_eq_transitionReindex 𝒞 S hS H N.F.obj N.alpha _).symm.trans
      N.cocycle).trans (groupoidTransitionComposite_eq 𝒞 S hS H N.F.obj N.alpha)

/-! ### The comparison of Stacks 0445 -/

/-- The comparison of Stacks 0445 at a groupoid `H` in algebraic spaces: a functor from the
`G`-equivariant quasi-coherent `𝒪_X`-modules to the quasi-coherent modules on `H` which leaves
the underlying module, the transition morphism and the morphisms unchanged, and is fully
faithful and essentially surjective. -/
structure ActionGroupoidModulesComparison (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (A : ModObj G.obj.X X)
    (H : GroupoidInAlgebraicSpaces 𝒞 S hS ⟨B, hB⟩) where
  /-- The comparison functor. -/
  functor : EquivariantQuasicoherentModule (hB := hB) G X hX A ⥤ QuasicoherentModule 𝒞 S hS H
  /-- The comparison functor is fully faithful. -/
  fullyFaithful : functor.FullyFaithful
  /-- The comparison functor is essentially surjective. -/
  essSurj : functor.EssSurj
  /-- The comparison leaves the underlying quasi-coherent module unchanged. -/
  module_eq : ∀ M, HEq (functor.obj M).F M.F
  /-- The comparison leaves the transition morphism unchanged. -/
  transition_eq : ∀ M, HEq (functor.obj M).alpha M.alpha
  /-- The comparison leaves the morphisms unchanged. -/
  map_eq : ∀ {M N} (f : M ⟶ N), HEq (functor.map f).hom f.hom

/-- **The comparison functor of Stacks 0445 is an equivalence of categories.** -/
theorem ActionGroupoidModulesComparison.isEquivalence
    {G : GroupAlgebraicSpace 𝒞 S hS B hB} {X : Over B}
    {hX : IsAlgebraicSpace 𝒞 S hS X.left} {A : ModObj G.obj.X X}
    {H : GroupoidInAlgebraicSpaces 𝒞 S hS ⟨B, hB⟩}
    (C : ActionGroupoidModulesComparison (hB := hB) G X hX A H) :
    C.functor.IsEquivalence where
  faithful := C.fullyFaithful.faithful
  full := C.fullyFaithful.full
  essSurj := C.essSurj

/-- The comparison functor, read as an equivalence between the `G`-equivariant quasi-coherent
`𝒪_X`-modules of Stacks 043T and the quasi-coherent modules of Stacks 0441 on `H`. -/
noncomputable def ActionGroupoidModulesComparison.equivalence
    {G : GroupAlgebraicSpace 𝒞 S hS B hB} {X : Over B}
    {hX : IsAlgebraicSpace 𝒞 S hS X.left} {A : ModObj G.obj.X X}
    {H : GroupoidInAlgebraicSpaces 𝒞 S hS ⟨B, hB⟩}
    (C : ActionGroupoidModulesComparison (hB := hB) G X hX A H) :
    EquivariantQuasicoherentModule (hB := hB) G X hX A ≌ QuasicoherentModule 𝒞 S hS H :=
  letI := C.isEquivalence
  C.functor.asEquivalence

/-- The comparison of Stacks 0445 read off a presentation of the action groupoid: given a
bundle `AlgebraicGeometry.Space.ActionGroupoidConstruction` pinning the object and arrow spaces
and the five structure maps of a groupoid `H` to those of the action of Stacks 0444, the rule
`(ℱ, α) ↦ (ℱ, α)` is a fully faithful and essentially surjective functor from the
`G`-equivariant quasi-coherent `𝒪_X`-modules to the quasi-coherent modules on `H`. -/
def comparisonOfConstruction (G : GroupAlgebraicSpace 𝒞 S hS B hB) (X : Over B)
    (hX : IsAlgebraicSpace 𝒞 S hS X.left) (A : ModObj G.obj.X X)
    (D : @ActionGroupoidConstruction 𝒞 S hS ⟨B, hB⟩ G.obj.X X G.obj.grp A G.property hX) :
    ActionGroupoidModulesComparison (hB := hB) G X hX A D.groupoid := by
  letI : GrpObj G.obj.X := G.obj.grp
  letI : ModObj G.obj.X X := A
  obtain ⟨H, hO, hR, hOB, hRB, hs, ht, e, he₁, he₂, hc, hi, hι⟩ := D
  obtain ⟨O, R, ob, rb, s, t, sob, tob, c, cb, pg⟩ := H
  dsimp only at hO hR hOB hRB hs ht hc hi
  subst O R
  have hob : ob = ObjectProperty.homMk X.hom :=
    ObjectProperty.hom_ext _ (eq_of_heq hOB)
  have hrb : rb = ObjectProperty.homMk (G.obj.X ⊗ X).hom :=
    ObjectProperty.hom_ext _ (eq_of_heq hRB)
  have hss : s = projection (hB := hB) G X hX :=
    ObjectProperty.hom_ext _ (eq_of_heq hs)
  have htt : t = action (hB := hB) G X hX A :=
    ObjectProperty.hom_ext _ (eq_of_heq ht)
  subst ob rb s t
  refine
    { functor :=
        { obj := fun M => ⟨M.F, M.alpha, ?_, ?_⟩
          map := fun {M N} f => ⟨f.hom, ?_⟩
          map_id := fun M => rfl
          map_comp := fun f g => rfl }
      fullyFaithful :=
        { preimage := fun {M N} f => ⟨f.hom, ?_⟩
          map_preimage := fun f => rfl
          preimage_map := fun f => rfl }
      essSurj := ?_
      module_eq := fun M => HEq.rfl
      transition_eq := fun M => HEq.rfl
      map_eq := fun f => HEq.rfl }
  · dsimp only
    have hc' : c.hom = e.hom ≫ (Stacks.Groupoids.ActionGroupoid.composition G.obj.X X).left :=
      eq_of_heq hc
    let P : Over B := Over.mk (e.hom ≫ (pullback (snd G.obj.X X) γ[G.obj.X, X]).hom)
    have hP : IsAlgebraicSpace 𝒞 S hS P.left :=
      (AlgebraicSpaces.fiberProduct 𝒞 S hS (projection (hB := hB) G X hX)
        (action (hB := hB) G X hX A)).property
    let j : P ⟶ pullback (snd G.obj.X X) γ[G.obj.X, X] := Over.homMk e.hom rfl
    let p := j ≫ pullback.fst (snd G.obj.X X) γ[G.obj.X, X]
    let q := j ≫ pullback.snd (snd G.obj.X X) γ[G.obj.X, X]
    let r := j ≫ Stacks.Groupoids.ActionGroupoid.composition G.obj.X X
    refine groupoidPullbackTransition_comp_eq_groupoidTransitionComposite 𝒞 S hS _ _ _
      (asSpaceHom hP (actionSpace (hB := hB) G X hX).property p)
      (asSpaceHom hP (actionSpace (hB := hB) G X hX).property q)
      (asSpaceHom hP (actionSpace (hB := hB) G X hX).property r)
      (ObjectProperty.hom_ext _ he₁)
      (ObjectProperty.hom_ext _ he₂)
      (ObjectProperty.hom_ext _ hc'.symm) ?_
    intro ht' hm' hs'
    exact M.cocycle hP p q r
      (by simp only [p, q, j, Category.assoc, pullback.condition])
      (by simp only [r, p, q, j, Stacks.Groupoids.ActionGroupoid.composition, Category.assoc,
        lift_fst, comp_lift_assoc])
      ht' hs'
  · dsimp only
    refine groupoidPullbackTransition_identityArrow_eq_pullbackTransport 𝒞 S hS _ _ _
      (ObjectProperty.homMk (Stacks.Groupoids.ActionGroupoid.identity G.obj.X X).left) ?_ ?_
    · apply ObjectProperty.hom_ext
      ext T x
      exact (identityArrow_hom_app _ T x).trans (congrFun (eq_of_heq (hi T)) x)
    · intro h'
      refine M.unit hX (Stacks.Groupoids.ActionGroupoid.identity G.obj.X X)
        (by simp only [Stacks.Groupoids.ActionGroupoid.identity, lift_fst]) ?_
  · convert f.comm using 1
  · convert f.comm using 1
  · refine ⟨fun N => ⟨{ F := N.F, alpha := N.alpha, cocycle := ?_, unit := ?_ }, ⟨Iso.refl _⟩⟩⟩
    · intro T hT p q r hcomp hmul htarget hsource
      have hmid : asSpaceHom hT (actionSpace (hB := hB) G X hX).property p ≫
          projection (hB := hB) G X hX =
            asSpaceHom hT (actionSpace (hB := hB) G X hX).property q ≫
              action (hB := hB) G X hX A :=
        ObjectProperty.hom_ext _ (congrArg Over.Hom.left hcomp)
      have hqs : r ≫ snd G.obj.X X = q ≫ snd G.obj.X X :=
        Over.OverMorphism.ext (congrArg (fun m => m.hom) hsource)
      have hc' : c.hom = e.hom ≫ (Stacks.Groupoids.ActionGroupoid.composition G.obj.X X).left :=
        eq_of_heq hc
      have hv :
          pullback.lift p q hcomp ≫ Stacks.Groupoids.ActionGroupoid.composition G.obj.X X = r := by
        apply CartesianMonoidalCategory.hom_ext
        · rw [hmul, Category.assoc, Stacks.Groupoids.ActionGroupoid.composition_fst,
            ← Category.assoc, comp_lift]
          simp only [← Category.assoc, pullback.lift_fst, pullback.lift_snd]
        · rw [hqs, Category.assoc, Stacks.Groupoids.ActionGroupoid.composition_source,
            ← Category.assoc, pullback.lift_snd]
      have hef : e.inv ≫ pullback.fst (projection (hB := hB) G X hX).hom
            (action (hB := hB) G X hX A).hom =
          (pullback.fst (snd G.obj.X X) γ[G.obj.X, X]).left :=
        (congrArg (e.inv ≫ ·) he₁.symm).trans (e.inv_hom_id_assoc _)
      have hes : e.inv ≫ pullback.snd (projection (hB := hB) G X hX).hom
            (action (hB := hB) G X hX A).hom =
          (pullback.snd (snd G.obj.X X) γ[G.obj.X, X]).left :=
        (congrArg (e.inv ≫ ·) he₂.symm).trans (e.inv_hom_id_assoc _)
      refine TransitionCocycle.comp 𝒞 S hS N.F.obj N.alpha (comp_comp_target _)
        (firstArrow_comp_source _) (comp_comp_source _)
        (QuasicoherentModule.transitionCocycle _ N)
        (ObjectProperty.homMk ((pullback.lift p q hcomp).left ≫ e.inv)) ?_ ?_ ?_
        htarget hmid hsource
      · exact ObjectProperty.hom_ext _ <| (Category.assoc _ _ _).trans
          ((congrArg ((pullback.lift p q hcomp).left ≫ ·) hef).trans
            (congrArg Over.Hom.left (pullback.lift_fst p q hcomp)))
      · exact ObjectProperty.hom_ext _ <| (Category.assoc _ _ _).trans
          ((congrArg ((pullback.lift p q hcomp).left ≫ ·) hes).trans
            (congrArg Over.Hom.left (pullback.lift_snd p q hcomp)))
      · exact ObjectProperty.hom_ext _ <|
          (congrArg (((pullback.lift p q hcomp).left ≫ e.inv) ≫ ·) hc').trans
          ((Category.assoc _ _ _).trans
            ((congrArg ((pullback.lift p q hcomp).left ≫ ·)
              (e.inv_hom_id_assoc
                (Stacks.Groupoids.ActionGroupoid.composition G.obj.X X).left)).trans
              (congrArg Over.Hom.left hv)))
    · intro T hT f hfst h
      have key :
          (f ≫ snd G.obj.X X) ≫ Stacks.Groupoids.ActionGroupoid.identity G.obj.X X = f := by
        apply CartesianMonoidalCategory.hom_ext
        · rw [hfst, Category.assoc, Stacks.Groupoids.ActionGroupoid.identity, lift_fst,
            ← Category.assoc, comp_toUnit]
        · rw [Category.assoc, Stacks.Groupoids.ActionGroupoid.identity, lift_snd, Category.comp_id]
      refine TransitionUnit.comp 𝒞 S hS N.F.obj N.alpha
        ((identityArrow_comp_target _).trans (identityArrow_comp_source _).symm)
        (QuasicoherentModule.transitionUnit _ N) (asSpaceHom hT hX (f ≫ snd G.obj.X X)) ?_ h
      refine Eq.trans ?_
        (congrArg (asSpaceHom hT (actionSpace (hB := hB) G X hX).property) key)
      apply ObjectProperty.hom_ext
      ext T' x
      exact (identityArrow_hom_app _ T' _).trans (congrFun (eq_of_heq (hi T')) _)

/-- The rule `(ℱ, α) ↦ (ℱ, α)` is a fully faithful and essentially surjective functor from the
`G`-equivariant quasi-coherent `𝒪_X`-modules of Stacks 043T to the quasi-coherent modules of
Stacks 0441 on the action groupoid of Stacks 0444, leaving the underlying quasi-coherent module,
the transition morphism and the morphisms unchanged. -/
@[stacks 0445]
noncomputable def actionGroupoidModulesComparison (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (X : Over B) (hX : IsAlgebraicSpace 𝒞 S hS X.left) (A : ModObj G.obj.X X) :
    ActionGroupoidModulesComparison (hB := hB) G X hX A (actionGroupoid G X hX A) :=
  letI : GrpObj G.obj.X := G.obj.grp
  letI : ModObj G.obj.X X := A
  comparisonOfConstruction G X hX A (groupoidOfAction ⟨B, hB⟩ G.obj.X X G.property hX)

/-- The rule `(ℱ, α) ↦ (ℱ, α)` is an equivalence between the category of `G`-equivariant
quasi-coherent `𝒪_X`-modules of Stacks 043T and the category of quasi-coherent modules of
Stacks 0441 on the action groupoid of Stacks 0444. -/
@[stacks 0445 "the equivalence of categories"]
noncomputable def actionGroupoidModulesEquivalence (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (X : Over B) (hX : IsAlgebraicSpace 𝒞 S hS X.left) (A : ModObj G.obj.X X) :
    EquivariantQuasicoherentModule (hB := hB) G X hX A ≌
      QuasicoherentModule 𝒞 S hS (actionGroupoid G X hX A) :=
  (actionGroupoidModulesComparison G X hX A).equivalence

end AlgebraicGeometry.Space

end
