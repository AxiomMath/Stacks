module

public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.FiberedCategory.CompFibered
public import StacksFrontier.CategoryTheory.Sites.Localization.StacksAndLocalization
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Slice
public import StacksFrontier.CategoryTheory.Sites.CocontinuousRightAdjointMorphismOfSites
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.RingedToposOfAFibredCategory

/-!
# A section of the localized projection of a fibred category

Let `p : C ⥤ D` be a fibred category over the underlying site of a ringed site `(D, O_D)`,
with `C` carrying the inherited topology, and let `U` be an object of `C`. The projection
`Over.post p : C/U ⟶ D/p(U)` of the localized sites induces a morphism of topoi, and that
morphism has a section: the functor sending `V ⟶ p(U)` to a chosen strongly cartesian lift,
which is continuous and cocontinuous and right adjoint to `Over.post p`, so its direct image
is the inverse image of the section and the composite is the identity.

## Main definitions

* `Stacks.Sites.FibredCategory.LocalizedProjectionSection`: the localized projection together
  with its section, each specified by the canonical (co)continuous functor it comes from, and
  with the two section identities.

## Main results

* `Stacks.Sites.FibredCategory.localizedProjectionSection`: that datum exists for every object
  of the total category.

## Implementation notes

The localized projection is pinned down by the continuous and cocontinuous functors of
`Over.post p`, so that an arbitrary morphism of topoi cannot serve as the projection. The
section is likewise pinned down by a functor of slice sites whose structure arrows are
strongly cartesian lifts, together with its comparison to the identity on the base slice and
both of its induced sheaf functors; compatibility with morphisms of fibred categories can
therefore be checked on cartesian lifts. The comparison to the identity is recorded as *being*
the counit of the adjunction: the adjunction and the isomorphism are otherwise unrelated data,
so composing the isomorphism with any automorphism of the identity functor would give another
legal value of the structure, and nothing about the counit could then be computed.
Equality of morphisms of topoi is expressed by natural isomorphisms of both functors, since
the adjunction datum of a morphism of topoi is not canonical.

The chosen cartesian lifts come from `CategoryTheory.Functor.chosenPullbacks`; the identity
`CategoryTheory.Functor.inheritedTopology_overPost` is what lets the slice projection inherit the
(co)continuity of `p` itself.

`Over.post`, `chosenPullbacks` and `cartesianLiftFunctor` are plain `def`s, so a morphism of
slice categories and the chosen lift it is compared against have types that agree only after
those `def`s are unfolded. Several goals below — in particular the `IsHomLift` side conditions
of the adjunction, where `((Over.post p).obj X).left` has to be recognised as `p.obj X.left`,
and the `eqToHom` composites of `cartesianLiftFunctor_base`, whose intermediate object is
`((cartesianLiftFunctor s U).obj V).left` on one side and the chosen pullback on the other —
are therefore not type-correct at `implicit` transparency, and instance search and `simp`
refuse them. Making these three `def`s, together with `Functor.Fiber` and
`Functor.Fiber.fiberInclusion`, locally `implicit_reducible` removes the obstruction.

## References

* [Stacks Project, Tag 08P9](https://stacks.math.columbia.edu/tag/08P9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

namespace Stacks.Sites.FibredCategory

-- `Fiber`, `fiberInclusion`, `chosenPullbacks` and `Over.post` are plain `def`s, so goals about
-- an object of a fibre, about a chosen pullback, or about the slice projection are not
-- type-correct at `implicit` transparency; see the implementation notes.
attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion
  Functor.chosenPullbacks Over.post

universe uD vD uC vC w

variable (s : FibredCategorySituation.{uD, vD, uC, vC, w}) (U : s.C)

private noncomputable def cartesianLiftFunctor : Over (s.p.obj U) ⥤ Over U := by
  let c := Functor.chosenPullbacks s.p
  let x : s.p.Fiber (s.p.obj U) := ⟨U, rfl⟩
  refine
    { obj := fun V => Over.mk (c.map V.hom x)
      map := fun {V W} f =>
        Over.homMk
          (IsStronglyCartesian.map s.p W.hom (c.map W.hom x)
            (show V.hom = f.left ≫ W.hom from (Over.w f).symm)
            (c.map V.hom x)) ?_
      map_id := ?_
      map_comp := ?_ }
  · exact IsStronglyCartesian.fac s.p W.hom (c.map W.hom x)
      (show V.hom = f.left ≫ W.hom from (Over.w f).symm) (c.map V.hom x)
  · intro V
    have : s.p.IsStronglyCartesian V.hom (c.map V.hom x) := c.isStronglyCartesian V.hom x
    apply Over.OverMorphism.ext
    simp only [IsStronglyCartesian.map_self]
    rfl
  · intro V W Z f g
    have : s.p.IsStronglyCartesian W.hom (c.map W.hom x) := c.isStronglyCartesian W.hom x
    have : s.p.IsStronglyCartesian V.hom (c.map V.hom x) := c.isStronglyCartesian V.hom x
    exact Over.OverMorphism.ext (IsStronglyCartesian.map_comp_map s.p Z.hom (c.map Z.hom x)
      (show W.hom = g.left ≫ Z.hom from (Over.w g).symm)
      (show V.hom = f.left ≫ W.hom from (Over.w f).symm)
      (c.map W.hom x) (c.map V.hom x)).symm

-- The structure arrow of a value of `cartesianLiftFunctor` is a chosen pullback only after
-- `cartesianLiftFunctor` is unfolded, which `simp` and instance search will not do.
attribute [local implicit_reducible] cartesianLiftFunctor

/-- The structure arrow of the lift of `V` is the chosen pullback of `V.hom` along `U`. -/
private lemma cartesianLiftFunctor_obj_hom (V : Over (s.p.obj U)) :
    ((cartesianLiftFunctor s U).obj V).hom =
      (Functor.chosenPullbacks s.p).map V.hom ⟨U, rfl⟩ := rfl

/-- The structure arrow of the lift of `V` is strongly cartesian over `V.hom`: it is a chosen
pullback, and those are strongly cartesian by construction. This is the hypothesis every
universal property used below needs, so it is supplied as an instance. -/
private instance cartesianLiftFunctor_isStronglyCartesian (V : Over (s.p.obj U)) :
    s.p.IsStronglyCartesian V.hom ((cartesianLiftFunctor s U).obj V).hom := by
  rw [cartesianLiftFunctor_obj_hom]
  exact (Functor.chosenPullbacks s.p).isStronglyCartesian V.hom ⟨U, rfl⟩

private lemma cartesianLiftFunctor_isStronglyCartesian_map_self (V : Over (s.p.obj U)) :
    s.p.IsStronglyCartesian (s.p.map ((cartesianLiftFunctor s U).obj V).hom)
      ((cartesianLiftFunctor s U).obj V).hom :=
  Functor.isStronglyCartesian_map_self s.p V.hom _

private noncomputable def cartesianLiftFunctor_base :
    cartesianLiftFunctor s U ⋙ (Over.post s.p : Over U ⥤ Over (s.p.obj U)) ≅
      𝟭 (Over (s.p.obj U)) := by
  let c := Functor.chosenPullbacks s.p
  let x : s.p.Fiber (s.p.obj U) := ⟨U, rfl⟩
  refine NatIso.ofComponents (fun V => Over.isoMk (eqToIso (c.obj V.hom x).2) ?_) ?_
  · change eqToHom (c.obj V.hom x).2 ≫ V.hom = s.p.map (c.map V.hom x)
    simpa using (IsHomLift.fac' s.p V.hom (c.map V.hom x)).symm
  · intro V W f
    apply Over.OverMorphism.ext
    change s.p.map ((cartesianLiftFunctor s U).map f).left ≫
      (eqToIso (c.obj W.hom x).2).hom =
        (eqToIso (c.obj V.hom x).2).hom ≫ f.left
    dsimp [cartesianLiftFunctor]
    simp only [Over.homMk_left]
    rw [IsHomLift.fac' s.p f.left _]
    simp

private lemma map_left_comp_cartesianLiftFunctor_base {X : Over U} {V : Over (s.p.obj U)}
    (g : X ⟶ (cartesianLiftFunctor s U).obj V) :
    (s.p.map g.left ≫ ((cartesianLiftFunctor_base s U).hom.app V).left) ≫ V.hom =
      s.p.map X.hom := by
  calc
    _ = s.p.map g.left ≫ (((cartesianLiftFunctor_base s U).hom.app V).left ≫ V.hom) :=
      Category.assoc _ _ _
    _ = s.p.map g.left ≫ (Over.post s.p |>.obj ((cartesianLiftFunctor s U).obj V)).hom := by
      congr 1
      exact Over.w ((cartesianLiftFunctor_base s U).hom.app V)
    _ = s.p.map (g.left ≫ ((cartesianLiftFunctor s U).obj V).hom) := by
      show s.p.map g.left ≫ s.p.map ((cartesianLiftFunctor s U).obj V).hom = _
      rw [← s.p.map_comp]
    _ = s.p.map X.hom := by rw [Over.w g]

/-- The morphism `X ⟶ cartesianLiftFunctor V` induced by `f : p(X) ⟶ V` through the universal
property of the strongly cartesian structure arrow of the lift of `V`. -/
private noncomputable def cartesianLiftFunctor_lift {X : Over U} {V : Over (s.p.obj U)}
    (f : (Over.post s.p).obj X ⟶ V) : X ⟶ (cartesianLiftFunctor s U).obj V :=
  Over.homMk
    (IsStronglyCartesian.map s.p V.hom ((cartesianLiftFunctor s U).obj V).hom
      (show s.p.map X.hom = f.left ≫ V.hom from (Over.w f).symm) X.hom)
    (IsStronglyCartesian.fac s.p V.hom ((cartesianLiftFunctor s U).obj V).hom
      (show s.p.map X.hom = f.left ≫ V.hom from (Over.w f).symm) X.hom)

private instance cartesianLiftFunctor_lift_isHomLift {X : Over U} {V : Over (s.p.obj U)}
    (f : (Over.post s.p).obj X ⟶ V) :
    s.p.IsHomLift f.left (cartesianLiftFunctor_lift s U f).left :=
  inferInstanceAs (s.p.IsHomLift f.left
    (IsStronglyCartesian.map s.p V.hom ((cartesianLiftFunctor s U).obj V).hom
      (show s.p.map X.hom = f.left ≫ V.hom from (Over.w f).symm) X.hom))

private lemma cartesianLiftFunctor_lift_comp {X : Over U} {V V' : Over (s.p.obj U)}
    (f : (Over.post s.p).obj X ⟶ V) (g : V ⟶ V') :
    cartesianLiftFunctor_lift s U (f ≫ g) =
      cartesianLiftFunctor_lift s U f ≫ (cartesianLiftFunctor s U).map g := by
  apply Over.OverMorphism.ext
  let c := Functor.chosenPullbacks s.p
  let x : s.p.Fiber (s.p.obj U) := ⟨U, rfl⟩
  let l := (cartesianLiftFunctor_lift s U f).left
  have hfac : s.p.map X.hom = (f.left ≫ g.left) ≫ V'.hom := by
    rw [Category.assoc, Over.w g]
    exact (Over.w f).symm
  have : s.p.IsHomLift g.left ((cartesianLiftFunctor s U).map g).left := by
    dsimp [cartesianLiftFunctor]
    show s.p.IsHomLift g.left
      (IsStronglyCartesian.map s.p V'.hom (c.map V'.hom x)
        (show V.hom = g.left ≫ V'.hom from (Over.w g).symm) (c.map V.hom x))
    infer_instance
  have hcomp : (l ≫ ((cartesianLiftFunctor s U).map g).left) ≫
      ((cartesianLiftFunctor s U).obj V').hom = X.hom := by
    rw [Category.assoc, Over.w ((cartesianLiftFunctor s U).map g)]
    exact Over.w (cartesianLiftFunctor_lift s U f)
  exact (IsStronglyCartesian.map_uniq s.p V'.hom ((cartesianLiftFunctor s U).obj V').hom
    hfac X.hom (l ≫ ((cartesianLiftFunctor s U).map g).left) hcomp).symm

private noncomputable def cartesianLiftFunctor_adj :
    (Over.post s.p : Over U ⥤ Over (s.p.obj U)) ⊣ cartesianLiftFunctor s U := by
  let c := Functor.chosenPullbacks s.p
  let x : s.p.Fiber (s.p.obj U) := ⟨U, rfl⟩
  let e := cartesianLiftFunctor_base s U
  refine Adjunction.mkOfHomEquiv
    { homEquiv := fun X V =>
        { toFun := cartesianLiftFunctor_lift s U
          invFun := fun g =>
            Over.homMk (s.p.map g.left ≫ (e.hom.app V).left)
              (map_left_comp_cartesianLiftFunctor_base s U g)
          left_inv := by
            intro f
            apply Over.OverMorphism.ext
            dsimp
            simp only [Over.homMk_left]
            rw [IsHomLift.fac' s.p f.left (cartesianLiftFunctor_lift s U f).left]
            simp [e, cartesianLiftFunctor_base]
          right_inv := by
            intro g
            apply Over.OverMorphism.ext
            dsimp
            let base : s.p.obj X.left ⟶ V.left :=
              s.p.map g.left ≫ (e.hom.app V).left
            have hgLift : s.p.IsHomLift base g.left := by
              apply IsHomLift.of_fac' s.p base g.left rfl (c.obj V.hom x).2
              simp [base, e, cartesianLiftFunctor_base]
            have hfac : s.p.map X.hom = base ≫ V.hom :=
              (map_left_comp_cartesianLiftFunctor_base s U g).symm
            exact (IsStronglyCartesian.map_uniq s.p V.hom
              (cartesianLiftFunctor s U |>.obj V).hom hfac X.hom g.left (Over.w g)).symm }
      homEquiv_naturality_left_symm := by
        intro X' X V f g
        apply Over.OverMorphism.ext
        dsimp
        simp [s.p.map_comp, Category.assoc]
      homEquiv_naturality_right := fun f g => cartesianLiftFunctor_lift_comp s U f g }

/-- The counit of the adjunction is the comparison isomorphism on the base slice.

Both components at `V` are morphisms out of `p` of the chosen lift of `V.hom`, and the counit's
is `p` of the identity followed by the comparison, so the two agree. -/
private lemma cartesianLiftFunctor_adj_counit :
    (cartesianLiftFunctor_adj s U).counit = (cartesianLiftFunctor_base s U).hom := by
  ext V
  show s.p.map (𝟙 _) ≫ _ = _
  simp

private lemma projectionSliceCocontinuous :
    (Over.post s.p : Over U ⥤ Over (s.p.obj U)).IsCocontinuous
      (s.topology.over U) (s.base.J.over (s.p.obj U)) := by
  have : s.p.IsCocontinuous s.topology s.base.J := FibredCategorySituation.isCocontinuous s
  infer_instance

private lemma cartesianSectionContinuous :
    cartesianLiftFunctor s U |>.IsContinuous
      (s.base.J.over (s.p.obj U)) (s.topology.over U) := by
  have := projectionSliceCocontinuous s U
  exact (cartesianLiftFunctor_adj s U).isContinuous_of_isCocontinuous
    (s.topology.over U) (s.base.J.over (s.p.obj U))

private lemma projectionSliceContinuous :
    (Over.post s.p : Over U ⥤ Over (s.p.obj U)).IsContinuous
      (s.topology.over U) (s.base.J.over (s.p.obj U)) := by
  let t : FibredCategorySituation.{max uD vD, vD, max uC vC, vC, w} :=
    { base := { C := Over (s.p.obj U), J := s.base.J.over (s.p.obj U),
                O := s.base.O.over (s.p.obj U) }
      C := Over U
      p := Over.post s.p
      isFibered := Functor.isFibered_overPost s.p U }
  have h := FibredCategorySituation.isContinuous t
  change (Over.post s.p : Over U ⥤ Over (s.p.obj U)).IsContinuous
    ((Over.post s.p).inheritedTopology (s.base.J.over (s.p.obj U))) _ at h
  rwa [Functor.inheritedTopology_overPost s.p s.base.J U] at h

private lemma coverage_contains_presieve {C : Type*} [Category* C] (K : Coverage C)
    [K.toPrecoverage.HasIsos] [K.toPrecoverage.IsStableUnderComposition]
    {X : C} {S : Sieve X} (hS : S ∈ K.toPrecoverage.toGrothendieck X) :
    ∃ R ∈ K.toPrecoverage X, R ≤ S := by
  change K.toPrecoverage.Saturate X S at hS
  rw [← K.saturate_iff_saturate_toPrecoverage] at hS
  induction hS with
  | of X R hR => exact ⟨R, hR, Sieve.le_generate R⟩
  | top X => exact ⟨Presieve.singleton (𝟙 X), Precoverage.mem_coverings_of_isIso _, by simp⟩
  | transitive X S T hS hT ih ih' =>
    obtain ⟨R, hR, hle⟩ := ih
    rw [Precoverage.mem_iff_exists_zeroHypercover] at hR
    obtain ⟨E, rfl⟩ := hR
    have h (i : E.I₀) : ∃ F : K.toPrecoverage.ZeroHypercover (E.X i),
        F.presieve₀ ≤ (T.pullback (E.f i)).arrows := by
      obtain ⟨R', hR', hle'⟩ := ih' (hle _ _ ⟨i⟩)
      rw [Precoverage.mem_iff_exists_zeroHypercover] at hR'
      obtain ⟨F, rfl⟩ := hR'
      exact ⟨F, hle'⟩
    choose F hF using h
    refine ⟨(E.bind F).presieve₀, (E.bind F).mem₀, ?_⟩
    rw [Presieve.ofArrows_le_iff]
    intro i
    exact hF _ _ _ ⟨i.snd⟩

private lemma cartesianLiftFunctor_unit_isIso (X : Over U)
    [s.p.IsStronglyCartesian (s.p.map X.hom) X.hom] :
    IsIso ((cartesianLiftFunctor_adj s U).unit.app X) := by
  let Y := (cartesianLiftFunctor s U).obj ((Over.post s.p).obj X)
  have hc : s.p.IsStronglyCartesian (s.p.map X.hom) Y.hom :=
    (chosenPullbacks s.p).isStronglyCartesian (s.p.map X.hom) ⟨U, rfl⟩
  let e : X ≅ Y := Over.isoMk
    (IsCartesian.domainUniqueUpToIso s.p (s.p.map X.hom) Y.hom X.hom)
    (IsCartesian.fac s.p (s.p.map X.hom) Y.hom X.hom)
  have : s.p.IsHomLift (𝟙 (s.p.obj X.left)) e.hom.left := by
    show s.p.IsHomLift _ (IsCartesian.map s.p (s.p.map X.hom) Y.hom X.hom)
    infer_instance
  have he : (cartesianLiftFunctor_adj s U).unit.app X = e.hom := by
    apply Over.OverMorphism.ext
    show IsStronglyCartesian.map s.p (s.p.map X.hom) Y.hom
      (g := 𝟙 _) (f' := s.p.map X.hom) (Category.id_comp _).symm X.hom = _
    exact (IsStronglyCartesian.map_uniq s.p (s.p.map X.hom) Y.hom
      (g := 𝟙 _) (f' := s.p.map X.hom) (Category.id_comp _).symm X.hom
      e.hom.left (Over.w e.hom)).symm
  rw [he]
  infer_instance

private lemma isStronglyCartesian_hom_of_isStronglyCartesian_left {X : Over U}
    {V : Over (s.p.obj U)} (b : X ⟶ (cartesianLiftFunctor s U).obj V)
    [s.p.IsStronglyCartesian (s.p.map b.left) b.left] :
    s.p.IsStronglyCartesian (s.p.map X.hom) X.hom := by
  have := cartesianLiftFunctor_isStronglyCartesian_map_self s U V
  have hcomp : s.p.IsStronglyCartesian
      (s.p.map b.left ≫ s.p.map ((cartesianLiftFunctor s U).obj V).hom)
      (b.left ≫ ((cartesianLiftFunctor s U).obj V).hom) := inferInstance
  rwa [← s.p.map_comp,
    show b.left ≫ ((cartesianLiftFunctor s U).obj V).hom = X.hom from Over.w b] at hcomp

private lemma cartesianSectionCocontinuous :
    (cartesianLiftFunctor s U).IsCocontinuous
      (s.base.J.over (s.p.obj U)) (s.topology.over U) := by
  let q : Over U ⥤ Over (s.p.obj U) := Over.post s.p
  let v := cartesianLiftFunctor s U
  let adj := cartesianLiftFunctor_adj s U
  have : q.IsFibered := Functor.isFibered_overPost s.p U
  constructor
  intro V S hS
  rw [← Functor.inheritedTopology_overPost s.p s.base.J U] at hS
  have : (Functor.inheritedCoverage q (s.base.J.over (s.p.obj U))).toPrecoverage.HasIsos :=
    inferInstanceAs (q.inheritedPrecoverage (s.base.J.over (s.p.obj U)).toPrecoverage).HasIsos
  have : (Functor.inheritedCoverage q
      (s.base.J.over (s.p.obj U))).toPrecoverage.IsStableUnderComposition :=
    inferInstanceAs
      (q.inheritedPrecoverage (s.base.J.over (s.p.obj U)).toPrecoverage).IsStableUnderComposition
  obtain ⟨R, hR, hRS⟩ := coverage_contains_presieve
    (Functor.inheritedCoverage q (s.base.J.over (s.p.obj U))) hS
  have : IsIso (adj.counit.app V) := by
    rw [NatTrans.congr_app (cartesianLiftFunctor_adj_counit s U) V]
    infer_instance
  apply (s.base.J.over (s.p.obj U)).superset_covering _
    ((s.base.J.over (s.p.obj U)).pullback_stable (inv (adj.counit.app V)) hR.2)
  intro W f hf
  rcases hf with ⟨Z, a, b, hb, hab⟩
  rcases hb with ⟨hb⟩
  rename_i X b
  have hb' : s.p.IsStronglyCartesian (s.p.map b.left) b.left := by
    apply (Functor.isStronglyCartesian_overForget_comp_iff s.p U b).1
    have h := (isStronglyCartesian_comp_forget_iff q b).1 (hR.1 b hb)
    simpa only [q, Over.post_forget_eq_forget_comp] using h
  have := isStronglyCartesian_hom_of_isStronglyCartesian_left s U b
  have := cartesianLiftFunctor_unit_isIso s U X
  have hfactor : v.map f = v.map a ≫ inv (adj.unit.app X) ≫ b := by
    have heq : f = a ≫ q.map b ≫ adj.counit.app V := by
      simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using
        (congrArg (fun k => k ≫ adj.counit.app V) hab).symm
    rw [heq, v.map_comp, v.map_comp]
    have hn := adj.unit.naturality b
    dsimp at hn
    rw [← IsIso.inv_comp_eq] at hn
    rw [← hn]
    simp only [Category.assoc]
    rw [show adj.unit.app (v.obj V) ≫ v.map (adj.counit.app V) = 𝟙 _ from
      adj.right_triangle_components V]
    exact congrArg (fun k => v.map a ≫ inv (adj.unit.app X) ≫ k) (Category.comp_id b)
  show S (v.map f)
  rw [hfactor]
  simpa only [Category.assoc] using
    S.downward_closed (hRS _ _ hb) (v.map a ≫ inv (adj.unit.app X))

/-- The data specifying the section of the projection localized at `U`. -/
public structure LocalizedProjectionSection where
  /-- The slice projection `Over.post p : C/U ⥤ D/p(U)` is continuous. -/
  isContinuous : (Over.post s.p : Over U ⥤ Over (s.p.obj U)).IsContinuous
    (s.topology.over U) (s.base.J.over (s.p.obj U))
  /-- The slice projection `Over.post p : C/U ⥤ D/p(U)` is cocontinuous. -/
  isCocontinuous : (Over.post s.p : Over U ⥤ Over (s.p.obj U)).IsCocontinuous
    (s.topology.over U) (s.base.J.over (s.p.obj U))
  /-- The morphism of topoi from `Sh(C/U)` to `Sh(D/p(U))` induced by the localized projection. -/
  projection : MorphismOfTopoi
    (Sheaf (s.topology.over U) (Type (max w uD vD uC vC)))
    (Sheaf (s.base.J.over (s.p.obj U)) (Type (max w uD vD uC vC)))
  /-- The inverse image of `projection` is the pushforward along the continuous functor
  `Over.post p`. -/
  projection_inverseImage :
    letI : (Over.post s.p : Over U ⥤ Over (s.p.obj U)).IsContinuous
      (s.topology.over U) (s.base.J.over (s.p.obj U)) := isContinuous
    projection.inverseImage =
      (Over.post s.p : Over U ⥤ Over (s.p.obj U)).sheafPushforwardContinuous
        (Type (max w uD vD uC vC)) (s.topology.over U) (s.base.J.over (s.p.obj U))
  /-- The direct image of `projection` is the pushforward along the cocontinuous functor
  `Over.post p`. -/
  projection_pushforward :
    letI : (Over.post s.p : Over U ⥤ Over (s.p.obj U)).IsCocontinuous
      (s.topology.over U) (s.base.J.over (s.p.obj U)) := isCocontinuous
    projection.pushforward =
      (Over.post s.p : Over U ⥤ Over (s.p.obj U)).sheafPushforwardCocontinuous
        (Type (max w uD vD uC vC)) (s.topology.over U) (s.base.J.over (s.p.obj U))
  /-- The section, a morphism of topoi from `Sh(D/p(U))` to `Sh(C/U)`. -/
  rightSection : MorphismOfTopoi
    (Sheaf (s.base.J.over (s.p.obj U)) (Type (max w uD vD uC vC)))
    (Sheaf (s.topology.over U) (Type (max w uD vD uC vC)))
  /-- The functor `D/p(U) ⥤ C/U` sending `V ⟶ p(U)` to a strongly cartesian lift of it. -/
  cartesianSectionFunctor : Over (s.p.obj U) ⥤ Over U
  /-- The composite of `cartesianSectionFunctor` with `Over.post p` is isomorphic to the
  identity. -/
  cartesianSection_base :
    cartesianSectionFunctor ⋙ (Over.post s.p : Over U ⥤ Over (s.p.obj U)) ≅
      𝟭 (Over (s.p.obj U))
  /-- `Over.post p` is left adjoint to `cartesianSectionFunctor`. -/
  cartesianSection_adjunction :
    (Over.post s.p : Over U ⥤ Over (s.p.obj U)) ⊣ cartesianSectionFunctor
  /-- The counit of `cartesianSection_adjunction` is the isomorphism `cartesianSection_base`. -/
  cartesianSection_counit :
    cartesianSection_adjunction.counit = cartesianSection_base.hom
  /-- The structure arrow of `cartesianSectionFunctor.obj V` is strongly cartesian. -/
  cartesianSection_isCartesian (V : Over (s.p.obj U)) :
    s.p.IsStronglyCartesian
      (s.p.map ((cartesianSectionFunctor.obj V).hom))
      ((cartesianSectionFunctor.obj V).hom)
  /-- `cartesianSectionFunctor` is continuous. -/
  cartesianSection_isContinuous : cartesianSectionFunctor.IsContinuous
    (s.base.J.over (s.p.obj U)) (s.topology.over U)
  /-- `cartesianSectionFunctor` is cocontinuous. -/
  cartesianSection_isCocontinuous : cartesianSectionFunctor.IsCocontinuous
    (s.base.J.over (s.p.obj U)) (s.topology.over U)
  /-- The inverse image of `rightSection` is isomorphic to the pushforward along the continuous
  functor `cartesianSectionFunctor`. -/
  rightSection_inverseImage_cartesian :
    letI : cartesianSectionFunctor.IsContinuous
      (s.base.J.over (s.p.obj U)) (s.topology.over U) := cartesianSection_isContinuous
    rightSection.inverseImage ≅
      cartesianSectionFunctor.sheafPushforwardContinuous
        (Type (max w uD vD uC vC)) (s.base.J.over (s.p.obj U)) (s.topology.over U)
  /-- The direct image of `rightSection` is isomorphic to the pushforward along the
  cocontinuous functor `cartesianSectionFunctor`. -/
  rightSection_pushforward_cartesian :
    letI : cartesianSectionFunctor.IsCocontinuous
      (s.base.J.over (s.p.obj U)) (s.topology.over U) := cartesianSection_isCocontinuous
    rightSection.pushforward ≅
      cartesianSectionFunctor.sheafPushforwardCocontinuous
        (Type (max w uD vD uC vC)) (s.base.J.over (s.p.obj U)) (s.topology.over U)
  /-- The inverse image of `rightSection` is the direct image of `projection`. -/
  rightSection_inverseImage : rightSection.inverseImage = projection.pushforward
  /-- The inverse image of `projection.comp rightSection` is isomorphic to the identity. -/
  rightSection_rightInverse_inverseImage :
    (projection.comp rightSection).inverseImage ≅
      𝟭 (Sheaf (s.base.J.over (s.p.obj U)) (Type (max w uD vD uC vC)))
  /-- The direct image of `projection.comp rightSection` is isomorphic to the identity. -/
  rightSection_rightInverse_pushforward :
    (projection.comp rightSection).pushforward ≅
      𝟭 (Sheaf (s.base.J.over (s.p.obj U)) (Type (max w uD vD uC vC)))

private theorem nonempty_localizedProjectionSection :
    Nonempty (LocalizedProjectionSection s U) := by
  let A := Type (max w uD vD uC vC)
  let J := s.topology.over U
  let K := s.base.J.over (s.p.obj U)
  let q : Over U ⥤ Over (s.p.obj U) := Over.post s.p
  let v := cartesianLiftFunctor s U
  have : q.IsContinuous J K := projectionSliceContinuous s U
  have : q.IsCocontinuous J K := projectionSliceCocontinuous s U
  have : v.IsContinuous K J := cartesianSectionContinuous s U
  have : v.IsCocontinuous K J := cartesianSectionCocontinuous s U
  let e : q.sheafPushforwardCocontinuous A J K ≅
      v.sheafPushforwardContinuous A K J :=
    (cartesianLiftFunctor_adj s U).sheafPushforwardCocontinuousIso A
  have : (q.sheafPushforwardContinuous A J K).IsRightAdjoint :=
    (q.sheafAdjunctionContinuous A J K).isRightAdjoint
  have : (q.sheafPushforwardCocontinuous A J K).IsRightAdjoint :=
    (q.sheafAdjunctionCocontinuous A J K).isRightAdjoint
  let π : MorphismOfTopoi (Sheaf J A) (Sheaf K A) :=
    { inverseImage := q.sheafPushforwardContinuous A J K
      pushforward := q.sheafPushforwardCocontinuous A J K
      adj := q.sheafAdjunctionCocontinuous A J K
      preservesFiniteLimits := inferInstance }
  let σ : MorphismOfTopoi (Sheaf K A) (Sheaf J A) :=
    { inverseImage := q.sheafPushforwardCocontinuous A J K
      pushforward := v.sheafPushforwardCocontinuous A K J
      adj := (v.sheafAdjunctionCocontinuous A K J).ofNatIsoLeft e.symm
      preservesFiniteLimits := inferInstance }
  let hi : (π.comp σ).inverseImage ≅ 𝟭 (Sheaf K A) :=
    isoWhiskerLeft (q.sheafPushforwardContinuous A J K) e ≪≫
      Functor.sheafPushforwardContinuousComp' (cartesianLiftFunctor_base s U) A K J K ≪≫
      Functor.sheafPushforwardContinuousId A K
  exact ⟨
    { isContinuous := inferInstance
      isCocontinuous := inferInstance
      projection := π
      projection_inverseImage := rfl
      projection_pushforward := rfl
      rightSection := σ
      cartesianSectionFunctor := v
      cartesianSection_base := cartesianLiftFunctor_base s U
      cartesianSection_adjunction := cartesianLiftFunctor_adj s U
      cartesianSection_counit := cartesianLiftFunctor_adj_counit s U
      cartesianSection_isCartesian := cartesianLiftFunctor_isStronglyCartesian_map_self s U
      cartesianSection_isContinuous := inferInstance
      cartesianSection_isCocontinuous := inferInstance
      rightSection_inverseImage_cartesian := e
      rightSection_pushforward_cartesian := Iso.refl _
      rightSection_inverseImage := rfl
      rightSection_rightInverse_inverseImage := hi
      rightSection_rightInverse_pushforward :=
        ((π.comp σ).adj.ofNatIsoLeft hi).rightAdjointUniq (Adjunction.id) }⟩

/-- The canonical localized projection has a section whose inverse image is its direct image. -/
@[stacks 08P9]
public noncomputable def localizedProjectionSection : LocalizedProjectionSection s U :=
  Classical.choice (by exact nonempty_localizedProjectionSection s U)

end Stacks.Sites.FibredCategory

end
