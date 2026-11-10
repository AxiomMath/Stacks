module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia
public import StacksFrontier.Deformation.FormalObject.Associated
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.RestrictedRepresentable

/-!
# A morphism of formal objects induces a Yoneda 2-cell (Stacks 06SL)

A morphism `a : ξ ⟶ η` of formal objects of a category cofibered in groupoids over `𝒞_Λ`,
lying over a map `ξ.base ⟶ η.base` of complete local algebras, induces a natural
isomorphism between their associated morphisms from the restricted representable categories
of Stacks 06HL. At each Artinian point its component is the pushforward of the corresponding
level map of the formal objects.

The construction is the one of the Stacks source. An Artinian point `α` of the restricted
coyoneda category of `η.base` is a map `η.base ⟶ A` with `A` Artinian; its maximal ideal has
a least vanishing power, and the index the associated morphism selects at `α` and at the
precomposition `f.obj α` is the same, so `a` has a level map between exactly the two levels
involved. Both the component of the 2-cell and its naturality are then forced, because the
canonical arrows to the chosen pushforwards are strongly cocartesian in a category cofibered
in groupoids.

## Main results

* `Deformation.associatedMorphism_map`: **Stacks 06SL**, the natural isomorphism over the
  base category, with its components characterized by the commuting square with the level
  map and the canonical arrows to the chosen pushforwards.
* `Deformation.associatedMorphism_map_unique`: **Stacks 06SL**, that square determines the
  natural isomorphism uniquely.

## Implementation notes

The source uses the least positive exponent `m` for which the maximal ideal of the Artinian
target has vanishing `m`-th power. Formal objects here are indexed by `n` with quotient by
the `(n + 1)`-st power, so the two selected indices are equal. An isomorphism of based
functors expresses both naturality and that every component lies over the identity of its
Artinian base. The component square specifies the canonical isomorphism uniquely.

## References

* [Stacks Project, Tag 06SL](https://stacks.math.columbia.edu/tag/06SL)
-/

@[expose] public section

open CategoryTheory

-- Several steps below identify a component of the 2-cell with a pushforward arrow, which
-- means seeing through the definition of a restricted representable category down to the
-- objects of the category of elements of Stacks 06GX.  Those definitions are made reducible
-- here so that `simp` and instance search can traverse that chain.
attribute [local implicit_reducible] Deformation.restrictedRepresentable
  CategoryTheory.BasedCategory.ofFunctor CategoryTheory.BasedFunctor.comp

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

private lemma associatedPointInclusion_lift
    {ξ : FormalObject p} (pushforwards : ChosenPushforwards p)
    (X : AssociatedMorphism ξ pushforwards)
    (α : (restrictedCoyoneda ξ.base).Elements) :
    p.IsHomLift (X.factor α) (X.pointInclusion α) := by
  let P := pushforwards (X.factor α)
  let x : p.Fiber (AdicTruncation.obj ξ.base (X.level α)) :=
    ⟨ξ.level (X.level α), ξ.level_eq (X.level α)⟩
  let i := P.inclusion x
  have hi : p.IsHomLift (X.factor α) i := P.cocartesian x |>.toIsHomLift
  have hi' : p.IsHomLift (X.factor α)
      (X.pointInclusion α ≫ eqToHom (X.obj_eq α)) := by
    simpa only [X.pointInclusion_eq α] using hi
  exact (IsHomLift.eqToHom_comp_lift_iff p (X.factor α)
    (X.pointInclusion α) (X.obj_eq α)).mp hi'

private lemma associatedPointInclusion_stronglyCocartesian
    (hp : IsCofiberedInGroupoids p)
    {ξ : FormalObject p} (pushforwards : ChosenPushforwards p)
    (X : AssociatedMorphism ξ pushforwards)
    (α : (restrictedCoyoneda ξ.base).Elements) :
    p.IsStronglyCocartesian (X.factor α) (X.pointInclusion α) := by
  exact isStronglyCocartesian_of_isCofiberedInGroupoids hp (X.factor α)
    (X.pointInclusion α) (associatedPointInclusion_lift pushforwards X α)

private lemma vertical_isIso
    (hp : IsCofiberedInGroupoids p)
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k} {x y : F}
    (φ : x ⟶ y) (hφ : p.IsHomLift (𝟙 A) φ) : IsIso φ := by
  have hOp : p.op.IsHomLift (𝟙 (Opposite.op A)) φ.op := by
    let := hφ
    refine IsHomLift.of_fac p.op _ _ ?_ ?_ ?_
    · exact congrArg Opposite.op (IsHomLift.codomain_eq p (𝟙 A) φ)
    · exact congrArg Opposite.op (IsHomLift.domain_eq p (𝟙 A) φ)
    · simpa using congrArg Quiver.Hom.op (IsHomLift.fac p (𝟙 A) φ)
  let : IsIso φ.op :=
    Functor.isIso_of_fiber_isGroupoid (hp.fiber_isGroupoid (Opposite.op A)) φ.op hOp
  exact isIso_of_op φ

private noncomputable def verticalIso
    (hp : IsCofiberedInGroupoids p)
    {A : ArtinianLocalAlgCat.{u, v, w} Λ k} {x y : F}
    (φ : x ⟶ y) (hφ : p.IsHomLift (𝟙 A) φ) : x ≅ y := by
  letI : IsIso φ := vertical_isIso hp φ hφ
  exact asIso φ

private lemma transitionTo_naturality
    {ξ η : FormalObject p} (a : ξ ⟶ η) {n m : ℕ} (h : n ≤ m) :
    transitionTo ξ h ≫ a.app n = a.app m ≫ transitionTo η h := by
  induction m, h using Nat.le_induction with
  | base => simp [transitionTo_self]
  | succ m hm ih =>
    rw [transitionTo_succ ξ hm, Category.assoc, ih, ← Category.assoc,
      a.naturality, Category.assoc, transitionTo_succ η hm]

private lemma transitionTo_top_cast
    (ξ : FormalObject p) {n N N' : ℕ} (h : N = N')
    (hn : n ≤ N) (hn' : n ≤ N') :
    eqToHom (congrArg ξ.level h.symm) ≫ transitionTo ξ hn =
      transitionTo ξ hn' := by
  cases h
  have hh : hn = hn' := Subsingleton.elim _ _
  subst hn'
  simp

/-- Pushing a transition map through `a` and a cast of levels, for equal levels `n = m`. -/
private lemma transitionTo_comp_app_eqToHom {ξ η : FormalObject p} (a : ξ ⟶ η) {n m N : ℕ}
    (e : n = m) (hn : n ≤ N) (hm : m ≤ N) {Z : F} (i : η.level m ⟶ Z) :
    transitionTo ξ hn ≫ a.app n ≫ eqToHom (congrArg η.level e) ≫ i =
      a.app N ≫ transitionTo η hm ≫ i := by
  cases e
  simp [← Category.assoc, transitionTo_naturality a hn]

private lemma formalFactor_comp
    {ξ η : FormalObject p}
    (a : ξ ⟶ η) {α : (restrictedCoyoneda η.base).Elements} {n m : ℕ}
    (bX : AdicTruncation.obj ξ.base n ⟶ α.1)
    (bY : AdicTruncation.obj η.base m ⟶ α.1) (h : n = m)
    (hx : bX.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base n)) =
      α.2.hom.comp a.base.hom)
    (hy : bY.hom.comp (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal η.base m)) = α.2.hom) :
    AdicTruncation.map a.base n ≫
      eqToHom (congrArg (AdicTruncation.obj η.base) h) ≫ bY = bX := by
  cases h
  apply ArtinianLocalAlgCat.hom_ext
  apply AlgHom.ext
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  change bY.hom (((AdicTruncation.functor n).map a.base).hom
      (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base n) r :
        AdicTruncation.obj ξ.base n)) =
    bX.hom (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base n) r)
  rw [adicTruncationMap_mk]
  calc
    bY.hom (Ideal.Quotient.mk (AdicTruncation.ideal η.base n) (a.base.hom r)) =
        α.2.hom (a.base.hom r) := by
          have hh := DFunLike.congr_fun hy (a.base.hom r)
          change bY.hom (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal η.base n)
            (a.base.hom r)) = α.2.hom (a.base.hom r) at hh
          simpa only [Ideal.Quotient.mkₐ_eq_mk, artinianToComplete] using hh
    _ = bX.hom (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base n) r) := by
      symm
      have hh := DFunLike.congr_fun hx r
      change bX.hom (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base n) r) =
        α.2.hom (a.base.hom r) at hh
      simpa only [Ideal.Quotient.mkₐ_eq_mk, artinianToComplete] using hh

private lemma formalLevel_cast_lift
    {η : FormalObject p} {n m : ℕ} (h : n = m) :
    p.IsHomLift (eqToHom (congrArg (AdicTruncation.obj η.base) h))
      (eqToHom (congrArg η.level h)) := by
  have hηn : p.obj (η.level n) = AdicTruncation.obj η.base n := η.level_eq n
  have hηm : p.obj (η.level m) = AdicTruncation.obj η.base m := η.level_eq m
  apply IsHomLift.of_fac p _ _ hηn hηm
  rw [CategoryTheory.eqToHom_map p]
  simp [eqToHom_trans]

set_option maxHeartbeats 4000000 in
-- The kernel typechecking of the assembled naturality proof of this component square exceeds
-- the default heartbeat budget.
/-- A morphism of formal objects gives the canonical 2-cell between the
associated morphisms of restricted representable categories. Its component
at an Artinian point is characterized by the square with the corresponding
level map of formal objects. -/
@[stacks 06SL "existence and component square"]
public theorem associatedMorphism_map
    (hp : IsCofiberedInGroupoids p)
    {ξ η : FormalObject p} (a : ξ ⟶ η)
    (pushforwards : ChosenPushforwards p) :
    let f := restrictedRepresentableMap a.base
    let X := associatedMorphism hp ξ pushforwards
    let Y := associatedMorphism hp η pushforwards
    ∃ τ : BasedFunctor.comp f X.toBasedFunctor ≅ Y.toBasedFunctor,
      ∀ α, ∃ h : X.level (f.obj α) = Y.level α,
        X.pointInclusion (f.obj α) ≫ τ.hom.app α =
          a.app (X.level (f.obj α)) ≫
            eqToHom (congrArg η.level h) ≫ Y.pointInclusion α := by
  classical
  dsimp only
  let f := restrictedRepresentableMap a.base
  let X := associatedMorphism hp ξ pushforwards
  let Y := associatedMorphism hp η pushforwards
  change ∃ τ : BasedFunctor.comp f X.toBasedFunctor ≅ Y.toBasedFunctor,
    ∀ α, ∃ h : X.level (f.obj α) = Y.level α,
      X.pointInclusion (f.obj α) ≫ τ.hom.app α =
        a.app (X.level (f.obj α)) ≫
          eqToHom (congrArg η.level h) ≫ Y.pointInclusion α
  have hlevel (α : (restrictedCoyoneda η.base).Elements) :
      X.level (f.obj α) = Y.level α := by
    apply Nat.le_antisymm
    · exact (X.factor_spec (f.obj α)).2.1 _ (Y.factor_spec α).1
    · exact (Y.factor_spec α).2.1 _ (X.factor_spec (f.obj α)).1
  have htarget (α : (restrictedCoyoneda η.base).Elements) :
      p.IsHomLift (X.factor (f.obj α))
        (a.app (X.level (f.obj α)) ≫ eqToHom (congrArg η.level (hlevel α)) ≫
          Y.pointInclusion α) := by
    have hX := (X.factor_spec (f.obj α)).2.2
    have hY := (Y.factor_spec α).2.2
    change (X.factor (f.obj α)).hom.comp
        (Ideal.Quotient.mkₐ Λ (AdicTruncation.ideal ξ.base (X.level (f.obj α)))) =
      α.2.hom.comp a.base.hom at hX
    have hfactor :=
      formalFactor_comp a (X.factor (f.obj α)) (Y.factor α) (hlevel α) hX hY
    have hfirst : p.IsHomLift
        (AdicTruncation.map a.base (X.level (f.obj α)) ≫
          eqToHom (congrArg (AdicTruncation.obj η.base) (hlevel α)))
        (a.app (X.level (f.obj α)) ≫ eqToHom (congrArg η.level (hlevel α))) := by
      let : p.IsHomLift (AdicTruncation.map a.base (X.level (f.obj α)))
          (a.app (X.level (f.obj α))) := by
        change p.IsHomLift ((AdicTruncation.functor (X.level (f.obj α))).map a.base)
          (a.app (X.level (f.obj α)))
        exact a.app_lift (X.level (f.obj α))
      let := formalLevel_cast_lift (p := p) (η := η) (hlevel α)
      exact IsHomLift.comp p _ _ _ _
    have hcomp : p.IsHomLift
        ((AdicTruncation.map a.base (X.level (f.obj α)) ≫
          eqToHom (congrArg (AdicTruncation.obj η.base) (hlevel α))) ≫ Y.factor α)
        ((a.app (X.level (f.obj α)) ≫ eqToHom (congrArg η.level (hlevel α))) ≫
          Y.pointInclusion α) := by
      let := hfirst
      let := associatedPointInclusion_lift pushforwards Y α
      exact IsHomLift.comp p
        (AdicTruncation.map a.base (X.level (f.obj α)) ≫
          eqToHom (congrArg (AdicTruncation.obj η.base) (hlevel α)))
        (Y.factor α)
        (a.app (X.level (f.obj α)) ≫ eqToHom (congrArg η.level (hlevel α)))
        (Y.pointInclusion α)
    rw [← hfactor]
    exact (Category.assoc (a.app (X.level (f.obj α)))
      (eqToHom (congrArg η.level (hlevel α))) (Y.pointInclusion α)) ▸ hcomp
  -- `t` is given as a single application rather than by a tactic block, so that `dsimp only`
  -- below exposes `IsStronglyCocartesian.map` and its `IsHomLift` instance and `fac` lemma
  -- apply directly.
  let t : ∀ α : (restrictedCoyoneda η.base).Elements,
      X.toBasedFunctor.obj (f.obj α) ⟶ Y.toBasedFunctor.obj α := fun α =>
    have := associatedPointInclusion_stronglyCocartesian hp pushforwards X (f.obj α)
    have := htarget α
    Functor.IsStronglyCocartesian.map p (X.factor (f.obj α))
      (X.pointInclusion (f.obj α)) (g := 𝟙 (f.obj α).1)
      (f' := X.factor (f.obj α)) (by simp)
      (a.app (X.level (f.obj α)) ≫ eqToHom (congrArg η.level (hlevel α)) ≫
        Y.pointInclusion α)
  have ht_lift (α : (restrictedCoyoneda η.base).Elements) :
      p.IsHomLift (𝟙 α.1) (t α) := by
    -- `t α` lies over the identity of `(f.obj α).1`, which is the identity of `α.1` only
    -- after unfolding `f`; stating the goal that way lets the `map` instance apply.
    change p.IsHomLift (𝟙 (f.obj α).1) (t α)
    dsimp only [t]
    infer_instance
  have ht_fac (α : (restrictedCoyoneda η.base).Elements) :
      X.pointInclusion (f.obj α) ≫ t α =
        a.app (X.level (f.obj α)) ≫
          eqToHom (congrArg η.level (hlevel α)) ≫ Y.pointInclusion α := by
    dsimp only [t]
    have := associatedPointInclusion_stronglyCocartesian hp pushforwards X (f.obj α)
    have := htarget α
    simp [Functor.IsStronglyCocartesian.fac]
  let ni : (BasedFunctor.comp f X.toBasedFunctor).toFunctor ≅ Y.toBasedFunctor.toFunctor :=
    NatIso.ofComponents (fun α ↦ verticalIso hp (t α) (ht_lift α)) (by
      intro α β g
      change X.toBasedFunctor.map (f.map g) ≫ t β =
        t α ≫ Y.toBasedFunctor.map g
      let n := X.level (f.obj α)
      let m := X.level (f.obj β)
      let N := max (Y.level α) (Y.level β)
      let hYα : Y.level α ≤ N := Nat.le_max_left _ _
      let hYβ : Y.level β ≤ N := Nat.le_max_right _ _
      have hα : n ≤ N := by dsimp [n]; rw [hlevel α]; exact hYα
      have hβ : m ≤ N := by dsimp [m]; rw [hlevel β]; exact hYβ
      have hmaxX : max n m = N := by
        calc
          max n m = max (Y.level α) (Y.level β) := by
            simpa [n, m] using congrArg₂ max (hlevel α) (hlevel β)
          _ = N := rfl
      let eα := congrArg η.level (hlevel α)
      let eβ := congrArg η.level (hlevel β)
      let T := transitionTo ξ hα
      let H := T ≫ X.pointInclusion (f.obj α)
      let htop : ξ.level N ⟶ ξ.level (max n m) :=
        eqToHom (congrArg ξ.level hmaxX.symm)
      let wX := X.toBasedFunctor.w_obj (f.obj α)
      let gbase := eqToHom wX ≫ g.hom
      let : Category ((restrictedCoyoneda ξ.base).Elements) :=
        (restrictedRepresentable ξ.base).category
      let : Category ((restrictedCoyoneda η.base).Elements) :=
        (restrictedRepresentable η.base).category
      let αE : (restrictedCoyoneda η.base).Elements := α
      let βE : (restrictedCoyoneda η.base).Elements := β
      let gE : αE ⟶ βE := g
      let αX : (restrictedCoyoneda ξ.base).Elements := f.obj α
      let βX : (restrictedCoyoneda ξ.base).Elements := f.obj β
      let gX : αX ⟶ βX := f.map g
      let iXα := X.pointInclusion αX
      let iXβ := X.pointInclusion βX
      let iYα := Y.pointInclusion αE
      let iYβ := Y.pointInclusion βE
      let Yg := Y.toBasedFunctor.map gE
      have hHlift : p.IsHomLift (p.map H) H := by
        apply IsHomLift.of_fac' p _ _ rfl rfl
        simp
      let := isStronglyCocartesian_of_isCofiberedInGroupoids hp (p.map H) H hHlift
      have hXmap : p.IsHomLift g.hom (X.toBasedFunctor.map (f.map g)) :=
        @BasedFunctor.preserves_isHomLift _ _ _ _ X.toBasedFunctor _ _ _ _ g.hom (f.map g)
          (IsHomLift.of_fac (restrictedRepresentable ξ.base).p _ _ rfl rfl rfl)
      have hYmap : p.IsHomLift g.hom (Y.toBasedFunctor.map g) :=
        @BasedFunctor.preserves_isHomLift _ _ _ _ Y.toBasedFunctor _ _ _ _ g.hom g
          (IsHomLift.of_fac (restrictedRepresentable η.base).p _ _ rfl rfl rfl)
      have hrightG : p.IsHomLift gbase (X.toBasedFunctor.map (f.map g) ≫ t β) := by
        have := ht_lift β
        have := IsHomLift.comp p g.hom (𝟙 β.obj) (X.toBasedFunctor.map (f.map g)) (t β)
        rw [Category.comp_id] at this
        exact (IsHomLift.lift_eqToHom_comp_iff p _ _ wX).mpr this
      have hleftG : p.IsHomLift gbase (t α ≫ Y.toBasedFunctor.map g) := by
        have := ht_lift α
        have := IsHomLift.comp p (𝟙 α.obj) g.hom (t α) (Y.toBasedFunctor.map g)
        rw [Category.id_comp] at this
        exact (IsHomLift.lift_eqToHom_comp_iff p _ _ wX).mpr this
      have hEq : T ≫ X.pointInclusion (f.obj α) ≫
            X.toBasedFunctor.map (f.map g) ≫ t β =
          T ≫ X.pointInclusion (f.obj α) ≫ t α ≫
            Y.toBasedFunctor.map g := by
        let Tβ := transitionTo ξ hβ
        let U := transitionTo η hYα
        let Uβ := transitionTo η hYβ
        calc
          T ≫ X.pointInclusion (f.obj α) ≫
              X.toBasedFunctor.map (f.map g) ≫ t β =
              Tβ ≫ X.pointInclusion (f.obj β) ≫ t β := by
                have hx := X.map_pointInclusion gX
                have hprefixα : htop ≫ transitionTo ξ (Nat.le_max_left n m) = T :=
                  transitionTo_top_cast ξ hmaxX (Nat.le_max_left n m) hα
                have hprefixβ : htop ≫ transitionTo ξ (Nat.le_max_right n m) = Tβ :=
                  transitionTo_top_cast ξ hmaxX (Nat.le_max_right n m) hβ
                calc
                  T ≫ X.pointInclusion (f.obj α) ≫
                      X.toBasedFunctor.map (f.map g) ≫ t β =
                      htop ≫ transitionTo ξ (Nat.le_max_left n m) ≫
                        X.pointInclusion (f.obj α) ≫
                        X.toBasedFunctor.map (f.map g) ≫ t β := by
                          simpa [Category.assoc] using congrArg
                            (fun q => q ≫ X.pointInclusion (f.obj α) ≫
                              X.toBasedFunctor.map (f.map g) ≫ t β)
                            hprefixα.symm
                  _ = htop ≫ transitionTo ξ (Nat.le_max_right n m) ≫
                        X.pointInclusion (f.obj β) ≫ t β := by
                          simpa [αX, βX, gX, restrictedRepresentable] using
                            congrArg (fun q => htop ≫ q ≫ t β) hx
                  _ = Tβ ≫ X.pointInclusion (f.obj β) ≫ t β := by
                          simpa [Category.assoc] using congrArg
                            (fun q => q ≫ X.pointInclusion (f.obj β) ≫ t β)
                            hprefixβ
          _ = Tβ ≫ a.app m ≫ eqToHom eβ ≫ iYβ := by
                simpa [Category.assoc] using
                  congrArg (fun q => Tβ ≫ q) (ht_fac β)
          _ = a.app N ≫ Uβ ≫ iYβ := transitionTo_comp_app_eqToHom a (hlevel β) hβ hYβ iYβ
          _ = a.app N ≫ U ≫ iYα ≫ Yg := by
                have hmap' : U ≫ iYα ≫ Yg = Uβ ≫ iYβ := by
                  simpa [U, Uβ, iYα, iYβ, Yg, hYα, hYβ] using
                    Y.map_pointInclusion gE
                exact congrArg (fun q => a.app N ≫ q) hmap'.symm
          _ = T ≫ a.app n ≫ eqToHom eα ≫ iYα ≫ Yg :=
                (transitionTo_comp_app_eqToHom a (hlevel α) hα hYα (iYα ≫ Yg)).symm
          _ = T ≫ iXα ≫ t α ≫ Yg := by
                simpa [Category.assoc, T, hα, n] using
                  congrArg (fun q => T ≫ q ≫ Yg)
                    (ht_fac α).symm
      let := hrightG
      let := hleftG
      exact Functor.IsStronglyCocartesian.ext p (p.map H) H gbase
        (by simpa [H] using hEq)
      )
  let τ : BasedFunctor.comp f X.toBasedFunctor ≅ Y.toBasedFunctor :=
    BasedNatIso.mkNatIso ni (fun α ↦ by
      exact ht_lift α)
  refine ⟨τ, ?_⟩
  intro α
  refine ⟨hlevel α, ?_⟩
  change X.pointInclusion (f.obj α) ≫ ni.hom.app α =
    a.app (X.level (f.obj α)) ≫
      eqToHom (congrArg η.level (hlevel α)) ≫ Y.pointInclusion α
  exact ht_fac α

/-- The commuting square with the level map determines the canonical
Yoneda 2-cell uniquely. -/
@[stacks 06SL "uniqueness"]
public theorem associatedMorphism_map_unique
    (hp : IsCofiberedInGroupoids p)
    {ξ η : FormalObject p} (a : ξ ⟶ η)
    (pushforwards : ChosenPushforwards p) :
    let f := restrictedRepresentableMap a.base
    let X := associatedMorphism hp ξ pushforwards
    let Y := associatedMorphism hp η pushforwards
    ∀ (τ σ : BasedFunctor.comp f X.toBasedFunctor ≅ Y.toBasedFunctor),
      (∀ α, ∃ h : X.level (f.obj α) = Y.level α,
        X.pointInclusion (f.obj α) ≫ τ.hom.app α =
          a.app (X.level (f.obj α)) ≫
            eqToHom (congrArg η.level h) ≫ Y.pointInclusion α) →
      (∀ α, ∃ h : X.level (f.obj α) = Y.level α,
        X.pointInclusion (f.obj α) ≫ σ.hom.app α =
          a.app (X.level (f.obj α)) ≫
            eqToHom (congrArg η.level h) ≫ Y.pointInclusion α) →
      τ = σ := by
  dsimp only
  let f := restrictedRepresentableMap a.base
  let X := associatedMorphism hp ξ pushforwards
  let Y := associatedMorphism hp η pushforwards
  intro τ σ hτ hσ
  have hcomp (α : (restrictedCoyoneda η.base).Elements) :
      τ.hom.app α = σ.hom.app α := by
    obtain ⟨hτlevel, hτsquare⟩ := hτ α
    obtain ⟨hσlevel, hσsquare⟩ := hσ α
    have hlevels : hτlevel = hσlevel := Subsingleton.elim _ _
    cases hlevels
    have hsquare : X.pointInclusion (f.obj α) ≫ τ.hom.app α =
        X.pointInclusion (f.obj α) ≫ σ.hom.app α :=
      hτsquare.trans hσsquare.symm
    let := associatedPointInclusion_stronglyCocartesian hp pushforwards X (f.obj α)
    -- Cancelling `X.pointInclusion (f.obj α)` is stated for two abstract morphisms, so that
    -- the lifting hypotheses are elaborated at the ambient category of `p` rather than at
    -- the one carried by `BasedCategory.ofFunctor p`; those are the same up to unfolding,
    -- but only the former is the instance `IsStronglyCocartesian.ext` looks for.
    have cancel : ∀ ψ ψ' : X.toBasedFunctor.obj (f.obj α) ⟶ Y.toBasedFunctor.obj α,
        p.IsHomLift (𝟙 (f.obj α).1) ψ → p.IsHomLift (𝟙 (f.obj α).1) ψ' →
        X.pointInclusion (f.obj α) ≫ ψ = X.pointInclusion (f.obj α) ≫ ψ' → ψ = ψ' := by
      intro ψ ψ' hψ hψ' hfac
      have := hψ
      have := hψ'
      exact Functor.IsStronglyCocartesian.ext p (X.factor (f.obj α))
        (X.pointInclusion (f.obj α)) (𝟙 (f.obj α).1) hfac
    exact cancel _ _ (τ.hom.isHomLift' α) (σ.hom.isHomLift' α) hsquare
  apply Iso.ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext α
  exact hcomp α

end Deformation

end
