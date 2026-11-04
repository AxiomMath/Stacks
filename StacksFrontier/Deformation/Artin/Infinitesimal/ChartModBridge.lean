module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.StackSrcSmooth
public import StacksFrontier.Deformation.Artin.Obstruction.LiftSituationPullback

/-!
# Lift classes of a chart point and the relation of the groupoid of the chart

Let `a : Sch/U₀ ⟶ 𝒳` be a `1`-morphism to a category fibred in groupoids, `ι : Spec P ⟶ U₀` a
chart, and `ξ w = a(ι ∘ Spec w)` the object of `𝒳` of a point `w : P → C`
(`AlgebraicGeometry.Stack.GroupoidLift.StackChart`). For a square-zero thickening `e : C' → C`,
every lift `ℓ : P → C'` of `w` gives a lift of `ξ w` along `Spec C ⟶ Spec C'`: the object `ξ ℓ`
with the cartesian arrow `ξ w = ξ (e ∘ ℓ) ⟶ ξ ℓ`. This file shows that two such lifts are
isomorphic, as lifts of `ξ w`, exactly when `ℓ₁` and `ℓ₂` are related in the groupoid of the
chart (`AlgebraicGeometry.Stack.GroupoidLift.Groupoid.Rel`): an isomorphism of lifts is an arrow
of the groupoid over `C'` reducing to the identity of `w`.

This is the first half of the comparison of the tangent modules of Stacks 07Y9 at `ξ w` with the
module `Mod w` of the groupoid of a chart, which the proof of Stacks 0DNT uses to compute flat
base change at a point lifting to a smooth chart.

## Main definitions

* `Deformation.Artin.ChartLift.liftClasses`: the lift classes of `ξ w` along `Spec C ⟶ Spec C'`.
* `Deformation.Artin.ChartLift.lift`: the lift attached to a lift of `w`.

## Main results

* `Deformation.Artin.ChartLift.mk_lift_eq_mk_lift_iff`: two chart lifts have the same class
  exactly when they are related.
* `Deformation.Artin.ChartLift.exists_mk_lift_eq`: for a chart formally smooth on objects every
  lift class is the class of a chart lift.
* `Deformation.Artin.ChartLift.bijective_modToLiftClasses`: `[D] ↦ [ξ (ℓ₀ + D)]` is a bijection
  from `Mod w` onto the lift classes, given that relation is membership of the difference in
  `S w`.

So the lift classes of `ξ w` are the lifts of `w` modulo the relation of the groupoid, which
the engine identifies with `Mod w` in the presence of a formally étale chart of the arrows
(`AlgebraicGeometry.Stack.GroupoidLift.rel_iff_mem_S`).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Stack.GroupoidLift AlgebraicGeometry.Space.ChartDescent
open AlgebraicGeometry.Stack.GroupoidLift.StackChart

namespace Deformation.Artin.ChartLift

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
  {U₀ : BigFppfOver B S hS} (a : Stack.schemeFibredCategory B S hS U₀ ⟶ 𝒳)
  {P : SmallAlg (ringOf B S hS T') B.cutoff} (ι : specOver P ⟶ U₀)
  {C' C : SmallAlg (ringOf B S hS T') B.cutoff} (e : SqZero C' C)
  (w : P.obj →ₐ[ringOf B S hS T'] C.obj)

/-- The lifts of `ξ w` along `Spec C ⟶ Spec C'`. -/
abbrev Lifts : Type _ :=
  (Under.post 𝒳.val.p).Fiber (Under.mk (eqToHom (ξ_obj a ι w) ≫ specOverMap e.q))

/-- The isomorphism classes of lifts of `ξ w` along `Spec C ⟶ Spec C'`. -/
abbrev liftClasses : Type _ :=
  Quotient (isIsomorphicSetoid (Lifts a ι e w))

variable {a ι e w}

/-- The arrow `ξ w ⟶ ξ ℓ` of a lift `ℓ` of `w`. -/
def liftArrow (ℓ : P.obj →ₐ[ringOf B S hS T'] C'.obj) (hℓ : e.q.hom.hom.comp ℓ = w) :
    ξ a ι w ⟶ ξ a ι ℓ :=
  eqToHom (congrArg (ξ a ι) hℓ.symm) ≫ trans a ι e.q ℓ

/-- The arrow `ξ w ⟶ ξ ℓ` of a lift `ℓ` of `w` lies over `Spec C ⟶ Spec C'`. -/
theorem liftArrow_isHomLift (ℓ : P.obj →ₐ[ringOf B S hS T'] C'.obj)
    (hℓ : e.q.hom.hom.comp ℓ = w) :
    𝒳.val.p.IsHomLift (specOverMap e.q) (liftArrow (a := a) (ι := ι) ℓ hℓ) := by
  subst hℓ
  simpa [liftArrow] using trans_isHomLift a ι e.q ℓ

/-- The lift of `ξ w` attached to a lift `ℓ` of `w`. -/
def lift (ℓ : P.obj →ₐ[ringOf B S hS T'] C'.obj) (hℓ : e.q.hom.hom.comp ℓ = w) :
    Lifts a ι e w :=
  underFiberObjMk 𝒳.val.p (ξ_obj a ι w) (specOverMap e.q) (liftArrow ℓ hℓ)
    (liftArrow_isHomLift ℓ hℓ)

/-- An identification `X = Y` of two objects equal to `Z` is heterogeneously equal to the
identity of `Z`. -/
theorem eqToHom_heq_id {𝒞 : Type*} [Category 𝒞] {X Y Z : 𝒞} (h₁ : X = Z) (h₂ : Y = Z)
    (p : X = Y) : HEq (eqToHom p) (𝟙 Z) := by
  subst h₁ h₂
  rfl

/-- An identification of objects lies over the identity. -/
theorem isHomLift_eqToHom {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {p : 𝒞 ⥤ 𝒟} {X Y : 𝒞}
    {R : 𝒟} (h : X = Y) (hX : p.obj X = R) : p.IsHomLift (𝟙 R) (eqToHom h) := by
  subst h
  simpa using IsHomLift.id hX

/-- The structure arrow of a morphism of lifts lies over the identity. -/
private theorem isHomLift_id_right {s t : Lifts a ι e w} (φ : s ⟶ t) :
    𝒳.val.p.IsHomLift (𝟙 (specOver C')) φ.1.right :=
  underPost_isHomLift_right 𝒳.val.p _ φ.1 φ.2

/-- An arrow `χ` is compatible with the arrows of the chart lifts `ℓ₁`, `ℓ₂` exactly when it
makes the square of `trans` commute up to the identification of the reductions. -/
private theorem liftArrow_comp_eq_iff {ℓ₁ ℓ₂ : P.obj →ₐ[ringOf B S hS T'] C'.obj}
    (h₁ : e.q.hom.hom.comp ℓ₁ = w) (h₂ : e.q.hom.hom.comp ℓ₂ = w)
    (χ : ξ a ι ℓ₁ ⟶ ξ a ι ℓ₂) :
    liftArrow (a := a) (ι := ι) ℓ₁ h₁ ≫ χ = liftArrow ℓ₂ h₂ ↔
      (eqToHom (congrArg (ξ a ι) (h₁.trans h₂.symm)) :
        ξ a ι (e.q.hom.hom.comp ℓ₁) ⟶ ξ a ι (e.q.hom.hom.comp ℓ₂)) ≫ trans a ι e.q ℓ₂ =
        trans a ι e.q ℓ₁ ≫ χ := by
  rw [liftArrow, liftArrow, Category.assoc, eqToHom_comp_iff, eqToHom_trans_assoc, eq_comm]

/-- A morphism of lifts of `ξ w` between two chart lifts is an arrow of the groupoid reducing to
the identity. -/
theorem rel_of_hom {ℓ₁ ℓ₂ : P.obj →ₐ[ringOf B S hS T'] C'.obj} (h₁ : e.q.hom.hom.comp ℓ₁ = w)
    (h₂ : e.q.hom.hom.comp ℓ₂ = w) (φ : lift (a := a) (ι := ι) ℓ₁ h₁ ⟶ lift ℓ₂ h₂) :
    Rel (stackGroupoid a ι) e w ℓ₁ ℓ₂ := by
  have hw : liftArrow (a := a) (ι := ι) ℓ₁ h₁ ≫ φ.1.right = liftArrow ℓ₂ h₂ := Under.w φ.1
  let g : Arr a ι C' := ⟨ℓ₁, ℓ₂, φ.1.right, isHomLift_id_right φ⟩
  refine ⟨g, ?_, rfl, rfl⟩
  have hl : 𝒳.val.p.IsHomLift (𝟙 (specOver C))
      (eqToHom (congrArg (ξ a ι) (h₁.trans h₂.symm)) :
        ξ a ι (e.q.hom.hom.comp ℓ₁) ⟶ ξ a ι (e.q.hom.hom.comp ℓ₂)) :=
    isHomLift_eqToHom _ (ξ_obj a ι _)
  show Arr.map a ι e.q g = Arr.idt w
  rw [Arr.map_eq_mk e.q g _ hl ((liftArrow_comp_eq_iff h₁ h₂ _).mp hw)]
  exact Arr.ext_heq h₁ h₂ (eqToHom_heq_id (congrArg (ξ a ι) h₁) (congrArg (ξ a ι) h₂)
    (congrArg (ξ a ι) (h₁.trans h₂.symm)))

/-- An arrow of the groupoid reducing to the identity of `w` is a morphism of the chart lifts of
its source and target. -/
theorem nonempty_hom_of_rel {ℓ₁ ℓ₂ : P.obj →ₐ[ringOf B S hS T'] C'.obj}
    (h₁ : e.q.hom.hom.comp ℓ₁ = w) (h₂ : e.q.hom.hom.comp ℓ₂ = w)
    (h : Rel (stackGroupoid a ι) e w ℓ₁ ℓ₂) :
    Nonempty (lift (a := a) (ι := ι) ℓ₁ h₁ ⟶ lift ℓ₂ h₂) := by
  obtain ⟨g, hmap, hs, ht⟩ := h
  obtain ⟨s, t, χ, hχ⟩ := g
  change s = ℓ₁ at hs
  change t = ℓ₂ at ht
  subst hs ht
  change Arr.map a ι e.q ⟨s, t, χ, hχ⟩ = Arr.idt w at hmap
  have hh := congr_arg_heq (fun g : Arr a ι C => g.hom) hmap
  have hμ := (conj_eqToHom_iff_heq _ _ (congrArg (ξ a ι) h₁) (congrArg (ξ a ι) h₂)).mpr hh
  have hfac := Arr.map_hom_fac (a := a) (ι := ι) e.q ⟨s, t, χ, hχ⟩
  change (Arr.map a ι e.q ⟨s, t, χ, hχ⟩).hom ≫ trans a ι e.q t = trans a ι e.q s ≫ χ at hfac
  rw [hμ] at hfac
  have he : (eqToHom (congrArg (ξ a ι) (h₁.trans h₂.symm)) :
      ξ a ι (e.q.hom.hom.comp s) ⟶ ξ a ι (e.q.hom.hom.comp t)) =
      eqToHom (congrArg (ξ a ι) h₁) ≫ 𝟙 (ξ a ι w) ≫ eqToHom (congrArg (ξ a ι) h₂).symm := by
    simp only [Category.id_comp, eqToHom_trans]
  exact ⟨underFiberHomMk 𝒳.val.p (ξ_obj a ι w) (specOverMap e.q) χ hχ
    ((liftArrow_comp_eq_iff h₁ h₂ χ).mpr ((congrArg (· ≫ trans a ι e.q t) he).trans hfac))⟩

/-- A morphism of lifts of a category fibred in groupoids is an isomorphism. -/
theorem nonempty_iso_of_hom {s t : Lifts a ι e w} (φ : s ⟶ t) : Nonempty (s ≅ t) := by
  have hχ := isHomLift_id_right φ
  have : IsIso φ.1.right := 𝒳.isFiberedInGroupoids.isIso_of_isHomLift_id φ.1.right hχ
  have hinv : 𝒳.val.p.IsHomLift (𝟙 (specOver C')) (CategoryTheory.inv φ.1.right) := by
    have := IsHomLift.inv 𝒳.val.p (𝟙 (specOver C')) φ.1.right
    simpa using this
  have hw : t.1.hom ≫ CategoryTheory.inv φ.1.right = s.1.hom := by
    rw [IsIso.comp_inv_eq]
    exact (Under.w φ.1).symm
  let ψ : t ⟶ s := underFiberHomMk 𝒳.val.p (ξ_obj a ι w) (specOverMap e.q) _ hinv hw
  exact ⟨⟨φ, ψ, Functor.Fiber.hom_ext (Under.UnderMorphism.ext (IsIso.hom_inv_id φ.1.right)),
    Functor.Fiber.hom_ext (Under.UnderMorphism.ext (IsIso.inv_hom_id φ.1.right))⟩⟩

/-- **Two chart lifts have the same class exactly when they are related in the groupoid of the
chart.** -/
theorem mk_lift_eq_mk_lift_iff {ℓ₁ ℓ₂ : P.obj →ₐ[ringOf B S hS T'] C'.obj}
    (h₁ : e.q.hom.hom.comp ℓ₁ = w) (h₂ : e.q.hom.hom.comp ℓ₂ = w) :
    (Quotient.mk _ (lift (a := a) (ι := ι) ℓ₁ h₁) : liftClasses a ι e w) =
        Quotient.mk _ (lift ℓ₂ h₂) ↔
      Rel (stackGroupoid a ι) e w ℓ₁ ℓ₂ := by
  constructor
  · intro h
    obtain ⟨φ⟩ := Quotient.exact h
    exact rel_of_hom h₁ h₂ φ.hom
  · intro h
    obtain ⟨φ⟩ := nonempty_hom_of_rel h₁ h₂ h
    exact Quotient.sound (nonempty_iso_of_hom φ)

/-- **Every lift of a chart point is a chart lift**, when the chart is formally smooth on objects
and `ι` lifts points of `U₀` across square-zero thickenings (the hypotheses of
`AlgebraicGeometry.Stack.GroupoidLift.stackGroupoid_srcFormallySmooth`). -/
theorem exists_mk_lift_eq
    (ha : Stack.IsFormallySmoothOnObjects B S hS (Stack.schemeFibredCategory B S hS U₀) 𝒳 a)
    (hι : ∀ {C' C : SmallAlg (ringOf B S hS T') B.cutoff} (e : SqZero C' C)
      (m' : specOver C' ⟶ U₀) (u : P.obj →ₐ[ringOf B S hS T'] C.obj),
      specOverMap e.q ≫ m' = specOverMap (SmallAlg.homMk u) ≫ ι →
      ∃ u' : P.obj →ₐ[ringOf B S hS T'] C'.obj, e.q.hom.hom.comp u' = u ∧
        specOverMap (SmallAlg.homMk u') ≫ ι = m')
    (c : liftClasses a ι e w) :
    ∃ (ℓ : P.obj →ₐ[ringOf B S hS T'] C'.obj) (hℓ : e.q.hom.hom.comp ℓ = w),
      Quotient.mk _ (lift (a := a) (ι := ι) ℓ hℓ) = c := by
  induction c using Quotient.ind with
  | _ t =>
  have hthk : Stacks.Thickenings.IsFirstOrderThickening
      ((BigFppfOver.toScheme B S hS).map (specOverMap e.q)) :=
    Stacks.Smooth.isFirstOrderThickening_specMap _ e.surj e.sq
  have hty : 𝒳.val.p.obj t.1.right = specOver C' :=
    underFiber_right_obj 𝒳.val.p (ξ_obj a ι w) (specOverMap e.q) t
  have ht : 𝒳.val.p.IsHomLift (specOverMap e.q) t.1.hom :=
    underFiber_isHomLift 𝒳.val.p (ξ_obj a ι w) (specOverMap e.q) t
  obtain ⟨x', hx', β, hβ, γ', hγ', hfac⟩ := ha.exists_lift_of_obj_eq (specOverMap e.q) inferInstance
    inferInstance hthk (x := pt ι w) rfl hty t.1.hom
  obtain ⟨L, ⟨⟨⟩⟩, m⟩ := x'
  change L = specOver C' at hx'
  subst hx'
  have fβ := IsHomLift.fac' (Stack.schemeFibredCategory B S hS U₀).val.p (specOverMap e.q) β
  change β.left = 𝟙 _ ≫ specOverMap e.q ≫ 𝟙 _ at fβ
  rw [Category.id_comp, Category.comp_id] at fβ
  have hm : specOverMap e.q ≫ m = specOverMap (SmallAlg.homMk w) ≫ ι := by
    rw [← fβ]
    exact Over.w β
  obtain ⟨ℓ, hℓ, hm'⟩ := hι e m w hm
  subst hm' hℓ
  have hβeq : β = Over.homMk (specOverMap e.q) (specOverMap_comp_pt ι e.q ℓ) :=
    Over.OverMorphism.ext fβ
  subst hβeq
  have hlift : liftArrow (a := a) (ι := ι) ℓ rfl ≫ γ' = t.1.hom := by
    rw [← hfac]
    exact congrArg (· ≫ γ') (Category.id_comp _)
  refine ⟨ℓ, rfl, Quotient.sound ?_⟩
  exact nonempty_iso_of_hom (underFiberHomMk 𝒳.val.p (ξ_obj a ι _) (specOverMap e.q) γ' hγ' hlift)

/-! ### The module of the groupoid and the lift classes -/

section ModEquiv

variable (ℓ₀ : P.obj →ₐ[ringOf B S hS T'] C'.obj) (h₀ : e.q.hom.hom.comp ℓ₀ = w)
  (hrel : ∀ {ℓ₁ ℓ₂ : P.obj →ₐ[ringOf B S hS T'] C'.obj}, e.q.hom.hom.comp ℓ₁ = w →
    e.q.hom.hom.comp ℓ₂ = w →
      (Rel (stackGroupoid a ι) e w ℓ₁ ℓ₂ ↔
        ℓ₂.toLinearMap - ℓ₁.toLinearMap ∈
          AlgebraicGeometry.Stack.GroupoidLift.S (stackGroupoid a ι) e w))

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- The difference of the lifts `ℓ₀ + D₁` and `ℓ₀ + D₂` of `w` is `D₁ - D₂`. -/
theorem toLinearMap_addLift_sub_addLift {D₁ D₂ : P.obj →ₗ[ringOf B S hS T'] C'.obj}
    (hD₁ : D₁ ∈ Der e w) (hD₂ : D₂ ∈ Der e w) :
    (addLift D₁ hD₁ ℓ₀ h₀).toLinearMap - (addLift D₂ hD₂ ℓ₀ h₀).toLinearMap = D₁ - D₂ := by
  rw [addLift_toLinearMap, addLift_toLinearMap]
  abel

include hrel in
/-- The lift class of `ℓ₀ + D`, as a function of the class of `D` in `Mod w`. -/
def modToLiftClasses : Mod (stackGroupoid a ι) e w → liftClasses a ι e w :=
  Quotient.lift (fun D : Der e w => Quotient.mk _
      (lift (a := a) (ι := ι) (addLift D.1 D.2 ℓ₀ h₀) (addLift_reduce D.1 D.2 ℓ₀ h₀)))
    (fun D₁ D₂ hD => by
      have hmem : D₁.1 - D₂.1 ∈ AlgebraicGeometry.Stack.GroupoidLift.S (stackGroupoid a ι) e w :=
        ((Submodule.quotientRel_def _).mp hD : D₁ - D₂ ∈ _)
      refine ((mk_lift_eq_mk_lift_iff _ _).mpr ((hrel (addLift_reduce _ _ _ _)
        (addLift_reduce _ _ _ _)).mpr ?_)).symm
      rw [toLinearMap_addLift_sub_addLift]
      exact hmem)

/-- `modToLiftClasses` sends the class of a derivation `D` to the class of the chart lift
`ξ (ℓ₀ + D)`. -/
theorem modToLiftClasses_mk (D : P.obj →ₗ[ringOf B S hS T'] C'.obj) (hD : D ∈ Der e w) :
    modToLiftClasses ℓ₀ h₀ hrel (mkMod D hD) =
      (Quotient.mk _ (lift (a := a) (ι := ι) (addLift D hD ℓ₀ h₀) (addLift_reduce D hD ℓ₀ h₀)) :
        liftClasses a ι e w) :=
  rfl

include hrel in
/-- **The lift classes of a chart point are the module of the groupoid of the chart**: for a
chart formally smooth on objects whose relation is the relation of `Mod w` (as it is in the
presence of a formally étale chart of the arrows near the identity,
`AlgebraicGeometry.Stack.GroupoidLift.rel_iff_mem_S`), `D ↦ [ξ (ℓ₀ + D)]` is a bijection
`Mod w ≃ liftClasses`. -/
theorem bijective_modToLiftClasses
    (ha : Stack.IsFormallySmoothOnObjects B S hS (Stack.schemeFibredCategory B S hS U₀) 𝒳 a)
    (hι : ∀ {C' C : SmallAlg (ringOf B S hS T') B.cutoff} (e : SqZero C' C)
      (m' : specOver C' ⟶ U₀) (u : P.obj →ₐ[ringOf B S hS T'] C.obj),
      specOverMap e.q ≫ m' = specOverMap (SmallAlg.homMk u) ≫ ι →
      ∃ u' : P.obj →ₐ[ringOf B S hS T'] C'.obj, e.q.hom.hom.comp u' = u ∧
        specOverMap (SmallAlg.homMk u') ≫ ι = m') :
    Function.Bijective (modToLiftClasses ℓ₀ h₀ hrel) := by
  refine ⟨fun x y hxy => ?_, fun c => ?_⟩
  · induction x using Submodule.Quotient.induction_on with
    | H D₁ =>
    induction y using Submodule.Quotient.induction_on with
    | H D₂ =>
    have hr := (mk_lift_eq_mk_lift_iff _ _).mp hxy
    rw [hrel (addLift_reduce _ _ _ _) (addLift_reduce _ _ _ _),
      toLinearMap_addLift_sub_addLift] at hr
    have hr' : D₂ - D₁ ∈ (AlgebraicGeometry.Stack.GroupoidLift.S (stackGroupoid a ι) e w).comap
        (Der e w).subtype := hr
    exact (Submodule.Quotient.eq _).mpr ((Submodule.neg_mem_iff _).mp (by
      simpa only [neg_sub] using hr'))
  · obtain ⟨ℓ, hℓ, rfl⟩ := exists_mk_lift_eq ha hι c
    refine ⟨mkMod _ (sub_mem_Der h₀ hℓ), ?_⟩
    rw [modToLiftClasses_mk]
    congr 2
    exact (eq_addLift h₀ hℓ).symm

end ModEquiv

end Deformation.Artin.ChartLift

end
