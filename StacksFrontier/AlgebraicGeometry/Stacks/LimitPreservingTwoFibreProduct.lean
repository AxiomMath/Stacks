module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.LimitPreservingOnObjects

/-!
# The 2-fibre product of limit preserving categories fibred in groupoids

Let `𝒳 ⟶ 𝒴` and `𝒵 ⟶ 𝒴` be 1-morphisms of categories fibred in groupoids over the big fppf site
of a scheme `S`. Stacks 07XM asserts two things about the 2-fibre product `𝒳 ×_𝒴 𝒵`: part (1),
that its structure morphism to `(Sch/S)_{fppf}` is limit preserving on objects in the sense of
Stacks 06CU; and part (2), that `𝒳 ×_𝒴 𝒵` is itself limit preserving in the sense of Stacks 07XL
when `𝒳`, `𝒴` and `𝒵` are. This file proves part (2); part (1) is
`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_toTerminalCFG_twoFibreProduct`.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreserving_twoFibreProduct`: **Stacks 07XM, part (2)**.

## Implementation notes

*What is proved.* The full statement of part (2): the colimit comparison of Stacks 07XL for
`𝒳 ×_𝒴 𝒵` is an equivalence of categories, hence essentially surjective, full and faithful. The
source says the arguments are omitted.

*The proof.* Limit preservation is transported through the three descent conditions of
`StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStageDescent`, which replace the colimit by
statements about cartesian arrows and vertical morphisms at a stage; the content of this file is
that each of the three holds for the 2-fibre product as soon as it holds for the factors. An
object of `𝒳 ×_𝒴 𝒵` over the cone point is a triple `(x, z, φ)` with `φ` vertical, and descending
it means descending `x` and `z` to a common stage and then descending `φ`, for which the
descent of vertical morphisms in `𝒴` is used. A morphism of the 2-fibre product is a pair of
morphisms making one square commute, so descending one means descending the pair and then forcing
the square, which is where descent of *equalities* in `𝒴` enters; cofilteredness of the index
category merges the several stages the two components are descended to.

*Universes.* The three categories fibred in groupoids are taken with total category in the same
universes as the site, as in part (1) and as `AlgebraicGeometry.BigFppfOver.twoFibreProduct`
requires. The descent statements proved on the way are universe-polymorphic in all of the
category, the two sources, the target and the index category.

## References

* [Stacks Project, Tag 07XM](https://stacks.math.columbia.edu/tag/07XM)
* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

attribute [local implicit_reducible] TwoFibreProductOver.structureFunctor
attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

namespace Deformation.Artin

universe uC vC uA vA uM vM uD vD vI wI

section TwoFibreDescent

variable {C : Type uC} [Category.{vC} C]
  {XA : Type uA} [Category.{vA} XA] {XM : Type uM} [Category.{vM} XM]
  {XZ : Type uD} [Category.{vD} XZ]
  {I : Type vI} [Category.{wI} I]

/- Instance search does not see through the split-fibre restriction functor, so without this the
`IsHomLift` instances of the comparison morphisms below are not found. -/
attribute [local implicit_reducible] Functor.SplitFiber.restrict

/-- A morphism from the image of an object over the cone point into an object
living over a stage factors, after passing to a later stage, through the image
of a morphism over that stage. -/
private lemma factor_through_stage
    (pX : XA ⥤ C) (pY : XM ⥤ C) [pX.IsFibered] [pY.IsFibered]
    (hY : pY.IsFiberedInGroupoids) (G : XA ⥤ XM) (hG : G ⋙ pY = pX)
    [IsCofiltered I] (Dg : I ⥤ C) (cc : Cone Dg)
    [(colimitComparison pY Dg cc).Full]
    (i : I) (x : pX.Fiber cc.pt) (xi : pX.Fiber (Dg.obj i))
    (yj : pY.Fiber (Dg.obj i)) (δ : x.1 ⟶ xi.1) (γ : G.obj x.1 ⟶ yj.1)
    [pX.IsHomLift (cc.π.app i) δ] [pY.IsHomLift (cc.π.app i) γ] :
    ∃ (k : I) (t : k ⟶ i) (xk : pX.Fiber (Dg.obj k))
      (δk : x.1 ⟶ xk.1) (γk : G.obj xk.1 ⟶ yj.1),
      pX.IsHomLift (cc.π.app k) δk ∧ pY.IsHomLift (Dg.map t) γk ∧
      G.map δk ≫ γk = γ := by
  let z : pY.Fiber cc.pt := ⟨G.obj x.1, (Functor.congr_obj hG x.1).trans x.2⟩
  let yi : pY.Fiber (Dg.obj i) :=
    ⟨G.obj xi.1, (Functor.congr_obj hG xi.1).trans xi.2⟩
  let aa : pY.SplitFiber (Dg.obj i) := ⟨Dg.obj i, yi, 𝟙 _⟩
  let bb : pY.SplitFiber (Dg.obj i) := ⟨Dg.obj i, yj, 𝟙 _⟩
  have hδY : pY.IsHomLift (cc.π.app i) (G.map δ) :=
    Functor.isHomLift_map_of_comp_eq hG _ δ
  let _ : pY.IsHomLift (cc.π.app i ≫ 𝟙 _) (G.map δ) := by simpa using hδY
  let _ : pY.IsHomLift (cc.π.app i ≫ 𝟙 _) γ := by
    simpa using (inferInstance : pY.IsHomLift (cc.π.app i) γ)
  let η := Functor.toPullbackFiber pY z yi (cc.π.app i ≫ 𝟙 _) (G.map δ)
  let θ := Functor.toPullbackFiber pY z yj (cc.π.app i ≫ 𝟙 _) γ
  let _ := hY.fiber_isGroupoid cc.pt
  let f := inv η ≫ θ
  obtain ⟨k, s, g, hg⟩ :=
    splitFiber_full_descent_same_stage pY Dg cc i aa bb f
  let si := Dg.map s ≫ 𝟙 (Dg.obj i)
  change (Functor.pullbackFiber pY yi si ⟶ Functor.pullbackFiber pY yj si) at g
  have hi : cc.π.app k ≫ si = cc.π.app i ≫ 𝟙 _ := by simp [si, cc.w s]
  let _ : pY.IsHomLift (cc.π.app k ≫ si) (G.map δ) := hi.symm ▸ inferInstance
  let _ : pY.IsHomLift (cc.π.app k ≫ si) γ := hi.symm ▸ inferInstance
  let ηk := Functor.toPullbackFiber pY z yi (cc.π.app k ≫ si) (G.map δ)
  let θk := Functor.toPullbackFiber pY z yj (cc.π.app k ≫ si) γ
  have hη := toPullbackFiber_heq pY z yi _ _ hi (G.map δ)
  have hθ := toPullbackFiber_heq pY z yj _ _ hi γ
  have hηg : ηk ≫ (Functor.SplitFiber.restrict pY (cc.π.app k)).map
      (X := (Functor.SplitFiber.restrict pY (Dg.map s)).obj aa)
      (Y := (Functor.SplitFiber.restrict pY (Dg.map s)).obj bb) g = θk := by
    apply eq_of_heq
    exact (Cat.comp_heq_of_eq (rfl : z = z)
      (congrArg (Functor.pullbackFiber pY yi) hi)
      (congrArg (Functor.pullbackFiber pY yj) hi) hη hg).trans
        ((heq_of_eq (by simp [f] : η ≫ f = θ)).trans hθ.symm)
  let xk := Functor.pullbackFiber pX xi si
  let d := Functor.IsPreFibered.pullbackMap xi.2 si
  let δk := Functor.IsStronglyCartesian.map pX si d
    (g := cc.π.app k) (by simpa using hi.symm) δ
  let _ : pY.IsHomLift si (G.map d) := Functor.isHomLift_map_of_comp_eq hG si d
  let ηs := Functor.toPullbackFiber pY
    (⟨G.obj xk.1, (Functor.congr_obj hG xk.1).trans xk.2⟩ : pY.Fiber (Dg.obj k))
    yi si (G.map d)
  let γk := Functor.Fiber.fiberInclusion.map ηs ≫
    Functor.Fiber.fiberInclusion.map g ≫
      Functor.IsPreFibered.pullbackMap yj.2 si
  have hδk : pX.IsHomLift (cc.π.app k) δk := inferInstance
  let _ : pY.IsHomLift (cc.π.app k) (G.map δk) :=
    Functor.isHomLift_map_of_comp_eq hG _ δk
  have he : G.map δk ≫ Functor.Fiber.fiberInclusion.map ηs =
      Functor.Fiber.fiberInclusion.map ηk ≫
        Functor.pullbackFiberProj yi si (cc.π.app k) := by
    apply Functor.IsStronglyCartesian.ext pY si
      (Functor.IsPreFibered.pullbackMap yi.2 si) (cc.π.app k)
    dsimp only [ηs, ηk]
    simp only [Category.assoc, Functor.toPullbackFiber_fac,
      Functor.pullbackFiberProj_fac]
    change G.map δk ≫ G.map d = G.map δ
    rw [← G.map_comp, Functor.IsStronglyCartesian.fac]
  refine ⟨k, s, xk, δk, γk, hδk, ?_, ?_⟩
  · have hh : pY.IsHomLift (𝟙 (Dg.obj k) ≫ 𝟙 (Dg.obj k) ≫ si) γk := by
      dsimp only [γk]
      infer_instance
    simpa [si] using hh
  · dsimp only [γk]
    rw [← Category.assoc, he]
    have hfac := Functor.SplitFiber.restrictHom_fac (p := pY) (cc.π.app k)
      (o := (Functor.SplitFiber.restrict pY (Dg.map s)).obj aa)
      (o' := (Functor.SplitFiber.restrict pY (Dg.map s)).obj bb) g
    change Functor.Fiber.fiberInclusion.map
      ((Functor.SplitFiber.restrict pY (cc.π.app k)).map
        (X := (Functor.SplitFiber.restrict pY (Dg.map s)).obj aa)
        (Y := (Functor.SplitFiber.restrict pY (Dg.map s)).obj bb) g) ≫
        Functor.IsPreFibered.pullbackMap yj.2 (cc.π.app k ≫ si) =
      Functor.pullbackFiberProj yi si (cc.π.app k) ≫
        Functor.Fiber.fiberInclusion.map g ≫
          Functor.IsPreFibered.pullbackMap yj.2 si at hfac
    rw [Category.assoc, ← hfac, ← Functor.map_comp_assoc, hηg]
    exact Functor.toPullbackFiber_fac pY z yj _ γ

/-- A representative of an object of the fibre over the cone point can be moved
to any earlier stage of the diagram. -/
private lemma homLift_at_earlier_stage (pX : XA ⥤ C) [pX.IsFibered]
    (Dg : I ⥤ C) (cc : Cone Dg) {i k : I} (s : k ⟶ i)
    (x : pX.Fiber cc.pt) (xi : pX.Fiber (Dg.obj i)) (δ : x.1 ⟶ xi.1)
    (hδ : pX.IsHomLift (cc.π.app i) δ) :
    ∃ (xk : pX.Fiber (Dg.obj k)) (δk : x.1 ⟶ xk.1),
      pX.IsHomLift (cc.π.app k) δk := by
  let := hδ
  exact ⟨Functor.pullbackFiber pX xi (Dg.map s),
    Functor.IsStronglyCartesian.map pX (Dg.map s)
      (Functor.IsPreFibered.pullbackMap xi.2 (Dg.map s))
      (g := cc.π.app k) (cc.w s).symm δ, inferInstance⟩

/-- Object descent produces a representative at a stage mapping to any
prescribed stage. -/
private lemma descentObj_at_stage (pX : XA ⥤ C) [pX.IsFibered]
    [IsCofiltered I] (Dg : I ⥤ C) (cc : Cone Dg) (hd : DescentObj pX Dg cc)
    (x : pX.Fiber cc.pt) (i : I) :
    ∃ (k : I) (_s : k ⟶ i) (xk : pX.Fiber (Dg.obj k)) (δ : x.1 ⟶ xk.1),
      pX.IsHomLift (cc.π.app k) δ := by
  obtain ⟨i', xi', δ', hδ'⟩ := hd x
  obtain ⟨xk, δk, hδk⟩ := homLift_at_earlier_stage pX Dg cc
    (IsCofiltered.minToRight i i') x xi' δ' hδ'
  exact ⟨IsCofiltered.min i i', IsCofiltered.minToLeft i i', xk, δk, hδk⟩

/-- **Object descent for a two-fibre product.** If both factors satisfy object
descent and the common target has a full comparison functor, then so does the
two-fibre product. -/
private lemma descentObj_twoFibreProduct
    (pA : XA ⥤ C) (pM : XM ⥤ C) (pZ : XZ ⥤ C)
    [pA.IsFibered] [pM.IsFibered] [pZ.IsFibered]
    (hM : pM.IsFiberedInGroupoids)
    (F : XA ⥤ XM) (G : XZ ⥤ XM) (hF : F ⋙ pM = pA) (hG : G ⋙ pM = pZ)
    [IsCofiltered I] (Dg : I ⥤ C) (cc : Cone Dg)
    [(colimitComparison pM Dg cc).Full]
    (hAobj : DescentObj pA Dg cc) (hZobj : DescentObj pZ Dg cc) :
    DescentObj (TwoFibreProductOver.structureFunctor pA pZ pM F G) Dg cc := by
  intro W
  obtain ⟨⟨Wbase, Wx, Wy, Whx, Why, Wiso, Wvert⟩, hW⟩ := W
  change Wbase = cc.pt at hW
  subst hW
  let x₀ : pA.Fiber cc.pt := ⟨Wx, Whx⟩
  let z₀ : pZ.Fiber cc.pt := ⟨Wy, Why⟩
  obtain ⟨i₁, x₁, δ₁, hδ₁⟩ := hAobj x₀
  obtain ⟨k, s, z₁, δZ, hδZ⟩ := descentObj_at_stage pZ Dg cc hZobj z₀ i₁
  obtain ⟨xk, δX, hδX⟩ := homLift_at_earlier_stage pA Dg cc s x₀ x₁ δ₁ hδ₁
  let := hδX
  let := hδZ
  let : pM.IsHomLift (𝟙 cc.pt) Wiso.hom := Wvert
  let : pM.IsHomLift (cc.π.app k) (G.map δZ) :=
    Functor.isHomLift_map_of_comp_eq hG _ δZ
  let : pM.IsHomLift (cc.π.app k) (Wiso.hom ≫ G.map δZ) :=
    IsHomLift.comp_lift_id_left' pM cc.pt Wiso.hom (cc.π.app k) (G.map δZ)
  obtain ⟨k', t, xk', δk, γk, hδk, hγk, hcomm⟩ :=
    factor_through_stage pA pM hM F hF Dg cc k x₀ xk
      (⟨G.obj z₁.1, (Functor.congr_obj hG z₁.1).trans z₁.2⟩ : pM.Fiber (Dg.obj k))
      δX (Wiso.hom ≫ G.map δZ)
  let := hδk
  let := hγk
  let ff := Dg.map t
  let zk := Functor.pullbackFiber pZ z₁ ff
  let dZ := Functor.IsPreFibered.pullbackMap z₁.2 ff
  let δkZ := Functor.IsStronglyCartesian.map pZ ff dZ
    (g := cc.π.app k') (cc.w t).symm δZ
  let : pM.IsHomLift ff (G.map dZ) :=
    Functor.isHomLift_map_of_comp_eq hG ff dZ
  let : pM.IsStronglyCartesian ff (G.map dZ) :=
    hM.isStronglyCartesian_homLift _ _
  let αk := Functor.IsCartesian.map pM ff (G.map dZ) γk
  let : pM.IsHomLift (𝟙 (Dg.obj k')) αk := inferInstance
  let : pM.IsStronglyCartesian (𝟙 (Dg.obj k')) αk :=
    hM.isStronglyCartesian_homLift _ _
  let : IsIso αk := Functor.IsStronglyCartesian.isIso_of_base_isIso
    (p := pM) (f := 𝟙 (Dg.obj k')) αk
  let : pA.IsHomLift (cc.π.app k') δk := hδk
  let : pZ.IsHomLift (cc.π.app k') δkZ := inferInstance
  let : pM.IsHomLift (cc.π.app k') (F.map δk) :=
    Functor.isHomLift_map_of_comp_eq hF _ δk
  let : pM.IsHomLift (cc.π.app k') (G.map δkZ) :=
    Functor.isHomLift_map_of_comp_eq hG _ δkZ
  let : pM.IsHomLift (cc.π.app k') (Wiso.hom ≫ G.map δkZ) :=
    IsHomLift.comp_lift_id_left' pM cc.pt Wiso.hom _ _
  have hsquare : F.map δk ≫ αk = Wiso.hom ≫ G.map δkZ := by
    apply Functor.IsStronglyCartesian.ext pM ff (G.map dZ) (cc.π.app k')
    rw [Category.assoc, show αk ≫ G.map dZ = γk from
      Functor.IsCartesian.fac pM ff (G.map dZ) γk, hcomm, Category.assoc,
      ← G.map_comp, Functor.IsStronglyCartesian.fac]
  let Wk : TwoFibreProductOver pA pZ pM F G :=
    { base := Dg.obj k'
      x := xk'.1
      y := zk.1
      hx := xk'.2
      hy := zk.2
      iso := asIso αk
      vertical := by
        change pM.IsHomLift (𝟙 (Dg.obj k')) αk
        infer_instance }
  refine ⟨k', ⟨Wk, rfl⟩,
    { hbase := cc.π.app k'
      a := δk
      b := δkZ
      ha := hδk
      hb := inferInstance
      w := hsquare }, ?_⟩
  refine IsHomLift.of_fac' (TwoFibreProductOver.structureFunctor pA pZ pM F G)
    (cc.π.app k') _ rfl rfl ?_
  change cc.π.app k' = eqToHom rfl ≫ cc.π.app k' ≫ eqToHom rfl
  simp

/-- Two transitions into one stage are equalized by a single further stage. -/
private lemma exists_merge [IsCofiltered I] {k₁ k₂ i : I}
    (s₁ : k₁ ⟶ i) (s₂ : k₂ ⟶ i) :
    ∃ (k : I) (t₁ : k ⟶ k₁) (t₂ : k ⟶ k₂), t₁ ≫ s₁ = t₂ ≫ s₂ := by
  refine ⟨IsCofiltered.eq (IsCofiltered.minToLeft k₁ k₂ ≫ s₁)
      (IsCofiltered.minToRight k₁ k₂ ≫ s₂),
    IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToLeft k₁ k₂,
    IsCofiltered.eqHom _ _ ≫ IsCofiltered.minToRight k₁ k₂, ?_⟩
  simp only [Category.assoc]
  exact IsCofiltered.eq_condition _ _

/-- The components of a morphism of the two-fibre product over `g` lie over `g`. -/
private lemma isHomLift_fst_snd {pA : XA ⥤ C} {pM : XM ⥤ C} {pZ : XZ ⥤ C}
    {F : XA ⥤ XM} {G : XZ ⥤ XM} {P Q : TwoFibreProductOver pA pZ pM F G} {R T : C}
    (g : R ⟶ T) (Δ : P ⟶ Q)
    [(TwoFibreProductOver.structureFunctor pA pZ pM F G).IsHomLift g Δ] :
    pA.IsHomLift g Δ.a ∧ pZ.IsHomLift g Δ.b :=
  ⟨Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.fst_comp_eq _ Δ,
    Functor.isHomLift_map_of_comp_eq TwoFibreProductOver.snd_comp_eq _ Δ⟩

/-- A strongly cartesian lift of `f` in the two-fibre product, with strongly cartesian
components, whose source lies over the source of `f`. -/
private lemma exists_isStronglyCartesian_base {pA : XA ⥤ C} {pM : XM ⥤ C} {pZ : XZ ⥤ C}
    [pA.IsFibered] [pZ.IsFibered] {F : XA ⥤ XM} {G : XZ ⥤ XM}
    (hF : Functor.IsFibredOneMorphism pA pM F) (hG : Functor.IsFibredOneMorphism pZ pM G)
    (Q : TwoFibreProductOver pA pZ pM F G) {V : C} (f : V ⟶ Q.base) :
    ∃ (P : TwoFibreProductOver pA pZ pM F G) (Φ : P ⟶ Q),
      (TwoFibreProductOver.structureFunctor pA pZ pM F G).IsStronglyCartesian f Φ ∧
        pA.IsStronglyCartesian f Φ.a ∧ pZ.IsStronglyCartesian f Φ.b ∧ P.base = V := by
  obtain ⟨P, Φ, h, ha, hb⟩ := TwoFibreProductOver.exists_isStronglyCartesian hF hG Q f
  have := h.toIsHomLift
  exact ⟨P, Φ, h, ha, hb, IsHomLift.domain_eq
    (TwoFibreProductOver.structureFunctor pA pZ pM F G) f Φ⟩

/-- In a category fibred in groupoids, an equality of composites with one
morphism over a transition propagates to every morphism lying over a transition
factoring through it. -/
private lemma eq_comp_of_isHomLift' (pX : XA ⥤ C) [pX.IsFibered]
    (hX : pX.IsFiberedInGroupoids) {V W W' : C} (g : W ⟶ V) (r : W' ⟶ W)
    {t xk xk' bb : XA} (dx : xk ⟶ t) (hdx : pX.IsHomLift g dx) (d : xk' ⟶ t)
    (hd : pX.IsHomLift (r ≫ g) d) {ψ ψ' : t ⟶ bb}
    (hres : dx ≫ ψ = dx ≫ ψ') : d ≫ ψ = d ≫ ψ' := by
  let := hdx
  let := hd
  let : pX.IsStronglyCartesian g dx := hX.isStronglyCartesian_homLift g dx
  have hfac : Functor.IsStronglyCartesian.map pX g dx (g := r) rfl d ≫ dx = d :=
    Functor.IsStronglyCartesian.fac pX g dx _ d
  rw [← hfac, Category.assoc, Category.assoc, hres]

/-- **Descent of equalities for a two-fibre product.** If both factors satisfy
descent of equalities of vertical morphisms, then so does the two-fibre
product. -/
private lemma descentEq_twoFibreProduct
    (pA : XA ⥤ C) (pM : XM ⥤ C) (pZ : XZ ⥤ C)
    [pA.IsFibered] [pM.IsFibered] [pZ.IsFibered]
    (hA : pA.IsFiberedInGroupoids) (hM : pM.IsFiberedInGroupoids)
    (hZ : pZ.IsFiberedInGroupoids)
    (F : XA ⥤ XM) (G : XZ ⥤ XM) (hF : F ⋙ pM = pA) (hG : G ⋙ pM = pZ)
    [IsCofiltered I] (Dg : I ⥤ C) (cc : Cone Dg)
    (hAeq : DescentEq pA Dg cc) (hZeq : DescentEq pZ Dg cc) :
    DescentEq (TwoFibreProductOver.structureFunctor pA pZ pM F G) Dg cc := by
  have hFmor : Functor.IsFibredOneMorphism pA pM F := hM.isFibredOneMorphism hF
  have hGmor : Functor.IsFibredOneMorphism pZ pM G := hM.isFibredOneMorphism hG
  intro i Pi Qi X
  obtain ⟨⟨Pbase, Px, Py, Phx, Phy, Piso, Pvert⟩, hP⟩ := Pi
  change Pbase = Dg.obj i at hP
  subst hP
  obtain ⟨⟨Qbase, Qx, Qy, Qhx, Qhy, Qiso, Qvert⟩, hQ⟩ := Qi
  change Qbase = Dg.obj i at hQ
  subst hQ
  obtain ⟨⟨Xbase, Xx, Xy, Xhx, Xhy, Xiso, Xvert⟩, hX⟩ := X
  change Xbase = cc.pt at hX
  subst hX
  intro Δ hΔ Ψ Ψ' hΨ hΨ' hcomm
  let := hΔ
  let := hΨ
  let := hΨ'
  obtain ⟨hΔa, hΔb⟩ := isHomLift_fst_snd (cc.π.app i) Δ
  obtain ⟨hΨa, hΨb⟩ := isHomLift_fst_snd (𝟙 (Dg.obj i)) Ψ
  obtain ⟨hΨ'a, hΨ'b⟩ := isHomLift_fst_snd (𝟙 (Dg.obj i)) Ψ'
  have hca : Δ.a ≫ Ψ.a = Δ.a ≫ Ψ'.a := by
    rw [← TwoFibreProductOver.comp_a, ← TwoFibreProductOver.comp_a, hcomm]
  have hcb : Δ.b ≫ Ψ.b = Δ.b ≫ Ψ'.b := by
    rw [← TwoFibreProductOver.comp_b, ← TwoFibreProductOver.comp_b, hcomm]
  obtain ⟨kA, sA, xkA, dxA, hdxA, hresA⟩ := hAeq i ⟨Px, Phx⟩ ⟨Qx, Qhx⟩ ⟨Xx, Xhx⟩
    Δ.a hΔa Ψ.a Ψ'.a hΨa hΨ'a hca
  obtain ⟨kZ, sZ, zkZ, dzZ, hdzZ, hresZ⟩ := hZeq i ⟨Py, Phy⟩ ⟨Qy, Qhy⟩ ⟨Xy, Xhy⟩
    Δ.b hΔb Ψ.b Ψ'.b hΨb hΨ'b hcb
  obtain ⟨k, sA', sZ', hmerge⟩ := exists_merge sA sZ
  obtain ⟨Pk, dP, hdPsc, hdPa, hdPb, hPkb⟩ :=
    exists_isStronglyCartesian_base hFmor hGmor
      (⟨Dg.obj i, Px, Py, Phx, Phy, Piso, Pvert⟩ :
        TwoFibreProductOver pA pZ pM F G) (Dg.map (sA' ≫ sA))
  refine ⟨k, sA' ≫ sA, ⟨Pk, hPkb⟩, dP, hdPsc.toIsHomLift, ?_⟩
  refine TwoFibreProductOver.Hom.ext' ?_ ?_
  · refine eq_comp_of_isHomLift' pA hA (Dg.map sA) (Dg.map sA') dxA hdxA dP.a
      ?_ hresA
    rw [← Dg.map_comp]
    exact hdPa.toIsHomLift
  · refine eq_comp_of_isHomLift' pZ hZ (Dg.map sZ) (Dg.map sZ') dzZ hdzZ dP.b
      ?_ hresZ
    rw [← Dg.map_comp, ← hmerge]
    exact hdPb.toIsHomLift

/-- **Descent of vertical morphisms for a two-fibre product.** If both factors
satisfy descent of vertical morphisms and the common target satisfies descent of
equalities, then the two-fibre product satisfies descent of vertical
morphisms. -/
private lemma descentHom_twoFibreProduct
    (pA : XA ⥤ C) (pM : XM ⥤ C) (pZ : XZ ⥤ C)
    [pA.IsFibered] [pM.IsFibered] [pZ.IsFibered]
    (hA : pA.IsFiberedInGroupoids) (hM : pM.IsFiberedInGroupoids)
    (hZ : pZ.IsFiberedInGroupoids)
    (F : XA ⥤ XM) (G : XZ ⥤ XM) (hF : F ⋙ pM = pA) (hG : G ⋙ pM = pZ)
    [IsCofiltered I] (Dg : I ⥤ C) (cc : Cone Dg)
    (hAhom : DescentHom pA Dg cc) (hZhom : DescentHom pZ Dg cc)
    (hMeq : DescentEq pM Dg cc) :
    DescentHom (TwoFibreProductOver.structureFunctor pA pZ pM F G) Dg cc := by
  have hFmor : Functor.IsFibredOneMorphism pA pM F := hM.isFibredOneMorphism hF
  have hGmor : Functor.IsFibredOneMorphism pZ pM G := hM.isFibredOneMorphism hG
  intro i Pi Qi X Y
  obtain ⟨⟨Pbase, Px, Py, Phx, Phy, Piso, Pvert⟩, hP⟩ := Pi
  change Pbase = Dg.obj i at hP
  subst hP
  obtain ⟨⟨Qbase, Qx, Qy, Qhx, Qhy, Qiso, Qvert⟩, hQ⟩ := Qi
  change Qbase = Dg.obj i at hQ
  subst hQ
  obtain ⟨⟨Xbase, Xx, Xy, Xhx, Xhy, Xiso, Xvert⟩, hXb⟩ := X
  change Xbase = cc.pt at hXb
  subst hXb
  obtain ⟨⟨Ybase, Yx, Yy, Yhx, Yhy, Yiso, Yvert⟩, hYb⟩ := Y
  change Ybase = cc.pt at hYb
  subst hYb
  intro Δ Ε hΔ hΕ Φ hΦ
  let := hΔ
  let := hΕ
  let := hΦ
  obtain ⟨hΔa, hΔb⟩ := isHomLift_fst_snd (cc.π.app i) Δ
  obtain ⟨hΕa, hΕb⟩ := isHomLift_fst_snd (cc.π.app i) Ε
  obtain ⟨hΦa, hΦb⟩ := isHomLift_fst_snd (𝟙 cc.pt) Φ
  obtain ⟨kA, sA, xkA, ykA, dxA, dyA, δkA, ψA, hdxA, hdyA, hδkA, hψA, eA1, eA2⟩ :=
    hAhom i ⟨Px, Phx⟩ ⟨Qx, Qhx⟩ ⟨Xx, Xhx⟩ ⟨Yx, Yhx⟩ Δ.a Ε.a hΔa hΕa Φ.a hΦa
  obtain ⟨kZ, sZ, xkZ, ykZ, dxZ, dyZ, δkZ, ψZ, hdxZ, hdyZ, hδkZ, hψZ, eZ1, eZ2⟩ :=
    hZhom i ⟨Py, Phy⟩ ⟨Qy, Qhy⟩ ⟨Xy, Xhy⟩ ⟨Yy, Yhy⟩ Δ.b Ε.b hΔb hΕb Φ.b hΦb
  obtain ⟨k₀, tA, tZ, hmerge⟩ := exists_merge sA sZ
  obtain ⟨Pk, dP, hdPsc, hdPa, hdPb, hPkb⟩ :=
    exists_isStronglyCartesian_base hFmor hGmor
      (⟨Dg.obj i, Px, Py, Phx, Phy, Piso, Pvert⟩ :
        TwoFibreProductOver pA pZ pM F G) (Dg.map (tA ≫ sA))
  obtain ⟨Qk, dQ, hdQsc, hdQa, hdQb, hQkb⟩ :=
    exists_isStronglyCartesian_base hFmor hGmor
      (⟨Dg.obj i, Qx, Qy, Qhx, Qhy, Qiso, Qvert⟩ :
        TwoFibreProductOver pA pZ pM F G) (Dg.map (tA ≫ sA))
  obtain ⟨PKb, PKx, PKy, PKhx, PKhy, PKiso, PKvert⟩ := Pk
  subst hPkb
  obtain ⟨QKb, QKx, QKy, QKhx, QKhy, QKiso, QKvert⟩ := Qk
  subst hQkb
  let := hdPa
  let := hdPb
  let := hdQa
  let := hdQb
  let := hdxA
  let := hdyA
  let := hδkA
  let := hψA
  let := hdxZ
  let := hdyZ
  let := hδkZ
  let := hψZ
  let : pA.IsStronglyCartesian (Dg.map sA) dxA :=
    hA.isStronglyCartesian_homLift _ _
  let : pA.IsStronglyCartesian (Dg.map sA) dyA :=
    hA.isStronglyCartesian_homLift _ _
  let : pZ.IsStronglyCartesian (Dg.map sZ) dxZ :=
    hZ.isStronglyCartesian_homLift _ _
  let : pZ.IsStronglyCartesian (Dg.map sZ) dyZ :=
    hZ.isStronglyCartesian_homLift _ _
  have hst : Dg.map (tA ≫ sA) = Dg.map tA ≫ Dg.map sA := Dg.map_comp tA sA
  have hstZ : Dg.map (tA ≫ sA) = Dg.map tZ ≫ Dg.map sZ := by
    rw [hmerge, Dg.map_comp]
  -- the comparison maps to the stage representatives of the two descents
  set χa := Functor.IsStronglyCartesian.map pA (Dg.map sA) dxA
    (g := Dg.map tA) hst dP.a with hχadef
  have hχafac : χa ≫ dxA = dP.a :=
    Functor.IsStronglyCartesian.fac pA (Dg.map sA) dxA hst dP.a
  set χb := Functor.IsStronglyCartesian.map pZ (Dg.map sZ) dxZ
    (g := Dg.map tZ) hstZ dP.b with hχbdef
  have hχbfac : χb ≫ dxZ = dP.b :=
    Functor.IsStronglyCartesian.fac pZ (Dg.map sZ) dxZ hstZ dP.b
  -- the descended vertical morphisms at the merged stage
  have hcompA : pA.IsHomLift (Dg.map (tA ≫ sA)) (χa ≫ ψA ≫ dyA) := by
    let : pA.IsHomLift (Dg.map sA) (ψA ≫ dyA) :=
      IsHomLift.comp_lift_id_left' pA (Dg.obj kA) ψA (Dg.map sA) dyA
    rw [hst]
    infer_instance
  have hcompZ : pZ.IsHomLift (Dg.map (tA ≫ sA)) (χb ≫ ψZ ≫ dyZ) := by
    let : pZ.IsHomLift (Dg.map sZ) (ψZ ≫ dyZ) :=
      IsHomLift.comp_lift_id_left' pZ (Dg.obj kZ) ψZ (Dg.map sZ) dyZ
    rw [hstZ]
    infer_instance
  let := hcompA
  let := hcompZ
  set Ψa := Functor.IsStronglyCartesian.map pA (Dg.map (tA ≫ sA)) dQ.a
    (g := 𝟙 (Dg.obj k₀)) (Category.id_comp _).symm (χa ≫ ψA ≫ dyA) with hΨadef
  have hΨafac : Ψa ≫ dQ.a = χa ≫ ψA ≫ dyA :=
    Functor.IsStronglyCartesian.fac pA (Dg.map (tA ≫ sA)) dQ.a _ _
  set Ψb := Functor.IsStronglyCartesian.map pZ (Dg.map (tA ≫ sA)) dQ.b
    (g := 𝟙 (Dg.obj k₀)) (Category.id_comp _).symm (χb ≫ ψZ ≫ dyZ) with hΨbdef
  have hΨbfac : Ψb ≫ dQ.b = χb ≫ ψZ ≫ dyZ :=
    Functor.IsStronglyCartesian.fac pZ (Dg.map (tA ≫ sA)) dQ.b _ _
  -- the factorisations of the given data through the merged stage
  let : (TwoFibreProductOver.structureFunctor pA pZ pM F G).IsHomLift
      (𝟙 cc.pt ≫ cc.π.app i) (Φ ≫ Ε) := inferInstance
  let : (TwoFibreProductOver.structureFunctor pA pZ pM F G).IsHomLift
      (cc.π.app i) (Φ ≫ Ε) := by
    simpa using
      (inferInstance : (TwoFibreProductOver.structureFunctor pA pZ pM F G).IsHomLift
        (𝟙 cc.pt ≫ cc.π.app i) (Φ ≫ Ε))
  let := hdPsc
  let := hdQsc
  set Δk := Functor.IsStronglyCartesian.map
    (TwoFibreProductOver.structureFunctor pA pZ pM F G) (Dg.map (tA ≫ sA)) dP
    (g := cc.π.app k₀) (cc.w (tA ≫ sA)).symm Δ with hΔkdef
  have hΔkfac : Δk ≫ dP = Δ :=
    Functor.IsStronglyCartesian.fac
      (TwoFibreProductOver.structureFunctor pA pZ pM F G) (Dg.map (tA ≫ sA))
      dP _ Δ
  set Θ := Functor.IsStronglyCartesian.map
    (TwoFibreProductOver.structureFunctor pA pZ pM F G) (Dg.map (tA ≫ sA)) dQ
    (g := cc.π.app k₀) (cc.w (tA ≫ sA)).symm (Φ ≫ Ε) with hΘdef
  have hΘfac : Θ ≫ dQ = Φ ≫ Ε :=
    Functor.IsStronglyCartesian.fac
      (TwoFibreProductOver.structureFunctor pA pZ pM F G) (Dg.map (tA ≫ sA))
      dQ _ (Φ ≫ Ε)
  have hΔklift : (TwoFibreProductOver.structureFunctor pA pZ pM F G).IsHomLift
      (cc.π.app k₀) Δk := by
    rw [hΔkdef]
    infer_instance
  let := hΔklift
  obtain ⟨hΔka, hΔkb⟩ := isHomLift_fst_snd (cc.π.app k₀) Δk
  obtain ⟨hΘa, hΘb⟩ := isHomLift_fst_snd (cc.π.app k₀) Θ
  let := hΔka
  let := hΔkb
  -- the factorisation of the descent data agrees with the chosen one
  have hΔkχa : Δk.a ≫ χa = δkA := by
    let : pA.IsHomLift (cc.π.app kA) (Δk.a ≫ χa) := by
      rw [← cc.w tA]
      exact inferInstance
    refine Functor.IsStronglyCartesian.ext pA (Dg.map sA) dxA (cc.π.app kA) ?_
    rw [Category.assoc, hχafac, eA1]
    exact congrArg TwoFibreProductOver.Hom.a hΔkfac
  have hΔkχb : Δk.b ≫ χb = δkZ := by
    let : pZ.IsHomLift (cc.π.app kZ) (Δk.b ≫ χb) := by
      rw [← cc.w tZ]
      exact inferInstance
    refine Functor.IsStronglyCartesian.ext pZ (Dg.map sZ) dxZ (cc.π.app kZ) ?_
    rw [Category.assoc, hχbfac, eZ1]
    exact congrArg TwoFibreProductOver.Hom.b hΔkfac
  have hΔkΨa : Δk.a ≫ Ψa = Θ.a := by
    refine Functor.IsStronglyCartesian.ext pA (Dg.map (tA ≫ sA)) dQ.a
      (cc.π.app k₀) ?_
    rw [Category.assoc, hΨafac, ← Category.assoc, hΔkχa, eA2]
    exact (congrArg TwoFibreProductOver.Hom.a hΘfac).symm
  have hΔkΨb : Δk.b ≫ Ψb = Θ.b := by
    refine Functor.IsStronglyCartesian.ext pZ (Dg.map (tA ≫ sA)) dQ.b
      (cc.π.app k₀) ?_
    rw [Category.assoc, hΨbfac, ← Category.assoc, hΔkχb, eZ2]
    exact (congrArg TwoFibreProductOver.Hom.b hΘfac).symm
  -- the comparison square holds after one more stage, by equality descent
  let : pA.IsHomLift (𝟙 (Dg.obj k₀)) Ψa := by rw [hΨadef]; infer_instance
  let : pZ.IsHomLift (𝟙 (Dg.obj k₀)) Ψb := by rw [hΨbdef]; infer_instance
  let : pM.IsHomLift (𝟙 (Dg.obj k₀)) (F.map Ψa) := hFmor.map_isHomLift _ _
  let : pM.IsHomLift (𝟙 (Dg.obj k₀)) (G.map Ψb) := hGmor.map_isHomLift _ _
  let : pM.IsHomLift (cc.π.app k₀) (F.map Δk.a) := hFmor.map_isHomLift _ _
  let : pM.IsHomLift (𝟙 (Dg.obj k₀)) (F.map Ψa ≫ QKiso.hom) :=
    IsHomLift.comp_of_lift_id pM (Dg.obj k₀) (F.map Ψa) QKiso.hom
  let : pM.IsHomLift (𝟙 (Dg.obj k₀)) (PKiso.hom ≫ G.map Ψb) :=
    IsHomLift.comp_of_lift_id pM (Dg.obj k₀) PKiso.hom (G.map Ψb)
  have hsq0 : F.map Δk.a ≫ F.map Ψa ≫ QKiso.hom =
      F.map Δk.a ≫ PKiso.hom ≫ G.map Ψb := by
    rw [← Category.assoc, ← F.map_comp, hΔkΨa, Θ.w, ← Category.assoc, Δk.w,
      Category.assoc, ← G.map_comp, hΔkΨb]
  obtain ⟨k₁, r, mk₁, dm, hdm, hresM⟩ :=
    hMeq k₀ ⟨F.obj PKx, (Functor.congr_obj hF PKx).trans PKhx⟩
      ⟨G.obj QKy, (Functor.congr_obj hG QKy).trans QKhy⟩
      ⟨F.obj Xx, (Functor.congr_obj hF Xx).trans Xhx⟩ (F.map Δk.a) inferInstance
      (F.map Ψa ≫ QKiso.hom) (PKiso.hom ≫ G.map Ψb) inferInstance inferInstance
      hsq0
  obtain ⟨Pk₁, ρ, hρsc, hρa, hρb, hPk₁b⟩ :=
    exists_isStronglyCartesian_base hFmor hGmor
      (⟨Dg.obj k₀, PKx, PKy, PKhx, PKhy, PKiso, PKvert⟩ :
        TwoFibreProductOver pA pZ pM F G) (Dg.map r)
  obtain ⟨Qk₁, σ, hσsc, hσa, hσb, hQk₁b⟩ :=
    exists_isStronglyCartesian_base hFmor hGmor
      (⟨Dg.obj k₀, QKx, QKy, QKhx, QKhy, QKiso, QKvert⟩ :
        TwoFibreProductOver pA pZ pM F G) (Dg.map r)
  let := hρsc
  let := hσsc
  let := hρa
  let := hρb
  let := hσa
  let := hσb
  let : pA.IsHomLift (Dg.map r) (ρ.a ≫ Ψa) := inferInstance
  let : pZ.IsHomLift (Dg.map r) (ρ.b ≫ Ψb) := inferInstance
  set Ψ'a := Functor.IsStronglyCartesian.map pA (Dg.map r) σ.a
    (g := 𝟙 (Dg.obj k₁)) (Category.id_comp _).symm (ρ.a ≫ Ψa) with hΨ'adef
  have hΨ'afac : Ψ'a ≫ σ.a = ρ.a ≫ Ψa :=
    Functor.IsStronglyCartesian.fac pA (Dg.map r) σ.a _ _
  set Ψ'b := Functor.IsStronglyCartesian.map pZ (Dg.map r) σ.b
    (g := 𝟙 (Dg.obj k₁)) (Category.id_comp _).symm (ρ.b ≫ Ψb) with hΨ'bdef
  have hΨ'bfac : Ψ'b ≫ σ.b = ρ.b ≫ Ψb :=
    Functor.IsStronglyCartesian.fac pZ (Dg.map r) σ.b _ _
  let : pA.IsHomLift (𝟙 (Dg.obj k₁)) Ψ'a := by rw [hΨ'adef]; infer_instance
  let : pZ.IsHomLift (𝟙 (Dg.obj k₁)) Ψ'b := by rw [hΨ'bdef]; infer_instance
  let : pM.IsHomLift (𝟙 (Dg.obj k₁)) (F.map Ψ'a) := hFmor.map_isHomLift _ _
  let : pM.IsHomLift (𝟙 (Dg.obj k₁)) (G.map Ψ'b) := hGmor.map_isHomLift _ _
  let : pM.IsHomLift (𝟙 (Dg.obj k₁)) Qk₁.iso.hom := hQk₁b ▸ Qk₁.vertical
  let : pM.IsHomLift (𝟙 (Dg.obj k₁)) Pk₁.iso.hom := hPk₁b ▸ Pk₁.vertical
  let : pM.IsStronglyCartesian (Dg.map r) (G.map σ.b) :=
    hGmor.map_isStronglyCartesian _ _ hσb
  let : pM.IsHomLift (Dg.map r) (F.map ρ.a) := hFmor.map_isHomLift _ _
  have hdmres : F.map ρ.a ≫ F.map Ψa ≫ QKiso.hom =
      F.map ρ.a ≫ PKiso.hom ≫ G.map Ψb := by
    refine eq_comp_of_isHomLift' pM hM (Dg.map r) (𝟙 (Dg.obj k₁)) dm hdm
      (F.map ρ.a) ?_ hresM
    rw [Category.id_comp]
    infer_instance
  have hsq1 : F.map Ψ'a ≫ Qk₁.iso.hom = Pk₁.iso.hom ≫ G.map Ψ'b := by
    let : pM.IsHomLift (𝟙 (Dg.obj k₁)) (F.map Ψ'a ≫ Qk₁.iso.hom) :=
      IsHomLift.comp_of_lift_id pM (Dg.obj k₁) (F.map Ψ'a) Qk₁.iso.hom
    let : pM.IsHomLift (𝟙 (Dg.obj k₁)) (Pk₁.iso.hom ≫ G.map Ψ'b) :=
      IsHomLift.comp_of_lift_id pM (Dg.obj k₁) Pk₁.iso.hom (G.map Ψ'b)
    refine Functor.IsStronglyCartesian.ext pM (Dg.map r) (G.map σ.b)
      (𝟙 (Dg.obj k₁)) ?_
    have hL : (F.map Ψ'a ≫ Qk₁.iso.hom) ≫ G.map σ.b =
        F.map ρ.a ≫ F.map Ψa ≫ QKiso.hom := by
      rw [Category.assoc, ← σ.w, ← Category.assoc, ← F.map_comp, hΨ'afac,
        F.map_comp, Category.assoc]
    have hR : (Pk₁.iso.hom ≫ G.map Ψ'b) ≫ G.map σ.b =
        F.map ρ.a ≫ PKiso.hom ≫ G.map Ψb := by
      rw [Category.assoc, ← G.map_comp, hΨ'bfac, G.map_comp,
        ← Category.assoc, ← ρ.w, Category.assoc]
    rw [hL, hR]
    exact hdmres
  set Ψ' := TwoFibreProductOver.Hom.mk' Ψ'a Ψ'b (by
    rw [IsHomLift.fac' pA (𝟙 (Dg.obj k₁)) Ψ'a,
      IsHomLift.fac' pZ (𝟙 (Dg.obj k₁)) Ψ'b]
    simp) hsq1 with hΨ'def
  have hΨ'lift : (TwoFibreProductOver.structureFunctor pA pZ pM F G).IsHomLift
      (𝟙 (Dg.obj k₁)) Ψ' := by
    refine IsHomLift.of_fac'
      (TwoFibreProductOver.structureFunctor pA pZ pM F G) (𝟙 (Dg.obj k₁)) Ψ'
      hPk₁b hQk₁b ?_
    change Ψ'.hbase = eqToHom hPk₁b ≫ 𝟙 (Dg.obj k₁) ≫ eqToHom hQk₁b.symm
    rw [hΨ'def, TwoFibreProductOver.Hom.mk'_hbase,
      IsHomLift.fac' pA (𝟙 (Dg.obj k₁)) Ψ'a]
    simp
  -- the final factorisation
  have hrs : Dg.map (r ≫ tA ≫ sA) = Dg.map r ≫ Dg.map (tA ≫ sA) :=
    Dg.map_comp r (tA ≫ sA)
  let : (TwoFibreProductOver.structureFunctor pA pZ pM F G).IsStronglyCartesian
      (Dg.map r ≫ Dg.map (tA ≫ sA)) (ρ ≫ dP) := inferInstance
  set Δk' := Functor.IsStronglyCartesian.map
    (TwoFibreProductOver.structureFunctor pA pZ pM F G)
    (Dg.map r ≫ Dg.map (tA ≫ sA)) (ρ ≫ dP) (g := cc.π.app k₁)
    (by rw [← hrs, cc.w (r ≫ tA ≫ sA)]) Δ with hΔk'def
  have hΔk'fac : Δk' ≫ ρ ≫ dP = Δ :=
    Functor.IsStronglyCartesian.fac
      (TwoFibreProductOver.structureFunctor pA pZ pM F G)
      (Dg.map r ≫ Dg.map (tA ≫ sA)) (ρ ≫ dP) _ Δ
  have hΔk'lift : (TwoFibreProductOver.structureFunctor pA pZ pM F G).IsHomLift
      (cc.π.app k₁) Δk' := by rw [hΔk'def]; infer_instance
  let := hΔk'lift
  obtain ⟨hΔk'a, hΔk'b⟩ := isHomLift_fst_snd (cc.π.app k₁) Δk'
  let := hΔk'a
  let := hΔk'b
  let : pA.IsStronglyCartesian (Dg.map (tA ≫ sA)) dP.a := hdPa
  have hΔk'ρa : Δk'.a ≫ ρ.a = Δk.a := by
    let : pA.IsHomLift (cc.π.app k₀) (Δk'.a ≫ ρ.a) := by
      rw [← cc.w r]
      exact inferInstance
    refine Functor.IsStronglyCartesian.ext pA (Dg.map (tA ≫ sA)) dP.a
      (cc.π.app k₀) ?_
    rw [Category.assoc]
    have h1 : Δk'.a ≫ ρ.a ≫ dP.a = Δ.a :=
      congrArg TwoFibreProductOver.Hom.a hΔk'fac
    have h2 : Δk.a ≫ dP.a = Δ.a := congrArg TwoFibreProductOver.Hom.a hΔkfac
    rw [h1, h2]
  have hΔk'ρb : Δk'.b ≫ ρ.b = Δk.b := by
    let : pZ.IsHomLift (cc.π.app k₀) (Δk'.b ≫ ρ.b) := by
      rw [← cc.w r]
      exact inferInstance
    refine Functor.IsStronglyCartesian.ext pZ (Dg.map (tA ≫ sA)) dP.b
      (cc.π.app k₀) ?_
    rw [Category.assoc]
    have h1 : Δk'.b ≫ ρ.b ≫ dP.b = Δ.b :=
      congrArg TwoFibreProductOver.Hom.b hΔk'fac
    have h2 : Δk.b ≫ dP.b = Δ.b := congrArg TwoFibreProductOver.Hom.b hΔkfac
    rw [h1, h2]
  refine ⟨k₁, r ≫ tA ≫ sA, ⟨Pk₁, hPk₁b⟩, ⟨Qk₁, hQk₁b⟩, ρ ≫ dP, σ ≫ dQ, Δk',
    Ψ', ?_, ?_, hΔk'lift, hΨ'lift, hΔk'fac, ?_⟩
  · rw [hrs]
    exact (inferInstance :
      (TwoFibreProductOver.structureFunctor pA pZ pM F G).IsStronglyCartesian
        (Dg.map r ≫ Dg.map (tA ≫ sA)) (ρ ≫ dP)).toIsHomLift
  · rw [hrs]
    exact (inferInstance :
      (TwoFibreProductOver.structureFunctor pA pZ pM F G).IsStronglyCartesian
        (Dg.map r ≫ Dg.map (tA ≫ sA)) (σ ≫ dQ)).toIsHomLift
  · refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · change Δk'.a ≫ Ψ'a ≫ σ.a ≫ dQ.a = Φ.a ≫ Ε.a
      rw [← Category.assoc Ψ'a σ.a, hΨ'afac, ← Category.assoc,
        ← Category.assoc, hΔk'ρa, hΔkΨa]
      exact congrArg TwoFibreProductOver.Hom.a hΘfac
    · change Δk'.b ≫ Ψ'b ≫ σ.b ≫ dQ.b = Φ.b ≫ Ε.b
      rw [← Category.assoc Ψ'b σ.b, hΨ'bfac, ← Category.assoc,
        ← Category.assoc, hΔk'ρb, hΔkΨb]
      exact congrArg TwoFibreProductOver.Hom.b hΘfac

end TwoFibreDescent

end Deformation.Artin

namespace AlgebraicGeometry.Stack

universe u v w

section Main

attribute [local implicit_reducible] Bicategory.InducedBicategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (pf : 𝒳 ⟶ 𝒴) (qf : 𝒵 ⟶ 𝒴)

/-- **Stacks 07XM, part (2).** If `𝒳`, `𝒴` and `𝒵` are limit preserving categories fibred in
groupoids over `(Sch/S)_{fppf}`, then so is the 2-fibre product `𝒳 ×_𝒴 𝒵`: for every directed
inverse system of affine schemes with limit `T`, the canonical comparison from the colimit of the
fibre categories over the stages to the fibre category over `T` is an equivalence. -/
@[stacks 07XM "part (2)"]
theorem isLimitPreserving_twoFibreProduct
    (h𝒳 : Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS 𝒳)
    (h𝒴 : Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS 𝒴)
    (h𝒵 : Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS 𝒵) :
    Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS
      (BigFppfOver.twoFibreProduct.{u, u, u + 1} B S hS 𝒳 𝒴 𝒵 pf qf) := by
  intro I instI hI D c hc
  have hXc := h𝒳 I D c hc
  have hYc := h𝒴 I D c hc
  have hZc := h𝒵 I D c hc
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  let : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  let : 𝒵.val.p.IsFibered := 𝒵.isFiberedInGroupoids.isFibered
  let := hXc
  let := hYc
  let := hZc
  let Fp := CatFiberedInGroupoids.homFunctor pf
  let Gq := CatFiberedInGroupoids.homFunctor qf
  have hFcomp : Fp ⋙ 𝒴.val.p = 𝒳.val.p := CatFiberedInGroupoids.homFunctor_comp_p pf
  have hGcomp : Gq ⋙ 𝒴.val.p = 𝒵.val.p := CatFiberedInGroupoids.homFunctor_comp_p qf
  have hAobj : Deformation.Artin.DescentObj 𝒳.val.p
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) :=
    Deformation.Artin.descentObj_of_essSurj 𝒳.val.p _ _
  have hZobj : Deformation.Artin.DescentObj 𝒵.val.p
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) :=
    Deformation.Artin.descentObj_of_essSurj 𝒵.val.p _ _
  have hAhom : Deformation.Artin.DescentHom 𝒳.val.p
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) :=
    Deformation.Artin.descentHom_of_full 𝒳.val.p 𝒳.isFiberedInGroupoids _ _
  have hZhom : Deformation.Artin.DescentHom 𝒵.val.p
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) :=
    Deformation.Artin.descentHom_of_full 𝒵.val.p 𝒵.isFiberedInGroupoids _ _
  have hAeq : Deformation.Artin.DescentEq 𝒳.val.p
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) :=
    Deformation.Artin.descentEq_of_faithful 𝒳.val.p 𝒳.isFiberedInGroupoids _ _
  have hZeq : Deformation.Artin.DescentEq 𝒵.val.p
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) :=
    Deformation.Artin.descentEq_of_faithful 𝒵.val.p 𝒵.isFiberedInGroupoids _ _
  have hMeq : Deformation.Artin.DescentEq 𝒴.val.p
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) :=
    Deformation.Artin.descentEq_of_faithful 𝒴.val.p 𝒴.isFiberedInGroupoids _ _
  have hP : Functor.IsFiberedInGroupoids
      (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p Fp Gq) :=
    TwoFibreProductOver.isFiberedInGroupoids 𝒳.val.p 𝒵.val.p 𝒴.val.p Fp Gq
      𝒳.isFiberedInGroupoids 𝒵.isFiberedInGroupoids 𝒴.isFiberedInGroupoids hFcomp hGcomp
  have hfibT : Functor.IsFibered
      (BigFppfOver.twoFibreProduct.{u, u, u + 1} B S hS 𝒳 𝒴 𝒵 pf qf).val.p :=
    (BigFppfOver.twoFibreProduct.{u, u, u + 1} B S hS 𝒳 𝒴 𝒵
      pf qf).isFiberedInGroupoids.isFibered
  have hfibP : Functor.IsFibered
      (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p Fp Gq) := hP.isFibered
  have hPobj : Deformation.Artin.DescentObj
      (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p Fp Gq)
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) :=
    Deformation.Artin.descentObj_twoFibreProduct 𝒳.val.p 𝒴.val.p 𝒵.val.p
      𝒴.isFiberedInGroupoids Fp Gq hFcomp hGcomp _ _ hAobj hZobj
  have hPhom : Deformation.Artin.DescentHom
      (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p Fp Gq)
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) :=
    Deformation.Artin.descentHom_twoFibreProduct 𝒳.val.p 𝒴.val.p 𝒵.val.p
      𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids 𝒵.isFiberedInGroupoids
      Fp Gq hFcomp hGcomp _ _ hAhom hZhom hMeq
  have hPeq : Deformation.Artin.DescentEq
      (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p Fp Gq)
      (D ⋙ BigAffineFppf.inclusion B S hS)
      ((BigAffineFppf.inclusion B S hS).mapCone c) :=
    Deformation.Artin.descentEq_twoFibreProduct 𝒳.val.p 𝒴.val.p 𝒵.val.p
      𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids 𝒵.isFiberedInGroupoids
      Fp Gq hFcomp hGcomp _ _ hAeq hZeq
  exact ⟨Deformation.Artin.faithful_of_descentEq _ hP _ _ hPeq,
    Deformation.Artin.full_of_descentHom _ hP _ _ hPhom,
    Deformation.Artin.essSurj_of_descentObj _ hP _ _ hPobj⟩

end Main

end AlgebraicGeometry.Stack

end
