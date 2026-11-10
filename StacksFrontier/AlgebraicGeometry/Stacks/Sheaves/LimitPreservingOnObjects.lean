module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Cones
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.FiberedCategory.ChoiceOfPullbacks
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct

/-!
# Limit preserving on objects

A morphism of categories fibred in groupoids over the big fppf category of a scheme is limit
preserving on objects when every object over an affine inverse limit, equipped with a cartesian
comparison to an object at a finite stage, descends to some later stage, compatibly with the
original comparison.

This file states that condition and proves its two stability properties: it is preserved by
base change along the 2-fibre product, and it is stable under composition.

## Main definitions

* `AlgebraicGeometry.BigFppfOver.IsLimitPreservingOnObjects`: the descent property together
  with its commuting comparison square.
* `AlgebraicGeometry.BigFppfOver.twoFibreProduct`: the 2-fibre product of two morphisms with a
  common target, as a category fibred in groupoids over the big fppf category.
* `AlgebraicGeometry.BigFppfOver.twoFibreProductSnd`: its projection to the second factor.

## Main results

* `AlgebraicGeometry.BigFppfOver.isLimitPreservingOnObjects_baseChange`: limit preservation on
  objects is stable under base change.
* `AlgebraicGeometry.BigFppfOver.isLimitPreservingOnObjects_comp`: limit preservation on
  objects is stable under composition.

## Implementation notes

Cartesian arrows express the source's restriction isomorphisms without choosing pullback
functors. The final equality is precisely the commutative square of Stacks 06CU, composed with
the cartesian maps to the original stage. A cone whose image in schemes is limiting represents
the affine inverse limit.

The 2-fibre product uses vertical comparison isomorphisms, as required for categories fibred in
groupoids over a fixed base, and the projection is the canonical second projection rather than
a chosen equivalent functor.

## References

* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
* [Stacks Project, Tag 06CV](https://stacks.math.columbia.edu/tag/06CV)
* [Stacks Project, Tag 06CW](https://stacks.math.columbia.edu/tag/06CW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.BigFppfOver

universe u v w

/-- **Stacks 06CU.** A morphism of categories fibred in groupoids is limit preserving on
objects: every comparison over an affine inverse limit descends, with the comparison square
commuting. -/
@[stacks 06CU]
def IsLimitPreservingOnObjects
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 : CatFiberedInGroupoids (BigFppfOver B S hS)) (p : 𝒳 ⟶ 𝒴) : Prop :=
  ∀ (I : Type v) [Category.{w} I] [IsCofiltered I]
    (D : I ⥤ BigAffineFppf B S hS) (c : Cone D),
    IsLimit ((BigAffineFppf.toScheme B S hS).mapCone c) →
    ∀ (i : I) (y : 𝒴.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj i)))
      (x : 𝒳.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt))
      (γ : (CatFiberedInGroupoids.homFunctor p).obj x.1 ⟶ y.1),
      𝒴.val.p.IsStronglyCartesian
        ((BigAffineFppf.inclusion B S hS).map (c.π.app i)) γ →
      ∃ (i' : I) (j : i' ⟶ i)
        (x' : 𝒳.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj (D.obj i')))
        (xU : 𝒳.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt))
        (δ : xU.1 ⟶ x'.1) (β : xU.1 ⟶ x.1)
        (γ' : (CatFiberedInGroupoids.homFunctor p).obj x'.1 ⟶ y.1),
        𝒳.val.p.IsStronglyCartesian
          ((BigAffineFppf.inclusion B S hS).map (c.π.app i')) δ ∧
        𝒳.val.p.IsHomLift
          (𝟙 ((BigAffineFppf.inclusion B S hS).obj c.pt)) β ∧ IsIso β ∧
        𝒴.val.p.IsStronglyCartesian
          ((BigAffineFppf.inclusion B S hS).map (D.map j)) γ' ∧
        (CatFiberedInGroupoids.homFunctor p).map δ ≫ γ' =
          (CatFiberedInGroupoids.homFunctor p).map β ≫ γ

/-- A 1-morphism of categories fibred in groupoids preserves the object of the base lying under
an object. -/
private theorem proj_homFunctor_obj {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {𝒳 𝒴 : CatFiberedInGroupoids (BigFppfOver B S hS)} (p : 𝒳 ⟶ 𝒴) {U : BigFppfOver B S hS}
    (x : 𝒳.val.p.Fiber U) : 𝒴.val.p.obj ((CatFiberedInGroupoids.homFunctor p).obj x.1) = U :=
  (Functor.congr_obj (CatFiberedInGroupoids.homFunctor_comp_p p) x.1).trans x.2

section BaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 𝒴 𝒵 : CatFiberedInGroupoids.{u, max u v, u + 1, max (u + 1) v w}
  (BigFppfOver B S hS))
variable (p : 𝒳 ⟶ 𝒴) (q : 𝒵 ⟶ 𝒴)

/-- The base change of `p` along `q`, formed as a 2-fibre product over the base site. -/
def twoFibreProduct : CatFiberedInGroupoids (BigFppfOver B S hS) :=
  CatFiberedInGroupoids.mk
    (BasedCategory.ofFunctor
      (TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)))
    (TwoFibreProductOver.isFiberedInGroupoids 𝒳.val.p 𝒵.val.p 𝒴.val.p
      (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
      𝒳.isFiberedInGroupoids 𝒵.isFiberedInGroupoids 𝒴.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor_comp_p p)
      (CatFiberedInGroupoids.homFunctor_comp_p q))

/-- The canonical projection of the base change to the second factor. -/
def twoFibreProductSnd : twoFibreProduct B S hS 𝒳 𝒴 𝒵 p q ⟶ 𝒵 :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := TwoFibreProductOver.snd 𝒳.val.p 𝒵.val.p 𝒴.val.p
        (CatFiberedInGroupoids.homFunctor p) (CatFiberedInGroupoids.homFunctor q)
      w := TwoFibreProductOver.snd_comp_eq }

/-- **Stacks 06CV.** Limit preservation on objects is stable under base change. -/
@[stacks 06CV]
theorem isLimitPreservingOnObjects_baseChange
    (hp : IsLimitPreservingOnObjects.{u, v, w} B S hS 𝒳 𝒴 p) :
    IsLimitPreservingOnObjects.{u, v, w} B S hS
      (twoFibreProduct B S hS 𝒳 𝒴 𝒵 p q) 𝒵
      (twoFibreProductSnd B S hS 𝒳 𝒴 𝒵 p q) := by
  intro I hI hcof D c hc i zi W δ hδ
  let Fp := CatFiberedInGroupoids.homFunctor p
  let Gq := CatFiberedInGroupoids.homFunctor q
  have : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  have : 𝒴.val.p.IsFibered := 𝒴.isFiberedInGroupoids.isFibered
  have : 𝒵.val.p.IsFibered := 𝒵.isFiberedInGroupoids.isFibered
  let inc := BigAffineFppf.inclusion B S hS
  let T := TwoFibreProductOver.structureFunctor 𝒳.val.p 𝒵.val.p 𝒴.val.p Fp Gq
  let fi := inc.map (c.π.app i)
  let W0 := W.1
  have hW : W0.base = c.pt.obj := W.property
  let x0 : 𝒳.val.p.Fiber c.pt.obj := ⟨W0.x, W0.hx.trans hW⟩
  let y0 : 𝒴.val.p.Fiber (D.obj i).obj := ⟨_, proj_homFunctor_obj q zi⟩
  let gamma : Fp.obj x0.1 ⟶ y0.1 := W0.iso.hom ≫ Gq.map δ
  have hδY : 𝒴.val.p.IsStronglyCartesian fi (Gq.map δ) :=
    CatFiberedInGroupoids.isStronglyCartesian_map q fi δ
  have hα : 𝒴.val.p.IsHomLift (𝟙 c.pt.obj) W0.iso.hom := by
    rw [← hW]
    exact W0.vertical
  have hgamma : 𝒴.val.p.IsStronglyCartesian fi gamma := by
    have hγlift : 𝒴.val.p.IsHomLift fi gamma := by
      simpa [gamma] using (@IsHomLift.comp_lift_id_left'
        _ _ _ _ 𝒴.val.p _ _ _ c.pt.obj W0.iso.hom hα
        _ _ fi (Gq.map δ) hδY.toIsHomLift)
    exact 𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift fi gamma
  obtain ⟨i', j, x', xU, δx, β, gamma', hδx, hβ, hβiso, hgamma', hcomm⟩ :=
    hp I D c hc i y0 x0 gamma hgamma
  have : 𝒳.val.p.IsHomLift (𝟙 c.pt.obj) β := hβ
  let f' := inc.map (c.π.app i')
  let gj := inc.map (D.map j)
  have hfactor : fi = f' ≫ gj := (congrArg inc.map (c.w j).symm).trans (inc.map_comp _ _)
  have hδxInc : 𝒳.val.p.IsStronglyCartesian f' δx := hδx
  have hgamma'Inc : 𝒴.val.p.IsStronglyCartesian gj gamma' := hgamma'
  let z' := Functor.IsPreFibered.pullbackObj zi.2 gj
  have hz' : 𝒵.val.p.obj z' = (D.obj i').obj :=
    Functor.IsPreFibered.pullbackObj_proj zi.2 gj
  let ζ : z' ⟶ zi.1 := Functor.IsPreFibered.pullbackMap zi.2 gj
  have hζ : 𝒵.val.p.IsStronglyCartesian gj ζ := inferInstance
  have hGζ : 𝒴.val.p.IsStronglyCartesian gj (Gq.map ζ) :=
    CatFiberedInGroupoids.isStronglyCartesian_map q gj ζ
  have hbaseIso : gj = (Iso.refl ((D.obj i').obj)).hom ≫ gj := by simp
  let theta : Fp.obj x'.1 ≅ Gq.obj z' :=
    Functor.IsStronglyCartesian.domainIsoOfBaseIso 𝒴.val.p hbaseIso (Gq.map ζ) gamma'
  have hthetaHom : theta.hom =
      Functor.IsStronglyCartesian.map 𝒴.val.p gj (Gq.map ζ) hbaseIso gamma' := rfl
  have hthetaSquare : theta.hom ≫ Gq.map ζ = gamma' :=
    Functor.IsStronglyCartesian.fac 𝒴.val.p gj (Gq.map ζ) hbaseIso gamma'
  have hthetaVert : 𝒴.val.p.IsHomLift (𝟙 ((D.obj i').obj)) theta.hom := by
    rw [hthetaHom]
    simpa using Functor.IsStronglyCartesian.map_isHomLift 𝒴.val.p
      gj (Gq.map ζ) hbaseIso gamma'
  let W' : TwoFibreProductOver 𝒳.val.p 𝒵.val.p 𝒴.val.p Fp Gq :=
    { base := (D.obj i').obj
      x := x'.1
      y := z'
      hx := x'.2
      hy := hz'
      iso := theta
      vertical := hthetaVert }
  let W'fib : (twoFibreProduct B S hS 𝒳 𝒴 𝒵 p q).val.p.Fiber
      ((BigAffineFppf.inclusion B S hS).obj (D.obj i')) := ⟨W', rfl⟩
  let αU : Fp.obj xU.1 ≅ Gq.obj W0.y :=
    { hom := Fp.map β ≫ W0.iso.hom
      inv := W0.iso.inv ≫ Fp.map (inv β)
      hom_inv_id := by simp
      inv_hom_id := by simp }
  have hFpβ : 𝒴.val.p.IsStronglyCartesian (𝟙 c.pt.obj) (Fp.map β) :=
    CatFiberedInGroupoids.isStronglyCartesian_map p (𝟙 c.pt.obj) β
  have hαU : 𝒴.val.p.IsHomLift (𝟙 c.pt.obj) αU.hom := by
    simpa [αU] using IsHomLift.comp_lift_id_left' 𝒴.val.p c.pt.obj
      (Fp.map β) (𝟙 c.pt.obj) W0.iso.hom
  let WU : TwoFibreProductOver 𝒳.val.p 𝒵.val.p 𝒴.val.p Fp Gq :=
    { base := c.pt.obj
      x := xU.1
      y := W0.y
      hx := xU.2
      hy := W0.hy.trans hW
      iso := αU
      vertical := hαU }
  let WUfib : (twoFibreProduct B S hS 𝒳 𝒴 𝒵 p q).val.p.Fiber
      ((BigAffineFppf.inclusion B S hS).obj c.pt) := ⟨WU, rfl⟩
  let zmap := Functor.IsStronglyCartesian.map 𝒵.val.p gj ζ hfactor δ
  have hzmapfac : zmap ≫ ζ = δ := Functor.IsStronglyCartesian.fac 𝒵.val.p gj ζ hfactor δ
  have hzmapLift : 𝒵.val.p.IsHomLift f' zmap :=
    Functor.IsStronglyCartesian.map_isHomLift 𝒵.val.p gj ζ hfactor δ
  have hzmapSC : 𝒵.val.p.IsStronglyCartesian f' zmap := by
    have : 𝒵.val.p.IsStronglyCartesian (f' ≫ gj) (zmap ≫ ζ) := by
      rw [hzmapfac, ← hfactor]
      exact hδ
    exact Functor.IsStronglyCartesian.of_comp 𝒵.val.p
      (f := f') (g := gj) (φ := zmap) (ψ := ζ)
  have hFpδx : 𝒴.val.p.IsStronglyCartesian f' (Fp.map δx) :=
    CatFiberedInGroupoids.isStronglyCartesian_map p f' δx
  have hGzmap : 𝒴.val.p.IsStronglyCartesian f' (Gq.map zmap) :=
    CatFiberedInGroupoids.isStronglyCartesian_map q f' zmap
  have hdeltaSquare : Fp.map δx ≫ theta.hom = αU.hom ≫ Gq.map zmap := by
    have hleft : 𝒴.val.p.IsHomLift f' (Fp.map δx ≫ theta.hom) :=
      IsHomLift.comp_lift_id_right' 𝒴.val.p f' (Fp.map δx) ((D.obj i').obj) theta.hom
    have hright : 𝒴.val.p.IsHomLift f' (αU.hom ≫ Gq.map zmap) :=
      @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒴.val.p _ _ _ c.pt.obj αU.hom hαU
        _ _ f' (Gq.map zmap) hGzmap.toIsHomLift
    have hpost : (Fp.map δx ≫ theta.hom) ≫ Gq.map ζ =
        (αU.hom ≫ Gq.map zmap) ≫ Gq.map ζ := by
      rw [Category.assoc, hthetaSquare]
      refine hcomm.trans ?_
      simp only [gamma, αU, Fp, Gq, ← hzmapfac, Category.assoc]
      congr 2
      exact (CatFiberedInGroupoids.homFunctor q).map_comp zmap ζ
    exact Functor.IsStronglyCartesian.ext 𝒴.val.p gj (Gq.map ζ) f' hpost
  let δtot : WU ⟶ W' :=
    { hbase := f'
      a := δx
      b := zmap
      ha := hδx.toIsHomLift
      hb := hzmapLift
      w := hdeltaSquare }
  let βtot : WU ⟶ W0 :=
    { hbase := eqToHom hW.symm
      a := β
      b := 𝟙 W0.y
      ha := by
        simpa using (inferInstance : 𝒳.val.p.IsHomLift (𝟙 c.pt.obj ≫ eqToHom hW.symm) β)
      hb := IsHomLift.of_commsq 𝒵.val.p (eqToHom hW.symm) (𝟙 W0.y)
          (W0.hy.trans hW) W0.hy (by simp)
      w := by
        change Fp.map β ≫ W0.iso.hom = (Fp.map β ≫ W0.iso.hom) ≫ Gq.map (𝟙 W0.y)
        rw [Gq.map_id, Category.comp_id] }
  have hβtotLift : (twoFibreProduct B S hS 𝒳 𝒴 𝒵 p q).val.p.IsHomLift
      (𝟙 ((BigAffineFppf.inclusion B S hS).obj c.pt)) βtot := by
    change T.IsHomLift (𝟙 c.pt.obj) βtot
    apply IsHomLift.of_commsq T (𝟙 c.pt.obj) βtot rfl hW
    change eqToHom hW.symm ≫ eqToHom hW = eqToHom rfl ≫ 𝟙 c.pt.obj
    simp
  have hβtotIso : IsIso βtot := TwoFibreProductOver.isIso_of_components βtot
  have hδtotLift : T.IsHomLift f' δtot := by
    change T.IsHomLift (T.map δtot) δtot
    exact inferInstance
  have hδtotSC : T.IsStronglyCartesian f' δtot :=
    TwoFibreProductOver.isStronglyCartesian_of_components
      (𝒴.isFiberedInGroupoids.isFibredOneMorphism
        (CatFiberedInGroupoids.homFunctor_comp_p p))
      (𝒴.isFiberedInGroupoids.isFibredOneMorphism
        (CatFiberedInGroupoids.homFunctor_comp_p q))
      f' δtot hδtotLift hδxInc hzmapSC
  refine ⟨i', j, W'fib, WUfib, δtot, βtot, ζ, hδtotSC, hβtotLift, hβtotIso, ?_, ?_⟩
  · exact hζ
  · change zmap ≫ ζ = (𝟙 W0.y) ≫ δ
    exact hzmapfac.trans (Category.id_comp δ).symm

end BaseChange

/-- **Stacks 06CW.** The composite of two morphisms of categories fibred in groupoids that are
limit preserving on objects is limit preserving on objects. -/
@[stacks 06CW]
theorem isLimitPreservingOnObjects_comp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (𝒳 𝒴 𝒵 : CatFiberedInGroupoids (BigFppfOver B S hS))
    (p : 𝒳 ⟶ 𝒴) (q : 𝒴 ⟶ 𝒵)
    (hp : IsLimitPreservingOnObjects.{u, v, w} B S hS 𝒳 𝒴 p)
    (hq : IsLimitPreservingOnObjects.{u, v, w} B S hS 𝒴 𝒵 q) :
    IsLimitPreservingOnObjects.{u, v, w} B S hS 𝒳 𝒵 (p ≫ q) := by
  intro I _ _ D c hc i z x γ hγ
  let y : 𝒴.val.p.Fiber ((BigAffineFppf.inclusion B S hS).obj c.pt) :=
    ⟨_, proj_homFunctor_obj p x⟩
  rcases hq I D c hc i z y γ hγ with
    ⟨i₁, j₁, y₁, yU, δq, βq, γq, hδq, hβq, hβqIso, hγq, hcommq⟩
  let U := (BigAffineFppf.inclusion B S hS).obj c.pt
  have : 𝒴.val.p.IsHomLift (𝟙 U) βq := hβq
  let eβ : yU.1 ≅ (CatFiberedInGroupoids.homFunctor p).obj x.1 := asIso βq
  have : 𝒴.val.p.IsHomLift (𝟙 U) eβ.inv := IsHomLift.lift_id_inv_isIso 𝒴.val.p U βq
  have hcart : 𝒴.val.p.IsStronglyCartesian
      ((BigAffineFppf.inclusion B S hS).map (c.π.app i₁)) (eβ.inv ≫ δq) := by
    have : 𝒴.val.p.IsStronglyCartesian (𝟙 U) eβ.inv := inferInstance
    simpa only [Category.id_comp] using
      (inferInstance : 𝒴.val.p.IsStronglyCartesian
        (𝟙 U ≫ (BigAffineFppf.inclusion B S hS).map (c.π.app i₁)) (eβ.inv ≫ δq))
  rcases hp I D c hc i₁ y₁ x (eβ.inv ≫ δq) hcart with
    ⟨i₂, j₂, x₂, xU, δp, βp, γp, hδp, hβp, hβpIso, hγp, hcommp⟩
  have hγout : 𝒵.val.p.IsStronglyCartesian
      ((BigAffineFppf.inclusion B S hS).map (D.map (j₂ ≫ j₁)))
      ((CatFiberedInGroupoids.homFunctor q).map γp ≫ γq) := by
    have : 𝒵.val.p.IsStronglyCartesian
        ((BigAffineFppf.inclusion B S hS).map (D.map j₂))
        ((CatFiberedInGroupoids.homFunctor q).map γp) :=
      CatFiberedInGroupoids.isStronglyCartesian_map q _ γp
    simpa using (inferInstance : 𝒵.val.p.IsStronglyCartesian
      ((BigAffineFppf.inclusion B S hS).map (D.map j₂) ≫
        (BigAffineFppf.inclusion B S hS).map (D.map j₁))
      ((CatFiberedInGroupoids.homFunctor q).map γp ≫ γq))
  refine ⟨i₂, j₂ ≫ j₁, x₂, xU, δp, βp,
    (CatFiberedInGroupoids.homFunctor q).map γp ≫ γq, hδp, hβp, hβpIso, hγout, ?_⟩
  change (CatFiberedInGroupoids.homFunctor q).map
      ((CatFiberedInGroupoids.homFunctor p).map δp) ≫
        ((CatFiberedInGroupoids.homFunctor q).map γp ≫ γq) =
      (CatFiberedInGroupoids.homFunctor q).map
        ((CatFiberedInGroupoids.homFunctor p).map βp) ≫ γ
  calc
    _ = (CatFiberedInGroupoids.homFunctor q).map
          ((CatFiberedInGroupoids.homFunctor p).map δp ≫ γp) ≫ γq := by
      simp only [Functor.map_comp, Category.assoc]
    _ = (CatFiberedInGroupoids.homFunctor q).map
          ((CatFiberedInGroupoids.homFunctor p).map βp ≫ eβ.inv ≫ δq) ≫ γq := by
      rw [hcommp]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      rw [hcommq, ← Category.assoc ((CatFiberedInGroupoids.homFunctor q).map eβ.inv)
        ((CatFiberedInGroupoids.homFunctor q).map βq) γ,
        ← Functor.map_comp]
      simp only [eβ, asIso_inv, IsIso.inv_hom_id]
      rw [(CatFiberedInGroupoids.homFunctor q).map_id]
      exact congrArg (fun f => (CatFiberedInGroupoids.homFunctor q).map
        ((CatFiberedInGroupoids.homFunctor p).map βp) ≫ f) (Category.id_comp γ)

end AlgebraicGeometry.BigFppfOver

end
