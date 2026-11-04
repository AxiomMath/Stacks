module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeOfCartesianLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentIsLocallyQuasicoherentLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeCartesianFlatObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageRuleAffineTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.VersalChartSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.CartesianArrowIsoLargeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherentFlatDescent

/-!
# The faithful `LQCoh^fbc` is detected on affine charts, at module universe `u + 1`

Let `𝒴` be an algebraic stack over `S` and `G` a module on its fppf site with sections in
`Type (u + 1)`. This file proves that `G` lies in the faithful `LQCoh^fbc(𝒪_𝒴)` (locally
quasi-coherent, Stacks 06WJ, with the flat base change property of Stacks 0762 read with the
pullback of sheaves) as soon as, for every object `y` of `𝒴` over an affine scheme `V`, the inverse
image of `G` along the 1-morphism `y : (Sch/V) ⟶ 𝒴` does. This is the locality the first move of
the proof of Stacks 0770 / 0771 needs, in pointwise form: instead of descending along a smooth
covering (Stacks 07AQ part (1), available only at module universe `u`), it reads the conditions
off the affine charts, through the sections-level characterization of the faithful class at large
module universes:

* a module cartesian on flat arrows between objects over affine schemes has the flat base change
  property
  (`Stack.hasSheafFlatBaseChangePropertyUnivLE_of_isCartesianOnFlatAffineArrows`)
  and is locally quasi-coherent, its small-étale restrictions being cartesian between affine
  objects
  (`SmallEtale.isQuasicoherentOnSite_of_bijective_restrictionBaseChange_freeModuleUniverse`);
* a module in the faithful class is cartesian on flat arrows between objects over affine schemes
  (`Stack.bijective_restrictionBaseChange_of_flat_freeModuleUniverse`), and a flat arrow
  `φ : x ⟶ y` over affine schemes is isomorphic to the image under the chart of `y` of the arrow
  of `Sch/V` below `φ`.

## Main results

* `Stack.isLocallyQuasicoherentWithSheafFlatBaseChangeUnivLE_of_isCartesianOnFlatAffineArrows`:
  an étale sheaf of modules on a category fibred in groupoids which is cartesian on flat arrows
  between objects over affine schemes lies in the faithful `LQCoh^fbc`, at module universe
  `max (u + 1) v w m`.
* `Stack.bijective_restrictionBaseChange_of_liftFunctor_map`: cartesianness along an arrow from
  cartesianness along its chart.
* `Stack.isCartesianOnFlatAffineArrows_of_objectStackMap`,
  `Stack.sheafFlatBaseChangeModuleRule_of_objectStackMap`: the faithful `LQCoh^fbc` at module
  universe `u + 1` is detected on affine charts.

## References

* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 07AQ](https://stacks.math.columbia.edu/tag/07AQ)
-/

@[expose] public section

open CategoryTheory Stacks.PresheafOfModules

universe u v w m v' w' t s

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-- **An étale sheaf of modules which is cartesian on flat arrows between affine objects lies in
the faithful `LQCoh^fbc`**, at module universe `max (u + 1) v w m`. -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChangeUnivLE_of_isCartesianOnFlatAffineArrows
    (G : PresheafOfModules.{max (u + 1) v w m}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj)
    (hG : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) G.presheaf)
    (hcart : IsCartesianOnFlatAffineArrows.{u, v, w, m} B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) G) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, max (u + 1) v w m}
      B E h S hS p hp G := by
  refine ⟨⟨hG, fun x => ⟨restrictModuleToSmallEtale_isSheaf B E h S hS p hp x G hG, ?_⟩⟩,
    hasSheafFlatBaseChangePropertyUnivLE_of_isCartesianOnFlatAffineArrows G hcart⟩
  refine SmallEtale.isQuasicoherentOnSite_of_bijective_restrictionBaseChange_freeModuleUniverse.{
    max v w m} B E h _ _ _ fun {T T'} g hT hT' => ?_
  refine (bijective_restrictionBaseChange_restrictModuleToSmallEtale_iff_freeModuleUniverse.{u, v,
    w, m} B E h S hS p hp G x g).2 ?_
  have := etale_etaleIndex_map B E h S hS p hp x g
  exact hcart _ (inferInstanceAs (Flat ((BigFppfOver.toScheme B S hS).map
      (p.map ((etaleIndex B E h S hS p hp x).map g)))))
    (isAffine_etaleIndex_obj B E h S hS p hp x T hT)
    (isAffine_etaleIndex_obj B E h S hS p hp x T' hT')

section Bridge

variable {𝒴 : Type v'} [Category.{w'} 𝒴] (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hq : q.IsFiberedInGroupoids)

/-- The faithful `LQCoh^fbc` class of an inverse image along a 1-morphism `f` with `f ⋙ q = p`,
read on the structure functor `p` of the source or on the composite `f ⋙ q`, at any module
universe. -/
theorem isLocallyQuasicoherentWithSheafFlatBaseChangeUnivLE_modulePullback_iff
    [UnivLE.{u, t}] (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) (hfq : (f ⋙ q).IsFiberedInGroupoids)
    (M : SheafOfModules.{t} (ringStructureSheafCore B S hS q hq B.topology le_rfl)) :
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, t} B E h S hS p hp
      ((modulePullback.{u, v, w, t, v', w'} B S hS p q hp hq f hf B.topology le_rfl).obj M).val ↔
    IsLocallyQuasicoherentWithSheafFlatBaseChange.{u, v, w, t} B E h S hS (f ⋙ q) hfq
      ((modulePresheafPullback.{u, v, w, v', w', t} B S hS q hq f hfq).obj M.val) := by
  subst hf
  rfl

end Bridge

section LiftArrow

variable {𝒴₀ : Type (u + 1)} [Category.{u} 𝒴₀] (q : 𝒴₀ ⥤ BigFppfOver B S hS)
  (hq : q.IsFiberedInGroupoids)

/-- **Cartesianness along an arrow from cartesianness along its chart.** For an arrow
`φ : x ⟶ y` of a category fibred in groupoids `q`, the functor `(Sch/V) ⥤ 𝒴` of the chosen
cartesian lifts of `y` (`V` the scheme below `y`) carries the arrow `(U → V) ⟶ (V = V)` of
`Sch/V` given by the morphism `U ⟶ V` below `φ` to an arrow isomorphic to `φ`; so a module
cartesian along that image is cartesian along `φ`. -/
theorem bijective_restrictionBaseChange_of_liftFunctor_map
    (G : PresheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS q hq (etaleTopology B) (etaleTopology_le_topology B)).obj)
    {x y : 𝒴₀} (φ : x ⟶ y)
    (hG : Function.Bijective (restrictionBaseChange.{u + 1, u, u, u + 1}
      (R := (structureSheaf B S hS q hq (etaleTopology B) (etaleTopology_le_topology B)).obj) G
      ((Functor.TwoYoneda.liftFunctor q hq (q.obj y) (Functor.Fiber.mk (a := y) rfl)).map
        (Over.homMk (q.map φ) (by simp) : Over.mk (q.map φ) ⟶ Over.mk (𝟙 (q.obj y)))).op)) :
    Function.Bijective (restrictionBaseChange.{u + 1, u, u, u + 1}
      (R := (structureSheaf B S hS q hq (etaleTopology B) (etaleTopology_le_topology B)).obj) G
      φ.op) := by
  have : q.IsFibered := hq.isFibered
  let V := q.obj y
  let gF := Functor.TwoYoneda.liftFunctor q hq V (Functor.Fiber.mk (a := y) rfl)
  let z₀ : Over V := Over.mk (𝟙 V)
  let z₁ : Over V := Over.mk (q.map φ)
  let ψ : z₁ ⟶ z₀ := Over.homMk (q.map φ) (by simp [z₀, z₁])
  let c₀ : gF.obj z₀ ⟶ y :=
    (Functor.TwoYoneda.chosenLift q hq V (Functor.Fiber.mk (a := y) rfl) z₀).φ
  let c₁ : gF.obj z₁ ⟶ y :=
    (Functor.TwoYoneda.chosenLift q hq V (Functor.Fiber.mk (a := y) rfl) z₁).φ
  have : q.IsStronglyCartesian z₀.hom c₀ :=
    (Functor.TwoYoneda.chosenLift q hq V (Functor.Fiber.mk (a := y) rfl) z₀).isStronglyCartesian
  have : q.IsStronglyCartesian z₁.hom c₁ :=
    (Functor.TwoYoneda.chosenLift q hq V (Functor.Fiber.mk (a := y) rfl) z₁).isStronglyCartesian
  have hgψ : gF.map ψ ≫ c₀ = c₁ :=
    Functor.IsStronglyCartesian.fac q z₀.hom c₀ (Over.w ψ).symm c₁
  have : q.IsHomLift z₁.hom φ := IsHomLift.map q φ
  let α : x ⟶ gF.obj z₁ := Functor.IsCartesian.map q z₁.hom c₁ φ
  have hα : α ≫ c₁ = φ := Functor.IsCartesian.fac q z₁.hom c₁ φ
  have : q.IsHomLift (𝟙 (q.obj x)) α := Functor.IsCartesian.map_isHomLift q z₁.hom c₁ φ
  have : q.IsStronglyCartesian (𝟙 (q.obj x)) α := hq.isStronglyCartesian_homLift _ _
  have : IsIso α := Functor.IsStronglyCartesian.isIso_of_base_isIso q (𝟙 (q.obj x)) α
  have : q.IsStronglyCartesian (𝟙 V) c₀ :=
    (Functor.TwoYoneda.chosenLift q hq V (Functor.Fiber.mk (a := y) rfl) z₀).isStronglyCartesian
  have : IsIso c₀ := Functor.IsStronglyCartesian.isIso_of_base_isIso q (𝟙 V) c₀
  have hsq : φ.op ≫ (inv α).op = c₀.op ≫ (gF.map ψ).op := by
    rw [← op_comp, ← op_comp]
    congr 1
    rw [hgψ, ← hα, IsIso.inv_hom_id_assoc]
  exact (bijective_restrictionBaseChange_iff_of_arrowIso_freeModuleUniverse.{u + 1, u, u, u + 1}
    (R := (structureSheaf B S hS q hq (etaleTopology B) (etaleTopology_le_topology B)).obj) G
    φ.op (gF.map ψ).op c₀.op (inv α).op hsq).2 hG

end LiftArrow

section Charts

variable {B E h S hS} in
/-- **Cartesianness of a module on an algebraic stack from its affine charts.** If the inverse
image of a module `G` on the fppf site of an algebraic stack `𝒴` along the 1-morphism
`y : (Sch/V) ⟶ 𝒴` of every object `y` of `𝒴` over an affine scheme `V` lies in the faithful
`LQCoh^fbc`, then `G` is cartesian on flat arrows between objects over affine schemes. -/
theorem isCartesianOnFlatAffineArrows_of_objectStackMap {𝒴 : AlgebraicStacks.{u, s} B S hS}
    (G : AlgebraicStacks.fppfModules B S hS 𝒴)
    (hG : ∀ y : 𝒴.val.val.obj, IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒴.val.val.p.obj y)) →
      AlgebraicStacks.sheafFlatBaseChangeModuleRule B S hS E h
        (schemeStack.{u, s} B S hS (𝒴.val.val.p.obj y))
        ((AlgebraicStacks.fppfModulePullback B S hS (objectStackMap B S hS 𝒴 y)).obj G)) :
    IsCartesianOnFlatAffineArrows.{u, u + 1, u, u} B S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
      (etaleTopology B) (etaleTopology_le_topology B) G.val := by
  intro x y φ hφ hx hy
  let g := objectStackMap B S hS 𝒴 y
  have hpull := (isLocallyQuasicoherentWithSheafFlatBaseChangeUnivLE_modulePullback_iff B E h S hS
    _ (schemeStack.{u, s} B S hS (𝒴.val.val.p.obj y)).val.isFiberedInGroupoids
    𝒴.val.val.p 𝒴.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor g.hom)
    (CatFiberedInGroupoids.homFunctor_comp_p g.hom)
    (isFiberedInGroupoids_homFunctor_comp B S hS g.hom) G).1 (hG y hy)
  have hq := 𝒴.val.isFiberedInGroupoids
  have : 𝒴.val.val.p.IsFibered := hq.isFibered
  let V := 𝒴.val.val.p.obj y
  let gF := CatFiberedInGroupoids.homFunctor g.hom
  let z₀ : Over V := Over.mk (𝟙 V)
  let z₁ : Over V := Over.mk (𝒴.val.val.p.map φ)
  let ψ : z₁ ⟶ z₀ := Over.homMk (𝒴.val.val.p.map φ) (by simp [z₀, z₁])
  let c₀ := (Functor.TwoYoneda.chosenLift 𝒴.val.val.p hq V (Functor.Fiber.mk (a := y) rfl) z₀).φ
  let c₁ := (Functor.TwoYoneda.chosenLift 𝒴.val.val.p hq V (Functor.Fiber.mk (a := y) rfl) z₁).φ
  have hgψ : gF.map ψ ≫ c₀ = c₁ :=
    Functor.IsStronglyCartesian.fac 𝒴.val.val.p z₀.hom c₀ (Over.w ψ).symm c₁
  have hψlift : 𝒴.val.val.p.IsHomLift ψ.left (gF.map ψ) :=
    Functor.IsStronglyCartesian.map_isHomLift 𝒴.val.val.p z₀.hom c₀ (Over.w ψ).symm c₁
  have hc₀ : 𝒴.val.val.p.IsHomLift z₀.hom c₀ :=
    (Functor.TwoYoneda.chosenLift 𝒴.val.val.p hq V (Functor.Fiber.mk (a := y) rfl)
      z₀).isStronglyCartesian.toIsHomLift
  have hc₁ : 𝒴.val.val.p.IsHomLift z₁.hom c₁ :=
    (Functor.TwoYoneda.chosenLift 𝒴.val.val.p hq V (Functor.Fiber.mk (a := y) rfl)
      z₁).isStronglyCartesian.toIsHomLift
  have e₀ : 𝒴.val.val.p.obj (gF.obj z₀) = V := @IsHomLift.domain_eq _ _ _ _ 𝒴.val.val.p _ _ _ _
    z₀.hom c₀ hc₀
  have e₁ : 𝒴.val.val.p.obj (gF.obj z₁) = 𝒴.val.val.p.obj x :=
    @IsHomLift.domain_eq _ _ _ _ 𝒴.val.val.p _ _ _ _ z₁.hom c₁ hc₁
  have hψ : Flat (B.inclusion.map ((gF ⋙ 𝒴.val.val.p).map ψ).left) :=
    morphismProperty_map_left_of_isHomLift B S hS 𝒴.val.val.p @Flat
      (respectsIso_of_isStableUnderComposition_of_isIso @Flat
        fun g hg => by have := hg; infer_instance)
      ψ.left hφ (gF.map ψ) hψlift
  have ha : IsAffine (((gF ⋙ 𝒴.val.val.p) ⋙ BigFppfOver.toScheme B S hS).obj z₁) := by
    show IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒴.val.val.p.obj (gF.obj z₁)))
    rw [e₁]
    exact hx
  have hb : IsAffine (((gF ⋙ 𝒴.val.val.p) ⋙ BigFppfOver.toScheme B S hS).obj z₀) := by
    show IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒴.val.val.p.obj (gF.obj z₀)))
    rw [e₀]
    exact hy
  have h₁ := bijective_restrictionBaseChange_of_flat_freeModuleUniverse.{u, u + 1, u, u}
    B E h S hS (gF ⋙ 𝒴.val.val.p) (isFiberedInGroupoids_homFunctor_comp B S hS g.hom) _ hpull
    ψ hψ ha hb
  have h₂ : Function.Bijective (restrictionBaseChange.{u + 1, u, u, u + 1}
      (R := (structureSheaf B S hS 𝒴.val.val.p hq (etaleTopology B)
        (etaleTopology_le_topology B)).obj) G.val (gF.map ψ).op) := h₁
  exact bijective_restrictionBaseChange_of_liftFunctor_map B S hS 𝒴.val.val.p hq G.val φ h₂

variable {B E h S hS} in
/-- **The faithful `LQCoh^fbc` is detected on affine charts**, at module universe `u + 1`: a
module `G` on the fppf site of an algebraic stack `𝒴` lies in `LQCoh^fbc(𝒪_𝒴)` as soon as its
inverse image along the 1-morphism `y : (Sch/V) ⟶ 𝒴` of every object `y` of `𝒴` over an affine
scheme `V` lies in `LQCoh^fbc(𝒪_{Sch/V})`. -/
theorem sheafFlatBaseChangeModuleRule_of_objectStackMap {𝒴 : AlgebraicStacks.{u, s} B S hS}
    (G : AlgebraicStacks.fppfModules B S hS 𝒴)
    (hG : ∀ y : 𝒴.val.val.obj, IsAffine ((BigFppfOver.toScheme B S hS).obj (𝒴.val.val.p.obj y)) →
      AlgebraicStacks.sheafFlatBaseChangeModuleRule B S hS E h
        (schemeStack.{u, s} B S hS (𝒴.val.val.p.obj y))
        ((AlgebraicStacks.fppfModulePullback B S hS (objectStackMap B S hS 𝒴 y)).obj G)) :
    AlgebraicStacks.sheafFlatBaseChangeModuleRule B S hS E h 𝒴 G :=
  isLocallyQuasicoherentWithSheafFlatBaseChangeUnivLE_of_isCartesianOnFlatAffineArrows.{u, u + 1,
    u, u} B E h S hS 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids G.val
    (G.isSheaf.of_le (BigFppfOver.associatedTopology_le_fppf B S hS _ .etale))
    (isCartesianOnFlatAffineArrows_of_objectStackMap G hG)

end Charts

end AlgebraicGeometry.Stack

end
