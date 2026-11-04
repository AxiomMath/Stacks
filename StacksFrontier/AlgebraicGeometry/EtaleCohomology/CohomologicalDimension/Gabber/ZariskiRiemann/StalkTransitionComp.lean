module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.CenteredGermDeathOfValuation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ProperModelLerayTermComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BoundaryStalkFrobeniusPullback

/-!
# The cocycle of the transition maps of stalks along refinements

For a refinement `π : Y' ⟶ Y` of proper models of `η = Spec (Frac B)` and a geometric point `s'`
of `Y'`, `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.stalkTransition` is the
map `(R^q j_* F)_{s' ≫ π} = (π⁻¹ R^q j_* F)_{s'} ⟶ (R^q j'_* F)_{s'}`, the stalk of the base change
map of the square `𝟙 ≫ j = j' ≫ π`. This file proves the cocycle condition of these maps along a
composite of refinements `Y'' ⟶ Y' ⟶ Y`
(`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.stalkTransition_comp`): the
transition of the composite at a geometric point `s` of `Y''` is the transition of `Y' ⟶ Y` at the
image of `s` followed by the transition of `Y'' ⟶ Y'` at `s`. This is the stalk form of the
transport cocycle `(g^π)^ρ = g^{πρ}` of Gabber's argument. As a consequence, a germ dying on a
refinement dies on every further refinement
(`AlgebraicGeometry.Scheme.ZariskiRiemann.deadAtStableUnderRefinement`), one of the inputs of the
Zariski–Riemann step of Gabber's germ-killing argument (Travaux de Gabber, Exposé XVIII-A, last
remark of §2).

The proof takes stalks in the sheaf-level pasting law
`Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageBaseChange_comp`. What it
needs on stalks is the compatibility of the identifications `(f⁻¹ G)_s ≅ G_{s ≫ f}` with the
composition isomorphism of inverse images
(`Stacks.EtaleCohomology.etaleAbelianInverseImageStalkMap_comp`), which is checked on germs: on
the germ of a section, the identification is the unit of the inverse-image/direct-image
adjunction followed by the germ at the corresponding lift
(`Stacks.EtaleCohomology.toPresheafFiber_comp_etaleAbelianInverseImageStalkMap`), the unit of a
composite adjunction is the composite of the units read through the composition isomorphism
(`Stacks.EtaleCohomology.etaleAbelianInverseImageDirectImageAdj_unit_comp_unit`), and the lifts
match (`AlgebraicGeometry.pointSmallEtaleBaseChangeFiberIso_comp`).

## Main definitions

* `Stacks.EtaleCohomology.etaleAbelianInverseImageStalkMap` — the identification
  `G_{s ≫ f} ⟶ (f⁻¹ G)_s` for the inverse image `Stacks.EtaleCohomology.etaleAbelianInverseImage`.

## Main results

* `Stacks.EtaleCohomology.etaleAbelianInverseImageStalkMap_comp` — the identifications of stalks
  of inverse images compose.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.stalkTransition_comp` — **the
  cocycle of the transition maps of stalks.**
* `AlgebraicGeometry.Scheme.ZariskiRiemann.deadAtStableUnderRefinement` — **death of a germ is
  stable under further refinement.**

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-! ### The unit of a composite adjunction -/

/-- The unit of the adjunction `F₀₂ ⊣ G₂₀`, followed by the image of the inverse of the comparison
`F₀₁ ⋙ F₁₂ ≅ F₀₂` of left adjoints, is the composite of the units of `F₀₁ ⊣ G₁₀` and
`F₁₂ ⊣ G₂₁` followed by the comparison `G₂₁ ⋙ G₁₀ ≅ G₂₀` of right adjoints. -/
theorem unit_comp_map_leftAdjointCompIso_inv_app {C₀ C₁ C₂ : Type*} [Category* C₀]
    [Category* C₁] [Category* C₂] {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀} (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁)
    (adj₀₂ : F₀₂ ⊣ G₂₀) (e : G₂₁ ⋙ G₁₀ ≅ G₂₀) (X : C₀) :
    adj₀₂.unit.app X ≫ G₂₀.map ((Adjunction.leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).inv.app X) =
      adj₀₁.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁.obj X)) ≫
        e.hom.app (F₁₂.obj (F₀₁.obj X)) := by
  rw [Adjunction.leftAdjointCompIso_inv_app, ← F₀₂.map_comp_assoc, ← F₀₂.map_comp_assoc,
    ← Adjunction.homEquiv_counit]
  exact (adj₀₂.homEquiv_unit _ _ _).symm.trans
    (((adj₀₂.homEquiv _ _).apply_symm_apply _).trans (Category.assoc _ _ _))

/-! ### Diagram chases

The composites below are type-correct only after unfolding stalk functors, direct images and
composites of functors, which stops `rw` from firing on them in place; each chase is stated for
bare morphisms of an abstract category and applied by `exact`, which does the unfolding once, in
the elaborator. -/

section Chases

variable {C : Type*} [Category* C]

private theorem chase_germ_stalkMap {A S₀ S₁ S₂ B B' : C} (germ : A ⟶ S₀) (inv : S₀ ⟶ S₁)
    (m : S₁ ⟶ S₂) (u : A ⟶ B) (g : B ⟶ S₁) (α : B ⟶ B') (g' : B' ⟶ S₂) (u' : A ⟶ B')
    (h₀ : germ ≫ inv = u ≫ g) (h₁ : g ≫ m = α ≫ g') (hu : u ≫ α = u') :
    germ ≫ inv ≫ m = u' ≫ g' := by
  rw [reassoc_of% h₀, h₁, reassoc_of% hu]

private theorem chase_naturality {S₀ S₁ S₂ T₀ T₁ T₂ : C} (a : S₀ ⟶ T₀) (i' : T₀ ⟶ T₁)
    (m' : T₁ ⟶ T₂) (i : S₀ ⟶ S₁) (m : S₁ ⟶ S₂) (p : S₁ ⟶ T₁) (n : S₂ ⟶ T₂)
    (h₁ : a ≫ i' = i ≫ p) (h₂ : p ≫ m' = m ≫ n) :
    a ≫ i' ≫ m' = (i ≫ m) ≫ n := by
  rw [reassoc_of% h₁, h₂, Category.assoc]

private theorem chase_unit {A B₁ B₂ C₁ C₂ : C} (ub : A ⟶ B₁) (ua : B₁ ⟶ B₂) (uab : A ⟶ C₁)
    (c : C₁ ⟶ C₂) (eW : B₂ ⟶ C₂) (k : C₂ ⟶ B₂) (hh : uab ≫ c = ub ≫ ua ≫ eW)
    (hk : eW ≫ k = 𝟙 _) : ub ≫ ua = uab ≫ c ≫ k := by
  rw [reassoc_of% hh, hk, Category.comp_id]

private theorem chase_stalkMap_comp {A S₀ S₁ S₂ B₁ B₂ S₀' T₁ C₁ C₂ : C} (germ : A ⟶ S₀)
    (βb : S₀ ⟶ S₁) (βa : S₁ ⟶ S₂) (ub : A ⟶ B₁) (gb : B₁ ⟶ S₁) (ua : B₁ ⟶ B₂)
    (gab : B₂ ⟶ S₂) (eq : S₀ ⟶ S₀') (g₁ : A ⟶ S₀') (βab : S₀' ⟶ T₁) (uab : A ⟶ C₁)
    (g₂ : C₁ ⟶ T₁) (φ' : T₁ ⟶ S₂) (c : C₁ ⟶ C₂) (g₃ : C₂ ⟶ S₂) (k : C₂ ⟶ B₂)
    (h₁ : germ ≫ βb = ub ≫ gb) (h₂ : gb ≫ βa = ua ≫ gab) (h₃ : germ ≫ eq = g₁)
    (h₄ : g₁ ≫ βab = uab ≫ g₂) (h₅ : g₂ ≫ φ' = c ≫ g₃) (h₆ : ub ≫ ua = uab ≫ c ≫ k)
    (h₇ : k ≫ gab = g₃) :
    germ ≫ βb ≫ βa = germ ≫ eq ≫ βab ≫ φ' := by
  rw [reassoc_of% h₁, h₂, reassoc_of% h₆, h₇, reassoc_of% h₃, reassoc_of% h₄, h₅]

private theorem chase_inv_hom {B C₂ : C} (eW e' : B ⟶ C₂) (k : C₂ ⟶ B) (he : eW = e')
    (hk : e' ≫ k = 𝟙 _) : eW ≫ k = 𝟙 _ := by
  rw [he, hk]

private theorem chase_germ_w {A B S : C} (k : A ⟶ B) (g : B ⟶ S) (g₁ g₂ : A ⟶ S)
    (hw : k ≫ g = g₁) (he : g₁ = g₂) : k ≫ g = g₂ :=
  hw.trans he

end Chases

/-! ### Stalks of inverse images -/

section StalkMap

variable {X X' X'' : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- **The identification of the stalk of an inverse image**, for the inverse image
`Stacks.EtaleCohomology.etaleAbelianInverseImage`: for `f : X' ⟶ X` and a geometric point `s` of
`X'`, the map `G_{s ≫ f} ⟶ (f⁻¹ G)_s`, the inverse of
`Stacks.EtaleCohomology.smallEtaleStalkPullbackAbIso` read through the identification
`Stacks.EtaleCohomology.smallEtalePullbackAbIsoEtaleAbelianInverseImage` of the two inverse
images. -/
def etaleAbelianInverseImageStalkMap (f : X' ⟶ X) (s : Spec (.of Ω) ⟶ X')
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    (smallEtaleStalkAb (s ≫ f)).obj G ⟶
      (smallEtaleStalkAb s).obj ((etaleAbelianInverseImage.{u, 0} f).obj G) :=
  (smallEtaleStalkPullbackAbIso f s).inv.app G ≫
    (smallEtaleStalkAb s).map ((smallEtalePullbackAbIsoEtaleAbelianInverseImage f).hom.app G)

/-- Transporting a germ of an abelian étale sheaf along an equality of geometric points (the
abelian form of `AlgebraicGeometry.toPresheafFiber_comp_eqToHom`). -/
theorem toPresheafFiber_comp_eqToHom_smallEtaleStalkAb {Y : Scheme.{u}}
    {t t' : Spec (.of Ω) ⟶ Y} (e : t = t') (G : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    (W : Y.Etale) (x : (Scheme.pointSmallEtale t).fiber.obj W) :
    (Scheme.pointSmallEtale t).toPresheafFiber W x G.obj ≫
        eqToHom (congrArg (fun t => (smallEtaleStalkAb t).obj G) e) =
      (Scheme.pointSmallEtale t').toPresheafFiber W
        (Over.homMk x.left (by rw [← e]; exact Over.w x)) G.obj := by
  subst e
  exact Category.comp_id _

/-- **The identification of stalks of an inverse image on germs**: on the germ at `s ≫ f` of a
section over an étale neighbourhood `W`, it is the unit of the inverse-image/direct-image
adjunction followed by the germ at the corresponding lift of `s` to `W ×_X X'`. -/
theorem toPresheafFiber_comp_etaleAbelianInverseImageStalkMap (f : X' ⟶ X)
    (s : Spec (.of Ω) ⟶ X') (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale)
    (v : (Scheme.pointSmallEtale (s ≫ f)).fiber.obj W) :
    (Scheme.pointSmallEtale (s ≫ f)).toPresheafFiber W v G.obj ≫
        etaleAbelianInverseImageStalkMap f s G =
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} f).unit.app G).hom.app (op W) ≫
        (Scheme.pointSmallEtale s).toPresheafFiber ((smallEtaleBaseChange f).obj W)
          ((pointSmallEtaleBaseChangeFiberIso f s).hom.app W v)
          ((etaleAbelianInverseImage.{u, 0} f).obj G).obj := by
  have h₀ := toPresheafFiber_comp_smallEtaleStalkPullbackAbIso_inv f s G W v
  have h₁ := Point.toPresheafFiber_naturality (Scheme.pointSmallEtale s)
    ((smallEtalePullbackAbIsoEtaleAbelianInverseImage f).hom.app G).hom
    ((smallEtaleBaseChange f).obj W) ((pointSmallEtaleComapFiberIso f s).hom.app W v)
  have hu := congrArg (fun φ => φ.hom.app (op W)) (Adjunction.unit_leftAdjointUniq_hom_app
    (smallEtaleAdjunctionAb f) (etaleAbelianInverseImageDirectImageAdj.{u, u + 1} f) G)
  exact chase_germ_stalkMap _ _ _ _ _ _ _ _ h₀ h₁ hu

/-- **The unit of the inverse image along a composite**, on sections over an étale `W`: the unit
for `b` followed by the unit for `a` is the unit for `a ≫ b`, followed by the composition
isomorphism `(a ≫ b)⁻¹ ≅ a⁻¹ b⁻¹` and restriction along the comparison of base changes. -/
theorem etaleAbelianInverseImageDirectImageAdj_unit_comp_unit (a : X'' ⟶ X') (b : X' ⟶ X)
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) (W : X.Etale) :
    ((etaleAbelianInverseImageDirectImageAdj.{u, 0} b).unit.app G).hom.app (op W) ≫
        ((etaleAbelianInverseImageDirectImageAdj.{u, 0} a).unit.app
          ((etaleAbelianInverseImage.{u, 0} b).obj G)).hom.app
            (op ((smallEtaleBaseChange b).obj W)) =
      ((etaleAbelianInverseImageDirectImageAdj.{u, 0} (a ≫ b)).unit.app G).hom.app (op W) ≫
        ((etaleAbelianInverseImageCompIso'.{u, 0} a b (a ≫ b) rfl).hom.app G).hom.app
          (op ((smallEtaleBaseChange (a ≫ b)).obj W)) ≫
        ((etaleAbelianInverseImage.{u, 0} a).obj
          ((etaleAbelianInverseImage.{u, 0} b).obj G)).obj.map
            ((smallEtaleBaseChangeComp a b).inv.app W).op := by
  have h := congrArg (fun φ => φ.hom.app (op W)) (unit_comp_map_leftAdjointCompIso_inv_app
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} b)
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} a)
    (etaleAbelianInverseImageDirectImageAdj.{u, 0} (a ≫ b))
    (etaleAbelianDirectImageCompIso'.{u, 0} a b (a ≫ b) rfl) G)
  have he := Functor.sheafPushforwardContinuousComp'_hom_app_hom_app
    (smallEtaleBaseChangeComp' a b (a ≫ b) rfl).symm AddCommGrpCat.{max (u + 1) 0}
    (smallEtaleTopology X) (smallEtaleTopology X') (smallEtaleTopology X'')
    ((etaleAbelianInverseImage.{u, 0} a).obj ((etaleAbelianInverseImage.{u, 0} b).obj G))
    (op W)
  have hk : ((etaleAbelianInverseImage.{u, 0} a).obj
        ((etaleAbelianInverseImage.{u, 0} b).obj G)).obj.map
          ((smallEtaleBaseChangeComp' a b (a ≫ b) rfl).symm.inv.app W).op ≫
      ((etaleAbelianInverseImage.{u, 0} a).obj
        ((etaleAbelianInverseImage.{u, 0} b).obj G)).obj.map
          ((smallEtaleBaseChangeComp a b).inv.app W).op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp]
    simp [smallEtaleBaseChangeComp']
  exact chase_unit _ _ _ _ _ _ h (chase_inv_hom _ _ _ he hk)

/-- **The identifications of stalks of inverse images compose**: for `a : X'' ⟶ X'`,
`b : X' ⟶ X` and a geometric point `s` of `X''`, the identification
`G_{(s ≫ a) ≫ b} ⟶ (b⁻¹ G)_{s ≫ a}` followed by `(b⁻¹ G)_{s ≫ a} ⟶ (a⁻¹ b⁻¹ G)_s` is the
identification `G_{s ≫ ab} ⟶ ((ab)⁻¹ G)_s` followed by the composition isomorphism
`(ab)⁻¹ ≅ a⁻¹ b⁻¹`. -/
theorem etaleAbelianInverseImageStalkMap_comp (a : X'' ⟶ X') (b : X' ⟶ X) (ab : X'' ⟶ X)
    (hab : ab = a ≫ b) (s : Spec (.of Ω) ⟶ X'') (G : Sheaf (smallEtaleTopology X) Ab.{u + 1}) :
    etaleAbelianInverseImageStalkMap b (s ≫ a) G ≫
        etaleAbelianInverseImageStalkMap a s ((etaleAbelianInverseImage.{u, 0} b).obj G) =
      eqToHom (by rw [hab, Category.assoc]) ≫ etaleAbelianInverseImageStalkMap ab s G ≫
        (smallEtaleStalkAb s).map
          ((etaleAbelianInverseImageCompIso'.{u, 0} a b ab hab).hom.app G) := by
  subst hab
  refine (Scheme.pointSmallEtale ((s ≫ a) ≫ b)).presheafFiber_hom_ext (P := G.obj)
    fun W x => ?_
  have h₁ := toPresheafFiber_comp_etaleAbelianInverseImageStalkMap b (s ≫ a) G W x
  have h₂ := toPresheafFiber_comp_etaleAbelianInverseImageStalkMap a s
    ((etaleAbelianInverseImage.{u, 0} b).obj G) ((smallEtaleBaseChange b).obj W)
    ((pointSmallEtaleBaseChangeFiberIso b (s ≫ a)).hom.app W x)
  have h₃ := toPresheafFiber_comp_eqToHom_smallEtaleStalkAb (Category.assoc s a b) G W x
  have h₆ := etaleAbelianInverseImageDirectImageAdj_unit_comp_unit a b G W
  have h₇ := chase_germ_w _ _ _ _ (Point.toPresheafFiber_w (Scheme.pointSmallEtale s)
      ((smallEtaleBaseChangeComp a b).inv.app W)
      ((pointSmallEtaleBaseChangeFiberIso a s).hom.app _
        ((pointSmallEtaleBaseChangeFiberIso b (s ≫ a)).hom.app W x))
      ((etaleAbelianInverseImage.{u, 0} a).obj
        ((etaleAbelianInverseImage.{u, 0} b).obj G)).obj)
    (congrArg (fun y => (Scheme.pointSmallEtale s).toPresheafFiber _ y
      ((etaleAbelianInverseImage.{u, 0} a).obj
        ((etaleAbelianInverseImage.{u, 0} b).obj G)).obj)
      (pointSmallEtaleBaseChangeFiberIso_comp a b s W x))
  exact chase_stalkMap_comp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃
    (toPresheafFiber_comp_etaleAbelianInverseImageStalkMap (a ≫ b) s G W _)
    (Point.toPresheafFiber_naturality (Scheme.pointSmallEtale s)
      ((etaleAbelianInverseImageCompIso'.{u, 0} a b (a ≫ b) rfl).hom.app G).hom
      ((smallEtaleBaseChange (a ≫ b)).obj W)
      ((pointSmallEtaleBaseChangeFiberIso (a ≫ b) s).hom.app W _)) h₆ h₇

/-- Naturality of the identification of stalks of an inverse image. -/
theorem etaleAbelianInverseImageStalkMap_naturality (f : X' ⟶ X) (s : Spec (.of Ω) ⟶ X')
    {G G' : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (τ : G ⟶ G') :
    (smallEtaleStalkAb (s ≫ f)).map τ ≫ etaleAbelianInverseImageStalkMap f s G' =
      etaleAbelianInverseImageStalkMap f s G ≫
        (smallEtaleStalkAb s).map ((etaleAbelianInverseImage.{u, 0} f).map τ) := by
  have h₁ := (smallEtaleStalkPullbackAbIso f s).inv.naturality τ
  have h₂ := ((smallEtaleStalkAb s).map_comp _ _).symm.trans
    ((congrArg (smallEtaleStalkAb s).map
      ((smallEtalePullbackAbIsoEtaleAbelianInverseImage f).hom.naturality τ)).trans
        ((smallEtaleStalkAb s).map_comp _ _))
  exact chase_naturality _ _ _ _ _ _ _ h₁ h₂

end StalkMap

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology
attribute [local instance] HasDerivedCategory.standard

open Stacks.EtaleCohomology

/-- The bookkeeping behind
`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.stalkTransition_comp`, with every
object and morphism a variable: `S` stands for the stalk functor at `s`, `Tφ`, `Tψ`, `Tab` for the
three transition maps, `hcomp` for the sheaf-level pasting law and `hA` for the composition of the
identifications of stalks of inverse images. -/
private theorem stalkTransition_comp_chase {C D : Type*} [Category* C] [Category* D] (S : D ⥤ C)
    {S₀ S₀' X₁ S₁ : C} {d₀ d₁ d₂ d₃ d₄ : D} (Tφ : S₀ ⟶ S₁) (Tψ : S₁ ⟶ S.obj d₃)
    (Tab : S₀' ⟶ S.obj d₄) (eq : S₀ ⟶ S₀') (β₁ : S₀ ⟶ X₁) (m₁ : X₁ ⟶ S₁)
    (β₂ : S₁ ⟶ S.obj d₂) (β₂' : X₁ ⟶ S.obj d₁) (βab : S₀' ⟶ S.obj d₀) (Φ : d₀ ⟶ d₁)
    (p : d₁ ⟶ d₂) (bψ : d₂ ⟶ d₃) (rinv : d₃ ⟶ d₄) (bab : d₀ ⟶ d₄) (rhom : d₄ ⟶ d₃)
    (hTφ : Tφ = β₁ ≫ m₁) (hTψ : Tψ = β₂ ≫ S.map bψ) (hTab : Tab = βab ≫ S.map bab)
    (hnat : m₁ ≫ β₂ = β₂' ≫ S.map p) (hA : β₁ ≫ β₂' = eq ≫ βab ≫ S.map Φ)
    (hcomp : bab = Φ ≫ p ≫ bψ ≫ rinv) (hc : rinv ≫ rhom = 𝟙 _) :
    Tφ ≫ Tψ = eq ≫ Tab ≫ S.map rhom := by
  simp only [hTφ, hTψ, hTab, hcomp, Functor.map_comp, Category.assoc]
  rw [← S.map_comp rinv rhom, hc, S.map_id, Category.comp_id, reassoc_of% hnat,
    reassoc_of% hA]

/-- An element killed by `d` is killed by `a ≫ b` when `d ≫ e = a ≫ b ≫ J.hom` for an
isomorphism `J`. -/
private theorem eq_zero_of_comp_eq {P Q R S T : AddCommGrpCat.{u + 1}} (a : P ⟶ Q) (b : Q ⟶ R)
    (J : R ≅ S) (d : P ⟶ T) (e : T ⟶ S) (h : d ≫ e = a ≫ b ≫ J.hom) (x : P) (hx : d x = 0) :
    (a ≫ b) x = 0 := by
  have h₁ := ConcreteCategory.congr_hom h x
  simp only [ConcreteCategory.comp_apply, hx, map_zero] at h₁
  rw [ConcreteCategory.comp_apply]
  have h₂ := congrArg J.inv h₁.symm
  simpa using h₂

namespace ProperModel

variable {B : Type u} [CommRing B]

/-- The transition map of stalks is the identification of the stalk of the inverse image followed
by the stalk of the base change map. -/
theorem Refinement.stalkTransition_eq {M' M : ProperModel B} (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M'.Y) :
    φ.stalkTransition F q s =
      etaleAbelianInverseImageStalkMap φ.π s
          (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) ≫
        (smallEtaleStalkAb s).map
          (etaleAbelianInverseImageRightDerivedDirectImageBaseChange M.j φ.π (𝟙 _) M'.j
            (by rw [Category.id_comp, φ.fac]) F q) := by
  rw [Refinement.stalkTransition, etaleAbelianInverseImageStalkMap, Iso.app_inv,
    Functor.map_comp, Category.assoc]

/-- **The cocycle of the transition maps of stalks** (the stalk form of the
transport cocycle `(g^π)^ρ = g^{πρ}`). For refinements `ψ : Y'' ⟶ Y'` and `φ : Y' ⟶ Y` and a geometric
point `s` of `Y''`, the transition map of `φ` at `s ≫ ψ` followed by that of `ψ` at `s` is the
transition map of the composite at `s` (the stalks at `(s ≫ ψ) ≫ φ` and `s ≫ (ψ ≫ φ)` being
identified), followed by the identification `𝟙⁻¹ F ≅ 𝟙⁻¹ 𝟙⁻¹ F` of the coefficients. It is the
stalk at `s` of the sheaf-level pasting law
`Stacks.EtaleCohomology.etaleAbelianInverseImageRightDerivedDirectImageBaseChange_comp`, through
`Stacks.EtaleCohomology.etaleAbelianInverseImageStalkMap_comp`. -/
theorem Refinement.stalkTransition_comp {M'' M' M : ProperModel B} (ψ : Refinement M'' M')
    (φ : Refinement M' M)
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ M''.Y) :
    φ.stalkTransition F q (s ≫ ψ.π) ≫
        ψ.stalkTransition ((etaleAbelianInverseImage.{u, 0} (𝟙 _)).obj F) q s =
      eqToHom (by rw [Category.assoc]; rfl) ≫ (ψ.comp φ).stalkTransition F q s ≫
        (smallEtaleStalkAb s).map (((etaleAbelianDirectImage.{u, 0} M''.j).rightDerived q).map
          ((etaleAbelianInverseImageCompIso'.{u, 0} (𝟙 _) (𝟙 _) (𝟙 _)
            (Category.comp_id _).symm).hom.app F)) := by
  have sq₁ : 𝟙 _ ≫ M.j = M'.j ≫ φ.π := by rw [Category.id_comp, φ.fac]
  have sq₂ : 𝟙 _ ≫ M'.j = M''.j ≫ ψ.π := by rw [Category.id_comp, ψ.fac]
  have hyp : 𝟙 _ ≫ M.j = M''.j ≫ (ψ.comp φ).π := by rw [Category.id_comp, (ψ.comp φ).fac]
  have hcomp := etaleAbelianInverseImageRightDerivedDirectImageBaseChange_comp φ.π M.j M'.j
    (𝟙 _) ψ.π M''.j (𝟙 _) sq₁ sq₂ (ψ.comp φ).π rfl (𝟙 _) (Category.comp_id _).symm hyp F q
  have hc : ((etaleAbelianDirectImage.{u, 0} M''.j).rightDerived q).map
        ((etaleAbelianInverseImageCompIso'.{u, 0} (𝟙 _) (𝟙 _) (𝟙 _)
          (Category.comp_id _).symm).inv.app F) ≫
      ((etaleAbelianDirectImage.{u, 0} M''.j).rightDerived q).map
        ((etaleAbelianInverseImageCompIso'.{u, 0} (𝟙 _) (𝟙 _) (𝟙 _)
          (Category.comp_id _).symm).hom.app F) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  exact stalkTransition_comp_chase (smallEtaleStalkAb s) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (stalkTransition_eq φ F q (s ≫ ψ.π))
    (stalkTransition_eq ψ ((etaleAbelianInverseImage.{u, 0} (𝟙 _)).obj F) q s)
    (stalkTransition_eq (ψ.comp φ) F q s)
    (etaleAbelianInverseImageStalkMap_naturality ψ.π s _)
    (etaleAbelianInverseImageStalkMap_comp ψ.π φ.π (ψ.comp φ).π rfl s
      (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F))
    hcomp hc

end ProperModel

/-- **Death is stable under further refinement** (the transport cocycle, stalk
form): a germ dying along `Y' ⟶ Y` at `s ≫ ψ` dies along every composite `Y'' ⟶ Y' ⟶ Y` at `s`, by
the cocycle `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.Refinement.stalkTransition_comp`
of the transition maps, the identification of the coefficients being an isomorphism. -/
theorem deadAtStableUnderRefinement : DeadAtStableUnderRefinement.{u} := by
  intro B _ _ M'' M' M ψ φ F q U g Ω _ _ s s' hs t ht ht' ℓ hd
  subst hs ht
  unfold ProperModel.Refinement.DeadAt at hd ⊢
  rw [eqToHom_refl, Category.id_comp] at hd
  exact eq_zero_of_comp_eq _ _ ((smallEtaleStalkAb s).mapIso
    (((etaleAbelianDirectImage.{u, 0} M''.j).rightDerived q).mapIso
      ((etaleAbelianInverseImageCompIso'.{u, 0} (𝟙 _) (𝟙 _) (𝟙 _)
        (Category.comp_id _).symm).app F))) _ _
    (ProperModel.Refinement.stalkTransition_comp ψ φ F q s) _ hd

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
