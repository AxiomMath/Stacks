module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.PullbackSystemCohomologyColimit

/-!
# The inverse image of a system of étale sheaves along a morphism of inverse systems

Let `e : D' ⟶ D` be a morphism of inverse systems of schemes over `Iᵒᵖ`, so that for `i' ≥ i` the
square `D'(i' → i) ≫ e_i = e_{i'} ≫ D(i' → i)` commutes, and let `(F_i, φ_{i'i})` be a system of
abelian sheaves on `D` in the sense of [Stacks, Tag 0EZL]. The inverse images `e_i^{-1}F_i` form a
system on `D'`: the transition at `i' ≥ i` is the comparison of the inverse images along the two
sides of the square, followed by `e_{i'}^{-1}φ_{i'i}`.

If moreover `c'` and `c` are cones over `D'` and `D` and `e_∞ : c'.pt ⟶ c.pt` is compatible with
the projections, then the inverse image along `e_∞` of a sheaf presenting `colim f_i^{-1}F_i`
presents `colim f'_i^{-1}e_i^{-1}F_i`: inverse image is a left adjoint.

This is the localisation of a presented system that [Stacks, Tag 0EYM] needs: the base changes
`U_i ×_{S_i} X_{i'}` of the levels of `X` along an étale `U_i ⟶ S_i` form an inverse system with
limit `U ×_S X`, and the restrictions of a system of sheaves on the `X_{i'}` form a system on it,
presented by the restriction of the presenting sheaf.

## Main definitions

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.baseChangeTransition` — the transition map.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.systemBaseChange` — **the system
  `e_i^{-1}F_i` on `D'`.**

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.baseChangeTransition_cocycle` — the cocycle
  condition.

## Implementation notes

All comparisons are `Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'`, with composites
named; the cocycle condition reduces, after moving the transitions of `F` past the comparisons by
naturality, to three instances of its associativity pentagon
`Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'_hom_app_map_inv_app`.

## References

* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology.SmallEtaleLimitCohomology

/-- The rearrangement behind `baseChangeTransition_cocycle`, in an abstract category: three
pentagons determine the composite of five comparisons. -/
theorem cube_algebra {C : Type*} [Category* C] {A₁ A₂ A₃ A₄ A₅ A₆ B₁ B₂ : C}
    (α : A₁ ≅ A₂) (β : A₂ ≅ A₃) (γ : A₃ ≅ A₄) (δ : A₄ ≅ A₅) (ε : A₅ ≅ A₆)
    (M : A₃ ≅ B₁) (N : A₁ ≅ B₁) (K : A₅ ≅ B₁) (ζ : A₆ ≅ B₂) (L : B₂ ≅ B₁)
    (h₁ : α.hom ≫ β.hom ≫ M.hom = N.hom) (h₂ : γ.inv ≫ M.hom = δ.hom ≫ K.hom)
    (h₃ : ε.hom ≫ ζ.hom ≫ L.hom = K.hom) :
    α.hom ≫ β.hom ≫ γ.hom ≫ δ.hom ≫ ε.hom = N.hom ≫ L.inv ≫ ζ.inv := by
  rw [← h₁, show M.hom = γ.hom ≫ δ.hom ≫ K.hom by rw [← h₂, Iso.hom_inv_id_assoc], ← h₃]
  simp

/-- The rearrangement behind `baseChangeLeg_compatible`, in an abstract category. -/
theorem cube_algebra' {C : Type*} [Category* C] {A₁ A₂ A₃ A₄ A₅ A₆ B B' : C}
    (α : A₁ ≅ A₂) (β : A₂ ≅ A₃) (γ : A₃ ≅ A₄) (δ : A₄ ≅ A₅) (ε : A₅ ≅ A₆)
    (M : A₃ ≅ B) (N : A₁ ≅ B) (K : A₅ ≅ B) (Z : B ≅ B') (W : B' ≅ A₆)
    (h₁ : α.hom ≫ β.hom ≫ M.hom = N.hom) (h₂ : γ.inv ≫ M.hom = δ.hom ≫ K.hom)
    (h₃ : ε.hom ≫ W.inv ≫ Z.inv = K.hom) :
    α.hom ≫ β.hom ≫ γ.hom ≫ δ.hom ≫ ε.hom = N.hom ≫ Z.hom ≫ W.hom :=
  cube_algebra α β γ δ ε M N K W.symm Z.symm h₁ h₂ h₃

section System

variable {I : Type v} [Preorder I] {D D' : Iᵒᵖ ⥤ Scheme.{u}} (e : D' ⟶ D)
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D'.obj i)) AddCommGrpCat.{u + 1}]

/-- **The transition map of the inverse image of a system along `e`.** At `a : i ⟶ j` it is the
comparison of the inverse images along the two sides of the naturality square
`D'(a) ≫ e_j = e_i ≫ D(a)`, followed by `e_i^{-1}` of the transition map of `F`. -/
def baseChangeTransition (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) {i j : Iᵒᵖ}
    (a : i ⟶ j) :
    (etaleAbelianInverseImage.{u, u + 1} (D'.map a)).obj
        ((etaleAbelianInverseImage.{u, u + 1} (e.app j)).obj (F.obj j)) ⟶
      (etaleAbelianInverseImage.{u, u + 1} (e.app i)).obj (F.obj i) :=
  (etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map a) (e.app j) (D'.map a ≫ e.app j)
      rfl).inv.app (F.obj j) ≫
    (etaleAbelianInverseImageCompIso'.{u, u + 1} (e.app i) (D.map a) (D'.map a ≫ e.app j)
      (e.naturality a)).hom.app (F.obj j) ≫
    (etaleAbelianInverseImage.{u, u + 1} (e.app i)).map (systemTransitionMap F a)

/-- **The comparisons of the cocycle condition.** The comparisons the transition maps of the
inverse image along `e` are built from, at `a` and `b`, compose to those at `a ≫ b`, read through
the comparisons along `D'(a ≫ b)` and `D(a ≫ b)`. -/
theorem baseChangeComparison_cocycle {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    (G : Sheaf (smallEtaleTopology (D.obj k)) AddCommGrpCat.{u + 1}) :
    (etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map a) (D'.map b) (D'.map (a ≫ b))
          (D'.map_comp a b)).hom.app ((etaleAbelianInverseImage.{u, u + 1} (e.app k)).obj G) ≫
        (etaleAbelianInverseImage.{u, u + 1} (D'.map a)).map
          ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map b) (e.app k)
              (D'.map b ≫ e.app k) rfl).inv.app G ≫
            (etaleAbelianInverseImageCompIso'.{u, u + 1} (e.app j) (D.map b)
              (D'.map b ≫ e.app k) (e.naturality b)).hom.app G) ≫
        (etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map a) (e.app j)
            (D'.map a ≫ e.app j) rfl).inv.app
          ((etaleAbelianInverseImage.{u, u + 1} (D.map b)).obj G) ≫
        (etaleAbelianInverseImageCompIso'.{u, u + 1} (e.app i) (D.map a)
            (D'.map a ≫ e.app j) (e.naturality a)).hom.app
          ((etaleAbelianInverseImage.{u, u + 1} (D.map b)).obj G) =
      (etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map (a ≫ b)) (e.app k)
          (D'.map (a ≫ b) ≫ e.app k) rfl).inv.app G ≫
        (etaleAbelianInverseImageCompIso'.{u, u + 1} (e.app i) (D.map (a ≫ b))
          (D'.map (a ≫ b) ≫ e.app k) (e.naturality (a ≫ b))).hom.app G ≫
        (etaleAbelianInverseImage.{u, u + 1} (e.app i)).map
          ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (D.map b) (D.map (a ≫ b))
            (D.map_comp a b)).hom.app G) := by
  have hP₁ : D'.map (a ≫ b) ≫ e.app k = D'.map a ≫ (D'.map b ≫ e.app k) := by
    rw [D'.map_comp, Category.assoc]
  have hP₂ : D'.map (a ≫ b) ≫ e.app k = (D'.map a ≫ e.app j) ≫ D.map b := by
    rw [hP₁, e.naturality b, Category.assoc]
  have hP₃ : D'.map (a ≫ b) ≫ e.app k = e.app i ≫ D.map (a ≫ b) := e.naturality (a ≫ b)
  have hpent₁ := etaleAbelianInverseImageCompIso'_hom_app_map_inv_app (e.app k) (D'.map b)
    (D'.map a) (D'.map b ≫ e.app k) rfl (D'.map (a ≫ b)) (D'.map_comp a b)
    (D'.map (a ≫ b) ≫ e.app k) rfl hP₁ G
  have hpent₂ := etaleAbelianInverseImageCompIso'_hom_app_map_inv_app (D.map b) (e.app j)
    (D'.map a) (D'.map b ≫ e.app k) (e.naturality b) (D'.map a ≫ e.app j) rfl
    (D'.map (a ≫ b) ≫ e.app k) hP₂ hP₁ G
  have hpent₃ := etaleAbelianInverseImageCompIso'_hom_app_map_inv_app (D.map b) (D.map a)
    (e.app i) (D.map (a ≫ b)) (D.map_comp a b) (D'.map a ≫ e.app j) (e.naturality a)
    (D'.map (a ≫ b) ≫ e.app k) hP₂ hP₃ G
  rw [(etaleAbelianInverseImage.{u, u + 1} (D'.map a)).map_comp]
  exact cube_algebra
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map a) (D'.map b) (D'.map (a ≫ b))
      (D'.map_comp a b)).app ((etaleAbelianInverseImage.{u, u + 1} (e.app k)).obj G))
    ((etaleAbelianInverseImage.{u, u + 1} (D'.map a)).mapIso
      ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map b) (e.app k)
        (D'.map b ≫ e.app k) rfl).app G).symm)
    ((etaleAbelianInverseImage.{u, u + 1} (D'.map a)).mapIso
      ((etaleAbelianInverseImageCompIso'.{u, u + 1} (e.app j) (D.map b)
        (D'.map b ≫ e.app k) (e.naturality b)).app G))
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map a) (e.app j)
      (D'.map a ≫ e.app j) rfl).app ((etaleAbelianInverseImage.{u, u + 1} (D.map b)).obj G)).symm
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (e.app i) (D.map a)
      (D'.map a ≫ e.app j) (e.naturality a)).app
        ((etaleAbelianInverseImage.{u, u + 1} (D.map b)).obj G))
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map a) (D'.map b ≫ e.app k)
      (D'.map (a ≫ b) ≫ e.app k) hP₁).app G).symm
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map (a ≫ b)) (e.app k)
      (D'.map (a ≫ b) ≫ e.app k) rfl).app G).symm
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map a ≫ e.app j) (D.map b)
      (D'.map (a ≫ b) ≫ e.app k) hP₂).app G).symm
    ((etaleAbelianInverseImage.{u, u + 1} (e.app i)).mapIso
      ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (D.map b) (D.map (a ≫ b))
        (D.map_comp a b)).app G).symm)
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (e.app i) (D.map (a ≫ b))
      (D'.map (a ≫ b) ≫ e.app k) hP₃).app G).symm
    hpent₁ ((Iso.inv_comp_eq _).mp hpent₂) hpent₃

/-- **The cocycle condition for the inverse image of a system along `e`.** -/
theorem baseChangeTransition_cocycle (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) {i j k : Iᵒᵖ}
    (a : i ⟶ j) (b : j ⟶ k) :
    (etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map a) (D'.map b) (D'.map (a ≫ b))
          (D'.map_comp a b)).hom.app
          ((etaleAbelianInverseImage.{u, u + 1} (e.app k)).obj (F.obj k)) ≫
        (etaleAbelianInverseImage.{u, u + 1} (D'.map a)).map (baseChangeTransition e F b) ≫
          baseChangeTransition e F a =
      baseChangeTransition e F (a ≫ b) := by
  have hnat₁ := (etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map a) (e.app j)
    (D'.map a ≫ e.app j) rfl).inv.naturality (systemTransitionMap F b)
  have hnat₂ := (etaleAbelianInverseImageCompIso'.{u, u + 1} (e.app i) (D.map a)
    (D'.map a ≫ e.app j) (e.naturality a)).hom.naturality (systemTransitionMap F b)
  simp only [Functor.comp_map] at hnat₁ hnat₂
  dsimp only [baseChangeTransition]
  rw [(etaleAbelianInverseImage.{u, u + 1} (D'.map a)).map_comp,
    (etaleAbelianInverseImage.{u, u + 1} (D'.map a)).map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hnat₁, reassoc_of% hnat₂, ← systemTransitionMap_comp F a b,
    (etaleAbelianInverseImage.{u, u + 1} (e.app i)).map_comp,
    (etaleAbelianInverseImage.{u, u + 1} (e.app i)).map_comp]
  simp only [← Category.assoc]
  refine congrArg (fun z => z ≫ _) (congrArg (fun z => z ≫ _) ?_)
  simpa only [Category.assoc, Functor.map_comp] using
    baseChangeComparison_cocycle e a b (F.obj k)

/-- **The inverse image of a system along `e`**: the sheaves `e_i^{-1}F_i` on the levels of `D'`,
with the transition maps `baseChangeTransition`. -/
def systemBaseChange (F : EtaleSheafSystem D AddCommGrpCat.{u + 1}) :
    EtaleSheafSystem D' AddCommGrpCat.{u + 1} :=
  EtaleSheafSystem.ofInverseImage
    (fun i => (etaleAbelianInverseImage.{u, u + 1} (e.app i)).obj (F.obj i))
    (fun a => baseChangeTransition e F a) (fun a b => baseChangeTransition_cocycle e F a b)

/-- The transition map of `systemBaseChange e F` along `a` is `baseChangeTransition e F a`. -/
theorem systemTransitionMap_systemBaseChange (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemTransitionMap (systemBaseChange e F) a = baseChangeTransition e F a :=
  EtaleSheafSystem.systemTransitionMap_ofInverseImage _ _
    (fun a b => baseChangeTransition_cocycle e F a b) a

/-! ### The presentation on the limit -/

section Presentation

variable {c' : Cone D'} {c : Cone D}
  [HasSheafify (smallEtaleTopology c'.pt) AddCommGrpCat.{u + 1}]
  [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
  (eL : c'.pt ⟶ c.pt) (he : ∀ i : Iᵒᵖ, conePi c' i ≫ e.app i = eL ≫ conePi c i)

/-- The comparison `f'_i^{-1}e_i^{-1} ≅ e_∞^{-1}f_i^{-1}` along the square
`f'_i ≫ e_i = e_∞ ≫ f_i`, at a sheaf. -/
def baseChangeLegComparison (i : Iᵒᵖ)
    (G : Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}) :
    (etaleAbelianInverseImage.{u, u + 1} (conePi c' i)).obj
        ((etaleAbelianInverseImage.{u, u + 1} (e.app i)).obj G) ≅
      (etaleAbelianInverseImage.{u, u + 1} eL).obj
        ((etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj G) :=
  ((etaleAbelianInverseImageCompIso'.{u, u + 1} (conePi c' i) (e.app i) (conePi c' i ≫ e.app i)
      rfl).app G).symm ≪≫
    (etaleAbelianInverseImageCompIso'.{u, u + 1} eL (conePi c i) (conePi c' i ≫ e.app i)
      (he i)).app G

/-- **The comparisons of the legs commute with the transition maps.** -/
theorem baseChangeLegComparison_comm {i j : Iᵒᵖ} (a : i ⟶ j)
    (G : Sheaf (smallEtaleTopology (D.obj j)) AddCommGrpCat.{u + 1}) :
    (coneInverseImageComp (c := c') a).hom.app
          ((etaleAbelianInverseImage.{u, u + 1} (e.app j)).obj G) ≫
        (etaleAbelianInverseImage.{u, u + 1} (conePi c' i)).map
          ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map a) (e.app j) (D'.map a ≫ e.app j)
              rfl).inv.app G ≫
            (etaleAbelianInverseImageCompIso'.{u, u + 1} (e.app i) (D.map a) (D'.map a ≫ e.app j)
              (e.naturality a)).hom.app G) ≫
        (baseChangeLegComparison e eL he i
          ((etaleAbelianInverseImage.{u, u + 1} (D.map a)).obj G)).hom =
      (baseChangeLegComparison e eL he j G).hom ≫
        (etaleAbelianInverseImage.{u, u + 1} eL).map
          ((coneInverseImageComp (c := c) a).hom.app G) := by
  have hQ₁ : conePi c' j ≫ e.app j = conePi c' i ≫ (D'.map a ≫ e.app j) := by
    rw [← conePi_comp c' a, Category.assoc]
  have hQ₂ : conePi c' j ≫ e.app j = (conePi c' i ≫ e.app i) ≫ D.map a := by
    rw [hQ₁, e.naturality a, Category.assoc]
  have hQ₃ : conePi c' j ≫ e.app j = eL ≫ conePi c j := he j
  have hpent₁ := etaleAbelianInverseImageCompIso'_hom_app_map_inv_app (e.app j) (D'.map a)
    (conePi c' i) (D'.map a ≫ e.app j) rfl (conePi c' j) (conePi_comp c' a).symm
    (conePi c' j ≫ e.app j) rfl hQ₁ G
  have hpent₂ := etaleAbelianInverseImageCompIso'_hom_app_map_inv_app (D.map a) (e.app i)
    (conePi c' i) (D'.map a ≫ e.app j) (e.naturality a) (conePi c' i ≫ e.app i) rfl
    (conePi c' j ≫ e.app j) hQ₂ hQ₁ G
  have hpent₃ := etaleAbelianInverseImageCompIso'_hom_app_map_inv_app (D.map a) (conePi c i)
    eL (conePi c j) (conePi_comp c a).symm (conePi c' i ≫ e.app i) (he i)
    (conePi c' j ≫ e.app j) hQ₂ hQ₃ G
  dsimp only [baseChangeLegComparison, coneInverseImageComp, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv]
  rw [(etaleAbelianInverseImage.{u, u + 1} (conePi c' i)).map_comp]
  exact cube_algebra'
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (conePi c' i) (D'.map a) (conePi c' j)
      (conePi_comp c' a).symm).app ((etaleAbelianInverseImage.{u, u + 1} (e.app j)).obj G))
    ((etaleAbelianInverseImage.{u, u + 1} (conePi c' i)).mapIso
      ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map a) (e.app j)
        (D'.map a ≫ e.app j) rfl).app G).symm)
    ((etaleAbelianInverseImage.{u, u + 1} (conePi c' i)).mapIso
      ((etaleAbelianInverseImageCompIso'.{u, u + 1} (e.app i) (D.map a)
        (D'.map a ≫ e.app j) (e.naturality a)).app G))
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (conePi c' i) (e.app i)
      (conePi c' i ≫ e.app i) rfl).app ((etaleAbelianInverseImage.{u, u + 1} (D.map a)).obj G)).symm
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} eL (conePi c i)
      (conePi c' i ≫ e.app i) (he i)).app ((etaleAbelianInverseImage.{u, u + 1} (D.map a)).obj G))
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (conePi c' i) (D'.map a ≫ e.app j)
      (conePi c' j ≫ e.app j) hQ₁).app G).symm
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (conePi c' j) (e.app j)
      (conePi c' j ≫ e.app j) rfl).app G).symm
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (conePi c' i ≫ e.app i) (D.map a)
      (conePi c' j ≫ e.app j) hQ₂).app G).symm
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} eL (conePi c j)
      (conePi c' j ≫ e.app j) hQ₃).app G)
    ((etaleAbelianInverseImage.{u, u + 1} eL).mapIso
      ((etaleAbelianInverseImageCompIso'.{u, u + 1} (conePi c i) (D.map a) (conePi c j)
        (conePi_comp c a).symm).app G))
    hpent₁ ((Iso.inv_comp_eq _).mp hpent₂) hpent₃

/-- The comparisons of the legs are natural in the sheaf. -/
theorem baseChangeLegComparison_naturality (i : Iᵒᵖ)
    {G₁ G₂ : Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}} (f : G₁ ⟶ G₂) :
    (etaleAbelianInverseImage.{u, u + 1} (conePi c' i)).map
          ((etaleAbelianInverseImage.{u, u + 1} (e.app i)).map f) ≫
        (baseChangeLegComparison e eL he i G₂).hom =
      (baseChangeLegComparison e eL he i G₁).hom ≫
        (etaleAbelianInverseImage.{u, u + 1} eL).map
          ((etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map f) := by
  have h₁ := (etaleAbelianInverseImageCompIso'.{u, u + 1} (conePi c' i) (e.app i)
    (conePi c' i ≫ e.app i) rfl).inv.naturality f
  have h₂ := (etaleAbelianInverseImageCompIso'.{u, u + 1} eL (conePi c i)
    (conePi c' i ≫ e.app i) (he i)).hom.naturality f
  simp only [Functor.comp_map] at h₁ h₂
  dsimp only [baseChangeLegComparison, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv]
  rw [reassoc_of% h₁, h₂, Category.assoc]

/-- **The comparisons of the legs commute with the diagram maps** of the two systems. -/
theorem baseChangeLegComparison_transition (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    (coneInverseImageComp (c := c') a).hom.app
          ((etaleAbelianInverseImage.{u, u + 1} (e.app j)).obj (F.obj j)) ≫
        (etaleAbelianInverseImage.{u, u + 1} (conePi c' i)).map (baseChangeTransition e F a) ≫
        (baseChangeLegComparison e eL he i (F.obj i)).hom =
      (baseChangeLegComparison e eL he j (F.obj j)).hom ≫
        (etaleAbelianInverseImage.{u, u + 1} eL).map
          ((coneInverseImageComp (c := c) a).hom.app (F.obj j) ≫
            (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (systemTransitionMap F a)) := by
  have hm : (etaleAbelianInverseImage.{u, u + 1} (conePi c' i)).map
        (baseChangeTransition e F a) =
      (etaleAbelianInverseImage.{u, u + 1} (conePi c' i)).map
          ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D'.map a) (e.app j) (D'.map a ≫ e.app j)
              rfl).inv.app (F.obj j) ≫
            (etaleAbelianInverseImageCompIso'.{u, u + 1} (e.app i) (D.map a) (D'.map a ≫ e.app j)
              (e.naturality a)).hom.app (F.obj j)) ≫
        (etaleAbelianInverseImage.{u, u + 1} (conePi c' i)).map
          ((etaleAbelianInverseImage.{u, u + 1} (e.app i)).map (systemTransitionMap F a)) := by
    rw [← Functor.map_comp, Category.assoc]
    rfl
  rw [hm, Category.assoc,
    baseChangeLegComparison_naturality e eL he i (systemTransitionMap F a),
    (etaleAbelianInverseImage.{u, u + 1} eL).map_comp]
  simpa only [Category.assoc] using congrArg (fun z => z ≫
    (etaleAbelianInverseImage.{u, u + 1} eL).map
      ((etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (systemTransitionMap F a)))
    (baseChangeLegComparison_comm e eL he a (F.obj j))

/-- The comparisons of the legs commute with the diagram maps, written with the transition maps
of the inverse image of the system. -/
theorem baseChangeLegComparison_systemTransitionMap (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    (coneInverseImageComp (c := c') a).hom.app ((systemBaseChange e F).obj j) ≫
        (etaleAbelianInverseImage.{u, u + 1} (conePi c' i)).map
          (systemTransitionMap (systemBaseChange e F) a) ≫
        (baseChangeLegComparison e eL he i (F.obj i)).hom =
      (baseChangeLegComparison e eL he j (F.obj j)).hom ≫
        (etaleAbelianInverseImage.{u, u + 1} eL).map
          ((coneInverseImageComp (c := c) a).hom.app (F.obj j) ≫
            (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (systemTransitionMap F a)) :=
  (congrArg (fun z => (coneInverseImageComp (c := c') a).hom.app ((systemBaseChange e F).obj j) ≫
      (etaleAbelianInverseImage.{u, u + 1} (conePi c' i)).map z ≫
        (baseChangeLegComparison e eL he i (F.obj i)).hom)
    (systemTransitionMap_systemBaseChange e F a)).trans
    (baseChangeLegComparison_transition e eL he F a)

/-- Conjugating a commuting square by two isomorphisms, in an abstract category. -/
private theorem conj_square {C : Type*} [Category* C] {A B P Q R E : C} (kj : A ≅ B)
    (m₁ : A ⟶ P) (m₂ : P ⟶ Q) (ki : Q ≅ R) (x : B ⟶ R) (t : Q ⟶ E)
    (h : m₁ ≫ m₂ ≫ ki.hom = kj.hom ≫ x) : x ≫ ki.inv ≫ t = kj.inv ≫ m₁ ≫ m₂ ≫ t := by
  rw [show x = kj.inv ≫ m₁ ≫ m₂ ≫ ki.hom by rw [h, Iso.inv_hom_id_assoc]]
  simp

/-- **The legs of the inverse image of a presented system**: the comparison
`f'_i^{-1}e_i^{-1}F_i ≅ e_∞^{-1}f_i^{-1}F_i` followed by the inverse image along `e_∞` of the leg
`f_i^{-1}F_i ⟶ 𝒢`. -/
def baseChangeLeg (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    {𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    (ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢)
    (i : Iᵒᵖ) :
    (etaleAbelianInverseImage.{u, u + 1} (conePi c' i)).obj ((systemBaseChange e F).obj i) ⟶
      (etaleAbelianInverseImage.{u, u + 1} eL).obj 𝒢 :=
  (baseChangeLegComparison e eL he i (F.obj i)).hom ≫
    (etaleAbelianInverseImage.{u, u + 1} eL).map (ι i)

/-- **The inverse image along `e_∞` of a colimit presentation is a colimit presentation** of the
inverse image of the system along `e`. Inverse image is a left adjoint: a compatible family of
maps out of the `f'_i^{-1}e_i^{-1}F_i` is, through the comparisons of the legs, a compatible
family of maps out of the `e_∞^{-1}f_i^{-1}F_i`, which by adjunction is a compatible family of
maps out of the `f_i^{-1}F_i`. -/
theorem isColimitPresentation_systemBaseChange (F : EtaleSheafSystem D AddCommGrpCat.{u + 1})
    {𝒢 : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
    {ι : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶ 𝒢}
    (h : IsColimitPresentation F 𝒢 ι) :
    IsColimitPresentation (systemBaseChange e F) ((etaleAbelianInverseImage.{u, u + 1} eL).obj 𝒢)
      (baseChangeLeg e eL he F ι) := by
  let adj := etaleAbelianInverseImageDirectImageAdj.{u, u + 1} eL
  let κ := fun i => baseChangeLegComparison e eL he i (F.obj i)
  have hsymm : ∀ {A : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
      {B : Sheaf (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}}
      {H : Sheaf (smallEtaleTopology c'.pt) AddCommGrpCat.{u + 1}} (f : A ⟶ B)
      (g : (etaleAbelianInverseImage.{u, u + 1} eL).obj B ⟶ H),
      (adj.homEquiv _ _).symm (f ≫ adj.homEquiv _ _ g) =
        (etaleAbelianInverseImage.{u, u + 1} eL).map f ≫ g := fun f g => by
    rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]
  refine ⟨fun {i j} a => ?_, fun H τ' hτ' => ?_⟩
  · dsimp only [baseChangeLeg]
    refine ((reassoc_of% (baseChangeLegComparison_systemTransitionMap e eL he F a))
      ((etaleAbelianInverseImage.{u, u + 1} eL).map (ι i))).trans ?_
    exact (Category.assoc _ _ _).trans (congrArg (fun z => _ ≫ z)
      (((etaleAbelianInverseImage.{u, u + 1} eL).map_comp _ _).symm.trans
        (congrArg (etaleAbelianInverseImage.{u, u + 1} eL).map
          ((Category.assoc _ _ _).trans (h.compatible a)))))
  · let τ : ∀ i : Iᵒᵖ, (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj (F.obj i) ⟶
        (etaleAbelianDirectImage.{u, u + 1} eL).obj H :=
      fun i => adj.homEquiv _ _ ((κ i).inv ≫ τ' i)
    have hτ : IsCompatibleFamily F _ τ := by
      intro i j a
      have key : (adj.homEquiv _ _).symm (((coneInverseImageComp (c := c) a).hom.app (F.obj j) ≫
            (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map (systemTransitionMap F a)) ≫
              τ i) = (adj.homEquiv _ _).symm (τ j) :=
        calc _ = (etaleAbelianInverseImage.{u, u + 1} eL).map
              ((coneInverseImageComp (c := c) a).hom.app (F.obj j) ≫
                (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).map
                  (systemTransitionMap F a)) ≫ (κ i).inv ≫ τ' i :=
              hsymm _ ((κ i).inv ≫ τ' i)
          _ = (κ j).inv ≫ (coneInverseImageComp (c := c') a).hom.app
                ((systemBaseChange e F).obj j) ≫
              (etaleAbelianInverseImage.{u, u + 1} (conePi c' i)).map
                (systemTransitionMap (systemBaseChange e F) a) ≫ τ' i :=
              conj_square (κ j) _ _ (κ i) _ (τ' i)
                (baseChangeLegComparison_systemTransitionMap e eL he F a)
          _ = (κ j).inv ≫ τ' j := congrArg (fun z => (κ j).inv ≫ z) (hτ' a)
          _ = _ := (Equiv.symm_apply_apply _ _).symm
      simpa only [Category.assoc] using (adj.homEquiv _ _).symm.injective key
    have hleg : ∀ (i : Iᵒᵖ) (y : (etaleAbelianInverseImage.{u, u + 1} eL).obj 𝒢 ⟶ H),
        baseChangeLeg e eL he F ι i ≫ y = τ' i ↔ ι i ≫ adj.homEquiv _ _ y = τ i := fun i y => by
      change (κ i).hom ≫ _ ≫ y = _ ↔ _
      refine (Iso.eq_inv_comp (κ i)).symm.trans ?_
      rw [← hsymm, Equiv.symm_apply_eq]
    obtain ⟨χ, hχ, hχu⟩ := h.existsUnique_desc _ τ hτ
    refine ⟨(adj.homEquiv _ _).symm χ, fun i => (hleg i _).mpr ?_, fun y hy => ?_⟩
    · rw [Equiv.apply_symm_apply]
      exact hχ i
    · exact (Equiv.symm_apply_apply (adj.homEquiv _ _) y).symm.trans
        (congrArg _ (hχu _ fun i => (hleg i y).mp (hy i)))

end Presentation

end System


end Stacks.EtaleCohomology.SmallEtaleLimitCohomology

end
