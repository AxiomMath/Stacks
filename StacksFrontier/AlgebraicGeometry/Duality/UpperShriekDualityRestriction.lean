module

public import StacksFrontier.AlgebraicGeometry.Duality.OpenImmersion.SheafHomRestrictionComp
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Composition

/-!
# The duality formula of [Stacks, Tag 0AU2] restricted to an open

Let `g : X ⟶ Y` be a morphism of `FTS_S`, `j` a compactification of `X` over `Y`, `K` a
dualizing complex on `Y`, and `h : X' ⟶ X` a morphism of `FTS_S` which is an open immersion.
Then `(h ≫ g)^!` may be computed at the compactification `X' ⊆ X ⊆ X̄` restricted from `j`, and
the isomorphism `g^!M ≅ R𝓗om(Lg^* D_Y(M), g^!K)` of [Stacks, Tag 0AU2] restricts along `h` to
the one for `h ≫ g`, through `Lh^* ∘ g^! ≅ (h ≫ g)^!` and the restriction of the derived
internal Hom of [Stacks, Tag 08DL].

## Main results

* `Stacks.Duality.UpperShriekDuality.upperShriekStdRestrictIso`,
  `Stacks.Duality.UpperShriekDuality.upperShriekDualizingRestrictIso`: `Lh^* ∘ g^! ≅ (h ≫ g)^!`
  and `Lh^*(g^!K) ≅ (h ≫ g)^!K`, at the standard model.
* `Stacks.Duality.UpperShriekDuality.upperShriekDualityIso_restrict`: the restriction of the
  isomorphism of [Stacks, Tag 0AU2].

## References

* [Stacks Project, Tag 0AU2](https://stacks.math.columbia.edu/tag/0AU2)
* [Stacks Project, Tag 08DL](https://stacks.math.columbia.edu/tag/08DL)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace Stacks.Duality.TwistedInverseImageDuality

attribute [local instance 10000] HasDerivedCategory.standard

variable {A B : Scheme.{u}} (g : A ⟶ B)

/-- **The canonical map is natural in the second variable.** -/
theorem pullSheafHomMap_naturality_right (P : Std B) {Z Z' : Std B} (z : Z ⟶ Z') :
    (pull g).map (((sheafHom B).obj (op P)).map z) ≫ pullSheafHomMap g P Z' =
      pullSheafHomMap g P Z ≫ ((sheafHom A).obj (op ((pull g).obj P))).map ((pull g).map z) := by
  apply (curry A _ _ _).injective
  rw [curry_pull_map_comp_pullSheafHomMap, curry_naturality_right, curry_pullSheafHomMap]
  have hz : curry B _ P Z' (((sheafHom B).obj (op P)).map z) = evaluation P Z ≫ z := by
    rw [evaluation_eq, ← curry_naturality_right, Category.id_comp]
  rw [hz, CategoryTheory.Functor.map_comp, Category.assoc]

end Stacks.Duality.TwistedInverseImageDuality

namespace Stacks.Duality.UpperShriekDuality

open Stacks.Duality.TwistedInverseImageDuality

attribute [local instance 10000] HasDerivedCategory.standard

variable {S : Scheme.{u}} [IsNoetherian S] {X' X Y : FTS S} (h : X' ⟶ X) [IsOpenImmersion h.left]
  (g : X ⟶ Y) (j : CompactificationOf (Over.mk g.left))

/-- `f^!` read at the standard model, restricted to an open: `Lh^* ∘ g^!_j ≅ (h ≫ g)^!` at the
compactification restricted along `h`. -/
def upperShriekStdRestrictIso :
    upperShriekStd g j ⋙ pull h.left ≅ upperShriekStd (h ≫ g) (j.precompOpen h.left) :=
  Functor.isoWhiskerRight (upperShriekStdIso g j) (pull h.left) ≪≫
    Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (pullCompIso h.left j.immersion (h.left ≫ j.immersion) rfl)) ≪≫
    (upperShriekStdIso (h ≫ g) (j.precompOpen h.left)).symm

variable {K : Std Y.left} (hK : IsDualizing K)

/-- `f^!K`, read at the standard model, restricted to an open. -/
def upperShriekDualizingRestrictIso :
    (pull h.left).obj (upperShriekDualizing g j hK) ≅
      upperShriekDualizing (h ≫ g) (j.precompOpen h.left) hK :=
  (pull h.left).mapIso ((pullModelConj j.immersion).app
      ((rightAdjointStd j.toBase).obj (dualizingObject hK))) ≪≫
    (pullCompIso h.left j.immersion (h.left ≫ j.immersion) rfl).app
      ((rightAdjointStd j.toBase).obj (dualizingObject hK)) ≪≫
    ((pullModelConj (h.left ≫ j.immersion)).app
      ((rightAdjointStd j.toBase).obj (dualizingObject hK))).symm

/-- The chase behind `upperShriekDualityIso_restrict`. -/
theorem upperShriekDualityIso_restrict_chase {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (L : 𝒟 ⥤ 𝒞) {d0 d1 d2 d3 d4 d5 : 𝒟} {e1 e2 e3 f1 f2 f3 f4 f5 g0 g1 g2 g3 : 𝒞}
    (m0 : d0 ⟶ d1) (dI : d1 ⟶ d2) (ps : d2 ⟶ d3) (s1 : d3 ⟶ d4) (t1 : d4 ⟶ d5)
    (q : L.obj d5 ⟶ e1) (s2 : e1 ⟶ e2) (t2 : e2 ⟶ e3)
    (a2 : L.obj d1 ⟶ f1) (a3 : f1 ⟶ f2) (b0 : f2 ⟶ f1) (b1 : f1 ⟶ f3) (b2 : f3 ⟶ f4)
    (b3 : f4 ⟶ f5) (b4 : f5 ⟶ e3)
    (a2' : L.obj d2 ⟶ f3) (q0 : L.obj d3 ⟶ g0) (s0 : g0 ⟶ g1) (t0 : g1 ⟶ f4)
    (q1 : L.obj d4 ⟶ g2) (s1' : g0 ⟶ g2) (t1' : g2 ⟶ e1) (s2' : g2 ⟶ g3) (t1'' : g3 ⟶ e2)
    (b3' : g1 ⟶ g3) (t0' : g3 ⟶ f5)
    (F1 : a3 ≫ b0 = 𝟙 _) (F2 : a2 ≫ b1 = L.map dI ≫ a2')
    (F3 : a2' ≫ b2 = L.map ps ≫ q0 ≫ s0 ≫ t0) (F4 : L.map s1 ≫ q1 = q0 ≫ s1')
    (F5 : L.map t1 ≫ q = q1 ≫ t1') (F6 : t1' ≫ s2 = s2' ≫ t1'') (F8 : t0 ≫ b3 = b3' ≫ t0')
    (F7 : s0 ≫ b3' = s1' ≫ s2') (F9 : t0' ≫ b4 = t1'' ≫ t2) {T : d0 ⟶ d5} {α : L.obj d0 ⟶ f2}
    {β : f2 ⟶ e3} (hT : T = m0 ≫ dI ≫ ps ≫ s1 ≫ t1) (hα : α = L.map m0 ≫ a2 ≫ a3)
    (hβ : β = b0 ≫ b1 ≫ b2 ≫ b3 ≫ b4) :
    L.map T ≫ q ≫ s2 ≫ t2 = α ≫ β := by
  subst hT hα hβ
  simp only [L.map_comp, Category.assoc]
  rw [reassoc_of% F1, reassoc_of% F2, reassoc_of% F3, reassoc_of% F8, reassoc_of% F7, F9,
    reassoc_of% F5, reassoc_of% F6, reassoc_of% F4]

omit [AlgebraicGeometry.IsNoetherian S] in
/-- A functor applied to two equal composites. -/
theorem map_comp_map_eq_of_comp_eq {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (F : 𝒞 ⥤ 𝒟)
    {a b c b' : 𝒞} (x : a ⟶ b) (y : b ⟶ c) (x' : a ⟶ b') (y' : b' ⟶ c) (e : x ≫ y = x' ≫ y') :
    F.map x ≫ F.map y = F.map x' ≫ F.map y' := by
  rw [← F.map_comp, e, F.map_comp]

omit [AlgebraicGeometry.IsNoetherian S] in
/-- Cancelling `F.map e.inv` against `F.mapIso e`. -/
theorem map_inv_comp_mapIso_hom_comp_trans_hom {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (F : 𝒞 ⥤ 𝒟) {a b : 𝒞} {c d : 𝒟} (e : a ≅ b) (x : F.obj b ≅ c) (y : c ≅ d) :
    x.hom ≫ y.hom = F.map e.inv ≫ (F.mapIso e).hom ≫ (x ≪≫ y).hom := by
  simp

omit [AlgebraicGeometry.IsNoetherian S] in
/-- Solving `x = e.inv ≫ r` for `e.hom ≫ x`. -/
theorem hom_comp_eq_of_eq_inv_comp {𝒞 : Type*} [Category 𝒞] {a b c : 𝒞} (e : a ≅ b)
    (x : b ⟶ c) (r : a ⟶ c) (h : x = e.inv ≫ r) : e.hom ≫ x = r := by
  rw [h, Iso.hom_inv_id_assoc]

/-- The components of `upperShriekStdRestrictIso`. -/
theorem upperShriekStdRestrictIso_hom_app (M : (plusCoh Y.left).FullSubcategory) :
    (upperShriekStdRestrictIso h g j).hom.app M =
      (pull h.left).map ((upperShriekStdIso g j).hom.app M) ≫
        (pullCompIso h.left j.immersion (h.left ≫ j.immersion) rfl).hom.app _ ≫
        (upperShriekStdIso (h ≫ g) (j.precompOpen h.left)).inv.app M := by
  simp [upperShriekStdRestrictIso]
  rfl

/-- **The isomorphism of [Stacks, Tag 0AU2] restricts to opens.** For an open immersion
`h : X' ⟶ X` and a compactification `j` of `g : X ⟶ Y`, restricting
`g^!M ≅ R𝓗om(Lg^* D_Y(M), g^!K)` along `h` gives the isomorphism for `h ≫ g` at the
compactification restricted along `h`, through `Lh^* ∘ g^! ≅ (h ≫ g)^!` and [Stacks, Tag 08DL]. -/
theorem upperShriekDualityIso_restrict (M : (plusCoh Y.left).FullSubcategory) :
    (pull h.left).map ((upperShriekDualityIso g j hK).hom.app M) ≫
        pullSheafHomMap h.left ((pull g.left).obj (((sheafHom Y.left).obj (op M.obj)).obj K))
          (upperShriekDualizing g j hK) ≫
        ((sheafHom X'.left).map ((pullCompIso h.left g.left (h ≫ g).left rfl).inv.app
          (((sheafHom Y.left).obj (op M.obj)).obj K)).op).app _ ≫
        ((sheafHom X'.left).obj _).map (upperShriekDualizingRestrictIso h g j hK).hom =
      (upperShriekStdRestrictIso h g j).hom.app M ≫
        (upperShriekDualityIso (h ≫ g) (j.precompOpen h.left) hK).hom.app M := by
  have F1 := (upperShriekStdIso (h ≫ g) (j.precompOpen h.left)).inv_hom_id_app M
  have F2 := ((pullCompIso h.left j.immersion (h.left ≫ j.immersion) rfl).hom.naturality
    ((dualityIso j.toBase hK).hom.app M)).symm
  have F3 := hom_comp_eq_of_eq_inv_comp
    ((pullCompIso h.left j.immersion (h.left ≫ j.immersion) rfl).app _) _ _
    (pullSheafHomMap_comp' h.left j.immersion rfl
      ((pull j.toBase).obj (((sheafHom Y.left).obj (op M.obj)).obj K))
      ((rightAdjointStd j.toBase).obj (dualizingObject hK)))
  have F4 := pullSheafHomMap_naturality h.left
    ((pullCompIso j.immersion j.toBase g.left (immersion_comp_toBase g j)).inv.app
      (((sheafHom Y.left).obj (op M.obj)).obj K))
    ((pull j.immersion).obj ((rightAdjointStd j.toBase).obj (dualizingObject hK)))
  have F5 := pullSheafHomMap_naturality_right h.left
    ((pull g.left).obj (((sheafHom Y.left).obj (op M.obj)).obj K))
    ((pullModelConj j.immersion).app
      ((rightAdjointStd j.toBase).obj (dualizingObject hK))).inv
  have F6 := ((sheafHom X'.left).map ((pullCompIso h.left g.left (h ≫ g).left rfl).inv.app
      (((sheafHom Y.left).obj (op M.obj)).obj K)).op).naturality
    ((pull h.left).map ((pullModelConj j.immersion).app
      ((rightAdjointStd j.toBase).obj (dualizingObject hK))).inv)
  have F8 := ((sheafHom X'.left).map ((pullCompIso (j.precompOpen h.left).immersion
      (j.precompOpen h.left).toBase (h ≫ g).left
      (immersion_comp_toBase (h ≫ g) (j.precompOpen h.left))).inv.app
        (((sheafHom Y.left).obj (op M.obj)).obj K)).op).naturality
    ((pullCompIso h.left j.immersion (h.left ≫ j.immersion) rfl).hom.app
      ((rightAdjointStd j.toBase).obj (dualizingObject hK)))
  have F7 := sheafHom_map_comp_app_eq _ _ _ _
    (pullCompIso_assoc_inv h.left j.immersion j.toBase rfl (immersion_comp_toBase g j)
      (immersion_comp_toBase (h ≫ g) (j.precompOpen h.left)) rfl
      (((sheafHom Y.left).obj (op M.obj)).obj K))
    ((pull h.left).obj ((pull j.immersion).obj
      ((rightAdjointStd j.toBase).obj (dualizingObject hK))))
  have F9 := map_comp_map_eq_of_comp_eq ((sheafHom X'.left).obj
      (op ((pull (h ≫ g).left).obj (((sheafHom Y.left).obj (op M.obj)).obj K))))
    ((pullCompIso h.left j.immersion (h.left ≫ j.immersion) rfl).hom.app
      ((rightAdjointStd j.toBase).obj (dualizingObject hK)))
    ((pullModelConj (h.left ≫ j.immersion)).app
      ((rightAdjointStd j.toBase).obj (dualizingObject hK))).inv
    ((pull h.left).map ((pullModelConj j.immersion).app
      ((rightAdjointStd j.toBase).obj (dualizingObject hK))).inv)
    (upperShriekDualizingRestrictIso h g j hK).hom
    (map_inv_comp_mapIso_hom_comp_trans_hom (pull h.left)
      ((pullModelConj j.immersion).app ((rightAdjointStd j.toBase).obj (dualizingObject hK)))
      ((pullCompIso h.left j.immersion (h.left ≫ j.immersion) rfl).app
        ((rightAdjointStd j.toBase).obj (dualizingObject hK)))
      ((pullModelConj (h.left ≫ j.immersion)).app
        ((rightAdjointStd j.toBase).obj (dualizingObject hK))).symm)
  exact upperShriekDualityIso_restrict_chase (pull h.left) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ F1 F2 F3 F4 F5 F6 F8 F7 F9 (upperShriekDualityIso_hom_app g j hK M)
    (upperShriekStdRestrictIso_hom_app h g j M)
    (upperShriekDualityIso_hom_app (h ≫ g) (j.precompOpen h.left) hK M)

end Stacks.Duality.UpperShriekDuality
