module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClopenDecomposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SystemPullbackCompApp

/-!
# The system of inverse images of one sheaf

Let `(X_i, f_{i'i})` be an inverse system of schemes over a preordered set `I` and let
`ι_i : X_i ⟶ S` be a compatible family of morphisms to a scheme `S`, so `f_{i'i} ≫ ι_i = ι_{i'}`.
The inverse images `ι_i⁻¹ G` of an abelian sheaf `G` on the small étale site of `S` form a system
of sheaves in the sense of Stacks 0EZL, with transition maps the comparisons
`f_{i'i}⁻¹ ι_i⁻¹ G ≅ ι_{i'}⁻¹ G` of inverse images along a composite. The cocycle condition is the
associativity of these comparisons, which is deduced here from the associativity of the
comparisons of direct images by passing to left adjoints.

More generally, for a morphism `e : (Y_i) ⟶ (T_i)` of inverse systems of schemes, the inverse
images `e_i⁻¹ℱ_i` of a system of sheaves `(ℱ_i, φ_{i'i})` on `(T_i)` form a system of sheaves on
`(Y_i)`; its transition maps are the comparisons `f_{i'i}⁻¹e_i⁻¹ ≅ e_{i'}⁻¹g_{i'i}⁻¹` through the
diagonal of the naturality squares followed by `e_{i'}⁻¹φ_{i'i}`.

## Main definitions

* `Stacks.EtaleCohomology.EtaleSheafSystem.ofCocone`: the system `i ↦ ι_i⁻¹ G`.
* `Stacks.EtaleCohomology.EtaleSheafSystem.pullback`: the system `i ↦ e_i⁻¹ℱ_i`.

## Main results

* `Stacks.EtaleCohomology.smallEtalePullbackAbComp'_assoc`: the comparisons of inverse images
  along composites are associative.
* `Stacks.EtaleCohomology.smallEtalePullbackAbCompApp_naturality_comp`: the comparisons attached
  to the naturality squares of a morphism of inverse systems compose.

## Implementation notes

The cocycle conditions are proved by a rearrangement in an arbitrary category applied to the
associativity and naturality squares of the comparisons, all written on components with
iterated inverse images as sources (`Stacks.EtaleCohomology.smallEtalePullbackAbCompApp`):
checking an identification of `(g⁻¹ ⋙ f⁻¹).obj M` with `f⁻¹(g⁻¹ M)` underneath a further inverse
image makes the kernel unfold the inverse image functor, so no such identification is left to it.

## References

* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

open Opposite

namespace Stacks.EtaleCohomology

/-- **The associativity pentagon of the comparison of inverse images**, deduced from the one of
direct images through the comparison of left adjoints. -/
theorem smallEtalePullbackAbComp'_assoc {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh) :
    Functor.isoWhiskerLeft (smallEtalePullbackAb h) (smallEtalePullbackAbComp' f g fg hfg) ≪≫
        smallEtalePullbackAbComp' fg h fgh h₁ =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (smallEtalePullbackAbComp' g h gh hgh) (smallEtalePullbackAb f) ≪≫
          smallEtalePullbackAbComp' f gh fgh h₂ := by
  simp only [smallEtalePullbackAbComp'_eq_leftAdjointCompIso]
  exact Adjunction.leftAdjointCompIso_assoc (smallEtaleAdjunctionAb h) (smallEtaleAdjunctionAb g)
    (smallEtaleAdjunctionAb f) (smallEtaleAdjunctionAb gh) (smallEtaleAdjunctionAb fg)
    (smallEtaleAdjunctionAb fgh) (smallEtalePushforwardAbComp' g h gh hgh)
    (smallEtalePushforwardAbComp' f g fg hfg) (smallEtalePushforwardAbComp' fg h fgh h₁)
    (smallEtalePushforwardAbComp' f gh fgh h₂)
    (by
      refine Iso.ext (NatTrans.ext (funext fun F => ?_))
      simpa using (smallEtalePushforwardAbComp'_assoc_app f g h fg hfg gh hgh fgh h₁ h₂ F).symm)

/-- The pentagon, evaluated at a sheaf. -/
theorem smallEtalePullbackAbComp'_assoc_app {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh)
    (G : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (smallEtalePullbackAbComp' f g fg hfg).hom.app ((smallEtalePullbackAb h).obj G) ≫
        (smallEtalePullbackAbComp' fg h fgh h₁).hom.app G =
      (smallEtalePullbackAb f).map ((smallEtalePullbackAbComp' g h gh hgh).hom.app G) ≫
        (smallEtalePullbackAbComp' f gh fgh h₂).hom.app G := by
  simpa using congrArg (fun z : _ ≅ _ => NatTrans.app z.hom G)
    (smallEtalePullbackAbComp'_assoc f g h fg hfg gh hgh fgh h₁ h₂)

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {S : Scheme.{u}}

/-- **The system of inverse images of one sheaf** along a compatible family of morphisms
`ι_i : X_i ⟶ S`: the sheaf `ι_i⁻¹ G` at each index, with the comparisons of inverse images along
composites as transition maps. -/
def EtaleSheafSystem.ofCocone (ι : ∀ i, D.obj i ⟶ S)
    (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ ι j = ι i)
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) : EtaleSheafSystem D Ab.{u + 1} where
  obj i := (smallEtalePullbackAb (ι i)).obj G
  map {i j} a := (smallEtalePullbackAbComp' (D.map a) (ι j) (ι i) (hι a).symm).hom.app G
  map_comp {i j k} a b := by
    rw [systemPullbackComp_eq]
    have hp := smallEtalePullbackAbComp'_assoc_app (D.map a) (D.map b) (ι k) (D.map (a ≫ b))
      (D.map_comp a b) (ι j) (hι b).symm (ι i) (hι (a ≫ b)).symm (hι a).symm G
    rw [← cancel_epi
      ((smallEtalePullbackAbComp' (D.map a) (D.map b) (D.map (a ≫ b)) (D.map_comp a b)).hom.app
        ((smallEtalePullbackAb (ι k)).obj G)), Iso.hom_inv_id_app_assoc, hp]

/-! ### The inverse image of a system along a morphism of inverse systems -/

section MorphismOfSystems

local notation "App" => smallEtalePullbackAbCompApp

/-- The associativity pentagon of the comparisons of inverse images, on components with iterated
inverse images as sources. -/
theorem smallEtalePullbackAbCompApp_assoc {T X Y Z : Scheme.{u}} (f : T ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : T ⟶ Y) (hfg : fg = f ≫ g) (gh : X ⟶ Z) (hgh : gh = g ≫ h)
    (fgh : T ⟶ Z) (h₁ : fgh = fg ≫ h) (h₂ : fgh = f ≫ gh)
    (G : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) :
    (App f g fg hfg ((smallEtalePullbackAb h).obj G)).hom ≫ (App fg h fgh h₁ G).hom =
      (smallEtalePullbackAb f).map (App g h gh hgh G).hom ≫ (App f gh fgh h₂ G).hom :=
  smallEtalePullbackAbComp'_assoc_app f g h fg hfg gh hgh fgh h₁ h₂ G

/-- The rearrangement behind
`Stacks.EtaleCohomology.smallEtalePullbackAbCompApp_naturality_comp`, in an arbitrary category:
three associativity squares `A₁`, `A₂`, `A₃` and four cancellations. -/
private theorem naturality_comp_algebra {E : Type*} [Category* E]
    {o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ : E} (s : o₁ ⟶ o₂) (s' : o₂ ⟶ o₁) (hs : s ≫ s' = 𝟙 o₁)
    (l₁ : o₂ ⟶ o₃) (l₂ : o₃ ⟶ o₄) (l₃ : o₄ ⟶ o₃) (hl₃ : l₂ ≫ l₃ = 𝟙 o₃) (c : o₄ ⟶ o₅)
    (d' : o₅ ⟶ o₆) (d : o₆ ⟶ o₅) (hd : d' ≫ d = 𝟙 o₅) (r : o₆ ⟶ o₇) (X : o₅ ⟶ o₈)
    (t : o₇ ⟶ o₈) (A₁ : d ≫ X = r ≫ t) (Y : o₃ ⟶ o₈) (A₂ : c ≫ X = l₃ ≫ Y) (z : o₁ ⟶ o₈)
    (A₃ : s' ≫ z = l₁ ≫ Y) (t' : o₈ ⟶ o₇) (ht : t ≫ t' = 𝟙 o₇) :
    s ≫ l₁ ≫ l₂ ≫ c ≫ d' ≫ r = z ≫ t' := by
  have key : s ≫ l₁ ≫ l₂ ≫ c ≫ d' ≫ r ≫ t = z := by
    rw [← A₁, reassoc_of% hd, A₂, reassoc_of% hl₃, ← A₃, reassoc_of% hs]
  rw [← key]
  simp only [Category.assoc, ht, Category.comp_id]

/-- The rearrangement behind `Stacks.EtaleCohomology.EtaleSheafSystem.pullbackMap_comp`, in an
arbitrary category: two naturality squares, the cocycle condition of the system and the
composition of the comparisons. -/
private theorem pullbackMap_comp_algebra {E : Type*} [Category* E]
    {o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ o₉ o₁₀ o₁₁ o₁₂ : E} (s : o₁ ⟶ o₂) (L : o₂ ⟶ o₅) (p₁ : o₂ ⟶ o₃)
    (p₂ : o₃ ⟶ o₄) (q : o₄ ⟶ o₅) (hL : L = p₁ ≫ p₂ ≫ q) (σ₁ : o₅ ⟶ o₆) (σ₂ : o₆ ⟶ o₇)
    (ε : o₇ ⟶ o₈) (σ₁' : o₄ ⟶ o₉) (q' : o₉ ⟶ o₆) (n₁ : q ≫ σ₁ = σ₁' ≫ q')
    (σ₂' : o₉ ⟶ o₁₀) (τ : o₁₀ ⟶ o₇) (n₂ : q' ≫ σ₂ = σ₂' ≫ τ) (c : o₁₀ ⟶ o₁₁)
    (ε' : o₁₁ ⟶ o₈) (hτ : τ ≫ ε = c ≫ ε') (ρ₁ : o₁ ⟶ o₁₂) (ρ₂ : o₁₂ ⟶ o₁₁)
    (hcomp : s ≫ p₁ ≫ p₂ ≫ σ₁' ≫ σ₂' ≫ c = ρ₁ ≫ ρ₂) :
    s ≫ L ≫ σ₁ ≫ σ₂ ≫ ε = ρ₁ ≫ ρ₂ ≫ ε' := by
  subst hL
  simp only [Category.assoc]
  rw [reassoc_of% n₁, reassoc_of% n₂, hτ, ← reassoc_of% hcomp]

variable {DY DT : Iᵒᵖ ⥤ Scheme.{u}} (e : DY ⟶ DT)

/-- **The comparisons attached to a morphism of inverse systems compose.** Along `i'' ≥ i' ≥ i`,
the comparison `f_{i''i}⁻¹e_i⁻¹ ≅ e_{i''}⁻¹g_{i''i}⁻¹` through the diagonal of the composite
naturality square is the composite of the comparisons of the two naturality squares, read through
the comparisons of inverse images along the two composite transitions. This is three instances of
the associativity of the comparisons of inverse images. -/
theorem smallEtalePullbackAbCompApp_naturality_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k)
    (M : Sheaf (smallEtaleTopology (DT.obj k)) Ab.{u + 1}) :
    (App (DY.map a) (DY.map b) (DY.map (a ≫ b)) (DY.map_comp a b)
          ((smallEtalePullbackAb (e.app k)).obj M)).inv ≫
        (smallEtalePullbackAb (DY.map a)).map
          (App (DY.map b) (e.app k) (DY.map b ≫ e.app k) rfl M).hom ≫
        (smallEtalePullbackAb (DY.map a)).map
          (App (e.app j) (DT.map b) (DY.map b ≫ e.app k) (e.naturality b) M).inv ≫
        (App (DY.map a) (e.app j) (DY.map a ≫ e.app j) rfl
          ((smallEtalePullbackAb (DT.map b)).obj M)).hom ≫
        (App (e.app i) (DT.map a) (DY.map a ≫ e.app j) (e.naturality a)
          ((smallEtalePullbackAb (DT.map b)).obj M)).inv ≫
        (smallEtalePullbackAb (e.app i)).map
          (App (DT.map a) (DT.map b) (DT.map (a ≫ b)) (DT.map_comp a b) M).hom =
      (App (DY.map (a ≫ b)) (e.app k) (DY.map (a ≫ b) ≫ e.app k) rfl M).hom ≫
        (App (e.app i) (DT.map (a ≫ b)) (DY.map (a ≫ b) ≫ e.app k) (e.naturality (a ≫ b))
          M).inv := by
  have h₁ : DY.map (a ≫ b) ≫ e.app k = (DY.map a ≫ e.app j) ≫ DT.map b := by
    simp only [Functor.map_comp, Category.assoc, e.naturality b]
  have h₃ : DY.map (a ≫ b) ≫ e.app k = DY.map a ≫ (DY.map b ≫ e.app k) := by
    rw [DY.map_comp, Category.assoc]
  have hl₃ : (smallEtalePullbackAb (DY.map a)).map
        (App (e.app j) (DT.map b) (DY.map b ≫ e.app k) (e.naturality b) M).inv ≫
      (smallEtalePullbackAb (DY.map a)).map
        (App (e.app j) (DT.map b) (DY.map b ≫ e.app k) (e.naturality b) M).hom = 𝟙 _ := by
    rw [← (smallEtalePullbackAb (DY.map a)).map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id]
  exact naturality_comp_algebra _ _ (Iso.inv_hom_id _) _ _ _ hl₃ _ _ _ (Iso.inv_hom_id _) _ _ _
    (smallEtalePullbackAbCompApp_assoc (e.app i) (DT.map a) (DT.map b) (DY.map a ≫ e.app j)
      (e.naturality a) (DT.map (a ≫ b)) (DT.map_comp a b) (DY.map (a ≫ b) ≫ e.app k) h₁
      (e.naturality (a ≫ b)) M) _
    (smallEtalePullbackAbCompApp_assoc (DY.map a) (e.app j) (DT.map b) (DY.map a ≫ e.app j)
      rfl (DY.map b ≫ e.app k) (e.naturality b) (DY.map (a ≫ b) ≫ e.app k) h₁ h₃ M) _
    (smallEtalePullbackAbCompApp_assoc (DY.map a) (DY.map b) (e.app k) (DY.map (a ≫ b))
      (DY.map_comp a b) (DY.map b ≫ e.app k) rfl (DY.map (a ≫ b) ≫ e.app k) rfl h₃ M)
    _ (Iso.hom_inv_id _)

variable (F : EtaleSheafSystem DT Ab.{u + 1})

/-- The transition map `g_{i'i}⁻¹ℱ_i ⟶ ℱ_{i'}` of a system of abelian sheaves, with its source
written as the inverse image of abelian sheaves along the transition morphism. -/
def EtaleSheafSystem.smallEtaleMap {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb (DT.map a)).obj (F.obj j) ⟶ F.obj i :=
  F.map a

/-- The cocycle condition of a system of abelian sheaves, in terms of
`Stacks.EtaleCohomology.EtaleSheafSystem.smallEtaleMap`. -/
theorem EtaleSheafSystem.smallEtaleMap_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (smallEtalePullbackAb (DT.map a)).map (EtaleSheafSystem.smallEtaleMap F b) ≫
        EtaleSheafSystem.smallEtaleMap F a =
      (App (DT.map a) (DT.map b) (DT.map (a ≫ b)) (DT.map_comp a b) (F.obj k)).hom ≫
        EtaleSheafSystem.smallEtaleMap F (a ≫ b) :=
  (show (smallEtalePullbackAbComp' (DT.map a) (DT.map b) (DT.map (a ≫ b))
        (DT.map_comp a b)).hom.app (F.obj k) ≫ F.map (a ≫ b) =
      (systemPullback DT Ab.{u + 1} a).map (F.map b) ≫ F.map a by
    rw [← systemPullbackComp_eq, ← F.map_comp a b, ← Category.assoc, Iso.hom_inv_id_app,
      Category.id_comp]).symm

/-- The transition map `f_{i'i}⁻¹e_i⁻¹ℱ_i ⟶ e_{i'}⁻¹ℱ_{i'}` of the inverse image of a system of
sheaves along a morphism of inverse systems: the comparison `f_{i'i}⁻¹e_i⁻¹ ≅ e_{i'}⁻¹g_{i'i}⁻¹`
through the diagonal of the naturality square, followed by `e_{i'}⁻¹φ_{i'i}`. -/
def EtaleSheafSystem.pullbackMap {i j : Iᵒᵖ} (a : i ⟶ j) :
    (smallEtalePullbackAb (DY.map a)).obj ((smallEtalePullbackAb (e.app j)).obj (F.obj j)) ⟶
      (smallEtalePullbackAb (e.app i)).obj (F.obj i) :=
  (App (DY.map a) (e.app j) (DY.map a ≫ e.app j) rfl (F.obj j)).hom ≫
    (App (e.app i) (DT.map a) (DY.map a ≫ e.app j) (e.naturality a) (F.obj j)).inv ≫
    (smallEtalePullbackAb (e.app i)).map (EtaleSheafSystem.smallEtaleMap F a)

/-- **The cocycle condition for the inverse image of a system along a morphism of systems.** -/
theorem EtaleSheafSystem.pullbackMap_comp {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (App (DY.map a) (DY.map b) (DY.map (a ≫ b)) (DY.map_comp a b)
          ((smallEtalePullbackAb (e.app k)).obj (F.obj k))).inv ≫
        (smallEtalePullbackAb (DY.map a)).map (EtaleSheafSystem.pullbackMap e F b) ≫
          EtaleSheafSystem.pullbackMap e F a =
      EtaleSheafSystem.pullbackMap e F (a ≫ b) := by
  have hL : (smallEtalePullbackAb (DY.map a)).map (EtaleSheafSystem.pullbackMap e F b) = _ :=
    ((smallEtalePullbackAb (DY.map a)).map_comp _ _).trans
    (congrArg ((smallEtalePullbackAb (DY.map a)).map _ ≫ ·)
      ((smallEtalePullbackAb (DY.map a)).map_comp _ _))
  have hτ : (smallEtalePullbackAb (e.app i)).map ((smallEtalePullbackAb (DT.map a)).map
        (EtaleSheafSystem.smallEtaleMap F b)) ≫
        (smallEtalePullbackAb (e.app i)).map (EtaleSheafSystem.smallEtaleMap F a) =
      (smallEtalePullbackAb (e.app i)).map
        (App (DT.map a) (DT.map b) (DT.map (a ≫ b)) (DT.map_comp a b) (F.obj k)).hom ≫
      (smallEtalePullbackAb (e.app i)).map (EtaleSheafSystem.smallEtaleMap F (a ≫ b)) :=
    ((smallEtalePullbackAb (e.app i)).map_comp _ _).symm.trans
      ((congrArg (smallEtalePullbackAb (e.app i)).map
        (EtaleSheafSystem.smallEtaleMap_comp F a b)).trans
        ((smallEtalePullbackAb (e.app i)).map_comp _ _))
  exact pullbackMap_comp_algebra _ _ _ _ _ hL _ _ _ _ _
    (smallEtalePullbackAbCompApp_hom_naturality (DY.map a) (e.app j) (DY.map a ≫ e.app j) rfl
      (EtaleSheafSystem.smallEtaleMap F b)) _ _
    (smallEtalePullbackAbCompApp_inv_naturality (e.app i) (DT.map a) (DY.map a ≫ e.app j)
      (e.naturality a) (EtaleSheafSystem.smallEtaleMap F b)) _ _ hτ _ _
    (smallEtalePullbackAbCompApp_naturality_comp e a b (F.obj k))

/-- **The inverse image of a system of sheaves along a morphism of inverse systems of schemes.**
For a morphism `e : (Y_i) ⟶ (T_i)` of inverse systems and a system `(ℱ_i, φ_{i'i})` of abelian
sheaves on `(T_i)`, the sheaves `e_i⁻¹ℱ_i` form a system on `(Y_i)`, with transition maps
`Stacks.EtaleCohomology.EtaleSheafSystem.pullbackMap`. -/
abbrev EtaleSheafSystem.pullback : EtaleSheafSystem DY Ab.{u + 1} where
  obj i := (smallEtalePullbackAb (e.app i)).obj (F.obj i)
  map a := EtaleSheafSystem.pullbackMap e F a
  map_comp a b := by
    rw [systemPullbackComp_eq]
    exact EtaleSheafSystem.pullbackMap_comp e F a b

/-- The sheaf of the inverse image system at `i` is `e_i⁻¹ℱ_i`. -/
@[simp]
theorem EtaleSheafSystem.pullback_obj (i : Iᵒᵖ) :
    (EtaleSheafSystem.pullback e F).obj i = (smallEtalePullbackAb (e.app i)).obj (F.obj i) := rfl

/-- The transition map of the inverse image system along `a` is
`Stacks.EtaleCohomology.EtaleSheafSystem.pullbackMap e F a`. -/
theorem EtaleSheafSystem.pullback_map {i j : Iᵒᵖ} (a : i ⟶ j) :
    (EtaleSheafSystem.pullback e F).map a = EtaleSheafSystem.pullbackMap e F a := rfl

end MorphismOfSystems

/-! ### Pulling back cohomology along isomorphisms and identities -/

section Iso

/-- Pulling back along `φ` is pulling back along the identity, followed by composing with `φ`. -/
private theorem etaleCohomologyPullback_eq_comp_mk₀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} {G : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (φ : (smallEtalePullbackAb f).obj F ⟶ G) (q : ℕ) :
    (etaleCohomologyPullback f φ q : Sheaf.H.{u + 1} F q → _) =
      (fun z => z.comp (Ext.mk₀ φ) (add_zero q)) ∘ etaleCohomologyPullback f (𝟙 _) q := by
  funext x
  simp only [Function.comp_apply, etaleCohomologyPullback_comp_mk₀, Category.id_comp]

/-- Composing with an isomorphism of sheaves is bijective on cohomology. -/
private theorem bijective_comp_mk₀_of_isIso {X : Scheme.{u}}
    {A B : Sheaf (smallEtaleTopology X) Ab.{u + 1}} (φ : A ⟶ B) [IsIso φ] (q : ℕ) :
    Function.Bijective (fun y : Sheaf.H.{u + 1} A q => y.comp (Ext.mk₀ φ) (add_zero q)) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨fun z => z.comp (Ext.mk₀ (inv φ)) (add_zero q), fun z => by simp [Ext.mk₀_comp_mk₀],
      fun z => by simp [Ext.mk₀_comp_mk₀]⟩

/-- **Pulling back étale cohomology along an isomorphism, with an isomorphism of sheaves, is
bijective**: an isomorphism is an open immersion onto the whole target. -/
theorem bijective_etaleCohomologyPullback_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    {F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} {G : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (φ : (smallEtalePullbackAb f).obj F ⟶ G) [IsIso φ] (q : ℕ) :
    Function.Bijective (etaleCohomologyPullback f φ q) := by
  have h₁ := bijective_etaleCohomologyPullback_pi (ι := Unit) (fun _ => f)
    (fun a b hab => absurd (Subsingleton.elim a b) hab)
    (by
      rw [Set.iUnion_const]
      exact Set.range_eq_univ.mpr (ConcreteCategory.bijective_of_isIso f.base).2) F q
  have h₂ : Function.Bijective (fun x : Sheaf.H.{u + 1} F q =>
      etaleCohomologyPullback f (𝟙 _) q x) := by
    refine ⟨fun x y h => h₁.1 (funext fun _ => h), fun y => ?_⟩
    obtain ⟨x, hx⟩ := h₁.2 fun _ => y
    exact ⟨x, congrFun hx ()⟩
  rw [etaleCohomologyPullback_eq_comp_mk₀]
  exact (bijective_comp_mk₀_of_isIso φ q).comp h₂

/-- **Pulling back along an identity, with the comparison of inverse images, is the identity.**
The map is idempotent by the composition law and the pentagon, and bijective. -/
theorem etaleCohomologyPullback_id_comp' {X S : Scheme.{u}} (g : X ⟶ S)
    (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (q : ℕ) (x : Sheaf.H.{u + 1}
      ((smallEtalePullbackAb g).obj G) q) :
    etaleCohomologyPullback (𝟙 X)
        ((smallEtalePullbackAbComp' (𝟙 X) g g (Category.id_comp g).symm).hom.app G) q x = x := by
  set P := etaleCohomologyPullback (𝟙 X)
    ((smallEtalePullbackAbComp' (𝟙 X) g g (Category.id_comp g).symm).hom.app G) q
  have hbij : Function.Bijective P := bijective_etaleCohomologyPullback_of_isIso _ _ q
  have hidem : ∀ y, P (P y) = P y := by
    intro y
    rw [etaleCohomologyPullback_comp (𝟙 X) (𝟙 X) (𝟙 X) (Category.id_comp _).symm]
    congr 2
    have hp := smallEtalePullbackAbComp'_assoc_app (𝟙 X) (𝟙 X) g (𝟙 X)
      (Category.id_comp _).symm g (Category.id_comp g).symm g (Category.id_comp g).symm
      (Category.id_comp g).symm G
    rw [← hp, Iso.inv_hom_id_app_assoc]
  exact hbij.1 (hidem x)

/-- Pulling back along a morphism equal to an identity, with the comparison of inverse images, is
the identity. -/
theorem etaleCohomologyPullback_comp'_of_eq_id {X S : Scheme.{u}} (m : X ⟶ X) (hm : m = 𝟙 X)
    (g : X ⟶ S) (h : g = m ≫ g) (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (q : ℕ)
    (x : Sheaf.H.{u + 1} ((smallEtalePullbackAb g).obj G) q) :
    etaleCohomologyPullback m ((smallEtalePullbackAbComp' m g g h).hom.app G) q x = x := by
  subst hm
  exact etaleCohomologyPullback_id_comp' g G q x

/-- **Pulling back around a commutative square.** If `a ≫ f = b ≫ g`, pulling back along `f`
and then along `a` is pulling back along `g` and then along `b`, followed by the comparison of
the two inverse images of the sheaf on the common target. -/
theorem etaleCohomologyPullback_square {W Y V Z : Scheme.{u}} (a : W ⟶ Y) (f : Y ⟶ Z) (b : W ⟶ V)
    (g : V ⟶ Z) (h : a ≫ f = b ≫ g) (F : Sheaf (smallEtaleTopology Z) Ab.{u + 1}) (q : ℕ)
    (x : Sheaf.H.{u + 1} F q) :
    etaleCohomologyPullback a (𝟙 _) q (etaleCohomologyPullback f (𝟙 _) q x) =
      etaleCohomologyPullback b ((smallEtalePullbackAbComp' b g (a ≫ f) h).hom.app F ≫
        (smallEtalePullbackAbComp' a f (a ≫ f) rfl).inv.app F) q
        (etaleCohomologyPullback g (𝟙 _) q x) := by
  rw [etaleCohomologyPullback_comp a f (a ≫ f) rfl, etaleCohomologyPullback_comp b g (a ≫ f) h]
  congr 2
  simp

/-- Pulling back followed by an isomorphism of sheaves is bijective exactly when plain pulling back
is. -/
theorem bijective_etaleCohomologyPullback_iff_of_isIso_sheaf {X Y : Scheme.{u}} (g : X ⟶ Y)
    {F : Sheaf (smallEtaleTopology Y) Ab.{u + 1}} {E : Sheaf (smallEtaleTopology X) Ab.{u + 1}}
    (φ : (smallEtalePullbackAb g).obj F ⟶ E) [IsIso φ] (q : ℕ) :
    Function.Bijective (etaleCohomologyPullback g φ q) ↔
      Function.Bijective (etaleCohomologyPullback g (𝟙 ((smallEtalePullbackAb g).obj F)) q) := by
  rw [etaleCohomologyPullback_eq_comp_mk₀]
  exact Function.Bijective.of_comp_iff' (bijective_comp_mk₀_of_isIso φ q) _

/-- **Bijectivity of pulling back is invariant under isomorphism of the morphism.** If
`i ≫ g₂ = g₁ ≫ j` with `i`, `j` isomorphisms and `φ : j⁻¹F ⟶ E` an isomorphism of sheaves, pulling
back along `g₂` is bijective on cohomology with coefficients in `F` if and only if pulling back
along `g₁` is bijective with coefficients in `E`. -/
theorem bijective_etaleCohomologyPullback_iff_of_isIso {P₁ P₂ Z₁ Z₂ : Scheme.{u}} (g₁ : P₁ ⟶ Z₁)
    (g₂ : P₂ ⟶ Z₂) (i : P₁ ⟶ P₂) (j : Z₁ ⟶ Z₂) [IsIso i] [IsIso j] (h : i ≫ g₂ = g₁ ≫ j)
    (F : Sheaf (smallEtaleTopology Z₂) Ab.{u + 1}) {E : Sheaf (smallEtaleTopology Z₁) Ab.{u + 1}}
    (φ : (smallEtalePullbackAb j).obj F ⟶ E) [IsIso φ] (q : ℕ) :
    Function.Bijective (etaleCohomologyPullback g₂ (𝟙 ((smallEtalePullbackAb g₂).obj F)) q) ↔
      Function.Bijective (etaleCohomologyPullback g₁ (𝟙 ((smallEtalePullbackAb g₁).obj E)) q) := by
  let ψ : (smallEtalePullbackAb i).obj ((smallEtalePullbackAb g₂).obj F) ⟶
      (smallEtalePullbackAb g₁).obj E :=
    (smallEtalePullbackAbComp' i g₂ (g₁ ≫ j) h.symm).hom.app F ≫
      (smallEtalePullbackAbComp' g₁ j (g₁ ≫ j) rfl).inv.app F ≫ (smallEtalePullbackAb g₁).map φ
  have hL : ∀ x : Sheaf.H.{u + 1} F q,
      etaleCohomologyPullback g₁ (𝟙 _) q (etaleCohomologyPullback j φ q x) =
        etaleCohomologyPullback i ψ q (etaleCohomologyPullback g₂ (𝟙 _) q x) := by
    intro x
    rw [etaleCohomologyPullback_comp g₁ j (g₁ ≫ j) rfl,
      etaleCohomologyPullback_comp i g₂ (g₁ ≫ j) h.symm]
    congr 2
    simp [ψ]
  have hj := bijective_etaleCohomologyPullback_of_isIso j φ q
  have hi := bijective_etaleCohomologyPullback_of_isIso i ψ q
  have hfun : (etaleCohomologyPullback g₁ (𝟙 _) q : _ → _) ∘ etaleCohomologyPullback j φ q =
      etaleCohomologyPullback i ψ q ∘ etaleCohomologyPullback g₂ (𝟙 _) q := funext hL
  refine ⟨fun hg => (Function.Bijective.of_comp_iff _ hj).mp ?_,
    fun hg => (Function.Bijective.of_comp_iff' hi _).mp ?_⟩
  · rw [hfun]
    exact hi.comp hg
  · rw [← hfun]
    exact hg.comp hj

end Iso

/-! ### The cohomology diagram of the system of inverse images of one sheaf -/

section Diagram

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} {S : Scheme.{u}}
  (ι : ∀ i, D.obj i ⟶ S) (hι : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), D.map a ≫ ι j = ι i)
  (G : Sheaf (smallEtaleTopology S) Ab.{u + 1}) (q : ℕ)

/-- **The cohomology diagram of the system of inverse images of one sheaf**: the functor
`i ↦ H^q(X_i, ι_i⁻¹ G)`, the maps being the pullbacks of cohomology along the transition
morphisms with the comparisons of inverse images. -/
def EtaleSheafSystem.ofCoconeCohomology : I ⥤ AddCommGrpCat.{u + 1} where
  obj i := AddCommGrpCat.of (Sheaf.H.{u + 1} ((smallEtalePullbackAb (ι (op i))).obj G) q)
  map {i j} a := AddCommGrpCat.ofHom (etaleCohomologyPullback (D.map a.op)
    ((smallEtalePullbackAbComp' (D.map a.op) (ι (op i)) (ι (op j)) (hι a.op).symm).hom.app G) q)
  map_id i := by
    ext x
    exact etaleCohomologyPullback_comp'_of_eq_id _ (D.map_id _) _ _ G q x
  map_comp {i j k} a b := by
    ext x
    have hab : D.map (a ≫ b).op = D.map b.op ≫ D.map a.op := by rw [op_comp, D.map_comp]
    change etaleCohomologyPullback (D.map (a ≫ b).op) _ q x =
      etaleCohomologyPullback (D.map b.op) _ q (etaleCohomologyPullback (D.map a.op) _ q x)
    rw [etaleCohomologyPullback_comp (D.map b.op) (D.map a.op) (D.map (a ≫ b).op) hab]
    congr 2
    have hp := smallEtalePullbackAbComp'_assoc_app (D.map b.op) (D.map a.op) (ι (op i))
      (D.map (a ≫ b).op) hab (ι (op j)) (hι a.op).symm (ι (op k))
      (hι (a ≫ b).op).symm (hι b.op).symm G
    rw [← cancel_epi ((smallEtalePullbackAbComp' (D.map b.op) (D.map a.op) (D.map (a ≫ b).op)
      hab).hom.app ((smallEtalePullbackAb (ι (op i))).obj G)),
      Iso.hom_inv_id_app_assoc, hp]

/-- The map of the cohomology diagram along `a : i ⟶ j` sends `x ∈ H^q(X_i, ι_i⁻¹ G)` to its
pullback along the transition morphism `D.map a.op`, composed with the comparison of inverse
images. -/
theorem EtaleSheafSystem.ofCoconeCohomology_map_apply {i j : I} (a : i ⟶ j)
    (x : Sheaf.H.{u + 1} ((smallEtalePullbackAb (ι (op i))).obj G) q) :
    (EtaleSheafSystem.ofCoconeCohomology ι hι G q).map a x =
      etaleCohomologyPullback (D.map a.op)
        ((smallEtalePullbackAbComp' (D.map a.op) (ι (op i)) (ι (op j)) (hι a.op).symm).hom.app G)
          q x :=
  rfl

end Diagram

end Stacks.EtaleCohomology
