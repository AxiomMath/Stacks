module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom.HomSystem

/-!
# Restriction of derived morphism sets to a smaller quasi-compact open

This file contains the second part of
`StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom`: the comparison morphisms of
derived pullbacks around squares of two-step factorisations of morphisms of ringed spaces and of
schemes, and the restriction of the system of derived morphism sets of a relative descent
situation along an inclusion `V₀ ≤ U₀` of quasi-compact opens of the fixed stage.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)
open Stacks.Cohomology.DerivedPushforwardAssociativity (derivedPullbackCompIsoCanonical_assoc
  derivedPullbackIdIso derivedPullbackCompIsoCanonical_id_comp)

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.DerivedPullback

/-! ### Derived pullback around a square of two-step factorisations -/

section TowerRingedSpaces

variable {A A' B B' B₀ Y Y' Y'' Z : RingedSpace.{u, u}}

/-- Derived pullback around a square whose horizontal edges are factored. The map
`Hom(Lg^*Lp^*K, Lg^*Lp^*L) ⟶ Hom(Le^*Lq^*K, Le^*Lq^*L)` attached to a commutative square
`r ≫ g ≫ p = e ≫ q` of morphisms of ringed spaces: read both sides through the composition
isomorphism and apply `factorHom` to the resulting factorisation. -/
def factorTowerHom (r : A ⟶ B) (g : B ⟶ Y) (p : Y ⟶ Z) (e : A ⟶ Y') (q : Y' ⟶ Z)
    (h : r ≫ g ≫ p = e ≫ q)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (φ : (derivedPullback g).obj ((derivedPullback p).obj K) ⟶
      (derivedPullback g).obj ((derivedPullback p).obj L)) :
    (derivedPullback e).obj ((derivedPullback q).obj K) ⟶
      (derivedPullback e).obj ((derivedPullback q).obj L) :=
  (factorEquiv e q (e ≫ q) rfl K L).symm
    (factorHom r (g ≫ p) (e ≫ q) h K L (factorEquiv g p (g ≫ p) rfl K L φ))

/-- The maps on derived Hom attached to two squares stacked along their common factored edge
`e ≫ q` compose. -/
theorem factorTowerHom_comp (r : A ⟶ B) (g : B ⟶ Y) (p : Y ⟶ Z) (e : A ⟶ Y') (q : Y' ⟶ Z)
    (s : A' ⟶ A) (e' : A' ⟶ Y'') (q' : Y'' ⟶ Z) (t : A' ⟶ B) (h : r ≫ g ≫ p = e ≫ q)
    (h' : s ≫ e ≫ q = e' ≫ q') (h'' : t ≫ g ≫ p = e' ≫ q') (hsr : s ≫ r = t)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (φ : (derivedPullback g).obj ((derivedPullback p).obj K) ⟶
      (derivedPullback g).obj ((derivedPullback p).obj L)) :
    factorTowerHom s e q e' q' h' K L (factorTowerHom r g p e q h K L φ) =
      factorTowerHom t g p e' q' h'' K L φ := by
  simp only [factorTowerHom, Equiv.apply_symm_apply]
  exact congrArg (factorEquiv e' q' (e' ≫ q') rfl K L).symm
    (factorHom_comp s r (g ≫ p) (e ≫ q) t (e' ≫ q') h hsr h'' h' K L _)

/-- A square whose vertical edge is an identity and whose two factored edges agree induces the
identity on derived Hom. -/
theorem factorTowerHom_id {r : B ⟶ B} (hr : r = 𝟙 B) (g : B ⟶ Y) (p : Y ⟶ Z)
    (h : r ≫ g ≫ p = g ≫ p)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (φ : (derivedPullback g).obj ((derivedPullback p).obj K) ⟶
      (derivedPullback g).obj ((derivedPullback p).obj L)) :
    factorTowerHom r g p g p h K L φ = φ := by
  simp only [factorTowerHom, factorHom_id hr (g ≫ p) h, Equiv.symm_apply_apply]

/-- The maps attached to squares with factored horizontal edges are compatible with factorisations
of their vertical edges. Two such squares over `tB ≫ g = g'` and under `tA ≫ e = e'` whose vertical
edges satisfy `tA ≫ r = r' ≫ tB` induce maps on derived morphism sets that commute. -/
theorem factorHom_factorTowerHom (p : Y ⟶ Z) (q : Y' ⟶ Z) (g : B ⟶ Y) (g' : B' ⟶ Y)
    (tB : B' ⟶ B) (e : A ⟶ Y') (e' : A' ⟶ Y') (tA : A' ⟶ A) (r : A ⟶ B) (r' : A' ⟶ B')
    (hg : tB ≫ g = g') (he : tA ≫ e = e') (h : r ≫ g ≫ p = e ≫ q)
    (h' : r' ≫ g' ≫ p = e' ≫ q) (hsr : tA ≫ r = r' ≫ tB)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (φ : (derivedPullback g).obj ((derivedPullback p).obj K) ⟶
      (derivedPullback g).obj ((derivedPullback p).obj L)) :
    factorHom tA e e' he ((derivedPullback q).obj K) ((derivedPullback q).obj L)
        (factorTowerHom r g p e q h K L φ) =
      factorTowerHom r' g' p e' q h' K L
        (factorHom tB g g' hg ((derivedPullback p).obj K) ((derivedPullback p).obj L) φ) := by
  have hpbA : tA ≫ e ≫ q = e' ≫ q := by rw [← Category.assoc, he]
  have hpbB : tB ≫ g ≫ p = g' ≫ p := by rw [← Category.assoc, hg]
  have hc : (r' ≫ tB) ≫ g ≫ p = e' ≫ q := by rw [Category.assoc, hpbB]; exact h'
  apply (factorEquiv e' q (e' ≫ q) rfl K L).injective
  simp only [factorTowerHom, Equiv.apply_symm_apply]
  rw [factorEquiv_factorHom tA e q (e ≫ q) e' (e' ≫ q) rfl he rfl hpbA K L,
    Equiv.apply_symm_apply,
    factorEquiv_factorHom tB g p (g ≫ p) g' (g' ≫ p) rfl hg rfl hpbB K L,
    factorHom_comp tA r (g ≫ p) (e ≫ q) (r' ≫ tB) (e' ≫ q) h hsr hc hpbA K L,
    factorHom_comp r' tB (g ≫ p) (g' ≫ p) (r' ≫ tB) (e' ≫ q) hpbB rfl hc h' K L]

/-- A square with factored horizontal edges composes with a square whose upper edge is unfactored.
Restricting along `r ≫ ra` in one step agrees with restricting along `ra` and then along `r`. -/
theorem factorTowerHom_factorSquareHom (g₀ : B₀ ⟶ Z) (ra : B ⟶ B₀) (g : B ⟶ Y) (p : Y ⟶ Z)
    (r : A ⟶ B) (e : A ⟶ Y') (q : Y' ⟶ Z) (ra' : A ⟶ B₀) (h₀ : ra ≫ g₀ = g ≫ p)
    (h : r ≫ g ≫ p = e ≫ q) (hra : r ≫ ra = ra') (h₀' : ra' ≫ g₀ = e ≫ q)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)))
    (ψ : (derivedPullback g₀).obj K ⟶ (derivedPullback g₀).obj L) :
    factorTowerHom r g p e q h K L (factorSquareHom ra g₀ g p h₀ K L ψ) =
      factorSquareHom ra' g₀ e q h₀' K L ψ := by
  simp only [factorTowerHom, factorSquareHom, Equiv.apply_symm_apply]
  exact congrArg (factorEquiv e q (e ≫ q) rfl K L).symm
    (factorHom_comp r ra g₀ (g ≫ p) ra' (e ≫ q) h₀ hra h₀' h K L ψ)

end TowerRingedSpaces

/-! ### Derived pullback around a square of two-step factorisations of morphisms of schemes -/

section TowerSchemes

variable {A A' B B' B₀ Y Y' Y'' Z : Scheme.{u}}

/-- Derived pullback around a square of morphisms of schemes whose horizontal edges are factored.
The map `Hom(Lg^*Lp^*K, Lg^*Lp^*L) ⟶ Hom(Le^*Lq^*K, Le^*Lq^*L)` attached to a commutative square
`r ≫ g ≫ p = e ≫ q`. -/
def schemeFactorTowerHom (r : A ⟶ B) (g : B ⟶ Y) (p : Y ⟶ Z) (e : A ⟶ Y') (q : Y' ⟶ Z)
    (h : r ≫ g ≫ p = e ≫ q)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ : (derivedPullback g.toLRSHom.toShHom).obj ((derivedPullback p.toLRSHom.toShHom).obj K) ⟶
      (derivedPullback g.toLRSHom.toShHom).obj ((derivedPullback p.toLRSHom.toShHom).obj L)) :
    (derivedPullback e.toLRSHom.toShHom).obj ((derivedPullback q.toLRSHom.toShHom).obj K) ⟶
      (derivedPullback e.toLRSHom.toShHom).obj ((derivedPullback q.toLRSHom.toShHom).obj L) :=
  factorTowerHom r.toLRSHom.toShHom g.toLRSHom.toShHom p.toLRSHom.toShHom e.toLRSHom.toShHom
    q.toLRSHom.toShHom (congrArg (fun m : A ⟶ Z ↦ m.toLRSHom.toShHom) h) K L φ

/-- The maps on derived Hom attached to two squares of morphisms of schemes stacked along their
common factored edge `e ≫ q` compose. -/
theorem schemeFactorTowerHom_comp (r : A ⟶ B) (g : B ⟶ Y) (p : Y ⟶ Z) (e : A ⟶ Y') (q : Y' ⟶ Z)
    (s : A' ⟶ A) (e' : A' ⟶ Y'') (q' : Y'' ⟶ Z) (t : A' ⟶ B) (h : r ≫ g ≫ p = e ≫ q)
    (h' : s ≫ e ≫ q = e' ≫ q') (h'' : t ≫ g ≫ p = e' ≫ q') (hsr : s ≫ r = t)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ : (derivedPullback g.toLRSHom.toShHom).obj ((derivedPullback p.toLRSHom.toShHom).obj K) ⟶
      (derivedPullback g.toLRSHom.toShHom).obj ((derivedPullback p.toLRSHom.toShHom).obj L)) :
    schemeFactorTowerHom s e q e' q' h' K L (schemeFactorTowerHom r g p e q h K L φ) =
      schemeFactorTowerHom t g p e' q' h'' K L φ :=
  factorTowerHom_comp r.toLRSHom.toShHom g.toLRSHom.toShHom p.toLRSHom.toShHom
    e.toLRSHom.toShHom q.toLRSHom.toShHom s.toLRSHom.toShHom e'.toLRSHom.toShHom
    q'.toLRSHom.toShHom t.toLRSHom.toShHom (congrArg (fun m : A ⟶ Z ↦ m.toLRSHom.toShHom) h)
    (congrArg (fun m : A' ⟶ Z ↦ m.toLRSHom.toShHom) h')
    (congrArg (fun m : A' ⟶ Z ↦ m.toLRSHom.toShHom) h'')
    (congrArg (fun m : A' ⟶ B ↦ m.toLRSHom.toShHom) hsr) K L φ

/-- A square of morphisms of schemes whose vertical edge is an identity and whose two factored
edges agree induces the identity on derived Hom. -/
theorem schemeFactorTowerHom_id {r : B ⟶ B} (hr : r = 𝟙 B) (g : B ⟶ Y) (p : Y ⟶ Z)
    (h : r ≫ g ≫ p = g ≫ p)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ : (derivedPullback g.toLRSHom.toShHom).obj ((derivedPullback p.toLRSHom.toShHom).obj K) ⟶
      (derivedPullback g.toLRSHom.toShHom).obj ((derivedPullback p.toLRSHom.toShHom).obj L)) :
    schemeFactorTowerHom r g p g p h K L φ = φ :=
  factorTowerHom_id (by subst hr; rfl) g.toLRSHom.toShHom p.toLRSHom.toShHom
    (congrArg (fun m : B ⟶ Z ↦ m.toLRSHom.toShHom) h) K L φ

/-- The maps attached to squares of morphisms of schemes with factored horizontal edges are
compatible with factorisations of their vertical edges. -/
theorem schemeFactorHom_schemeFactorTowerHom (p : Y ⟶ Z) (q : Y' ⟶ Z) (g : B ⟶ Y) (g' : B' ⟶ Y)
    (tB : B' ⟶ B) (e : A ⟶ Y') (e' : A' ⟶ Y') (tA : A' ⟶ A) (r : A ⟶ B) (r' : A' ⟶ B')
    (hg : tB ≫ g = g') (he : tA ≫ e = e') (h : r ≫ g ≫ p = e ≫ q)
    (h' : r' ≫ g' ≫ p = e' ≫ q) (hsr : tA ≫ r = r' ≫ tB)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (φ : (derivedPullback g.toLRSHom.toShHom).obj ((derivedPullback p.toLRSHom.toShHom).obj K) ⟶
      (derivedPullback g.toLRSHom.toShHom).obj ((derivedPullback p.toLRSHom.toShHom).obj L)) :
    schemeFactorHom tA e e' he ((derivedPullback q.toLRSHom.toShHom).obj K)
        ((derivedPullback q.toLRSHom.toShHom).obj L) (schemeFactorTowerHom r g p e q h K L φ) =
      schemeFactorTowerHom r' g' p e' q h' K L
        (schemeFactorHom tB g g' hg ((derivedPullback p.toLRSHom.toShHom).obj K)
          ((derivedPullback p.toLRSHom.toShHom).obj L) φ) :=
  factorHom_factorTowerHom p.toLRSHom.toShHom q.toLRSHom.toShHom g.toLRSHom.toShHom
    g'.toLRSHom.toShHom tB.toLRSHom.toShHom e.toLRSHom.toShHom e'.toLRSHom.toShHom
    tA.toLRSHom.toShHom r.toLRSHom.toShHom r'.toLRSHom.toShHom
    (congrArg (fun m : B' ⟶ Y ↦ m.toLRSHom.toShHom) hg)
    (congrArg (fun m : A' ⟶ Y' ↦ m.toLRSHom.toShHom) he)
    (congrArg (fun m : A ⟶ Z ↦ m.toLRSHom.toShHom) h)
    (congrArg (fun m : A' ⟶ Z ↦ m.toLRSHom.toShHom) h')
    (congrArg (fun m : A' ⟶ B ↦ m.toLRSHom.toShHom) hsr) K L φ

/-- A square of morphisms of schemes with factored horizontal edges composes with a square whose
upper edge is unfactored. -/
theorem schemeFactorTowerHom_schemeFactorSquareHom (g₀ : B₀ ⟶ Z) (ra : B ⟶ B₀) (g : B ⟶ Y)
    (p : Y ⟶ Z) (r : A ⟶ B) (e : A ⟶ Y') (q : Y' ⟶ Z) (ra' : A ⟶ B₀) (h₀ : ra ≫ g₀ = g ≫ p)
    (h : r ≫ g ≫ p = e ≫ q) (hra : r ≫ ra = ra') (h₀' : ra' ≫ g₀ = e ≫ q)
    (K L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z.toRingedSpace)))
    (ψ : (derivedPullback g₀.toLRSHom.toShHom).obj K ⟶
      (derivedPullback g₀.toLRSHom.toShHom).obj L) :
    schemeFactorTowerHom r g p e q h K L (schemeFactorSquareHom ra g₀ g p h₀ K L ψ) =
      schemeFactorSquareHom ra' g₀ e q h₀' K L ψ :=
  factorTowerHom_factorSquareHom g₀.toLRSHom.toShHom ra.toLRSHom.toShHom g.toLRSHom.toShHom
    p.toLRSHom.toShHom r.toLRSHom.toShHom e.toLRSHom.toShHom q.toLRSHom.toShHom
    ra'.toLRSHom.toShHom (congrArg (fun m : B ⟶ Z ↦ m.toLRSHom.toShHom) h₀)
    (congrArg (fun m : A ⟶ Z ↦ m.toLRSHom.toShHom) h)
    (congrArg (fun m : A ⟶ B₀ ↦ m.toLRSHom.toShHom) hra)
    (congrArg (fun m : A ⟶ Z ↦ m.toLRSHom.toShHom) h₀') K L ψ

end TowerSchemes

end Stacks.DerivedPullback


namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{v, u} I)

attribute [local implicit_reducible] restrict

variable (K₀ L₀ : DerivedCategory (SheafOfModules.{u} (structureSheafRing D.X₀.left.toRingedSpace)))
variable (U₀ : D.X₀.left.Opens) (hU₀ : IsCompact (U₀ : Set D.X₀.left))
variable (V₀ : D.X₀.left.Opens) (hV₀ : IsCompact (V₀ : Set D.X₀.left)) (hVU : V₀ ≤ U₀)

/-! ### Restriction to a smaller quasi-compact open of the fixed stage -/

/-- The canonical morphism `Vᵢ = Sᵢ ×_{S₀} V₀ ⟶ Uᵢ = Sᵢ ×_{S₀} U₀`, the base change along
`f_{i0}` of the inclusion `V₀ ⟶ U₀` of quasi-compact opens of `X₀`. -/
def restrictToLarger (i : D.LaterIndex) :
    (D.restrict V₀ hV₀).schemeAt i ⟶ (D.restrict U₀ hU₀).schemeAt i :=
  pullback.lift ((D.restrict V₀ hV₀).toFixedStage i ≫ D.X₀.left.homOfLE hVU)
    (pullback.snd (V₀.ι ≫ D.X₀.hom) (D.baseMap i))
    (by
      change ((D.restrict V₀ hV₀).toFixedStage i ≫ D.X₀.left.homOfLE hVU) ≫ U₀.ι ≫ D.X₀.hom =
        pullback.snd (V₀.ι ≫ D.X₀.hom) (D.baseMap i) ≫ D.baseMap i
      rw [Category.assoc, ← Category.assoc (D.X₀.left.homOfLE hVU), Scheme.homOfLE_ι]
      exact pullback.condition)

/-- The inclusion `Vᵢ ⟶ Uᵢ` lies over the inclusion `V₀ ⟶ U₀`. -/
theorem restrictToLarger_comp_toFixedStage (i : D.LaterIndex) :
    D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i ≫ (D.restrict U₀ hU₀).toFixedStage i =
      (D.restrict V₀ hV₀).toFixedStage i ≫ D.X₀.left.homOfLE hVU :=
  pullback.lift_fst _ _ _

/-- The inclusion `Vᵢ ⟶ Uᵢ` is a morphism over `Sᵢ`. -/
theorem restrictToLarger_comp_snd (i : D.LaterIndex) :
    D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i ≫ pullback.snd (U₀.ι ≫ D.X₀.hom) (D.baseMap i) =
      pullback.snd (V₀.ι ≫ D.X₀.hom) (D.baseMap i) :=
  pullback.lift_snd _ _ _

/-- The inclusions `Vᵢ ⟶ Uᵢ ⟶ Xᵢ` compose to the inclusion `Vᵢ ⟶ Xᵢ`. -/
theorem restrictToLarger_comp_restrictToAmbient (i : D.LaterIndex) :
    D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i ≫ D.restrictToAmbient U₀ hU₀ i =
      D.restrictToAmbient V₀ hV₀ i := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.restrictToAmbient_comp_toFixedStage U₀ hU₀ i, ← Category.assoc,
      D.restrictToLarger_comp_toFixedStage U₀ hU₀ V₀ hV₀ hVU i, Category.assoc,
      Scheme.homOfLE_ι, D.restrictToAmbient_comp_toFixedStage V₀ hV₀ i]
  · rw [Category.assoc, D.restrictToAmbient_comp_snd U₀ hU₀ i,
      D.restrictToLarger_comp_snd U₀ hU₀ V₀ hV₀ hVU i, D.restrictToAmbient_comp_snd V₀ hV₀ i]

/-- The smaller restricted stage is an open subscheme of the larger one. -/
instance isOpenImmersion_restrictToLarger (i : D.LaterIndex) :
    IsOpenImmersion (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i) := by
  have : IsOpenImmersion
      (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i ≫ D.restrictToAmbient U₀ hU₀ i) := by
    rw [D.restrictToLarger_comp_restrictToAmbient U₀ hU₀ V₀ hV₀ hVU i]
    infer_instance
  exact IsOpenImmersion.of_comp _ (D.restrictToAmbient U₀ hU₀ i)

/-- If `f ≫ a = b` for open immersions, the range of `f` is the preimage under `a` of the range
of `b`, given as `W`. -/
private theorem opensRange_eq_preimage_of_comp_eq {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    [IsOpenImmersion f] (a : Y ⟶ Z) [IsOpenImmersion a] (b : X ⟶ Z) [IsOpenImmersion b]
    (hfab : f ≫ a = b) (W : Z.Opens) (hb : b.opensRange = W) :
    f.opensRange = a ⁻¹ᵁ W := by
  have key : a ''ᵁ f.opensRange = W := by
    subst hfab hb
    rw [Scheme.Hom.opensRange_comp]
  simpa only [Scheme.Hom.preimage_image_eq] using congrArg (a ⁻¹ᵁ ·) key

/-- The smaller restricted stage is the preimage of `V₀` in `Uᵢ`. -/
theorem opensRange_restrictToLarger (i : D.LaterIndex) :
    (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i).opensRange =
      (D.restrict U₀ hU₀).toFixedStage i ⁻¹ᵁ U₀.ι ⁻¹ᵁ V₀ := by
  rw [opensRange_eq_preimage_of_comp_eq _ (D.restrictToAmbient U₀ hU₀ i) _
    (D.restrictToLarger_comp_restrictToAmbient U₀ hU₀ V₀ hV₀ hVU i) _
    (D.opensRange_restrictToAmbient V₀ hV₀ i)]
  exact congrArg (fun m ↦ m ⁻¹ᵁ V₀) (D.restrictToAmbient_comp_toFixedStage U₀ hU₀ i)

/-- The canonical morphism `V = S ×_{S₀} V₀ ⟶ U = S ×_{S₀} U₀`, the base change along `f₀` of
the inclusion `V₀ ⟶ U₀` of quasi-compact opens of `X₀`. -/
def restrictToLargerLimit : (D.restrict V₀ hV₀).limitScheme ⟶ (D.restrict U₀ hU₀).limitScheme :=
  pullback.lift ((D.restrict V₀ hV₀).limitToFixedStage ≫ D.X₀.left.homOfLE hVU)
    (pullback.snd (V₀.ι ≫ D.X₀.hom) (D.descent.limitCone.π.app (op D.descent.base)))
    (by
      change ((D.restrict V₀ hV₀).limitToFixedStage ≫ D.X₀.left.homOfLE hVU) ≫ U₀.ι ≫ D.X₀.hom =
        pullback.snd (V₀.ι ≫ D.X₀.hom) (D.descent.limitCone.π.app (op D.descent.base)) ≫
          D.descent.limitCone.π.app (op D.descent.base)
      rw [Category.assoc, ← Category.assoc (D.X₀.left.homOfLE hVU), Scheme.homOfLE_ι]
      exact pullback.condition)

/-- The inclusion `V ⟶ U` lies over the inclusion `V₀ ⟶ U₀`. -/
theorem restrictToLargerLimit_comp_limitToFixedStage :
    D.restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU ≫ (D.restrict U₀ hU₀).limitToFixedStage =
      (D.restrict V₀ hV₀).limitToFixedStage ≫ D.X₀.left.homOfLE hVU :=
  pullback.lift_fst _ _ _

/-- The inclusion `V ⟶ U` is a morphism over `S`. -/
theorem restrictToLargerLimit_comp_snd :
    D.restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU ≫
        pullback.snd (U₀.ι ≫ D.X₀.hom) (D.descent.limitCone.π.app (op D.descent.base)) =
      pullback.snd (V₀.ι ≫ D.X₀.hom) (D.descent.limitCone.π.app (op D.descent.base)) :=
  pullback.lift_snd _ _ _

/-- The inclusions `V ⟶ U ⟶ X` compose to the inclusion `V ⟶ X`. -/
theorem restrictToLargerLimit_comp_restrictToAmbientLimit :
    D.restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU ≫ D.restrictToAmbientLimit U₀ hU₀ =
      D.restrictToAmbientLimit V₀ hV₀ := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.restrictToAmbientLimit_comp_limitToFixedStage U₀ hU₀, ← Category.assoc,
      D.restrictToLargerLimit_comp_limitToFixedStage U₀ hU₀ V₀ hV₀ hVU, Category.assoc,
      Scheme.homOfLE_ι, D.restrictToAmbientLimit_comp_limitToFixedStage V₀ hV₀]
  · rw [Category.assoc, D.restrictToAmbientLimit_comp_snd U₀ hU₀,
      D.restrictToLargerLimit_comp_snd U₀ hU₀ V₀ hV₀ hVU, D.restrictToAmbientLimit_comp_snd V₀ hV₀]

/-- The smaller restricted limit is an open subscheme of the larger one. -/
instance isOpenImmersion_restrictToLargerLimit :
    IsOpenImmersion (D.restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU) := by
  have : IsOpenImmersion
      (D.restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU ≫ D.restrictToAmbientLimit U₀ hU₀) := by
    rw [D.restrictToLargerLimit_comp_restrictToAmbientLimit U₀ hU₀ V₀ hV₀ hVU]
    infer_instance
  exact IsOpenImmersion.of_comp _ (D.restrictToAmbientLimit U₀ hU₀)

/-- The smaller restricted limit is the preimage of `V₀` in `U`. -/
theorem opensRange_restrictToLargerLimit :
    (D.restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU).opensRange =
      (D.restrict U₀ hU₀).limitToFixedStage ⁻¹ᵁ U₀.ι ⁻¹ᵁ V₀ := by
  rw [opensRange_eq_preimage_of_comp_eq _ (D.restrictToAmbientLimit U₀ hU₀) _
    (D.restrictToLargerLimit_comp_restrictToAmbientLimit U₀ hU₀ V₀ hV₀ hVU) _
    (D.opensRange_restrictToAmbientLimit V₀ hV₀)]
  exact congrArg (fun m ↦ m ⁻¹ᵁ V₀) (D.restrictToAmbientLimit_comp_limitToFixedStage U₀ hU₀)

/-- The inclusions `Vᵢ ⟶ Uᵢ` are compatible with the transition morphisms. -/
theorem restrictToLarger_transition {i j : D.LaterIndex} (hij : i.1 ≤ j.1) :
    (D.restrict V₀ hV₀).transition hij ≫ D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i =
      D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU j ≫ (D.restrict U₀ hU₀).transition hij := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.restrictToLarger_comp_toFixedStage U₀ hU₀ V₀ hV₀ hVU i,
      ← Category.assoc, (D.restrict V₀ hV₀).transition_comp_toFixedStage hij, Category.assoc,
      (D.restrict U₀ hU₀).transition_comp_toFixedStage hij,
      D.restrictToLarger_comp_toFixedStage U₀ hU₀ V₀ hV₀ hVU j]
  · show _ ≫ pullback.snd (U₀.ι ≫ D.X₀.hom) (D.baseMap i) =
      _ ≫ pullback.snd (U₀.ι ≫ D.X₀.hom) (D.baseMap i)
    rw [Category.assoc, D.restrictToLarger_comp_snd U₀ hU₀ V₀ hV₀ hVU i, Category.assoc,
      show (D.restrict U₀ hU₀).transition hij ≫ pullback.snd (U₀.ι ≫ D.X₀.hom) (D.baseMap i) =
          pullback.snd (U₀.ι ≫ D.X₀.hom) (D.baseMap j) ≫
            D.descent.system.map (homOfLE hij).op from pullback.lift_snd _ _ _,
      ← Category.assoc, D.restrictToLarger_comp_snd U₀ hU₀ V₀ hV₀ hVU j]
    exact pullback.lift_snd _ _ _

/-- The inclusions `Vᵢ ⟶ Uᵢ` and `V ⟶ U` are compatible with the projections from the limit. -/
theorem restrictToLarger_projection (i : D.LaterIndex) :
    (D.restrict V₀ hV₀).projection i ≫ D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i =
      D.restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU ≫ (D.restrict U₀ hU₀).projection i := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.restrictToLarger_comp_toFixedStage U₀ hU₀ V₀ hV₀ hVU i,
      ← Category.assoc, (D.restrict V₀ hV₀).projection_comp_toFixedStage i, Category.assoc,
      (D.restrict U₀ hU₀).projection_comp_toFixedStage i,
      D.restrictToLargerLimit_comp_limitToFixedStage U₀ hU₀ V₀ hV₀ hVU]
  · show _ ≫ pullback.snd (U₀.ι ≫ D.X₀.hom) (D.baseMap i) =
      _ ≫ pullback.snd (U₀.ι ≫ D.X₀.hom) (D.baseMap i)
    rw [Category.assoc, D.restrictToLarger_comp_snd U₀ hU₀ V₀ hV₀ hVU i, Category.assoc,
      show (D.restrict U₀ hU₀).projection i ≫ pullback.snd (U₀.ι ≫ D.X₀.hom) (D.baseMap i) =
          pullback.snd (U₀.ι ≫ D.X₀.hom) (D.descent.limitCone.π.app (op D.descent.base)) ≫
            D.descent.limitCone.π.app (op i.1) from pullback.lift_snd _ _ _,
      ← Category.assoc, D.restrictToLargerLimit_comp_snd U₀ hU₀ V₀ hV₀ hVU]
    exact pullback.lift_snd _ _ _

/-- The inclusion of a quasi-compact open into itself induces the identity at each stage. -/
theorem restrictToLarger_refl (i : D.LaterIndex) :
    D.restrictToLarger U₀ hU₀ U₀ hU₀ le_rfl i = 𝟙 ((D.restrict U₀ hU₀).schemeAt i) := by
  apply pullback.hom_ext
  · rw [D.restrictToLarger_comp_toFixedStage U₀ hU₀ U₀ hU₀ le_rfl i, Scheme.homOfLE_rfl,
      Category.id_comp]
    exact Category.comp_id _
  · show _ ≫ pullback.snd (U₀.ι ≫ D.X₀.hom) (D.baseMap i) =
      _ ≫ pullback.snd (U₀.ι ≫ D.X₀.hom) (D.baseMap i)
    rw [D.restrictToLarger_comp_snd U₀ hU₀ U₀ hU₀ le_rfl i, Category.id_comp]

/-- The inclusion of a quasi-compact open into itself induces the identity at the limit. -/
theorem restrictToLargerLimit_refl :
    D.restrictToLargerLimit U₀ hU₀ U₀ hU₀ le_rfl = 𝟙 ((D.restrict U₀ hU₀).limitScheme) := by
  apply pullback.hom_ext
  · rw [D.restrictToLargerLimit_comp_limitToFixedStage U₀ hU₀ U₀ hU₀ le_rfl, Scheme.homOfLE_rfl,
      Category.id_comp]
    exact Category.comp_id _
  · show _ ≫ pullback.snd (U₀.ι ≫ D.X₀.hom)
          (D.descent.limitCone.π.app (op D.descent.base)) =
      _ ≫ pullback.snd (U₀.ι ≫ D.X₀.hom) (D.descent.limitCone.π.app (op D.descent.base))
    rw [D.restrictToLargerLimit_comp_snd U₀ hU₀ U₀ hU₀ le_rfl, Category.id_comp]

variable (W₀ : D.X₀.left.Opens) (hW₀ : IsCompact (W₀ : Set D.X₀.left)) (hWV : W₀ ≤ V₀)

/-- The inclusions induced by `W₀ ≤ V₀ ≤ U₀` compose at each stage. -/
theorem restrictToLarger_comp_restrictToLarger (i : D.LaterIndex) :
    D.restrictToLarger V₀ hV₀ W₀ hW₀ hWV i ≫ D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i =
      D.restrictToLarger U₀ hU₀ W₀ hW₀ (hWV.trans hVU) i := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.restrictToLarger_comp_toFixedStage U₀ hU₀ V₀ hV₀ hVU i,
      ← Category.assoc, D.restrictToLarger_comp_toFixedStage V₀ hV₀ W₀ hW₀ hWV i, Category.assoc,
      Scheme.homOfLE_homOfLE, D.restrictToLarger_comp_toFixedStage U₀ hU₀ W₀ hW₀ (hWV.trans hVU) i]
  · show _ ≫ pullback.snd (U₀.ι ≫ D.X₀.hom) (D.baseMap i) =
      _ ≫ pullback.snd (U₀.ι ≫ D.X₀.hom) (D.baseMap i)
    rw [Category.assoc, D.restrictToLarger_comp_snd U₀ hU₀ V₀ hV₀ hVU i,
      D.restrictToLarger_comp_snd V₀ hV₀ W₀ hW₀ hWV i,
      D.restrictToLarger_comp_snd U₀ hU₀ W₀ hW₀ (hWV.trans hVU) i]

/-- The inclusions induced by `W₀ ≤ V₀ ≤ U₀` compose at the limit. -/
theorem restrictToLargerLimit_comp_restrictToLargerLimit :
    D.restrictToLargerLimit V₀ hV₀ W₀ hW₀ hWV ≫ D.restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU =
      D.restrictToLargerLimit U₀ hU₀ W₀ hW₀ (hWV.trans hVU) := by
  apply pullback.hom_ext
  · rw [Category.assoc, D.restrictToLargerLimit_comp_limitToFixedStage U₀ hU₀ V₀ hV₀ hVU,
      ← Category.assoc, D.restrictToLargerLimit_comp_limitToFixedStage V₀ hV₀ W₀ hW₀ hWV,
      Category.assoc, Scheme.homOfLE_homOfLE,
      D.restrictToLargerLimit_comp_limitToFixedStage U₀ hU₀ W₀ hW₀ (hWV.trans hVU)]
  · show _ ≫ pullback.snd (U₀.ι ≫ D.X₀.hom)
          (D.descent.limitCone.π.app (op D.descent.base)) =
      _ ≫ pullback.snd (U₀.ι ≫ D.X₀.hom) (D.descent.limitCone.π.app (op D.descent.base))
    rw [Category.assoc, D.restrictToLargerLimit_comp_snd U₀ hU₀ V₀ hV₀ hVU,
      D.restrictToLargerLimit_comp_snd V₀ hV₀ W₀ hW₀ hWV,
      D.restrictToLargerLimit_comp_snd U₀ hU₀ W₀ hW₀ (hWV.trans hVU)]

/-! ### Base change of the derived pullbacks along an inclusion of quasi-compact opens -/

/-- The inclusion `Vᵢ ⟶ Uᵢ` lies over `X₀`: the composites `Vᵢ ⟶ Uᵢ ⟶ U₀ ⟶ X₀` and
`Vᵢ ⟶ V₀ ⟶ X₀` agree. -/
theorem restrictToLarger_comp_toFixedStage_comp_ι (i : D.LaterIndex) :
    D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i ≫ (D.restrict U₀ hU₀).toFixedStage i ≫ U₀.ι =
      (D.restrict V₀ hV₀).toFixedStage i ≫ V₀.ι := by
  rw [← Category.assoc, D.restrictToLarger_comp_toFixedStage U₀ hU₀ V₀ hV₀ hVU i,
    Category.assoc, Scheme.homOfLE_ι]

/-- The inclusion `V ⟶ U` lies over `X₀`: the composites `V ⟶ U ⟶ U₀ ⟶ X₀` and `V ⟶ V₀ ⟶ X₀`
agree. -/
theorem restrictToLargerLimit_comp_limitToFixedStage_comp_ι :
    D.restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU ≫ (D.restrict U₀ hU₀).limitToFixedStage ≫ U₀.ι =
      (D.restrict V₀ hV₀).limitToFixedStage ≫ V₀.ι := by
  rw [← Category.assoc, D.restrictToLargerLimit_comp_limitToFixedStage U₀ hU₀ V₀ hV₀ hVU,
    Category.assoc, Scheme.homOfLE_ι]

/-- Restriction from `U₀` to a smaller quasi-compact open `V₀` on derived morphism sets at a stage,
from `Hom_{D(𝒪_{Uᵢ})}(Lf_{i0}^*(K₀|_{U₀}), Lf_{i0}^*(L₀|_{U₀}))` to
`Hom_{D(𝒪_{Vᵢ})}(Lf_{i0}^*(K₀|_{V₀}), Lf_{i0}^*(L₀|_{V₀}))`: apply the derived pullback along
`Vᵢ ⟶ Uᵢ` and transport along the comparison isomorphisms. -/
def homRestrictToSmaller (i : D.LaterIndex)
    (φ : (derivedPullback ((D.restrict U₀ hU₀).toFixedStage i).toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀) ⟶
        (derivedPullback ((D.restrict U₀ hU₀).toFixedStage i).toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀)) :
    (derivedPullback ((D.restrict V₀ hV₀).toFixedStage i).toLRSHom.toShHom).obj
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀) ⟶
      (derivedPullback ((D.restrict V₀ hV₀).toFixedStage i).toLRSHom.toShHom).obj
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀) :=
  Stacks.DerivedPullback.schemeFactorTowerHom (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i)
    ((D.restrict U₀ hU₀).toFixedStage i) U₀.ι ((D.restrict V₀ hV₀).toFixedStage i) V₀.ι
    (D.restrictToLarger_comp_toFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU i) K₀ L₀ φ

/-- Restriction from `U₀` to a smaller quasi-compact open `V₀` on derived morphism sets at the
limit, from `Hom_{D(𝒪_U)}(Lf₀^*(K₀|_{U₀}), Lf₀^*(L₀|_{U₀}))` to
`Hom_{D(𝒪_V)}(Lf₀^*(K₀|_{V₀}), Lf₀^*(L₀|_{V₀}))`. -/
def homRestrictToSmallerLimit
    (φ : (derivedPullback (D.restrict U₀ hU₀).limitToFixedStage.toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀) ⟶
        (derivedPullback (D.restrict U₀ hU₀).limitToFixedStage.toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀)) :
    (derivedPullback (D.restrict V₀ hV₀).limitToFixedStage.toLRSHom.toShHom).obj
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀) ⟶
      (derivedPullback (D.restrict V₀ hV₀).limitToFixedStage.toLRSHom.toShHom).obj
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀) :=
  Stacks.DerivedPullback.schemeFactorTowerHom (D.restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU)
    (D.restrict U₀ hU₀).limitToFixedStage U₀.ι (D.restrict V₀ hV₀).limitToFixedStage V₀.ι
    (D.restrictToLargerLimit_comp_limitToFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU) K₀ L₀ φ

/-- Restriction to a smaller quasi-compact open is a map of systems of derived morphism sets. It
commutes with the transition maps of the two restricted situations. -/
theorem homTransition_homRestrictToSmaller {i j : D.LaterIndex} (hij : i.1 ≤ j.1)
    (φ : (derivedPullback ((D.restrict U₀ hU₀).toFixedStage i).toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀) ⟶
        (derivedPullback ((D.restrict U₀ hU₀).toFixedStage i).toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀)) :
    (D.restrict V₀ hV₀).homTransition ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀)
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀) hij
        (D.homRestrictToSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU i φ) =
      D.homRestrictToSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU j
        ((D.restrict U₀ hU₀).homTransition ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀)
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀) hij φ) :=
  Stacks.DerivedPullback.schemeFactorHom_schemeFactorTowerHom U₀.ι V₀.ι
    ((D.restrict U₀ hU₀).toFixedStage i) ((D.restrict U₀ hU₀).toFixedStage j)
    ((D.restrict U₀ hU₀).transition hij) ((D.restrict V₀ hV₀).toFixedStage i)
    ((D.restrict V₀ hV₀).toFixedStage j) ((D.restrict V₀ hV₀).transition hij)
    (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i) (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU j)
    ((D.restrict U₀ hU₀).transition_comp_toFixedStage hij)
    ((D.restrict V₀ hV₀).transition_comp_toFixedStage hij)
    (D.restrictToLarger_comp_toFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU i)
    (D.restrictToLarger_comp_toFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU j)
    (D.restrictToLarger_transition U₀ hU₀ V₀ hV₀ hVU hij) K₀ L₀ φ

/-- Restriction to a smaller quasi-compact open is a map of cocones on the systems of derived
morphism sets. It commutes with the comparison maps to the limits of the two restricted
situations. -/
theorem homComparison_homRestrictToSmaller (i : D.LaterIndex)
    (φ : (derivedPullback ((D.restrict U₀ hU₀).toFixedStage i).toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀) ⟶
        (derivedPullback ((D.restrict U₀ hU₀).toFixedStage i).toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀)) :
    (D.restrict V₀ hV₀).homComparison ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀)
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀) i
        (D.homRestrictToSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU i φ) =
      D.homRestrictToSmallerLimit K₀ L₀ U₀ hU₀ V₀ hV₀ hVU
        ((D.restrict U₀ hU₀).homComparison ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀)
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀) i φ) :=
  Stacks.DerivedPullback.schemeFactorHom_schemeFactorTowerHom U₀.ι V₀.ι
    ((D.restrict U₀ hU₀).toFixedStage i) (D.restrict U₀ hU₀).limitToFixedStage
    ((D.restrict U₀ hU₀).projection i) ((D.restrict V₀ hV₀).toFixedStage i)
    (D.restrict V₀ hV₀).limitToFixedStage ((D.restrict V₀ hV₀).projection i)
    (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i) (D.restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU)
    ((D.restrict U₀ hU₀).projection_comp_toFixedStage i)
    ((D.restrict V₀ hV₀).projection_comp_toFixedStage i)
    (D.restrictToLarger_comp_toFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU i)
    (D.restrictToLargerLimit_comp_limitToFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU)
    (D.restrictToLarger_projection U₀ hU₀ V₀ hV₀ hVU i) K₀ L₀ φ

/-- Restriction to a smaller quasi-compact open as a morphism of the systems of derived morphism
sets over the stages at or beyond the fixed stage. -/
def homFunctorRestrictToSmaller :
    (D.restrict U₀ hU₀).homFunctor ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀)
        ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀) ⟶
      (D.restrict V₀ hV₀).homFunctor ((derivedPullback V₀.ι.toLRSHom.toShHom).obj K₀)
        ((derivedPullback V₀.ι.toLRSHom.toShHom).obj L₀) where
  app i := TypeCat.ofHom (D.homRestrictToSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU i)
  naturality i j h := by
    ext φ
    exact (D.homTransition_homRestrictToSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU (leOfHom h) φ).symm

/-- Restriction to `U₀` followed by restriction to a smaller `V₀` is restriction to `V₀`. The
restriction maps of the ambient situation to all quasi-compact opens of `X₀` are coherent. -/
theorem homRestrictToSmaller_homRestrictToOpen (i : D.LaterIndex)
    (ψ : (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj K₀ ⟶
      (derivedPullback (D.toFixedStage i).toLRSHom.toShHom).obj L₀) :
    D.homRestrictToSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU i (D.homRestrictToOpen K₀ L₀ U₀ hU₀ i ψ) =
      D.homRestrictToOpen K₀ L₀ V₀ hV₀ i ψ :=
  Stacks.DerivedPullback.schemeFactorTowerHom_schemeFactorSquareHom (D.toFixedStage i)
    (D.restrictToAmbient U₀ hU₀ i) ((D.restrict U₀ hU₀).toFixedStage i) U₀.ι
    (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i) ((D.restrict V₀ hV₀).toFixedStage i) V₀.ι
    (D.restrictToAmbient V₀ hV₀ i) (D.restrictToAmbient_comp_toFixedStage U₀ hU₀ i)
    (D.restrictToLarger_comp_toFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU i)
    (D.restrictToLarger_comp_restrictToAmbient U₀ hU₀ V₀ hV₀ hVU i)
    (D.restrictToAmbient_comp_toFixedStage V₀ hV₀ i) K₀ L₀ ψ

/-- Restriction to `U₀` followed by restriction to a smaller `V₀` is restriction to `V₀`, at the
limit. -/
theorem homRestrictToSmallerLimit_homRestrictToOpenLimit
    (ψ : (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).obj K₀ ⟶
      (derivedPullback D.limitToFixedStage.toLRSHom.toShHom).obj L₀) :
    D.homRestrictToSmallerLimit K₀ L₀ U₀ hU₀ V₀ hV₀ hVU
        (D.homRestrictToOpenLimit K₀ L₀ U₀ hU₀ ψ) =
      D.homRestrictToOpenLimit K₀ L₀ V₀ hV₀ ψ :=
  Stacks.DerivedPullback.schemeFactorTowerHom_schemeFactorSquareHom D.limitToFixedStage
    (D.restrictToAmbientLimit U₀ hU₀) (D.restrict U₀ hU₀).limitToFixedStage U₀.ι
    (D.restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU) (D.restrict V₀ hV₀).limitToFixedStage V₀.ι
    (D.restrictToAmbientLimit V₀ hV₀) (D.restrictToAmbientLimit_comp_limitToFixedStage U₀ hU₀)
    (D.restrictToLargerLimit_comp_limitToFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU)
    (D.restrictToLargerLimit_comp_restrictToAmbientLimit U₀ hU₀ V₀ hV₀ hVU)
    (D.restrictToAmbientLimit_comp_limitToFixedStage V₀ hV₀) K₀ L₀ ψ

/-- Restriction along `U₀ ≤ U₀` is the identity at each stage. -/
theorem homRestrictToSmaller_refl (i : D.LaterIndex) :
    D.homRestrictToSmaller K₀ L₀ U₀ hU₀ U₀ hU₀ le_rfl i = id :=
  funext fun φ ↦ Stacks.DerivedPullback.schemeFactorTowerHom_id
    (D.restrictToLarger_refl U₀ hU₀ i) ((D.restrict U₀ hU₀).toFixedStage i) U₀.ι
    (D.restrictToLarger_comp_toFixedStage_comp_ι U₀ hU₀ U₀ hU₀ le_rfl i) K₀ L₀ φ

/-- Restriction along `U₀ ≤ U₀` is the identity at the limit. -/
theorem homRestrictToSmallerLimit_refl :
    D.homRestrictToSmallerLimit K₀ L₀ U₀ hU₀ U₀ hU₀ le_rfl = id :=
  funext fun φ ↦ Stacks.DerivedPullback.schemeFactorTowerHom_id
    (D.restrictToLargerLimit_refl U₀ hU₀) (D.restrict U₀ hU₀).limitToFixedStage U₀.ι
    (D.restrictToLargerLimit_comp_limitToFixedStage_comp_ι U₀ hU₀ U₀ hU₀ le_rfl) K₀ L₀ φ

/-- Restriction along `W₀ ≤ V₀ ≤ U₀` composes at each stage. -/
theorem homRestrictToSmaller_homRestrictToSmaller (i : D.LaterIndex)
    (φ : (derivedPullback ((D.restrict U₀ hU₀).toFixedStage i).toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀) ⟶
        (derivedPullback ((D.restrict U₀ hU₀).toFixedStage i).toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀)) :
    D.homRestrictToSmaller K₀ L₀ V₀ hV₀ W₀ hW₀ hWV i
        (D.homRestrictToSmaller K₀ L₀ U₀ hU₀ V₀ hV₀ hVU i φ) =
      D.homRestrictToSmaller K₀ L₀ U₀ hU₀ W₀ hW₀ (hWV.trans hVU) i φ :=
  Stacks.DerivedPullback.schemeFactorTowerHom_comp
    (D.restrictToLarger U₀ hU₀ V₀ hV₀ hVU i) ((D.restrict U₀ hU₀).toFixedStage i) U₀.ι
    ((D.restrict V₀ hV₀).toFixedStage i) V₀.ι (D.restrictToLarger V₀ hV₀ W₀ hW₀ hWV i)
    ((D.restrict W₀ hW₀).toFixedStage i) W₀.ι
    (D.restrictToLarger U₀ hU₀ W₀ hW₀ (hWV.trans hVU) i)
    (D.restrictToLarger_comp_toFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU i)
    (D.restrictToLarger_comp_toFixedStage_comp_ι V₀ hV₀ W₀ hW₀ hWV i)
    (D.restrictToLarger_comp_toFixedStage_comp_ι U₀ hU₀ W₀ hW₀ (hWV.trans hVU) i)
    (D.restrictToLarger_comp_restrictToLarger U₀ hU₀ V₀ hV₀ hVU W₀ hW₀ hWV i) K₀ L₀ φ

/-- Restriction along `W₀ ≤ V₀ ≤ U₀` composes at the limit. -/
theorem homRestrictToSmallerLimit_homRestrictToSmallerLimit
    (φ : (derivedPullback (D.restrict U₀ hU₀).limitToFixedStage.toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj K₀) ⟶
        (derivedPullback (D.restrict U₀ hU₀).limitToFixedStage.toLRSHom.toShHom).obj
          ((derivedPullback U₀.ι.toLRSHom.toShHom).obj L₀)) :
    D.homRestrictToSmallerLimit K₀ L₀ V₀ hV₀ W₀ hW₀ hWV
        (D.homRestrictToSmallerLimit K₀ L₀ U₀ hU₀ V₀ hV₀ hVU φ) =
      D.homRestrictToSmallerLimit K₀ L₀ U₀ hU₀ W₀ hW₀ (hWV.trans hVU) φ :=
  Stacks.DerivedPullback.schemeFactorTowerHom_comp
    (D.restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU) (D.restrict U₀ hU₀).limitToFixedStage U₀.ι
    (D.restrict V₀ hV₀).limitToFixedStage V₀.ι (D.restrictToLargerLimit V₀ hV₀ W₀ hW₀ hWV)
    (D.restrict W₀ hW₀).limitToFixedStage W₀.ι
    (D.restrictToLargerLimit U₀ hU₀ W₀ hW₀ (hWV.trans hVU))
    (D.restrictToLargerLimit_comp_limitToFixedStage_comp_ι U₀ hU₀ V₀ hV₀ hVU)
    (D.restrictToLargerLimit_comp_limitToFixedStage_comp_ι V₀ hV₀ W₀ hW₀ hWV)
    (D.restrictToLargerLimit_comp_limitToFixedStage_comp_ι U₀ hU₀ W₀ hW₀ (hWV.trans hVU))
    (D.restrictToLargerLimit_comp_restrictToLargerLimit U₀ hU₀ V₀ hV₀ hVU W₀ hW₀ hWV) K₀ L₀ φ

end AlgebraicGeometry.RelativeDescentSituation

end
