module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.TameMultiplicativeGroup.KummerTower

/-!
# Geometric generic points of covers of `𝐆_m` as ring maps

A finite étale cover `Y ⟶ 𝐆_{m,k}` is affine. A point of its fibre at the geometric generic point
`η̄ : Spec Ω ⟶ 𝐆_m` is the same as a ring map `Γ(Y) → Ω` whose composite with the structure map
`k[x]_x → Γ(Y)` is the base map `k[x]_x → Ω`; maps of covers act by precomposition, and a map of
global sections over `k[x]_x` comes from a unique map of covers.

## Main definitions

* `AlgebraicGeometry.TameMultiplicativeGroup.strHom Y`: the structure map `k[x]_x → Γ(Y)`.
* `AlgebraicGeometry.TameMultiplicativeGroup.pointRingHom y`: the ring map of a point.
* `AlgebraicGeometry.TameMultiplicativeGroup.pointOfRingHom`: the point of a ring map.
* `AlgebraicGeometry.TameMultiplicativeGroup.homOfRingHom`: the map of covers of a ring map.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.TameMultiplicativeGroup

variable {k : Type u} [Field k]

/-- The structure morphism of a cover, with target `𝐆_m`. -/
abbrev homGm (Y : FiniteEtaleOver (Gm k)) : Y.left ⟶ Gm k := Y.hom

/-- The source of a finite étale cover of `𝐆_m` is affine. -/
instance (Y : FiniteEtaleOver (Gm k)) : IsAffine Y.left := by
  haveI : IsFinite (homGm Y) := Y.prop.1
  exact isAffine_of_isAffineHom (homGm Y)

/-- The structure map `k[x]_x → Γ(Y)` of a cover. -/
def strHom (Y : FiniteEtaleOver (Gm k)) : CommRingCat.of (Ring k) ⟶ Γ(Y.left, ⊤) :=
  (Scheme.ΓSpecIso _).inv ≫ (homGm Y).appTop

/-- The structure morphism of a cover is `Spec` of `strHom Y`, up to `Y ≅ Spec Γ(Y)`. -/
theorem hom_eq_strHom (Y : FiniteEtaleOver (Gm k)) :
    homGm Y = Y.left.isoSpec.hom ≫ Spec.map (strHom Y) := by
  rw [strHom, Spec.map_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality,
    Category.assoc, Scheme.isoSpec_Spec_hom, ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id,
    Category.comp_id]

/-- The ring map `Γ(Y) → Ω` of a point `Spec Ω ⟶ Y`. -/
def pointRingHom {Y : FiniteEtaleOver (Gm k)} (y : Spec (CommRingCat.of (Omega k)) ⟶ Y.left) :
    Γ(Y.left, ⊤) ⟶ CommRingCat.of (Omega k) :=
  Spec.preimage (y ≫ Y.left.isoSpec.hom)

/-- `Spec` of the ring map of a point `y` is `y` followed by `Y ≅ Spec Γ(Y)`. -/
theorem specMap_pointRingHom {Y : FiniteEtaleOver (Gm k)}
    (y : Spec (CommRingCat.of (Omega k)) ⟶ Y.left) :
    Spec.map (pointRingHom y) = y ≫ Y.left.isoSpec.hom := Spec.map_preimage _

/-- The point `Spec Ω ⟶ Y` of a ring map `Γ(Y) → Ω`. -/
def pointOfRingHom {Y : FiniteEtaleOver (Gm k)} (χ : Γ(Y.left, ⊤) ⟶ CommRingCat.of (Omega k)) :
    Spec (CommRingCat.of (Omega k)) ⟶ Y.left :=
  Spec.map χ ≫ Y.left.isoSpec.inv

/-- The ring map of the point of a ring map `χ` is `χ`. -/
theorem pointRingHom_pointOfRingHom {Y : FiniteEtaleOver (Gm k)}
    (χ : Γ(Y.left, ⊤) ⟶ CommRingCat.of (Omega k)) : pointRingHom (pointOfRingHom χ) = χ := by
  rw [pointRingHom, pointOfRingHom, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Spec.preimage_map]

/-- The point of the ring map of a point `y` is `y`. -/
theorem pointOfRingHom_pointRingHom {Y : FiniteEtaleOver (Gm k)}
    (y : Spec (CommRingCat.of (Omega k)) ⟶ Y.left) : pointOfRingHom (pointRingHom y) = y := by
  rw [pointOfRingHom, specMap_pointRingHom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- A point `Spec Ω ⟶ Y` is determined by its ring map `Γ(Y) → Ω`. -/
theorem pointRingHom_injective {Y : FiniteEtaleOver (Gm k)} :
    Function.Injective (pointRingHom (Y := Y)) := fun y y' h ↦ by
  rw [← pointOfRingHom_pointRingHom y, h, pointOfRingHom_pointRingHom]

/-- A point lies over the geometric generic point exactly when its ring map is over `k[x]_x`. -/
theorem comp_hom_eq_iff {Y : FiniteEtaleOver (Gm k)}
    (y : Spec (CommRingCat.of (Omega k)) ⟶ Y.left) :
    y ≫ homGm Y = (genericGeometricPoint k).hom ↔
      strHom Y ≫ pointRingHom y = CommRingCat.ofHom (baseHom k) := by
  rw [← specMap_baseHom, hom_eq_strHom, ← Category.assoc, ← specMap_pointRingHom, ← Spec.map_comp]
  exact ⟨fun h ↦ Spec.map_injective h, fun h ↦ by rw [h]⟩

/-- The ring map of `y ≫ g` is the ring map of `y` precomposed with `g` on global sections. -/
theorem pointRingHom_comp {Y Y' : FiniteEtaleOver (Gm k)} (g : Y ⟶ Y')
    (y : Spec (CommRingCat.of (Omega k)) ⟶ Y.left) :
    pointRingHom (y ≫ g.left) = g.left.appTop ≫ pointRingHom y := by
  apply Spec.map_injective
  rw [specMap_pointRingHom, Spec.map_comp, specMap_pointRingHom, Category.assoc,
    Category.assoc, Scheme.isoSpec_hom_naturality]

/-- The map of covers given by a map of global sections over `k[x]_x`. -/
def homOfRingHom {Y Y' : FiniteEtaleOver (Gm k)} (θ : Γ(Y'.left, ⊤) ⟶ Γ(Y.left, ⊤))
    (hθ : strHom Y' ≫ θ = strHom Y) : Y ⟶ Y' :=
  MorphismProperty.Over.homMk (Y.left.isoSpec.hom ≫ Spec.map θ ≫ Y'.left.isoSpec.inv) (by
    change _ ≫ homGm Y' = homGm Y
    rw [Category.assoc, Category.assoc, hom_eq_strHom Y', Iso.inv_hom_id_assoc, ← Spec.map_comp,
      hθ, ← hom_eq_strHom])

/-- The ring map of `y` followed by `homOfRingHom θ hθ` is the ring map of `y` precomposed with
`θ`. -/
theorem pointRingHom_homOfRingHom {Y Y' : FiniteEtaleOver (Gm k)}
    (θ : Γ(Y'.left, ⊤) ⟶ Γ(Y.left, ⊤)) (hθ : strHom Y' ≫ θ = strHom Y)
    (y : Spec (CommRingCat.of (Omega k)) ⟶ Y.left) :
    pointRingHom (y ≫ (homOfRingHom θ hθ).left) = θ ≫ pointRingHom y := by
  apply Spec.map_injective
  show Spec.map (Spec.preimage _) = _
  rw [Spec.map_preimage, Spec.map_comp, specMap_pointRingHom]
  show y ≫ (Y.left.isoSpec.hom ≫ Spec.map θ ≫ Y'.left.isoSpec.inv) ≫ Y'.left.isoSpec.hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end AlgebraicGeometry.TameMultiplicativeGroup

end
