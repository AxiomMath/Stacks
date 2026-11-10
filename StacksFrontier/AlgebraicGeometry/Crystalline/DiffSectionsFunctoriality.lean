module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelThickeningRingHom

/-!
# The differentials of an object of `CRIS(X/S)` on global sections, functorially

`Crystalline.GlobalCrystallineSituation.dpDifferentialsMapSheaf` is the map
`Ω_{T_B/S,δ_B} ⟶ gh_* Ω_{T_A/S,δ_A}` of sheaves induced by a morphism `g : A ⟶ B` of
`CRIS(X/S)`. The functoriality `...GlobalCrystallineSituation.firstOrderThickeningSiteMap` of
the first-order universal thickening of [Stacks, Tag 07J2] acts on sections of structure sheaves
by `(b, ω) ↦ (gh^♯ b, dg ω)`.

This module studies that map on global sections, as a map
`Ω_{T_B/S,δ_B}(T_B) ⟶ Ω_{T_A/S,δ_A}(T_A)` between the modules
`Crystalline.GlobalCrystallineSituation.crysDiffSections` in which the connection of
[Stacks, Tag 07J6] takes its values. It is semilinear for the map on section rings, it carries
the universal divided power derivation of `T_B` to that of `T_A` precomposed with the map on
section rings, and restriction along `...GlobalCrystallineSituation.firstOrderThickeningSiteMap`
carries the square-zero summand to the square-zero summand by it.

## Main definitions

* `crysDiffSectionsMap`: the map on global sections of the divided power differentials induced
  by a morphism of `CRIS(X/S)`.

## Main results

* `crysDiffSectionsMap_add`, `crysDiffSectionsMap_smul`: the map is additive and semilinear.
* `crysDiffSectionsMap_crysDerivation`: the map carries `d_{T_B} b` to `d_{T_A}(g^♯ b)`.
* `crysSheafRingMap_siteMap_diffSection`: the restriction of a differential section along the
  functoriality of the first-order thickening is the differential section of its image.
* `crysDiffSectionsMap_id`, `crysDiffSectionsMap_comp`: the map is functorial.

## References

* [Stacks Project, Tag 07J2](https://stacks.math.columbia.edu/tag/07J2)
* [Stacks Project, Tag 07J6](https://stacks.math.columbia.edu/tag/07J6)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite PresheafOfModules
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} {A B : Thickening S}

/-- The map on global sections of the divided power differentials induced by a morphism of
`CRIS(X/S)`: the map `...GlobalCrystallineSituation.dpDifferentialsMapSheaf` of sheaves,
evaluated on the top open. -/
def crysDiffSectionsMap (g : A ⟶ B) (ω : crysDiffSections B) : crysDiffSections A :=
  (dpDifferentialsMapSheaf g).app ⊤ ω

/-- The map on differentials is additive. -/
theorem crysDiffSectionsMap_add (g : A ⟶ B) (ω ω' : crysDiffSections B) :
    crysDiffSectionsMap g (ω + ω') = crysDiffSectionsMap g ω + crysDiffSectionsMap g ω' :=
  map_add ((dpDifferentialsMapSheaf g).app ⊤).hom ω ω'

/-- The map on differentials sends zero to zero. -/
@[simp] theorem crysDiffSectionsMap_zero (g : A ⟶ B) :
    crysDiffSectionsMap g (0 : crysDiffSections B) = 0 :=
  map_zero ((dpDifferentialsMapSheaf g).app ⊤).hom

/-- The map on differentials is semilinear for the map on section rings. -/
theorem crysDiffSectionsMap_smul (g : A ⟶ B) (b : crysSheafRing S B) (ω : crysDiffSections B) :
    crysDiffSectionsMap g (b • ω) = crysSheafRingMap g b • crysDiffSectionsMap g ω :=
  Scheme.Modules.Hom.app_smul (dpDifferentialsMapSheaf g) b ω

/-- The map on differentials carries the universal divided power derivation of the target to
the universal divided power derivation of the source precomposed with the map on section
rings. -/
theorem crysDiffSectionsMap_crysDerivation (g : A ⟶ B) (b : crysSheafRing S B) :
    crysDiffSectionsMap g (crysDerivation B b) = crysDerivation A (crysSheafRingMap g b) :=
  dpDifferentialsMapSheaf_sheafApp g ⊤ b

/-- The restriction of a differential section along the functoriality of the first-order
thickening is the differential section of its image. -/
theorem crysSheafRingMap_siteMap_diffSection (g : A ⟶ B) (ω : crysDiffSections B) :
    crysSheafRingMap (firstOrderThickeningSiteMap g) (firstOrderThickeningDiffSection B ω) =
      firstOrderThickeningDiffSection A (crysDiffSectionsMap g ω) := by
  refine sqZeroExt_ext ?_ rfl
  change (ambientHom g).app ⊤ (0 : crysSheafRing S B) = 0
  exact map_zero ((ambientHom g).app ⊤).hom

/-- The map on differentials of the identity is the identity. -/
@[simp] theorem crysDiffSectionsMap_id (A : Thickening S) (ω : crysDiffSections A) :
    crysDiffSectionsMap (𝟙 A) ω = ω :=
  congrArg (fun φ : objDPDifferentials A ⟶ pushforwardDPDifferentials (𝟙 A) ↦
    ConcreteCategory.hom (φ.app ⊤) ω) (dpDifferentialsMapSheaf_id A)

/-- The map on differentials of a composite is the composite of the maps. -/
theorem crysDiffSectionsMap_comp {C : Thickening S} (g : A ⟶ B) (h : B ⟶ C)
    (ω : crysDiffSections C) :
    crysDiffSectionsMap (g ≫ h) ω = crysDiffSectionsMap g (crysDiffSectionsMap h ω) :=
  congrArg (fun φ : objDPDifferentials C ⟶ pushforwardDPDifferentials (g ≫ h) ↦
    ConcreteCategory.hom (φ.app ⊤) ω) (dpDifferentialsMapSheaf_comp g h)

end Crystalline.GlobalCrystallineSituation

end
