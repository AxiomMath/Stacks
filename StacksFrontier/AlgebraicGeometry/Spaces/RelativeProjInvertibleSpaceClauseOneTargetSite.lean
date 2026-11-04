module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackIdUnitLaw

/-!
# The slot `hsite` of the target square of clause (1) of Stacks 0D2Z

The target square of clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w : W ⟶ U(ψ)`
(`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares`) has among its hypotheses the
naturality of the identification `ρ` of the inverse image along `r = c ≫ q` of an attached
module, along the identification `ζ : v^*𝒜_d ≅ Z` (its slot `hsite`).  At the chart maps `c` is
the section `c_w` of the fibre `q`, so `r = 𝟙` and `ρ` is the unit law `(𝟙)^* ≅ 𝟭` of
Stacks 03LU; the slot is then the naturality of that unit law, with the transport along
`𝟙 ≫ v = v` absorbed.

Both pieces are read off the defining equations of the unit law
(`AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackCompIso_id_left`, with the
unit datum identified by `AlgebraicGeometry.Space.modulePushforwardCoherence_modulePullbackIdIso`)
and the naturality of a natural transformation, never by unfolding
`AlgebraicGeometry.Space.modulePullback`.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_id_left_hom_app`: the left unit law of
  Stacks 03LU at a module: `v^*(𝟙)^*M ≅ (𝟙 ≫ v)^*M = v^*M` is `(𝟙)^*(v^*M) ≅ v^*M`.
* `AlgebraicGeometry.Space.modulePullbackIdIso_hom_app_square`: **the slot `hsite` of the target
  square at `r = 𝟙`**, with the trivial splitting `Fc = 𝟙`.

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The left unit law of [Stacks Project, Tag 03LU], read at a module**: the comparison
`v^*((𝟙)^*M) ≅ (𝟙 ≫ v)^*M = v^*M` of Stacks 03LU is the unit law `(𝟙)^* ≅ 𝟭` at `v^*M`.

Read off the defining equation of the unit datum of the coherence
(`AlgebraicGeometry.Space.ModulePushforwardCoherence.modulePullbackCompIso_id_left`), whose unit
datum is the identification carrying the 03LU tag by
`AlgebraicGeometry.Space.modulePushforwardCoherence_modulePullbackIdIso`, and read at the module
by `Stacks.CategoryTheory.isoWhiskerLeft_trans_rightUnitor_hom_app`: no spelling of
`AlgebraicGeometry.Space.modulePullback` is unfolded. -/
theorem modulePullbackCompIso_id_left_hom_app {R Y : AlgebraicSpaces B S hS} (v : R ⟶ Y)
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (modulePullbackCompIso B S hS (𝟙 R) v).hom.app M =
      (modulePullbackIdIso B S hS R).hom.app ((modulePullback B S hS v).obj M) := by
  have h1 := (modulePushforwardCoherence B S hS).modulePullbackCompIso_id_left v
  rw [modulePushforwardCoherence_modulePullbackIdIso] at h1
  rw [h1]
  exact Stacks.CategoryTheory.isoWhiskerLeft_trans_rightUnitor_hom_app
    (modulePullback B S hS v) (modulePullbackIdIso B S hS R) M

/-- **The slot `hsite` of the target square of clause (1) of [Stacks Project, Tag 0D2Z] at
`r = 𝟙`**: for an identification `ζ : v^*M ≅ Z`, the inverse image along `𝟙` of `ζ`, followed by
the unit law `(𝟙)^*Z ≅ Z` of Stacks 03LU and by the trivial splitting `𝟙`, is the comparison
`v^*((𝟙)^*M) ≅ (𝟙 ≫ v)^*M` of Stacks 03LU, the transport along `𝟙 ≫ v = v` and `ζ`.

This is the hypothesis `hsite` of
`AlgebraicGeometry.Space.comp_comp_eq_map_of_target_squares` at `Φ = modulePullback`,
`κ = modulePullbackCompIso`, `r = 𝟙`, `ρr = (modulePullbackIdIso …).app Z` and `Fc = 𝟙`: the
naturality of the unit law, with the transport along `𝟙 ≫ v = v` reflexive. -/
theorem modulePullbackIdIso_hom_app_square {R Y : AlgebraicSpaces B S hS} (v : R ⟶ Y)
    {M : Modules.{u, u} B S hS Y.1 Y.2} {Zr : Modules.{u, u} B S hS R.1 R.2}
    (ζ : (modulePullback B S hS v).obj M ≅ Zr) (hv : 𝟙 R ≫ v = v) :
    (modulePullback B S hS (𝟙 R)).map ζ.hom ≫
        (modulePullbackIdIso B S hS R).hom.app Zr ≫ 𝟙 Zr =
      ((modulePullbackCompIso B S hS (𝟙 R) v).hom.app M ≫
        eqToHom (congrArg (fun k : R ⟶ Y => (modulePullback B S hS k).obj M) hv)) ≫ ζ.hom := by
  have he : eqToHom (congrArg (fun k : R ⟶ Y => (modulePullback B S hS k).obj M) hv) =
      𝟙 ((modulePullback B S hS v).obj M) := rfl
  have hc : (modulePullbackIdIso B S hS R).hom.app Zr ≫ 𝟙 Zr =
      (modulePullbackIdIso B S hS R).hom.app Zr := Category.comp_id _
  have hr : (modulePullbackCompIso B S hS (𝟙 R) v).hom.app M ≫
        eqToHom (congrArg (fun k : R ⟶ Y => (modulePullback B S hS k).obj M) hv) =
      (modulePullbackIdIso B S hS R).hom.app ((modulePullback B S hS v).obj M) := by
    rw [modulePullbackCompIso_id_left_hom_app, he]
    exact Category.comp_id _
  rw [hc, hr]
  exact (modulePullbackIdIso B S hS R).hom.naturality ζ.hom

end AlgebraicGeometry.Space

end
