module

public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Basic
public import StacksFrontier.Topology.Sheaves.Sheafify.ModuleStalkTensor

/-!
# The coborder comparison of relative differentials, on sections and on germs

Let `i : Z ⟶ X` be an immersion of schemes over `S`, factored as the closed immersion
`j = i.liftCoborder` into the coborder neighbourhood `W = i.coborderRange` followed by the open
immersion `ι : W ⟶ X`. The canonical map `ι^*Ω_{X/S} ⟶ Ω_{W/S}` is an isomorphism, and
`Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso` is the resulting identification
`j^*Ω_{W/S} ≅ i^*Ω_{X/S}`.

This file computes that identification on the generators `1 ⊗ d a`: it carries the section
`1 ⊗ d_{W/S}(ι^♯ a)` of `j^*Ω_{W/S}` to the section `1 ⊗ d_{X/S} a` of `i^*Ω_{X/S}`, for every
local section `a` of `𝒪_X`. In particular its germ at a point of `Z`, and hence its stalk, is
the identity on generators.

## Main definitions

* `Stacks.ConormalSequenceRight.facPullbackDifferentialsIso`: the same comparison attached to an
  arbitrary factorization `i = j ≫ ι` with `ι` an open immersion.

## Main results

* `Stacks.ConormalSequenceRight.facPullbackDifferentialsIso_hom_app_unit`: the comparison of a
  composite `j ≫ ι` carries `1 ⊗ d_{W/S}(ι^♯ a)` to `1 ⊗ d_{X/S} a`, as sections.
* `Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso_germ` and
  `Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso_stalk_germ`: the same for the
  coborder comparison of an immersion, read on germs and on the induced map of stalks.
* `Stacks.ConormalSequenceRight.unit_comp_pullbackComp_inv`: the unit of
  `(j ≫ ι)^* ⊣ (j ≫ ι)_*` is the composite of the two units, through
  `AlgebraicGeometry.Scheme.Modules.pullbackComp`.

## Route

No stalk computation is performed. The identification is pinned by a *sections* identity, from
which the germ and stalk statements follow by applying the germ map to both sides.

The sections identity is formal. Writing `c` for the canonical map `ι^*Ω_{X/S} ⟶ Ω_{W/S}`, the
comparison is `j^*(c⁻¹)` followed by `j^*ι^* ≅ (j ≫ ι)^*`. Naturality of the unit of
`j^* ⊣ j_*` along `c` moves `j^*(c)` past the unit, where it cancels `j^*(c⁻¹)`; and
`AlgebraicGeometry.Scheme.Hom.relativeDifferentialsMap_app_d` says precisely that `c` carries
`1 ⊗ d_{X/S} a` to `d_{W/S}(ι^♯ a)`. What remains is that the two units, carried by
`AlgebraicGeometry.Scheme.Modules.pullbackComp`, compose to the unit of the composite, which is
the conjugation identity `CategoryTheory.unit_conjugateEquiv` for the two adjunctions with right
adjoints `ι_* j_*` and `(j ≫ ι)_*`.

## Implementation notes

The opens `i ⁻¹ᵁ U` and `j ⁻¹ᵁ ι ⁻¹ᵁ U` are equal only propositionally, because
`AlgebraicGeometry.Scheme.Hom.liftCoborder_ι` is not a definitional equality; so the sections
identity cannot be stated with `i` in it. It is therefore proved for the factorization
`i = j ≫ ι` taken literally, where the two opens are definitionally equal, and transported by
substituting the factorization in the generalized comparison
`Stacks.ConormalSequenceRight.facPullbackDifferentialsIso`. The statement exported to consumers
is the germ one, where the two sides are allowed to sit over different opens because they land
in the same stalk.

Germs are taken with `TopCat.Presheaf.germ (C := Ab.{u})` on the underlying presheaf of the
sheaf of modules, which is the spelling that
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv` and
`Stacks.RelativeDifferentialStalkMap.relativeDifferentialsStalkKaehlerEquiv` state their
generator formulas in.

## References

* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace Stacks.ConormalSequenceRight

variable {Z W X S : Scheme.{u}}

/-! ### The unit of a composite pullback -/

/-- **The unit of `(j ≫ ι)^* ⊣ (j ≫ ι)_*` is the composite of the two units**, carried by the
comparison isomorphism `AlgebraicGeometry.Scheme.Modules.pullbackComp`. This is the
pseudofunctoriality of the pullback read on units. -/
theorem unit_comp_pullbackComp_inv (j : Z ⟶ W) (ι : W ⟶ X) (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ ι)).unit.app M ≫
        (Scheme.Modules.pushforward (j ≫ ι)).map
          ((Scheme.Modules.pullbackComp j ι).inv.app M) =
      (Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M ≫
        (Scheme.Modules.pushforward ι).map
          ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
            ((Scheme.Modules.pullback ι).obj M)) ≫
          (Scheme.Modules.pushforwardComp j ι).hom.app
            ((Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback ι).obj M)) := by
  have h := CategoryTheory.unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction j))
    (Scheme.Modules.pullbackPushforwardAdjunction (j ≫ ι))
    (Scheme.Modules.pullbackComp j ι).inv M
  simpa [CategoryTheory.Adjunction.comp_unit_app,
    Scheme.Modules.conjugateEquiv_pullbackComp_inv] using h.symm

/-- **The two units compose to the unit of the composite, on sections.** The unit of
`ι^* ⊣ ι_*` followed by the unit of `j^* ⊣ j_*` and by the comparison
`AlgebraicGeometry.Scheme.Modules.pullbackComp` is the unit of `(j ≫ ι)^* ⊣ (j ≫ ι)_*`. -/
theorem pullbackComp_hom_app_unit_unit (j : Z ⟶ W) (ι : W ⟶ X) (M : X.Modules)
    (U : X.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackComp j ι).hom.app M).app ((j ≫ ι) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
            ((Scheme.Modules.pullback ι).obj M)).app (ι ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M).app U m)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ ι)).unit.app M).app U m := by
  have h := congrArg (fun ψ => Scheme.Modules.Hom.app ψ U) (unit_comp_pullbackComp_inv j ι M)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app] at h
  have hm : ((Scheme.Modules.pullbackComp j ι).inv.app M).app ((j ≫ ι) ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ ι)).unit.app M).app U m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          ((Scheme.Modules.pullback ι).obj M)).app (ι ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M).app U m) := by
    have h2 := ConcreteCategory.congr_hom h m
    simp only [CategoryTheory.comp_apply] at h2
    exact h2
  have hcancel := congrArg (fun ψ => Scheme.Modules.Hom.app ψ ((j ≫ ι) ⁻¹ᵁ U))
    ((Scheme.Modules.pullbackComp j ι).inv_hom_id_app M)
  simp only [Scheme.Modules.Hom.comp_app, Scheme.Modules.Hom.id_app] at hcancel
  rw [← hm]
  exact ConcreteCategory.congr_hom hcancel _

/-! ### The comparison attached to a factorization -/

/-- **The comparison `j^*Ω_{W/S} ≅ i^*Ω_{X/S}` of a factorization `i = j ≫ ι` with `ι` an open
immersion.** The canonical map `ι^*Ω_{X/S} ⟶ Ω_{W/S}` is an isomorphism; pulling it back along
`j` and using `j^*ι^* ≅ (j ≫ ι)^* = i^*` gives the identification. -/
noncomputable def facPullbackDifferentialsIso (j : Z ⟶ W) (ι : W ⟶ X) [IsOpenImmersion ι]
    (i : Z ⟶ X) (hi : j ≫ ι = i) (p : X ⟶ S) :
    (Scheme.Modules.pullback j).obj (Scheme.Hom.relativeDifferentials (ι ≫ p)) ≅
      (Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p) :=
  (Scheme.Modules.pullback j).mapIso
      (asIso (Scheme.Hom.relativeDifferentialsMap ι p (ι ≫ p) (𝟙 S) (by simp))).symm ≪≫
    (Scheme.Modules.pullbackComp j ι).app _ ≪≫
    (Scheme.Modules.pullbackCongr hi).app _

/-- The coborder comparison of an immersion is the comparison of its canonical factorization. -/
theorem coborderPullbackDifferentialsIso_eq {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (p : X ⟶ S) :
    coborderPullbackDifferentialsIso i p =
      facPullbackDifferentialsIso i.liftCoborder i.coborderRange.ι i i.liftCoborder_ι p :=
  rfl

/-- The comparison of a factorization, as a composite of three morphisms. -/
theorem facPullbackDifferentialsIso_hom (j : Z ⟶ W) (ι : W ⟶ X) [IsOpenImmersion ι]
    (i : Z ⟶ X) (hi : j ≫ ι = i) (p : X ⟶ S) :
    (facPullbackDifferentialsIso j ι i hi p).hom =
      (Scheme.Modules.pullback j).map
          (inv (Scheme.Hom.relativeDifferentialsMap ι p (ι ≫ p) (𝟙 S) (by simp))) ≫
        (Scheme.Modules.pullbackComp j ι).hom.app (Scheme.Hom.relativeDifferentials p) ≫
          (Scheme.Modules.pullbackCongr hi).hom.app (Scheme.Hom.relativeDifferentials p) := by
  simp [facPullbackDifferentialsIso]

/-- Transporting a pullback along the reflexivity proof does nothing. -/
theorem pullbackCongr_rfl_hom_app {f : Z ⟶ X} (M : X.Modules) :
    (Scheme.Modules.pullbackCongr (rfl : f = f)).hom.app M = 𝟙 _ :=
  rfl

/-! ### The comparison on generators -/

/-- **The comparison of a composite carries `1 ⊗ d_{W/S}(ι^♯ a)` to `1 ⊗ d_{X/S} a`.** This is
the identification of `Stacks.ConormalSequenceRight.facPullbackDifferentialsIso` on the
generators of the pullback, read on sections over an open set of `X`. -/
theorem facPullbackDifferentialsIso_hom_app_unit (j : Z ⟶ W) (ι : W ⟶ X) [IsOpenImmersion ι]
    (p : X ⟶ S) (U : X.Opens) (a : Γ(X, U)) :
    (facPullbackDifferentialsIso j ι (j ≫ ι) rfl p).hom.app ((j ≫ ι) ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
            (Scheme.Hom.relativeDifferentials (ι ≫ p))).app (ι ⁻¹ᵁ U)
          ((Scheme.Hom.universalRelativeDerivation (ι ≫ p)).d ((ι.app U).hom a))) =
      ((Scheme.Modules.pullbackPushforwardAdjunction (j ≫ ι)).unit.app
          (Scheme.Hom.relativeDifferentials p)).app U
        ((Scheme.Hom.universalRelativeDerivation p).d a) := by
  -- the canonical map of the open immersion carries `1 ⊗ d a` to `d (ι^♯ a)`
  have hA : (Scheme.Hom.relativeDifferentialsMap ι p (ι ≫ p) (𝟙 S) (by simp)).app (ι ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app
            (Scheme.Hom.relativeDifferentials p)).app U
          ((Scheme.Hom.universalRelativeDerivation p).d a)) =
      (Scheme.Hom.universalRelativeDerivation (ι ≫ p)).d ((ι.app U).hom a) := by
    have h := Scheme.Hom.relativeDifferentialsMap_app_d (f := ι) (p := p) (p' := ι ≫ p) (𝟙 S)
      (by simp) U a
    rw [Adjunction.homEquiv_unit] at h
    exact h
  -- naturality of the unit of `j^* ⊣ j_*` along that canonical map
  have hB : ∀ x, ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
        (Scheme.Hom.relativeDifferentials (ι ≫ p))).app (ι ⁻¹ᵁ U)
        ((Scheme.Hom.relativeDifferentialsMap ι p (ι ≫ p) (𝟙 S) (by simp)).app (ι ⁻¹ᵁ U) x) =
      ((Scheme.Modules.pullback j).map
            (Scheme.Hom.relativeDifferentialsMap ι p (ι ≫ p) (𝟙 S) (by simp))).app
          (j ⁻¹ᵁ ι ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
            ((Scheme.Modules.pullback ι).obj (Scheme.Hom.relativeDifferentials p))).app
          (ι ⁻¹ᵁ U) x) := by
    intro x
    have h := congrArg (fun ψ => Scheme.Modules.Hom.app ψ (ι ⁻¹ᵁ U))
      ((Scheme.Modules.pullbackPushforwardAdjunction j).unit.naturality
        (Scheme.Hom.relativeDifferentialsMap ι p (ι ≫ p) (𝟙 S) (by simp)))
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
      Scheme.Modules.pushforward_map_app] at h
    exact ConcreteCategory.congr_hom h x
  -- the comparison cancels the pullback of the canonical map
  have hC : ∀ x, (facPullbackDifferentialsIso j ι (j ≫ ι) rfl p).hom.app ((j ≫ ι) ⁻¹ᵁ U)
        (((Scheme.Modules.pullback j).map
            (Scheme.Hom.relativeDifferentialsMap ι p (ι ≫ p) (𝟙 S) (by simp))).app
          ((j ≫ ι) ⁻¹ᵁ U) x) =
      ((Scheme.Modules.pullbackComp j ι).hom.app
        (Scheme.Hom.relativeDifferentials p)).app ((j ≫ ι) ⁻¹ᵁ U) x := by
    intro x
    have hmap : (Scheme.Modules.pullback j).map
          (Scheme.Hom.relativeDifferentialsMap ι p (ι ≫ p) (𝟙 S) (by simp)) ≫
        (facPullbackDifferentialsIso j ι (j ≫ ι) rfl p).hom =
        (Scheme.Modules.pullbackComp j ι).hom.app (Scheme.Hom.relativeDifferentials p) := by
      rw [facPullbackDifferentialsIso_hom, pullbackCongr_rfl_hom_app,
        Category.comp_id ((Scheme.Modules.pullbackComp j ι).hom.app
          (Scheme.Hom.relativeDifferentials p)),
        ← Category.assoc, ← CategoryTheory.Functor.map_comp, IsIso.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp]
    have h := congrArg (fun ψ => Scheme.Modules.Hom.app ψ ((j ≫ ι) ⁻¹ᵁ U)) hmap
    simp only [Scheme.Modules.Hom.comp_app] at h
    exact ConcreteCategory.congr_hom h x
  refine Eq.trans (congrArg
    (fun y => (facPullbackDifferentialsIso j ι (j ≫ ι) rfl p).hom.app ((j ≫ ι) ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
          (Scheme.Hom.relativeDifferentials (ι ≫ p))).app (ι ⁻¹ᵁ U) y)) hA.symm) ?_
  refine Eq.trans (congrArg
    (fun y => (facPullbackDifferentialsIso j ι (j ≫ ι) rfl p).hom.app ((j ≫ ι) ⁻¹ᵁ U) y)
    (hB (((Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app
      (Scheme.Hom.relativeDifferentials p)).app U
        ((Scheme.Hom.universalRelativeDerivation p).d a)))) ?_
  exact Eq.trans (hC _) (pullbackComp_hom_app_unit_unit j ι
    (Scheme.Hom.relativeDifferentials p) U ((Scheme.Hom.universalRelativeDerivation p).d a))

/-- **The comparison of a factorization on germs.** The germ at `z` of `1 ⊗ d_{W/S}(ι^♯ a)` goes
to the germ at `z` of `1 ⊗ d_{X/S} a`. The two germs may be taken over different opens of `Z`,
since they land in the same stalk. -/
theorem facPullbackDifferentialsIso_germ (j : Z ⟶ W) (ι : W ⟶ X) [IsOpenImmersion ι]
    (i : Z ⟶ X) (hi : j ≫ ι = i) (p : X ⟶ S) (U : X.Opens) (a : Γ(X, U)) (z : Z)
    (hz : z ∈ i ⁻¹ᵁ U) (hz' : z ∈ j ⁻¹ᵁ ι ⁻¹ᵁ U) :
    TopCat.Presheaf.germ (C := Ab.{u})
        ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf
        (j ⁻¹ᵁ ι ⁻¹ᵁ U) z hz'
        ((facPullbackDifferentialsIso j ι i hi p).hom.app (j ⁻¹ᵁ ι ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackPushforwardAdjunction j).unit.app
              (Scheme.Hom.relativeDifferentials (ι ≫ p))).app (ι ⁻¹ᵁ U)
            ((Scheme.Hom.universalRelativeDerivation (ι ≫ p)).d ((ι.app U).hom a)))) =
      TopCat.Presheaf.germ (C := Ab.{u})
        ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf
        (i ⁻¹ᵁ U) z hz
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
            (Scheme.Hom.relativeDifferentials p)).app U
          ((Scheme.Hom.universalRelativeDerivation p).d a)) := by
  subst hi
  exact congrArg
    (TopCat.Presheaf.germ (C := Ab.{u})
      ((Scheme.Modules.pullback (j ≫ ι)).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf
      ((j ≫ ι) ⁻¹ᵁ U) z hz)
    (facPullbackDifferentialsIso_hom_app_unit j ι p U a)

/-- **The coborder comparison of an immersion on germs.** For an immersion `i : Z ⟶ X` over `S`
with closed factor `j` into the coborder neighbourhood and open factor `ι`, the germ at `z` of
`1 ⊗ d_{W/S}(ι^♯ a)` goes to the germ at `z` of `1 ⊗ d_{X/S} a`, for every local section `a` of
`𝒪_X`. -/
theorem coborderPullbackDifferentialsIso_germ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (p : X ⟶ S) (U : X.Opens) (a : Γ(X, U)) (z : Z) (hz : z ∈ i ⁻¹ᵁ U)
    (hz' : z ∈ i.liftCoborder ⁻¹ᵁ i.coborderRange.ι ⁻¹ᵁ U) :
    TopCat.Presheaf.germ (C := Ab.{u})
        ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf
        (i.liftCoborder ⁻¹ᵁ i.coborderRange.ι ⁻¹ᵁ U) z hz'
        ((coborderPullbackDifferentialsIso i p).hom.app
          (i.liftCoborder ⁻¹ᵁ i.coborderRange.ι ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
              (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).app
              (i.coborderRange.ι ⁻¹ᵁ U)
            ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d
              ((i.coborderRange.ι.app U).hom a)))) =
      TopCat.Presheaf.germ (C := Ab.{u})
        ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf
        (i ⁻¹ᵁ U) z hz
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
            (Scheme.Hom.relativeDifferentials p)).app U
          ((Scheme.Hom.universalRelativeDerivation p).d a)) :=
  facPullbackDifferentialsIso_germ i.liftCoborder i.coborderRange.ι i i.liftCoborder_ι p U a z
    hz hz'

/-- **The coborder comparison on stalks.** The induced map of stalks at `z` carries the germ of
`1 ⊗ d_{W/S}(ι^♯ a)` to the germ of `1 ⊗ d_{X/S} a`. Composed with the generator formulas of
`RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv` on both sides, this says
that on generators the stalk of the comparison is the identity. -/
theorem coborderPullbackDifferentialsIso_stalk_germ {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (p : X ⟶ S) (U : X.Opens) (a : Γ(X, U)) (z : Z) (hz : z ∈ i ⁻¹ᵁ U)
    (hz' : z ∈ i.liftCoborder ⁻¹ᵁ i.coborderRange.ι ⁻¹ᵁ U) :
    Stacks.Sheafify.ModuleStalkTensor.stalkLinearMapOfHom Z.sheaf.presheaf z
        (coborderPullbackDifferentialsIso i p).hom.val
        (TopCat.Presheaf.germ (C := Ab.{u})
          ((Scheme.Modules.pullback i.liftCoborder).obj
            (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).val.presheaf
          (i.liftCoborder ⁻¹ᵁ i.coborderRange.ι ⁻¹ᵁ U) z hz'
          (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
              (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p))).app
              (i.coborderRange.ι ⁻¹ᵁ U)
            ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d
              ((i.coborderRange.ι.app U).hom a)))) =
      TopCat.Presheaf.germ (C := Ab.{u})
        ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf
        (i ⁻¹ᵁ U) z hz
        (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
            (Scheme.Hom.relativeDifferentials p)).app U
          ((Scheme.Hom.universalRelativeDerivation p).d a)) := by
  refine Eq.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply
    (i.liftCoborder ⁻¹ᵁ i.coborderRange.ι ⁻¹ᵁ U) z hz'
    ((PresheafOfModules.toPresheaf Z.ringCatSheaf.obj).map
      (coborderPullbackDifferentialsIso i p).hom.val) _) ?_
  exact coborderPullbackDifferentialsIso_germ i p U a z hz hz'

end Stacks.ConormalSequenceRight

end
