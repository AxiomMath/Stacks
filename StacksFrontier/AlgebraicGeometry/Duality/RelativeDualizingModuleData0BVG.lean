module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Noetherian
public import StacksFrontier.AlgebraicGeometry.Discriminant.FactorizationIndependence
public import StacksFrontier.AlgebraicGeometry.Discriminant.Localization
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule0BVG
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.RingTheory.TraceElement.FiniteFlat
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation

/-!
# Chart data for the relative dualizing module of a locally quasi-finite morphism

Let `f : Y ⟶ X` be a locally quasi-finite morphism of locally Noetherian schemes.  For a pair
of affine charts `V ⊆ f⁻¹ U` the algebraic relative dualizing module
`Stacks.Discriminant.dualizingModule` of Tag 0BSZ is defined from a finite-open factorization
of `Γ(X, U) → Γ(Y, V)`, and Tags 0BT1 and 0BT2 say that it does not depend on the
factorization and that it localizes correctly in the base and in the source.  The relative
dualizing module `ω_{Y/X}` is a coherent `𝒪_Y`-module whose sections on every such `V` are
`ω_{Γ(Y,V)/Γ(X,U)}`, compatibly with all of that.

This file records the *data* that such a module carries, as the structure
`Stacks.Discriminant.RelativeDualizingModuleData`, together with the chart input that is
available unconditionally and with the rigidity statements that pin the underlying sheaf.

## Main definitions

* `Stacks.Discriminant.AffineChartPair` is the type of pairs of an affine open of the base
  and an affine open of the source lying over it.
* `Stacks.Discriminant.RelativeDualizingModuleData` bundles a sheaf on the source together
  with its affine identifications with the algebraic relative dualizing modules, their
  independence of the chosen finite-open factorization, and their compatibility with
  shrinking the base chart and the source chart to a principal open.

## Main results

* `Stacks.Discriminant.exists_affineChartPair` and
  `Stacks.Discriminant.iSup_affineChartPair_eq_top` say that the source opens of the chart
  pairs cover the source.
* `Stacks.Discriminant.nontrivial_dualizingModule_ofFinite` and
  `Stacks.Discriminant.nontrivial_dualizingModule_ofFinite_self` show the algebraic relative
  dualizing module of a module-finite algebra is not the zero module when its dual is not,
  and in particular that the one of `A → A` is not when `A` is not the zero ring.
* `Stacks.Discriminant.RelativeDualizingModuleData.subsingleton_sections_iff` and
  `Stacks.Discriminant.RelativeDualizingModuleData.nontrivial_sections` show that the
  sections of the sheaf of such a datum over an affine chart vanish exactly when the
  algebraic relative dualizing module of that chart vanishes;
  `Stacks.Discriminant.RelativeDualizingModuleData.nontrivial_sections_ofFinite` composes
  this with the previous item.  Together they rule out the zero sheaf as a carrier of chart
  data: on any chart whose coordinate-ring map is module-finite with nonzero dual the
  sections are nonzero.

## Implementation notes

The structure's `localEquiv` field is indexed by a chart pair *and* a finite-open
factorization of its coordinate-ring map, rather than by a chart pair alone, so that no
factorization has to be chosen to state it; `localEquiv_natural` is then the assertion that
the family is the canonical comparison of Tag 0BT1 in every variable.  Independence of the
factorization is therefore not an extra construction but a field, and
`Stacks.Discriminant.dualizingModuleEquiv_refl` together with
`Stacks.Discriminant.dualizingModuleEquiv_trans` are what make the field satisfiable.

The two remaining compatibilities are stated only for *principal* shrinkings — of the base
chart in `localEquiv_baseBasicOpen`, through Tag 0BT2 part (1), and of the source chart in
`localEquiv_basicOpen`, through Tag 0BT2 part (2).  No compatibility is required between two
affine charts of the base that are not related by inverting a single function, which is the
exact extent to which Tag 0BT2 supplies comparisons.

Restriction of sections is the already available `Γ(X, V)`-linear restriction map
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ`.

## References

* [Stacks Project, Tag 0BSZ](https://stacks.math.columbia.edu/tag/0BSZ)
* [Stacks Project, Tag 0BT1](https://stacks.math.columbia.edu/tag/0BT1)
* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
* [Stacks Project, Tag 0BVG](https://stacks.math.columbia.edu/tag/0BVG)
-/


@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry TensorProduct

universe u v

namespace Stacks.Discriminant

open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

section OfFinite

attribute [local instance] algebraDualModule

/-- For a module-finite algebra the algebraic relative dualizing module of the identity
factorization is `Hom_A(B, A) ⊗_B B`, so it is nonzero as soon as `Hom_A(B, A)` is. -/
theorem nontrivial_dualizingModule_ofFinite (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] [Nontrivial (Module.Dual A B)] :
    Nontrivial (dualizingModule (selfFactorization A B)) := by
  unfold dualizingModule
  exact (TensorProduct.rid B (Module.Dual A B)).toEquiv.nontrivial

/-- The algebraic relative dualizing module of the identity factorization of `A → A` is not
the zero module when `A` is not the zero ring: it is `Hom_A(A, A) ⊗_A A`, which is `A`. -/
theorem nontrivial_dualizingModule_ofFinite_self (A : Type u) [CommRing A] [Nontrivial A] :
    Nontrivial (dualizingModule (selfFactorization A A)) :=
  have : Nontrivial (Module.Dual A A) :=
    (LinearMap.ringLmapEquivSelf A A A).toEquiv.nontrivial
  nontrivial_dualizingModule_ofFinite A A

end OfFinite

section ChartData

/-- A chart pair of a morphism of schemes: an affine open of the base together with an affine
open of the source lying over it. -/
def AffineChartPair {X Y : Scheme.{u}} (f : Y ⟶ X) : Type u :=
  {p : X.affineOpens × Y.affineOpens // (p.2).1 ≤ f ⁻¹ᵁ (p.1).1}

/-- Every point of the source lies in an affine open mapping into an affine open of the
base. -/
theorem exists_affineChartPair {X Y : Scheme.{u}} (f : Y ⟶ X) (y : Y) :
    ∃ (U : X.affineOpens) (V : Y.affineOpens), y ∈ V.1 ∧ V.1 ≤ f ⁻¹ᵁ U.1 := by
  obtain ⟨-, ⟨U, hU, rfl⟩, hfy, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.base y)) isOpen_univ
  obtain ⟨-, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ (f ⁻¹ᵁ U).1 from hfy) (f ⁻¹ᵁ U).2
  exact ⟨⟨U, hU⟩, ⟨V, hV⟩, hyV, hVU⟩

/-- The source opens of the chart pairs of a morphism cover the source. -/
theorem iSup_affineChartPair_eq_top {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (⨆ p : AffineChartPair f, ((p.1).2).1) = ⊤ := by
  refine top_le_iff.mp fun y _ ↦ ?_
  obtain ⟨U, V, hyV, hVU⟩ := exists_affineChartPair f y
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(U, V), hVU⟩, hyV⟩

/-- The chart data of the relative dualizing module of a locally quasi-finite morphism of
locally Noetherian schemes, as described in Tag 0BVG: a sheaf on the source, together with
the canonical identification of its sections over every affine chart with the algebraic
relative dualizing module of that chart. -/
structure RelativeDualizingModuleData {X Y : Scheme.{u}} (f : Y ⟶ X)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyQuasiFinite f] where
  /-- The underlying sheaf of modules on the source. -/
  sheaf : Y.Modules
  /-- The sheaf is quasi-coherent. -/
  isQuasicoherent : sheaf.IsQuasicoherent
  /-- The sheaf is coherent. -/
  isCoherent : sheaf.IsCoherent
  /-- The dualizing module on each affine chart is realized by a finite-open
  factorization of its coordinate-ring map. -/
  factorization :
    ∀ (U : X.affineOpens) (V : Y.affineOpens)
      (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) :=
        (f.appLE U V hVU).hom.toAlgebra
      Nonempty (FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
  /-- The sections of the sheaf over an affine chart are the algebraic relative dualizing
  module. -/
  localEquiv :
    ∀ (U : X.affineOpens) (V : Y.affineOpens)
      (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) :=
        (f.appLE U V hVU).hom.toAlgebra
      ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
        Γ(sheaf, V.1) ≃ₗ[Γ(Y, V.1)] dualizingModule F
  /-- The affine identification is independent of the chosen finite-open factorization. -/
  localEquiv_natural :
    ∀ (U : X.affineOpens) (V : Y.affineOpens)
      (hVU : V.1 ≤ f ⁻¹ᵁ U.1),
      letI : IsNoetherianRing Γ(X, U.1) :=
        IsLocallyNoetherian.component_noetherian U
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) :=
        (f.appLE U V hVU).hom.toAlgebra
      ∀ (F G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
        (s : Γ(sheaf, V.1)),
        localEquiv U V hVU G s =
          dualizingModuleEquiv F G (localEquiv U V hVU F s)
  /-- Localizing an affine open of the base does not change the identification
  of sections on an affine open of the source contained over it. -/
  localEquiv_baseBasicOpen :
    ∀ (U : X.affineOpens) (V : Y.affineOpens)
      (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (a : Γ(X, U.1))
      (hVa : V.1 ≤ f ⁻¹ᵁ (X.basicOpen a)),
      let Ua : X.affineOpens := ⟨X.basicOpen a, U.2.basicOpen a⟩
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) :=
        (f.appLE U V hVU).hom.toAlgebra
      letI : Algebra Γ(X, Ua.1) Γ(Y, V.1) :=
        (f.appLE Ua V hVa).hom.toAlgebra
      letI : Algebra Γ(X, U.1) Γ(X, Ua.1) :=
        (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
      letI : IsNoetherianRing Γ(X, U.1) :=
        IsLocallyNoetherian.component_noetherian U
      letI : IsNoetherianRing Γ(Y, V.1) :=
        IsLocallyNoetherian.component_noetherian V
      letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
        (RingHom.quasiFinite_algebraMap).mp
          (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
      letI : IsLocalization.Away a Γ(X, Ua.1) :=
        U.2.isLocalization_basicOpen a
      letI : IsScalarTower Γ(X, U.1) Γ(X, Ua.1) Γ(Y, V.1) :=
        IsScalarTower.of_algebraMap_eq' (by
          change (f.appLE U V hVU).hom =
            ((f.appLE Ua V hVa).hom).comp
              (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom
          rw [← CommRingCat.hom_comp, f.map_appLE hVa
            (homOfLE (X.basicOpen_le a)).op])
      ∀ (F : FiniteOpenFactorization.{u, u, u}
          Γ(X, U.1) Γ(Y, V.1))
        (G : FiniteOpenFactorization.{u, u, u}
          Γ(X, Ua.1) Γ(Y, V.1)) (s : Γ(sheaf, V.1)),
        localEquiv Ua V hVa G s =
          dualizingModule_equiv_of_isLocalization_away a F G
            (localEquiv U V hVU F s)
  /-- The affine identifications commute with restriction to principal opens;
  the corresponding map of algebraic dualizing modules is localization. -/
  localEquiv_basicOpen :
    ∀ (U : X.affineOpens) (V : Y.affineOpens)
      (hVU : V.1 ≤ f ⁻¹ᵁ U.1) (g : Γ(Y, V.1)),
      let W : Y.affineOpens := ⟨Y.basicOpen g, V.2.basicOpen g⟩
      let hWU : W.1 ≤ f ⁻¹ᵁ U.1 := (Y.basicOpen_le g).trans hVU
      letI : Algebra Γ(X, U.1) Γ(Y, V.1) :=
        (f.appLE U V hVU).hom.toAlgebra
      letI : Algebra Γ(X, U.1) Γ(Y, W.1) :=
        (f.appLE U W hWU).hom.toAlgebra
      letI : Algebra Γ(Y, V.1) Γ(Y, W.1) :=
        (Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom.toAlgebra
      letI : IsNoetherianRing Γ(X, U.1) :=
        IsLocallyNoetherian.component_noetherian U
      letI : IsNoetherianRing Γ(Y, V.1) :=
        IsLocallyNoetherian.component_noetherian V
      letI : Algebra.QuasiFinite Γ(X, U.1) Γ(Y, V.1) :=
        (RingHom.quasiFinite_algebraMap).mp
          (LocallyQuasiFinite.quasiFinite_appLE U.2 V.2 hVU)
      letI : IsLocalization.Away g Γ(Y, W.1) :=
        V.2.isLocalization_basicOpen g
      letI : IsScalarTower Γ(X, U.1) Γ(Y, V.1) Γ(Y, W.1) :=
        IsScalarTower.of_algebraMap_eq' (by
          change (f.appLE U W hWU).hom =
            ((Y.presheaf.map (homOfLE (Y.basicOpen_le g)).op).hom).comp
              (f.appLE U V hVU).hom
          rw [← CommRingCat.hom_comp, ← f.appLE_map hVU
            (homOfLE (Y.basicOpen_le g)).op])
      ∀ (F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1))
        (G : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, W.1)),
        letI : Module Γ(Y, V.1) (dualizingModule G) :=
          Module.compHom (dualizingModule G)
            (algebraMap Γ(Y, V.1) Γ(Y, W.1))
        letI : IsScalarTower Γ(Y, V.1) Γ(Y, W.1)
            (dualizingModule G) :=
          IsScalarTower.of_compHom Γ(Y, V.1) Γ(Y, W.1) _
        ∃ (r : dualizingModule F →ₗ[Γ(Y, V.1)]
            dualizingModule G)
          (hr : IsLocalizedModule (Submonoid.powers g) r),
          (∀ s : Γ(sheaf, V.1),
              localEquiv U W hWU G ((restrictₗ sheaf (Y.basicOpen_le g)) s) =
                r (localEquiv U V hVU F s)) ∧
            (∀ m : dualizingModule G,
              localizedModule_dualizingModule_equiv g F G r hr m = m)

end ChartData

namespace RelativeDualizingModuleData

variable {X Y : Scheme.{u}} {f : Y ⟶ X} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  [LocallyQuasiFinite f]

/-- The sections of the sheaf of a chart datum over an affine chart are the zero module
exactly when the algebraic relative dualizing module of that chart is.  In particular the
sheaf of a chart datum is not the zero sheaf as soon as one chart has nonvanishing algebraic
relative dualizing module. -/
theorem subsingleton_sections_iff (D : RelativeDualizingModuleData f) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      Subsingleton Γ(D.sheaf, V.1) ↔ Subsingleton (dualizingModule F) := by
  intro F
  exact ⟨fun _ ↦ (D.localEquiv U V hVU F).toEquiv.symm.subsingleton,
    fun _ ↦ (D.localEquiv U V hVU F).toEquiv.subsingleton⟩

/-- A chart whose algebraic relative dualizing module is nonzero has nonzero sections in any
chart datum. -/
theorem nontrivial_sections (D : RelativeDualizingModuleData f) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1) :
    letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
    ∀ F : FiniteOpenFactorization.{u, u, u} Γ(X, U.1) Γ(Y, V.1),
      Nontrivial (dualizingModule F) → Nontrivial Γ(D.sheaf, V.1) := by
  intro F hF
  have := hF
  exact (D.localEquiv U V hVU F).toEquiv.nontrivial

/-- On a chart whose coordinate-ring map is module-finite with nonzero `A`-dual, the sections
of the sheaf of any chart datum are nonzero. -/
theorem nontrivial_sections_ofFinite (D : RelativeDualizingModuleData f) (U : X.affineOpens)
    (V : Y.affineOpens) (hVU : V.1 ≤ f ⁻¹ᵁ U.1)
    (hfin : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
      Module.Finite Γ(X, U.1) Γ(Y, V.1))
    (hdual : letI : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
      Nontrivial (Module.Dual Γ(X, U.1) Γ(Y, V.1))) :
    Nontrivial Γ(D.sheaf, V.1) :=
  let : Algebra Γ(X, U.1) Γ(Y, V.1) := (f.appLE U V hVU).hom.toAlgebra
  let := hfin
  let := hdual
  D.nontrivial_sections U V hVU
    (selfFactorization Γ(X, U.1) Γ(Y, V.1))
    (nontrivial_dualizingModule_ofFinite _ _)

end RelativeDualizingModuleData

end Stacks.Discriminant

end
