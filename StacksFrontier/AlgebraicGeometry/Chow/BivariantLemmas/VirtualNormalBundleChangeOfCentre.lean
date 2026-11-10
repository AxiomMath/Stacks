module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessNormalSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleNormalConeBaseChange
public import StacksFrontier.AlgebraicGeometry.Constructions.VectorBundleLift
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreChangeOfCentre
public import StacksFrontier.AlgebraicGeometry.Chow.NormalConeZeroSection

/-!
# The vector bundle of a virtual normal bundle over the normal cone of a regular immersion

Let `iY : Y ⟶ X` be a regular closed immersion with `Y` locally Noetherian, `iZY : Z ⟶ Y` a closed
immersion, `iZ = iZY ≫ iY`, and `𝒩₁` a virtual normal bundle for `iZ` (Stacks 0FBQ) with total
space `N₁ = 𝐕(𝒩₁^∨)`. Let `a : 𝒞_{Y/X}^∨∨|_Z ⟶ 𝒩₁^∨` be compatible with the surjections onto the
conormal sheaves and the canonical map `𝒞_{Y/X}|_Z ⟶ 𝒞_{Z/X}` of Stacks 01R4: this is the left
square of the hypothesis of Stacks 0FEC (`Stacks.Chow.ConormalCompatibleVirtualNormalBundles`)
when the virtual normal bundle of `Y ⊆ X` is the normal bundle `𝒞_{Y/X}^∨` of the regular
immersion. The last step of the proof of Stacks 0FEC uses the morphism

  `Ψ : N₁ ⟶ 𝐕(𝒞_{Y/X}^∨∨|_Z) = 𝐕(𝒞_{Y/X}^∨∨) ×_Y Z ⟶ 𝐕(𝒞_{Y/X}^∨∨) ≅ C_YX`

and two facts about it, proved here:

* (G1) on the normal cone `C_ZX ⊆ N₁` it is the morphism of normal cones `C_ZX ⟶ C_YX` induced by
  `ℐ_Y ⊆ ℐ_Z` (`Stacks.Chow.normalConeChangeOfCentreMap`), and it lies over `Z ⟶ Y`;
* (G2) if `0 ⟶ 𝒞_{Y/X}^∨∨|_Z ⟶ 𝒩₁^∨ ⟶ (𝒩')^∨ ⟶ 0` is short exact, `𝒩'` a virtual normal bundle for
  `iZY`, then `N' ⟶ N₁` is the base change of the zero section `o : Y ⟶ C_YX` along `Ψ`.

Both are statements about morphisms into vector bundles, which are classified by module maps
(`AlgebraicGeometry.Scheme.Modules.vectorBundleClassifyingMap`). For (G1) the classifying map of
`C_ZX ⟶ C_YX ⟶ 𝐕(𝒞_{Y/X}^∨∨)` is computed on degree-one classes: on the charts over affine opens
`U = Spec A` of `X` the morphism of normal cones is `Gr_{ℐ_Y(U)}(A) ⟶ Gr_{ℐ_Z(U)}(A)`, which
carries the class of `a ∈ ℐ_Y(U)` to its class in `ℐ_Z(U)/ℐ_Z(U)²`, i.e. to its image under Stacks
01R4. For (G2) the zero section of `C_YX` is that of the vector bundle (on the charts it is cut out
by the positive-degree ideal, which contains the degree-one classes), and the fibre of
`𝐕(𝒩₁^∨) ⟶ 𝐕(ℰ)` over the zero section is `𝐕(coker)`
(`AlgebraicGeometry.Scheme.Modules.isPullback_vectorBundleMap_of_shortExact`).

## Main definitions

* `Stacks.Chow.regularNormalConeIso` — `C_YX ≅ 𝐕(𝒞_{Y/X}^∨∨)` for a regular immersion.
* `Stacks.Chow.normalConeCompMap` — the morphism `Ψ : N₁ ⟶ C_YX`.

## Main results

* `Stacks.Chow.normalConeCompMap_toBase` — `Ψ` lies over `Z ⟶ Y`.
* `Stacks.Chow.normalConeEmbedding_comp_normalConeCompMap` — **(G1)**: `ι ≫ Ψ` is the change of
  centre `C_ZX ⟶ C_YX`.
* `Stacks.Chow.isPullback_normalConeCompMap_normalConeZeroSection` — **(G2)**:
  `N' = N₁ ×_{C_YX} Y`; `Stacks.Chow.comap_normalConeZeroSectionIdeal_normalConeCompMap` — the
  same on ideals.
* `Stacks.Chow.conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeChangeOfCentreOver` — the
  change of centre on degree-one classes is the canonical map of Stacks 01R4.
* `Stacks.Chow.normalConeZeroSectionOver_comp_normalConeEmbedding` — `C_YX ⟶ N` carries the zero
  section of the normal cone to that of the vector bundle, for any virtual normal bundle.

## Implementation notes

The instance `AlgebraicGeometry.IsImmersion.comp` is erased in this file, so that
`IsImmersion (iZY ≫ iY)` is found through `IsClosedImmersion (iZY ≫ iY)`, as in the files the chart
computations come from. With two instance paths the normal cones `C_ZX` they produce are
definitionally but not syntactically equal, and unifying them unfolds the relative spectrum.

These are prerequisites of Stacks 0FEC and carry no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 0FEC](https://stacks.math.columbia.edu/tag/0FEC)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 0634](https://stacks.math.columbia.edu/tag/0634)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ReflexiveModules AlgebraicGeometry.Scheme.Modules
open Stacks.Immersion RingedSpaceModuleAdjunction Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.AffineAlgebraEquivalence Stacks.SymAlgSheaf Stacks.RelativeSpec.AlgebraSheaf

universe u

namespace Stacks.Chow

/- The immersion `Z ⟶ Y ⟶ X` is read as a closed immersion, as in the files this one builds on:
the instance `IsImmersion (iZY ≫ iY)` then comes from `IsClosedImmersion (iZY ≫ iY)`, and the
normal cones, charts and virtual normal bundles of the two files agree syntactically. -/
attribute [-instance] AlgebraicGeometry.IsImmersion.comp

section Charts

variable {X Y Z : Scheme.{u}} (iY : Y ⟶ X) [IsClosedImmersion iY] (iZY : Z ⟶ Y)
  [IsClosedImmersion iZY] (h : iY.ker ≤ (iZY ≫ iY).ker)

/-- The ring map underlying the identity of `X` on an affine open is the identity. -/
theorem affineBaseChangeMap_id (U : X.affineOpens) :
    affineBaseChangeMap (𝟙 X) (U := U) (U' := U) (fun _ hx => hx) = RingHom.id Γ(X, U.1) := by
  ext x
  simp only [affineBaseChangeMap, Scheme.Hom.appLE, Scheme.Hom.id_app]
  exact congrArg (fun k => CommRingCat.Hom.hom k x) (X.presheaf.map_id (op U.1))

/-- **The change of centre on the charts is the base-change comparison along the identity**:
the two ring maps `Γ(Y ∩ U, 𝒞_{Y/X,*}) ⟶ Γ(Z ∩ U, 𝒞_{Z/X,*})` built from `ℐ_Y(U) ⊆ ℐ_Z(U)` agree,
the square `Z ⟶ Y ⟶ X`, `Z ⟶ X ⟶ X` commuting. -/
theorem conormalSectionsChangeOfCentre_eq_baseChange (U : X.affineOpens) :
    conormalSectionsChangeOfCentre (iZY ≫ iY) iY h U =
      conormalSectionsBaseChange (𝟙 X) iY (iZY ≫ iY) iZY (Category.comp_id _)
        (U := U) (U' := U) (fun _ hx => hx) := by
  have key : ∀ (φ : Γ(X, U.1) →+* Γ(X, U.1)) (_ : φ = RingHom.id Γ(X, U.1))
      (h₁ : (iY.ker.ideal U).map (RingHom.id Γ(X, U.1)) ≤ (iZY ≫ iY).ker.ideal U)
      (h₂ : (iY.ker.ideal U).map φ ≤ (iZY ≫ iY).ker.ideal U),
      infinityChartFibreMap (RingHom.id Γ(X, U.1)) h₁ = infinityChartFibreMap φ h₂ := by
    rintro φ rfl h₁ h₂
    rfl
  unfold conormalSectionsChangeOfCentre conormalSectionsBaseChange
  rw [key _ (affineBaseChangeMap_id U) _
      (map_ideal_ker_le (𝟙 X) (fun _ hx => hx) iY (iZY ≫ iY) iZY (Category.comp_id _))]

/-- The pullback of the section `ΓSpecIso⁻¹ x` along `Spec.map f` is `ΓSpecIso⁻¹ (f x)`. -/
private theorem appLE_top_spec_map_ΓSpecIso_inv {A B : CommRingCat.{u}} (f : A ⟶ B) (x : A) :
    ((Spec.map f).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso A).inv.hom x) =
      (Scheme.ΓSpecIso B).inv.hom (f.hom x) := by
  change ((Spec.map f).appLE ⊤ (Spec.map f ⁻¹ᵁ ⊤) le_rfl).hom _ = _
  rw [Scheme.Hom.appLE_eq_app]
  exact (congrArg (fun φ => CommRingCat.Hom.hom φ x) (Scheme.ΓSpecIso_inv_naturality f)).symm

/-- **The change of centre on sections over the charts.** A section of the conormal algebra of
`Y` over `Y ∩ U`, viewed on `C_YX` over `U`, pulled back along `C_ZX ⟶ C_YX` and then to the chart
of `C_ZX` over `U`, is its image under the map of conormal algebras. -/
theorem normalConeChart_appLE_normalConeChangeOfCentreMap_appLE (U : X.affineOpens)
    (x : (Stacks.Conormal.conormalAlgebraSheaf iY).right.obj.obj (op (iY ⁻¹ᵁ U.1)))
    (O : (Stacks.Conormal.normalCone (iZY ≫ iY)).Opens)
    (h₁ : ⊤ ≤ normalConeChart (iZY ≫ iY) U ⁻¹ᵁ O)
    (h₂ : O ≤ normalConeChangeOfCentreMap (iZY ≫ iY) iY h ⁻¹ᵁ
      ((relativeSpecGluingData (Stacks.Conormal.conormalAlgebraSheaf iY)).toBase ⁻¹ᵁ
        (subschemeAffineOpen iY U).1)) :
    ((normalConeChart (iZY ≫ iY) U).appLE O ⊤ h₁).hom
        ((normalConeChangeOfCentreMap (iZY ≫ iY) iY h).appLE _ O h₂ |>.hom
          ((pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf iY)).inv.right.hom.app
            (op (iY ⁻¹ᵁ U.1)) x)) =
      (Scheme.ΓSpecIso _).inv.hom ((conormalSectionsBaseChange (𝟙 X) iY (iZY ≫ iY) iZY
        (Category.comp_id _) (U := U) (U' := U) (fun _ hx => hx)).hom x) := by
  rw [← conormalSectionsChangeOfCentre_eq_baseChange iY iZY h U]
  have hcomp : ∀ y, ((normalConeChart (iZY ≫ iY) U).appLE O ⊤ h₁).hom
      (((normalConeChangeOfCentreMap (iZY ≫ iY) iY h).appLE _ O h₂).hom y) =
      ((normalConeChart (iZY ≫ iY) U ≫ normalConeChangeOfCentreMap (iZY ≫ iY) iY h).appLE _ ⊤
        (by rw [Scheme.Hom.comp_preimage]
            exact h₁.trans ((normalConeChart (iZY ≫ iY) U).preimage_mono h₂))).hom y :=
    fun y => by
      rw [← Scheme.Hom.appLE_comp_appLE]
      rfl
  refine (hcomp _).trans ?_
  have key : ∀ (m : normalConeChartSource (iZY ≫ iY) U ⟶ Stacks.Conormal.normalCone iY)
      (_ : m = Spec.map (conormalSectionsChangeOfCentre (iZY ≫ iY) iY h U) ≫
        normalConeChart iY U)
      (e : ⊤ ≤ m ⁻¹ᵁ ((relativeSpecGluingData (Stacks.Conormal.conormalAlgebraSheaf iY)).toBase ⁻¹ᵁ
        (subschemeAffineOpen iY U).1)),
      (m.appLE _ ⊤ e).hom ((pushforwardAlgebraIso
          (Stacks.Conormal.conormalAlgebraSheaf iY)).inv.right.hom.app (op (iY ⁻¹ᵁ U.1)) x) =
        (Scheme.ΓSpecIso _).inv.hom
          ((conormalSectionsChangeOfCentre (iZY ≫ iY) iY h U).hom x) := by
    rintro m rfl e
    have h1 : (Spec.map (conormalSectionsChangeOfCentre (iZY ≫ iY) iY h U) ≫
        normalConeChart iY U).appLE _ ⊤ e =
        (normalConeChart iY U).appLE _ ⊤
          (by exact (le_ι_preimage
            (relativeSpecGluingData (Stacks.Conormal.conormalAlgebraSheaf iY))
            (subschemeAffineOpen iY U))) ≫
          (Spec.map (conormalSectionsChangeOfCentre (iZY ≫ iY) iY h U)).appLE ⊤ ⊤ le_top :=
      (Scheme.Hom.appLE_comp_appLE (Spec.map (conormalSectionsChangeOfCentre (iZY ≫ iY) iY h U))
        (normalConeChart iY U) _ ⊤ ⊤ (by exact (le_ι_preimage
          (relativeSpecGluingData (Stacks.Conormal.conormalAlgebraSheaf iY))
            (subschemeAffineOpen iY U))) le_top).symm
    rw [h1]
    have h2 := ι_appLE_pushforwardAlgebraIso_inv (Stacks.Conormal.conormalAlgebraSheaf iY)
      (subschemeAffineOpen iY U) x
    exact (congrArg _ h2).trans
      (appLE_top_spec_map_ΓSpecIso_inv (conormalSectionsChangeOfCentre (iZY ≫ iY) iY h U) x)
  exact key _ (specMap_conormalSectionsChangeOfCentre_normalConeChart (iZY ≫ iY) iY h U).symm _

/-- **Sections of the normal cone over the part lying over an affine open are determined on its
chart.** Two sections of `C_ZX` over an open `O` lying over the affine open `U` of `X` and
containing the image of the chart over `U` agree if they agree on that chart: every chart over a
smaller affine open factors through it. -/
theorem normalCone_sections_ext_of_chart {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (U : X.affineOpens) {O : (Stacks.Conormal.normalCone i).Opens}
    (hO : O ≤ normalConeToX i ⁻¹ᵁ U.1) (h₁ : ⊤ ≤ normalConeChart i U ⁻¹ᵁ O)
    {a b : Γ(Stacks.Conormal.normalCone i, O)}
    (h : ((normalConeChart i U).appLE O ⊤ h₁).hom a = ((normalConeChart i U).appLE O ⊤ h₁).hom b) :
    a = b := by
  have hrange : ∀ U' : X.affineOpens, U'.1 ≤ U.1 →
      Set.range (normalConeChart i U').base ⊆ Set.range (normalConeChart i U).base := by
    intro U' hU' x hx
    have h1 : x ∈ (normalConeChart i U').opensRange := hx
    rw [opensRange_normalConeChart] at h1
    have h2 : x ∈ (normalConeChart i U).opensRange := by
      rw [opensRange_normalConeChart]
      exact (normalConeToX i).preimage_mono hU' h1
    exact h2
  have hRO : normalConeToX i ⁻¹ᵁ U.1 ≤ O := by
    rw [← opensRange_normalConeChart]
    rintro _ ⟨y, rfl⟩
    exact h₁ (Set.mem_univ y)
  refine normalCone_sections_ext i U.1
    (fun U' hU' => ((normalConeToX i).preimage_mono hU').trans hRO) hO fun U' hU' => ?_
  let k := IsOpenImmersion.lift (normalConeChart i U) (normalConeChart i U') (hrange U' hU')
  have key : ∀ (m : normalConeChartSource i U' ⟶ Stacks.Conormal.normalCone i)
      (_ : m = k ≫ normalConeChart i U) (e : ⊤ ≤ m ⁻¹ᵁ O),
      (m.appLE O ⊤ e).hom a = (m.appLE O ⊤ e).hom b := by
    rintro m rfl e
    rw [← Scheme.Hom.appLE_comp_appLE k (normalConeChart i U) O ⊤ ⊤ h₁ le_top,
      CommRingCat.comp_apply, CommRingCat.comp_apply, h]
  exact key _ (IsOpenImmersion.lift_fac _ _ _).symm _

end Charts

section Comparison

variable {X Y Z : Scheme.{u}} (iY : Y ⟶ X) [IsClosedImmersion iY] (iZY : Z ⟶ Y)
  [IsClosedImmersion iZY] (h : iY.ker ≤ (iZY ≫ iY).ker)

/-- The morphism of normal cones `C_ZX ⟶ C_YX` of `Stacks.Chow.normalConeChangeOfCentreMap`, as a
morphism of schemes over `Y`. -/
abbrev normalConeChangeOfCentreOver :
    (Over.mk (Stacks.Conormal.normalConeToBase (iZY ≫ iY) ≫ iZY) : Over Y) ⟶
      Over.mk (Stacks.Conormal.normalConeToBase iY) :=
  Over.homMk (normalConeChangeOfCentreMap (iZY ≫ iY) iY h)
    (normalConeChangeOfCentreMap_toBase (iZY ≫ iY) iY h iZY rfl)

/-- The chart computation behind
`Stacks.Chow.conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeChangeOfCentreOver`: the
two sides agree on the chart of `C_ZX` over an affine open `U`. -/
theorem normalConeChart_appLE_pushforwardAlgebraMap_normalConeChangeOfCentreOver
    (U : X.affineOpens) (c : (Stacks.Conormal.conormalSheaf iY).val.obj (op (iY ⁻¹ᵁ U.1)))
    (h₁ : ⊤ ≤ normalConeChart (iZY ≫ iY) U ⁻¹ᵁ
      ((Stacks.Conormal.normalConeToBase (iZY ≫ iY) ≫ iZY) ⁻¹ᵁ (iY ⁻¹ᵁ U.1))) :
    ((normalConeChart (iZY ≫ iY) U).appLE _ ⊤ h₁).hom
        (((pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf iY)).inv.right.hom.app
            (op (iY ⁻¹ᵁ U.1)) ≫
          (pushforwardAlgebraMap (normalConeChangeOfCentreOver iY iZY h)).right.hom.app
            (op (iY ⁻¹ᵁ U.1))).hom
          ((conormalDegreeOneIncl iY).val.app (op (iY ⁻¹ᵁ U.1))
            ((Stacks.Conormal.conormalDegreeOneHom iY).val.app (op (iY ⁻¹ᵁ U.1)) c))) =
      ((normalConeChart (iZY ≫ iY) U).appLE _ ⊤ h₁).hom
        ((pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf (iZY ≫ iY))).inv.right.hom.app
          (op (iZY ⁻¹ᵁ (iY ⁻¹ᵁ U.1)))
          ((conormalDegreeOneIncl (iZY ≫ iY)).val.app (op (iZY ⁻¹ᵁ (iY ⁻¹ᵁ U.1)))
            ((Stacks.Conormal.conormalDegreeOneHom (iZY ≫ iY)).val.app
              (op (iZY ⁻¹ᵁ (iY ⁻¹ᵁ U.1)))
              (((modulePullbackPushforwardAdjunction iZY.toLRSHom.toShHom).homEquiv _ _
                (Stacks.Immersion.immersionConormalSheafMap (iZY ≫ iY) iY iZY (𝟙 X)
                  (Stacks.Immersion.toShHom_square (Category.comp_id _)))).val.app
                    (op (iY ⁻¹ᵁ U.1)) c)))) := by
  have hUU : U.1 ≤ (𝟙 X) ⁻¹ᵁ U.1 := fun _ hx => hx
  have hTle : (subschemeAffineOpen (iZY ≫ iY) U).1 ≤ iZY ⁻¹ᵁ (iY ⁻¹ᵁ U.1) :=
    Stacks.Immersion.preimage_le_preimage_of_square (Category.comp_id _) U.1 U.1 hUU
  have hA := pushforwardAlgebraMap_app (normalConeChangeOfCentreOver iY iZY h) (iY ⁻¹ᵁ U.1)
    (preimage_le_preimage_preimage _ _)
  have hL := normalConeChart_appLE_normalConeChangeOfCentreMap_appLE iY iZY h U
    ((conormalDegreeOneIncl iY).val.app (op (iY ⁻¹ᵁ U.1))
      ((Stacks.Conormal.conormalDegreeOneHom iY).val.app (op (iY ⁻¹ᵁ U.1)) c))
    ((Stacks.Conormal.normalConeToBase (iZY ≫ iY) ≫ iZY) ⁻¹ᵁ (iY ⁻¹ᵁ U.1)) h₁
    (preimage_le_preimage_preimage (normalConeChangeOfCentreOver iY iZY h) _)
  have hR := normalConeChart_appLE_pushforwardAlgebraIso_inv (iZY ≫ iY) U
    (iZY ⁻¹ᵁ (iY ⁻¹ᵁ U.1)) hTle
    ((conormalDegreeOneIncl (iZY ≫ iY)).val.app (op (iZY ⁻¹ᵁ (iY ⁻¹ᵁ U.1)))
      ((Stacks.Conormal.conormalDegreeOneHom (iZY ≫ iY)).val.app (op (iZY ⁻¹ᵁ (iY ⁻¹ᵁ U.1)))
        (((modulePullbackPushforwardAdjunction iZY.toLRSHom.toShHom).homEquiv _ _
          (Stacks.Immersion.immersionConormalSheafMap (iZY ≫ iY) iY iZY (𝟙 X)
            (Stacks.Immersion.toShHom_square (Category.comp_id _)))).val.app
              (op (iY ⁻¹ᵁ U.1)) c))) h₁
  have hC := conormalSectionsBaseChange_conormalDegreeOneHom' iY (iZY ≫ iY) iZY (𝟙 X)
    (Category.comp_id _) hUU c
  refine Eq.trans ?_ ((hL.trans (congrArg (Scheme.ΓSpecIso _).inv.hom hC)).trans hR.symm)
  exact congrArg ((normalConeChart (iZY ≫ iY) U).appLE _ ⊤ h₁).hom
    (congrArg (fun φ => CommRingCat.Hom.hom φ _) hA)

/-- `Stacks.Chow.normalConeChart_appLE_pushforwardAlgebraMap_normalConeChangeOfCentreOver`, with
the two sides written as morphisms of modules. -/
theorem normalConeChart_appLE_pushforwardAlgebraMap_normalConeChangeOfCentreOver'
    (U : X.affineOpens) (c : (Stacks.Conormal.conormalSheaf iY).val.obj (op (iY ⁻¹ᵁ U.1)))
    (h₁ : ⊤ ≤ normalConeChart (iZY ≫ iY) U ⁻¹ᵁ
      ((Stacks.Conormal.normalConeToBase (iZY ≫ iY) ≫ iZY) ⁻¹ᵁ (iY ⁻¹ᵁ U.1))) :
    ((normalConeChart (iZY ≫ iY) U).appLE _ ⊤ h₁).hom
        (((Stacks.Conormal.conormalDegreeOneHom iY ≫ conormalDegreeOneIncl iY ≫
          underlyingModuleMap (pushforwardAlgebraIso
            (Stacks.Conormal.conormalAlgebraSheaf iY)).inv ≫
          underlyingModuleMap (pushforwardAlgebraMap
            (normalConeChangeOfCentreOver iY iZY h))).val.app (op (iY ⁻¹ᵁ U.1))).hom c) =
      ((normalConeChart (iZY ≫ iY) U).appLE _ ⊤ h₁).hom
        ((((modulePullbackPushforwardAdjunction iZY.toLRSHom.toShHom).homEquiv _ _
          (Stacks.Immersion.immersionConormalSheafMap (iZY ≫ iY) iY iZY (𝟙 X)
            (Stacks.Immersion.toShHom_square (Category.comp_id _))) ≫
        (pushforward iZY).map (Stacks.Conormal.conormalDegreeOneHom (iZY ≫ iY) ≫
          conormalDegreeOneIncl (iZY ≫ iY) ≫ underlyingModuleMap (pushforwardAlgebraIso
            (Stacks.Conormal.conormalAlgebraSheaf (iZY ≫ iY))).inv)).val.app
              (op (iY ⁻¹ᵁ U.1))).hom c) :=
  normalConeChart_appLE_pushforwardAlgebraMap_normalConeChangeOfCentreOver iY iZY h U c h₁

/-- `Stacks.Chow.conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeChangeOfCentreOver` on
the sections over `Y ∩ U`, `U ⊆ X` an affine open. -/
theorem conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeChangeOfCentreOver_app
    (U : X.affineOpens) (c : (Stacks.Conormal.conormalSheaf iY).val.obj (op (iY ⁻¹ᵁ U.1))) :
    ((Stacks.Conormal.conormalDegreeOneHom iY ≫ conormalDegreeOneIncl iY ≫
          underlyingModuleMap (pushforwardAlgebraIso
            (Stacks.Conormal.conormalAlgebraSheaf iY)).inv ≫
          underlyingModuleMap (pushforwardAlgebraMap
            (normalConeChangeOfCentreOver iY iZY h))).val.app (op (iY ⁻¹ᵁ U.1))).hom c =
      (((modulePullbackPushforwardAdjunction iZY.toLRSHom.toShHom).homEquiv _ _
          (Stacks.Immersion.immersionConormalSheafMap (iZY ≫ iY) iY iZY (𝟙 X)
            (Stacks.Immersion.toShHom_square (Category.comp_id _))) ≫
        (pushforward iZY).map (Stacks.Conormal.conormalDegreeOneHom (iZY ≫ iY) ≫
          conormalDegreeOneIncl (iZY ≫ iY) ≫ underlyingModuleMap (pushforwardAlgebraIso
            (Stacks.Conormal.conormalAlgebraSheaf (iZY ≫ iY))).inv)).val.app
              (op (iY ⁻¹ᵁ U.1))).hom c :=
  normalCone_sections_ext_of_chart (iZY ≫ iY) U le_rfl
    (top_le_normalConeChart_preimage (iZY ≫ iY) U)
    (normalConeChart_appLE_pushforwardAlgebraMap_normalConeChangeOfCentreOver' iY iZY h U c _)

/-- The preimages of affine opens of `X` under a closed immersion form a basis of `Y`. -/
private theorem isBasis_preimage_affineOpens {X Y : Scheme.{u}} (iY : Y ⟶ X)
    [IsClosedImmersion iY] :
    TopologicalSpace.Opens.IsBasis (Set.range fun U : X.affineOpens => iY ⁻¹ᵁ U.1) := by
  rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
  intro O z hz
  obtain ⟨_, ⟨V, rfl⟩, hzV, hVO⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp (Stacks.Conormal.conormalChart_isBasis iY) hz
  exact ⟨_, ⟨V.1, rfl⟩, hzV, hVO⟩

/-- **The change of centre on degree-one classes of the conormal algebra.** On the
pushed-forward structure sheaves, `C_ZX ⟶ C_YX` carries the degree-one class of a local section of
`𝒞_{Y/X}` to the degree-one class of its image under the canonical map `𝒞_{Y/X}|_Z ⟶ 𝒞_{Z/X}` of
Stacks 01R4, transposed along `i^* ⊣ i_*`. -/
theorem conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeChangeOfCentreOver :
    Stacks.Conormal.conormalDegreeOneHom iY ≫ conormalDegreeOneIncl iY ≫
        underlyingModuleMap (pushforwardAlgebraIso
          (Stacks.Conormal.conormalAlgebraSheaf iY)).inv ≫
        underlyingModuleMap (pushforwardAlgebraMap (normalConeChangeOfCentreOver iY iZY h)) =
      (modulePullbackPushforwardAdjunction iZY.toLRSHom.toShHom).homEquiv _ _
          (Stacks.Immersion.immersionConormalSheafMap (iZY ≫ iY) iY iZY (𝟙 X)
            (Stacks.Immersion.toShHom_square (Category.comp_id _))) ≫
        (pushforward iZY).map (Stacks.Conormal.conormalDegreeOneHom (iZY ≫ iY) ≫
          conormalDegreeOneIncl (iZY ≫ iY) ≫ underlyingModuleMap (pushforwardAlgebraIso
            (Stacks.Conormal.conormalAlgebraSheaf (iZY ≫ iY))).inv) := by
  refine sheafOfModules_hom_ext_of_isBasis _ _ (isBasis_preimage_affineOpens iY) fun U c => ?_
  have h' := conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeChangeOfCentreOver_app
    iY iZY h U c
  refine Eq.trans ?_ (h'.trans ?_)
  · rfl
  · rfl

/-- The degree-one surjection of a virtual normal bundle, followed by the degree-one inclusion,
is its surjection `σ` followed by the degree-one comparison and inclusion. -/
private theorem conormalDegreeOneSurjection_comp_incl_comp_inv {X Z : Scheme.{u}} {i : Z ⟶ X}
    [IsClosedImmersion i] (N : VirtualNormalBundle i) :
    N.conormalDegreeOneSurjection ≫ conormalDegreeOneIncl i ≫
        underlyingModuleMap (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i)).inv =
      N.surjection ≫ (Stacks.Conormal.conormalDegreeOneHom i ≫ conormalDegreeOneIncl i ≫
        underlyingModuleMap (pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf i)).inv) :=
  by
  rw [VirtualNormalBundle.conormalDegreeOneSurjection, Stacks.Conormal.conormalDegreeOneIso_hom]
  exact Category.assoc _ _ _

/-- **The classifying map of `C_ZX ⟶ C_YX ⟶ N` over `Y`**, for a virtual normal bundle `𝒩` of
`Y ⟶ X`: the surjection `σ : 𝒩^∨ ⟶ 𝒞_{Y/X}` followed by the transpose of the canonical map
`𝒞_{Y/X}|_Z ⟶ 𝒞_{Z/X}` of Stacks 01R4 and the degree-one inclusion of the conormal algebra of
`Z`. -/
theorem vectorBundleClassifyingMap_normalConeChangeOfCentreOver_comp
    (𝒩 : VirtualNormalBundle iY) :
    vectorBundleClassifyingMap (dualSheaf 𝒩.bundle)
        (normalConeChangeOfCentreOver iY iZY h ≫ (normalConeToNormalBundleOver iY ≫
          vectorBundleMap Y 𝒩.conormalDegreeOneSurjection)) =
      𝒩.surjection ≫ (modulePullbackPushforwardAdjunction iZY.toLRSHom.toShHom).homEquiv _ _
          (Stacks.Immersion.immersionConormalSheafMap (iZY ≫ iY) iY iZY (𝟙 X)
            (Stacks.Immersion.toShHom_square (Category.comp_id _))) ≫
        (pushforward iZY).map (Stacks.Conormal.conormalDegreeOneHom (iZY ≫ iY) ≫
          conormalDegreeOneIncl (iZY ≫ iY) ≫ underlyingModuleMap (pushforwardAlgebraIso
            (Stacks.Conormal.conormalAlgebraSheaf (iZY ≫ iY))).inv) := by
  have R0 := vectorBundleClassifyingMap_comp (dualSheaf 𝒩.bundle)
    (normalConeChangeOfCentreOver iY iZY h)
    (normalConeToNormalBundleOver iY ≫ vectorBundleMap Y 𝒩.conormalDegreeOneSurjection)
  have R1 := vectorBundleClassifyingMap_normalConeEmbedding 𝒩
  refine R0.trans ((congrArg (· ≫ underlyingModuleMap
    (pushforwardAlgebraMap (normalConeChangeOfCentreOver iY iZY h))) R1).trans ?_)
  rw [conormalDegreeOneSurjection_comp_incl_comp_inv]
  exact (Category.assoc _ _ _).trans (congrArg (𝒩.surjection ≫ ·)
    (((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).trans
      (conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeChangeOfCentreOver iY iZY h)))

end Comparison

section Classifying

/-- The classifying map of `k ≫ 𝐕(f)`, from that of `k`. -/
private theorem vectorBundleClassifyingMap_comp_vectorBundleMap_of_eq {S : Scheme.{u}}
    {F G : SheafOfModules.{u} S.ringCatSheaf} [F.IsQuasicoherent] [G.IsQuasicoherent]
    (f : F ⟶ G) {T : Over S} (k : T ⟶ vectorBundleOver S (F := G))
    {c : G ⟶ underlyingModule (pushforwardAlgebra T.hom)}
    (hk : vectorBundleClassifyingMap G k = c) :
    vectorBundleClassifyingMap F (k ≫ vectorBundleMap S f) = f ≫ c :=
  (vectorBundleClassifyingMap_comp_vectorBundleMap F f k).trans (congrArg (f ≫ ·) hk)

/-- The classifying map of `(Over.map g).map m ≫ (𝐕(g^*M) ⟶ 𝐕(M))`, from that of `m`. -/
private theorem vectorBundleClassifyingMap_map_comp_vectorBundlePullbackProjection_of_eq
    {T S : Scheme.{u}} (g : T ⟶ S) (M : S.Modules) [M.IsQuasicoherent] {W : Over T}
    (m : W ⟶ vectorBundleOver T (F := (Scheme.Modules.pullback g).obj M))
    {c : (Scheme.Modules.pullback g).obj M ⟶ underlyingModule (pushforwardAlgebra W.hom)}
    (hm : vectorBundleClassifyingMap ((Scheme.Modules.pullback g).obj M) m = c) :
    vectorBundleClassifyingMap M ((Over.map g).map m ≫ vectorBundlePullbackProjection g M) =
      (pullbackPushforwardAdjunction g).unit.app M ≫ (pushforward g).map c :=
  (vectorBundleClassifyingMap_map_comp_vectorBundlePullbackProjection g M m).trans
    (congrArg (fun t => (pullbackPushforwardAdjunction g).unit.app M ≫ (pushforward g).map t) hm)


variable {X Y Z : Scheme.{u}} (iY : Y ⟶ X) [IsClosedImmersion iY] (iZY : Z ⟶ Y)
  [IsClosedImmersion iZY] (N₁ : VirtualNormalBundle (iZY ≫ iY))

/-- **The classifying map of `C_ZX ⟶ N₁ ⟶ V(ℰ|_Z) ⟶ V(ℰ)`**, as a morphism of schemes over `Y`,
for a quasi-coherent `ℰ` on `Y` with a map `σ_Y : ℰ ⟶ 𝒞_{Y/X}` and `a : ℰ|_Z ⟶ 𝒩₁^∨` compatible
with the surjection of `𝒩₁` and the canonical map `𝒞_{Y/X}|_Z ⟶ 𝒞_{Z/X}` of Stacks 01R4: it is
`σ_Y` followed by the transpose of that canonical map and the degree-one inclusion of the conormal
algebra of `Z`. -/
theorem vectorBundleClassifyingMap_map_comp_vectorBundlePullbackProjection_of_comp_surjection
    {E : Y.Modules} [E.IsQuasicoherent] (σY : E ⟶ conormalModule iY)
    (a : (Scheme.Modules.pullback iZY).obj E ⟶ dualSheaf N₁.bundle)
    (ha : a ≫ N₁.surjection = (Scheme.Modules.pullback iZY).map σY ≫
      immersionConormalSheafMap (iZY ≫ iY) iY iZY (𝟙 X) (toShHom_square (Category.comp_id _))) :
    vectorBundleClassifyingMap E
        ((Over.map iZY).map ((normalConeToNormalBundleOver (iZY ≫ iY) ≫
          vectorBundleMap Z N₁.conormalDegreeOneSurjection) ≫ vectorBundleMap Z a) ≫
          vectorBundlePullbackProjection iZY E) =
      σY ≫ (modulePullbackPushforwardAdjunction iZY.toLRSHom.toShHom).homEquiv _ _
          (immersionConormalSheafMap (iZY ≫ iY) iY iZY (𝟙 X)
            (toShHom_square (Category.comp_id _))) ≫
        (pushforward iZY).map (Stacks.Conormal.conormalDegreeOneHom (iZY ≫ iY) ≫
          conormalDegreeOneIncl (iZY ≫ iY) ≫ underlyingModuleMap (pushforwardAlgebraIso
            (Stacks.Conormal.conormalAlgebraSheaf (iZY ≫ iY))).inv) := by
  have e0 := conormalDegreeOneSurjection_comp_incl_comp_inv N₁
  have e1 : a ≫ N₁.conormalDegreeOneSurjection ≫ conormalDegreeOneIncl (iZY ≫ iY) ≫
      underlyingModuleMap (pushforwardAlgebraIso
        (Stacks.Conormal.conormalAlgebraSheaf (iZY ≫ iY))).inv =
      (modulePullback iZY.toLRSHom.toShHom).map σY ≫
        immersionConormalSheafMap (iZY ≫ iY) iY iZY (𝟙 X) (toShHom_square (Category.comp_id _)) ≫
          (Stacks.Conormal.conormalDegreeOneHom (iZY ≫ iY) ≫
            conormalDegreeOneIncl (iZY ≫ iY) ≫ underlyingModuleMap (pushforwardAlgebraIso
              (Stacks.Conormal.conormalAlgebraSheaf (iZY ≫ iY))).inv) :=
    (congrArg (a ≫ ·) e0).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (Stacks.Conormal.conormalDegreeOneHom (iZY ≫ iY) ≫
          conormalDegreeOneIncl (iZY ≫ iY) ≫ underlyingModuleMap (pushforwardAlgebraIso
            (Stacks.Conormal.conormalAlgebraSheaf (iZY ≫ iY))).inv)) ha).trans
        (Category.assoc _ _ _)))
  have s0 := vectorBundleClassifyingMap_comp_vectorBundleMap_of_eq a
    (normalConeToNormalBundleOver (iZY ≫ iY) ≫ vectorBundleMap Z N₁.conormalDegreeOneSurjection)
    (vectorBundleClassifyingMap_normalConeEmbedding N₁)
  have s1 := vectorBundleClassifyingMap_map_comp_vectorBundlePullbackProjection_of_eq iZY E
    ((normalConeToNormalBundleOver (iZY ≫ iY) ≫
      vectorBundleMap Z N₁.conormalDegreeOneSurjection) ≫ vectorBundleMap Z a) s0
  refine s1.trans ?_
  refine (pullbackPushforwardAdjunction_unit_comp_pushforward_map iZY _ _ _).trans ?_
  refine (congrArg ((modulePullbackPushforwardAdjunction iZY.toLRSHom.toShHom).homEquiv _ _)
    e1).trans ?_
  refine ((modulePullbackPushforwardAdjunction iZY.toLRSHom.toShHom).homEquiv_naturality_left
    _ _).trans ?_
  exact congrArg (σY ≫ ·)
    ((modulePullbackPushforwardAdjunction iZY.toLRSHom.toShHom).homEquiv_naturality_right _ _)

end Classifying

section ZeroSection

variable {X Y : Scheme.{u}} (iY : Y ⟶ X) [IsClosedImmersion iY]

/-- **Degree-one classes lie in the positive-degree ideal.** On the chart of `C_YX` over an
affine open `U`, the degree-one class of a section of `𝒞_{Y/X}` over `Y ∩ U` lies in the ideal
`Gr_I(A)₊` cutting out the zero section (`Stacks.Chow.normalConeChartZeroSectionIdeal`). -/
theorem conormalDegreeOneIncl_mem_normalConeChartZeroSectionIdeal (U : X.affineOpens)
    (c : (Stacks.Conormal.conormalSheaf iY).val.obj (op (iY ⁻¹ᵁ U.1))) :
    (conormalDegreeOneIncl iY).val.app (op (iY ⁻¹ᵁ U.1))
        ((Stacks.Conormal.conormalDegreeOneHom iY).val.app (op (iY ⁻¹ᵁ U.1)) c) ∈
      normalConeChartZeroSectionIdeal iY U := by
  obtain ⟨J, eW, heW⟩ := Stacks.Conormal.exists_affineModel iY U.1 U.2
  have hJ : Stacks.Conormal.chartIdeal iY U = J := by
    rw [Stacks.Conormal.chartIdeal, Scheme.Hom.app_eq_appLE]
    exact Stacks.Conormal.ker_appLE_eq_of_affineModel iY U.1 U.2 J eW heW
  subst hJ
  obtain ⟨a, ha⟩ := Ideal.toCotangent_surjective (Stacks.Conormal.chartIdeal iY U)
    ((Stacks.Conormal.affineConormalIsoCotangent iY U.1 U.2 _ eW heW).hom.hom c)
  have hc : c = (Stacks.Conormal.affineConormalIsoCotangent iY U.1 U.2 _ eW heW).inv.hom
      ((Stacks.Conormal.chartIdeal iY U).toCotangent a) := by
    have key : ∀ {R : Type u} [Ring R] {A B : ModuleCat.{u} R} (q : A ≅ B) (y : A),
        q.inv.hom (q.hom.hom y) = y := fun q y => congrArg (fun k => k.hom y) q.hom_inv_id
    rw [ha]
    exact (key (Stacks.Conormal.affineConormalIsoCotangent iY U.1 U.2 _ eW heW) c).symm
  subst hc
  rw [Stacks.Conormal.conormalDegreeOneHom_localMap iY U inferInstance eW heW a,
    conormalDegreeOneIncl_app]
  have ha' : a.1 ∈ iY.ker.ideal U := by rw [← chartIdeal_eq_ker_ideal]; exact a.2
  have hz := Stacks.Conormal.conormalAlgebraSheafSectionsEquiv_of_mk iY U inferInstance 1 a.1
    (by simpa only [pow_one] using a.2)
  let z : AssociatedGraded.gradedRing (iY.ker.ideal U) :=
    DirectSum.of (fun k => AssociatedGraded.piece (M := Γ(X, U.1)) (iY.ker.ideal U) k) 1
      (AssociatedGraded.mk (iY.ker.ideal U) 1 ⟨a.1, by simp⟩)
  have e1 := exceptionalChartSectionsEquiv_conormalEquiv iY U z
  simp only [z, AssociatedGraded.gradedRingMapOfRingHom_of, AssociatedGraded.pieceMapOfRingHom_mk,
    RingHom.id_apply] at e1
  have hmem :
      z ∈ (HomogeneousIdeal.irrelevant (AssociatedGraded.grading (iY.ker.ideal U))).toIdeal :=
    Stacks.ExternalGrading.of_mem_irrelevant one_ne_zero _
  have hy := Ideal.mem_map_of_mem (conormalGradedSectionsEquiv iY U) hmem
  change (conormalEquivInfinityChartFibre (iY.ker.ideal U)).trans
    (exceptionalChartSectionsEquiv iY U) z ∈ _ at hy
  rw [RingEquiv.trans_apply, e1, hz] at hy
  exact hy

/-- **The zero section kills the sections vanishing on the chart's vertex.** A section `x` of
`C_YX` over the part lying over an affine open `U` of `X` whose restriction to the chart
`Spec Gr_I(A)` lies in the positive-degree ideal pulls back to zero along the zero section
`o : Y ⟶ C_YX`: on the chart, `o` is cut out by that ideal. -/
theorem normalConeZeroSection_appLE_eq_zero (U : X.affineOpens)
    (x : Γ(Stacks.Conormal.normalCone iY, normalConeToX iY ⁻¹ᵁ U.1))
    {y : (conormalSituation iY).algebra.sections (subschemeAffineOpen iY U).1}
    (hy : y ∈ normalConeChartZeroSectionIdeal iY U)
    (hx : ((normalConeChart iY U).appLE _ ⊤ (top_le_normalConeChart_preimage iY U)).hom x =
      (Scheme.ΓSpecIso _).inv.hom y)
    (V : Y.Opens) (hle : V ≤ normalConeZeroSection iY ⁻¹ᵁ (normalConeToX iY ⁻¹ᵁ U.1)) :
    ((normalConeZeroSection iY).appLE _ V hle).hom x = 0 := by
  obtain ⟨q, H⟩ : ∃ q, IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (normalConeChartZeroSectionIdeal iY U)))) q
      (normalConeChart iY U) (normalConeZeroSectionIdeal iY).subschemeι :=
    ⟨_, isPullback_normalConeChart_normalConeZeroSectionIdeal iY U⟩
  have : IsOpenImmersion q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) H
      inferInstance
  have hq : q ≫ (normalConeZeroSectionIdeal iY).subschemeι =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (normalConeChartZeroSectionIdeal iY U))) ≫
        normalConeChart iY U := H.w.symm
  have hrange : q ''ᵁ ⊤ =
      (normalConeZeroSectionIdeal iY).subschemeι ⁻¹ᵁ (normalConeToX iY ⁻¹ᵁ U.1) := by
    rw [Scheme.Hom.image_top_eq_opensRange, Proj.opensRange_eq_preimage_of_isPullback H,
      opensRange_normalConeChart]
  have e₁ : q ''ᵁ ⊤ ≤
      (normalConeZeroSectionIdeal iY).subschemeι ⁻¹ᵁ (normalConeToX iY ⁻¹ᵁ U.1) := hrange.le
  have e₂ : V ≤ inv ((normalConeZeroSectionIdeal iY).subschemeι ≫
      Stacks.Conormal.normalConeToBase iY) ⁻¹ᵁ (q ''ᵁ ⊤) := by
    rw [hrange, ← Scheme.Hom.comp_preimage]
    exact hle
  have hsplit : (normalConeZeroSection iY).appLE (normalConeToX iY ⁻¹ᵁ U.1) V hle =
      (normalConeZeroSectionIdeal iY).subschemeι.appLE (normalConeToX iY ⁻¹ᵁ U.1) (q ''ᵁ ⊤) e₁ ≫
        (inv ((normalConeZeroSectionIdeal iY).subschemeι ≫
          Stacks.Conormal.normalConeToBase iY)).appLE (q ''ᵁ ⊤) V e₂ :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have hinj : Function.Injective
      (q.appLE (q ''ᵁ ⊤) ⊤ (Scheme.Hom.preimage_image_eq q ⊤).ge).hom := by
    rw [← Scheme.Hom.appIso_hom']
    exact (ConcreteCategory.bijective_of_isIso (q.appIso ⊤).hom).1
  have e₃ : ⊤ ≤ (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (normalConeChartZeroSectionIdeal iY U))) ≫ normalConeChart iY U) ⁻¹ᵁ
        (normalConeToX iY ⁻¹ᵁ U.1) :=
    fun _ _ => top_le_normalConeChart_preimage iY U (Set.mem_univ _)
  have hc :
      (normalConeZeroSectionIdeal iY).subschemeι.appLE (normalConeToX iY ⁻¹ᵁ U.1) (q ''ᵁ ⊤) e₁ ≫
      q.appLE (q ''ᵁ ⊤) ⊤ (Scheme.Hom.preimage_image_eq q ⊤).ge =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (normalConeChartZeroSectionIdeal iY U))) ≫
        normalConeChart iY U).appLE (normalConeToX iY ⁻¹ᵁ U.1) ⊤ e₃ := by
    have key : ∀ (m : Spec (CommRingCat.of ((conormalSituation iY).algebra.sections
          (subschemeAffineOpen iY U).1 ⧸ normalConeChartZeroSectionIdeal iY U)) ⟶
          Stacks.Conormal.normalCone iY)
        (_ : m = Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (normalConeChartZeroSectionIdeal iY U))) ≫ normalConeChart iY U)
        (e : ⊤ ≤ m ⁻¹ᵁ (normalConeToX iY ⁻¹ᵁ U.1)),
        m.appLE (normalConeToX iY ⁻¹ᵁ U.1) ⊤ e =
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
            (normalConeChartZeroSectionIdeal iY U))) ≫ normalConeChart iY U).appLE
            (normalConeToX iY ⁻¹ᵁ U.1) ⊤ e₃ := by
      rintro m rfl e
      rfl
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).trans (key _ hq _)
  have h1 : (Spec.map (CommRingCat.ofHom
      (Ideal.Quotient.mk (normalConeChartZeroSectionIdeal iY U))) ≫
        normalConeChart iY U).appLE (normalConeToX iY ⁻¹ᵁ U.1) ⊤ e₃ =
      (normalConeChart iY U).appLE (normalConeToX iY ⁻¹ᵁ U.1) ⊤
          (top_le_normalConeChart_preimage iY U) ≫
        (Spec.map (CommRingCat.ofHom
          (Ideal.Quotient.mk (normalConeChartZeroSectionIdeal iY U)))).appLE ⊤ ⊤ le_top :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h3 := appLE_top_spec_map_ΓSpecIso_inv (CommRingCat.ofHom
    (Ideal.Quotient.mk (normalConeChartZeroSectionIdeal iY U))) y
  have hs : ((normalConeZeroSectionIdeal iY).subschemeι.appLE (normalConeToX iY ⁻¹ᵁ U.1)
      (q ''ᵁ ⊤) e₁).hom x = 0 := by
    apply hinj
    refine (CommRingCat.comp_apply _ _ x).symm.trans ?_
    refine (congrArg (fun φ => CommRingCat.Hom.hom φ x) (hc.trans h1)).trans ?_
    refine (CommRingCat.comp_apply _ _ x).trans ?_
    refine (congrArg _ hx).trans ?_
    refine h3.trans ?_
    refine (congrArg _ ((Ideal.Quotient.eq_zero_iff_mem
      (I := normalConeChartZeroSectionIdeal iY U)).2 hy)).trans ?_
    exact (map_zero _).trans (map_zero _).symm
  exact (congrArg (fun φ => CommRingCat.Hom.hom φ x) hsplit).trans
    ((CommRingCat.comp_apply _ _ x).trans ((congrArg _ hs).trans (map_zero _)))

/-- The zero section `o : Y ⟶ C_YX`, as a morphism of schemes over `Y`. -/
abbrev normalConeZeroSectionOver :
    (Over.mk (𝟙 Y) : Over Y) ⟶ Over.mk (Stacks.Conormal.normalConeToBase iY) :=
  Over.homMk (normalConeZeroSection iY) (normalConeZeroSection_toBase iY)

/-- **The zero section kills degree-one classes**, on the sections over `Y ∩ U`, `U ⊆ X` an affine
open: the degree-one class of a section of `𝒞_{Y/X}`, pulled back along `o : Y ⟶ C_YX`, is zero. -/
theorem conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeZeroSectionOver_app
    (U : X.affineOpens) (c : (Stacks.Conormal.conormalSheaf iY).val.obj (op (iY ⁻¹ᵁ U.1))) :
    ((pushforwardAlgebraMap (normalConeZeroSectionOver iY)).right.hom.app (op (iY ⁻¹ᵁ U.1))).hom
      ((pushforwardAlgebraIso (Stacks.Conormal.conormalAlgebraSheaf iY)).inv.right.hom.app
        (op (iY ⁻¹ᵁ U.1)) ((conormalDegreeOneIncl iY).val.app (op (iY ⁻¹ᵁ U.1))
          ((Stacks.Conormal.conormalDegreeOneHom iY).val.app (op (iY ⁻¹ᵁ U.1)) c))) = 0 := by
  have hA := pushforwardAlgebraMap_app (normalConeZeroSectionOver iY) (iY ⁻¹ᵁ U.1)
    (preimage_le_preimage_preimage _ _)
  have hres : ((Stacks.Conormal.conormalAlgebraSheaf iY).right.obj.map
      (homOfLE (le_refl (iY ⁻¹ᵁ U.1))).op).hom
      ((conormalDegreeOneIncl iY).val.app (op (iY ⁻¹ᵁ U.1))
        ((Stacks.Conormal.conormalDegreeOneHom iY).val.app (op (iY ⁻¹ᵁ U.1)) c)) =
      (conormalDegreeOneIncl iY).val.app (op (iY ⁻¹ᵁ U.1))
        ((Stacks.Conormal.conormalDegreeOneHom iY).val.app (op (iY ⁻¹ᵁ U.1)) c) :=
    congrArg (fun φ => CommRingCat.Hom.hom φ _)
      ((Stacks.Conormal.conormalAlgebraSheaf iY).right.obj.map_id (op (iY ⁻¹ᵁ U.1)))
  have hx := (normalConeChart_appLE_pushforwardAlgebraIso_inv iY U (iY ⁻¹ᵁ U.1) le_rfl
    ((conormalDegreeOneIncl iY).val.app (op (iY ⁻¹ᵁ U.1))
      ((Stacks.Conormal.conormalDegreeOneHom iY).val.app (op (iY ⁻¹ᵁ U.1)) c))
    (top_le_normalConeChart_preimage iY U)).trans
    (congrArg (Scheme.ΓSpecIso _).inv.hom hres)
  refine (congrArg (fun φ => CommRingCat.Hom.hom φ _) hA).trans ?_
  exact normalConeZeroSection_appLE_eq_zero iY U _
    (conormalDegreeOneIncl_mem_normalConeChartZeroSectionIdeal iY U c) hx _ _

/-- **The zero section of the normal cone is the zero section of the vector bundle.** For a
virtual normal bundle `𝒩` of `Y ⟶ X`, the zero section `o : Y ⟶ C_YX` followed by the canonical
closed immersion `ι : C_YX ⟶ N` is the zero section of `N = 𝐕(𝒩^∨)`: its classifying map
`𝒩^∨ ⟶ 𝒞_{Y/X} ⟶ 𝒞_{Y/X,*} ⟶ o_* 𝒪_Y` kills the degree-one classes. -/
theorem normalConeZeroSectionOver_comp_normalConeEmbedding (𝒩 : VirtualNormalBundle iY) :
    normalConeZeroSectionOver iY ≫ (normalConeToNormalBundleOver iY ≫
        vectorBundleMap Y 𝒩.conormalDegreeOneSurjection) =
      vectorBundleLiftZeroOver (dualSheaf 𝒩.bundle) := by
  apply vectorBundle_hom_ext
  refine (vectorBundleClassifyingMap_comp _ _ _).trans ?_
  refine (congrArg (· ≫ underlyingModuleMap (pushforwardAlgebraMap
    (normalConeZeroSectionOver iY))) (vectorBundleClassifyingMap_normalConeEmbedding 𝒩)).trans ?_
  refine Eq.trans ?_ (vectorBundleClassifyingMap_vectorBundleLiftZeroOver _).symm
  rw [conormalDegreeOneSurjection_comp_incl_comp_inv]
  refine sheafOfModules_hom_ext_of_isBasis _ _ (isBasis_preimage_affineOpens iY) fun U s => ?_
  have key := conormalDegreeOneIncl_comp_pushforwardAlgebraMap_normalConeZeroSectionOver_app iY U
    ((𝒩.surjection.val.app (op (iY ⁻¹ᵁ U.1))).hom s)
  refine Eq.trans ?_ (key.trans ?_)
  · rfl
  · rfl

end ZeroSection

section Map

variable {X Y Z : Scheme.{u}} (iY : Y ⟶ X) [IsClosedImmersion iY] [IsLocallyNoetherian Y]
  (hreg : IsRegularImmersion iY) (iZY : Z ⟶ Y) [IsClosedImmersion iZY]
  (N₁ : VirtualNormalBundle (iZY ≫ iY))
  (a : (Scheme.Modules.pullback iZY).obj (dualSheaf (dualSheaf (conormalModule iY))) ⟶
    dualSheaf N₁.bundle)

include hreg in
/-- The dual `𝒞_{Y/X}^∨∨` of the normal bundle of a regular immersion is quasi-coherent. -/
theorem isQuasicoherent_dualSheaf_dualSheaf_conormalModule :
    (dualSheaf (dualSheaf (conormalModule iY))).IsQuasicoherent :=
  (VirtualNormalBundle.ofIsRegularImmersion iY hreg).isQuasicoherent_dualSheaf

/-- **The normal cone of a regular immersion is its normal bundle**, as an isomorphism
`C_YX ≅ 𝐕(𝒞_{Y/X}^∨∨)`: the closed immersion `ι` of the normal bundle
`Stacks.Chow.VirtualNormalBundle.ofIsRegularImmersion`, an isomorphism by
`Stacks.Chow.VirtualNormalBundle.isIso_normalConeEmbedding_ofIsRegularImmersion`. -/
def regularNormalConeIso :
    Stacks.Conormal.normalCone iY ≅ (VirtualNormalBundle.ofIsRegularImmersion iY hreg).totalSpace :=
  @asIso _ _ _ _ (VirtualNormalBundle.ofIsRegularImmersion iY hreg).normalConeEmbedding
    (VirtualNormalBundle.isIso_normalConeEmbedding_ofIsRegularImmersion hreg)

/-- The isomorphism `C_YX ≅ 𝐕(𝒞_{Y/X}^∨∨)` is the closed immersion `ι`. -/
@[simp]
theorem regularNormalConeIso_hom :
    (regularNormalConeIso iY hreg).hom =
      (VirtualNormalBundle.ofIsRegularImmersion iY hreg).normalConeEmbedding :=
  rfl

/-- **The morphism `Ψ : N₁ ⟶ C_YX`**: the morphism of vector bundles `N₁ ⟶ 𝐕(𝒞_{Y/X}^∨∨|_Z)` of
`a`, the projection `𝐕(𝒞_{Y/X}^∨∨|_Z) = 𝐕(𝒞_{Y/X}^∨∨) ×_Y Z ⟶ 𝐕(𝒞_{Y/X}^∨∨)`, and the inverse of
`C_YX ≅ 𝐕(𝒞_{Y/X}^∨∨)`. -/
def normalConeCompMap : N₁.totalSpace ⟶ Stacks.Conormal.normalCone iY :=
  haveI := isQuasicoherent_dualSheaf_dualSheaf_conormalModule iY hreg
  (vectorBundleMap Z a).left ≫
    (vectorBundlePullbackProjection iZY (dualSheaf (dualSheaf (conormalModule iY)))).left ≫
      (regularNormalConeIso iY hreg).inv

include hreg in
/-- **`Ψ` lies over `Z ⟶ Y`.** -/
@[reassoc]
theorem normalConeCompMap_toBase :
    normalConeCompMap iY hreg iZY N₁ a ≫ Stacks.Conormal.normalConeToBase iY =
      N₁.projection ≫ iZY := by
  have := isQuasicoherent_dualSheaf_dualSheaf_conormalModule iY hreg
  have h1 : (regularNormalConeIso iY hreg).inv ≫ Stacks.Conormal.normalConeToBase iY =
      (VirtualNormalBundle.ofIsRegularImmersion iY hreg).projection := by
    rw [Iso.inv_comp_eq, regularNormalConeIso_hom,
      VirtualNormalBundle.normalConeEmbedding_projection]
  have h2 := Over.w (vectorBundlePullbackProjection iZY (dualSheaf (dualSheaf (conormalModule iY))))
  have h3 := vectorBundleMap_left_comp Z a
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) h1))).trans ?_)
  change _ ≫ _ ≫ vectorBundleToBase Y _ = vectorBundleToBase Z _ ≫ iZY
  refine (congrArg (_ ≫ ·) h2).trans ?_
  change _ ≫ vectorBundleToBase Z _ ≫ iZY = _
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ iZY) h3)

include hreg in
/-- **Stacks 0FEC, G1: `Ψ` restricts to the change of centre on the normal cone.** The canonical
closed immersion `ι : C_ZX ⟶ N₁` followed by `Ψ` is the morphism of normal cones `C_ZX ⟶ C_YX`
induced by `ℐ_Y ⊆ ℐ_Z` (`Stacks.Chow.normalConeChangeOfCentreMap`). -/
theorem normalConeEmbedding_comp_normalConeCompMap
    (ha : a ≫ N₁.surjection =
      (Scheme.Modules.pullback iZY).map (regularNormalSurjection iY hreg) ≫
        immersionConormalSheafMap (iZY ≫ iY) iY iZY (𝟙 X) (toShHom_square (Category.comp_id _)))
    (h : iY.ker ≤ (iZY ≫ iY).ker) :
    N₁.normalConeEmbedding ≫ normalConeCompMap iY hreg iZY N₁ a =
      normalConeChangeOfCentreMap (iZY ≫ iY) iY h := by
  have := isQuasicoherent_dualSheaf_dualSheaf_conormalModule iY hreg
  have L := vectorBundleClassifyingMap_map_comp_vectorBundlePullbackProjection_of_comp_surjection
    iY iZY N₁ (E := dualSheaf (VirtualNormalBundle.ofIsRegularImmersion iY hreg).bundle)
    (VirtualNormalBundle.ofIsRegularImmersion iY hreg).surjection a ha
  have R := vectorBundleClassifyingMap_normalConeChangeOfCentreOver_comp iY iZY h
    (VirtualNormalBundle.ofIsRegularImmersion iY hreg)
  have H := congrArg Over.Hom.left (vectorBundle_hom_ext _ (L.trans R.symm))
  have H' : (Stacks.Conormal.normalConeToNormalBundle (iZY ≫ iY) ≫
      (vectorBundleMap Z N₁.conormalDegreeOneSurjection).left) ≫ (vectorBundleMap Z a).left ≫
        (vectorBundlePullbackProjection iZY
          (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion iY hreg).bundle)).left =
      normalConeChangeOfCentreMap (iZY ≫ iY) iY h ≫
        Stacks.Conormal.normalConeToNormalBundle iY ≫ (vectorBundleMap Y
          (VirtualNormalBundle.ofIsRegularImmersion iY hreg).conormalDegreeOneSurjection).left :=
    (Category.assoc _ _ _).symm.trans H
  have e : ((vectorBundleMap Z a).left ≫ (vectorBundlePullbackProjection iZY
      (dualSheaf (dualSheaf (conormalModule iY)))).left ≫ (regularNormalConeIso iY hreg).inv) ≫
        (regularNormalConeIso iY hreg).hom =
      (vectorBundleMap Z a).left ≫ (vectorBundlePullbackProjection iZY
        (dualSheaf (dualSheaf (conormalModule iY)))).left :=
    (Category.assoc _ _ _).trans (congrArg ((vectorBundleMap Z a).left ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.inv_hom_id _)).trans
        (Category.comp_id _))))
  rw [← cancel_mono (regularNormalConeIso iY hreg).hom, normalConeCompMap]
  exact (Category.assoc _ _ _).trans ((congrArg (N₁.normalConeEmbedding ≫ ·) e).trans H')

include hreg in
/-- `Ψ` is the composite `N₁ ⟶ 𝐕(𝒞_{Y/X}^∨∨|_Z) ⟶ 𝐕(𝒞_{Y/X}^∨∨) ≅ C_YX` and the zero section of
`C_YX` is that of `𝐕(𝒞_{Y/X}^∨∨)`
(`Stacks.Chow.normalConeZeroSectionOver_comp_normalConeEmbedding`): read through
`C_YX ≅ 𝐕(𝒞_{Y/X}^∨∨)`. -/
theorem normalConeZeroSection_comp_regularNormalConeIso_hom :
    normalConeZeroSection iY ≫ (regularNormalConeIso iY hreg).hom =
      vectorBundleLiftZero
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion iY hreg).bundle) := by
  have H : normalConeZeroSection iY ≫ Stacks.Conormal.normalConeToNormalBundle iY ≫
      (vectorBundleMap Y
        (VirtualNormalBundle.ofIsRegularImmersion iY hreg).conormalDegreeOneSurjection).left =
      vectorBundleLiftZero
        (dualSheaf (VirtualNormalBundle.ofIsRegularImmersion iY hreg).bundle) :=
    congrArg Over.Hom.left (normalConeZeroSectionOver_comp_normalConeEmbedding iY
      (VirtualNormalBundle.ofIsRegularImmersion iY hreg))
  rw [regularNormalConeIso_hom]
  exact H

include hreg in
/-- **Stacks 0FEC, G2: `N' = Ψ⁻¹(0)`.** For a virtual normal bundle `𝒩'` of `Z ⟶ Y` and
`b : 𝒩₁^∨ ⟶ (𝒩')^∨` such that `0 ⟶ 𝒞_{Y/X}^∨∨|_Z ⟶ 𝒩₁^∨ ⟶ (𝒩')^∨ ⟶ 0` (by `a` and `b`) is short
exact, the closed immersion `N' ⟶ N₁` of `b` is the base change of the zero section
`o : Y ⟶ C_YX` along `Ψ : N₁ ⟶ C_YX`: `N' = N₁ ×_{Ψ, C_YX, o} Y`. -/
theorem isPullback_normalConeCompMap_normalConeZeroSection {N' : VirtualNormalBundle iZY}
    (b : dualSheaf N₁.bundle ⟶ dualSheaf N'.bundle) (hab : IsShortExactSequenceOfModules a b) :
    IsPullback (vectorBundleMap Z b).left (N'.projection ≫ iZY)
      (normalConeCompMap iY hreg iZY N₁ a) (normalConeZeroSection iY) := by
  have := isQuasicoherent_dualSheaf_dualSheaf_conormalModule iY hreg
  obtain ⟨w, hS⟩ := hab
  have sq1 := isPullback_vectorBundleMap_of_shortExact a b w hS
  have sq2 := isPullback_vectorBundleLiftZero_vectorBundlePullbackProjection iZY
    (dualSheaf (dualSheaf (conormalModule iY)))
  have h0 := normalConeZeroSection_comp_regularNormalConeIso_hom iY hreg
  have hg : vectorBundleLiftZero (dualSheaf (dualSheaf (conormalModule iY))) ≫
      (regularNormalConeIso iY hreg).inv = 𝟙 Y ≫ normalConeZeroSection iY :=
    (congrArg (· ≫ (regularNormalConeIso iY hreg).inv) h0).symm.trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Iso.hom_inv_id _)).trans
        ((Category.comp_id _).trans (Category.id_comp _).symm)))
  have sq := (sq1.paste_vert sq2).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (regularNormalConeIso iY hreg).symm (fst' := (vectorBundleMap Z b).left)
    (snd' := N'.projection ≫ iZY) (f' := normalConeCompMap iY hreg iZY N₁ a)
    (g' := normalConeZeroSection iY) (by simp) (by simp; rfl)
    ((Category.assoc _ _ _).trans (Category.id_comp _).symm) hg
  exact sq
include hreg in
/-- The square of `Stacks.Chow.isPullback_normalConeCompMap_normalConeZeroSection` commutes:
`N' ⟶ N₁ ⟶ C_YX` factors through the zero section. -/
theorem vectorBundleMap_left_comp_normalConeCompMap {N' : VirtualNormalBundle iZY}
    (b : dualSheaf N₁.bundle ⟶ dualSheaf N'.bundle) (hab : IsShortExactSequenceOfModules a b) :
    (vectorBundleMap Z b).left ≫ normalConeCompMap iY hreg iZY N₁ a =
      N'.projection ≫ iZY ≫ normalConeZeroSection iY :=
  ((isPullback_normalConeCompMap_normalConeZeroSection iY hreg iZY N₁ a b hab).w).trans
    (Category.assoc _ _ _)

include hreg in
/-- **Stacks 0FEC, G2, on ideals.** The inverse image along `Ψ : N₁ ⟶ C_YX` of the ideal `D₀` of
the zero section of `C_YX` is the ideal of the closed immersion `N' ⟶ N₁` of `b`. -/
theorem comap_normalConeZeroSectionIdeal_normalConeCompMap {N' : VirtualNormalBundle iZY}
    (b : dualSheaf N₁.bundle ⟶ dualSheaf N'.bundle) (hab : IsShortExactSequenceOfModules a b) :
    (normalConeZeroSectionIdeal iY).comap (normalConeCompMap iY hreg iZY N₁ a) =
      (vectorBundleMap Z b).left.ker := by
  rw [ker_eq_comap_ker_of_isPullback
    (isPullback_normalConeCompMap_normalConeZeroSection iY hreg iZY N₁ a b hab),
    ker_normalConeZeroSection]
  rfl

end Map

end Stacks.Chow

end
