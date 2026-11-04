module

public import StacksFrontier.AlgebraicGeometry.RelativeSpec.Glueing
public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSpecRepresentability.Basic

/-!
# The glued relative spectrum represents the relative spectrum functor

Let `S` be a scheme and let `A` be a quasi-coherent sheaf of commutative `𝒪_S`-algebras. The
functor sending a test scheme `T` to the pairs `(f : T ⟶ S, φ : A ⟶ f_* 𝒪_T)` is represented
by the scheme `π : X ⟶ S` obtained by gluing the affine spectra `Spec A(U)`, the universal
element being `(π, A ⟶ π_* 𝒪_X)`. In particular the functor is representable, and the glued
relative spectrum is canonically isomorphic over `S` to any scheme representing it.

## Main definitions

* `Stacks.RelativeSpec.universalAlgebraMap` is the universal map `A ⟶ π_* 𝒪_X`.
* `Stacks.RelativeSpec.universalRelativeSpecPair` is the universal element of the functor.
* `Stacks.RelativeSpec.relativeSpecRepresentableBy` is the representing data.
* `Stacks.RelativeSpec.gluedSpectrumIso` is the comparison with any representing scheme.

## Main results

* `Stacks.RelativeSpec.relativeSpecFunctor_isRepresentable`: the functor is representable.
* `Stacks.RelativeSpec.gluedSpectrumIso_hom_toBase` and
  `Stacks.RelativeSpec.gluedSpectrumIso_inv_toBase`: the comparison is an isomorphism over `S`.
* `Stacks.RelativeSpec.universalAlgebraMap_app_chartAppLE`: on an affine open `U` of the base,
  the universal map is the canonical identification of `A(U)` with the sections of `𝒪_X` over
  `π⁻¹(U)`; `Stacks.RelativeSpec.isIso_universalAlgebraMap_app` records that it is therefore an
  isomorphism there.
* `Stacks.RelativeSpec.toBase_app`: the sections of `π` over an open of the base factor as the
  structure morphism of `A` followed by the universal map.

## Implementation notes

The universal map is taken to be the inverse of
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`, the isomorphism `π_* 𝒪_X ≅ A` whose
component over an affine open `U` of the base is the identification of the sections of `𝒪_X`
over `π⁻¹(U)` with `A(U)`; this makes the chartwise description of the universal map immediate.

A pair `(f, φ)` over `T` is sent to the morphism `T ⟶ X` glued from the morphisms
`f⁻¹(U) ⟶ Spec A(U) ⟶ X` attached to the components of `φ` on the affine opens `U` of `S`,
using `AlgebraicGeometry.Scheme.glueOverAffinePreimages`. That this is inverse to pulling back
the universal element is checked on those preimages, where everything is a statement about
morphisms into an affine scheme and hence about ring maps.

## References

* [Stacks Project, Tag 01LU](https://stacks.math.columbia.edu/tag/01LU)
* [Stacks Project, Tag 01LV](https://stacks.math.columbia.edu/tag/01LV)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AffineAlgebraEquivalence

universe u

namespace Stacks.RelativeSpec

/-- The canonical map from the sections of a scheme over an open to the global sections of the
corresponding open subscheme is the inverse of `AlgebraicGeometry.Scheme.Opens.topIso`. -/
theorem ιTopIso_eq_topIso_inv {X : Scheme.{u}} (W : X.Opens) : ιTopIso W = W.topIso.inv :=
  (Iso.comp_hom_eq_id W.topIso).mp (ιTopIso_comp_topIso_hom W)

/-- The canonical identification of the global sections of an open subscheme with the sections
of the ambient scheme over that open. -/
theorem ι_appLE_self {X : Scheme.{u}} (W : X.Opens) :
    W.ι.appLE W ⊤ W.ι_preimage_self.ge = W.topIso.inv :=
  ιTopIso_eq_topIso_inv W

/-- The global sections of the composite of `Z.toSpecΓ` with the spectrum of a ring map
`u : R ⟶ Γ(X, Z)`, read through `Scheme.ΓSpecIso`, are `u` followed by `Z.topIso.inv`. -/
private theorem inv_comp_toSpecΓ_comp_specMap_appTop {X : Scheme.{u}} (Z : X.Opens)
    {R : CommRingCat.{u}} (u : R ⟶ Γ(X, Z)) :
    (Scheme.ΓSpecIso R).inv ≫ (Z.toSpecΓ ≫ Spec.map u).appTop = u ≫ Z.topIso.inv := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
    Category.assoc, Scheme.Opens.toSpecΓ_appTop, Iso.inv_hom_id_assoc]

/-- A morphism from an open subscheme `Z` of `X` into the spectrum of a ring `R` is the one
attached to a ring map `R ⟶ Γ(X, Z)` precisely when that ring map is the one it induces on
global sections. -/
theorem toSpecΓ_specMap_eq {X : Scheme.{u}} (Z : X.Opens) {R : CommRingCat.{u}}
    (u : R ⟶ Γ(X, Z)) (g : Z.toScheme ⟶ Spec R)
    (hg : u ≫ Z.topIso.inv = (Scheme.ΓSpecIso R).inv ≫ g.appTop) :
    Z.toSpecΓ ≫ Spec.map u = g := by
  apply ext_to_Spec
  exact (inv_comp_toSpecΓ_comp_specMap_appTop Z u).trans hg

/-- The sections of a chart, read through the identification of the chart with the open
subscheme `π⁻¹(U)`. -/
theorem GluedSpectrum.chartAppLE_eq {s : RelativeSpecSituation.{u}} (X : GluedSpectrum s)
    (U : s.base.affineOpens) :
    X.chartAppLE U = (X.toBase ⁻¹ᵁ U.1).topIso.inv ≫ (X.chartIsoPreimage U).hom.appTop := by
  have h := appLE_congr_hom (X.chartIsoPreimage_hom_ι U) (le_preimage_of_comp_ι _)
    (X.chart_preimage U).ge
  rw [show X.chartAppLE U = _ from h.symm, appLE_comp_ι, ιTopIso_eq_topIso_inv]

variable (s : RelativeSpecSituation.{u})

/-! ### The universal algebra map -/

/-- **Stacks Project, Tag 01LX(3), in the form used here.** The universal map `A ⟶ π_* 𝒪_X`
from a quasi-coherent algebra to the pushforward of the structure sheaf of its relative
spectrum. -/
noncomputable def universalAlgebraMap :
    Under.mk s.algebra.hom.hom ⟶ Under.mk (gluedSpectrum s).toBase.c :=
  Under.homMk ((pushforwardAlgebraIso s.algebra).inv.right.hom) <| by
    have h : s.algebra.hom ≫ (pushforwardAlgebraIso s.algebra).inv.right =
        (pushforwardAlgebra (relativeSpecToBase s.algebra)).hom := Under.w _
    exact congrArg (fun k => k.hom) h

/-- Over an affine open `U` of the base, the universal map is inverse to the identification of
the sections of the structure sheaf of the relative spectrum over `π⁻¹(U)` with `A(U)`. -/
theorem universalAlgebraMap_app_chartAppLE (U : s.base.affineOpens) :
    (universalAlgebraMap s).right.app (.op U.1) ≫ (gluedSpectrum s).chartAppLE U =
      (Scheme.ΓSpecIso (s.algebra.sections U.1)).inv := by
  have h1 : (gluedSpectrum s).chartAppLE U ≫ (Scheme.ΓSpecIso (s.algebra.sections U.1)).hom
      = (pushforwardSheafIso s.algebra).hom.hom.app (.op (U.1 : s.base.Opens)) :=
    (pushforwardSheafIso_hom_app s.algebra U).symm
  have h2 : (TopCat.Sheaf.forget CommRingCat.{u} s.base).map
          (pushforwardSheafIso s.algebra).inv ≫
        (TopCat.Sheaf.forget CommRingCat.{u} s.base).map (pushforwardSheafIso s.algebra).hom
      = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id]
    exact (TopCat.Sheaf.forget CommRingCat.{u} s.base).map_id _
  have h3 : (pushforwardSheafIso s.algebra).inv.hom.app (.op (U.1 : s.base.Opens)) ≫
      (pushforwardSheafIso s.algebra).hom.hom.app (.op (U.1 : s.base.Opens)) =
      𝟙 (s.algebra.sections U.1) :=
    congrArg (fun k => NatTrans.app k (.op (U.1 : s.base.Opens))) h2
  refine (Iso.comp_hom_eq_id (Scheme.ΓSpecIso (s.algebra.sections U.1))).mp ?_
  rw [Category.assoc, h1]
  exact h3

/-- The sections of the structure morphism of the relative spectrum over an open of the base
factor as the structure morphism of the algebra followed by the universal map. -/
theorem toBase_app (U : s.base.Opens) :
    (gluedSpectrum s).toBase.app U =
      s.algebra.hom.hom.app (.op U) ≫ (universalAlgebraMap s).right.app (.op U) :=
  (congrArg (fun k => NatTrans.app k (.op U)) (Under.w (universalAlgebraMap s))).symm

/-- The universal element of the relative spectrum functor: the structure morphism of the
relative spectrum together with the universal algebra map. -/
noncomputable def universalRelativeSpecPair : RelativeSpecPair s (gluedSpectrum s).scheme :=
  ⟨(gluedSpectrum s).toBase, universalAlgebraMap s⟩

/-- The sections of a chart over an affine open `U` of the base identify `A(U)` with the
sections of the structure sheaf of the relative spectrum over `π⁻¹(U)`. -/
instance isIso_chartAppLE (U : s.base.affineOpens) :
    IsIso ((gluedSpectrum s).chartAppLE U) := by
  have : IsIso ((gluedSpectrum s).chartIsoPreimage U).hom.appTop :=
    inferInstanceAs (IsIso (Scheme.Γ.map ((gluedSpectrum s).chartIsoPreimage U).hom.op))
  rw [GluedSpectrum.chartAppLE_eq]
  infer_instance

/-- The universal map over an affine open `U` of the base, written through the identification of
the chart of `U` with the open subscheme `π⁻¹(U)`. -/
theorem universalAlgebraMap_app (U : s.base.affineOpens) :
    (universalAlgebraMap s).right.app (.op U.1) =
      (Scheme.ΓSpecIso (s.algebra.sections U.1)).inv ≫
        ((gluedSpectrum s).chartIsoPreimage U).inv.appTop ≫
          ((gluedSpectrum s).toBase ⁻¹ᵁ U.1).topIso.hom := by
  have hinv : ((gluedSpectrum s).chartIsoPreimage U).inv.appTop ≫
      ((gluedSpectrum s).chartIsoPreimage U).hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id, Scheme.Hom.id_appTop]
  have key : ((Scheme.ΓSpecIso (s.algebra.sections U.1)).inv ≫
        ((gluedSpectrum s).chartIsoPreimage U).inv.appTop ≫
        ((gluedSpectrum s).toBase ⁻¹ᵁ U.1).topIso.hom) ≫ (gluedSpectrum s).chartAppLE U =
      (Scheme.ΓSpecIso (s.algebra.sections U.1)).inv := by
    rw [GluedSpectrum.chartAppLE_eq, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
      hinv, Category.comp_id]
  exact (cancel_mono ((gluedSpectrum s).chartAppLE U)).mp
    ((universalAlgebraMap_app_chartAppLE s U).trans key.symm)


/-- The universal map over an affine open `U` of the base, transported to the global sections of
the open subscheme `π⁻¹(U)`. -/
theorem universalAlgebraMap_app_comp_topIso_inv (U : s.base.affineOpens) :
    (universalAlgebraMap s).right.app (.op U.1) ≫
        ((gluedSpectrum s).toBase ⁻¹ᵁ U.1).topIso.inv =
      (Scheme.ΓSpecIso (s.algebra.sections U.1)).inv ≫
        ((gluedSpectrum s).chartIsoPreimage U).inv.appTop := by
  rw [universalAlgebraMap_app, Category.assoc, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- Over an affine open `U` of the base, the universal map `A ⟶ π_* 𝒪_X` is an isomorphism on
sections: it is inverse to the identification of the sections of the structure sheaf of the
relative spectrum over `π⁻¹(U)` with `A(U)`. -/
instance isIso_universalAlgebraMap_app (U : s.base.affineOpens) :
    IsIso ((universalAlgebraMap s).right.app (.op U.1)) := by
  have h : IsIso ((universalAlgebraMap s).right.app (.op U.1) ≫
      (gluedSpectrum s).chartAppLE U) := by
    rw [universalAlgebraMap_app_chartAppLE]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((gluedSpectrum s).chartAppLE U)

/-! ### Morphisms into the relative spectrum attached to a pair -/

variable {s}
variable {T : Scheme.{u}} (p : RelativeSpecPair s T)

/-- The restriction to the inverse image of an affine open `U` of the base of the morphism
attached to a pair: the canonical morphism to the spectrum of its sections, followed by the
chart of `U`. -/
noncomputable def pairLocal (U : s.base.affineOpens) :
    (p.1 ⁻¹ᵁ U.1).toScheme ⟶ (gluedSpectrum s).scheme :=
  (p.1 ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (p.2.right.app (.op U.1)) ≫ (gluedSpectrum s).chart U

/-- The local morphisms attached to a pair are compatible with the inclusion of the inverse image
of a smaller affine open into that of a larger one. -/
theorem pairLocal_naturality (U V : s.base.affineOpens) (h : U.1 ≤ V.1) :
    T.homOfLE (p.1.preimage_mono h) ≫ pairLocal p V = pairLocal p U := by
  have hn : s.algebra.right.obj.map (homOfLE h).op ≫ p.2.right.app (.op U.1) =
      p.2.right.app (.op V.1) ≫ T.presheaf.map (homOfLE (p.1.preimage_mono h)).op :=
    p.2.right.naturality (homOfLE h).op
  dsimp only [pairLocal]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, ← Spec.map_comp_assoc, ← hn,
    Spec.map_comp]
  simp only [Category.assoc, (gluedSpectrum s).chart_naturality h]

/-- The local morphism attached to a pair over an affine open `U`, followed by the structure
morphism of the relative spectrum, is the restriction of the first component of the pair to
the inverse image of `U`. -/
theorem pairLocal_toBase (U : s.base.affineOpens) :
    pairLocal p U ≫ (gluedSpectrum s).toBase = (p.1 ⁻¹ᵁ U.1).ι ≫ p.1 := by
  have hw : s.algebra.hom.hom.app (.op U.1) ≫ p.2.right.app (.op U.1) = p.1.app U.1 :=
    congrArg (fun k => k.app (.op U.1)) (Under.w p.2)
  calc pairLocal p U ≫ (gluedSpectrum s).toBase
      = (p.1 ⁻¹ᵁ U.1).toSpecΓ ≫
          (Spec.map (p.2.right.app (.op U.1)) ≫ (gluedSpectrum s).chart U) ≫
            (gluedSpectrum s).toBase := Category.assoc _ _ _
    _ = (p.1 ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (p.2.right.app (.op U.1)) ≫
          ((gluedSpectrum s).chart U ≫ (gluedSpectrum s).toBase) :=
        congrArg (fun k => (p.1 ⁻¹ᵁ U.1).toSpecΓ ≫ k) (Category.assoc _ _ _)
    _ = (p.1 ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (p.2.right.app (.op U.1)) ≫
          (Spec.map (s.algebra.hom.hom.app (.op U.1)) ≫ U.2.isoSpec.inv ≫ U.1.ι) :=
        congrArg (fun k => (p.1 ⁻¹ᵁ U.1).toSpecΓ ≫
          Spec.map (p.2.right.app (.op U.1)) ≫ k) ((gluedSpectrum s).chart_comp_toBase U)
    _ = (p.1 ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (p.1.app U.1) ≫ U.2.isoSpec.inv ≫ U.1.ι := by
        rw [← Spec.map_comp_assoc, hw]
        rfl
    _ = p.1 ∣_ U.1 ≫ U.1.toSpecΓ ≫ U.2.fromSpec :=
        Scheme.Opens.toSpecΓ_naturality_assoc p.1 U.1 U.2.fromSpec
    _ = p.1 ∣_ U.1 ≫ U.1.ι := congrArg (fun k => p.1 ∣_ U.1 ≫ k) U.2.toSpecΓ_fromSpec
    _ = (p.1 ⁻¹ᵁ U.1).ι ≫ p.1 := morphismRestrict_ι p.1 U.1

/-- The morphism to the relative spectrum attached to a pair `(f, φ)`. -/
noncomputable def pairToHom : T ⟶ (gluedSpectrum s).scheme :=
  Scheme.glueOverAffinePreimages p.1 (pairLocal p) (pairLocal_naturality p)

/-- The morphism attached to a pair restricts, on the inverse image of an affine open `U` of the
base, to the local morphism attached to the pair over `U`. -/
@[reassoc]
theorem ι_pairToHom (U : s.base.affineOpens) :
    (p.1 ⁻¹ᵁ U.1).ι ≫ pairToHom p = pairLocal p U :=
  Scheme.ι_glueOverAffinePreimages p.1 (pairLocal p) (pairLocal_naturality p) U

/-- The morphism attached to a pair `(f, φ)`, followed by the structure morphism of the relative
spectrum, is `f`. -/
theorem pairToHom_toBase : pairToHom p ≫ (gluedSpectrum s).toBase = p.1 := by
  refine Scheme.hom_ext_of_affinePreimages p.1 fun U => ?_
  rw [← Category.assoc, ι_pairToHom, pairLocal_toBase]

/-! ### The representing data -/

/-- Over an affine open `U` of the base, the universal map followed by the sections of the
morphism attached to a pair `(f, φ)` is the component of `φ` over `U`. -/
theorem pairToHom_appLE (U : s.base.affineOpens)
    (h : p.1 ⁻¹ᵁ U.1 ≤ pairToHom p ⁻¹ᵁ ((gluedSpectrum s).toBase ⁻¹ᵁ U.1)) :
    (universalAlgebraMap s).right.app (.op U.1) ≫
        (pairToHom p).appLE ((gluedSpectrum s).toBase ⁻¹ᵁ U.1) (p.1 ⁻¹ᵁ U.1) h =
      p.2.right.app (.op U.1) := by
  set W := p.1 ⁻¹ᵁ U.1
  set Z := (gluedSpectrum s).toBase ⁻¹ᵁ U.1
  set χ := p.2.right.app (.op U.1) with hχ
  set l := W.toSpecΓ ≫ Spec.map χ with hl
  have hi : (⊤ : W.toScheme.Opens) ≤ (W.ι ≫ pairToHom p) ⁻¹ᵁ Z := by
    rw [Scheme.Hom.comp_preimage]
    exact W.ι_preimage_self.ge.trans (W.ι.preimage_mono h)
  have hj : (⊤ : W.toScheme.Opens) ≤ (l ≫ (gluedSpectrum s).chart U) ⁻¹ᵁ Z := by
    rw [Scheme.Hom.comp_preimage, (gluedSpectrum s).chart_preimage U]
    simp
  have he : W.ι ≫ pairToHom p = l ≫ (gluedSpectrum s).chart U := by
    simpa only [pairLocal, hl, hχ, Category.assoc] using ι_pairToHom p U
  apply (cancel_mono W.topIso.inv).mp
  rw [Category.assoc, ← ι_appLE_self W, Scheme.Hom.appLE_comp_appLE,
    appLE_congr_hom he hi hj,
    ← l.appLE_comp_appLE ((gluedSpectrum s).chart U) Z ⊤ ⊤
      ((gluedSpectrum s).chart_preimage U).ge (by simp),
    ← Category.assoc, universalAlgebraMap_app_chartAppLE s U, appLE_top_top l (by simp)]
  rw [hl]
  exact (inv_comp_toSpecΓ_comp_specMap_appTop W χ).trans (by rw [ι_appLE_self])

/-! ### The universal element is universal -/

/-- The local morphism over an affine open `U` attached to the pullback of the universal element
along `f` is the restriction of `f` to the inverse image of `U`. -/
theorem pairLocal_pullback_universalRelativeSpecPair (f : T ⟶ (gluedSpectrum s).scheme)
    (U : s.base.affineOpens) :
    pairLocal (RelativeSpecPair.pullback f (universalRelativeSpecPair s)) U =
      ((f ≫ (gluedSpectrum s).toBase) ⁻¹ᵁ U.1).ι ≫ f := by
  have hecomp : ((gluedSpectrum s).chartIsoPreimage U).inv ≫ (gluedSpectrum s).chart U =
      ((gluedSpectrum s).toBase ⁻¹ᵁ U.1).ι := by
    rw [← (gluedSpectrum s).chartIsoPreimage_hom_ι U, Iso.inv_hom_id_assoc]
  have hinv : ((gluedSpectrum s).toBase ⁻¹ᵁ U.1).toSpecΓ ≫
        Spec.map ((universalAlgebraMap s).right.app (.op U.1)) =
      ((gluedSpectrum s).chartIsoPreimage U).inv :=
    toSpecΓ_specMap_eq _ _ _ (universalAlgebraMap_app_comp_topIso_inv s U)
  have h0 : pairLocal (RelativeSpecPair.pullback f (universalRelativeSpecPair s)) U =
      ((f ≫ (gluedSpectrum s).toBase) ⁻¹ᵁ U.1).toSpecΓ ≫
        Spec.map (f.app ((gluedSpectrum s).toBase ⁻¹ᵁ U.1)) ≫
          Spec.map ((universalAlgebraMap s).right.app (.op U.1)) ≫
            (gluedSpectrum s).chart U :=
    congrArg (fun k => ((f ≫ (gluedSpectrum s).toBase) ⁻¹ᵁ U.1).toSpecΓ ≫ k)
      (Spec.map_comp_assoc ((universalAlgebraMap s).right.app (.op U.1))
        (f.app ((gluedSpectrum s).toBase ⁻¹ᵁ U.1)) ((gluedSpectrum s).chart U))
  have h1 := Scheme.Opens.toSpecΓ_naturality_assoc f ((gluedSpectrum s).toBase ⁻¹ᵁ U.1)
    (Spec.map ((universalAlgebraMap s).right.app (.op U.1)) ≫ (gluedSpectrum s).chart U)
  have h2 : ((gluedSpectrum s).toBase ⁻¹ᵁ U.1).toSpecΓ ≫
        Spec.map ((universalAlgebraMap s).right.app (.op U.1)) ≫
          (gluedSpectrum s).chart U =
      ((gluedSpectrum s).toBase ⁻¹ᵁ U.1).ι :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k => k ≫ (gluedSpectrum s).chart U) hinv).trans hecomp)
  exact h0.trans (h1.trans ((congrArg
    (fun k => f ∣_ ((gluedSpectrum s).toBase ⁻¹ᵁ U.1) ≫ k) h2).trans
      (morphismRestrict_ι f ((gluedSpectrum s).toBase ⁻¹ᵁ U.1))))

/-- The morphism attached to the pullback of the universal element along `f` is `f`. -/
theorem pairToHom_pullback_universalRelativeSpecPair (f : T ⟶ (gluedSpectrum s).scheme) :
    pairToHom (RelativeSpecPair.pullback f (universalRelativeSpecPair s)) = f := by
  refine Scheme.hom_ext_of_affinePreimages (f ≫ (gluedSpectrum s).toBase) fun U => ?_
  exact (ι_pairToHom (RelativeSpecPair.pullback f (universalRelativeSpecPair s)) U).trans
    (pairLocal_pullback_universalRelativeSpecPair f U)

/-- A morphism `m` into the relative spectrum pulls the universal element back to a pair `(f, φ)`
as soon as `m` lies over `f` and, over every affine open `U` of the base, the universal map
followed by the sections of `m` is the component of `φ` over `U`. -/
theorem pullback_universalRelativeSpecPair_eq (m : T ⟶ (gluedSpectrum s).scheme)
    (hb : m ≫ (gluedSpectrum s).toBase = p.1)
    (hm : ∀ (U : s.base.affineOpens)
      (h : p.1 ⁻¹ᵁ U.1 ≤ m ⁻¹ᵁ ((gluedSpectrum s).toBase ⁻¹ᵁ U.1)),
      (universalAlgebraMap s).right.app (.op U.1) ≫
          m.appLE ((gluedSpectrum s).toBase ⁻¹ᵁ U.1) (p.1 ⁻¹ᵁ U.1) h =
        p.2.right.app (.op U.1)) :
    RelativeSpecPair.pullback m (universalRelativeSpecPair s) = p := by
  obtain ⟨g, φ⟩ := p
  dsimp only at hb
  subst hb
  refine congrArg (Sigma.mk _) (Under.UnderMorphism.ext ?_)
  refine TopCat.Sheaf.hom_ext s.algebra.right.obj
    ((TopCat.Sheaf.pushforward CommRingCat (m ≫ (gluedSpectrum s).toBase).base).obj T.sheaf)
    (by rw [Subtype.range_coe]; exact s.base.isBasis_affineOpens) fun U => ?_
  have happ : m.appLE ((gluedSpectrum s).toBase ⁻¹ᵁ U.1)
      (m ⁻¹ᵁ ((gluedSpectrum s).toBase ⁻¹ᵁ U.1)) le_rfl =
      m.app ((gluedSpectrum s).toBase ⁻¹ᵁ U.1) := m.appLE_eq_app
  exact (congrArg (fun k => (universalAlgebraMap s).right.app (.op U.1) ≫ k) happ).symm.trans
    (hm U le_rfl)

/-- The pullback of the universal element along the morphism attached to a pair is that pair. -/
theorem pullback_universalRelativeSpecPair_pairToHom :
    RelativeSpecPair.pullback (pairToHom p) (universalRelativeSpecPair s) = p :=
  pullback_universalRelativeSpecPair_eq p (pairToHom p) (pairToHom_toBase p) (pairToHom_appLE p)

/-! ### Representability -/

variable (s)

/-- The glued relative spectrum represents the relative spectrum functor, with universal element
the structure morphism together with the universal algebra map. -/
@[stacks 01LV, stacks 01LW "the relative spectrum with its universal algebra map"]
noncomputable def relativeSpecRepresentableBy :
    (relativeSpecFunctor s).RepresentableBy (gluedSpectrum s).scheme where
  homEquiv {X} :=
    { toFun := fun f => RelativeSpecPair.pullback f (universalRelativeSpecPair s)
      invFun := pairToHom
      left_inv := pairToHom_pullback_universalRelativeSpecPair
      right_inv := pullback_universalRelativeSpecPair_pairToHom }
  homEquiv_comp {X X'} f g := by
    change RelativeSpecPair.pullback (f ≫ g) (universalRelativeSpecPair s) =
      (relativeSpecFunctor s).map f.op (RelativeSpecPair.pullback g (universalRelativeSpecPair s))
    rw [show (relativeSpecFunctor s).map f.op
        (RelativeSpecPair.pullback g (universalRelativeSpecPair s)) =
      RelativeSpecPair.pullback f
        (RelativeSpecPair.pullback g (universalRelativeSpecPair s)) from rfl]
    refine congrArg (Sigma.mk _) ?_
    rfl

/-- The bijection of the representing data sends a morphism to the pullback of the universal
element along it. -/
@[simp]
theorem relativeSpecRepresentableBy_homEquiv {T : Scheme.{u}}
    (f : T ⟶ (gluedSpectrum s).scheme) :
    (relativeSpecRepresentableBy s).homEquiv f =
      RelativeSpecPair.pullback f (universalRelativeSpecPair s) :=
  rfl

/-- The first component of the pair attached to a morphism `f` into the relative spectrum is `f`
followed by the structure morphism. -/
theorem relativeSpecRepresentableBy_homEquiv_fst {T : Scheme.{u}}
    (f : T ⟶ (gluedSpectrum s).scheme) :
    ((relativeSpecRepresentableBy s).homEquiv f).1 = f ≫ (gluedSpectrum s).toBase := rfl

/-- The functor associated to a quasi-coherent algebra on a scheme is representable by a
scheme. -/
@[stacks 01LU]
theorem relativeSpecFunctor_isRepresentable : (relativeSpecFunctor s).IsRepresentable :=
  (relativeSpecRepresentableBy s).isRepresentable

/-- The canonical comparison between the glued relative spectrum and any scheme representing the
relative spectrum functor. -/
noncomputable def gluedSpectrumIso {X : Scheme.{u}}
    (h : (relativeSpecFunctor s).RepresentableBy X) : (gluedSpectrum s).scheme ≅ X :=
  (relativeSpecRepresentableBy s).uniqueUpToIso h

/-- The canonical comparison with a representing scheme corresponds, under its bijection, to the
universal element of the glued relative spectrum. -/
theorem gluedSpectrumIso_homEquiv {X : Scheme.{u}}
    (h : (relativeSpecFunctor s).RepresentableBy X) :
    h.homEquiv (gluedSpectrumIso s h).hom = universalRelativeSpecPair s := by
  show h.homEquiv (h.homEquiv.symm
    ((relativeSpecRepresentableBy s).homEquiv (𝟙 _))) = universalRelativeSpecPair s
  rw [Equiv.apply_symm_apply]
  exact congrArg (Sigma.mk _) rfl

/-- The canonical comparison between the glued relative spectrum and a scheme representing the
relative spectrum functor is a morphism over the base, where the representing scheme carries the
structure morphism of its universal element. -/
@[stacks 01LV "canonical comparison over the base"]
theorem gluedSpectrumIso_hom_toBase {X : Scheme.{u}}
    (h : (relativeSpecFunctor s).RepresentableBy X) :
    (gluedSpectrumIso s h).hom ≫ (h.homEquiv (𝟙 X)).1 = (gluedSpectrum s).toBase := by
  have he := congrArg Sigma.fst (gluedSpectrumIso_homEquiv s h)
  rwa [h.homEquiv_eq] at he

/-- The inverse of the canonical comparison is a morphism over the base as well, so that the
comparison is an isomorphism of schemes over the base. -/
theorem gluedSpectrumIso_inv_toBase {X : Scheme.{u}}
    (h : (relativeSpecFunctor s).RepresentableBy X) :
    (gluedSpectrumIso s h).inv ≫ (gluedSpectrum s).toBase = (h.homEquiv (𝟙 X)).1 := by
  rw [← gluedSpectrumIso_hom_toBase s h, Iso.inv_hom_id_assoc]

end Stacks.RelativeSpec

end
