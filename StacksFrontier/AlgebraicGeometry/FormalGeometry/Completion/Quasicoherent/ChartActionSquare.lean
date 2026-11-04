module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.ChartIdealSheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.PushforwardIdealPowerGradedModulePlus

/-!
# The action square of an affine chart of the base

Let `f : X ⟶ Y` be a morphism of schemes, `ℐ ⊆ 𝒪_Y` a quasi-coherent sheaf of ideals, `ℱ` a
quasi-coherent `𝒪_X`-module and `V` an affine open of `Y`. [Stacks, Tag 02O8] on the chart
`f⁻¹(V) ⟶ Spec Γ(Y, V)` makes `⨁ₙ Hᵖ(f⁻¹(V), ℐⁿℱ)` a module over the *ring* Rees algebra
`B = ⨁ₙ ℐ(V)ⁿ`, a homogeneous element `b` of degree `k` acting through the morphism of sheaves
`Stacks.Cohomology.FormalFunctions.actHom`; the graded module
`Stacks.Blowup.pushforwardReesGradedModulePlus` on `Y` is acted on instead by the *sheaf* Rees
algebra `⨁ₙ ℐⁿ`, a section of `ℐᵏ` over `V` acting through `Stacks.Blowup.mulRestrict`.

Both act on sections over an open `W` of `f⁻¹(V)` by multiplying an ambient section of `ℱ` over
`j(W)`, where `j = (f⁻¹V).ι`, by one function in `Γ(X, j(W))`, and
`Stacks.Algebraization.piece_reesFiltrationModule_affineBaseChart` makes the two sheaves equal;
so the comparison of the two actions collapses to a single identity of functions. **This file
proves that identity**, and the identity of ring maps `Γ(Y, V) ⟶ Γ(X, j(W))` behind it.

## Main results

* `Stacks.Algebraization.affineBaseChart_appLE`: **the ring-map identity.** The structure
  morphism of the chart induces on `Γ(Y, V) ⟶ Γ(X, j(W))` the map `f` itself induces, namely
  `AlgebraicGeometry.Scheme.Hom.appLE`.
* `Stacks.Algebraization.chartReesSection`: the section of `ℐʲ` over `V` attached to a
  homogeneous element of degree `k` of the ring Rees algebra, for any degree `j` equal to `k`.
* `Stacks.Algebraization.reesPieceAmbient_gradedReesSection_eq`: **the action square**, as the
  identity of the two functions by which the two actions multiply.
* `Stacks.Algebraization.reesMultiple_affineBaseChart`: the degree-`d` piece of the chart's
  graded module, *as a concrete submodule* of `ℱ|_{f⁻¹V}`, is the restriction of `ℐᵈℱ`.
* `Stacks.Algebraization.actHom_comp_chartPieceRestrict`: **the action square as an identity of
  morphisms of sheaves of modules on `f⁻¹(V)`** — the morphism-level lift of the scalar identity.
  Acting by `b` on the chart and then comparing the pieces is comparing the pieces and then
  multiplying by the corresponding section of `ℐᵏ`.

## References

* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02O9](https://stacks.math.columbia.edu/tag/02O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.FormalFunctions
open Stacks.AlgebraicGeometry.SubmoduleRestrict
open SheafOfModules.GradedModule

universe u

attribute [local instance] Stacks.Algebraization.sectionsModuleΓ
  Stacks.Algebraization.sectionsModuleΓSheaf

namespace Stacks.Algebraization

/-! ### Transports between subsheaves, at variables -/

/-- **A square of morphisms of sheaves of modules, from an identity of sections.** If
`β (α x) = δ (γ x)` for every section `x` of `A` over every open, then `α ≫ β = γ ≫ δ`. -/
public theorem comp_eq_comp_of_sections {Z : Scheme.{u}} {A B C D : Z.Modules}
    (α : A ⟶ B) (β : B ⟶ D) (γ : A ⟶ C) (δ : C ⟶ D)
    (h : ∀ (U : (Opens Z)ᵒᵖ) (x : A.val.obj U),
      (β.val.app U).hom ((α.val.app U).hom x) = (δ.val.app U).hom ((γ.val.app U).hom x)) :
    α ≫ β = γ ≫ δ :=
  SheafOfModules.hom_ext <| PresheafOfModules.Hom.ext <| funext fun U ↦
    ModuleCat.hom_ext <| LinearMap.ext (h U)

/-- **The factored comparison of the two spellings of a restricted subsheaf.** A submodule `P` of
`ℱ|_{Y'}` that is known to be the restriction of a submodule `N` of `ℱ` is compared with
`(restrictFunctor g).obj N.toSheafOfModules` in two steps: the transport
`Stacks.Cohomology.FormalFunctions.submoduleCast` along the equality of submodules, whose effect
on an ambient section is known, followed by the comparison of the two spellings, which is
supplied by `Stacks.AlgebraicGeometry.SubmoduleRestrict.restrictTo_toSheafOfModules'`. -/
public def restrictToCompare {A : Type u} [CommRing A] (Z : Over (Spec (.of A)))
    {Zt : Scheme.{u}} (g : Z.left ⟶ Zt) [hg : IsOpenImmersion g]
    {G : Zt.Modules} (N : G.Submodule) {P : (Scheme.Modules.restrict G g).Submodule}
    (e : P = restrictTo g N) :
    (P.toSheafOfModules : Z.left.Modules) ⟶
      (Scheme.Modules.restrictFunctor g).obj (N.toSheafOfModules : Zt.Modules) :=
  submoduleCast Z (Scheme.Modules.restrict G g) e ≫ eqToHom (restrictTo_toSheafOfModules' g N)

/-- **The factored comparison does not move an ambient section.** -/
public theorem restrictToCompare_coe {A : Type u} [CommRing A] (Z : Over (Spec (.of A)))
    {Zt : Scheme.{u}} (g : Z.left ⟶ Zt) [hg : IsOpenImmersion g]
    {G : Zt.Modules} (N : G.Submodule) {P : (Scheme.Modules.restrict G g).Submodule}
    (e : P = restrictTo g N) (U : (Opens Z.left)ᵒᵖ)
    (y : (P.toSheafOfModules : Z.left.Modules).val.obj U) :
    (((restrictToCompare Z g N e).val.app U).hom y).1 = y.1 := by
  subst e
  rfl

/-- **A function on an open subscheme acts on the sections of a restricted module as the
corresponding function on the image open acts on the ambient module.** -/
public theorem smul_restrictFunctor_ι {Z : Scheme.{u}} (U₀ : Z.Opens) (G : Z.Modules)
    (W : U₀.toScheme.Opens) (r : Γ(U₀.toScheme, W))
    (z : Γ((Scheme.Modules.restrictFunctor U₀.ι).obj G, W)) :
    (show Γ(G, U₀.ι ''ᵁ W) from r • z) =
      (show Γ(Z, U₀.ι ''ᵁ W) from r) • (show Γ(G, U₀.ι ''ᵁ W) from z) := by
  have h1 : r • z = (show Γ((Scheme.Modules.restrictFunctor U₀.ι).obj G, W) from
      (U₀.ι.appIso W).inv r • (show Γ(G, U₀.ι ''ᵁ W) from z)) := rfl
  rw [h1, Scheme.Opens.ι_appIso]
  rfl

/-- `smul_restrictFunctor_ι` with the scalar and the section replaced by ones they are equal to
on the image open: if `r = r'` and `z = z'` there, then `r • z = r' • z'`. -/
public theorem smul_restrictFunctor_ι_eq {Z : Scheme.{u}} (U₀ : Z.Opens) (G : Z.Modules)
    (W : U₀.toScheme.Opens) (r : Γ(U₀.toScheme, W)) (r' : Γ(Z, U₀.ι ''ᵁ W))
    (hr : (show Γ(Z, U₀.ι ''ᵁ W) from r) = r')
    (z : Γ((Scheme.Modules.restrictFunctor U₀.ι).obj G, W)) (z' : Γ(G, U₀.ι ''ᵁ W))
    (hz : (show Γ(G, U₀.ι ''ᵁ W) from z) = z') :
    (show Γ(G, U₀.ι ''ᵁ W) from r • z) = r' • z' := by
  subst hr hz
  exact smul_restrictFunctor_ι U₀ G W r z

/-- **Multiplication by a homogeneous section of the Rees algebra, on ambient sections**: it
multiplies the ambient section of `ℱ` by the function attached to the homogeneous section. -/
public theorem reesMultipleSmul_coe {Z : Scheme.{u}} (K : Z.IdealSheafData)
    (G : SheafOfModules.{u} Z.ringCatSheaf) (n i : ℤ) (U : (Opens Z)ᵒᵖ)
    (z : ((Stacks.Blowup.reesMultiple K n G).toSheafOfModules).val.obj U)
    (r : (Stacks.Blowup.reesPiece K i).val.obj U) :
    (Stacks.Blowup.reesMultipleSmul K G n i U z r).1 =
      Stacks.Blowup.reesPieceAmbient K i U.unop r • z.1 := rfl

/-- The comparison of the two spellings of a restricted subsheaf is the identity on sections. -/
public theorem val_eqToHom_restrictTo {Z W' : Scheme.{u}} (g : W' ⟶ Z) [IsOpenImmersion g]
    {G : Z.Modules} (N : G.Submodule) (U : (Opens W')ᵒᵖ)
    (y : ((restrictTo g N).toSheafOfModules : W'.Modules).val.obj U) :
    ((eqToHom (restrictTo_toSheafOfModules' g N)).val.app U) y = y :=
  rfl

/-- **A transport along an equality of sheaves of modules does not move a section.** -/
public theorem heq_eqToHom_toSheafOfModules {Z : Scheme.{u}} {G : Z.Modules} {P : G.Submodule}
    {N : Z.Modules} (h : (P.toSheafOfModules : Z.Modules) = N) (U : (Opens Z)ᵒᵖ)
    (y : (P.toSheafOfModules : Z.Modules).val.obj U) :
    HEq (((eqToHom h).val.app U) y) y := by
  subst h
  rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData)

/-! ### The ring map of a chart on an open of `f⁻¹(V)` -/

/-- **The restricted morphism on sections over an open of `f⁻¹(V)`.** Reading a function on `V`
as a global function on `V` read as a scheme and pulling it back along `f ∣_ V` to an open `W` of
`f⁻¹(V)` is pulling it back along `f` to the image of `W` in `X`. -/
public theorem topIso_inv_comp_morphismRestrict_appLE (V : Y.Opens)
    (W : (f ⁻¹ᵁ V).toScheme.Opens) (e : W ≤ (f ∣_ V) ⁻¹ᵁ ⊤) :
    V.topIso.inv ≫ (f ∣_ V).appLE ⊤ W e =
      f.appLE V ((f ⁻¹ᵁ V).ι ''ᵁ W) ((f ⁻¹ᵁ V).ι_image_le W) := by
  rw [morphismRestrict_appLE, Scheme.Opens.topIso_inv]
  exact Scheme.Hom.map_appLE' f _ V.ι_image_top

/-- **The structure morphism of the chart on global sections.** `Γ(Y, V) ≅ Γ(Spec Γ(Y, V), ⊤)`
followed by the chart's structure morphism is `V.topIso.inv` followed by `f ∣_ V`. -/
public theorem ΓSpecIso_inv_comp_affineBaseChart_appTop (V : Y.affineOpens) :
    (Scheme.ΓSpecIso (.of ↥Γ(Y, V.1))).inv ≫ (affineBaseChart f V).hom.appTop =
      V.1.topIso.inv ≫ (f ∣_ V.1).appTop := by
  have : IsAffine V.1.toScheme := V.2
  have hmap : ((Scheme.ΓSpecIso (.of ↥Γ(Y, V.1))).inv ≫ V.2.isoSpec.hom.appTop) =
      V.1.topIso.inv := by
    rw [V.2.isoSpec_hom_appTop]
    exact Iso.inv_hom_id_assoc _ _
  show (Scheme.ΓSpecIso (.of ↥Γ(Y, V.1))).inv ≫
      ((f ∣_ V.1) ≫ V.2.isoSpec.hom).appTop = _
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, hmap]

/-- **The ring-map identity.** The ring map `Γ(Y, V) ⟶ Γ(X, j(W))` that the chart's structure
morphism induces — read through `Γ(Y, V) ≅ Γ(Spec Γ(Y, V), ⊤)` and restricted to an open `W` of
`f⁻¹(V)` — is the one `f` itself induces. -/
public theorem affineBaseChart_appLE (V : Y.affineOpens)
    (W : (f ⁻¹ᵁ V.1).toScheme.Opens) :
    ((Scheme.ΓSpecIso (.of ↥Γ(Y, V.1))).inv ≫ (affineBaseChart f V).hom.appTop) ≫
        (f ⁻¹ᵁ V.1).toScheme.presheaf.map (homOfLE (le_top (a := W))).op =
      f.appLE V.1 ((f ⁻¹ᵁ V.1).ι ''ᵁ W) ((f ⁻¹ᵁ V.1).ι_image_le W) := by
  rw [ΓSpecIso_inv_comp_affineBaseChart_appTop]
  exact (Category.assoc _ _ _).trans
    (topIso_inv_comp_morphismRestrict_appLE f V.1 W le_top)

/-- The scalar by which `Stacks.Cohomology.FormalFunctions.actHom` multiplies on the chart is the
pullback along `f` of the function on `V`. -/
public theorem ringSectionToGamma_baseRingToSections_affineBaseChart (V : Y.affineOpens)
    (W : (f ⁻¹ᵁ V.1).toScheme.Opens) (a : Γ(Y, V.1)) :
    (Stacks.Blowup.ringSectionToGamma
        (baseRingToSections ↥Γ(Y, V.1) (affineBaseChart f V) (op W) a) :
      Γ(X, (f ⁻¹ᵁ V.1).ι ''ᵁ W)) =
      f.appLE V.1 ((f ⁻¹ᵁ V.1).ι ''ᵁ W) ((f ⁻¹ᵁ V.1).ι_image_le W) a :=
  congrArg (fun φ : Γ(Y, V.1) ⟶ Γ(X, (f ⁻¹ᵁ V.1).ι ''ᵁ W) => φ a)
    (affineBaseChart_appLE f V W)

/-! ### The homogeneous section of `ℐ` attached to an element of the ring Rees algebra -/

/-- **The section of `ℐʲ` over `V` attached to a homogeneous element of degree `k` of the ring
Rees algebra `B = ⨁ₙ ℐ(V)ⁿ`.** Over the affine open `V` the sections of `ℐᵏ` are `ℐ(V)ᵏ`
(`Stacks.Blowup.reesPieceAffineEquiv`) and the underlying element of a homogeneous element of
degree `k` lies there (`Stacks.Cohomology.FormalFunctions.reesElt_mem`). The section is taken in
any degree `j` equal to `k`. -/
public def chartReesSection (V : Y.affineOpens) {k : ℕ}
    (b : ↥(Stacks.Blowup.reesGrading (I.ideal V) k)) {j : ℤ} (hj : (k : ℤ) = j) :
    (Stacks.Blowup.reesPiece I j).val.obj (op V.1) :=
  SheafOfModules.castHom (Stacks.Blowup.reesPiece I) hj (op V.1)
    ((Stacks.Blowup.reesPieceAffineEquiv I (k : ℤ) (Int.natCast_nonneg k) V).symm
      ⟨reesElt (I.ideal V) b, by simpa using reesElt_mem (I.ideal V) b⟩)

/-- **The image in `Γ(Y, V)` of the attached section is the underlying element of `ℐ(V)ᵏ`.** -/
public theorem reesPieceAmbient_chartReesSection (V : Y.affineOpens) {k : ℕ}
    (b : ↥(Stacks.Blowup.reesGrading (I.ideal V) k)) {j : ℤ} (hj : (k : ℤ) = j) :
    Stacks.Blowup.reesPieceAmbient I j V.1 (chartReesSection I V b hj) =
      reesElt (I.ideal V) b :=
  (Stacks.Blowup.reesPieceAmbient_castHom I hj V.1 _).trans
    ((Stacks.Blowup.reesPieceAffineEquiv_coe I (k : ℤ) (Int.natCast_nonneg k) V _).symm.trans
      (congrArg (fun z : ↥(I.ideal V ^ ((k : ℤ)).toNat) => (z : Γ(Y, V.1)))
        ((Stacks.Blowup.reesPieceAffineEquiv I (k : ℤ)
          (Int.natCast_nonneg k) V).apply_symm_apply _)))

/-! ### The action square -/

/-- **The action square of a chart**, as the identity of the two functions by which the two
actions multiply an ambient section of `ℱ` over `j(W)`.

On the left `Stacks.Cohomology.FormalFunctions.actHom` multiplies by the image in
`Γ(f⁻¹(V), W)` of the global section of the chart's Rees algebra attached to `b`; on the right
`Stacks.Blowup.mulRestrict` multiplies by the image in `Γ(X, j(W))` of the restriction of the
inverse image of the section of `ℐᵏ` over `V` attached to `b`. -/
public theorem reesPieceAmbient_gradedReesSection_eq (V : Y.affineOpens) {k : ℕ}
    (b : ↥(Stacks.Blowup.reesGrading (I.ideal V) k)) (W : (f ⁻¹ᵁ V.1).toScheme.Opens) :
    Stacks.Blowup.reesPieceAmbient
        (baseIdealSheaf ↥Γ(Y, V.1) (I.ideal V) (affineBaseChart f V).hom) (k : ℤ) W
        ((gradedReesSection (I.ideal V) (affineBaseChart f V) b).eval (op W)) =
      Stacks.Blowup.reesPieceAmbient (I.comap f) (k : ℤ) ((f ⁻¹ᵁ V.1).ι ''ᵁ W)
        (Stacks.restr (Stacks.Blowup.reesPiece (I.comap f) (k : ℤ)).val
          (homOfLE ((f ⁻¹ᵁ V.1).ι_image_le W)).op
          (Stacks.Blowup.reesPieceComapSection f I (k : ℤ) (op V.1)
            (chartReesSection I V b rfl))) := by
  have hcomap : Stacks.Blowup.reesPieceAmbient (I.comap f) (k : ℤ) (f ⁻¹ᵁ V.1)
        (Stacks.Blowup.reesPieceComapSection f I (k : ℤ) (op V.1)
          (chartReesSection I V b rfl)) =
      (f.app V.1) (Stacks.Blowup.reesPieceAmbient I (k : ℤ) V.1
        (chartReesSection I V b rfl)) :=
    Stacks.Blowup.reesPieceAmbient_comap f I (k : ℤ) V.1 (chartReesSection I V b rfl)
  rw [Stacks.Blowup.reesPieceAmbient_restr, hcomap, reesPieceAmbient_chartReesSection,
    reesPieceAmbient_gradedReesSection]
  exact ringSectionToGamma_baseRingToSections_affineBaseChart f V W (reesElt (I.ideal V) b)

/-! ### The pieces of the chart's graded module, as subsheaves of `ℱ|_{f⁻¹V}` -/

variable (F : X.Modules)

/-- **The pieces of the chart's graded module, as concrete submodules.** The degree-`d` piece of
`Stacks.Cohomology.FormalFunctions.reesFiltrationModule` on the chart is the restriction to
`f⁻¹(V)` of the subsheaf `ℐ^{d'}ℱ` of `ℱ`, for any degree `d'` equal to `d`. -/
public theorem reesMultiple_affineBaseChart [F.IsQuasicoherent] (V : Y.affineOpens)
    {d d' : ℤ} (hd : d = d') :
    Stacks.Blowup.reesMultiple
        (baseIdealSheaf ↥Γ(Y, V.1) (I.ideal V) (affineBaseChart f V).hom) d
        (affineBaseChartModule f F V) =
      restrictTo (f ⁻¹ᵁ V.1).ι (Stacks.Blowup.reesMultiple (I.comap f) d' F) := by
  subst hd
  rw [baseIdealSheaf_affineBaseChart I f V]
  exact Stacks.Blowup.reesMultiple_comap_ι (I.comap f) (f ⁻¹ᵁ V.1) F d

/-! ### The action square, as an identity of morphisms -/

/-- **The comparison of a piece of the chart's graded module with the restriction of `ℐᵈℱ`**, in
the factored spelling: `restrictToCompare` at `reesMultiple_affineBaseChart`. -/
public def chartPieceRestrict [F.IsQuasicoherent] (V : Y.affineOpens) (d : ℤ) :
    (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
        (affineBaseChartModule f F V)).piece d ⟶
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V.1).ι).obj (Stacks.Blowup.reesComapMod f I F d) :=
  restrictToCompare (affineBaseChart f V) (f ⁻¹ᵁ V.1).ι
    (hg := inferInstanceAs (IsOpenImmersion (f ⁻¹ᵁ V.1).ι))
    (Stacks.Blowup.reesMultiple (I.comap f) d F)
    (reesMultiple_affineBaseChart f I F V (rfl : d = d))

/-- `chartPieceRestrict` does not move an ambient section of `ℱ`. -/
public theorem chartPieceRestrict_coe [F.IsQuasicoherent] (V : Y.affineOpens) (d : ℤ)
    (U : (Opens ↥(f ⁻¹ᵁ V.1))ᵒᵖ)
    (y : ((reesFiltrationModule (I.ideal V) (affineBaseChart f V)
      (affineBaseChartModule f F V)).piece d).val.obj U) :
    (((chartPieceRestrict f I F V d).val.app U).hom y).1 = y.1 := by
  have : IsOpenImmersion (show (affineBaseChart f V).left ⟶ X from (f ⁻¹ᵁ V.1).ι) :=
    inferInstanceAs (IsOpenImmersion (f ⁻¹ᵁ V.1).ι)
  simp only [chartPieceRestrict]
  apply restrictToCompare_coe

/-- **The action of `b` on the chart, on ambient sections**: it multiplies by the image in
`Γ(f⁻¹(V), W)` of the global section of the chart's Rees algebra attached to `b`. -/
public theorem actHom_reesFiltrationModule_coe [F.IsQuasicoherent] (V : Y.affineOpens) {k : ℕ}
    (b : ↥(Stacks.Blowup.reesGrading (I.ideal V) k)) (n : ℤ)
    (W : (f ⁻¹ᵁ V.1).toScheme.Opens)
    (x : ((reesFiltrationModule (I.ideal V) (affineBaseChart f V)
      (affineBaseChartModule f F V)).piece n).val.obj (op W)) :
    (((actHom (I.ideal V) (affineBaseChart f V)
        (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
          (affineBaseChartModule f F V)) b n rfl).val.app (op W)).hom x).1 =
      Stacks.Blowup.reesPieceAmbient
          (baseIdealSheaf ↥Γ(Y, V.1) (I.ideal V) (affineBaseChart f V).hom) (k : ℤ) W
          ((gradedReesSection (I.ideal V) (affineBaseChart f V) b).eval (op W)) • x.1 := rfl

/-- **`Stacks.Blowup.mulRestrict` on sections is a multiplication of the Rees algebra of
`ℐ𝒪_X`**, over the image open. -/
public theorem mulRestrict_reesMultipleSmul (V : Y.affineOpens) (n i : ℤ)
    (r : (Stacks.Blowup.reesPiece (I.comap f) i).val.obj (op (f ⁻¹ᵁ V.1)))
    (W : (f ⁻¹ᵁ V.1).toScheme.Opens)
    (y : ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V.1).ι).obj
      (Stacks.Blowup.reesComapMod f I F n)).val.obj (op W)) :
    (((Stacks.Blowup.mulRestrict f I F n i V.1 r).val.app (op W)).hom y).1 =
      (Stacks.Blowup.reesMultipleSmul (I.comap f) F n i
        (op ((f ⁻¹ᵁ V.1).ι ''ᵁ W)) y
        (Stacks.restr (Stacks.Blowup.reesPiece (I.comap f) i).val
          (homOfLE ((f ⁻¹ᵁ V.1).ι_image_le W)).op r)).1 := rfl

/-- **The action square of a chart, as an identity of morphisms of sheaves of modules on
`f⁻¹(V)`.** Acting on the degree-`n` piece of the chart's graded module by a homogeneous element
`b` of degree `k` of the ring Rees algebra, and then comparing the degree-`n + k` piece with the
restriction of `ℐⁿ⁺ᵏℱ`, is comparing the degree-`n` piece with the restriction of `ℐⁿℱ` and then
multiplying by the section of `ℐᵏ𝒪_X` over `f⁻¹(V)` attached to `b`. -/
public theorem actHom_comp_chartPieceRestrict [F.IsQuasicoherent] (V : Y.affineOpens) {k : ℕ}
    (b : ↥(Stacks.Blowup.reesGrading (I.ideal V) k)) (n : ℤ) :
    actHom (I.ideal V) (affineBaseChart f V)
        (reesFiltrationModule (I.ideal V) (affineBaseChart f V)
          (affineBaseChartModule f F V)) b n rfl ≫
        chartPieceRestrict f I F V (n + (k : ℤ)) =
      chartPieceRestrict f I F V n ≫
        Stacks.Blowup.mulRestrict f I F n (k : ℤ) V.1
          (Stacks.Blowup.reesPieceComapSection f I (k : ℤ) (op V.1)
            (chartReesSection I V b rfl)) := by
  refine comp_eq_comp_of_sections _ _ _ _ fun U x => Subtype.ext ?_
  refine Eq.trans (chartPieceRestrict_coe f I F V (n + (k : ℤ)) U _) ?_
  refine Eq.trans (actHom_reesFiltrationModule_coe f I F V b n U.unop x) ?_
  refine Eq.trans (smul_restrictFunctor_ι_eq (f ⁻¹ᵁ V.1) F U.unop
    (Stacks.Blowup.reesPieceAmbient
      (baseIdealSheaf ↥Γ(Y, V.1) (I.ideal V) (affineBaseChart f V).hom) (k : ℤ) U.unop
      ((gradedReesSection (I.ideal V) (affineBaseChart f V) b).eval U))
    _ (reesPieceAmbient_gradedReesSection_eq f I V b U.unop)
    x.1 _ (chartPieceRestrict_coe f I F V n U x).symm) ?_
  exact (Eq.trans (mulRestrict_reesMultipleSmul f I F V n (k : ℤ) _ U.unop _)
    (reesMultipleSmul_coe (I.comap f) F n (k : ℤ)
      (op ((f ⁻¹ᵁ V.1).ι ''ᵁ U.unop)) _ _)).symm

end Stacks.Algebraization

end
