module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerTransitionMulSection
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionIsomorphismLocus
public import StacksFrontier.AlgebraicGeometry.NonvanishingTrivialization.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.Converse
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleTrivialization
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.SectionLocusCodimension
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.StalkCriterion

/-!
# Affine charts for a section on the locus where its module is invertible

Let `s` be a global section of an `𝒪_Y`-module `L`. Where `L` is invertible, near every point
there is an open `D`, a section `e` of `L` over `D` freely generating the stalks, and a function
`g` on `D` with `s|_D = g e`; the isomorphism locus of `s` then meets `D` in the basic open
`D(g)`. This module constructs such charts, and affine ones inside a given neighbourhood.

## Main results

* `AlgebraicGeometry.bijective_toSpanSingleton_smul_iff_isUnit`: scaling a basis of a module by `r`
  gives a basis exactly when `r` is a unit.
* `AlgebraicGeometry.mem_sectionIsomorphismLocus_iff_bijective_stalkMapL`: membership of
  `AlgebraicGeometry.sectionIsomorphismLocus` is bijectivity of
  `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL`.
* `AlgebraicGeometry.mem_sectionIsomorphismLocus_iff_isIso_stalkMapOfHom`: membership of
  `AlgebraicGeometry.sectionIsomorphismLocus` is invertibility of `stalkMapOfHom`.
* `AlgebraicGeometry.mem_sectionIsomorphismLocus_restrict_iff`: the isomorphism locus of a
  restricted section is the preimage of the isomorphism locus.
* `AlgebraicGeometry.restrictSection_eval`: the restricted section evaluates on an open of `V`
  as the original section on its image.
* `AlgebraicGeometry.exists_sectionLocusChart_of_isInvertible`: the chart for an invertible
  module.
* `AlgebraicGeometry.exists_affine_sectionLocusChart`: an affine chart inside any neighbourhood
  of a point of an open on which the module is invertible.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (stalkMapOfHom)
open Stacks.AlgebraicGeometry.ReflexivePowers (restrictSection unitHomEquiv_symm_restrictSection)

universe u

namespace AlgebraicGeometry

/-- If `m` spans `M` freely, then so does `r • m` if and only if `r` is a unit. -/
theorem bijective_toSpanSingleton_smul_iff_isUnit {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] {m : M} (hm : Function.Bijective (LinearMap.toSpanSingleton R M m)) (r : R) :
    Function.Bijective (LinearMap.toSpanSingleton R M (r • m)) ↔ IsUnit r := by
  have hcomp : ⇑(LinearMap.toSpanSingleton R M (r • m)) =
      ⇑(LinearMap.toSpanSingleton R M m) ∘ fun a => a * r := by
    funext a
    simp [mul_smul]
  rw [hcomp, Function.Bijective.of_comp_iff' hm]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨a, ha⟩ := h.2 1
    exact ⟨⟨r, a, by rwa [mul_comm], ha⟩, rfl⟩
  · obtain ⟨v, rfl⟩ := h
    exact (Units.mulRight v).bijective

variable {Y : Scheme.{u}}

/-- A point lies in `sectionIsomorphismLocus L s` if and only if the `𝒪_{Y, y}`-linear stalk map
`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkMapL` of the morphism `𝒪_Y ⟶ L` determined
by `s` is bijective. -/
theorem mem_sectionIsomorphismLocus_iff_bijective_stalkMapL (L : Y.Modules) (s : L.sections)
    (y : Y) :
    y ∈ sectionIsomorphismLocus L s ↔ Function.Bijective (stalkMapL Y.toRingedSpace
      (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)).val L.val
      (L.unitHomEquiv.symm s).val y) :=
  mem_sectionIsomorphismLocus_iff L s y

/-- If `s` restricts to `g • e` after mapping along `i`, then `s` evaluates there as the
restrictions of `g` and `e`. -/
private theorem eval_eq_smul_map {Y : Scheme.{u}} (L : Y.Modules) (s : L.sections)
    {U V : Y.Opens} (i : op V ⟶ op U) (g : Γ(Y, V)) (e : Γ(L, V))
    (h : L.presheaf.map i (s.eval (op V)) = L.presheaf.map i (g • e)) :
    s.eval (op U) = Y.presheaf.map i g • L.presheaf.map i e :=
  (PresheafOfModules.sections_property s i).symm.trans
    (h.trans (Scheme.Modules.map_smul L i.unop g e))

/-- Let `L` be an invertible module on a scheme `Y` and `s` a global section. Near every point
`y` there is an open `D`, a section `e` of `L` over `D` and a function `g` on `D` with
`s|_D = g e`, such that a point of `D` lies in the isomorphism locus of `s` if and only if it lies
in the basic open of `g`. -/
theorem exists_sectionLocusChart_of_isInvertible (L : Y.Modules)
    [Stacks.SheafOfModules.IsInvertible Y.toRingedSpace.presheaf
      (structureSheafRing Y.toRingedSpace).property L]
    (s : L.sections) (y : Y) :
    ∃ (D : Y.Opens) (_ : y ∈ D) (e : Γ(L, D)) (g : Γ(Y, D)),
      s.eval (op D) = g • e ∧
        ∀ x ∈ D, (x ∈ sectionIsomorphismLocus L s ↔ x ∈ Y.basicOpen g) := by
  obtain ⟨N, ⟨ψ⟩⟩ := (Stacks.SheafOfModules.isInvertible_iff_exists_tensor_iso_unit
    (O := Y.toRingedSpace.presheaf)
    (hO := (structureSheafRing Y.toRingedSpace).property) L).mp ‹_›
  obtain ⟨D₁, hy₁, e₁, b₁, hsb⟩ := Stacks.SheafOfModules.exists_tensorPairing_eq_one_nhds ψ y
  have key := fun z hz =>
    Stacks.SheafOfModules.bijective_smul_grpGerm_of_tensorPairing_eq_one hsb z hz
  obtain ⟨a, ha⟩ := (key y hy₁).2
    (grpGerm Y.toRingedSpace L.val y D₁ hy₁ (s.eval (op D₁)))
  obtain ⟨D₂, hy₂, g₂, hg₂⟩ := Y.presheaf.exists_germ_eq a
  have hy₁₂ : y ∈ D₁ ⊓ D₂ := ⟨hy₁, hy₂⟩
  set e₁₂ : Γ(L, D₁ ⊓ D₂) := L.presheaf.map (homOfLE (inf_le_left : D₁ ⊓ D₂ ≤ D₁)).op e₁
    with he₁₂
  set g₁₂ := Y.presheaf.map (homOfLE (inf_le_right : D₁ ⊓ D₂ ≤ D₂)).op g₂ with hg₁₂
  have hgerm : grpGerm Y.toRingedSpace L.val y (D₁ ⊓ D₂) hy₁₂ (s.eval (op (D₁ ⊓ D₂))) =
      grpGerm Y.toRingedSpace L.val y (D₁ ⊓ D₂) hy₁₂ (g₁₂ • e₁₂) := by
    refine Eq.trans ?_
      (stalkModule_germ_smul Y.toRingedSpace L.val y (D₁ ⊓ D₂) hy₁₂ g₁₂ e₁₂).symm
    have h1 : ringGerm Y.toRingedSpace y (D₁ ⊓ D₂) hy₁₂ g₁₂ = a :=
      (Y.presheaf.germ_res_apply (homOfLE (inf_le_right : D₁ ⊓ D₂ ≤ D₂)) y hy₁₂ g₂).trans hg₂
    have h2 : grpGerm Y.toRingedSpace L.val y (D₁ ⊓ D₂) hy₁₂ e₁₂ =
        grpGerm Y.toRingedSpace L.val y D₁ hy₁ e₁ :=
      TopCat.Presheaf.germ_res_apply L.presheaf
        (homOfLE (inf_le_left : D₁ ⊓ D₂ ≤ D₁)) y hy₁₂ e₁
    have h3 : grpGerm Y.toRingedSpace L.val y (D₁ ⊓ D₂) hy₁₂ (s.eval (op (D₁ ⊓ D₂))) =
        grpGerm Y.toRingedSpace L.val y D₁ hy₁ (s.eval (op D₁)) :=
      (Stacks.SheafOfModules.grpGerm_eval s y _ hy₁₂).trans
        (Stacks.SheafOfModules.grpGerm_eval s y _ hy₁).symm
    rw [h3, h1, h2]
    exact ha.symm
  obtain ⟨W, hyW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq L.presheaf y hy₁₂ hy₁₂
    (s.eval (op (D₁ ⊓ D₂))) (g₁₂ • e₁₂) hgerm
  obtain rfl : iU = iV := Subsingleton.elim _ _
  have hWD₁ : W ≤ D₁ := (leOfHom iU).trans inf_le_left
  have hs' := eval_eq_smul_map L s iU.op g₁₂ e₁₂ hW
  refine ⟨W, hyW, L.presheaf.map iU.op e₁₂, Y.presheaf.map iU.op g₁₂, hs', fun x hx => ?_⟩
  · have hxD₁ : x ∈ D₁ := hWD₁ hx
    let L' : _root_.SheafOfModules (structureSheafRing Y.toRingedSpace) := L
    have hcomp : (stalkMapL Y.toRingedSpace
          (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)).val L'.val
          (L'.unitHomEquiv.symm s).val x) ∘
          (Stacks.SheafOfModules.unitStalkLinearEquiv Y.toRingedSpace x) =
        LinearMap.toSpanSingleton (ringStalk Y.toRingedSpace x)
          (grpStalk Y.toRingedSpace L'.val x)
          (Stacks.SheafOfModules.globalGerm L' s x) :=
      funext (Stacks.SheafOfModules.stalkMapL_unitStalkLinearEquiv L' s x)
    have hglob : Stacks.SheafOfModules.globalGerm L' s x =
        ringGerm Y.toRingedSpace x W hx (Y.presheaf.map iU.op g₁₂) •
          grpGerm Y.toRingedSpace L'.val x D₁ hxD₁ e₁ := by
      refine (Stacks.SheafOfModules.grpGerm_eval s x W hx).symm.trans ?_
      refine (congrArg (grpGerm Y.toRingedSpace L'.val x W hx) hs').trans ?_
      refine (stalkModule_germ_smul Y.toRingedSpace L'.val x W hx _ _).trans ?_
      congr 1
      exact (TopCat.Presheaf.germ_res_apply L.presheaf iU x hx e₁₂).trans
        (TopCat.Presheaf.germ_res_apply L.presheaf _ x _ e₁)
    have hkey : Function.Bijective (LinearMap.toSpanSingleton (ringStalk Y.toRingedSpace x)
        (grpStalk Y.toRingedSpace L'.val x)
          (grpGerm Y.toRingedSpace L'.val x D₁ hxD₁ e₁)) := key x hxD₁
    have h1 : x ∈ sectionIsomorphismLocus L s ↔ Function.Bijective (stalkMapL Y.toRingedSpace
          (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)).val L'.val
          (L'.unitHomEquiv.symm s).val x) :=
      mem_sectionIsomorphismLocus_iff_bijective_stalkMapL L s x
    have h2 : Function.Bijective (stalkMapL Y.toRingedSpace
          (SheafOfModules.unit (structureSheafRing Y.toRingedSpace)).val L'.val
          (L'.unitHomEquiv.symm s).val x) ↔
        Function.Bijective (LinearMap.toSpanSingleton (ringStalk Y.toRingedSpace x)
          (grpStalk Y.toRingedSpace L'.val x)
          (Stacks.SheafOfModules.globalGerm L' s x)) := by
      rw [← hcomp]
      exact (Function.Bijective.of_comp_iff _
        (Stacks.SheafOfModules.unitStalkLinearEquiv Y.toRingedSpace x).bijective).symm
    rw [hglob] at h2
    exact h1.trans (h2.trans ((bijective_toSpanSingleton_smul_iff_isUnit hkey _).trans
      (Scheme.mem_basicOpen Y _ x hx).symm))

/-- The restriction of `s` to `V`, evaluated on an open `D` of `V`, is `s` evaluated on the image
of `D` in `X`. -/
theorem restrictSection_eval {X : Scheme.{u}} (V : X.Opens) (F : X.Modules) (s : F.sections)
    (D : V.toScheme.Opens) :
    (restrictSection V F s).eval (op D) = s.eval (op (V.ι ''ᵁ D)) := by
  have hhom : ((Scheme.Modules.restrictUnitIso V.ι).hom.val.app (op D)).hom
      (1 : Γ(X, V.ι ''ᵁ D)) = (1 : Γ(V, D)) :=
    map_one (V.ι.appIso D).hom.hom
  have hinv : ((Scheme.Modules.restrictUnitIso V.ι).inv.val.app (op D)).hom
      (1 : Γ(V, D)) = (1 : Γ(X, V.ι ''ᵁ D)) := by
    rw [← hhom]
    exact congrArg (fun f => (f.val.app (op D)).hom (1 : Γ(X, V.ι ''ᵁ D)))
      (Scheme.Modules.restrictUnitIso V.ι).hom_inv_id
  have h1 : (restrictSection V F s).eval (op D) =
      (((Scheme.Modules.restrictFunctor V.ι).map (F.unitHomEquiv.symm s)).val.app (op D)).hom
        (((Scheme.Modules.restrictUnitIso V.ι).inv.val.app (op D)).hom (1 : Γ(V, D))) := rfl
  rw [h1, hinv]
  have h2 := SheafOfModules.unitHomEquiv_apply_coe F (F.unitHomEquiv.symm s) (op (V.ι ''ᵁ D))
  rw [Equiv.apply_symm_apply] at h2
  exact h2.symm

/-- A point lies in `sectionIsomorphismLocus F s` if and only if the stalk map `stalkMapOfHom` of
the morphism `𝒪_Y ⟶ ℱ` determined by `s` is an isomorphism there. -/
theorem mem_sectionIsomorphismLocus_iff_isIso_stalkMapOfHom (F : Y.Modules) (s : F.sections)
    (y : Y) :
    y ∈ sectionIsomorphismLocus F s ↔ IsIso (stalkMapOfHom (F.unitHomEquiv.symm s) y) :=
  Iff.rfl

/-- The isomorphism locus of the restriction of `s` to an open `V` is the preimage of the
isomorphism locus of `s` under the inclusion `V ⟶ Y`. -/
theorem mem_sectionIsomorphismLocus_restrict_iff (V : Y.Opens) (F : Y.Modules) (s : F.sections)
    (w : V.toScheme) :
    w ∈ sectionIsomorphismLocus ((Scheme.Modules.restrictFunctor V.ι).obj F)
        (restrictSection V F s) ↔
      V.ι.base w ∈ sectionIsomorphismLocus F s := by
  rw [mem_sectionIsomorphismLocus_iff_isIso_stalkMapOfHom,
    mem_sectionIsomorphismLocus_iff_isIso_stalkMapOfHom,
    ← isIso_stalkMapOfHom_restrictFunctor_map_iff V.ι (F.unitHomEquiv.symm s) w,
    unitHomEquiv_symm_restrictSection]
  have hmc : stalkMapOfHom ((Scheme.Modules.restrictUnitIso V.ι).inv ≫
        (Scheme.Modules.restrictFunctor V.ι).map (F.unitHomEquiv.symm s)) w =
      stalkMapOfHom ((Scheme.Modules.restrictUnitIso V.ι).inv) w ≫
        stalkMapOfHom ((Scheme.Modules.restrictFunctor V.ι).map (F.unitHomEquiv.symm s)) w :=
    (Scheme.Modules.toPresheaf V.toScheme ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} w).map_comp _ _
  have hinv : IsIso (Scheme.Modules.restrictUnitIso V.ι).inv :=
    ⟨⟨(Scheme.Modules.restrictUnitIso V.ι).hom,
      (Scheme.Modules.restrictUnitIso V.ι).inv_hom_id,
      (Scheme.Modules.restrictUnitIso V.ι).hom_inv_id⟩⟩
  have hi : IsIso (stalkMapOfHom ((Scheme.Modules.restrictUnitIso V.ι).inv) w) :=
    Functor.map_isIso (Scheme.Modules.toPresheaf V.toScheme ⋙
      TopCat.Presheaf.stalkFunctor Ab.{u} w) _
  rw [hmc]
  exact ⟨fun _ => IsIso.of_isIso_comp_left
    (stalkMapOfHom ((Scheme.Modules.restrictUnitIso V.ι).inv) w) _, fun _ => inferInstance⟩

/-- Let `V` be an open on which `ℱ` is invertible. Inside any neighbourhood `N` of a point `y` of
`V` there is an affine open `D ∋ y`, a section `e` of `ℱ` over `D` and a function `g` on `D` with
`s|_D = g e`, such that the isomorphism locus of `s` meets `D` in `D(g)`. -/
theorem exists_affine_sectionLocusChart {X : Scheme.{u}} (F : X.Modules) (s : F.sections) (V :
    X.Opens)
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.toRingedSpace.presheaf
      (structureSheafRing V.toScheme.toRingedSpace).property
      ((Scheme.Modules.restrictFunctor V.ι).obj F))
    {y : X} (hy : y ∈ V) {N : X.Opens} (hyN : y ∈ N) :
    ∃ D : X.Opens, IsAffineOpen D ∧ y ∈ D ∧ D ≤ N ∧ ∃ (e : Γ(F, D)) (g : Γ(X, D)),
      s.eval (op D) = g • e ∧
        ∀ x ∈ D, (x ∈ sectionIsomorphismLocus F s ↔ x ∈ X.basicOpen g) := by
  have := hV
  obtain ⟨D', hyD', e', g', hs', hloc'⟩ :=
    exists_sectionLocusChart_of_isInvertible ((Scheme.Modules.restrictFunctor V.ι).obj F)
      (restrictSection V F s) ⟨y, hy⟩
  have hyD₀ : y ∈ V.ι ''ᵁ D' := ⟨⟨y, hy⟩, hyD', rfl⟩
  obtain ⟨D, hDaff, hyD, hDle⟩ := (Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show y ∈ (V.ι ''ᵁ D') ⊓ N from ⟨hyD₀, hyN⟩)
  have hDD₀ : D ≤ V.ι ''ᵁ D' := hDle.trans inf_le_left
  have hsm : (g' • e' : Γ((Scheme.Modules.restrictFunctor V.ι).obj F, D')) =
      (@id Γ(X, V.ι ''ᵁ D') g') • (@id Γ(F, V.ι ''ᵁ D') e') := by
    have h := Scheme.Modules.smul_restrictAppIso_hom_apply V.ι F D' g' e'
    rwa [Scheme.Opens.ι_appIso] at h
  have hs₀ : s.eval (op (V.ι ''ᵁ D')) =
      (@id Γ(X, V.ι ''ᵁ D') g') • (@id Γ(F, V.ι ''ᵁ D') e') :=
    ((restrictSection_eval V F s D').symm.trans hs').trans hsm
  refine ⟨D, hDaff, hyD, hDle.trans inf_le_right,
    F.presheaf.map (homOfLE hDD₀).op (@id Γ(F, V.ι ''ᵁ D') e'),
    X.presheaf.map (homOfLE hDD₀).op (@id Γ(X, V.ι ''ᵁ D') g'),
    eval_eq_smul_map F s (homOfLE hDD₀).op _ _ (congrArg _ hs₀), fun x hx => ?_⟩
  · obtain ⟨x', hx'D', rfl⟩ := hDD₀ hx
    have hb : X.basicOpen (X.presheaf.map (homOfLE hDD₀).op (@id Γ(X, V.ι ''ᵁ D') g')) =
        D ⊓ X.basicOpen (@id Γ(X, V.ι ''ᵁ D') g') :=
      Scheme.basicOpen_res X _ _
    rw [hb]
    refine (mem_sectionIsomorphismLocus_restrict_iff V F s x').symm.trans
      ((hloc' x' hx'D').trans ?_)
    exact Scheme.Opens.mem_basicOpen_toScheme.trans ⟨fun h => ⟨hx, h⟩, fun h => h.2⟩

end AlgebraicGeometry

end
