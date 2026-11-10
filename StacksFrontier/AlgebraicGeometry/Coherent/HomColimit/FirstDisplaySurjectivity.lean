module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.FirstDisplayInjectivity
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowTensorIso
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.TensorSheafHom
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The first display of Tag 01YB

Let `X` be a Noetherian scheme, let `I` be a quasi-coherent sheaf of ideals, let `U = X \ V(I)`,
let `G` be a coherent `𝒪_X`-module and let `F` be a quasi-coherent `𝒪_X`-module. This file proves
that the canonical map `canonicalMapToHomRestrict`

`colim_n Hom_{𝒪_X}(Iⁿ G, F) ⟶ Hom_{𝒪_U}(G|_U, F|_U)`

is bijective, which is the first display of [Stacks, Tag 01YB].

Given `θ : G|_U ⟶ F|_U` and a morphism `ψ : Iⁿ ⟶ SheafHom_{𝒪_X}(G, F)` with `ψ(1) = θ`, and `m`
such that `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G` is an isomorphism, the morphism `Iⁿ ⊗_{𝒪_X} G ⟶ F`
attached to `ψ`, restricted to `Iᵐ(Iⁿ ⊗_{𝒪_X} G)` and read through that isomorphism, is a morphism
`φ' : I^{n+m} G ⟶ F` restricting to `θ` on `U`.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.overApp`: a morphism `G|_U ⟶ F|_U`, read on the
  sections over an open contained in `U`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.transferHom`: **the morphism
  `φ' : I^{n+m} G ⟶ F`** attached to a morphism `ψ : Iⁿ ⟶ SheafHom_{𝒪_X}(G, F)` and an `m` for
  which `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G` is an isomorphism.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.over_hom_ext`: two morphisms `G|_U ⟶ F|_U`
  agreeing on sections are equal.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.eq_smul_map_oneSection`: over an open disjoint
  from the support of `I` a section of `Iⁿ` is its own value times the unit section.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.evalSection_app_idealPow`: consequently
  `ψ(a)(g) = a θ(g)` for `a` a section of `Iⁿ` over an open contained in `U`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.tensorHomToModule_app_eq_overApp`: **over an open
  contained in `U` the morphism `Iⁿ ⊗_{𝒪_X} G ⟶ F` attached to `ψ` is `θ` composed with
  multiplication of sections.**
* `Stacks.AlgebraicGeometry.IdealPowerColimit.homRestrict_transferHom`: `φ'` restricts to `θ`
  on `U`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_homRestrict_eq`: **the first display in
  existence form** — every morphism `G|_U ⟶ F|_U` is the restriction of a morphism `I^k G ⟶ F`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToHomRestrict_surjective`:
  surjectivity of the first display.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToHomRestrict_bijective`: **the first
  display of [Stacks, Tag 01YB].**

## Implementation notes

The morphism `Iⁿ ⊗_{𝒪_X} G ⟶ F` attached to `ψ` is
`Stacks.AlgebraicGeometry.InternalHomModules.tensorHomToModule`, for the tensor product
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`.

A section of `G` over an open `V ≤ U` is a section of `G|_U` over the object `V ⟶ U` of the slice
site, and `overApp` is the component of a morphism `G|_U ⟶ F|_U` there.

`transferHom` precomposes with the inverse of `Iᵐ(Iⁿ ⊗_{𝒪_X} G) ⟶ I^{n+m} G`, and that inverse is
evaluated through `app_inv_app`.

## References

* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
* [Stacks Project, Tag 01CN](https://stacks.math.columbia.edu/tag/01CN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealProduct
open Stacks.AlgebraicGeometry.InternalHomModules
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.SheafOfModules

noncomputable section

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}} {A G F : X.Modules}

/-! ### Generalities on morphisms of modules -/

/-- Applying a composite of morphisms of modules to a section. -/
public theorem app_comp_apply {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (V : X.Opens)
    (x : Γ(M, V)) : (f ≫ g).app V x = g.app V (f.app V x) :=
  congr($(Scheme.Modules.Hom.comp_app (U := V) f g) x)

/-- An isomorphism of modules is undone by its inverse on sections. -/
public theorem app_inv_app {M N : X.Modules} (f : M ⟶ N) (hf : IsIso f) (V : X.Opens)
    (w : Γ(N, V)) : f.app V ((@inv _ _ _ _ _ hf).app V w) = w :=
  congrArg (fun q : N ⟶ N ↦ ConcreteCategory.hom (q.app V) w) (@IsIso.inv_hom_id _ _ _ _ f hf)

/-! ### Morphisms `G|_U ⟶ F|_U` on sections -/

/-- A morphism `G|_U ⟶ F|_U`, read on the sections over an open `V` contained in `U`: its
component at the object `V ⟶ U` of the slice site over `U`. -/
public noncomputable def overApp {U : X.Opens} (θ : G.over U ⟶ F.over U) {V : X.Opens}
    (hVU : V ≤ U) (g : Γ(G, V)) : Γ(F, V) :=
  (θ.val.app (op (Over.mk (homOfLE hVU)))).hom g

/-- A morphism `G|_U ⟶ F|_U` is additive on sections. -/
public theorem overApp_add {U : X.Opens} (θ : G.over U ⟶ F.over U) {V : X.Opens} (hVU : V ≤ U)
    (g g' : Γ(G, V)) : overApp θ hVU (g + g') = overApp θ hVU g + overApp θ hVU g' :=
  map_add (θ.val.app (op (Over.mk (homOfLE hVU)))).hom g g'

/-- A morphism `G|_U ⟶ F|_U` is linear on sections. -/
public theorem overApp_smul {U : X.Opens} (θ : G.over U ⟶ F.over U) {V : X.Opens} (hVU : V ≤ U)
    (r : Γ(X, V)) (g : Γ(G, V)) : overApp θ hVU (r • g) = r • overApp θ hVU g :=
  (θ.val.app (op (Over.mk (homOfLE hVU)))).hom.map_smul r g

/-- A morphism `G|_U ⟶ F|_U` takes a finite sum of sections to the sum of the values. -/
public theorem overApp_sum {U : X.Opens} (θ : G.over U ⟶ F.over U) {V : X.Opens} (hVU : V ≤ U)
    {k : ℕ} (g : Fin k → Γ(G, V)) :
    overApp θ hVU (∑ j, g j) = ∑ j, overApp θ hVU (g j) :=
  map_sum (θ.val.app (op (Over.mk (homOfLE hVU)))).hom g Finset.univ

/-- A morphism `G|_U ⟶ F|_U` commutes with restriction to a smaller open contained in `U`. -/
public theorem overApp_naturality {U : X.Opens} (θ : G.over U ⟶ F.over U) {V V' : X.Opens}
    (hVU : V ≤ U) (hV'V : V' ≤ V) (g : Γ(G, V)) :
    F.presheaf.map (homOfLE hV'V).op (overApp θ hVU g)
      = overApp θ (hV'V.trans hVU) (G.presheaf.map (homOfLE hV'V).op g) :=
  (PresheafOfModules.naturality_apply θ.val
    (Over.homMk (homOfLE hV'V) (Subsingleton.elim _ _) :
      Over.mk (homOfLE (hV'V.trans hVU)) ⟶ Over.mk (homOfLE hVU)).op g).symm

/-- **Two morphisms `G|_U ⟶ F|_U` agreeing on the sections over every open contained in `U` are
equal.** -/
public theorem over_hom_ext {U : X.Opens} {θ θ' : G.over U ⟶ F.over U}
    (h : ∀ (V : X.Opens) (hVU : V ≤ U) (g : Γ(G, V)), overApp θ hVU g = overApp θ' hVU g) :
    θ = θ' := by
  ext W g
  exact h W.unop.left (leOfHom W.unop.hom) g

/-- The restriction to `U` of a morphism out of `Iⁿ G`, read on sections: it sends a section `g`
of `G` over an open contained in `U` to `φ(g)`. -/
public theorem overApp_homRestrict (I : X.IdealSheafData) {n : ℕ} {U : X.Opens}
    (hU : Disjoint (U : Set X) (I.support : Set X)) (φ : idealPowSmul I n G ⟶ F)
    {V : X.Opens} (hVU : V ≤ U) (g : Γ(G, V)) :
    overApp (homRestrict I hU φ) hVU g
      = φ.app V ⟨g, mem_idealPowerMultiple_of_le I n G hU hVU g⟩ :=
  val_homRestrict_app I hU φ (op (Over.mk (homOfLE hVU))) g

/-! ### A morphism into a sheaf Hom, read off away from the support of `I` -/

/-- Over an open disjoint from the support of `I` a section of `Iⁿ` is its own value times the unit
section. -/
public theorem eq_smul_map_oneSection (I : X.IdealSheafData) (n : ℕ) {V : X.Opens}
    (hVU : V ≤ (I.support.compl : X.Opens)) (a : Γ(idealPow I n, V)) {r : Γ(X, V)}
    (hr : (a.1 : Γ(X, V)) = r) :
    a = r • (idealPow I n).presheaf.map (homOfLE hVU).op (oneSection I n) := by
  refine Subtype.ext ?_
  change (a.1 : Γ(X, V))
    = r * X.presheaf.map (homOfLE hVU).op (1 : Γ(X, (I.support.compl : X.Opens)))
  rwa [map_one, mul_one]

/-- If `ψ : Iⁿ ⟶ SheafHom_{𝒪_X}(G, F)` has `θ` as its value on the unit section over
`U = X \ V(I)`, then over an open `V ≤ U` the morphism `ψ(a) : G|_V ⟶ F|_V` attached to a section
`a` of `Iⁿ` with value `r` is `r θ`, that is `ψ(a)(g) = r θ(g)`. -/
public theorem evalSection_app_idealPow (I : X.IdealSheafData) (n : ℕ)
    {θ : G.over (I.support.compl : X.Opens) ⟶ F.over (I.support.compl : X.Opens)}
    {ψ : idealPow I n ⟶ sheafHomModules G F}
    (hψ : ψ.app (I.support.compl : X.Opens) (oneSection I n) = θ.val)
    {V : X.Opens} (hVU : V ≤ (I.support.compl : X.Opens)) (a : Γ(idealPow I n, V))
    {r : Γ(X, V)} (hr : (a.1 : Γ(X, V)) = r) (g : Γ(G, V)) :
    evalSection X.sheaf.obj G.val F.val (op V) (ψ.app V a) g = r • overApp θ hVU g := by
  have h1 : ψ.app V a
      = r • (sheafHomModules G F).presheaf.map (homOfLE hVU).op θ.val := by
    refine Eq.trans (congrArg (ConcreteCategory.hom (ψ.app V))
      (eq_smul_map_oneSection I n hVU a hr)) ?_
    refine Eq.trans (Scheme.Modules.Hom.app_smul ψ r _) ?_
    refine congrArg (fun w : Γ(sheafHomModules G F, V) ↦ r • w) ?_
    refine Eq.trans (app_naturality ψ hVU (oneSection I n)).symm ?_
    exact congrArg (ConcreteCategory.hom
      ((sheafHomModules G F).presheaf.map (homOfLE hVU).op)) hψ
  exact (congrArg (fun w : Γ(sheafHomModules G F, V) ↦
    evalSection X.sheaf.obj G.val F.val (op V) w g) h1).trans
    (evalSection_smul_left X.sheaf.obj G.val F.val (op V) r _ g)

/-- **Over an open contained in `U = X \ V(I)` the morphism `Iⁿ ⊗_{𝒪_X} G ⟶ F` attached to `ψ` is
`θ` composed with multiplication of sections.** -/
public theorem tensorHomToModule_app_eq_overApp (I : X.IdealSheafData) (n : ℕ)
    {θ : G.over (I.support.compl : X.Opens) ⟶ F.over (I.support.compl : X.Opens)}
    {ψ : idealPow I n ⟶ sheafHomModules G F}
    (hψ : ψ.app (I.support.compl : X.Opens) (oneSection I n) = θ.val)
    {V : X.Opens} (hVU : V ≤ (I.support.compl : X.Opens))
    (t : Γ(tensorModules (idealPow I n) G, V)) :
    (tensorHomToModule ψ).app V t
      = overApp θ hVU ((idealPowTensorToModule I n G).app V t) := by
  refine sub_eq_zero.mp (eq_zero_of_locally_zero _ fun p hp ↦ ?_)
  obtain ⟨V', hV'V, hpV', k, a, b, heq⟩ :=
    exists_affineOpen_sum_toTensorSheafSection (idealPow I n) G V t p hp
  obtain ⟨r, hrdef⟩ : ∃ r : Fin k → Γ(X, V'.1), ∀ j, ((a j).1 : Γ(X, V'.1)) = r j :=
    ⟨fun j ↦ ((a j).1 : Γ(X, V'.1)), fun _ ↦ rfl⟩
  refine ⟨V'.1, hV'V, hpV', ?_⟩
  refine Eq.trans (map_sub (ConcreteCategory.hom
    (F.presheaf.map (homOfLE hV'V).op)) _ _) ?_
  refine sub_eq_zero.mpr ?_
  have hL : F.presheaf.map (homOfLE hV'V).op ((tensorHomToModule ψ).app V t)
      = ∑ j, r j • overApp θ (hV'V.trans hVU) (b j) := by
    rw [app_naturality (tensorHomToModule ψ) hV'V t, heq]
    refine (map_sum (ConcreteCategory.hom ((tensorHomToModule ψ).app V'.1)) _ Finset.univ).trans
      (Finset.sum_congr rfl fun j _ ↦
      (tensorHomToModule_app_toTensorSheafSection ψ V'.1 (a j) (b j)).trans
        (evalSection_app_idealPow I n hψ (hV'V.trans hVU) (a j) (hrdef j) (b j)))
  have hR : F.presheaf.map (homOfLE hV'V).op
        (overApp θ hVU ((idealPowTensorToModule I n G).app V t))
      = ∑ j, r j • overApp θ (hV'V.trans hVU) (b j) := by
    rw [overApp_naturality θ hVU hV'V, app_naturality (idealPowTensorToModule I n G) hV'V t, heq]
    refine (congrArg (overApp θ (hV'V.trans hVU))
      (map_sum (ConcreteCategory.hom ((idealPowTensorToModule I n G).app V'.1)) _
        Finset.univ)).trans ((overApp_sum θ (hV'V.trans hVU) _).trans <|
      Finset.sum_congr rfl fun j _ ↦
      (congrArg (overApp θ (hV'V.trans hVU))
        (smulToModule_app_toTensorSheafSection (idealPowInclusion I n) G V'.1 (a j) (b j) (r j)
          (hrdef j))).trans (overApp_smul θ (hV'V.trans hVU) (r j) (b j)))
  exact hL.trans hR.symm

/-! ### The morphism `φ' : I^{n+m} G ⟶ F` -/

/-- The morphism `φ' : I^{n+m} G ⟶ F`: the morphism `Iⁿ ⊗_{𝒪_X} G ⟶ F` attached to `ψ`, restricted
to the subsheaf `Iᵐ(Iⁿ ⊗_{𝒪_X} G)` and read through the isomorphism
`Iᵐ(Iⁿ ⊗_{𝒪_X} G) ≅ I^{n+m} G`. -/
public noncomputable def transferHom [G.IsQuasicoherent] (I : X.IdealSheafData) {n : ℕ}
    (ψ : idealPow I n ⟶ sheafHomModules G F) (m : ℕ)
    (hiso : IsIso (idealPowSmulTensorToSmul I n m G)) :
    idealPowSmul I (n + m) G ⟶ F :=
  @inv _ _ _ _ _ hiso ≫
    submoduleι (idealPowerMultiple I m (tensorModules (idealPow I n) G)) ≫
      tensorHomToModule ψ

/-- If `ψ(1) = θ`, then `transferHom I ψ m hiso` restricts to `θ` on `U = X \ V(I)`. -/
public theorem homRestrict_transferHom [G.IsQuasicoherent] (I : X.IdealSheafData) {n : ℕ}
    {θ : G.over (I.support.compl : X.Opens) ⟶ F.over (I.support.compl : X.Opens)}
    {ψ : idealPow I n ⟶ sheafHomModules G F}
    (hψ : ψ.app (I.support.compl : X.Opens) (oneSection I n) = θ.val) (m : ℕ)
    (hiso : IsIso (idealPowSmulTensorToSmul I n m G)) :
    homRestrict I (disjoint_supportCompl_support I) (transferHom I ψ m hiso) = θ := by
  refine over_hom_ext fun V hVU g ↦ ?_
  refine Eq.trans (overApp_homRestrict I (disjoint_supportCompl_support I)
    (transferHom I ψ m hiso) hVU g) ?_
  refine Eq.trans (app_comp_apply (@inv _ _ _ _ _ hiso) _ V _) ?_
  refine Eq.trans (app_comp_apply (submoduleι
    (idealPowerMultiple I m (tensorModules (idealPow I n) G))) (tensorHomToModule ψ) V _) ?_
  refine Eq.trans (tensorHomToModule_app_eq_overApp I n hψ hVU _) ?_
  refine congrArg (overApp θ hVU) ?_
  refine Eq.trans (app_comp_apply (submoduleι
    (idealPowerMultiple I m (tensorModules (idealPow I n) G)))
      (idealPowTensorToModule I n G) V _).symm ?_
  refine Eq.trans (val_idealPowSmulTensorToSmul_app I n m G V _).symm ?_
  exact congrArg (fun y : Γ(idealPowSmul I (n + m) G, V) ↦ (y.1 : Γ(G, V)))
    (app_inv_app (idealPowSmulTensorToSmul I n m G) hiso V _)

/-! ### The first display -/

/-- Let `X` be a Noetherian scheme, `I` a quasi-coherent sheaf of ideals, `G` a coherent and `F` a
quasi-coherent `𝒪_X`-module and `U = X \ V(I)`. Every morphism `G|_U ⟶ F|_U` is the restriction of
a morphism `I^k G ⟶ F` for some `k`. -/
public theorem exists_homRestrict_eq [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData)
    (G F : X.Modules) [G.IsCoherent] [F.IsQuasicoherent]
    (θ : G.over (I.support.compl : X.Opens) ⟶ F.over (I.support.compl : X.Opens)) :
    ∃ (k : ℕ) (φ : idealPowSmul I k G ⟶ F),
      homRestrict I (disjoint_supportCompl_support I) φ = θ := by
  have hGqc : G.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent G
  have := isQuasicoherent_sheafHomModules G F (isFinitePresentation_of_isCoherent' G)
  obtain ⟨n, ψ, hψ⟩ := exists_hom_idealPow_app_oneSection_eq_of_isQuasicoherent I
    (sheafHomModules G F) θ.val
  obtain ⟨c, hc⟩ := exists_isIso_idealPowSmulTensorToSmul I n G ‹G.IsCoherent›
  exact ⟨n + c, transferHom I ψ c (hc c le_rfl), homRestrict_transferHom I hψ c (hc c le_rfl)⟩

/-- For `X` Noetherian, `G` coherent and `F` quasi-coherent, the canonical map
`colim_n Hom_{𝒪_X}(Iⁿ G, F) ⟶ Hom_{𝒪_U}(G|_U, F|_U)` is surjective. -/
public theorem canonicalMapToHomRestrict_surjective [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (G F : X.Modules) [G.IsCoherent] [F.IsQuasicoherent] :
    Function.Surjective (canonicalMapToHomRestrict I G F) := by
  intro θ
  obtain ⟨k, φ, hφ⟩ := exists_homRestrict_eq I G F θ
  exact ⟨Limits.colimit.ι (idealPowSmulHomSystem I G F) k φ,
    (canonicalMapToHomRestrict_ι I G F k φ).trans hφ⟩

/-- For a Noetherian scheme `X`, a quasi-coherent sheaf of ideals `I` with complement
`U = X \ V(I)`, a coherent `𝒪_X`-module `G` and a quasi-coherent `𝒪_X`-module `F`, the canonical
map

`colim_n Hom_{𝒪_X}(Iⁿ G, F) ⟶ Hom_{𝒪_U}(G|_U, F|_U)`

is bijective. -/
@[stacks 01YB "first display", sga "2 II Theorem6" "b)"]
public theorem canonicalMapToHomRestrict_bijective [AlgebraicGeometry.IsNoetherian X]
    (I : X.IdealSheafData) (G F : X.Modules) [G.IsCoherent] [F.IsQuasicoherent] :
    Function.Bijective (canonicalMapToHomRestrict I G F) :=
  ⟨canonicalMapToHomRestrict_injective I G F, canonicalMapToHomRestrict_surjective I G F⟩

end Stacks.AlgebraicGeometry.IdealPowerColimit

end

end
