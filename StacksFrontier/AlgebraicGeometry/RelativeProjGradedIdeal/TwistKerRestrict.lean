module

public import StacksFrontier.Algebra.Module.FaithfullyFlat.PreimageBaseChange
public import StacksFrontier.AlgebraicGeometry.AffineOpenSectionsBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.ModulesOverOpen
public import StacksFrontier.AlgebraicGeometry.PullbackSections.AffineGeneration
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Descent
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Stalk
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.TwistKerBaseChange
public import StacksFrontier.AlgebraicGeometry.RelativeProjGradedIdeal.TwistRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.TwistComparison

/-!
# Restriction of the graded ideal of Tag 0801 along a base change, over arbitrary opens

Let `hs : Y' ⟶ Y` be a morphism of schemes, `A` a quasi-coherent graded `𝒪_Y`-algebra, `A₁` one
on `Y'` with an isomorphism `Φ : A₁ ≅ hs^*A` of sheaves of graded algebras, and
`pc : Proj_{Y'}(A₁) ⟶ Proj_Y(A)` the identification `Proj(A₁) ≅ Proj(hs^*A)` followed by the
base-change morphism of Tag 01O3. Let `i : Z ⟶ Proj_Y(A)` and `i₁ : Z₁ ⟶ Proj_{Y'}(A₁)` be closed
immersions with `g : Z₁ ⟶ Z` over `pc`. This file compares the graded ideals of Tag 0801 of `Z`
and `Z₁`
(`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistKerGradedIdeal`): the restriction
`a ↦ Φ⁻¹(hs^*a)` carries the first into the second, and when the square of `g` over `pc` is
cartesian and `hs` is flat, over affine opens the second is spanned by the restrictions of the
first. The case of global sections over affine bases, read through the equations of `Z`, is
`StacksFrontier/AlgebraicGeometry/RelativeProjGradedIdeal/TwistKerBaseChange.lean`; this file works
over arbitrary opens `W₁ ≤ hs⁻¹W`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.twistKerRestrict`: the restriction
  `Γ(W, A_n) → Γ(W₁, A₁_n)`, `a ↦ Φ⁻¹(hs^*a)`, for `W₁ ≤ hs⁻¹W`.
* `Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.pullbackSquareTwistMap`: the comparison
  `g^*(i^*𝒪(n)) ≅ i₁^*(pc^*𝒪(n)) ⟶ i₁^*𝒪₁(n)` of the targets of the two degreewise maps.

## Main results

* `…twistKerRestrict_add`, `…twistKerRestrict_smul`: the restriction is additive and semilinear
  along `hs.appLE W W₁`.
* `…mem_twistKer_restrict`: **the restriction carries the ideal of `Z` into the ideal of `Z₁`**.
* `…twistKer_le_span_restrict`: **for `hs` flat, the square cartesian and `W`, `W₁` affine, the
  ideal of `Z₁` over `W₁` is spanned by the restrictions of the ideal of `Z` over `W`.**

## Implementation notes

The degreewise map of Tag 0801 for `A₁` on a restriction is the comparison of the targets applied
to the pullback along `g` of the degreewise map for `A`
(`twistRestrictMapNat_twistKerRestrict`); this is the compatibility of the twists with `ψ`
(`Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist`
`.congrBaseChangePsi_comp_congrBaseChangeTwistIso`) read on sections, and it is proved once at
free variables (`pullbackSection_psi_eq_pullbackSquareTwistMap`). The flat case is then
degree-zero flat base change for the direct image along `Z ⟶ Y`
(`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`), the
description of sections of a pullback over a pair of affine opens
(`AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`), and the flat base change of a kernel
(`LinearMap.ker_le_span_image_ker_of_flat`), assembled at free variables in
`app_eq_zero_mem_span_of_isPullback`; the cartesian square of Stacks 084B (3) is
`Stacks.AlgebraicGeometry.RelativeProjGradedIdeal.isPullback_comparison`.

## References

* [Stacks Project, Tag 0801](https://stacks.math.columbia.edu/tag/0801)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjBaseChangeTwist
open Stacks.AlgebraicGeometry (Tag07ZGTwist.twistAlgebra GluedTwistAlgebra.twistDataOfGradedAlgebra)
open scoped TensorProduct ChangeOfRings

namespace Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

universe u

/-! ### Pulled-back sections over a pair of affine opens -/

section AffinePullback

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
  (hU : IsAffineOpen U) {V : Y.Opens} (hV : IsAffineOpen V) (hVU : V ≤ f ⁻¹ᵁ U)
  {F' : Y.Modules} (e : (Scheme.Modules.pullback f).obj F ⟶ F') [IsIso e]

include hU hV in
/-- Over a pair of affine opens, the images under an isomorphism `e` of the pulled-back sections
span the sections of the target of `e`. -/
theorem span_range_app_pullbackSection_eq_top :
    Submodule.span Γ(Y, V) (Set.range fun a : Γ(F, U) =>
      e.app V (Scheme.Modules.pullbackSection f F U V hVU a)) = ⊤ := by
  let ε := Scheme.Modules.sectionsLinearMap e V
  have hrange : (Set.range fun a : Γ(F, U) =>
      e.app V (Scheme.Modules.pullbackSection f F U V hVU a)) =
      ε '' Scheme.Modules.pullbackSectionRange f F U V hVU :=
    Set.range_comp ε _
  rw [hrange, Submodule.span_image,
    Scheme.Modules.span_range_pullbackSection_eq_top f F hU hV hVU, Submodule.map_top,
    LinearMap.range_eq_top]
  exact Function.RightInverse.surjective (g := (inv e).val.app (op V))
    (fun x => congrArg (fun φ => φ.val.app (op V) x) (IsIso.inv_hom_id e))

include hU hV in
/-- **Over a pair of affine opens, pulling back followed by an isomorphism is a base change.**
For `U ⊆ X`, `V ⊆ Y` affine with `V ≤ f⁻¹U`, `F` quasi-coherent and `e : f^*F ≅ F'`, the
`Γ(X, U)`-linear map `Γ(F, U) → Γ(F', V)`, `a ↦ e(f^*a)`, has bijective base change along
`Γ(X, U) → Γ(Y, V)`: this is `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso` followed by
`e`. -/
theorem bijective_liftBaseChange_app_pullbackSection :
    letI := (f.appLE U V hVU).hom.toAlgebra
    letI : Module Γ(X, U) Γ(F', V) := Module.compHom _ (f.appLE U V hVU).hom
    haveI : IsScalarTower Γ(X, U) Γ(Y, V) Γ(F', V) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ∀ (ν : Γ(F, U) →ₗ[Γ(X, U)] Γ(F', V)),
      (∀ y, ν y = e.app V (Scheme.Modules.pullbackSection f F U V hVU y)) →
        Function.Bijective (ν.liftBaseChange Γ(Y, V)) := by
  let := (f.appLE U V hVU).hom.toAlgebra
  let : Module Γ(X, U) Γ(F', V) := Module.compHom _ (f.appLE U V hVU).hom
  have : IsScalarTower Γ(X, U) Γ(Y, V) Γ(F', V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  intro ν hν
  let := Scheme.Modules.pullbackSectionsModule f F U V hVU
  have : IsScalarTower Γ(X, U) Γ(Y, V) Γ((Scheme.Modules.pullback f).obj F, V) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let π := Scheme.Modules.pullbackSectionₗ f F U V hVU
  have hπ : IsBaseChange Γ(Y, V) π :=
    AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso (f.appLE U V hVU).hom rfl
      (affinePullbackSectionsBaseChangeIso f F hU hV hVU) π
      (affinePullbackSectionsBaseChangeIso_one_tmul f F hU hV hVU)
  let ε := Scheme.Modules.sectionsLinearMap e V
  have hε : Function.Bijective ε :=
    ⟨Function.LeftInverse.injective (g := (inv e).val.app (op V))
      (fun x => congrArg (fun φ => φ.val.app (op V) x) (IsIso.hom_inv_id e)),
     Function.RightInverse.surjective (g := (inv e).val.app (op V))
      (fun x => congrArg (fun φ => φ.val.app (op V) x) (IsIso.inv_hom_id e))⟩
  have key : ∀ t, ν.liftBaseChange Γ(Y, V) t = ε (hπ.equiv t) := by
    intro t
    induction t with
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
    | tmul b y =>
        rw [LinearMap.liftBaseChange_tmul, IsBaseChange.equiv_tmul, map_smul, hν]
        rfl
  rw [show (ν.liftBaseChange Γ(Y, V) : _ → _) = ε ∘ hπ.equiv from funext key]
  exact hε.comp hπ.equiv.bijective

end AffinePullback

/-! ### The flat base change of a kernel, at free variables -/

section FlatKernel

variable {Y Y' X X' : Scheme.{u}} (hs : Y' ⟶ Y) [Flat hs] {q : X ⟶ Y} {q₁ : X' ⟶ Y'}
  {g : X' ⟶ X} (hY : IsPullback g q₁ q hs) [QuasiCompact q] [QuasiSeparated q]
  (G : X.Modules) [G.IsQuasicoherent] {G₁ : X'.Modules}
  (θ : (Scheme.Modules.pullback g).obj G ⟶ G₁) (hθ : IsIso θ)
  {M : Y.Modules} [M.IsQuasicoherent] {M₁ : Y'.Modules}
  (e : (Scheme.Modules.pullback hs).obj M ⟶ M₁) (he : IsIso e)
  (σ : M ⟶ (Scheme.Modules.pushforward q).obj G)
  (σ₁ : M₁ ⟶ (Scheme.Modules.pushforward q₁).obj G₁)

include hY hθ he in
/-- **The kernel of a map into a direct image, along a flat base change, over affine opens.**
Let `σ : M ⟶ q_*G` and `σ₁ : M₁ ⟶ q₁_*G₁` be morphisms over a cartesian square with `hs` flat and
`q` quasi-compact and quasi-separated, `M` and `G` quasi-coherent, compared through isomorphisms
`e : hs^*M ≅ M₁` and `θ : g^*G ≅ G₁` (`h`). Then over affine opens `W₁ ≤ hs⁻¹W` the kernel of `σ₁`
on `W₁` is spanned by the images under `e ∘ hs^*` of the kernel of `σ` on `W`: by degree-zero
flat base change the target of `σ₁` is the base change of the target of `σ`, and over a flat ring
map the kernel of a base change is the base change of the kernel. -/
theorem app_eq_zero_mem_span_of_isPullback {W : Y.Opens} {W₁ : Y'.Opens} (hW : W₁ ≤ hs ⁻¹ᵁ W)
    (hWa : IsAffineOpen W) (hW₁a : IsAffineOpen W₁) (hV : q₁ ⁻¹ᵁ W₁ ≤ g ⁻¹ᵁ (q ⁻¹ᵁ W))
    (h : ∀ a : Γ(M, W), σ₁.val.app (op W₁)
        (e.val.app (op W₁) (Scheme.Modules.pullbackSection hs M W W₁ hW a)) =
      θ.val.app (op (q₁ ⁻¹ᵁ W₁)) (Scheme.Modules.pullbackSection g G (q ⁻¹ᵁ W) (q₁ ⁻¹ᵁ W₁) hV
        (σ.val.app (op W) a)))
    (x : Γ(M₁, W₁)) (hx : σ₁.val.app (op W₁) x = 0) :
    x ∈ Submodule.span Γ(Y', W₁)
      ((fun a => e.app W₁ (Scheme.Modules.pullbackSection hs M W W₁ hW a)) ''
        {a | σ.val.app (op W) a = 0}) := by
  have := hθ
  have := he
  let : Algebra Γ(Y, W) Γ(Y', W₁) := (hs.appLE W W₁ hW).hom.toAlgebra
  have : Module.Flat Γ(Y, W) Γ(Y', W₁) := hs.flat_appLE hWa hW₁a hW
  let : Module Γ(Y, W) Γ(M₁, W₁) := Module.compHom _ (hs.appLE W W₁ hW).hom
  have : IsScalarTower Γ(Y, W) Γ(Y', W₁) Γ(M₁, W₁) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module Γ(Y, W) Γ((Scheme.Modules.pushforward q₁).obj G₁, W₁) :=
    Module.compHom _ (hs.appLE W W₁ hW).hom
  have : IsScalarTower Γ(Y, W) Γ(Y', W₁) Γ((Scheme.Modules.pushforward q₁).obj G₁, W₁) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let := Scheme.Modules.pullbackSectionsModule hs M W W₁ hW
  let := Scheme.Modules.pullbackSectionsModule hs ((Scheme.Modules.pushforward q).obj G) W W₁ hW
  let π := Scheme.Modules.pullbackSectionₗ hs M W W₁ hW
  let π' := Scheme.Modules.pullbackSectionₗ hs ((Scheme.Modules.pushforward q).obj G) W W₁ hW
  let L := (AffinePushforward.baseChangeNatTrans hY.w).app G ≫
    (Scheme.Modules.pushforward q₁).map θ
  have : IsIso ((AffinePushforward.baseChangeNatTrans hY.w).app G) :=
    Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat hY G
  have : IsIso L := IsIso.comp_isIso
  let ρ : Γ(M, W) →ₗ[Γ(Y, W)] Γ(M₁, W₁) :=
    { toFun := fun a => e.app W₁ (π a)
      map_add' := fun a b => (congrArg (e.app W₁) (π.map_add a b)).trans (map_add _ _ _)
      map_smul' := fun r a => (congrArg (e.app W₁) (π.map_smul r a)).trans
        (Scheme.Modules.Hom.app_smul e _ _) }
  let ν : Γ((Scheme.Modules.pushforward q).obj G, W) →ₗ[Γ(Y, W)]
      Γ((Scheme.Modules.pushforward q₁).obj G₁, W₁) :=
    { toFun := fun y => L.app W₁ (π' y)
      map_add' := fun a b => (congrArg (L.app W₁) (π'.map_add a b)).trans (map_add _ _ _)
      map_smul' := fun r a => (congrArg (L.app W₁) (π'.map_smul r a)).trans
        (Scheme.Modules.Hom.app_smul L _ _) }
  have hν := (bijective_liftBaseChange_app_pullbackSection hs ((Scheme.Modules.pushforward q).obj G)
    hWa hW₁a hW L ν (fun _ => rfl)).1
  have hρ := span_range_app_pullbackSection_eq_top hs M hWa hW₁a hW e
  have hh : ∀ a, Scheme.Modules.sectionsLinearMap σ₁ W₁ (ρ a) =
      ν (Scheme.Modules.sectionsLinearMap σ W a) := by
    intro a
    refine (h a).trans ?_
    have hq : q₁ ⁻¹ᵁ (hs ⁻¹ᵁ W) ≤ g ⁻¹ᵁ (q ⁻¹ᵁ W) := fun z hz => by
      show (g ≫ q) z ∈ W
      rwa [hY.w]
    have hb :=
      Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeNatTrans_app_pullbackSection
      hY.w G W W₁ hW hq hV (σ.app W a)
    exact congrArg (θ.app (q₁ ⁻¹ᵁ W₁)) hb.symm
  have hsurj : Function.Surjective (ρ.liftBaseChange Γ(Y', W₁)) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_liftBaseChange, LinearMap.coe_range]
    exact hρ
  exact LinearMap.ker_le_span_image_ker_of_flat ρ hsurj
    (Scheme.Modules.sectionsLinearMap σ W) ν hν (Scheme.Modules.sectionsLinearMap σ₁ W₁) hh hx

end FlatKernel

/-! ### The chase at free variables -/

section Abstract

variable {Y Y' P P₁ Z Z₁ : Scheme.{u}} (p : P ⟶ Y) (p₁ : P₁ ⟶ Y') (hs : Y' ⟶ Y)
  (pc : P₁ ⟶ P) (hpcT : pc ≫ p = p₁ ≫ hs) (i : Z ⟶ P) (i₁ : Z₁ ⟶ P₁) (g : Z₁ ⟶ Z)
  (hw : g ≫ i = i₁ ≫ pc) {M : Y.Modules} {M₁ : Y'.Modules} {G : P.Modules} {G₁ : P₁.Modules}
  (ψ : M ⟶ (Scheme.Modules.pushforward p).obj G) (Φk : M₁ ⟶ (Scheme.Modules.pullback hs).obj M)
  (θ : (Scheme.Modules.pullback pc).obj G ⟶ G₁)
  (ψ₁ : M₁ ⟶ (Scheme.Modules.pushforward p₁).obj G₁)

/-- The comparison `g^*(i^*G) ≅ (g ≫ i)^*G = (i₁ ≫ pc)^*G ≅ i₁^*(pc^*G) ⟶ i₁^*G₁`. -/
def pullbackSquareTwistMap :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pullback i).obj G) ⟶
      (Scheme.Modules.pullback i₁).obj G₁ :=
  (Scheme.Modules.pullbackComp g i).hom.app G ≫ (Scheme.Modules.pullbackCongr hw).hom.app G ≫
    (Scheme.Modules.pullbackComp i₁ pc).inv.app G ≫ (Scheme.Modules.pullback i₁).map θ

/-- The comparison is an isomorphism when `θ` is. -/
theorem isIso_pullbackSquareTwistMap (hθ : IsIso θ) :
    IsIso (pullbackSquareTwistMap pc i i₁ g hw θ) := by
  unfold pullbackSquareTwistMap; infer_instance

/-- **The chase.** If `ψ₁` is `Φk`, followed by the base change of `ψ` along the square of `pc`
over `hs`, followed by `θ`, then for `a₁` with `Φk(a₁) = hs^*a` the restriction to `Z₁` of
`ψ₁(a₁)` is the image under `pullbackSquareTwistMap` of the pullback along `g` of the restriction
to `Z` of `ψ(a)`. -/
theorem pullbackSection_psi_eq_pullbackSquareTwistMap
    (hψ₁ : (Φk ≫ basePsi p p₁ hs pc hpcT ψ) ≫ (Scheme.Modules.pushforward p₁).map θ = ψ₁)
    {W : Y.Opens} {W₁ : Y'.Opens} (hW : W₁ ≤ hs ⁻¹ᵁ W)
    (hV : i₁ ⁻¹ᵁ (p₁ ⁻¹ᵁ W₁) ≤ g ⁻¹ᵁ (i ⁻¹ᵁ (p ⁻¹ᵁ W)))
    (a : Γ(M, W)) (a₁ : Γ(M₁, W₁))
    (ha : Φk.val.app (op W₁) a₁ = Scheme.Modules.pullbackSection hs M W W₁ hW a) :
    Scheme.Modules.pullbackSection i₁ G₁ (p₁ ⁻¹ᵁ W₁) (i₁ ⁻¹ᵁ (p₁ ⁻¹ᵁ W₁)) le_rfl
        (ψ₁.val.app (op W₁) a₁) =
      (pullbackSquareTwistMap pc i i₁ g hw θ).val.app (op (i₁ ⁻¹ᵁ (p₁ ⁻¹ᵁ W₁)))
        (Scheme.Modules.pullbackSection g ((Scheme.Modules.pullback i).obj G)
          (i ⁻¹ᵁ (p ⁻¹ᵁ W)) (i₁ ⁻¹ᵁ (p₁ ⁻¹ᵁ W₁)) hV
          (Scheme.Modules.pullbackSection i G (p ⁻¹ᵁ W) (i ⁻¹ᵁ (p ⁻¹ᵁ W)) le_rfl
            (ψ.val.app (op W) a))) := by
  have h' : p₁ ⁻¹ᵁ W₁ ≤ pc ⁻¹ᵁ (p ⁻¹ᵁ W) := fun x hx => by
    show (pc ≫ p) x ∈ W
    rw [hpcT]
    exact hW hx
  have h₁ : i₁ ⁻¹ᵁ (p₁ ⁻¹ᵁ W₁) ≤ (i₁ ≫ pc) ⁻¹ᵁ (p ⁻¹ᵁ W) := fun x hx => h' hx
  have h₂ : i₁ ⁻¹ᵁ (p₁ ⁻¹ᵁ W₁) ≤ (g ≫ i) ⁻¹ᵁ (p ⁻¹ᵁ W) := fun x hx => hV hx
  have e1 : ψ₁.val.app (op W₁) a₁ = θ.val.app (op (p₁ ⁻¹ᵁ W₁))
      (Scheme.Modules.pullbackSection pc G (p ⁻¹ᵁ W) (p₁ ⁻¹ᵁ W₁) h' (ψ.val.app (op W) a)) := by
    rw [← hψ₁]
    show θ.val.app (op (p₁ ⁻¹ᵁ W₁)) ((basePsi p p₁ hs pc hpcT ψ).val.app (op W₁)
      (Φk.val.app (op W₁) a₁)) = _
    rw [ha, basePsi_pullbackSection p p₁ hs pc hpcT ψ W W₁ hW h' a]
  rw [e1, ← Scheme.Modules.pullbackSection_naturality i₁ θ]
  have e2 := Scheme.Modules.pullbackSection_comp i₁ pc G (p ⁻¹ᵁ W) (p₁ ⁻¹ᵁ W₁)
    (i₁ ⁻¹ᵁ (p₁ ⁻¹ᵁ W₁)) h' le_rfl h₁ (ψ.val.app (op W) a)
  have e3 := Scheme.Modules.pullbackSection_comp g i G (p ⁻¹ᵁ W) (i ⁻¹ᵁ (p ⁻¹ᵁ W))
    (i₁ ⁻¹ᵁ (p₁ ⁻¹ᵁ W₁)) le_rfl hV h₂ (ψ.val.app (op W) a)
  have e4 := Scheme.Modules.pullbackSection_congr hw G (p ⁻¹ᵁ W) (i₁ ⁻¹ᵁ (p₁ ⁻¹ᵁ W₁)) h₂ h₁
    (ψ.val.app (op W) a)
  show _ = ((Scheme.Modules.pullback i₁).map θ).val.app _
    (((Scheme.Modules.pullbackComp i₁ pc).inv.app G).val.app _
      (((Scheme.Modules.pullbackCongr hw).hom.app G).val.app _
        (((Scheme.Modules.pullbackComp g i).hom.app G).val.app _ _)))
  rw [e3, e4, ← e2]
  refine congrArg (((Scheme.Modules.pullback i₁).map θ).val.app _) ?_
  show _ = (((Scheme.Modules.pullbackComp i₁ pc).hom.app G ≫
    (Scheme.Modules.pullbackComp i₁ pc).inv.app G).val.app _) _
  rw [Iso.hom_inv_id_app]
  rfl

end Abstract

variable {Y Y' : Scheme.{u}} (A : SheafGradedAlgebra Y) (hs : Y' ⟶ Y) {A₁ : SheafGradedAlgebra Y'}
  (Φ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A₁)
    (situationAlgebra (A.pullback hs)))
  (hΦ : ∀ n : ℤ, IsIso (Φ.app n))

/-- **The restriction of a homogeneous local section along `hs`**: for `W₁ ≤ hs⁻¹W`, a section `a`
of `A_n` over `W` goes to `Φ⁻¹(hs^*a)`, a section of `A₁_n` over `W₁`. -/
def twistKerRestrict (n : ℤ) {W : Y.Opens} {W₁ : Y'.Opens} (hW : W₁ ≤ hs ⁻¹ᵁ W)
    (a : Γ(A.piece n, W)) : Γ(A₁.piece n, W₁) :=
  haveI := hΦ n
  (inv (Φ.app n)).val.app (op W₁) (Scheme.Modules.pullbackSection hs (A.piece n) W W₁ hW a)

/-- The restriction is `Φ⁻¹` applied to the pulled-back section, on the nose. -/
theorem twistKerRestrict_eq (n : ℤ) {W : Y.Opens} {W₁ : Y'.Opens} (hW : W₁ ≤ hs ⁻¹ᵁ W)
    (a : Γ(A.piece n, W)) :
    twistKerRestrict A hs Φ hΦ n hW a =
      Scheme.Modules.Hom.app (haveI := hΦ n; (asIso (Φ.app n)).inv) W₁
        (Scheme.Modules.pullbackSection hs (A.piece n) W W₁ hW a) := rfl

/-- `Φ` carries the restriction back to the pulled-back section. -/
theorem app_twistKerRestrict (n : ℤ) {W : Y.Opens} {W₁ : Y'.Opens} (hW : W₁ ≤ hs ⁻¹ᵁ W)
    (a : Γ(A.piece n, W)) :
    (Φ.app n).val.app (op W₁) (twistKerRestrict A hs Φ hΦ n hW a) =
      Scheme.Modules.pullbackSection hs (A.piece n) W W₁ hW a := by
  have := hΦ n
  exact congrArg (fun φ => φ.val.app (op W₁)
    (Scheme.Modules.pullbackSection hs (A.piece n) W W₁ hW a)) (IsIso.inv_hom_id (Φ.app n))

/-- The restriction is additive. -/
theorem twistKerRestrict_add (n : ℤ) {W : Y.Opens} {W₁ : Y'.Opens} (hW : W₁ ≤ hs ⁻¹ᵁ W)
    (a b : Γ(A.piece n, W)) :
    twistKerRestrict A hs Φ hΦ n hW (a + b) =
      twistKerRestrict A hs Φ hΦ n hW a + twistKerRestrict A hs Φ hΦ n hW b := by
  let := Scheme.Modules.pullbackSectionsModule hs (A.piece n) W W₁ hW
  have := hΦ n
  exact (congrArg ((inv (Φ.app n)).val.app (op W₁))
    ((Scheme.Modules.pullbackSectionₗ hs (A.piece n) W W₁ hW).map_add a b)).trans (map_add _ _ _)

/-- The restriction is semilinear along `hs.appLE W W₁`. -/
theorem twistKerRestrict_smul (n : ℤ) {W : Y.Opens} {W₁ : Y'.Opens} (hW : W₁ ≤ hs ⁻¹ᵁ W)
    (r : Γ(Y, W)) (a : Γ(A.piece n, W)) :
    twistKerRestrict A hs Φ hΦ n hW (r • a) =
      (hs.appLE W W₁ hW).hom r • twistKerRestrict A hs Φ hΦ n hW a := by
  let := Scheme.Modules.pullbackSectionsModule hs (A.piece n) W W₁ hW
  have := hΦ n
  exact (congrArg ((inv (Φ.app n)).val.app (op W₁))
    ((Scheme.Modules.pullbackSectionₗ hs (A.piece n) W W₁ hW).map_smul r a)).trans
    (((inv (Φ.app n)).val.app (op W₁)).hom.map_smul _ _)

/-! ### The ideal along a restriction followed by a base change -/

section Ideal

variable (pc : (relativeProj A₁).scheme ⟶ (relativeProj A).scheme)
  (hpc : pc = (relativeProjCongr Φ hΦ).hom ≫ baseChangeHom A hs)
  {Z Z₁ : Scheme.{u}} (i : Z ⟶ (relativeProj A).scheme) (i₁ : Z₁ ⟶ (relativeProj A₁).scheme)
  (g : Z₁ ⟶ Z)

include hpc in
/-- `pc` lies over `hs`. -/
theorem comp_toBase_of_eq_relativeProjCongr_comp :
    pc ≫ (relativeProj A).toBase = (relativeProj A₁).toBase ≫ hs := by
  rw [hpc, Category.assoc, baseChangeHom_comp_toBase, ← Category.assoc,
    relativeProjCongr_hom_comp_toBase]

/-- The open of `Z₁` over `W₁` lies over the open of `Z` over `W`. -/
theorem twistOpen_le_preimage
    (hpcT : pc ≫ (relativeProj A).toBase = (relativeProj A₁).toBase ≫ hs)
    (hw : g ≫ i = i₁ ≫ pc) {W : Y.Opens} {W₁ : Y'.Opens} (hW : W₁ ≤ hs ⁻¹ᵁ W) :
    i₁ ⁻¹ᵁ ((relativeProj A₁).toBase ⁻¹ᵁ W₁) ≤
      g ⁻¹ᵁ (i ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W)) := fun x hx => by
  show (g ≫ i ≫ (relativeProj A).toBase) x ∈ W
  rw [reassoc_of% hw, hpcT]
  exact hW hx

include hpc in
/-- **The degreewise map of Tag 0801 on a restriction.** For `m ≥ 0`, the map
`A₁_m ⟶ p₁_*(i₁_*(i₁^*𝒪(m)))` on the restriction of `a` is the comparison
`pullbackSquareTwistMap` applied to the pullback along `g` of the image of `a` under the map for
`A`. -/
theorem twistRestrictMapNat_twistKerRestrict (hw : g ≫ i = i₁ ≫ pc) (m : ℕ) {W : Y.Opens}
    {W₁ : Y'.Opens} (hW : W₁ ≤ hs ⁻¹ᵁ W)
    (hV : i₁ ⁻¹ᵁ ((relativeProj A₁).toBase ⁻¹ᵁ W₁) ≤
      g ⁻¹ᵁ (i ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W)))
    (a : Γ(A.piece (m : ℤ), W)) :
    (twistRestrictMapNat A₁ (GluedTwistAlgebra.twistDataOfGradedAlgebra A₁) i₁ m).val.app (op W₁)
        (twistKerRestrict A hs Φ hΦ m hW a) =
      (pullbackSquareTwistMap pc i i₁ g hw
          ((congrBaseChangeTwistIso A hs Φ hΦ pc hpc).hom.app (m : ℤ))).val.app
        (op (i₁ ⁻¹ᵁ ((relativeProj A₁).toBase ⁻¹ᵁ W₁)))
        (Scheme.Modules.pullbackSection g ((Scheme.Modules.pullback i).obj
            ((Tag07ZGTwist.twistAlgebra A).piece (m : ℤ)))
          (i ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W)) (i₁ ⁻¹ᵁ ((relativeProj A₁).toBase ⁻¹ᵁ W₁)) hV
          ((twistRestrictMapNat A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) i m).val.app (op W)
            a)) := by
  have hpcT := comp_toBase_of_eq_relativeProjCongr_comp A hs Φ hΦ pc hpc
  refine (twistRestrictMapNat_app A₁ _ i₁ m W₁ _).trans ?_
  refine (pullbackSection_psi_eq_pullbackSquareTwistMap (relativeProj A).toBase
    (relativeProj A₁).toBase hs pc hpcT i i₁ g hw
    ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ m)
    ((congrHom Φ).app (m : ℤ)) ((congrBaseChangeTwistIso A hs Φ hΦ pc hpc).hom.app (m : ℤ))
    ((GluedTwistAlgebra.twistDataOfGradedAlgebra A₁).ψ m)
    (congrBaseChangePsi_comp_congrBaseChangeTwistIso A hs Φ hΦ pc hpc hpcT m) hW hV a
    (twistKerRestrict A hs Φ hΦ (m : ℤ) hW a)
    (app_twistKerRestrict A hs Φ hΦ (m : ℤ) hW a)).trans ?_
  rw [twistRestrictMapNat_app A _ i m W a]

include hpc in
/-- **Restriction carries the graded ideal of Tag 0801 into the graded ideal of the base-changed
closed subscheme.** -/
theorem mem_twistKer_restrict [IsClosedImmersion i] [IsClosedImmersion i₁]
    [QuasiCompact (relativeProj A).toBase] [QuasiCompact (relativeProj A₁).toBase]
    (hw : g ≫ i = i₁ ≫ pc) (n : ℤ) {W : Y.Opens} {W₁ : Y'.Opens}
    (hW : W₁ ≤ hs ⁻¹ᵁ W) (a : Γ(A.piece n, W))
    (ha : a ∈ ((twistKerGradedIdeal A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) i).piece
      n).toSubmodule.obj
      (op W)) :
    twistKerRestrict A hs Φ hΦ n hW a ∈
      ((twistKerGradedIdeal A₁ (GluedTwistAlgebra.twistDataOfGradedAlgebra A₁) i₁).piece
        n).toSubmodule.obj
        (op W₁) := by
  rcases lt_or_ge n 0 with hn | hn
  · rw [section_eq_zero_of_isZero (A₁.negative_isZero n hn) W₁ (twistKerRestrict A hs Φ hΦ n hW a)]
    exact Submodule.zero_mem _
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have hV := twistOpen_le_preimage A hs pc i i₁ g
    (comp_toBase_of_eq_relativeProjCongr_comp A hs Φ hΦ pc hpc) hw hW
  have h := twistRestrictMapNat_twistKerRestrict A hs Φ hΦ pc hpc i i₁ g hw m hW hV a
  rw [twistRestrictMapNat_app, twistRestrictMapNat_app,
    (mem_twistKerGradedIdeal_iff A _ i m W a).1 ha] at h
  let := Scheme.Modules.pullbackSectionsModule g
    ((Scheme.Modules.pullback i).obj
      ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra.piece (m : ℤ)))
    (i ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ W)) _ hV
  rw [(mem_twistKerGradedIdeal_iff A₁ _ i₁ m W₁ _), h,
    show Scheme.Modules.pullbackSection g _ _ _ hV 0 = 0 from
      (Scheme.Modules.pullbackSectionₗ g _ _ _ hV).map_zero]
  exact map_zero _

include hpc in
/-- **Over affine opens and along a flat base change, the graded ideal of the base-changed closed
subscheme is spanned by the restrictions of the graded ideal.** -/
theorem twistKer_le_span_restrict [IsClosedImmersion i] [IsClosedImmersion i₁]
    [QuasiCompact (relativeProj A).toBase] [QuasiCompact (relativeProj A₁).toBase] [Flat hs]
    (hsq : IsPullback g i₁ i pc) (n : ℤ) {W : Y.Opens}
    {W₁ : Y'.Opens} (hW : W₁ ≤ hs ⁻¹ᵁ W) (hWa : IsAffineOpen W) (hW₁a : IsAffineOpen W₁) :
    ((twistKerGradedIdeal A₁ (GluedTwistAlgebra.twistDataOfGradedAlgebra A₁) i₁).piece n
        ).toSubmodule.obj (op W₁) ≤
      Submodule.span Γ(Y', W₁) (twistKerRestrict A hs Φ hΦ n hW ''
        SetLike.coe (((twistKerGradedIdeal A (GluedTwistAlgebra.twistDataOfGradedAlgebra A)
          i).piece n).toSubmodule.obj (op W))) := by
  rcases lt_or_ge n 0 with hn | hn
  · intro x _
    rw [section_eq_zero_of_isZero (A₁.negative_isZero n hn) W₁ x]
    exact Submodule.zero_mem _
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have hpcT := comp_toBase_of_eq_relativeProjCongr_comp A hs Φ hΦ pc hpc
  have hY : IsPullback g (i₁ ≫ (relativeProj A₁).toBase) (i ≫ (relativeProj A).toBase) hs :=
    hsq.paste_vert (isPullback_comparison hs A Φ hΦ pc hpc)
  have : IsSeparated (relativeProj A).toBase :=
    Stacks.AlgebraicGeometry.RelativeProjSeparated.isSeparated_toBase A (relativeProj A)
  have : ((Scheme.Modules.pullback i).obj
      ((Tag07ZGTwist.twistAlgebra A).piece (m : ℤ))).IsQuasicoherent :=
    Stacks.Conormal.gradedPullback_isQuasicoherent i
      (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra
      (fun n => (GluedTwistAlgebra.twistDataOfGradedAlgebra A).isQuasicoherent n) (m : ℤ)
  have hθ₀ : IsIso ((congrBaseChangeTwistIso A hs Φ hΦ pc hpc).hom.app (m : ℤ)) :=
    ⟨(congrBaseChangeTwistIso A hs Φ hΦ pc hpc).inv.app (m : ℤ),
      congrArg (fun f => f.app (m : ℤ)) (congrBaseChangeTwistIso A hs Φ hΦ pc hpc).hom_inv_id,
      congrArg (fun f => f.app (m : ℤ)) (congrBaseChangeTwistIso A hs Φ hΦ pc hpc).inv_hom_id⟩
  have := hΦ (m : ℤ)
  have hV := twistOpen_le_preimage A hs pc i i₁ g hpcT hsq.w hW
  intro x hx
  have hx' : (twistRestrictMapNat A₁ (GluedTwistAlgebra.twistDataOfGradedAlgebra A₁) i₁ m).val.app
      (op W₁) x = 0 :=
    (twistRestrictMapNat_app A₁ _ i₁ m W₁ x).trans
      ((mem_twistKerGradedIdeal_iff A₁ _ i₁ m W₁ x).1 hx)
  have key := app_eq_zero_mem_span_of_isPullback (M := A.piece (m : ℤ))
    (M₁ := A₁.piece (m : ℤ)) hs hY _
    (pullbackSquareTwistMap pc i i₁ g hsq.w
      ((congrBaseChangeTwistIso A hs Φ hΦ pc hpc).hom.app (m : ℤ)))
    (isIso_pullbackSquareTwistMap pc i i₁ g hsq.w _ hθ₀)
    (@inv _ _ _ _ (Φ.app (m : ℤ)) (hΦ m)) (@IsIso.inv_isIso _ _ _ _ _ (hΦ m))
    (twistRestrictMapNat A (GluedTwistAlgebra.twistDataOfGradedAlgebra A) i m)
    (twistRestrictMapNat A₁ (GluedTwistAlgebra.twistDataOfGradedAlgebra A₁) i₁ m)
    hW hWa hW₁a hV
    (fun a => twistRestrictMapNat_twistKerRestrict A hs Φ hΦ pc hpc i i₁ g hsq.w m hW hV a)
    x hx'
  refine Submodule.span_mono (R := Γ(Y', W₁)) (M := Γ(A₁.piece (m : ℤ), W₁)) ?_ key
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨a, ?_, rfl⟩
  exact (mem_twistKerGradedIdeal_iff A _ i m W a).2
    ((twistRestrictMapNat_app A _ i m W a).symm.trans ha)

end Ideal

end Stacks.AlgebraicGeometry.RelativeProjGradedIdeal

end
