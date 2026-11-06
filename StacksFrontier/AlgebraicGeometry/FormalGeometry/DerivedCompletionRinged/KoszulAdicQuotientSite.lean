module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ImageSubsheafUniversal
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AdicQuotientFactorization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.GeneratedIdealSheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulAffineSectionsHomology
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulTopCohomologySheaf
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulTopSingleProjections
public import StacksFrontier.AlgebraicGeometry.IdealPowerSections.CompatibleFractions
public import StacksFrontier.CategoryTheory.Sites.Modules.IdealSubsheafLocal
public import StacksFrontier.CategoryTheory.Sites.Modules.SubmoduleQuotientTower

/-!
# The pigeonhole comparison of the Koszul quotients with the adic quotients, at site level

Let `(𝒞, 𝒪)` be a ringed site, let `f_1, …, f_r` be global sections of `𝒪` and let
`ℐ = (f_1, …, f_r) ⊂ 𝒪` be the sheaf of ideals they generate,
`AlgebraicGeometry.RingedSite.generatedIdealSheaf`. For an **arbitrary** sheaf of `𝒪`-modules
`ℱ` this file proves the two containments

`ℐ^{r(n+1)+1}ℱ ⊆ (f_1^{n+1}, …, f_r^{n+1})ℱ ⊆ ℐ^{n+1}ℱ`

between the products of `ℱ` with the powers of `ℐ` (`Stacks.Sites.idealPowSmul` at the largest
submodule) and the image of the Koszul generator map
`AlgebraicGeometry.RingedSite.koszulGeneratorsMap`, whose cokernel is the top cohomology sheaf of
the Koszul complex on `f_1^{n+1}, …, f_r^{n+1}` with coefficients in `ℱ`; and it deduces the
**pigeonhole comparison of the tower of those top cohomology sheaves with the tower
`n ↦ ℱ/ℐⁿ⁺¹ℱ`** of `Stacks.Sites.adicQuotientTowerOn`, as a natural transformation with eventual
inverses. This is the comparison of part (3) of [Stacks, Tag 0A0K], and no Noetherian,
coherence or quasi-compactness hypothesis enters it.

## Implementation notes

On a scheme the same containments are
`Stacks.Algebraization.globalSpanMultiple_le_idealPowerMultiple` and
`Stacks.Algebraization.idealPowerMultiple_le_globalSpanMultiple`, proved affine open by affine
open: both subsheaves there are `Stacks.Algebraization.affineLocalMultiple`, cut out by an ideal
of sections over each affine open, and the containment of subsheaves is checked by the
containment of those ideals. A ringed site has no affine opens, and the sections of `ℐ` over an
object are only *locally* `𝒪`-linear combinations of the `f_i`
(`AlgebraicGeometry.RingedSite.mem_generatedIdealSheaf_iff`), so the ring-theoretic pigeonhole
has to be applied after passing to a covering sieve. That is
`AlgebraicGeometry.RingedSite.exists_sieve_pow_sectionSpan`: a section of `ℐ^m` is locally a sum
of `m`-fold products of local combinations of the `f_i`, hence locally lies in the `m`-th power
of the objectwise ideal they span, and there
`Stacks.AlgebraicGeometry.IdealPowerSections.span_range_pow_le_span_range_pow` applies.

`AlgebraicGeometry.RingedSite.adicQuotientTower` is the tower of the quotients by the powers
`ℐⁿ⁺¹` themselves, while `Stacks.Sites.adicQuotientTowerOn` at `ℱ = 𝒪` is the tower of the
quotients by the products `ℐⁿ⁺¹𝒪`. The two subsheaves are *equal*
(`Stacks.Sites.idealSmul_top`), but the two towers are not the same term, so the comparison at
the coefficient `𝒪` is read across by
`AlgebraicGeometry.RingedSite.adicQuotientTowerOnUnitHom`, an isomorphism of towers whose
components are the maps on quotients induced by the two containments.

A quotient of a sheaf of modules is a cokernel, so the comparison of two such quotients is built
from two vanishing composites, and each of those is the statement that one subsheaf is contained
in the image of the morphism the other quotient is taken of. The general form of that step is
`Stacks.SheafOfModules.ImageSubsheaf.ι_comp_cokernelπ_eq_zero_of_le` and
`Stacks.SheafOfModules.ImageSubsheaf.comp_cokernelπ_submoduleι_eq_zero`, for an arbitrary
morphism of sheaves of modules: the image subsheaf is the least submodule through which the
morphism factors (`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_le`), and the
factorisation through it is an epimorphism (`Stacks.SheafOfModules.ImageSubsheaf.epi_toImage`).

## Main results

* `Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_ι_comp_eq_zero` — a morphism killing `u`
  kills the image subsheaf of `u`; in particular the image subsheaf of a morphism dies in its
  cokernel.
* `AlgebraicGeometry.RingedSite.exists_sieve_pow_sectionSpan` — a section of `ℐ^m` lies, locally,
  in the `m`-th power of the objectwise ideal spanned by the generators.
* `AlgebraicGeometry.RingedSite.idealPowSmul_le_imageSubmodule_koszulGeneratorsMap` — **the
  pigeonhole containment** `ℐ^{r(n+1)+1}ℱ ⊆ (f_1^{n+1}, …, f_r^{n+1})ℱ`, at an arbitrary
  coefficient.
* `AlgebraicGeometry.RingedSite.imageSubmodule_koszulScalarOn_le_idealPowSmul` — the easy
  containment `(f_i^{n+1})ℱ ⊆ ℐ^{n+1}ℱ`, one generator at a time.
* `AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotientOn` and
  `RingedSite.exists_hasEventualInverses_koszulTopHomologySystem_adicQuotientTowerOn` — **the
  comparison of the tower of Koszul top cohomology sheaves of an arbitrary `ℱ` with the tower
  `n ↦ ℱ/ℐⁿ⁺¹ℱ`, as a natural transformation with eventual inverses.** This is the site-level form
  of the pigeonhole step of part (3) of [Stacks, Tag 0A0K]; the scheme-level form is
  `Stacks.Algebraization.koszulTopQuotientToAdicQuotient` with
  `Stacks.Algebraization.hasEventualInverses_koszulTopQuotientToAdicQuotient`.
* `AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotient` and
  `AlgebraicGeometry.RingedSite.hasEventualInverses_koszulTopHomologyToAdicQuotient` — the
  coefficient-`𝒪` case of the same comparison, read into
  `AlgebraicGeometry.RingedSite.adicQuotientTower` through
  `AlgebraicGeometry.RingedSite.adicQuotientTowerOnUnitHom`.
* `AlgebraicGeometry.RingedSite.exists_isDerivedLimitWithProjections_adicReductionTower_completion`
  — **part (1) of [Stacks, Tag 0A0K] over the adic quotient tower**, on an arbitrary ringed site,
  for an arbitrary object `K` of `D(𝒪)`, with the pro-vanishing of the Koszul cohomology sheaves
  below the top degree as the only hypothesis, and with the projections named.
* `AlgebraicGeometry.RingedSite.isDerivedLimit_adicReductionTower_completion_of_model` — the same
  at a flat Noetherian model, with that hypothesis discharged and **no quasi-compactness**.

## References

* [Stacks Project, Tag 0A0E](https://stacks.math.columbia.edu/tag/0A0E)
* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0942](https://stacks.math.columbia.edu/tag/0942)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v₁ u₁

namespace Stacks.SheafOfModules.ImageSubsheaf

section Cokernel

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M N : SheafOfModules.{u} R}

/-- **A morphism killing `u` kills the image subsheaf of `u`.** The factorisation of `u` through
its image is an epimorphism (`Stacks.SheafOfModules.ImageSubsheaf.epi_toImage`), so the inclusion
of the image may be cancelled against the vanishing of `u`. -/
@[reassoc]
theorem imageSubmodule_ι_comp_eq_zero {Z : SheafOfModules.{u} R} (u : M ⟶ N) (w : N ⟶ Z)
    (h : u ≫ w = 0) : (imageSubmodule u).ι ≫ w = 0 := by
  rw [← cancel_epi (toImage u), comp_zero, ← Category.assoc, toImage_ι, h]

/-- **A subsheaf contained in the image of `u` is killed by every morphism killing `u`.** This is
the form in which a containment of subsheaves produces the backward map between two quotients of
one sheaf of modules. -/
@[reassoc]
theorem ι_comp_eq_zero_of_le_imageSubmodule {Z : SheafOfModules.{u} R} (u : M ⟶ N) (w : N ⟶ Z)
    (h : u ≫ w = 0) {P : N.Submodule} (hP : P ≤ imageSubmodule u) : P.ι ≫ w = 0 := by
  rw [← Stacks.SheafOfModules.Submodule.homOfLE_comp_ι hP, Category.assoc,
    imageSubmodule_ι_comp_eq_zero u w h, comp_zero]

/-- **The image subsheaf of a morphism of sheaves of modules dies in its cokernel.** -/
@[reassoc]
theorem imageSubmodule_ι_comp_cokernelπ (u : M ⟶ N) [HasCokernel u] :
    (imageSubmodule u).ι ≫ cokernel.π u = 0 :=
  imageSubmodule_ι_comp_eq_zero u _ (cokernel.condition u)

/-- **A subsheaf contained in the image of a morphism dies in the cokernel of that morphism.** -/
@[reassoc]
theorem ι_comp_cokernelπ_eq_zero_of_le (u : M ⟶ N) [HasCokernel u] {P : N.Submodule}
    (h : P ≤ imageSubmodule u) : P.ι ≫ cokernel.π u = 0 :=
  ι_comp_eq_zero_of_le_imageSubmodule u _ (cokernel.condition u) h

/-- **A morphism whose image lies in a subsheaf dies in the quotient by that subsheaf.** The
morphism factors through the subsheaf by
`Stacks.SheafOfModules.ImageSubsheaf.exists_factorThru_iff_imageSubmodule_le`, and the inclusion
of the subsheaf dies in the cokernel it is the kernel of.

This is the form in which a containment of subsheaves produces the forward map between two
quotients of one sheaf of modules. -/
@[reassoc]
theorem comp_cokernelπ_submoduleι_eq_zero {A : SheafOfModules.{u} R} (g : A ⟶ N)
    {P : N.Submodule} [HasCokernel P.ι] (h : imageSubmodule g ≤ P) :
    g ≫ cokernel.π P.ι = 0 := by
  obtain ⟨k, hk⟩ := (exists_factorThru_iff_imageSubmodule_le g).2 h
  rw [← hk, Category.assoc, cokernel.condition, comp_zero]

end Cokernel

end Stacks.SheafOfModules.ImageSubsheaf

namespace AlgebraicGeometry.RingedSite

section Pigeonhole

open Stacks.Sites Stacks.SheafOfModules.ImageSubsheaf

attribute [local instance] hasSheafCompose_forget₂_ringCat

variable {X : RingedSite.{u, u, u}} {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **A section of `ℐ^m` lies locally in the `m`-th power of the objectwise ideal spanned by the
generators.**

The sections of `ℐ = (f_1, …, f_r)` over an object are only *locally* `𝒪`-linear combinations of
the `f_i`, so a product of `m` of them is only locally a product of `m` combinations; two
covering sieves have a covering intersection, which is what makes the statement survive both the
product and the sum in `Submodule.mul_induction_on`. -/
theorem exists_sieve_pow_sectionSpan : ∀ (m : ℕ) {U : X.Cᵒᵖ} {x : X.O.obj.obj U},
    x ∈ sectionIdeal (generatedIdealSheaf f) U ^ m →
      ∃ S : Sieve U.unop, S ∈ X.J U.unop ∧ ∀ ⦃W : X.C⦄ (g : W ⟶ U.unop), S g →
        (X.O.obj.map g.op).hom x ∈ sectionSpan f (op W) ^ m := by
  intro m
  induction m with
  | zero =>
      intro U x _
      refine ⟨⊤, X.J.top_mem U.unop, fun W g _ => ?_⟩
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | succ m ih =>
      intro U x hx
      rw [pow_succ'] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        obtain ⟨Sa, hSa, hahyp⟩ :=
          Stacks.SheafOfModules.exists_sieve_of_mem_sheafifySubmodule
            (N := presheafGeneratedIdeal f) (x := a) ha
        obtain ⟨Sb, hSb, hbhyp⟩ := ih hb
        refine ⟨Sa ⊓ Sb, X.J.intersection_covering hSa hSb, fun W g hg => ?_⟩
        rw [map_mul, pow_succ']
        exact Ideal.mul_mem_mul (hahyp g hg.1) (hbhyp g hg.2)
      · intro y z hy hz
        obtain ⟨Sy, hSy, hyhyp⟩ := hy
        obtain ⟨Sz, hSz, hzhyp⟩ := hz
        refine ⟨Sy ⊓ Sz, X.J.intersection_covering hSy hSz, fun W g hg => ?_⟩
        rw [map_add]
        exact Submodule.add_mem _ (hyhyp g hg.1) (hzhyp g hg.2)

variable (n : ℕ) (ℱ : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))

/-- The value of the generator scalar `f_i^{n+1}` on a section `z` of `ℱ` is `f_i^{n+1} • z`. -/
private theorem koszulScalarOn_koszulGenExp_app (U : X.Cᵒᵖ) (i : Fin r) (z : ℱ.val.obj U) :
    (koszulScalarOn X f (koszulGenExp n i) ℱ).val.app U z =
      globalSectionVal (f i) U ^ (n + 1) • z := by
  rw [koszulScalarOn_app]
  exact congrArg (· • z) (Stacks.Algebraization.koszulValue_koszulGenExp X f n U i)

/-- **`f_i^{n+1} · z` is a value of the Koszul generator map on `ℱ`**: it is the image of the
section of the `r`-fold product of copies of `ℱ` supported in the `i`-th factor at `z`. -/
theorem pow_globalSectionVal_smul_mem_rangeSubmodule_koszulGeneratorsMap (U : X.Cᵒᵖ) (i : Fin r)
    (z : ℱ.val.obj U) :
    globalSectionVal (f i) U ^ (n + 1) • z ∈
      (rangeSubmodule (koszulGeneratorsMap X f n ℱ)).obj U := by
  refine ⟨(Stacks.Algebraization.koszulSingle X ℱ i).val.app U z, ?_⟩
  exact (congrArg (fun φ : ℱ ⟶ ℱ => φ.val.app U z)
    (Stacks.Algebraization.koszulSingle_comp_koszulGeneratorsMap X f n ℱ i)).trans
      (koszulScalarOn_koszulGenExp_app f n ℱ U i z)

/-- **An `𝒪`-linear combination of the `f_i^{n+1}`, acting on a section of `ℱ`, is a value of
the Koszul generator map.** The generators themselves are handled by
`AlgebraicGeometry.RingedSite.pow_globalSectionVal_smul_mem_rangeSubmodule_koszulGeneratorsMap`,
and the objectwise range is a submodule, which closes the induction over the span. -/
theorem smul_mem_rangeSubmodule_koszulGeneratorsMap (U : X.Cᵒᵖ) {a : X.O.obj.obj U}
    (ha : a ∈ Ideal.span (Set.range fun i => globalSectionVal (f i) U ^ (n + 1)))
    (z : ℱ.val.obj U) :
    a • z ∈ (rangeSubmodule (koszulGeneratorsMap X f n ℱ)).obj U := by
  induction ha using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact pow_globalSectionVal_smul_mem_rangeSubmodule_koszulGeneratorsMap f n ℱ U i z
  | zero =>
      rw [zero_smul]
      exact zero_mem _
  | add x y _ _ hx hy =>
      rw [add_smul]
      exact add_mem hx hy
  | smul c x _ hx =>
      rw [smul_assoc]
      exact Submodule.smul_mem _ c hx

/-- **The pigeonhole bound on the objectwise spans**: the `(r(n+1)+1)`-st power of the ideal
spanned by `f_1, …, f_r` over an object lies in the ideal spanned by the `f_i^{n+1}` there.

This is `Stacks.AlgebraicGeometry.IdealPowerSections.span_range_pow_le_span_range_pow` at
`ι = Fin r`: a product of `r(n+1)+1` of the generators must repeat one of them at least `n+1`
times. -/
theorem sectionSpan_pow_le_span_pow_globalSectionVal (U : X.Cᵒᵖ) :
    sectionSpan f U ^ (r * (n + 1) + 1) ≤
      Ideal.span (Set.range fun i => globalSectionVal (f i) U ^ (n + 1)) := by
  have h := Stacks.AlgebraicGeometry.IdealPowerSections.span_range_pow_le_span_range_pow
    (fun i : Fin r => globalSectionVal (f i) U) (n + 1)
  rwa [Fintype.card_fin] at h

/-- **The pigeonhole containment** `ℐ^{r(n+1)+1}ℱ ⊆ (f_1^{n+1}, …, f_r^{n+1})ℱ`, at an arbitrary
coefficient: the product of `ℱ` with the `(r(n+1)+1)`-st power of the ideal sheaf generated by
`f_1, …, f_r` lies inside the image of the Koszul generator map on `ℱ`.

Both steps are local. `Stacks.Sites.idealPowSmul_le_iff` reduces the containment to the
objectwise products `ℐ(U)^{r(n+1)+1} · ℱ(U)`; a section of that power of the objectwise ideal
lies, after restriction along the arrows of a covering sieve, in the `(r(n+1)+1)`-st power of the
objectwise ideal spanned by the generators
(`AlgebraicGeometry.RingedSite.exists_sieve_pow_sectionSpan`); there the ring-theoretic
pigeonhole `Stacks.AlgebraicGeometry.IdealPowerSections.span_range_pow_le_span_range_pow`
puts it in the ideal spanned by the `f_i^{n+1}`, whose action on a section of `ℱ` is a value of
the generator map
(`AlgebraicGeometry.RingedSite.smul_mem_rangeSubmodule_koszulGeneratorsMap`); and the image
subsheaf is the closure of the objectwise range under local membership
(`Stacks.SheafOfModules.ImageSubsheaf.imageSubmodule_eq_sheafifySubmodule`).

Nothing Noetherian, coherent or quasi-compact is used, and the exponent does not depend on
`ℱ`. -/
theorem idealPowSmul_le_imageSubmodule_koszulGeneratorsMap :
    idealPowSmul (M := ℱ) (generatedIdealSheaf f) (r * (n + 1) + 1) ⊤ ≤
      imageSubmodule (koszulGeneratorsMap X f n ℱ) := by
  refine (idealPowSmul_le_iff (generatedIdealSheaf f) (r * (n + 1) + 1) ⊤ _).2 fun U =>
    Submodule.smul_le.2 fun a ha z _ => ?_
  obtain ⟨S, hS, haS⟩ := exists_sieve_pow_sectionSpan f (r * (n + 1) + 1) ha
  rw [imageSubmodule_eq_sheafifySubmodule]
  refine Stacks.SheafOfModules.mem_sheafifySubmodule_of_mem hS fun W g hg => ?_
  rw [ℱ.val.map_smul]
  exact smul_mem_rangeSubmodule_koszulGeneratorsMap f n ℱ (op W)
    (sectionSpan_pow_le_span_pow_globalSectionVal f n (op W) (haS g hg)) _

/-- **The easy half of the pigeonhole, one generator at a time**: multiplication by `f_i^{n+1}`
on `ℱ` has image inside `ℐ^{n+1}ℱ`.

The value over an object is `f_i^{n+1}` times a section of `ℱ`, and `f_i^{n+1}` is a product of
`n+1` sections of `ℐ`, so the value is a product of a section of `ℐ^{n+1}` with a section of
`ℱ`. -/
theorem imageSubmodule_koszulScalarOn_le_idealPowSmul (i : Fin r) :
    imageSubmodule (koszulScalarOn X f (koszulGenExp n i) ℱ) ≤
      idealPowSmul (M := ℱ) (generatedIdealSheaf f) (n + 1) ⊤ := by
  refine (imageSubmodule_le_iff _).2 fun U x => ?_
  rw [koszulScalarOn_koszulGenExp_app]
  exact smul_mem_idealPowSmul (generatedIdealSheaf f)
    (mem_idealPow_of_mem_pow (generatedIdealSheaf f) (n + 1)
      (Ideal.pow_mem_pow (globalSectionVal_mem_generatedIdealSheaf f i U) (n + 1)))
    (Stacks.SheafOfModules.mem_top_obj x)

/-! ### The two vanishing composites -/

/-- **The Koszul generator map dies in every quotient of `ℱ` by a subsheaf containing
`ℐ^{n+1}ℱ`**: each generator `f_i^{n+1}` is a section of `ℐ^{n+1}`, so each summand of the
generator map factors through `ℐ^{n+1}ℱ`. -/
theorem koszulGeneratorsMap_comp_cokernelπ_of_le {P : ℱ.Submodule} [HasCokernel P.ι]
    (hP : idealPowSmul (M := ℱ) (generatedIdealSheaf f) (n + 1) ⊤ ≤ P) :
    koszulGeneratorsMap X f n ℱ ≫ cokernel.π P.ι = 0 := by
  rw [koszulGeneratorsMap, Preadditive.sum_comp]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Category.assoc,
    show koszulScalarOn X f (koszulGenExp n i) ℱ ≫ cokernel.π P.ι = 0 from
      comp_cokernelπ_submoduleι_eq_zero _
        ((imageSubmodule_koszulScalarOn_le_idealPowSmul f n ℱ i).trans hP),
    comp_zero]

/-- **A subsheaf of `ℱ` contained in `ℐ^{m}ℱ` dies against every morphism killing the Koszul
generator map** as soon as `m ≥ r(n+1)+1`, which is the pigeonhole containment
`AlgebraicGeometry.RingedSite.idealPowSmul_le_imageSubmodule_koszulGeneratorsMap` together with
the decrease of the products `ℐ^mℱ`. -/
theorem ι_comp_eq_zero_of_le_idealPowSmul
    {Z : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))} (w : ℱ ⟶ Z)
    (hw : koszulGeneratorsMap X f n ℱ ≫ w = 0) {P : ℱ.Submodule} {m : ℕ}
    (hm : r * (n + 1) + 1 ≤ m)
    (hP : P ≤ idealPowSmul (M := ℱ) (generatedIdealSheaf f) m ⊤) :
    P.ι ≫ w = 0 :=
  ι_comp_eq_zero_of_le_imageSubmodule _ w hw
    (hP.trans ((idealPowSmul_antitone (M := ℱ) (generatedIdealSheaf f) ⊤ hm).trans
      (idealPowSmul_le_imageSubmodule_koszulGeneratorsMap f n ℱ)))

end Pigeonhole

/-! ### The comparison of the Koszul top-cohomology tower with the adic quotient tower -/

section Comparison

open Stacks.Sites Stacks.SheafOfModules.ImageSubsheaf CategoryTheory.AlternatingCech
open scoped IsMulCommutative

attribute [local instance]
  hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u}) {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- The top degree of the Koszul complex, in the spelling `r - 1 + 1` which the index type of its
top-degree term carries. -/
abbrev koszulTopDeg (r : ℕ) : ℤ := (r : ℤ) - 1 + 1

/-- For the cohomological complex shape on `ℤ`, the degree following the top degree is
`koszulTopDeg r + 1`. -/
theorem next_koszulTopDeg : (ComplexShape.up ℤ).next (koszulTopDeg r) = koszulTopDeg r + 1 :=
  ComplexShape.next_eq' _ rfl

/-- For the cohomological complex shape on `ℤ`, the degree preceding the top degree is
`r - 1`. -/
theorem prev_koszulTopDeg : (ComplexShape.up ℤ).prev (koszulTopDeg r) = (r : ℤ) - 1 :=
  (ComplexShape.up ℤ).prev_eq' rfl

variable (M : SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (n : ℕ)

/-- **The projection of the top-degree term of the Koszul complex onto its unique factor**, at
the spelling of that term which the complex itself produces. The index type of the top degree
has one element, `CategoryTheory.AlternatingCech.eq_topIdx`, so this is an isomorphism with
inverse `AlgebraicGeometry.RingedSite.koszulTopTermInj`. -/
def koszulTopTermProj : (koszulPowerComplexOn X f M n).X (koszulTopDeg r) ⟶ M :=
  Pi.π (fun S : AlternatingCech.Idx r (koszulTopDeg r) =>
    (koszulPowerFunctorOn X f M n).obj S.1) (AlternatingCech.topIdx r)

/-- The inverse of `AlgebraicGeometry.RingedSite.koszulTopTermProj`: the lift all of whose
components are the identity. -/
def koszulTopTermInj : M ⟶ (koszulPowerComplexOn X f M n).X (koszulTopDeg r) :=
  Pi.lift fun _ : AlternatingCech.Idx r (koszulTopDeg r) => 𝟙 M

/-- `koszulTopTermInj` followed by `koszulTopTermProj` is the identity of `ℱ`. -/
@[reassoc (attr := simp)]
theorem koszulTopTermInj_comp_koszulTopTermProj :
    koszulTopTermInj X f M n ≫ koszulTopTermProj X f M n = 𝟙 M :=
  Pi.lift_comp_π _ _

/-- `koszulTopTermProj` at level `n` followed by `koszulTopTermInj` at any level `k` is the
identity of the top-degree term of the Koszul complex at level `n`. -/
theorem koszulTopTermProj_comp_koszulTopTermInj (k : ℕ) :
    koszulTopTermProj X f M n ≫ koszulTopTermInj X f M k =
      𝟙 ((koszulPowerComplexOn X f M n).X (koszulTopDeg r)) := by
  refine Pi.hom_ext _ _ fun S => ?_
  obtain rfl : S = AlternatingCech.topIdx r := AlternatingCech.eq_topIdx S
  show koszulTopTermProj X f M n ≫ koszulTopTermInj X f M k ≫ koszulTopTermProj X f M k =
    𝟙 ((koszulPowerComplexOn X f M n).X (koszulTopDeg r)) ≫ koszulTopTermProj X f M k
  rw [koszulTopTermInj_comp_koszulTopTermProj, Category.comp_id]
  exact (Category.id_comp _).symm

/-- **The last differential of the Koszul complex, read into `ℱ` through the unique top-degree
factor, factors through the generator map.** This is
`AlgebraicGeometry.RingedSite.koszulTopDifferential_comp_eq` with the differential of the complex
in place of `CategoryTheory.AlternatingCech.d`. -/
theorem d_comp_koszulTopTermProj :
    (koszulPowerComplexOn X f M n).d ((r : ℤ) - 1) (koszulTopDeg r) ≫
        koszulTopTermProj X f M n =
      fromCoIdxProduct X r M ≫ koszulGeneratorsMap X f n M :=
  (congrArg (fun φ => φ ≫ koszulTopProj X r M)
      (AlternatingCech.complex_d (koszulPowerFunctorOn X f M n) ((r : ℤ) - 1))).trans
    (koszulTopDifferential_comp_eq X f n M).symm

/-- **The generator map factors through the last differential.** This is
`AlgebraicGeometry.RingedSite.koszulGeneratorsMap_eq_comp` with the differential of the complex
in place of `CategoryTheory.AlternatingCech.d`. -/
theorem toCoIdxProduct_comp_d_comp_koszulTopTermProj :
    toCoIdxProduct X r M ≫ ((koszulPowerComplexOn X f M n).d ((r : ℤ) - 1) (koszulTopDeg r) ≫
        koszulTopTermProj X f M n) =
      koszulGeneratorsMap X f n M :=
  (congrArg (fun φ => toCoIdxProduct X r M ≫ φ ≫ koszulTopProj X r M)
      (AlternatingCech.complex_d (koszulPowerFunctorOn X f M n) ((r : ℤ) - 1))).trans
    (koszulGeneratorsMap_eq_comp X f n M)

/-- **The canonical map `ℱ ⟶ H^r(K^n ⊗ ℱ)` onto the top cohomology sheaf of the Koszul
complex**: the inverse of the projection onto the unique top-degree factor, followed by the
canonical map out of the top-degree term. -/
def koszulToTopHomologyOn :
    M ⟶ (koszulPowerComplexOn X f M n).homology (koszulTopDeg r) :=
  koszulTopTermInj X f M n ≫
    HomologicalComplex.topToHomology (koszulPowerComplexOn X f M n)
      (next_koszulTopDeg (r := r)) (koszulPowerComplexOn_d_top_eq_zero' X f n M)

/-- `koszulToTopHomologyOn` is `koszulTopTermInj` followed by the canonical map from the
top-degree term to the top cohomology sheaf. -/
theorem koszulToTopHomologyOn_eq :
    koszulToTopHomologyOn X f M n =
      koszulTopTermInj X f M n ≫
        HomologicalComplex.topToHomology (koszulPowerComplexOn X f M n)
          (next_koszulTopDeg (r := r)) (koszulPowerComplexOn_d_top_eq_zero' X f n M) :=
  rfl

/-- The generator map dies in the top cohomology sheaf: it factors through the last differential
of the complex, which the canonical map out of the top-degree term kills. -/
theorem koszulGeneratorsMap_comp_koszulToTopHomologyOn :
    koszulGeneratorsMap X f n M ≫ koszulToTopHomologyOn X f M n = 0 := by
  have h1 : koszulGeneratorsMap X f n M ≫ koszulTopTermInj X f M n =
      toCoIdxProduct X r M ≫
        (koszulPowerComplexOn X f M n).d ((r : ℤ) - 1) (koszulTopDeg r) := by
    refine Pi.hom_ext _ _ fun S => ?_
    obtain rfl : S = AlternatingCech.topIdx r := AlternatingCech.eq_topIdx S
    show koszulGeneratorsMap X f n M ≫ koszulTopTermInj X f M n ≫ koszulTopTermProj X f M n =
      toCoIdxProduct X r M ≫ (koszulPowerComplexOn X f M n).d ((r : ℤ) - 1) (koszulTopDeg r) ≫
        koszulTopTermProj X f M n
    rw [koszulTopTermInj_comp_koszulTopTermProj, Category.comp_id]
    exact (toCoIdxProduct_comp_d_comp_koszulTopTermProj X f M n).symm
  show koszulGeneratorsMap X f n M ≫ koszulTopTermInj X f M n ≫
      HomologicalComplex.topToHomology (koszulPowerComplexOn X f M n)
        (next_koszulTopDeg (r := r)) (koszulPowerComplexOn_d_top_eq_zero' X f n M) = 0
  rw [← Category.assoc, h1]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun φ => toCoIdxProduct X r M ≫ φ)
        (HomologicalComplex.d_comp_topToHomology (koszulPowerComplexOn X f M n)
          (next_koszulTopDeg (r := r)) (koszulPowerComplexOn_d_top_eq_zero' X f n M)
          ((r : ℤ) - 1))).trans comp_zero)

/-- **The transition of the dual Koszul tower is the identity on the top-degree factor.** The
factor is indexed by the full subset, whose complement is empty, so the monomial by which the
transition multiplies it is the empty one. -/
theorem map_f_koszulTopDeg_comp_koszulTopTermProj {m k : ℕ} (hkm : k ≤ m) :
    ((koszulDualSystemOn X f M).map (homOfLE hkm).op).f (koszulTopDeg r) ≫
        koszulTopTermProj X f M k =
      koszulTopTermProj X f M m := by
  rw [koszulDualSystemOn_map_down]
  show AlternatingCech.mapX (koszulPowerTransDownOn X f M hkm) (koszulTopDeg r) ≫
    koszulTopTermProj X f M k = koszulTopTermProj X f M m
  refine (AlternatingCech.mapX_comp_pi (koszulPowerTransDownOn X f M hkm)
    (AlternatingCech.topIdx r)).trans ?_
  rw [koszulPowerTransDownOn_app,
    show koszulScalarOn X f (AlternatingCech.downExp m k (AlternatingCech.topIdx r).1) M =
        koszulScalarOn X f 0 M from
      koszulScalarOn_congr X f (fun i => by simp [AlternatingCech.downExp]) M,
    koszulScalarOn_zero]
  exact Category.comp_id _

/-- The transition of the dual Koszul tower is the identity in the top degree. -/
theorem map_f_koszulTopDeg_eq_id {m k : ℕ} (hkm : k ≤ m) :
    ((koszulDualSystemOn X f M).map (homOfLE hkm).op).f (koszulTopDeg r) =
      𝟙 ((koszulPowerComplexOn X f M m).X (koszulTopDeg r)) := by
  have h1 : ((koszulDualSystemOn X f M).map (homOfLE hkm).op).f (koszulTopDeg r) ≫
      (koszulTopTermProj X f M k ≫ koszulTopTermInj X f M k) =
      𝟙 ((koszulPowerComplexOn X f M m).X (koszulTopDeg r)) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun φ => φ ≫ koszulTopTermInj X f M k)
          (map_f_koszulTopDeg_comp_koszulTopTermProj X f M hkm)).trans
        (koszulTopTermProj_comp_koszulTopTermInj X f M m k))
  refine Eq.trans ?_ h1
  exact ((congrArg (fun φ =>
      ((koszulDualSystemOn X f M).map (homOfLE hkm).op).f (koszulTopDeg r) ≫ φ)
      (koszulTopTermProj_comp_koszulTopTermInj X f M k k)).trans (Category.comp_id _)).symm

/-! ### The transition maps of the adic quotient tower -/

/-- The transition map `𝒪/ℐᵏ ⟶ 𝒪/ℐᵏ` induced by `k ≤ k` is the identity. -/
theorem adicQuotientModuleMap_le_rfl (k : ℕ) :
    Stacks.Sites.adicQuotientModuleMap (X := X) (generatedIdealSheaf f) (le_refl k) = 𝟙 _ := by
  refine (cancel_epi (Stacks.Sites.adicQuotientModuleπ (X := X) (generatedIdealSheaf f) k)).1 ?_
  exact (Stacks.Sites.adicQuotientModuleπ_comp_adicQuotientModuleMap (X := X)
    (generatedIdealSheaf f) (le_refl k)).trans (Category.comp_id _).symm

/-- For `a ≤ b ≤ c`, the transition maps `𝒪/ℐᶜ ⟶ 𝒪/ℐᵇ ⟶ 𝒪/ℐᵃ` compose to the transition map
`𝒪/ℐᶜ ⟶ 𝒪/ℐᵃ`. -/
theorem adicQuotientModuleMap_comp {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    Stacks.Sites.adicQuotientModuleMap (X := X) (generatedIdealSheaf f) hbc ≫
        Stacks.Sites.adicQuotientModuleMap (X := X) (generatedIdealSheaf f) hab =
      Stacks.Sites.adicQuotientModuleMap (X := X) (generatedIdealSheaf f) (hab.trans hbc) := by
  refine (cancel_epi (Stacks.Sites.adicQuotientModuleπ (X := X) (generatedIdealSheaf f) c)).1 ?_
  exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun φ => φ ≫ Stacks.Sites.adicQuotientModuleMap (X := X)
            (generatedIdealSheaf f) hab)
          (Stacks.Sites.adicQuotientModuleπ_comp_adicQuotientModuleMap (X := X)
            (generatedIdealSheaf f) hbc)).trans
        (Stacks.Sites.adicQuotientModuleπ_comp_adicQuotientModuleMap (X := X)
          (generatedIdealSheaf f) hab))).trans
    (Stacks.Sites.adicQuotientModuleπ_comp_adicQuotientModuleMap (X := X)
      (generatedIdealSheaf f) (hab.trans hbc)).symm

/-- **The transition maps of the tower `n ↦ 𝒪/ℐⁿ⁺¹` are the transition maps of the quotients**,
at an arbitrary pair of levels and not only at successive ones. -/
theorem adicQuotientTower_map_eq {m k : ℕ} (h : k ≤ m) :
    (adicQuotientTower X (generatedIdealSheaf f)).map (homOfLE h).op =
      Stacks.Sites.adicQuotientModuleMap (X := X) (generatedIdealSheaf f)
        (Nat.succ_le_succ h) :=
  NoetherianAdicCompletion.ofOpSequence_map_eq _
    (fun _ _ h => Stacks.Sites.adicQuotientModuleMap (X := X) (generatedIdealSheaf f)
      (Nat.succ_le_succ h))
    (fun k => adicQuotientModuleMap_le_rfl X f (k + 1))
    (fun m _k h => (adicQuotientModuleMap_comp X f (Nat.succ_le_succ h)
      (Nat.le_succ (m + 1))).symm) m k h

/-- For `k ≤ m`, the projection `𝒪 ⟶ 𝒪/ℐᵐ⁺¹` followed by the transition map of the tower
`n ↦ 𝒪/ℐⁿ⁺¹` is the projection `𝒪 ⟶ 𝒪/ℐᵏ⁺¹`. -/
theorem adicQuotientModuleπ_comp_adicQuotientTower_map {m k : ℕ} (h : k ≤ m) :
    Stacks.Sites.adicQuotientModuleπ (X := X) (generatedIdealSheaf f) (m + 1) ≫
        (adicQuotientTower X (generatedIdealSheaf f)).map (homOfLE h).op =
      Stacks.Sites.adicQuotientModuleπ (X := X) (generatedIdealSheaf f) (k + 1) :=
  (congrArg (fun φ => Stacks.Sites.adicQuotientModuleπ (X := X) (generatedIdealSheaf f) (m + 1) ≫ φ)
      (adicQuotientTower_map_eq X f h)).trans
    (Stacks.Sites.adicQuotientModuleπ_comp_adicQuotientModuleMap (X := X)
      (generatedIdealSheaf f) (Nat.succ_le_succ h))

/-- **The projection of `𝒪` onto the level `n` of the tower `n ↦ 𝒪/ℐⁿ⁺¹`**, ascribed into the
spelling of the category of sheaves of modules which the tower itself carries.

`Stacks.Sites.adicQuotientModuleπ` lands in `AlgebraicGeometry.RingedSite.Modules X`, whose
category instance is not the one
`SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)` carries, so a composite mixing
the two is not type-correct at the transparency `rw` builds its motive at. Everything below is
stated at this one spelling. -/
def adicQuotientTowerπ (n : ℕ) :
    SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⟶
      (adicQuotientTower X (generatedIdealSheaf f)).obj (op n) :=
  Stacks.Sites.adicQuotientModuleπ (X := X) (generatedIdealSheaf f) (n + 1)

/-- The projection `𝒪 ⟶ 𝒪/ℐⁿ⁺¹` is an epimorphism. -/
instance epi_adicQuotientTowerπ (n : ℕ) : Epi (adicQuotientTowerπ X f n) :=
  inferInstanceAs
    (Epi (cokernel.π (Stacks.Sites.idealPow (generatedIdealSheaf f) (n + 1)).ι))

/-- For `k ≤ m`, `adicQuotientTowerπ` at level `m` followed by the transition map of the tower
`n ↦ 𝒪/ℐⁿ⁺¹` is `adicQuotientTowerπ` at level `k`. -/
@[reassoc]
theorem adicQuotientTowerπ_comp_map {m k : ℕ} (h : k ≤ m) :
    adicQuotientTowerπ X f m ≫
        (adicQuotientTower X (generatedIdealSheaf f)).map (homOfLE h).op =
      adicQuotientTowerπ X f k :=
  adicQuotientModuleπ_comp_adicQuotientTower_map X f h

/-! ### The transformation of towers, at an arbitrary coefficient -/

/-- The downward Koszul transition is the identity in the top degree, in the spelling
`AlgebraicGeometry.RingedSite.koszulPowerComplexOnDown`. -/
theorem koszulPowerComplexOnDown_f_koszulTopDeg_eq_id {m k : ℕ} (hkm : k ≤ m) :
    (koszulPowerComplexOnDown X f M hkm).f (koszulTopDeg r) =
      𝟙 ((koszulPowerComplexOn X f M m).X (koszulTopDeg r)) := by
  rw [← koszulDualSystemOn_map_down]
  exact map_f_koszulTopDeg_eq_id X f M hkm

/-- The transition of the dual Koszul tower is the identity on the top-degree factor, in the
spelling `AlgebraicGeometry.RingedSite.koszulDualComplexOnMap` of the one-step transition. -/
theorem koszulDualComplexOnMap_f_comp_koszulTopTermProj (m : ℕ) :
    (koszulDualComplexOnMap X f M m).f (koszulTopDeg r) ≫ koszulTopTermProj X f M m =
      koszulTopTermProj X f M (m + 1) := by
  rw [← koszulDualSystemOn_map_succ X f M m]
  exact map_f_koszulTopDeg_comp_koszulTopTermProj X f M (Nat.le_add_right m 1)

/-- **The Koszul generator map on `ℱ` dies in `ℱ/ℐ^{n+1}ℱ`**: its image is `ℐ^{n+1}ℱ` itself,
by the easy half of the pigeonhole. -/
theorem koszulGeneratorsMap_comp_adicQuotientTowerOnπ :
    koszulGeneratorsMap X f n M ≫
      Stacks.Sites.adicQuotientTowerOnπ (generatedIdealSheaf f) M n = 0 :=
  koszulGeneratorsMap_comp_cokernelπ_of_le f n M le_rfl

/-- The composite `K^n ⊗ ℱ ⟶ ℱ ⟶ ℱ/ℐ^{n+1}ℱ` out of the top-degree term of the Koszul complex
kills the incoming differential, so it descends to the top cohomology sheaf. -/
theorem d_comp_koszulTopTermProj_comp_adicQuotientTowerOnπ :
    (koszulPowerComplexOn X f M n).d ((r : ℤ) - 1) (koszulTopDeg r) ≫
        (koszulTopTermProj X f M n ≫
          Stacks.Sites.adicQuotientTowerOnπ (generatedIdealSheaf f) M n) = 0 := by
  rw [← Category.assoc, d_comp_koszulTopTermProj]
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun φ => fromCoIdxProduct X r M ≫ φ)
        (koszulGeneratorsMap_comp_adicQuotientTowerOnπ X f M n)).trans comp_zero)

/-- **The comparison `H^r(K^n ⊗ ℱ) ⟶ ℱ/ℐ^{n+1}ℱ` at one level**: the quotient map
`ℱ ⟶ ℱ/ℐ^{n+1}ℱ`, read through the unique top-degree factor, descends to the top cohomology
sheaf because the generators `f_i^{n+1}` are sections of `ℐ^{n+1}`. -/
def koszulTopHomologyToAdicQuotientAppOn :
    (koszulPowerComplexOn X f M n).homology (koszulTopDeg r) ⟶
      (Stacks.Sites.adicQuotientTowerOn (X := X) (generatedIdealSheaf f) M).obj (op n) :=
  HomologicalComplex.descTopHomology (koszulPowerComplexOn X f M n)
    (next_koszulTopDeg (r := r))
    (koszulPowerComplexOn_d_top_eq_zero' X f n M)
    ((r : ℤ) - 1) (prev_koszulTopDeg (r := r))
    (koszulTopTermProj X f M n ≫
      Stacks.Sites.adicQuotientTowerOnπ (generatedIdealSheaf f) M n)
    (d_comp_koszulTopTermProj_comp_adicQuotientTowerOnπ X f M n)

/-- The canonical map from the top-degree term to `H^r(K^n ⊗ ℱ)`, followed by the comparison
`H^r(K^n ⊗ ℱ) ⟶ ℱ/ℐ^{n+1}ℱ`, is `koszulTopTermProj` followed by the quotient map
`ℱ ⟶ ℱ/ℐ^{n+1}ℱ`. -/
@[reassoc]
theorem topToHomology_comp_koszulTopHomologyToAdicQuotientAppOn :
    HomologicalComplex.topToHomology (koszulPowerComplexOn X f M n)
          (next_koszulTopDeg (r := r))
          (koszulPowerComplexOn_d_top_eq_zero' X f n M) ≫
        koszulTopHomologyToAdicQuotientAppOn X f M n =
      koszulTopTermProj X f M n ≫
        Stacks.Sites.adicQuotientTowerOnπ (generatedIdealSheaf f) M n :=
  HomologicalComplex.topToHomology_comp_descTopHomology _ _ _ _ _ _ _

/-- The naturality square of the comparison `H^r(K^n ⊗ ℱ) ⟶ ℱ/ℐ^{n+1}ℱ` at one step of the two
towers: the transition of the Koszul tower is the identity on the top-degree factor, and the
transition of the adic quotient tower is a quotient map out of the same `ℱ`. -/
theorem homologyMap_koszulDualComplexOnMap_comp_koszulTopHomologyToAdicQuotientAppOn (n : ℕ) :
    HomologicalComplex.homologyMap (koszulDualComplexOnMap X f M n) (koszulTopDeg r) ≫
        koszulTopHomologyToAdicQuotientAppOn X f M n =
      koszulTopHomologyToAdicQuotientAppOn X f M (n + 1) ≫
        (Stacks.Sites.adicQuotientTowerOn (X := X) (generatedIdealSheaf f) M).map
          (homOfLE (Nat.le_add_right n 1)).op := by
  refine HomologicalComplex.hom_ext_topToHomology _ (next_koszulTopDeg (r := r))
    (koszulPowerComplexOn_d_top_eq_zero' X f (n + 1) M) ?_
  rw [← reassoc_of% (HomologicalComplex.topToHomology_naturality
      (koszulDualComplexOnMap X f M n) (next_koszulTopDeg (r := r))
      (koszulPowerComplexOn_d_top_eq_zero' X f (n + 1) M)
      (koszulPowerComplexOn_d_top_eq_zero' X f n M)),
    topToHomology_comp_koszulTopHomologyToAdicQuotientAppOn,
    reassoc_of% (koszulDualComplexOnMap_f_comp_koszulTopTermProj X f M n),
    topToHomology_comp_koszulTopHomologyToAdicQuotientAppOn_assoc]
  exact congrArg (fun g => koszulTopTermProj X f M (n + 1) ≫ g)
    (Stacks.Sites.adicQuotientTowerOnπ_comp_map (generatedIdealSheaf f) M
      (Nat.le_add_right n 1)).symm

/-- **The comparison of the tower of Koszul top cohomology sheaves of `ℱ` with the tower
`n ↦ ℱ/ℐⁿ⁺¹ℱ`**, as a genuine natural transformation, at an arbitrary coefficient.

At level `n` it is the quotient map `ℱ ⟶ ℱ/ℐ^{n+1}ℱ` descended to
`H^r(K(𝒪, f_1^{n+1}, …, f_r^{n+1}) ⊗ ℱ)`, which is possible because the generators `f_i^{n+1}`
are sections of `ℐ^{n+1}`. -/
def koszulTopHomologyToAdicQuotientOn :
    koszulDualSystemOn X f M ⋙
        HomologicalComplex.homologyFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (ComplexShape.up ℤ) (koszulTopDeg r) ⟶
      Stacks.Sites.adicQuotientTowerOn (X := X) (generatedIdealSheaf f) M :=
  NatTrans.ofOpSequence (koszulTopHomologyToAdicQuotientAppOn X f M) (fun n => by
    rw [show (koszulDualSystemOn X f M ⋙
          HomologicalComplex.homologyFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) (koszulTopDeg r)).map
          (homOfLE (Nat.le_add_right n 1)).op =
        HomologicalComplex.homologyMap
          ((koszulDualSystemOn X f M).map (homOfLE (Nat.le_add_right n 1)).op)
          (koszulTopDeg r) from rfl,
      koszulDualSystemOn_map_succ]
    exact homologyMap_koszulDualComplexOnMap_comp_koszulTopHomologyToAdicQuotientAppOn X f M n)

/-- The component of `koszulTopHomologyToAdicQuotientOn` at level `n` is
`koszulTopHomologyToAdicQuotientAppOn`. -/
theorem koszulTopHomologyToAdicQuotientOn_app (n : ℕ) :
    (koszulTopHomologyToAdicQuotientOn X f M).app (op n) =
      koszulTopHomologyToAdicQuotientAppOn X f M n :=
  rfl

/-- **The backward comparison `ℱ/ℐ^{m+1}ℱ ⟶ H^r(K^n ⊗ ℱ)`** supplied by the pigeonhole
containment `ℐ^{m+1}ℱ ⊆ (f_1^{n+1}, …, f_r^{n+1})ℱ`, available as soon as
`m + 1 ≥ r(n+1)+1`. -/
def adicQuotientToKoszulTopHomologyOn (m : ℕ) (hm : r * (n + 1) + 1 ≤ m + 1) :
    (Stacks.Sites.adicQuotientTowerOn (X := X) (generatedIdealSheaf f) M).obj (op m) ⟶
      (koszulPowerComplexOn X f M n).homology (koszulTopDeg r) :=
  cokernel.desc (Stacks.Sites.idealPowSmul (M := M) (generatedIdealSheaf f) (m + 1) ⊤).ι
    (koszulToTopHomologyOn X f M n)
    (ι_comp_eq_zero_of_le_idealPowSmul f n M _
      (koszulGeneratorsMap_comp_koszulToTopHomologyOn X f M n) hm le_rfl)

/-- The quotient map `ℱ ⟶ ℱ/ℐ^{m+1}ℱ` followed by the backward comparison
`ℱ/ℐ^{m+1}ℱ ⟶ H^r(K^n ⊗ ℱ)` is the canonical map `ℱ ⟶ H^r(K^n ⊗ ℱ)`. -/
@[reassoc]
theorem adicQuotientTowerOnπ_comp_adicQuotientToKoszulTopHomologyOn (m : ℕ)
    (hm : r * (n + 1) + 1 ≤ m + 1) :
    Stacks.Sites.adicQuotientTowerOnπ (generatedIdealSheaf f) M m ≫
        adicQuotientToKoszulTopHomologyOn X f M n m hm =
      koszulToTopHomologyOn X f M n :=
  cokernel.π_desc _ _ _

/-- **The two composition identities of the pro-isomorphism, forward half**: the comparison at
level `m` followed by the backward map at level `n` is the transition of the Koszul tower. Both
sides are determined by their restriction along the epimorphism
`HomologicalComplex.topToHomology`, where they become the identity on the unique top-degree
factor. -/
theorem koszulTopHomologyToAdicQuotientAppOn_comp_adicQuotientToKoszulTopHomologyOn
    (m : ℕ) (hnm : n ≤ m) (hm : r * (n + 1) + 1 ≤ m + 1) :
    koszulTopHomologyToAdicQuotientAppOn X f M m ≫
        adicQuotientToKoszulTopHomologyOn X f M n m hm =
      HomologicalComplex.homologyMap (koszulPowerComplexOnDown X f M hnm) (koszulTopDeg r) := by
  refine HomologicalComplex.hom_ext_topToHomology _ (next_koszulTopDeg (r := r))
    (koszulPowerComplexOn_d_top_eq_zero' X f m M) ?_
  rw [← HomologicalComplex.topToHomology_naturality
      (koszulPowerComplexOnDown X f M hnm) (next_koszulTopDeg (r := r))
      (koszulPowerComplexOn_d_top_eq_zero' X f m M)
      (koszulPowerComplexOn_d_top_eq_zero' X f n M),
    koszulPowerComplexOnDown_f_koszulTopDeg_eq_id,
    topToHomology_comp_koszulTopHomologyToAdicQuotientAppOn_assoc,
    adicQuotientTowerOnπ_comp_adicQuotientToKoszulTopHomologyOn, koszulToTopHomologyOn_eq,
    reassoc_of% (koszulTopTermProj_comp_koszulTopTermInj X f M m n)]

/-- **The two composition identities of the pro-isomorphism, backward half**: the backward map at
level `n` followed by the comparison at level `n` is the transition of the adic quotient
tower. -/
theorem adicQuotientToKoszulTopHomologyOn_comp_koszulTopHomologyToAdicQuotientAppOn
    (m : ℕ) (hnm : n ≤ m) (hm : r * (n + 1) + 1 ≤ m + 1) :
    adicQuotientToKoszulTopHomologyOn X f M n m hm ≫
        koszulTopHomologyToAdicQuotientAppOn X f M n =
      (Stacks.Sites.adicQuotientTowerOn (X := X) (generatedIdealSheaf f) M).map
        (homOfLE hnm).op := by
  refine (cancel_epi (Stacks.Sites.adicQuotientTowerOnπ (generatedIdealSheaf f) M m)).1 ?_
  rw [reassoc_of% (adicQuotientTowerOnπ_comp_adicQuotientToKoszulTopHomologyOn X f M n m hm),
    koszulToTopHomologyOn_eq, Category.assoc,
    topToHomology_comp_koszulTopHomologyToAdicQuotientAppOn,
    reassoc_of% (koszulTopTermInj_comp_koszulTopTermProj X f M n)]
  exact (Stacks.Sites.adicQuotientTowerOnπ_comp_map (generatedIdealSheaf f) M hnm).symm

/-- **The comparison of the Koszul top cohomology tower of `ℱ` with the tower `n ↦ ℱ/ℐⁿ⁺¹ℱ` has
eventual inverses.** At level `n` the level `max n (r(n+1))` serves: the pigeonhole containment
`ℐ^{r(n+1)+1}ℱ ⊆ (f_1^{n+1}, …, f_r^{n+1})ℱ` gives the backward quotient map, and the two
composition identities are
`koszulTopHomologyToAdicQuotientAppOn_comp_adicQuotientToKoszulTopHomologyOn` and
`adicQuotientToKoszulTopHomologyOn_comp_koszulTopHomologyToAdicQuotientAppOn`. -/
theorem hasEventualInverses_koszulTopHomologyToAdicQuotientOn :
    NoetherianAdicCompletion.HasEventualInverses
      (koszulTopHomologyToAdicQuotientOn X f M) := by
  intro n
  have hm : r * (n + 1) + 1 ≤ max n (r * (n + 1)) + 1 :=
    Nat.succ_le_succ (le_max_right _ _)
  refine ⟨max n (r * (n + 1)), le_max_left _ _,
    adicQuotientToKoszulTopHomologyOn X f M n (max n (r * (n + 1))) hm, ?_, ?_⟩
  · exact (koszulTopHomologyToAdicQuotientAppOn_comp_adicQuotientToKoszulTopHomologyOn X f M n
        (max n (r * (n + 1))) (le_max_left _ _) hm).trans
      (congrArg (fun ψ => HomologicalComplex.homologyMap ψ (koszulTopDeg r))
        (koszulDualSystemOn_map_down X f M (le_max_left n (r * (n + 1)))).symm)
  · exact adicQuotientToKoszulTopHomologyOn_comp_koszulTopHomologyToAdicQuotientAppOn X f M n
      (max n (r * (n + 1))) (le_max_left _ _) hm

/-- **The comparison at the degree `r` spelling of the top cohomology**, at an arbitrary
coefficient. The tower of `AlgebraicGeometry.RingedSite.koszulTopHomologySystem` is taken in
degree `r`, while the index type of the top-degree term of the Koszul complex carries the degree
in the spelling `r - 1 + 1`; the two integers are equal, so the existence statement transports
along that equality. -/
theorem exists_hasEventualInverses_homologyFunctor_adicQuotientTowerOn (p : ℤ)
    (hp : koszulTopDeg r = p) :
    ∃ χ : koszulDualSystemOn X f M ⋙
          HomologicalComplex.homologyFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) p ⟶
        Stacks.Sites.adicQuotientTowerOn (X := X) (generatedIdealSheaf f) M,
      NoetherianAdicCompletion.HasEventualInverses χ := by
  subst hp
  exact ⟨koszulTopHomologyToAdicQuotientOn X f M,
    hasEventualInverses_koszulTopHomologyToAdicQuotientOn X f M⟩

/-- **The tower of Koszul top cohomology sheaves of an arbitrary sheaf of modules `ℱ` is
pro-isomorphic to the tower `n ↦ ℱ/ℐⁿ⁺¹ℱ`, through a natural transformation with eventual
inverses** — on an arbitrary ringed site, at an arbitrary coefficient, with no Noetherian,
coherence or quasi-compactness hypothesis.

This is the site-level form of the pigeonhole step of [Stacks, Tag 0A0K] part (3), and the form
that `NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses`
consumes: an `InverseSequence.ProIso` records only a zig-zag at a reindexing and has no
component `X_n ⟶ Y_n` at all. The transformation itself is existentially bound only because the
tower is spelled with the top degree as `r` while the index type of the top-degree term of the
Koszul complex carries it as `r - 1 + 1`; see
`AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotientOn` for the transformation at the
second spelling.

The scheme-level form of the same statement is
`Stacks.Algebraization.koszulTopQuotientToAdicQuotient` together with
`Stacks.Algebraization.hasEventualInverses_koszulTopQuotientToAdicQuotient`. -/
theorem exists_hasEventualInverses_koszulTopHomologySystem_adicQuotientTowerOn :
    ∃ χ : koszulTopHomologySystem X f M ⟶
        Stacks.Sites.adicQuotientTowerOn (X := X) (generatedIdealSheaf f) M,
      NoetherianAdicCompletion.HasEventualInverses χ :=
  exists_hasEventualInverses_homologyFunctor_adicQuotientTowerOn X f M (r : ℤ) (by ring)

/-! ### The coefficient `𝒪`: the tower `n ↦ 𝒪/ℐⁿ⁺¹` -/

/-- **The comparison `𝒪/ℐⁿ⁺¹𝒪 ⟶ 𝒪/ℐⁿ⁺¹` at one level**, ascribed into the spelling of the two
towers.

`AlgebraicGeometry.RingedSite.adicQuotientTower` is the tower of the powers `ℐⁿ⁺¹` themselves,
while `Stacks.Sites.adicQuotientTowerOn` at `ℱ = 𝒪` is the tower of the products `ℐⁿ⁺¹𝒪`. The
two subsheaves are equal by `Stacks.Sites.idealPowSmul_top`, so the map on quotients they induce
is an isomorphism; the two towers are not the same term, which is why the identification is made
here. Its type is written through the two towers rather than through the cokernels they are
built from, so that the composites below are formed at one spelling, as
`AlgebraicGeometry.RingedSite.adicQuotientTowerπ` is. -/
def adicQuotientTowerOnUnitHomApp (n : ℕ) :
    (Stacks.Sites.adicQuotientTowerOn (X := X) (generatedIdealSheaf f)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj (op n) ⟶
      (adicQuotientTower X (generatedIdealSheaf f)).obj (op n) :=
  Stacks.SheafOfModules.Submodule.quotientMapOfLE
    (Stacks.Sites.idealPowSmul_top (generatedIdealSheaf f) (n + 1)).le

/-- The inverse of `AlgebraicGeometry.RingedSite.adicQuotientTowerOnUnitHomApp`: the map on
quotients induced by the opposite containment `ℐⁿ⁺¹ ⊆ ℐⁿ⁺¹𝒪`. -/
def adicQuotientTowerOnUnitInvApp (n : ℕ) :
    (adicQuotientTower X (generatedIdealSheaf f)).obj (op n) ⟶
      (Stacks.Sites.adicQuotientTowerOn (X := X) (generatedIdealSheaf f)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj (op n) :=
  Stacks.SheafOfModules.Submodule.quotientMapOfLE
    (Stacks.Sites.idealPowSmul_top (generatedIdealSheaf f) (n + 1)).ge

/-- The identification of the two towers carries the projection of `𝒪` onto `𝒪/ℐⁿ⁺¹𝒪` to its
projection onto `𝒪/ℐⁿ⁺¹`. -/
@[reassoc (attr := simp)]
theorem adicQuotientTowerOnπ_comp_adicQuotientTowerOnUnitHomApp (n : ℕ) :
    Stacks.Sites.adicQuotientTowerOnπ (generatedIdealSheaf f)
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n ≫
        adicQuotientTowerOnUnitHomApp X f n =
      adicQuotientTowerπ X f n :=
  Stacks.SheafOfModules.Submodule.π_comp_quotientMapOfLE
    (Stacks.Sites.idealPowSmul_top (generatedIdealSheaf f) (n + 1)).le

/-- **The comparison of the adic quotient tower at the coefficient `𝒪` with the tower
`n ↦ 𝒪/ℐⁿ⁺¹`.** Both squares are composites of quotient maps of the same `𝒪`, so they agree
after the epimorphism `Stacks.Sites.adicQuotientTowerOnπ`. -/
def adicQuotientTowerOnUnitHom :
    Stacks.Sites.adicQuotientTowerOn (X := X) (generatedIdealSheaf f)
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
      adicQuotientTower X (generatedIdealSheaf f) where
  app a := adicQuotientTowerOnUnitHomApp X f a.unop
  naturality a b φ := by
    have h1 : Stacks.Sites.adicQuotientTowerOnπ (generatedIdealSheaf f)
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) a.unop ≫
        (Stacks.Sites.adicQuotientTowerOn (X := X) (generatedIdealSheaf f)
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).map φ ≫
          adicQuotientTowerOnUnitHomApp X f b.unop =
        adicQuotientTowerπ X f b.unop := by
      rw [← Category.assoc]
      exact (congrArg (fun g => g ≫ adicQuotientTowerOnUnitHomApp X f b.unop)
          (Stacks.Sites.adicQuotientTowerOnπ_comp_map (generatedIdealSheaf f)
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (leOfHom φ.unop))).trans
        (adicQuotientTowerOnπ_comp_adicQuotientTowerOnUnitHomApp X f b.unop)
    have h2 : Stacks.Sites.adicQuotientTowerOnπ (generatedIdealSheaf f)
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) a.unop ≫
        adicQuotientTowerOnUnitHomApp X f a.unop ≫
          (adicQuotientTower X (generatedIdealSheaf f)).map φ =
        adicQuotientTowerπ X f b.unop := by
      rw [← Category.assoc]
      exact (congrArg (fun g => g ≫ (adicQuotientTower X (generatedIdealSheaf f)).map φ)
          (adicQuotientTowerOnπ_comp_adicQuotientTowerOnUnitHomApp X f a.unop)).trans
        (adicQuotientModuleπ_comp_adicQuotientTower_map X f (leOfHom φ.unop))
    exact (cancel_epi (Stacks.Sites.adicQuotientTowerOnπ (generatedIdealSheaf f)
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) a.unop)).1
      (h1.trans h2.symm)

/-- The component of `adicQuotientTowerOnUnitHom` at level `n` is
`adicQuotientTowerOnUnitHomApp`. -/
theorem adicQuotientTowerOnUnitHom_app (n : ℕ) :
    (adicQuotientTowerOnUnitHom X f).app (op n) = adicQuotientTowerOnUnitHomApp X f n :=
  rfl

/-- **The identification of the two towers has eventual inverses**, at the same level: it is an
isomorphism, the inverse at level `n` being
`AlgebraicGeometry.RingedSite.adicQuotientTowerOnUnitInvApp`. Both composites are maps on
quotients induced by `N ⊆ N`, hence identities. -/
theorem hasEventualInverses_adicQuotientTowerOnUnitHom :
    NoetherianAdicCompletion.HasEventualInverses (adicQuotientTowerOnUnitHom X f) := by
  intro n
  refine ⟨n, le_rfl, adicQuotientTowerOnUnitInvApp X f n, ?_, ?_⟩
  · refine Eq.trans ?_ ((Stacks.Sites.adicQuotientTowerOn (X := X) (generatedIdealSheaf f)
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).map_id (op n)).symm
    exact (Stacks.SheafOfModules.Submodule.quotientMapOfLE_comp
        (Stacks.Sites.idealPowSmul_top (generatedIdealSheaf f) (n + 1)).le
        (Stacks.Sites.idealPowSmul_top (generatedIdealSheaf f) (n + 1)).ge le_rfl).trans
      (Stacks.SheafOfModules.Submodule.quotientMapOfLE_self le_rfl)
  · refine Eq.trans ?_ ((adicQuotientTower X (generatedIdealSheaf f)).map_id (op n)).symm
    exact (Stacks.SheafOfModules.Submodule.quotientMapOfLE_comp
        (Stacks.Sites.idealPowSmul_top (generatedIdealSheaf f) (n + 1)).ge
        (Stacks.Sites.idealPowSmul_top (generatedIdealSheaf f) (n + 1)).le le_rfl).trans
      (Stacks.SheafOfModules.Submodule.quotientMapOfLE_self le_rfl)

/-- **The comparison `H^r(K^n) ⟶ 𝒪/ℐ^{n+1}` at one level**: the coefficient-`𝒪` case of
`AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotientAppOn`, read into the tower
`n ↦ 𝒪/ℐⁿ⁺¹`. -/
def koszulTopHomologyToAdicQuotientApp :
    (koszulPowerComplexOn X f
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n).homology
        (koszulTopDeg r) ⟶
      (adicQuotientTower X (generatedIdealSheaf f)).obj (op n) :=
  koszulTopHomologyToAdicQuotientAppOn X f
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n ≫
    adicQuotientTowerOnUnitHomApp X f n

/-- `koszulTopHomologyToAdicQuotientApp` is `koszulTopHomologyToAdicQuotientAppOn` at the
coefficient `𝒪`, followed by `adicQuotientTowerOnUnitHomApp`. -/
theorem koszulTopHomologyToAdicQuotientApp_eq :
    koszulTopHomologyToAdicQuotientApp X f n =
      koszulTopHomologyToAdicQuotientAppOn X f
          (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n ≫
        adicQuotientTowerOnUnitHomApp X f n :=
  rfl

/-- The canonical map from the top-degree term to `H^r(K^n)`, followed by the comparison
`H^r(K^n) ⟶ 𝒪/ℐ^{n+1}`, is `koszulTopTermProj` followed by the projection `adicQuotientTowerπ`. -/
@[reassoc]
theorem topToHomology_comp_koszulTopHomologyToAdicQuotientApp :
    HomologicalComplex.topToHomology
          (koszulPowerComplexOn X f
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n)
          (next_koszulTopDeg (r := r))
          (koszulPowerComplexOn_d_top_eq_zero' X f n
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ≫
        koszulTopHomologyToAdicQuotientApp X f n =
      koszulTopTermProj X f (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) n ≫
        adicQuotientTowerπ X f n := by
  rw [koszulTopHomologyToAdicQuotientApp_eq, ← Category.assoc,
    topToHomology_comp_koszulTopHomologyToAdicQuotientAppOn, Category.assoc,
    adicQuotientTowerOnπ_comp_adicQuotientTowerOnUnitHomApp]

/-- **The comparison of the tower of Koszul top cohomology sheaves of `𝒪` with the tower
`n ↦ 𝒪/ℐⁿ⁺¹`**, as a genuine natural transformation: the coefficient-`𝒪` case of
`AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotientOn`, read into the tower
`n ↦ 𝒪/ℐⁿ⁺¹`.

At level `n` it is the quotient map `𝒪 ⟶ 𝒪/ℐ^{n+1}` descended to
`H^r(K(𝒪, f_1^{n+1}, …, f_r^{n+1}))`, which is possible because the generators `f_i^{n+1}` are
sections of `ℐ^{n+1}`. -/
def koszulTopHomologyToAdicQuotient :
    koszulDualSystemOn X f (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⋙
        HomologicalComplex.homologyFunctor
          (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (ComplexShape.up ℤ) (koszulTopDeg r) ⟶
      adicQuotientTower X (generatedIdealSheaf f) :=
  koszulTopHomologyToAdicQuotientOn X f
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≫
    adicQuotientTowerOnUnitHom X f

/-- The component of `koszulTopHomologyToAdicQuotient` at level `n` is
`koszulTopHomologyToAdicQuotientApp`. -/
theorem koszulTopHomologyToAdicQuotient_app (n : ℕ) :
    (koszulTopHomologyToAdicQuotient X f).app (op n) =
      koszulTopHomologyToAdicQuotientApp X f n :=
  rfl

/-- **The comparison of the Koszul top cohomology tower of `𝒪` with the tower `n ↦ 𝒪/ℐⁿ⁺¹` has
eventual inverses**: the coefficient-`𝒪` case of
`AlgebraicGeometry.RingedSite.hasEventualInverses_koszulTopHomologyToAdicQuotientOn`, composed
with the identification of the two towers. -/
theorem hasEventualInverses_koszulTopHomologyToAdicQuotient :
    NoetherianAdicCompletion.HasEventualInverses (koszulTopHomologyToAdicQuotient X f) :=
  (hasEventualInverses_koszulTopHomologyToAdicQuotientOn X f
      (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).comp
    (hasEventualInverses_adicQuotientTowerOnUnitHom X f)

/-- **The comparison at the degree `r` spelling of the top cohomology.** The tower of
`AlgebraicGeometry.RingedSite.koszulTopHomologySystem` is taken in degree `r`, while the index
type of the top-degree term of the Koszul complex carries the degree in the spelling `r - 1 + 1`;
the two integers are equal, so the existence statement transports along that equality. -/
theorem exists_hasEventualInverses_homologyFunctor_adicQuotientTower (p : ℤ)
    (hp : koszulTopDeg r = p) :
    ∃ χ : koszulDualSystemOn X f
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⋙
          HomologicalComplex.homologyFunctor
            (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ) p ⟶
        adicQuotientTower X (generatedIdealSheaf f),
      NoetherianAdicCompletion.HasEventualInverses χ := by
  subst hp
  exact ⟨koszulTopHomologyToAdicQuotient X f,
    hasEventualInverses_koszulTopHomologyToAdicQuotient X f⟩

/-- **The tower of Koszul top cohomology sheaves of `𝒪` is pro-isomorphic to the tower
`n ↦ 𝒪/ℐⁿ⁺¹`, through a natural transformation with eventual inverses** — on an arbitrary ringed
site, with no Noetherian, coherence or quasi-compactness hypothesis.

This is the coefficient-`𝒪` case of
`exists_hasEventualInverses_koszulTopHomologySystem_adicQuotientTowerOn`. The transformation is
existentially bound only because the tower is spelled with the top degree as `r`, while the index
type of the top-degree term of the Koszul complex carries it as `r - 1 + 1`;
`AlgebraicGeometry.RingedSite.koszulTopHomologyToAdicQuotient` is the transformation at the second
spelling. -/
theorem exists_hasEventualInverses_koszulTopHomologySystem_adicQuotientTower :
    ∃ χ : koszulTopHomologySystem X f
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
        adicQuotientTower X (generatedIdealSheaf f),
      NoetherianAdicCompletion.HasEventualInverses χ :=
  exists_hasEventualInverses_homologyFunctor_adicQuotientTower X f (r : ℤ) (by ring)

end Comparison

/-! ### The pinned presentation of the completion over the adic quotient tower -/

section Presentation

open Stacks.Sites Stacks.SheafOfModules.ImageSubsheaf
open scoped IsMulCommutative

attribute [local instance] HasDerivedCategory.standard hasFiniteBiproducts_sheafOfModules
  hasSheafCompose_forget₂_ringCat

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [HasWeakSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [HasWeakSheafify X.J CommRingCat.{u}] {r : ℕ}
  (f : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- A natural isomorphism of towers has eventual inverses, at the same level. -/
private theorem hasEventualInverses_of_isIso {C : Type u₁} [Category.{v₁} C] {F G : ℕᵒᵖ ⥤ C}
    (φ : F ⟶ G) [IsIso φ] : NoetherianAdicCompletion.HasEventualInverses φ := fun n => by
  refine ⟨n, le_rfl, inv (φ.app (op n)), ?_, ?_⟩ <;> simp

/-- **The comparison of the coefficient-free dual Koszul tower with the tower `n ↦ 𝒪/ℐⁿ⁺¹` in
degree zero, with eventual inverses.**

Four steps compose. The identification of [Stacks, Tag 0A0E]'s tower at the coefficient object
`𝒪` with the dual Koszul tower (`AlgebraicGeometry.RingedSite.koszulTensorDualSystemIso`) and the
absorption of that coefficient into the Koszul complex
(`AlgebraicGeometry.RingedSite.koszulTensorDualSystemCoefficientIso`) are isomorphisms of towers,
so they have eventual inverses at the same level; [Stacks, Tag 0G3D] across the shift by `r` is
`AlgebraicGeometry.RingedSite.hasEventualInverses_koszulShiftedDualToTopSingle`, where the
pro-vanishing hypothesis is used; and the last step is the pigeonhole comparison
`exists_hasEventualInverses_koszulTopHomologySystem_adicQuotientTower`, whiskered into degree
zero of the derived category. -/
theorem exists_hasEventualInverses_derivedSheafHomSystem_adicQuotientTower
    (hpz : ∀ (n : ℕ) (p : ℤ), p < r → ∃ (m : ℕ) (_ : n ≤ m),
      HomologicalComplex.homologyMap
        ((koszulDualSystemOn X f
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).map
          (homOfLE ‹n ≤ m›).op) p = 0) :
    ∃ ψ : derivedSheafHomSystem X (koszulPowerSystem X f ⋙ DerivedCategory.Q)
          (derivedStructureSheaf X) ⟶
        adicQuotientTower X (generatedIdealSheaf f) ⋙
          DerivedCategory.singleFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0,
      NoetherianAdicCompletion.HasEventualInverses ψ := by
  obtain ⟨χ, hχ⟩ := exists_hasEventualInverses_koszulTopHomologySystem_adicQuotientTower X f
  exact ⟨_, (hasEventualInverses_of_isIso (koszulTensorDualSystemIso X f
    (derivedStructureSheaf X)).inv).comp ((hasEventualInverses_of_isIso
      (koszulTensorDualSystemCoefficientIso X f
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).hom).comp
      ((hasEventualInverses_koszulShiftedDualToTopSingle X f
        (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) hpz).comp
          (hχ.whiskerRight _)))⟩

/-- **Part (1) of [Stacks, Tag 0A0K] over the adic quotient tower, on an arbitrary ringed site,
with the pro-vanishing of the Koszul cohomology sheaves below the top degree as the only
hypothesis**: the Čech completion `K^∧` of an **arbitrary** object `K` of `D(𝒪)` is a derived
limit of the tower `n ↦ K ⊗^𝐋_𝒪 𝒪/ℐⁿ⁺¹`, through named projections.

[Stacks, Tag 0A0E] with its projections pinned
(`isDerivedLimitWithProjections_tensorDerivedDualSystem_koszulPowerSystem_completion`) presents
`K^∧` over the tower `n ↦ K ⊗^𝐋_𝒪 (K^n)^∨`, which is the coefficient-free dual tower whiskered
by `K ⊗^𝐋 -`; the comparison of that tower with `n ↦ 𝒪/ℐⁿ⁺¹` in degree zero is
`AlgebraicGeometry.RingedSite.exists_hasEventualInverses_derivedSheafHomSystem_adicQuotientTower`,
whiskered by the same functor, and
`NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses` carries the
projections across. The coefficient object enters both towers as that one whiskering functor, so
no constraint of the derived tensor product is used.

No quasi-compactness and nothing Noetherian is assumed here: the hypothesis `hpz` is the exact
content quasi-compactness is spent on in the scheme-level chain, and
`Stacks.KoszulProZero.exists_koszulDualSystemOn_homologyMap_eq_zero_of_model` and
`Stacks.KoszulProZero.exists_koszulDualSystemOn_over_homologyMap_eq_zero` discharge it — at a
flat Noetherian model, and on the slice over an affine open of a merely locally Noetherian
scheme. -/
theorem exists_isDerivedLimitWithProjections_adicReductionTower_completion
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    [HasProduct fun n : ℕ ↦ (derivedSheafHomSystem X
      (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op n)]
    [HasProduct fun n : ℕ ↦ (tensorDerivedDualSystem X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
      (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op n)]
    [HasProduct fun n : ℕ ↦ (adicReductionTower X (generatedIdealSheaf f) K).obj (op n)]
    (hpz : ∀ (n : ℕ) (p : ℤ), p < r → ∃ (m : ℕ) (_ : n ≤ m),
      HomologicalComplex.homologyMap
        ((koszulDualSystemOn X f
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).map
          (homOfLE ‹n ≤ m›).op) p = 0) :
    ∃ p : ∀ n : ℕ, (completionFunctor X f).obj K ⟶
        (adicReductionTower X (generatedIdealSheaf f) K).obj ⟨n⟩,
      NoetherianAdicCompletion.IsDerivedLimitWithProjections
        (adicReductionTower X (generatedIdealSheaf f) K)
        ((completionFunctor X f).obj K) p := by
  obtain ⟨ψ, hψ⟩ := exists_hasEventualInverses_derivedSheafHomSystem_adicQuotientTower X f hpz
  exact ⟨_, NoetherianAdicCompletion.IsDerivedLimitWithProjections.comp_of_hasEventualInverses
    (Functor.whiskerRight ψ
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).tensor.obj K))
    (hψ.whiskerRight _)
    (isDerivedLimitWithProjections_tensorDerivedDualSystem_koszulPowerSystem_completion X f K)⟩

/-- **Part (1) of [Stacks, Tag 0A0K] over the adic quotient tower, as the derived-limit
predicate.** The projections of
`AlgebraicGeometry.RingedSite.exists_isDerivedLimitWithProjections_adicReductionTower_completion`
forgotten. -/
theorem isDerivedLimit_adicReductionTower_completion
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    [HasProduct fun n : ℕ ↦ (derivedSheafHomSystem X
      (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op n)]
    [HasProduct fun n : ℕ ↦ (tensorDerivedDualSystem X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
      (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op n)]
    [HasProduct fun n : ℕ ↦ (adicReductionTower X (generatedIdealSheaf f) K).obj (op n)]
    (hpz : ∀ (n : ℕ) (p : ℤ), p < r → ∃ (m : ℕ) (_ : n ≤ m),
      HomologicalComplex.homologyMap
        ((koszulDualSystemOn X f
            (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).map
          (homOfLE ‹n ≤ m›).op) p = 0) :
    CategoryTheory.Pretriangulated.IsDerivedLimit
      (adicReductionTower X (generatedIdealSheaf f) K) ((completionFunctor X f).obj K) := by
  obtain ⟨p, hp⟩ :=
    exists_isDerivedLimitWithProjections_adicReductionTower_completion X f K hpz
  exact hp.isDerivedLimit

/-- **Part (1) of [Stacks, Tag 0A0K] over the adic quotient tower at a flat Noetherian model,
with no quasi-compactness anywhere.**

`Stacks.KoszulProZero.exists_koszulDualSystemOn_homologyMap_eq_zero_of_model` discharges the
pro-vanishing hypothesis on a ringed site carrying one flat Noetherian model uniform over a
basis: a Noetherian ring `A`, elements `a_1, …, a_r ∈ A` and a finite `A`-module `M` such that
every object is covered by objects `V` over which `𝒪(V)` is an `A`-algebra carrying `a_i` to
`f_i|_V` and `𝒪(V)` is the base change of `M` along a flat `A`-module. The Artin–Rees level is
computed once over the model, so no cover is maximised over and no quasi-compactness enters. -/
theorem isDerivedLimit_adicReductionTower_completion_of_model
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasCoproduct ((koszulPowerSystem X f ⋙ DerivedCategory.Q).obj)]
    [HasProduct fun n : ℕ ↦ (derivedSheafHomSystem X
      (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op n)]
    [HasProduct fun n : ℕ ↦ (tensorDerivedDualSystem X
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)
      (koszulPowerSystem X f ⋙ DerivedCategory.Q) K).obj (op n)]
    [HasProduct fun n : ℕ ↦ (adicReductionTower X (generatedIdealSheaf f) K).obj (op n)]
    (A : Type u) [CommRing A] [IsNoetherianRing A] (a : Fin r → A)
    (M : ModuleCat.{u} A) [Module.Finite A M]
    (hmodel : ∀ U : X.Cᵒᵖ, ∃ P : Presieve U.unop, Sieve.generate P ∈ X.J U.unop ∧
      ∀ ⦃V : X.C⦄ (g : V ⟶ U.unop), P g →
        ∃ (ρ : A →+* (X.O.obj.obj (op V))) (S : ModuleCat.{u} A),
          (∀ i, ρ (a i) = globalSectionVal (f i) (op V)) ∧ Module.Flat A S ∧
            Nonempty ((Stacks.KoszulProZero.modelSectionsFunctor X (op V) ρ).obj
                (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ≅
              (Stacks.KoszulCoefficientProIso.rTensorFunctor S).obj M)) :
    CategoryTheory.Pretriangulated.IsDerivedLimit
      (adicReductionTower X (generatedIdealSheaf f) K) ((completionFunctor X f).obj K) :=
  isDerivedLimit_adicReductionTower_completion X f K
    (fun n p hp => Stacks.KoszulProZero.exists_koszulDualSystemOn_homologyMap_eq_zero_of_model
      X f (SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) A a M hmodel n p hp)

end Presentation

end AlgebraicGeometry.RingedSite

end
