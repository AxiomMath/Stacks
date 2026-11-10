module

public import StacksFrontier.AlgebraicGeometry.AmpleCharacterization.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecFormula
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MulSecInjective
public import StacksFrontier.AlgebraicGeometry.SectionProduct.MonoidalUnitBridge
public import StacksFrontier.AlgebraicGeometry.ModuleSectionExtension.Basic

/-!
# Clauses (5) and (6) of Stacks Tag 01Q3

Clauses (5) and (6) of [Stacks, Tag 01Q3] say that for every quasi-coherent sheaf `F` on `X` —
respectively for every quasi-coherent sheaf of ideals — the sum of the images of the canonical
maps

`Γ(X, F ⊗_{𝒪_X} L^{⊗ n}) ⊗_𝐙 L^{⊗ -n} ⟶ F`,  `n ≥ 1`,

equals `F`. This file states those maps, states the two clauses, and proves both from ampleness,
which is clause (1).

## Main definitions

* `Stacks.AmpleCharacterization.unitHom`: a global section of `M` as a morphism out of the
  monoidal unit, the form `Stacks.TensorSectionNonvanishing.mulRight` takes a section in.
* `Stacks.AmpleCharacterization.negTensorCancelIso`: `L ^⊗ (-n) ⊗ L ^⊗ n ≅ 𝒪_X`.
* `Stacks.AmpleCharacterization.twistHom`: **the canonical map** `L ^⊗ (-n) ⟶ F` attached to one
  global section of `F ⊗ L ^⊗ n`.

## Main results

* `Stacks.AmpleCharacterization.whiskerRight_twistHom`: the property that defines `twistHom`.
* `Stacks.AmpleCharacterization.comp_mulRight`: multiplication by a fixed global section is
  natural.
* `Stacks.AmpleCharacterization.bijective_mapFun_mulRight_unitHom`: multiplication by a global
  section of an invertible module is bijective on the stalk at every point where it does not
  vanish — clause 2 of [Stacks, Tag 01CY] in whiskered form, with the section given as a global
  section.
* `Stacks.AmpleCharacterization.exists_mem_range_twistHom`: **every germ of a quasi-coherent `F`
  is in the image of a single one of the maps**, for `L` ample.
* `Stacks.AmpleCharacterization.iSup_range_twistHom_eq_top_of_isAmple`: **clause (5)**.
* `Stacks.AmpleCharacterization.iSup_range_twistHom_ideal_eq_top_of_isAmple`: **clause (6)**.

## Why `twistHom` is defined by its universal property

Tensoring by `L ^⊗ n` is an equivalence of `X.Modules`
(`Stacks.AmpleGlobalGeneration.isEquivalence_tensorRight`), and after tensoring, the clause's map
attached to `m` becomes the evaluation isomorphism `L^{⊗ -n} ⊗ L^{⊗ n} ≅ 𝒪_X` followed by `m`.
An equivalence is faithful, so that property determines the map, and taking it as the definition
avoids evaluating the monoidal structure of `X.Modules` on sections — which is localized from the
sectionwise one and has no formula (see
`StacksFrontier/AlgebraicGeometry/SectionTensorFormula/Basic.lean`).

The whole proof is then run through that property. Multiplication by `σ` is natural, so

`twistHom L F n m ≫ mulRight F σ = (mulRight L^{⊗ -n} σ ≫ evaluation) ≫ m`,

and on the stalk at a point where `σ` does not vanish, multiplication by `σ` is bijective; so
dividing by `σ` — which is what the source's "`t` is the image of `τ ⊗ σ^{-1}`" does — is
injectivity of that bijection. No inverse of `σ` is ever constructed.

## The equality of subsheaves is read on stalks

Clause (5) asserts an equality of subsheaves of `F`. It is stated here as the equality, at every
point, of the sum of the images of the induced maps on stalks with the whole stalk. For sheaves of
modules the two are the same assertion: the stalk functor is exact and commutes with the filtered
colimit that computes a sum of subsheaves, and a subsheaf whose every stalk is the whole stalk is
the whole sheaf. This is also the form in which every other generation statement in this
repository is phrased — `Stacks.AmpleLocalGeneration.IsFinGenOn`,
`Stacks.SectionTensorFormula.span_germ_tensorSection_eq_top` — and the form clause (5)'s consumers
use.

## The converses

**Both converses are proved**, in `./ClauseSixConverse.lean`. The source closes its cycle by
`(6) ⇒ (1)`: given an affine open `U ∋ x`, it takes the quasi-coherent sheaf of ideals of the
reduced closed subscheme `X ∖ U` (Schemes, Section 01IZ), applies clause (6) to it, and gets a
section of `L ^⊗ n` not vanishing at `x` and vanishing along `X ∖ U`, so that `X_s ⊆ U` is affine
by [Stacks, Tag 01PV]. That sheaf of ideals is `Stacks.ComplementIdeal.sheaf`, assembled in
`./ComplementIdeal.lean` out of Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal` and
`Stacks.Divisors.idealSheafOfModules`; Tag 01PV is
`Stacks.NonvanishingAffineIntersection.isAffineOfLeAffine`. The implications are
`Stacks.AmpleCharacterization.isAmple_of_iSup_range_twistHom_ideal` and
`Stacks.AmpleCharacterization.isAmple_of_iSup_range_twistHom`.

## References

* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TopologicalSpace Opposite
open Stacks.Ample
open Stacks.TensorSectionNonvanishing (mulRight mulSec)

universe u

namespace Stacks.AmpleCharacterization

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory
  Stacks.SectionRingGeometric.schemePreadditive
  Stacks.SectionRingGeometric.schemeTensorRightAdditive

variable {X : Scheme.{u}} (L : X.Modules) [IsInvertibleModule X L]

/-! ### Multiplication by a global section is natural -/

/-- **Multiplication by a fixed global section of `G` is natural.** -/
theorem comp_mulRight {A A' G : X.Modules} (g : A ⟶ A') (f : 𝟙_ X.Modules ⟶ G) :
    g ≫ mulRight A' f = mulRight A f ≫ (g ▷ G) := by
  rw [Stacks.TensorSectionNonvanishing.mulRight, Stacks.TensorSectionNonvanishing.mulRight,
    ← Category.assoc, rightUnitor_inv_naturality, Category.assoc, ← whisker_exchange,
    Category.assoc]

/-! ### Global sections as morphisms out of the monoidal unit -/

/-- A global section of `M`, as a morphism out of the monoidal unit. -/
def unitHom (M : X.Modules) (m : Γ(M, ⊤)) : 𝟙_ X.Modules ⟶ M :=
  Stacks.SectionProduct.ofUnitHom
    (M.unitHomEquiv.symm ((Stacks.NonvanishingSpelling.sectionsEquiv X M).symm m))

/-- `Stacks.AmpleCharacterization.unitHom` carries the canonical unit section over `U` to the
restriction of `m`. -/
theorem app_monoidalUnitSection_unitHom (M : X.Modules) (m : Γ(M, ⊤)) (U : X.Opens) :
    (unitHom M m).app U (Stacks.SectionProduct.monoidalUnitSection X U) =
      Stacks.SectionExtension.resTop U m :=
  Stacks.SectionProduct.app_monoidalUnitSection_ofUnitHom M _ U

/-- Multiplication by `m`, on sections, is the sectionwise product with the restriction of
`m`. -/
theorem mulSec_unitHom (F M : X.Modules) (m : Γ(M, ⊤)) {U : X.Opens} (t : Γ(F, U)) :
    (mulRight F (unitHom M m)).app U t =
      Stacks.SectionTensorFormula.tensorSection F M t (Stacks.SectionExtension.resTop U m) :=
  Stacks.SectionProduct.mulSec_ofUnitHom_eq_tensorSection F M _ t

/-- **Multiplication by a global section of an invertible module that vanishes nowhere on `W`
is bijective on the stalk at every point of `W`.** This is clause 2 of [Stacks, Tag 01CY] in
whiskered form, `Stacks.SectionProduct.bijective_mapFun_mulRight_unitHomEquiv_symm`, with its
section given as a global section. -/
theorem bijective_mapFun_mulRight_unitHom (F M : X.Modules) [IsInvertibleModule X M]
    (σ : Γ(M, ⊤)) {W : X.Opens} {x : X} (hx : x ∈ W)
    (hW : ∀ y ∈ W, y ∈ nonvanishingLocus M σ) :
    Function.Bijective (Stacks.ModuleStalk.mapFun (mulRight F (unitHom M σ)) x) := by
  obtain ⟨N, ⟨ψ⟩⟩ := Stacks.SectionProduct.exists_tensorSheaf_iso_unit M
  exact Stacks.SectionProduct.bijective_mapFun_mulRight_unitHomEquiv_symm F M N ψ
    ((Stacks.NonvanishingSpelling.sectionsEquiv X M).symm σ) hx
    fun y hy => (Stacks.NonvanishingSpelling.stalkNonvanishingLocus_symm_eq X M σ).ge (hW y hy)

/-! ### The canonical morphism out of a negative twist -/

/-- `L ^⊗ (-n) ⊗ L ^⊗ n ≅ 𝒪_X`, the evaluation isomorphism of Stacks Tag 01CU read through the
braiding. -/
def negTensorCancelIso (n : ℤ) :
    tensorPowModule X L (-n) ⊗ tensorPowModule X L n ≅ 𝟙_ X.Modules :=
  β_ _ _ ≪≫ AlgebraicGeometry.SheafOfModules.tensorPowMulNegIso X.presheaf
    (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf X) L n

/-- **The canonical morphism `L ^⊗ (-n) ⟶ F` attached to a global section `m` of
`F ⊗ L ^⊗ n`.** This is the map whose images clauses (5) and (6) of [Stacks, Tag 01Q3] sum over:
the clause's map `Γ(X, F ⊗ L^{⊗ n}) ⊗_𝐙 L^{⊗ -n} ⟶ F` is, by definition of a tensor product over
`𝐙`, the sum of these over `m ∈ Γ(X, F ⊗ L^{⊗ n})`, so its image is the sum of their images.

It is defined by the property that pins it. Tensoring by `L ^⊗ n` is an equivalence
(`Stacks.AmpleGlobalGeneration.isEquivalence_tensorRight`), hence faithful, and after tensoring
the clause's map becomes `L^{⊗ -n} ⊗ L^{⊗ n} ≅ 𝒪_X --m--> F ⊗ L^{⊗ n}`: the evaluation
isomorphism of Stacks Tag 01CU followed by the global section `m`. That is exactly what
`Stacks.AmpleCharacterization.whiskerRight_twistHom` says, and faithfulness makes it a
definition. -/
def twistHom (F : X.Modules) (n : ℤ) (m : Γ(F ⊗ tensorPowModule X L n, ⊤)) :
    tensorPowModule X L (-n) ⟶ F :=
  haveI := Stacks.AmpleGlobalGeneration.isEquivalence_tensorRight L n
  (CategoryTheory.MonoidalCategory.tensorRight (tensorPowModule X L n)).preimage
    ((negTensorCancelIso L n).hom ≫ unitHom (F ⊗ tensorPowModule X L n) m)

/-- **The property that defines `Stacks.AmpleCharacterization.twistHom`.** -/
theorem whiskerRight_twistHom (F : X.Modules) (n : ℤ)
    (m : Γ(F ⊗ tensorPowModule X L n, ⊤)) :
    twistHom L F n m ▷ tensorPowModule X L n =
      (negTensorCancelIso L n).hom ≫ unitHom (F ⊗ tensorPowModule X L n) m := by
  have := Stacks.AmpleGlobalGeneration.isEquivalence_tensorRight L n
  exact (CategoryTheory.MonoidalCategory.tensorRight (tensorPowModule X L n)).map_preimage _

/-! ### Stalk bookkeeping -/

/-- An isomorphism of `𝒪_X`-modules is bijective on every stalk. -/
theorem bijective_mapFun_of_iso {M N : X.Modules} (e : M ≅ N) (x : X) :
    Function.Bijective (Stacks.ModuleStalk.mapFun e.hom x) :=
  Stacks.SectionProduct.mapFun_bijective_of_isIso e.hom x

/-! ### Clause (5) from ampleness -/

open scoped Stacks.ModuleStalk

/-- **Every germ of a quasi-coherent module on a scheme carrying an ample invertible module lies
in the image of one of the maps of clause (5) of [Stacks, Tag 01Q3]** — not merely in the sum of
those images.

This is the source's argument. A germ at `x` is the germ of a section `t` over some open `V`;
clause (3) puts a nonvanishing open `X_s ⊆ V` through `x`, and the module-valued form of
[Stacks, Tag 01PW] (`Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_family_of`
`_isAmple`) produces a degree `p ≥ 1`, a global section `σ` of `L ^⊗ p` with `X_σ = X_s`, and a
global section `τ` of `F ⊗ L ^⊗ p` restricting on `X_s` to `t ⊗ σ`. In the source's words, `t` is
the image of `τ ⊗ σ^{-1}`.

The division by `σ` is carried out on the stalk, where multiplying by `σ` is **bijective**
(clause 2 of [Stacks, Tag 01CY], `Stacks.AmpleCharacterization`
`.bijective_mapFun_mulRight_unitHom`): naturality of multiplication by `σ` turns the defining
property of `twistHom` into the equation `twistHom · (mulRight σ) = (mulRight σ · evaluation) · τ`,
and injectivity of multiplication by `σ` at `x` cancels it. -/
theorem exists_mem_range_twistHom (hL : IsAmple X L) (F : X.Modules) [F.IsQuasicoherent]
    (x : X) (g : TopCat.Presheaf.stalk (C := Ab.{u}) F.presheaf x) :
    ∃ (n : ℕ) (_ : 1 ≤ n) (m : Γ(F ⊗ tensorPowModule X L (n : ℤ), ⊤)),
      g ∈ LinearMap.range (Stacks.ModuleStalk.map (twistHom L F (n : ℤ) m) x) := by
  obtain ⟨V, hxV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq F.presheaf g
  obtain ⟨N, hN, s, hxs, hsV⟩ :=
    Stacks.SectionExtension.isBasisNonvanishing_of_isAmple X L hL x V hxV
  obtain ⟨p, σ, τ, ⟨e, he, hpe⟩, hUeq, hres⟩ :=
    Stacks.ModuleSectionExtension.exists_tensorPow_tensorSection_family_of_isAmple L hL F hN s
      (κ := PUnit.{u + 1}) fun _ => F.presheaf.map (homOfLE hsV).op t
  have hp : 1 ≤ p := by
    rw [hpe]
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  refine ⟨p, hp, τ PUnit.unit, ?_⟩
  have hWσ : ∀ y ∈ Stacks.AmpleTheory.powNonvanishingOpen X L N s,
      y ∈ nonvanishingLocus (tensorPowModule X L (p : ℤ)) σ := by
    intro y hy
    rw [hUeq] at hy
    exact hy
  have hbij1 := bijective_mapFun_mulRight_unitHom F (tensorPowModule X L (p : ℤ)) σ hxs hWσ
  have hbij2 := bijective_mapFun_mulRight_unitHom (tensorPowModule X L (-(p : ℤ)))
    (tensorPowModule X L (p : ℤ)) σ hxs hWσ
  have hbiju : Function.Bijective (Stacks.ModuleStalk.mapFun
      (mulRight (tensorPowModule X L (-(p : ℤ))) (unitHom _ σ) ≫
        (negTensorCancelIso L (p : ℤ)).hom) x) := by
    have hfun : Stacks.ModuleStalk.mapFun
        (mulRight (tensorPowModule X L (-(p : ℤ))) (unitHom _ σ) ≫
          (negTensorCancelIso L (p : ℤ)).hom) x =
        Stacks.ModuleStalk.mapFun (negTensorCancelIso L (p : ℤ)).hom x ∘
          Stacks.ModuleStalk.mapFun
            (mulRight (tensorPowModule X L (-(p : ℤ))) (unitHom _ σ)) x :=
      funext fun w => Stacks.ModuleStalk.mapFun_comp _ _ x w
    rw [hfun]
    exact (bijective_mapFun_of_iso (negTensorCancelIso L (p : ℤ)) x).comp hbij2
  obtain ⟨v, hv⟩ := hbiju.2 (((𝟙_ X.Modules).presheaf.germ
    (Stacks.AmpleTheory.powNonvanishingOpen X L N s) x hxs).hom
      (Stacks.SectionProduct.monoidalUnitSection X _))
  have hB : twistHom L F (p : ℤ) (τ PUnit.unit) ≫
        mulRight F (unitHom (tensorPowModule X L (p : ℤ)) σ) =
      (mulRight (tensorPowModule X L (-(p : ℤ))) (unitHom (tensorPowModule X L (p : ℤ)) σ) ≫
          (negTensorCancelIso L (p : ℤ)).hom) ≫
        unitHom (F ⊗ tensorPowModule X L (p : ℤ)) (τ PUnit.unit) := by
    rw [comp_mulRight, whiskerRight_twistHom, Category.assoc]
  refine ⟨v, ?_⟩
  rw [Stacks.ModuleStalk.map_apply,
    ← TopCat.Presheaf.germ_res_apply F.presheaf (homOfLE hsV) x hxs t]
  refine hbij1.1 ?_
  rw [← Stacks.ModuleStalk.mapFun_comp, hB, Stacks.ModuleStalk.mapFun_comp, hv,
    Stacks.ModuleStalk.mapFun_germ, Stacks.ModuleStalk.mapFun_germ,
    app_monoidalUnitSection_unitHom, mulSec_unitHom, ← hres PUnit.unit]

/-- **Clause (5) of [Stacks, Tag 01Q3]** — the clause labelled 01Q8: for every quasi-coherent
sheaf `F` on `X` the sum of the images of the canonical maps
`Γ(X, F ⊗ L^{⊗ n}) ⊗_𝐙 L^{⊗ -n} ⟶ F`, over `n ≥ 1`, equals `F`.

The `n`-th canonical map is the sum over `m ∈ Γ(X, F ⊗ L^{⊗ n})` of the maps
`Stacks.AmpleCharacterization.twistHom L F n m`, a tensor product over `𝐙` with a free abelian
group being the direct sum; so the sum of the images of the canonical maps is the sum of the
images of the `twistHom L F n m`, which is what is written.

**The equality of subsheaves is read on stalks**, as `Stacks.AmpleLocalGeneration.IsFinGenOn` and
every other generation statement in this repository is. For sheaves of modules the two readings
agree: the stalk functor is exact and commutes with the filtered colimit defining a sum of
subsheaves, and a submodule of `F` whose stalks are all of `F` is `F`. What is proved is in fact
stronger than the clause and is what the source's proof gives — every germ lies in the image of a
*single* one of the maps, by `Stacks.AmpleCharacterization.exists_mem_range_twistHom`. -/
@[stacks 01Q3 "clause (5)", ega "II 4.5.5" "(a) ⇒ (b)"]
theorem iSup_range_twistHom_eq_top_of_isAmple (hL : IsAmple X L) :
    ∀ F : X.Modules, F.IsQuasicoherent → ∀ x : X,
      (⨆ (n : ℕ) (_ : 1 ≤ n) (m : Γ(F ⊗ tensorPowModule X L (n : ℤ), ⊤)),
        LinearMap.range (Stacks.ModuleStalk.map (twistHom L F (n : ℤ) m) x)) = ⊤ := by
  intro F hF x
  have := hF
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨n, hn, m, hmem⟩ := exists_mem_range_twistHom L hL F x g
  exact Submodule.mem_iSup_of_mem n
    (Submodule.mem_iSup_of_mem hn (Submodule.mem_iSup_of_mem m hmem))

/-- **Clause (6) of [Stacks, Tag 01Q3]** — the clause labelled 01Q9: clause (5) with `F` ranging
over the quasi-coherent sheaves of ideals of `X`.

A sheaf of ideals is a module `J` with a monomorphism into `𝒪_X`. The clause is clause (5) with
its quantifier restricted, which is why the source proves it by the single word "clearly"; the
restriction is recorded here rather than left implicit because clauses (6) and (9) are the two
the source's cycle re-enters ampleness through. -/
@[stacks 01Q3 "clause (6)", ega "II 4.5.5" "(a) ⇒ (b), ideals"]
theorem iSup_range_twistHom_ideal_eq_top_of_isAmple (hL : IsAmple X L) :
    ∀ (J : X.Modules) (j : J ⟶ Stacks.Ample.unitModule X), Mono j → J.IsQuasicoherent →
      ∀ x : X, (⨆ (n : ℕ) (_ : 1 ≤ n) (m : Γ(J ⊗ tensorPowModule X L (n : ℤ), ⊤)),
        LinearMap.range (Stacks.ModuleStalk.map (twistHom L J (n : ℤ) m) x)) = ⊤ :=
  fun J _ _ hJ => iSup_range_twistHom_eq_top_of_isAmple L hL J hJ

end Stacks.AmpleCharacterization

end
