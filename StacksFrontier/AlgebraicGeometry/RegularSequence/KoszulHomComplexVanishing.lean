module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.KoszulExteriorLocalBasis
public import StacksFrontier.Algebra.Homology.ChainComplexAsCochainComplex
public import StacksFrontier.AlgebraicGeometry.RegularSequence.KoszulQuotientAnnihilation
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplexVanishingDifferential
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.ExtFromStrictlyPerfectResolution

/-!
# The Hom complex from the Koszul complex into the quotient has vanishing differential

Let `X` be a topological space, `O♯` a sheaf of commutative rings on it, `φ : (O♯)ʳ ⟶ O♯` a
morphism of sheaves of modules with ideal sheaf `I` its image, and `O_X = O♯/I` the quotient.
The Koszul complex of `φ`, read as a cochain complex, is a resolution of `O_X`; this file proves
that the internal Hom complex

`SheafHom^•(⋀^{-•}((O♯)ʳ), O_X)`

has **vanishing differential**. Its cohomology sheaves are therefore its terms, which is what
turns the computation of the Ext sheaves of `O_X` by that resolution into a closed formula.

The reason is the shape of the Koszul differential. The target is concentrated in degree zero,
so by the Leibniz rule the differential of the Hom complex is precomposition with the
differential of the Koszul complex. On the ordered exterior products of the tautological
generators that differential is an alternating sum whose coefficients are the scalars `φ(e)`
attached to those generators — and such a scalar annihilates every section of `O♯/I`. A section
of an exterior power is, near every point, a combination of those ordered products, so the whole
of the image of the Koszul differential is killed; the quotient is a sheaf, so the value
vanishes outright.

## Main results

* `Stacks.SheafOfModules.app_sum_smul` and `Stacks.SheafOfModules.app_sum_smul_eq_zero`: a
  morphism of sheaves of modules distributes over a finite combination of sections, and kills
  one as soon as it kills each of its terms.
* `Stacks.RegularSequence.KoszulChainData.app_dNat_eq_zero`: **a morphism from an exterior
  power of `(O♯)ʳ` into `O♯/I` kills the image of the Koszul differential.**
* `Stacks.RegularSequence.KoszulChainData.app_chain_d_eq_zero`: the same for the differential of
  the associated chain complex, in every integer degree.
* `Stacks.RegularSequence.KoszulChainData.sheafHomComplex_d_eq_zero`: **the differential of the
  internal Hom complex out of the Koszul cochain complex into `O♯/I` vanishes.**

## Implementation notes

The morphisms into which the Koszul differential is composed are morphisms of sheaves of
modules on the *slice site* over an open set, because that is what a section of the internal Hom
complex is. Nothing about the slice site is used beyond what every morphism of sheaves has: that
it is linear on sections and commutes with restriction. So the argument is run on sections, with
the slice-site arrow carried along as a parameter, rather than by restricting the Koszul data to
the slice site — which would require a construction that is not available.

The three index conventions in play are reconciled once each. The Koszul differential is given
on exterior powers in natural degrees as
`Stacks.RegularSequence.KoszulChainData.dNat`; the associated chain complex is `ℤ`-indexed, and
its terms are only *equal* to the exterior powers, so the comparison carries `eqToHom`s, which
are discharged by substituting the equalities (`app_dNat_eq_zero_transport`); and the Hom
complex is cohomologically indexed, which is the reindexing `n ↦ -n` of
`Stacks.ChainComplex.asCochain`, whose terms and differentials are definitionally those of the
chain complex, so no transport is needed there.

## References

* [Stacks Project, Tag 0622](https://stacks.math.columbia.edu/tag/0622)
* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.RingedSite HomologicalComplex
open scoped ExteriorAlgebra

universe u

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  {M N : _root_.SheafOfModules.{u} R}

/-- **A morphism of sheaves of modules distributes over a finite combination of sections.** -/
theorem app_sum_smul (g : M ⟶ N) (W : Cᵒᵖ) {ι : Type} [Fintype ι] (c : ι → R.obj.obj W)
    (z : ι → M.val.obj W) :
    g.val.app W (∑ k, c k • z k) = ∑ k, c k • g.val.app W (z k) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun k _ => map_smul _ _ _

/-- **A morphism of sheaves of modules kills a finite combination of sections as soon as it
kills each of its terms.** -/
theorem app_sum_smul_eq_zero (β : M ⟶ N) (W : Cᵒᵖ) {ι : Type} [Fintype ι] (c : ι → R.obj.obj W)
    (z : ι → M.val.obj W) (h : ∀ k, c k • β.val.app W (z k) = 0) :
    β.val.app W (∑ k, c k • z k) = 0 := by
  rw [app_sum_smul]
  exact Finset.sum_eq_zero fun k _ => h k

end Stacks.SheafOfModules

namespace Stacks.RegularSequence.KoszulChainData

open Stacks.SheafOfModules Stacks.ChainComplex

variable {X : TopCat.{u}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u}}
  {r : ℕ}
  {A : SheafOfModules.TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (koszulFreeSheaf Osharp r)}
  {φ : koszulFreeSheaf Osharp r ⟶
    SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
  (K : KoszulChainData.{u, u, u} A φ)

/-- **A morphism into `O♯/I` kills the Koszul differential of an ordered exterior product of
tautological generators.** That differential is an alternating sum whose coefficients are
multiples of the scalars attached by `φ`, and each of those annihilates the quotient. -/
theorem app_dNat_exteriorBasisSection_eq_zero (n : ℕ) (U W : Opens ↥X) (j : W ⟶ U)
    (β : (A.exteriorPower n).over U ⟶ (koszulQuotient φ).over U)
    (i : Fin (n + 1) → Fin r) :
    β.val.app (op (Over.mk j))
      ((K.dNat n).val.app (op W) (exteriorBasisSection A W (n + 1) i)) = 0 := by
  rw [dNat_exteriorBasisSection K n W i]
  exact app_sum_smul_eq_zero β (op (Over.mk j)) _ _
    fun k => mul_unitScalar_smul_koszulQuotient_eq_zero φ (op W) _ _ _

/-- **A morphism into `O♯/I` kills the Koszul differential of a combination of ordered exterior
products.** -/
theorem app_dNat_sum_eq_zero (n : ℕ) (U W : Opens ↥X) (j : W ⟶ U)
    (β : (A.exteriorPower n).over U ⟶ (koszulQuotient φ).over U)
    (a : ↑(Set.powersetCard (Fin r) (n + 1)) → Osharp.obj.obj (op W)) :
    β.val.app (op (Over.mk j)) ((K.dNat n).val.app (op W)
      (∑ t, a t • exteriorBasisSection A W (n + 1) (wedgeIndex (n + 1) t))) = 0 := by
  rw [app_sum_smul (K.dNat n) (op W) a _]
  refine app_sum_smul_eq_zero β (op (Over.mk j)) a _ fun t => ?_
  rw [app_dNat_exteriorBasisSection_eq_zero K n U W j β (wedgeIndex (n + 1) t)]
  exact smul_zero _

/-- **A morphism into `O♯/I` kills the Koszul differential of a section after restriction to a
neighbourhood on which that section is a combination of ordered exterior products.** -/
theorem app_dNat_restrict_eq_zero (n : ℕ) (U : Opens ↥X)
    (β : (A.exteriorPower n).over U ⟶ (koszulQuotient φ).over U)
    (V : Opens ↥X) (i : V ⟶ U) (y : (A.exteriorPower (n + 1)).val.obj (op V))
    (W : Opens ↥X) (hWV : W ≤ V)
    (a : ↑(Set.powersetCard (Fin r) (n + 1)) → Osharp.obj.obj (op W))
    (ha : (A.exteriorPower (n + 1)).val.map (homOfLE hWV).op y =
      ∑ t, a t • exteriorBasisSection A W (n + 1) (wedgeIndex (n + 1) t)) :
    (koszulQuotient φ).val.map (homOfLE hWV).op
      (β.val.app (op (Over.mk i)) ((K.dNat n).val.app (op V) y)) = 0 := by
  have hnatβ : β.val.app (op (Over.mk (homOfLE hWV ≫ i)))
        ((A.exteriorPower n).val.map (homOfLE hWV).op ((K.dNat n).val.app (op V) y))
      = (koszulQuotient φ).val.map (homOfLE hWV).op
        (β.val.app (op (Over.mk i)) ((K.dNat n).val.app (op V) y)) :=
    PresheafOfModules.naturality_apply β.val
      (Over.homMk (homOfLE hWV) : Over.mk (homOfLE hWV ≫ i) ⟶ Over.mk i).op _
  have hnatd : (A.exteriorPower n).val.map (homOfLE hWV).op ((K.dNat n).val.app (op V) y)
      = (K.dNat n).val.app (op W) ((A.exteriorPower (n + 1)).val.map (homOfLE hWV).op y) :=
    (PresheafOfModules.naturality_apply (K.dNat n).val (homOfLE hWV).op y).symm
  rw [← hnatβ, hnatd, ha]
  exact app_dNat_sum_eq_zero K n U W (homOfLE hWV ≫ i) β a

/-- **A morphism from an exterior power of `(O♯)ʳ` into `O♯/I` kills the image of the Koszul
differential.** Every section of the exterior power is, near every point, a combination of
ordered exterior products of the tautological generators, where the statement is the previous
one; the quotient is a sheaf, so the value vanishes outright. -/
theorem app_dNat_eq_zero (n : ℕ) (U : Opens ↥X)
    (β : (A.exteriorPower n).over U ⟶ (koszulQuotient φ).over U)
    (V : Opens ↥X) (i : V ⟶ U) (y : (A.exteriorPower (n + 1)).val.obj (op V)) :
    β.val.app (op (Over.mk i)) ((K.dNat n).val.app (op V) y) = 0 := by
  refine TopCat.Presheaf.section_ext
    (⟨(koszulQuotient φ).val.presheaf, (koszulQuotient φ).isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat.{u} X) V _ 0 fun x hx => ?_
  obtain ⟨W, hWV, hxW, a, ha⟩ :=
    exists_restrict_eq_sum_smul_exteriorBasisSection A (n + 1) V hx y
  have hzero : (koszulQuotient φ).val.presheaf.map (homOfLE hWV).op
      (β.val.app (op (Over.mk i)) ((K.dNat n).val.app (op V) y)) = 0 :=
    app_dNat_restrict_eq_zero K n U β V i y W hWV a ha
  have hg := TopCat.Presheaf.germ_res_apply (koszulQuotient φ).val.presheaf (homOfLE hWV) x hxW
    (β.val.app (op (Over.mk i)) ((K.dNat n).val.app (op V) y))
  rw [hzero, map_zero] at hg
  rw [← hg]
  exact (map_zero _).symm

/-- `Stacks.RegularSequence.KoszulChainData.app_dNat_eq_zero` with the source and target of the
differential presented through equalities, so that the degree transports of the associated chain
complex can be substituted away. -/
theorem app_dNat_eq_zero_transport (n : ℕ) (U : Opens ↥X)
    {M₀ M₁ : SheafOfModules.{u} (toRingCat (Opens.grothendieckTopology ↥X) Osharp)}
    (h₀ : M₀ = A.exteriorPower n) (h₁ : M₁ = A.exteriorPower (n + 1))
    (β : M₀.over U ⟶ (koszulQuotient φ).over U) (δ : M₁ ⟶ M₀)
    (hδ : δ = eqToHom h₁ ≫ K.dNat n ≫ eqToHom h₀.symm)
    (V : Opens ↥X) (i : V ⟶ U) (y : M₁.val.obj (op V)) :
    β.val.app (op (Over.mk i)) (δ.val.app (op V) y) = 0 := by
  subst h₀
  subst h₁
  subst hδ
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact app_dNat_eq_zero K n U β V i y

/-- **A morphism from a term of the Koszul chain complex into `O♯/I` kills the image of the
differential coming into that term.** In negative degrees the term vanishes and there is nothing
to prove; in nonnegative degrees this is the statement about the exterior powers, transported
along the identification of the terms of the chain complex with them. -/
theorem app_chain_d_eq_zero (U : Opens ↥X) (q q' : ℤ) (hq : q' = q + 1)
    (β : (K.chain.X q).over U ⟶ (koszulQuotient φ).over U)
    (V : Opens ↥X) (i : V ⟶ U) (y : (K.chain.X q').val.obj (op V)) :
    β.val.app (op (Over.mk i)) ((K.chain.d q' q).val.app (op V) y) = 0 := by
  rcases lt_or_ge q 0 with hneg | hpos
  · have h0 : (K.chain.d q' q).val.app (op V) y = 0 :=
      Stacks.SheafOfModules.section_eq_zero_of_isZero (K.isZero_chain_X_of_neg hneg) (op V) _
    rw [h0]
    exact map_zero _
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, q = ((m : ℕ) : ℤ) := ⟨q.toNat, by omega⟩
    obtain rfl : q' = ((m + 1 : ℕ) : ℤ) := by rw [hq]; push_cast; ring
    refine app_dNat_eq_zero_transport K m U (K.chain_X ((m : ℕ) : ℤ))
      (K.chain_X ((m + 1 : ℕ) : ℤ)) β _ ?_ V i y
    rw [← K.chain_d_natCast m]
    simp

section HomComplex

attribute [local instance] HasDerivedCategory.standard

variable [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The differential of the internal Hom complex out of the Koszul cochain complex into
`O♯/I` vanishes.** The target is concentrated in degree zero, so by the Leibniz rule the
differential is precomposition with the differential of the Koszul complex, and that is killed
by every morphism into the quotient. -/
theorem sheafHomComplex_d_eq_zero (n : ℤ) :
    (RingedSite.sheafHomComplex (Stacks.SheafOfModules.ringedSite Osharp)
        (asCochain K.chain)
        ((single (Stacks.SheafOfModules.StructureSheafModules Osharp)
          (ComplexShape.up ℤ) 0).obj (koszulQuotient.{u, u, u} φ))).obj.d n (n + 1) = 0 := by
  refine RingedSite.SheafHomComplex.d_eq_zero_of_single
    (Stacks.SheafOfModules.ringedSite Osharp) (koszulQuotient.{u, u, u} φ) _
    (fun U V i m p hp f y => ?_) n
  exact app_chain_d_eq_zero K U (-(p + 1)) (-p) (by omega) _ V i y

end HomComplex

end Stacks.RegularSequence.KoszulChainData

end
