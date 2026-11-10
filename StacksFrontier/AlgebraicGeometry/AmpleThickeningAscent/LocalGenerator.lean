module

public import StacksFrontier.AlgebraicGeometry.AmpleTheory.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.NonvanishingLocusRestrict
public import StacksFrontier.AlgebraicGeometry.SectionProduct.Basic

/-!
# A section of an invertible module vanishing nowhere on an open is a basis there

Let `M` be an invertible `𝒪_X`-module on a scheme and let `τ` be a section of `M` over an open
`W` whose germ avoids `𝔪_y M_y` at every point `y` of `W`. Then every section of `M` over `W` is
`a • τ` for exactly one function `a` on `W`.

`Stacks.NonvanishingSpelling.bijective_smul` is this statement for the restriction of a *global*
section to an open inside its nonvanishing locus. The section here is local, which is what a
computation in local coordinates needs: the pullback of a basis section of a trivialization along
a morphism of schemes is a local section of the pullback module that vanishes nowhere (by
[Stacks, Tag 0H78] over an open), and it has to serve as a basis upstairs.

The proof is the one of the global statement. Over a trivializing open `V` inside `W` the
trivializing function `e` of `τ` has unit germs, because `τ = e • b` for the basis section `b`,
which vanishes nowhere; so `e` is a unit and multiplication by `τ` is multiplication by a unit in
the trivialization. Bijectivity glues over a cover by such opens.

## Main results

* `Stacks.AmpleThickeningAscent.nonvanishingLocusOn_smul`: `W_{a • σ} = D(a) ∩ W_σ`, for any
  module.
* `Stacks.AmpleThickeningAscent.nonvanishingLocusOn_res`: the nonvanishing locus of a restriction.
* `Stacks.AmpleThickeningAscent.nonvanishingLocusOn_basis`: the basis section of a
  trivialization vanishes nowhere on its open.
* `Stacks.AmpleThickeningAscent.bijective_smul_of_nonvanishing`: the division by a nowhere
  vanishing local section.

## References

* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.NonvanishingLocusRestrict (nonvanishingLocusOn mem_nonvanishingLocusOn_iff)
open Stacks.ModuleStalk

universe u

namespace Stacks.AmpleThickeningAscent

variable {X : Scheme.{u}}

/-! ### The sheaf property of a module, in the section spelling -/

/-- Sections of an `𝒪_X`-module agreeing on the members of a cover agree. -/
theorem modules_eq_of_locally_eq (M : X.Modules) {ι : Type*} (U : ι → X.Opens) (V : X.Opens)
    (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U) (m m' : Γ(M, V))
    (h : ∀ i, M.presheaf.map (iUV i).op m = M.presheaf.map (iUV i).op m') : m = m' :=
  TopCat.Sheaf.eq_of_locally_eq' (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} _)
    U V iUV hcover m m' h

/-- Compatible sections of an `𝒪_X`-module over the members of a cover glue. -/
theorem modules_exists_gluing (M : X.Modules) {ι : Type*} (U : ι → X.Opens) (V : X.Opens)
    (iUV : ∀ i, U i ⟶ V) (hcover : V ≤ iSup U) (sf : ∀ i, Γ(M, U i))
    (h : ∀ i j, M.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (sf i) =
      M.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (sf j)) :
    ∃ s : Γ(M, V), ∀ i, M.presheaf.map (iUV i).op s = sf i :=
  (TopCat.Sheaf.existsUnique_gluing'
    (⟨M.val.presheaf, M.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} _) U V iUV hcover sf h).exists

/-! ### Nonvanishing loci of local sections -/

/-- **`W_{a • σ} = D(a) ∩ W_σ`.** The germ of `a • σ` is `a_y • σ_y`, which avoids `𝔪_y M_y`
exactly when `a_y` is a unit and `σ_y` avoids it. No hypothesis on the module. -/
theorem nonvanishingLocusOn_smul (M : X.Modules) {W : X.Opens} (a : Γ(X, W)) (σ : Γ(M, W)) :
    nonvanishingLocusOn M W (a • σ) = (X.basicOpen a : Set X) ∩ nonvanishingLocusOn M W σ := by
  ext y
  constructor
  · rintro ⟨hy, h⟩
    rw [Stacks.ModuleStalk.germ_smul, smul_mem_maximalSmul_iff, not_or, not_not] at h
    exact ⟨(X.mem_basicOpen a y hy).mpr h.1, hy, h.2⟩
  · rintro ⟨ha, hy, h⟩
    refine ⟨hy, ?_⟩
    rw [Stacks.ModuleStalk.germ_smul, smul_mem_maximalSmul_iff, not_or, not_not]
    exact ⟨(X.mem_basicOpen a y hy).mp ha, h⟩

/-- **The nonvanishing locus of a restriction** is the part of the nonvanishing locus inside the
smaller open: germs do not see restriction. -/
theorem nonvanishingLocusOn_res (M : X.Modules) {W W' : X.Opens} (h : W' ≤ W) (σ : Γ(M, W)) :
    nonvanishingLocusOn M W' (M.presheaf.map (homOfLE h).op σ) =
      (W' : Set X) ∩ nonvanishingLocusOn M W σ := by
  ext y
  constructor
  · rintro ⟨hy, hσ⟩
    refine ⟨hy, h hy, ?_⟩
    rwa [TopCat.Presheaf.germ_res_apply] at hσ
  · rintro ⟨hy, hσ⟩
    refine ⟨hy, ?_⟩
    rw [TopCat.Presheaf.germ_res_apply]
    exact hσ.2

/-- **The basis section of a sectionwise trivialization vanishes nowhere on its open.** -/
theorem nonvanishingLocusOn_basis {M : X.Modules} {V : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) :
    nonvanishingLocusOn M V (Stacks.NonvanishingOpen.basis t) = V :=
  Set.Subset.antisymm (fun _ h => h.1)
    fun _ hy => ⟨hy, Stacks.NonvanishingOpen.notMem_maximalSmul_germ_basis t hy⟩

/-! ### Division by a nowhere vanishing local section -/

/-- **Division by a nowhere vanishing section inside a trivializing open.** If `M` has a
sectionwise trivialization over `V` and `τ` is a section over `W ≤ V` vanishing nowhere on `W`,
then its trivializing function is a unit (its germs are, since `τ = e • b` for the basis section
`b`, which vanishes nowhere), so multiplication by `τ` is a bijection. -/
theorem bijective_smul_of_triv {M : X.Modules} {V W : X.Opens}
    (t : Stacks.SheafDescent.Trivialization X.presheaf M.val V) (hWV : W ≤ V) (τ : Γ(M, W))
    (hτ : (W : Set X) ⊆ nonvanishingLocusOn M W τ) :
    Function.Bijective fun a : Γ(X, W) => a • τ := by
  have hu : IsUnit (Stacks.NonvanishingOpen.triv t (homOfLE hWV) τ) := by
    refine X.toRingedSpace.isUnit_of_isUnit_germ W _ fun y hy => ?_
    have hτy := (hτ hy).2
    rw [Stacks.SectionProduct.eq_triv_smul_res_basis t (homOfLE hWV) τ,
      Stacks.ModuleStalk.germ_smul, smul_mem_maximalSmul_iff, not_or, not_not] at hτy
    exact hτy.1
  obtain ⟨v, hv⟩ := hu
  refine ⟨fun a b hab => (Units.mul_left_inj v).mp ?_, fun l => ?_⟩
  · rw [hv, ← Stacks.NonvanishingOpen.triv_smul, ← Stacks.NonvanishingOpen.triv_smul]
    exact congrArg (Stacks.NonvanishingOpen.triv t (homOfLE hWV)) hab
  · refine ⟨Stacks.NonvanishingOpen.triv t (homOfLE hWV) l * (↑v⁻¹ : Γ(X, W)),
      (t.θ W (homOfLE hWV)).injective ?_⟩
    change Stacks.NonvanishingOpen.triv t (homOfLE hWV) _ =
      Stacks.NonvanishingOpen.triv t (homOfLE hWV) l
    rw [Stacks.NonvanishingOpen.triv_smul, ← hv, mul_assoc, Units.inv_mul, mul_one]

/-- **Division by a nowhere vanishing local section.** If `M` is invertible and `τ` is a section
of `M` over `W` whose germ avoids `𝔪_y M_y` at every point of `W`, then `a ↦ a • τ` is a bijection
from `Γ(X, W)` to `Γ(M, W)`. Bijectivity holds over the trivializing opens by
`Stacks.AmpleThickeningAscent.bijective_smul_of_triv` and glues. -/
theorem bijective_smul_of_nonvanishing (M : X.Modules) [Stacks.Ample.IsInvertibleModule X M]
    {W : X.Opens} (τ : Γ(M, W)) (hτ : (W : Set X) ⊆ nonvanishingLocusOn M W τ) :
    Function.Bijective fun a : Γ(X, W) => a • τ := by
  choose T hyT ht using fun y : W => Stacks.SectionProduct.exists_trivialization_at M (y : X)
  let V : W → X.Opens := fun y => W ⊓ T y
  let iV : ∀ y, V y ⟶ W := fun y => homOfLE inf_le_left
  have hcover : W ≤ iSup V := fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hx, hyT ⟨x, hx⟩⟩
  have hres : ∀ {P Q : X.Opens} (i : Q ⟶ P) (a : Γ(X, P)) (σ : Γ(M, P)),
      M.presheaf.map i.op (a • σ) = X.presheaf.map i.op a • M.presheaf.map i.op σ :=
    fun i a σ => Scheme.Modules.map_smul M i a σ
  -- multiplication by a restriction of `τ` is bijective inside each trivializing open
  have hbij : ∀ (y : W) (P : X.Opens) (hP : P ≤ V y), Function.Bijective
      fun a : Γ(X, P) => a • M.presheaf.map (homOfLE (hP.trans inf_le_left)).op τ := by
    intro y P hP
    refine bijective_smul_of_triv (ht y).some (hP.trans inf_le_right) _ fun z hz => ?_
    rw [nonvanishingLocusOn_res]
    exact ⟨hz, hτ ((hP.trans inf_le_left) hz)⟩
  have hresres : ∀ {P Q R : X.Opens} (h₁ : Q ≤ P) (h₂ : P ≤ R) (σ : Γ(M, R)),
      M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op σ) =
        M.presheaf.map (homOfLE (h₁.trans h₂)).op σ := by
    intro P Q R h₁ h₂ σ
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  constructor
  · intro a b hab
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf V W iV hcover a b fun y => ?_
    refine (hbij y (V y) le_rfl).1 ?_
    change X.presheaf.map (iV y).op a • M.presheaf.map (iV y).op τ =
      X.presheaf.map (iV y).op b • M.presheaf.map (iV y).op τ
    rw [← hres, ← hres]
    exact congrArg (M.presheaf.map (iV y).op) hab
  · intro l
    choose a ha using fun y => (hbij y (V y) le_rfl).2 (M.presheaf.map (iV y).op l)
    have ha' : ∀ y, a y • M.presheaf.map (iV y).op τ = M.presheaf.map (iV y).op l := ha
    have hloc : ∀ (y : W) (P : X.Opens) (hP : P ≤ V y),
        X.presheaf.map (homOfLE hP).op (a y) •
            M.presheaf.map (homOfLE (hP.trans inf_le_left)).op τ =
          M.presheaf.map (homOfLE (hP.trans inf_le_left)).op l := by
      intro y P hP
      rw [← hresres hP inf_le_left τ, ← hres, ha' y]
      exact hresres hP inf_le_left l
    have hcompat : ∀ y y', X.presheaf.map (homOfLE (inf_le_left : V y ⊓ V y' ≤ V y)).op (a y) =
        X.presheaf.map (homOfLE (inf_le_right : V y ⊓ V y' ≤ V y')).op (a y') := by
      intro y y'
      refine (hbij y (V y ⊓ V y') inf_le_left).1 ?_
      change X.presheaf.map (homOfLE inf_le_left).op (a y) • _ =
        X.presheaf.map (homOfLE inf_le_right).op (a y') • _
      rw [hloc y _ inf_le_left]
      exact (hloc y' _ inf_le_right).symm
    obtain ⟨A, hA⟩ : ∃ A : Γ(X, W), ∀ y, X.presheaf.map (iV y).op A = a y :=
      (X.sheaf.existsUnique_gluing' V W iV hcover a hcompat).exists
    refine ⟨A, modules_eq_of_locally_eq M V W iV hcover _ l fun y => ?_⟩
    change M.presheaf.map (iV y).op (A • τ) = M.presheaf.map (iV y).op l
    rw [hres, ← ha' y, hA y]

end Stacks.AmpleThickeningAscent

end
