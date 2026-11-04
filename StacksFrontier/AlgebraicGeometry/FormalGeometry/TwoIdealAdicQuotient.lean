module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.AdicQuotientMap
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFunctor.Adjunction
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PowerAnnihilated

/-!
# Dividing a sheaf of modules by two incomparable ideal powers

Let `X` be a scheme, let `ℐ, 𝒦 ⊆ 𝒪_X` be quasi-coherent ideal sheaves and let `M` be a
quasi-coherent sheaf of modules on `X`. Dividing `M` first by `𝒦 ᵉ` and then by `ℐ ⁿ` produces
`M / (ℐ ⁿ + 𝒦 ᵉ) M`, and so does dividing in the other order. This file proves that the two
double quotients are canonically isomorphic, compatibly with the projections out of `M`.

Existing material on double quotients assumes one of the two powers *contains* the other
(`Stacks.Algebraization.doubleIdealPowerQuotientIso`, where the first division is invisible
modulo the second). Here the two ideals are unrelated, so neither division is invisible and the
identification has to be built from the universal property on both sides.

The two ingredients are: annihilation by an ideal power passes along an epimorphism of
quasi-coherent modules, so each of the two double quotients is annihilated by both `ℐ ⁿ` and
`𝒦 ᵉ`; and a morphism into a module annihilated by `ℐ ⁿ` descends through the projection
`M ⟶ M / ℐ ⁿ M`. Descending the composite projection of one order through the two projections of
the other order, twice, gives two mutually inverse comparison maps.

## Main definitions

* `Stacks.Algebraization.isoOfEpiFac` — two epimorphisms out of a common object, each factoring
  through the other, identify their targets.
* `Stacks.Algebraization.idealPowerQuotientDesc` — the descent of a morphism through the
  projection `M ⟶ M / ℐ ⁿ M`, available when the target is annihilated by `ℐ ⁿ`.
* `Stacks.Algebraization.idealPowerQuotientCommMap` and
  `Stacks.Algebraization.idealPowerQuotientCommIso` — the comparison
  `(M / 𝒦 ᵉ M) / ℐ ⁿ (…) ⟶ (M / ℐ ⁿ M) / 𝒦 ᵉ (…)` and the isomorphism it is half of.
* `Stacks.Algebraization.idealPowerQuotientSupIso` — the identification of the double quotient
  with `M / (ℐ ⁿ + 𝒦 ᵉ) M`, the sum being the join `ℐ ⁿ ⊔ 𝒦 ᵉ` of quasi-coherent ideal
  sheaves.

## Main results

* `Stacks.Algebraization.idealPowerMultiple_eq_bot_of_epi` — annihilation by `ℐ ⁿ` passes along
  an epimorphism of quasi-coherent sheaves of modules.
* `Stacks.Algebraization.idealPowerMultiple_idealPowerQuotient_eq_bot_of_eq_bot` — a module
  annihilated by `ℐ ⁿ` has `𝒦 ᵉ`-quotient annihilated by `ℐ ⁿ`.
* `Stacks.Algebraization.idealPowerMultiple_idealPowerQuotient_eq_bot_of_pow_le` — for
  `ℐ ⁿ ⊆ 𝒥 ᵐ` the `𝒥 ᵐ`-quotient is already annihilated by `ℐ ⁿ`.
* `Stacks.Algebraization.idealPowerQuotientCommMap_π` — the comparison map is determined by its
  compatibility with the two composite projections out of `M`.
* `Stacks.Algebraization.idealPowerMultiple_sup_eq_bot` — a module annihilated by two ideal
  powers is annihilated by their sum.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` carrying its own
category instance, so composites below name the category with `(C := X.Modules)` and the
epimorphism property of a quotient projection comes from the instance
`Stacks.Algebraization.epi_cokernel_π_submodule_ι` rather than from Mathlib's instance for a
cokernel projection. The complete lattice of submodules is the local instance used by the
neighbouring modules.

`isoOfEpiFac` takes its two epimorphism hypotheses as explicit arguments: at the use sites below
the relevant epimorphism is a composite of two quotient projections, and supplying the witness
avoids relying on instance search through that composite.

## References

* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 088A](https://stacks.math.columbia.edu/tag/088A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Algebraization

/-! ### Two epimorphic presentations of one object -/

/-- Two epimorphisms `p : M ⟶ D` and `q : M ⟶ E` out of a common object, each factoring through
the other, identify `D` with `E`.

The two factorizations are mutually inverse because `p` and `q` are epimorphisms: composing them
in either order and cancelling the relevant epimorphism leaves an identity. -/
public def isoOfEpiFac {C : Type*} [Category C] {M D E : C} {p : M ⟶ D} {q : M ⟶ E}
    (hp : Epi p) (hq : Epi q) (d : D ⟶ E) (d' : E ⟶ D)
    (hd : p ≫ d = q) (hd' : q ≫ d' = p) :
    D ≅ E where
  hom := d
  inv := d'
  hom_inv_id := (cancel_epi p).1 (by rw [← Category.assoc, hd, hd', Category.comp_id])
  inv_hom_id := (cancel_epi q).1 (by rw [← Category.assoc, hd', hd, Category.comp_id])

variable {X : Scheme.{u}}

/-! ### Annihilation by an ideal power passes to quotients -/

/-- **Annihilation passes along an epimorphism.** If `f : M ⟶ N` is a surjection of quasi-coherent
sheaves of modules and `ℐ ⁿ M = 0`, then `ℐ ⁿ N = 0`.

Over an affine open every section of `N` is the image of a section of `M`, by
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen`, and `f` is `Γ(X, U)`-linear, so the
sections of `N` are annihilated by `ℐ(U) ⁿ` because those of `M` are. -/
public theorem idealPowerMultiple_eq_bot_of_epi (I : X.IdealSheafData) (n : ℕ)
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) [Epi f]
    (hM : idealPowerMultiple I n M = ⊥) :
    idealPowerMultiple I n N = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun U a ha x => ?_
  obtain ⟨y, hy⟩ : ∃ y, f.app U.1 y = x :=
    Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen X f U.1 U.2 x
  calc a • x
      = a • f.app U.1 y := by rw [hy]
    _ = f.app U.1 (a • y) := (Scheme.Modules.Hom.app_smul f a y).symm
    _ = f.app U.1 0 := by
        rw [affine_sections_annihilated_of_idealPowerMultiple_eq_bot hM U ha y]
    _ = 0 := map_zero _

/-- A module annihilated by `ℐ ⁿ` has `𝒦 ᵉ`-quotient annihilated by `ℐ ⁿ`: the quotient
projection is an epimorphism of quasi-coherent modules. -/
public theorem idealPowerMultiple_idealPowerQuotient_eq_bot_of_eq_bot (I K : X.IdealSheafData)
    (n e : ℕ) (M : X.Modules) [M.IsQuasicoherent] (hM : idealPowerMultiple I n M = ⊥) :
    idealPowerMultiple I n (idealPowerQuotient K e M) = ⊥ :=
  idealPowerMultiple_eq_bot_of_epi I n
    (cokernel.π (C := X.Modules) (idealPowerMultiple K e M).ι) hM

/-- **The containment case.** If `ℐ ⁿ ⊆ 𝒥 ᵐ` then the `𝒥 ᵐ`-quotient of `M` is already
annihilated by `ℐ ⁿ`, since `ℐ ⁿ` of any module is contained in `𝒥 ᵐ` of it. -/
public theorem idealPowerMultiple_idealPowerQuotient_eq_bot_of_pow_le {I J : X.IdealSheafData}
    {n m : ℕ} (h : I ^ n ≤ J ^ m) (M : X.Modules) [M.IsQuasicoherent] :
    idealPowerMultiple I n (idealPowerQuotient J m M) = ⊥ :=
  le_antisymm ((idealPowerMultiple_le_of_pow_le h (idealPowerQuotient J m M)).trans
    (idealPowerMultiple_idealPowerQuotient_eq_bot J m M).le) bot_le

/-! ### Descending a morphism through a quotient projection -/

/-- The descent of `f : M ⟶ N` through the projection `M ⟶ M / ℐ ⁿ M`, available whenever the
target is annihilated by `ℐ ⁿ`. -/
public def idealPowerQuotientDesc (I : X.IdealSheafData) (n : ℕ) {M N : X.Modules}
    (f : M ⟶ N) (hN : idealPowerMultiple I n N = ⊥) :
    idealPowerQuotient I n M ⟶ N :=
  cokernel.desc (C := X.Modules) (idealPowerMultiple I n M).ι f
    (comp_eq_zero_of_idealPowerMultiple_eq_bot I n f hN)

/-- The descent recovers `f` on composing with the quotient projection. -/
@[reassoc]
public theorem idealPowerQuotientDesc_π (I : X.IdealSheafData) (n : ℕ) {M N : X.Modules}
    (f : M ⟶ N) (hN : idealPowerMultiple I n N = ⊥) :
    cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι ≫
        idealPowerQuotientDesc I n f hN =
      f :=
  cokernel.π_desc _ _ _

/-! ### The two orders of division agree -/

section Comm

variable (I K : X.IdealSheafData) (n e : ℕ) (M : X.Modules)

/-- The composite projection `M ⟶ M / 𝒦 ᵉ M ⟶ (M / 𝒦 ᵉ M) / ℐ ⁿ (M / 𝒦 ᵉ M)`, one of the two
presentations of `M / (ℐ ⁿ + 𝒦 ᵉ) M`. -/
public abbrev doubleIdealPowerQuotientProjection :
    M ⟶ idealPowerQuotient I n (idealPowerQuotient K e M) :=
  cokernel.π (C := X.Modules) (idealPowerMultiple K e M).ι ≫
    cokernel.π (C := X.Modules) (idealPowerMultiple I n (idealPowerQuotient K e M)).ι

/-- Descending `f` first through the `𝒦 ᵉ`-quotient and then through the `ℐ ⁿ`-quotient recovers
`f` on composing with the composite projection. -/
private theorem doubleIdealPowerQuotientProjection_desc_desc {N : X.Modules}
    {f : M ⟶ N} (hK : idealPowerMultiple K e N = ⊥) (hI : idealPowerMultiple I n N = ⊥) :
    doubleIdealPowerQuotientProjection I K n e M ≫
        idealPowerQuotientDesc I n (idealPowerQuotientDesc K e f hK) hI = f := by
  rw [doubleIdealPowerQuotientProjection, Category.assoc, idealPowerQuotientDesc_π,
    idealPowerQuotientDesc_π]

/-- The composite projection onto a double quotient is an epimorphism. -/
public theorem epi_doubleIdealPowerQuotientProjection :
    Epi (doubleIdealPowerQuotientProjection I K n e M) := by
  have h1 : Epi (cokernel.π (C := X.Modules) (idealPowerMultiple K e M).ι) :=
    epi_cokernel_π_submodule_ι _
  have h2 : Epi (cokernel.π (C := X.Modules)
      (idealPowerMultiple I n (idealPowerQuotient K e M)).ι) :=
    epi_cokernel_π_submodule_ι _
  exact @epi_comp _ _ _ _ _ _ h1 _ h2

variable [M.IsQuasicoherent]

/-- A double quotient is annihilated by the power divided out last. -/
public theorem idealPowerMultiple_doubleIdealPowerQuotient_eq_bot_outer :
    idealPowerMultiple I n (idealPowerQuotient I n (idealPowerQuotient K e M)) = ⊥ :=
  idealPowerMultiple_idealPowerQuotient_eq_bot I n (idealPowerQuotient K e M)

/-- A double quotient is annihilated by the power divided out first: that power already
annihilates the inner quotient, and annihilation passes to the further quotient. -/
public theorem idealPowerMultiple_doubleIdealPowerQuotient_eq_bot_inner :
    idealPowerMultiple K e (idealPowerQuotient I n (idealPowerQuotient K e M)) = ⊥ :=
  idealPowerMultiple_idealPowerQuotient_eq_bot_of_eq_bot K I e n (idealPowerQuotient K e M)
    (idealPowerMultiple_idealPowerQuotient_eq_bot K e M)

/-- The comparison map `(M / 𝒦 ᵉ M) / ℐ ⁿ (…) ⟶ (M / ℐ ⁿ M) / 𝒦 ᵉ (…)`, obtained by descending
the composite projection in the second order through the two projections of the first. -/
public def idealPowerQuotientCommMap :
    idealPowerQuotient I n (idealPowerQuotient K e M) ⟶
      idealPowerQuotient K e (idealPowerQuotient I n M) :=
  idealPowerQuotientDesc I n
    (idealPowerQuotientDesc K e (doubleIdealPowerQuotientProjection K I e n M)
      (idealPowerMultiple_doubleIdealPowerQuotient_eq_bot_outer K I e n M))
    (idealPowerMultiple_doubleIdealPowerQuotient_eq_bot_inner K I e n M)

/-- The comparison map carries one composite projection to the other; the projection being an
epimorphism, this determines it. -/
public theorem idealPowerQuotientCommMap_π :
    doubleIdealPowerQuotientProjection I K n e M ≫ idealPowerQuotientCommMap I K n e M =
      doubleIdealPowerQuotientProjection K I e n M :=
  doubleIdealPowerQuotientProjection_desc_desc ..

/-- The comparison map on the two composite projections, with the projections written out and
the composite right-associated.

This is the form the consumers rewrite with: a goal arrives with the outer projection applied to
a further map, so the composite needs to be grouped to the right rather than hidden inside
`doubleIdealPowerQuotientProjection`. -/
@[reassoc]
public theorem idealPowerQuotientCommMap_cokernel_π :
    cokernel.π (C := X.Modules) (idealPowerMultiple K e M).ι ≫
        cokernel.π (C := X.Modules)
            (idealPowerMultiple I n (idealPowerQuotient K e M)).ι ≫
          idealPowerQuotientCommMap I K n e M =
      cokernel.π (C := X.Modules) (idealPowerMultiple I n M).ι ≫
        cokernel.π (C := X.Modules)
          (idealPowerMultiple K e (idealPowerQuotient I n M)).ι :=
  (Category.assoc (obj := X.Modules) _ _ _).symm.trans (idealPowerQuotientCommMap_π I K n e M)

/-- **The two-ideal double quotient is symmetric.** For a quasi-coherent `M` and unrelated ideal
sheaves `ℐ, 𝒦`, dividing by `𝒦 ᵉ` and then `ℐ ⁿ` gives the same module as dividing by `ℐ ⁿ` and
then `𝒦 ᵉ`, namely `M / (ℐ ⁿ + 𝒦 ᵉ) M`. -/
public def idealPowerQuotientCommIso :
    idealPowerQuotient I n (idealPowerQuotient K e M) ≅
      idealPowerQuotient K e (idealPowerQuotient I n M) :=
  isoOfEpiFac (epi_doubleIdealPowerQuotientProjection I K n e M)
    (epi_doubleIdealPowerQuotientProjection K I e n M)
    (idealPowerQuotientCommMap I K n e M) (idealPowerQuotientCommMap K I e n M)
    (idealPowerQuotientCommMap_π I K n e M) (idealPowerQuotientCommMap_π K I e n M)

/-- The symmetry isomorphism is the comparison map. -/
@[simp]
public theorem idealPowerQuotientCommIso_hom :
    (idealPowerQuotientCommIso I K n e M).hom = idealPowerQuotientCommMap I K n e M :=
  rfl

/-- The inverse of the symmetry isomorphism is the comparison map in the other order. -/
@[simp]
public theorem idealPowerQuotientCommIso_inv :
    (idealPowerQuotientCommIso I K n e M).inv = idealPowerQuotientCommMap K I e n M :=
  rfl

end Comm

/-! ### The double quotient is the quotient by the sum of the two multiples -/

/-- A module annihilated by `ℐ ⁿ` and by `𝒦 ᵉ` is annihilated by the sum ideal sheaf
`ℐ ⁿ + 𝒦 ᵉ`: over an affine open a section of the sum is a sum of a section of each summand, and
each summand kills the module. -/
public theorem idealPowerMultiple_sup_eq_bot {I K : X.IdealSheafData} {n e : ℕ} {N : X.Modules}
    (hI : idealPowerMultiple I n N = ⊥) (hK : idealPowerMultiple K e N = ⊥) :
    idealPowerMultiple (I ^ n ⊔ K ^ e) 1 N = ⊥ := by
  refine idealPowerMultiple_eq_bot_of_affine_sections_annihilated fun U a ha x => ?_
  have hsplit : a ∈ I.ideal U ^ n ⊔ K.ideal U ^ e := by simpa using ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 hsplit
  rw [add_smul, affine_sections_annihilated_of_idealPowerMultiple_eq_bot hI U hb x,
    affine_sections_annihilated_of_idealPowerMultiple_eq_bot hK U hc x, add_zero]

/-- `ℐ ⁿ` is one of the two summands of the sum ideal sheaf. -/
public theorem pow_le_sup_pow_pow_one (I K : X.IdealSheafData) (n e : ℕ) :
    I ^ n ≤ (I ^ n ⊔ K ^ e) ^ 1 := by
  rw [pow_one]
  exact le_sup_left

section Sup

variable (I K : X.IdealSheafData) (n e : ℕ) (M : X.Modules) [M.IsQuasicoherent]

/-- The comparison `(M / 𝒦 ᵉ M) / ℐ ⁿ (…) ⟶ M / (ℐ ⁿ + 𝒦 ᵉ) M`, obtained by descending the
projection onto the quotient by the sum through the two projections of the double quotient.

Each descent is available because the quotient by the sum is annihilated by each summand, which
is the containment case `idealPowerMultiple_idealPowerQuotient_eq_bot_of_pow_le`. -/
public def idealPowerQuotientSupHom :
    idealPowerQuotient I n (idealPowerQuotient K e M) ⟶
      idealPowerQuotient (I ^ n ⊔ K ^ e) 1 M :=
  idealPowerQuotientDesc I n
    (idealPowerQuotientDesc K e
      (cokernel.π (C := X.Modules) (idealPowerMultiple (I ^ n ⊔ K ^ e) 1 M).ι)
      (idealPowerMultiple_idealPowerQuotient_eq_bot_of_pow_le
        (by rw [pow_one]; exact le_sup_right) M))
    (idealPowerMultiple_idealPowerQuotient_eq_bot_of_pow_le (pow_le_sup_pow_pow_one I K n e) M)

/-- The comparison carries the composite projection onto the double quotient to the projection
onto the quotient by the sum. -/
public theorem idealPowerQuotientSupHom_π :
    doubleIdealPowerQuotientProjection I K n e M ≫ idealPowerQuotientSupHom I K n e M =
      cokernel.π (C := X.Modules) (idealPowerMultiple (I ^ n ⊔ K ^ e) 1 M).ι :=
  doubleIdealPowerQuotientProjection_desc_desc ..

/-- The comparison `M / (ℐ ⁿ + 𝒦 ᵉ) M ⟶ (M / 𝒦 ᵉ M) / ℐ ⁿ (…)`, obtained by descending the
composite projection onto the double quotient, which the sum annihilates. -/
public def idealPowerQuotientSupInv :
    idealPowerQuotient (I ^ n ⊔ K ^ e) 1 M ⟶
      idealPowerQuotient I n (idealPowerQuotient K e M) :=
  idealPowerQuotientDesc (I ^ n ⊔ K ^ e) 1 (doubleIdealPowerQuotientProjection I K n e M)
    (idealPowerMultiple_sup_eq_bot
      (idealPowerMultiple_doubleIdealPowerQuotient_eq_bot_outer I K n e M)
      (idealPowerMultiple_doubleIdealPowerQuotient_eq_bot_inner I K n e M))

/-- The comparison in the other direction carries the projection onto the quotient by the sum to
the composite projection onto the double quotient. -/
public theorem idealPowerQuotientSupInv_π :
    cokernel.π (C := X.Modules) (idealPowerMultiple (I ^ n ⊔ K ^ e) 1 M).ι ≫
        idealPowerQuotientSupInv I K n e M =
      doubleIdealPowerQuotientProjection I K n e M :=
  idealPowerQuotientDesc_π _ _ _ _

/-- **The two-ideal double quotient is the quotient by the sum.** For a quasi-coherent `M` and
ideal sheaves `ℐ, 𝒦` with no containment between the relevant powers,
`(M / 𝒦 ᵉ M) / ℐ ⁿ (M / 𝒦 ᵉ M) ≅ M / (ℐ ⁿ + 𝒦 ᵉ) M`,
the sum being the join `ℐ ⁿ ⊔ 𝒦 ᵉ` in the complete lattice of quasi-coherent ideal sheaves. -/
public def idealPowerQuotientSupIso :
    idealPowerQuotient I n (idealPowerQuotient K e M) ≅
      idealPowerQuotient (I ^ n ⊔ K ^ e) 1 M :=
  isoOfEpiFac (epi_doubleIdealPowerQuotientProjection I K n e M)
    (epi_cokernel_π_submodule_ι (idealPowerMultiple (I ^ n ⊔ K ^ e) 1 M))
    (idealPowerQuotientSupHom I K n e M) (idealPowerQuotientSupInv I K n e M)
    (idealPowerQuotientSupHom_π I K n e M) (idealPowerQuotientSupInv_π I K n e M)

/-- The sum isomorphism is the comparison map. -/
@[simp]
public theorem idealPowerQuotientSupIso_hom :
    (idealPowerQuotientSupIso I K n e M).hom = idealPowerQuotientSupHom I K n e M :=
  rfl

/-- The inverse of the sum isomorphism is the comparison in the other direction. -/
@[simp]
public theorem idealPowerQuotientSupIso_inv :
    (idealPowerQuotientSupIso I K n e M).inv = idealPowerQuotientSupInv I K n e M :=
  rfl

end Sup

end Stacks.Algebraization

end
