module

public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.FormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerQuotientSections
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.InfinitesimalBaseIdealSections
public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.ReesCohomologyFiniteReduction
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkBaseChangeComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk form of the theorem on formal functions, on Tag 02O8 alone

Let `f : X ⟶ Y` be a proper morphism of schemes with `Y` locally Noetherian and let `y` be a
point of `Y`. `StacksFrontier/AlgebraicGeometry/FormalFunctions/StalkFormalFunctions.lean` states
[Stacks, Tag 02OD] at `p = 0` for the structure sheaf as the predicate
`Stacks.FormalFunctions.IsFormalFunctionsStalk f y` — the bijectivity of the comparison
`(f_* 𝒪_X)_y ^∧ ⟶ limₙ Γ(X_n, 𝒪_{X_n})` — and reduces it to the two uniform bounds of
[Stacks, Tag 02OB] read at the stalk. This file supplies those two bounds, and therefore proves
the predicate and [Stacks, Tag 0G7X] with it, from the single remaining hypothesis
[Stacks, Tag 02O8].

The mathematics is a transport. Write `A = 𝒪_{Y,y}`, `I = 𝔪_y`, `X' = X ×_Y Spec A` with
structure morphism `g : X' ⟶ Spec A`, and `𝓘 = I · 𝒪_{X'}`. Instantiating the affine side of
the theorem on formal functions
(`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`)
at `A`, `g`, `I`, `ℱ = 𝒪_{X'}` and `p = 0` produces one integer `c` with a bound on the kernels
of `H⁰(X', 𝒪_{X'}) ⟶ H⁰(X', 𝒪_{X'}/𝓘 ⁿ)` and a stabilization of the images in the tower. Those
are statements about the ideal-power quotients over the affine base; the two bounds
`Stacks.FormalFunctions.isFormalFunctionsStalk_of_uniformBounds` consumes are the same
statements about `(f_* 𝒪_X)_y ⟶ Γ(X_n, 𝒪_{X_n})`. Three identifications carry one to the other:

* degree zero is sections, by
  `Stacks.Cohomology.FormalFunctions.moduleGlobalSectionsRightDerivedZeroIso`;
* `𝒪_{X'}/𝓘 ⁿ` is the structure sheaf of the closed subscheme cut out by `𝓘 ⁿ`, by
  `Stacks.Cohomology.FormalFunctions.idealPowerQuotientSubschemeIso`, compatibly with the
  quotient projection and with lowering the exponent;
* that subscheme is the `n`-th infinitesimal neighbourhood of the fibre, by
  `Stacks.FormalFunctions.infinitesimalNeighbourhoodIsoSubscheme`, compatibly with the inclusion
  into `X'` and with the transition morphisms;

and finally `Stacks.FormalFunctions.stalkBaseChangeRestrictHom`, which is `𝒪_{Y,y}`-linear and —
by degree-zero flat base change along `Spec 𝒪_{Y,y} ⟶ Y`, [Stacks, Tag 02KH] part (1) at `i = 0`,
available as `Stacks.FormalFunctions.bijective_stalkBaseChangeRestrictHom` — bijective, moves the
statements from `Γ(X', 𝒪_{X'})` to the stalk `(f_* 𝒪_X)_y`.

## Main results

* `Stacks.FormalFunctions.isFormalFunctionsStalk_of_02O8` — **[Stacks, Tag 02OD] at `p = 0` for
  the structure sheaf, over a locally Noetherian base, granted [Stacks, Tag 02O8]**.
* `Stacks.FormalFunctions.extendsOverNeighbourhood_of_02O8` — **[Stacks, Tag 0G7X] over a
  locally Noetherian base, granted [Stacks, Tag 02O8]**: an idempotent global function on the
  fibre `X_y` extends to `f ⁻¹ U` for some open neighbourhood `U` of `y`.

**No `@[stacks 0G7X]` attribute is attached, and none may be**: both statements carry
[Stacks, Tag 02O8] as the named hypothesis `h02O8`, in the same general form
`Stacks.Cohomology.FormalFunctions.exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8`
consumes it, and this library does not prove it. The general case of [Stacks, Tag 0G7X], where
the base is not assumed locally Noetherian, is not addressed: the source reduces it to the
Noetherian case by writing `f` as a limit of proper morphisms of finite presentation, and that
reduction is not carried out here.

## Implementation notes

**Which bijections are needed where.** The transport of the kernel bound needs an
`𝒪_{Y,y}`-*linear* bijection on the source side, because that clause alone mentions a submodule
`I ^ (n - c) · M`; it is `Stacks.FormalFunctions.stalkToCohomology`, and the containment is moved
by its inverse through `Stacks.FormalFunctions.map_mem_pow_smul_top`. On the target side the only
thing asked of the identification `H⁰(X', 𝒪_{X'}/𝓘 ⁿ) ≅ Γ(X_n, 𝒪)` is that it be injective and
kill `0`. The transport of the image clause is a pure statement about ranges, and is done
element by element, so it needs no linearity at all — only that the two identifications be
bijections and intertwine the four maps. That is why no comparison between the `𝒪_{Y,y}`-module
structure of `Γ(X_n, 𝒪)` — through `Stacks.FormalFunctions.infinitesimalBaseRingHom` — and the
one coming from the affine base is ever needed.

**Spellings of the same type.** `Γ((𝓘 ⁿ).subscheme, ⊤)` and the global sections of the
pushforward of its structure sheaf to `X'` are definitionally equal but not syntactically so, and
the conversion between them is expensive enough that `rw` cannot be asked to perform it: the
unifier must whnf the pushforward side, which it only does when that side is given first. Every
lemma below is therefore stated in whichever of the two spellings its *consumers* produce, and
the places where the two meet are crossed in term mode — `congrArg` with an explicitly annotated
binder — rather than by rewriting.

## References

* [Stacks Project, Tag 02O8](https://stacks.math.columbia.edu/tag/02O8)
* [Stacks Project, Tag 02OB](https://stacks.math.columbia.edu/tag/02OB)
* [Stacks Project, Tag 02OC](https://stacks.math.columbia.edu/tag/02OC)
* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry ModuleCat.Algebra

universe u

namespace Stacks.FormalFunctions

open Stacks.Algebraization Stacks.Cohomology.FormalFunctions

attribute [local instance] Stacks.Cohomology.AffineBase.baseSectionsAlgebra

variable {X Y : Scheme.{u}}

/-! ### Two generalities -/

/-- A linear map carries `J ^ m M` into `J ^ m N`. -/
public theorem map_mem_pow_smul_top {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (e : M →ₗ[R] N) (J : Ideal R) (m : ℕ) {x : M}
    (hx : x ∈ J ^ m • (⊤ : Submodule R M)) : e x ∈ J ^ m • (⊤ : Submodule R N) := by
  refine Submodule.smul_induction_on hx (fun a ha z _ => ?_) fun z w hz hw => ?_
  · rw [map_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [map_add]
    exact add_mem hz hw

/-- Naturality of the degree-zero comparison, read on elements. -/
private theorem rightDerivedZeroIso_naturality_apply {W : Scheme.{u}} {M N : W.Modules}
    (φ : M ⟶ N) (x : ↥((((moduleGlobalSections W).rightDerived 0)).obj M)) :
    ((moduleGlobalSectionsRightDerivedZeroIso W).hom.app N).hom
        ((((moduleGlobalSections W).rightDerived 0).map φ).hom x) =
      φ.app ⊤ (((moduleGlobalSectionsRightDerivedZeroIso W).hom.app M).hom x) :=
  NatTrans.naturality_apply (moduleGlobalSectionsRightDerivedZeroIso W).hom φ x

/-- The degree-zero comparison is invertible, read on elements. -/
private theorem rightDerivedZeroIso_hom_inv_apply {W : Scheme.{u}} (M : W.Modules)
    (x : ↥((((moduleGlobalSections W).rightDerived 0)).obj M)) :
    ((moduleGlobalSectionsRightDerivedZeroIso W).inv.app M).hom
        (((moduleGlobalSectionsRightDerivedZeroIso W).hom.app M).hom x) = x :=
  ((moduleGlobalSectionsRightDerivedZeroIso W).app M).hom_inv_id_apply x

/-- The inverse of the degree-zero comparison, read on elements. -/
private theorem rightDerivedZeroIso_inv_hom_apply {W : Scheme.{u}} (M : W.Modules)
    (s : Γ(M, (⊤ : W.Opens))) :
    ((moduleGlobalSectionsRightDerivedZeroIso W).hom.app M).hom
        (((moduleGlobalSectionsRightDerivedZeroIso W).inv.app M).hom s) = s :=
  ((moduleGlobalSectionsRightDerivedZeroIso W).app M).inv_hom_id_apply s

/-! ### The tower of ideal-power quotients on the base change -/

section Transport

variable (f : X ⟶ Y) (y : Y)

/-- The quotient `𝒪_{X'} / (𝔪_y 𝒪_{X'}) ⁿ` on `X' = X ×_Y Spec 𝒪_{Y,y}`. -/
private abbrev baseQuotient (n : ℕ) : (stalkBaseChange f y).Modules :=
  idealPowerQuotient (infinitesimalBaseIdealSheaf f y) n
    (Scheme.unitModule (stalkBaseChange f y))

/-- The projection `𝒪_{X'} ⟶ 𝒪_{X'} / (𝔪_y 𝒪_{X'}) ⁿ`. -/
private abbrev baseQuotientπ (n : ℕ) :
    Scheme.unitModule (stalkBaseChange f y) ⟶ baseQuotient f y n :=
  cokernel.π (C := (stalkBaseChange f y).Modules)
    (idealPowerMultiple (infinitesimalBaseIdealSheaf f y) n
      (Scheme.unitModule (stalkBaseChange f y))).ι

private theorem subschemeIso_appTop_inv_hom (n : ℕ) :
    (infinitesimalNeighbourhoodIsoSubscheme f y n).inv.appTop ≫
        (infinitesimalNeighbourhoodIsoSubscheme f y n).hom.appTop = 𝟙 _ := by
  rw [← Scheme.Hom.comp_appTop, Iso.hom_inv_id]
  rfl

private theorem subschemeIso_appTop_hom_inv (n : ℕ) :
    (infinitesimalNeighbourhoodIsoSubscheme f y n).hom.appTop ≫
        (infinitesimalNeighbourhoodIsoSubscheme f y n).inv.appTop = 𝟙 _ := by
  rw [← Scheme.Hom.comp_appTop, Iso.inv_hom_id]
  rfl

private theorem subschemeIso_hom_inv (n : ℕ)
    (s : Γ((infinitesimalBaseIdealSheaf f y ^ n).subscheme, ⊤)) :
    ((infinitesimalNeighbourhoodIsoSubscheme f y n).hom.appTop).hom
        (((infinitesimalNeighbourhoodIsoSubscheme f y n).inv.appTop).hom s) = s :=
  ConcreteCategory.congr_hom (subschemeIso_appTop_inv_hom f y n) s

private theorem subschemeIso_inv_hom (n : ℕ)
    (t : Γ(infinitesimalNeighbourhood f y n, ⊤)) :
    ((infinitesimalNeighbourhoodIsoSubscheme f y n).inv.appTop).hom
        (((infinitesimalNeighbourhoodIsoSubscheme f y n).hom.appTop).hom t) = t :=
  ConcreteCategory.congr_hom (subschemeIso_appTop_hom_inv f y n) t

private theorem quotIso_hom_inv (n : ℕ)
    (s : Γ((infinitesimalBaseIdealSheaf f y ^ n).subscheme, ⊤)) :
    (idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) n).hom.app ⊤
        ((idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) n).inv.app ⊤ s) =
      s :=
  ((moduleGlobalSections (stalkBaseChange f y)).mapIso
    (idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) n)).inv_hom_id_apply s

private theorem quotIso_inv_hom (n : ℕ) (w : Γ(baseQuotient f y n,
    (⊤ : (stalkBaseChange f y).Opens))) :
    (idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) n).inv.app ⊤
        ((idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) n).hom.app ⊤ w) =
      w :=
  ((moduleGlobalSections (stalkBaseChange f y)).mapIso
    (idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) n)).hom_inv_id_apply w

/-! ### Global sections of the quotients are the functions on the infinitesimal neighbourhoods -/

/-- `Γ(X', 𝒪_{X'}/𝓘 ⁿ) ⟶ Γ(X_n, 𝒪)`. -/
private def quotSectionsToInfinitesimal (n : ℕ)
    (w : Γ(baseQuotient f y n, (⊤ : (stalkBaseChange f y).Opens))) :
    Γ(infinitesimalNeighbourhood f y n, ⊤) :=
  ((infinitesimalNeighbourhoodIsoSubscheme f y n).inv.appTop).hom
    ((idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) n).hom.app ⊤ w)

/-- The inverse of `Stacks.FormalFunctions.quotSectionsToInfinitesimal`. -/
private def infinitesimalToQuotSections (n : ℕ) (t : Γ(infinitesimalNeighbourhood f y n, ⊤)) :
    Γ(baseQuotient f y n, (⊤ : (stalkBaseChange f y).Opens)) :=
  (idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) n).inv.app ⊤
    (((infinitesimalNeighbourhoodIsoSubscheme f y n).hom.appTop).hom t)

private theorem quotSectionsToInfinitesimal_infinitesimalToQuotSections (n : ℕ)
    (t : Γ(infinitesimalNeighbourhood f y n, ⊤)) :
    quotSectionsToInfinitesimal f y n (infinitesimalToQuotSections f y n t) = t := by
  change ((infinitesimalNeighbourhoodIsoSubscheme f y n).inv.appTop).hom
      ((idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) n).hom.app ⊤
        ((idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) n).inv.app ⊤
          (((infinitesimalNeighbourhoodIsoSubscheme f y n).hom.appTop).hom t))) = t
  rw [quotIso_hom_inv, subschemeIso_inv_hom]

private theorem infinitesimalToQuotSections_quotSectionsToInfinitesimal (n : ℕ)
    (w : Γ(baseQuotient f y n, (⊤ : (stalkBaseChange f y).Opens))) :
    infinitesimalToQuotSections f y n (quotSectionsToInfinitesimal f y n w) = w :=
  (congrArg (fun s : Γ((infinitesimalBaseIdealSheaf f y ^ n).subscheme, ⊤) =>
      (idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) n).inv.app ⊤ s)
    (subschemeIso_hom_inv f y n
      ((idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) n).hom.app ⊤
        w))).trans (quotIso_inv_hom f y n w)

/-- **The projection square on sections.** -/
private theorem quotSectionsToInfinitesimal_π (n : ℕ) (s : Γ(stalkBaseChange f y, ⊤)) :
    quotSectionsToInfinitesimal f y n ((baseQuotientπ f y n).app ⊤ s) =
      ((infinitesimalιBaseChange f y n).appTop).hom s := by
  have h1 := idealPowerQuotientSubschemeSectionsIso_hom_app_top_π
    (infinitesimalBaseIdealSheaf f y) n s
  have h2 := ConcreteCategory.congr_hom (subschemeι_appTop_eq f y n) s
  rw [CommRingCat.comp_apply] at h2
  change ((infinitesimalNeighbourhoodIsoSubscheme f y n).inv.appTop).hom
      ((idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) n).hom.app ⊤
        ((baseQuotientπ f y n).app ⊤ s)) = _
  rw [h1, h2, subschemeIso_inv_hom]

/-- Restricting along the inclusion of ideal-power subschemes is, under the identification of
those subschemes with the infinitesimal neighbourhoods, the transition map. -/
private theorem transition_appTop_eq_of_inclusion {n k : ℕ} (h : n ≤ k)
    (s : Γ((infinitesimalBaseIdealSheaf f y ^ k).subscheme, ⊤)) :
    ((infinitesimalNeighbourhoodIsoSubscheme f y n).inv.appTop).hom
        ((idealPowerSubschemeInclusion (infinitesimalBaseIdealSheaf f y) h).appTop s) =
      ((infinitesimalTransition f y h).appTop).hom
        (((infinitesimalNeighbourhoodIsoSubscheme f y k).inv.appTop).hom s) := by
  have h2 := ConcreteCategory.congr_hom (appTop_infinitesimalTransition_eq f y h)
    (((infinitesimalNeighbourhoodIsoSubscheme f y k).inv.appTop).hom s)
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply, subschemeIso_hom_inv] at h2
  rw [← h2, subschemeIso_inv_hom]

/-- **The transition square on sections.** -/
private theorem quotSectionsToInfinitesimal_drop {n k : ℕ} (h : n ≤ k)
    (w : Γ(baseQuotient f y k, (⊤ : (stalkBaseChange f y).Opens))) :
    quotSectionsToInfinitesimal f y n
        ((idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) h
          (Scheme.unitModule (stalkBaseChange f y))).app ⊤ w) =
      ((infinitesimalTransition f y h).appTop).hom (quotSectionsToInfinitesimal f y k w) :=
  (congrArg (fun s : Γ((infinitesimalBaseIdealSheaf f y ^ n).subscheme, ⊤) =>
      ((infinitesimalNeighbourhoodIsoSubscheme f y n).inv.appTop).hom s)
    (idealPowerQuotientSubschemeSectionsIso_hom_app_top_drop
      (infinitesimalBaseIdealSheaf f y) h w)).trans
    (transition_appTop_eq_of_inclusion f y h
      ((idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) k).hom.app ⊤ w))

private theorem quotSectionsToInfinitesimal_zero (n : ℕ) :
    quotSectionsToInfinitesimal f y n 0 = 0 :=
  (congrArg (fun s : Γ((infinitesimalBaseIdealSheaf f y ^ n).subscheme, ⊤) =>
      ((infinitesimalNeighbourhoodIsoSubscheme f y n).inv.appTop).hom s)
    (map_zero ((idealPowerQuotientSubschemeIso (infinitesimalBaseIdealSheaf f y) n).hom.app
      ⊤).hom)).trans (map_zero ((infinitesimalNeighbourhoodIsoSubscheme f y n).inv.appTop).hom)

/-! ### The comparison out of the cohomology of the base change -/

/-- **`H⁰(X', 𝒪_{X'}/𝓘 ⁿ) ⟶ Γ(X_n, 𝒪)`**, degree-zero cohomology included. -/
private def quotToInfinitesimal (n : ℕ)
    (x : ↥((((moduleGlobalSections (stalkBaseChange f y)).rightDerived 0)).obj
      (baseQuotient f y n))) : Γ(infinitesimalNeighbourhood f y n, ⊤) :=
  quotSectionsToInfinitesimal f y n
    (((moduleGlobalSectionsRightDerivedZeroIso (stalkBaseChange f y)).hom.app
      (baseQuotient f y n)).hom x)

/-- The inverse of `Stacks.FormalFunctions.quotToInfinitesimal`. -/
private def infinitesimalToQuot (n : ℕ) (t : Γ(infinitesimalNeighbourhood f y n, ⊤)) :
    ↥((((moduleGlobalSections (stalkBaseChange f y)).rightDerived 0)).obj
      (baseQuotient f y n)) :=
  ((moduleGlobalSectionsRightDerivedZeroIso (stalkBaseChange f y)).inv.app
      (baseQuotient f y n)).hom (infinitesimalToQuotSections f y n t)

private theorem quotToInfinitesimal_infinitesimalToQuot (n : ℕ)
    (t : Γ(infinitesimalNeighbourhood f y n, ⊤)) :
    quotToInfinitesimal f y n (infinitesimalToQuot f y n t) = t :=
  (congrArg (quotSectionsToInfinitesimal f y n)
    (rightDerivedZeroIso_inv_hom_apply (baseQuotient f y n)
      (infinitesimalToQuotSections f y n t))).trans
    (quotSectionsToInfinitesimal_infinitesimalToQuotSections f y n t)

private theorem infinitesimalToQuot_quotToInfinitesimal (n : ℕ)
    (x : ↥((((moduleGlobalSections (stalkBaseChange f y)).rightDerived 0)).obj
      (baseQuotient f y n))) :
    infinitesimalToQuot f y n (quotToInfinitesimal f y n x) = x :=
  (congrArg ((moduleGlobalSectionsRightDerivedZeroIso (stalkBaseChange f y)).inv.app
      (baseQuotient f y n)).hom
    (infinitesimalToQuotSections_quotSectionsToInfinitesimal f y n
      (((moduleGlobalSectionsRightDerivedZeroIso (stalkBaseChange f y)).hom.app
        (baseQuotient f y n)).hom x))).trans
    (rightDerivedZeroIso_hom_inv_apply (baseQuotient f y n) x)

private theorem quotToInfinitesimal_bijective (n : ℕ) :
    Function.Bijective (quotToInfinitesimal f y n) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨infinitesimalToQuot f y n, infinitesimalToQuot_quotToInfinitesimal f y n,
      quotToInfinitesimal_infinitesimalToQuot f y n⟩

private theorem quotToInfinitesimal_zero (n : ℕ) : quotToInfinitesimal f y n 0 = 0 :=
  (congrArg (quotSectionsToInfinitesimal f y n)
      (map_zero ((moduleGlobalSectionsRightDerivedZeroIso (stalkBaseChange f y)).hom.app
        (baseQuotient f y n)).hom)).trans (quotSectionsToInfinitesimal_zero f y n)

/-- **The transition square.** -/
private theorem quotToInfinitesimal_drop {n k : ℕ} (h : n ≤ k)
    (z : ↥((((moduleGlobalSections (stalkBaseChange f y)).rightDerived 0)).obj
      (baseQuotient f y k))) :
    quotToInfinitesimal f y n
        ((((moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
          (idealPowerQuotientDrop (infinitesimalBaseIdealSheaf f y) h
            (Scheme.unitModule (stalkBaseChange f y)))).hom z) =
      infinitesimalFunctionsMap f y n k h (quotToInfinitesimal f y k z) :=
  (congrArg (quotSectionsToInfinitesimal f y n)
    (rightDerivedZeroIso_naturality_apply _ z)).trans
    (quotSectionsToInfinitesimal_drop f y h _)

/-! ### The comparison out of the stalk -/

/-- **The map `(f_* 𝒪_X)_y ⟶ H⁰(X', 𝒪_{X'})` of `𝒪_{Y,y}`-modules**, the degree-zero flat base
change comparison read through the identification of `H⁰` with global sections. -/
private def stalkToCohomology :
    pushforwardStalkModule f y →ₗ[↥(Y.presheaf.stalk y)]
      cohomologyOverBase ↥(Y.presheaf.stalk y) (stalkBaseChangeStructure f y) 0
        (Scheme.unitModule (stalkBaseChange f y)) where
  toFun a := ((moduleGlobalSectionsRightDerivedZeroIso (stalkBaseChange f y)).inv.app
    (Scheme.unitModule (stalkBaseChange f y))).hom ((stalkBaseChangeRestrictHom f y).hom a)
  map_add' a b := by
    simp only [map_add]
    exact map_add ((moduleGlobalSectionsRightDerivedZeroIso (stalkBaseChange f y)).inv.app
      (Scheme.unitModule (stalkBaseChange f y))).hom _ _
  map_smul' r a := by
    have hr : (stalkBaseChangeRestrictHom f y).hom ((toPushforwardStalk f y).hom r) =
        baseRingHom ↥(Y.presheaf.stalk y) (stalkBaseChangeStructure f y) r := by
      have h := ConcreteCategory.congr_hom
        (stalkBaseChangeRestrictHom_toPushforwardStalk f y) r
      rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
      exact h
    change ((moduleGlobalSectionsRightDerivedZeroIso (stalkBaseChange f y)).inv.app
        (Scheme.unitModule (stalkBaseChange f y))).hom
        ((stalkBaseChangeRestrictHom f y).hom ((toPushforwardStalk f y).hom r * a)) =
      (baseRingHom ↥(Y.presheaf.stalk y) (stalkBaseChangeStructure f y) r) •
        ((moduleGlobalSectionsRightDerivedZeroIso (stalkBaseChange f y)).inv.app
          (Scheme.unitModule (stalkBaseChange f y))).hom
          ((stalkBaseChangeRestrictHom f y).hom a)
    rw [map_mul, hr]
    exact map_smul ((moduleGlobalSectionsRightDerivedZeroIso (stalkBaseChange f y)).inv.app
      (Scheme.unitModule (stalkBaseChange f y))).hom _ _

private theorem stalkToCohomology_bijective
    (hbc : Function.Bijective (stalkBaseChangeRestrictHom f y).hom) :
    Function.Bijective (stalkToCohomology f y) := by
  have hiso : Function.Bijective ((moduleGlobalSectionsRightDerivedZeroIso
      (stalkBaseChange f y)).inv.app (Scheme.unitModule (stalkBaseChange f y))).hom :=
    Function.bijective_iff_has_inverse.2
      ⟨((moduleGlobalSectionsRightDerivedZeroIso (stalkBaseChange f y)).hom.app
          (Scheme.unitModule (stalkBaseChange f y))).hom,
        rightDerivedZeroIso_inv_hom_apply (Scheme.unitModule (stalkBaseChange f y)),
        rightDerivedZeroIso_hom_inv_apply (Scheme.unitModule (stalkBaseChange f y))⟩
  exact hiso.comp hbc

/-- **The projection square.** -/
private theorem quotToInfinitesimal_stalk (n : ℕ) (a : pushforwardStalkModule f y) :
    quotToInfinitesimal f y n
        ((((moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
          (baseQuotientπ f y n)).hom (stalkToCohomology f y a)) =
      infinitesimalStalkRestrict f y n a := by
  have e3 := ConcreteCategory.congr_hom (infinitesimalStalkRestrictHom_eq f y n) a
  rw [CommRingCat.comp_apply] at e3
  refine ((congrArg (quotSectionsToInfinitesimal f y n)
    (rightDerivedZeroIso_naturality_apply (baseQuotientπ f y n)
      (stalkToCohomology f y a))).trans
    ((quotSectionsToInfinitesimal_π f y n _).trans ?_))
  refine (congrArg ((infinitesimalιBaseChange f y n).appTop).hom
    (rightDerivedZeroIso_inv_hom_apply (Scheme.unitModule (stalkBaseChange f y))
      ((stalkBaseChangeRestrictHom f y).hom a))).trans e3.symm

end Transport

/-! ### The two bounds, and the theorem -/

/-- **The stalk form of the theorem on formal functions at `p = 0` for the structure sheaf,
granted [Stacks, Tag 02O8].** -/
public theorem isFormalFunctionsStalk_of_02O8 (f : X ⟶ Y) [IsProper f] [IsLocallyNoetherian Y]
    (y : Y)
    (h02O8 : ∀ (A' : Type u) [CommRing A'] [IsNoetherianRing A'] (I' : Ideal A')
      (X' : Over (Spec (.of A'))) (_ : AlgebraicGeometry.IsProper X'.hom)
      (F' : X'.left.Modules) (_ : Stacks.SheafOfModules.IsCoherent F') (p' : ℕ),
      (cohomologyIdealPowerSystem I' X' F' p').IsReesFinite) :
    IsFormalFunctionsStalk f y := by
  have hA : IsNoetherianRing ↥(Y.presheaf.stalk y) := inferInstance
  have : IsLocallyNoetherian (stalkBaseChange f y) := inferInstance
  have hcoh : Stacks.SheafOfModules.IsCoherent (Scheme.unitModule (stalkBaseChange f y)) :=
    Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent
      Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have hbc := bijective_stalkBaseChangeRestrictHom f y
  obtain ⟨c, hker, -, hrange⟩ :=
    @exists_uniform_bound_cohomology_idealPowerQuotient_of_02O8 ↥(Y.presheaf.stalk y) _ hA _
      (stalkBaseChangeStructure f y) inferInstance (stalkMaximalIdeal y)
      (Scheme.unitModule (stalkBaseChange f y)) hcoh 0 h02O8
  refine isFormalFunctionsStalk_of_uniformBounds f y c (fun n hn x hx => ?_)
    (fun n k hnk hc => ?_)
  · have hx0 : quotToInfinitesimal f y n
        ((((moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
          (baseQuotientπ f y n)).hom (stalkToCohomology f y x)) = 0 :=
      (quotToInfinitesimal_stalk f y n x).trans (LinearMap.mem_ker.1 hx)
    have hz : (((moduleGlobalSections (stalkBaseChange f y)).rightDerived 0).map
        (baseQuotientπ f y n)).hom (stalkToCohomology f y x) = 0 :=
      (quotToInfinitesimal_bijective f y n).1
        (hx0.trans (quotToInfinitesimal_zero f y n).symm)
    have hmem := hker n hn (LinearMap.mem_ker.2 hz)
    have hsymm := map_mem_pow_smul_top
      (LinearEquiv.ofBijective (stalkToCohomology f y)
        (stalkToCohomology_bijective f y hbc)).symm.toLinearMap
      (stalkMaximalIdeal y) (n - c) hmem
    rwa [show (LinearEquiv.ofBijective (stalkToCohomology f y)
        (stalkToCohomology_bijective f y hbc)).symm.toLinearMap
        (stalkToCohomology f y x) = x from
      (LinearEquiv.ofBijective (stalkToCohomology f y)
        (stalkToCohomology_bijective f y hbc)).symm_apply_apply x] at hsymm
  · refine Submodule.ext fun t => ⟨?_, ?_⟩
    · rintro ⟨s, rfl⟩
      obtain ⟨z, hz⟩ := (quotToInfinitesimal_bijective f y k).2 s
      obtain ⟨v, hv⟩ := LinearMap.mem_range.1 ((hrange n k hc).le (LinearMap.mem_range_self _ z))
      obtain ⟨a, ha⟩ := (stalkToCohomology_bijective f y hbc).2 v
      exact ⟨a, by rw [← quotToInfinitesimal_stalk f y n a, ha, hv,
        quotToInfinitesimal_drop f y hnk z, hz]⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨z, hz⟩ := LinearMap.mem_range.1
        ((hrange n k hc).ge (LinearMap.mem_range_self _ (stalkToCohomology f y a)))
      exact ⟨quotToInfinitesimal f y k z,
        by rw [← quotToInfinitesimal_drop f y hnk z, hz]; exact quotToInfinitesimal_stalk f y n a⟩

/-- **Stacks Tag 0G7X over a locally Noetherian base**, granted Tag 02O8. -/
public theorem extendsOverNeighbourhood_of_02O8 (f : X ⟶ Y) [IsProper f]
    [IsLocallyNoetherian Y] (y : Y)
    (h02O8 : ∀ (A' : Type u) [CommRing A'] [IsNoetherianRing A'] (I' : Ideal A')
      (X' : Over (Spec (.of A'))) (_ : AlgebraicGeometry.IsProper X'.hom)
      (F' : X'.left.Modules) (_ : Stacks.SheafOfModules.IsCoherent F') (p' : ℕ),
      (cohomologyIdealPowerSystem I' X' F' p').IsReesFinite)
    (e : Γ(f.fiber y, ⊤)) (he : IsIdempotentElem e) :
    Stacks.AlgebraicGeometry.Fibres.ExtendsOverNeighbourhood f y e :=
  extendsOverNeighbourhood_of_isFormalFunctionsStalk f y
    (isFormalFunctionsStalk_of_02O8 f y h02O8) e he

/-! ### Tag 02O8 discharged -/

/-- **[Stacks, Tag 02O8] in the general form the transport above consumes.**  The graded module
`⨁ₙ Hᵖ(X, Iⁿℱ)` is finite over the Rees algebra `⨁ₙ Iⁿ`, for every Noetherian base ring, every
ideal of it, every proper scheme over it, every coherent module and every degree.  This is
`Stacks.Cohomology.FormalFunctions.isCohomologyReesFinite`, quantified. -/
@[ega "III 3.3.2", ega "III 4.1.7.7", sga "2 XII 5.8" "(ii), special case"]
public theorem isReesFinite_cohomologyIdealPowerSystem :
    ∀ (A' : Type u) [CommRing A'] [IsNoetherianRing A'] (I' : Ideal A')
      (X' : Over (Spec (.of A'))) (_ : AlgebraicGeometry.IsProper X'.hom)
      (F' : X'.left.Modules) (_ : Stacks.SheafOfModules.IsCoherent F') (p' : ℕ),
      (cohomologyIdealPowerSystem I' X' F' p').IsReesFinite := by
  intro A' _ _ I' X' hX' F' hF' p'
  have : _root_.SheafOfModules.IsCoherent F' :=
    AlgebraicGeometry.CoherentAbelian.isCoherent_of_stacksIsCoherent hF'
  exact isCohomologyReesFinite I' X' F' p' hX'

/-- **[Stacks, Tag 0G7X] over a locally Noetherian base, unconditionally.**  For `f : X ⟶ Y`
proper with `Y` locally Noetherian and `y` a point of `Y`, every idempotent of
`Γ(X_y, 𝒪_{X_y})` is the restriction of a section of `𝒪_X` over `f ⁻¹ᵁ U` for some open
neighbourhood `U` of `y` — equivalently, it lies in the image of `(f_* 𝒪_X)_y`.

**No `@[stacks 0G7X]` attribute, and none may be attached**: Tag 0G7X assumes nothing about `Y`
beyond `f` being proper, and `[IsLocallyNoetherian Y]` is a *strengthened* hypothesis, so this
statement is weaker than the tag.  The source proves the general case from this one by the
approximation argument of [Stacks, Tag 0A0P], which is not carried out in this repository. -/
public theorem extendsOverNeighbourhood_of_isLocallyNoetherian (f : X ⟶ Y) [IsProper f]
    [IsLocallyNoetherian Y] (y : Y) (e : Γ(f.fiber y, ⊤)) (he : IsIdempotentElem e) :
    Stacks.AlgebraicGeometry.Fibres.ExtendsOverNeighbourhood f y e :=
  extendsOverNeighbourhood_of_02O8 f y isReesFinite_cohomologyIdealPowerSystem e he

/-- **The stalk form of [Stacks, Tag 02OD] at `p = 0` for the structure sheaf**, for a proper
morphism onto a locally Noetherian base, unconditionally. -/
public theorem isFormalFunctionsStalk_of_isProper (f : X ⟶ Y) [IsProper f]
    [IsLocallyNoetherian Y] (y : Y) : IsFormalFunctionsStalk f y :=
  isFormalFunctionsStalk_of_02O8 f y isReesFinite_cohomologyIdealPowerSystem

end Stacks.FormalFunctions

end
