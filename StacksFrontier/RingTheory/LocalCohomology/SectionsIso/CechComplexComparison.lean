module

public import Mathlib.CategoryTheory.Limits.Lattice
public import StacksFrontier.CategoryTheory.Sites.CechComplex
public import StacksFrontier.RingTheory.CechComplexHomology
public import StacksFrontier.RingTheory.LocalCohomology.BasicOpenSections.Glue
public import StacksFrontier.RingTheory.LocalCohomology.MappingConeH0.Cover
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Čech complex of a standard open cover and the algebraic Čech complex

Let `R` be a commutative ring, `f : Fin n → R` a finite family of elements and `M` an
`R`-module whose universe is independent of the ring's. The standard opens `D(f i)` form a
family of opens of `Spec R`, and the Čech complex of that family with coefficients in the
quasi-coherent module `M̃` is `CategoryTheory.cechComplexFunctor` applied to the presheaf of
sections of `M̃`: its degree-`m` term is the product, over all tuples
`x : Fin (m + 1) → Fin n`, of the sections of `M̃` over the intersection
`D(f (x 0)) ∩ ⋯ ∩ D(f (x m))`.

On the algebraic side `StacksFrontier.RingTheory.CechAcyclicity` builds the same complex out of
localizations: the degree-`m` term `CechTerm M f 1 m` is the product, over the same tuples, of
the modules `M` localized away from `1 * f (x 0) ⋯ f (x m)`, and
`StacksFrontier.RingTheory.CechComplexHomology` packages it as an object of
`CochainComplex (ModuleCat R) ℕ`.

This file identifies the two **as cochain complexes**, not merely degreewise. The intersection
of the members of the family selected by a tuple is the standard open of the product of the
selected elements, and the sections of `M̃` on a standard open `D(g)` are the localization
`M_g`; so the terms agree. Both differentials are the alternating sum of the restriction maps
along the face maps of a tuple, and a restriction map out of a localization is determined by
its value on the constant fractions `m / 1`; so the differentials agree.

## Main definitions

* `Stacks.LocalCohomology.moduleSectionsPresheaf` — the presheaf of `R`-modules of locally
  fractional sections of `M̃` on the opens of `Spec R`.
* `Stacks.LocalCohomology.standardCechTermEquiv` — the identification
  `Γ(D(f (x 0)) ∩ ⋯ ∩ D(f (x m)), M̃) ≃ₗ[R] M_{f (x 0) ⋯ f (x m)}`.
* `Stacks.LocalCohomology.standardCechTermIso` — the degreewise identification of the two
  complexes.
* `Stacks.LocalCohomology.standardCechComplexIso` — **the identification of the two complexes**.

## Main results

* `Stacks.LocalCohomology.interStandardOpen_eq_basicOpen` — the intersection selected by a
  tuple is the standard open of the product of the selected elements.
* `Stacks.LocalCohomology.moduleSectionsRestrict_eq_resAway` — restriction of sections between
  standard opens is the canonical map of localizations.
* `Stacks.LocalCohomology.d_comp_toStandardCechTerm` — the degreewise identification commutes
  with the two differentials.

## Implementation notes

The family of opens is `fun i ↦ basicOpen (f i)` in the lattice `Opens (Spec R)`, where the
terminal object is the whole spectrum. The Čech *complex* of a family does not refer to the
covered object at all — only its augmentation does — so no slice category is needed here, and
in particular this is the right complex to compare with the algebraic one for a family whose
standard opens cover a proper open subset of `Spec R`. Reconciling it with the complex of the
same family taken in the slice over the open it covers, which is the form
`Stacks.Cohomology.CechSheaf.cechComplexFunctorOfCover` takes and in which the coefficients are
modules over the ring of sections on that open rather than over `R`, is not done here.

The twist `1` of the algebraic complex is kept rather than cancelled, so that the degree-`m`
term localizes away from `1 * tupleProd f x` and matches
`Stacks.RingTheory.CechAcyclicity.CechTerm` syntactically; this is the same convention as
`StacksFrontier/AlgebraicGeometry/Cohomology/Cech/StandardCoverVanishing.lean`, which proves the
degreewise comparison for a quasi-coherent module on an affine open of a scheme and deliberately
does not assemble it into an isomorphism of complexes.

The localizing element of the degree-`m` term is the product `f (x 0) ⋯ f (x m)` over the
*tuple*, taken with multiplicity, and not the product over the set of indices occurring in the
tuple. The two differ, but they have the same standard open and the same localization; using the
tuple product means no finite set of indices and no reindexing appears on either side.

## References

* [Stacks Project, Tag 01EO](https://stacks.math.columbia.edu/tag/01EO)
* [Stacks Project, Tag 01HR](https://stacks.math.columbia.edu/tag/01HR)
* [Stacks Project, Tag 01X9](https://stacks.math.columbia.edu/tag/01X9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open PrimeSpectrum (basicOpen)
open Stacks.CategoryTheory.CechComplex
open Stacks.RingTheory.CechAcyclicity

universe v u

namespace Stacks.LocalCohomology

attribute [local instance] ModuleCat.hasLimitsOfSize

variable {R : Type u} [CommRing R] {n : ℕ} (f : Fin n → R) (M : ModuleCat.{max u v} R)

/-- Products indexed by `Type` in `ModuleCat.{max u v} R`, stated directly: since the bump the
search through `ModuleCat.hasLimitsOfSize` and its `UnivLE` side goal times out. -/
local instance : HasProducts.{0} (ModuleCat.{max u v} R) := fun J ↦
  (ModuleCat.hasLimitsOfSize.{0, 0, max u v, u} (R := R)).has_limits_of_shape (Discrete J)

/-! ### The presheaf of sections of the associated module -/

/-- The presheaf of `R`-modules of locally fractional sections of `M̃` on the opens of `Spec R`:
its value on an open `U` is `Γ(U, M̃) = moduleSections M U` and its restriction maps are
`Stacks.LocalCohomology.moduleSectionsRestrict`. This is the presheaf whose Čech complex for a
family of standard opens is compared with the algebraic Čech complex below. -/
def moduleSectionsPresheaf : (Opens (PrimeSpectrum.Top R))ᵒᵖ ⥤ ModuleCat.{max u v} R where
  obj U := ModuleCat.of R (moduleSections M U.unop)
  map i := ModuleCat.ofHom (moduleSectionsRestrict M (leOfHom i.unop))
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The value of the presheaf of sections of `M̃` on an open is the module of locally fractional
sections there. -/
@[simp]
theorem moduleSectionsPresheaf_obj (U : (Opens (PrimeSpectrum.Top R))ᵒᵖ) :
    (moduleSectionsPresheaf M).obj U = ModuleCat.of R (moduleSections M U.unop) :=
  rfl

/-- The restriction maps of the presheaf of sections of `M̃` are
`Stacks.LocalCohomology.moduleSectionsRestrict`. -/
@[simp]
theorem moduleSectionsPresheaf_map {U V : (Opens (PrimeSpectrum.Top R))ᵒᵖ} (i : U ⟶ V) :
    (moduleSectionsPresheaf M).map i =
      ModuleCat.ofHom (moduleSectionsRestrict M (leOfHom i.unop)) :=
  rfl

/-! ### The intersections of a family of standard opens -/

/-- The standard open of the product of the elements selected by a tuple is the intersection of
the standard opens of those elements. -/
theorem basicOpen_tupleProd_eq_iInf :
    ∀ {m : ℕ} (x : Fin (m + 1) → Fin n),
      basicOpen (tupleProd f x) = ⨅ k, basicOpen (f (x k)) := by
  intro m
  induction m with
  | zero =>
    intro x
    rw [tupleProd, Fin.prod_univ_one]
    exact le_antisymm (le_iInf fun k ↦ by rw [Fin.fin_one_eq_zero k]) (iInf_le _ 0)
  | succ m ih =>
    intro x
    have h : basicOpen (∏ i : Fin (m + 1), f (x i.succ)) =
        ⨅ k : Fin (m + 1), basicOpen (f (x k.succ)) := ih fun k ↦ x k.succ
    rw [tupleProd, Fin.prod_univ_succ, PrimeSpectrum.basicOpen_mul, h]
    exact le_antisymm
      (le_iInf (Fin.cases inf_le_left fun j ↦ inf_le_right.trans (iInf_le _ j)))
      (le_inf (iInf_le _ 0) (le_iInf fun k ↦ iInf_le _ k.succ))

/-- The intersection of the members of the family `D(f i)` selected by a tuple `x` is the
standard open of `1 * tupleProd f x`; the twist by `1` matches the degree-`m` term of the
algebraic Čech complex. -/
theorem interStandardOpen_eq_basicOpen {m : ℕ} (x : Fin (m + 1) → Fin n) :
    inter (fun i ↦ basicOpen (f i)) x = basicOpen (1 * tupleProd f x) := by
  rw [inter_eq_iInf, one_mul, basicOpen_tupleProd_eq_iInf]

/-! ### Restriction of sections between standard opens -/

/-- **Restriction of sections between standard opens is the canonical map of localizations.**
For `a ∣ b` the standard open `D(b)` is contained in `D(a)`, and restricting sections of `M̃`
from `D(a)` to `D(b)` becomes, under `Γ(D(g), M̃) ≅ M_g`, the map `M_a ⟶ M_b` of
`Stacks.RingTheory.CechAcyclicity.resAway`. Both sides are `R`-linear maps out of a localization
of `M` at the powers of `a` which agree on the constant fractions `m / 1`, so they agree. -/
theorem moduleSectionsRestrict_eq_resAway {a b : R} (hab : a ∣ b)
    (hle : basicOpen b ≤ basicOpen a) :
    (moduleSectionsBasicOpenEquiv M b).toLinearMap.comp (moduleSectionsRestrict M hle) =
      (resAway (M : Type _) hab).comp (moduleSectionsBasicOpenEquiv M a).toLinearMap := by
  refine IsLocalizedModule.ext (Submonoid.powers a) (moduleSectionsMk M (basicOpen a))
    (isUnit_powers_awayLoc (M := (M : Type _)) hab) (LinearMap.ext fun m ↦ ?_)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [show moduleSectionsRestrict M hle (moduleSectionsMk M (basicOpen a) m) =
      moduleSectionsMk M (basicOpen b) m from
    LinearMap.congr_fun (moduleSectionsRestrict_comp_moduleSectionsMk M hle) m]
  rw [moduleSectionsBasicOpenEquiv_moduleSectionsMk,
    moduleSectionsBasicOpenEquiv_moduleSectionsMk, resAway_mk_one]

/-- `Stacks.LocalCohomology.moduleSectionsRestrict_eq_resAway` with both opens presented through
an equality with a standard open, which is how they occur in the Čech complex: the terms of the
Čech complex are the sections over the categorical products `inter`, and those are only *equal*
to standard opens, not given as such. -/
theorem moduleSectionsBasicOpenEquiv_congr_restrict {a b : R} (hab : a ∣ b)
    {U W : Opens (PrimeSpectrum.Top R)} (hU : U = basicOpen a) (hW : W = basicOpen b)
    (hle : W ≤ U) (z : moduleSections M U) :
    moduleSectionsBasicOpenEquiv M b
        (moduleSectionsCongr M hW (moduleSectionsRestrict M hle z)) =
      resAway (M : Type _) hab
        (moduleSectionsBasicOpenEquiv M a (moduleSectionsCongr M hU z)) := by
  subst hU
  subst hW
  exact LinearMap.congr_fun (moduleSectionsRestrict_eq_resAway M hab hle) z

/-! ### The degreewise comparison of the two complexes -/

/-- **`Γ(D(f (x 0)) ∩ ⋯ ∩ D(f (x m)), M̃) ≅ M_{f (x 0) ⋯ f (x m)}`.** The sections of `M̃` over
the intersection of the members of the family `D(f i)` selected by a tuple `x` are `M` localized
away from the product of the selected elements: the intersection *is* the standard open of that
product, and the sections of `M̃` on a standard open are the corresponding localization. -/
def standardCechTermEquiv {m : ℕ} (x : Fin (m + 1) → Fin n) :
    moduleSections M (inter (fun i ↦ basicOpen (f i)) x) ≃ₗ[R]
      AwayLoc (M : Type _) (1 * tupleProd f x) :=
  (moduleSectionsCongr M (interStandardOpen_eq_basicOpen f x)).trans
    (moduleSectionsBasicOpenEquiv M (1 * tupleProd f x))

/-- **The degreewise comparison carries restrictions to the maps of localizations.** The
restriction from the intersection selected by a tuple `y` with its `j`-th entry omitted to the
intersection selected by `y` becomes the canonical map of localizations attached to the
divisibility `Stacks.RingTheory.CechAcyclicity.dvd_face`. -/
theorem standardCechTermEquiv_restrict {m : ℕ} (y : Fin (m + 2) → Fin n) (j : Fin (m + 2))
    (w : moduleSections M (inter (fun i ↦ basicOpen (f i)) fun i ↦ y (j.succAbove i))) :
    standardCechTermEquiv f M y
        (moduleSectionsRestrict M
          (leOfHom (interMap (fun i ↦ basicOpen (f i)) y j.succAbove)) w) =
      resAway (M : Type _) (dvd_face f 1 y j)
        (standardCechTermEquiv f M (fun i ↦ y (j.succAbove i)) w) :=
  moduleSectionsBasicOpenEquiv_congr_restrict M (dvd_face f 1 y j)
    (interStandardOpen_eq_basicOpen f fun i ↦ y (j.succAbove i))
    (interStandardOpen_eq_basicOpen f y) _ w

/-- The degree-`m` comparison map from the Čech complex of the family `D(f i)` to the algebraic
Čech complex of `f`: its component at a tuple `x` is the projection onto the sections over the
corresponding intersection, followed by `Stacks.LocalCohomology.standardCechTermEquiv`. -/
def toStandardCechTerm (m : ℕ) :
    ((cechComplexFunctor fun i ↦ basicOpen (f i)).obj (moduleSectionsPresheaf M)).X m ⟶
      ModuleCat.of R (CechTerm (M : Type _) f 1 m) :=
  ModuleCat.ofHom (LinearMap.pi fun x ↦
    (standardCechTermEquiv f M x).toLinearMap.comp
      (π (fun i ↦ basicOpen (f i)) (moduleSectionsPresheaf M) m x).hom)

/-- The component of `Stacks.LocalCohomology.toStandardCechTerm` at a tuple. -/
theorem toStandardCechTerm_apply (m : ℕ)
    (z : ((cechComplexFunctor fun i ↦ basicOpen (f i)).obj (moduleSectionsPresheaf M)).X m)
    (x : Fin (m + 1) → Fin n) :
    (toStandardCechTerm f M m).hom z x =
      standardCechTermEquiv f M x
        ((π (fun i ↦ basicOpen (f i)) (moduleSectionsPresheaf M) m x).hom z) :=
  rfl

/-- The degree-`m` comparison map from the algebraic Čech complex of `f` to the Čech complex of
the family `D(f i)`, inverse to `Stacks.LocalCohomology.toStandardCechTerm`. -/
def ofStandardCechTerm (m : ℕ) :
    ModuleCat.of R (CechTerm (M : Type _) f 1 m) ⟶
      ((cechComplexFunctor fun i ↦ basicOpen (f i)).obj (moduleSectionsPresheaf M)).X m :=
  lift (fun i ↦ basicOpen (f i)) (moduleSectionsPresheaf M) fun x ↦
    ModuleCat.ofHom ((standardCechTermEquiv f M x).symm.toLinearMap.comp
      (LinearMap.proj (R := R) (φ := fun x ↦ AwayLoc (M : Type _) (1 * tupleProd f x)) x))

/-- Applying both sides of an equation `g ≫ h = k` of module maps to an element. -/
private theorem hom_apply_of_comp_eq {A B C : ModuleCat.{max u v} R} {g : A ⟶ B} {h : B ⟶ C}
    {k : A ⟶ C} (e : g ≫ h = k) (z : A) : h.hom (g.hom z) = k.hom z := by
  subst e
  rfl

/-- The component of `Stacks.LocalCohomology.ofStandardCechTerm` at a tuple, on elements. -/
theorem π_ofStandardCechTerm (m : ℕ) (s : CechTerm (M : Type _) f 1 m)
    (x : Fin (m + 1) → Fin n) :
    (π (fun i ↦ basicOpen (f i)) (moduleSectionsPresheaf M) m x).hom
        ((ofStandardCechTerm f M m).hom s) =
      (standardCechTermEquiv f M x).symm (s x) := by
  exact hom_apply_of_comp_eq (A := ModuleCat.of R (CechTerm (M : Type _) f 1 m))
    (lift_comp_π (fun i ↦ basicOpen (f i)) (moduleSectionsPresheaf M) _ x) s

/-- `Stacks.LocalCohomology.toStandardCechTerm` is a retraction of
`Stacks.LocalCohomology.ofStandardCechTerm`. -/
theorem ofStandardCechTerm_comp_toStandardCechTerm (m : ℕ) :
    ofStandardCechTerm f M m ≫ toStandardCechTerm f M m = 𝟙 _ :=
  ModuleCat.hom_ext (LinearMap.ext fun s ↦ funext fun x ↦ by
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, toStandardCechTerm_apply,
      π_ofStandardCechTerm, LinearEquiv.apply_symm_apply]
    rfl)

/-- `Stacks.LocalCohomology.ofStandardCechTerm` is a retraction of
`Stacks.LocalCohomology.toStandardCechTerm`. -/
theorem toStandardCechTerm_comp_ofStandardCechTerm (m : ℕ) :
    toStandardCechTerm f M m ≫ ofStandardCechTerm f M m = 𝟙 _ :=
  hom_ext (fun i ↦ basicOpen (f i)) (moduleSectionsPresheaf M) fun x ↦ by
    rw [Category.assoc, Category.id_comp]
    refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
    rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
      π_ofStandardCechTerm, toStandardCechTerm_apply]
    exact (standardCechTermEquiv f M x).symm_apply_apply _

/-- **The degreewise identification of the two Čech complexes.** The degree-`m` term of the Čech
complex of the family `D(f i)` with coefficients in `M̃` is the degree-`m` term of the algebraic
Čech complex of `f` with coefficients in `M`. -/
def standardCechTermIso (m : ℕ) :
    ((cechComplexFunctor fun i ↦ basicOpen (f i)).obj (moduleSectionsPresheaf M)).X m ≅
      ModuleCat.of R (CechTerm (M : Type _) f 1 m) where
  hom := toStandardCechTerm f M m
  inv := ofStandardCechTerm f M m
  hom_inv_id := toStandardCechTerm_comp_ofStandardCechTerm f M m
  inv_hom_id := ofStandardCechTerm_comp_toStandardCechTerm f M m

/-! ### The comparison of the differentials -/

/-- The component at a tuple `y` of the Čech differential, on elements: the alternating sum of
the restrictions along the face maps of `y`. -/
theorem π_d_apply_eq_sum (m : ℕ)
    (z : ((cechComplexFunctor fun i ↦ basicOpen (f i)).obj (moduleSectionsPresheaf M)).X m)
    (y : Fin (m + 2) → Fin n) :
    (π (fun i ↦ basicOpen (f i)) (moduleSectionsPresheaf M) (m + 1) y).hom
        ((((cechComplexFunctor fun i ↦ basicOpen (f i)).obj
          (moduleSectionsPresheaf M)).d m (m + 1)).hom z) =
      ∑ j : Fin (m + 2), (-1 : ℤ) ^ (j : ℕ) •
        moduleSectionsRestrict M
            (leOfHom (interMap (fun i ↦ basicOpen (f i)) y j.succAbove))
          ((π (fun i ↦ basicOpen (f i)) (moduleSectionsPresheaf M) m
            fun i ↦ y (j.succAbove i)).hom z) := by
  rw [hom_apply_of_comp_eq (d_comp_π (fun i ↦ basicOpen (f i)) (moduleSectionsPresheaf M) m y) z,
    ModuleCat.hom_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [ModuleCat.hom_zsmul, LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  rfl

/-- **The differentials agree.** The degreewise comparison carries the Čech differential of the
family `D(f i)` to the algebraic Čech differential
`Stacks.RingTheory.CechAcyclicity.cechD`: both are alternating sums of restriction maps, and the
summands agree by `Stacks.LocalCohomology.standardCechTermEquiv_restrict`. -/
theorem d_comp_toStandardCechTerm (m : ℕ) :
    ((cechComplexFunctor fun i ↦ basicOpen (f i)).obj (moduleSectionsPresheaf M)).d m (m + 1) ≫
        toStandardCechTerm f M (m + 1) =
      toStandardCechTerm f M m ≫ ModuleCat.ofHom (cechD (M : Type _) f 1 m) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ funext fun y ↦ ?_)
  have hsmul : ∀ (k : ℕ) (w : AwayLoc (M : Type _) (1 * tupleProd f y)),
      ((-1 : ℤ) ^ k) • w = ((-1 : R) ^ k) • w := fun k w ↦ by
    rw [← Int.cast_smul_eq_zsmul R ((-1 : ℤ) ^ k) w]
    norm_num
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
    toStandardCechTerm_apply, π_d_apply_eq_sum, map_sum, ModuleCat.hom_ofHom, cechD_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [map_zsmul, hsmul]
  exact congrArg (fun w ↦ ((-1 : R) ^ (j : ℕ)) • w)
    ((standardCechTermEquiv_restrict f M y j _).trans
      (congrArg (resAway (M : Type _) (dvd_face f 1 y j))
        (toStandardCechTerm_apply f M m z fun i ↦ y (j.succAbove i)).symm))

/-- **The Čech complex of the family of standard opens `D(f i)` with coefficients in `M̃` is the
algebraic Čech complex of `f` with coefficients in `M`.** The terms agree because the
intersection selected by a tuple is the standard open of the product of the selected elements
and the sections of `M̃` on a standard open are the corresponding localization; the differentials
agree because both are the same alternating sum of restriction maps. -/
def standardCechComplexIso :
    (cechComplexFunctor fun i ↦ basicOpen (f i)).obj (moduleSectionsPresheaf M) ≅
      cechCochainComplex (M : Type _) f 1 :=
  HomologicalComplex.Hom.isoOfComponents (standardCechTermIso f M) fun i j hij ↦ by
    obtain rfl : i + 1 = j := hij
    rw [cechCochainComplex_d]
    exact (d_comp_toStandardCechTerm f M i).symm

/-- The degree-`m` component of the forward map of
`Stacks.LocalCohomology.standardCechComplexIso` is `Stacks.LocalCohomology.toStandardCechTerm`. -/
@[simp]
theorem standardCechComplexIso_hom_f (m : ℕ) :
    (standardCechComplexIso f M).hom.f m = toStandardCechTerm f M m :=
  rfl

/-- The degree-`m` component of the inverse map of
`Stacks.LocalCohomology.standardCechComplexIso` is `Stacks.LocalCohomology.ofStandardCechTerm`. -/
@[simp]
theorem standardCechComplexIso_inv_f (m : ℕ) :
    (standardCechComplexIso f M).inv.f m = ofStandardCechTerm f M m :=
  rfl

/-! ### Consequences for Čech cohomology -/

/-- **The Čech cohomology of the family `D(f i)` with coefficients in `M̃` is the cohomology of
the algebraic Čech complex of `f` with coefficients in `M`.** This is
`Stacks.LocalCohomology.standardCechComplexIso` after applying the homology functor. -/
def standardCechHomologyIso (m : ℕ) :
    ((cechComplexFunctor fun i ↦ basicOpen (f i)).obj (moduleSectionsPresheaf M)).homology m ≅
      (cechCochainComplex (M : Type _) f 1).homology m :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{max u v} R) (ComplexShape.up ℕ) m).mapIso
    (standardCechComplexIso f M)

/-- **Positive-degree Čech cohomology of `M̃` vanishes for a standard cover of `Spec R`.** If the
family `f` generates the unit ideal — equivalently, if the standard opens `D(f i)` cover
`Spec R` — then the Čech complex of that family with coefficients in `M̃` has vanishing homology
in every positive degree, because the algebraic Čech complex does. -/
@[ega "III 1.2.4" "special case"]
theorem isZero_homology_standardCech (hf : Ideal.span (Set.range f) = ⊤) (m : ℕ) :
    IsZero (((cechComplexFunctor fun i ↦ basicOpen (f i)).obj
      (moduleSectionsPresheaf M)).homology (m + 1)) :=
  (isZero_homology_cechCochainComplex (M := (M : Type _)) f hf 1 m).of_iso
    (standardCechHomologyIso f M (m + 1))

end Stacks.LocalCohomology

end
