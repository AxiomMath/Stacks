module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryClosedMaps
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryHomotopyCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.ExtLinear
public import StacksFrontier.Algebra.DifferentialGraded.Module.InternalHom

/-!
# The cohomology of a differential graded module, computed explicitly

The cohomology of a right differential graded module `X` over a differential graded algebra
`(A, d)` over a commutative ring `R` is by definition the homology of its underlying cochain
complex of `R`-modules. This file computes it: the degree-`n` cohomology is the kernel of the
differential on the degree-`n` homogeneous component modulo the image of the differential coming
from degree `n - 1`, as an explicit quotient of `R`-modules.

That explicit description is then transported along the data presenting the internal hom
`Hom^•_B(N, P)` of Tag 0FQR, whose degree-`n` component is the degree-`n` homogeneous
right-`B`-linear maps `N → P`. The outcome is that the degree-`n` cohomology of the internal hom
is the degree-`n` cohomology of the Hom complex of the differential graded category of right
differential graded `B`-modules, and that in degree zero this is `Hom_{K(B)}(N, P)` — `R`-linearly,
because the bijection of Tag 09LC between morphisms of the homotopy category and degree-zero
cohomology classes is a map of `R`-modules.

## Main definitions

* `DifferentialGradedModule.gradedCocycles`, `DifferentialGradedModule.gradedCoboundaries` and
  `DifferentialGradedModule.gradedCohomology`: the degree-`n` cocycles, coboundaries and
  cohomology of a differential graded module, as explicit `R`-modules.
* `DGCategory.cocyclesSubmodule`, `DGCategory.boundariesSubmodule` and
  `DGCategory.homCohomology`: the same for the Hom complex of a differential graded category.
* `DifferentialGradedModule.HomModuleData.homologyZeroIso`: the headline identification
  `H^0(Hom^•_B(N, P)) ≅ Hom_{K(B)}(N, P)`.

## Main results

* `DifferentialGradedModule.gradedCohomologyIso`: the homology of the underlying cochain complex
  is the explicit quotient, and `DifferentialGradedModule.homologyπ_gradedCohomologyIso_hom`
  pins that identification down: it sends the homology class of a cycle to its class in the
  quotient.
* `DGCategory.homotopyClassEquiv`: homotopy classes of degree-zero cocycles are degree-zero
  cohomology classes of the Hom complex.
* `DifferentialGradedModule.homotopyCategoryHomLinearEquiv`: the bijection
  `DifferentialGradedModule.homotopyCategoryHomEquiv` is `R`-linear.
* `DifferentialGradedModule.HomModuleData.gradedCohomologyEquiv` and
  `DifferentialGradedModule.HomModuleData.homologyIso`: the transport of the explicit cohomology
  through the presentation of the internal hom.

## Implementation notes

*Why the differential carries its target degree.* `DifferentialGradedModule.gradedDifferential`
goes from degree `i` to degree `i + 1`, so describing the coboundaries in degree `n` would
require identifying `X^{n-1+1}` with `X^n`. `DifferentialGradedModule.gradedDifferentialTo` takes
the target degree and a proof `i + 1 = n` instead, which makes every statement below cast-free;
`DGCategory.dₗ` does the same for a differential graded category, on top of the existing
`DGCategory.d'`.

*Why a left homology datum rather than a chain of isomorphisms.* The underlying cochain complex
is built with `CochainComplex.of`, whose differential is a `dif` on an equality of degrees, so it
is only propositionally equal to `gradedDifferential`. The short complex of three consecutive
degrees is therefore compared with an explicit one (`DifferentialGradedModule.gradedSc`) by an
isomorphism, and Mathlib's explicit left homology datum of a short complex of modules is
transported along it. Going through a left homology datum rather than composing homology
isomorphisms is what makes the compatibility with `homologyπ` available from Mathlib instead of
having to be rebuilt.

*Why the module structure sits on `DGCategory.homCohomology` and not on
`DGCategory.HomotopyClass`.* `DGCategory.HomotopyClass` is a quotient by a setoid, not by a
submodule, so it carries no `R`-module structure; `DGCategory.homCohomology` is the same quotient
presented as a quotient of modules and does. The two are identified by
`DGCategory.homotopyClassEquiv`, and the `R`-linearity of the comparison with the homotopy
category is recorded against `homCohomology`. No new instance is placed on `HomotopyClass` or on
`DGCategory.Cocycle`: an instance on either would have to be found by instance search through a
semireducible definition, which is below the transparency instance search runs at.

*Degrees other than zero.* Only degree zero is identified with `Hom_{K(B)}(N, P)`; the degree-`n`
statement is obtained by shifting the target, since
`DifferentialGradedModule.shiftHomModuleIso` identifies `Hom^•_B(N, P)[k]` with
`Hom^•_B(N, P[k])` with no intervening sign.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
* [Stacks Project, Tag 09JI](https://stacks.math.columbia.edu/tag/09JI)
* [Stacks Project, Tag 0FQR](https://stacks.math.columbia.edu/tag/0FQR)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}

/-! ### Cocycles, coboundaries and cohomology of a differential graded module -/

/-- The differential of a differential graded module, as a map from the homogeneous component
of degree `i` to that of a prescribed degree `n` with `i + 1 = n`. -/
def gradedDifferentialTo (X : DifferentialGradedModule A) {i n : ℤ} (h : i + 1 = n) :
    X.grading i →ₗ[R] X.grading n where
  toFun x := ⟨X.d x, h ▸ X.d_mem i x x.2⟩
  map_add' x y := Subtype.ext (X.d.map_add (x : X.M) (y : X.M))
  map_smul' r x := Subtype.ext (X.d.map_smul r (x : X.M))

/-- The differential into a prescribed degree is the differential of the module. -/
@[simp] theorem gradedDifferentialTo_apply (X : DifferentialGradedModule A) {i n : ℤ}
    (h : i + 1 = n) (x : X.grading i) : (X.gradedDifferentialTo h x : X.M) = X.d x := rfl

/-- The degree-`n` cocycles of a differential graded module: the kernel of its differential on
the homogeneous component of degree `n`. -/
def gradedCocycles (X : DifferentialGradedModule A) (n : ℤ) : Submodule R (X.grading n) :=
  LinearMap.ker (X.gradedDifferential n)

/-- A homogeneous element of degree `n` is a cocycle exactly when the differential kills it. -/
theorem mem_gradedCocycles {X : DifferentialGradedModule A} {n : ℤ} {x : X.grading n} :
    x ∈ X.gradedCocycles n ↔ X.gradedDifferential n x = 0 := Iff.rfl

/-- The differential from degree `i`, corestricted to the degree-`n` cocycles, for `i + 1 = n`. -/
def gradedToCocycles (X : DifferentialGradedModule A) {i n : ℤ} (h : i + 1 = n) :
    X.grading i →ₗ[R] X.gradedCocycles n :=
  (X.gradedDifferentialTo h).codRestrict (X.gradedCocycles n) fun x =>
    Subtype.ext (LinearMap.congr_fun X.d_comp_d (x : X.M))

/-- The degree-`n` coboundaries, as a submodule of the degree-`n` cocycles: the image of the
differential coming from degree `n - 1`. -/
def gradedCoboundaries (X : DifferentialGradedModule A) (n : ℤ) :
    Submodule R (X.gradedCocycles n) :=
  LinearMap.range (X.gradedToCocycles (i := n - 1) (by omega))

/-- The coboundaries in degree `n` are the image of the differential from any degree `i` with
`i + 1 = n`. -/
theorem gradedCoboundaries_eq_range (X : DifferentialGradedModule A) {i n : ℤ} (h : i + 1 = n) :
    X.gradedCoboundaries n = LinearMap.range (X.gradedToCocycles h) := by
  obtain rfl : i = n - 1 := by omega
  rfl

/-- A degree-`n` cocycle is a coboundary exactly when it is the differential of a homogeneous
element of degree `n - 1`. -/
theorem mem_gradedCoboundaries {X : DifferentialGradedModule A} {n : ℤ}
    (x : X.gradedCocycles n) :
    x ∈ X.gradedCoboundaries n ↔
      ∃ y : X.grading (n - 1), X.d y = ((x : X.grading n) : X.M) := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, by rw [← hy]; rfl⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, Subtype.ext (Subtype.ext hy)⟩

/-- The degree-`n` cohomology of a differential graded module, computed explicitly as the
degree-`n` cocycles modulo the degree-`n` coboundaries. -/
def gradedCohomology (X : DifferentialGradedModule A) (n : ℤ) : ModuleCat.{u} R :=
  ModuleCat.of R (X.gradedCocycles n ⧸ X.gradedCoboundaries n)

/-! ### Comparison with the homology of the underlying cochain complex -/

/-- The differential squares to zero, in the form needed to build the short complex of three
consecutive degrees. -/
theorem gradedDifferential_comp_gradedDifferentialTo (X : DifferentialGradedModule A)
    {i n : ℤ} (h : i + 1 = n) :
    (X.gradedDifferential n).comp (X.gradedDifferentialTo h) = 0 :=
  LinearMap.ext fun x => Subtype.ext (LinearMap.congr_fun X.d_comp_d (x : X.M))

/-- The short complex of `R`-modules formed by the homogeneous components of degrees `i`, `n` and
`n + 1`, for `i + 1 = n`. -/
def gradedSc (X : DifferentialGradedModule A) {i n : ℤ} (h : i + 1 = n) :
    ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (X.gradedDifferentialTo h) (X.gradedDifferential n)
    (X.gradedDifferential_comp_gradedDifferentialTo h)

/-- Mathlib's map into the cycles of the short complex is the differential corestricted to the
cocycles. -/
theorem gradedSc_moduleCatToCycles (X : DifferentialGradedModule A) {i n : ℤ} (h : i + 1 = n) :
    (X.gradedSc h).moduleCatToCycles = X.gradedToCocycles h := rfl

/-- The three consecutive terms of the underlying cochain complex form the short complex
`DifferentialGradedModule.gradedSc`. -/
def gradedScIso (X : DifferentialGradedModule A) {i n : ℤ} (h : i + 1 = n) :
    ((forgetToCochainComplex A).obj X).sc' i n (n + 1) ≅ X.gradedSc h := by
  subst h
  exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
    ((Category.id_comp _).trans
      ((toCochainComplex_d X i).symm.trans (Category.comp_id _).symm))
    ((Category.id_comp _).trans
      ((toCochainComplex_d X (i + 1)).symm.trans (Category.comp_id _).symm))

/-- The explicit left homology datum of the degree-`n` part of the underlying cochain complex:
its cycles are the degree-`n` cocycles and its homology is the degree-`n` cohomology. -/
def gradedLeftHomologyData (X : DifferentialGradedModule A) (n : ℤ) :
    (((forgetToCochainComplex A).obj X).sc' (n - 1) n (n + 1)).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofIso (X.gradedScIso (show n - 1 + 1 = n by omega)).symm
    (X.gradedSc (show n - 1 + 1 = n by omega)).moduleCatLeftHomologyData

/-- The projection of the explicit left homology datum is the quotient map by the
coboundaries. -/
theorem gradedLeftHomologyData_π (X : DifferentialGradedModule A) (n : ℤ) :
    (X.gradedLeftHomologyData n).π = ModuleCat.ofHom (X.gradedCoboundaries n).mkQ := rfl

/-- The degree-`n` cycles of the underlying cochain complex are the degree-`n` cocycles. -/
def gradedCyclesIso (X : DifferentialGradedModule A) (n : ℤ) :
    ((forgetToCochainComplex A).obj X).cycles n ≅ ModuleCat.of R (X.gradedCocycles n) :=
  ((forgetToCochainComplex A).obj X).cyclesIsoSc' (n - 1) n (n + 1)
      (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n) ≪≫
    (X.gradedLeftHomologyData n).cyclesIso

/-- **The degree-`n` cohomology of a differential graded module, explicitly.** The homology of the
underlying cochain complex in degree `n` is the degree-`n` cocycles modulo the degree-`n`
coboundaries. -/
def gradedCohomologyIso (X : DifferentialGradedModule A) (n : ℤ) :
    ((forgetToCochainComplex A).obj X).homology n ≅ X.gradedCohomology n :=
  ((forgetToCochainComplex A).obj X).homologyIsoSc' (n - 1) n (n + 1)
      (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n) ≪≫
    (X.gradedLeftHomologyData n).homologyIso

/-- The identification of cohomology with cocycles modulo coboundaries is the canonical one: it
takes the homology class of a cycle to the class of the corresponding cocycle. -/
theorem homologyπ_gradedCohomologyIso_hom (X : DifferentialGradedModule A) (n : ℤ) :
    ((forgetToCochainComplex A).obj X).homologyπ n ≫ (X.gradedCohomologyIso n).hom =
      (X.gradedCyclesIso n).hom ≫ ModuleCat.ofHom (X.gradedCoboundaries n).mkQ :=
  (HomologicalComplex.π_homologyIsoSc'_hom_assoc _ (n - 1) n (n + 1)
      (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n) _).trans
    ((congrArg (fun z => (((forgetToCochainComplex A).obj X).cyclesIsoSc' (n - 1) n (n + 1)
          (CochainComplex.prev ℤ n) (CochainComplex.next ℤ n)).hom ≫ z)
        (ShortComplex.LeftHomologyData.homologyπ_comp_homologyIso_hom _
          (X.gradedLeftHomologyData n))).trans (Category.assoc _ _ _).symm)

end DifferentialGradedModule

namespace DGCategory

variable {R : Type u} [CommRing R] (A : DGCategory.{v, w, u} R)

/-! ### Cohomology of the Hom complex of a differential graded category -/

/-- The differential of a differential graded category, into a prescribed degree, as an
`R`-linear map. -/
def dₗ {x y : A.Obj} {m n : ℤ} (h : m + 1 = n) : A.Hom x y m →ₗ[R] A.Hom x y n where
  toFun := A.d' h
  map_add' f g := by cases h; exact A.d_add f g
  map_smul' r f := by cases h; exact A.d_smul r f

/-- The degree-`n` cocycles of the Hom complex from `x` to `y`, as an `R`-submodule of the
degree-`n` morphisms. -/
def cocyclesSubmodule (x y : A.Obj) (n : ℤ) : Submodule R (A.Hom x y n) :=
  LinearMap.ker (A.dₗ (show n + 1 = n + 1 from rfl) : A.Hom x y n →ₗ[R] A.Hom x y (n + 1))

/-- A degree-`n` morphism is a cocycle exactly when it is closed. -/
theorem mem_cocyclesSubmodule {x y : A.Obj} {n : ℤ} {f : A.Hom x y n} :
    f ∈ A.cocyclesSubmodule x y n ↔ A.d f = 0 := Iff.rfl

/-- The degree-`i` morphisms, differentiated into the degree-`n` cocycles, for `i + 1 = n`. -/
def toCocycles (x y : A.Obj) {i n : ℤ} (h : i + 1 = n) :
    A.Hom x y i →ₗ[R] A.cocyclesSubmodule x y n :=
  (A.dₗ h).codRestrict _ fun f => by cases h; exact A.d_d f

/-- Differentiating into the cocycles does not change the morphism. -/
@[simp] theorem toCocycles_val (x y : A.Obj) {i n : ℤ} (h : i + 1 = n) (f : A.Hom x y i) :
    (A.toCocycles x y h f : A.Hom x y n) = A.d' h f := rfl

/-- The degree-`n` coboundaries of the Hom complex, as an `R`-submodule of the degree-`n`
cocycles. -/
def boundariesSubmodule (x y : A.Obj) (n : ℤ) : Submodule R (A.cocyclesSubmodule x y n) :=
  LinearMap.range (A.toCocycles x y (show n - 1 + 1 = n by omega))

/-- The coboundaries in degree `n` are the image of the differential from any degree `i` with
`i + 1 = n`. -/
theorem boundariesSubmodule_eq_range (x y : A.Obj) {i n : ℤ} (h : i + 1 = n) :
    A.boundariesSubmodule x y n = LinearMap.range (A.toCocycles x y h) := by
  obtain rfl : i = n - 1 := by omega
  rfl

/-- The degree-`n` cohomology of the Hom complex from `x` to `y`: the degree-`n` cocycles modulo
the degree-`n` coboundaries. -/
def homCohomology (x y : A.Obj) (n : ℤ) : Type v :=
  A.cocyclesSubmodule x y n ⧸ A.boundariesSubmodule x y n

/-- Degree-`n` cohomology classes of the Hom complex form an additive group. -/
instance (x y : A.Obj) (n : ℤ) : AddCommGroup (A.homCohomology x y n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ A.boundariesSubmodule x y n))

/-- Degree-`n` cohomology classes of the Hom complex form a module over the base ring. -/
instance (x y : A.Obj) (n : ℤ) : Module R (A.homCohomology x y n) :=
  inferInstanceAs (Module R (_ ⧸ A.boundariesSubmodule x y n))

/-- The cohomology class of a cocycle. -/
def homCohomologyMk {x y : A.Obj} {n : ℤ} (f : A.cocyclesSubmodule x y n) :
    A.homCohomology x y n :=
  Submodule.Quotient.mk f

/-- Two degree-zero cocycles are homotopic exactly when their difference is a coboundary. -/
theorem homotopic_iff_sub_mem {x y : A.Obj} (f g : A.cocyclesSubmodule x y 0) :
    A.Homotopic f g ↔ f - g ∈ A.boundariesSubmodule x y 0 := by
  rw [A.boundariesSubmodule_eq_range x y (show (-1 : ℤ) + 1 = 0 by omega)]
  exact ⟨fun ⟨h, hh⟩ => ⟨h, Subtype.ext hh.symm⟩,
    fun ⟨h, hh⟩ => ⟨h, (congrArg Subtype.val hh).symm⟩⟩

/-- The homotopy classes of degree-zero cocycles are the degree-zero cohomology classes of the
Hom complex. -/
@[sga "2 V 1.1" "more general"]
def homotopyClassEquiv (x y : A.Obj) : A.HomotopyClass x y ≃ A.homCohomology x y 0 :=
  Quotient.congr (Equiv.refl _) fun f g =>
    (A.homotopic_iff_sub_mem f g).trans (Submodule.quotientRel_def _).symm

/-- The identification of homotopy classes with cohomology classes sends the homotopy class of a
cocycle to its cohomology class. -/
@[simp] theorem homotopyClassEquiv_mk (x y : A.Obj) (f : A.cocyclesSubmodule x y 0) :
    A.homotopyClassEquiv x y (Quotient.mk _ f) = A.homCohomologyMk f := rfl

end DGCategory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]

/-! ### `R`-linearity of the comparison with the homotopy category -/

/-- **The bijection of Tag 09LC is `R`-linear.** Morphisms of the homotopy category of
differential graded `A`-modules are the degree-zero cohomology classes of the differential graded
Hom module, as modules over the base ring. -/
def homotopyCategoryHomLinearEquiv (A : DifferentialGradedAlgebra R)
    (L M : DifferentialGradedModule A) :
    (((toHomotopyCategory A).obj L) ⟶ ((toHomotopyCategory A).obj M)) ≃ₗ[R]
      (dgCategory A).homCohomology L M 0 :=
  { toFun := fun α => (dgCategory A).homotopyClassEquiv L M (homotopyCategoryHomEquiv A L M α)
    invFun := fun c =>
      (homotopyCategoryHomEquiv A L M).symm (((dgCategory A).homotopyClassEquiv L M).symm c)
    left_inv := fun α => by
      simp only [Equiv.symm_apply_apply]
    right_inv := fun c => by
      simp only [Equiv.apply_symm_apply]
    map_add' := by rintro ⟨f⟩ ⟨g⟩; rfl
    map_smul' := by rintro r ⟨f⟩; rfl }

/-- The `R`-linear identification of homotopy-category morphisms with degree-zero cohomology
classes is the bijection of Tag 09LC followed by the identification of homotopy classes with
cohomology classes. -/
@[simp] theorem homotopyCategoryHomLinearEquiv_apply (A : DifferentialGradedAlgebra R)
    (L M : DifferentialGradedModule A)
    (α : ((toHomotopyCategory A).obj L) ⟶ ((toHomotopyCategory A).obj M)) :
    homotopyCategoryHomLinearEquiv A L M α =
      (dgCategory A).homotopyClassEquiv L M (homotopyCategoryHomEquiv A L M α) := rfl

/-! ### The cohomology of the internal hom -/

variable {A B : DifferentialGradedAlgebra R} {N P : DifferentialGradedModule B}
  {L : BimoduleStructure A B N}

namespace HomModuleData

/-- The degree-`n` cocycles of the internal hom are the closed degree-`n` homogeneous maps. -/
theorem map_gradedCocycles (H : HomModuleData A B N P L) (n : ℤ) :
    (H.module.gradedCocycles n).map (H.homogeneousEquiv n).toLinearMap =
      (dgCategory B).cocyclesSubmodule N P n := by
  ext g
  rw [Submodule.mem_map_equiv, DGCategory.mem_cocyclesSubmodule, mem_gradedCocycles]
  constructor
  · intro hg
    have := H.map_d n ((H.homogeneousEquiv n).symm g)
    rw [hg, map_zero, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  · intro hg
    apply (H.homogeneousEquiv (n + 1)).injective
    rwa [H.map_d n, LinearEquiv.apply_symm_apply, map_zero]

/-- The identification of the degree-`n` part of the internal hom with the degree-`n` homogeneous
maps, restricted to cocycles. -/
def cocyclesEquiv (H : HomModuleData A B N P L) (n : ℤ) :
    H.module.gradedCocycles n ≃ₗ[R] (dgCategory B).cocyclesSubmodule N P n :=
  (H.homogeneousEquiv n).ofSubmodules _ _ (H.map_gradedCocycles n)

/-- On cocycles, the identification of the internal hom with homogeneous maps commutes with the
differentials. -/
theorem cocyclesEquiv_comp_gradedToCocycles (H : HomModuleData A B N P L) {i n : ℤ}
    (h : i + 1 = n) :
    (H.cocyclesEquiv n).toLinearMap.comp (H.module.gradedToCocycles h) =
      ((dgCategory B).toCocycles N P h).comp (H.homogeneousEquiv i).toLinearMap := by
  subst h
  exact LinearMap.ext fun x => Subtype.ext (H.map_d i x)

/-- The degree-`n` coboundaries of the internal hom are the degree-`n` coboundaries of the
differential graded category of right differential graded `B`-modules. -/
theorem map_gradedCoboundaries (H : HomModuleData A B N P L) (n : ℤ) :
    (H.module.gradedCoboundaries n).map (H.cocyclesEquiv n).toLinearMap =
      (dgCategory B).boundariesSubmodule N P n := by
  have h : n - 1 + 1 = n := by omega
  calc (H.module.gradedCoboundaries n).map (H.cocyclesEquiv n).toLinearMap
      = LinearMap.range ((H.cocyclesEquiv n).toLinearMap.comp
          (H.module.gradedToCocycles h)) := by
        rw [LinearMap.range_comp, H.module.gradedCoboundaries_eq_range h]
    _ = LinearMap.range (((dgCategory B).toCocycles N P h).comp
          (H.homogeneousEquiv (n - 1)).toLinearMap) := by
        rw [H.cocyclesEquiv_comp_gradedToCocycles h]
    _ = (dgCategory B).boundariesSubmodule N P n := by
        rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
          (dgCategory B).boundariesSubmodule_eq_range N P h]

/-- **The degree-`n` cohomology of the internal hom.** The explicit degree-`n` cohomology of
`Hom^•_B(N, P)` is the degree-`n` cohomology of the Hom complex of the differential graded
category of right differential graded `B`-modules: closed degree-`n` homogeneous maps modulo
coboundaries. -/
def gradedCohomologyEquiv (H : HomModuleData A B N P L) (n : ℤ) :
    (H.module.gradedCocycles n ⧸ H.module.gradedCoboundaries n) ≃ₗ[R]
      (dgCategory B).homCohomology N P n :=
  Submodule.Quotient.equiv _ _ (H.cocyclesEquiv n) (H.map_gradedCoboundaries n)

/-- The degree-`n` cohomology of the underlying cochain complex of the internal hom is the
degree-`n` cohomology of the Hom complex of the differential graded category. -/
def homologyIso (H : HomModuleData A B N P L) (n : ℤ) :
    ((forgetToCochainComplex A).obj H.module).homology n ≅
      ModuleCat.of R ((dgCategory B).homCohomology N P n) :=
  H.module.gradedCohomologyIso n ≪≫ (H.gradedCohomologyEquiv n).toModuleIso

/-- The explicit degree-zero cohomology of `Hom^•_B(N, P)` is the set of homotopy classes of
homogeneous maps, that is, the degree-zero homotopy classes of the differential graded
category. -/
@[sga "2 V 1.1" "more general"]
def gradedCohomologyZeroHomotopyClassEquiv (H : HomModuleData A B N P L) :
    (H.module.gradedCocycles 0 ⧸ H.module.gradedCoboundaries 0) ≃
      (dgCategory B).HomotopyClass N P :=
  (H.gradedCohomologyEquiv 0).toEquiv.trans
    ((dgCategory B).homotopyClassEquiv N P).symm

/-- **Degree-zero cohomology of the internal hom is the homotopy-category Hom.** The explicit
degree-zero cohomology of `Hom^•_B(N, P)` is `Hom_{K(B)}(N, P)`, `R`-linearly. -/
def gradedCohomologyZeroEquiv (H : HomModuleData A B N P L) :
    (H.module.gradedCocycles 0 ⧸ H.module.gradedCoboundaries 0) ≃ₗ[R]
      (((toHomotopyCategory B).obj N) ⟶ ((toHomotopyCategory B).obj P)) :=
  (H.gradedCohomologyEquiv 0).trans (homotopyCategoryHomLinearEquiv B N P).symm

/-- **`H^0_A(Hom^•_B(N, P)) ≅ Hom_{K(B)}(N, P)`.** The degree-zero cohomology of the internal hom,
as a module over the base ring, is the module of morphisms `N → P` in the homotopy category of
right differential graded `B`-modules. -/
def homologyZeroIso (H : HomModuleData A B N P L) :
    ((forgetToCochainComplex A).obj H.module).homology 0 ≅
      ModuleCat.of R (((toHomotopyCategory B).obj N) ⟶ ((toHomotopyCategory B).obj P)) :=
  H.module.gradedCohomologyIso 0 ≪≫ H.gradedCohomologyZeroEquiv.toModuleIso

end HomModuleData

end DifferentialGradedModule

end
