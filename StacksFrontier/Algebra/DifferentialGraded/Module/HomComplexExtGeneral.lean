module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import StacksFrontier.Algebra.DGA.DerivedCategory
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryClosedMaps
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomCohomology
public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalAcyclicGeneral
public import StacksFrontier.CategoryTheory.DifferentialGraded.HomComplex
public import StacksCore.Tactic.StacksAttribute

/-! # The cohomology of the differential graded Hom complex is `Ext` in the derived category

Let `(A, d)` be a differential graded algebra over a commutative ring `R`, with the base ring, the
algebra and the modules in three independent universes, and let `L` and `M` be right differential
graded `A`-modules. The differential graded category of Tag 09LC attaches to them the Hom complex

`Hom^•_{(A, d)}(L, M) : ⋯ ⟶ Hom^n(L, M) ⟶ Hom^{n + 1}(L, M) ⟶ ⋯`

of abelian groups, whose degree-`n` term is the group of degree-`n` homogeneous right `A`-linear
maps `L → M`. This file computes its cohomology:

* `H^n(Hom^•_{(A, d)}(L, M)) = Hom_{K(A, d)}(L, M[n])` — Tag 09LC in every degree;
* `H^n(Hom^•_{(A, d)}(L, M)) = Ext^n_{D(A, d)}(L, M)` whenever `L` is orthogonal on the left to the
  acyclic modules, in particular whenever `L` has property (P).

The second statement is the content that Tag 0CS5 and Tag 0BYW together provide — degree-`n`
cohomology of `RHom(L, M)` is `Ext^n_{D(A, d)}(L, M)`, and ordinary differential graded Hom
computes `RHom` out of a module with property (P) — in the one form in which Tag 0CS6 needs it,
and at universes at which those two tags are not available; see the implementation notes.

## Main definitions

* `DifferentialGradedModule.General.homComplex`: the Hom complex `Hom^•_{(A, d)}(L, M)`, as a
  cochain complex of abelian groups.
* `DifferentialGradedModule.General.homOfClosed`: the homomorphism `L ⟶ M[n]` attached to a closed
  degree-`n` homogeneous map, which is Tag 09LC's identification on cocycles.
* `DifferentialGradedModule.General.homComplexHomologyEquiv`: **Tag 09LC in every degree**, the
  identification `H^n(Hom^•_{(A, d)}(L, M)) ≅ Hom_{K(A, d)}(L, M[n])`.
* `DifferentialGradedModule.General.homComplexExtEquiv`: the identification
  `H^n(Hom^•_{(A, d)}(L, M)) ≅ Ext^n_{D(A, d)}(L, M)` at a module orthogonal on the left to the
  acyclic ones.
* `DifferentialGradedModule.General.homComplexExtEquivOfPropertyP`: the same at a module with
  property (P).

## Main results

* `DifferentialGradedModule.General.closedToHomotopy_surjective` and
  `DifferentialGradedModule.General.ker_closedToHomotopy`: a homotopy class of homomorphisms
  `L ⟶ M[n]` is the class of a closed degree-`n` homogeneous map, and two closed maps have the same
  class exactly when they differ by a coboundary.
* `DifferentialGradedModule.General.bijective_q_map_of_leftOrthogonal`: the localization
  `K(A, d) ⥤ D(A, d)` is bijective on the morphisms out of a module orthogonal on the left to the
  acyclic ones.
* `DifferentialGradedModule.General.homComplexHomologyEquiv_mk`: the identification of Tag 09LC
  sends the cohomology class of a closed degree-`n` homogeneous map to the homotopy class of the
  homomorphism `L ⟶ M[n]` it is, which is what pins it down.

## Implementation notes

*Why this is not an instance of Tags 0BYW and 0CS5.* Those two tags are formalized in
`StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomLeftOrthogonal` and
`StacksFrontier.Algebra.DifferentialGraded.Module.DerivedHomExtIso`, as statements about a
`DifferentialGradedModule.DerivedHomData` — a right derived functor of internal hom out of a
bimodule. Both are available only on the diagonal: `R : Type u` together with
`DifferentialGradedAlgebra.{u, u} R` and modules in `Type u`, because they are built over
`DifferentialGradedModule.quasiIsomorphisms'` and
`DifferentialGradedModule.degreeZeroCohomologyOnHomotopy'`, which exist at a single universe only.
An endomorphism differential graded algebra of a complex of sheaves is an algebra over `ℤ` whose
carrier lies in the section universe of the site, so the diagonal is satisfiable there only for
the zero universe.

What is formalized here is not the general statement of those tags but the composite they
produce for `Ext` out of a *module* — the route through the derived functor is replaced by the
direct one, which needs no derived functor and no bimodule at all: Tag 09LC identifies the
cohomology of the Hom complex with the morphism groups of `K(A, d)`, and Tag 09KY's mechanism
turns those into the morphism groups of `D(A, d)` at a left-orthogonal module. Every ingredient of
that route is already universe polymorphic, so no part of the single-universe family has to be
lifted.

*Why the quasi-isomorphisms are the unprimed ones.* `DifferentialGradedModule.quasiIsomorphisms`
of `StacksFrontier.Algebra.DGA.QuasiIsomorphisms` is polymorphic in all three universes and is the
class over which `StacksFrontier.Algebra.DGA.DerivedCategory` builds `D(A, d)`; the primed class of
`StacksFrontier.Algebra.DifferentialGraded.Module.QuasiIsomorphism` is the same formula at equal
universes but is attached to a different pretriangulated structure on `K(A, d)`, and the two
families cannot yet be merged — see the `Naming` section of
`StacksFrontier.Algebra.DGA.QuasiIsomorphisms`. Nothing below touches the primed class.

*Why Tag 09LC is reached in every degree at once.* A closed degree-`n` homogeneous map `L → M` is
the same thing as a homomorphism `L ⟶ M[n]` of differential graded modules, with the same
underlying `R`-linear map, and it is a coboundary exactly when that homomorphism is null-homotopic:
these are `DifferentialGradedModule.homogeneousMapDifferential_eq_zero_iff_exists_hom_shift` and
`DifferentialGradedModule.homotopic_zero_iff_exists_homogeneousMapDifferential`, the two statements
of Tag 09LC that are already stated for an arbitrary degree. So the degree-`n` cohomology of the
Hom complex is read off directly, with no reduction to degree zero and no sign bookkeeping across a
shift of the complex.

*How the cohomology group is presented.* Mathlib's `CategoryTheory.ShortComplex.abHomologyIso`
presents the homology of a short complex of abelian groups as `ker g / range f`, by an explicit
left homology datum; the degree-`n` cohomology of a cochain complex is the homology of the short
complex of degrees `n - 1, n, n + 1`. The identification below is therefore a quotient-group
isomorphism, obtained from `QuotientAddGroup.quotientKerEquivOfSurjective`, and
`DifferentialGradedModule.General.homComplexHomologyEquiv_mk` records what it does on a
cocycle.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
* [Stacks Project, Tag 09KW](https://stacks.math.columbia.edu/tag/09KW)
* [Stacks Project, Tag 09KY](https://stacks.math.columbia.edu/tag/09KY)
* [Stacks Project, Tag 09KM](https://stacks.math.columbia.edu/tag/09KM)
* [Stacks Project, Tag 0BYW](https://stacks.math.columbia.edu/tag/0BYW)
* [Stacks Project, Tag 0CS5](https://stacks.math.columbia.edu/tag/0CS5)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace DGCategory

variable {R : Type u} [CommRing R] (A : DGCategory.{v, w, u} R)

/-- The differential of the Hom complex, applied to a homogeneous morphism: it is the
differential of the differential graded category, transported to the prescribed target degree.

This is `DGCategory.homComplex_d_eq` with the `dite` of the complex shape already resolved and the
resulting morphism of abelian groups already applied, which is the form in which the differential
is used below. -/
theorem homComplex_d_apply (x y : A.Obj) {n m : ℤ} (h : n + 1 = m) (f : A.Hom x y n) :
    ((A.homComplex x y).d n m).hom f = A.d' h f := by
  rw [A.homComplex_d_eq x y n m h]
  rfl

end DGCategory

namespace DifferentialGradedModule.General

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra.{u, v} R)

/-! ### The Hom complex -/

/-- **The differential graded Hom complex `Hom^•_{(A, d)}(L, M)`** (Tag 09LC), at independent
universes for the base ring, the algebra and the modules: the cochain complex of abelian groups
whose degree-`n` term is the group of degree-`n` homogeneous right `A`-linear maps `L → M` and
whose differential is the one of the differential graded category of right differential graded
`A`-modules. -/
abbrev homComplex (L M : DifferentialGradedModule.{u, v, w} A) :
    CochainComplex AddCommGrpCat.{w} ℤ :=
  (dgCategory.{u, v, w} A).homComplex L M

variable (L M : DifferentialGradedModule.{u, v, w} A)

/-- The short complex of the three degrees `n - 1`, `n`, `n + 1` of the Hom complex, whose
homology is the degree-`n` cohomology. -/
abbrev homSc (n : ℤ) : ShortComplex AddCommGrpCat.{w} :=
  (homComplex A L M).sc' (n - 1) n (n + 1)

/-- The degree-`n` term of the short complex of three degrees is the group of degree-`n`
homogeneous maps.

The two are equal by definition, but not syntactically; naming the identification keeps every
statement below about `↥(HomogeneousMap A L M n)` rather than about an unreduced projection of the
short complex, which is what lets the rewrites fire. -/
def scX₂ (n : ℤ) : ↥((homSc A L M n).X₂) ≃+ ↥(HomogeneousMap A L M n) :=
  AddEquiv.refl _

/-- The degree-`n - 1` term of the short complex of three degrees is the group of degree-`n - 1`
homogeneous maps; see `DifferentialGradedModule.General.scX₂`. -/
def scX₁ (n : ℤ) : ↥((homSc A L M n).X₁) ≃+ ↥(HomogeneousMap A L M (n - 1)) :=
  AddEquiv.refl _

/-- The differential of the differential graded category of differential graded modules, read on
underlying `R`-linear maps: transporting it to a prescribed target degree does not change it.

The transported morphism is passed in as a homogeneous map of the target degree together with the
equation identifying it, rather than written out with the transport: the transport is an `Eq.mpr`
along the degrees, and no rewrite can be set up against the underlying linear map of such a term,
whereas the equation can be discharged by the degrees being substituted. -/
theorem dgCategory_d'_val {m : ℤ} (f : ↥(HomogeneousMap A L M m)) {n : ℤ} (h : m + 1 = n) :
    ∀ g : ↥(HomogeneousMap A L M n), (dgCategory.{u, v, w} A).d' h f = g →
      (g : L.M →ₗ[R] M.M) =
        ((homogeneousMapDifferential A f : ↥(HomogeneousMap A L M (m + 1))) :
          L.M →ₗ[R] M.M) := by
  subst h
  rintro g rfl
  rfl

/-- A degree-`n` homogeneous map is killed by the differential of the short complex exactly when
it is closed for the differential of the differential graded category. -/
theorem homSc_g_eq_zero_iff (n : ℤ) (f : ↥((homSc A L M n).X₂)) :
    (homSc A L M n).g.hom f = 0 ↔ homogeneousMapDifferential A (scX₂ A L M n f) = 0 := by
  change ((homComplex A L M).d n (n + 1)).hom f = 0 ↔ _
  rw [(dgCategory.{u, v, w} A).homComplex_d_apply L M (show n + 1 = n + 1 from rfl) f]
  rfl

/-- The differential of the short complex coming from degree `n - 1`, read on underlying
`R`-linear maps. -/
theorem homSc_f_val (n : ℤ) (g : ↥((homSc A L M n).X₁)) :
    ((scX₂ A L M n ((homSc A L M n).f.hom g) : L.M →ₗ[R] M.M)) =
      ((homogeneousMapDifferential A (scX₁ A L M n g) :
        ↥(HomogeneousMap A L M (n - 1 + 1))) : L.M →ₗ[R] M.M) := by
  have h : n - 1 + 1 = n := by omega
  exact dgCategory_d'_val A L M (scX₁ A L M n g) h _
    ((dgCategory.{u, v, w} A).homComplex_d_apply L M h (scX₁ A L M n g)).symm

/-! ### Closed homogeneous maps and homomorphisms into the shift -/

/-- **The homomorphism `L ⟶ M[n]` attached to a closed degree-`n` homogeneous map** (Tag 09LC):
the same underlying `R`-linear map, read as a homomorphism of differential graded modules into the
`n`-th shift of the target. -/
def homOfClosed {n : ℤ} (f : ↥(HomogeneousMap A L M n))
    (hf : homogeneousMapDifferential A f = 0) : Hom L (shift M n) :=
  ((homogeneousMapDifferential_eq_zero_iff_exists_hom_shift A L M n f).mp hf).choose

/-- The homomorphism attached to a closed degree-`n` homogeneous map has that map as its
underlying `R`-linear map. -/
@[simp] theorem homOfClosed_toFun {n : ℤ} (f : ↥(HomogeneousMap A L M n))
    (hf : homogeneousMapDifferential A f = 0) :
    (homOfClosed A L M f hf).toFun = (f : L.M →ₗ[R] M.M) :=
  ((homogeneousMapDifferential_eq_zero_iff_exists_hom_shift A L M n f).mp hf).choose_spec

/-- A homomorphism into the `n`-th shift of the target is determined by its underlying `R`-linear
map, so it is the one attached to the closed degree-`n` homogeneous map it is. -/
theorem eq_homOfClosed {n : ℤ} (f : ↥(HomogeneousMap A L M n))
    (hf : homogeneousMapDifferential A f = 0) (g : Hom L (shift M n))
    (hg : g.toFun = (f : L.M →ₗ[R] M.M)) : g = homOfClosed A L M f hf :=
  Hom.ext (by rw [hg, homOfClosed_toFun])

/-- The underlying `R`-linear map of a homomorphism `L ⟶ M[n]` is a degree-`n` homogeneous right
`A`-linear map `L → M`. -/
theorem toFun_mem_homogeneousMapSubmodule {n : ℤ} (g : Hom L (shift M n)) :
    g.toFun ∈ homogeneousMapSubmodule A L M n :=
  ⟨fun i x hx => g.map_grading i x hx, fun a x => g.map_smul x a⟩

/-! ### The comparison with the morphisms of the homotopy category -/

/-- **Tag 09LC on cocycles.** The homotopy class of the homomorphism `L ⟶ M[n]` attached to a
closed degree-`n` homogeneous map, as a morphism of the homotopy category. The assignment is
additive because the homomorphism has the homogeneous map as its underlying `R`-linear map. -/
def closedToHomotopy (n : ℤ) :
    ↥(AddCommGrpCat.Hom.hom (homSc A L M n).g).ker →+
      ((toHomotopyCategory A).obj L ⟶ (toHomotopyCategory A).obj (shift M n)) :=
  AddMonoidHom.mk'
    (fun f => (toHomotopyCategory A).map
      (homOfClosed A L M (scX₂ A L M n f.1) ((homSc_g_eq_zero_iff A L M n f.1).mp f.2)))
    (by
      intro f g
      have hsum : homOfClosed A L M (scX₂ A L M n (f + g).1)
            ((homSc_g_eq_zero_iff A L M n (f + g).1).mp (f + g).2) =
          homOfClosed A L M (scX₂ A L M n f.1)
              ((homSc_g_eq_zero_iff A L M n f.1).mp f.2) +
            homOfClosed A L M (scX₂ A L M n g.1)
              ((homSc_g_eq_zero_iff A L M n g.1).mp g.2) := by
        refine (eq_homOfClosed A L M _ _ _ ?_).symm
        change (homOfClosed A L M (scX₂ A L M n f.1) _).toFun +
          (homOfClosed A L M (scX₂ A L M n g.1) _).toFun = _
        rw [homOfClosed_toFun, homOfClosed_toFun]
        rw [show (f + g).1 = f.1 + g.1 from rfl, map_add]
        rfl
      change (toHomotopyCategory A).map
        (homOfClosed A L M (scX₂ A L M n (f + g).1) _) = _
      rw [hsum]
      rfl)

/-- The comparison of `DifferentialGradedModule.General.closedToHomotopy` is the homotopy class of
the attached homomorphism, by definition. -/
theorem closedToHomotopy_apply (n : ℤ)
    (f : ↥(AddCommGrpCat.Hom.hom (homSc A L M n).g).ker) :
    closedToHomotopy A L M n f =
      (toHomotopyCategory A).map
        (homOfClosed A L M (scX₂ A L M n f.1) ((homSc_g_eq_zero_iff A L M n f.1).mp f.2)) :=
  rfl

/-- **Every homotopy class is the class of a closed homogeneous map.** The homotopy quotient
functor is full, and the underlying `R`-linear map of a homomorphism `L ⟶ M[n]` is a closed
degree-`n` homogeneous map. -/
theorem closedToHomotopy_surjective (n : ℤ) :
    Function.Surjective (closedToHomotopy A L M n) := by
  intro α
  obtain ⟨g, rfl⟩ := (toHomotopyCategory A).map_surjective α
  have hmem : g.toFun ∈ homogeneousMapSubmodule A L M n :=
    toFun_mem_homogeneousMapSubmodule A L M g
  refine ⟨⟨(scX₂ A L M n).symm ⟨g.toFun, hmem⟩, ?_⟩, ?_⟩
  · refine (homSc_g_eq_zero_iff A L M n _).mpr ?_
    rw [AddEquiv.apply_symm_apply]
    exact (homogeneousMapDifferential_eq_zero_iff_exists_hom_shift A L M n ⟨g.toFun, hmem⟩).mpr
      ⟨g, rfl⟩
  · rw [closedToHomotopy_apply]
    refine congrArg (toHomotopyCategory A).map ?_
    refine (eq_homOfClosed A L M _ _ g ?_).symm
    rw [AddEquiv.apply_symm_apply]

/-- **Two closed homogeneous maps have the same homotopy class exactly when they differ by a
coboundary.** The homotopy class of the attached homomorphism vanishes exactly when that
homomorphism is null-homotopic, which is Tag 09LC's description of the coboundaries. -/
theorem ker_closedToHomotopy (n : ℤ) :
    (closedToHomotopy A L M n).ker = (homSc A L M n).abToCycles.range := by
  ext f
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.mem_range]
  rw [closedToHomotopy_apply]
  set f₀ := scX₂ A L M n f.1 with hf₀
  set hcl := (homSc_g_eq_zero_iff A L M n f.1).mp f.2
  have hF := homOfClosed_toFun A L M f₀ hcl
  have hzero : (toHomotopyCategory A).map (homOfClosed A L M f₀ hcl) = 0 ↔
      Homotopic (homOfClosed A L M f₀ hcl) 0 := by
    exact CategoryTheory.Quotient.functor_map_eq_iff (homotopyRel A) _ 0
  rw [hzero, homotopic_zero_iff_exists_homogeneousMapDifferential A f₀ _ hF]
  have hcoe : ∀ y : ↥((homSc A L M n).X₁),
      ((homSc A L M n).abToCycles y : ↥((homSc A L M n).X₂)) =
        (homSc A L M n).f.hom y := fun _ => rfl
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨(scX₁ A L M n).symm g, Subtype.ext ((scX₂ A L M n).injective (Subtype.ext ?_))⟩
    rw [hcoe, homSc_f_val A L M n ((scX₁ A L M n).symm g), AddEquiv.apply_symm_apply, ← hf₀]
    exact hg
  · rintro ⟨g, hg⟩
    refine ⟨scX₁ A L M n g, ?_⟩
    have hg' : scX₂ A L M n ((homSc A L M n).f.hom g) = f₀ := by
      rw [hf₀, ← hcoe]
      exact congrArg (scX₂ A L M n) (congrArg Subtype.val hg)
    rw [← homSc_f_val A L M n g, hg']

/-! ### Tag 09LC in every degree -/

/-- Postcomposition with an isomorphism of the target, as an isomorphism of morphism groups of a
preadditive category. -/
def homAddEquivOfIso {C : Type*} [Category C] [Preadditive C] {X Y Z : C} (e : Y ≅ Z) :
    (X ⟶ Y) ≃+ (X ⟶ Z) where
  toFun f := f ≫ e.hom
  invFun g := g ≫ e.inv
  left_inv f := by simp
  right_inv g := by simp
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _

/-- Two equal targets have the same morphism group, as an isomorphism of groups. -/
def homAddEquivOfEq {C : Type*} [Category C] [Preadditive C] {X Y Z : C} (h : Y = Z) :
    (X ⟶ Y) ≃+ (X ⟶ Z) := by
  subst h
  exact AddEquiv.refl _

/-- The homotopy class of the `n`-th shift of a differential graded module is the `n`-th shift of
its homotopy class. -/
theorem toHomotopyCategory_obj_shift (n : ℤ) :
    (toHomotopyCategory A).obj (shift M n) = ((toHomotopyCategory A).obj M)⟦n⟧ := by
  rw [quotient_obj_shift M n, shiftFunctor_eq_shiftFunctor]
  rfl

/-- The degree-`n` cohomology of the Hom complex, as the closed degree-`n` homogeneous maps modulo
the coboundaries. This is Mathlib's explicit left homology datum of a short complex of abelian
groups, read on the three degrees `n - 1`, `n`, `n + 1` of the Hom complex. -/
def homScHomologyEquiv (n : ℤ) :
    ↥((homComplex A L M).homology n) ≃+
      (↥(AddCommGrpCat.Hom.hom (homSc A L M n).g).ker ⧸
        (homSc A L M n).abToCycles.range) :=
  (((homComplex A L M).homologyIsoSc' (n - 1) n (n + 1) (by simp) (by simp)) ≪≫
    ShortComplex.abHomologyIso _).addCommGroupIsoToAddEquiv

/-- **Tag 09LC in every degree, at independent universes.** The degree-`n` cohomology of the
differential graded Hom complex `Hom^•_{(A, d)}(L, M)` is the group of morphisms `L ⟶ M[n]` of the
homotopy category of right differential graded `A`-modules.

A degree-`n` cohomology class is a closed degree-`n` homogeneous map modulo coboundaries, a closed
degree-`n` homogeneous map is a homomorphism `L ⟶ M[n]`, and a coboundary is a null-homotopic
one. -/
@[stacks 09LC "the cohomology of the Hom complex in every degree, at independent universes",
  sga "4 XVII 2.2.8" "partial"]
def homComplexHomologyEquiv (n : ℤ) :
    ↥((homComplex A L M).homology n) ≃+
      ((toHomotopyCategory A).obj L ⟶ ((toHomotopyCategory A).obj M)⟦n⟧) :=
  (homScHomologyEquiv A L M n).trans
    (((QuotientAddGroup.quotientAddEquivOfEq
            (ker_closedToHomotopy A L M n).symm).trans
          (QuotientAddGroup.quotientKerEquivOfSurjective (closedToHomotopy A L M n)
            (closedToHomotopy_surjective A L M n))).trans
      (homAddEquivOfEq (toHomotopyCategory_obj_shift A M n)))

/-- The identification of Tag 09LC sends the class of a closed degree-`n` homogeneous map to the
homotopy class of the homomorphism `L ⟶ M[n]` it is. -/
theorem homComplexHomologyEquiv_mk (n : ℤ)
    (f : ↥(AddCommGrpCat.Hom.hom (homSc A L M n).g).ker) :
    homComplexHomologyEquiv A L M n ((homScHomologyEquiv A L M n).symm
        (QuotientAddGroup.mk f)) =
      homAddEquivOfEq (toHomotopyCategory_obj_shift A M n) (closedToHomotopy A L M n f) := by
  rw [homComplexHomologyEquiv, AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rfl

/-! ### The morphisms of the derived category out of a left-orthogonal module -/

attribute [local instance 10000] instPretriangulatedHomotopyCategory

/-- **Morphisms out of a left-orthogonal object are not changed by localization** (the mechanism
of Tag 09KY), at independent universes. If `P` is orthogonal on the left to the acyclic
differential graded `A`-modules then the localization functor `K(A, d) ⥤ D(A, d)` is bijective on
the morphisms out of `P`.

The quasi-isomorphisms are the class attached to the acyclic objects by
`DifferentialGradedModule.acyclic_trW_eq_quasiIsomorphisms`, so the localization is one at that
class and Mathlib's orthogonality criterion applies. -/
theorem bijective_q_map_of_leftOrthogonal {P : HomotopyCategory.{u, v, w} A}
    (hP : (acyclic.{u, v, w} A).leftOrthogonal P) (Y : HomotopyCategory.{u, v, w} A) :
    Function.Bijective ((quasiIsomorphisms.{u, v, w} A).Q.map : (P ⟶ Y) → _) := by
  have hloc : (quasiIsomorphisms.{u, v, w} A).Q.IsLocalization
      (acyclic.{u, v, w} A).trW := by
    rw [acyclic_trW_eq_quasiIsomorphisms]
    infer_instance
  exact hP.map_bijective_of_isTriangulated _ Y

/-- The localization functor, read on the morphisms out of a left-orthogonal object, as an
isomorphism of morphism groups. -/
def qMapAddEquiv {P : HomotopyCategory.{u, v, w} A}
    (hP : (acyclic.{u, v, w} A).leftOrthogonal P) (Y : HomotopyCategory.{u, v, w} A) :
    (P ⟶ Y) ≃+ ((quasiIsomorphisms.{u, v, w} A).Q.obj P ⟶
      (quasiIsomorphisms.{u, v, w} A).Q.obj Y) :=
  AddEquiv.ofBijective ((quasiIsomorphisms.{u, v, w} A).Q.mapAddHom)
    (bijective_q_map_of_leftOrthogonal A hP Y)

/-! ### The cohomology of the Hom complex is `Ext` in the derived category -/

/-- **`H^n(Hom^•_{(A, d)}(L, M)) = Ext^n_{D(A, d)}(L, M)`**, at independent universes, for `L`
orthogonal on the left to the acyclic modules.

This is the content that Tag 0CS5 and Tag 0BYW together provide, in the form Tag 0CS6 asks for:
Tag 09LC identifies the cohomology of the Hom complex with the morphism groups of `K(A, d)`
(`DifferentialGradedModule.General.homComplexHomologyEquiv`), and the localization functor is
bijective on the morphisms out of a left-orthogonal object
(`DifferentialGradedModule.General.bijective_q_map_of_leftOrthogonal`), which is the mechanism of
Tag 09KY; the shift is moved across the localization by its commutation with the translation.

With `Ext^n_{D(A, d)}(L, M) = Hom_{D(A, d)}(L, M[n])`, as everywhere in Tag 0CS6, the right-hand
side is that `Ext`-group. -/
@[stacks 0CS5 "the cohomology of ordinary differential graded Hom is Ext out of a module \
orthogonal to the acyclics, at independent universes",
  stacks 0BYW "ordinary differential graded Hom out of a left-orthogonal module computes derived \
Hom, read on cohomology, at independent universes"]
def homComplexExtEquiv (n : ℤ)
    (hL : (acyclic.{u, v, w} A).leftOrthogonal ((toHomotopyCategory A).obj L)) :
    ↥((homComplex A L M).homology n) ≃+
      ((quasiIsomorphisms.{u, v, w} A).Q.obj ((toHomotopyCategory A).obj L) ⟶
        ((quasiIsomorphisms.{u, v, w} A).Q.obj ((toHomotopyCategory A).obj M))⟦n⟧) :=
  (homComplexHomologyEquiv A L M n).trans
    ((qMapAddEquiv A hL (((toHomotopyCategory A).obj M)⟦n⟧)).trans
      (homAddEquivOfIso
        (((quasiIsomorphisms.{u, v, w} A).Q.commShiftIso (A := ℤ) n).app
          ((toHomotopyCategory A).obj M))))

/-- **`H^n(Hom^•_{(A, d)}(L, M)) = Ext^n_{D(A, d)}(L, M)` for `L` with property (P)**, at
independent universes.

A differential graded module with property (P) is orthogonal on the left to the acyclic modules,
which is Tag 09KM at independent universes
(`DifferentialGradedModule.General.leftOrthogonal_acyclic_of_propertyP`), so the previous
identification applies. This is the source's own sufficient condition in Tag 0BYW. -/
@[stacks 0BYW "the property-(P) sufficient condition, read on cohomology, at independent \
universes"]
def homComplexExtEquivOfPropertyP {L M : DifferentialGradedModule.{u, v, max v w} A} (n : ℤ)
    (hL : Nonempty (PropertyPFiltration L)) :
    ↥((homComplex A L M).homology n) ≃+
      ((quasiIsomorphisms.{u, v, max v w} A).Q.obj ((toHomotopyCategory A).obj L) ⟶
        ((quasiIsomorphisms.{u, v, max v w} A).Q.obj ((toHomotopyCategory A).obj M))⟦n⟧) :=
  homComplexExtEquiv A L M n (leftOrthogonal_acyclic_of_propertyP hL.some)

end DifferentialGradedModule.General

end
