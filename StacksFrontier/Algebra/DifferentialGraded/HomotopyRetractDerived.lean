module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleOfTensor
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.OppositeHom
public import StacksFrontier.Algebra.DifferentialGraded.HomotopyRetract
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.EvaluationAtOne

/-!
# A homotopy retraction is invertible in the derived category

Let `φ : B → C` be a homomorphism of differential graded algebras over a commutative ring `R`
which carries a homotopy retraction in the sense of
`DifferentialGradedAlgebra.HomotopyRetract`, and let `ψ : A → B` and `χ : A → C` be
homomorphisms with `φ ∘ ψ = χ`. Then `B` and `C` are left differential graded `A`-algebras and
`φ` is a homomorphism of left differential graded `A`-modules. Its underlying map of cochain
complexes of `R`-modules is a homotopy equivalence — the section and the homotopy of the
retraction are `R`-linear, which is all a cochain-level homotopy equivalence asks for — hence a
quasi-isomorphism, hence an isomorphism in the derived category `D(Aᵒᵖᵖ, d)` of left
differential graded `A`-modules.

Following the convention of the chapter, a left differential graded module is recorded as a
right module over the graded opposite algebra, so the ambient category is that of right modules
over `Aᵒᵖᵖ` and every algebra and homomorphism in sight is replaced by its graded opposite.

## Main definitions

* `DifferentialGradedAlgebra.oppHom`: a homomorphism of differential graded algebras, read on
  the graded opposites.
* `DifferentialGradedAlgebra.HomotopyRetract.opposite`: a homotopy retraction, read on the
  graded opposites.
* `DifferentialGradedModule.cochainMapOfGraded`: a grading-preserving `R`-linear map commuting
  with the differentials, as a map of the underlying cochain complexes. It is not required to
  be linear over the coefficient algebra.
* `DifferentialGradedModule.restrictedRegularHom`: a homomorphism of differential graded
  algebras over a common base, as a homomorphism of the restricted regular modules.
* `DifferentialGradedAlgebra.HomotopyRetract.cochainHomotopyEquiv`: the homotopy equivalence of
  underlying cochain complexes given by a homotopy retraction.

## Main results

* `DifferentialGradedModule.cochainHomotopyOfGraded`: a degree-lowering `R`-linear operator
  satisfying the homotopy identity is a homotopy of the induced cochain maps.
* `DifferentialGradedAlgebra.HomotopyRetract.quasiIso_restrictedRegularHom`: the cochain map
  underlying the restricted regular homomorphism of a homotopy retraction is a
  quasi-isomorphism.
* `DifferentialGradedAlgebra.HomotopyRetract.isIso_derived`: its image in the derived category
  of left differential graded `A`-modules is an isomorphism.

## Implementation notes

The underlying cochain complex of a restricted module is that of the original module by
`DifferentialGradedModule.restrictScalars_toCochainComplex`, and the cochain map underlying a
homomorphism of differential graded modules is assembled from the same data as
`DifferentialGradedModule.cochainMapOfGraded`, so the two presentations agree definitionally.

The identifications between the cochain complex of a differential graded module and the
componentwise constructions on its homogeneous pieces hold by definition but not reducibly so,
which is why `toCochainComplex`, `gradedDifferential` and the two componentwise constructions
are made locally reducible, exactly as in
`StacksFrontier/Algebra/DifferentialGraded/Module/QuasiIsomorphism.lean`.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 09KW](https://stacks.math.columbia.edu/tag/09KW)
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX)
-/

@[expose] public section

open CategoryTheory DifferentialGraded.Bimodule

universe u

namespace DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-- A homomorphism of differential graded algebras, read on the graded opposite algebras. -/
noncomputable abbrev oppHom {A B : DifferentialGradedAlgebra.{u, u} R} (φ : A.Hom B) :
    (oppAlgebra A).Hom (oppAlgebra B) :=
  oppositeHom (opposite R A) (opposite R B) φ

/-- `oppHom φ` is `φ` conjugated by the two canonical identifications between an algebra and
its graded opposite. -/
theorem oppHom_apply {A B : DifferentialGradedAlgebra.{u, u} R} (φ : A.Hom B)
    (a : (oppAlgebra A).A) :
    (oppHom φ).toAlgebraHom a = (opposite R B).equiv.symm (φ.toAlgebraHom ((opposite R A).equiv a))
  := rfl

namespace HomotopyRetract

variable {B C : DifferentialGradedAlgebra.{u, u} R} {φ : B.Hom C}

/-- A homotopy retraction of `φ`, read on the graded opposite algebras: the section and the
homotopy are conjugated by the two canonical identifications of underlying graded modules. -/
noncomputable def opposite (ρ : HomotopyRetract φ) : HomotopyRetract (oppHom φ) where
  sec := (DifferentialGradedAlgebra.opposite R B).equiv.symm.toLinearMap ∘ₗ ρ.sec ∘ₗ
    (DifferentialGradedAlgebra.opposite R C).equiv.toLinearMap
  sec_mem n b hb := by
    rw [(DifferentialGradedAlgebra.opposite R B).mem_grading_iff]
    change (DifferentialGradedAlgebra.opposite R B).equiv
      ((DifferentialGradedAlgebra.opposite R B).equiv.symm
        (ρ.sec ((DifferentialGradedAlgebra.opposite R C).equiv b))) ∈ B.grading n
    rw [LinearEquiv.apply_symm_apply]
    exact ρ.sec_mem n _ (((DifferentialGradedAlgebra.opposite R C).mem_grading_iff n b).mp hb)
  sec_d b := by
    apply (DifferentialGradedAlgebra.opposite R B).equiv.injective
    change (DifferentialGradedAlgebra.opposite R B).equiv
        ((DifferentialGradedAlgebra.opposite R B).equiv.symm
          (ρ.sec ((DifferentialGradedAlgebra.opposite R C).equiv ((oppAlgebra C).d b)))) =
      (DifferentialGradedAlgebra.opposite R B).equiv
        ((oppAlgebra B).d
          ((DifferentialGradedAlgebra.opposite R B).equiv.symm
            (ρ.sec ((DifferentialGradedAlgebra.opposite R C).equiv b))))
    rw [LinearEquiv.apply_symm_apply, (DifferentialGradedAlgebra.opposite R B).map_d,
      LinearEquiv.apply_symm_apply, (DifferentialGradedAlgebra.opposite R C).map_d, ρ.sec_d]
  hom_sec b := by
    rw [oppHom_apply]
    change (DifferentialGradedAlgebra.opposite R C).equiv.symm
      (φ.toAlgebraHom ((DifferentialGradedAlgebra.opposite R B).equiv
        ((DifferentialGradedAlgebra.opposite R B).equiv.symm
          (ρ.sec ((DifferentialGradedAlgebra.opposite R C).equiv b))))) = b
    rw [LinearEquiv.apply_symm_apply, ρ.hom_sec, LinearEquiv.symm_apply_apply]
  htp := (DifferentialGradedAlgebra.opposite R B).equiv.symm.toLinearMap ∘ₗ ρ.htp ∘ₗ
    (DifferentialGradedAlgebra.opposite R B).equiv.toLinearMap
  htp_mem n a ha := by
    rw [(DifferentialGradedAlgebra.opposite R B).mem_grading_iff]
    change (DifferentialGradedAlgebra.opposite R B).equiv
      ((DifferentialGradedAlgebra.opposite R B).equiv.symm
        (ρ.htp ((DifferentialGradedAlgebra.opposite R B).equiv a))) ∈ B.grading (n - 1)
    rw [LinearEquiv.apply_symm_apply]
    exact ρ.htp_mem n _ (((DifferentialGradedAlgebra.opposite R B).mem_grading_iff n a).mp ha)
  htp_eq a := by
    apply (DifferentialGradedAlgebra.opposite R B).equiv.injective
    have key := ρ.htp_eq ((DifferentialGradedAlgebra.opposite R B).equiv a)
    rw [oppHom_apply]
    change (DifferentialGradedAlgebra.opposite R B).equiv
        ((DifferentialGradedAlgebra.opposite R B).equiv.symm
          (ρ.sec ((DifferentialGradedAlgebra.opposite R C).equiv
            ((DifferentialGradedAlgebra.opposite R C).equiv.symm
              (φ.toAlgebraHom ((DifferentialGradedAlgebra.opposite R B).equiv a))))) - a) =
      (DifferentialGradedAlgebra.opposite R B).equiv
        ((oppAlgebra B).d
            ((DifferentialGradedAlgebra.opposite R B).equiv.symm
              (ρ.htp ((DifferentialGradedAlgebra.opposite R B).equiv a))) +
          (DifferentialGradedAlgebra.opposite R B).equiv.symm
            (ρ.htp ((DifferentialGradedAlgebra.opposite R B).equiv ((oppAlgebra B).d a))))
    rw [map_sub, map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply, (DifferentialGradedAlgebra.opposite R B).map_d,
      LinearEquiv.apply_symm_apply, (DifferentialGradedAlgebra.opposite R B).map_d, key]

end HomotopyRetract

end DifferentialGradedAlgebra

namespace DifferentialGradedModule

open DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

section Cochain

variable {A A' : DifferentialGradedAlgebra.{u, u} R}
  {M : DifferentialGradedModule.{u, u, u} A} {N : DifferentialGradedModule.{u, u, u} A'}

/-- A grading-preserving `R`-linear map, restricted to a homogeneous component. -/
def gradedOfLinear (l : M.M →ₗ[R] N.M)
    (hmem : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → l x ∈ N.grading n) (n : ℤ) :
    M.grading n →ₗ[R] N.grading n where
  toFun x := ⟨l x, hmem n x x.property⟩
  map_add' x y := Subtype.ext (l.map_add (x : M.M) (y : M.M))
  map_smul' r x := Subtype.ext (l.map_smul r (x : M.M))

/-- A grading-preserving `R`-linear map commuting with the differentials, as a map of the
underlying cochain complexes. It is not required to be linear over the coefficient algebra, so
this is strictly more general than `DifferentialGradedModule.Hom.toCochainMap`. -/
def cochainMapOfGraded (l : M.M →ₗ[R] N.M)
    (hmem : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → l x ∈ N.grading n)
    (hd : ∀ x, l (M.d x) = N.d (l x)) :
    M.toCochainComplex ⟶ N.toCochainComplex :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (gradedOfLinear l hmem n)) (fun n => by
    simp only [toCochainComplex_d]
    ext x
    exact Subtype.ext (hd (x : M.grading n).val).symm)

/- The underlying cochain complex, its differential and the two componentwise constructions are
made locally reducible: the comparisons below are between a construction on `M.grading n` and
the same construction on `M.toCochainComplex.X n`, equal by definition but not reducibly so. -/
attribute [local implicit_reducible] toCochainComplex gradedDifferential gradedOfLinear
  cochainMapOfGraded

@[simp] theorem cochainMapOfGraded_f (l : M.M →ₗ[R] N.M)
    (hmem : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → l x ∈ N.grading n)
    (hd : ∀ x, l (M.d x) = N.d (l x)) (n : ℤ) :
    (cochainMapOfGraded l hmem hd).f n = ModuleCat.ofHom (gradedOfLinear l hmem n) := rfl

/-- Transporting a homogeneous element along an equality of degrees does not change it. -/
theorem gradingEqToHom_apply {i j : ℤ} (h : i = j) (x : N.grading i) :
    ((eqToHom (congrArg (fun n => ModuleCat.of R (N.grading n)) h)).hom x : N.M) = x := by
  subst j
  rfl

/-- **A degree-lowering `R`-linear operator satisfying the homotopy identity is a homotopy.**
If `l - l' = d ∘ k + k ∘ d` for an `R`-linear `k` lowering the degree by one, then the two
induced cochain maps are homotopic. -/
noncomputable def cochainHomotopyOfGraded (l l' : M.M →ₗ[R] N.M)
    (hmem : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → l x ∈ N.grading n)
    (hd : ∀ x, l (M.d x) = N.d (l x))
    (hmem' : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → l' x ∈ N.grading n)
    (hd' : ∀ x, l' (M.d x) = N.d (l' x))
    (k : M.M →ₗ[R] N.M)
    (hk : ∀ (n : ℤ) (x : M.M), x ∈ M.grading n → k x ∈ N.grading (n - 1))
    (heq : ∀ x, l x - l' x = N.d (k x) + k (M.d x)) :
    _root_.Homotopy (cochainMapOfGraded l hmem hd) (cochainMapOfGraded l' hmem' hd') := by
  let j (n m : ℤ) (hnm : m + 1 = n) : M.grading n →ₗ[R] N.grading m :=
    { toFun := fun x => ⟨k x, by
        have hx := hk n x x.property
        simpa only [show n - 1 = m by omega] using hx⟩
      map_add' := fun x y => Subtype.ext (map_add k (x : M.M) (y : M.M))
      map_smul' := fun r x => Subtype.ext (k.map_smul r (x : M.M)) }
  refine { hom := fun n m => if hnm : m + 1 = n then ModuleCat.ofHom (j n m hnm) else 0
           zero := fun n m hnm => dite_eq_right hnm
           comm := ?_ }
  intro n
  rw [dNext_eq _ (i' := n + 1) (by rfl),
    prevD_eq _ (j' := n - 1) (by change n - 1 + 1 = n; omega)]
  simp only [dite_eq_left (show n - 1 + 1 = n by omega)]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change M.grading n at x
  apply Subtype.ext
  simp only [toCochainComplex, CochainComplex.of.d, sub_add_cancel, dite_true]
  simp only [eqToHom_refl, Category.comp_id, ModuleCat.hom_add, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.add_apply, Submodule.coe_add,
    gradingEqToHom_apply (N := N) (show n - 1 + 1 = n by omega)]
  change l (x : M.M) = k (M.d (x : M.M)) + N.d (k (x : M.M)) + l' (x : M.M)
  rw [sub_eq_iff_eq_add.mp (heq (x : M.M))]
  abel

end Cochain

section Restricted

variable {A B C : DifferentialGradedAlgebra.{u, u} R}

/-- **A homomorphism of differential graded algebras over a common base, as a homomorphism of
the restricted regular left modules.** The hypothesis is that the triangle `A → B → C`
commutes. -/
noncomputable def restrictedRegularHom (ψ : A.Hom B) (χ : A.Hom C) (φ : B.Hom C)
    (hcomp : ∀ a, φ.toAlgebraHom (ψ.toAlgebraHom a) = χ.toAlgebraHom a) :
    restrictScalars (oppHom ψ) (regularModule (oppAlgebra B)) ⟶
      restrictScalars (oppHom χ) (regularModule (oppAlgebra C)) where
  toFun := (oppHom φ).toAlgebraHom.toLinearMap
  map_smul x a := by
    have key : ∀ y : (oppAlgebra B).A,
        (oppHom φ).toAlgebraHom (y * (oppHom ψ).toAlgebraHom a) =
          (oppHom φ).toAlgebraHom y * (oppHom χ).toAlgebraHom a := by
      intro y
      rw [map_mul]
      congr 1
      rw [oppHom_apply, oppHom_apply, oppHom_apply, LinearEquiv.apply_symm_apply, hcomp]
    exact key x
  map_grading n x hx := (oppHom φ).map_grading n x hx
  map_d := LinearMap.ext fun x => (oppHom φ).map_d x

/-- **Composition of restricted regular homomorphisms**, up to an equality of the underlying
algebra homomorphisms. -/
theorem restrictedRegularHom_comp_eq {E : DifferentialGradedAlgebra.{u, u} R} {ψ : A.Hom B}
    {χ : A.Hom C} {ω : A.Hom E} {φ : B.Hom C} {φ' : C.Hom E} {φ₁ : B.Hom E}
    (h₁ : ∀ a, φ.toAlgebraHom (ψ.toAlgebraHom a) = χ.toAlgebraHom a)
    (h₂ : ∀ a, φ'.toAlgebraHom (χ.toAlgebraHom a) = ω.toAlgebraHom a)
    (h₃ : ∀ a, φ₁.toAlgebraHom (ψ.toAlgebraHom a) = ω.toAlgebraHom a)
    (heq : φ'.toAlgebraHom.comp φ.toAlgebraHom = φ₁.toAlgebraHom) :
    restrictedRegularHom ψ χ φ h₁ ≫ restrictedRegularHom χ ω φ' h₂ =
      restrictedRegularHom ψ ω φ₁ h₃ := by
  refine DifferentialGradedModule.Hom.ext ?_
  refine LinearMap.ext fun x => ?_
  show (oppHom φ').toAlgebraHom ((oppHom φ).toAlgebraHom x) = (oppHom φ₁).toAlgebraHom x
  rw [oppHom_apply, oppHom_apply, oppHom_apply, LinearEquiv.apply_symm_apply]
  exact congrArg (DifferentialGradedAlgebra.opposite R E).equiv.symm
    (congrArg (fun φ₂ => φ₂ ((DifferentialGradedAlgebra.opposite R B).equiv x)) heq)

end Restricted

end DifferentialGradedModule

namespace DifferentialGradedAlgebra

namespace HomotopyRetract

open DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra.{u, u} R}
  {φ : B.Hom C}

/-- **The homotopy equivalence of underlying cochain complexes given by a homotopy
retraction.** The section is a cochain map because it preserves the grading and commutes with
the differentials, it is a one-sided inverse on the nose, and the other composite is homotopic
to the identity through the homotopy operator. -/
noncomputable def cochainHomotopyEquiv (ρ : HomotopyRetract φ) :
    HomotopyEquiv (regularModule (oppAlgebra B)).toCochainComplex
      (regularModule (oppAlgebra C)).toCochainComplex := by
  refine
    { hom := cochainMapOfGraded (M := regularModule (oppAlgebra B))
        (N := regularModule (oppAlgebra C)) (oppHom φ).toAlgebraHom.toLinearMap
        (fun n x hx => (oppHom φ).map_grading n x hx) (fun x => (oppHom φ).map_d x)
      inv := cochainMapOfGraded (M := regularModule (oppAlgebra C))
        (N := regularModule (oppAlgebra B)) ρ.opposite.sec
        (fun n x hx => ρ.opposite.sec_mem n x hx) (fun x => ρ.opposite.sec_d x)
      homotopyHomInvId := ?_
      homotopyInvHomId := ?_ }
  · exact cochainHomotopyOfGraded (M := regularModule (oppAlgebra B))
      (N := regularModule (oppAlgebra B))
      (ρ.opposite.sec ∘ₗ (oppHom φ).toAlgebraHom.toLinearMap) LinearMap.id
      (fun n x hx => ρ.opposite.sec_mem n _ ((oppHom φ).map_grading n x hx))
      (fun x => by
        change ρ.opposite.sec ((oppHom φ).toAlgebraHom ((oppAlgebra B).d x)) = _
        rw [(oppHom φ).map_d, ρ.opposite.sec_d]
        rfl)
      (fun _ x _ => by exact ‹x ∈ _›) (fun _ => rfl) ρ.opposite.htp
      (fun n x hx => ρ.opposite.htp_mem n x hx) (fun x => ρ.opposite.htp_eq x)
  · refine _root_.Homotopy.ofEq ?_
    ext n x
    exact Subtype.ext (ρ.opposite.hom_sec
      (x : (regularModule (oppAlgebra C)).grading n).val)

/-- **The cochain map underlying a homotopy retraction, read on the restricted regular left
modules, is a quasi-isomorphism.** -/
theorem quasiIso_restrictedRegularHom (ρ : HomotopyRetract φ) (ψ : A.Hom B) (χ : A.Hom C)
    (hcomp : ∀ a, φ.toAlgebraHom (ψ.toAlgebraHom a) = χ.toAlgebraHom a) :
    QuasiIso ((forgetToCochainComplex (oppAlgebra A)).map
      (restrictedRegularHom ψ χ φ hcomp)) := by
  have hrw : (forgetToCochainComplex (oppAlgebra A)).map (restrictedRegularHom ψ χ φ hcomp) =
      ρ.cochainHomotopyEquiv.hom := rfl
  rw [hrw]
  exact HomotopyEquiv.quasiIso_hom ρ.cochainHomotopyEquiv

/-- **A homotopy retraction becomes an isomorphism in the derived category of left differential
graded modules over a base.** -/
theorem isIso_derived (ρ : HomotopyRetract φ) (ψ : A.Hom B) (χ : A.Hom C)
    (hcomp : ∀ a, φ.toAlgebraHom (ψ.toAlgebraHom a) = χ.toAlgebraHom a) :
    IsIso ((quasiIsomorphisms' (oppAlgebra A)).Q.map
      ((toHomotopyCategory (oppAlgebra A)).map (restrictedRegularHom ψ χ φ hcomp))) :=
  isIso_q_map_toHomotopyCategory_map _ (ρ.quasiIso_restrictedRegularHom ψ χ hcomp)

end HomotopyRetract

end DifferentialGradedAlgebra
