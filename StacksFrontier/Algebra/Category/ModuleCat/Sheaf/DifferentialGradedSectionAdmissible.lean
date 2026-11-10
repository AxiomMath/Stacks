module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedCone
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedSectionModule
public import StacksFrontier.Algebra.DifferentialGraded.Module.Admissible
public import StacksFrontier.Algebra.DifferentialGraded.Module.Bijective
public import StacksFrontier.Algebra.DifferentialGraded.Module.Shift

/-!
# Taking sections preserves admissible short exact sequences and shifts

Let `(A, d)` be a sheaf of differential graded algebras on a site and let `U` be an object of
the site. Taking sections over `U` turns a right differential graded `A`-module `M` into a
differential graded module `M(U)` over the section algebra `A(U)`. This file shows that this
operation is compatible with the two constructions out of which the tower of Tag 0FSH is built:

* an admissible short exact sequence `0 → K → L → M → 0` — one which splits after forgetting the
  differentials — goes to an admissible short exact sequence `0 → K(U) → L(U) → M(U) → 0` of
  differential graded `A(U)`-modules: the splitting maps are homomorphisms of graded modules,
  and they are read on sections degree by degree;
* the degree-one shift `K[1]` has as sections the degree-one shift `K(U)[1]` of the sections.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.totalSectionsMap`: a family of morphisms of sheaves of
  modules, one in each degree, read on the total sections over `U`.
* `SheafOfModules.DifferentialGradedModule.sectionGradedHom`: a homomorphism of the underlying
  graded modules, read on sections over `U`, as a homomorphism of graded `A(U)`-modules.

## Main results

* `SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.sectionMap`: **taking sections
  over `U` carries an admissible short exact sequence of right differential graded `A`-modules to
  an admissible short exact sequence of differential graded `A(U)`-modules.**
* `SheafOfModules.DifferentialGradedModule.nonempty_sectionModule_shifted_iso`: **the sections of
  a degree-one shift are the degree-one shift of the sections**, for every choice of shift.

## Implementation notes

All the identities between maps of sections are checked coordinatewise: the total sections are a
direct sum over the degrees, `SheafOfModules.DifferentialGradedModule.totalSectionsMap` is
`DirectSum.map`, and `DirectSum.map_apply` reduces each identity to the corresponding identity of
morphisms of sheaves of modules in one degree, evaluated at one section.

The shift is a chosen one (`SheafOfModules.DifferentialGradedModule.shiftPackage`), whose
underlying complex is only propositionally the shifted complex; the comparison is therefore made
for an arbitrary `ShiftPackage`, after substituting its complex. The degree bookkeeping is then
the reindexing `n ↦ n + 1` of the direct sum of sections, absorbed by `SheafOfModules.of_heq`.

## References

* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT)
* [Stacks Project, Tag 0FS5](https://stacks.math.columbia.edu/tag/0FS5)
* [Stacks Project, Tag 0FSH](https://stacks.math.columbia.edu/tag/0FSH)
-/

@[expose] public noncomputable section

open CategoryTheory DirectSum

universe t a v u

namespace SheafOfModules

namespace DifferentialGradedModule

attribute [local instance] GradedAlgebra.sectionsGOne GradedAlgebra.sectionsGMul
  GradedAlgebra.sectionsGRing Stacks.uliftIntAlgebra sectionRModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {A : DifferentialGradedAlgebra.{t, a} R}

/-! ### Degreewise families read on total sections -/

section TotalSections

variable {M N P : DifferentialGradedModule.{t, a, a} A} (U : Cᵒᵖ)

/-- **A family of morphisms of sheaves of modules, one in each degree, read on the total sections
over `U`.** -/
def totalSectionsMap (φ : ∀ n, M.complex.X n ⟶ N.complex.X n) :
    M.totalSections U →+ N.totalSections U :=
  DirectSum.map fun n ↦ AddMonoidHom.mk' (fun x ↦ (φ n).val.app U x) fun x y ↦ map_add _ x y

/-- The degree `n` component of `totalSectionsMap U φ x` is the value of `φ n` on sections over
`U` at the degree `n` component of `x`. -/
@[simp] theorem totalSectionsMap_apply (φ : ∀ n, M.complex.X n ⟶ N.complex.X n)
    (x : M.totalSections U) (n : ℤ) :
    totalSectionsMap U φ x n = (φ n).val.app U (x n) :=
  DirectSum.map_apply _ n x

/-- On a total section concentrated in degree `n`, `totalSectionsMap U φ` applies `φ n` over
`U`. -/
@[simp] theorem totalSectionsMap_of (φ : ∀ n, M.complex.X n ⟶ N.complex.X n) (n : ℤ)
    (x : M.sectionsPiece U n) :
    totalSectionsMap U φ (DirectSum.of (M.sectionsPiece U) n x) =
      DirectSum.of (N.sectionsPiece U) n ((φ n).val.app U x) :=
  DirectSum.map_of _ n x

/-- The map of total sections induced by a homomorphism of differential graded modules is the
degreewise family of its components, read on total sections. -/
theorem sectionMap_toFun_apply (f : M ⟶ N) (x : M.totalSections U) :
    (sectionMap f U).toFun x = totalSectionsMap U (fun n ↦ f.toHomologicalComplex.f n) x := rfl

/-- Composing two degreewise families and reading the result on sections is reading them one
after the other. -/
theorem totalSectionsMap_comp (φ : ∀ n, M.complex.X n ⟶ N.complex.X n)
    (ψ : ∀ n, N.complex.X n ⟶ P.complex.X n) (x : M.totalSections U) :
    totalSectionsMap U (fun n ↦ φ n ≫ ψ n) x = totalSectionsMap U ψ (totalSectionsMap U φ x) :=
  DirectSum.ext fun n ↦ by simp only [totalSectionsMap_apply]; rfl

/-- The family of identities is the identity on sections. -/
theorem totalSectionsMap_id (x : M.totalSections U) :
    totalSectionsMap U (fun n ↦ 𝟙 (M.complex.X n)) x = x :=
  DirectSum.ext fun n ↦ by simp only [totalSectionsMap_apply]; rfl

/-- A degreewise sum of families is read on sections as the sum of the two maps. -/
theorem totalSectionsMap_add (φ ψ : ∀ n, M.complex.X n ⟶ N.complex.X n)
    (x : M.totalSections U) :
    totalSectionsMap U (fun n ↦ φ n + ψ n) x =
      totalSectionsMap U φ x + totalSectionsMap U ψ x :=
  DirectSum.ext fun n ↦ by
    simp only [totalSectionsMap_apply, DirectSum.add_apply]; rfl

/-- The zero family is zero on sections. -/
theorem totalSectionsMap_zero (x : M.totalSections U) :
    totalSectionsMap U (fun n ↦ (0 : M.complex.X n ⟶ N.complex.X n)) x = 0 :=
  DirectSum.ext fun n ↦ by
    simp only [totalSectionsMap_apply, DirectSum.zero_apply]; rfl

/-- Two degreewise families which agree degree by degree agree on sections. -/
theorem totalSectionsMap_congr {φ ψ : ∀ n, M.complex.X n ⟶ N.complex.X n} (h : ∀ n, φ n = ψ n)
    (x : M.totalSections U) : totalSectionsMap U φ x = totalSectionsMap U ψ x := by
  rw [show φ = ψ from funext h]

end TotalSections

/-! ### Homomorphisms of graded modules read on sections -/

section Graded

variable {M N : DifferentialGradedModule.{t, a, a} A}

/-- The degreewise components of a homomorphism of the underlying graded modules, as morphisms
between the pieces of the complexes. -/
abbrev gradedComponents
    (φ : GradedModule.ofDifferentialGraded M ⟶ GradedModule.ofDifferentialGraded N) (n : ℤ) :
    M.complex.X n ⟶ N.complex.X n :=
  φ.app n

/-- The degreewise components of a homomorphism of the underlying graded modules, read on total
sections, commute with the right action of the section algebra. -/
theorem totalSectionsMap_act
    (φ : GradedModule.ofDifferentialGraded M ⟶ GradedModule.ofDifferentialGraded N) (U : Cᵒᵖ)
    (x : M.totalSections U) (s : A.toGradedAlgebra.totalSections U) :
    totalSectionsMap U (gradedComponents φ) (M.act U x s) =
      N.act U (totalSectionsMap U (gradedComponents φ) x) s := by
  induction x using DirectSum.induction_on with
  | zero => simp only [map_zero, AddMonoidHom.zero_apply]
  | add x y hx hy => simp only [map_add, AddMonoidHom.add_apply, hx, hy]
  | of n p =>
      induction s using DirectSum.induction_on with
      | zero => simp only [map_zero]
      | add s s' hs hs' => simp only [map_add, hs, hs']
      | of i q =>
          simp only [act_of, actOn_of, totalSectionsMap_of]
          exact congrArg (DirectSum.of (N.sectionsPiece U) (n + i)) (φ.map_smul n i U p q)

/-- **A homomorphism of the underlying graded modules, read on sections over `U`**, as a
homomorphism of graded modules over the section algebra `A(U)`. -/
def sectionGradedHom
    (φ : GradedModule.ofDifferentialGraded M ⟶ GradedModule.ofDifferentialGraded N) (U : Cᵒᵖ) :
    _root_.DifferentialGradedModule.GradedHom (M.sectionModule U) (N.sectionModule U) where
  toFun := uliftIntLinear (totalSectionsMap U (gradedComponents φ))
  map_smul x s := totalSectionsMap_act φ U x s
  map_grading := by
    rintro n x ⟨p, rfl⟩
    change totalSectionsMap U (gradedComponents φ) (DirectSum.of (M.sectionsPiece U) n p) ∈
      Stacks.ExternalGrading.intSummand (N.sectionsPiece U) n
    rw [totalSectionsMap_of]
    exact Stacks.ExternalGrading.of_mem_intSummand _ n _

/-- The underlying map of `sectionGradedHom φ U` is the family of degreewise components of `φ`
read on total sections over `U`. -/
@[simp] theorem sectionGradedHom_toFun
    (φ : GradedModule.ofDifferentialGraded M ⟶ GradedModule.ofDifferentialGraded N) (U : Cᵒᵖ)
    (x : M.totalSections U) :
    (sectionGradedHom φ U).toFun x = totalSectionsMap U (gradedComponents φ) x := rfl

end Graded

/-! ### Admissible short exact sequences -/

section Admissible

variable {K L M : DifferentialGradedModule.{t, a, a} A} {f : K ⟶ L} {g : L ⟶ M}

/-- An identity between homomorphisms of graded modules, read in one degree on one section. -/
theorem GradedModule.Hom.congr_app_apply {X Y : GradedModule.{t, a, a} A.toGradedAlgebra}
    {φ ψ : X ⟶ Y} (h : φ = ψ) (n : ℤ) (U : Cᵒᵖ) (x : (X.piece n).val.obj U) :
    (φ.app n).val.app U x = (ψ.app n).val.app U x := by
  rw [h]

/-- **Taking sections over `U` carries an admissible short exact sequence of right differential
graded `A`-modules to an admissible short exact sequence of differential graded
`A(U)`-modules.** The retraction of `f` and the section of `g`, homomorphisms of graded modules,
are read on sections, and the splitting identities hold coordinatewise. -/
theorem IsAdmissibleShortExact.sectionMap (h : IsAdmissibleShortExact f g) (U : Cᵒᵖ) :
    _root_.DifferentialGradedModule.IsAdmissibleShortExact
      (DifferentialGradedModule.sectionMap f U) (DifferentialGradedModule.sectionMap g U) := by
  obtain ⟨Sp⟩ := h
  have hfr : ∀ x : K.totalSections U,
      totalSectionsMap U (gradedComponents Sp.r)
        (totalSectionsMap U (fun n ↦ f.toHomologicalComplex.f n) x) = x := fun x ↦
    DirectSum.ext fun n ↦ by
      simp only [totalSectionsMap_apply]
      exact GradedModule.Hom.congr_app_apply Sp.f_r n U (x n)
  have hsg : ∀ x : M.totalSections U,
      totalSectionsMap U (fun n ↦ g.toHomologicalComplex.f n)
        (totalSectionsMap U (gradedComponents Sp.s) x) = x := fun x ↦
    DirectSum.ext fun n ↦ by
      simp only [totalSectionsMap_apply]
      exact GradedModule.Hom.congr_app_apply Sp.s_g n U (x n)
  have hid : ∀ x : L.totalSections U,
      totalSectionsMap U (fun n ↦ f.toHomologicalComplex.f n)
          (totalSectionsMap U (gradedComponents Sp.r) x) +
        totalSectionsMap U (gradedComponents Sp.s)
          (totalSectionsMap U (fun n ↦ g.toHomologicalComplex.f n) x) = x := fun x ↦
    DirectSum.ext fun n ↦ by
      simp only [DirectSum.add_apply, totalSectionsMap_apply]
      exact GradedModule.Hom.congr_app_apply Sp.id n U (x n)
  have hfg : ∀ x : K.totalSections U,
      totalSectionsMap U (fun n ↦ g.toHomologicalComplex.f n)
        (totalSectionsMap U (fun n ↦ f.toHomologicalComplex.f n) x) = 0 := fun x ↦
    DirectSum.ext fun n ↦ by
      simp only [DirectSum.zero_apply, totalSectionsMap_apply]
      exact GradedModule.Hom.congr_app_apply Sp.graded_comp_eq_zero n U (x n)
  refine
    { injective := Function.LeftInverse.injective hfr
      surjective := Function.RightInverse.surjective hsg
      exact := ?_
      admissibleMono := ⟨sectionGradedHom Sp.r U, hfr⟩
      admissibleEpi := ⟨sectionGradedHom Sp.s U, hsg⟩ }
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact hfg y
  · intro hx
    refine ⟨totalSectionsMap U (gradedComponents Sp.r) x, ?_⟩
    have h0 : totalSectionsMap U (fun n ↦ g.toHomologicalComplex.f n) x = 0 := hx
    have := hid x
    rwa [h0, map_zero, add_zero] at this

end Admissible

/-! ### Sections of a shift -/

section Shift

/-- An `HEq` between two bilinear actions whose targets are pieces of one family in equal
degrees gives an `HEq` between their values. -/
theorem heq_apply_apply_of_heq {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (T : ℤ → Type a) [∀ k, AddCommGroup (T k)] {k k' : ℤ} (hk : k = k')
    {φ : X →+ Y →+ T k} {ψ : X →+ Y →+ T k'} (h : HEq φ ψ) (x : X) (y : Y) :
    HEq (φ x y) (ψ x y) := by
  subst hk
  rw [eq_of_heq h]

/-- Evaluation of a multiple of a morphism of sheaves of modules by a unit of `ℤ`. -/
theorem units_smul_val_app_apply {X Y : SheafOfModules.{a} R} (c : ℤˣ) (φ : X ⟶ Y) (U : Cᵒᵖ)
    (x : X.val.obj U) : (c • φ).val.app U x = (c : ℤ) • φ.val.app U x := by
  rw [Units.smul_def]
  exact map_zsmul (AddMonoidHom.mk' (fun ψ : X ⟶ Y ↦ ψ.val.app U x) fun _ _ ↦ rfl) (c : ℤ) φ

/-- **The sections of a degree-one shift are the degree-one shift of the sections**, for every
choice `s` of the shift of `K`: the reindexing `n ↦ n + 1` of the direct sum of sections is an
isomorphism of differential graded `A(U)`-modules `K[1](U) ≅ K(U)[1]`. The right action of the
shift is the action of `K` and its differential is minus the differential of `K`, which is the
differential of the shift of a differential graded module. -/
theorem nonempty_sectionModule_shifted_iso (K : DifferentialGradedModule.{t, a, a} A)
    (s : ShiftPackage K) (U : Cᵒᵖ) :
    Nonempty (s.shifted.sectionModule U ≅
      _root_.DifferentialGradedModule.shift (K.sectionModule U) 1) := by
  rcases s with ⟨⟨c, μ, h_assoc, h_one, h_leib⟩, hc, ha⟩
  dsimp only at hc ha ⊢
  subst hc
  let Sh : DifferentialGradedModule.{t, a, a} A :=
    ⟨(CochainComplex.shiftFunctor (SheafOfModules.{a} R) 1).obj K.complex, μ, h_assoc, h_one,
      h_leib⟩
  change Nonempty (Sh.sectionModule U ≅ _)
  -- the reindexing of the direct sum of sections
  let e : Sh.totalSections U →+ K.totalSections U :=
    DirectSum.toAddMonoid fun n ↦ DirectSum.of (K.sectionsPiece U) (n + 1)
  have he : ∀ (n : ℤ) (p : Sh.sectionsPiece U n),
      e (DirectSum.of (Sh.sectionsPiece U) n p) = DirectSum.of (K.sectionsPiece U) (n + 1) p :=
    fun n p ↦ DirectSum.toAddMonoid_of _ n p
  let e' : K.totalSections U →+ Sh.totalSections U :=
    DirectSum.toAddMonoid fun m ↦ (DirectSum.of (Sh.sectionsPiece U) (m - 1)).comp
      (castHom K.complex.X (sub_add_cancel m 1).symm U)
  have he' : ∀ (m : ℤ) (p : K.sectionsPiece U m),
      e' (DirectSum.of (K.sectionsPiece U) m p) =
        DirectSum.of (Sh.sectionsPiece U) (m - 1)
          (castHom K.complex.X (sub_add_cancel m 1).symm U p) :=
    fun m p ↦ DirectSum.toAddMonoid_of _ m p
  have hee' : ∀ x, e' (e x) = x := DFunLike.congr_fun <|
    show e'.comp e = AddMonoidHom.id _ from
    DirectSum.addHom_ext fun n p ↦ by
      rw [AddMonoidHom.comp_apply, he, he']
      exact of_heq (add_sub_cancel_right n 1) (heq_castHom K.complex.X _ U p)
  have he'e : ∀ x, e (e' x) = x := DFunLike.congr_fun <|
    show e.comp e' = AddMonoidHom.id _ from
    DirectSum.addHom_ext fun m p ↦ by
      rw [AddMonoidHom.comp_apply, he', he]
      exact of_heq (sub_add_cancel m 1) (heq_castHom K.complex.X _ U p)
  let φ : _root_.DifferentialGradedModule.Hom (Sh.sectionModule U)
      (_root_.DifferentialGradedModule.shift (K.sectionModule U) 1) :=
    { toFun := uliftIntLinear e
      map_smul := by
        intro x b
        change e (Sh.act U x b) = K.act U (e x) b
        induction x using DirectSum.induction_on with
        | zero =>
            rw [map_zero (Sh.act U), map_zero e, map_zero (K.act U)]
            exact map_zero e
        | add x y hx hy =>
            rw [map_add (Sh.act U), map_add e, map_add (K.act U)]
            change e (Sh.act U x b + Sh.act U y b) = K.act U (e x) b + K.act U (e y) b
            rw [map_add, hx, hy]
        | of n p =>
            induction b using DirectSum.induction_on with
            | zero => simp only [map_zero]
            | add b b' hb hb' => simp only [map_add, hb, hb']
            | of i q =>
                rw [act_of, actOn_of, he, he, act_of, actOn_of]
                exact of_heq (by omega)
                  (heq_apply_apply_of_heq (fun k ↦ (K.complex.X k).val.obj U) (by omega)
                    (ha n i U) p q)
      map_grading := by
        rintro n x ⟨p, rfl⟩
        change e (DirectSum.of (Sh.sectionsPiece U) n p) ∈
          Stacks.ExternalGrading.intSummand (K.sectionsPiece U) (n + 1)
        rw [he]
        exact Stacks.ExternalGrading.of_mem_intSummand _ _ _
      map_d := by
        refine LinearMap.ext fun x ↦ ?_
        change e (Sh.sectionD U x) = ((1 : ℤ).negOnePow : ℤ) • K.sectionD U (e x)
        induction x using DirectSum.induction_on with
        | zero => rw [map_zero, map_zero, map_zero, smul_zero]
        | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]
        | of n p =>
            rw [sectionD_of, he, he, sectionD_of, ← map_zsmul]
            exact congrArg (DirectSum.of (K.sectionsPiece U) (n + 1 + 1))
              (units_smul_val_app_apply ((1 : ℤ).negOnePow) (K.complex.d (n + 1) (n + 1 + 1)) U p) }
  exact ⟨_root_.DifferentialGradedModule.Hom.isoOfBijective φ
    ⟨Function.LeftInverse.injective hee', Function.RightInverse.surjective he'e⟩⟩

end Shift

end DifferentialGradedModule

end SheafOfModules

end
