module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.Dimension.Torsion.Finite
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.LinearAlgebra.FreeModule.PID
public import StacksCore.Tactic.StacksAttribute

/-!
# Discriminant groups of integral lattices

The discriminant group of an integral bilinear form on a finite free
`ℤ`-module is the cokernel `M⁺/M` of its Gram map. This file relates the
discriminant group of a lattice to those of a saturated sublattice and of that
sublattice's orthogonal complement, and identifies the torsion of the cokernel
of an adjoint composite with a discriminant group.

## Main definitions

* `LinearMap.BilinForm.DiscriminantGroup`: the discriminant group `M⁺/M`.
* `LinearMap.BilinForm.SubmoduleDiscriminantGroup`: the discriminant group of
  the form restricted to a submodule.
* `LinearMap.BilinForm.OrthogonalSumQuotient`: the quotient of the ambient
  module by a submodule together with its orthogonal complement.

## Main results

* `LinearMap.BilinForm.exists_injective_to_discriminantGroup_left` and
  `LinearMap.BilinForm.exists_injective_to_discriminantGroup_orthogonal`: the
  quotient by a saturated submodule and its orthogonal complement injects into
  the discriminant group of either factor, with cokernel a quotient of the
  discriminant group of the ambient lattice.
* `LinearMap.BilinForm.torsionCokernelEquiv_discriminantGroup_range`: for
  adjoint maps between positive definite lattices with unimodular form on the
  source, the torsion of the cokernel of the composite is the discriminant
  group of the image.

## References

* [Stacks Project, Tag 0C6V](https://stacks.math.columbia.edu/tag/0C6V)
* [Stacks Project, Tag 0C6W](https://stacks.math.columbia.edu/tag/0C6W)
-/

@[expose] public section

namespace LinearMap.BilinForm

/-! ### Discriminant groups and orthogonal complements -/

/-- The discriminant group `M⁺/M` of an integral bilinear module.  Integrally,
this is the cokernel of the Gram map `M → M⁺`. -/
public abbrev DiscriminantGroup {M : Type*} [AddCommGroup M] [module : Module ℤ M]
    (form : LinearMap.BilinForm ℤ M) :=
  Module.Dual ℤ M ⧸ LinearMap.range form

/-- The discriminant group `A⁺/A` of the form restricted to a submodule `A`. -/
public abbrev SubmoduleDiscriminantGroup {M : Type*} [AddCommGroup M]
    [Module ℤ M] (form : LinearMap.BilinForm ℤ M) (A : Submodule ℤ M) :=
  DiscriminantGroup (module := A.module) (form.restrict A)

/-- The quotient of a module by a submodule together with its orthogonal
complement. -/
public abbrev OrthogonalSumQuotient {M : Type*} [AddCommGroup M] [Module ℤ M]
    (form : LinearMap.BilinForm ℤ M) (A : Submodule ℤ M) :=
  M ⧸ (A ⊔ A.orthogonalBilin form)

/-- A positive definite integral bilinear form has injective Gram map. -/
private theorem injective_of_pos {M : Type*} [AddCommGroup M] [Module ℤ M]
    (form : LinearMap.BilinForm ℤ M) (hpos : ∀ x : M, x ≠ 0 → 0 < form x x) :
    Function.Injective form := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  by_contra hx0
  exact (hpos x hx0).ne' (by simpa using LinearMap.congr_fun (LinearMap.mem_ker.mp hx) x)

/-- A finite free `ℤ`-module has the same rank as its dual. -/
private theorem finrank_dual_eq_finrank {M : Type*} [AddCommGroup M] [Module.Free ℤ M]
    [Module.Finite ℤ M] : Module.finrank ℤ (Module.Dual ℤ M) = Module.finrank ℤ M :=
  (Module.Free.chooseBasis ℤ M).toDualEquiv.finrank_eq.symm

private theorem dualRestrict_surjective_of_quotient_torsionFree
    {L : Type*} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (S : Submodule ℤ L) (hS : Module.IsTorsionFree ℤ (L ⧸ S)) :
    Function.Surjective S.dualRestrict := by
  let : Module.IsTorsionFree ℤ (L ⧸ S) := hS
  let : Module.Free ℤ (L ⧸ S) := Module.free_iff_isTorsionFree.mpr inferInstance
  obtain ⟨sec, hsec⟩ := Module.projective_lifting_property S.mkQ LinearMap.id
    S.mkQ_surjective
  let proj : L →ₗ[ℤ] S :=
    ((LinearMap.id : L →ₗ[ℤ] L) - sec.comp S.mkQ).codRestrict S (by
      intro x
      have hz : S.mkQ (((LinearMap.id : L →ₗ[ℤ] L) - sec.comp S.mkQ) x) = 0 := by
        change S.mkQ x - S.mkQ (sec (S.mkQ x)) = 0
        rw [← LinearMap.comp_apply, hsec]
        simp
      simpa only [S.ker_mkQ] using (LinearMap.mem_ker.mpr hz :
        ((LinearMap.id : L →ₗ[ℤ] L) - sec.comp S.mkQ) x ∈ LinearMap.ker S.mkQ))
  intro f
  refine ⟨f.comp proj, ?_⟩
  ext x
  apply congrArg f
  apply Subtype.ext
  change (x : L) - sec (S.mkQ (x : L)) = x
  simp [show S.mkQ (x : L) = 0 by simp]

private theorem quotient_torsionFree_orthogonal
    {L : Type*} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (form : LinearMap.BilinForm ℤ L) (hform_symm : form.IsSymm)
    (A : Submodule ℤ L) :
    Module.IsTorsionFree ℤ (L ⧸ A.orthogonalBilin form) := by
  let f : L →ₗ[ℤ] Module.Dual ℤ A := A.dualRestrict.comp form
  have hker : LinearMap.ker f = A.orthogonalBilin form := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_orthogonalBilin]
    constructor
    · intro hx a ha
      simpa [f, hform_symm.eq] using LinearMap.congr_fun hx ⟨a, ha⟩
    · intro hx
      ext a
      simpa [f, hform_symm.eq] using hx a a.property
  let e : (L ⧸ A.orthogonalBilin form) ≃ₗ[ℤ] LinearMap.range f := by
    rw [← hker]
    exact f.quotKerEquivRange
  exact e.injective.moduleIsTorsionFree e (fun r x ↦ e.map_smul r x)

private theorem orthogonal_orthogonal_eq_of_torsionFree_quotient
    {L : Type*} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (form : LinearMap.BilinForm ℤ L) (hform_symm : form.IsSymm)
    (hform_pos : ∀ x : L, x ≠ 0 → 0 < form x x)
    (A : Submodule ℤ L) (hA : Module.IsTorsionFree ℤ (L ⧸ A)) :
    (A.orthogonalBilin form).orthogonalBilin form = A := by
  have hrange : Module.finrank ℤ (LinearMap.range form) =
      Module.finrank ℤ (Module.Dual ℤ L) := by
    rw [LinearMap.finrank_range_of_inj (injective_of_pos form hform_pos),
      finrank_dual_eq_finrank]
  let : Finite (DiscriminantGroup form) :=
    Submodule.finiteQuotientOfFreeOfRankEq (LinearMap.range form) hrange
  let : Fintype (DiscriminantGroup form) := Fintype.ofFinite _
  let : Module.IsTorsionFree ℤ (L ⧸ A) := hA
  let : Module.Free ℤ (L ⧸ A) := Module.free_iff_isTorsionFree.mpr inferInstance
  apply le_antisymm
  · intro x hx
    by_contra hxa
    have hqx : A.mkQ x ≠ 0 := by simpa using hxa
    obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_ne_zero ℤ hqx
    let φ : Module.Dual ℤ L := ψ.comp A.mkQ
    have hφx : φ x ≠ 0 := hψ
    let n := Nat.card (DiscriminantGroup form)
    have hn : n ≠ 0 := Nat.card_ne_zero.mpr ⟨Nonempty.intro 0, inferInstance⟩
    have hq : n • (Submodule.Quotient.mk φ : DiscriminantGroup form) = 0 := by
      simp [n]
    have hm' : (n : ℤ) • φ ∈ LinearMap.range form := by
      rw [← Submodule.Quotient.mk_eq_zero]
      simpa using hq
    obtain ⟨b, hb⟩ := hm'
    have hborth : b ∈ A.orthogonalBilin form := by
      intro a ha
      have hφa : φ a = 0 := by
        change ψ (A.mkQ a) = 0
        rw [show A.mkQ a = 0 by
          rw [← LinearMap.mem_ker, A.ker_mkQ]
          exact ha, map_zero]
      calc
        form a b = form b a := hform_symm.eq _ _
        _ = ((n : ℤ) • φ) a := LinearMap.congr_fun hb a
        _ = 0 := by simp [hφa]
    exact mul_ne_zero (Int.ofNat_ne_zero.mpr hn) hφx
      (by simpa [hx b hborth] using (LinearMap.congr_fun hb x).symm)
  · exact Submodule.le_orthogonalBilin_orthogonalBilin hform_symm.isRefl

private theorem exists_injective_to_discriminantGroup
    {L : Type*} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (form : LinearMap.BilinForm ℤ L) (hform_symm : form.IsSymm)
    (S : Submodule ℤ L) (hS : Module.IsTorsionFree ℤ (L ⧸ S)) :
    ∃ i : (L ⧸ (S ⊔ S.orthogonalBilin form)) →ₗ[ℤ]
        SubmoduleDiscriminantGroup form S,
      Function.Injective i ∧
        ∃ q : DiscriminantGroup form →ₗ[ℤ]
            (SubmoduleDiscriminantGroup form S ⧸ LinearMap.range i),
          Function.Surjective q := by
  let r : L →ₗ[ℤ] Module.Dual ℤ S := S.dualRestrict.comp form
  let p : L →ₗ[ℤ] SubmoduleDiscriminantGroup form S :=
    (LinearMap.range (form.restrict S)).mkQ.comp r
  have hker : LinearMap.ker p = S ⊔ S.orthogonalBilin form := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_sup]
    constructor
    · intro hx
      change Submodule.Quotient.mk (r x) = 0 at hx
      obtain ⟨s, hs⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
      refine ⟨s, s.property, x - s, ?_, by simp⟩
      intro a ha
      have heq := LinearMap.congr_fun hs ⟨a, ha⟩
      change form a (x - s) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (by simpa [r, hform_symm.eq] using heq.symm)
    · rintro ⟨s, hs, b, hb, rfl⟩
      change Submodule.Quotient.mk (r (s + b)) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      refine ⟨⟨s, hs⟩, ?_⟩
      ext a
      change form s a = form (s + b) a
      simp only [map_add, LinearMap.add_apply]
      rw [show form b a = 0 from (hform_symm.eq b a).trans (hb a a.property), add_zero]
  let i := (S ⊔ S.orthogonalBilin form).liftQ p hker.ge
  refine ⟨i, ?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ hker.ge hker.le
  · let q := (LinearMap.range form).mapQ (LinearMap.range i)
      (show Module.Dual ℤ L →ₗ[ℤ] SubmoduleDiscriminantGroup form S from
        (LinearMap.range (form.restrict S)).mkQ.comp S.dualRestrict) (by
        rintro _ ⟨x, rfl⟩
        change _ ∈ LinearMap.range i
        refine ⟨(S ⊔ S.orthogonalBilin form).mkQ x, ?_⟩
        simp [i, p, r])
    refine ⟨q, fun y ↦ ?_⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ f
    obtain ⟨g, rfl⟩ := dualRestrict_surjective_of_quotient_torsionFree S hS f
    exact ⟨Submodule.Quotient.mk g, by simp [q, Submodule.mapQ_apply]⟩

/-- **Stacks Project, Tag 0C6V (left-hand map).**  The quotient by a saturated
submodule and its orthogonal complement injects into the discriminant group of
the submodule.  The cokernel of this injection is a quotient of the
discriminant group of the ambient lattice. -/
@[stacks 0C6V "the map to the discriminant group of A"]
public theorem exists_injective_to_discriminantGroup_left
    {L : Type*} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (form : LinearMap.BilinForm ℤ L) (hform_symm : form.IsSymm)
    (A : Submodule ℤ L) (hA : Module.IsTorsionFree ℤ (L ⧸ A)) :
    ∃ i : OrthogonalSumQuotient form A →ₗ[ℤ]
        SubmoduleDiscriminantGroup form A,
      Function.Injective i ∧
        ∃ q : DiscriminantGroup form →ₗ[ℤ]
            (SubmoduleDiscriminantGroup form A ⧸ LinearMap.range i),
          Function.Surjective q :=
  exists_injective_to_discriminantGroup form hform_symm A hA

/-- **Stacks Project, Tag 0C6V (right-hand map).**  The quotient by a saturated
submodule and its orthogonal complement injects into the discriminant group of
the orthogonal complement.  The cokernel of this injection is a quotient of
the discriminant group of the ambient lattice. -/
@[stacks 0C6V "the map to the discriminant group of B"]
public theorem exists_injective_to_discriminantGroup_orthogonal
    {L : Type*} [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L]
    (form : LinearMap.BilinForm ℤ L) (hform_symm : form.IsSymm)
    (hform_pos : ∀ x : L, x ≠ 0 → 0 < form x x)
    (A : Submodule ℤ L) (hA : Module.IsTorsionFree ℤ (L ⧸ A)) :
    ∃ i : OrthogonalSumQuotient form A →ₗ[ℤ]
        SubmoduleDiscriminantGroup form (A.orthogonalBilin form),
      Function.Injective i ∧
        ∃ q : DiscriminantGroup form →ₗ[ℤ]
            (SubmoduleDiscriminantGroup form (A.orthogonalBilin form) ⧸
              LinearMap.range i),
          Function.Surjective q := by
  have hsum : A.orthogonalBilin form ⊔
      (A.orthogonalBilin form).orthogonalBilin form = A ⊔ A.orthogonalBilin form := by
    rw [orthogonal_orthogonal_eq_of_torsionFree_quotient form hform_symm hform_pos A hA,
      sup_comm]
  change ∃ i : (L ⧸ (A ⊔ A.orthogonalBilin form)) →ₗ[ℤ]
      SubmoduleDiscriminantGroup form (A.orthogonalBilin form),
    Function.Injective i ∧
      ∃ q : DiscriminantGroup form →ₗ[ℤ]
          (SubmoduleDiscriminantGroup form (A.orthogonalBilin form) ⧸ LinearMap.range i),
        Function.Surjective q
  rw [← hsum]
  exact exists_injective_to_discriminantGroup form hform_symm _
    (quotient_torsionFree_orthogonal form hform_symm A)

/-! ### Torsion in the cokernel of an adjoint composite -/

/-- **Stacks Project, Tag 0C6W.** For a pair of adjoint maps of positive
definite integral lattices, when the form on the source is unimodular, the
torsion in the cokernel of `dStar.comp d` is isomorphic to the discriminant
group of the image lattice. -/
@[stacks 0C6W]
public theorem torsionCokernelEquiv_discriminantGroup_range
    {L₀ L₁ : Type*}
    [AddCommGroup L₀] [Module.Free ℤ L₀] [Module.Finite ℤ L₀]
    [AddCommGroup L₁] [Module.Free ℤ L₁] [Module.Finite ℤ L₁]
    (form₀ : LinearMap.BilinForm ℤ L₀) (form₁ : LinearMap.BilinForm ℤ L₁)
    (hform₀_symm : form₀.IsSymm) (hform₁_symm : form₁.IsSymm)
    (hform₁_pos : ∀ x : L₁, x ≠ 0 → 0 < form₁ x x)
    (d : L₀ →ₗ[ℤ] L₁) (dStar : L₁ →ₗ[ℤ] L₀)
    (hadjoint : LinearMap.IsAdjointPair form₀ form₁ d dStar)
    (hunimodular : Function.Bijective form₀) :
    Nonempty
      (AddCommGroup.torsion (L₀ ⧸ LinearMap.range (dStar.comp d)) ≃ₗ[ℤ]
        SubmoduleDiscriminantGroup form₁ (LinearMap.range d)) := by
  let A : Submodule ℤ L₁ := LinearMap.range d
  let r : L₀ →ₗ[ℤ] A := d.rangeRestrict
  let e₀ : L₀ ≃ₗ[ℤ] Module.Dual ℤ L₀ := LinearEquiv.ofBijective form₀ hunimodular
  let p : Module.Dual ℤ A →ₗ[ℤ] L₀ := e₀.symm.toLinearMap.comp r.dualMap
  let g : A →ₗ[ℤ] Module.Dual ℤ A := form₁.restrict A
  let f : L₀ →ₗ[ℤ] L₀ := dStar.comp d
  have hr : Function.Surjective r := d.surjective_rangeRestrict
  have hp : Function.Injective p :=
    e₀.symm.injective.comp (LinearMap.dualMap_injective_of_surjective hr)
  have hg : Function.Injective g :=
    injective_of_pos _ fun a ha ↦ hform₁_pos a (fun h ↦ ha (Subtype.ext h))
  have hpg : (p.comp g).comp r = f := by
    ext x
    apply e₀.injective
    change e₀ (e₀.symm (r.dualMap (g (r x)))) = e₀ (f x)
    rw [LinearEquiv.apply_symm_apply]
    ext y
    change form₁ (d x) (d y) = form₀ (dStar (d x)) y
    rw [hform₀_symm.eq, hform₁_symm.eq]
    exact hadjoint y (d x)
  have hrange : LinearMap.range (p.comp g) = LinearMap.range f := by
    rw [← hpg, LinearMap.range_comp_of_range_eq_top (p.comp g) (LinearMap.range_eq_top.mpr hr)]
  have hquot_torsion : Module.IsTorsion ℤ (Module.Dual ℤ A ⧸ LinearMap.range g) := by
    rw [← Module.finrank_eq_zero_iff_isTorsion]
    have hs := (LinearMap.range g).finrank_quotient_add_finrank
    rw [LinearMap.finrank_range_of_inj hg, finrank_dual_eq_finrank] at hs
    omega
  let q : (Module.Dual ℤ A ⧸ LinearMap.range g) →ₗ[ℤ] (L₀ ⧸ LinearMap.range f) :=
    (LinearMap.range g).mapQ (LinearMap.range f) p (by
      rw [← hrange]
      rintro _ ⟨x, rfl⟩
      exact ⟨x, rfl⟩)
  have hq_inj : Function.Injective q := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, ← hrange] at hx
      obtain ⟨a, ha⟩ := hx
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, hp (by simpa using ha)⟩
  have hq_torsion (x : Module.Dual ℤ A ⧸ LinearMap.range g) : q x ∈
      AddCommGroup.torsion (L₀ ⧸ LinearMap.range f) := by
    rw [← Submodule.torsion_int]
    change q x ∈ Submodule.torsion ℤ (L₀ ⧸ LinearMap.range f)
    rw [Submodule.mem_torsion_iff]
    obtain ⟨n, hn⟩ := hquot_torsion (x := x)
    exact ⟨n, by simpa using congr_arg q hn⟩
  let qt : (Module.Dual ℤ A ⧸ LinearMap.range g) →ₗ[ℤ]
      AddCommGroup.torsion (L₀ ⧸ LinearMap.range f) := {
    toFun x := ⟨q x, hq_torsion x⟩
    map_add' _ _ := Subtype.ext (q.map_add _ _)
    map_smul' _ _ := Subtype.ext (q.map_smul _ _) }
  have hqt_surj : Function.Surjective qt := by
    intro x
    rcases x with ⟨x, hx⟩
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [← Submodule.torsion_int] at hx
      change Submodule.Quotient.mk x ∈ Submodule.torsion ℤ (L₀ ⧸ LinearMap.range f) at hx
      rw [Submodule.mem_torsion_iff] at hx
      obtain ⟨n, hn⟩ := hx
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hn
      have hnx : n.1 • x ∈ LinearMap.range p := by
        rw [← hrange] at hn
        rcases hn with ⟨a, ha⟩
        exact ⟨g a, ha⟩
      rcases hnx with ⟨a, ha⟩
      have hzero : ∀ y ∈ LinearMap.ker r, form₀ x y = 0 := by
        intro y hy
        have hh := LinearMap.congr_fun (congr_arg e₀ ha) y
        have hmul : n.1 * form₀ x y = 0 := by
          calc
            n.1 * form₀ x y = a (r y) := by
              simpa [p, e₀, LinearMap.dualMap_apply] using hh.symm
            _ = 0 := by rw [show r y = 0 from hy]; simp
        exact (mul_eq_zero.mp hmul).resolve_left
          (mem_nonZeroDivisors_iff_ne_zero.mp n.2)
      have hdual : form₀ x ∈ LinearMap.range r.dualMap := by
        rwa [LinearMap.range_dualMap_eq_dualAnnihilator_ker_of_surjective r hr,
          Submodule.mem_dualAnnihilator]
      rcases hdual with ⟨b, hb⟩
      refine ⟨Submodule.Quotient.mk b, ?_⟩
      apply Subtype.ext
      change q (Submodule.Quotient.mk b) = Submodule.Quotient.mk x
      rw [Submodule.mapQ_apply, Submodule.Quotient.eq]
      simp [show p b = x from e₀.injective (by simpa [p, e₀] using hb)]
  exact ⟨(LinearEquiv.ofBijective qt ⟨fun x y h => hq_inj (congr_arg Subtype.val h),
    hqt_surj⟩).symm⟩

end LinearMap.BilinForm
