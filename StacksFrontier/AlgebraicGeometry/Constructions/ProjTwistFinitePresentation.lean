module

public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationFromAffine
public import StacksFrontier.AlgebraicGeometry.RelativeProjFiniteType.Twists
public import StacksFrontier.RingTheory.GradedAlgebra.NoetherianModel
public import StacksFrontier.RingTheory.GradedAlgebra.Proj.TwistFinitePresentation

/-!
# Finite presentation of the twists on a homogeneous spectrum

Let `A` be a commutative ring graded by `𝒜 : ℕ → σ` which is a finitely presented algebra over a
base ring mapping into degree zero. Every twist `𝒪(t)` of the structure sheaf on `Proj 𝒜` is then
a module of finite presentation. This is the absolute case of the assertion of Stacks tag 0D4D.

Finite presentation is local, and the standard opens `D₊(f)` are affine opens of `Proj 𝒜`; over
one of them the sections of the twist are the degree-zero part of the twisted localization. That
module is finite over the degree-zero localization `A₍f₎`
(`AlgebraicGeometry.ProjectiveSpectrum.Proj.finite_twistSections`), but finiteness upgrades to
finite presentation only over a Noetherian ring, and `A₍f₎` need not be one. The source's argument
is therefore the Noetherian model: write `A` as a scalar extension `R ⊗_{R₀} A₀` of a graded
algebra of finite type over a Noetherian subring `R₀ ⊆ R`
(`Stacks.GradedModel.exists_noetherianGradedModel`), note that over the model the degree-zero
localization is of finite type over `R₀` hence Noetherian (Stacks tag 07Z2 (1)) and the twisted
localization is a finite module over it (Stacks tag 07Z2 (2)), hence finitely presented, and
transport that along the two chart-level isomorphisms of
`StacksFrontier.RingTheory.GradedAlgebra.Proj.TwistFinitePresentation`.

The cover used is therefore not all homogeneous elements of positive degree: an arbitrary
homogeneous element need not come from the model. It is the images of the homogeneous elements of
positive degree of `𝒜₀`, which do cover because together with the degree-zero part they generate
`A` as an algebra over `𝒜 0`, by `AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'`.

## Main results

* `Stacks.ProjTwistFinitePresentation.mloc_eq_twistAway`: the degree-zero localization of a twist
  of the regular graded module, as a span of degree-zero fractions inside the localized module,
  is the localized twist of `StacksFrontier.RingTheory.GradedAlgebra.Proj.StandardOpenBaseChange`.
* `Stacks.ProjTwistFinitePresentation.finitePresentation_twistAway_of_noetherian`: over a
  Noetherian base a localized twist of a graded algebra of finite type is finitely presented.
* `Stacks.ProjTwistFinitePresentation.finitePresentation_twistSections`: finite presentation of
  the sections of a twisting sheaf over a standard open, given it for the localized twist.
* `Stacks.ProjTwistFinitePresentation.finitePresentation_twistAway_of_model`: finite presentation
  of the localized twists at the images of the homogeneous elements of a Noetherian model.
* `Stacks.ProjTwistFinitePresentation.isFinitePresentation_twistingSheaf`: every twist on the
  homogeneous spectrum of a finitely presented graded algebra is a module of finite presentation.

## Implementation notes

The localized twist of `Stacks.ProjStandardOpenBaseChange.twistAway` lives in the ordinary
localization `Localization (powers f)`, while the degree-zero localization of a graded module
lives in `LocalizedModule (powers f) A`. For the regular module those two are the same type, with
the same module structure over the degree-zero localization, so `mloc_eq_twistAway` is a plain
equality of submodules: one generating set is contained in the other, the only point being that a
numerator whose prescribed degree is negative is zero.

The twisting sheaf is built from a grading by additive subgroups, while the Noetherian model and
the chart-level base change are stated for gradings by submodules over a base ring. That
transport is `GradedRing.toSubmodules` on the ring and `GradedModule.toSubmodules` on the module,
with `HomogeneousLocalization.Away.toSubmodulesEquiv` identifying the two degree-zero
localizations of the ring; it is carried out at the level of the module of sections over a
standard open, which is what `finitePresentation_twistSections` does, and never on the twisting
sheaf or on the projective spectrum itself.

The base ring of the statement is an arbitrary ring mapping into degree zero rather than `𝒜 0`
itself, because that is the form in which the hypothesis of Stacks tag 0D4D arrives: on an affine
open `U` of the base the graded ring of sections is finitely presented over `Γ(S, U)`, which is
in general smaller than the degree-zero part.

## References

* [Stacks Project, Tag 0D4D](https://stacks.math.columbia.edu/tag/0D4D)
* [Stacks Project, Tag 07Z2](https://stacks.math.columbia.edu/tag/07Z2)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open HomogeneousLocalization Stacks.ProjStandardOpenBaseChange

universe u w

/-- The grading action of natural-number ring degrees on integer module degrees, by addition. -/
local instance twistFinitePresentationDegreeVAdd : VAdd ℕ ℤ where
  vadd n z := (n : ℤ) + z

namespace Stacks.ProjTwistFinitePresentation

section Mloc

variable {R A : Type u} {σ : Type w} [CommRing R] [CommRing A] [Algebra R A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  (𝒜' : ℕ → Submodule R A) [GradedAlgebra 𝒜']
  (ℳ : ℤ → Submodule R A) [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜' ℳ] (t : ℤ)

omit [GradedRing 𝒜] [DirectSum.Decomposition ℳ] [SetLike.GradedSMul 𝒜' ℳ] in
/-- **The degree-zero localization of a twist is the localized twist.** The two spans have, as
generators, exactly the degree-zero fractions whose numerator is homogeneous of the degree the
twist prescribes, so they coincide. -/
public theorem mloc_eq_twistAway
    (hℳ : ∀ (i : ℤ) (x : A), x ∈ ℳ i ↔ x ∈ integerGrading (S := A) 𝒜 (i + t))
    (hmem : ∀ (i : ℕ) (x : A), x ∈ 𝒜' i ↔ x ∈ 𝒜 i) (f : A) (d : ℕ) :
    MLoc 𝒜' ℳ f d = twistAway 𝒜' f d t := by
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
  · rintro z ⟨n, x, hx, rfl⟩
    have hx' : x ∈ integerGrading (S := A) 𝒜 (((n * d : ℕ) : ℤ) + t) := by
      rw [show ((n * d : ℕ) : ℤ) = n • (d : ℤ) from by push_cast; ring]
      exact (hℳ _ x).mp hx
    by_cases hnn : 0 ≤ ((n * d : ℕ) : ℤ) + t
    · have heq : integerGrading (S := A) 𝒜 (((n * d : ℕ) : ℤ) + t) =
          homogeneousSubmodule (S := A) 𝒜 (((n * d : ℕ) : ℤ) + t).toNat := by
        conv_lhs => rw [← Int.toNat_of_nonneg hnn]
        exact integerGrading_natCast 𝒜 _
      rw [heq] at hx'
      exact Submodule.subset_span ⟨n, (((n * d : ℕ) : ℤ) + t).toNat, x,
        Int.toNat_of_nonneg hnn, (hmem _ x).mpr hx', rfl⟩
    · have hz : x = 0 := by
        rw [integerGrading_neg 𝒜 _ (by omega)] at hx'
        simpa using hx'
      subst hz
      change Localization.mk (0 : A) _ ∈ twistAway 𝒜' f d t
      rw [Localization.mk_zero]
      exact Submodule.zero_mem _
  · rintro z ⟨k, e, x, he, hx, rfl⟩
    refine Submodule.subset_span ⟨k, x, (hℳ _ x).mpr ?_, rfl⟩
    rw [show k • (d : ℤ) + t = (e : ℤ) from by rw [he]; push_cast; ring,
      integerGrading_natCast]
    exact (hmem _ x).mp hx

end Mloc

section Model

variable {R₀ A₀ : Type u} [CommRing R₀] [CommRing A₀] [Algebra R₀ A₀]
  (𝒜₀ : ℕ → Submodule R₀ A₀) [GradedAlgebra 𝒜₀]

/-- The degree-zero part of a graded algebra contains the image of its structure map. -/
private theorem algebraMap_mem_zero (r : R₀) : algebraMap R₀ A₀ r ∈ 𝒜₀ 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact (𝒜₀ 0).smul_mem r SetLike.GradedOne.one_mem

/-- **Over a Noetherian base, a localized twist of a graded algebra of finite type is a module of
finite presentation.** It is a finite module by Stacks tag 07Z2 (2), and the degree-zero
localization is Noetherian because it is of finite type over the Noetherian base, by Stacks tag
07Z2 (1). -/
public theorem finitePresentation_twistAway_of_noetherian [IsNoetherianRing R₀]
    [Algebra.FiniteType R₀ A₀] {d : ℕ} {x₀ : A₀} (hx₀ : x₀ ∈ 𝒜₀ d) (hd : 0 < d) (t : ℤ) :
    Module.FinitePresentation (Away 𝒜₀ x₀) (twistAway 𝒜₀ x₀ d t) := by
  have hft := homogeneousLocalization_away_finiteType 𝒜₀ x₀ d hx₀
  have hnoeth : IsNoetherianRing (Away 𝒜₀ x₀) :=
    Algebra.FiniteType.isNoetherianRing R₀ (SLoc 𝒜₀ x₀)
  let _ : SetLike.GradedSMul 𝒜₀ (GradedModule.toSubmodules 𝒜₀ (twistGrading 𝒜₀ t)
      (algebraMap_mem_zero 𝒜₀)) :=
    ⟨fun {_ _ _ _} ha hb =>
      SetLike.GradedSMul.smul_mem (A := 𝒜₀) (B := twistGrading 𝒜₀ t) ha hb⟩
  have hfin : Module.Finite (Away 𝒜₀ x₀)
      (MLoc 𝒜₀ (GradedModule.toSubmodules 𝒜₀ (twistGrading 𝒜₀ t)
        (algebraMap_mem_zero 𝒜₀)) x₀ d) :=
    moduleLocalization_away_finite 𝒜₀ _ x₀ d hx₀ hd
  rw [mloc_eq_twistAway 𝒜₀ 𝒜₀ _ t (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) x₀ d] at hfin
  exact Module.finitePresentation_of_finite _ _

end Model

section Sections

variable {A : Type u} {σ : Type w} {R : Type u} [CommRing A] [CommRing R] [Algebra R A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  (h0 : ∀ r : R, algebraMap R A r ∈ 𝒜 0)

/-- **The sections of a twisting sheaf over a standard open are a module of finite presentation
as soon as the localized twist is.** The sections are the degree-zero part of the twisted
localization, and that is the span of the same degree-zero fractions as the localized twist; the
only transport is the identification of the degree-zero localizations of the `SetLike` grading
and of its promotion to a grading by submodules. -/
public theorem finitePresentation_twistSections {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d)
    (t : ℤ) (h : Module.FinitePresentation (Away (GradedRing.toSubmodules 𝒜 h0) f)
      (twistAway (GradedRing.toSubmodules 𝒜 h0) f d t)) :
    Module.FinitePresentation (Away 𝒜 f)
      ((twistingSheaf 𝒜 t).val.obj (.op (ProjectiveSpectrum.basicOpen 𝒜 f))) := by
  classical
  let 𝒜' := GradedRing.toSubmodules 𝒜 h0
  let ℳ' := GradedModule.toSubmodules 𝒜 (twistGrading 𝒜 t) h0
  have hkey : Module.FinitePresentation (Away 𝒜' f) (MLoc 𝒜' ℳ' f d) := by
    rwa [mloc_eq_twistAway 𝒜 𝒜' ℳ' t (fun _ _ => Iff.rfl) (fun _ _ => Iff.rfl) f d]
  have hmem : ∀ y, y ∈ MLoc 𝒜' ℳ' f d ↔
      y ∈ GradedModuleDegreeZeroLocalization 𝒜 (twistGrading 𝒜 t) f := by
    intro y
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · obtain ⟨n, x, hx, rfl⟩ := (mem_MLoc_iff 𝒜' ℳ' f d hf y).mp hy
      exact Submodule.subset_span ⟨d, n, hf, x, hx, rfl⟩
    · obtain ⟨n, x, hx, he⟩ :=
        degreeZeroFraction_surjective 𝒜 (twistGrading 𝒜 t) hf ⟨y, hy⟩
      have hy' : deg0frac f n x = y := congrArg Subtype.val he
      exact hy' ▸ deg0frac_mem_MLoc 𝒜' ℳ' f d n x hx
  let ε := (HomogeneousLocalization.Away.toSubmodulesEquiv 𝒜 h0 f).symm
  have hval : ∀ r : Away 𝒜' f, (ε r).val = r.val := by
    intro r
    have hr := HomogeneousLocalization.Away.val_toSubmodulesEquiv 𝒜 h0 f (ε r)
    rwa [(HomogeneousLocalization.Away.toSubmodulesEquiv 𝒜 h0 f).apply_symm_apply r, eq_comm] at hr
  have hgdz : Module.FinitePresentation (Away 𝒜 f)
      (GradedModuleDegreeZeroLocalization 𝒜 (twistGrading 𝒜 t) f) :=
    Module.FinitePresentation.of_addEquiv ε
      { toFun := fun x => ⟨x.1, (hmem x.1).mp x.2⟩
        invFun := fun x => ⟨x.1, (hmem x.1).mpr x.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl }
      (fun r x => Subtype.ext (by
        change r.val • (x.1 : MLocAll f (M := A)) = (ε r).val • x.1
        rw [hval])) hkey
  exact Module.FinitePresentation.of_equiv
    (associatedModuleSheafStandardOpenEquiv 𝒜 (twistGrading 𝒜 t) hf hd).symm

end Sections



section ModelImage

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜]
  {R₀ A₀ : Type u} [CommRing R₀] [CommRing A₀] [Algebra R₀ R] [Algebra R₀ A₀]
  (𝒜₀ : ℕ → Submodule R₀ A₀) [GradedAlgebra 𝒜₀]

/-- **The localized twists at the images of the homogeneous elements of a Noetherian model are
modules of finite presentation.** Over the model the twist is a finite module over a Noetherian
ring, hence finitely presented; the conclusion passes to the scalar extension and then across the
identification of the extension with the given graded ring. -/
public theorem finitePresentation_twistAway_of_model [IsNoetherianRing R₀]
    [Algebra.FiniteType R₀ A₀] (e : TensorProduct R₀ R A₀ ≃ₐ[R] A)
    (hgr : ∀ (i : ℕ) (x : TensorProduct R₀ R A₀), x ∈ (𝒜₀ i).baseChange R → e x ∈ 𝒜 i)
    {d : ℕ} (hd : 0 < d) {x₀ : A₀} (hx₀ : x₀ ∈ 𝒜₀ d) (t : ℤ) :
    Module.FinitePresentation (Away 𝒜 (e ((1 : R) ⊗ₜ[R₀] x₀)))
      (twistAway 𝒜 (e ((1 : R) ⊗ₜ[R₀] x₀)) d t) := by
  have hBC := finitePresentation_twistAway_baseChange 𝒜₀ x₀ d
    (standardOpenBaseChange (R' := R) 𝒜₀ x₀ d hx₀ hd) t
    (finitePresentation_twistAway_of_noetherian 𝒜₀ hx₀ hd t)
  have hg : gradedBaseChangeMap (R' := R) 𝒜₀ x₀ ∈ (𝒜₀ d).baseChange R :=
    (gradedBaseChangeMap (R' := R) 𝒜₀).map_mem hx₀
  exact finitePresentation_twistAway_of_ringEquiv 𝒜 (fun i => (𝒜₀ i).baseChange R)
    e.toRingEquiv hgr hg t hBC

end ModelImage

section Absolute

variable {A : Type u} {σ : Type w} {R : Type u} [CommRing A] [CommRing R] [Algebra R A]
  [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  (h0 : ∀ r : R, algebraMap R A r ∈ 𝒜 0)

include h0 in
/-- **Every twist of the structure sheaf on a homogeneous spectrum is a module of finite
presentation** when the graded ring is a finitely presented algebra over a base ring mapping
into degree zero. -/
public theorem isFinitePresentation_twistingSheaf [Algebra.FinitePresentation R A] (t : ℤ) :
    SheafOfModules.IsFinitePresentation.{u, u, u} (twistingSheaf 𝒜 t) := by
  classical
  obtain ⟨R₀, -, hR₀noeth, A₀, hring, halg, 𝒜₀, hgraded, hFTA₀, -, fh, e, -, hetmul⟩ :=
    Stacks.GradedModel.exists_noetherianGradedModel (GradedRing.toSubmodules 𝒜 h0)
  have he1 : ∀ x : A₀, e ((1 : R) ⊗ₜ[R₀] x) = fh x := fun x => by
    rw [hetmul 1 x, one_smul]
  have hgr : ∀ (i : ℕ) (x : TensorProduct R₀ R A₀),
      x ∈ (𝒜₀ i).baseChange R → e x ∈ GradedRing.toSubmodules 𝒜 h0 i := by
    intro i x hx
    rw [Submodule.baseChange_eq_span] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨z, hz, rfl⟩ := hy
        exact (he1 z) ▸ fh.map_mem hz
    | zero => simp
    | add y z _ _ ihy ihz => simpa using add_mem ihy ihz
    | smul r y _ ih => simpa using Submodule.smul_mem _ r ih
  -- the homogeneous elements of positive degree coming from the model
  let F : (Σ m : ℕ+, 𝒜₀ (m : ℕ)) → A := fun i => e ((1 : R) ⊗ₜ[R₀] (i.2 : A₀))
  have hFmem : ∀ i : Σ m : ℕ+, 𝒜₀ (m : ℕ), F i ∈ 𝒜 (i.1 : ℕ) := fun i =>
    hgr _ _ (Submodule.tmul_mem_baseChange_of_mem _ i.2.2)
  have hzero : ∀ c : A, c ∈ 𝒜 0 → c ∈ Algebra.adjoin (𝒜 0) (Set.range F) := fun c hc =>
    Subalgebra.algebraMap_mem _ (⟨c, hc⟩ : 𝒜 0)
  have hall : ∀ y : TensorProduct R₀ R A₀, e y ∈ Algebra.adjoin (𝒜 0) (Set.range F) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul r a =>
        rw [hetmul r a, Algebra.smul_def]
        refine mul_mem (hzero _ (h0 r)) ?_
        rw [show fh a = ∑ n ∈ (DirectSum.decompose 𝒜₀ a).support,
            fh ((DirectSum.decompose 𝒜₀ a n : A₀)) from by
          conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜₀ a]
          rw [map_sum]]
        refine sum_mem fun n _ => ?_
        rcases Nat.eq_zero_or_pos n with hn | hn
        · subst hn
          exact hzero _ (fh.map_mem (DirectSum.decompose 𝒜₀ a 0).2)
        · exact Algebra.subset_adjoin
            ⟨⟨⟨n, hn⟩, DirectSum.decompose 𝒜₀ a n⟩, he1 _⟩
    | add y y' hy hy' => simpa using add_mem hy hy'
  have hadjoin : Algebra.adjoin (𝒜 0) (Set.range F) = ⊤ :=
    top_unique fun z _ => by simpa using hall (e.symm z)
  have hcover : (⨆ i, Proj.basicOpen 𝒜 (F i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top' 𝒜 F (fun i => ⟨(i.1 : ℕ), hFmem i⟩) hadjoin
  have hqc : SheafOfModules.IsQuasicoherent.{u, u, u} (twistingSheaf 𝒜 t) := inferInstance
  let G : (AlgebraicGeometry.Proj 𝒜).Modules := twistingSheaf 𝒜 t
  let _ : G.IsQuasicoherent := hqc
  refine Stacks.AlgebraicGeometry.FinitePresentationLocal.isFinitePresentation_of_affineCover
    G (fun i => Proj.basicOpen 𝒜 (F i)) (TopologicalSpace.IsOpenCover.mk hcover)
    (fun i => Proj.isAffineOpen_basicOpen 𝒜 _ (hFmem i) i.1.2) fun i => ?_
  let _ : Module (Away 𝒜 (F i)) Γ(G, Proj.basicOpen 𝒜 (F i)) :=
    associatedModuleSheafStandardOpenModule 𝒜 (twistGrading 𝒜 t) (F i)
  let ε : Away 𝒜 (F i) ≃+* Γ(AlgebraicGeometry.Proj 𝒜, Proj.basicOpen 𝒜 (F i)) :=
    (Proj.basicOpenIsoAway 𝒜 (F i) (hFmem i) i.1.2).commRingCatIsoToRingEquiv
  exact Module.FinitePresentation.of_addEquiv ε (AddEquiv.refl _) (fun _ _ => rfl)
    (finitePresentation_twistSections 𝒜 h0 i.1.2 (hFmem i) t
      (finitePresentation_twistAway_of_model (GradedRing.toSubmodules 𝒜 h0) 𝒜₀ e hgr
        i.1.2 i.2.2 t))

end Absolute

end Stacks.ProjTwistFinitePresentation

end
