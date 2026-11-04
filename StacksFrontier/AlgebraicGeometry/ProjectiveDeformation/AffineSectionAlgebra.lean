module

public import StacksFrontier.AlgebraicGeometry.ProjectiveDeformation.DegreeBound
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.SectionRingBaseChange.AffineBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeTrivialisationSections
public import StacksFrontier.Deformation.Examples.Linear.GradedAlgebras
public import StacksFrontier.RingTheory.TensorProduct.IsBaseChangeBijectiveSquare

/-!
# The graded algebra of global sections of a deformation over an Artinian base

Let `P` be a polarized family and `D = (X', S', i, i', f', ℒ')` an admissible deformation of `P`
whose base `S'` is affine and has a point every open neighbourhood of which is everything (for
instance the spectrum of an Artinian local ring). At the degree bound `d₀` of
[Stacks, Tag 0D4F] (`PolarizedFamily.degreeBound`) the global sections of the truncated section
algebra

`Q(D) = Γ(S', 𝒪_{S'} ⊕ ⨁_{d ≥ d₀} f'_* ℒ'^{⊗ d})`

form a graded algebra, finite free in every degree, over any ring `R` identified with `Γ(S', 𝒪)`.
This is the object `(A, Q)` of the category of Stacks 0D3L attached to the deformation in the proof
of [Stacks, Tag 0D4S], and a morphism of admissible deformations gives a morphism of that category
(pulling sections back), which is a base change by [Stacks, Tag 0D4F].

## Main definitions

* `…AdmissibleDeformation.sectionAlgebra`: the truncated section algebra at the chosen degree
  bound.
* `…AdmissibleDeformation.toProjectiveGradedAlgebra`: `Q(D)` as an object of Stacks 0D3L.
* `…AdmissibleDeformation.sectionRingHom`, `…toProjectiveGradedAlgebraHom`: the morphism attached
  to a morphism of admissible deformations.
* `…AdmissibleDeformation.Hom.comp`: composition of morphisms of admissible deformations.

## Main results

* `Stacks.AlgebraicGeometry.free_finite_sections_of_isFiniteLocallyFree`.
* `…AdmissibleDeformation.free_finite_sectionPieces`, `…free_finite_sectionGrading`.
* `…AdmissibleDeformation.isBaseChange_sectionRingHom`.
* `…AdmissibleDeformation.sectionRingHom_comp`: the construction is functorial.

## References

* [Stacks Project, Tag 0D4S](https://stacks.math.columbia.edu/tag/0D4S)
* [Stacks Project, Tag 0D4F](https://stacks.math.columbia.edu/tag/0D4F)
* [Stacks Project, Tag 0D3L](https://stacks.math.columbia.edu/tag/0D3L)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

namespace Stacks.AlgebraicGeometry

/-- Free finite modules transport along linear equivalences. -/
private theorem free_finite_of_linearEquiv {R M N : Type*} [Semiring R] [AddCommMonoid M]
    [AddCommMonoid N] [Module R M] [Module R N] (e : M ≃ₗ[R] N)
    (h : Module.Free R M ∧ Module.Finite R M) : Module.Free R N ∧ Module.Finite R N :=
  haveI := h.1
  haveI := h.2
  ⟨Module.Free.of_equiv e, Module.Finite.equiv e⟩

/-- **On a scheme whose only open neighbourhood of some point is everything, the global sections
of a finite locally free module are finite free**, read on the sections of the underlying sheaf.
Such a point lies in a member of any trivializing cover, which is therefore everything. -/
theorem free_finite_sections_of_isFiniteLocallyFree {S : Scheme.{u}} (s₀ : S)
    (hs₀ : ∀ U : S.Opens, s₀ ∈ U → U = ⊤) (M : S.Modules)
    (hM : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := S.ringCatSheaf) M) :
    Module.Free (ToType (S.ringCatSheaf.obj.obj (op ⊤))) (ToType (M.val.obj (op ⊤))) ∧
      Module.Finite (ToType (S.ringCatSheaf.obj.obj (op ⊤))) (ToType (M.val.obj (op ⊤))) := by
  obtain ⟨I, U, m, s, hU, hbij⟩ := Stacks.SheafOfModules.exists_localTrivialisation M hM
  have : s₀ ∈ ⨆ i, U i := by rw [hU]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp this
  have hUi := hs₀ (U i) hi
  let f : (⊤ : Opens S) ⟶ U i := homOfLE (by rw [hUi])
  let L : (ULift.{u} (Fin (m i)) → ToType (S.ringCatSheaf.obj.obj (op ⊤))) →ₗ[
      ToType (S.ringCatSheaf.obj.obj (op ⊤))] ToType (M.val.obj (op ⊤)) :=
    { toFun := fun c => Stacks.SheafOfModules.combSections M (s i) f c
      map_add' := fun c d => by
        simp only [Stacks.SheafOfModules.combSections, Pi.add_apply, add_smul,
          Finset.sum_add_distrib]
      map_smul' := fun r c => by
        simp only [Stacks.SheafOfModules.combSections, Pi.smul_apply, smul_eq_mul, mul_smul,
          RingHom.id_apply, Finset.smul_sum] }
  exact free_finite_of_linearEquiv (LinearEquiv.ofBijective L (hbij i f))
    ⟨inferInstance, inferInstance⟩

/-- Sections over `⊤` are transported along an isomorphism of modules. -/
def sectionsTopLinearEquiv {S : Scheme.{u}} {M N : S.Modules} (e : M ≅ N) :
    Γ(M, ⊤) ≃ₗ[Γ(S, ⊤)] Γ(N, ⊤) :=
  LinearEquiv.ofLinear (Scheme.Modules.sectionsLinearMap e.hom ⊤)
    (Scheme.Modules.sectionsLinearMap e.inv ⊤)
    (by ext x; exact Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app e ⊤ x)
    (by
      ext x
      exact Stacks.AlgebraicGeometry.ProjChartRatioPullbackLocalMul.hom_app_inv_app e.symm ⊤ x)

/-- `free_finite_sections_of_isFiniteLocallyFree`, in the `Γ(M, ⊤)` spelling of the global
sections. -/
theorem free_finite_sections_of_isFiniteLocallyFree' {S : Scheme.{u}} (s₀ : S)
    (hs₀ : ∀ U : S.Opens, s₀ ∈ U → U = ⊤) (M : S.Modules)
    (hM : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := S.ringCatSheaf) M) :
    Module.Free Γ(S, ⊤) Γ(M, ⊤) ∧ Module.Finite Γ(S, ⊤) Γ(M, ⊤) :=
  free_finite_sections_of_isFiniteLocallyFree s₀ hs₀ M hM

end Stacks.AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily.AdmissibleDeformation

open Stacks.AlgebraicGeometry.SectionRingBaseChange Stacks.AlgebraicGeometry.SectionAlgebra
open DirectSum

variable {P : PolarizedFamily.{u}} (D : P.AdmissibleDeformation)

/-- The truncated section algebra of `D` at the chosen degree bound. -/
abbrev sectionAlgebra : SheafGradedAlgebra D.S' :=
  haveI := D.finitePresentation.quasiCompact
  haveI := D.finitePresentation.quasiSeparated
  Stacks.AlgebraicGeometry.SectionRingBaseChange.tailAlgebra D.f' D.L' P.degreeBound
    P.degreeBound_pos

/-- Over a base whose only neighbourhood of some point is everything, every homogeneous piece of
the sections of the truncated section algebra is finite free. -/
theorem free_finite_sectionPieces (s₀ : D.S') (hs₀ : ∀ U : D.S'.Opens, s₀ ∈ U → U = ⊤) (n : ℕ) :
    Module.Free Γ(D.S', ⊤) (D.sectionAlgebra.sectionPieces ⊤ n) ∧
      Module.Finite Γ(D.S', ⊤) (D.sectionAlgebra.sectionPieces ⊤ n) := by
  by_cases h0 : (n : ℤ) = 0
  · obtain rfl : n = 0 := by exact_mod_cast h0
    have h1 : Module.Free (ToType (D.S'.ringCatSheaf.obj.obj (op ⊤)))
        (ToType ((_root_.SheafOfModules.unit D.S'.ringCatSheaf).val.obj (op ⊤))) :=
      Module.Free.self _
    have h2 : Module.Finite (ToType (D.S'.ringCatSheaf.obj.obj (op ⊤)))
        (ToType ((_root_.SheafOfModules.unit D.S'.ringCatSheaf).val.obj (op ⊤))) :=
      Module.Finite.self _
    exact ⟨h1, h2⟩
  · by_cases hn : (P.degreeBound : ℤ) ≤ (n : ℤ)
    · obtain ⟨φ⟩ := IsTruncatedSectionAlgebraWithComparison.piece_iso D
        (D.isTruncatedSectionAlgebraWithComparison_truncatedSectionAlgebra
          P.degreeBound P.degreeBound_pos) n (by exact_mod_cast hn)
      exact free_finite_of_linearEquiv (sectionsTopLinearEquiv φ).symm
        (free_finite_sections_of_isFiniteLocallyFree' s₀ hs₀ _
          ((degreeBoundData P).isFiniteLocallyFree D n (by exact_mod_cast hn)))
    · have hsub : Subsingleton (D.sectionAlgebra.sectionPieces ⊤ n) :=
        ⟨fun x y => (eq_zero_of_tailPiece D.laurentPushforward P.degreeBound h0 hn (op ⊤) x).trans
          (eq_zero_of_tailPiece D.laurentPushforward P.degreeBound h0 hn (op ⊤) y).symm⟩
      have : Finite (D.sectionAlgebra.sectionPieces ⊤ n) := Finite.of_subsingleton
      exact ⟨Module.Free.of_subsingleton _ _, Module.Finite.of_finite⟩

section Over

attribute [local instance] Stacks.SymGraded.AffinePieces.sectionRingAlgebra

variable {R : Type u} [CommRing R] (ρ : R →+* Γ(D.S', ⊤))

/-- The graded ring of global sections of the truncated section algebra, as an algebra over a
ring mapping to the global functions of the base. -/
@[instance_reducible]
def sectionRingAlgebraOver : Algebra R (D.sectionAlgebra.sectionRing ⊤) :=
  ((algebraMap Γ(D.S', ⊤) (D.sectionAlgebra.sectionRing ⊤)).comp ρ).toAlgebra

/-- The ring `Γ(S', 𝒪)` as an algebra over a ring mapping to it. -/
@[instance_reducible]
def baseAlgebraOver : Algebra R Γ(D.S', ⊤) := ρ.toAlgebra

/-- The two algebra structures over `R` and over `Γ(S', 𝒪)` form a tower. -/
theorem isScalarTower_sectionRingAlgebraOver :
    letI := sectionRingAlgebraOver D ρ
    letI := baseAlgebraOver D ρ
    IsScalarTower R Γ(D.S', ⊤) (D.sectionAlgebra.sectionRing ⊤) := by
  let := sectionRingAlgebraOver D ρ
  let := baseAlgebraOver D ρ
  refine IsScalarTower.of_algebraMap_smul fun r x => ?_
  exact Algebra.smul_def (ρ r) x

/-- The degree-`n` part of the graded ring of global sections, as a submodule over `R`. -/
def sectionGrading (n : ℕ) :
    letI := sectionRingAlgebraOver D ρ
    Submodule R (D.sectionAlgebra.sectionRing ⊤) :=
  letI := sectionRingAlgebraOver D ρ
  letI := baseAlgebraOver D ρ
  haveI := isScalarTower_sectionRingAlgebraOver D ρ
  (gradingSubmodule D.sectionAlgebra ⊤ n).restrictScalars R

/-- Membership in the degree-`n` part over `R` is membership in the degree-`n` part. -/
theorem mem_sectionGrading (n : ℕ) (x : D.sectionAlgebra.sectionRing ⊤) :
    x ∈ sectionGrading D ρ n ↔ x ∈ gradingSubmodule D.sectionAlgebra ⊤ n := Iff.rfl

/-- The decomposition of the graded ring of global sections into its parts over `R`. -/
@[instance_reducible]
def sectionGradingDecomposition :
    letI := sectionRingAlgebraOver D ρ
    DirectSum.Decomposition (sectionGrading D ρ) := by
  letI := sectionRingAlgebraOver D ρ
  let d : D.sectionAlgebra.sectionRing ⊤ →+ DirectSum ℕ (fun n => ↥(sectionGrading D ρ n)) :=
    DirectSum.toAddMonoid fun n =>
      (DirectSum.of (fun n => sectionGrading D ρ n) n).comp
        ((gradingSubmoduleEquiv D.sectionAlgebra ⊤ n).toLinearMap.toAddMonoidHom)
  refine DirectSum.Decomposition.ofAddHom _ d ?_ ?_
  · apply DirectSum.addHom_ext
    intro n x
    simp only [d, AddMonoidHom.comp_apply, DirectSum.toAddMonoid_of, AddMonoidHom.id_apply]
    exact DirectSum.coeAddMonoidHom_of (sectionGrading D ρ) n _
  · apply DirectSum.addHom_ext
    intro n y
    obtain ⟨x, hx⟩ := y
    obtain ⟨a, rfl⟩ := hx
    simp only [d, AddMonoidHom.comp_apply, DirectSum.coeAddMonoidHom_of, AddMonoidHom.id_apply]
    exact (DirectSum.toAddMonoid_of _ n a).trans (congrArg (DirectSum.of _ n) (Subtype.ext rfl))

/-- The graded ring of global sections is a graded algebra over `R`. -/
@[instance_reducible]
def sectionGradedAlgebra :
    letI := sectionRingAlgebraOver D ρ
    _root_.GradedAlgebra (sectionGrading D ρ) := by
  letI := sectionRingAlgebraOver D ρ
  exact { toDecomposition := sectionGradingDecomposition D ρ
          one_mem := ⟨_, (DirectSum.one_def _).symm⟩
          mul_mem := by
            rintro n m a b ⟨a, rfl⟩ ⟨b, rfl⟩
            exact ⟨_, (DirectSum.of_mul_of (A := D.sectionAlgebra.sectionPieces ⊤) a b).symm⟩ }

/-- **Over a base algebra identified with the global functions, every graded piece is finite
free.** -/
theorem free_finite_sectionGrading (hρ : Function.Bijective ρ) (s₀ : D.S')
    (hs₀ : ∀ U : D.S'.Opens, s₀ ∈ U → U = ⊤) (n : ℕ) :
    letI := sectionRingAlgebraOver D ρ
    Module.Free R (sectionGrading D ρ n) ∧ Module.Finite R (sectionGrading D ρ n) := by
  let := sectionRingAlgebraOver D ρ
  let := baseAlgebraOver D ρ
  have := isScalarTower_sectionRingAlgebraOver D ρ
  obtain ⟨_, _⟩ := free_finite_of_linearEquiv (gradingSubmoduleEquiv D.sectionAlgebra ⊤ n)
    (free_finite_sectionPieces D s₀ hs₀ n)
  obtain ⟨_, _⟩ := free_finite_of_linearEquiv
    (LinearEquiv.ofBijective (Algebra.linearMap R Γ(D.S', ⊤)) hρ) ⟨.self R, .self R⟩
  have : Module.Free R (gradingSubmodule D.sectionAlgebra ⊤ n) :=
    Module.Free.trans (R := R) (S := Γ(D.S', ⊤))
  have : Module.Finite R (gradingSubmodule D.sectionAlgebra ⊤ n) :=
    Module.Finite.trans Γ(D.S', ⊤) _
  let eS := Submodule.restrictScalarsEquiv R Γ(D.S', ⊤) (D.sectionAlgebra.sectionRing ⊤)
    (gradingSubmodule D.sectionAlgebra ⊤ n)
  exact free_finite_of_linearEquiv (eS.restrictScalars R).symm ⟨inferInstance, inferInstance⟩

end Over

/-- **The graded algebra of global sections of a deformation over an Artinian base**, as an
object of the category of graded algebras finite projective in each degree over `𝒞_Λ`
(Stacks 0D3L). -/
def toProjectiveGradedAlgebra {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k) (ρ : R →+* Γ(D.S', ⊤))
    (hρ : Function.Bijective ρ) (s₀ : D.S') (hs₀ : ∀ U : D.S'.Opens, s₀ ∈ U → U = ⊤) :
    Deformation.Examples.ProjectiveGradedAlgebra.{u, u, u, u} Λ k :=
  letI := sectionRingAlgebraOver D ρ
  letI := sectionGradedAlgebra D ρ
  { base := R
    carrier := D.sectionAlgebra.sectionRing ⊤
    grading := sectionGrading D ρ
    finite := fun n => (free_finite_sectionGrading D ρ hρ s₀ hs₀ n).2
    projective := fun n =>
      haveI := (free_finite_sectionGrading D ρ hρ s₀ hs₀ n).1
      inferInstance }

section Hom

attribute [local instance] Stacks.SymGraded.AffinePieces.sectionRingAlgebra

variable {D₁ D₂ : P.AdmissibleDeformation} (φ : Hom D₁ D₂)

/-- **The homomorphism of graded rings of global sections attached to a morphism of admissible
deformations**: pulling sections back along the morphism of total spaces. -/
def sectionRingHom : D₂.sectionAlgebra.sectionRing ⊤ →+* D₁.sectionAlgebra.sectionRing ⊤ :=
  haveI := D₁.finitePresentation.quasiCompact
  haveI := D₁.finitePresentation.quasiSeparated
  haveI := D₂.finitePresentation.quasiCompact
  haveI := D₂.finitePresentation.quasiSeparated
  squareRingHom φ.total D₂.f' D₁.f' φ.base φ.isPullback.w D₂.L' D₁.L' φ.polarization
    P.degreeBound P.degreeBound P.degreeBound_pos P.degreeBound_pos le_rfl ⊤ ⊤
    le_rfl

/-- The section ring homomorphism lies over the map of global functions of the bases. -/
theorem sectionRingHom_strHom (r : Γ(D₂.S', ⊤)) :
    sectionRingHom φ (D₂.sectionAlgebra.strHom ⊤ r) =
      D₁.sectionAlgebra.strHom ⊤ (φ.base.appLE ⊤ ⊤ le_rfl r) :=
  squareRingHom_strHom _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ r

/-- The section ring homomorphism preserves the grading. -/
theorem sectionRingHom_mem (n : ℕ) (x : D₂.sectionAlgebra.sectionRing ⊤)
    (hx : x ∈ gradingSubmodule D₂.sectionAlgebra ⊤ n) :
    sectionRingHom φ x ∈ gradingSubmodule D₁.sectionAlgebra ⊤ n := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨_, (squareRingHom_of _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ y).symm⟩

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
  {R₁ R₂ : Deformation.ArtinianLocalAlgCat.{u, u, u} Λ k}
  {ρ₁ : R₁ →+* Γ(D₁.S', ⊤)} {ρ₂ : R₂ →+* Γ(D₂.S', ⊤)}

private instance (D : P.AdmissibleDeformation) : QuasiCompact D.f' :=
  D.finitePresentation.quasiCompact

private instance (D : P.AdmissibleDeformation) : QuasiSeparated D.f' :=
  D.finitePresentation.quasiSeparated

/-- The section ring homomorphism is semilinear over a compatible morphism of base algebras. -/
theorem sectionRingHom_smul (b : R₂ ⟶ R₁)
    (hb : ∀ r, φ.base.appLE ⊤ ⊤ le_rfl (ρ₂ r) = ρ₁ (b.hom r)) (r : R₂)
    (x : D₂.sectionAlgebra.sectionRing ⊤) :
    letI := sectionRingAlgebraOver D₂ ρ₂
    letI := sectionRingAlgebraOver D₁ ρ₁
    sectionRingHom φ (r • x) = b.hom r • sectionRingHom φ x := by
  let := sectionRingAlgebraOver D₂ ρ₂
  let := sectionRingAlgebraOver D₁ ρ₁
  show sectionRingHom φ (algebraMap Γ(D₂.S', ⊤) _ (ρ₂ r) * x) =
    algebraMap Γ(D₁.S', ⊤) _ (ρ₁ (b.hom r)) * sectionRingHom φ x
  rw [map_mul, Stacks.SymGraded.AffinePieces.algebraMap_sectionRingAlgebra,
    Stacks.SymGraded.AffinePieces.algebraMap_sectionRingAlgebra, sectionRingHom_strHom, hb]

/-- **The section ring homomorphism is a base change** over a compatible morphism of base
algebras, when the bases are affine and identified with the base algebras. -/
theorem isBaseChange_sectionRingHom [IsAffine D₁.S'] [IsAffine D₂.S'] (hρ₁ : Function.Bijective ρ₁)
    (hρ₂ : Function.Bijective ρ₂) (b : R₂ ⟶ R₁)
    (hb : ∀ r, φ.base.appLE ⊤ ⊤ le_rfl (ρ₂ r) = ρ₁ (b.hom r)) :
    letI := sectionRingAlgebraOver D₂ ρ₂
    letI := sectionRingAlgebraOver D₁ ρ₁
    letI : Algebra R₂ R₁ := b.hom.toAlgebra
    letI : Module R₂ (D₁.sectionAlgebra.sectionRing ⊤) :=
      Module.compHom (D₁.sectionAlgebra.sectionRing ⊤) b.hom.toRingHom
    letI : IsScalarTower R₂ R₁ (D₁.sectionAlgebra.sectionRing ⊤) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    IsBaseChange R₁
      ({ (sectionRingHom φ).toAddMonoidHom with
          map_smul' := sectionRingHom_smul φ b hb } :
        D₂.sectionAlgebra.sectionRing ⊤ →ₗ[R₂] D₁.sectionAlgebra.sectionRing ⊤) := by
  let := sectionRingAlgebraOver D₂ ρ₂
  let := sectionRingAlgebraOver D₁ ρ₁
  let : Algebra R₂ R₁ := b.hom.toAlgebra
  let : Module R₂ (D₁.sectionAlgebra.sectionRing ⊤) :=
    Module.compHom (D₁.sectionAlgebra.sectionRing ⊤) b.hom.toRingHom
  let : IsScalarTower R₂ R₁ (D₁.sectionAlgebra.sectionRing ⊤) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let a := φ.base.appLE ⊤ ⊤ le_rfl
  let : Algebra R₂ Γ(D₂.S', ⊤) := ρ₂.toAlgebra
  let : Algebra Γ(D₂.S', ⊤) Γ(D₁.S', ⊤) := a.hom.toAlgebra
  let : Algebra R₁ Γ(D₁.S', ⊤) := ρ₁.toAlgebra
  let : Algebra R₂ Γ(D₁.S', ⊤) := (ρ₁.comp b.hom.toRingHom).toAlgebra
  have : IsScalarTower R₂ Γ(D₂.S', ⊤) Γ(D₁.S', ⊤) :=
    IsScalarTower.of_algebraMap_eq fun r => (hb r).symm
  have : IsScalarTower R₂ R₁ Γ(D₁.S', ⊤) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have := isScalarTower_sectionRingAlgebraOver D₂ ρ₂
  have := isScalarTower_sectionRingAlgebraOver D₁ ρ₁
  let : ∀ n, Module Γ(D₂.S', ⊤) (D₁.sectionAlgebra.sectionPieces ⊤ n) :=
    fun n => Module.compHom _ a.hom
  have : ∀ n, IsScalarTower Γ(D₂.S', ⊤) Γ(D₁.S', ⊤) (D₁.sectionAlgebra.sectionPieces ⊤ n) :=
    fun n => IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hf := isBaseChange_lmap_tailMapLinearTop φ.total D₂.f' D₁.f' φ.base φ.isPullback.w D₂.L'
    D₁.L' φ.polarization P.degreeBound P.degreeBound_pos le_rfl
    (fun n => (degreeBoundData P).isIso_algebraPullbackHom φ n)
  have : IsScalarTower R₂ Γ(D₁.S', ⊤) (D₁.sectionAlgebra.sectionRing ⊤) :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      show ρ₁ (b.hom r) • x =
        algebraMap Γ(D₁.S', ⊤) (D₁.sectionAlgebra.sectionRing ⊤) (ρ₁ (b.hom r)) * x
      exact (Algebra.smul_def _ _)
  have : IsScalarTower R₂ Γ(D₂.S', ⊤) (D₁.sectionAlgebra.sectionRing ⊤) :=
    IsScalarTower.of_algebraMap_smul fun r x => by
      show ρ₂ r • x =
        algebraMap Γ(D₁.S', ⊤) (D₁.sectionAlgebra.sectionRing ⊤) (ρ₁ (b.hom r)) * x
      rw [← hb, ← Algebra.smul_def]
      rfl
  have key := IsBaseChange.of_bijective_square (R₂ := R₂) (R₁ := R₁) (Γ₂ := Γ(D₂.S', ⊤))
    (Γ₁ := Γ(D₁.S', ⊤)) (M := D₂.sectionAlgebra.sectionRing ⊤)
    (N := D₁.sectionAlgebra.sectionRing ⊤) hρ₁ hρ₂ _ hf
  have heq : ({ (sectionRingHom φ).toAddMonoidHom with
          map_smul' := sectionRingHom_smul φ b hb } :
        D₂.sectionAlgebra.sectionRing ⊤ →ₗ[R₂] D₁.sectionAlgebra.sectionRing ⊤) =
      (DirectSum.lmap fun n => tailMapLinearTop φ.total D₂.f' D₁.f' φ.base φ.isPullback.w D₂.L'
        D₁.L' φ.polarization P.degreeBound P.degreeBound_pos le_rfl
          n).restrictScalars R₂ :=
    LinearMap.ext fun x => (lmap_tailMapLinearTop_apply φ.total D₂.f' D₁.f' φ.base
      φ.isPullback.w D₂.L' D₁.L' φ.polarization P.degreeBound P.degreeBound_pos
      le_rfl x).symm
  rw [heq]
  exact key

/-- **The composite of two morphisms of admissible deformations**: the pasted cartesian square,
with the identification of polarizations through the pullback pseudofunctor. -/
def Hom.comp {D₃ : P.AdmissibleDeformation} (ψ : Hom D₂ D₃) : Hom D₁ D₃ where
  base := φ.base ≫ ψ.base
  total := φ.total ≫ ψ.total
  isPullback := φ.isPullback.paste_horiz ψ.isPullback
  base_comm := by rw [← Category.assoc, φ.base_comm, ψ.base_comm]
  total_comm := by rw [← Category.assoc, φ.total_comm, ψ.total_comm]
  polarization := (Scheme.Modules.pullbackComp φ.total ψ.total).symm.app D₃.L' ≪≫
    (Scheme.Modules.pullback φ.total).mapIso ψ.polarization ≪≫ φ.polarization

/-- **The section ring homomorphisms compose.** -/
theorem sectionRingHom_comp {D₃ : P.AdmissibleDeformation} (ψ : Hom D₂ D₃) :
    sectionRingHom (φ.comp ψ) = (sectionRingHom φ).comp (sectionRingHom ψ) := by
  exact squareRingHom_comp ψ.total φ.total D₃.f' D₂.f' D₁.f' ψ.base φ.base ψ.isPullback.w
    φ.isPullback.w D₃.L' D₂.L' D₁.L' ψ.polarization φ.polarization P.degreeBound
    P.degreeBound_pos ⊤ ⊤ ⊤ le_rfl le_rfl

/-- **The morphism of graded algebras of global sections attached to a morphism of admissible
deformations**, as a morphism of the category of graded algebras finite projective in each degree
over `𝒞_Λ` (Stacks 0D3L), over a compatible morphism of base algebras. -/
def toProjectiveGradedAlgebraHom [IsAffine D₁.S'] [IsAffine D₂.S'] (hρ₁ : Function.Bijective ρ₁)
    (hρ₂ : Function.Bijective ρ₂) (s₁ : D₁.S') (hs₁ : ∀ U : D₁.S'.Opens, s₁ ∈ U → U = ⊤)
    (s₂ : D₂.S') (hs₂ : ∀ U : D₂.S'.Opens, s₂ ∈ U → U = ⊤) (b : R₂ ⟶ R₁)
    (hb : ∀ r, φ.base.appLE ⊤ ⊤ le_rfl (ρ₂ r) = ρ₁ (b.hom r)) :
    Deformation.Examples.ProjectiveGradedAlgebra.Hom
      (D₂.toProjectiveGradedAlgebra R₂ ρ₂ hρ₂ s₂ hs₂)
      (D₁.toProjectiveGradedAlgebra R₁ ρ₁ hρ₁ s₁ hs₁) where
  base := b
  map := sectionRingHom φ
  map_smul := sectionRingHom_smul φ b hb
  map_mem := fun d x hx => sectionRingHom_mem φ d x hx
  isBaseChange := isBaseChange_sectionRingHom φ hρ₁ hρ₂ b hb

/-- The ring map of `toProjectiveGradedAlgebraHom` is the section ring homomorphism. -/
theorem toProjectiveGradedAlgebraHom_map [IsAffine D₁.S'] [IsAffine D₂.S']
    (hρ₁ : Function.Bijective ρ₁) (hρ₂ : Function.Bijective ρ₂) (s₁ : D₁.S')
    (hs₁ : ∀ U : D₁.S'.Opens, s₁ ∈ U → U = ⊤) (s₂ : D₂.S')
    (hs₂ : ∀ U : D₂.S'.Opens, s₂ ∈ U → U = ⊤) (b : R₂ ⟶ R₁)
    (hb : ∀ r, φ.base.appLE ⊤ ⊤ le_rfl (ρ₂ r) = ρ₁ (b.hom r)) :
    (toProjectiveGradedAlgebraHom φ hρ₁ hρ₂ s₁ hs₁ s₂ hs₂ b hb).map = sectionRingHom φ := rfl

end Hom

end Stacks.AlgebraicGeometry.ProjectiveDeformation.PolarizedFamily.AdmissibleDeformation
end
