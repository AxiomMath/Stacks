module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Prod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic
public import StacksFrontier.Algebra.Module.Projective.Determinant.ShortExact
public import StacksFrontier.Homology.TwoTermComplex.DeterminantLine.SurjectiveQuasiIso

/-!
# Compatibility of the determinant isomorphism with composition

The canonical isomorphism of determinant lines attached to a degreewise-surjective
quasi-isomorphism is compatible with composition. The comparison runs through the tower of
kernels of a composite of two surjections and the naturality of the determinant equivalence of a
short exact sequence.

## Main results

* `TwoTermComplex.determinantEquivOfSurjectiveQuasiIso_comp`: compatibility with composition.

## References

* [Stacks Project, Tag 0FJL](https://stacks.math.columbia.edu/tag/0FJL)
-/

namespace TwoTermComplex

/-! ### Compatibility with composition -/

section

universe u v₁ v₀ w₁ w₀ x₁ x₀ v w x

open TwoTermComplex

variable {R : Type u} [CommRing R]
variable {A : Type v} {B : Type w} {C : Type x}
variable [AddCommGroup A] [Module R A] [Module.Finite R A] [Module.Projective R A]
variable [AddCommGroup B] [Module R B] [Module.Finite R B] [Module.Projective R B]
variable [AddCommGroup C] [Module R C] [Module.Finite R C] [Module.Projective R C]

private def kernelTowerInclusion (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    LinearMap.ker f →ₗ[R] LinearMap.ker (g.comp f) :=
  (LinearMap.ker f).subtype.codRestrict (LinearMap.ker (g.comp f)) (by
    intro z
    change g (f z.1) = 0
    rw [z.property, map_zero])

private def kernelTowerProjection (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    LinearMap.ker (g.comp f) →ₗ[R] LinearMap.ker g :=
  (f.domRestrict (LinearMap.ker (g.comp f))).codRestrict (LinearMap.ker g) (by
    intro z
    change g (f z.1) = 0
    exact z.property)

omit [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B]
    [Module.Finite R C] [Module.Projective R C] in
private theorem kernelTowerProjection_surjective (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Surjective f) : Function.Surjective (kernelTowerProjection f g) := by
  intro z
  obtain ⟨a, ha⟩ := hf z.1
  refine ⟨⟨a, ?_⟩, ?_⟩
  · show g (f a) = 0
    rw [ha]
    exact z.property
  · apply Subtype.ext
    exact ha

omit [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B]
    [Module.Finite R C] [Module.Projective R C] in
private theorem kernelTower_exact (f : A →ₗ[R] B) (g : B →ₗ[R] C) :
    Function.Exact (kernelTowerInclusion f g) (kernelTowerProjection f g) := by
  intro z
  constructor
  · intro hz
    refine ⟨⟨z.1, ?_⟩, ?_⟩
    · show f z.1 = 0
      simpa [kernelTowerProjection] using congrArg Subtype.val hz
    · exact Subtype.ext rfl
  · rintro ⟨y, rfl⟩
    apply Subtype.ext
    simp [kernelTowerProjection, kernelTowerInclusion]

private noncomputable def kernelTowerDetEquiv (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Surjective f)
    [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)]
    [Module.Finite R (LinearMap.ker g)] [Module.Projective R (LinearMap.ker g)]
    [Module.Finite R (LinearMap.ker (g.comp f))]
    [Module.Projective R (LinearMap.ker (g.comp f))] :
    TensorProduct R
        (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker f))
        (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker g)) ≃ₗ[R]
      ProjectiveDeterminant.module (R := R) (M := LinearMap.ker (g.comp f)) :=
  (TensorProduct.congr determinantAnnihilatorEquiv determinantAnnihilatorEquiv).trans <|
    (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
      (kernelTowerInclusion f g) (kernelTowerProjection f g)
      (by intro x y h; apply Subtype.ext; simpa [kernelTowerInclusion] using congrArg Subtype.val h)
      (kernelTower_exact f g) (kernelTowerProjection_surjective f g hf)).val |>.trans
        determinantAnnihilatorEquiv.symm

private theorem kernelDeterminantEquiv_comp
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hfg : Function.Surjective (g.comp f))
    [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)]
    [Module.Finite R (LinearMap.ker g)] [Module.Projective R (LinearMap.ker g)]
    [Module.Finite R (LinearMap.ker (g.comp f))]
    [Module.Projective R (LinearMap.ker (g.comp f))]
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker f))
    (z : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker g))
    (y : ProjectiveDeterminant.module (R := R) (M := C)) :
    kernelDeterminantEquiv (g.comp f) hfg
        (kernelTowerDetEquiv f g hf (x ⊗ₜ[R] z) ⊗ₜ[R] y) =
      kernelDeterminantEquiv f hf
        (x ⊗ₜ[R] kernelDeterminantEquiv g hg (z ⊗ₜ[R] y)) := by
  let EAf := determinantAnnihilatorEquiv (R := R) (M := LinearMap.ker f)
  let EAg := determinantAnnihilatorEquiv (R := R) (M := LinearMap.ker g)
  let EAfg := determinantAnnihilatorEquiv (R := R) (M := LinearMap.ker (g.comp f))
  let EAa := determinantAnnihilatorEquiv (R := R) (M := A)
  let EAb := determinantAnnihilatorEquiv (R := R) (M := B)
  let EAc := determinantAnnihilatorEquiv (R := R) (M := C)
  let γfg := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker (g.comp f)).subtype (g.comp f)
    (LinearMap.ker (g.comp f)).injective_subtype
    (g.comp f).exact_subtype_ker_map hfg).val
  let γf := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker f).subtype f (LinearMap.ker f).injective_subtype
    f.exact_subtype_ker_map hf).val
  let γg := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker g).subtype g (LinearMap.ker g).injective_subtype
    g.exact_subtype_ker_map hg).val
  let γk := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (kernelTowerInclusion f g) (kernelTowerProjection f g)
    (by intro a b h; apply Subtype.ext; simpa [kernelTowerInclusion] using congrArg Subtype.val h)
    (kernelTower_exact f g) (kernelTowerProjection_surjective f g hf)).val
  obtain ⟨t, ht⟩ := (ExteriorAlgebra.map_surjective_iff.mpr
    (kernelTowerProjection_surjective f g hf))
      (EAg z : ExteriorAlgebra R (LinearMap.ker g))
  obtain ⟨w, hw⟩ := (ExteriorAlgebra.map_surjective_iff.mpr hfg)
    (EAc y : ExteriorAlgebra R C)
  apply EAa.injective
  show γfg (EAfg (kernelTowerDetEquiv f g hf (x ⊗ₜ[R] z)) ⊗ₜ[R] EAc y) =
    γf (EAf x ⊗ₜ[R] EAb (kernelDeterminantEquiv g hg (z ⊗ₜ[R] y)))
  have hγk := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (kernelTowerInclusion f g) (kernelTowerProjection f g)
    (by intro a b h; apply Subtype.ext; simpa [kernelTowerInclusion] using congrArg Subtype.val h)
    (kernelTower_exact f g) (kernelTowerProjection_surjective f g hf)).property
    (EAf x) (EAg z) t ht
  have hγg := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker g).subtype g (LinearMap.ker g).injective_subtype
    g.exact_subtype_ker_map hg).property (EAg z) (EAc y)
      (ExteriorAlgebra.map f w) (by
        rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
        exact hw)
  have hγfg := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker (g.comp f)).subtype (g.comp f)
    (LinearMap.ker (g.comp f)).injective_subtype
    (g.comp f).exact_subtype_ker_map hfg).property
    (EAfg (kernelTowerDetEquiv f g hf (x ⊗ₜ[R] z))) (EAc y) w hw
  have hγf := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker f).subtype f (LinearMap.ker f).injective_subtype
    f.exact_subtype_ker_map hf).property
    (EAf x) (EAb (kernelDeterminantEquiv g hg (z ⊗ₜ[R] y)))
    (ExteriorAlgebra.map (LinearMap.ker (g.comp f)).subtype t * w) (by
      rw [map_mul]
      show ExteriorAlgebra.map f
          (ExteriorAlgebra.map (LinearMap.ker (g.comp f)).subtype t) *
        ExteriorAlgebra.map f w =
          (γg (EAg z ⊗ₜ[R] EAc y) : ExteriorAlgebra R B)
      rw [hγg, ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
      have hlin : f.comp (LinearMap.ker (g.comp f)).subtype =
          (LinearMap.ker g).subtype.comp (kernelTowerProjection f g) := by
        ext q
        rfl
      rw [hlin, ← ExteriorAlgebra.map_comp_map]
      exact congrArg (fun q => ExteriorAlgebra.map (LinearMap.ker g).subtype q *
        ExteriorAlgebra.map f w) ht)
  apply Subtype.ext
  rw [hγfg, hγf]
  show ExteriorAlgebra.map (LinearMap.ker (g.comp f)).subtype
      (γk (EAf x ⊗ₜ[R] EAg z) : ExteriorAlgebra R _) * w = _
  rw [hγk, map_mul, ← mul_assoc]
  congr 1
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
  rfl

private theorem annihilator_mapEquiv
    (e : A ≃ₗ[R] B) (x : ProjectiveDeterminant.module (R := R) (M := A)) :
    ((determinantAnnihilatorEquiv (R := R) (M := B)
      (ProjectiveDeterminant.mapEquiv e x)) : ExteriorAlgebra R B) =
      ExteriorAlgebra.map e
        ((determinantAnnihilatorEquiv (R := R) (M := A) x) : ExteriorAlgebra R A) :=
  rfl

private theorem determinantExact_naturality
    {A' : Type*} {B' : Type*} {C' : Type*}
    [AddCommGroup A'] [Module R A'] [Module.Finite R A'] [Module.Projective R A']
    [AddCommGroup B'] [Module R B'] [Module.Finite R B'] [Module.Projective R B']
    [AddCommGroup C'] [Module R C'] [Module.Finite R C'] [Module.Projective R C']
    (f : A →ₗ[R] B) (g : B →ₗ[R] C)
    (f' : A' →ₗ[R] B') (g' : B' →ₗ[R] C')
    (hf : Function.Injective f) (hex : Function.Exact f g) (hg : Function.Surjective g)
    (hf' : Function.Injective f') (hex' : Function.Exact f' g')
    (hg' : Function.Surjective g')
    (α : A ≃ₗ[R] A') (β : B ≃ₗ[R] B') (γ : C ≃ₗ[R] C')
    (hαβ : ∀ a, β (f a) = f' (α a))
    (hβγ : ∀ b, γ (g b) = g' (β b))
    (x : ProjectiveDeterminant.module (R := R) (M := A))
    (z : ProjectiveDeterminant.module (R := R) (M := C)) :
    let G := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact f g hf hex hg).val
    let G' := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact f' g' hf' hex'
      hg').val
    let EA := determinantAnnihilatorEquiv (R := R) (M := A)
    let EC := determinantAnnihilatorEquiv (R := R) (M := C)
    let EB := determinantAnnihilatorEquiv (R := R) (M := B)
    let EA' := determinantAnnihilatorEquiv (R := R) (M := A')
    let EC' := determinantAnnihilatorEquiv (R := R) (M := C')
    let EB' := determinantAnnihilatorEquiv (R := R) (M := B')
    EB'.symm (G' (EA' (ProjectiveDeterminant.mapEquiv α x) ⊗ₜ[R]
      EC' (ProjectiveDeterminant.mapEquiv γ z))) =
      ProjectiveDeterminant.mapEquiv β (EB.symm (G (EA x ⊗ₜ[R] EC z))) := by
  dsimp only
  apply (determinantAnnihilatorEquiv (R := R) (M := B')).injective
  show (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
      f' g' hf' hex' hg').val
      (determinantAnnihilatorEquiv (R := R) (M := A')
          (ProjectiveDeterminant.mapEquiv α x) ⊗ₜ[R]
       determinantAnnihilatorEquiv (R := R) (M := C')
          (ProjectiveDeterminant.mapEquiv γ z)) =
    determinantAnnihilatorEquiv (R := R) (M := B')
      (ProjectiveDeterminant.mapEquiv β
        ((determinantAnnihilatorEquiv (R := R) (M := B)).symm
          ((ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
            f g hf hex hg).val
            (determinantAnnihilatorEquiv (R := R) (M := A) x ⊗ₜ[R]
              determinantAnnihilatorEquiv (R := R) (M := C) z))))
  exact Subtype.ext ((ProjectiveDeterminant.determinantTensorDeterminantEquiv_naturality
    f g f' g' hf hex hg hf' hex' hg' α β γ hαβ hβγ).2.2.2
    (determinantAnnihilatorEquiv (R := R) (M := A) x)
    (determinantAnnihilatorEquiv (R := R) (M := C) z)
    (determinantAnnihilatorEquiv (R := R) (M := A')
      (ProjectiveDeterminant.mapEquiv α x))
    (determinantAnnihilatorEquiv (R := R) (M := C')
      (ProjectiveDeterminant.mapEquiv γ z))
    (annihilator_mapEquiv α x).symm (annihilator_mapEquiv γ z).symm).symm

/-- **Stacks 0FJL.** The canonical determinant equivalence associated to a composite of
degreewise-surjective quasi-isomorphisms of two-term finite-projective complexes is the
composite of their canonical determinant equivalences. -/
@[stacks 0FJL]
public theorem determinantEquivOfSurjectiveQuasiIso_comp
    {R : Type u} [CommRing R]
    {K₁ : Type v₁} {K₀ : Type v₀} {L₁ : Type w₁} {L₀ : Type w₀}
    {M₁ : Type x₁} {M₀ : Type x₀}
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
    [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
    [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
    [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
    [AddCommGroup M₁] [Module R M₁] [Module.Finite R M₁] [Module.Projective R M₁]
    [AddCommGroup M₀] [Module R M₀] [Module.Finite R M₀] [Module.Projective R M₀]
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀) (M : M₁ →ₗ[R] M₀)
    (a : TwoTermComplex.Hom K L) (b : TwoTermComplex.Hom L M)
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso)
    (hb : b.IsDegreewiseSurjective) (hqb : b.IsQuasiIso) :
    let c : TwoTermComplex.Hom K M :=
      { neg := b.neg.comp a.neg
        zero := b.zero.comp a.zero
        comm
    := by rw [LinearMap.comp_assoc, a.comm, ← LinearMap.comp_assoc, b.comm,
          LinearMap.comp_assoc] }
    let hc : c.IsDegreewiseSurjective :=
      ⟨hb.1.comp ha.1, hb.2.comp ha.2⟩
    ∃ hqc : c.IsQuasiIso,
      letI : Module.Finite R (LinearMap.ker a.neg) :=
        TwoTermComplex.kernel_finite a.neg ha.1
      letI : Module.Projective R (LinearMap.ker a.neg) :=
        TwoTermComplex.kernel_projective a.neg ha.1
      letI : Module.Finite R (LinearMap.ker a.zero) :=
        TwoTermComplex.kernel_finite a.zero ha.2
      letI : Module.Projective R (LinearMap.ker a.zero) :=
        TwoTermComplex.kernel_projective a.zero ha.2
      letI : Module.Finite R (LinearMap.ker b.neg) :=
        TwoTermComplex.kernel_finite b.neg hb.1
      letI : Module.Projective R (LinearMap.ker b.neg) :=
        TwoTermComplex.kernel_projective b.neg hb.1
      letI : Module.Finite R (LinearMap.ker b.zero) :=
        TwoTermComplex.kernel_finite b.zero hb.2
      letI : Module.Projective R (LinearMap.ker b.zero) :=
        TwoTermComplex.kernel_projective b.zero hb.2
      letI : Module.Finite R (LinearMap.ker c.neg) :=
        TwoTermComplex.kernel_finite c.neg hc.1
      letI : Module.Projective R (LinearMap.ker c.neg) :=
        TwoTermComplex.kernel_projective c.neg hc.1
      letI : Module.Finite R (LinearMap.ker c.zero) :=
        TwoTermComplex.kernel_finite c.zero hc.2
      letI : Module.Projective R (LinearMap.ker c.zero) :=
        TwoTermComplex.kernel_projective c.zero hc.2
      let Da := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K L a ha hqa
      let Db := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso L M b hb hqb
      let Dc := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K M c hc hqc
      Da.equiv.trans Db.equiv = Dc.equiv := by
  let c : TwoTermComplex.Hom K M :=
    { neg := b.neg.comp a.neg
      zero := b.zero.comp a.zero
      comm := by rw [LinearMap.comp_assoc, a.comm, ← LinearMap.comp_assoc, b.comm,
        LinearMap.comp_assoc] }
  let hc : c.IsDegreewiseSurjective :=
    ⟨by intro z; obtain ⟨y, rfl⟩ := hb.1 z; obtain ⟨x, rfl⟩ := ha.1 y; exact ⟨x, rfl⟩,
     by intro z; obtain ⟨y, rfl⟩ := hb.2 z; obtain ⟨x, rfl⟩ := ha.2 y; exact ⟨x, rfl⟩⟩
  have hqc : c.IsQuasiIso := by
    have hn : c.hMinus = b.hMinus.comp a.hMinus := by ext x; rfl
    have hz : c.hZero = b.hZero.comp a.hZero := by ext x; rfl
    rw [TwoTermComplex.Hom.IsQuasiIso, hn, hz]
    exact ⟨hqb.1.comp hqa.1, hqb.2.comp hqa.2⟩
  refine ⟨hqc, ?_⟩
  let : Module.Finite R (LinearMap.ker a.neg) :=
    TwoTermComplex.kernel_finite a.neg ha.1
  let : Module.Projective R (LinearMap.ker a.neg) :=
    TwoTermComplex.kernel_projective a.neg ha.1
  let : Module.Finite R (LinearMap.ker a.zero) :=
    TwoTermComplex.kernel_finite a.zero ha.2
  let : Module.Projective R (LinearMap.ker a.zero) :=
    TwoTermComplex.kernel_projective a.zero ha.2
  let : Module.Finite R (LinearMap.ker b.neg) :=
    TwoTermComplex.kernel_finite b.neg hb.1
  let : Module.Projective R (LinearMap.ker b.neg) :=
    TwoTermComplex.kernel_projective b.neg hb.1
  let : Module.Finite R (LinearMap.ker b.zero) :=
    TwoTermComplex.kernel_finite b.zero hb.2
  let : Module.Projective R (LinearMap.ker b.zero) :=
    TwoTermComplex.kernel_projective b.zero hb.2
  let : Module.Finite R (LinearMap.ker c.neg) :=
    TwoTermComplex.kernel_finite c.neg hc.1
  let : Module.Projective R (LinearMap.ker c.neg) :=
    TwoTermComplex.kernel_projective c.neg hc.1
  let : Module.Finite R (LinearMap.ker c.zero) :=
    TwoTermComplex.kernel_finite c.zero hc.2
  let : Module.Projective R (LinearMap.ker c.zero) :=
    TwoTermComplex.kernel_projective c.zero hc.2
  let Da := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K L a ha hqa
  let Db := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso L M b hb hqb
  let Dc := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K M c hc hqc
  let ea : LinearMap.ker a.neg ≃ₗ[R] LinearMap.ker a.zero :=
    LinearEquiv.ofBijective a.kernelDifferential Da.kernelAcyclic
  let eb : LinearMap.ker b.neg ≃ₗ[R] LinearMap.ker b.zero :=
    LinearEquiv.ofBijective b.kernelDifferential Db.kernelAcyclic
  let ec : LinearMap.ker c.neg ≃ₗ[R] LinearMap.ker c.zero :=
    LinearEquiv.ofBijective c.kernelDifferential Dc.kernelAcyclic
  have hinc (q : LinearMap.ker a.neg) :
      ec (kernelTowerInclusion a.neg b.neg q) =
        kernelTowerInclusion a.zero b.zero (ea q) :=
    Subtype.ext rfl
  have hproj (q : LinearMap.ker c.neg) :
      eb (kernelTowerProjection a.neg b.neg q) =
        kernelTowerProjection a.zero b.zero (ec q) :=
    Subtype.ext (LinearMap.congr_fun a.comm q.1).symm
  have hnat
      (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
      (z : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker b.neg)) :
      kernelTowerDetEquiv a.zero b.zero ha.2
          (delta a.kernelDifferential Da.kernelRankZero x ⊗ₜ[R]
            delta b.kernelDifferential Db.kernelRankZero z) =
        delta c.kernelDifferential Dc.kernelRankZero
          (kernelTowerDetEquiv a.neg b.neg ha.1 (x ⊗ₜ[R] z)) := by
    have H := determinantExact_naturality
      (kernelTowerInclusion a.neg b.neg) (kernelTowerProjection a.neg b.neg)
      (kernelTowerInclusion a.zero b.zero) (kernelTowerProjection a.zero b.zero)
      (by intro p q h; apply Subtype.ext;
          simpa [kernelTowerInclusion] using congrArg Subtype.val h)
      (kernelTower_exact a.neg b.neg)
      (kernelTowerProjection_surjective a.neg b.neg ha.1)
      (by intro p q h; apply Subtype.ext;
          simpa [kernelTowerInclusion] using congrArg Subtype.val h)
      (kernelTower_exact a.zero b.zero)
      (kernelTowerProjection_surjective a.zero b.zero ha.2)
      ea ec eb hinc hproj x z
    have haMap (q) : ProjectiveDeterminant.mapEquiv ea q =
        delta a.kernelDifferential Da.kernelRankZero q := rfl
    have hbMap (q) : ProjectiveDeterminant.mapEquiv eb q =
        delta b.kernelDifferential Db.kernelRankZero q := rfl
    have hcMap (q) : ProjectiveDeterminant.mapEquiv ec q =
        delta c.kernelDifferential Dc.kernelRankZero q := rfl
    simpa only [kernelTowerDetEquiv, haMap, hbMap, hcMap,
      LinearEquiv.trans_apply, TensorProduct.congr_tmul] using H
  apply Dc.unique (Da.equiv.trans Db.equiv)
  intro φ x y
  let Tn := kernelTowerDetEquiv a.neg b.neg ha.1
  let Tz := kernelTowerDetEquiv a.zero b.zero ha.2
  have hcomp0 (p : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.zero))
      (q : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker b.zero))
      (r : ProjectiveDeterminant.module (R := R) (M := M₀)) :
      kernelDeterminantEquiv c.zero hc.2 (Tz (p ⊗ₜ[R] q) ⊗ₜ[R] r) =
        kernelDeterminantEquiv a.zero ha.2
          (p ⊗ₜ[R] kernelDeterminantEquiv b.zero hb.2 (q ⊗ₜ[R] r)) :=
    kernelDeterminantEquiv_comp a.zero b.zero ha.2 hb.2 hc.2 p q r
  have hcomp1 (p : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
      (q : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker b.neg))
      (r : ProjectiveDeterminant.module (R := R) (M := M₁)) :
      kernelDeterminantEquiv c.neg hc.1 (Tn (p ⊗ₜ[R] q) ⊗ₜ[R] r) =
        kernelDeterminantEquiv a.neg ha.1
          (p ⊗ₜ[R] kernelDeterminantEquiv b.neg hb.1 (q ⊗ₜ[R] r)) :=
    kernelDeterminantEquiv_comp a.neg b.neg ha.1 hb.1 hc.1 p q r
  have hpure (p : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
      (q : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker b.neg)) :
      kernelDeterminantEquiv c.zero hc.2
        (delta c.kernelDifferential Dc.kernelRankZero (Tn (p ⊗ₜ[R] q)) ⊗ₜ[R]
          (Da.equiv.trans Db.equiv) φ y) =
        φ (kernelDeterminantEquiv c.neg hc.1 (Tn (p ⊗ₜ[R] q) ⊗ₜ[R] y)) := by
    calc
      _ = kernelDeterminantEquiv c.zero hc.2
          (Tz (delta a.kernelDifferential Da.kernelRankZero p ⊗ₜ[R]
            delta b.kernelDifferential Db.kernelRankZero q) ⊗ₜ[R]
            (Da.equiv.trans Db.equiv) φ y) := by rw [hnat p q]
      _ = kernelDeterminantEquiv a.zero ha.2
          (delta a.kernelDifferential Da.kernelRankZero p ⊗ₜ[R]
            kernelDeterminantEquiv b.zero hb.2
              (delta b.kernelDifferential Db.kernelRankZero q ⊗ₜ[R]
                Db.equiv (Da.equiv φ) y)) := hcomp0 _ _ _
      _ = kernelDeterminantEquiv a.zero ha.2
          (delta a.kernelDifferential Da.kernelRankZero p ⊗ₜ[R]
            (Da.equiv φ) (kernelDeterminantEquiv b.neg hb.1 (q ⊗ₜ[R] y))) := by
              rw [Db.compatibility]
      _ = φ (kernelDeterminantEquiv a.neg ha.1
          (p ⊗ₜ[R] kernelDeterminantEquiv b.neg hb.1 (q ⊗ₜ[R] y))) := by
              rw [Da.compatibility]
      _ = _ := by rw [hcomp1]
  have h_all (t : TensorProduct R
      (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker a.neg))
      (ProjectiveDeterminant.module (R := R) (M := LinearMap.ker b.neg))) :
      kernelDeterminantEquiv c.zero hc.2
        (delta c.kernelDifferential Dc.kernelRankZero (Tn t) ⊗ₜ[R]
          (Da.equiv.trans Db.equiv) φ y) =
        φ (kernelDeterminantEquiv c.neg hc.1 (Tn t ⊗ₜ[R] y)) := by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul p q => exact hpure p q
    | add p q hp hq => simpa only [map_add, TensorProduct.add_tmul] using congrArg₂ (· + ·) hp hq
  simpa only [Tn.apply_symm_apply] using h_all (Tn.symm x)

end

end TwoTermComplex
