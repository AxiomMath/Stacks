module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Prod
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic
public import StacksFrontier.Algebra.Module.Projective.Determinant.ShortExact
public import StacksFrontier.Homology.TwoTermComplex.DeterminantLine.Composition
public import StacksFrontier.Homology.TwoTermComplex.DeterminantLine.SurjectiveQuasiIso

/-!
# Homotopic surjections induce the same determinant isomorphism

Two degreewise-surjective quasi-isomorphisms out of one complex that are homotopic induce the
same isomorphism, the comparison being the determinant identity
`det (1 + a ∘ b) = det (1 + b ∘ a)` for the homotopy. The homotopy is first lifted to an
automorphism of the source complex of determinant one, which is possible after adding a
contractible summand, and the isomorphism is shown to be unchanged by such an automorphism.

## Main results

* `TwoTermComplex.determinantEquiv_eq_of_homotopic_surjections`: homotopic degreewise-surjective
  quasi-isomorphisms induce the same isomorphism.

## References

* [Stacks Project, Tag 0FJK](https://stacks.math.columbia.edu/tag/0FJK)
-/

namespace TwoTermComplex

/-! ### Homotopic surjections induce the same isomorphism -/

section

universe u v₁ v₀ w₁ w₀

private theorem determinant_id
    {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M] :
    ProjectiveDeterminant.det (LinearMap.id : M →ₗ[R] M) = 1 := by
  symm
  apply (Classical.choose_spec (ProjectiveDeterminant.existsUnique_scalar
    (ProjectiveDeterminant.map (fun _ => rfl) (LinearMap.id : M →ₗ[R] M)))).2
  rw [ProjectiveDeterminant.map_id]
  simp

/-- A shear on a product of finite projective modules has determinant one. -/
private theorem determinant_shear
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) :
    ProjectiveDeterminant.det
      ((LinearMap.fst R M N).prod
        ((LinearMap.snd R M N) + f.comp (LinearMap.fst R M N))) = 1 := by
  let i : N →ₗ[R] M × N := LinearMap.inr R M N
  let p : M × N →ₗ[R] N := f.comp (LinearMap.fst R M N)
  have hshear :
      ((LinearMap.fst R M N).prod
        ((LinearMap.snd R M N) + f.comp (LinearMap.fst R M N))) =
        LinearMap.id + i.comp p := by
    ext x <;> simp [i, p]
  rw [hshear, ProjectiveDeterminant.det_one_add_comp_comm i p]
  have hpi : p.comp i = 0 := by
    ext x
    simp [p, i]
  rw [hpi]
  simp only [add_zero]
  exact determinant_id

/-- A shear on a product of modules is bijective. -/
private theorem shear_bijective
    {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) :
    Function.Bijective ((LinearMap.fst R M N).prod
      ((LinearMap.snd R M N) + f.comp (LinearMap.fst R M N))) := by
  let t : M × N →ₗ[R] M × N := (LinearMap.fst R M N).prod
    ((LinearMap.snd R M N) + f.comp (LinearMap.fst R M N))
  let s : M × N →ₗ[R] M × N := (LinearMap.fst R M N).prod
    ((LinearMap.snd R M N) - f.comp (LinearMap.fst R M N))
  have hleft : Function.LeftInverse s t := fun x => Prod.ext rfl (by simp [t, s])
  have hright : Function.RightInverse s t := fun x => Prod.ext rfl (by simp [t, s])
  exact ⟨hleft.injective, hright.surjective⟩

/-- An endomorphism of a finite projective module acts on the determinant line by its
determinant. -/
private theorem map_eq_det_smul_id
    {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (f : M →ₗ[R] M) :
    ProjectiveDeterminant.map (fun _ => rfl) f = ProjectiveDeterminant.det f • LinearMap.id :=
  (Classical.choose_spec (ProjectiveDeterminant.existsUnique_scalar
    (ProjectiveDeterminant.map (fun _ => rfl) f))).1

private theorem determinantAnnihilatorEquiv_val
    {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (x : ProjectiveDeterminant.module (R := R) (M := M)) :
    ((TwoTermComplex.determinantAnnihilatorEquiv x :
      ↥(⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m)))) :
      ExteriorAlgebra R M) = x.1 := by
  simp [TwoTermComplex.determinantAnnihilatorEquiv]

private theorem determinantMap_val
    {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    (k : M →ₗ[R] M)
    (x : ProjectiveDeterminant.module (R := R) (M := M)) :
    ((ProjectiveDeterminant.map (fun _ => rfl) k x :
      ProjectiveDeterminant.module (R := R) (M := M)) : ExteriorAlgebra R M) =
      ExteriorAlgebra.map k x.1 := by
  rfl

private theorem determinantMapEquiv_annihilator_val
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (e : M ≃ₗ[R] N)
    (x : ProjectiveDeterminant.module (R := R) (M := M)) :
    ((TwoTermComplex.determinantAnnihilatorEquiv
      (ProjectiveDeterminant.mapEquiv e x) :
      ↥(⨅ n : N, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R n)))) :
      ExteriorAlgebra R N) =
    ExteriorAlgebra.map e
      ((TwoTermComplex.determinantAnnihilatorEquiv x :
        ↥(⨅ m : M, LinearMap.ker (LinearMap.mulLeft R (ExteriorAlgebra.ι R m)))) :
        ExteriorAlgebra R M) := by
  simp only [TwoTermComplex.determinantAnnihilatorEquiv]
  rfl

private theorem kernelDeterminantEquiv_val
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f)
    [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)]
    (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker f))
    (y : ProjectiveDeterminant.module (R := R) (M := N)) :
    let γ := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
      (LinearMap.ker f).subtype f (LinearMap.ker f).injective_subtype
      f.exact_subtype_ker_map hf).val
    ((TwoTermComplex.kernelDeterminantEquiv f hf (x ⊗ₜ[R] y) :
      ProjectiveDeterminant.module (R := R) (M := M)) : ExteriorAlgebra R M) =
    (γ (TwoTermComplex.determinantAnnihilatorEquiv x ⊗ₜ[R]
      TwoTermComplex.determinantAnnihilatorEquiv y) : ExteriorAlgebra R M) := by
  dsimp
  simp [TwoTermComplex.kernelDeterminantEquiv,
    TwoTermComplex.determinantAnnihilatorEquiv]

/-- Naturality of the determinant equivalence of a surjection under an automorphism
of its source that fixes the quotient. -/
private theorem kernelDeterminantEquiv_naturality_of_equiv
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (f g : M →ₗ[R] N) (hf : Function.Surjective f) (hg : Function.Surjective g)
    [Module.Finite R (LinearMap.ker f)] [Module.Projective R (LinearMap.ker f)]
    [Module.Finite R (LinearMap.ker g)] [Module.Projective R (LinearMap.ker g)]
    (k : M →ₗ[R] M) (e : LinearMap.ker g ≃ₗ[R] LinearMap.ker f)
    (hfg : f.comp k = g)
    (hek : ∀ x : LinearMap.ker g, (e x : M) = k x) :
    ∀ (x : ProjectiveDeterminant.module (R := R) (M := LinearMap.ker g))
      (y : ProjectiveDeterminant.module (R := R) (M := N)),
      ProjectiveDeterminant.map (fun _ => rfl) k
        (TwoTermComplex.kernelDeterminantEquiv g hg (x ⊗ₜ[R] y)) =
      TwoTermComplex.kernelDeterminantEquiv f hf
        (ProjectiveDeterminant.mapEquiv e x ⊗ₜ[R] y) := by
  let eg := TwoTermComplex.determinantAnnihilatorEquiv (R := R)
    (M := LinearMap.ker g)
  let ef := TwoTermComplex.determinantAnnihilatorEquiv (R := R)
    (M := LinearMap.ker f)
  let en := TwoTermComplex.determinantAnnihilatorEquiv (R := R) (M := N)
  let γg := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker g).subtype g (LinearMap.ker g).injective_subtype
      g.exact_subtype_ker_map hg).val
  let γf := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker f).subtype f (LinearMap.ker f).injective_subtype
      f.exact_subtype_ker_map hf).val
  intro x y
  obtain ⟨z, hz⟩ := (ExteriorAlgebra.map_surjective_iff.mpr hg)
    (en y : ExteriorAlgebra R N)
  have hval :
      ((ProjectiveDeterminant.map (fun _ => rfl) k
        (TwoTermComplex.kernelDeterminantEquiv g hg (x ⊗ₜ[R] y)) :
        ProjectiveDeterminant.module (R := R) (M := M)) : ExteriorAlgebra R M) =
      ((TwoTermComplex.kernelDeterminantEquiv f hf
        (ProjectiveDeterminant.mapEquiv e x ⊗ₜ[R] y) :
        ProjectiveDeterminant.module (R := R) (M := M)) : ExteriorAlgebra R M) := by
    rw [determinantMap_val, kernelDeterminantEquiv_val,
      kernelDeterminantEquiv_val]
    change ExteriorAlgebra.map k
        (γg (eg x ⊗ₜ[R] en y) : ExteriorAlgebra R M) =
      (γf (ef (ProjectiveDeterminant.mapEquiv e x) ⊗ₜ[R] en y) :
        ExteriorAlgebra R M)
    have hγg := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker g).subtype g (LinearMap.ker g).injective_subtype
      g.exact_subtype_ker_map hg).property (eg x) (en y) z hz
    have hγf := (ProjectiveDeterminant.determinantTensorDeterminantEquiv_of_exact
    (LinearMap.ker f).subtype f (LinearMap.ker f).injective_subtype
      f.exact_subtype_ker_map hf).property
      (ef (ProjectiveDeterminant.mapEquiv e x)) (en y)
      (ExteriorAlgebra.map k z) (by
        rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hfg, hz])
    rw [hγg, hγf, map_mul]
    congr 1
    change ExteriorAlgebra.map k
      (ExteriorAlgebra.map (LinearMap.ker g).subtype x.1) =
      ExteriorAlgebra.map (LinearMap.ker f).subtype
        (ExteriorAlgebra.map e x.1)
    have hlin : k.comp (LinearMap.ker g).subtype =
        (LinearMap.ker f).subtype.comp e.toLinearMap := by
      ext t
      exact (hek t).symm
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
      ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    rw [hlin]
  exact Subtype.ext hval

private theorem kernel_equiv_of_source_bijective
    {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (f g : M →ₗ[R] N) (k : M →ₗ[R] M)
    (hfg : f.comp k = g) (hk : Function.Bijective k) :
    ∃ e : LinearMap.ker g ≃ₗ[R] LinearMap.ker f,
      ∀ x : LinearMap.ker g, (e x : M) = k x := by
  let eMap : LinearMap.ker g →ₗ[R] LinearMap.ker f :=
    ((k.domRestrict (LinearMap.ker g)).codRestrict (LinearMap.ker f))
      (fun x => by
        rw [LinearMap.mem_ker]
        change f (k x.1) = 0
        rw [← LinearMap.comp_apply, hfg]
        exact x.2)
  have he : Function.Bijective eMap := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hk.1 (congrArg Subtype.val hxy))
    · intro x
      obtain ⟨y, hy⟩ := hk.2 x.1
      have hyg : y ∈ LinearMap.ker g := by
        rw [LinearMap.mem_ker, ← hfg]
        change f (k y) = 0
        rw [hy]
        exact x.2
      exact ⟨⟨y, hyg⟩, Subtype.ext hy⟩
  exact ⟨LinearEquiv.ofBijective eMap he, fun _ => rfl⟩

private theorem delta_naturality
    {R M M' N N' : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Projective R M]
    [AddCommGroup M'] [Module R M'] [Module.Finite R M'] [Module.Projective R M']
    [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    [AddCommGroup N'] [Module R N'] [Module.Finite R N'] [Module.Projective R N']
    (f : M →ₗ[R] N) (g : M' →ₗ[R] N')
    (hf : TwoTermComplex.IsRankZero f) (hg : TwoTermComplex.IsRankZero g)
    (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N)
    (hcomm : f.comp eM.toLinearMap = eN.toLinearMap.comp g)
    (x : ProjectiveDeterminant.module (R := R) (M := M')) :
    ProjectiveDeterminant.mapEquiv eN (TwoTermComplex.delta g hg x) =
      TwoTermComplex.delta f hf (ProjectiveDeterminant.mapEquiv eM x) := by
  apply Subtype.ext
  change ExteriorAlgebra.map eN.toLinearMap (ExteriorAlgebra.map g x.1) =
    ExteriorAlgebra.map f (ExteriorAlgebra.map eM.toLinearMap x.1)
  rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map,
    ← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map, hcomm]

private theorem homotopy_lift_identities
    {R : Type*} [CommRing R]
    {K₁ K₀ L₁ L₀ : Type*}
    [AddCommGroup K₁] [Module R K₁]
    [AddCommGroup K₀] [Module R K₀]
    [AddCommGroup L₁] [Module R L₁]
    [AddCommGroup L₀] [Module R L₀]
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀)
    (a : TwoTermComplex.Hom K L) (h : K₀ →ₗ[R] L₁)
    (hLift : K₀ →ₗ[R] K₁) (hh : a.neg.comp hLift = h) :
    let kneg : K₁ →ₗ[R] K₁ := LinearMap.id + hLift.comp K
    let kzero : K₀ →ₗ[R] K₀ := LinearMap.id + K.comp hLift
    a.neg.comp kneg = a.neg + h.comp K ∧
      a.zero.comp kzero = a.zero + L.comp h ∧
        kzero.comp K = K.comp kneg := by
  dsimp
  constructor
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply, map_add]
    simpa only [LinearMap.comp_apply] using
      congrArg (fun y : L₁ => a.neg x + y)
        (congrArg (fun f : K₀ →ₗ[R] L₁ => f (K x)) hh)
  constructor
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply, map_add]
    rw [show a.zero (K (hLift x)) = L (a.neg (hLift x)) from
      LinearMap.congr_fun a.comm (hLift x)]
    simpa only [LinearMap.comp_apply] using
      congrArg (fun y : L₀ => a.zero x + y)
        (congrArg (fun f : K₀ →ₗ[R] L₁ => L (f x)) hh)
  · ext x
    simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply, map_add]

/-- The morphism obtained from `a` by adding the homotopy `h`. -/
private def addHomotopy
    {R : Type*} [CommRing R]
    {K₁ K₀ L₁ L₀ : Type*}
    [AddCommGroup K₁] [Module R K₁]
    [AddCommGroup K₀] [Module R K₀]
    [AddCommGroup L₁] [Module R L₁]
    [AddCommGroup L₀] [Module R L₀]
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀) (a : TwoTermComplex.Hom K L) (h : K₀ →ₗ[R] L₁) :
    TwoTermComplex.Hom K L where
  neg := a.neg + h.comp K
  zero := a.zero + L.comp h
  comm := by
    ext x
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
    rw [show a.zero (K x) = L (a.neg x) from LinearMap.congr_fun a.comm x]

private theorem homotopic_isQuasiIso
    {R : Type*} [CommRing R]
    {K₁ K₀ L₁ L₀ : Type*}
    [AddCommGroup K₁] [Module R K₁]
    [AddCommGroup K₀] [Module R K₀]
    [AddCommGroup L₁] [Module R L₁]
    [AddCommGroup L₀] [Module R L₀]
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀) (a : TwoTermComplex.Hom K L)
    (hqa : a.IsQuasiIso) (h : K₀ →ₗ[R] L₁) :
    (addHomotopy K L a h).IsQuasiIso := by
  let b := addHomotopy K L a h
  have hminus : b.hMinus = a.hMinus := by
    ext x
    simp [b, addHomotopy, TwoTermComplex.Hom.hMinus]
  have hzero : b.hZero = a.hZero := by
    ext x
    change Submodule.Quotient.mk (b.zero x) = Submodule.Quotient.mk (a.zero x)
    rw [Submodule.Quotient.eq]
    refine ⟨h x, by simp [b, addHomotopy]⟩
  change b.IsQuasiIso
  rw [TwoTermComplex.Hom.IsQuasiIso, hminus, hzero]
  exact hqa

private theorem determinantEquiv_eq_of_source_bijective
    {R : Type*} [CommRing R]
    {K₁ K₀ L₁ L₀ : Type*}
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
    [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
    [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
    [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀)
    (a b : TwoTermComplex.Hom K L)
    (ha : a.IsDegreewiseSurjective) (hb : b.IsDegreewiseSurjective)
    (hqa : a.IsQuasiIso) (hqb : b.IsQuasiIso)
    (kn : K₁ →ₗ[R] K₁) (kz : K₀ →ₗ[R] K₀)
    (hkn : Function.Bijective kn) (hkz : Function.Bijective kz)
    (hK : kz.comp K = K.comp kn)
    (han : a.neg.comp kn = b.neg) (haz : a.zero.comp kz = b.zero)
    (hdet : ProjectiveDeterminant.det kn = ProjectiveDeterminant.det kz) :
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
    (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K L a ha hqa).equiv =
      (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K L b hb hqb).equiv := by
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
  let Da := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K L a ha hqa
  let Db := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K L b hb hqb
  obtain ⟨en, hen⟩ := kernel_equiv_of_source_bijective a.neg b.neg kn han hkn
  obtain ⟨ez, hez⟩ := kernel_equiv_of_source_bijective a.zero b.zero kz haz hkz
  have hcomm : a.kernelDifferential.comp en.toLinearMap =
      ez.toLinearMap.comp b.kernelDifferential := by
    ext x
    change K (en x).1 = (ez (b.kernelDifferential x)).1
    rw [hen x, hez (b.kernelDifferential x)]
    change K (kn x.1) = kz (K x.1)
    exact (LinearMap.congr_fun hK x.1).symm
  have hscalar (φ : TwoTermComplex.determinantLine K)
      (x : ProjectiveDeterminant.module (R := R) (M := K₁)) :
      φ (ProjectiveDeterminant.map (fun _ => rfl) kn x) =
        ProjectiveDeterminant.map (fun _ => rfl) kz (φ x) := by
    rw [map_eq_det_smul_id kn, map_eq_det_smul_id kz, hdet]
    simp
  apply Db.unique Da.equiv
  intro φ x y
  have hDa := Da.compatibility φ (ProjectiveDeterminant.mapEquiv en x) y
  have hn := kernelDeterminantEquiv_naturality_of_equiv
    a.neg b.neg ha.1 hb.1 kn en han hen x y
  have hz := kernelDeterminantEquiv_naturality_of_equiv
    a.zero b.zero ha.2 hb.2 kz ez haz hez
    (TwoTermComplex.delta b.kernelDifferential Db.kernelRankZero x) (Da.equiv φ y)
  have hd := delta_naturality a.kernelDifferential b.kernelDifferential
    Da.kernelRankZero Db.kernelRankZero en ez hcomm x
  apply (ProjectiveDeterminant.map_bijective (LinearEquiv.ofBijective kz hkz)).1
  calc
    ProjectiveDeterminant.map (fun _ => rfl) kz
        (TwoTermComplex.kernelDeterminantEquiv b.zero hb.2
          (TwoTermComplex.delta b.kernelDifferential Db.kernelRankZero x ⊗ₜ[R]
            Da.equiv φ y)) =
      TwoTermComplex.kernelDeterminantEquiv a.zero ha.2
        (ProjectiveDeterminant.mapEquiv ez
          (TwoTermComplex.delta b.kernelDifferential Db.kernelRankZero x) ⊗ₜ[R]
            Da.equiv φ y) := hz
    _ = φ (TwoTermComplex.kernelDeterminantEquiv a.neg ha.1
          (ProjectiveDeterminant.mapEquiv en x ⊗ₜ[R] y)) := by rw [hd]; exact hDa
    _ = φ (ProjectiveDeterminant.map (fun _ => rfl) kn
          (TwoTermComplex.kernelDeterminantEquiv b.neg hb.1 (x ⊗ₜ[R] y))) := by rw [hn]
    _ = ProjectiveDeterminant.map (fun _ => rfl) kz
          (φ (TwoTermComplex.kernelDeterminantEquiv b.neg hb.1 (x ⊗ₜ[R] y))) :=
        hscalar φ _

/-- A common section of the two maps in degree minus one makes the homotopy lift
surjective in both degrees. The quasi-isomorphism hypothesis identifies the kernel of
`a.zero` with the image of the differential on the kernel of `a.neg`. -/
private theorem homotopy_lift_surjective_of_common_section
    {R : Type*} [CommRing R]
    {K₁ K₀ L₁ L₀ : Type*}
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
    [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
    [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
    [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀) (a : TwoTermComplex.Hom K L)
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso)
    (h : K₀ →ₗ[R] L₁) (hbzero : Function.Surjective (a.zero + L.comp h))
    (s : L₁ →ₗ[R] K₁) (hs : a.neg.comp s = LinearMap.id)
    (hbs : Function.Surjective ((a.neg + h.comp K).comp s)) :
    Function.Surjective ((LinearMap.id : K₁ →ₗ[R] K₁) + (s.comp h).comp K) ∧
      Function.Surjective ((LinearMap.id : K₀ →ₗ[R] K₀) + K.comp (s.comp h)) := by
  let kneg : K₁ →ₗ[R] K₁ := LinearMap.id + (s.comp h).comp K
  let kzero : K₀ →ₗ[R] K₀ := LinearMap.id + K.comp (s.comp h)
  have hneg : Function.Surjective kneg := by
    intro x
    let z : K₁ := x - s (a.neg x)
    obtain ⟨y, hy⟩ := hbs (a.neg x - h (K z))
    refine ⟨z + s y, ?_⟩
    have hsy : kneg (s y) = s (((a.neg + h.comp K).comp s) y) := by
      simp only [kneg, LinearMap.comp_apply, LinearMap.add_apply,
        LinearMap.id_apply, map_add]
      rw [show a.neg (s y) = y from
        congrArg (fun f : L₁ →ₗ[R] L₁ => f y) hs]
    simp only [map_add, hsy]
    change z + s (h (K z)) + s (((a.neg + h.comp K).comp s) y) = x
    rw [hy, add_assoc, ← map_add]
    dsimp [z]
    abel_nf
  let : Module.Finite R (LinearMap.ker a.neg) :=
    TwoTermComplex.kernel_finite a.neg ha.1
  let : Module.Projective R (LinearMap.ker a.neg) :=
    TwoTermComplex.kernel_projective a.neg ha.1
  let : Module.Finite R (LinearMap.ker a.zero) :=
    TwoTermComplex.kernel_finite a.zero ha.2
  let : Module.Projective R (LinearMap.ker a.zero) :=
    TwoTermComplex.kernel_projective a.zero ha.2
  have hd : Function.Surjective a.kernelDifferential :=
    (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K L a ha hqa).kernelAcyclic.2
  obtain ⟨-, haz, hK⟩ := homotopy_lift_identities K L a h (s.comp h) (by
    rw [← LinearMap.comp_assoc, hs]
    simp)
  have hzero : Function.Surjective kzero := by
    intro x
    obtain ⟨y, hy⟩ := hbzero (a.zero x)
    have hk : x - kzero y ∈ LinearMap.ker a.zero := by
      rw [LinearMap.mem_ker]
      rw [map_sub, ← LinearMap.comp_apply, haz, hy, sub_self]
    obtain ⟨z, hz⟩ := hd ⟨x - kzero y, hk⟩
    obtain ⟨w, hw⟩ := hneg z
    refine ⟨y + K w, ?_⟩
    calc
      kzero (y + K w) = kzero y + K (kneg w) := by
        rw [map_add, ← LinearMap.comp_apply, hK, LinearMap.comp_apply]
      _ = kzero y + K z := by rw [hw]
      _ = x := by
        have hzval : K z = x - kzero y := congrArg Subtype.val hz
        rw [hzval]
        abel
  exact ⟨hneg, hzero⟩

/-- A common section gives isomorphisms of the two terms of the source complex. -/
private theorem homotopy_lift_bijective_of_common_section
    {R : Type*} [CommRing R]
    {K₁ K₀ L₁ L₀ : Type*}
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
    [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
    [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
    [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀) (a : TwoTermComplex.Hom K L)
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso)
    (h : K₀ →ₗ[R] L₁) (hbzero : Function.Surjective (a.zero + L.comp h))
    (s : L₁ →ₗ[R] K₁) (hs : a.neg.comp s = LinearMap.id)
    (hbs : Function.Surjective ((a.neg + h.comp K).comp s)) :
    Function.Bijective ((LinearMap.id : K₁ →ₗ[R] K₁) + (s.comp h).comp K) ∧
      Function.Bijective ((LinearMap.id : K₀ →ₗ[R] K₀) + K.comp (s.comp h)) := by
  obtain ⟨hn, hz⟩ := homotopy_lift_surjective_of_common_section K L a ha hqa h
    hbzero s hs hbs
  exact ⟨OrzechProperty.bijective_of_surjective_endomorphism _ hn,
    OrzechProperty.bijective_of_surjective_endomorphism _ hz⟩

private theorem determinantEquiv_eq_of_homotopic_surjections_of_common_section
    {R : Type*} [CommRing R]
    {K₁ K₀ L₁ L₀ : Type*}
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
    [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
    [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
    [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀)
    (a b : TwoTermComplex.Hom K L)
    (ha : a.IsDegreewiseSurjective) (hb : b.IsDegreewiseSurjective)
    (hqa : a.IsQuasiIso) (hqb : b.IsQuasiIso)
    (h : K₀ →ₗ[R] L₁)
    (hbn : b.neg = a.neg + h.comp K)
    (hbz : b.zero = a.zero + L.comp h)
    (s : L₁ →ₗ[R] K₁) (hs : a.neg.comp s = LinearMap.id)
    (hbs : Function.Surjective (b.neg.comp s)) :
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
    (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K L a ha hqa).equiv =
      (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K L b hb hqb).equiv := by
  let kn : K₁ →ₗ[R] K₁ := LinearMap.id + (s.comp h).comp K
  let kz : K₀ →ₗ[R] K₀ := LinearMap.id + K.comp (s.comp h)
  obtain ⟨hkn, hkz⟩ :=
    homotopy_lift_bijective_of_common_section K L a ha hqa h
      (by rw [← hbz]; exact hb.2) s hs (by rw [← hbn]; exact hbs)
  obtain ⟨han, haz, hK⟩ :=
    homotopy_lift_identities K L a h (s.comp h) (by
      rw [← LinearMap.comp_assoc, hs]
      simp)
  have hdet : ProjectiveDeterminant.det kn = ProjectiveDeterminant.det kz :=
    ProjectiveDeterminant.det_one_add_comp_comm (s.comp h) K
  exact determinantEquiv_eq_of_source_bijective K L a b ha hb hqa hqb kn kz
    hkn hkz hK (han.trans hbn.symm) (haz.trans hbz.symm) hdet

/-- Adding a contractible summand makes the homotopy into an isomorphism of source
complexes. This construction works without a common splitting of the two surjections. -/
private theorem stabilized_homotopy
    {R : Type*} [CommRing R]
    {K₁ K₀ L₁ L₀ : Type*}
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
    [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
    [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
    [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀)
    (a : TwoTermComplex.Hom K L) (h : K₀ →ₗ[R] L₁) :
    let KS : K₁ × L₁ →ₗ[R] K₀ × L₁ := K.prodMap LinearMap.id
    let Aneg : K₁ × L₁ →ₗ[R] L₁ := a.neg.coprod LinearMap.id
    let Azero : K₀ × L₁ →ₗ[R] L₀ := a.zero.coprod L
    let Bneg : K₁ × L₁ →ₗ[R] L₁ := (a.neg + h.comp K).coprod LinearMap.id
    let Bzero : K₀ × L₁ →ₗ[R] L₀ := (a.zero + L.comp h).coprod L
    ∃ Tneg : K₁ × L₁ →ₗ[R] K₁ × L₁,
      ∃ Tzero : K₀ × L₁ →ₗ[R] K₀ × L₁,
        Function.Bijective Tneg ∧ Function.Bijective Tzero ∧
          Tzero.comp KS = KS.comp Tneg ∧
          Aneg.comp Tneg = Bneg ∧ Azero.comp Tzero = Bzero ∧
          ProjectiveDeterminant.det Tneg = 1 ∧
          ProjectiveDeterminant.det Tzero = 1 := by
  dsimp
  let tn : K₁ × L₁ →ₗ[R] K₁ × L₁ :=
    (LinearMap.fst R K₁ L₁).prod
      ((LinearMap.snd R K₁ L₁) + (h.comp K).comp (LinearMap.fst R K₁ L₁))
  let tz : K₀ × L₁ →ₗ[R] K₀ × L₁ :=
    (LinearMap.fst R K₀ L₁).prod
      ((LinearMap.snd R K₀ L₁) + h.comp (LinearMap.fst R K₀ L₁))
  refine ⟨tn, tz, shear_bijective _, shear_bijective _, ?_, ?_, ?_, ?_, ?_⟩
  · ext x <;> simp [tn, tz, LinearMap.prodMap_apply]
  · ext x <;> simp [tn, LinearMap.comp_apply]
  · ext x <;> simp [tz, LinearMap.comp_apply]
  · exact determinant_shear (h.comp K)
  · exact determinant_shear h

/-- Projection away from a contractible summand induces isomorphisms on cohomology. -/
private theorem isQuasiIso_fst_prod_id
    {R K₁ K₀ T : Type*} [CommRing R]
    [AddCommGroup K₁] [Module R K₁]
    [AddCommGroup K₀] [Module R K₀]
    [AddCommGroup T] [Module R T]
    (K : K₁ →ₗ[R] K₀) :
    (show TwoTermComplex.Hom (K.prodMap (LinearMap.id : T →ₗ[R] T)) K from
      { neg := LinearMap.fst R K₁ T
        zero := LinearMap.fst R K₀ T
        comm := by ext x <;> rfl }).IsQuasiIso := by
  let KS := K.prodMap (LinearMap.id : T →ₗ[R] T)
  let p : TwoTermComplex.Hom KS K :=
    { neg := LinearMap.fst R K₁ T
      zero := LinearMap.fst R K₀ T
      comm := by ext x <;> rfl }
  change p.IsQuasiIso
  constructor
  · constructor
    · intro x y hxy
      exact Subtype.ext (Prod.ext (congrArg Subtype.val hxy)
        ((congrArg Prod.snd x.property).trans (congrArg Prod.snd y.property).symm))
    · intro x
      refine ⟨⟨(x.val, 0), ?_⟩, ?_⟩
      · change (K x.val, (0 : T)) = 0
        simp
      · rfl
  · constructor
    · intro x y hxy
      induction x using Submodule.Quotient.induction_on with | _ x =>
      induction y using Submodule.Quotient.induction_on with | _ y =>
      change Submodule.Quotient.mk x.1 = Submodule.Quotient.mk y.1 at hxy
      rw [Submodule.Quotient.eq] at hxy
      obtain ⟨z, hz⟩ := hxy
      rw [Submodule.Quotient.eq]
      exact ⟨(z, x.2 - y.2), Prod.ext hz rfl⟩
    · intro x
      induction x using Submodule.Quotient.induction_on with | _ x =>
      exact ⟨Submodule.Quotient.mk (x, (0 : T)), rfl⟩

/-- **Stacks 0FJK.** Homotopic degreewise-surjective quasi-isomorphisms between two-term
complexes of finite projective modules induce the same canonical equivalence of determinant
lines. -/
@[stacks 0FJK]
public theorem determinantEquiv_eq_of_homotopic_surjections
    {R : Type u} [CommRing R]
    {K₁ : Type v₁} {K₀ : Type v₀} {L₁ : Type w₁} {L₀ : Type w₀}
    [AddCommGroup K₁] [Module R K₁] [Module.Finite R K₁] [Module.Projective R K₁]
    [AddCommGroup K₀] [Module R K₀] [Module.Finite R K₀] [Module.Projective R K₀]
    [AddCommGroup L₁] [Module R L₁] [Module.Finite R L₁] [Module.Projective R L₁]
    [AddCommGroup L₀] [Module R L₀] [Module.Finite R L₀] [Module.Projective R L₀]
    (K : K₁ →ₗ[R] K₀) (L : L₁ →ₗ[R] L₀) (a : TwoTermComplex.Hom K L)
    (ha : a.IsDegreewiseSurjective) (hqa : a.IsQuasiIso) (h : K₀ →ₗ[R] L₁)
    (hbneg : Function.Surjective (a.neg + h.comp K))
    (hbzero : Function.Surjective (a.zero + L.comp h)) :
    let b : TwoTermComplex.Hom K L :=
      { neg := a.neg + h.comp K
        zero := a.zero + L.comp h
        comm
    := by
          ext x
          simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
          rw [show a.zero (K x) = L (a.neg x) from LinearMap.congr_fun a.comm x] }
    b.IsQuasiIso ∧ ∀ hqb : b.IsQuasiIso,
      letI : Module.Finite R (LinearMap.ker a.neg) :=
        TwoTermComplex.kernel_finite a.neg ha.1
      letI : Module.Projective R (LinearMap.ker a.neg) :=
        TwoTermComplex.kernel_projective a.neg ha.1
      letI : Module.Finite R (LinearMap.ker a.zero) :=
        TwoTermComplex.kernel_finite a.zero ha.2
      letI : Module.Projective R (LinearMap.ker a.zero) :=
        TwoTermComplex.kernel_projective a.zero ha.2
      letI : Module.Finite R (LinearMap.ker b.neg) :=
        TwoTermComplex.kernel_finite b.neg hbneg
      letI : Module.Projective R (LinearMap.ker b.neg) :=
        TwoTermComplex.kernel_projective b.neg hbneg
      letI : Module.Finite R (LinearMap.ker b.zero) :=
        TwoTermComplex.kernel_finite b.zero hbzero
      letI : Module.Projective R (LinearMap.ker b.zero) :=
        TwoTermComplex.kernel_projective b.zero hbzero
      let Da := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K L a ha hqa
      let Db := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K L b
        ⟨hbneg, hbzero⟩ hqb
      Da.equiv = Db.equiv := by
  let b := addHomotopy K L a h
  have hqb : b.IsQuasiIso := homotopic_isQuasiIso K L a hqa h
  refine ⟨hqb, ?_⟩
  intro hqb
  let hb : b.IsDegreewiseSurjective := ⟨hbneg, hbzero⟩
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
  let KS : K₁ × L₁ →ₗ[R] K₀ × L₁ := K.prodMap LinearMap.id
  let p : TwoTermComplex.Hom KS K :=
    { neg := LinearMap.fst R K₁ L₁
      zero := LinearMap.fst R K₀ L₁
      comm := by ext x <;> rfl }
  have hp : p.IsDegreewiseSurjective :=
    ⟨fun x => ⟨(x, 0), rfl⟩, fun x => ⟨(x, 0), rfl⟩⟩
  have hqp : p.IsQuasiIso := isQuasiIso_fst_prod_id K
  let q (s : L₁ →ₗ[R] K₁) : TwoTermComplex.Hom KS K :=
    { neg := p.neg + (s.comp (LinearMap.snd R K₀ L₁)).comp KS
      zero := p.zero + K.comp (s.comp (LinearMap.snd R K₀ L₁))
      comm := by
        ext x <;> simp [p, KS, LinearMap.prodMap_apply] }
  have hq (s : L₁ →ₗ[R] K₁) : (q s).IsDegreewiseSurjective := by
    constructor <;> intro x
    · exact ⟨(x, 0), by simp [q, p, KS, LinearMap.prodMap_apply]⟩
    · exact ⟨(x, 0), by simp [q, p]⟩
  have hqq (s : L₁ →ₗ[R] K₁) : (q s).IsQuasiIso :=
    homotopic_isQuasiIso KS K p hqp (s.comp (LinearMap.snd R K₀ L₁))
  let : Module.Finite R (LinearMap.ker p.neg) :=
    TwoTermComplex.kernel_finite p.neg hp.1
  let : Module.Projective R (LinearMap.ker p.neg) :=
    TwoTermComplex.kernel_projective p.neg hp.1
  let : Module.Finite R (LinearMap.ker p.zero) :=
    TwoTermComplex.kernel_finite p.zero hp.2
  let : Module.Projective R (LinearMap.ker p.zero) :=
    TwoTermComplex.kernel_projective p.zero hp.2
  let (s : L₁ →ₗ[R] K₁) : Module.Finite R (LinearMap.ker (q s).neg) :=
    TwoTermComplex.kernel_finite (q s).neg (hq s).1
  let (s : L₁ →ₗ[R] K₁) : Module.Projective R (LinearMap.ker (q s).neg) :=
    TwoTermComplex.kernel_projective (q s).neg (hq s).1
  let (s : L₁ →ₗ[R] K₁) : Module.Finite R (LinearMap.ker (q s).zero) :=
    TwoTermComplex.kernel_finite (q s).zero (hq s).2
  let (s : L₁ →ₗ[R] K₁) : Module.Projective R (LinearMap.ker (q s).zero) :=
    TwoTermComplex.kernel_projective (q s).zero (hq s).2
  let Dp := TwoTermComplex.determinantEquivOfSurjectiveQuasiIso KS K p hp hqp
  have hDq (s : L₁ →ₗ[R] K₁) : Dp.equiv =
      (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso KS K (q s) (hq s)
        (hqq s)).equiv := by
    apply determinantEquiv_eq_of_homotopic_surjections_of_common_section
      KS K p (q s) hp (hq s) hqp (hqq s)
      (s.comp (LinearMap.snd R K₀ L₁)) rfl rfl
      (LinearMap.inl R K₁ L₁)
    · ext x
      rfl
    · intro x
      exact ⟨x, by simp [q, p, KS, LinearMap.prodMap_apply]⟩
  obtain ⟨sa, hsa⟩ := Module.projective_lifting_property a.neg LinearMap.id ha.1
  obtain ⟨sb, hsb⟩ := Module.projective_lifting_property b.neg LinearMap.id hb.1
  let C (c : TwoTermComplex.Hom K L) (s : L₁ →ₗ[R] K₁) : TwoTermComplex.Hom KS L :=
    { neg := c.neg.comp (q s).neg
      zero := c.zero.comp (q s).zero
      comm := by rw [LinearMap.comp_assoc, (q s).comm, ← LinearMap.comp_assoc,
        c.comm, LinearMap.comp_assoc] }
  let A := C a sa
  let B := C b sb
  have hA : A.IsDegreewiseSurjective :=
    ⟨ha.1.comp (hq sa).1, ha.2.comp (hq sa).2⟩
  have hB : B.IsDegreewiseSurjective :=
    ⟨hb.1.comp (hq sb).1, hb.2.comp (hq sb).2⟩
  obtain ⟨hqA, hcA⟩ :=
    determinantEquivOfSurjectiveQuasiIso_comp KS K L (q sa) a
      (hq sa) (hqq sa) ha hqa
  obtain ⟨hqB, hcB⟩ :=
    determinantEquivOfSurjectiveQuasiIso_comp KS K L (q sb) b
      (hq sb) (hqq sb) hb hqb
  let : Module.Finite R (LinearMap.ker A.neg) :=
    TwoTermComplex.kernel_finite A.neg hA.1
  let : Module.Projective R (LinearMap.ker A.neg) :=
    TwoTermComplex.kernel_projective A.neg hA.1
  let : Module.Finite R (LinearMap.ker A.zero) :=
    TwoTermComplex.kernel_finite A.zero hA.2
  let : Module.Projective R (LinearMap.ker A.zero) :=
    TwoTermComplex.kernel_projective A.zero hA.2
  let : Module.Finite R (LinearMap.ker B.neg) :=
    TwoTermComplex.kernel_finite B.neg hB.1
  let : Module.Projective R (LinearMap.ker B.neg) :=
    TwoTermComplex.kernel_projective B.neg hB.1
  let : Module.Finite R (LinearMap.ker B.zero) :=
    TwoTermComplex.kernel_finite B.zero hB.2
  let : Module.Projective R (LinearMap.ker B.zero) :=
    TwoTermComplex.kernel_projective B.zero hB.2
  have hCn (c : TwoTermComplex.Hom K L) (s : L₁ →ₗ[R] K₁) (hs : c.neg.comp s = LinearMap.id) :
      (C c s).neg = c.neg.coprod LinearMap.id := LinearMap.ext fun x =>
    (map_add c.neg x.1 (s x.2)).trans (congrArg (c.neg x.1 + ·) (LinearMap.congr_fun hs x.2))
  have hCz (c : TwoTermComplex.Hom K L) (s : L₁ →ₗ[R] K₁) (hs : c.neg.comp s = LinearMap.id) :
      (C c s).zero = c.zero.coprod L := LinearMap.ext fun x =>
    (map_add c.zero x.1 (K (s x.2))).trans <| congrArg (c.zero x.1 + ·) <|
      (LinearMap.congr_fun c.comm (s x.2)).trans (congrArg L (LinearMap.congr_fun hs x.2))
  obtain ⟨tn, tz, htn, htz, hcomm, hneg, hzero, hdetn, hdetz⟩ :=
    stabilized_homotopy K L a h
  have hDAB := determinantEquiv_eq_of_source_bijective KS L A B hA hB hqA hqB
    tn tz htn htz hcomm
    (by rw [hCn a sa hsa, hCn b sb hsb]; exact hneg)
    (by rw [hCz a sa hsa, hCz b sb hsb]; exact hzero)
    (hdetn.trans hdetz.symm)
  have hcomp : Dp.equiv.trans
      (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K L a ha hqa).equiv =
      Dp.equiv.trans
      (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso K L b hb hqb).equiv := by
    calc
      _ = (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso KS L A hA hqA).equiv := by
        rw [hDq sa]
        exact hcA
      _ = (TwoTermComplex.determinantEquivOfSurjectiveQuasiIso KS L B hB hqB).equiv := hDAB
      _ = _ := by
        rw [hDq sb]
        exact hcB.symm
  apply LinearEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := Dp.equiv.surjective x
  exact congrArg (fun e => e y) hcomp

end

end TwoTermComplex
