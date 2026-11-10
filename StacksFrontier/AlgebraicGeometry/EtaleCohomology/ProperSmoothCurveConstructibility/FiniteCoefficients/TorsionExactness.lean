module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Field.ZMod

/-!
# Functors of torsion modules factoring through abelian groups are exact

Let `ℓ` be a prime. A short exact sequence of abelian groups killed by `ℓ` is a short exact
sequence of `𝔽_ℓ`-vector spaces, hence splits. So an additive functor out of abelian groups
carries it to a short exact sequence, and so does every functor `Φ` out of `Λ`-modules whose
composite with a faithful exact functor factors, up to isomorphism, through the underlying
abelian groups. This is the step of [Stacks, Tag 0GKW] where a finite `Λ`-module killed by a
prime is presented by finite free `Λ/ℓΛ`-modules: `M ↦ R^q f_* M̲` is exact on modules killed by
`ℓ`, because its underlying abelian sheaf only depends on the underlying abelian group.

## Main results

* `Stacks.EtaleCohomology.FiniteCoefficients.splitting_of_nsmul_eq_zero`: a short exact sequence
  of abelian groups whose middle term is killed by a prime splits.
* `Stacks.EtaleCohomology.FiniteCoefficients.shortExact_map_of_nsmul_eq_zero`: the exactness of
  `Φ` on short exact sequences of `Λ`-modules killed by `ℓ`.

## References

* [Stacks Project, Tag 0GKW](https://stacks.math.columbia.edu/tag/0GKW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v w

namespace Stacks.EtaleCohomology.FiniteCoefficients

/-- **A short exact sequence of abelian groups whose middle term is killed by a prime `ℓ`
splits**: it is a short exact sequence of `𝔽_ℓ`-vector spaces, and an injection of vector spaces
has a linear retraction. -/
def splitting_of_nsmul_eq_zero (ℓ : ℕ) [Fact ℓ.Prime] {T : ShortComplex AddCommGrpCat.{w}}
    (hT : T.ShortExact) (h : ∀ x : T.X₂, ℓ • x = 0) : T.Splitting :=
  have hf : Function.Injective T.f.hom := (AddCommGrpCat.mono_iff_injective T.f).1 hT.mono_f
  have h₁ : ∀ y : T.X₁, ℓ • y = 0 := fun y ↦ hf (by rw [map_nsmul, h, map_zero])
  letI : Module (ZMod ℓ) T.X₁ := AddCommGroup.zmodModule h₁
  letI : Module (ZMod ℓ) T.X₂ := AddCommGroup.zmodModule h
  have hr := (T.f.hom.toZModLinearMap ℓ).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 hf)
  ShortComplex.Splitting.ofExactOfRetraction T hT.exact
    (AddCommGrpCat.ofHom hr.choose.toAddMonoidHom)
    (by
      ext y
      exact LinearMap.congr_fun hr.choose_spec y)
    hT.epi_g

variable {Λ : Type v} [Ring Λ] {D E : Type*} [Category D] [Abelian D] [Category E] [Abelian E]

/-- **A functor of `Λ`-modules whose underlying values only depend on the underlying abelian
groups is exact on modules killed by a prime.** Let `Φ` be a functor out of `Λ`-modules and `F` a
faithful exact functor such that `Φ ⋙ F` is, up to isomorphism, an additive functor `Ψ` of the
underlying abelian groups. Then `Φ` carries every short exact sequence of `Λ`-modules whose middle
term is killed by a prime `ℓ` to a short exact sequence: the underlying sequence of abelian
groups splits (`splitting_of_nsmul_eq_zero`), so `Ψ` carries it to a split, hence short exact,
sequence, and `F` reflects short exactness. -/
theorem shortExact_map_of_nsmul_eq_zero (Φ : ModuleCat.{max v w} Λ ⥤ E) [Φ.PreservesZeroMorphisms]
    (F : E ⥤ D) [F.Additive] [F.Faithful] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (Ψ : AddCommGrpCat.{max v w} ⥤ D) [Ψ.Additive]
    (e : Φ ⋙ F ≅ forget₂ (ModuleCat.{max v w} Λ) AddCommGrpCat.{max v w} ⋙ Ψ)
    (ℓ : ℕ) [Fact ℓ.Prime] {S : ShortComplex (ModuleCat.{max v w} Λ)} (hS : S.ShortExact)
    (h : ∀ x : S.X₂, ℓ • x = 0) : (S.map Φ).ShortExact := by
  have hT : (S.map (forget₂ (ModuleCat.{max v w} Λ) AddCommGrpCat.{max v w})).ShortExact :=
    hS.map_of_exact _
  have hF : ((S.map Φ).map F).ShortExact :=
    ShortComplex.shortExact_of_iso (S.mapNatIso e).symm
      ((splitting_of_nsmul_eq_zero ℓ hT h).map Ψ).shortExact
  exact
    { exact := ((S.map Φ).exact_map_iff_of_faithful F).1 hF.exact
      mono_f := F.mono_of_mono_map hF.mono_f
      epi_g := F.epi_of_epi_map hF.epi_g }

section Presentation

variable {Λ : Type v} [CommRing Λ] {E : Type*} [Category E] [Abelian E]

/-- The finite free `Λ/ℓΛ`-module of rank `k`, as a `Λ`-module. -/
abbrev freeQuotient (ℓ : ℕ) (k : ℕ) : ModuleCat.{v} Λ :=
  ModuleCat.of Λ (Fin k → Λ ⧸ Ideal.span {(ℓ : Λ)})

/-- The module `freeQuotient ℓ k` is killed by `ℓ`. -/
theorem nsmul_freeQuotient (ℓ k : ℕ) (x : freeQuotient (Λ := Λ) ℓ k) : ℓ • x = 0 := by
  funext i
  change ℓ • x i = 0
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (x i)
  rw [← ha, ← map_nsmul, nsmul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

/-- Every finite `Λ`-module killed by `ℓ` is a quotient of a finite free `Λ/ℓΛ`-module. -/
theorem exists_surjective_freeQuotient (ℓ : ℕ) (M : Type v) [AddCommGroup M] [Module Λ M]
    [Module.Finite Λ M] (h : ∀ x : M, ℓ • x = 0) :
    ∃ (k : ℕ) (p : (Fin k → Λ ⧸ Ideal.span {(ℓ : Λ)}) →ₗ[Λ] M), Function.Surjective p := by
  obtain ⟨k, m, hm⟩ := Module.Finite.exists_fin (R := Λ) (M := M)
  have hle (i : Fin k) :
      Ideal.span {(ℓ : Λ)} ≤ LinearMap.ker (LinearMap.toSpanSingleton Λ M (m i)) := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change (ℓ : Λ) • m i = 0
    rw [Nat.cast_smul_eq_nsmul, h]
  let φ (i : Fin k) : (Λ ⧸ Ideal.span {(ℓ : Λ)}) →ₗ[Λ] M :=
    Submodule.liftQ _ (LinearMap.toSpanSingleton Λ M (m i)) (hle i)
  refine ⟨k, ∑ i, (φ i).comp (LinearMap.proj i), fun x ↦ ?_⟩
  have hx : x ∈ Submodule.span Λ (Set.range m) := by rw [hm]; trivial
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun Λ).1 hx
  refine ⟨fun i ↦ Ideal.Quotient.mk _ (c i), ?_⟩
  simp [φ, LinearMap.sum_apply]
  rfl

variable (Φ : ModuleCat.{v} Λ ⥤ E) [Φ.Additive] (P : ObjectProperty E) [P.IsWeakSerreClass]
  (ℓ : ℕ)
  (hΦ : ∀ {S : ShortComplex (ModuleCat.{v} Λ)}, S.ShortExact → (∀ x : S.X₂, ℓ • x = 0) →
    (S.map Φ).ShortExact)

include hΦ

/-- If `Φ` is exact on short exact sequences of modules killed by `ℓ` and `Φ(Λ/ℓΛ)` lies in a weak
Serre class, so does `Φ` of every finite free `Λ/ℓΛ`-module. -/
theorem prop_map_freeQuotient (h₁ : P (Φ.obj (ModuleCat.of Λ (Λ ⧸ Ideal.span {(ℓ : Λ)}))))
    (k : ℕ) : P (Φ.obj (freeQuotient ℓ k)) := by
  induction k with
  | zero =>
    refine P.prop_of_isZero (Φ.map_isZero ?_)
    rw [ModuleCat.isZero_iff_subsingleton]
    exact inferInstanceAs (Subsingleton (Fin 0 → _))
  | succ k ih =>
    let π : (Fin (k + 1) → Λ ⧸ Ideal.span {(ℓ : Λ)}) →ₗ[Λ] (Fin k → Λ ⧸ Ideal.span {(ℓ : Λ)}) :=
      LinearMap.funLeft Λ _ Fin.succ
    have hπ : Function.Surjective π := LinearMap.funLeft_surjective_of_injective _ _ _
      (Fin.succ_injective k)
    have hS := LinearMap.shortExact_shortComplexKer hπ
    have hSΦ := hΦ hS (nsmul_freeQuotient ℓ (k + 1))
    refine P.prop_X₂_of_shortExact hSΦ ?_ ih
    -- the kernel of `π` is `Λ/ℓΛ`, placed in the coordinate `0`
    let e : (Λ ⧸ Ideal.span {(ℓ : Λ)}) ≃ₗ[Λ] LinearMap.ker π :=
      { toFun := fun a ↦ ⟨Pi.single 0 a, by
          funext i
          simp [π, LinearMap.funLeft, (Fin.succ_ne_zero i)]⟩
        invFun := fun x ↦ x.1 0
        map_add' := fun a b ↦ by ext1; simp [Pi.single_add]
        map_smul' := fun c a ↦ by ext1; simp [Pi.single_smul']
        left_inv := fun a ↦ by simp
        right_inv := fun x ↦ by
          ext1
          funext i
          refine Fin.cases ?_ (fun j ↦ ?_) i
          · simp
          · have : x.1 j.succ = 0 := congr_fun x.2 j
            simp [Fin.succ_ne_zero, this] }
    exact P.prop_of_iso (Φ.mapIso e.toModuleIso) h₁

/-- **Reduction to `Λ/ℓΛ`.** Let `Λ` be a Noetherian ring and `ℓ` a natural number. If `Φ` is exact
on short exact sequences of modules killed by `ℓ` and `Φ(Λ/ℓΛ)` lies in a weak Serre class `P`,
then `Φ(M)` lies in `P` for every finite `Λ`-module `M` killed by `ℓ`: present `M` as
`(Λ/ℓΛ)^a → (Λ/ℓΛ)^b → M → 0`, then `Φ(M)` is the cokernel of `Φ((Λ/ℓΛ)^a) → Φ((Λ/ℓΛ)^b)`. -/
theorem prop_map_of_nsmul_eq_zero [IsNoetherianRing Λ]
    (h₁ : P (Φ.obj (ModuleCat.of Λ (Λ ⧸ Ideal.span {(ℓ : Λ)}))))
    (M : ModuleCat.{v} Λ) [Module.Finite Λ M] (h : ∀ x : M, ℓ • x = 0) : P (Φ.obj M) := by
  obtain ⟨k, p, hp⟩ := exists_surjective_freeQuotient (Λ := Λ) ℓ M h
  have hK : ∀ x : LinearMap.ker p, ℓ • x = 0 := fun x ↦ by
    ext1
    exact nsmul_freeQuotient ℓ k x.1
  obtain ⟨k', q, hq⟩ := exists_surjective_freeQuotient (Λ := Λ) ℓ (LinearMap.ker p) hK
  have hS₁ := hΦ (LinearMap.shortExact_shortComplexKer hp) (nsmul_freeQuotient ℓ k)
  have hS₂ := hΦ (LinearMap.shortExact_shortComplexKer hq) (nsmul_freeQuotient ℓ k')
  have : Epi (Φ.map (ModuleCat.ofHom q)) := hS₂.epi_g
  let c := isCokernelEpiComp hS₁.gIsCokernel (Φ.map (ModuleCat.ofHom q))
    (h := Φ.map (ModuleCat.ofHom q) ≫ Φ.map (ModuleCat.ofHom (LinearMap.ker p).subtype)) rfl
  exact P.prop_of_iso (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) c)
    (P.prop_cokernel _ (prop_map_freeQuotient Φ P ℓ hΦ h₁ k')
      (prop_map_freeQuotient Φ P ℓ hΦ h₁ k))

end Presentation

end Stacks.EtaleCohomology.FiniteCoefficients

end
