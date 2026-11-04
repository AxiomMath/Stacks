module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.Etale.Field
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.RootsOfUnityModuleSliceConstant
import StacksCore.Tactic.EgaSgaAttribute

/-!
# `μ_N` is locally constant on a scheme over a field in which `N` is invertible

Let `X` be a scheme over a field `k` with `N ≠ 0` in `k`. The cyclotomic field `k' = k(ζ_N)` is a
finite separable extension of `k`. So for every étale `X`-scheme `U` the base change
`U_{k'} = U ×_k k'` is étale over `U` and surjects onto it. It carries the primitive `N`-th root
of unity `ζ_N ∈ k'`, so `μ_N` is constant on `U_{k'}`
(`Stacks.Kummer.isConstant_overPullback_rootsOfUnityModule`). Hence `μ_N` is a locally
constant sheaf of `ℤ/N`-modules.

## Main definitions

* `Stacks.Kummer.cyclotomicBaseChange`: the étale `X`-scheme `U ×_k k(ζ_N)` over `U`.
* `Stacks.Kummer.cyclotomicBaseChangeStructMap`: its structure map `k(ζ_N) → Γ(U_{k(ζ_N)}, 𝒪)`.

## Main results

* `Stacks.Kummer.isLocallyConstant_rootsOfUnityModule`: `μ_N` is locally constant.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u v

namespace Stacks.Kummer

variable {X : Scheme.{u}} {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) (N : ℕ) [NeZero N]
  [NeZero (N : k)]

/-- `Spec k(ζ_N) ⟶ Spec k` is étale: the cyclotomic extension is finite and separable. -/
instance etale_spec_cyclotomicField :
    Etale (Spec.map (CommRingCat.ofHom (algebraMap k (CyclotomicField N k)))) := by
  have : Algebra.IsSeparable k (CyclotomicField N k) := IsCyclotomicExtension.isSeparable {N} k _
  have : FiniteDimensional k (CyclotomicField N k) :=
    IsCyclotomicExtension.finiteDimensional {N} k _
  have : Algebra.FormallyEtale k (CyclotomicField N k) := Algebra.FormallyEtale.of_isSeparable k _
  have : Algebra.FinitePresentation k (CyclotomicField N k) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  have he : Algebra.Etale k (CyclotomicField N k) := ⟨inferInstance, inferInstance⟩
  exact HasRingHomProperty.Spec_iff.mpr
    ((RingHom.etale_algebraMap (R := k) (S := CyclotomicField N k)).mpr he)

/-- The base change `U ×_k k(ζ_N)` of an étale `X`-scheme, as an étale `X`-scheme. -/
def cyclotomicBaseChange (U : X.Etale) : X.Etale :=
  Scheme.Etale.mk (pullback.fst (U.hom ≫ f)
    (Spec.map (CommRingCat.ofHom (algebraMap k (CyclotomicField N k)))) ≫ U.hom)

/-- The projection `U ×_k k(ζ_N) ⟶ U`. -/
def cyclotomicBaseChangeπ (U : X.Etale) : cyclotomicBaseChange f N U ⟶ U :=
  MorphismProperty.Over.homMk (pullback.fst _ _) rfl

/-- The structure map `k(ζ_N) → Γ(U ×_k k(ζ_N), 𝒪)`. -/
def cyclotomicBaseChangeStructMap (U : X.Etale) :
    CyclotomicField N k →+* Γ((cyclotomicBaseChange f N U).left, ⊤) :=
  ((Scheme.ΓSpecIso (.of (CyclotomicField N k))).inv ≫
    (pullback.snd (U.hom ≫ f)
      (Spec.map (CommRingCat.ofHom (algebraMap k (CyclotomicField N k))))).appTop).hom

/-- `U ×_k k(ζ_N) ⟶ U` is surjective. -/
theorem range_cyclotomicBaseChangeπ (U : X.Etale) :
    Set.range (cyclotomicBaseChangeπ f N U).left = Set.univ := by
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k (CyclotomicField N k)))) :=
    ⟨fun x => ⟨default, Subsingleton.elim _ _⟩⟩
  exact Set.range_eq_univ.2 (pullback.fst (U.hom ≫ f) _).surjective

include f in
/-- **`μ_N` is a locally constant sheaf of `ℤ/N`-modules** on the small étale site of a scheme over
a field in which `N` is invertible: it is constant on the étale covering `U ×_k k(ζ_N) ⟶ U` of
every étale `X`-scheme `U`. -/
@[sga "4 XIX 3.3" "partial", sga "4 XVI 3.10" "Remark 3.10 a)"]
theorem isLocallyConstant_rootsOfUnityModule
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U)
      (ModuleCat.{max (u + 1) v} (ZMod N))] :
    Stacks.ConstantSheaf.IsLocallyConstant X.smallEtaleTopology
      (rootsOfUnityModule.{u, v} X N) where
  exists_cover U := by
    refine ⟨PUnit, fun _ => cyclotomicBaseChange f N U, fun _ => cyclotomicBaseChangeπ f N U,
      ?_, fun _ => ?_⟩
    · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
      exact Set.eq_univ_of_forall fun p => Set.mem_iUnion.2 ⟨PUnit.unit, by
        rw [range_cyclotomicBaseChangeπ]; trivial⟩
    · exact isConstant_overPullback_rootsOfUnityModule.{u, v} _
        (cyclotomicBaseChangeStructMap f N U) (IsCyclotomicExtension.zeta_spec N k _)

end Stacks.Kummer

end
