module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleSectionsBaseChange
import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.Properties.LocallyProjective
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Projective
public import StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibresProd
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.AffineSections

/-!
# Local projectivity descends along fpqc coverings

A quasi-coherent module on a scheme is locally projective as soon as its pullback to every
member of an fpqc covering is locally projective.

## Main results

* `AlgebraicGeometry.isLocallyProjective_of_pullback_fpqc`: local projectivity of a
  quasi-coherent module descends along an fpqc covering.

## Implementation notes

An fpqc covering is expressed as membership of its family of arrows in
`AlgebraicGeometry.Scheme.fpqcPrecoverage`, pullback of modules is
`AlgebraicGeometry.Scheme.Modules.pullback`, and local projectivity is the predicate of
Tag 05JP.

Over an affine open `U` of the base, quasi-compactness of the covering produces finitely many
affine opens of its members whose images cover `U`. Their product ring is faithfully flat over
`Γ(X, U)`, because each factor is flat and every prime of `Γ(X, U)` lifts to some factor, and
the base change of `Γ(F, U)` to the product ring is the product of the base changes, hence
projective. Projectivity then descends along the faithfully flat extension.

## References

* [Stacks Project, Tag 05JZ](https://stacks.math.columbia.edu/tag/05JZ)
-/

@[expose] public section

open CategoryTheory
open scoped DirectSum TensorProduct

universe u v

namespace AlgebraicGeometry

/-- A quasi-compact fpqc family refines an affine open of the base by finitely many affine
opens of its members. -/
private lemma fpqc_affine_refinement {X : Scheme.{u}} {I : Type v}
    (X' : I → Scheme.{u}) (f : ∀ i, X' i ⟶ X)
    (hfpqc : Presieve.ofArrows X' f ∈ Scheme.fpqcPrecoverage X)
    (U : X.Opens) (hU : IsAffineOpen U) :
    ∃ (n : ℕ) (idx : Fin n → I) (V : ∀ j, (X' (idx j)).Opens),
      (∀ j, IsAffineOpen (V j)) ∧
      (⋃ j, f (idx j) '' (V j : Set (X' (idx j)))) = U := by
  let 𝒰 : PreZeroHypercover X := ⟨I, X', f⟩
  have hqc : QuasiCompactCover 𝒰 := by
    change (Presieve.ofArrows X' f ∈ Scheme.qcPrecoverage X) ∧ _ at hfpqc
    exact Scheme.presieve₀_mem_qcPrecoverage_iff.mp hfpqc.1
  exact QuasiCompactCover.exists_isAffineOpen_of_isCompact 𝒰 hU.isCompact

/-- A finite product of flat algebras over `R` in which every prime of `R` is in the image of
some factor is faithfully flat over `R`. -/
@[sga "3 VIB 11.9.1" "partial"]
private theorem faithfullyFlat_pi_of_prime_lifts {R : Type*} [CommRing R] {ι : Type*}
    [Finite ι] (S : ι → Type*) [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (hflat : ∀ i, Module.Flat R (S i))
    (hlift : ∀ p : PrimeSpectrum R,
      ∃ i, ∃ q : PrimeSpectrum (S i),
        PrimeSpectrum.comap (algebraMap R (S i)) q = p) :
    (algebraMap R (∀ i, S i)).FaithfullyFlat := by
  have _ := Fintype.ofFinite ι
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  constructor
  · exact RingHom.flat_algebraMap_iff.mpr <|
      Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype R ι S).symm
  · intro p
    obtain ⟨i, q, hq⟩ := hlift p
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom S i) q, ?_⟩
    change PrimeSpectrum.comap ((Pi.evalRingHom S i).comp (algebraMap R (∀ i, S i))) q = p
    rw [show (Pi.evalRingHom S i).comp (algebraMap R (∀ i, S i)) = algebraMap R (S i) from
      RingHom.ext fun _ => rfl]
    exact hq

/-- A finite product of modules, each projective over its own factor, is projective over the
product ring. -/
private theorem projective_pi_of_components {ι : Type*} [Finite ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module (S i) (M i)]
    (hprojective : ∀ i, Module.Projective (S i) (M i)) :
    Module.Projective (∀ i, S i) (∀ i, M i) := by
  classical
  have _ := Fintype.ofFinite ι
  let R := ∀ i, S i
  let : ∀ i, Algebra R (S i) := fun i => (Pi.evalRingHom S i).toAlgebra
  let : ∀ i, Module R (M i) := fun i => Module.compHom (M i) (algebraMap R (S i))
  have hcomponent (i : ι) : Module.Projective R (M i) := by
    have : IsScalarTower R (S i) (M i) := .of_algebraMap_smul fun _ _ => rfl
    have : Module.Projective R (S i) := by
      let inc : (S i) →ₗ[R] R :=
        { toFun := Pi.single i
          map_add' := Pi.single_add i
          map_smul' := Pi.single_smul i }
      let ev : R →ₗ[R] S i :=
        { toFun := fun x => x i
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      exact Module.Projective.of_split inc ev (LinearMap.ext fun x => Pi.single_eq_same i x)
    have : Module.Projective (S i) (M i) := hprojective i
    exact Module.Projective.trans R (S i) (M i)
  exact Module.Projective.of_equiv' (DirectSum.linearEquivFunOnFintype R ι M)

/-- Base change to a finite product of algebras is projective as soon as each factorwise base
change is. -/
private theorem projective_tensorProduct_pi {R : Type*} [CommRing R] {ι : Type*}
    [Finite ι] (S : ι → Type*) [∀ i, CommRing (S i)]
    [∀ i, Algebra R (S i)] (M : Type*) [AddCommGroup M] [Module R M]
    (h : ∀ i, Module.Projective (S i) (S i ⊗[R] M)) :
    Module.Projective (∀ i, S i) ((∀ i, S i) ⊗[R] M) := by
  classical
  have _ := Fintype.ofFinite ι
  let T := ∀ i, S i
  let : Algebra R T := Pi.algebra (ι := ι) (R := R) S
  let : ∀ i, Algebra T (S i) := fun i => (Pi.evalRingHom S i).toAlgebra
  let : ∀ i, Module T (S i ⊗[R] M) := fun i => Module.compHom _ (algebraMap T (S i))
  let e : (T ⊗[R] M) ≃ₗ[R] (∀ i, S i ⊗[R] M) :=
    (TensorProduct.comm R T M).trans ((TensorProduct.piRight R R M S).trans
      (LinearEquiv.piCongrRight fun i => TensorProduct.comm R M (S i)))
  have hsmul (a : T) (x : T ⊗[R] M) : e (a • x) = a • e x := by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp [map_add, hx, hy]
    | tmul s m =>
      ext i
      change TensorProduct.comm R M (S i)
          (TensorProduct.piRight R R M S (m ⊗ₜ[R] (a * s)) i) =
        algebraMap T (S i) a • TensorProduct.comm R M (S i)
          (TensorProduct.piRight R R M S (m ⊗ₜ[R] s) i)
      simp only [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul,
        TensorProduct.comm_tmul]
      change (a i * s i) ⊗ₜ[R] m = (algebraMap T (S i) a * s i) ⊗ₜ[R] m
      rw [show algebraMap T (S i) a = a i from rfl]
  let eT : (T ⊗[R] M) ≃ₗ[T] (∀ i, S i ⊗[R] M) := { e with map_smul' := hsmul }
  have : Module.Projective T (∀ i, S i ⊗[R] M) :=
    projective_pi_of_components S (fun i => S i ⊗[R] M) h
  exact Module.Projective.of_equiv' eT.symm

/-- Every prime of the ring of functions on an affine open lifts to one of finitely many
affine opens of a covering family whose images cover it. -/
private lemma affineRefinement_prime_lifts {X : Scheme.{u}} {I : Type v}
    (X' : I → Scheme.{u}) (f : ∀ i, X' i ⟶ X) (U : X.Opens)
    (hU : IsAffineOpen U) (n : ℕ) (idx : Fin n → I)
    (V : ∀ j, (X' (idx j)).Opens) (hV : ∀ j, IsAffineOpen (V j))
    (hVU : ∀ j, V j ≤ (f (idx j)) ⁻¹ᵁ U)
    (hcover : (⋃ j, f (idx j) '' (V j : Set (X' (idx j)))) = U) :
    ∀ p : PrimeSpectrum Γ(X, U), ∃ j, ∃ q : PrimeSpectrum Γ(X' (idx j), V j),
    PrimeSpectrum.comap ((f (idx j)).appLE U (V j) (hVU j)).hom q = p := by
  intro p
  let p' : ↥(Spec Γ(X, U)) := p
  have hxU : hU.fromSpec p' ∈ U := by
    change hU.fromSpec p' ∈ (U : Set X)
    rw [← hU.range_fromSpec]
    exact ⟨p', rfl⟩
  have hxcover : hU.fromSpec p' ∈ ⋃ j, f (idx j) '' (V j : Set (X' (idx j))) := by
    rwa [hcover]
  obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxcover
  obtain ⟨y, hyV, hyf⟩ := (Set.mem_image _ _ _).mp hxj
  let α := (f (idx j)).appLE U (V j) (hVU j)
  obtain ⟨q', hq⟩ : y ∈ Set.range (hV j).fromSpec := by rwa [(hV j).range_fromSpec]
  let q : ↥(Spec Γ(X' (idx j), V j)) := q'
  have hpoint : hU.fromSpec.base ((Spec.map α).base q) = hU.fromSpec.base p := by
    calc
      hU.fromSpec.base ((Spec.map α).base q) =
          (f (idx j)).base ((hV j).fromSpec.base q) :=
        congrArg (fun g : Scheme.Hom _ X => g.base q)
          (IsAffineOpen.SpecMap_appLE_fromSpec (f (idx j)) hU (hV j) (hVU j))
      _ = hU.fromSpec.base p := by rwa [hq]
  refine ⟨j, q, ?_⟩
  change (Spec.map α) q = p
  rw [Spec.map_apply]
  exact hU.fromSpec.isOpenEmbedding.injective hpoint

/-- **Stacks Project, Tag 05JZ.** Local projectivity of a quasi-coherent module descends
along an fpqc covering. -/
@[stacks 05JZ]
theorem isLocallyProjective_of_pullback_fpqc {X : Scheme.{u}} (F : X.Modules)
    (hF : F.IsQuasicoherent) {I : Type v} (X' : I → Scheme.{u}) (f : ∀ i, X' i ⟶ X)
    (hfpqc : Presieve.ofArrows X' f ∈ Scheme.fpqcPrecoverage X)
    (hprojective : ∀ i,
      Scheme.Modules.IsLocallyProjective ((Scheme.Modules.pullback (f i)).obj F)) :
    Scheme.Modules.IsLocallyProjective F := by
  classical
  intro U hU
  let R : Type u := Γ(X, U)
  let M : Type u := Γ(F, U)
  obtain ⟨n, idx, V, hVaff, hcover⟩ := fpqc_affine_refinement X' f hfpqc U hU
  have hVU (j : Fin n) : V j ≤ (f (idx j)) ⁻¹ᵁ U := by
    intro x hx
    change f (idx j) x ∈ (U : Set X)
    rw [← hcover]
    exact Set.mem_iUnion.mpr ⟨j, x, hx, rfl⟩
  let S : Fin n → Type u := fun j => Γ(X' (idx j), V j)
  let α (j : Fin n) : CommRingCat.of R ⟶ CommRingCat.of (S j) :=
    (f (idx j)).appLE U (V j) (hVU j)
  let : ∀ j, Algebra R (S j) := fun j => (α j).hom.toAlgebra
  have hflatFamily : ∀ i, Flat (f i) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @Flat)).mp
      (Scheme.propQCPrecoverage_le_precoverage X hfpqc)).2
  have hflat (j : Fin n) : Module.Flat R (S j) := by
    have _hf : Flat (f (idx j)) := hflatFamily (idx j)
    exact RingHom.flat_algebraMap_iff.mp
      ((f (idx j)).flat_appLE hU (hVaff j) (hVU j))
  let : Algebra R (∀ j, S j) := Pi.algebra (ι := Fin n) (R := R) S
  have : Module.FaithfullyFlat R (∀ j, S j) :=
    RingHom.faithfullyFlat_algebraMap_iff.mp <| faithfullyFlat_pi_of_prime_lifts S hflat
      (affineRefinement_prime_lifts X' f U hU n idx V hVaff hVU hcover)
  have hcomponents (j : Fin n) : Module.Projective (S j) (S j ⊗[R] M) := by
    have : Module.Projective (S j)
        Γ(((Scheme.Modules.pullback (f (idx j))).obj F), V j) :=
      hprojective (idx j) (V j) (hVaff j)
    exact Module.Projective.of_equiv'
      (affinePullbackSectionsBaseChangeIso (f (idx j)) F hU
        (hVaff j) (hVU j)).symm.toLinearEquiv
  have : Module.Projective (∀ j, S j) ((∀ j, S j) ⊗[R] M) :=
    projective_tensorProduct_pi S M hcomponents
  change Module.Projective Γ(X, U) Γ(F, U)
  exact Module.Projective.of_projective_tensorProduct (∀ j, S j)

end AlgebraicGeometry

end
