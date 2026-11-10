module

public import StacksFrontier.AlgebraicGeometry.Discriminant.TraceCondition
public import StacksFrontier.RingTheory.TraceElement.ProjectiveTrace

/-!
# The trace element of a finite flat algebra

A finite algebra `A → B` factors through itself: the identity makes `Spec B → Spec B` an open
immersion, so `Stacks.Discriminant.selfFactorization` is a finite-open factorization with
intermediate algebra `B`, and the relative dualizing module it presents is
`Hom_A(B, A) ⊗_B B`. When moreover `B` is flat over a Noetherian `A`, the ordinary trace
functional `x ↦ Tr(x ·)` of the finite projective algebra `B`, tensored with `1`, is an
element of that module, and this file shows that it is a trace element in the sense of
Tag 0BT6.

The verification is the computation of the trace of multiplication on a direct factor. After a
base change `A₁` and a decomposition `A₁ ⊗_A B ≃ C × D` with `C` finite over `A₁`, the
intermediate algebra of the base-changed factorization is `A₁ ⊗_A B` itself, so the
restriction of the trace element to `C` is the `A₁`-trace of the element of `A₁ ⊗_A B`
corresponding to `(c, 0)`. That trace is computed by conjugating multiplication along the
decomposition and splitting off the second factor, where multiplication by `0` has trace `0`.

## Main definitions

* `Stacks.Discriminant.selfFactorization`: the finite-open factorization of a finite algebra
  through itself.
* `Stacks.Discriminant.finiteFlatTraceElement`: the ordinary trace of a finite flat algebra,
  viewed in its relative dualizing module.

## Main results

* `Stacks.Discriminant.isTraceElement_finiteFlatTraceElement`: Tag 0BT8, the ordinary trace is
  the trace element of a finite flat map of Noetherian rings.

## References

* [Stacks Project, Tag 0BT8](https://stacks.math.columbia.edu/tag/0BT8)
* [Stacks Project, Tag 0BT6](https://stacks.math.columbia.edu/tag/0BT6)
-/

@[expose] public noncomputable section

open scoped TensorProduct

universe u v x y z

namespace Stacks.Discriminant

attribute [local instance] algebraDualModule

/-- The finite-open factorization of a finite algebra through itself. The second map is the
identity, so it induces the identity on spectra and every away localization along it is
bijective. -/
def selfFactorization (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] : FiniteOpenFactorization.{u, v, v} A B where
  middle := B
  commRingMiddle := inferInstance
  algebraMiddle := inferInstance
  algebraTarget := inferInstance
  scalarTower := inferInstance
  finite_middle := inferInstance
  isOpenEmbedding_comap := by
    change Topology.IsOpenEmbedding (fun x : PrimeSpectrum B => x)
    exact ⟨.id, IsOpenMap.id.isOpen_range⟩
  awayMap_bijective := by
    intro g _
    refine ⟨?_, ?_⟩
    · rw [Localization.awayMap_injective_iff]
      intro a ha
      exact ⟨0, by simpa using ha⟩
    · rw [Localization.awayMap_surjective_iff]
      intro a
      exact ⟨a, 0, by simp⟩

/-- The ordinary trace of a finite flat algebra, regarded as an element of its relative
dualizing module through `Stacks.Discriminant.selfFactorization`. -/
def finiteFlatTraceElement (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [Module.Finite A B] [Module.Flat A B] :
    dualizingModule (selfFactorization A B) := by
  have : Module.FinitePresentation A B := Module.finitePresentation_of_finite A B
  have : Module.Projective A B := Module.Flat.projective_of_finitePresentation
  exact dualizingModule.tmul (selfFactorization A B)
    ((finiteProjectiveTrace A B).comp (Algebra.lmul A B).toLinearMap) 1

/-- A finite flat module over a Noetherian ring is projective. -/
private theorem projective_of_finite_flat_of_isNoetherianRing (R : Type*) (M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] [IsNoetherianRing R] [Module.Finite R M] [Module.Flat R M] :
    Module.Projective R M :=
  have := Module.finitePresentation_of_finite R M
  Module.Flat.projective_of_finitePresentation

/-- A retract of a finite projective module is finite and projective. -/
private theorem finite_and_projective_of_retract {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [Module.Finite R N] [Module.Projective R N]
    (i : M →ₗ[R] N) (p : N →ₗ[R] M) (h : p.comp i = LinearMap.id) :
    Module.Finite R M ∧ Module.Projective R M :=
  ⟨Module.Finite.of_surjective p fun m => ⟨i m, LinearMap.congr_fun h m⟩,
    Module.Projective.of_split i p h⟩

/-- **Stacks Project, Tag 0BT8.** For a finite flat map of Noetherian rings, the ordinary
trace of the finite projective algebra is a trace element of the relative dualizing module. -/
@[stacks 0BT8]
theorem isTraceElement_finiteFlatTraceElement (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A] [IsNoetherianRing B]
    [Module.Finite A B] [Module.Flat A B] :
    IsTraceElement.{u, v, v, x, y, z} (selfFactorization A B) (finiteFlatTraceElement A B) := by
  have : Module.Projective A B := projective_of_finite_flat_of_isNoetherianRing A B
  intro A₁ _ _ _ C D _ _ _ _ e hfinite
  let F := selfFactorization A B
  let e₀ : F.middle ≃ₐ[A] B :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }
  have : Module.Projective A F.middle := Module.Projective.of_equiv' e₀.symm.toLinearEquiv
  let f₀ : Module.Dual A F.middle :=
    (finiteProjectiveTrace A F.middle).comp (Algebra.lmul A F.middle).toLinearMap
  let F₁ := FiniteOpenFactorization.baseChange F A₁
  have : Module.Finite A₁ (A₁ ⊗[A] B) := Module.Finite.base_change A A₁ B
  have : Module.Flat A₁ (A₁ ⊗[A] B) := Module.Flat.baseChange A A₁ B
  have : Module.Projective A₁ (A₁ ⊗[A] B) :=
    projective_of_finite_flat_of_isNoetherianRing A₁ (A₁ ⊗[A] B)
  let eb : (A₁ ⊗[A] B) ≃ₗ[A₁] C × D := e.toLinearEquiv
  let p : (A₁ ⊗[A] B) →ₗ[A₁] C := (LinearMap.fst A₁ C D).comp eb.toLinearMap
  let i : C →ₗ[A₁] (A₁ ⊗[A] B) := eb.symm.toLinearMap.comp (LinearMap.inl A₁ C D)
  let q : (A₁ ⊗[A] B) →ₗ[A₁] D := (LinearMap.snd A₁ C D).comp eb.toLinearMap
  let j : D →ₗ[A₁] (A₁ ⊗[A] B) := eb.symm.toLinearMap.comp (LinearMap.inr A₁ C D)
  have hpi : p.comp i = LinearMap.id := by ext c; simp [p, i]
  have : Module.Finite A₁ C := hfinite
  have hqj : q.comp j = LinearMap.id := by ext d; simp [q, j]
  have hprojective : Module.Projective A₁ C := (finite_and_projective_of_retract i p hpi).2
  obtain ⟨_, _⟩ := finite_and_projective_of_retract j q hqj
  let eB : F₁.middle ≃ₐ[A₁] (A₁ ⊗[A] B) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : A₁ ≃ₐ[A₁] A₁) (e₀.restrictScalars A)
  have : Module.Finite A₁ F₁.middle := F₁.finite_middle
  have : Module.Projective A₁ F₁.middle := Module.Projective.of_equiv' eB.symm.toLinearEquiv
  let eProd : F₁.middle ≃ₐ[A₁] C × D := eB.trans e
  let : Algebra F₁.middle C :=
    ((RingHom.fst C D).comp (e.toRingEquiv.toRingHom.comp F₁.algebraTarget.algebraMap)).toAlgebra
  have hfactor (b : F₁.middle) : algebraMap F₁.middle C b = (eProd b).1 := rfl
  let pB : F₁.middle →ₗ[F₁.middle] C := Algebra.linearMap F₁.middle C
  let iB : C →ₗ[F₁.middle] F₁.middle :=
    { toFun := fun c => eProd.symm (c, 0)
      map_add' := fun c c' => eProd.injective (by simp)
      map_smul' := fun b c => by
        simp only [Algebra.smul_def, RingHom.id_apply]
        refine eProd.injective ?_
        rw [map_mul]
        exact Prod.ext (by simp [hfactor]) (by simp) }
  have hpBiB : pB.comp iB = LinearMap.id := by
    ext c
    change algebraMap F₁.middle C (eProd.symm (c, 0)) = c
    rw [hfactor]
    simp
  obtain ⟨hmfinite, hmprojective⟩ := finite_and_projective_of_retract iB pB hpBiB
  refine ⟨hprojective, hmfinite, hmprojective, ?_⟩
  ext c
  have hτ : dualizingModule.baseChange (selfFactorization A B) A₁ (finiteFlatTraceElement A B) =
      dualizingModule.tmul F₁ (f₀.baseChange A₁) (1 ⊗ₜ[A] (1 : B)) := by
    change dualizingModule.baseChange F A₁ (dualizingModule.tmul F f₀ (1 : B)) = _
    rw [dualizingModule.baseChange_tmul]
  have hfactorTrace : finiteProjectiveTrace F₁.middle C (Algebra.lmul F₁.middle C c) =
      eProd.symm (c, 0) :=
    finiteProjectiveTrace_lmul_of_prodEquiv eProd.toRingEquiv hfactor c
  have hbaseValue : (f₀.baseChange A₁) (eProd.symm (c, 0)) =
      finiteProjectiveTrace A₁ F₁.middle
        (Algebra.lmul A₁ F₁.middle (eProd.symm (c, 0))) :=
    congrArg (fun g => g (eProd.symm (c, 0)))
      (dualBaseChange_finiteProjectiveTrace_lmul A F.middle A₁)
  have hmul : eProd.toLinearEquiv.conj
      (Algebra.lmul A₁ F₁.middle (eProd.symm (c, 0))) =
      LinearMap.prodMap (Algebra.lmul A₁ C c) (Algebra.lmul A₁ D 0) := by
    apply LinearMap.ext
    rintro ⟨c', d'⟩
    refine Prod.ext ?_ ?_
    · simp [LinearEquiv.conj_apply, Algebra.coe_lmul_eq_mul, eProd.apply_symm_apply]
    · simp [LinearEquiv.conj_apply, Algebra.coe_lmul_eq_mul, eProd.apply_symm_apply]
  have hprodTrace : finiteProjectiveTrace A₁ F₁.middle
      (Algebra.lmul A₁ F₁.middle (eProd.symm (c, 0))) =
      finiteProjectiveTrace A₁ C (Algebra.lmul A₁ C c) := by
    rw [← finiteProjectiveTrace_conj_linearEquiv eProd.toLinearEquiv
      (Algebra.lmul A₁ F₁.middle (eProd.symm (c, 0))), hmul, finiteProjectiveTrace_prodMap]
    simp
  change (finiteFactorRestriction (selfFactorization A B) A₁ C D e (by intro; rfl) hfinite
      hprojective inferInstance inferInstance).1
      (dualizingModule.baseChange (selfFactorization A B) A₁ (finiteFlatTraceElement A B)) c =
    finiteProjectiveTrace A₁ C (Algebra.lmul A₁ C c)
  rw [hτ, (finiteFactorRestriction (selfFactorization A B) A₁ C D e (by intro; rfl) hfinite
    hprojective inferInstance inferInstance).2 (f₀.baseChange A₁) (1 ⊗ₜ[A] (1 : B)) c]
  have hunit : (e (1 ⊗ₜ[A] (1 : B))).1 = 1 := by
    rw [show (1 : A₁) ⊗ₜ[A] (1 : B) = 1 from Algebra.TensorProduct.one_def.symm, map_one]
    rfl
  rw [hunit, one_mul]
  change (f₀.baseChange A₁)
      (finiteProjectiveTrace F₁.middle C (Algebra.lmul F₁.middle C c)) =
    finiteProjectiveTrace A₁ C (Algebra.lmul A₁ C c)
  rw [hfactorTrace, hbaseValue, hprodTrace]

end Stacks.Discriminant

end
