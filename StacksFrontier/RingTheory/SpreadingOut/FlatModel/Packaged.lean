module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel.DirectedModel
public import StacksFrontier.RingTheory.SpreadingOut.FlatModel.UniverseTransport

/-!
# Stacks 02JO, packaged

The three-part statement of Stacks 02JO at the universe generality the source asserts.

## Main results

* `Module.Flat.exists_flat_models_and_eventually_flat`: Stacks 02JO.
-/

@[expose] public section

universe uR uS uM uI uA uB uN uR₀ uS₀ uM₀

open scoped TensorProduct

/-! ### The packaged statement of Stacks 02JO -/

open Module.Flat.DirectedModel in
attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- **Stacks 02JO.** Let `R → S` be of finite presentation and let `M` be a finitely presented
`S`-module which is flat over `R`. Then:

1. there are a ring `R₀` of finite type over `ℤ`, an `R₀`-algebra `S₀` of finite type and a finite
   `S₀`-module `M₀` flat over `R₀`, with maps to `R`, `S` and `M` exhibiting `S = R ⊗_{R₀} S₀` and
   `M = S ⊗_{S₀} M₀`;
2. if `R = colim_λ R_λ` is a directed colimit, such a model already exists over some `R_λ`, with
   `R_λ → S_λ` of finite presentation and `M_λ` a finitely presented `S_λ`-module;
3. if `(R → S, M) = colim_λ (R_λ → S_λ, M_λ)` is a directed colimit of finitely presented pairs
   with cartesian transition squares, then `M_λ` is flat over `R_λ` for all large `λ`.

This is the packaged three-part form of the tag, stated at the universe generality the source
asserts: the index `I`, the three colimits `R`, `S`, `M`, the stage families `A`, `B`, `N` and the
model `R₀`, `S₀`, `M₀` of part (1) all live in independent universes. The three parts are also
available separately as `Module.Flat.exists_finiteType_model`,
`Module.Flat.exists_finitePresentation_model_of_directed` and
`Module.Flat.eventually_flat_of_directed`, which are proved with `R` and `S` in one universe (and,
in part (1), with the model in that universe); this statement is deduced from them by the universe
transport of the previous section, with no repetition of the spreading-out argument. -/
@[stacks 02JO]
theorem Module.Flat.exists_flat_models_and_eventually_flat
    {R : Type uR} {S : Type uS} {M : Type uM}
    [CommRing R] [CommRing S] [Algebra R S] [Algebra.FinitePresentation R S]
    [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.FinitePresentation S M] [Module.Flat R M] :
    (∃ (R₀ : Type uR₀) (S₀ : Type uS₀) (M₀ : Type uM₀)
        (_ : CommRing R₀) (_ : CommRing S₀) (_ : Algebra R₀ S₀)
        (_ : Algebra R₀ R) (_ : Algebra S₀ S) (_ : Algebra R₀ S)
        (_ : IsScalarTower R₀ R S) (_ : IsScalarTower R₀ S₀ S)
        (_ : AddCommGroup M₀) (_ : Module S₀ M₀) (_ : Module R₀ M₀)
        (_ : IsScalarTower R₀ S₀ M₀) (_ : Module S₀ M) (_ : IsScalarTower S₀ S M)
        (f : M₀ →ₗ[S₀] M),
      Algebra.FiniteType ℤ R₀ ∧ Algebra.FiniteType R₀ S₀ ∧ Module.Finite S₀ M₀ ∧
        Module.Flat R₀ M₀ ∧ Algebra.IsPushout R₀ R S₀ S ∧ IsBaseChange S f) ∧
    (∀ (I : Type uI) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (A : I → Type uA) (_ : ∀ i, CommRing (A i))
        (a : ∀ i j, i ≤ j → A i →+* A j)
        (_ : DirectedSystem A (fun i j h ↦ a i j h))
        (ρ : ∀ i, A i →+* R),
      (∀ i j (h : i ≤ j), ρ j ∘ a i j h = ρ i) →
      (∀ x : R, ∃ i y, ρ i y = x) →
      (∀ i y, ρ i y = 0 → ∃ (j : I) (h : i ≤ j), a i j h y = 0) →
      ∃ i : I,
        letI : Algebra (A i) R := (ρ i).toAlgebra
        ∃ (T : Type (max uA uS)) (P : Type (max (max uA uS) uM))
            (_ : CommRing T) (_ : Algebra (A i) T)
            (_ : Algebra T S) (_ : Algebra (A i) S)
            (_ : IsScalarTower (A i) R S) (_ : IsScalarTower (A i) T S)
            (_ : AddCommGroup P) (_ : Module T P) (_ : Module (A i) P)
            (_ : IsScalarTower (A i) T P) (_ : Module T M) (_ : IsScalarTower T S M)
            (f : P →ₗ[T] M),
          algebraMap (A i) R = ρ i ∧
            Algebra.FinitePresentation (A i) T ∧ Module.FinitePresentation T P ∧
            Module.Flat (A i) P ∧ Algebra.IsPushout (A i) R T S ∧ IsBaseChange S f) ∧
    (∀ (I : Type uI) (_ : Preorder I) (_ : Nonempty I) (_ : IsDirected I (· ≤ ·))
        (A : I → Type uA) (B : I → Type uB) (N : I → Type uN)
        (_ : ∀ i, CommRing (A i)) (_ : ∀ i, CommRing (B i))
        (_ : ∀ i, AddCommGroup (N i)) (_ : ∀ i, Module (B i) (N i))
        (a : ∀ i j, i ≤ j → A i →+* A j)
        (b : ∀ i j, i ≤ j → B i →+* B j)
        (_ : DirectedSystem A (fun i j h ↦ a i j h))
        (_ : DirectedSystem B (fun i j h ↦ b i j h))
        (g : ∀ i, A i →+* B i)
        (n : ∀ i j, (h : i ≤ j) → N i →ₛₗ[b i j h] N j)
        (ρ : ∀ i, A i →+* R) (σ : ∀ i, B i →+* S)
        (ν : ∀ i, N i →+ M)
        (hg : ∀ i j (h : i ≤ j), (g j).comp (a i j h) = (b i j h).comp (g i)),
      (∀ i x, n i i le_rfl x = x) →
      (∀ i j k (hij : i ≤ j) (hjk : j ≤ k) x,
        n j k hjk (n i j hij x) = n i k (hij.trans hjk) x) →
      (∀ i j (h : i ≤ j), ρ j ∘ a i j h = ρ i) →
      (∀ i j (h : i ≤ j), σ j ∘ b i j h = σ i) →
      (∀ i j (h : i ≤ j) x, ν j (n i j h x) = ν i x) →
      (∀ i, (algebraMap R S).comp (ρ i) = (σ i).comp (g i)) →
      (∀ i x m, ν i (g i x • m) = ρ i x • ν i m) →
      (∀ i y m, ν i (y • m) = σ i y • ν i m) →
      (∀ x : R, ∃ i y, ρ i y = x) →
      (∀ i y, ρ i y = 0 → ∃ (j : I) (h : i ≤ j), a i j h y = 0) →
      (∀ x : S, ∃ i y, σ i y = x) →
      (∀ i y, σ i y = 0 → ∃ (j : I) (h : i ≤ j), b i j h y = 0) →
      (∀ x : M, ∃ i y, ν i y = x) →
      (∀ i y, ν i y = 0 → ∃ (j : I) (h : i ≤ j), n i j h y = 0) →
      (∀ i,
        letI : Algebra (A i) (B i) := (g i).toAlgebra
        Algebra.FinitePresentation (A i) (B i)) →
      (∀ i, Module.FinitePresentation (B i) (N i)) →
      (∀ i j (h : i ≤ j),
        letI : Algebra (A i) (B i) := (g i).toAlgebra
        letI : Algebra (A i) (A j) := (a i j h).toAlgebra
        letI : Algebra (B i) (B j) := (b i j h).toAlgebra
        letI : Algebra (A j) (B j) := (g j).toAlgebra
        letI : Algebra (A i) (B j) := ((g j).comp (a i j h)).toAlgebra
        letI : IsScalarTower (A i) (A j) (B j) :=
          IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
        letI : IsScalarTower (A i) (B i) (B j) :=
          IsScalarTower.of_algebraMap_smul fun x y ↦ by
            change b i j h (g i x) * y = g j (a i j h x) * y
            exact congrArg (fun z : B j ↦ z * y)
              (by simpa using (RingHom.congr_fun (hg i j h) x).symm)
        Algebra.IsPushout (A i) (A j) (B i) (B j)) →
      (∀ i j (h : i ≤ j),
        letI : Algebra (B i) (B j) := (b i j h).toAlgebra
        letI : Module (B i) (N j) := Module.compHom (N j) (b i j h)
        letI : IsScalarTower (B i) (B j) (N j) :=
          IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
        IsBaseChange (B j)
          (⟨(n i j h).toAddHom, fun x y ↦ (n i j h).map_smul' x y⟩ :
            N i →ₗ[B i] N j)) →
      ∃ i, ∀ j, i ≤ j →
        letI : Module (A j) (N j) := Module.compHom (N j) (g j)
        Module.Flat (A j) (N j)) := by
  -- A copy `S'` of `S` in the universe of `R`: `S` is of finite type over `R`, hence `Small`
  -- there, and the three parts above all need `R` and `S` in one universe.
  have : Small.{uR} S := Algebra.FiniteType.small.{uR} (R := R)
  obtain ⟨S', _, _, ⟨e⟩⟩ := Algebra.exists_small_copy.{uR} (R := R) (S := S)
  let : Algebra S' S := e.toRingHom.toAlgebra
  have : IsScalarTower R S' S := .of_algebraMap_eq fun x => (e.commutes x).symm
  let : Module S' M := Module.compHom M e.toRingHom
  have : IsScalarTower S' S M := .of_algebraMap_smul fun _ _ => rfl
  have : IsScalarTower R S' M := .of_algebraMap_smul fun x m => by
    show e (algebraMap R S' x) • m = x • m
    rw [e.commutes]
    exact IsScalarTower.algebraMap_smul S x m
  have : Algebra.FinitePresentation R S' := Algebra.FinitePresentation.equiv e.symm
  have : Module.FinitePresentation S' M :=
    Module.FinitePresentation.of_bijective_algebraMap (R := S') (R' := S) e.bijective
  refine ⟨?_, ?_, ?_⟩
  · -- Part (1)
    obtain ⟨R₀, S₀, M₀, _, _, _, _, _, _, _, _, _, _, _, _, _, _, f, _, _, _, _, _, hf⟩ :=
      Module.Flat.exists_finiteType_model (R := R) (S := S') M
    let : Algebra S₀ S := ((algebraMap S' S).comp (algebraMap S₀ S')).toAlgebra
    have : IsScalarTower S₀ S' S := .of_algebraMap_eq fun _ => rfl
    let : Algebra R₀ S := ((algebraMap S' S).comp (algebraMap R₀ S')).toAlgebra
    have : IsScalarTower R₀ S' S := .of_algebraMap_eq fun _ => rfl
    have : IsScalarTower R₀ R S := .of_algebraMap_eq fun x => by
      show algebraMap S' S (algebraMap R₀ S' x) = algebraMap R S (algebraMap R₀ R x)
      rw [IsScalarTower.algebraMap_apply R₀ R S', ← IsScalarTower.algebraMap_apply R S' S]
    have : IsScalarTower R₀ S₀ S := .of_algebraMap_eq fun x => by
      show algebraMap S' S (algebraMap R₀ S' x)
        = algebraMap S' S (algebraMap S₀ S' (algebraMap R₀ S₀ x))
      rw [← IsScalarTower.algebraMap_apply R₀ S₀ S']
    have : IsScalarTower S₀ S M := .of_algebraMap_smul fun x m => by
      show algebraMap S' S (algebraMap S₀ S' x) • m = x • m
      rw [IsScalarTower.algebraMap_smul S, IsScalarTower.algebraMap_smul S']
    have : Algebra.IsPushout R₀ R S₀ S :=
      Algebra.IsPushout.of_equiv e (RingHom.ext fun _ => rfl)
    let e₀ : S' ≃ₐ[S₀] S := AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun _ => rfl
    have hf' : IsBaseChange S f :=
      IsBaseChange.of_algEquiv e₀.symm (fun s m => by
        show e (e.symm s) • m = s • m
        rw [AlgEquiv.apply_symm_apply]) hf
    exact Module.Flat.exists_small_finiteType_model (C := R₀) (R := R) f hf'
  · -- Part (2)
    intro I _ _ _ A _ a _ ρ hρ hs hz
    obtain ⟨i, T₀, P₀, _, _, _, _, _, _, _, _, _, _, _, _, f, _, _, _, _, hf⟩ :=
      Module.Flat.exists_finitePresentation_model_of_directed (R := R) (S := S') M a ρ
        (fun i j h x => congrFun (hρ i j h) x) hs hz
    refine ⟨i, ?_⟩
    let : Algebra (A i) R := (ρ i).toAlgebra
    let : Algebra T₀ S := ((algebraMap S' S).comp (algebraMap T₀ S')).toAlgebra
    have : IsScalarTower T₀ S' S := .of_algebraMap_eq fun _ => rfl
    let : Algebra (A i) S := ((algebraMap S' S).comp (algebraMap (A i) S')).toAlgebra
    have : IsScalarTower (A i) S' S := .of_algebraMap_eq fun _ => rfl
    have : IsScalarTower (A i) R S := .of_algebraMap_eq fun x => by
      show algebraMap S' S (algebraMap (A i) S' x) = algebraMap R S (algebraMap (A i) R x)
      rw [IsScalarTower.algebraMap_apply (A i) R S', ← IsScalarTower.algebraMap_apply R S' S]
    have : IsScalarTower (A i) T₀ S := .of_algebraMap_eq fun x => by
      show algebraMap S' S (algebraMap (A i) S' x)
        = algebraMap S' S (algebraMap T₀ S' (algebraMap (A i) T₀ x))
      rw [← IsScalarTower.algebraMap_apply (A i) T₀ S']
    have : IsScalarTower T₀ S M := .of_algebraMap_smul fun x m => by
      show algebraMap S' S (algebraMap T₀ S' x) • m = x • m
      rw [IsScalarTower.algebraMap_smul S, IsScalarTower.algebraMap_smul S']
    have : Algebra.IsPushout (A i) R T₀ S :=
      Algebra.IsPushout.of_equiv e (RingHom.ext fun _ => rfl)
    let e₀ : S' ≃ₐ[T₀] S := AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun _ => rfl
    have hf' : IsBaseChange S f :=
      IsBaseChange.of_algEquiv e₀.symm (fun s m => by
        show e (e.symm s) • m = s • m
        rw [AlgEquiv.apply_symm_apply]) hf
    have : Small.{max uA uS} T₀ := Algebra.FiniteType.small.{max uA uS} (R := A i)
    have : Small.{max (max uA uS) uM} T₀ :=
      Algebra.FiniteType.small.{max (max uA uS) uM} (R := A i)
    have : Small.{max (max uA uS) uM} P₀ := Module.Finite.small.{max (max uA uS) uM} T₀ P₀
    obtain ⟨T, P, _, _, _, _, _, _, _, _, _, _, _, _, u, h1, h2, h3, h4, h5⟩ :=
      Module.Flat.exists_small_finitePresentation_model.{max uA uS, max (max uA uS) uM}
        (C := A i) (R := R) f hf'
    exact ⟨T, P, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      inferInstance, u, rfl, h1, h2, h3, h4, h5⟩
  · -- Part (3)
    intro I _ _ _ A B N _ _ _ _ a b _ _ g n ρ σ ν hg hn₀ hn₁ hρ hσ hν hρσ _ hνσ
      hRs hRz hSs hSz hMs hMz hBfp hNfp hp hb
    let : ∀ i, Algebra (A i) (B i) := fun i => (g i).toAlgebra
    have : ∀ i, Small.{uA} (B i) := fun i => Algebra.FiniteType.small.{uA} (R := A i)
    choose B' _ _ hB' using fun i => Algebra.exists_small_copy.{uA} (R := A i) (S := B i)
    let eB : ∀ i, B' i ≃ₐ[A i] B i := fun i => (hB' i).some
    let : ∀ i, Algebra (B' i) (B i) := fun i => (eB i).toRingHom.toAlgebra
    let : ∀ i, Module (B' i) (N i) := fun i => Module.compHom (N i) (eB i).toRingHom
    have htB : ∀ i, IsScalarTower (B' i) (B i) (N i) :=
      fun i => .of_algebraMap_smul fun _ _ => rfl
    have hcomm : ∀ i (x : A i), eB i (algebraMap (A i) (B' i) x) = g i x :=
      fun i x => (eB i).commutes x
    let b' : ∀ i j, i ≤ j → B' i →+* B' j := fun i j h =>
      (eB j).symm.toRingHom.comp ((b i j h).comp (eB i).toRingHom)
    have hb'apply : ∀ i j (h : i ≤ j) (x : B' i), eB j (b' i j h x) = b i j h (eB i x) :=
      fun i j h x => (eB j).apply_symm_apply _
    let σ' : ∀ i, B' i →+* S' := fun i =>
      e.symm.toRingHom.comp ((σ i).comp (eB i).toRingHom)
    have hσ'apply : ∀ i (x : B' i), e (σ' i x) = σ i (eB i x) :=
      fun i x => e.apply_symm_apply _
    let n' : ∀ i j, (h : i ≤ j) → N i →ₛₗ[b' i j h] N j := fun i j h =>
      { toFun := n i j h
        map_add' := (n i j h).map_add
        map_smul' := fun x m => by
          show n i j h (eB i x • m) = eB j (b' i j h x) • n i j h m
          rw [hb'apply]
          exact (n i j h).map_smulₛₗ (eB i x) m }
    let ν' : ∀ i, N i →ₛₗ[σ' i] M := fun i =>
      { toFun := ν i
        map_add' := (ν i).map_add
        map_smul' := fun x m => by
          show ν i (eB i x • m) = e (σ' i x) • ν i m
          rw [hσ'apply]
          exact hνσ i (eB i x) m }
    have hdsB' : DirectedSystem B' fun i j h => b' i j h := by
      constructor
      · intro i x
        apply (eB i).injective
        rw [hb'apply, DirectedSystem.map_self' (fun i j h => b i j h)]
      · intro k j i hij hjk x
        apply (eB k).injective
        rw [hb'apply, hb'apply, hb'apply, DirectedSystem.map_map' (fun i j h => b i j h)]
    have hdsN' : DirectedSystem N fun i j h => n' i j h :=
      ⟨fun i x => hn₀ i x, fun {_ _ _} hij hjk x => hn₁ _ _ _ hij hjk x⟩
    have hab'' : ∀ i j (h : i ≤ j) (x : A i),
        b' i j h (algebraMap (A i) (B' i) x) = algebraMap (A j) (B' j) (a i j h x) := by
      intro i j h x
      refine (eB j).injective ?_
      rw [hb'apply, hcomm, hcomm]
      exact (RingHom.congr_fun (hg i j h) x).symm
    have hab' : ∀ i j (h : i ≤ j),
        (b' i j h).comp (algebraMap (A i) (B' i)) = (algebraMap (A j) (B' j)).comp (a i j h) :=
      fun i j h => RingHom.ext (hab'' i j h)
    have hρ' : ∀ i j (h : i ≤ j) x, ρ j (a i j h x) = ρ i x :=
      fun i j h x => congrFun (hρ i j h) x
    have hσ' : ∀ i j (h : i ≤ j) x, σ' j (b' i j h x) = σ' i x := by
      intro i j h x
      refine e.injective ?_
      rw [hσ'apply, hσ'apply, hb'apply]
      exact congrFun (hσ i j h) (eB i x)
    have hν' : ∀ i j (h : i ≤ j) x, ν' j (n' i j h x) = ν' i x := fun i j h x => hν i j h x
    have hρσ' : ∀ i, (σ' i).comp (algebraMap (A i) (B' i)) = (algebraMap R S').comp (ρ i) := by
      intro i
      refine RingHom.ext fun x => e.injective ?_
      show e (σ' i (algebraMap (A i) (B' i) x)) = e (algebraMap R S' (ρ i x))
      rw [hσ'apply, hcomm, e.commutes]
      exact (RingHom.congr_fun (hρσ i) x).symm
    have hσs' : ∀ s : S', ∃ i x, σ' i x = s := by
      intro s
      obtain ⟨i, y, hy⟩ := hSs (e s)
      refine ⟨i, (eB i).symm y, e.injective ?_⟩
      rw [hσ'apply, (eB i).apply_symm_apply, hy]
    have hσz' : ∀ i x, σ' i x = 0 → ∃ j, ∃ h : i ≤ j, b' i j h x = 0 := by
      intro i x hx
      obtain ⟨j, h, hj⟩ := hSz i (eB i x) (by rw [← hσ'apply, hx, map_zero])
      exact ⟨j, h, (eB j).injective (by rw [hb'apply, hj, map_zero])⟩
    have hfp' : ∀ i, Algebra.FinitePresentation (A i) (B' i) := by
      intro i
      have := hBfp i
      exact Algebra.FinitePresentation.equiv (eB i).symm
    have hfpN' : ∀ i, Module.FinitePresentation (B' i) (N i) := by
      intro i
      have := hNfp i
      have := htB i
      exact Module.FinitePresentation.of_bijective_algebraMap (R := B' i) (R' := B i)
        (eB i).bijective
    have hpush' : ∀ i j (h : i ≤ j), CategoryTheory.IsPushout (CommRingCat.ofHom (a i j h))
        (CommRingCat.ofHom (algebraMap (A i) (B' i)))
        (CommRingCat.ofHom (algebraMap (A j) (B' j))) (CommRingCat.ofHom (b' i j h)) := by
      intro i j h
      let : Algebra (A i) (A j) := (a i j h).toAlgebra
      let : Algebra (B i) (B j) := (b i j h).toAlgebra
      let : Algebra (A i) (B j) := ((g j).comp (a i j h)).toAlgebra
      have : IsScalarTower (A i) (A j) (B j) := .of_algebraMap_smul fun _ _ => rfl
      have : IsScalarTower (A i) (B i) (B j) := .of_algebraMap_smul fun x y => by
        show b i j h (g i x) * y = g j (a i j h x) * y
        exact congrArg (fun z : B j => z * y)
          (by simpa using (RingHom.congr_fun (hg i j h) x).symm)
      have hpij : Algebra.IsPushout (A i) (A j) (B i) (B j) := hp i j h
      let : Algebra (B' i) (B' j) := (b' i j h).toAlgebra
      let : Algebra (A i) (B' j) := ((algebraMap (A j) (B' j)).comp (a i j h)).toAlgebra
      have : IsScalarTower (A i) (A j) (B' j) := .of_algebraMap_eq fun _ => rfl
      have : IsScalarTower (A i) (B' i) (B' j) :=
        .of_algebraMap_eq fun x => (hab'' i j h x).symm
      refine CommRingCat.isPushout_iff_isPushout.mpr ?_
      refine Algebra.IsPushout.of_algEquiv₂ (eB i).symm (eB j).symm fun x => ?_
      refine (eB j).injective ?_
      show eB j ((eB j).symm (b i j h x)) = eB j (b' i j h ((eB i).symm x))
      rw [(eB j).apply_symm_apply, hb'apply, (eB i).apply_symm_apply]
    have hbc' : ∀ i j (h : i ≤ j), let := algebraB b' h
        let := Module.compHom (N j) (b' i j h)
        have : IsScalarTower (B' i) (B' j) (N j) := .of_algebraMap_smul fun _ _ => rfl
        IsBaseChange (B' j) (transLinear b' n' h) := by
      intro i j h
      let : Algebra (B i) (B j) := (b i j h).toAlgebra
      let : Module (B i) (N j) := Module.compHom (N j) (b i j h)
      have : IsScalarTower (B i) (B j) (N j) := .of_algebraMap_smul fun _ _ => rfl
      have hbij : IsBaseChange (B j)
          (⟨(n i j h).toAddHom, fun x y => (n i j h).map_smul' x y⟩ : N i →ₗ[B i] N j) :=
        hb i j h
      let : Algebra (B' i) (B' j) := (b' i j h).toAlgebra
      let : Module (B' i) (N j) := Module.compHom (N j) (b' i j h)
      have : IsScalarTower (B' i) (B' j) (N j) := .of_algebraMap_smul fun _ _ => rfl
      let : Algebra (B' i) (B j) := ((b i j h).comp (eB i).toRingHom).toAlgebra
      have : IsScalarTower (B' i) (B i) (B j) := .of_algebraMap_eq fun _ => rfl
      have : IsScalarTower (B' i) (B i) (N j) := .of_algebraMap_smul fun x m => by
        show (b i j h) (eB i x) • m = eB j (b' i j h x) • m
        rw [hb'apply]
      have : IsScalarTower (B' i) (B j) (N j) := .of_algebraMap_smul fun x m => by
        show (b i j h) (eB i x) • m = eB j (b' i j h x) • m
        rw [hb'apply]
      have h1 := IsBaseChange.restrictScalars_of_surjective (A := B' i) (B := B i)
        (eB i).bijective.surjective _ hbij
      refine IsBaseChange.of_algEquiv
        (AlgEquiv.ofRingEquiv (f := (eB j).toRingEquiv) (fun x => by
          show eB j (b' i j h x) = b i j h (eB i x)
          exact hb'apply i j h x))
        (fun s m => rfl) h1
    obtain ⟨i₀, hi₀⟩ := Module.Flat.eventually_flat_of_directed (R := R) (S := S') M
      a b' n' hab' ρ σ' ν' hρ' hσ' hν' hρσ' hRs hRz hσs' hσz' hMs hMz hpush' hbc' hfp' hfpN'
    refine ⟨i₀, fun j hj => ?_⟩
    have heq : Module.compHom (N j) (algebraMap (A j) (B' j)) = Module.compHom (N j) (g j) :=
      Module.ext' _ _ fun x m => by
        show eB j (algebraMap (A j) (B' j) x) • m = g j x • m
        rw [hcomm]
    exact heq ▸ hi₀ j hj
