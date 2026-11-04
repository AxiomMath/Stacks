module

public import Mathlib.RingTheory.Ideal.Finsupp
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.EilenbergSwindle
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Module.Kaplansky

/-!
# Big projective modules are free

Bass's theorem: over a commutative ring whose quotient by its Jacobson radical is Noetherian, a
countably generated projective module all of whose localisations at maximal ideals have infinite
rank is free. The engine is the Eilenberg swindle of
`StacksFrontier.Algebra.Module.EilenbergSwindle`, and the route is the source's. A projective module
has a free complement making the sum free; every element then lies in a finite free direct summand
of a slightly larger module; an element which generates the module together with a submodule can
be corrected inside that submodule to become unimodular; hence every element lies in a finite
stably free direct summand; and Kaplansky's criterion (Stacks 0591) makes the whole module free.

## Main definitions

There are no new definitions.

## Main results

* `exists_free_prod_of_projective`: every projective module has a free complement whose direct sum
  with it is free.
* `exists_finite_free_summand_containing_zero_prod`: after adjoining a finite free module to a
  projective module, a given element lies in a finite free direct summand.
* `exists_mem_add_unimodular`: an element which generates a projective module of infinite local
  rank together with a submodule can be modified inside that submodule to become unimodular.
* `exists_finite_isStablyFree_summand_containing`: every element of such a module lies in a finite
  stably free direct summand.
* `free_of_countablyGenerated_projective_of_localization_not_finite`: Bass's theorem.

## Implementation notes

Binary direct sums of modules are represented by product types, and the existence of a module
isomorphism by a nonempty type of linear equivalences. Infinite rank of a localisation is
expressed as failure of finite generation, and a direct summand by a complementary submodule via
`IsCompl`. The complements produced live in `Type (max u v)`, which accommodates both the ring and
the given module without imposing a universe-smallness hypothesis. Since `Module.IsStablyFree`
does not include finite generation, finiteness is stated separately alongside it.

## References

* [Bass]
* [Akasaki]
* [Hinohara]
* [Stacks, Tag 0GVG](https://stacks.math.columbia.edu/tag/0GVG)
* [Stacks, Tag 0GVH](https://stacks.math.columbia.edu/tag/0GVH)
* [Stacks, Tag 0GVI](https://stacks.math.columbia.edu/tag/0GVI)
* [Stacks, Tag 0GVJ](https://stacks.math.columbia.edu/tag/0GVJ)
* [Stacks, Tag 0GVK](https://stacks.math.columbia.edu/tag/0GVK)
-/

@[expose] public section

universe u v

section ProjectiveFreeComplement

/-- A linear map `i : P → M` with a retraction `s : M → P` splits `M` as `P × ker s`. -/
private noncomputable def splitLinearEquiv {R M P : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P]
    (i : P →ₗ[R] M) (s : M →ₗ[R] P) (h : s.comp i = LinearMap.id) :
    M ≃ₗ[R] P × LinearMap.ker s := by
  have hi (x : P) : s (i x) = x := DFunLike.congr_fun h x
  let f : M →ₗ[R] P × LinearMap.ker s :=
    { toFun := fun x ↦ (s x, ⟨x - i (s x), by
          rw [LinearMap.mem_ker, map_sub, hi, sub_self]⟩)
      map_add' := by
        intro x y
        apply Prod.ext
        · simp
        · apply Subtype.ext
          change x + y - i (s (x + y)) = (x - i (s x)) + (y - i (s y))
          simp only [map_add]
          abel
      map_smul' := by
        intro r x
        apply Prod.ext
        · simp
        · apply Subtype.ext
          change r • x - i (s (r • x)) = r • (x - i (s x))
          simp [smul_sub] }
  let g : (P × LinearMap.ker s) →ₗ[R] M := i.coprod (LinearMap.ker s).subtype
  refine LinearEquiv.ofLinearMap f g ?_ ?_
  · apply DFunLike.ext _ _
    rintro ⟨x, y⟩
    apply Prod.ext
    · change s (i x + y) = x
      rw [map_add, hi, LinearMap.mem_ker.mp y.property, add_zero]
    · apply Subtype.ext
      change i x + y - i (s (i x + y)) = y
      rw [map_add, hi, LinearMap.mem_ker.mp y.property, add_zero]
      abel
  · apply DFunLike.ext _ _
    intro x
    change i (s x) + (x - i (s x)) = x
    abel

/-- A projective module is a direct summand of a free module with a free complementary
summand. -/
@[stacks 0GVG]
theorem exists_free_prod_of_projective
    {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Projective R P] :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F)
      (_ : Module.Free R F), Module.Free R (P × F) := by
  classical
  by_cases hR : Nontrivial R
  · let := hR
    let s : (P →₀ R) →ₗ[R] P := Finsupp.linearCombination R id
    obtain ⟨i, hi⟩ :=
      Module.projective_def.mp (inferInstance : Module.Projective R P)
    let G := ℕ →₀ R
    let F := (P →₀ R) × G
    have hFnfg : ¬ Module.Finite R F := fun _ ↦
      Module.not_finite_of_infinite_basis (Finsupp.basisSingleOne : Module.Basis ℕ R G)
        (Module.Finite.of_surjective (LinearMap.snd R (P →₀ R) G) LinearMap.snd_surjective)
    obtain ⟨e⟩ := eilenberg_swindle P (LinearMap.ker s × G) F
      ⟨(LinearEquiv.prodAssoc R P (LinearMap.ker s) G).symm.trans
        (LinearEquiv.prodCongr (splitLinearEquiv (R := R) i s (LinearMap.ext hi)).symm
          (LinearEquiv.refl R G))⟩ hFnfg
    exact ⟨F, inferInstance, inferInstance, inferInstance, Module.Free.of_equiv e.symm⟩
  · have := not_nontrivial_iff_subsingleton.mp hR
    exact ⟨PUnit.{max u v + 1}, inferInstance, inferInstance,
      Module.Free.of_subsingleton' R _, Module.Free.of_subsingleton' R _⟩

end ProjectiveFreeComplement

section FiniteFreeSummandContainingElement

/-- The span of finitely many vectors of a basis is finite and free. -/
private theorem finite_free_span_image {R M ι : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (b : Module.Basis ι R M) (T : Finset ι) :
    Module.Finite R (Submodule.span R (b '' (T : Set ι))) ∧
      Module.Free R (Submodule.span R (b '' (T : Set ι))) := by
  have hli : LinearIndependent R (fun i : T => b i) :=
    b.linearIndependent.comp Subtype.val Subtype.val_injective
  have heq : Submodule.span R (Set.range (fun i : T => b i)) =
      Submodule.span R (b '' (T : Set ι)) := by
    congr 1
    ext y
    simp
  exact ⟨Module.Finite.of_basis (heq ▸ Module.Basis.span hli),
    Module.Free.of_basis (heq ▸ Module.Basis.span hli)⟩

/-- Every element of a free module lies in a finite free direct summand, namely the span of the
basis vectors occurring in its expansion. -/
private theorem finiteFreeSummand {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [Module.Free R M] (x : M) :
    ∃ (K : Submodule R M), Module.Finite R K ∧ Module.Free R K ∧ x ∈ K ∧
      ∃ K' : Submodule R M, IsCompl K K' := by
  classical
  let b := Module.Free.chooseBasis R M
  let S := (b.repr x).support
  obtain ⟨hfin, hfree⟩ := finite_free_span_image b S
  refine ⟨_, hfin, hfree, b.mem_span_repr_support x, Submodule.span R (b '' ((S : Set _)ᶜ)), ?_⟩
  exact b.linearIndependent.isCompl_span_image b.span_eq isCompl_compl

/-- The free factor in `F × P` may be shrunk to a finite free one without losing the finite free
summand around `(0, s)`. -/
private theorem shrinkFirstFactor
    {R F P : Type*} [Ring R] [AddCommGroup F] [Module R F] [Module.Free R F]
    [AddCommGroup P] [Module R P] (s : P) [Module.Free R (F × P)] :
    ∃ (F₀ : Type u_2) (_ : AddCommGroup F₀) (_ : Module R F₀)
      (_ : Module.Finite R F₀) (_ : Module.Free R F₀),
      ∃ (K : Submodule R (F₀ × P)) (_ : Module.Finite R K) (_ : Module.Free R K),
        (0, s) ∈ K ∧ ∃ K' : Submodule R (F₀ × P), IsCompl K K' := by
  classical
  obtain ⟨K₁, hK₁fin, hK₁free, hs, K₁', hcompl⟩ :=
    finiteFreeSummand (R := R) (M := F × P) (0, s)
  let b := Module.Free.chooseBasis R F
  obtain ⟨g, hg⟩ := Module.finite_def.mp hK₁fin
  let T : Finset (Module.Free.ChooseBasisIndex R F) :=
    g.biUnion fun x ↦ (b.repr (x : F × P).1).support
  let A : Submodule R F := Submodule.span R (b '' (T : Set _))
  obtain ⟨hAfin, hAfree⟩ := finite_free_span_image b T
  let j : A × P →ₗ[R] F × P :=
    (A.subtype.prodMap (LinearMap.id (R := R) (M := P)))
  have hKle : K₁ ≤ A.prod ⊤ := by
    intro x hx
    have hspan : Submodule.span R (g : Set K₁) ≤
        (A.prod ⊤).comap K₁.subtype := Submodule.span_le.2 fun y hy => by
      show (y : F × P) ∈ A.prod ⊤
      refine ⟨?_, trivial⟩
      apply Submodule.span_mono (Set.image_mono (Finset.subset_iff.2 fun i hi =>
        Finset.mem_biUnion.2 ⟨y, hy, hi⟩))
      exact b.mem_span_repr_support (y : F × P).1
    exact hspan (by rw [hg]; trivial : (⟨x, hx⟩ : K₁) ∈ Submodule.span R (g : Set K₁))
  let K := K₁.comap j
  let L := K₁'.comap j
  let q : K →ₗ[R] K₁ := LinearMap.codRestrict K₁ (j.domRestrict K) fun x => x.property
  have eq_surj : Function.Surjective q := by
    intro (x : K₁)
    have hxA : (x : F × P).1 ∈ A := (hKle x.property).1
    refine ⟨⟨(⟨(x : F × P).1, hxA⟩, (x : F × P).2), ?_⟩, ?_⟩
    · exact x.property
    · apply Subtype.ext
      rfl
  let eK : K ≃ₗ[R] K₁ := LinearEquiv.ofBijective q
    ⟨fun x y h ↦ by
        have hraw : j x = j y := congrArg Subtype.val h
        apply Subtype.ext
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg Prod.fst hraw
        · simpa [j] using congrArg Prod.snd hraw,
      eq_surj⟩
  let : Module.Finite R K := Module.Finite.equiv eK.symm
  let : Module.Free R K := Module.Free.of_equiv eK.symm
  have hKL : IsCompl K L := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff]
      apply le_antisymm
      · intro x hx
        rw [Submodule.mem_bot]
        have hjx : j x = 0 := by
          have hmem : j x ∈ (⊥ : Submodule R (F × P)) :=
            hcompl.1.le_bot ⟨hx.1, hx.2⟩
          simpa using hmem
        apply Prod.ext
        · apply Subtype.ext
          exact congrArg Prod.fst hjx
        · simpa [j] using congrArg Prod.snd hjx
      · exact bot_le
    · rw [codisjoint_iff]
      apply top_unique
      intro x _
      rw [Submodule.mem_sup]
      have hjmem : j x ∈ K₁ ⊔ K₁' := by rw [hcompl.2.eq_top]; trivial
      rw [Submodule.mem_sup] at hjmem
      obtain ⟨k, hk, l, hl, hsum⟩ := hjmem
      have hkA : k.1 ∈ A := (hKle hk).1
      have hlA : l.1 ∈ A := by
        have hz := A.sub_mem x.1.property hkA
        have hfst : k.1 + l.1 = (x.1 : F) := by
          simpa [j] using congrArg Prod.fst hsum
        rw [← hfst] at hz
        simpa using hz
      let ka : A × P := (⟨k.1, hkA⟩, k.2)
      let la : A × P := (⟨l.1, hlA⟩, l.2)
      refine ⟨ka, hk, la, hl, ?_⟩
      apply Prod.ext
      · apply Subtype.ext
        simpa [ka, la, j] using congrArg Prod.fst hsum
      · simpa [ka, la, j] using congrArg Prod.snd hsum
  refine ⟨A, inferInstance, inferInstance, hAfin, hAfree, K, inferInstance,
    inferInstance, ?_, L, hKL⟩
  simpa [K, j] using hs

/-- For an element `s` of a projective module `P`, there is a finite free module `F` and a
finite free direct summand of `F × P` containing `(0, s)`. -/
@[stacks 0GVH]
theorem exists_finite_free_summand_containing_zero_prod
    {R : Type u} [Ring R] {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Projective R P] (s : P) :
    ∃ (F : Type (max u v)) (_ : AddCommGroup F) (_ : Module R F)
      (_ : Module.Finite R F) (_ : Module.Free R F),
      ∃ (K : Submodule R (F × P)) (_ : Module.Finite R K) (_ : Module.Free R K),
        (0, s) ∈ K ∧ ∃ K' : Submodule R (F × P), IsCompl K K' := by
  classical
  obtain ⟨F, _, _, hFfree, hPFfree⟩ := exists_free_prod_of_projective (R := R) (P := P)
  let : Module.Free R F := hFfree
  let : Module.Free R (P × F) := hPFfree
  let : Module.Free R (F × P) :=
    Module.Free.of_equiv (LinearEquiv.prodComm R P F)
  exact shrinkFirstFactor (R := R) (F := F) s

end FiniteFreeSummandContainingElement

section UnimodularElement

open Submodule

/-- Evaluation of a linear functional at a fixed element, as a linear map on the dual. -/
private def evalAt {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    (x : P) : (P →ₗ[R] R) →ₗ[R] R where
  toFun φ := φ x
  map_add' φ ψ := by simp
  map_smul' r φ := by simp

/-- The Noetherian-induction core of Stacks 0GVI: if every cofinite submodule contains an element
on which some functional is a unit modulo a given maximal ideal, then a maximal member of the
family of ideals `{ φ (s + m) : φ }` is the unit ideal. -/
private theorem exists_mem_add_dual_eq_one_of_large {R P : Type*} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup P] [Module R P] (M : Submodule R P) (s : P)
    (hM : M.CoFG)
    (hlarge : ∀ (K : Submodule R P), K.CoFG → ∀ (p : Ideal R), p.IsMaximal →
      ∃ t ∈ K, ∃ φ : P →ₗ[R] R, φ t ∉ p) :
    ∃ m ∈ M, ∃ φ : P →ₗ[R] R, φ (s + m) = 1 := by
  let J (m : P) : Ideal R := (evalAt (s + m)).range
  let D : Set (Ideal R) := {I | ∃ m ∈ M, J m = I}
  have hD : D.Nonempty := ⟨J 0, 0, M.zero_mem, rfl⟩
  obtain ⟨I, ⟨m, hm, hI⟩, hmax⟩ :=
    (set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R)) D hD
  by_cases htop : I = ⊤
  · have hone : (1 : R) ∈ (evalAt (s + m)).range := by
      show (1 : R) ∈ J m
      rw [hI, htop]
      trivial
    obtain ⟨φ, hφ⟩ := hone
    exact ⟨m, hm, φ, hφ⟩
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I htop
  have hJp : J m ≤ p := by rw [hI]; exact hIp
  have hfg : (J m).FG := Ideal.fg_of_isNoetherianRing _
  obtain ⟨S, hSfin, hSspan⟩ := Submodule.fg_def.mp hfg
  have hS : ∀ a : S, (a : R) ∈ J m := by
    intro a
    rw [← hSspan]
    exact Submodule.subset_span a.property
  choose φ hφ using fun a : S => (hS a : (a : R) ∈ (evalAt (s + m)).range)
  let K : Submodule R P := M ⊓ sInf (Set.range fun a : S => (φ a).ker)
  let : Finite S := hSfin.to_subtype
  have hK : K.CoFG := by
    apply hM.inf
    apply Submodule.CoFG.sInf_of_finite
    · exact Set.finite_range (fun a : S => (φ a).ker)
    · intro N hN
      obtain ⟨a, rfl⟩ := hN
      exact Submodule.CoFG.ker (φ a)
  obtain ⟨t, ht, ψ, hψ⟩ := hlarge K hK p hp
  have htM : t ∈ M := ht.1
  have hφt : ∀ a : S, φ a t = 0 := by
    intro a
    have hk : t ∈ (φ a).ker := (Submodule.mem_sInf).mp ht.2 _ ⟨a, rfl⟩
    exact LinearMap.mem_ker.mp hk
  have hle : J m ≤ J (m + t) := by
    rw [← hSspan]
    apply Submodule.span_le.mpr
    intro a ha
    let b : S := ⟨a, ha⟩
    have hav : φ b (s + m) = a := hφ b
    have hav' : φ b (s + (m + t)) = a := by
      rw [show s + (m + t) = (s + m) + t by abel, map_add, hφt, add_zero]
      exact hav
    exact ⟨φ b, hav'⟩
  have hnot : ¬ J (m + t) ≤ p := by
    intro h
    have hψm : ψ (s + m) ∈ p := hJp ⟨ψ, rfl⟩
    have hψmt : ψ (s + (m + t)) ∈ p := h ⟨ψ, rfl⟩
    have : ψ t ∈ p := by
      have heq : ψ (s + (m + t)) = ψ (s + m) + ψ t := by
        rw [show s + (m + t) = (s + m) + t by abel, map_add]
      rw [heq] at hψmt
      simpa only [add_sub_cancel_left] using p.sub_mem hψmt hψm
    exact hψ this
  have hlt : J m < J (m + t) := lt_of_le_of_ne hle (by intro h; apply hnot; exact h ▸ hJp)
  have hmtt : m + t ∈ M := M.add_mem hm htM
  exact False.elim (hmax (J (m + t)) ⟨m + t, hmtt, rfl⟩ (by rw [← hI]; exact hlt))

/-- An element of a projective module killed modulo `I` by every functional lies in `I • ⊤`. -/
private theorem dual_mem_ideal_smul_top {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (I : Ideal R) (x : P) (h : ∀ φ : P →ₗ[R] R, φ x ∈ I) :
    x ∈ I • (⊤ : Submodule R P) := by
  obtain ⟨sec, hsec⟩ := Module.projective_def.mp (inferInstance : Module.Projective R P)
  let ret : (P →₀ R) →ₗ[R] P := Finsupp.linearCombination R id
  have hsx : sec x ∈ Finsupp.submodule (fun _ : P => I) := by
    rw [Finsupp.mem_submodule_iff]
    intro i
    exact h ((Finsupp.lapply i) ∘ₗ sec)
  have heq : Finsupp.submodule (fun _ : P => I) =
      I • (⊤ : Submodule R (P →₀ R)) := by
    calc
      Finsupp.submodule (fun _ : P => I) =
          Finsupp.submodule (fun _ : P => I • (⊤ : Submodule R R)) := by simp
      _ = I • Finsupp.submodule (fun _ : P => (⊤ : Submodule R R)) :=
        Finsupp.submodule_smul R P (fun _ => (⊤ : Submodule R R)) I
      _ = I • (⊤ : Submodule R (P →₀ R)) := by rw [Finsupp.submodule_top]
  rw [heq] at hsx
  have hret : ret (sec x) ∈ I • (⊤ : Submodule R P) :=
    Submodule.smul_top_le_comap_smul_top I ret hsx
  simpa only [ret, hsec x] using hret

/-- A cofinite submodule contained in `I • ⊤` makes the fibre `P / I • ⊤` a finite module over
`R / I`. -/
private theorem finite_fiber_of_cofg_le {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] (I : Ideal R) (K : Submodule R P)
    (hK : K.CoFG) (hKI : K ≤ I • (⊤ : Submodule R P)) :
    Module.Finite (R ⧸ I) (P ⧸ I • (⊤ : Submodule R P)) := by
  let f : (P ⧸ K) →ₛₗ[Ideal.Quotient.mk I]
      (P ⧸ I • (⊤ : Submodule R P)) :=
    { toFun := Submodule.factor hKI
      map_add' := by intros x y; exact map_add _ _ _
      map_smul' := by
        intro r x
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          simp only [← Submodule.Quotient.mk_smul]
          rfl }
  exact Module.Finite.of_surjective f (Submodule.factor_surjective hKI)

/-- Finiteness over `R` transfers to finiteness over a quotient `R / I` acting compatibly. -/
private theorem finite_over_quotient_of_finite {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R)
    [Module (R ⧸ I) M] [IsScalarTower R (R ⧸ I) M]
    [Module.Finite R M] : Module.Finite (R ⧸ I) M := by
  let e : M →ₛₗ[Ideal.Quotient.mk I] M :=
    ⟨AddHom.id _, fun r x => (IsScalarTower.algebraMap_smul (R ⧸ I) r x).symm⟩
  exact Module.Finite.of_surjective e Function.surjective_id

/-- The fibre `M / I • ⊤` is `R / I ⊗ M`, as a module over `R / I`. -/
private noncomputable def quotTensorEquiv {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M]
    [Module R M] (I : Ideal R) :
    TensorProduct R (R ⧸ I) M ≃ₗ[R ⧸ I] M ⧸ I • (⊤ : Submodule R M) :=
  (TensorProduct.quotTensorEquivQuotSMul M I).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective

/-- A free module with finite fibre at a maximal ideal is finite. -/
private theorem finite_of_free_finite_fiber {R F : Type*} [CommRing R]
    [AddCommGroup F] [Module R F] [Module.Free R F]
    (I : Ideal R) [I.IsMaximal]
    [Module.Finite R (F ⧸ I • (⊤ : Submodule R F))] :
    Module.Finite R F := by
  let : Module.Finite (R ⧸ I) (F ⧸ I • (⊤ : Submodule R F)) :=
    finite_over_quotient_of_finite I
  let b := Module.Free.chooseBasis R F
  let e := quotTensorEquiv F I
  let b' : Module.Basis (Module.Free.ChooseBasisIndex R F) (R ⧸ I)
      (F ⧸ I • (⊤ : Submodule R F)) :=
    (b.baseChange (R ⧸ I)).map e
  let : Finite (Module.Free.ChooseBasisIndex R F) := Module.Finite.finite_basis b'
  exact Module.Finite.of_basis b

/-- A finite fibre at a maximal ideal stays finite after localising there. -/
private theorem finite_local_fiber_of_finite_fiber {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] (p : Ideal R) [p.IsMaximal]
    (hfin : Module.Finite (R ⧸ p) (P ⧸ p • (⊤ : Submodule R P))) :
    Module.Finite (Localization.AtPrime p)
      (LocalizedModule p.primeCompl P ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime p) •
          (⊤ : Submodule (Localization.AtPrime p) (LocalizedModule p.primeCompl P))) := by
  let S := Localization.AtPrime p
  let Q := P ⧸ p • (⊤ : Submodule R P)
  let : Module.Finite (R ⧸ p) Q := hfin
  let : Module.Finite R Q := Module.Finite.trans (R ⧸ p) Q
  let : Module.Finite S (LocalizedModule p.primeCompl Q) :=
    Module.Finite.of_isLocalizedModule p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl Q)
  have hpmap : Submodule.localized' S p.primeCompl (Algebra.linearMap R S) p =
      IsLocalRing.maximalIdeal S := by
    rw [Submodule.localized'_eq_span]
    show Ideal.map (algebraMap R S) p = IsLocalRing.maximalIdeal S
    have hunder : Ideal.under R (IsLocalRing.maximalIdeal S) = p :=
      IsLocalization.AtPrime.under_maximalIdeal S p
    calc
      Ideal.map (algebraMap R S) p =
          Ideal.map (algebraMap R S) (Ideal.under R (IsLocalRing.maximalIdeal S)) :=
        congrArg (Ideal.map (algebraMap R S)) hunder.symm
      _ = IsLocalRing.maximalIdeal S :=
        IsLocalization.map_under p.primeCompl S (IsLocalRing.maximalIdeal S)
  have hloc : (p • (⊤ : Submodule R P)).localized p.primeCompl =
      IsLocalRing.maximalIdeal S • (⊤ : Submodule S (LocalizedModule p.primeCompl P)) := by
    show Submodule.localized' S p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl P)
      (p • (⊤ : Submodule R P)) = _
    rw [Submodule.localized'_smul, Submodule.localized'_top, hpmap]
  let e := localizedQuotientEquiv p.primeCompl (p • (⊤ : Submodule R P))
  rw [hloc] at e
  exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

/-- If all localisations of a projective module at maximal ideals have infinite rank, then every
cofinite submodule contains an element on which some functional is a unit at a given maximal
ideal. -/
private theorem cofg_has_dual_outside_maximal {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hP : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl P))
    (K : Submodule R P) (hK : K.CoFG) (p : Ideal R) (hp : p.IsMaximal) :
    ∃ t ∈ K, ∃ φ : P →ₗ[R] R, φ t ∉ p := by
  by_contra hn
  have hdual : ∀ t ∈ K, ∀ φ : P →ₗ[R] R, φ t ∈ p := by
    intro t ht φ
    by_contra hφ
    exact hn ⟨t, ht, φ, hφ⟩
  have hKle : K ≤ p • (⊤ : Submodule R P) := by
    intro t ht
    exact dual_mem_ideal_smul_top p t (hdual t ht)
  have hfinfiber := finite_fiber_of_cofg_le p K hK hKle
  have hfinlocalfiber := finite_local_fiber_of_finite_fiber p hfinfiber
  let S := Localization.AtPrime p
  let PL := LocalizedModule p.primeCompl P
  let : Module.Projective S PL := inferInstance
  let : Module.Free S PL := Module.free_of_projective_of_isLocalRing
  let : Module.Finite S
      (PL ⧸ IsLocalRing.maximalIdeal S • (⊤ : Submodule S PL)) := hfinlocalfiber
  have hfinloc : Module.Finite S PL :=
    finite_of_free_finite_fiber (IsLocalRing.maximalIdeal S)
  exact hP ⟨p, hp⟩ hfinloc

/-- The functional induced on the fibre `P / I • ⊤` by a functional on `P`. -/
private def reduceDual {R P : Type*} [CommRing R] [AddCommGroup P] [Module R P]
    (I : Ideal R) (φ : P →ₗ[R] R) :
    (P ⧸ I • (⊤ : Submodule R P)) →ₗ[R ⧸ I] (R ⧸ I) := by
  let f : P →ₛₗ[Ideal.Quotient.mk I] (R ⧸ I) :=
    { toFun := fun x => Ideal.Quotient.mk I (φ x)
      map_add' := by intro x y; simp
      map_smul' := by intro r x; simp [map_smul, smul_eq_mul] }
  have hker : I • (⊤ : Submodule R P) ≤ f.ker := by
    intro x hx
    have hx' : φ x ∈ I := by
      have h := Submodule.smul_top_le_comap_smul_top I φ hx
      simpa using h
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr hx'
  let f' := (I • (⊤ : Submodule R P)).liftQ f hker
  exact
    { toFun := f'
      map_add' := by intro x y; exact map_add f' x y
      map_smul' := by
        intro a x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          change f' (Submodule.Quotient.mk (r • x)) =
            Ideal.Quotient.mk I r • f' (Submodule.Quotient.mk x)
          exact f'.map_smulₛₗ r (Submodule.Quotient.mk x) }

private theorem reduceDual_mk {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] (I : Ideal R) (φ : P →ₗ[R] R) (x : P) :
    reduceDual I φ (Submodule.Quotient.mk x) = Ideal.Quotient.mk I (φ x) := rfl

/-- The previous statement for the fibre `P / I • ⊤` over `R / I`. -/
private theorem quotient_cofg_has_dual_outside_maximal {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (hP : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl P))
    (I : Ideal R)
    (K : Submodule (R ⧸ I) (P ⧸ I • (⊤ : Submodule R P)))
    (hK : K.CoFG) (q : Ideal (R ⧸ I)) (hq : q.IsMaximal) :
    ∃ t ∈ K, ∃ φ : (P ⧸ I • (⊤ : Submodule R P)) →ₗ[R ⧸ I] (R ⧸ I), φ t ∉ q := by
  let Q := P ⧸ I • (⊤ : Submodule R P)
  let qmap : P →ₗ[R] Q := (I • (⊤ : Submodule R P)).mkQ
  let g : P →ₗ[R] Q ⧸ K := ((K.mkQ).restrictScalars R).comp qmap
  have hgsurj : Function.Surjective g := by
    intro z
    obtain ⟨y, rfl⟩ := K.mkQ_surjective z
    obtain ⟨x, rfl⟩ := (I • (⊤ : Submodule R P)).mkQ_surjective y
    exact ⟨x, rfl⟩
  let Kpre := g.ker
  have hKpre : Kpre.CoFG := by
    have : Module.Finite (R ⧸ I) (Q ⧸ K) := hK
    have : Module.Finite R (Q ⧸ K) := Module.Finite.trans (R ⧸ I) (Q ⧸ K)
    exact Module.Finite.of_surjective (g.quotKerEquivOfSurjective hgsurj).symm.toLinearMap
      (g.quotKerEquivOfSurjective hgsurj).symm.surjective
  let p := Ideal.comap (Ideal.Quotient.mk I) q
  have : p.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
      (Ideal.Quotient.mk_surjective) (H := hq)
  obtain ⟨t, ht, φ, hφ⟩ := cofg_has_dual_outside_maximal hP Kpre hKpre p ‹p.IsMaximal›
  have htK : qmap t ∈ K := by
    have hgz : g t = 0 := LinearMap.mem_ker.mp ht
    change K.mkQ (qmap t) = 0 at hgz
    exact (Submodule.Quotient.mk_eq_zero K).mp hgz
  refine ⟨qmap t, htK, reduceDual I φ, ?_⟩
  rw [show qmap t = Submodule.Quotient.mk t by rfl, reduceDual_mk]
  exact hφ

/-- The fibre of a projective module is projective over the quotient ring. -/
private theorem projective_quotient_smul_top {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (I : Ideal R) :
    Module.Projective (R ⧸ I) (P ⧸ I • (⊤ : Submodule R P)) := by
  let e := quotTensorEquiv P I
  let : Module.Projective (R ⧸ I) (TensorProduct R (R ⧸ I) P) := inferInstance
  exact Module.Projective.of_equiv' e

/-- Stacks 0GVI modulo an ideal: the corrected element is unimodular after reduction mod `I`. -/
private theorem exists_mem_add_dual_one_mod_ideal {R P : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (M : Submodule R P) (s : P) (I : Ideal R)
    (hR : IsNoetherianRing (R ⧸ I))
    (hP : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl P))
    (hspan : Submodule.span R {s} ⊔ M = ⊤) :
    ∃ m ∈ M, ∃ φ : P →ₗ[R] R, Ideal.Quotient.mk I (φ (s + m)) = 1 := by
  let Q := P ⧸ I • (⊤ : Submodule R P)
  let qmap : P →ₛₗ[Ideal.Quotient.mk I] Q :=
    { toFun := fun x => Submodule.Quotient.mk x
      map_add' := by intro x y; exact map_add (I • (⊤ : Submodule R P)).mkQ x y
      map_smul' := by intro r x; rfl }
  let Mbar : Submodule (R ⧸ I) Q := Submodule.map qmap M
  have hqsurj : Function.Surjective qmap :=
    (I • (⊤ : Submodule R P)).mkQ_surjective
  have hspanbar : Submodule.span (R ⧸ I) {qmap s} ⊔ Mbar = ⊤ := by
    apply top_unique
    intro y hy
    obtain ⟨x, rfl⟩ := hqsurj y
    have hx : x ∈ Submodule.span R {s} ⊔ M := by rw [hspan]; trivial
    have hxy : qmap x ∈ Submodule.map qmap (Submodule.span R {s} ⊔ M) :=
      ⟨x, hx, rfl⟩
    rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton] at hxy
    exact hxy
  let : IsNoetherianRing (R ⧸ I) := hR
  let : Module.Projective (R ⧸ I) Q := projective_quotient_smul_top I
  let π : Q →ₗ[R ⧸ I] Q ⧸ Mbar := Mbar.mkQ
  have hspanQ : Submodule.span (R ⧸ I) {π (qmap s)} = ⊤ := by
    have hm : Submodule.map π Mbar = ⊥ := by
      apply (Submodule.eq_bot_iff _).mpr
      intro y hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact (Submodule.Quotient.mk_eq_zero Mbar).mpr hx
    have hmap := congrArg (Submodule.map π) hspanbar
    rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton, hm,
      sup_bot_eq, Submodule.map_top, LinearMap.range_eq_top.mpr Mbar.mkQ_surjective] at hmap
    exact hmap
  have : Module.Finite (R ⧸ I) (Q ⧸ Mbar) := by
    apply Module.finite_def.mpr
    rw [← hspanQ]
    exact Submodule.fg_span_singleton (π (qmap s))
  obtain ⟨mbar, hmbar, φbar, hφbar⟩ :=
    exists_mem_add_dual_eq_one_of_large Mbar (qmap s) ‹Mbar.CoFG›
      (quotient_cofg_has_dual_outside_maximal hP I)
  obtain ⟨m, hm, rfl⟩ := hmbar
  let f : R →ₗ[R] R ⧸ I := Algebra.linearMap R (R ⧸ I)
  let g : P →ₗ[R] R ⧸ I :=
    (φbar.restrictScalars R).comp (I • (⊤ : Submodule R P)).mkQ
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property f g
    (by
      intro y
      obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨r, by change (Ideal.Quotient.mk I) r = y; exact hr⟩)
  refine ⟨m, hm, φ, ?_⟩
  have hφx : f (φ (s + m)) = g (s + m) :=
    DFunLike.congr_fun hφ (s + m)
  change (Ideal.Quotient.mk I) (φ (s + m)) = φbar (qmap s + qmap m) at hφx
  exact hφx.trans hφbar

/-- If `P` is projective and has infinite rank after localization at every maximal ideal, then
an element which generates `P` together with `M` can be modified by an element of `M` to become
unimodular. -/
@[stacks 0GVI]
theorem exists_mem_add_unimodular
    {R : Type u} [CommRing R] {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Projective R P] (M : Submodule R P) (s : P)
    (hR : IsNoetherianRing (R ⧸ Ideal.jacobson (⊥ : Ideal R)))
    (hP : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl P))
    (hspan : Submodule.span R {s} ⊔ M = ⊤) :
    ∃ m ∈ M, ∃ φ : P →ₗ[R] R, φ (s + m) = 1 := by
  let I := Ideal.jacobson (⊥ : Ideal R)
  obtain ⟨m, hm, φ, hφ⟩ := exists_mem_add_dual_one_mod_ideal M s I hR hP hspan
  have hmem : φ (s + m) - 1 ∈ I := by
    apply (Ideal.Quotient.eq_zero_iff_mem).mp
    rw [map_sub, hφ, map_one, sub_self]
  obtain ⟨u, hu⟩ := Ideal.isUnit_of_sub_one_mem_jacobson_bot
    (φ (s + m)) hmem
  refine ⟨m, hm, (↑u⁻¹ : R) • φ, ?_⟩
  show (↑u⁻¹ : R) * φ (s + m) = 1
  rw [← hu]
  simp

end UnimodularElement

section FiniteStablyFreeSummand

/-- Cancelling a free factor: if `R × M ≅ K × R` with `K` finite stably free, then `M` is finite
stably free. -/
private theorem free_stable_cancel
    {R M K : Type*} [CommRing R]
    [AddCommGroup M] [Module R M]
    [AddCommGroup K] [Module R K]
    [Module.Finite R K] [Module.IsStablyFree R K]
    (e : (R × M) ≃ₗ[R] (K × R)) :
    Module.Finite R M ∧ Module.IsStablyFree R M := by
  have : Module.Finite R (R × M) := Module.Finite.equiv e.symm
  have hfin : Module.Finite R M :=
    Module.Finite.of_surjective (LinearMap.snd R R M) LinearMap.snd_surjective
  obtain ⟨N, _, _, hNfin, hNfree, hKNfree⟩ :=
    Module.IsStablyFree.exist_free_prod R K
  let : Module.Finite R N := hNfin
  let : Module.Free R N := hNfree
  let : Module.Free R (K × N) := hKNfree
  let e' : (M × (R × N)) ≃ₗ[R] ((K × N) × R) :=
    (LinearEquiv.prodAssoc R M R N).symm |>.trans
      ((LinearEquiv.prodComm R M R).prodCongr (LinearEquiv.refl R N)) |>.trans
      (e.prodCongr (LinearEquiv.refl R N)) |>.trans
      (LinearEquiv.prodAssoc R K R N) |>.trans
      ((LinearEquiv.refl R K).prodCongr (LinearEquiv.prodComm R R N)) |>.trans
      (LinearEquiv.prodAssoc R K N R).symm
  let : Module.Free R (M × (R × N)) := Module.Free.of_equiv e'.symm
  exact ⟨hfin, Module.IsStablyFree.of_free_prod R M (R × N)⟩

/-- A unimodular element splits off a free rank-one factor. -/
private noncomputable def splitEvalEquiv {R Q : Type*} [CommRing R]
    [AddCommGroup Q] [Module R Q] (φ : Q →ₗ[R] R) (u : Q)
    (hu : φ u = 1) : Q ≃ₗ[R] R × LinearMap.ker φ := by
  let f : Q →ₗ[R] R × LinearMap.ker φ :=
    { toFun := fun x ↦ (φ x, ⟨x - φ x • u, by simp [LinearMap.mem_ker, hu]⟩)
      map_add' := by
        intro x y
        apply Prod.ext
        · simp
        · apply Subtype.ext
          change x + y - φ (x + y) • u = (x - φ x • u) + (y - φ y • u)
          simp only [map_add, add_smul]
          abel
      map_smul' := by
        intro r x
        apply Prod.ext
        · simp
        · apply Subtype.ext
          simp [smul_sub, mul_smul] }
  let g : R × LinearMap.ker φ →ₗ[R] Q :=
    { toFun := fun x ↦ x.1 • u + x.2
      map_add' := by intro x y; simp [add_smul]; abel
      map_smul' := by intro r x; simp [mul_smul, smul_add] }
  refine LinearEquiv.ofLinearMap f g ?_ ?_
  · apply LinearMap.ext
    intro x
    apply Prod.ext
    · change φ (x.1 • u + x.2) = x.1
      rw [map_add, map_smul, hu, smul_eq_mul, mul_one,
        LinearMap.mem_ker.mp x.2.property, add_zero]
    · apply Subtype.ext
      change (x.1 • u + x.2) - φ (x.1 • u + x.2) • u = x.2
      rw [map_add, map_smul, hu, smul_eq_mul, mul_one,
        LinearMap.mem_ker.mp x.2.property, add_zero]
      abel
  · apply LinearMap.ext
    intro x
    change φ x • u + (x - φ x • u) = x
    abel

/-- The right factor of a product isomorphic to a projective module is projective. -/
private theorem projective_right_of_prod_equiv {R M A B : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid A] [AddCommMonoid B]
    [Module R M] [Module R A] [Module R B] [Module.Projective R M]
    (e : (A × B) ≃ₗ[R] M) : Module.Projective R B := by
  let i : B →ₗ[R] M := e.toLinearMap.comp (LinearMap.inr R A B)
  let s : M →ₗ[R] B := (LinearMap.snd R A B).comp e.symm.toLinearMap
  apply Module.Projective.of_split i s
  ext b
  simp [i, s]

/-- Localisation commutes with binary products of modules. -/
private noncomputable def loc_prod_equiv {R : Type*} [CommRing R]
    (S : Submonoid R) (M N : Type*) [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] :
    LocalizedModule S (M × N) ≃ₗ[Localization S]
      LocalizedModule S M × LocalizedModule S N := by
  let f := LocalizedModule.mkLinearMap S (M × N)
  let g := (LocalizedModule.mkLinearMap S M).prodMap (LocalizedModule.mkLinearMap S N)
  exact IsLocalizedModule.mapEquiv S f g (Localization S) (LinearEquiv.refl R (M × N))

/-- Localisation of a linear equivalence. -/
private noncomputable def loc_equiv {R : Type*} [CommRing R]
    (S : Submonoid R) {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (e : M ≃ₗ[R] N) :
    LocalizedModule S M ≃ₗ[Localization S] LocalizedModule S N :=
  IsLocalizedModule.mapEquiv S (LocalizedModule.mkLinearMap S M)
    (LocalizedModule.mkLinearMap S N) (Localization S) e

/-- Infinite local rank is inherited by a product with the module on the right. -/
private theorem large_prod_right
    {R A P : Type*} [CommRing R]
    [AddCommGroup A] [Module R A]
    [AddCommGroup P] [Module R P]
    (hP : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl P)) :
    ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl (A × P)) := by
  intro p hAP
  let T := p.asIdeal.primeCompl
  let S := Localization.AtPrime p.asIdeal
  let : Module.Finite S (LocalizedModule T (A × P)) := hAP
  let pr : LocalizedModule T (A × P) →ₗ[S] LocalizedModule T P :=
    (LocalizedModule.equivTensorProduct T P).symm.toLinearMap.comp
      (((LinearMap.snd R A P).baseChange S).comp
        (LocalizedModule.equivTensorProduct T (A × P)).toLinearMap)
  have hpr : Function.Surjective pr :=
    (LocalizedModule.equivTensorProduct T P).symm.surjective.comp
      (((LinearMap.snd R A P).baseChange_surjective S LinearMap.snd_surjective).comp
        (LocalizedModule.equivTensorProduct T (A × P)).surjective)
  exact hP p (Module.Finite.of_surjective pr hpr)

/-- Infinite local rank passes to the right factor of a product isomorphic to the module. -/
private theorem loc_nonfinite_prod_right {R M A B : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup A] [AddCommGroup B]
    [Module R M] [Module R A] [Module R B] [Module.Finite R A]
    (e : (A × B) ≃ₗ[R] M)
    (hinf : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) :
    ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl B) := by
  intro p hB
  let S := p.asIdeal.primeCompl
  let ep := loc_prod_equiv S A B
  let em := loc_equiv S e
  have hA : Module.Finite (Localization S) (LocalizedModule S A) := inferInstance
  have hAB : Module.Finite (Localization S)
      (LocalizedModule S A × LocalizedModule S B) := by
    let := hA
    let := hB
    infer_instance
  have hM : Module.Finite (Localization S) (LocalizedModule S M) :=
    let := hAB
    Module.Finite.equiv (ep.symm.trans em)
  exact hinf p hM

/-- The kernel of a surjection onto a projective module has a complement. -/
private theorem exists_isCompl_ker_of_surjective {R P N : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N] [Module.Projective R N]
    (f : P →ₗ[R] N) (hf : Function.Surjective f) :
    ∃ M' : Submodule R P, IsCompl (LinearMap.ker f) M' := by
  obtain ⟨i, hi⟩ := Module.projective_lifting_property f LinearMap.id hf
  have hfi : ∀ y, f (i y) = y := fun y => DFunLike.congr_fun hi y
  let C : Submodule R P := LinearMap.range i
  let pr : P →ₗ[R] C := LinearMap.codRestrict C (i.comp f) fun x ↦ ⟨f x, rfl⟩
  have hpr : ∀ x : C, pr x = x := by
    rintro ⟨x, y, rfl⟩
    apply Subtype.ext
    show i (f (i y)) = i y
    rw [hfi]
  have hker : LinearMap.ker pr = LinearMap.ker f := by
    ext x
    constructor
    · intro hx
      have hx' : i (f x) = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
      exact LinearMap.mem_ker.mpr (by simpa [hfi] using congrArg f hx')
    · intro hx
      apply LinearMap.mem_ker.mpr
      apply Subtype.ext
      show i (f x) = 0
      rw [LinearMap.mem_ker.mp hx, map_zero]
  exact ⟨C, hker ▸ (LinearMap.isCompl_of_proj hpr).symm⟩

/-- A linear map on `R × P` killing `(1, p₀)` only sees `x` through `x.2 - x.1 • p₀`. -/
private theorem map_zero_sub_smul_eq {R P N : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    (h : R × P →ₗ[R] N) {p₀ : P} (h1 : h (1, p₀) = 0) (x : R × P) :
    h (0, x.2 - x.1 • p₀) = h x := by
  rw [show ((0 : R), x.2 - x.1 • p₀) = x - x.1 • (1, p₀) by ext <;> simp, map_sub, map_smul, h1,
    smul_zero, sub_zero]

/-- If `e' : R × P ≃ A × N` sends `(1, p₀)` into `A × 0`, then `R × ker f ≃ A`, where `f` is the
`N`-coordinate of `e'` restricted to `P`. -/
private theorem nonempty_prod_ker_equiv {R P A N : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [AddCommGroup A] [Module R A] [AddCommGroup N] [Module R N]
    (e' : (R × P) ≃ₗ[R] (A × N)) (p₀ : P) (h1 : (e' (1, p₀)).2 = 0) :
    Nonempty ((R × LinearMap.ker (((LinearMap.snd R A N).comp e'.toLinearMap).comp
      (LinearMap.inr R R P))) ≃ₗ[R] A) := by
  let h : R × P →ₗ[R] N := (LinearMap.snd R A N).comp e'.toLinearMap
  have h_one_p : h (1, p₀) = 0 := h1
  let M : Submodule R P := LinearMap.ker (h.comp (LinearMap.inr R R P))
  let j : R × M →ₗ[R] (R × P) :=
    { toFun := fun z ↦ (z.1, z.2.1 + z.1 • p₀)
      map_add' := by
        intro x y
        apply Prod.ext
        · rfl
        · show (x.2.1 + y.2.1) + (x.1 + y.1) • p₀ =
            (x.2.1 + x.1 • p₀) + (y.2.1 + y.1 • p₀)
          rw [add_smul]
          abel
      map_smul' := by
        intro r x
        apply Prod.ext
        · rfl
        · show r • x.2.1 + (r * x.1) • p₀ = r • (x.2.1 + x.1 • p₀)
          rw [smul_add, mul_smul] }
  have hj : ∀ z, h (j z) = 0 := by
    intro z
    have hpair : j z = z.1 • (1, p₀) + (0, z.2.1) := by
      apply Prod.ext
      · simp [j]
      · simp [j, add_comm]
    rw [hpair, map_add, map_smul, h_one_p, smul_zero, zero_add]
    exact LinearMap.mem_ker.mp z.2.property
  let t : R × M →ₗ[R] A := (LinearMap.fst R A N).comp (e'.toLinearMap.comp j)
  have htinj : Function.Injective t := by
    intro x y hxy
    have hjxy := e'.injective (Prod.ext hxy ((hj x).trans (hj y).symm))
    have hfst : x.1 = y.1 := by simpa [j] using congrArg Prod.fst hjxy
    apply Prod.ext
    · exact hfst
    · apply Subtype.ext
      have h := congrArg Prod.snd hjxy
      change x.2.1 + x.1 • p₀ = y.2.1 + y.1 • p₀ at h
      rw [hfst] at h
      exact add_right_cancel h
  have htsurj : Function.Surjective t := by
    intro y
    let x := e'.symm (y, 0)
    have hm : x.2 - x.1 • p₀ ∈ M := by
      apply LinearMap.mem_ker.mpr
      show h (0, x.2 - x.1 • p₀) = 0
      rw [map_zero_sub_smul_eq h h_one_p]
      show (e' x).2 = 0
      simp [x]
    refine ⟨(x.1, ⟨x.2 - x.1 • p₀, hm⟩), ?_⟩
    have hjx : j (x.1, ⟨x.2 - x.1 • p₀, hm⟩) = x := by
      apply Prod.ext
      · rfl
      · show (x.2 - x.1 • p₀) + x.1 • p₀ = x.2
        abel
    show (e' (j (x.1, ⟨x.2 - x.1 • p₀, hm⟩))).1 = y
    rw [hjx]
    simp [x]
  exact ⟨LinearEquiv.ofBijective t ⟨htinj, htsurj⟩⟩

/-- With a unimodular element of `Q` in hand, the free factor of `R × P ≅ K × Q` can be cancelled
against `R`, producing the finite stably free summand of `P` around `s`. -/
private theorem coordinate_cancel
    {R P K Q : Type*} [CommRing R]
    [AddCommGroup P] [Module R P]
    [AddCommGroup K] [Module R K]
    [AddCommGroup Q] [Module R Q]
    [Module.Finite R K] [Module.IsStablyFree R K] [Module.Projective R Q]
    (e : (R × P) ≃ₗ[R] (K × Q)) (s p₀ : P)
    (hs : (e (0, s)).2 = 0)
    (φ : Q →ₗ[R] R) (hu : φ ((e (1, p₀)).2) = 1) :
    ∃ M : Submodule R P,
      Module.Finite R M ∧ Module.IsStablyFree R M ∧ s ∈ M ∧
        ∃ M' : Submodule R P, IsCompl M M' := by
  classical
  let u := (e (1, p₀)).2
  let b : Q ≃ₗ[R] R × LinearMap.ker φ := splitEvalEquiv φ u hu
  let e' : (R × P) ≃ₗ[R] ((K × R) × LinearMap.ker φ) :=
    e.trans (((LinearEquiv.refl R K).prodCongr b).trans
      (LinearEquiv.prodAssoc R K R (LinearMap.ker φ)).symm)
  let h : R × P →ₗ[R] LinearMap.ker φ := (LinearMap.snd R (K × R) _).comp e'.toLinearMap
  have h_zero_s : h (0, s) = 0 := by
    apply Subtype.ext
    show ((e (0, s)).2 - φ ((e (0, s)).2) • u) = 0
    simp [hs]
  have h_one_p : h (1, p₀) = 0 := by
    apply Subtype.ext
    show u - φ u • u = 0
    simp [u, hu]
  let f : P →ₗ[R] LinearMap.ker φ := h.comp (LinearMap.inr R R P)
  have hf_surj : Function.Surjective f := by
    intro y
    let x := e'.symm ((0, 0), y)
    refine ⟨x.2 - x.1 • p₀, ?_⟩
    show h (0, x.2 - x.1 • p₀) = y
    rw [map_zero_sub_smul_eq h h_one_p]
    show (e' x).2 = y
    simp [x]
  have : Module.Projective R (LinearMap.ker φ) := projective_right_of_prod_equiv b.symm
  obtain ⟨et⟩ := nonempty_prod_ker_equiv e' p₀ h_one_p
  obtain ⟨hfin, hstable⟩ := free_stable_cancel et
  exact ⟨f.ker, hfin, hstable, LinearMap.mem_ker.mpr h_zero_s,
    exists_isCompl_ker_of_surjective f hf_surj⟩

/-- Cancelling `R` from an isomorphism `R × P ≅ K × Q` with `K` finite stably free. -/
private theorem cancel_equiv
    {R P K Q : Type*} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    [AddCommGroup K] [Module R K] [Module.Finite R K] [Module.IsStablyFree R K]
    [AddCommGroup Q] [Module R Q]
    (s : P)
    (hR : IsNoetherianRing (R ⧸ Ideal.jacobson (⊥ : Ideal R)))
    (hP : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl P))
    (e : (R × P) ≃ₗ[R] K × Q)
    (hs : (e (0, s)).2 = 0) :
    ∃ M : Submodule R P,
      Module.Finite R M ∧ Module.IsStablyFree R M ∧ s ∈ M ∧
        ∃ M' : Submodule R P, IsCompl M M' := by
  classical
  have : Module.Projective R Q := projective_right_of_prod_equiv e.symm
  let r : (R × P) →ₗ[R] Q := (LinearMap.snd R K Q).comp e.toLinearMap
  have hQ : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl Q) :=
    loc_nonfinite_prod_right e.symm (large_prod_right hP)
  let f : P →ₗ[R] Q := r.comp (LinearMap.inr R R P)
  let a : Q := r (1, (0 : P))
  have hspan : Submodule.span R {a} ⊔ LinearMap.range f = ⊤ := by
    apply top_unique
    intro q _
    let x := e.symm (0, q)
    have hq : q = r x := by
      show q = (e x).2
      simp [x]
    have hx : x = x.1 • (1, (0 : P)) + (0, x.2) := by
      ext <;> simp
    rw [hq, hx, map_add, map_smul]
    apply Submodule.add_mem_sup
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp : a ∈ ({a} : Set Q)))
    · exact ⟨x.2, rfl⟩
  obtain ⟨m, hm, φ, hφ⟩ :=
    exists_mem_add_unimodular (LinearMap.range f) a hR hQ hspan
  obtain ⟨p₀, rfl⟩ := hm
  have hu : φ ((e (1, p₀)).2) = 1 := by
    have heq : ((1 : R), p₀) = (1, (0 : P)) + (0, p₀) := by ext <;> simp
    calc
      φ ((e (1, p₀)).2) = φ (r (1, p₀)) := rfl
      _ = φ (r ((1, (0 : P)) + (0, p₀))) := congrArg (φ ∘ r) heq
      _ = φ (a + f p₀) := by
        show φ (r ((1, (0 : P)) + (0, p₀))) =
          φ (r (1, (0 : P)) + r (0, p₀))
        rw [map_add]
      _ = 1 := hφ
  exact coordinate_cancel e s p₀ hs φ hu

/-- If `P ≅ K × Q` carries `s` into the finite stably free factor `K`, then `s` lies in a finite
stably free direct summand of `P`. -/
private theorem summand_of_product_equiv
    {R P K Q : Type*} [CommRing R]
    [AddCommGroup P] [Module R P]
    [AddCommGroup K] [Module R K] [Module.Finite R K] [Module.IsStablyFree R K]
    [AddCommGroup Q] [Module R Q]
    (e : P ≃ₗ[R] K × Q) (s : P) (hs : (e s).2 = 0) :
    ∃ M : Submodule R P,
      Module.Finite R M ∧ Module.IsStablyFree R M ∧ s ∈ M ∧
        ∃ M' : Submodule R P, IsCompl M M' := by
  let i : K →ₗ[R] P := e.symm.toLinearMap.comp (LinearMap.inl R K Q)
  let j : Q →ₗ[R] P := e.symm.toLinearMap.comp (LinearMap.inr R K Q)
  let M := LinearMap.range i
  let M' := LinearMap.range j
  have hi : Function.Injective i := by
    intro a b hab
    have := congrArg e hab
    simpa [i] using this
  let ei : K ≃ₗ[R] M := LinearEquiv.ofBijective i.rangeRestrict
    ⟨(fun a b h => hi (congrArg Subtype.val h)), i.surjective_rangeRestrict⟩
  have hfin : Module.Finite R M := Module.Finite.equiv ei
  have hstable : Module.IsStablyFree R M := Module.IsStablyFree.equiv ei
  have hsM : s ∈ M := by
    refine ⟨(e s).1, ?_⟩
    have hp : e s = ((e s).1, 0) := by ext <;> simp [hs]
    show e.symm ((e s).1, 0) = s
    rw [← hp, e.symm_apply_apply]
  have hc : IsCompl M M' := by
    constructor
    · rw [disjoint_iff_inf_le]
      intro x hx
      obtain ⟨a, ha⟩ := hx.1
      obtain ⟨b, hb⟩ := hx.2
      have heq : (a, (0 : Q)) = (0, b) := by
        calc
          (a, (0 : Q)) = e (i a) := by simp [i]
          _ = e x := congrArg e ha
          _ = e (j b) := congrArg e hb.symm
          _ = (0, b) := by simp [j]
      have ha0 : a = 0 := congrArg Prod.fst heq
      rw [ha0] at ha
      simpa using ha.symm
    · rw [codisjoint_iff_le_sup]
      intro x _
      have hdecomp : x = i (e x).1 + j (e x).2 := by
        apply e.injective
        simp [i, j]
      rw [hdecomp]
      exact Submodule.add_mem_sup ⟨(e x).1, rfl⟩ ⟨(e x).2, rfl⟩
  exact ⟨M, hfin, hstable, hsM, M', hc⟩

/-- Cancelling a finite free factor `Fin n → R` one coordinate at a time. -/
private theorem cancel_fin
    {R : Type u} {P : Type v} [CommRing R]
    [AddCommGroup P] [Module R P] [Module.Projective R P]
    (s : P)
    (hR : IsNoetherianRing (R ⧸ Ideal.jacobson (⊥ : Ideal R)))
    (hP : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl P)) :
    ∀ n : ℕ, ∀ {K Q : Type (max u v)}, ∀ [AddCommGroup K] [Module R K]
      [Module.Finite R K] [Module.IsStablyFree R K]
      [AddCommGroup Q] [Module R Q],
      ∀ (e : ((Fin n → R) × P) ≃ₗ[R] K × Q),
        (e (0, s)).2 = 0 →
        ∃ M : Submodule R P,
          Module.Finite R M ∧ Module.IsStablyFree R M ∧ s ∈ M ∧
            ∃ M' : Submodule R P, IsCompl M M' := by
  intro n
  induction n with
  | zero =>
    intro K Q _ _ _ _ _ _ e hs
    let f : P →ₗ[R] ((Fin 0 → R) × P) := LinearMap.inr R (Fin 0 → R) P
    have hfsurj : Function.Surjective f := by
      rintro ⟨x, y⟩
      refine ⟨y, ?_⟩
      apply Prod.ext
      · funext i
        exact Fin.elim0 i
      · rfl
    have hfinj : Function.Injective f := by
      intro x y h
      exact congrArg Prod.snd h
    let ef : P ≃ₗ[R] ((Fin 0 → R) × P) :=
      LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
    have hzero : ef s = (0, s) := rfl
    exact summand_of_product_equiv (ef.trans e) s (by simpa [hzero] using hs)
  | succ n ih =>
    intro K Q _ _ _ _ _ _ e hs
    let C := (Fin n → R) × P
    let t : (R × C) ≃ₗ[R] ((Fin (n + 1) → R) × P) :=
      (LinearEquiv.prodAssoc R R (Fin n → R) P).symm.trans
        ((Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R)).prodCongr
          (LinearEquiv.refl R P))
    let e' : (R × C) ≃ₗ[R] K × Q := t.trans e
    have hlarge : ∀ p : MaximalSpectrum R,
        ¬ Module.Finite (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl C) := large_prod_right hP
    have hzero : t (0, (0, s)) = (0, s) := by
      apply Prod.ext
      · show (Fin.consLinearEquiv R (fun _ : Fin (n + 1) => R)) (0, 0) = 0
        exact map_zero _
      · rfl
    have hs' : (e' (0, (0, s))).2 = 0 := by simpa [e', hzero] using hs
    obtain ⟨M, hMfin, hMstable, hsM, Q', hc⟩ :=
      cancel_equiv (R := R) (P := C) (0, s) hR hlarge e' hs'
    let : Module.Finite R M := hMfin
    let : Module.IsStablyFree R M := hMstable
    let em : C ≃ₗ[R] M × Q' := (M.prodEquivOfIsCompl Q' hc).symm
    have hsM' : (em (0, s)).2 = 0 :=
      (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero M Q' hc).mpr hsM
    exact ih em hsM'

/-- A finite free module over a nontrivial ring is isomorphic to some `Fin n → R`. -/
private theorem finite_free_equiv_pi
    {R : Type u} [CommRing R] [Nontrivial R]
    {F : Type v} [AddCommGroup F] [Module R F]
    [Module.Finite R F] [Module.Free R F] :
    ∃ n : ℕ, Nonempty (F ≃ₗ[R] (Fin n → R)) := by
  classical
  let b := Module.Free.chooseBasis R F
  let ι := Module.Free.ChooseBasisIndex R F
  let : Finite ι := Module.Finite.finite_basis b
  let : Fintype ι := Fintype.ofFinite ι
  let e₁ : F ≃ₗ[R] (ι → R) :=
    b.repr.trans (Finsupp.linearEquivFunOnFinite R R ι)
  let e₂ : (Fin (Fintype.card ι) → R) ≃ₗ[R] (ι → R) :=
    LinearEquiv.piCongrLeft R (fun _ : ι => R) (Fintype.equivFin ι).symm
  exact ⟨Fintype.card ι, ⟨e₁.trans e₂.symm⟩⟩

/-- Every element of a projective module of infinite rank at all maximal ideals lies in a finite
stably free direct summand, provided the quotient by the Jacobson radical is Noetherian. -/
@[stacks 0GVJ]
theorem exists_finite_isStablyFree_summand_containing
    {R : Type u} [CommRing R] {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Projective R P] (s : P)
    (hR : IsNoetherianRing (R ⧸ Ideal.jacobson (⊥ : Ideal R)))
    (hP : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl P)) :
    ∃ M : Submodule R P,
      Module.Finite R M ∧ Module.IsStablyFree R M ∧ s ∈ M ∧
        ∃ M' : Submodule R P, IsCompl M M' := by
  classical
  by_cases htriv : Nontrivial R
  · let : Nontrivial R := htriv
    obtain ⟨F, hFc, hFm, hFfin, hFfree, K, hKfin, hKfree, hs, Q, hc⟩ :=
      exists_finite_free_summand_containing_zero_prod (R := R) (P := P) s
    let : AddCommGroup F := hFc
    let : Module R F := hFm
    let : Module.Finite R F := hFfin
    let : Module.Free R F := hFfree
    let : Module.Finite R K := hKfin
    let : Module.Free R K := hKfree
    let : Module.IsStablyFree R K := inferInstance
    obtain ⟨n, ⟨eF⟩⟩ := finite_free_equiv_pi (R := R) (F := F)
    let t : ((Fin n → R) × P) ≃ₗ[R] (F × P) :=
      eF.symm.prodCongr (LinearEquiv.refl R P)
    let e : ((Fin n → R) × P) ≃ₗ[R] K × Q :=
      t.trans (K.prodEquivOfIsCompl Q hc).symm
    have heq : t (0, s) = (0, s) := by simp [t]
    have hs' : (e (0, s)).2 = 0 := by
      show ((K.prodEquivOfIsCompl Q hc).symm (t (0, s))).2 = 0
      rw [heq]
      exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero K Q hc).mpr hs
    exact cancel_fin s hR hP n e hs'
  · let : Subsingleton R := (not_nontrivial_iff_subsingleton).mp htriv
    let : Subsingleton P := Module.subsingleton R P
    refine ⟨⊥, inferInstance, inferInstance, ?_, ⊤, isCompl_bot_top⟩
    simp [Subsingleton.elim s 0]

end FiniteStablyFreeSummand

section BigProjectivesAreFree

/-- Splitting one free rank-one factor off a projective module of infinite local rank. -/
private theorem exists_rank_one_split {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    (hR : IsNoetherianRing (R ⧸ Ideal.jacobson (⊥ : Ideal R)))
    (hinf : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) :
    ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q),
      Nonempty ((R × Q) ≃ₗ[R] M) ∧ Module.Projective R Q ∧
      (∀ p : MaximalSpectrum R,
        ¬ Module.Finite (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl Q)) := by
  obtain ⟨m, _, φ, hφ⟩ :=
    exists_mem_add_unimodular (⊤ : Submodule R M) 0 hR hinf (by simp)
  have hm : φ m = 1 := by simpa using hφ
  let e := (splitEvalEquiv φ m hm).symm
  refine ⟨φ.ker, inferInstance, inferInstance, ⟨e⟩,
    projective_right_of_prod_equiv e, ?_⟩
  exact loc_nonfinite_prod_right e hinf

/-- Splitting `n` free rank-one factors off a projective module of infinite local rank. -/
private theorem exists_split_fin {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    (hR : IsNoetherianRing (R ⧸ Ideal.jacobson (⊥ : Ideal R)))
    (hinf : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) (n : ℕ) :
    ∃ (Q : Type v) (_ : AddCommGroup Q) (_ : Module R Q),
      Nonempty (((Fin n → R) × Q) ≃ₗ[R] M) ∧ Module.Projective R Q ∧
      (∀ p : MaximalSpectrum R,
        ¬ Module.Finite (Localization.AtPrime p.asIdeal)
          (LocalizedModule p.asIdeal.primeCompl Q)) := by
  induction n with
  | zero =>
      refine ⟨M, inferInstance, inferInstance, ?_, inferInstance, hinf⟩
      exact ⟨LinearEquiv.uniqueProd⟩
  | succ n ih =>
      obtain ⟨Q, hQa, hQm, ⟨e⟩, hQproj, hQinf⟩ := ih
      let := hQa
      let := hQm
      let := hQproj
      obtain ⟨Q', hQ'a, hQ'm, ⟨e'⟩, hQ'proj, hQ'inf⟩ :=
        exists_rank_one_split hR hQinf
      let := hQ'a
      let := hQ'm
      let efin : (Fin (n+1) → R) ≃ₗ[R] (Fin n → R) × R :=
        (Fin.consLinearEquiv R (fun _ : Fin (n+1) => R)).symm.trans
          (LinearEquiv.prodComm R R (Fin n → R))
      let enew : ((Fin (n+1) → R) × Q') ≃ₗ[R] M :=
        (efin.prodCongr (LinearEquiv.refl R Q')).trans
          ((LinearEquiv.prodAssoc R (Fin n → R) R Q').trans
            ((LinearEquiv.prodCongr (LinearEquiv.refl R (Fin n → R)) e').trans e))
      exact ⟨Q', hQ'a, hQ'm, ⟨enew⟩, hQ'proj, hQ'inf⟩

/-- A free left factor of a product isomorphic to `M` becomes a free direct summand of `M`. -/
private theorem free_summand_of_prod_equiv {R M A B : Type*} [Semiring R]
    [AddCommMonoid M] [AddCommMonoid A] [AddCommMonoid B]
    [Module R M] [Module R A] [Module R B] [Module.Free R A]
    (e : (A × B) ≃ₗ[R] M) :
    ∃ F G : Submodule R M, IsCompl F G ∧ Module.Free R F ∧
      ∀ a : A, e (a, 0) ∈ F := by
  let L : Submodule R (A × B) := (LinearMap.inl R A B).range
  let T : Submodule R (A × B) := (LinearMap.inr R A B).range
  let F := L.map e.toLinearMap
  let G := T.map e.toLinearMap
  refine ⟨F, G, Submodule.isCompl_map e LinearMap.isCompl_range_inl_inr, ?_, ?_⟩
  · let ei : A ≃ₗ[R] L := LinearEquiv.ofInjective (LinearMap.inl R A B) (by
      intro x y h
      exact congrArg Prod.fst h)
    let eF : L ≃ₗ[R] F :=
      Submodule.equivMapOfInjective e.toLinearMap e.injective L
    exact Module.Free.of_equiv (ei.trans eF)
  · intro a
    exact ⟨(a, 0), ⟨a, rfl⟩, rfl⟩

/-- The complement of a submodule of a projective module is projective. -/
private theorem projective_of_compl {R M : Type*} [Ring R]
    [AddCommGroup M] [Module R M] [Module.Projective R M]
    {A B : Submodule R M} (h : IsCompl A B) : Module.Projective R B :=
  Module.Projective.of_split B.subtype (B.projectionOnto A h.symm)
    (Submodule.projectionOnto_comp_subtype h.symm)

/-- Every element of a projective module of infinite local rank lies in a free direct summand. -/
private theorem exists_free_summand_containing {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M]
    (hR : IsNoetherianRing (R ⧸ Ideal.jacobson (⊥ : Ideal R)))
    (hinf : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) (x : M) :
    ∃ F G : Submodule R M, IsCompl F G ∧ Module.Free R F ∧ x ∈ F := by
  obtain ⟨K, hKfin, hKstable, hxK, K', hcompl⟩ :=
    exists_finite_isStablyFree_summand_containing x hR hinf
  have := hKstable
  have : Module.Projective R K' := projective_of_compl hcompl
  have hK'inf : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl K') :=
    loc_nonfinite_prod_right (K.prodEquivOfIsCompl K' hcompl) hinf
  obtain ⟨N, hNa, hNm, hNfin, hNfree, hKNfree⟩ :=
    Module.IsStablyFree.exist_free_prod R K
  let := hNa
  let := hNm
  let := hNfin
  let := hNfree
  let κ := Module.Free.ChooseBasisIndex R N
  let : Fintype κ := Module.Free.ChooseBasisIndex.fintype R N
  let n := Fintype.card κ
  let eN : N ≃ₗ[R] (Fin n → R) :=
    (Module.Free.chooseBasis R N).equivFun.trans
      (LinearEquiv.funCongrLeft R R (Fintype.equivFin κ).symm)
  obtain ⟨Q, hQa, hQm, ⟨e'⟩, _, _⟩ := exists_split_fin hR hK'inf n
  let := hQa
  let := hQm
  let eM : ((K × N) × Q) ≃ₗ[R] M :=
    (((LinearEquiv.prodCongr (LinearEquiv.prodCongr (LinearEquiv.refl R K) eN)
      (LinearEquiv.refl R Q)).trans
      (LinearEquiv.prodAssoc R K (Fin n → R) Q)).trans
      (LinearEquiv.prodCongr (LinearEquiv.refl R K) e')).trans
      (K.prodEquivOfIsCompl K' hcompl)
  let : Module.Free R (K × N) := hKNfree
  obtain ⟨F, G, hFG, hFfree, hmem⟩ := free_summand_of_prod_equiv eM
  refine ⟨F, G, hFG, hFfree, ?_⟩
  have he : eM ((⟨x, hxK⟩, 0), 0) = x := by
    simp [eM, eN]
  rw [← he]
  exact hmem (⟨x, hxK⟩, 0)

/-- A projective module of infinite local rank has Kaplansky's property (P). -/
private theorem propertyP_of_projective_large {R : Type u} {M : Type v}
    [CommRing R] [AddCommGroup M] [Module R M] [Module.Projective R M]
    (hR : IsNoetherianRing (R ⧸ Ideal.jacobson (⊥ : Ideal R)))
    (hinf : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl M)) :
    PropertyP R M := by
  intro N N' hNN' hfree hfin x hx
  let : Module.Finite R N' := hfin
  have : Module.Projective R N := projective_of_compl hNN'.symm
  have hNinf : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl N) :=
    loc_nonfinite_prod_right (N'.prodEquivOfIsCompl N hNN'.symm) hinf
  obtain ⟨F0, G0, hFG, hFfree, hxF⟩ :=
    exists_free_summand_containing hR hNinf (⟨x, hx⟩ : N)
  let F : Submodule R M := F0.map N.subtype
  let G : Submodule R M := G0.map N.subtype
  refine ⟨F, ⟨⟨G, ?_, ?_⟩, ?_⟩, ?_⟩
  · exact Submodule.disjoint_map N.injective_subtype hFG.disjoint
  · rw [← Submodule.map_sup, hFG.sup_eq_top, Submodule.map_subtype_top]
  · exact Module.Free.of_equiv
      (Submodule.equivMapOfInjective N.subtype N.injective_subtype F0)
  · exact ⟨⟨x, hx⟩, hxF, rfl⟩

/-- A countably generated projective module over a commutative ring is free if the quotient by
the Jacobson radical is Noetherian and every localization at a maximal ideal has infinite
rank. -/
@[stacks 0GVK]
theorem free_of_countablyGenerated_projective_of_localization_not_finite
    {R : Type u} [CommRing R] {P : Type v} [AddCommGroup P] [Module R P]
    [Module.Projective R P]
    (hR : IsNoetherianRing (R ⧸ Ideal.jacobson (⊥ : Ideal R)))
    (hP : Module.CountablyGenerated R P)
    (hPinf : ∀ p : MaximalSpectrum R,
      ¬ Module.Finite (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl P)) :
    Module.Free R P :=
  countablyGenerated_propertyP_free hP (propertyP_of_projective_large hR hPinf)

end BigProjectivesAreFree
