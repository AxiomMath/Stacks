module

public import Mathlib.RingTheory.LocalRing.Module
public import StacksCore.RingTheory.Nakayama
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Smoothing.SyntomicCompleteIntersectionExtension
public import StacksFrontier.RingTheory.Syntomic.ConormalRank
public import StacksFrontier.RingTheory.Syntomic.SquarePresentation

/-!
# Lifting a finite syntomic algebra with a section along a small extension

Let `C' → C` be a surjection of commutative rings with nilpotent kernel `I`, with `C` artinian,
and let `B` be a finite syntomic `C`-algebra with a section `B → C`. Then `B` and its section
lift: there are a finite syntomic `C'`-algebra `B'`, a section `B' → C'`, and a surjection
`B' → B` with kernel `IB'`, that is an identification of `B' ⊗_{C'} C` with `B`, carrying the one
section to the other. For a small extension of artinian local rings this is the deformation
problem that Stacks 0FL3 reduces the smoothness of `V_d` over `Z` to, together with the solution
the remark gives for it.

## Main results

* `Algebra.IsRelativeGlobalCompleteIntersection.of_finite_syntomic`: a finite syntomic algebra
  with semilocal spectrum is a relative global complete intersection.
* `Algebra.exists_square_presentation_section`: a finite syntomic algebra with a section over an
  artinian base has a presentation with as many relations as variables in which the section is
  the evaluation of every variable at zero.
* `Algebra.exists_finite_syntomic_section_lift`: the lift.

## Implementation notes

*The square presentation.* The conormal module `I/I²` of any finite polynomial presentation of a
quasi-finite syntomic algebra `B` over `C` is finite projective of rank the number of variables
(`Algebra.rankAtStalk_cotangent_eq_card_of_quasiFinite_syntomic`). When `Spec B` is semilocal —
as it is for `B` finite over an artinian `C` — a finite flat module of constant rank is free
(Lemma 02M9), so Lemma 07CF produces a presentation whose relations are a basis of its conormal
module, with one more variable and one more relation than the given presentation; it is therefore
square. Quasi-finiteness makes the dimension condition of Definition 00SP automatic, so this is a
relative global complete intersection (`Algebra.exists_square_presentation`).

*The translation.* A section `σ : B → C` of a square presentation `B = C[x_1, …, x_n]/(f_1, …,
f_n)` need not kill the variables, but subtracting `σ(x_i)` from `x_i` is an automorphism of the
polynomial ring carrying the presentation to one that it does: the generators `x_i - σ(x_i)` lie
in the kernel of `σ`, and `σ` becomes the evaluation of every variable at zero. Each relation then
has vanishing constant term, being in the kernel of that evaluation.

*The lift.* Lifting the coefficients of `f_i` and correcting the constant term to zero gives
`f'_i ∈ C'[x_1, …, x_n]` with `f'_i(0) = 0` reducing to `f_i`, and `B' = C'[x_1, …, x_n]/(f'_1, …,
f'_n)` with the evaluation of the variables at zero as its section. The reduction map is the
composite `C'[x] → C[x] → B`; its kernel is `(f'_1, …, f'_n) + I·C'[x]` because `C'[x] → C[x]` is
surjective with kernel `I·C'[x]`, which is the identification of `B' ⊗_{C'} C` with `B`. So `B'`
is finite over `C'` by Nakayama for a nilpotent ideal (00DV (12)) and its presentation is square,
whence it is a relative global complete intersection, zero-dimensional fibres coming from
finiteness, and syntomic by Lemma 00SW.

*The geometric assertion.* That `V_d = π_d^{-1}(U_d)` is smooth over `Z` is
`AlgebraicGeometry.universalSyntomicPreimage_smooth`, deduced from the lemma proved here by the
infinitesimal lifting criterion of Tag 02HX, which is the criterion the source uses for the
companion Lemma 0FL1: a morphism locally of finite type over a locally Noetherian base is smooth
at a point exactly when it lifts against small extensions, and a small extension is a surjection
of *artinian local* rings (`InfinitesimalLifting.IsSmallExtension`). Its target is therefore
semilocal, which is all the lemma proved here asks of `C`, and the criterion itself is
`InfinitesimalLifting.infinitesimal_lifting_criterion_for_smoothness`. The criterion of Tag 02H6,
against first-order thickenings of arbitrary affine schemes, would not serve: the implication
(1) ⟹ (4) of Tag 0FKY over an arbitrary base is
`AlgebraicGeometry.hasAffineSquarePresentation_of_finite_syntomic`, and what it gives is a square
presentation only after shrinking `Spec C` to a basic open, so the construction above would lift
`B → C` only locally on `Spec C`, whereas that criterion asks for a lift over all of `Spec C'`.
The lifting problem for `V_d` is translated into the one solved here by the functor of points of
`V_d` (`AlgebraicGeometry.pointedSyntomicEquiv`): a point of `V_d` over a scheme is a
multiplication table whose classifying morphism factors through `U_d` together with the
coordinates of a section of the algebra of that table. The statement of Tag 0FL1, that `U_d`
itself is smooth over `Z`, is `AlgebraicGeometry.universalSyntomicOpen_smooth`.

## References

* [Stacks Project, Tag 0FL3](https://stacks.math.columbia.edu/tag/0FL3)
* [Stacks Project, Tag 0FL1](https://stacks.math.columbia.edu/tag/0FL1)
* [Stacks Project, Tag 0FKY](https://stacks.math.columbia.edu/tag/0FKY)
* [Stacks Project, Tag 02HX](https://stacks.math.columbia.edu/tag/02HX)
* [Stacks Project, Tag 00SW](https://stacks.math.columbia.edu/tag/00SW)
* [Stacks Project, Tag 00SP](https://stacks.math.columbia.edu/tag/00SP)
* [Stacks Project, Tag 07CF](https://stacks.math.columbia.edu/tag/07CF)
* [Stacks Project, Tag 02M9](https://stacks.math.columbia.edu/tag/02M9)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

@[expose] public section

universe u

open scoped TensorProduct

/-- A finite syntomic algebra whose spectrum is semilocal is a relative global complete
intersection: the conormal module of a presentation is finite flat of rank the number of
variables, hence free, so Lemma 07CF makes the presentation square. -/
theorem Algebra.IsRelativeGlobalCompleteIntersection.of_finite_syntomic
    (C B : Type u) [CommRing C] [CommRing B] [Algebra C B]
    [Algebra.Syntomic C B] [Module.Finite C B] [Finite (MaximalSpectrum B)] :
    Algebra.IsRelativeGlobalCompleteIntersection C B := by
  obtain ⟨n, f, hf, -⟩ := Algebra.FinitePresentation.out (R := C) (A := B)
  have heval : MvPolynomial.aeval (fun i : Fin n => f (MvPolynomial.X i)) = f := by
    ext i
    simp
  let P : Algebra.Generators C B (Fin n) :=
    Algebra.Generators.ofSurjective (fun i => f (MvPolynomial.X i)) (by rw [heval]; exact hf)
  have hlci : RingHom.IsLocalCompleteIntersection (algebraMap C B) :=
    (NaiveCotangent.hasTorAmplitude_tfae_syntomic C B (Algebra.Syntomic C B) (by simp)
      (RingHom.IsLocalCompleteIntersection (algebraMap C B)) (by simp)).mp
      ‹Algebra.Syntomic C B›
  obtain ⟨hfin, hproj⟩ := P.cotangent_finite_projective_of_isLocalCompleteIntersection hlci
  have : Module.Finite B P.toExtension.Cotangent := hfin
  have : Module.Projective B P.toExtension.Cotangent := hproj
  have : Module.Flat B P.toExtension.Cotangent := Module.Flat.of_projective
  have hfree : Module.Free B P.toExtension.Cotangent := by
    refine Module.free_of_flat_of_finrank_eq B _ n fun Pm => ?_
    have hmax : Pm.asIdeal.IsMaximal := Pm.isMaximal
    let : Field (B ⧸ Pm.asIdeal) := Ideal.Quotient.field _
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum (B ⧸ Pm.asIdeal)) := inferInstance
    have h1 := Module.rankAtStalk_baseChange (R := B) (M := P.toExtension.Cotangent)
      (S := B ⧸ Pm.asIdeal) q
    have h2 := Algebra.rankAtStalk_cotangent_eq_card_of_quasiFinite_syntomic P
      (PrimeSpectrum.comap (algebraMap B (B ⧸ Pm.asIdeal)) q)
    have h3 : Module.rankAtStalk (R := B ⧸ Pm.asIdeal)
        ((B ⧸ Pm.asIdeal) ⊗[B] P.toExtension.Cotangent) =
        (Module.finrank (B ⧸ Pm.asIdeal) ((B ⧸ Pm.asIdeal) ⊗[B] P.toExtension.Cotangent) :
          PrimeSpectrum (B ⧸ Pm.asIdeal) → ℕ) :=
      Module.rankAtStalk_eq_finrank_of_free
    have h4 := congrFun h3 q
    simp only [Pi.natCast_apply, Nat.cast_id] at h4
    omega
  exact Stacks.Smoothing.syntomic_freeConormal_isRelativeGlobalCompleteIntersection ⟨n, P, hfree⟩

/-- The ideal spanned by elements killed by a ring homomorphism lies in its kernel. -/
private theorem span_range_le_ker_of_forall_eq_zero {R S F ι : Type*} [CommRing R] [Semiring S]
    [FunLike F R S] [RingHomClass F R S] (f : F) (g : ι → R) (h : ∀ i, f (g i) = 0) :
    Ideal.span (Set.range g) ≤ RingHom.ker f := by
  rw [Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact h i

/-- A finite syntomic algebra with a section over an artinian base has a presentation by as many
relations as variables in which the section is the evaluation of every variable at zero. -/
theorem Algebra.exists_square_presentation_section
    (C B : Type u) [CommRing C] [CommRing B] [Algebra C B]
    [IsArtinianRing C] [Algebra.Syntomic C B] [Module.Finite C B] [Nontrivial B]
    (σ : B →ₐ[C] C) :
    ∃ (n : ℕ) (val : Fin n → B) (g : Fin n → MvPolynomial (Fin n) C),
      Function.Surjective (MvPolynomial.aeval val : MvPolynomial (Fin n) C →ₐ[C] B) ∧
      RingHom.ker (MvPolynomial.aeval val : MvPolynomial (Fin n) C →ₐ[C] B) =
        Ideal.span (Set.range g) ∧
      σ.comp (MvPolynomial.aeval val) =
        (MvPolynomial.aeval (fun _ => 0) : MvPolynomial (Fin n) C →ₐ[C] C) := by
  classical
  have : IsArtinianRing B := IsArtinianRing.of_finite C B
  have : Algebra.IsRelativeGlobalCompleteIntersection C B :=
    Algebra.IsRelativeGlobalCompleteIntersection.of_finite_syntomic C B
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum B) := inferInstance
  have := q.isPrime
  obtain ⟨n, P, -⟩ := Algebra.exists_square_presentation (R := C) (S := B) q.asIdeal
  set s : Fin n → C := fun i => σ (P.val i) with hs
  set val : Fin n → B := fun i => P.val i - algebraMap C B (s i) with hval
  set t0 : MvPolynomial (Fin n) C →ₐ[C] MvPolynomial (Fin n) C :=
    MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C (s i) with ht0
  set t1 : MvPolynomial (Fin n) C →ₐ[C] MvPolynomial (Fin n) C :=
    MvPolynomial.aeval fun i => MvPolynomial.X i - MvPolynomial.C (s i) with ht1
  have ht10 : ∀ p, t0 (t1 p) = p := by
    have h : t0.comp t1 = AlgHom.id C _ := by
      ext i
      simp [ht0, ht1]
    exact AlgHom.congr_fun h
  have hev : ∀ p, (MvPolynomial.aeval val : MvPolynomial (Fin n) C →ₐ[C] B) (t0 p) =
      MvPolynomial.aeval P.val p := by
    have h : (MvPolynomial.aeval val : MvPolynomial (Fin n) C →ₐ[C] B).comp t0 =
        MvPolynomial.aeval P.val := by
      ext i
      simp [ht0, hval]
    exact AlgHom.congr_fun h
  have hrel : ∀ r, (MvPolynomial.aeval P.val : MvPolynomial (Fin n) C →ₐ[C] B)
      (P.relation r) = 0 := by
    intro r
    have h := P.relation_mem_ker r
    rwa [Algebra.Generators.ker_eq_ker_aeval_val, RingHom.mem_ker] at h
  refine ⟨n, val, fun r => t0 (P.relation r), fun b => ⟨t0 (P.σ b), ?_⟩, ?_, ?_⟩
  · exact (hev _).trans (P.aeval_val_σ b)
  · apply le_antisymm
    · intro p hp
      have hp1 : t1 p ∈ RingHom.ker (MvPolynomial.aeval P.val :
          MvPolynomial (Fin n) C →ₐ[C] B) := by
        rwa [RingHom.mem_ker, ← hev, ht10]
      rw [← Algebra.Generators.ker_eq_ker_aeval_val, ← P.span_range_relation_eq_ker,
        Ideal.mem_span_range_iff_exists_fun] at hp1
      obtain ⟨c, hc⟩ := hp1
      rw [Ideal.mem_span_range_iff_exists_fun]
      refine ⟨fun r => t0 (c r), ?_⟩
      rw [← ht10 p, ← hc]
      simp [map_sum, map_mul]
    · exact span_range_le_ker_of_forall_eq_zero _ _ fun r => (hev _).trans (hrel r)
  · ext i
    simp [hval, hs]

/-- The lift of Stacks 0FL3 from a square presentation whose relations have vanishing constant
term, which is what a section killing the variables provides. -/
private theorem Algebra.exists_finite_syntomic_lift_of_square_presentation
    {C' C B : Type u} [CommRing C'] [CommRing C] [CommRing B] [Algebra C' C] [Algebra C B]
    [Module.Finite C B]
    (hsurj : Function.Surjective (algebraMap C' C))
    (hnil : IsNilpotent (RingHom.ker (algebraMap C' C)))
    (σ : B →ₐ[C] C) {n : ℕ} (val : Fin n → B) (g : Fin n → MvPolynomial (Fin n) C)
    (hevsurj : Function.Surjective (MvPolynomial.aeval val : MvPolynomial (Fin n) C →ₐ[C] B))
    (hker : RingHom.ker (MvPolynomial.aeval val : MvPolynomial (Fin n) C →ₐ[C] B) =
      Ideal.span (Set.range g))
    (hsecev : σ.comp (MvPolynomial.aeval val) =
      (MvPolynomial.aeval (fun _ => 0) : MvPolynomial (Fin n) C →ₐ[C] C)) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra C' B'),
      Algebra.Syntomic C' B' ∧ Module.Finite C' B' ∧
        ∃ (sec : B' →ₐ[C'] C') (φ : B' →+* B),
          Function.Surjective φ ∧
          RingHom.ker φ = Ideal.map (algebraMap C' B') (RingHom.ker (algebraMap C' C)) ∧
          (∀ c : C', φ (algebraMap C' B' c) = algebraMap C B (algebraMap C' C c)) ∧
          (∀ b : B', σ (φ b) = algebraMap C' C (sec b)) := by
  classical
  set I := RingHom.ker (algebraMap C' C) with hIdef
  set ψ : MvPolynomial (Fin n) C' →+* MvPolynomial (Fin n) C :=
    MvPolynomial.map (algebraMap C' C) with hψdef
  have hψC : ∀ c : C', ψ (MvPolynomial.C c) = MvPolynomial.C (algebraMap C' C c) := fun c => by
    simp [hψdef]
  have hψsurj : Function.Surjective ψ := MvPolynomial.map_surjective _ hsurj
  have hgker : ∀ r, (MvPolynomial.aeval val : MvPolynomial (Fin n) C →ₐ[C] B) (g r) = 0 := by
    intro r
    rw [← RingHom.mem_ker, hker]
    exact Ideal.subset_span ⟨r, rfl⟩
  have hgconst : ∀ r, MvPolynomial.constantCoeff (g r) = 0 := by
    intro r
    have h1 := AlgHom.congr_fun hsecev (g r)
    rw [AlgHom.comp_apply, hgker r, map_zero] at h1
    simpa using h1.symm
  choose u hu using fun r => hψsurj (g r)
  set g' : Fin n → MvPolynomial (Fin n) C' := fun r =>
    u r - MvPolynomial.C (MvPolynomial.constantCoeff (u r)) with hg'def
  have hcu : ∀ r, algebraMap C' C (MvPolynomial.constantCoeff (u r)) = 0 := by
    intro r
    have h := MvPolynomial.constantCoeff_map (algebraMap C' C) (u r)
    rw [← hψdef, hu r, hgconst r] at h
    exact h.symm
  have hg'map : ∀ r, ψ (g' r) = g r := by
    intro r
    have h1 : ψ (MvPolynomial.C (MvPolynomial.constantCoeff (u r))) = 0 := by
      rw [hψC, hcu r, map_zero]
    calc ψ (g' r) = ψ (u r) - ψ (MvPolynomial.C (MvPolynomial.constantCoeff (u r))) := by
          simp only [hg'def]
          exact map_sub _ _ _
      _ = g r := by rw [h1, hu r, sub_zero]
  have hg'const : ∀ r, MvPolynomial.constantCoeff (g' r) = 0 := by
    intro r
    simp [hg'def]
  set J' : Ideal (MvPolynomial (Fin n) C') := Ideal.span (Set.range g') with hJ'def
  set χ : MvPolynomial (Fin n) C' →+* B :=
    ((MvPolynomial.aeval val : MvPolynomial (Fin n) C →ₐ[C] B) :
      MvPolynomial (Fin n) C →+* B).comp ψ with hχdef
  have hχapply : ∀ p, χ p = (MvPolynomial.aeval val : MvPolynomial (Fin n) C →ₐ[C] B) (ψ p) :=
    fun p => rfl
  have hχsurj : Function.Surjective χ := by
    intro b
    obtain ⟨p, hp⟩ := hevsurj b
    obtain ⟨p', hp'⟩ := hψsurj p
    exact ⟨p', by rw [hχapply, hp', hp]⟩
  have hJχ : J' ≤ RingHom.ker χ := by
    refine span_range_le_ker_of_forall_eq_zero _ _ fun r => ?_
    rw [hχapply, hg'map r]
    exact hgker r
  have hkerψ : RingHom.ker ψ = Ideal.map (MvPolynomial.C : C' →+* MvPolynomial (Fin n) C') I :=
    MvPolynomial.ker_map _
  have hkerχ : RingHom.ker χ =
      J' ⊔ Ideal.map (MvPolynomial.C : C' →+* MvPolynomial (Fin n) C') I := by
    refine le_antisymm (fun p hp => ?_) (sup_le hJχ ?_)
    · have hp1 : ψ p ∈ Ideal.span (Set.range g) := by
        rw [← hker, RingHom.mem_ker]
        rw [RingHom.mem_ker, hχapply] at hp
        exact hp
      rw [Ideal.mem_span_range_iff_exists_fun] at hp1
      obtain ⟨c, hc⟩ := hp1
      choose c' hc' using fun r => hψsurj (c r)
      have hv : ψ (∑ r, c' r * g' r) = ψ p := by
        rw [map_sum, ← hc]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [map_mul, hc' r, hg'map r]
      have hd : p - ∑ r, c' r * g' r ∈ RingHom.ker ψ := by
        rw [RingHom.mem_ker, map_sub, hv, sub_self]
      have hsum : (∑ r, c' r * g' r) ∈ J' := by
        rw [hJ'def, Ideal.mem_span_range_iff_exists_fun]
        exact ⟨c', rfl⟩
      have := Submodule.add_mem _ (Submodule.mem_sup_right (hkerψ ▸ hd))
        (Submodule.mem_sup_left hsum)
      simpa using this
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, hχapply]
      rw [hψC, show algebraMap C' C a = 0 from ha]
      simp
  set φ : (MvPolynomial (Fin n) C' ⧸ J') →+* B := Ideal.Quotient.lift J' χ hJχ with hφdef
  have hφmk : ∀ p, φ (Ideal.Quotient.mk J' p) = χ p := fun p => rfl
  have hφsurj : Function.Surjective φ := by
    intro b
    obtain ⟨p, hp⟩ := hχsurj b
    exact ⟨Ideal.Quotient.mk J' p, by rw [hφmk, hp]⟩
  have hkerφ : RingHom.ker φ =
      Ideal.map (algebraMap C' (MvPolynomial (Fin n) C' ⧸ J')) I := by
    rw [hφdef, Ideal.ker_quotient_lift _ hJχ, hkerχ, Ideal.map_sup, Ideal.map_quotient_self,
      bot_sup_eq, Ideal.map_map]
    rfl
  have hsecJ : J' ≤ RingHom.ker (MvPolynomial.aeval (fun _ => 0) :
      MvPolynomial (Fin n) C' →ₐ[C'] C') :=
    span_range_le_ker_of_forall_eq_zero _ _ fun r => by simpa using hg'const r
  set sec : (MvPolynomial (Fin n) C' ⧸ J') →ₐ[C'] C' :=
    Ideal.Quotient.liftₐ J' (MvPolynomial.aeval (fun _ => 0)) fun _ ha => hsecJ ha with hsecdef
  have hsecmk : ∀ p, sec (Ideal.Quotient.mk J' p) =
      (MvPolynomial.aeval (fun _ => 0) : MvPolynomial (Fin n) C' →ₐ[C'] C') p := fun p => rfl
  have hcompat1 : ∀ c : C', φ (algebraMap C' (MvPolynomial (Fin n) C' ⧸ J') c) =
      algebraMap C B (algebraMap C' C c) := by
    intro c
    have h1 : algebraMap C' (MvPolynomial (Fin n) C' ⧸ J') c =
        Ideal.Quotient.mk J' (MvPolynomial.C c) := rfl
    rw [h1, hφmk, hχapply]
    rw [hψC]
    simp
  have hcompat2 : ∀ b, σ (φ b) = algebraMap C' C (sec b) := by
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [hφmk, hsecmk, hχapply]
    rw [← AlgHom.comp_apply, hsecev]
    have h2 : MvPolynomial.constantCoeff (ψ p) =
        algebraMap C' C (MvPolynomial.constantCoeff p) := by
      simp [hψdef, MvPolynomial.constantCoeff_map]
    simp [h2]
  have hsmul : ∀ (c : C') (z : MvPolynomial (Fin n) C' ⧸ J'),
      φ (c • z) = algebraMap C' C c • φ z := by
    intro c z
    rw [Algebra.smul_def, map_mul, hcompat1, Algebra.smul_def]
  have hfin : Module.Finite C' (MvPolynomial (Fin n) C' ⧸ J') := by
    obtain ⟨sB, hsB⟩ := Module.finite_def.mp (inferInstance : Module.Finite C B)
    choose lf hlf using hφsurj
    refine Module.finite_def.mpr ⟨sB.image lf, ?_⟩
    refine Submodule.span_eq_top_of_span_image_mkQ_eq_top_of_isNilpotent I hnil _ ?_
    rw [Submodule.eq_top_iff']
    intro y
    obtain ⟨x, rfl⟩ := (I • (⊤ : Submodule C' (MvPolynomial (Fin n) C' ⧸ J'))).mkQ_surjective y
    have hx : φ x ∈ Submodule.span C (↑sB : Set B) := by rw [hsB]; exact Submodule.mem_top
    rw [Submodule.mem_span_finset] at hx
    obtain ⟨cf, -, hcf⟩ := hx
    choose cl hcl using fun b => hsurj (cf b)
    have hx0 : φ (∑ b ∈ sB, cl b • lf b) = φ x := by
      set_option synthInstance.maxHeartbeats 200000 in rw [map_sum φ, ← hcf]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hsmul, hcl b, hlf b]
    have hd : x - ∑ b ∈ sB, cl b • lf b ∈
        I • (⊤ : Submodule C' (MvPolynomial (Fin n) C' ⧸ J')) := by
      have hmem : x - ∑ b ∈ sB, cl b • lf b ∈ RingHom.ker φ := by
        rw [RingHom.mem_ker, RingHom.map_sub φ, hx0, sub_self]
      rw [hkerφ] at hmem
      have hsm := Ideal.smul_top_eq_map (R := C') (S := MvPolynomial (Fin n) C' ⧸ J') I
      rw [hsm]
      exact hmem
    have hmk : (I • (⊤ : Submodule C' (MvPolynomial (Fin n) C' ⧸ J'))).mkQ x =
        (I • (⊤ : Submodule C' (MvPolynomial (Fin n) C' ⧸ J'))).mkQ
          (∑ b ∈ sB, cl b • lf b) := by
      rw [← sub_eq_zero, ← map_sub, Submodule.mkQ_apply]
      exact (Submodule.Quotient.mk_eq_zero _).mpr hd
    rw [hmk, map_sum]
    refine Submodule.sum_mem _ fun b hb => ?_
    rw [map_smul, Submodule.mkQ_apply]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨lf b, ?_, rfl⟩)
    simpa using Finset.mem_image_of_mem lf hb
  have hsyn : Algebra.Syntomic C' (MvPolynomial (Fin n) C' ⧸ J') := by
    have := hfin
    let Pr : Algebra.Presentation C' (MvPolynomial (Fin n) C' ⧸ Ideal.span (Set.range g'))
      (Fin n) (Fin n) := Algebra.Presentation.naive
    have hPr : Pr.IsRelativeGlobalCompleteIntersection := by
      refine ⟨fun p _ hnt => ?_⟩
      have := hnt
      rw [Algebra.QuasiFinite.ringKrullDim_fiber_eq_zero p]
      simp
    have := Algebra.IsRelativeGlobalCompleteIntersection.of_presentation Pr
    exact Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection _ _
  exact ⟨MvPolynomial (Fin n) C' ⧸ J', inferInstance, inferInstance, hsyn, hfin, sec, φ,
    hφsurj, hkerφ, hcompat1, hcompat2⟩

/-- **Stacks Project, Tag 0FL3,** the deformation problem the remark reduces the smoothness of
`V_d` over `Z` to, and its solution. Along a surjection `C' → C` with nilpotent kernel `I` onto a
nonzero artinian ring — a small extension, in particular — a finite syntomic `C`-algebra `B` with
a section `B → C` lifts to a finite syntomic `C'`-algebra `B'` with a section `B' → C'`, together
with a surjection `B' → B` with kernel `IB'` carrying the one section to the other: the tensor
product of `B' → C'` with `C` is `B → C`. -/
@[stacks 0FL3 "the deformation problem the remark reduces the smoothness of V_d over Z to, and \
the remark's solution of it: along a surjection C' → C with nilpotent kernel onto a nonzero \
artinian ring (a small extension of artinian local rings in particular) a finite syntomic \
C-algebra with a section lifts to a finite syntomic C'-algebra with a section whose tensor \
product with C recovers it, the reduction being a surjection B' → B with kernel I·B' that \
matches the two sections."]
theorem Algebra.exists_finite_syntomic_section_lift
    {C' C B : Type u} [CommRing C'] [CommRing C] [CommRing B] [Algebra C' C] [Algebra C B]
    [IsArtinianRing C] [Nontrivial C] [Algebra.Syntomic C B] [Module.Finite C B]
    (hsurj : Function.Surjective (algebraMap C' C))
    (hnil : IsNilpotent (RingHom.ker (algebraMap C' C)))
    (σ : B →ₐ[C] C) :
    ∃ (B' : Type u) (_ : CommRing B') (_ : Algebra C' B'),
      Algebra.Syntomic C' B' ∧ Module.Finite C' B' ∧
        ∃ (sec : B' →ₐ[C'] C') (φ : B' →+* B),
          Function.Surjective φ ∧
          RingHom.ker φ = Ideal.map (algebraMap C' B') (RingHom.ker (algebraMap C' C)) ∧
          (∀ c : C', φ (algebraMap C' B' c) = algebraMap C B (algebraMap C' C c)) ∧
          (∀ b : B', σ (φ b) = algebraMap C' C (sec b)) := by
  have : Nontrivial B := σ.toRingHom.domain_nontrivial
  obtain ⟨n, val, g, hevsurj, hker, hsecev⟩ := Algebra.exists_square_presentation_section C B σ
  exact Algebra.exists_finite_syntomic_lift_of_square_presentation hsurj hnil σ val g hevsurj
    hker hsecev

end
