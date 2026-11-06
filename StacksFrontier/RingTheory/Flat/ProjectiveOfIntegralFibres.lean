module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Localization.BaseChange
public import StacksFrontier.RingTheory.Flat.GenericFlatness
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Projective
public import StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibresCompletion
public import StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibresProd
public import StacksFrontier.RingTheory.Flat.ProjectiveOfIntegralFibresQuotient
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat finite type algebras with geometrically integral fibres are projective

This file proves Stacks 05FS: a finite type flat algebra `S` over a Noetherian ring `R` whose
fibre rings `S ⊗_R κ(𝔭)` are geometrically integral over `κ(𝔭)` is projective as an `R`-module.

The proof is the source's. One shows by Noetherian induction on the ideals of `R` that every
reduction `S/IS = (R ⧸ I) ⊗_R S` is projective over `R ⧸ I`; the conclusion is the case `I = 0`.
At an ideal `I`, writing `A` for the quotient `R ⧸ I` and `C = A ⊗_R S`, the induction
hypothesis says that `D ⊗_A C` is projective over `D` for every proper quotient `D` of `A`. If
`A` is not reduced, `A ⧸ nilradical A` is such a quotient and Stacks 05CG finishes. If `A` is
reduced, generic freeness (Stacks 051Z) provides a nonzero `f` with `C_f` free over `A_f`, the
ring map `A → A_f × A^∧` into the product with the `f`-adic completion is faithfully flat
(Stacks 00MB), and faithfully flat descent of projectivity (Stacks 05A9) reduces the claim to
the two factors: over `A_f` the base change is free, and over `A^∧` it is projective by the
criterion of Stacks 05DP, which is
`Module.Projective.tensorProduct_adicCompletion`.

## Main results

* `Module.Free.exists_ne_zero_of_isReduced`: the form generic flatness takes in the proof — over
  a reduced Noetherian base there is a nonzero `f` with `A_f ⊗_A C` free over `A_f`.
* `Module.Projective.of_forall_quotient_tensorProduct_of_isReduced`: the reduced case of the
  induction, where the descent along `A → A_f × A^∧` happens.
* `Module.Projective.baseChange_of_geometricallyIntegral`: the induction itself, that `A ⊗_R S`
  is projective over `A` for every quotient `A` of `R`.
* `Module.Flat.projective_of_finiteType_of_geometricallyIntegral_fibres`: **Stacks 05FS**.

## Implementation notes

The induction is run on the statement "for every ring `A` with `R → A` surjective of kernel `I`,
the base change `A ⊗_R S` is projective over `A`", quantified over the *type* `A` rather than
stated for `R ⧸ I`. Quantifying over types costs nothing — `R ⧸ I` is such an `A` — and it
removes every double-quotient transport from the proof: a quotient of `A` is again a quotient of
`R`, so the induction hypothesis applies to it on the nose, and the only comparison left is the
`A`-algebra isomorphism `D ⊗_A (A ⊗_R S) ≅ D ⊗_R S`,
`TensorProduct.AlgebraTensorModule.cancelBaseChange`. It is also exactly the shape in which the
completed step consumes the induction hypothesis, for `A^∧/IA^∧`, which is a quotient of `A` but
is not presented as one.

The well-founded relation is `(· > ·)` on `Ideal R`, available as `WellFoundedGT (Ideal R)` from
`IsNoetherianRing R`; `IsWellFounded.induction` is the recursor.

The models of the localization are Mathlib's: `A_f` is `Localization.Away f` and `A_f ⊗_A C` is
the base change, identified with the canonical model
`Localization (Algebra.algebraMapSubmonoid C (Submonoid.powers f))` of `C_f` fixed by
`Algebra.IsFinitePresentationFreeAway` through `isLocalizedModule_iff_isBaseChange`.

## References

* [Stacks Project, Tag 05FS](https://stacks.math.columbia.edu/tag/05FS)
* [Stacks Project, Tag 051Z](https://stacks.math.columbia.edu/tag/051Z)
* [Stacks Project, Tag 05A9](https://stacks.math.columbia.edu/tag/05A9)
* [Stacks Project, Tag 05DP](https://stacks.math.columbia.edu/tag/05DP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

open scoped TensorProduct

universe u

/-- **Generic freeness in the form Stacks 05FS uses it.** Let `A` be a reduced Noetherian ring
which is not the zero ring and let `C` be a finite type `A`-algebra. Then there is a nonzero
`f : A` such that `A_f ⊗_A C` is free over `A_f = Localization.Away f`.

This is Stacks 051Z, `Algebra.exists_isOpen_dense_isFinitePresentationFreeAway`, at the module
`C` itself: a point of the dense open it produces lies in a standard open `D(f)` on which the
condition 051U holds, and `f ≠ 0` because `D(0)` is empty. The condition 051U is stated for the
canonical model `Localization (Algebra.algebraMapSubmonoid C (Submonoid.powers f))` of `C_f`,
which is identified with the base change `A_f ⊗_A C` by `isLocalizedModule_iff_isBaseChange`. -/
@[ega "IV 11.4.6" "Domain base with M = B",
  ega "IV 6.9.2" "M = B",
  ega "IV 8.9.4.1" "Case M = B",
  sga "1 IV 6.7" "special case"]
theorem Module.Free.exists_ne_zero_of_isReduced (A C : Type u) [CommRing A] [IsReduced A]
    [Nontrivial A] [CommRing C] [Algebra A C] [Algebra.FiniteType A C] :
    ∃ f : A, f ≠ 0 ∧ Module.Free (Localization.Away f) (Localization.Away f ⊗[A] C) := by
  obtain ⟨U, -, hUd, hU⟩ :=
    Algebra.exists_isOpen_dense_isFinitePresentationFreeAway (R := A) (S := C) (M := C)
  obtain ⟨u, hu⟩ := hUd.nonempty
  obtain ⟨f, hf, -, hfree⟩ := hU u hu
  refine ⟨f, fun hf0 => (PrimeSpectrum.mem_basicOpen _ _).mp hf (hf0 ▸ Submodule.zero_mem _), ?_⟩
  have hloc : IsLocalizedModule (Submonoid.powers f)
      (IsScalarTower.toAlgHom A C
        (Localization (Algebra.algebraMapSubmonoid C (Submonoid.powers f)))).toLinearMap :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have := hfree.2.2.1
  exact Module.Free.of_equiv
    (((isLocalizedModule_iff_isBaseChange (Submonoid.powers f) (Localization.Away f) _).mp
      hloc).equiv.symm)

/-- **The reduced case of the Noetherian induction of Stacks 05FS.** Let `A` be a reduced
Noetherian ring and `C` a flat finite type `A`-algebra whose fibres are geometrically integral.
If `D ⊗_A C` is projective over `D` for every ring `D` which is a quotient of `A` by a nonzero
ideal, then `C` is projective over `A`.

Generic freeness gives a nonzero `f` with `A_f ⊗_A C` free over `A_f`. The ring map
`A → A_f × A^∧` into the product with the `f`-adic completion of `A` is faithfully flat, by
`Module.faithfullyFlat_prod_of_forall_ne_top`: a maximal ideal `𝔪` of `A` either misses `f`, and
then `𝔪A_f` is prime hence proper, or contains `f`, and then `𝔪A^∧` is proper by
`AdicCompletion.smul_top_ne_top_of_le`. So by Stacks 05A9 it suffices to make
`(A_f × A^∧) ⊗_A C` projective over `A_f × A^∧`, which by
`Module.Projective.of_prod_tensorProduct` is the two factors separately: freeness on the `A_f`
side, and `Module.Projective.tensorProduct_adicCompletion` on the `A^∧` side. -/
theorem Module.Projective.of_forall_quotient_tensorProduct_of_isReduced (A C : Type u)
    [CommRing A] [CommRing C] [Algebra A C] [IsNoetherianRing A] [IsReduced A]
    [Algebra.FiniteType A C] [Module.Flat A C]
    (h : GeometricallyIntegral (Spec.map (ofHom (algebraMap A C))))
    (hquot : ∀ (D : Type u) [CommRing D] [Algebra A D],
      Function.Surjective (algebraMap A D) → RingHom.ker (algebraMap A D) ≠ ⊥ →
      Module.Projective D (D ⊗[A] C)) :
    Module.Projective A C := by
  rcases subsingleton_or_nontrivial A with _ | _
  · have : Subsingleton C :=
      subsingleton_of_zero_eq_one (by rw [← map_one (algebraMap A C), ← map_zero (algebraMap A C),
        Subsingleton.elim (0 : A) 1])
    exact Module.Projective.of_subsingleton A C
  obtain ⟨f, hf0, hfree⟩ := Module.Free.exists_ne_zero_of_isReduced A C
  have hspan : Ideal.span {f} ≠ ⊥ := fun hc => hf0 (Ideal.span_singleton_eq_bot.mp hc)
  -- The two factors of `A_f × A^∧` have projective base changes.
  have hAf : Module.Projective (Localization.Away f) (Localization.Away f ⊗[A] C) :=
    have := hfree
    inferInstance
  have hAc : Module.Projective (AdicCompletion (Ideal.span {f}) A)
      (AdicCompletion (Ideal.span {f}) A ⊗[A] C) :=
    Module.Projective.tensorProduct_adicCompletion A C h (Ideal.span {f}) hspan hquot
  -- `A → A_f × A^∧` is faithfully flat.
  have hff : Module.FaithfullyFlat A (Localization.Away f × AdicCompletion (Ideal.span {f}) A) :=
    Module.faithfullyFlat_prod_of_forall_ne_top fun m hm => by
      rcases em (f ∈ m) with hfm | hfm
      · exact Or.inr (AdicCompletion.smul_top_ne_top_of_le _ hm.ne_top
          (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hfm)))
      · refine Or.inl ?_
        have hp : (m.map (algebraMap A (Localization.Away f))).IsPrime :=
          IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) _ m hm.isPrime (by
            rw [Set.disjoint_left]
            rintro x ⟨n, rfl⟩ hx
            exact hfm (hm.isPrime.mem_of_pow_mem n hx))
        rw [Ideal.smul_top_eq_map, Ne, Submodule.restrictScalars_eq_top_iff]
        exact hp.ne_top
  have : Module.Projective (Localization.Away f × AdicCompletion (Ideal.span {f}) A)
      ((Localization.Away f × AdicCompletion (Ideal.span {f}) A) ⊗[A] C) :=
    Module.Projective.of_prod_tensorProduct _ _ C hAf hAc
  exact Module.Projective.of_projective_tensorProduct
    (Localization.Away f × AdicCompletion (Ideal.span {f}) A)

/-- **The Noetherian induction of Stacks 05FS.** Let `R` be a Noetherian ring and `S` a flat
finite type `R`-algebra whose fibres are geometrically integral. Then for every ring `A` which
is a quotient of `R`, the base change `A ⊗_R S` is projective over `A`.

The induction is on the kernel `I` of `R → A`, downward in the ideals of `R`, which is
well-founded because `R` is Noetherian. Every proper quotient `D` of `A` is a quotient of `R`
with a strictly larger kernel (`RingHom.ker_lt_ker_of_tower`), so the induction hypothesis
applies to it; that is the hypothesis both the non-radical step
(`Module.Flat.projective_of_projective_tensorProduct_quotient_nilradical`, Stacks 05CG) and the
reduced step (`Module.Projective.of_forall_quotient_tensorProduct_of_isReduced`) consume. -/
theorem Module.Projective.baseChange_of_geometricallyIntegral (R S : Type u) [CommRing R]
    [CommRing S] [Algebra R S] [IsNoetherianRing R] [Algebra.FiniteType R S] [Module.Flat R S]
    (h : GeometricallyIntegral (Spec.map (ofHom (algebraMap R S)))) (I : Ideal R) :
    ∀ (A : Type u) [CommRing A] [Algebra R A], Function.Surjective (algebraMap R A) →
      RingHom.ker (algebraMap R A) = I → Module.Projective A (A ⊗[R] S) := by
  refine (wellFounded_gt (α := Ideal R)).induction
    (C := fun I => ∀ (A : Type u) [CommRing A] [Algebra R A],
      Function.Surjective (algebraMap R A) → RingHom.ker (algebraMap R A) = I →
      Module.Projective A (A ⊗[R] S)) I ?_
  clear I
  intro I ih A _ _ hsurj hkerA
  have : IsNoetherianRing A := isNoetherianRing_of_surjective R A (algebraMap R A) hsurj
  have hC : GeometricallyIntegral (Spec.map (ofHom (algebraMap A (A ⊗[R] S)))) :=
    h.baseChange_algebraMap A
  have hquot : ∀ (D : Type u) [CommRing D] [Algebra A D],
      Function.Surjective (algebraMap A D) → RingHom.ker (algebraMap A D) ≠ ⊥ →
      Module.Projective D (D ⊗[A] (A ⊗[R] S)) := by
    intro D _ _ hDs hDk
    let : Algebra R D := ((algebraMap A D).comp (algebraMap R A)).toAlgebra
    have : IsScalarTower R A D := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have := ih _ (hkerA ▸ RingHom.ker_lt_ker_of_tower hsurj hDk) D (hDs.comp hsurj) rfl
    exact Module.Projective.of_equiv
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R A D D S).symm
  rcases eq_or_ne (nilradical A) ⊥ with hnil | hnil
  · have : IsReduced A := nilradical_eq_bot_iff.mp hnil
    exact Module.Projective.of_forall_quotient_tensorProduct_of_isReduced A _ hC hquot
  · refine Module.Flat.projective_of_projective_tensorProduct_quotient_nilradical A _
      (hquot (A ⧸ nilradical A) ?_ ?_)
    · rw [Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.mk_surjective
    · rwa [Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]

/-- **Stacks Project, Tag 05FS.** A flat finite type algebra over a Noetherian ring whose fibres
are geometrically integral is projective as a module over its base ring. -/
@[stacks 05FS]
theorem Module.Flat.projective_of_finiteType_of_geometricallyIntegral_fibres
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [IsNoetherianRing R] [Algebra.FiniteType R S] [Module.Flat R S]
    (h : ∀ (p : Ideal R) [p.IsPrime],
      letI : Algebra p.ResidueField (S ⊗[R] p.ResidueField) :=
        Algebra.TensorProduct.rightAlgebra
      Algebra.IsGeometricallyIntegral p.ResidueField (S ⊗[R] p.ResidueField)) :
    Module.Projective R S :=
  have := Module.Projective.baseChange_of_geometricallyIntegral R S
    (geometricallyIntegral_algebraMap_iff_residueField.mpr h) ⊥ R (fun x => ⟨x, rfl⟩)
    (by ext x; simp [Algebra.algebraMap_self, RingHom.mem_ker])
  Module.Projective.of_equiv (TensorProduct.lid R S)

end
