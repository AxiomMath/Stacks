module

public import StacksFrontier.Algebra.Homology.SpectralSequence.EulerCharacteristic
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Leray.GrothendieckSequenceAbuts

/-!
# The Euler characteristic of a composite of right derived functors

Let `F : 𝒜 ⥤ ℬ` and `G : ℬ ⥤ Mod_k` be additive functors between abelian categories with enough
injectives, `G` left exact and valued in vector spaces over a field `k`, such that `F` carries
injective objects to objects acyclic for `G`. For an object `X` of `𝒜` such that the vector
spaces `R^pG(R^qF(X))` are finite-dimensional and only finitely many of them are nonzero, the
Grothendieck spectral sequence `E_2^{p,q} = R^pG(R^qF(X)) ⟹ R^{p+q}(G ∘ F)(X)` shows that each
`R^n(G ∘ F)(X)` is finite-dimensional, that only finitely many of them are nonzero, and that

`∑ₙ (-1)ⁿ dim R^n(G ∘ F)(X) = ∑_{p,q} (-1)^{p+q} dim R^pG(R^qF(X))`.

With `F` a direct image and `G` the global sections over the base field this is the identity
`χ(X, 𝓕) = ∑ᵢ (-1)ⁱ χ(Y, Rⁱf_*𝓕)` of [Stacks, Tag 0EDD].

## Main results

* `CategoryTheory.Functor.finsum_finrank_rightDerived_comp_eq`: the identity above, for the
  right derived functors `CategoryTheory.Functor.rightDerived` computed by injective
  resolutions.

## References

* [Stacks Project, Tag 0EDD](https://stacks.math.columbia.edu/tag/0EDD)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace CategoryTheory.Functor

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- A finite sum over `ℤ` of a function vanishing in negative degrees is the sum over `ℕ`. -/
private theorem finsum_int_eq_finsum_nat {M : Type*} [AddCommMonoid M] (f : ℤ → M)
    (hf : ∀ n < 0, f n = 0) : ∑ᶠ n : ℤ, f n = ∑ᶠ m : ℕ, f m := by
  rw [← finsum_mem_range Nat.cast_injective, ← finsum_mem_univ]
  refine finsum_mem_inter_support_eq _ _ _ ?_
  ext n
  simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_univ, true_and, Function.mem_support]
  exact ⟨fun hn => ⟨⟨n.toNat, Int.toNat_of_nonneg (not_lt.1 fun h => hn (hf n h))⟩, hn⟩,
    fun h => h.2⟩

/-- A finite sum over `ℤ × ℤ` of a function vanishing off the first quadrant is the sum over
`ℕ × ℕ`. -/
private theorem finsum_int_prod_eq_finsum_nat_prod {M : Type*} [AddCommMonoid M]
    (f : ℤ × ℤ → M) (hf : ∀ pq : ℤ × ℤ, pq.1 < 0 ∨ pq.2 < 0 → f pq = 0) :
    ∑ᶠ pq : ℤ × ℤ, f pq = ∑ᶠ ab : ℕ × ℕ, f ((ab.1 : ℤ), (ab.2 : ℤ)) := by
  rw [← finsum_mem_range (g := fun ab : ℕ × ℕ => ((ab.1 : ℤ), (ab.2 : ℤ)))
    (Nat.cast_injective.prodMap Nat.cast_injective), ← finsum_mem_univ]
  refine finsum_mem_inter_support_eq _ _ _ ?_
  ext pq
  simp only [Set.mem_inter_iff, Set.mem_range, Set.mem_univ, true_and, Function.mem_support]
  refine ⟨fun hpq => ⟨?_, hpq⟩, fun h => h.2⟩
  have h₁ : 0 ≤ pq.1 := not_lt.1 fun h => hpq (hf pq (Or.inl h))
  have h₂ : 0 ≤ pq.2 := not_lt.1 fun h => hpq (hf pq (Or.inr h))
  exact ⟨(pq.1.toNat, pq.2.toNat), Prod.ext (Int.toNat_of_nonneg h₁) (Int.toNat_of_nonneg h₂)⟩

variable {𝒜 ℬ : Type*} [Category 𝒜] [Category ℬ] [Abelian 𝒜] [Abelian ℬ]
  [EnoughInjectives 𝒜] [EnoughInjectives ℬ] {k : Type u} [Field k]

/-- The right derived functors on `D⁺` vanish in negative degrees ([Stacks, Tag 05TD],
part (1)). -/
private theorem isZero_rightDerivedPlus_obj_of_neg {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    [Abelian 𝒞] [Abelian 𝒟] [EnoughInjectives 𝒞] [HasDerivedCategory 𝒞] [HasDerivedCategory 𝒟]
    (Φ : 𝒞 ⥤ 𝒟) [Φ.Additive] (i : ℤ) (hi : i < 0) (Y : 𝒞) :
    IsZero ((Φ.rightDerivedPlus i).obj Y) :=
  (Functor.isZero_iff _).1 ((isZero_and_preservesFiniteLimits_and_isIso_iff_preservesFiniteLimits
    Φ Φ.rightDerivedFunctorPlus Φ.rightDerivedFunctorPlusUnith).1 i hi) Y

/-- **The Euler characteristic of a composite of right derived functors.** Let `F : 𝒜 ⥤ ℬ` and
`G : ℬ ⥤ Mod_k` be additive, `G` left exact, between abelian categories with enough injectives,
such that `R^nG(F(I)) = 0` for every injective `I` and `n > 0`. If the vector spaces
`R^pG(R^qF(X))` are finite-dimensional and only finitely many are nonzero, then every
`R^n(G ∘ F)(X)` is finite-dimensional, only finitely many are nonzero, and
`∑ₙ (-1)ⁿ dim R^n(G ∘ F)(X) = ∑_{p,q} (-1)^{p+q} dim R^pG(R^qF(X))`. -/
theorem finsum_finrank_rightDerived_comp_eq (F : 𝒜 ⥤ ℬ) (G : ℬ ⥤ ModuleCat.{v} k)
    [F.Additive] [G.Additive] [PreservesFiniteLimits G]
    (hFG : ∀ I : 𝒜, Injective I → ∀ n : ℕ, 0 < n → IsZero ((G.rightDerived n).obj (F.obj I)))
    (X : 𝒜)
    (hfin : ∀ p q : ℕ, Module.Finite k ((G.rightDerived p).obj ((F.rightDerived q).obj X)))
    (hsupp : {pq : ℕ × ℕ |
      ¬ IsZero ((G.rightDerived pq.1).obj ((F.rightDerived pq.2).obj X))}.Finite) :
    (∀ n : ℕ, Module.Finite k (((F ⋙ G).rightDerived n).obj X)) ∧
      {n : ℕ | ¬ IsZero (((F ⋙ G).rightDerived n).obj X)}.Finite ∧
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (((F ⋙ G).rightDerived n).obj X) : ℤ) =
        ∑ᶠ pq : ℕ × ℕ, (-1 : ℤ) ^ (pq.1 + pq.2) *
          (Module.finrank k ((G.rightDerived pq.1).obj ((F.rightDerived pq.2).obj X)) : ℤ) := by
  classical
  let := HasDerivedCategory.standard 𝒜
  let := HasDerivedCategory.standard ℬ
  let := HasDerivedCategory.standard (ModuleCat.{v} k)
  have hFG' (I : 𝒜) (hI : Injective I) : G.rightAcyclic (F.obj I) := by
    refine ((rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus G (F.obj I)).2
      inferInstance).2 fun i hi => ?_
    lift i to ℕ using hi.le
    exact (hFG I hI i (by exact_mod_cast hi)).of_iso
      ((Stacks.DerivedIndexing.rightDerivedIso G i).app _).symm
  obtain ⟨K, hK⟩ := exists_abutsTo_homology_rightDerivedFunctorPlus_comp F G hFG'
    ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj X)
  let Fil : ∀ (_p n : ℤ), Subobject (K.X.X n) := fun p n =>
    Subobject.mk ((K.filtration.ι.app (op p)).f n)
  let Zc : ∀ (_r _p n : ℤ), Subobject (K.X.X n) := fun r p n =>
    Fil p n ⊓ (Subobject.pullback (K.X.d n (n + 1))).obj (Fil (p + r) (n + 1))
  let Dc : ∀ (_r _p n : ℤ), Subobject (K.X.X n) := fun r p n =>
    Zc (r - 1) (p + 1) n ⊔
      (Subobject.«exists» (K.X.d (n - 1) n)).obj (Zc (r - 1) (p - r + 1) (n - 1))
  obtain ⟨E, -, hE₂, habuts⟩ := hK Fil (fun _ _ => rfl) Zc (fun _ _ _ => rfl) Dc
    (fun _ _ _ => rfl)
  have e₂ (a b : ℕ) : Nonempty ((E.page 2 zero_le_two).X ((a : ℤ), (b : ℤ)) ≅
      (G.rightDerived a).obj ((F.rightDerived b).obj X)) :=
    ⟨(hE₂ a b).some ≪≫ (G.rightDerivedPlus a).mapIso
      ((Stacks.DerivedIndexing.rightDerivedIso F b).app X).symm ≪≫
        ((Stacks.DerivedIndexing.rightDerivedIso G a).app _).symm⟩
  have hnat (pq : ℤ × ℤ) (h : ¬ (pq.1 < 0 ∨ pq.2 < 0)) : ∃ a b : ℕ, pq = ((a : ℤ), (b : ℤ)) := by
    obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 fun h' => h (Or.inl h'))
    obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 fun h' => h (Or.inr h'))
    exact ⟨a, b, Prod.ext ha hb⟩
  have hzero (pq : ℤ × ℤ) (h : pq.1 < 0 ∨ pq.2 < 0) :
      IsZero ((E.page 2 zero_le_two).X pq) := by
    refine IsZero.of_iso ?_ (hE₂ pq.1 pq.2).some
    by_cases hp : pq.1 < 0
    · exact isZero_rightDerivedPlus_obj_of_neg G pq.1 hp _
    · obtain ⟨a, ha⟩ := Int.eq_ofNat_of_zero_le (not_lt.1 hp)
      rw [ha]
      have hY := isZero_rightDerivedPlus_obj_of_neg F pq.2 (h.resolve_left hp) X
      refine IsZero.of_iso ?_ ((Stacks.DerivedIndexing.rightDerivedIso G a).app _).symm
      cases a with
      | zero => exact (G.map_isZero hY).of_iso (G.rightDerivedZeroIsoSelf.app _)
      | succ n =>
        have : Injective ((DerivedCategory.Plus.homologyFunctor ℬ pq.2).obj
            (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj X))) :=
          hY.injective
        exact G.isZero_rightDerived_obj_injective_succ n _
  have hfin₂ (pq : ℤ × ℤ) : Module.Finite k ((E.page 2 zero_le_two).X pq) := by
    by_cases h : pq.1 < 0 ∨ pq.2 < 0
    · have : Subsingleton ((E.page 2 zero_le_two).X pq) :=
        ModuleCat.subsingleton_of_isZero (hzero pq h)
      have : Finite ((E.page 2 zero_le_two).X pq) := Finite.of_subsingleton
      exact Module.Finite.of_finite
    · obtain ⟨a, b, rfl⟩ := hnat pq h
      obtain ⟨e⟩ := e₂ a b
      have := hfin a b
      exact Module.Finite.equiv e.symm.toLinearEquiv
  have hsupp₂ : {pq : ℤ × ℤ | ¬ IsZero ((E.page 2 zero_le_two).X pq)}.Finite := by
    refine (hsupp.image fun ab : ℕ × ℕ => ((ab.1 : ℤ), (ab.2 : ℤ))).subset fun pq hpq => ?_
    obtain ⟨a, b, rfl⟩ := hnat pq fun h => hpq (hzero pq h)
    exact ⟨(a, b), fun hz => hpq (hz.of_iso (e₂ a b).some), rfl⟩
  obtain ⟨hHfin, hHsupp, hsum⟩ := habuts.finsum_finrank_eq (2 : ℤ) zero_le_two hfin₂ hsupp₂
  have eH (m : ℕ) : ((F ⋙ G).rightDerived m).obj X ≅
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{v} k) m).obj
        ((F ⋙ G).rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj X)) :=
    (Stacks.DerivedIndexing.rightDerivedIso (F ⋙ G) m).app X
  have hHneg (n : ℤ) (hn : n < 0) : IsZero ((DerivedCategory.Plus.homologyFunctor
      (ModuleCat.{v} k) n).obj ((F ⋙ G).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor 𝒜 0).obj X))) :=
    isZero_rightDerivedPlus_obj_of_neg (F ⋙ G) n hn X
  refine ⟨fun m => Module.Finite.equiv (eH m).symm.toLinearEquiv,
    (hHsupp.preimage Nat.cast_injective.injOn).subset fun m hm hz => hm (hz.of_iso (eH m)), ?_⟩
  rw [finsum_int_eq_finsum_nat _ fun n hn => by
      rw [HomologicalComplex.finrank_eq_zero_of_isZero (hHneg n hn), Nat.cast_zero, mul_zero],
    finsum_int_prod_eq_finsum_nat_prod _ fun pq h => by
      rw [HomologicalComplex.finrank_eq_zero_of_isZero (hzero pq h), Nat.cast_zero,
        mul_zero]] at hsum
  refine Eq.trans (finsum_congr fun m => ?_) (hsum.trans (finsum_congr fun ab => ?_))
  · rw [Int.coe_negOnePow_natCast, (eH m).toLinearEquiv.finrank_eq]
  · rw [show ((ab.1 : ℤ) + (ab.2 : ℤ)) = ((ab.1 + ab.2 : ℕ) : ℤ) by push_cast; ring,
      Int.coe_negOnePow_natCast, (e₂ ab.1 ab.2).some.toLinearEquiv.finrank_eq]

end CategoryTheory.Functor

end
