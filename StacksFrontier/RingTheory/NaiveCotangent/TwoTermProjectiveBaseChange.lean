module

public import StacksFrontier.RingTheory.NaiveCotangent.FormallySmoothExtensionQuasiIso
public import StacksFrontier.RingTheory.NaiveCotangent.TwoTermFlatBaseChange
public import StacksFrontier.RingTheory.TateMap.DetNLBaseChange

/-!
# Base change of a quasi-isomorphism onto a complex with projective degree-`0` term

Let `f : A ⟶ B` be a chain map of two-term complexes of `S`-modules `X₁ --d--> X₀` which is a
quasi-isomorphism, bijective on `H₁ = ker d` and on `H₀ = coker d`.  If the degree-`0` term
`B.X₀` of the target is a projective `S`-module, then `f` is a homotopy equivalence, and
therefore `f ⊗ T` is again a quasi-isomorphism for **every** `S`-algebra `T`, flat or not.

The reason is the mapping cone `0 ⟶ A.X₁ ⟶ A.X₀ × B.X₁ ⟶ B.X₀ ⟶ 0`, with maps
`a ↦ (d a, f₁ a)` and `(x, b) ↦ f₀ x - d b`.  It is exact precisely because `f` is a
quasi-isomorphism, and projectivity of `B.X₀` splits it.  A section `s = (s₀, s₁)` of the
right-hand map and the retraction `r` of the left-hand map that it determines assemble into a
chain map `g = (r ∘ inr, s₀) : B ⟶ A` inverse to `f` up to the homotopies `-(r ∘ inl)` and `s₁`.
Homotopy equivalences are preserved by every additive functor, in particular by `T ⊗_S -`.

Applied to the naive cotangent complexes of two extensions `P`, `P'` of an `R`-algebra `S` whose
rings are formally smooth over `R`, this shows that the chain map induced by a morphism of
extensions `P ⟶ P'` stays a quasi-isomorphism after base change to any `S`-algebra `C`: the
degree-`0` term `S ⊗_{P'} Ω[P'⁄R]` is projective because `Ω[P'⁄R]` is.  In particular the map
`ker (C ⊗ d_P) ⟶ ker (C ⊗ d_{P'})` on degree `-1` cycles is bijective.

## Main results

* `NaiveCotangent.isHomotopyEquiv_of_isQuasiIso_of_projective`: a quasi-isomorphism of two-term
  complexes whose target has projective degree-`0` term is a homotopy equivalence.
* `NaiveCotangent.IsQuasiIso.baseChange_of_projective`: base change along any ring map preserves
  a quasi-isomorphism whose target has projective degree-`0` term.
* `NaiveCotangent.isQuasiIso_baseChange_nlExtensionMap_of_formallySmooth`: for a morphism of
  extensions whose rings are formally smooth, the base change of the induced chain map of naive
  cotangent complexes to any algebra is a quasi-isomorphism.
* `NaiveCotangent.bijOn_lTensor_cotangentMap_ker_of_formallySmooth`: the same statement on
  degree `-1` cycles, in the `TensorProduct.AlgebraTensorModule.lTensor` spelling of the base
  changed complex.

## Implementation notes

The splitting is used through the homotopy equivalence it produces rather than through the base
change of the cone: a homotopy equivalence is a finite list of identities between composites of
linear maps, which base change by `LinearMap.baseChange_comp` and `LinearMap.baseChange_sub`, so
no identification of `T ⊗_S (A.X₀ × B.X₁)` with `(T ⊗_S A.X₀) × (T ⊗_S B.X₁)` is needed.

`TensorProduct.AlgebraTensorModule.lTensor C C φ` and `LinearMap.baseChange C φ` are the same
term `TensorProduct.AlgebraTensorModule.map LinearMap.id φ`, so the statement on degree `-1`
cycles in the first spelling is the `H₁` half of the quasi-isomorphism, read on kernels by
`NaiveCotangent.bijOn_ker_of_bijective_onH₁`.

The two extensions `P` and `P'` are taken with rings in one universe, as in
`NaiveCotangent.nlExtensionMap_isQuasiIso_of_formallySmooth`, on which the statements rest.

## References

* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9), where the statement is
  used.
* [Stacks Project, Tag 00S1](https://stacks.math.columbia.edu/tag/00S1)
* [Stacks Project, Tag 031J](https://stacks.math.columbia.edu/tag/031J), projectivity of the
  module of differentials of a formally smooth algebra.
-/

@[expose] public section

namespace NaiveCotangent

open TensorProduct

/-!
## A quasi-isomorphism onto a complex with projective degree-`0` term
-/

section Projective

variable {S : Type*} [CommRing S] {A B : TwoTerm S}

/-- A chain map bijective on `H₁` carries `ker A.d` bijectively onto `ker B.d`. -/
private theorem bijOn_ker_of_bijective_onH₁_aux {f : ChainMap A B}
    (hf : Function.Bijective f.onH₁) :
    Set.BijOn f.f₁ (LinearMap.ker A.d) (LinearMap.ker B.d) := by
  refine ⟨fun x hx => (f.onH₁ ⟨x, hx⟩).2, fun x hx y hy hxy => ?_, fun y hy => ?_⟩
  · exact congrArg Subtype.val (hf.1 (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) (Subtype.ext hxy))
  · obtain ⟨⟨x, hx⟩, hxy⟩ := hf.2 ⟨y, hy⟩
    exact ⟨x, hx, congrArg Subtype.val hxy⟩

/-- **A quasi-isomorphism onto a complex with projective degree-`0` term is a homotopy
equivalence.**  The mapping cone `0 ⟶ A.X₁ ⟶ A.X₀ × B.X₁ ⟶ B.X₀ ⟶ 0` is exact because `f` is a
quasi-isomorphism and splits because `B.X₀` is projective; the splitting data are a homotopy
inverse of `f` together with the two homotopies. -/
theorem isHomotopyEquiv_of_isQuasiIso_of_projective {f : ChainMap A B} (hf : IsQuasiIso f)
    [Module.Projective S B.X₀] : IsHomotopyEquiv f := by
  -- The two maps of the mapping cone.
  let α : A.X₁ →ₗ[S] A.X₀ × B.X₁ := LinearMap.prod A.d f.f₁
  let β : A.X₀ × B.X₁ →ₗ[S] B.X₀ :=
    f.f₀ ∘ₗ LinearMap.fst S A.X₀ B.X₁ - B.d ∘ₗ LinearMap.snd S A.X₀ B.X₁
  have hα (a : A.X₁) : α a = (A.d a, f.f₁ a) := rfl
  have hβ (m : A.X₀ × B.X₁) : β m = f.f₀ m.1 - B.d m.2 := rfl
  have hβα (a : A.X₁) : β (α a) = 0 := by
    rw [hβ, hα, chainMap_comm_apply, sub_self]
  -- Exactness of the cone, from the quasi-isomorphism.
  have hker := bijOn_ker_of_bijective_onH₁_aux hf.1
  have hαinj : Function.Injective α := (injective_iff_map_eq_zero α).mpr fun a ha => by
    rw [hα, Prod.mk_eq_zero] at ha
    exact hker.injOn ha.1 (zero_mem _) (by simpa using ha.2)
  have hβsurj : Function.Surjective β := fun y => by
    obtain ⟨x, hx⟩ := hf.2.2 (Submodule.Quotient.mk y)
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [onH₀_mk, Submodule.Quotient.eq] at hx
    obtain ⟨b, hb⟩ := hx
    exact ⟨(x, b), by rw [hβ, hb, sub_sub_cancel]⟩
  have hexact (m : A.X₀ × B.X₁) (hm : β m = 0) : ∃ a, α a = m := by
    obtain ⟨x, b⟩ := m
    rw [hβ, sub_eq_zero] at hm
    have hx : f.onH₀ (Submodule.Quotient.mk x) = 0 := by
      rw [onH₀_mk, Submodule.Quotient.mk_eq_zero, hm]
      exact LinearMap.mem_range_self _ _
    rw [← map_zero f.onH₀] at hx
    have hx' := hf.2.1 hx
    rw [Submodule.Quotient.mk_eq_zero] at hx'
    obtain ⟨a', ha'⟩ := hx'
    have hcyc : b - f.f₁ a' ∈ H₁ B := by
      change B.d (b - f.f₁ a') = 0
      rw [map_sub, chainMap_comm_apply, ha', ← hm, sub_self]
    obtain ⟨a'', ha''0, h''⟩ := hker.surjOn hcyc
    refine ⟨a' + a'', ?_⟩
    rw [hα, map_add, map_add, ha', ha''0, h'', add_zero, add_sub_cancel]
  -- The splitting.
  obtain ⟨s, hs⟩ := β.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hβsurj)
  have hs' (y : B.X₀) : β (s y) = y := LinearMap.congr_fun hs y
  let q : A.X₀ × B.X₁ →ₗ[S] LinearMap.range α :=
    (LinearMap.id - s ∘ₗ β).codRestrict (LinearMap.range α) (fun m => by
      obtain ⟨a, ha⟩ := hexact (m - s (β m)) (by rw [map_sub, hs', sub_self])
      exact ⟨a, ha⟩)
  let r : A.X₀ × B.X₁ →ₗ[S] A.X₁ := (LinearEquiv.ofInjective α hαinj).symm.toLinearMap ∘ₗ q
  have hαr (m : A.X₀ × B.X₁) : α (r m) = m - s (β m) := by
    have h := LinearEquiv.ofInjective_apply α (h := hαinj)
      ((LinearEquiv.ofInjective α hαinj).symm (q m))
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  have hrα (a : A.X₁) : r (α a) = a := hαinj (by rw [hαr, hβα, map_zero, sub_zero])
  have hαr₁ (m : A.X₀ × B.X₁) : A.d (r m) = m.1 - (s (β m)).1 := congrArg Prod.fst (hαr m)
  have hαr₂ (m : A.X₀ × B.X₁) : f.f₁ (r m) = m.2 - (s (β m)).2 := congrArg Prod.snd (hαr m)
  -- The homotopy inverse.
  let g : ChainMap B A :=
    { f₁ := r ∘ₗ LinearMap.inr S A.X₀ B.X₁
      f₀ := LinearMap.fst S A.X₀ B.X₁ ∘ₗ s
      comm := LinearMap.ext fun b => by
        change A.d (r (0, b)) = (s (B.d b)).1
        simp only [hαr₁, hβ, map_zero, zero_sub, map_neg, Prod.fst_neg, neg_neg] }
  refine ⟨g, ⟨-(r ∘ₗ LinearMap.inl S A.X₀ B.X₁), ?_, ?_⟩,
    ⟨LinearMap.snd S A.X₀ B.X₁ ∘ₗ s, ?_, ?_⟩⟩
  · refine LinearMap.ext fun a => ?_
    change r (0, f.f₁ a) - a = -r (A.d a, 0)
    have h : r (A.d a, 0) + r (0, f.f₁ a) = a := by
      rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
      exact hrα a
    calc r (0, f.f₁ a) - a = r (0, f.f₁ a) - (r (A.d a, 0) + r (0, f.f₁ a)) := by rw [h]
      _ = -r (A.d a, 0) := by abel
  · refine LinearMap.ext fun x => ?_
    change (s (f.f₀ x)).1 - x = A.d (-r (x, 0))
    rw [map_neg, hαr₁, hβ, map_zero, sub_zero, neg_sub]
  · refine LinearMap.ext fun b => ?_
    change f.f₁ (r (0, b)) - b = (s (B.d b)).2
    rw [hαr₂, hβ, map_zero, zero_sub, map_neg, Prod.snd_neg, sub_neg_eq_add, add_sub_cancel_left]
  · refine LinearMap.ext fun y => ?_
    change f.f₀ (s y).1 - y = B.d (s y).2
    have h := hs' y
    rw [hβ] at h
    generalize s y = m at h ⊢
    rw [← h, sub_sub_cancel]

end Projective

/-!
## Base change of homotopies and homotopy equivalences
-/

section BaseChange

variable {S : Type*} [CommRing S] (T : Type*) [CommRing T] [Algebra S T]

/-- **Base change of a quasi-isomorphism onto a complex with projective degree-`0` term.**  If
`f : A ⟶ B` is a quasi-isomorphism of two-term complexes of `S`-modules and `B.X₀` is a
projective `S`-module, then `f ⊗ T` is a quasi-isomorphism for every `S`-algebra `T`, with no
flatness assumption on `T`: `f` is a homotopy equivalence
(`NaiveCotangent.isHomotopyEquiv_of_isQuasiIso_of_projective`), and base change preserves those. -/
theorem IsQuasiIso.baseChange_of_projective {A B : TwoTerm S} {f : ChainMap A B}
    [Module.Projective S B.X₀] (hf : IsQuasiIso f) : IsQuasiIso (f.baseChange T) :=
  isQuasiIso_of_isHomotopyEquiv
    (IsHomotopyEquiv.baseChange T (isHomotopyEquiv_of_isQuasiIso_of_projective hf))

/-- A chain map bijective on `H₁` carries the kernel of the source differential bijectively onto
the kernel of the target differential.  This is the converse of
`NaiveCotangent.bijective_onH₁_of_bijOn`. -/
theorem bijOn_ker_of_bijective_onH₁ {A B : TwoTerm S} {f : ChainMap A B}
    (hf : Function.Bijective f.onH₁) :
    Set.BijOn f.f₁ (LinearMap.ker A.d) (LinearMap.ker B.d) :=
  bijOn_ker_of_bijective_onH₁_aux hf

end BaseChange

/-!
## Formally smooth extensions
-/

section Extension

open Algebra

universe w u v

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
  {P P' : Extension.{w} R S}

/-- The cotangent space `S ⊗_P Ω[P⁄R]` of an extension whose ring is formally smooth over `R` is
a projective `S`-module, being the base change of the projective `P`-module `Ω[P⁄R]`. -/
theorem projective_cotangentSpace_of_formallySmooth (P : Extension.{w} R S)
    [FormallySmooth R P.Ring] : Module.Projective S P.CotangentSpace :=
  Module.Projective.tensorProduct (R := S) (R₀ := P.Ring) (M := S) (N := Ω[P.Ring⁄R])

/-- **A morphism of extensions into an extension with formally smooth ring, from one with
formally smooth ring, induces a homotopy equivalence of naive cotangent complexes.** -/
theorem isHomotopyEquiv_nlExtensionMap_of_formallySmooth (f : P.Hom P')
    [FormallySmooth R P.Ring] [FormallySmooth R P'.Ring] :
    IsHomotopyEquiv (nlExtensionMap f) :=
  @isHomotopyEquiv_of_isQuasiIso_of_projective S _ _ _ _
    (nlExtensionMap_isQuasiIso_of_formallySmooth f) (projective_cotangentSpace_of_formallySmooth P')

/-- **Base change of the comparison of two formally smooth presentations.**  For extensions `P`,
`P'` of `S` over `R` whose rings are formally smooth over `R`, a morphism of extensions
`f : P ⟶ P'` and any `S`-algebra `C`, the base change to `C` of the chain map
`NL(P) ⟶ NL(P')` is a quasi-isomorphism. -/
theorem isQuasiIso_baseChange_nlExtensionMap_of_formallySmooth (C : Type*) [CommRing C]
    [Algebra S C] (f : P.Hom P') [FormallySmooth R P.Ring] [FormallySmooth R P'.Ring] :
    IsQuasiIso ((nlExtensionMap f).baseChange C) :=
  isQuasiIso_of_isHomotopyEquiv
    ((isHomotopyEquiv_nlExtensionMap_of_formallySmooth f).baseChange C)

/-- **Degree `-1` cycles of the base changed comparison of two formally smooth presentations.**
For extensions `P`, `P'` of `S` over `R` whose rings are formally smooth over `R`, a morphism of
extensions `f : P ⟶ P'` and any `S`-algebra `C`, the map `C ⊗_S Cotangent.map f` carries the
kernel of `C ⊗_S d_P` bijectively onto the kernel of `C ⊗_S d_{P'}`. -/
theorem bijOn_lTensor_cotangentMap_ker_of_formallySmooth (C : Type*) [CommRing C]
    [Algebra S C] (f : P.Hom P') [FormallySmooth R P.Ring] [FormallySmooth R P'.Ring] :
    Set.BijOn (AlgebraTensorModule.lTensor C C (Extension.Cotangent.map f))
      (LinearMap.ker (AlgebraTensorModule.lTensor C C P.cotangentComplex))
      (LinearMap.ker (AlgebraTensorModule.lTensor C C P'.cotangentComplex)) :=
  bijOn_ker_of_bijective_onH₁
    (isQuasiIso_baseChange_nlExtensionMap_of_formallySmooth C f).1

end Extension

end NaiveCotangent

end
