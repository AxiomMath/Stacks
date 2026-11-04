module

public import StacksFrontier.RingTheory.CompleteIntersection.Local
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.CompleteLocalRing.PowerSeriesFormallySmooth
public import StacksFrontier.RingTheory.LocalCompleteIntersection.Basic
public import StacksFrontier.RingTheory.LocalCompleteIntersection.FlatLocalHomomorphism
public import StacksFrontier.RingTheory.RelativeDimension.Basic
public import StacksFrontier.RingTheory.Syntomic.SyntomicAt
public import StacksFrontier.AlgebraicGeometry.Descent.SyntomicDescent

/-!
# Descent of the local complete intersection condition along a faithfully flat syntomic algebra

This file proves
`Stacks.RingTheory.SyntomicDescent.LciDescendsAlongFaithfullyFlatSyntomic`, the descent of the
local-complete-intersection condition along a faithfully flat syntomic algebra, and places the
Stacks tags for the scheme-level descent of syntomicity.

## Main results

* `Stacks.RingTheory.SyntomicDescent.isCompleteIntersectionRing_of_flat`: a Noetherian local
  ring is a complete intersection as soon as it admits a flat local homomorphism to a complete
  intersection local ring whose closed fibre is again a complete intersection.
* `Stacks.RingTheory.SyntomicDescent.isLocalCompleteIntersection_of_faithfullyFlat_syntomic`:
  for `k → A → B` with `k` a field, `A` of finite type over `k` and `A → B` syntomic and
  faithfully flat, `B` being a local complete intersection over `k` forces `A` to be one.
* `Stacks.RingTheory.SyntomicDescent.lciDescendsAlongFaithfullyFlatSyntomic` packages that as
  the predicate named in `StacksFrontier.AlgebraicGeometry.Descent.SyntomicAlgebra`.
* `Stacks.Syntomic.syntomic_of_comp` and
  `Stacks.Syntomic.syntomic_of_comp_of_locallyOfFinitePresentation` are the unconditional
  scheme-level statements. They no longer consume the predicate:
  `AlgebraicGeometry.syntomic_of_comp_surjective_syntomic` proves the scheme-level descent
  outright, by the fppf route, so only the tags are placed here.

## Implementation notes

The field `k` disappears at once: `A` and `B` are of finite type over `k`, so
`LocalCompleteIntersection.isLocalCompleteIntersection_iff_isLocalCompleteIntersectionRing`
(Lemma 09Q6 (2)) rewrites both sides of the implication into the absolute, completion-based
`IsLocalCompleteIntersectionRing`. What is left is a statement about one prime `𝔮` of `A` at a
time: that `A_𝔮` is a complete intersection.

`A → B` is faithfully flat, so `𝔮` is the contraction of a prime `𝔮'` of `B`
(`Ideal.exists_isPrime_liesOver_of_faithfullyFlat`); `𝔮'` is in turn the contraction of a prime
`𝔔` of the fibre `κ(𝔮) ⊗_A B` (`Ideal.Fiber.exists_comap_includeRight_eq`), which is the form
needed to recognise the closed fibre of `A_𝔮 → B_{𝔮'}` as a localization of `κ(𝔮) ⊗_A B`:
Mathlib's `Ideal.Fiber.localizationAlgEquivQuotient` identifies `(κ(𝔮) ⊗_A B)_𝔔` with
`B_{𝔮'} ⧸ 𝔮 B_{𝔮'}`. Syntomicity of `A → B` makes `κ(𝔮) ⊗_A B` a local complete intersection
over `κ(𝔮)` (`Algebra.Syntomic.isLocalCompleteIntersection_fiber`), so Lemma 09Q6 (2) again
makes that closed fibre a complete intersection ring, and `B_{𝔮'}` is one because `B` is.

That leaves the purely local statement `isCompleteIntersectionRing_of_flat`, which is Stacks'
own argument for Tag 02K3. Passing to the completions `Â` and `B̂` keeps flatness (Lemma 0C4G,
`adicCompletionMap_flat_iff`) and lets Lemma 07NN
(`exists_powerSeries_presentation_of_isLocalHom`) produce the commutative square

```
B̂ ← S
↑    ↑
Â ← R
```

with `R` and `S` regular local and adic complete, both rows surjective, `R → S` flat and
`S ⧸ 𝔪_R S` regular local. This is exactly the square that Lemma 02JP
(`exists_isRegular_ofList_eq_ker_algebraMap_of_flat`) consumes, so no presentations by
polynomial algebras have to be built. Its two regular-sequence hypotheses come from Lemma 09PZ
(`forall_regularPresentation_iff_exists`), which turns one regular-local presentation with
regular-sequence kernel into all of them: for `ker (S → B̂)` directly from
`IsCompleteIntersectionRing B`, and for its image in `S ⧸ 𝔪_R S` from
`IsCompleteIntersectionRing (B ⧸ 𝔪_A B)` after the identification
`(B ⧸ 𝔪_A B)^ ≃ B̂ ⧸ 𝔪_A B̂` (`nonempty_ringEquiv_adicCompletion_quotient`, Lemma 00MB) and
the computation `Ideal.map q_B (𝔪_R S) = Ideal.map (B → B̂) (𝔪_A B)`, which uses that `q_A` is a
surjective local homomorphism. The conclusion of 02JP is a regular sequence generating
`ker (R → Â)`, which with `R` regular local is the definition of
`IsCompleteIntersectionRing A`.

**The commuting square of a ring map
with the induced map of completions is declared, privately and identically, in ten modules of the
tree, including the module that defines `adicCompletionMap` itself. Making any one of them public
is not possible without editing all the others: a `private` declaration does not shadow an
imported public one of the same name, so exposing the copy in
`StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties` makes every other copy fail to
elaborate with "a non-private declaration has already been declared" (for instance
`StacksFrontier/RingTheory/FormalFibres/Localization.lean:136`). This file therefore keeps its own
private copy.

## References

* [Stacks Project, Tag 02K3](https://stacks.math.columbia.edu/tag/02K3)
* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing LocalCompleteIntersection
open RingTheory.Sequence

universe u

namespace Stacks.RingTheory.SyntomicDescent

/-- The map induced on completions at the maximal ideals by a local homomorphism of Noetherian
local rings is again a local homomorphism. -/
private theorem isLocalHom_adicCompletionMap {A B : Type*} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] :
    IsLocalHom (adicCompletionMap f (maximalIdeal A) (maximalIdeal B)
      (IsLocalRing.map_maximalIdeal_le f)) := by
  apply ((IsLocalRing.local_hom_TFAE _).out 1 3).mpr
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map,
    adicCompletionMap_comp_algebraMap, ← Ideal.map_map,
    AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.map_mono (IsLocalRing.map_maximalIdeal_le f)

/-- For a surjection `q : S → T` carrying `I` onto `J`, the kernel of the induced map
`S ⧸ I → T ⧸ J` is the image of `ker q`. -/
private theorem ker_quotient_lift_comp_mk {S T : Type*} [CommRing S] [CommRing T] {q : S →+* T}
    (hq : Function.Surjective q) {I : Ideal S} {J : Ideal T} (h : I.map q = J)
    (H : ∀ a ∈ I, ((Ideal.Quotient.mk J).comp q) a = 0) :
    RingHom.ker (Ideal.Quotient.lift I ((Ideal.Quotient.mk J).comp q) H) =
      (RingHom.ker q).map (Ideal.Quotient.mk I) := by
  have hker : RingHom.ker ((Ideal.Quotient.mk J).comp q) = I ⊔ RingHom.ker q := by
    have hc : RingHom.ker ((Ideal.Quotient.mk J).comp q) = Ideal.comap q J := by
      ext x
      simp only [RingHom.mem_ker, RingHom.comp_apply, Ideal.mem_comap]
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [hc, ← h, Ideal.comap_map_of_surjective q hq, ← RingHom.ker_eq_comap_bot]
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := I) x
    have hy : y ∈ RingHom.ker ((Ideal.Quotient.mk J).comp q) :=
      RingHom.mem_ker.mpr (RingHom.mem_ker.mp hx)
    rw [hker] at hy
    rw [← bot_sup_eq (RingHom.ker q |>.map _), ← Ideal.map_quotient_self I, ← Ideal.map_sup]
    exact Ideal.mem_map_of_mem _ hy
  · rw [Ideal.map_le_iff_le_comap]
    intro y hy
    have hmem : y ∈ RingHom.ker ((Ideal.Quotient.mk J).comp q) :=
      hker ▸ Ideal.mem_sup_right hy
    exact RingHom.mem_ker.mp hmem

/-- If `X` is a complete intersection ring and `C` is a complete Noetherian local ring
isomorphic to the completion of `X`, then every surjection from a regular local ring onto `C` has
kernel generated by a regular sequence. -/
private theorem exists_isRegular_ofList_eq_ker_of_isCompleteIntersectionRing {X C : Type u}
    [CommRing X] [IsLocalRing X] [IsNoetherianRing X] [CommRing C] [IsLocalRing C]
    [IsNoetherianRing C] [IsAdicComplete (maximalIdeal C) C]
    (hX : IsCompleteIntersectionRing X) (e : AdicCompletion (maximalIdeal X) X ≃+* C)
    (T : Type u) [CommRing T] [IsRegularLocalRing T] (f : T →+* C) (hf : Function.Surjective f) :
    ∃ rs : List T, IsRegular T rs ∧ Ideal.ofList rs = RingHom.ker f := by
  obtain ⟨T', iT, hT, h, hh, _, rs, hrs, hker⟩ := hX
  refine (forall_regularPresentation_iff_exists C).mpr
    ⟨T', iT, hT, e.toRingHom.comp h, e.surjective.comp hh, rs, hrs, ?_⟩ T f hf
  rw [hker, RingHom.ker_comp_of_injective _ e.injective]

/-- Let `B` be a Noetherian local ring and `I₀` an ideal with `B ⧸ I₀` a complete intersection.
Then every surjection from a regular local ring onto `B̂ ⧸ I₀ B̂` has kernel generated by a
regular sequence. -/
private theorem exists_isRegular_ofList_eq_ker_of_isCompleteIntersectionRing_quotient {B : Type u}
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (I₀ : Ideal B)
    [IsLocalRing (B ⧸ I₀)] [IsNoetherianRing (B ⧸ I₀)]
    (hfib : IsCompleteIntersectionRing (B ⧸ I₀)) (T : Type u) [CommRing T]
    [IsRegularLocalRing T]
    (f : T →+* AdicCompletion (maximalIdeal B) B ⧸
      I₀.map (algebraMap B (AdicCompletion (maximalIdeal B) B)))
    (hf : Function.Surjective f) :
    ∃ rs : List T, IsRegular T rs ∧ Ideal.ofList rs = RingHom.ker f := by
  set Fh := AdicCompletion (maximalIdeal (B ⧸ I₀)) (B ⧸ I₀)
  set C := AdicCompletion (maximalIdeal B) B ⧸
    I₀.map (algebraMap B (AdicCompletion (maximalIdeal B) B))
  obtain ⟨e0⟩ := nonempty_ringEquiv_adicCompletion_quotient (R := B) I₀
  have : IsLocalRing C := e0.isLocalRing
  have : IsNoetherianRing C := isNoetherianRing_of_ringEquiv Fh e0
  have : IsAdicComplete (maximalIdeal C) C := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal e0]
    exact (IsAdicComplete.congr_ringEquiv (maximalIdeal Fh) e0).mpr inferInstance
  exact exists_isRegular_ofList_eq_ker_of_isCompleteIntersectionRing hfib e0 T f hf

/-- **Descent of the complete intersection condition along a flat local homomorphism.** Let
`A → B` be a flat local homomorphism of Noetherian local rings. If `B` is a complete intersection
local ring and so is its closed fibre `B ⧸ 𝔪_A B`, then `A` is a complete intersection local
ring. The ideal `I₀` is the closed fibre ideal `𝔪_A B`, passed separately so that a caller which
has it in another spelling does not have to rewrite inside a quotient type. -/
theorem isCompleteIntersectionRing_of_flat {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)] [Module.Flat A B] (I₀ : Ideal B)
    (hI₀ : I₀ = (maximalIdeal A).map (algebraMap A B))
    [IsLocalRing (B ⧸ I₀)] [IsNoetherianRing (B ⧸ I₀)]
    (hB : IsCompleteIntersectionRing B) (hfib : IsCompleteIntersectionRing (B ⧸ I₀)) :
    IsCompleteIntersectionRing A := by
  classical
  set Ah := AdicCompletion (maximalIdeal A) A
  set Bh := AdicCompletion (maximalIdeal B) B
  set fh : Ah →+* Bh := adicCompletionMap (algebraMap A B) (maximalIdeal A) (maximalIdeal B)
    (IsLocalRing.map_maximalIdeal_le (algebraMap A B)) with hfh
  have hfhlocal : IsLocalHom fh := isLocalHom_adicCompletionMap (algebraMap A B)
  have hfhflat : fh.Flat :=
    (adicCompletionMap_flat_iff (algebraMap A B)).mpr (RingHom.flat_algebraMap_iff.mpr ‹_›)
  obtain ⟨R, S, _, hRreg, _, _, hSreg, _, g, qA, qB, hqA, hqB, _, hqAlocal, _, hcomm, -,
    hflatRS, hSbarreg⟩ := exists_powerSeries_presentation_of_isLocalHom fh
  let _ : Algebra R S := g.toAlgebra
  let _ : Algebra R Ah := qA.toAlgebra
  let _ : Algebra S Bh := qB.toAlgebra
  let _ : Algebra Ah Bh := fh.toAlgebra
  let _ : Algebra R Bh := (qB.comp g).toAlgebra
  have htowerS : IsScalarTower R S Bh := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have htowerA : IsScalarTower R Ah Bh := IsScalarTower.of_algebraMap_eq' hcomm.symm
  have hflatAh : Module.Flat Ah Bh := RingHom.flat_algebraMap_iff.mp hfhflat
  have hCM : Module.IsMaximalCohenMacaulay R R :=
    (IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay R).2
  set mR : Ideal S := (maximalIdeal R).map (algebraMap R S) with hmR
  have hmRg : mR = Ideal.map g (maximalIdeal R) := by
    rw [hmR, RingHom.algebraMap_toAlgebra]
  have hJ : ∃ rs : List S, IsRegular S rs ∧
      Ideal.ofList rs = RingHom.ker (algebraMap S Bh) := by
    exact exists_isRegular_ofList_eq_ker_of_isCompleteIntersectionRing hB (RingEquiv.refl _) S
      (algebraMap S Bh) hqB
  have hmap : Ideal.map qB mR = Ideal.map (algebraMap B Bh) I₀ := by
    rw [hmRg, Ideal.map_map, ← hcomm, ← Ideal.map_map,
      IsLocalRing.map_maximalIdeal_of_surjective qA hqA, AdicCompletion.maximalIdeal_eq_map,
      Ideal.map_map, hfh, adicCompletionMap_comp_algebraMap, ← Ideal.map_map, hI₀]
  have hmRle : ∀ a ∈ mR, ((Ideal.Quotient.mk (Ideal.map (algebraMap B Bh) I₀)).comp qB) a = 0 :=
    fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (hmap ▸ Ideal.mem_map_of_mem qB ha)
  have hsurj : Function.Surjective (Ideal.Quotient.lift mR _ hmRle) := fun z => by
    obtain ⟨y, rfl⟩ := (Ideal.Quotient.mk_surjective.comp hqB) z
    exact ⟨Ideal.Quotient.mk mR y, rfl⟩
  have : IsRegularLocalRing (S ⧸ mR) := hmRg ▸ hSbarreg
  have hJbar : ∃ rs : List (S ⧸ mR), IsRegular (S ⧸ mR) rs ∧
      Ideal.ofList rs = (RingHom.ker (algebraMap S Bh)).map (Ideal.Quotient.mk mR) := by
    obtain ⟨rs, hrs, hker⟩ :=
      exists_isRegular_ofList_eq_ker_of_isCompleteIntersectionRing_quotient I₀ hfib (S ⧸ mR) _
        hsurj
    exact ⟨rs, hrs, hker.trans (ker_quotient_lift_comp_mk hqB hmap hmRle)⟩
  obtain ⟨rs, hrs, hker⟩ :=
    exists_isRegular_ofList_eq_ker_algebraMap_of_flat (R := R) (S := S) (A := Ah) (B := Bh)
      hCM hqA hqB hJ hJbar
  exact ⟨R, inferInstance, hRreg, qA, hqA, hqAlocal, rs, hrs, hker⟩

/-- **Descent of the local-complete-intersection condition over a field.** For `k → A → B` with
`k` a field, `A` of finite type over `k`, and `A → B` syntomic and faithfully flat: if `B` is a
local complete intersection over `k`, then so is `A`. This is the commutative algebra content of
Stacks Tag 02K3. -/
theorem isLocalCompleteIntersection_of_faithfullyFlat_syntomic (k A B : Type u) [Field k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra A B] [Algebra k B] [IsScalarTower k A B]
    [Module.FaithfullyFlat A B] [Algebra.Syntomic A B] [Algebra.FiniteType k A]
    (hB : IsLocalCompleteIntersection k B) : IsLocalCompleteIntersection k A := by
  classical
  have : Algebra.FinitePresentation A B := Algebra.Syntomic.finitePresentation
  have hFTB : Algebra.FiniteType k B :=
    Algebra.FiniteType.trans (R := k) (S := A) ‹_› inferInstance
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  have hBabs : IsLocalCompleteIntersectionRing B :=
    (isLocalCompleteIntersection_iff_isLocalCompleteIntersectionRing k B).mp hB
  refine (isLocalCompleteIntersection_iff_isLocalCompleteIntersectionRing k A).mpr ?_
  intro q hq
  have : q.IsPrime := hq
  have hfibLci : IsLocalCompleteIntersection q.ResidueField (q.Fiber B) :=
    Algebra.Syntomic.isLocalCompleteIntersection_fiber (R := A) (S := B) q
  have : IsNoetherianRing (q.Fiber B) :=
    Algebra.FiniteType.isNoetherianRing q.ResidueField (q.Fiber B)
  have hfibAbs : IsLocalCompleteIntersectionRing (q.Fiber B) :=
    (isLocalCompleteIntersection_iff_isLocalCompleteIntersectionRing q.ResidueField
      (q.Fiber B)).mp hfibLci
  obtain ⟨q0, hq0p, hq0lo⟩ := Ideal.exists_isPrime_liesOver_of_faithfullyFlat (A := A) (B := B) q
  have : q0.IsPrime := hq0p
  have : q0.LiesOver q := hq0lo
  obtain ⟨Q, hQp, hQ⟩ := Ideal.Fiber.exists_comap_includeRight_eq q0 q Ideal.LiesOver.over.symm
  have : Q.IsPrime := hQp
  subst hQ
  let _ := Localization.AtPrime.algebraOfLiesOver q
    (Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] q.Fiber B))
  set q' := Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] q.Fiber B)
  have hlh : IsLocalHom (algebraMap (Localization.AtPrime q) (Localization.AtPrime q')) := by
    rw [Localization.AtPrime.IsLiesOverAlgebra.algebraMap_eq]
    infer_instance
  have hflatAB' : Module.Flat A (Localization.AtPrime q') :=
    (Algebra.Syntomic.flat_localization_and_isCompleteIntersection_fiber (R := A) (S := B) q').1
  have hflat : Module.Flat (Localization.AtPrime q) (Localization.AtPrime q') :=
    (Localization.AtPrime.flat_localRingHom_iff q q').mpr hflatAB'
  have e := Ideal.Fiber.localizationAlgEquivQuotient q Q
  have : IsLocalRing (Localization.AtPrime q' ⧸
      Ideal.map (algebraMap A (Localization.AtPrime q')) q) := e.toRingEquiv.isLocalRing
  have : IsNoetherianRing (Localization.AtPrime q' ⧸
      Ideal.map (algebraMap A (Localization.AtPrime q')) q) :=
    isNoetherianRing_of_ringEquiv (Localization.AtPrime Q) e.toRingEquiv
  have hquot : IsCompleteIntersectionRing (Localization.AtPrime q' ⧸
      Ideal.map (algebraMap A (Localization.AtPrime q')) q) :=
    isCompleteIntersectionRing_of_ringEquiv e.toRingEquiv (hfibAbs Q)
  have hideal : Ideal.map (algebraMap A (Localization.AtPrime q')) q =
      (maximalIdeal (Localization.AtPrime q)).map
        (algebraMap (Localization.AtPrime q) (Localization.AtPrime q')) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq A (Localization.AtPrime q) (Localization.AtPrime q')]
  exact isCompleteIntersectionRing_of_flat _ hideal (hBabs q') hquot

/-- The descent of the local-complete-intersection condition over a field, in the packaged form
taken as a hypothesis by `StacksFrontier.AlgebraicGeometry.Descent.SyntomicAlgebra`. -/
theorem lciDescendsAlongFaithfullyFlatSyntomic :
    LciDescendsAlongFaithfullyFlatSyntomic.{u} :=
  fun k A B _ _ _ _ _ _ _ _ _ _ => isLocalCompleteIntersection_of_faithfullyFlat_syntomic k A B

end Stacks.RingTheory.SyntomicDescent

namespace Stacks.Syntomic

variable {X Y S : Scheme.{u}}

/-- **Stacks Project, Tag 02KM (syntomic case).** Syntomicity descends along a surjective
syntomic morphism: if `f : X ⟶ Y` is surjective and syntomic and `f ≫ q` is syntomic, then
`q : Y ⟶ S` is syntomic.

This is the syntomic one of the lemma's three cases; the étale case is
`Stacks.Etale.etale_of_comp_surjective_etale` and the smooth case is
`Stacks.Smooth.smooth_of_comp_surjective_smooth`. -/
@[stacks 02KM "syntomic_case"]
theorem syntomic_of_comp (f : X ⟶ Y) (q : Y ⟶ S) [Surjective f] (hf : Syntomic f)
    (hcomp : Syntomic (f ≫ q)) : Syntomic q :=
  syntomic_of_comp_surjective_syntomic f q hf hcomp

/-- **Stacks Project, Tag 02K3.** Let `X ⟶ Y ⟶ S` be morphisms of schemes with `X ⟶ Y`
surjective and syntomic and the composite `X ⟶ S` syntomic. If `Y ⟶ S` is locally of finite
presentation, then `Y ⟶ S` is syntomic. -/
@[stacks 02K3]
theorem syntomic_of_comp_of_locallyOfFinitePresentation (f : X ⟶ Y) (q : Y ⟶ S) [Surjective f]
    (hf : Syntomic f) (hcomp : Syntomic (f ≫ q)) [LocallyOfFinitePresentation q] :
    Syntomic q :=
  syntomic_of_comp f q hf hcomp

end Stacks.Syntomic

end
