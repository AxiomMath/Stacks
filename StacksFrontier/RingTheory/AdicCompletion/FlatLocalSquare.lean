module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties

/-!
# Flatness across a square of local homomorphisms with bijective completions

Consider a commuting square of local homomorphisms of Noetherian local rings

```
P ⟶ R
↓   ↓
Q ⟶ S
```

whose horizontal arrows induce bijections on the completions at the maximal ideals. Then the
right vertical arrow is flat as soon as the left one is.

## Main results

* `evalₐ_adicCompletionMap`: the level `n` evaluation of the map induced on adic completions is
  reduction modulo the `n`-th powers.
* `adicCompletionMap_comp_adicCompletionMap`: the maps induced on adic completions are
  functorial.
* `adicCompletionMap_congr`: equal homomorphisms induce the same map on adic completions.
* `flat_of_flat_of_bijective_adicCompletionMap`: flatness transfers across such a square.

## References

* [Stacks Project, Tag 0C4G](https://stacks.math.columbia.edu/tag/0C4G)
-/

@[expose] public section

universe u v w

section

/-- The level `n` evaluation of the map induced on adic completions is reduction of the given
homomorphism modulo the `n`-th powers. -/
public theorem evalₐ_adicCompletionMap {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (f : A →+* B) (J : Ideal A) (I : Ideal B) (hf : J.map f ≤ I) (n : ℕ)
    (x : AdicCompletion J A) :
    AdicCompletion.evalₐ I n (adicCompletionMap f J I hf x) =
      Ideal.quotientMap (I ^ n) f
        (Ideal.map_le_iff_le_comap.mp (by
          rw [Ideal.map_pow]; exact Ideal.pow_right_mono hf n))
        (AdicCompletion.evalₐ J n x) := by
  rw [adicCompletionMap, AdicCompletion.evalₐ_liftRingHom]
  rfl

/-- The maps induced on adic completions are functorial. -/
public theorem adicCompletionMap_comp_adicCompletionMap {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (I : Ideal A) (J : Ideal B) (K : Ideal C)
    (hf : I.map f ≤ J) (hg : J.map g ≤ K) (hgf : I.map (g.comp f) ≤ K) :
    (adicCompletionMap g J K hg).comp (adicCompletionMap f I J hf) =
      adicCompletionMap (g.comp f) I K hgf := by
  refine RingHom.ext fun x ↦ AdicCompletion.ext_evalₐ fun n ↦ ?_
  rw [RingHom.comp_apply, evalₐ_adicCompletionMap, evalₐ_adicCompletionMap,
    evalₐ_adicCompletionMap]
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [← hr]
  rfl

/-- Equal homomorphisms induce the same map on adic completions. -/
public theorem adicCompletionMap_congr {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    {f g : A →+* B} (I : Ideal A) (J : Ideal B) (hf : I.map f ≤ J) (hg : I.map g ≤ J)
    (h : f = g) :
    adicCompletionMap f I J hf = adicCompletionMap g I J hg := by
  subst h
  rfl

end

section

open IsLocalRing

/-- Ideals contained along a composite of ring homomorphisms stay contained. -/
private theorem map_comp_le_of_le {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    {f : A →+* B} {g : B →+* C} {I : Ideal A} {J : Ideal B} {K : Ideal C}
    (hf : I.map f ≤ J) (hg : J.map g ≤ K) : I.map (g.comp f) ≤ K := by
  rw [← Ideal.map_map]
  exact (Ideal.map_mono hf).trans hg

/-- Given a commuting square `z ∘ u = v ∘ w` of local homomorphisms of Noetherian local rings
whose horizontal arrows `u` and `v` induce bijections on the completions at the maximal ideals,
if the left vertical arrow `w` is flat, so is the right vertical arrow `z`. -/
public theorem flat_of_flat_of_bijective_adicCompletionMap
    {P Q R S : Type u} [CommRing P] [CommRing Q] [CommRing R] [CommRing S]
    [IsLocalRing P] [IsLocalRing Q] [IsLocalRing R] [IsLocalRing S]
    [IsNoetherianRing P] [IsNoetherianRing Q] [IsNoetherianRing R] [IsNoetherianRing S]
    {u : P →+* R} {v : Q →+* S} {w : P →+* Q} {z : R →+* S}
    [IsLocalHom u] [IsLocalHom v] [IsLocalHom w] [IsLocalHom z]
    (hsq : z.comp u = v.comp w)
    (hu : Function.Bijective (adicCompletionMap u (maximalIdeal P) (maximalIdeal R)
      (map_maximalIdeal_le u)))
    (hv : Function.Bijective (adicCompletionMap v (maximalIdeal Q) (maximalIdeal S)
      (map_maximalIdeal_le v)))
    (hw : _root_.RingHom.Flat w) :
    _root_.RingHom.Flat z := by
  have hzu := map_comp_le_of_le (map_maximalIdeal_le u) (map_maximalIdeal_le z)
  have hvw := map_comp_le_of_le (map_maximalIdeal_le w) (map_maximalIdeal_le v)
  let uc := adicCompletionMap u (maximalIdeal P) (maximalIdeal R) (map_maximalIdeal_le u)
  let vc := adicCompletionMap v (maximalIdeal Q) (maximalIdeal S) (map_maximalIdeal_le v)
  let wc := adicCompletionMap w (maximalIdeal P) (maximalIdeal Q) (map_maximalIdeal_le w)
  let zc := adicCompletionMap z (maximalIdeal R) (maximalIdeal S) (map_maximalIdeal_le z)
  have hcomm : zc.comp uc = vc.comp wc := by
    show (adicCompletionMap z _ _ _).comp (adicCompletionMap u _ _ _) =
      (adicCompletionMap v _ _ _).comp (adicCompletionMap w _ _ _)
    rw [adicCompletionMap_comp_adicCompletionMap u z _ _ _ _ _ hzu,
      adicCompletionMap_comp_adicCompletionMap w v _ _ _ _ _ hvw]
    exact adicCompletionMap_congr _ _ hzu hvw hsq
  let eu : AdicCompletion (maximalIdeal P) P ≃+* AdicCompletion (maximalIdeal R) R :=
    RingEquiv.ofBijective uc hu
  have heq : vc.comp (wc.comp eu.symm.toRingHom) = zc := RingHom.ext fun y ↦
    (DFunLike.congr_fun hcomm (eu.symm y)).symm.trans (congrArg zc (eu.apply_symm_apply y))
  exact (adicCompletionMap_flat_iff z).mp (heq ▸ ((_root_.RingHom.Flat.of_bijective
    eu.symm.bijective).comp ((adicCompletionMap_flat_iff w).mpr hw)).comp
      (_root_.RingHom.Flat.of_bijective hv) : _root_.RingHom.Flat zc)

end

end
