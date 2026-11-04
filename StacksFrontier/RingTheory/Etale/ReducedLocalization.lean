module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Smooth.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.RingTheory.Smooth.Reduced

/-!
# Reducedness of the local rings of an étale algebra

For an étale ring map `A → B` and prime ideals `q` of `B` and `p = q ∩ A` of `A`, the local
ring `A_p` is reduced if and only if `B_q` is. This is the reducedness clause of the list of
properties of local rings which are invariant under étale localization.

## Main results

* `isReduced_localizationAtPrime_iff_of_etale`: reducedness of the local rings at
  corresponding primes of an étale map agree.

## Implementation notes

The forward implication factors through the localization `B' = (M)⁻¹B` of `B` at the image of
`A \ p`, which is a smooth — indeed étale — `A_p`-algebra because it is the base change
`A_p ⊗_A B`, so it is reduced by Stacks 033B through `Algebra.isReduced_of_smooth`; the local
ring `B_q` is a further localization of `B'`, and reducedness passes to localizations.

The reverse implication is faithful flatness: an étale map is flat, flatness passes to the
induced local homomorphism `A_p → B_q`, and a flat local homomorphism of local rings is
faithfully flat, hence injective, so reducedness descends from `B_q` to `A_p`.

The two primes are related by the equation `q.comap (algebraMap A B) = p` rather than by an
`Ideal.LiesOver` instance, so that a caller holding the equation can apply the statement
without producing an instance first.

## References

* [Stacks Project, Tag 033B](https://stacks.math.columbia.edu/tag/033B)
* [Stacks Project, Tag 0BBL](https://stacks.math.columbia.edu/tag/0BBL)
-/

@[expose] public section

universe u v

/-- The localization of an étale algebra at a prime over a reduced local ring is reduced: it
is a further localization of the base change of the algebra to that local ring, which is
smooth over it and therefore reduced. -/
@[ega "IV 7.5.3" "(viii), special case"]
private theorem isReduced_localizationAtPrime_of_etale {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] (p : Ideal A) [p.IsPrime] (q : Ideal B)
    [q.IsPrime] (hq : q.comap (algebraMap A B) = p) [IsReduced (Localization.AtPrime p)] :
    IsReduced (Localization.AtPrime q) := by
  let M := p.primeCompl
  let N := q.primeCompl
  let M' := M.map (algebraMap A B)
  let B' := Localization M'
  have hMN : M' ≤ N := by
    rintro x ⟨a, ha, rfl⟩
    exact fun h => ha (hq ▸ h)
  let g : Localization.AtPrime p →+* B' :=
    IsLocalization.map B' (algebraMap A B) (Submonoid.le_comap_map M)
  let : Algebra (Localization.AtPrime p) B' := g.toAlgebra
  have : Algebra.Smooth (Localization.AtPrime p) B' :=
    Algebra.Smooth.of_equiv (Localization.tensorRightAlgEquiv M B)
  have hN : ∀ x : M', IsUnit (algebraMap B (Localization.AtPrime q) x) := fun x =>
    IsLocalization.map_units (Localization.AtPrime q) (⟨(x : B), hMN x.property⟩ : N)
  let j : B' →+* Localization.AtPrime q :=
    IsLocalization.lift (M := M') (S := B') (g := algebraMap B (Localization.AtPrime q)) hN
  let : Algebra B' (Localization.AtPrime q) := j.toAlgebra
  have : IsScalarTower B B' (Localization.AtPrime q) :=
    IsScalarTower.of_algebraMap_eq fun x => (IsLocalization.lift_eq hN x).symm
  have : IsLocalization (N.map (algebraMap B B')) (Localization.AtPrime q) :=
    IsLocalization.isLocalization_of_submonoid_le (S := B') (T := Localization.AtPrime q) M' N hMN
  exact isReduced_localizationPreserves (N.map (algebraMap B B')) (Localization.AtPrime q)
    (Algebra.isReduced_of_smooth (Localization.AtPrime p) B')

/-- **Stacks 0BBL, reducedness.** For prime ideals `p` and `q` corresponding under an étale
map `A → B`, the local ring of `A` at `p` is reduced if and only if the local ring of `B` at
`q` is reduced. -/
@[stacks 0BBL "reduced"]
theorem isReduced_localizationAtPrime_iff_of_etale {A : Type u} {B : Type v} [CommRing A]
    [CommRing B] [Algebra A B] [Algebra.Etale A B] (p : Ideal A) [p.IsPrime] (q : Ideal B)
    [q.IsPrime] (hq : q.comap (algebraMap A B) = p) :
    IsReduced (Localization.AtPrime p) ↔ IsReduced (Localization.AtPrime q) := by
  let f := Localization.localRingHom p q (algebraMap A B) hq.symm
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) := f.toAlgebra
  have : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    show IsLocalHom f
    infer_instance
  have hf : f.Flat :=
    RingHom.Flat.localRingHom (RingHom.Etale.iff_flat_and_formallyUnramified.mp
      ((RingHom.etale_algebraMap (R := A) (S := B)).mpr inferInstance)).1 q p hq.symm
  refine ⟨fun _ => isReduced_localizationAtPrime_of_etale p q hq, fun _ => ?_⟩
  have : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) := hf
  have : Module.FaithfullyFlat (Localization.AtPrime p) (Localization.AtPrime q) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact isReduced_of_injective (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
    (FaithfulSMul.algebraMap_injective _ _)

end
