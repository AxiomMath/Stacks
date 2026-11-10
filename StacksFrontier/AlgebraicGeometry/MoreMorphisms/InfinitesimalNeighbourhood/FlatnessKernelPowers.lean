module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalNeighbourhood.Flatness
import all StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalNeighbourhood.Flatness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flatness from a family of closed subschemes with power stalk ideals

[Stacks, Tag 0D4G] is `AlgebraicGeometry.isFlatAt_of_flat_infinitesimalNeighbourhoods`: flatness
of `f : X ⟶ S` at a point follows from flatness of its base changes to the infinitesimal
neighbourhoods of a closed subscheme. This file records the same argument for any family of
closed subschemes whose stalk ideals are the powers of one ideal, and its instance for the
thickenings `Spec (A ⧸ J ^ (n + 1))` of `V(J)` in an affine scheme.

## Main results

* `AlgebraicGeometry.flat_stalkMap_of_flat_pullbacks_of_ker_eq_pow`: flatness at a point from
  flatness along closed immersions whose stalk kernels are the powers of one ideal.
* `AlgebraicGeometry.flat_stalkMap_of_flat_pullbacks_spec_quotient_pow`: the case of the
  thickenings `Spec (A ⧸ J ^ (n + 1)) ⟶ Spec A`.

## Implementation notes

The proof reuses the private stalk computations of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.InfinitesimalNeighbourhood.Flatness`, which is why
that module is imported with `import all`.

## References

* [Stacks Project, Tag 0D4G](https://stacks.math.columbia.edu/tag/0D4G)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Flatness at a point from flatness along a family of closed subschemes whose stalk ideals
are the powers of one ideal.** Let `f : X ⟶ S` be a morphism of locally Noetherian schemes and
let `gₙ : Tₙ ⟶ S` be closed immersions through `f x`, at points `zₙ`, such that the kernel of the
stalk map of `gₙ` at `zₙ` is the `(n + 1)`-st power of the kernel of the stalk map of `g₀` at
`z₀`. If every base change of `f` along `gₙ` is flat, then `f` is flat at `x`.

This is [Stacks, Tag 0D4G] with the infinitesimal neighbourhoods of a closed subscheme replaced
by any family of closed subschemes with the same stalks; the proof is the one of
`AlgebraicGeometry.isFlatAt_of_flat_infinitesimalNeighbourhoods`. -/
@[sga "3 X 4.3" "more general"]
theorem flat_stalkMap_of_flat_pullbacks_of_ker_eq_pow
    {X S : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian S]
    (f : X ⟶ S) {T : ℕ → Scheme.{u}} (g : ∀ n, T n ⟶ S) [∀ n, IsClosedImmersion (g n)]
    (hflat : ∀ n : ℕ, Flat (pullback.snd f (g n)))
    (x : X) (z : ∀ n, T n) (hz : ∀ n, f x = g n (z n))
    (hker : ∀ n, RingHom.ker
        (eqToHom (congrArg S.presheaf.stalk (hz n)) ≫ (g n).stalkMap (z n)).hom =
      RingHom.ker
        (eqToHom (congrArg S.presheaf.stalk (hz 0)) ≫ (g 0).stalkMap (z 0)).hom ^ (n + 1)) :
    (f.stalkMap x).hom.Flat := by
  let R := S.presheaf.stalk (f x)
  let A := X.presheaf.stalk x
  let : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let q := eqToHom (congrArg S.presheaf.stalk (hz 0)) ≫ (g 0).stalkMap (z 0)
  let I := RingHom.ker q.hom
  change Module.Flat R A
  refine flat_ringHom_of_flat_quotient_pow_local I (Ideal.map_le_iff_le_comap.mpr
    ((IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top q.hom)).trans_eq
      (IsLocalRing.maximalIdeal_comap (f.stalkMap x).hom).symm)) fun n => ?_
  let qn := eqToHom (congrArg S.presheaf.stalk (hz n)) ≫ (g n).stalkMap (z n)
  let : Algebra R ((T n).presheaf.stalk (z n)) := qn.hom.toAlgebra
  exact flat_quotient_of_flat_tensor (Q := (T n).presheaf.stalk (z n)) (I ^ (n + 1))
    (((g n).stalkMap_surjective (z n)).comp
      (asIso (eqToHom (congrArg S.presheaf.stalk (hz n)))).commRingCatIsoToRingEquiv.surjective)
    (hker n) (flat_tensor_stalk_of_flat_pullback f (g n) (hflat n) x (z n) (hz n))

/-- The kernel of the global-sections map of `Spec (A ⧸ K) ⟶ Spec A` is `K`, carried to the
global sections of `Spec A`. -/
private lemma ker_ideal_top_spec_quotient {A : Type u} [CommRing A] (K : Ideal A) :
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).ker.ideal
        ⟨⊤, isAffineOpen_top (Spec (.of A))⟩ =
      K.map (Scheme.ΓSpecIso (.of A)).inv.hom := by
  rw [Scheme.Hom.ker_apply]
  let e := (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv
  let e' := (Scheme.ΓSpecIso (.of (A ⧸ K))).commRingCatIsoToRingEquiv
  have hcomp : (e' : _ →+* (A ⧸ K)).comp
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).appTop.hom =
      (Ideal.Quotient.mk K).comp (e : _ →+* A) :=
    congrArg CommRingCat.Hom.hom
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk K)))
  change RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).appTop.hom = _
  have hk : RingHom.ker (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).appTop.hom =
      RingHom.ker ((e' : _ →+* (A ⧸ K)).comp
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).appTop.hom) := by
    ext a
    simp [RingHom.mem_ker]
  rw [hk, hcomp, ← RingHom.comap_ker, Ideal.mk_ker]
  exact (Ideal.map_symm (f := e) (I := K)).symm

/-- **Flatness at a point over `V(J)` from flatness over the thickenings
`Spec (A ⧸ J ^ (n + 1))`.** Let `f : X ⟶ Spec A` with `X` locally Noetherian and `A` Noetherian,
and let `x ∈ X` lie over `V(J)`. If the base change of `f` to every `Spec (A ⧸ J ^ (n + 1))` is
flat, then `f` is flat at `x`. This is [Stacks, Tag 0D4G] for the closed subscheme `V(J)` of an
affine scheme, with its infinitesimal neighbourhoods written as spectra. -/
theorem flat_stalkMap_of_flat_pullbacks_spec_quotient_pow {X : Scheme.{u}}
    [IsLocallyNoetherian X] {A : Type u} [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (f : X ⟶ Spec (.of A))
    (hflat : ∀ n : ℕ, Flat (pullback.snd f
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1)))))))
    (x : X) (hx : J ≤ (f x).asIdeal) : (f.stalkMap x).hom.Flat := by
  let g : ∀ n : ℕ, Spec (.of (A ⧸ J ^ (n + 1))) ⟶ Spec (.of A) := fun n =>
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (J ^ (n + 1))))
  have : ∀ n, IsClosedImmersion (g n) := fun n =>
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hle : ∀ n, RingHom.ker (Ideal.Quotient.mk (J ^ (n + 1))) ≤ (f x).asIdeal := fun n =>
    Ideal.mk_ker.trans_le ((Ideal.pow_le_self (Nat.succ_ne_zero n)).trans hx)
  let p : PrimeSpectrum A := f x
  let z : ∀ n, Spec (.of (A ⧸ J ^ (n + 1))) := fun n =>
    ⟨p.asIdeal.map (Ideal.Quotient.mk (J ^ (n + 1))),
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (hle n)⟩
  have hz : ∀ n, f x = g n (z n) := fun n => by
    apply PrimeSpectrum.ext
    change p.asIdeal = Ideal.comap (Ideal.Quotient.mk (J ^ (n + 1)))
      (p.asIdeal.map (Ideal.Quotient.mk (J ^ (n + 1))))
    rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.mpr (hle n)]
  refine flat_stalkMap_of_flat_pullbacks_of_ker_eq_pow f g hflat x z hz fun n => ?_
  have key (m : ℕ) := ker_stalkMap_congr_eq_map (g m) (z m) ⊤ (isAffineOpen_top (Spec (.of A)))
    (f x) trivial (hz m)
  rw [key, key]
  simp only [g, ker_ideal_top_spec_quotient, ← Ideal.map_pow, zero_add, pow_one]

end AlgebraicGeometry
