module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksFrontier.RingTheory.FibreProduct

/-!
# The affine local model for a pushout along a closed immersion

Let `g : A →+* C` be a surjection of commutative rings and let `f : B →+* C` be any ring map.
The fibre product `D = B ×_C A` is the affine local model for the pushout of
`Spec B ← Spec C → Spec A` along the closed immersion `Spec C → Spec A`: the square of rings

```
D ---> B
|      |
v      v
A ---> C
```

is *cocartesian*, so that applying `Spec` turns it into a cartesian square of affine schemes,
the projection `D → B` is surjective, so that `Spec B → Spec D` is a closed immersion, and the
projection `D → A` is integral as soon as `f` is, so that `Spec A → Spec D` is integral.

This is the algebraic input shared by the two pushout constructions of
[Stacks Project, Tag 07RT] (a thickening and an affine morphism) and
[Stacks Project, Tag 0E25] (a closed immersion and an integral morphism); neither extra
hypothesis on `f` is needed for the cocartesian square itself.

## Main results

* `Stacks.Pushout.isPushout_ofHom_pullback` is the cocartesian square of rings: for `g`
  surjective, `C` is the pushout of `B ← D → A` in `CommRingCat`.
* `Stacks.Pushout.isPullback_ofHom_pullback` is the cartesian square of rings, which needs no
  hypothesis on `f` or `g`.
* `Stacks.Pushout.isPullback_specMap_pullback` is the resulting cartesian square of affine
  schemes, in the orientation of Tag 0E25: `Spec C = Spec A ×_{Spec D} Spec B`.
* `Stacks.Pushout.isClosedImmersion_specMap_pullbackFst`: the map `Spec B → Spec D` is a
  closed immersion.
* `Stacks.Pushout.isIntegralHom_specMap_pullbackSnd`: the map `Spec A → Spec D` is integral
  when `f` is integral.

## Implementation notes

The fibre product is Mathlib's `RingHom.pullback`, a subring of `B × A`, with projections
`RingHom.pullbackFst` and `RingHom.pullbackSnd`.  It is the same subring as the point of
`CommRingCat.pullbackCone`, so the statements here can be fed to the results of
`StacksFrontier.RingTheory.FibreProduct` directly.

The cocartesian square is proved by hand rather than by exhibiting `C` as a tensor product: the
mediating map out of `C` is obtained from `RingHom.liftOfSurjective`, the hypothesis
`RingHom.ker g ≤ RingHom.ker v` being supplied by the elements `(0, a)` of the fibre product,
which exist precisely because `g a = 0`.  Equality with the first leg uses surjectivity of `g`
once more, to lift `f b` to an element of `A` and hence `b` to an element of the fibre product.

What is *not* proved here is the universal property of [Stacks Project, Tag 0ET0]: that
`Spec (B ×_C A)` is the pushout of `Spec B ← Spec C → Spec A` in the category of all schemes,
rather than only in affine schemes, where it is `Stacks.Pushout.isPullback_ofHom_pullback` read
in the opposite category.  The source proves it by exhibiting the underlying topological space
as the pushout of topological spaces, which is
`StacksFrontier.RingTheory.FibreProduct.Spectrum`, identifying the structure sheaf with the fibre
product of the two direct images, and then constructing the mediating morphism of locally
ringed spaces by hand.  Only the first of those three steps is available.

## References

* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
* [Stacks Project, Tag 0E1S](https://stacks.math.columbia.edu/tag/0E1S)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0ET0](https://stacks.math.columbia.edu/tag/0ET0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Pushout

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- An element of `A` killed by `g` gives an element `(0, a)` of the fibre product `B ×_C A`. -/
theorem mem_pullback_of_mem_ker (f : B →+* C) (g : A →+* C) {a : A} (ha : a ∈ RingHom.ker g) :
    ((0 : B), a) ∈ f.pullback g := by
  simpa using (RingHom.mem_ker.mp ha).symm

/-- A pair `(b, a)` with `g a = f b` is an element of the fibre product `B ×_C A`. -/
theorem mem_pullback_iff (f : B →+* C) (g : A →+* C) (b : B) (a : A) :
    (b, a) ∈ f.pullback g ↔ f b = g a := by
  simp

/-- If two ring maps out of `B` and `A` agree on the fibre product `B ×_C A`, then they agree on
every pair `(b, a)` with `f b = g a`. -/
private theorem apply_eq_of_comp_eq {S : Type u} [CommRing S] {f : B →+* C} {g : A →+* C}
    {u : B →+* S} {v : A →+* S} (h : u.comp (f.pullbackFst g) = v.comp (f.pullbackSnd g))
    {b : B} {a : A} (hba : f b = g a) : u b = v a :=
  RingHom.congr_fun h ⟨(b, a), (mem_pullback_iff f g b a).mpr hba⟩

/-- If two ring maps out of `B` and `A` agree on the fibre product `B ×_C A`, then the one out
of `A` kills the kernel of `g`.  This is what makes the fibre product square cocartesian. -/
theorem ker_le_ker_of_comp_eq {S : Type u} [CommRing S] (f : B →+* C) (g : A →+* C)
    (u : B →+* S) (v : A →+* S)
    (h : u.comp (f.pullbackFst g) = v.comp (f.pullbackSnd g)) :
    RingHom.ker g ≤ RingHom.ker v := fun a ha ↦ by
  simpa using (apply_eq_of_comp_eq h (b := 0) (by simpa using (RingHom.mem_ker.mp ha).symm)).symm

/-- **The cocartesian square of rings.** For a surjection `g : A →+* C` and an arbitrary ring
map `f : B →+* C`, the ring `C` is the pushout of `B ← B ×_C A → A` in `CommRingCat`. -/
theorem isPushout_ofHom_pullback (f : B →+* C) (g : A →+* C) (hg : Function.Surjective g) :
    IsPushout (CommRingCat.ofHom (f.pullbackFst g)) (CommRingCat.ofHom (f.pullbackSnd g))
      (CommRingCat.ofHom f) (CommRingCat.ofHom g) := by
  have hsq : CommRingCat.ofHom (f.pullbackFst g) ≫ CommRingCat.ofHom f =
      CommRingCat.ofHom (f.pullbackSnd g) ≫ CommRingCat.ofHom g := by
    rw [← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, f.pullback_comm_sq g]
  have hcolim : IsColimit
      (PushoutCocone.mk (CommRingCat.ofHom f) (CommRingCat.ofHom g) hsq) := by
    refine PushoutCocone.isColimitAux' _ fun s ↦ ?_
    have hcomp : s.inl.hom.comp (f.pullbackFst g) = s.inr.hom.comp (f.pullbackSnd g) :=
      congrArg CommRingCat.Hom.hom s.condition
    have hker : RingHom.ker g ≤ RingHom.ker s.inr.hom :=
      ker_le_ker_of_comp_eq f g s.inl.hom s.inr.hom hcomp
    exact ⟨CommRingCat.ofHom (g.liftOfSurjective hg ⟨s.inr.hom, hker⟩), by
      refine CommRingCat.hom_ext (RingHom.ext fun b ↦ ?_)
      obtain ⟨a, ha⟩ := hg (f b)
      show (g.liftOfSurjective hg ⟨s.inr.hom, hker⟩) (f b) = s.inl.hom b
      rw [show f b = g a from ha.symm, RingHom.liftOfSurjective_comp_apply]
      exact (apply_eq_of_comp_eq hcomp ha.symm).symm, by
      exact CommRingCat.hom_ext (g.liftOfSurjective_comp hg ⟨s.inr.hom, hker⟩), by
      intro m _ hm
      exact CommRingCat.hom_ext
        (g.eq_liftOfSurjective hg s.inr.hom hker m.hom (congrArg CommRingCat.Hom.hom hm))⟩
  exact IsPushout.of_isColimit hcolim

/-- The fibre product square of rings is cartesian. -/
theorem isPullback_ofHom_pullback (f : B →+* C) (g : A →+* C) :
    IsPullback (CommRingCat.ofHom (f.pullbackFst g)) (CommRingCat.ofHom (f.pullbackSnd g))
      (CommRingCat.ofHom f) (CommRingCat.ofHom g) :=
  IsPullback.of_isLimit
    (CommRingCat.pullbackConeIsLimit (CommRingCat.ofHom f) (CommRingCat.ofHom g))

/-- **The cartesian square of affine schemes.** In the orientation of Tag 0E25, with
`X = Spec A`, `Y = Spec B`, `Z = Spec C` and the pushout `Spec (B ×_C A)`, the defining square
is a fibre square. -/
theorem isPullback_specMap_pullback (f : B →+* C) (g : A →+* C) (hg : Function.Surjective g) :
    IsPullback (Spec.map (CommRingCat.ofHom g)) (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom (f.pullbackSnd g)))
      (Spec.map (CommRingCat.ofHom (f.pullbackFst g))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_ofHom_pullback f g hg)).flip

/-- **The closed immersion.** The map `Spec B → Spec (B ×_C A)` is a closed immersion, because
the projection `B ×_C A → B` is surjective. -/
theorem isClosedImmersion_specMap_pullbackFst (f : B →+* C) (g : A →+* C)
    (hg : Function.Surjective g) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom (f.pullbackFst g))) :=
  IsClosedImmersion.spec_of_surjective _
    (RingHom.surjective_pullbackFst_of_surjective f g hg)

/-- **The integral morphism.** The map `Spec A → Spec (B ×_C A)` is integral, because the
projection `B ×_C A → A` is an integral ring map (Tag 0E1S). -/
theorem isIntegralHom_specMap_pullbackSnd (f : B →+* C) (g : A →+* C)
    (hg : Function.Surjective g) (hf : f.IsIntegral) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom (f.pullbackSnd g))) :=
  IsIntegralHom.SpecMap_iff.mpr
    (RingFibreProduct.pullback_snd_isIntegral_of_surjective f g hg hf)

end Stacks.Pushout

end
