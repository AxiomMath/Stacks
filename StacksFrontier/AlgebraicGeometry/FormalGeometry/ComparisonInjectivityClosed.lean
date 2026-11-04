module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.SupportClosure
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ComparisonInjectivity

/-!
# The injectivity half of Stacks 0EG2

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `F` be a
coherent module on `U`. `Stacks.Algebraization.comparisonMap` compares the sections of `F`
defined on arbitrarily small neighbourhoods of the formal locus `U ∩ V(I)` with the compatible
families of sections of `F / Iⁿ F` on all of `U`.

This file closes the injectivity half of Stacks 0EG2. The source's argument is: a section `s`
of `F` near the formal locus killed by the comparison has vanishing germ along the formal locus
by Krull's intersection theorem, which is
`Stacks.Algebraization.germ_eq_zero_of_comparisonAt_apply_eq_zero`; every associated point `x`
of `F` specializes to a point `y` of the formal locus, so the germ of `s` at `x` vanishes too,
since `F_x` receives the stalk `F_y`; and a section with vanishing germs at every associated
point is zero.

The hypothesis that every associated point of `F` specializes into the formal locus is the one
the source obtains from the depth-one reduction of Tag 0DX3 — it is exactly the sentence "an
associated point `x` of `F` must have `closure {x} ∩ U ∩ Y ≠ ∅` by the previous paragraph" — and
it is taken here as an explicit hypothesis, so that the reduction itself, which replaces `F` by
a quotient isomorphic to it near the formal locus, is a separate step.

## Main results

* `Stacks.Algebraization.mem_support_baseIdealSheaf` — a point over `V(I)` lies in the support
  of `I · 𝒪_X`, the converse of `Stacks.Algebraization.support_baseIdealSheaf_le`.
* `Stacks.Algebraization.mono_comparisonMap_of_associatedPoints_specializes_vanishing` — **the
  injectivity half of Stacks 0EG2**: the comparison map is a monomorphism provided the closure
  of every associated point of `F` meets `U ∩ V(I)`.

## Implementation notes

Germ vanishing is transported along the specialization by
`AlgebraicGeometry.germ_eq_zero_of_specializes`, which needs only the map on stalks attached to
a specialization; and the passage from vanishing germs at the associated points to vanishing of
the section is `AlgebraicGeometry.eq_zero_of_forall_germ_associatedPoints_eq_zero`, stated over
an arbitrary open because the section here lives on a neighbourhood of the formal locus rather
than on all of `U`.

The hypothesis is phrased with `I ≤ y.1.asIdeal`, the source's `y ∈ V(I)`, rather than with
membership in the support of `I · 𝒪_U`; the two agree, by
`Stacks.Algebraization.support_baseIdealSheaf_le` and
`Stacks.Algebraization.mem_support_baseIdealSheaf`, and the former is the weaker hypothesis to
discharge. The point of the formal locus it produces automatically lies in the neighbourhood, by
`Stacks.Algebraization.support_idealSheafNearVanishing_le`, and so does the associated point
above it, since an open containing a point contains every point it is a specialization of.

## References

* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0DX3](https://stacks.math.columbia.edu/tag/0DX3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

open Stacks.Cohomology.FormalFunctions in
/-- A point lying over the zero locus of `I` lies in the support of the extended ideal sheaf
`I · 𝒪_X`. Together with `Stacks.Algebraization.support_baseIdealSheaf_le` this identifies that
support with the preimage of `V(I)`.

The functions on `X` which do not generate the unit ideal in the local ring at `x` form an
ideal, namely the contraction of the maximal ideal along the germ map, and `x` lies in the
support of `I · 𝒪_X` exactly when the generating ideal `baseIdeal A I f` is contained in it. By
the universal property of `Ideal.map` that only has to be checked on the image of `I`, where it
is the hypothesis read through the identification of the basic opens of `Spec A`. -/
theorem mem_support_baseIdealSheaf {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) {x : X} (hx : I ≤ (f.base x).asIdeal) :
    x ∈ (baseIdealSheaf A I f).support := by
  have hJ : ∀ g : Γ(X, ⊤),
      g ∈ Ideal.comap (X.presheaf.germ ⊤ x trivial).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ↔ x ∉ X.basicOpen g := by
    intro g
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      X.mem_basicOpen (U := ⊤) g x trivial]
  have hgen : baseIdeal A I f ≤ Ideal.comap (X.presheaf.germ ⊤ x trivial).hom
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) := by
    refine Ideal.map_le_iff_le_comap.2 fun c hc => ?_
    refine Ideal.mem_comap.2 ((hJ _).2 fun hmem => ?_)
    have hc' : ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom c =
        (ConcreteCategory.hom f.appTop)
          ((ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv) c) := rfl
    rw [hc', ← Scheme.preimage_basicOpen_top f
      ((ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv) c)] at hmem
    have hb : f.base x ∈ (Spec (CommRingCat.of A)).basicOpen
        ((ConcreteCategory.hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv) c) := hmem
    rw [basicOpen_eq_of_affine] at hb
    exact (PrimeSpectrum.mem_basicOpen c _).1 hb (hx hc)
  have hsupp : ((baseIdealSheaf A I f).support : Set X) =
      X.zeroLocus (U := ⊤) (baseIdeal A I f : Set Γ(X, ⊤)) :=
    Scheme.IdealSheafData.coe_support_ofIdealTop (baseIdeal A I f)
  exact hsupp.symm.subset ((X.mem_zeroLocus_iff _ x).2 fun g hg => (hJ g).1 (hgen hg))

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules)

/-- **Stacks 0EG2, the injectivity half.** The comparison map from the sections of a coherent
module `F` on `U = Spec(A) ∖ V(𝔞)` defined near the formal locus `U ∩ V(I)` to the compatible
families of sections of `F / Iⁿ F` on `U` is a monomorphism, provided the closure of every
associated point of `F` meets `U ∩ V(I)`.

This is the source's injectivity paragraph: a section killed by the comparison has vanishing
germ at every point of the formal locus, by Krull's intersection theorem in the form
`Stacks.Algebraization.germ_eq_zero_of_comparisonAt_apply_eq_zero`; germ vanishing transports
from a point to the points specializing to it, so the hypothesis makes the germs vanish at every
associated point of `F`; and a section whose germs vanish at every associated point is zero,
which is "a section `s ∈ F(V)` in the kernel would have to have empty support, hence would have
to be zero".

The hypothesis is the sentence "an associated point `x` of `F` must have
`closure {x} ∩ U ∩ Y ≠ ∅` by the previous paragraph", with `Y = V(I)`; the previous paragraph is
the depth-one reduction of Tag 0DX3, after which a point `x` of `U` with
`closure {x} ∩ V(I) ⊆ V(𝔞)` has `depth(F_x) ≥ 1` and is therefore not an associated point of
`F`. Here `x ⤳ y` with `I ≤ y.1.asIdeal` says exactly that `y` lies in `closure {x} ∩ U ∩ Y`. -/
theorem mono_comparisonMap_of_associatedPoints_specializes_vanishing [IsNoetherianRing A]
    [F.IsCoherent]
    (hAss : ∀ x : (complementZeroLocus A a : Scheme),
      x ∈ Stacks.Divisors.associatedPoints F →
      ∃ y : (complementZeroLocus A a : Scheme), x ⤳ y ∧ I ≤ y.1.asIdeal) :
    Mono (comparisonMap A I a F) := by
  have _ : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  refine mono_comparisonMap_of_forall_germ_eq_zero A I a F fun V s hg => ?_
  refine eq_zero_of_forall_germ_associatedPoints_eq_zero F V.openSet s fun x hx hxass => ?_
  obtain ⟨y, hxy, hyI⟩ := hAss x hxass
  have hysupp : y ∈ (idealSheafNearVanishing A I a).support :=
    mem_support_baseIdealSheaf I (complementZeroLocus A a).ι hyI
  exact germ_eq_zero_of_specializes F V.openSet
    (support_idealSheafNearVanishing_le A I a V hysupp) hx hxy s (hg y hysupp)

end Stacks.Algebraization

end
