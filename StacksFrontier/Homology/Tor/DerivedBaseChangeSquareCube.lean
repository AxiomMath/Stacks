module

public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquarePasting

/-!
# The derived base-change comparison across the cube of localizations

Let `(R, A, R', A')` be a commuting square of commutative rings, let `R → R₂` and `A → A₂` be
localizations, and stack below the first square a second one, `(R', A', R₃, A₃)`, so that the
outer rectangle is `(R, A, R₃, A₃)`. Suppose the two source corners of that rectangle localize
into a square `(R₂, A₂, R₃, A₃)`: ring maps `b₂ : R₂ → R₃`, `c₂ : A₂ → A₃` and `t : R₃ → A₃`
with `c₂ ∘ a₂ = t ∘ b₂`, compatible with the rectangle's edges in the sense that
`b₂ ∘ (R → R₂) = e ∘ b` and `c₂ ∘ (A → A₂) = v ∘ c`.

Then the Tag 065Z comparison of `(R₂, A₂, R₃, A₃)`, read on complexes already living over `A₂`,
is the comparison of the original square `(R, A, R', A')` extended along `R' → R₃` and followed
by the comparison of the bottom square `(R', A', R₃, A₃)`.

This is the two halves of the cube joined: `RingTheory.TorIndependence.squareComparison_localized`
moves the two source corners `R`, `A` to `R₂`, `A₂`, and
`RingTheory.TorIndependence.squareComparison_pasted` moves the two target corners `R'`, `A'` to
`R₃`, `A₃`. What this module adds is their composition, which is not a `rewrite` away: the mixed
square of the first law has edges `b₂ ∘ (R → R₂)` and `c₂ ∘ (A → A₂)` while the outer rectangle
of the second has edges `e ∘ b` and `v ∘ c`, and these are equal ring maps with different
spellings. A comparison's type mentions its edges through the functors it connects, so the two
cannot be interchanged by `rw`; the pasting law is therefore restated with the rectangle's edges
as *variables*, which `subst` specializes, and the equality of ring maps appears in the
conclusion as the transport
`RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr`.

## Main definitions

* `RingTheory.TorIndependence.totalDerivedExtensionScalarsCongr`: equal ring maps have equal
  derived extension-of-scalars functors.

## Main results

* `RingTheory.TorIndependence.squareComparison_pasted'`: the pasting law for a rectangle whose
  two edges are merely *equal* to the composites `e ∘ b` and `v ∘ c`.
* `RingTheory.TorIndependence.squareComparison_cube`: the two laws joined.

## Implementation notes

The model of the derived category is a binder `[HasDerivedCategory.{w} (ModuleCat.{u} ·)]` for
each of the rings, not `HasDerivedCategory.standard`: a statement proved at one model says
nothing about another, and the consumers of Tag 0DJ8 work at a locally small model.

## References

* [The Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [The Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Functor
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct ChangeOfRings

universe u w

namespace RingTheory.TorIndependence

section Congr

variable {R T : Type u} [CommRing R] [CommRing T]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} T)]

/-- **Equal ring maps have equal derived extension-of-scalars functors.** The chosen total
derived functor depends on the ring map alone, so an equality of ring maps transports it. -/
public def totalDerivedExtensionScalarsCongr {k l : R →+* T} (h : k = l) :
    (totalDerivedExtensionScalars.{u, u, u} k).functor ≅
      (totalDerivedExtensionScalars.{u, u, u} l).functor :=
  eqToIso (congrArg (fun m => (totalDerivedExtensionScalars.{u, u, u} m).functor) h)

/-- The transport along an equality of a ring map with itself is the identity. -/
@[simp]
public theorem totalDerivedExtensionScalarsCongr_rfl (k : R →+* T) :
    totalDerivedExtensionScalarsCongr.{u, w} (rfl : k = k) = Iso.refl _ := rfl

end Congr

section Pasted

variable {R A R' A' R₃ A₃ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A'] [CommRing R₃] [CommRing A₃]
  (a : R →+* A) (b : R →+* R') (c : A →+* A') (d : R' →+* A')
  (e : R' →+* R₃) (v : A' →+* A₃) (t : R₃ →+* A₃)
  (sq : c.comp a = d.comp b) (sqb : v.comp d = t.comp e)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
  [HasDerivedCategory.{w} (ModuleCat.{u} R₃)] [HasDerivedCategory.{w} (ModuleCat.{u} A₃)]

include sq sqb in
/-- **The pasting law for a rectangle whose edges are equal to the composites.** This is
`RingTheory.TorIndependence.squareComparison_pasted` for any two ring maps `B`, `C` equal to
`e ∘ b` and `v ∘ c` rather than for those composites themselves, the two equalities appearing in
the conclusion as transports of the derived extension-of-scalars functors.

The generalization is what lets the pasting law be composed with
`RingTheory.TorIndependence.squareComparison_localized`, whose mixed square has the *other*
spelling of the same two edges. -/
public theorem squareComparison_pasted' (B : R →+* R₃) (C : A →+* A₃)
    (hB : B = e.comp b) (hC : C = v.comp c) (sqBC : C.comp a = t.comp B) :
    squareComparison.{u, w} a B C t sqBC =
      Functor.whiskerLeft ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory)
          (totalDerivedExtensionScalarsCongr.{u, w} hB).hom ≫
        pastedComparison.{u, w} a b c d e v t sq sqb ≫
          Functor.whiskerRight (totalDerivedExtensionScalarsCongr.{u, w} hC).inv
            ((ModuleCat.restrictScalars.{u} t).mapDerivedCategory) := by
  subst hB
  subst hC
  refine Eq.trans (squareComparison_pasted.{u, w} a b c d e v t sq sqb) ?_
  simp only [totalDerivedExtensionScalarsCongr_rfl, Iso.refl_hom, Iso.refl_inv,
    Functor.whiskerLeft_id', Functor.whiskerRight_id', Category.id_comp, Category.comp_id]

end Pasted

section Joined

variable {R A R' A' R₂ A₂ R₃ A₃ : Type u}
  [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
  [CommRing R₂] [CommRing A₂] [CommRing R₃] [CommRing A₃]
  [Algebra R R₂] [Algebra A A₂]
  (SR : Submonoid R) [IsLocalization SR R₂]
  (SA : Submonoid A) [IsLocalization SA A₂]
  (a : R →+* A) (b : R →+* R') (c : A →+* A') (d : R' →+* A')
  (e : R' →+* R₃) (v : A' →+* A₃)
  (a₂ : R₂ →+* A₂) (b₂ : R₂ →+* R₃) (c₂ : A₂ →+* A₃) (t : R₃ →+* A₃)
  (sq : c.comp a = d.comp b) (sqb : v.comp d = t.comp e)
  (hloc : (algebraMap A A₂).comp a = a₂.comp (algebraMap R R₂))
  (hsq : c₂.comp a₂ = t.comp b₂)
  (hB : b₂.comp (algebraMap R R₂) = e.comp b)
  (hC : c₂.comp (algebraMap A A₂) = v.comp c)
  [HasDerivedCategory.{w} (ModuleCat.{u} R)] [HasDerivedCategory.{w} (ModuleCat.{u} A)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R')] [HasDerivedCategory.{w} (ModuleCat.{u} A')]
  [HasDerivedCategory.{w} (ModuleCat.{u} R₂)] [HasDerivedCategory.{w} (ModuleCat.{u} A₂)]
  [HasDerivedCategory.{w} (ModuleCat.{u} R₃)] [HasDerivedCategory.{w} (ModuleCat.{u} A₃)]

include sq sqb hloc hsq hB hC in
/-- **The Tag 065Z comparison across the whole cube of localizations.** The comparison of the
localized square `(R₂, A₂, R₃, A₃)`, read on complexes already over `A₂`, is the comparison of
the square `(R, A, R', A')` extended along `R' → R₃` and followed by the comparison of the
bottom square `(R', A', R₃, A₃)`, under the two source identifications of
`RingTheory.TorIndependence.localizedSquareDomainIso` and
`RingTheory.TorIndependence.localizedSquareCodomainIso`.

Taking `(R₂, A₂, R₃, A₃)` to be the four local rings at a point of a chart's open `U'` and
`(R, A, R', A')` to be the chart's four coordinate rings, this is the naturality of the Tag 065Z
comparison along the cube of localizations that the affine reduction of Tag 0DJ8 consumes. -/
public theorem squareComparison_cube :
    (localizedSquareDomainIso.{u, w} SR a a₂ b₂ hloc).hom ≫
        squareComparison.{u, w} a₂ b₂ c₂ t hsq =
      Functor.whiskerLeft ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory)
          (Functor.whiskerLeft ((ModuleCat.restrictScalars.{u} a).mapDerivedCategory)
              (totalDerivedExtensionScalarsCongr.{u, w} hB).hom ≫
            pastedComparison.{u, w} a b c d e v t sq sqb ≫
              Functor.whiskerRight (totalDerivedExtensionScalarsCongr.{u, w} hC).inv
                ((ModuleCat.restrictScalars.{u} t).mapDerivedCategory)) ≫
        (localizedSquareCodomainIso.{u, w} SA c₂ t).hom := by
  refine Eq.trans (squareComparison_localized.{u, w} SR SA a a₂ b₂ c₂ t hloc hsq) ?_
  exact congrArg (fun z => Functor.whiskerLeft
      ((ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory) z ≫
      (localizedSquareCodomainIso.{u, w} SA c₂ t).hom)
    (squareComparison_pasted'.{u, w} a b c d e v t sq sqb _ _ hB hC
      (localizedSquare_comm a a₂ b₂ c₂ t hloc hsq))

end Joined

end RingTheory.TorIndependence

end
