module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ProperPartOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ConnectedFibres
public import StacksFrontier.RingTheory.Henselian.Pair.Operations
public import StacksFrontier.Topology.Sheaves.Spectral.ClosedSubsetGlobalSections

/-!
# Global sections of a sheaf on a proper scheme over a henselian pair are read off the closed fibre

Let `(A, I)` be a henselian pair and let `f : X ⟶ Spec A` be proper.  Restriction of any sheaf of
sets on the topological space of `X` to the closed fibre `Z = X ×_{Spec A} Spec (A ⧸ I)` is
bijective on global sections, granted geometric connectedness of the Stein first factor of every
proper morphism to `Spec A`.

The space of `X` is spectral, so by
`Stacks.bijective_globalSectionsRestriction_of_isConnected_inter_closure` the assertion reduces to
a purely topological one: the closed fibre meets the closure of every point of `X` in a connected
set.  For a single point `x` that intersection is the closed fibre of the integral closed
subscheme `closure {x}`, which is again proper over `Spec A`, so only the case of an irreducible
`X` has to be treated.  There the Stein factorization `X ⟶ f.normalization ⟶ Spec A` writes
`f.normalization` as the spectrum of an `A`-algebra `B` integral over `A`;  then `(B, IB)` is a
henselian pair and `f.normalization` is irreducible, so `V(IB)` is connected because it is the
vanishing locus of the sum of `IB` with a prime;  and the first factor carries that connectedness
up to `X`, being a surjective closed map with connected fibres.

## Main results

* `AlgebraicGeometry.isConnected_closedFibre_inter_closure_of_henselianPair`: the closed fibre of
  a proper morphism to the spectrum of a henselian pair meets the closure of every point in a
  connected set, granted the connectedness hypothesis `hconn`.
* `AlgebraicGeometry.bijective_globalSectionsRestriction_closedFibre_of_henselianPair`:
  restriction to the closed fibre is bijective on global sections of every sheaf of sets on the
  space of `X`, granted `hconn`.
* `AlgebraicGeometry.bijective_globalSectionsRestriction_closedFibre_of_henselianPair_of_isProper`:
  the same conclusion with no further hypothesis.

## Implementation notes

The closed fibre is presented as the subset `Set.range (pullback.fst f (Spec (A ⧸ I) ⟶ Spec A))`
of the space of `X`, which `AlgebraicGeometry.Scheme.Pullback.range_fst` identifies with
`f ⁻¹' V(I)`;  the first projection is a closed immersion, so this subset carries the topology of
the fibre product.  Restriction of a sheaf to it is the inverse image along the inclusion, and the
equality of section sets asserted by the source is stated as bijectivity of the canonical
restriction map `Stacks.globalSectionsRestriction`.

**The `@[stacks 0A0B]` attribute is attached to the third result only.**  The first two results
carry a hypothesis `hconn` that the tag does not have:  that `g.toNormalization` is
geometrically connected for *every* proper `g : Y ⟶ Spec A`.  This is the connectedness conjunct
of clause (1) of [Stacks, Tag 03H2], Zariski's connectedness theorem for the Stein factorization,
quantified over all proper morphisms to `Spec A`.  The quantifier is forced, because the reduction
to an irreducible source applies it to the closed subscheme `closure {x}` for every `x : X` and not
to `f` alone.  The third result discharges `hconn` by
`Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper`.

Coefficients are sheaves of sets in the universe of the space, which is the generality of
`Stacks.bijective_globalSectionsRestriction_of_isConnected_inter_closure`.

## References

* [Stacks Project, Tag 0A0B](https://stacks.math.columbia.edu/tag/0A0B)
* [Stacks Project, Tag 09ZG](https://stacks.math.columbia.edu/tag/09ZG)
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X)
* [Stacks Project, Tag 02OD](https://stacks.math.columbia.edu/tag/02OD)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 09XK](https://stacks.math.columbia.edu/tag/09XK)
* [Stacks Project, Tag 09Y6](https://stacks.math.columbia.edu/tag/09Y6)
* [Stacks Project, Tag 094L](https://stacks.math.columbia.edu/tag/094L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.SteinFactorization

universe u

namespace AlgebraicGeometry

/-- A surjective closed map is coinducing. -/
private theorem isCoinducing_of_isClosedMap {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {g : α → β} (hg : Continuous g) (hsurj : Function.Surjective g)
    (hclosed : IsClosedMap g) : Topology.IsCoinducing g := by
  refine Topology.isCoinducing_iff_isClosed.mpr fun s => ⟨fun hs => ?_, fun hs => hs.preimage hg⟩
  rw [← Set.image_preimage_eq_of_subset (fun y _ => hsurj y) (s := s)]
  exact hclosed _ hs

/-- If the preimage of `S` under `i ≫ f` is connected, then `f ⁻¹' S` meets the range of `i` in a
connected set. -/
private theorem isConnected_preimage_inter_range {X Y Z : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ Z)
    (S : Set Z) (h : _root_.IsConnected ((i ≫ f) ⁻¹' S)) :
    _root_.IsConnected (f ⁻¹' S ∩ Set.range i) := by
  have := h.image i i.continuous.continuousOn
  rwa [show (i ≫ f) ⁻¹' S = i.base ⁻¹' (f.base ⁻¹' S) from rfl,
    Set.image_preimage_eq_inter_range] at this

/-- For `(A, I)` a henselian pair and `f : X ⟶ Spec A` proper with `X` irreducible and
`f.toNormalization` geometrically connected, the closed fibre `f ⁻¹' V(I)` is connected. -/
private theorem isConnected_preimage_zeroLocus_of_irreducibleSpace (A : Type u) [CommRing A]
    (I : Ideal A) (hI : HenselianPair A I) {X : Scheme.{u}} [IrreducibleSpace X]
    (f : X ⟶ Spec (.of A)) [IsProper f] [GeometricallyConnected f.toNormalization] :
    _root_.IsConnected (f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) := by
  have : IsAffine f.normalization := isAffine_of_isAffineHom f.fromNormalization
  let B := Γ(f.normalization, ⊤)
  let φ : CommRingCat.of A ⟶ B :=
    Spec.preimage (f.normalization.isoSpec.inv ≫ f.fromNormalization)
  have hφ : Spec.map φ = f.normalization.isoSpec.inv ≫ f.fromNormalization :=
    Spec.map_preimage _
  let _ : Algebra A B := φ.hom.toAlgebra
  have hint : IsIntegralHom (Spec.map φ) := hφ ▸ inferInstance
  have : Algebra.IsIntegral A B := ⟨IsIntegralHom.SpecMap_iff.mp hint⟩
  have halg : (algebraMap A B) = φ.hom := rfl
  -- `(B, IB)` is a henselian pair, by Stacks 09XK.
  have hJ : HenselianPair B (I.map (algebraMap A B)) := henselianPair_map_of_isIntegral I hI
  -- `f.normalization` is irreducible, being the image of an irreducible space.
  have hsurj : Function.Surjective f.toNormalization.base := f.toNormalization.surjective
  have : IrreducibleSpace f.normalization := by
    rw [irreducibleSpace_def]
    have hX : IsIrreducible (Set.univ : Set X) := IrreducibleSpace.isIrreducible_univ X
    have h := hX.image f.toNormalization.base
      f.toNormalization.continuous.continuousOn
    rwa [Set.image_univ, Set.range_eq_univ.mpr hsurj] at h
  have hirr : IrreducibleSpace (PrimeSpectrum B) :=
    f.normalization.isoSpec.hom.homeomorph.irreducibleSpace_iff.mp inferInstance
  have hp : (nilradical B).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hirr
  -- `V(IB)` is connected, by Stacks 09Y6.
  have hspec : _root_.IsConnected
      (PrimeSpectrum.zeroLocus ((I.map (algebraMap A B) : Ideal B) : Set B)) := by
    have h := isConnected_zeroLocus_add (I.map (algebraMap A B)) (nilradical B) hJ hp
    rwa [show (nilradical B + I.map (algebraMap A B) : Ideal B)
        = nilradical B ⊔ I.map (algebraMap A B) from Ideal.add_eq_sup,
      PrimeSpectrum.zeroLocus_sup, PrimeSpectrum.zeroLocus_nilradical, Set.univ_inter] at h
  -- Transport it to `f.normalization` along the second factor.
  have hpre : (f.normalization.isoSpec.inv ≫ f.fromNormalization) ⁻¹'
        PrimeSpectrum.zeroLocus (I : Set A)
      = PrimeSpectrum.zeroLocus ((I.map (algebraMap A B) : Ideal B) : Set B) := by
    rw [← hφ]
    change PrimeSpectrum.comap φ.hom ⁻¹' _ = _
    rw [PrimeSpectrum.preimage_comap_zeroLocus, halg, Ideal.map,
      PrimeSpectrum.zeroLocus_span]
  have hbase : _root_.IsConnected
      (f.fromNormalization ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) := by
    have h := isConnected_preimage_inter_range f.normalization.isoSpec.inv f.fromNormalization
      (PrimeSpectrum.zeroLocus (I : Set A)) (hpre ▸ hspec)
    rwa [Set.range_eq_univ.mpr f.normalization.isoSpec.inv.surjective, Set.inter_univ] at h
  have hclosed : IsClosed (f.fromNormalization ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) :=
    (PrimeSpectrum.isClosed_zeroLocus _).preimage f.fromNormalization.continuous
  -- Carry it up along the first factor, which is surjective, closed and has connected fibres.
  have hco : Topology.IsCoinducing f.toNormalization.base :=
    isCoinducing_of_isClosedMap f.toNormalization.continuous hsurj
      f.toNormalization.isClosedMap
  have h := Topology.IsCoinducing.isConnected_preimage_of_isClosed
    f.toNormalization.isConnected_preimage_singleton hco hclosed hbase
  have hcomp : f.toNormalization.base ⁻¹'
        (f.fromNormalization.base ⁻¹' PrimeSpectrum.zeroLocus (I : Set A))
      = f.base ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
    rw [show f.toNormalization.base ⁻¹'
          (f.fromNormalization.base ⁻¹' PrimeSpectrum.zeroLocus (I : Set A))
        = (f.toNormalization ≫ f.fromNormalization).base ⁻¹'
          PrimeSpectrum.zeroLocus (I : Set A) from rfl,
      toNormalization_fromNormalization f]
  rwa [hcomp] at h

/-- For `(A, I)` a henselian pair and `f : X ⟶ Spec A` proper, the closed fibre `f ⁻¹' V(I)` meets
the closure of every point of `X` in a connected set, granted geometric connectedness of the Stein
first factor of every proper morphism to `Spec A`. -/
theorem isConnected_closedFibre_inter_closure_of_henselianPair (A : Type u) [CommRing A]
    (I : Ideal A) (hI : HenselianPair A I) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (hconn : ∀ {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A)) [IsProper g],
      GeometricallyConnected g.toNormalization) (x : X) :
    _root_.IsConnected (f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ∩ closure ({x} : Set X)) := by
  let T : Closeds X := ⟨closure ({x} : Set X), isClosed_closure⟩
  let D := Scheme.IdealSheafData.vanishingIdeal T
  let i : D.subscheme ⟶ X := D.subschemeι
  have hrange : Set.range i = closure ({x} : Set X) := by
    rw [D.range_subschemeι]
    simp [D, T]
  have himage : i '' (Set.univ : Set D.subscheme) = closure ({x} : Set X) := by
    rw [Set.image_univ, hrange]
  have hImageIrr : IrreducibleSpace ↥(i '' (Set.univ : Set D.subscheme)) := by
    rw [himage]
    exact Subtype.irreducibleSpace <|
      (isIrreducible_singleton : IsIrreducible ({x} : Set X)).closure
  have hUnivIrr : IrreducibleSpace ↥(Set.univ : Set D.subscheme) :=
    (i.isClosedEmbedding.isEmbedding.homeomorphImage
      (Set.univ : Set D.subscheme)).irreducibleSpace_iff.mpr hImageIrr
  have : IrreducibleSpace D.subscheme :=
    (Homeomorph.Set.univ D.subscheme).irreducibleSpace_iff.mp hUnivIrr
  have : IsProper (i ≫ f) := inferInstance
  have := hconn (i ≫ f)
  have hY := isConnected_preimage_zeroLocus_of_irreducibleSpace A I hI (i ≫ f)
  have hfib := isConnected_preimage_inter_range i f (PrimeSpectrum.zeroLocus (I : Set A)) hY
  rwa [hrange] at hfib

/-- For `(A, I)` a henselian pair and `f : X ⟶ Spec A` proper, restriction to the closed fibre
`X ×_{Spec A} Spec (A ⧸ I)` is bijective on global sections of every sheaf of sets on the space of
`X`, granted geometric connectedness of the Stein first factor of every proper morphism to
`Spec A`. -/
theorem bijective_globalSectionsRestriction_closedFibre_of_henselianPair (A : Type u) [CommRing A]
    (I : Ideal A) (hI : HenselianPair A I) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [IsProper f]
    (hconn : ∀ {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A)) [IsProper g],
      GeometricallyConnected g.toNormalization)
    (F : TopCat.Sheaf (Type u) (TopCat.of X)) :
    Function.Bijective (Stacks.globalSectionsRestriction
      (Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) F) := by
  have hZ : Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))
      = f ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) := by
    rw [Scheme.Pullback.range_fst, range_spec_map_quotient_mk I]
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
  have : SpectralSpace X := by constructor
  rw [hZ]
  refine Stacks.bijective_globalSectionsRestriction_of_isConnected_inter_closure _
    ((PrimeSpectrum.isClosed_zeroLocus _).preimage f.continuous) (fun x => ?_) F
  exact isConnected_closedFibre_inter_closure_of_henselianPair A I hI f hconn x

/-- For `(A, I)` a henselian pair and `f : X ⟶ Spec A` proper, restriction to the closed fibre
`X ×_{Spec A} Spec (A ⧸ I)` is bijective on global sections of every sheaf of sets on the space
of `X`. -/
@[stacks 0A0B]
theorem bijective_globalSectionsRestriction_closedFibre_of_henselianPair_of_isProper
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [IsProper f]
    (F : TopCat.Sheaf (Type u) (TopCat.of X)) :
    Function.Bijective (Stacks.globalSectionsRestriction
      (Set.range (pullback.fst f (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) F) := by
  have hconn : ∀ {Y : Scheme.{u}} (g : Y ⟶ Spec (.of A)) [IsProper g],
      GeometricallyConnected g.toNormalization := by
    intro Y g _
    exact Stacks.SteinFactorization.geometricallyConnected_toNormalization_of_isProper g
  exact bijective_globalSectionsRestriction_closedFibre_of_henselianPair A I hI f hconn F

end AlgebraicGeometry
