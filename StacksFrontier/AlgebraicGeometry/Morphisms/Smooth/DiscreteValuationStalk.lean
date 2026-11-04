module

public import StacksFrontier.AlgebraicGeometry.SmoothAtClosedFibre.SeparableResidue
public import StacksFrontier.RingTheory.DiscreteValuationRing.FormallySmoothExtension
public import StacksFrontier.RingTheory.DiscreteValuationRing.RamificationCharacterization
public import StacksFrontier.RingTheory.FormallySmooth.AdicArrowIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness at a point whose stalk map is a formally smooth extension of discrete valuation rings

Let `f : X ⟶ S` be flat and locally of finite presentation and let `x` be a point of `X` at which
both local rings `𝒪_{S, f x}` and `𝒪_{X, x}` are discrete valuation rings. Flatness makes the
stalk map a faithfully flat local homomorphism, hence an extension of discrete valuation rings, so
formal smoothness of that map in the topology of the maximal ideal of `𝒪_{X, x}` is equivalent to
weak unramifiedness together with separability of the residue-field extension. Those two
conditions are exactly what makes `f` smooth at `x`: the first identifies the local ring of the
scheme-theoretic fibre through `x` with `κ(x)`, and the second makes `κ(f x) → κ(x)` formally
smooth.

## Main results

* `AlgebraicGeometry.smoothAt_of_formallySmoothNAdic_stalkMap`: a flat morphism locally of finite
  presentation is smooth at a point where the stalk map is an adically formally smooth extension
  of discrete valuation rings.

## Implementation notes

The algebra structure making the stalk map an extension is the one induced by the stalk map
itself, so the hypothesis is stated on `AlgebraicGeometry.Scheme.Hom.stalkMap` rather than on an
`algebraMap`. The residue-field extension appears as
`AlgebraicGeometry.Scheme.Hom.residueFieldMap`, which is `IsLocalRing.ResidueField.map` of the
stalk map, and separability is converted to formal smoothness of that map.

## References

* [Stacks Project, Tag 09E7](https://stacks.math.columbia.edu/tag/09E7)
* [Stacks Project, Tag 01V9](https://stacks.math.columbia.edu/tag/01V9)
* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
-/

public noncomputable section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry

/-- **A flat morphism locally of finite presentation is smooth at a point where the stalk map is
an adically formally smooth extension of discrete valuation rings.** If `𝒪_{S, f x}` and
`𝒪_{X, x}` are discrete valuation rings and the stalk map of `f` at `x` is formally smooth for
the topology of the maximal ideal of `𝒪_{X, x}`, then `f` is smooth at `x`.

By Tag 09E7 the hypothesis says that the extension is weakly unramified with separable
residue-field extension, which are the two conditions of Tag 01V9 read on the stalk map. -/
@[ega "IV 17.5.1" "c)⇒a)"]
theorem smoothAt_of_formallySmoothNAdic_stalkMap {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [Flat f] (x : X)
    [IsDomain (S.presheaf.stalk (f x))] [IsDiscreteValuationRing (S.presheaf.stalk (f x))]
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    (h : RingHom.FormallySmoothNAdic.{u} (f.stalkMap x).hom
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))) :
    InfinitesimalLifting.SmoothAt f x := by
  let : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have hlh : IsLocalHom (algebraMap (S.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    f.toLRSHom.prop x
  have hflat : Module.Flat (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := Flat.stalkMap f x
  have hff : Module.FaithfullyFlat (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hext : IsDiscreteValuationRing.IsExtension
      (S.presheaf.stalk (f x)) (X.presheaf.stalk x) := ⟨⟩
  obtain ⟨hweak, hsep⟩ :=
    (IsDiscreteValuationRing.formallySmooth_iff_weaklyUnramified_and_isSeparableExtension
      (S.presheaf.stalk (f x)) (X.presheaf.stalk x)).mp h
  refine Stacks.SmoothAtClosedFibre.smoothAt_of_flat_of_formallySmooth_residueFieldMap f x
    (Flat.stalkMap f x)
    ((IsDiscreteValuationRing.map_maximalIdeal_eq_iff_isWeaklyUnramified _ _).mpr hweak) ?_
  have hmap : algebraMap (IsLocalRing.ResidueField (S.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) = (f.residueFieldMap x).hom := by
    refine RingHom.ext fun y => ?_
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective y
    rfl
  have hfs : (algebraMap (IsLocalRing.ResidueField (S.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x))).FormallySmooth :=
    RingHom.formallySmooth_algebraMap.mpr
      ((Algebra.FormallySmooth.iff_isSeparableExtension _ _).mpr hsep)
  exact hmap ▸ hfs

/-- **Smoothness at a point from an adically formally smooth model of the stalk map.** If the
stalk map of `f` at `x` is isomorphic, as an arrow, to a map `φ : A →+* B` of local rings which is
formally smooth for the topology of the maximal ideal of `B`, then `f` is smooth at `x`.

This is the form in which the local criterion is applied: the local rings `A` and `B` are
localizations of rings of which the two stalks are only abstractly known to be localizations, so
the two vertical maps are isomorphisms of rings and not algebra maps over a common base. -/
@[ega "IV 17.5.1" "c)⇒a)"]
theorem smoothAt_of_formallySmoothNAdic_of_arrowEquiv {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [Flat f] (x : X)
    [IsDomain (S.presheaf.stalk (f x))] [IsDiscreteValuationRing (S.presheaf.stalk (f x))]
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) (eA : A ≃+* S.presheaf.stalk (f x)) (eB : B ≃+* X.presheaf.stalk x)
    (hcomm : (f.stalkMap x).hom.comp eA.toRingHom = eB.toRingHom.comp φ)
    (h : RingHom.FormallySmoothNAdic.{u, v, w} φ (IsLocalRing.maximalIdeal B)) :
    InfinitesimalLifting.SmoothAt f x :=
  smoothAt_of_formallySmoothNAdic_stalkMap f x
    (RingHom.FormallySmoothNAdic.of_arrowEquiv_of_map_eq eA eB hcomm
      (IsLocalRing.map_ringEquiv_maximalIdeal eB) h)

/-- **Smoothness at a point whose stalk map is a localization of an algebra, adically formally
smooth.** Let `p` be the contraction to `A` of a prime `q` of an `A`-algebra `B`, and suppose the
two stalks of `f` at `x` are identified with the two localizations `A_p` and `B_q` by ring
isomorphisms compatible with the structure maps of `A` and of `B`. If `A_p → B_q` is formally
smooth for the topology of the maximal ideal of `B_q`, then `f` is smooth at `x`.

The compatibility demanded of the two identifications is a single equation over elements of `A`:
a map out of a localization is determined by its restriction to the ring, so that equation
already forces the square against `Localization.localRingHom` to commute.

This is the criterion the reduced fibre theorem applies at a generic point of a fibre, where
`A` and `B` are the two integral closures of the base-change package of Tag 09EM and the formal
smoothness is the solution property of Tag 09EN(2).

This is the smoothness step of the proof of Tag 09IL, the last paragraph, for a solution that is
already available; the existence of the finite extension and the identification supplying `eA`,
`eB` and `hbase` are inputs. The full statement of that tag is
`AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback`. -/
theorem smoothAt_of_formallySmoothNAdic_localRingHom {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] [Flat f] (x : X)
    [IsDomain (S.presheaf.stalk (f x))] [IsDiscreteValuationRing (S.presheaf.stalk (f x))]
    [IsDomain (X.presheaf.stalk x)] [IsDiscreteValuationRing (X.presheaf.stalk x)]
    {A : Type v} {B : Type w} [CommRing A] [CommRing B] [Algebra A B]
    {p : Ideal A} [p.IsPrime] {q : Ideal B} [q.IsPrime] (hpq : p = q.comap (algebraMap A B))
    (eA : Localization.AtPrime p ≃+* S.presheaf.stalk (f x))
    (eB : Localization.AtPrime q ≃+* X.presheaf.stalk x)
    (hbase : ∀ a : A, (f.stalkMap x).hom (eA (algebraMap A (Localization.AtPrime p) a)) =
      eB (algebraMap B (Localization.AtPrime q) (algebraMap A B a)))
    (h : RingHom.FormallySmoothNAdic.{u, v, w}
      (Localization.localRingHom p q (algebraMap A B) hpq)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q))) :
    InfinitesimalLifting.SmoothAt f x := by
  refine smoothAt_of_formallySmoothNAdic_of_arrowEquiv f x _ eA eB ?_ h
  refine IsLocalization.ringHom_ext p.primeCompl (RingHom.ext fun a => ?_)
  simpa using (hbase a).trans (congrArg eB
    (Localization.localRingHom_to_map p q (algebraMap A B) hpq a).symm)

end AlgebraicGeometry

end
