module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedAbove
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Restriction
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafDegreeZero

/-!
# Approximating a complex bounded above by a module placed in its top degree

Let `X` be a ringed space, let `𝒦` be a complex of `𝒪_X`-modules whose cohomology vanishes above a
degree `p`, and suppose that, locally on `X`, there is a direct summand `𝒜` of a finite free module
together with a map `𝒜 ⟶ Z^p(𝒦)` whose composite with `Z^p(𝒦) ⟶ H^p(𝒦)` is an epimorphism. Then
`𝒦` is `p`-pseudo-coherent, the approximating strictly perfect complex being `𝒜` placed in degree
`p`.

This is the approximation that the converse half of Stacks 09VA produces at the top nonvanishing
cohomological degree: there the source `𝒜` is a finite free module, obtained from
`AlgebraicGeometry.RingedSpace.isFiniteType_homology_of_isPseudoCoherentFrom_derivedPushforward`,
and the map to the cycles is the local lift of the resulting epimorphism onto `H^p(𝒦)`.

Two things have to be checked about the morphism `𝒜[-p] ⟶ 𝒦` determined by a map `𝒜 ⟶ Z^p(𝒦)`:
that it is an isomorphism on cohomology above `p`, which holds because both sides vanish there,
and that it is an epimorphism on cohomology in degree `p`. The second is the only content. It
follows from the naturality square of `homologyπ`: the composite
`Z^p(𝒜[-p]) ⟶ Z^p(𝒦) ⟶ H^p(𝒦)` is an epimorphism because it is a factor of the given one, and
`H^p(𝒜[-p]) ⟶ H^p(𝒦)` receives it from `Z^p(𝒜[-p]) ⟶ H^p(𝒜[-p])`.

## Main definitions

* `CochainComplex.homFromSingleOfCycles`: the morphism `𝒜[-p] ⟶ 𝒦` determined by a map
  `𝒜 ⟶ Z^p(𝒦)`.

## Main results

* `CategoryTheory.epi_homologyMap_of_epi_cyclesMap_comp_homologyπ`: a morphism of complexes is an
  epimorphism on degree-`p` homology as soon as the composite of its map on degree-`p` cycles with
  the projection to degree-`p` homology is one. No hypothesis on either complex.
* `CochainComplex.epi_homologyMap_homFromSingleOfCycles`:
  `CochainComplex.homFromSingleOfCycles` is an epimorphism on degree-`p` homology when the given
  map to the cycles is, after composing with the projection to the homology.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_local_epi_homologyπ` and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_of_local_epi_homologyπ`: the resulting
  criterion for `p`-pseudo-coherence, for a complex and for the object of the derived category it
  represents.

## Implementation notes

`CategoryTheory.epi_homologyMap_of_epi_cyclesMap_comp_homologyπ` is stated for an arbitrary
homological complex in an arbitrary abelian category, since nothing else is used: it is
`HomologicalComplex.homologyπ_naturality` together with the fact that the second factor of an
epimorphic composite is an epimorphism.

The factorisation `𝒜 ⟶ Z^p(𝒜[-p]) ⟶ Z^p(𝒦)` of the given map is checked after composing with the
monomorphism `Z^p(𝒦) ⟶ 𝒦^p`, where both sides reduce to the given map by
`HomologicalComplex.cyclesMap_i`, `HomologicalComplex.liftCycles_i` and
`CochainComplex.homFromSingleOfCycles_f`.

## References

* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Definition 20.46.4 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe v u d

namespace CategoryTheory

/-- **A morphism of complexes which is an epimorphism from the degree-`p` cycles onto the
degree-`p` homology is an epimorphism on degree-`p` homology.** The naturality square of
`HomologicalComplex.homologyπ` exhibits the given composite as
`Z^p(K) ⟶ H^p(K) ⟶ H^p(L)`, and the second factor of an epimorphic composite is an
epimorphism. -/
public theorem epi_homologyMap_of_epi_cyclesMap_comp_homologyπ {C : Type u} [Category.{v} C]
    [Abelian C] {ι : Type*} {c : ComplexShape ι} {K L : HomologicalComplex C c} (f : K ⟶ L)
    (p : ι) (h : Epi (HomologicalComplex.cyclesMap f p ≫ L.homologyπ p)) :
    Epi (HomologicalComplex.homologyMap f p) := by
  have h2 : K.homologyπ p ≫ HomologicalComplex.homologyMap f p =
      HomologicalComplex.cyclesMap f p ≫ L.homologyπ p :=
    HomologicalComplex.homologyπ_naturality f p
  rw [← h2] at h
  have := h
  exact epi_of_epi (K.homologyπ p) _

end CategoryTheory

namespace CochainComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasZeroObject C]

/-- **The morphism `𝒜[-p] ⟶ 𝒦` determined by a map `𝒜 ⟶ Z^p(𝒦)`.** Its only nonzero component is
in degree `p`, where it is the given map followed by the inclusion of the cycles; that composite is
killed by the differential, which is what `HomologicalComplex.mkHomFromSingle` requires. -/
public def homFromSingleOfCycles (L : CochainComplex C ℤ) (p : ℤ) {A : C} (c : A ⟶ L.cycles p) :
    (HomologicalComplex.single C (ComplexShape.up ℤ) p).obj A ⟶ L :=
  HomologicalComplex.mkHomFromSingle (c ≫ L.iCycles p) (fun k hk => by
    simp only [ComplexShape.up_Rel] at hk
    subst hk
    rw [Category.assoc, L.iCycles_d, comp_zero])

/-- The degree-`p` component of `CochainComplex.homFromSingleOfCycles`. -/
public theorem homFromSingleOfCycles_f (L : CochainComplex C ℤ) (p : ℤ) {A : C}
    (c : A ⟶ L.cycles p) :
    (homFromSingleOfCycles L p c).f p =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p A).hom ≫ c ≫ L.iCycles p :=
  HomologicalComplex.mkHomFromSingle_f _ _

/-- **`𝒜[-p] ⟶ 𝒦` is an epimorphism on degree-`p` cohomology** when the given map `𝒜 ⟶ Z^p(𝒦)`
becomes one after composing with `Z^p(𝒦) ⟶ H^p(𝒦)`.

The differential of `𝒜[-p]` vanishes, so `𝒜` maps to `Z^p(𝒜[-p])` compatibly with the given map to
`Z^p(𝒦)`; hence `Z^p(𝒜[-p]) ⟶ Z^p(𝒦) ⟶ H^p(𝒦)` is an epimorphism, and
`CategoryTheory.epi_homologyMap_of_epi_cyclesMap_comp_homologyπ` applies. -/
public theorem epi_homologyMap_homFromSingleOfCycles (L : CochainComplex C ℤ) (p : ℤ) {A : C}
    (c : A ⟶ L.cycles p) (hc : Epi (c ≫ L.homologyπ p)) :
    Epi (HomologicalComplex.homologyMap (homFromSingleOfCycles L p c) p) := by
  set S := (HomologicalComplex.single C (ComplexShape.up ℤ) p).obj A with hS
  set f := homFromSingleOfCycles L p c with hf
  have hd : S.d p (p + 1) = 0 := rfl
  set iA := S.liftCycles ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) p A).inv)
    (p + 1) (by simp) (by rw [hd, comp_zero]) with hiA
  have hkey : iA ≫ HomologicalComplex.cyclesMap f p = c := by
    rw [← cancel_mono (L.iCycles p), Category.assoc, HomologicalComplex.cyclesMap_i,
      ← Category.assoc, hiA, HomologicalComplex.liftCycles_i, hf, homFromSingleOfCycles_f,
      ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  refine CategoryTheory.epi_homologyMap_of_epi_cyclesMap_comp_homologyπ f p ?_
  have h2 : Epi (iA ≫ HomologicalComplex.cyclesMap f p ≫ L.homologyπ p) := by
    rw [← Category.assoc, hkey]
    exact hc
  have := h2
  exact epi_of_epi iA _

end CochainComplex

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}}

/-- **A complex with no cohomology above `p` which locally admits a map to its degree-`p` cycles
from a direct summand of a finite free module, epimorphic onto the degree-`p` cohomology, is
`p`-pseudo-coherent.**

The approximating strictly perfect complex is the given module placed in degree `p`
(`StrictlyPerfect.isStrictlyPerfect_single`) and the approximating morphism is
`CochainComplex.homFromSingleOfCycles`. Above degree `p` both complexes have vanishing cohomology
— the one because it is concentrated in degree `p`, the other by hypothesis and because
restriction to an open subspace is exact — so the map on cohomology there is a map between zero
objects; in degree `p` it is an epimorphism by
`CochainComplex.epi_homologyMap_homFromSingleOfCycles`. -/
public theorem isPseudoCoherentComplexFrom_of_local_epi_homologyπ
    (L : CochainComplex (OXMod.{u, u} X) ℤ) (p : ℤ)
    (hvanish : ∀ j : ℤ, p < j → IsZero (L.homology j))
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ A : OXMod.{u, u} (X.restrict U.isOpenEmbedding), IsDirectSummandOfFiniteFree A ∧
        ∃ c : A ⟶ (restrictComplex L U).cycles p,
          Epi (c ≫ (restrictComplex L U).homologyπ p)) :
    IsPseudoCoherentComplexFrom L p := by
  intro x
  obtain ⟨U, hxU, A, hA, c, hc⟩ := h x
  refine ⟨U, hxU, (HomologicalComplex.single _ (ComplexShape.up ℤ) p).obj A,
    isStrictlyPerfect_single hA p,
    CochainComplex.homFromSingleOfCycles (restrictComplex L U) p c, fun j hj => ?_, ?_⟩
  · refine (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) p A j
      (by lia)).isIso ?_ _
    exact isZero_restrictComplex_homology L U j (hvanish j hj)
  · exact CochainComplex.epi_homologyMap_homFromSingleOfCycles _ p c hc

/-- The object of the derived category represented by a complex as in
`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_local_epi_homologyπ` is
`p`-pseudo-coherent. -/
public theorem isPseudoCoherentFrom_Q_of_local_epi_homologyπ
    [HasDerivedCategory.{d} (OXMod.{u, u} X)] (L : CochainComplex (OXMod.{u, u} X) ℤ) (p : ℤ)
    (hvanish : ∀ j : ℤ, p < j → IsZero (L.homology j))
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ A : OXMod.{u, u} (X.restrict U.isOpenEmbedding), IsDirectSummandOfFiniteFree A ∧
        ∃ c : A ⟶ (restrictComplex L U).cycles p,
          Epi (c ≫ (restrictComplex L U).homologyπ p)) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj L) p :=
  IsPseudoCoherentComplexFrom.isPseudoCoherentFrom_Q
    (isPseudoCoherentComplexFrom_of_local_epi_homologyπ L p hvanish h)

end AlgebraicGeometry.RingedSpace

end
