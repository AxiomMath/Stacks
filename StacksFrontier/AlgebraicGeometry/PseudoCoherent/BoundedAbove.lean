module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedRestrict
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ImmersionIndependence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardOXMod
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TrivialRange

/-!
# Pseudo-coherence from vanishing cohomology, and local boundedness above

An object of the derived category of `𝒪_X`-modules whose cohomology vanishes in every degree at
least `m` is `m`-pseudo-coherent, and an `m`-pseudo-coherent object has, locally, no cohomology
in high degrees. For a morphism of ringed spaces `i : Z ⟶ X` the second statement holds on
neighbourhoods of the form `i⁻¹U` with `U` open in `X`, and for a closed embedding `i` the first
one passes to `Ri_*E`.

## Main results

* `AlgebraicGeometry.RingedSpace.exists_opens_preimage_eq`: an open of a subspace of a ringed
  space is the preimage of an open of the ambient space.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_isZero_homology_ge` and
  `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_isZero_homology_ge`: vanishing of the
  cohomology in all degrees at least `m` implies `m`-pseudo-coherence, for a complex and for an
  object of the derived category.
* `AlgebraicGeometry.RingedSpace.exists_isZero_homology_gt_derivedRestrict`: an
  `m`-pseudo-coherent object of `D(𝒪_X)` is bounded above on a neighbourhood of every point.
* `AlgebraicGeometry.RingedSpace.exists_opens_isZero_homology_gt_derivedRestrict_preimage`: the
  same on neighbourhoods `i⁻¹U`, for a morphism of ringed spaces whose underlying map is inducing.
* `AlgebraicGeometry.RingedSpace.isZero_homology_derivedPushforward`: `H^j(Ri_*E) = i_*H^j(E)`
  vanishes wherever `H^j(E)` does, `i_*` being exact at a closed embedding.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedPushforward_of_isZero_homology_ge`:
  for a closed embedding `i`, if `E` has no cohomology in degrees at least `m` then `Ri_*E` is
  `m`-pseudo-coherent.

## References

* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Definition 20.46.4 (Tag 08CB)](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Lemma 20.47.4 (Tag 08DN)](https://stacks.math.columbia.edu/tag/08DN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open scoped ZeroObject

universe d d' u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}}

/-! ### The opens of a subspace -/

/-- **The opens of a subspace are cut out by the opens of the ambient space.** If the underlying
continuous map of a morphism of ringed spaces `i : Z ⟶ X` is inducing, then every open `V` of `Z`
is the preimage of an open of `X`. -/
public theorem exists_opens_preimage_eq {Z : RingedSpace.{u, u}} (i : Z ⟶ X)
    (hi : Topology.IsInducing i.hom.base) (V : Opens Z.carrier) :
    ∃ U : Opens X.carrier, (Opens.map i.hom.base).obj U = V := by
  obtain ⟨t, ht, hts⟩ := hi.isOpen_iff.mp V.isOpen
  exact ⟨⟨t, ht⟩, Opens.ext hts⟩

/-! ### The base case: no cohomology above `m` -/

/-- Restriction to an open subspace kills the cohomology in a degree where the cohomology of the
complex already vanishes. -/
public theorem isZero_restrictComplex_homology (E : CochainComplex (OXMod.{u, u} X) ℤ)
    (U : Opens X.carrier) (j : ℤ) (h : IsZero (E.homology j)) :
    IsZero ((restrictComplex E U).homology j) :=
  IsZero.of_iso ((restrictModules X U).map_isZero h) (restrictComplexHomologyIso E U j)

/-- A complex of `𝒪_X`-modules whose cohomology vanishes in every degree at least `m` is
`m`-pseudo-coherent. -/
public theorem isPseudoCoherentComplexFrom_of_isZero_homology_ge
    (E : CochainComplex (OXMod.{u, u} X) ℤ) (m : ℤ)
    (h : ∀ j : ℤ, m ≤ j → IsZero (E.homology j)) : IsPseudoCoherentComplexFrom E m := by
  intro _
  have hzero : ∀ j : ℤ, IsZero (((0 : CochainComplex
      (OXMod.{u, u} (X.restrict (⊤ : Opens X.carrier).isOpenEmbedding)) ℤ)).X j) :=
    fun j => (HomologicalComplex.eval _ (ComplexShape.up ℤ) j).map_isZero (isZero_zero _)
  have key : ∀ j : ℤ, m ≤ j → IsZero ((restrictComplex E (⊤ : Opens X.carrier)).homology j) :=
    fun j hj => isZero_restrictComplex_homology E ⊤ j (h j hj)
  refine ⟨⊤, trivial, 0, StrictlyPerfect.isStrictlyPerfect_zero, 0, fun j hj => ?_, ?_⟩
  · exact (HomologicalComplex.isZero_homology_of_isZero_X _ _ (hzero j)).isIso (key j hj.le) _
  · exact (key m le_rfl).epi _

/-! ### `i_*` and vanishing cohomology -/

section PushforwardComplex

variable {Z : RingedSpace.{u, u}} (i : Z ⟶ X)

/-- For a closed embedding `i`, the pushforward `i_*` of a complex of `𝒪_Z`-modules has
vanishing cohomology in every degree where the cohomology of the complex vanishes. -/
public theorem isZero_homology_pushforwardComplex
    (hi : Topology.IsClosedEmbedding i.hom.base) (K : CochainComplex (OXMod.{u, u} Z) ℤ) (j : ℤ)
    (h : IsZero (K.homology j)) :
    IsZero ((((pushforwardOXMod i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K).homology j) :=
  have := preservesFiniteColimits_pushforwardOXMod i hi
  IsZero.of_iso ((pushforwardOXMod i).map_isZero h) ((K.sc j).mapHomologyIso (pushforwardOXMod i))

end PushforwardComplex

variable [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- The cohomology of the chosen complex representing `E` vanishes where that of `E` does. -/
private theorem isZero_homology_objPreimage {Y : RingedSpace.{u, u}}
    [HasDerivedCategory.{d} (OXMod.{u, u} Y)] (E : DerivedCategory (OXMod.{u, u} Y)) (j : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) j).obj E)) :
    IsZero ((DerivedCategory.Q.objPreimage E).homology j) :=
  h.of_iso ((derivedHomologyIso _ j).symm ≪≫ (DerivedCategory.homologyFunctor _ j).mapIso
    (Functor.objObjPreimageIso DerivedCategory.Q E))

/-- An object of the derived category of `𝒪_X`-modules whose cohomology vanishes in every degree
at least `m` is `m`-pseudo-coherent. -/
public theorem isPseudoCoherentFrom_of_isZero_homology_ge
    (E : DerivedCategory (OXMod.{u, u} X)) (m : ℤ)
    (h : ∀ j : ℤ, m ≤ j → IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) j).obj E)) :
    IsPseudoCoherentFrom E m := by
  set K := DerivedCategory.Q.objPreimage E
  have e : DerivedCategory.Q.obj K ≅ E := Functor.objObjPreimageIso DerivedCategory.Q E
  exact ⟨K, isPseudoCoherentComplexFrom_of_isZero_homology_ge K m fun j hj =>
    isZero_homology_objPreimage E j (h j hj), ⟨e⟩⟩

/-! ### Boundedness above on a neighbourhood of a point -/

/-- **An `m`-pseudo-coherent object of `D(𝒪_X)` is bounded above near every point.** Every point
of `X` has an open neighbourhood `U` and an integer `b` such that the cohomology of `E|_U`
vanishes in every degree above `b`. -/
public theorem exists_isZero_homology_gt_derivedRestrict
    [∀ U : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]
    (E : DerivedCategory (OXMod.{u, u} X)) (m : ℤ) (hE : IsPseudoCoherentFrom E m)
    (x : X.carrier) :
    ∃ U : Opens X.carrier, x ∈ U ∧ ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor
        (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) j).obj
          ((derivedRestrictModules X U).obj E)) := by
  obtain ⟨K, hK, ⟨eK⟩⟩ := hE
  obtain ⟨U, hxU, P, hP, α, hα, -⟩ := hK x
  obtain ⟨a, ha⟩ := exists_forall_gt_isZero hP
  refine ⟨U, hxU, max a m, fun j hj => ?_⟩
  have := hα j ((le_max_right a m).trans_lt hj)
  have hKj : IsZero ((restrictComplex K U).homology j) :=
    (HomologicalComplex.isZero_homology_of_isZero_X _ _
      (ha j ((le_max_left a m).trans_lt hj))).of_iso
      (asIso (HomologicalComplex.homologyMap α j)).symm
  refine hKj.of_iso ?_
  refine (DerivedCategory.homologyFunctor _ j).mapIso ?_ ≪≫
    derivedHomologyIso (restrictComplex K U) j
  exact (derivedRestrictModules X U).mapIso eK.symm ≪≫ derivedRestrictModulesObjQIso X U K

/-! ### Shrinking the ambient space -/

/-- Let `i : Z ⟶ Y` be a morphism of ringed spaces whose underlying continuous map is inducing,
and let `E` be an `m`-pseudo-coherent object of `D(𝒪_Z)`. Then every point of `Z` has a
neighbourhood of the form `i⁻¹U` for `U` open in `Y` on which `E` has no cohomology in high
degrees. -/
public theorem exists_opens_isZero_homology_gt_derivedRestrict_preimage
    {Y Z : RingedSpace.{u, u}} (i : Z ⟶ Y) (hi : Topology.IsInducing i.hom.base)
    [HasDerivedCategory.{d} (OXMod.{u, u} Z)]
    [∀ V : Opens Z.carrier,
      HasDerivedCategory.{d'} (OXMod.{u, u} (Z.restrict V.isOpenEmbedding))]
    (E : DerivedCategory (OXMod.{u, u} Z)) (m : ℤ) (hE : IsPseudoCoherentFrom E m)
    (x : Z.carrier) :
    ∃ U : Opens Y.carrier, x ∈ (Opens.map i.hom.base).obj U ∧ ∃ b : ℤ, ∀ j : ℤ, b < j →
      IsZero ((DerivedCategory.homologyFunctor
        (OXMod.{u, u} (Z.restrict ((Opens.map i.hom.base).obj U).isOpenEmbedding)) j).obj
          ((derivedRestrictModules Z ((Opens.map i.hom.base).obj U)).obj E)) := by
  obtain ⟨V, hxV, b, hb⟩ := exists_isZero_homology_gt_derivedRestrict E m hE x
  obtain ⟨U, rfl⟩ := exists_opens_preimage_eq i hi V
  exact ⟨U, hxV, b, hb⟩

/-! ### The base case on the target: `Ri_*E` when `E` has no cohomology above `m` -/

section Pushforward

variable {Z : RingedSpace.{u, u}} (i : Z ⟶ X) [HasDerivedCategory.{d} (OXMod.{u, u} Z)]

/-- For a closed embedding `i`, the cohomology `H^j(Ri_*E) = i_*H^j(E)` vanishes in every degree
`j` where `H^j(E)` does. -/
public theorem isZero_homology_derivedPushforward
    (hi : Topology.IsClosedEmbedding i.hom.base) (E : DerivedCategory (OXMod.{u, u} Z)) (j : ℤ)
    (h : IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Z) j).obj E)) :
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) j).obj
      ((derivedPushforwardOXMod i hi).obj E)) := by
  set K := DerivedCategory.Q.objPreimage E
  have e : DerivedCategory.Q.obj K ≅ E := Functor.objObjPreimageIso DerivedCategory.Q E
  refine IsZero.of_iso
    (isZero_homology_pushforwardComplex i hi K j (isZero_homology_objPreimage E j h)) ?_
  exact (DerivedCategory.homologyFunctor _ j).mapIso
      ((derivedPushforwardOXMod i hi).mapIso e.symm ≪≫
        (derivedPushforwardOXModFactors i hi).app K) ≪≫
    derivedHomologyIso (((pushforwardOXMod i).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) j

/-- For a closed embedding `i`, if the cohomology of `E` vanishes in every degree at least `m`
then `Ri_*E` is `m`-pseudo-coherent. -/
public theorem isPseudoCoherentFrom_derivedPushforward_of_isZero_homology_ge
    (hi : Topology.IsClosedEmbedding i.hom.base) (E : DerivedCategory (OXMod.{u, u} Z)) (m : ℤ)
    (h : ∀ j : ℤ, m ≤ j → IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Z) j).obj E)) :
    IsPseudoCoherentFrom ((derivedPushforwardOXMod i hi).obj E) m :=
  isPseudoCoherentFrom_of_isZero_homology_ge _ m fun j hj =>
    isZero_homology_derivedPushforward i hi E j (h j hj)

end Pushforward

end AlgebraicGeometry.RingedSpace

end
