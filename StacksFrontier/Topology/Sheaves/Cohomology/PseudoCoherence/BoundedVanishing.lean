module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedApproximation
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Restriction
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.Topology.Sheaves.Cohomology.MappingConeApproximation.ShiftLemmas

/-!
# Shrinking a vanishing statement, and pseudo-coherence below a bound

Two facts shared by the two descending inductions that prove Stacks 09V7 and Stacks 09V8.

The first is that restriction of a complex of `𝒪_X`-modules to a smaller open subspace kills
whatever restriction to the larger one kills, both termwise and on cohomology. The local
boundedness hypothesis of each of those two tags is stated over an open neighbourhood of a point
chosen by that hypothesis, while the strictly perfect approximation is found over an open
neighbourhood chosen by pseudo-coherence; the induction runs over the intersection, and these
lemmas carry the boundedness there.

The second is that an object of the derived category whose cohomology vanishes in degrees `≥ m`
is `m`-pseudo-coherent, the zero complex being an approximation of it over all of `X`. This is
the base case of both inductions.

## Main results

* `AlgebraicGeometry.RingedSpace.isZero_restrictComplex_X_of_le` and
  `AlgebraicGeometry.RingedSpace.isZero_restrictComplex_homology_of_le`: vanishing of a term,
  resp. of a cohomology sheaf, of a restricted complex passes to a smaller open subspace.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_isLE`: an object of the derived category
  which is `IsLE (m - 1)` is `m`-pseudo-coherent.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_single_of_isZero`: a zero module placed in
  degree zero is `m`-pseudo-coherent for every `m`.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_single`: a module placed in degree `d` is
  `m`-pseudo-coherent exactly when the same module placed in degree zero is
  `(m - d)`-pseudo-coherent.

## Implementation notes

Restriction from `U` to `W ≤ U` is restriction to the open `(Opens.map U.inclusion').obj W` of
`X|_U` followed by the identification of modules there with modules on `X|_W`, and the image of
that preimage is `W` again by `Stacks.Cohomology.PerfectComplexTriangles.image_preimage_of_le`.
This is the same route
`AlgebraicGeometry.RingedSpace.exists_restricted_approximation` takes for an
approximation, and the rewrite along that equality of opens is performed in the `Prop` being
proved rather than by transporting an isomorphism.

`AlgebraicGeometry.RingedSpace.nestedModulesEquivalence_functor_additive` is registered as a
local instance here for the same reason as where it is proved: its subject is built by tactics
and is expensive for instance search to unfold while refuting a goal about another functor.

## References

* [The Stacks Project, Lemma 20.46.10 (09V7)](https://stacks.math.columbia.edu/tag/09V7)
* [The Stacks Project, Lemma 20.46.11 (09V8)](https://stacks.math.columbia.edu/tag/09V8)
* [The Stacks Project, Definition 20.46.4 (08CB)](https://stacks.math.columbia.edu/tag/08CB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open scoped ZeroObject

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

attribute [local instance 10] nestedModulesEquivalence_functor_additive

/-- Vanishing of a term of a complex restricted to an open subspace `U` passes to any smaller
open subspace `W`. -/
public theorem isZero_restrictComplex_X_of_le {U W : Opens X.carrier} (hWU : W ≤ U)
    (F : CochainComplex (OXMod.{u, u} X) ℤ) {i : ℤ}
    (h : IsZero ((restrictComplex F U).X i)) : IsZero ((restrictComplex F W).X i) := by
  set V : Opens (X.restrict U.isOpenEmbedding).carrier := (Opens.map U.inclusion').obj W
  have key : IsZero ((restrictComplex F (U.isOpenEmbedding.functor.obj V)).X i) :=
    (((nestedModulesEquivalence U V).functor.isZero_obj
      ((restrictModules (X.restrict U.isOpenEmbedding) V).isZero_obj h))).of_iso
      (HomologicalComplex.Hom.isoApp (nestedComplexIso U V F) i).symm
  rwa [Stacks.Cohomology.PerfectComplexTriangles.image_preimage_of_le hWU] at key

/-- Vanishing of a cohomology sheaf of a complex restricted to an open subspace `U` passes to any
smaller open subspace `W`: restriction is exact, so it commutes with cohomology. -/
public theorem isZero_restrictComplex_homology_of_le {U W : Opens X.carrier} (hWU : W ≤ U)
    (F : CochainComplex (OXMod.{u, u} X) ℤ) {i : ℤ}
    (h : IsZero ((restrictComplex F U).homology i)) :
    IsZero ((restrictComplex F W).homology i) := by
  set V : Opens (X.restrict U.isOpenEmbedding).carrier := (Opens.map U.inclusion').obj W
  let R := restrictModules (X.restrict U.isOpenEmbedding) V
  let G := (nestedModulesEquivalence U V).functor
  have : PreservesFiniteLimits R := restrictModules_preservesFiniteLimits _ V
  have : PreservesFiniteColimits R := restrictModules_preservesFiniteColimits _ V
  have hR : IsZero ((restrictComplex (restrictComplex F U) V).homology i) :=
    (R.isZero_obj h).of_iso (((restrictComplex F U).sc i).mapHomologyIso R)
  have hG : IsZero (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (restrictComplex (restrictComplex F U) V)).homology i) :=
    (G.isZero_obj hR).of_iso (((restrictComplex (restrictComplex F U) V).sc i).mapHomologyIso G)
  have key : IsZero ((restrictComplex F (U.isOpenEmbedding.functor.obj V)).homology i) :=
    hG.of_iso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) i).mapIso
      (nestedComplexIso U V F)).symm
  rwa [Stacks.Cohomology.PerfectComplexTriangles.image_preimage_of_le hWU] at key

/-- A complex of `𝒪_X`-modules whose cohomology vanishes in degrees `≥ m` is
`m`-pseudo-coherent: the zero complex, which is strictly perfect, approximates it over all
of `X`. -/
public theorem isPseudoCoherentComplexFrom_of_isZero_homology
    (K : CochainComplex (OXMod.{u, u} X) ℤ) (m : ℤ)
    (hK : ∀ i : ℤ, m ≤ i → IsZero ((restrictComplex K ⊤).homology i)) :
    IsPseudoCoherentComplexFrom K m := fun _ =>
  ⟨⊤, trivial, 0, isStrictlyPerfect_of_forall_isZero fun i =>
      (HomologicalComplex.eval _ _ i).isZero_obj (isZero_zero _), 0,
    fun j hj => ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).isZero_obj
      (isZero_zero _)).isIso (hK j hj.le) _,
    (hK m le_rfl).epi _⟩

/-- **An object of the derived category of `𝒪_X`-modules which is `IsLE (m - 1)` is
`m`-pseudo-coherent.** It is represented by a complex with no terms above `m - 1`, whose
cohomology therefore vanishes in degrees `≥ m`, as does that of its restriction to any open
subspace. -/
public theorem isPseudoCoherentFrom_of_isLE
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (E : DerivedCategory (OXMod.{u, u} X)) (m : ℤ) [E.IsLE (m - 1)] :
    IsPseudoCoherentFrom E m := by
  obtain ⟨K, hK, ⟨e⟩⟩ := E.exists_iso_Q_obj_of_isLE (m - 1)
  refine ⟨K, isPseudoCoherentComplexFrom_of_isZero_homology K m fun i hi => ?_, ⟨e.symm⟩⟩
  exact ShortComplex.isZero_homology_of_isZero_X₂ _
    ((restrictModules X ⊤).isZero_obj (K.isZero_of_isStrictlyLE (m - 1) i (by omega)))

/-- A zero module of `𝒪_X`-modules placed in degree zero is `m`-pseudo-coherent for every `m`:
the object of the derived category it defines is zero, hence `IsLE (m - 1)`. -/
public theorem isPseudoCoherentFrom_single_of_isZero
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (M : OXMod.{u, u} X) (m : ℤ) (hM : IsZero M) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj M) m := by
  have : ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj M).IsLE (m - 1) := by
    rw [DerivedCategory.isLE_iff]
    exact fun i _ => (DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).isZero_obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).isZero_obj hM)
  exact isPseudoCoherentFrom_of_isLE _ m

/-- **A module placed in degree `d` is `m`-pseudo-coherent when the same module placed in degree
zero is `(m - d)`-pseudo-coherent.** Placing a module in degree `d` is placing it in degree zero
and shifting by `-d`, and shifting by `n` lowers the degree an object is pseudo-coherent from
by `n`. -/
public theorem isPseudoCoherentFrom_single
    [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    (M : OXMod.{u, u} X) (e m : ℤ)
    (hM : IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj M) (m - e)) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) e).obj M) m := by
  refine IsPseudoCoherentFrom.of_iso (E := (((DerivedCategory.singleFunctors
    (OXMod.{u, u} X)).functor 0 ⋙ shiftFunctor _ (-e)).obj M)) ?_
    (((DerivedCategory.singleFunctors (OXMod.{u, u} X)).shiftIso (-e) e 0 (by omega)).app M)
  simpa using isPseudoCoherentFrom_shift hM (-e)

end AlgebraicGeometry.RingedSpace

end
