module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherentObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# A perfect object is pseudo-coherent and locally of finite Tor dimension

Let `(C, O)` be a ringed site. A perfect complex of `O`-modules is pseudo-coherent, a perfect
object of `D(O)` is pseudo-coherent, and a perfect object of `D(O)` locally has finite Tor
dimension. Together these are the implication (1) ⟹ (2) of Stacks 08G8.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplex_of_isPerfectComplex`: a perfect complex
  is pseudo-coherent.
* `AlgebraicGeometry.RingedSite.isPseudoCoherent_of_isPerfect`: a perfect object of `D(O)` is
  pseudo-coherent.
* In the namespace `Stacks.SheafOfModules.DerivedTensorProduct`:
  * `hasFiniteTorDimension_of_isStrictlyPerfect_model_anyUniverse`: an object of `D(O)`
    represented by a strictly perfect complex has finite Tor dimension.
  * `locallyHasFiniteTorDimension_of_isPerfect_anyUniverse`: a perfect object of `D(O)` locally
    has finite Tor dimension.
  * `hasFiniteTorDimension_of_isStrictlyPerfect_model` and
    `locallyHasFiniteTorDimension_of_isPerfect`: the same two statements for a site in `Type`.

## Implementation notes

Pseudo-coherence is immediate from the definitions: perfectness provides, above a covering of
each object, a strictly perfect complex mapping *quasi-isomorphically* to the restriction, and a
quasi-isomorphism is in particular an isomorphism on cohomology in every degree and an
epimorphism on cohomology in the bottom degree, which is what `m`-pseudo-coherence asks for, for
every `m`.

Locally finite Tor dimension is the source's "a direct summand of a finite free module is flat,
hence `E|_{U_i}` has finite Tor dimension by Stacks 08G1". The two inputs are
`Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect`, which is that sentence, and the easy
direction of Stacks 08G1,
`Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitude_of_flatRepresentative`: a strictly
perfect complex is bounded and has flat terms, so it is a bounded flat representative of the
object it computes, and the interval between its lowest and highest nonzero degrees is a Tor
amplitude interval. The covering is the one perfectness supplies, not the maximal one: a perfect
object need not have a strictly perfect model over an object itself, only over a covering of it.

The universes collapse to one in the Tor-dimension clause. Flatness of a direct summand of a
finite free module is available only when the sections of the structure sheaf live in `max u v`,
that being where the unit law for the tensor product is — see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/FlatnessOfFiniteFreeSummands.lean`
— and a slice of a `RingedSite.{u, u, u}` is again a `RingedSite.{u, u, u}`, so the clause is
stated on the diagonal, which is closed under the operation it is about. The pseudo-coherence
clause needs neither and keeps the object and morphism universes free.

The Tor-dimension clause is stated twice: once on the diagonal at an arbitrary universe, with
the `_anyUniverse` suffix, and once for a site in `Type`, the two consumers of the clause asking
for it at those two shapes. The `Type` statements are instances of the arbitrary-universe ones
and are proved by applying them.

This file carries **no** `@[stacks 08G8]` attribute: the full statement of Stacks 08G8 is an
equivalence, and only the implication (1) ⟹ (2) is proved here, so the tag would sit on a
strictly weaker statement. The converse implication, which goes through Stacks 08G7
(`Stacks.SheafOfModules.DerivedTensorProduct.torAmplitudePerfectnessCriterion`), and the
equivalence that the two assemble into — which is where the tag sits — are in
`StacksFrontier/CategoryTheory/Sites/Cohomology/Perfect/PerfectnessCriterion.lean`.

## References

* [Stacks Project, Tag 08G8](https://stacks.math.columbia.edu/tag/08G8)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 08G1](https://stacks.math.columbia.edu/tag/08G1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v d

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, 0})
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]

/-- A perfect complex of `O`-modules is `m`-pseudo-coherent for every `m`: the strictly perfect
local models of a perfect complex map to it by quasi-isomorphisms, which are isomorphisms on
cohomology in all degrees. -/
theorem isPseudoCoherentComplex_of_isPerfectComplex
    {E : CochainComplex (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hE : X.IsPerfectComplex E) :
    X.IsPseudoCoherentComplex E := by
  intro m U
  obtain ⟨S, hS, hmodels⟩ := hE U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨P, hP, q, hq⟩ := hmodels f hf
  let := hq
  exact ⟨P, hP, q, fun _ _ => inferInstance, inferInstance⟩

variable [HasSheafify X.J AddCommGrpCat.{0}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- A perfect object of `D(O)` is pseudo-coherent. This is the first clause of the implication
(1) ⟹ (2) of Stacks 08G8. -/
theorem isPseudoCoherent_of_isPerfect
    {E : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hE : X.IsPerfect E) :
    X.IsPseudoCoherent E := by
  obtain ⟨K, hK, e⟩ := hE
  exact ⟨K, isPseudoCoherentComplex_of_isPerfectComplex X hK, e⟩

end AlgebraicGeometry.RingedSite

/-! ### Locally finite Tor dimension -/

namespace Stacks.SheafOfModules.DerivedTensorProduct

open AlgebraicGeometry

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

section AnyUniverse

variable {X : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{u}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} (X.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

variable
  [∀ U : X.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{u, u, u} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, u, u} X)] in
/-- **An object represented by a strictly perfect complex has finite Tor dimension.** A strictly
perfect complex is bounded and its terms are direct summands of finite free `O`-modules, hence
flat, so it is a bounded flat representative and the easy direction of Stacks 08G1 gives Tor
amplitude in the interval between its lowest and highest nonzero degrees.

The site's universes are arbitrary here, on the diagonal;
`hasFiniteTorDimension_of_isStrictlyPerfect_model` is this statement for a site in `Type`. -/
theorem hasFiniteTorDimension_of_isStrictlyPerfect_model_anyUniverse (V : X.C)
    (T' : DerivedTensorProduct.{u, u, u, d} (X.over V))
    (F : RingedSite.DerivedModules.{u, u, u, d} (X.over V))
    {P : CochainComplex (RingedSite.Modules.{u, u, u} (X.over V)) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).O) P)
    (e : DerivedCategory.Q.obj P ≅ F) :
    HasFiniteTorDimension T' F := by
  obtain ⟨n, hn⟩ := hP.bounded.bddAbove
  obtain ⟨m, hm⟩ := hP.bounded.bddBelow
  refine ⟨m, n, hasTorAmplitude_of_flatRepresentative T' F m n P
    (fun i => Stacks.SheafOfModules.isFlat_X_of_isStrictlyPerfect hP i) (fun i hi => ?_) e⟩
  by_contra hz
  simp only [Set.mem_Icc, not_and_or, not_le] at hi
  rcases hi with h | h
  · exact absurd (hm (show i ∈ {j : ℤ | ¬ IsZero (P.X j)} from hz)) (by omega)
  · exact absurd (hn (show i ∈ {j : ℤ | ¬ IsZero (P.X j)} from hz)) (by omega)

/-- **A perfect object of `D(O)` locally has finite Tor dimension**, the Tor-dimension clause of
the implication (1) ⟹ (2) of Stacks 08G8.

The covering is the one perfectness supplies; over each of its members the strictly perfect
model has finite Tor dimension by
`hasFiniteTorDimension_of_isStrictlyPerfect_model_anyUniverse`, and it computes the restriction
of `E` because the given quasi-isomorphism becomes an isomorphism in the derived category of the
slice.

The site's universes are arbitrary here, on the diagonal;
`locallyHasFiniteTorDimension_of_isPerfect` is this statement for a site in `Type`. -/
theorem locallyHasFiniteTorDimension_of_isPerfect_anyUniverse
    (T : ∀ U : X.C, DerivedTensorProduct.{u, u, u, d} (X.over U))
    (E : RingedSite.DerivedModules.{u, u, u, d} X) (hE : X.IsPerfect E) :
    LocallyHasFiniteTorDimension T E := by
  obtain ⟨Ecpx, hEcpx, ⟨eE⟩⟩ := hE
  intro U
  obtain ⟨S, hS, hmodels⟩ := hEcpx U
  refine ⟨S, hS, fun {V} f hf => ?_⟩
  obtain ⟨P, hP, q, hq⟩ := hmodels f hf
  have eQ : DerivedCategory.Q.obj P ≅
      DerivedCategory.Q.obj (X.restrictComplex Ecpx V) := by
    let : IsIso (DerivedCategory.Q.map q) :=
      (DerivedCategory.isIso_Q_map_iff_quasiIso
        (C := SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) q).2 hq
    exact asIso (DerivedCategory.Q.map q)
  exact hasFiniteTorDimension_of_isStrictlyPerfect_model_anyUniverse V (T V) _ hP
    (eQ ≪≫
      ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategoryFactors.app Ecpx).symm ≪≫
      (SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.mapIso eE)

end AnyUniverse

/-! ### The Tor-dimension clause for a site in `Type` -/

section TypeZero

variable {X : RingedSite.{0, 0, 0}}
  [HasSheafify X.J AddCommGrpCat.{0}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]

attribute [local instance] RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

variable [HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} X)]
  [hSliceDerived : ∀ U : X.C,
    HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} (X.over U))]

attribute [local instance] RingedSite.sliceHasDerivedCategory sliceDerived

variable
  [∀ U : X.C, (Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} (X.over U).O).Additive]
  [∀ (U : X.C) M,
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{0, 0, 0, 0, 0} (X.over U).O).obj M).Additive]
  [∀ (U : X.C) (K L : CochainComplex (RingedSite.Modules.{0, 0, 0} (X.over U)) ℤ),
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor (X.over U).O) (ComplexShape.up ℤ)]

attribute [local instance] sliceTensorAdditive sliceTensorObjAdditive sliceHasMapBifunctor

omit [HasSheafify X.J AddCommGrpCat.{0}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{0, 0, 0} X)] in
/-- **An object represented by a strictly perfect complex has finite Tor dimension.** A strictly
perfect complex is bounded and its terms are direct summands of finite free `O`-modules, hence
flat, so it is a bounded flat representative and the easy direction of Stacks 08G1 gives Tor
amplitude in the interval between its lowest and highest nonzero degrees. -/
theorem hasFiniteTorDimension_of_isStrictlyPerfect_model (V : X.C)
    (T' : DerivedTensorProduct.{0, 0, 0, d} (X.over V))
    (F : RingedSite.DerivedModules.{0, 0, 0, d} (X.over V))
    {P : CochainComplex (RingedSite.Modules.{0, 0, 0} (X.over V)) ℤ}
    (hP : IsStrictlyPerfect (Stacks.SheafOfModules.Tensor.ringSheaf (X.over V).O) P)
    (e : DerivedCategory.Q.obj P ≅ F) :
    HasFiniteTorDimension T' F :=
  hasFiniteTorDimension_of_isStrictlyPerfect_model_anyUniverse V T' F hP e

/-- **A perfect object of `D(O)` locally has finite Tor dimension**, the Tor-dimension clause of
the implication (1) ⟹ (2) of Stacks 08G8.

The covering is the one perfectness supplies; over each of its members the strictly perfect
model has finite Tor dimension by `hasFiniteTorDimension_of_isStrictlyPerfect_model`, and it
computes the restriction of `E` because the given quasi-isomorphism becomes an isomorphism in
the derived category of the slice. -/
theorem locallyHasFiniteTorDimension_of_isPerfect
    (T : ∀ U : X.C, DerivedTensorProduct.{0, 0, 0, d} (X.over U))
    (E : RingedSite.DerivedModules.{0, 0, 0, d} X) (hE : X.IsPerfect E) :
    LocallyHasFiniteTorDimension T E :=
  locallyHasFiniteTorDimension_of_isPerfect_anyUniverse T E hE

end TypeZero

end Stacks.SheafOfModules.DerivedTensorProduct

end
