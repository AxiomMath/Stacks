module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.RestrictionGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.PseudoCoherenceAlongAnExactFunctor

/-!
# Pseudo-coherence over an object of the site, read on the depth-one slices

Let `(C, O)` be a ringed site, let `K` be a complex of `O`-modules and let `V` be an object of
`C`.  Two descriptions of "`K` is `m`-pseudo-coherent over `V`" are compared here.

* The *sliced* description, `(C/V, O|_V)`-pseudo-coherence of the restriction `K|_V`.  Its data
  are strictly perfect complexes on the **iterated** slices `(C/V)/Z`.
* The *depth-one* description: the objects `W` of `C` carrying a strictly perfect approximation
  of `K|_W` in the sense of
  `AlgebraicGeometry.RingedSite.HasStrictlyPerfectApproximation` cut out a covering sieve of
  `V`, and of every object below `V`.

The second never mentions an iterated slice.  That is what makes it usable as the conclusion of
a recursion which localizes repeatedly: a slice of a slice never appears, because the index
stays an object of `C`.

## Main definitions

* `AlgebraicGeometry.RingedSite.approximationSieveGeneral`: the sieve of arrows whose source
  carries a strictly perfect `m`-approximation of `K`.  It is a sieve because an approximation
  restricts along an arrow of the site
  (`AlgebraicGeometry.RingedSite.hasStrictlyPerfectApproximation_of_hom`).

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_iff_approximationSieve`:
  `m`-pseudo-coherence of a complex is exactly that this sieve covers every object.  This holds
  by definition and is stated so that the sieve may be used in its place.
* `AlgebraicGeometry.RingedSite.approximationSieve_mem_of_isPseudoCoherentComplexFrom_over`:
  the sliced description implies the depth-one one.  The approximation that `K|_V` carries over
  an object `Z` of `C/V` lives on the iterated slice `(C/V)/Z` and is brought down to `C/Z.left`
  by `Stacks.SheafOfModules.sliceBackward`.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_over_of_approximationSieve`: the
  converse.  A depth-one approximation over `Z.left` is pushed to the iterated slice by
  `Stacks.SheafOfModules.sliceEquiv`.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_over_restrictComplex_of_locally`:
  **pseudo-coherence of a restriction is local on the object**.  If the restrictions of `K` to
  the members of a covering of `V` are `m`-pseudo-coherent on their own localized ringed sites,
  then `K|_V` is `m`-pseudo-coherent on `(C/V, O|_V)`.  This is the relative form of
  Stacks 08FU (3), and the two implications above are what make it provable without comparing
  the slices of `C/V` with the slices of `C` at depth two.

## Implementation notes

The two transports are the ones already performed in
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean` (down, inside the
proof of Stacks 08FU (3)) and in
`StacksFrontier/AlgebraicGeometry/PseudoCoherentSites/RestrictionGeneral.lean` (up, inside the
proof of the complex-level half of Stacks 08FU (3)).  There they are steps of larger proofs
whose hypotheses are pseudo-coherence on the whole site; here they are isolated and their
hypotheses localized at `V`, which is the only change.

`isStrictlyPerfect_sliceBackward` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean` is `private`, so it
is restated below as
`AlgebraicGeometry.RingedSite.isStrictlyPerfect_sliceBackward_general`, with the same proof from
the public `Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex`,
`sliceBackward_preservesFiniteColimits` and `sliceBackwardUnitIso`.

**No `@[stacks]` attribute is attached to anything here.**  Stacks 08FU (3) is carried by the
two files named above; what is below is a comparison of two descriptions of its local data,
which is not a clause of 08FU or of any other tag.

## References

* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
* [Stacks Project, Tag 04IX](https://stacks.math.columbia.edu/tag/04IX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d d'

namespace AlgebraicGeometry.RingedSite

section Bridge

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

-- The sheafification data of the slices and of the iterated slices, and the exactness of
-- restriction, at the spellings the localized ringed site uses.  All of these are `local
-- instance`s of
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/TorAmplitude/LocallyFiniteTorDimension.lean` and
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean`, already at a
-- free sections universe `w`; the declarations are imported, so only the instance attribute has
-- to be re-enabled here.
attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective
attribute [local instance] iterHasSheafify iterWEq iterHasSheafifyAll iterWEqAll
attribute [local instance] overMapLimits overMapColimits ovFunctorLimits ovFunctorColimits

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Transport from an iterated slice carries a complex which is strictly perfect there to a
strictly perfect complex on the slice.

This repeats the `private` `isStrictlyPerfect_sliceBackward` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean`; that file is
owned elsewhere, so the declaration cannot be made public there.  Its proof is reproduced
verbatim from the public `Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex`. -/
theorem isStrictlyPerfect_sliceBackward_general {U V : X.C} (f : V ⟶ U)
    {P : CochainComplex
      (SheafOfModules.{w}
        (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).over (Over.mk f))) ℤ}
    (hP : IsStrictlyPerfect
      (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U).over (Over.mk f)) P) :
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
      (((Stacks.SheafOfModules.sliceBackward.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  have : PreservesFiniteColimits
      (Stacks.SheafOfModules.sliceBackward.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) f) :=
    Stacks.SheafOfModules.sliceBackward_preservesFiniteColimits f
  Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex _
    (Stacks.SheafOfModules.sliceBackwardUnitIso.{w} f) hP

/-- **The sieve of arrows whose source carries a strictly perfect `m`-approximation of `K`.**
It is a sieve because such an approximation restricts along an arrow of the site.

This repeats the `private` `approximationSieve` of
`StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/DistinguishedTriangles.lean`, which
is owned elsewhere and so cannot be the surviving declaration. -/
def approximationSieveGeneral
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (m : ℤ)
    (U : X.C) : Sieve U where
  arrows {_V} _ := X.HasStrictlyPerfectApproximation K m _V
  downward_closed := fun hf g => hasStrictlyPerfectApproximation_of_hom X K m g hf

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- Pulling the approximation sieve back along an arrow gives the approximation sieve of the
source: membership depends only on the source object of the arrow. -/
theorem approximationSieveGeneral_pullback
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (m : ℤ)
    {U V : X.C} (g : V ⟶ U) :
    (approximationSieveGeneral X K m U).pullback g = approximationSieveGeneral X K m V :=
  Sieve.ext fun _ _ => Iff.rfl

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **`m`-pseudo-coherence of a complex is exactly that the approximation sieve covers every
object.**  This holds by definition; it is recorded so that the sieve may be used in place of
the existential over covering presieves. -/
theorem isPseudoCoherentComplexFrom_iff_approximationSieve
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (m : ℤ) :
    X.IsPseudoCoherentComplexFrom K m ↔
      ∀ U : X.C, approximationSieveGeneral X K m U ∈ X.J U := by
  constructor
  · intro h U
    obtain ⟨S, hS, hdata⟩ := h U
    exact X.J.superset_covering ((Sieve.generate_le_iff _ _).mpr fun _ _ hf => hdata _ hf) hS
  · intro h U
    exact ⟨(approximationSieveGeneral X K m U).arrows, by simpa using h U, fun _ _ hg => hg⟩

/-- An exact functor carries the data of an approximation `α` to the data of the approximation
`F α ≫ e.hom`, for any identification `e` of the image of the target. -/
private theorem approximation_conditions_map {A B : Type*} [Category A] [Abelian A]
    [Category B] [Abelian B] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] {P Q : CochainComplex A ℤ} {R : CochainComplex B ℤ} {m : ℤ}
    (α : P ⟶ Q) (e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q ≅ R)
    (hiso : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hepi : Epi (HomologicalComplex.homologyMap α m)) :
    (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ e.hom) j)) ∧
    Epi (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ e.hom) m) :=
  have : F.PreservesHomology := Functor.preservesHomologyOfExact F
  ⟨fun j hj => isIso_homologyMap_comp_iso _ e j (isIso_homologyMap_map F α j (hiso j hj)),
    epi_homologyMap_comp_iso _ e m (epi_homologyMap_map F α m hepi)⟩

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The sliced description of pseudo-coherence over `V` implies the depth-one one.**  If the
restriction `K|_V` is `m`-pseudo-coherent on the localized ringed site over `V`, then the
objects carrying a strictly perfect `m`-approximation of `K` cut out a covering sieve of `V`.

The definition of pseudo-coherence of `K|_V` is used only at the terminal object `Over.mk (𝟙 V)`
of `C/V`, whose covering presieves are the covering presieves of `V`; the approximation it
provides over an object `Z` of `C/V` lives on the iterated slice `(C/V)/Z` and is carried down
to `C/Z.left` by `Stacks.SheafOfModules.sliceBackward`, whose composite with restriction to the
iterated slice is restriction along `Z.hom`. -/
theorem approximationSieve_mem_of_isPseudoCoherentComplexFrom_over
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (m : ℤ)
    (V : X.C)
    (hc : (X.over V).IsPseudoCoherentComplexFrom (X.restrictComplex K V) m) :
    approximationSieveGeneral X K m V ∈ X.J V := by
  obtain ⟨S₁, hS₁, hdata₁⟩ := hc (Over.mk (𝟙 V))
  have hgen : Sieve.generate (Presieve.map (Over.forget V) S₁) ∈ X.J V := by
    rw [Sieve.generate_map_eq_functorPushforward]
    exact hS₁
  refine X.J.superset_covering ((Sieve.generate_le_iff _ _).mpr ?_) hgen
  rintro W g @⟨Z, u, hv⟩
  obtain ⟨P, hP, α, hgt, hep⟩ := hdata₁ u hv
  let Sb :=
    Stacks.SheafOfModules.sliceBackward.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom
  let Sbc := Sb.mapHomologicalComplex (ComplexShape.up ℤ)
  let e₁ :=
    (Stacks.SheafOfModules.sliceBackwardComplexIso.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      Z.hom).app (X.restrictComplex K V)
  let e₂ :=
    (Stacks.SheafOfModules.overFunctorMapComplexIso.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      Z.hom).app K
  let e := e₁ ≪≫ e₂
  have : PreservesFiniteLimits Sb :=
    Stacks.SheafOfModules.sliceBackward_preservesFiniteLimits Z.hom
  have : PreservesFiniteColimits Sb :=
    Stacks.SheafOfModules.sliceBackward_preservesFiniteColimits Z.hom
  exact ⟨Sbc.obj P, isStrictlyPerfect_sliceBackward_general X Z.hom hP, Sbc.map α ≫ e.hom,
    approximation_conditions_map Sb α e hgt hep⟩

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- **The depth-one description of pseudo-coherence over `V` implies the sliced one.**  If the
approximation sieve covers every object below `V`, then the restriction `K|_V` is
`m`-pseudo-coherent on the localized ringed site over `V`.

A depth-one approximation over `Z.left` is pushed to the iterated slice `(C/V)/Z` by
`Stacks.SheafOfModules.sliceEquiv`, which is an equivalence, hence exact and compatible with
strict perfectness (`Stacks.SheafOfModules.isStrictlyPerfect_sliceEquiv_general`), and which
matches restriction along `Z.hom` with restriction to the iterated slice
(`Stacks.SheafOfModules.sliceEquivOverFunctorComplexIsoGeneral`). -/
theorem isPseudoCoherentComplexFrom_over_of_approximationSieve
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (m : ℤ)
    (V : X.C)
    (hloc : ∀ Z : Over V, approximationSieveGeneral X K m Z.left ∈ X.J Z.left) :
    (X.over V).IsPseudoCoherentComplexFrom (X.restrictComplex K V) m := by
  intro Z
  refine ⟨Presieve.functorPullback (Over.forget V)
    (approximationSieveGeneral X K m Z.left).arrows, ?_, ?_⟩
  · have hS₁ : Sieve.generate (approximationSieveGeneral X K m Z.left).arrows ∈ X.J Z.left := by
      simpa using hloc Z
    have hmem : (Sieve.overEquiv Z).symm
        (Sieve.generate (approximationSieveGeneral X K m Z.left).arrows) ∈ (X.J.over V) Z := by
      rw [X.J.mem_over_iff]
      simpa using hS₁
    rw [show Sieve.generate (Presieve.functorPullback (Over.forget V)
        (approximationSieveGeneral X K m Z.left).arrows) =
      (Sieve.overEquiv Z).symm
        (Sieve.generate (approximationSieveGeneral X K m Z.left).arrows) from
        (Sieve.overEquiv_symm_generate _).symm]
    exact hmem
  · intro W f hf
    obtain ⟨P, hP, α, hiso, hepi⟩ := hf
    let Fe :=
      (Stacks.SheafOfModules.sliceEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V W).functor
    let Fec := Fe.mapHomologicalComplex (ComplexShape.up ℤ)
    let e : Fec.obj (X.restrictComplex K W.left) ≅
        (X.over V).restrictComplex (X.restrictComplex K V) W :=
      Fec.mapIso
          ((Stacks.SheafOfModules.overFunctorMapComplexIso.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W.hom).app K).symm ≪≫
        (Stacks.SheafOfModules.sliceEquivOverFunctorComplexIsoGeneral
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V W).app (X.restrictComplex K V)
    have : PreservesFiniteLimits Fe := inferInstance
    have : PreservesFiniteColimits Fe := inferInstance
    exact ⟨Fec.obj P,
      Stacks.SheafOfModules.isStrictlyPerfect_sliceEquiv_general
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V W hP,
      Fec.map α ≫ e.hom, approximation_conditions_map Fe α e hiso hepi⟩

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat] in
/-- An `n`-pseudo-coherent complex is `i`-pseudo-coherent for every `i ≥ n`: the same
approximation serves, since the two conditions it satisfies only weaken. -/
theorem isPseudoCoherentComplexFrom_mono_general
    (E : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    {n i : ℤ}
    (hE : X.IsPseudoCoherentComplexFrom E n) (hni : n ≤ i) :
    X.IsPseudoCoherentComplexFrom E i := by
  rcases hni.eq_or_lt with rfl | hni
  · exact hE
  · intro U
    obtain ⟨S, hS, hP⟩ := hE U
    refine ⟨S, hS, fun V f hf => ?_⟩
    obtain ⟨P, hP, α, hα, _⟩ := hP f hf
    have : IsIso (HomologicalComplex.homologyMap α i) := hα i hni
    exact ⟨P, hP, α, fun j hj => hα j (hni.trans hj), inferInstance⟩

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- An `n`-pseudo-coherent object of `D(O)` is `i`-pseudo-coherent for every `i ≥ n`. -/
theorem isPseudoCoherentFrom_mono_general
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {n i : ℤ}
    (h : X.IsPseudoCoherentFrom E n) (hni : n ≤ i) : X.IsPseudoCoherentFrom E i := by
  obtain ⟨P, hP, e⟩ := h
  exact ⟨P, isPseudoCoherentComplexFrom_mono_general X P hP hni, e⟩

variable [hRestrDer : ∀ U : X.C,
  HasDerivedCategory.{d'}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

-- The derived-category models of the slices, at both spellings; again the `local instance`s of
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean`.
attribute [local instance] locallyOverRingSheafHasDerivedCategory ovHasDerived

omit [HasSheafify X.J AddCommGrpCat] [X.J.WEqualsLocallyBijective AddCommGrpCat]
  [HasDerivedCategory (SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf X.O))] in
/-- **Pseudo-coherence of a restriction is local on the object**, the relative form of
Stacks 08FU (3).  Let `K` be a complex of `O`-modules, let `V` be an object of `C` and let `T`
be a covering sieve of `V`.  If for every arrow `W ⟶ V` of `T` the restriction `K|_W` is
`m`-pseudo-coherent on the localized ringed site over `W`, then `K|_V` is `m`-pseudo-coherent
on the localized ringed site over `V`.

The passage goes through the depth-one description: each `W` of `T` gives a covering sieve of
`W` whose sources carry approximations
(`approximationSieve_mem_of_isPseudoCoherentComplexFrom_over`), transitivity of the topology
assembles those into a covering sieve of `V`, pullback stability carries it to every object
below `V`, and `isPseudoCoherentComplexFrom_over_of_approximationSieve` returns to the sliced
description.  No comparison between the slices of `C/V` and the slices of `C` at depth two is
needed, which is what makes this statement available where
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general` — stated at the ambient
site, hence at `C/V` only through its own slices — is not. -/
theorem isPseudoCoherentFrom_over_restrictComplex_of_locally
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (m : ℤ)
    (V : X.C)
    (T : Sieve V) (hT : T ∈ X.J V)
    (h : ∀ ⦃W : X.C⦄ (g : W ⟶ V), T g →
      (X.over W).IsPseudoCoherentFrom (DerivedCategory.Q.obj (X.restrictComplex K W)) m) :
    (X.over V).IsPseudoCoherentFrom (DerivedCategory.Q.obj (X.restrictComplex K V)) m := by
  have hW : ∀ ⦃W : X.C⦄ (g : W ⟶ V), T g → approximationSieveGeneral X K m W ∈ X.J W := by
    intro W g hg
    refine approximationSieve_mem_of_isPseudoCoherentComplexFrom_over X K m W ?_
    exact isPseudoCoherentComplexFrom_of_iso_general (X.over W) _ m (h g hg)
      (X.restrictComplex K W) (Iso.refl _)
  have hV : approximationSieveGeneral X K m V ∈ X.J V := by
    refine X.J.transitive hT _ fun {W} g hg => ?_
    rw [approximationSieveGeneral_pullback]
    exact hW g hg
  refine ⟨X.restrictComplex K V,
    isPseudoCoherentComplexFrom_over_of_approximationSieve X K m V fun Z => ?_, ⟨Iso.refl _⟩⟩
  rw [← approximationSieveGeneral_pullback X K m Z.hom]
  exact X.J.pullback_stable Z.hom hV

end Bridge

end AlgebraicGeometry.RingedSite

end
