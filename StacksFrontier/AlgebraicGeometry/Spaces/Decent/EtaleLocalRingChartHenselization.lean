module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ElementaryEtaleNeighborhoodGeometricPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricStalkBaseChange
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.BaseChange
public import StacksFrontier.RingTheory.HenselizationUniverse.Basic

/-!
# The étale local ring as a strict henselization of a neighborhood stalk

The étale local ring of an algebraic space at a geometric point `x̄` is a strict henselization
of the local ring `𝒪_{U, u}` of a scheme chart at the point under the chosen lift of `x̄`, for
every chosen separable algebraic closure of the residue field of that local ring. For an
elementary étale neighborhood `(U, u)` of the point `x` below `x̄` the lift is the one supplied
by the residue-field point of `u`, so `u` itself is the point at which the stalk is taken.

## Main results

* `AlgebraicGeometry.Space.isHenselization_chartLocalRingToEtaleLocalRing`: the étale local ring
  at `x̄` is a strict henselization of `𝒪_{U, u}` *along the canonical map of Stacks 05VP*.
* `AlgebraicGeometry.Space.exists_algebra_isHenselization_etaleLocalRing_chart`: the étale local
  ring at `x̄` is a strict henselization of `𝒪_{U, u}` for a small étale neighbourhood.
* `AlgebraicGeometry.Space.exists_algebra_isHenselization_etaleLocalRing_elementary`: the same
  for an elementary étale neighbourhood of the point below `x̄`, where the stalk is taken at the
  distinguished point.
* `AlgebraicGeometry.Space.strictlyHenselianLocalRing_etaleLocalRing`: the étale local ring at
  every geometric point is a strictly henselian local ring.

## Implementation notes

The comparison of Stacks 04KF is already available as
`AlgebraicGeometry.Space.chartStrictHenselizationEquiv`, identifying the étale local ring with
the strict henselization chosen in `AlgebraicGeometry.Space.chartHenselizationTower`; the
algebra structure transported along it is the canonical map of Stacks 05VP, so the comparison
is a map of algebras over the neighborhood stalk by construction. What that tower prescribes as
the residue extension is the separable closure of the residue field inside the field of the
geometric point, and an arbitrary chosen separable closure is matched to it by uniqueness of
separable closures; the two transports are
`IsLocalRing.IsHenselization.of_ringEquiv` and `IsLocalRing.IsHenselization.of_algEquiv`.

For an elementary étale neighborhood the point of the chart scheme at which the stalk is taken
is the image of the closed point of the field spectrum of the geometric point, and the lift
factors through the residue-field point of the distinguished point, whose image is that point.

## References

* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 08HT](https://stacks.math.columbia.edu/tag/08HT)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u v w

namespace IsLocalRing.IsHenselization

/-- A henselization with a prescribed residue extension is a henselization with respect to any
isomorphic extension of the residue field. -/
theorem of_algEquiv {R : Type u} [CommRing R] [IsLocalRing R]
    {L : Type v} [Field L] [Algebra (ResidueField R) L]
    {L' : Type w} [Field L'] [Algebra (ResidueField R) L']
    {Rh : Type*} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh]
    [IsHenselization R L Rh] (φ : L' ≃ₐ[ResidueField R] L) :
    IsHenselization R L' Rh where
  henselian := IsHenselization.henselian (R := R) (L := L) (Rh := Rh)
  ind_etale := IsHenselization.ind_etale (R := R) (L := L) (Rh := Rh)
  exists_residueFieldEquiv := by
    obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := L) (Rh := Rh)
    refine ⟨φ.toRingEquiv.trans e, fun y ↦ ?_⟩
    change e (φ (algebraMap (ResidueField R) L' (residue R y))) = _
    rw [φ.commutes]
    exact he y

/-- A ring isomorphic to a henselization of `R`, over `R`, is a henselization of `R`. -/
theorem of_ringEquiv {R : Type u} [CommRing R] [IsLocalRing R]
    {L : Type v} [Field L] [Algebra (ResidueField R) L]
    {Rh : Type*} [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh] [IsHenselization R L Rh]
    {Rh' : Type*} [CommRing Rh'] [IsLocalRing Rh'] [Algebra R Rh'] (ψ : Rh ≃+* Rh')
    (hψ : ∀ r : R, ψ (algebraMap R Rh r) = algebraMap R Rh' r) :
    IsHenselization R L Rh' := by
  have : HenselianLocalRing Rh := IsHenselization.henselian (R := R) (L := L) (Rh := Rh)
  have hloc : IsLocalHom (ψ : Rh →+* Rh') := IsLocalHom.of_surjective _ ψ.surjective
  refine ⟨HenselianLocalRing.of_ringEquiv ψ,
    StacksDraft.indEtale_of_equiv (RingEquiv.refl R) ψ hψ
      (IsHenselization.ind_etale (R := R) (L := L) (Rh := Rh)), ?_⟩
  obtain ⟨e, he⟩ := IsHenselization.exists_residueFieldEquiv (R := R) (L := L) (Rh := Rh)
  refine ⟨e.trans (ResidueField.mapEquiv (ψ : Rh ≃+* Rh')), fun y ↦ ?_⟩
  change ResidueField.mapEquiv (ψ : Rh ≃+* Rh') (e _) = _
  rw [he y]
  change ResidueField.map (ψ : Rh →+* Rh') (residue Rh (algebraMap R Rh y)) = _
  rw [ResidueField.map_residue]
  exact congrArg (residue Rh') (hψ y)

/-- **Functoriality of the strict henselization along a local ring map** (Stacks 0BSK). Let
`θ : A ⟶ A'` be a local homomorphism of local rings, let `Ash` be a henselization of `A` with
respect to a separable algebraic closure `κA` of its residue field, and let `A'sh` be one of `A'`
with respect to `κA'`. Then some local homomorphism `Ash ⟶ A'sh` lies over `θ`.

The map is not unique: it depends on a choice of embedding `κA ⟶ κA'` over the residue field of
`A`, which exists because `κA'` is separably closed and `κA` is separable over that residue
field. Once the embedding is fixed the map is unique, by Stacks 04GU. -/
theorem exists_isLocalHom_comp_of_isSepClosure
    {A : Type*} [CommRing A] [IsLocalRing A] {A' : Type*} [CommRing A'] [IsLocalRing A']
    (θ : A →+* A') [IsLocalHom θ]
    {κA : Type*} [Field κA] [Algebra (ResidueField A) κA] [IsSepClosure (ResidueField A) κA]
    {κA' : Type*} [Field κA'] [Algebra (ResidueField A') κA']
    [IsSepClosure (ResidueField A') κA']
    {Ash : Type*} [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash] [IsHenselization A κA Ash]
    {A'sh : Type*} [CommRing A'sh] [IsLocalRing A'sh] [Algebra A' A'sh]
    [IsHenselization A' κA' A'sh] :
    ∃ ψ : Ash →+* A'sh,
      IsLocalHom ψ ∧ ψ.comp (algebraMap A Ash) = (algebraMap A' A'sh).comp θ := by
  letI : Algebra A A'sh := ((algebraMap A' A'sh).comp θ).toAlgebra
  letI : Algebra (ResidueField A) κA' :=
    ((algebraMap (ResidueField A') κA').comp (ResidueField.map θ)).toAlgebra
  haveI : IsSepClosed κA' := IsSepClosure.sep_closed (ResidueField A')
  haveI : HenselianLocalRing A'sh :=
    IsHenselization.henselian (R := A') (L := κA') (Rh := A'sh)
  obtain ⟨eA, heA⟩ :=
    IsHenselization.exists_residueFieldEquiv (R := A) (L := κA) (Rh := Ash)
  obtain ⟨eA', heA'⟩ :=
    IsHenselization.exists_residueFieldEquiv (R := A') (L := κA') (Rh := A'sh)
  let lam : κA →ₐ[ResidueField A] κA' := IsSepClosed.lift
  have hres : (eA'.toRingHom.comp (lam.toRingHom.comp eA.symm.toRingHom)).comp
        ((residue Ash).comp (algebraMap A Ash)) =
      (residue A'sh).comp (algebraMap A A'sh) := by
    refine RingHom.ext fun a ↦ ?_
    change eA' (lam (eA.symm (residue Ash (algebraMap A Ash a)))) = _
    rw [← heA a, eA.symm_apply_apply, lam.commutes]
    change eA' (algebraMap (ResidueField A') κA' (ResidueField.map θ (residue A a))) = _
    rw [ResidueField.map_residue, heA' (θ a)]
    rfl
  obtain ⟨ψ, hψ, -⟩ := StacksDraft.existsUnique_isLocalHom_comp_residue_of_indEtale
    (A := A) (B := Ash) (C := A'sh)
    (StacksDraft.indEtale_of_isHenselization κA) _ hres
  exact ⟨ψ.toRingHom, ⟨hψ.1.map_nonunit⟩, RingHom.ext fun a ↦ ψ.commutes a⟩

end IsLocalRing.IsHenselization

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)

include hX

/-- **Stacks 04KF, with the structure map named.** The étale local ring of an algebraic space at
a geometric point `x̄` is a strict henselization of the local ring `𝒪_{U, u}` of a scheme chart
at the point under the chosen lift, *along the canonical map of Stacks 05VP*
`AlgebraicGeometry.Space.chartLocalRingToEtaleLocalRing`, with the separable closure of the
residue field of `𝒪_{U, u}` inside the residue field of the geometric point as the residue
extension.

This is the form `AlgebraicGeometry.Space.exists_algebra_isHenselization_etaleLocalRing_chart`
is proved from: there the algebra structure is produced existentially and an arbitrary chosen
separable closure is matched to this one by uniqueness of separable closures, which is all the
residue extension is used for. Naming the structure map is what lets a statement about
`𝒪_{U, u} → 𝒪_{X, x̄}` — flatness, locality, lengths, orders of vanishing — be read off the
henselization. -/
@[stacks 04KF "the étale local ring is a strict henselization of a neighborhood stalk along the
canonical map of Stacks 05VP", sga "4½ Arcata 2.3.1" "partial, special case"]
theorem isHenselization_chartLocalRingToEtaleLocalRing {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) :
    @IsHenselization ↥(chartLocalRing B S hS X V) _ _
      (separableClosure (ResidueField ↥(chartLocalRing B S hS X V))
        (chartGeometricPoint V).residueField) _ _
      (etaleLocalRing B S hS X x : Type (u + 1)) _
      (isLocalRing_etaleLocalRing B S hS X hX x)
      (chartLocalRingToEtaleLocalRing B S hS X hX V).toAlgebra :=
  letI : IsLocalRing (etaleLocalRing B S hS X x : Type (u + 1)) :=
    isLocalRing_etaleLocalRing B S hS X hX x
  letI : Algebra ↥(chartLocalRing B S hS X V)
      (etaleLocalRing B S hS X x : Type (u + 1)) :=
    (chartLocalRingToEtaleLocalRing B S hS X hX V).toAlgebra
  IsHenselization.of_ringEquiv (chartStrictHenselizationEquiv B S hS X hX V) fun _ ↦ rfl

/-- **Stacks 04KF.** The étale local ring of an algebraic space at a geometric point is a strict
henselization of the local ring of a scheme chart at the point under the chosen lift, for every
chosen separable algebraic closure of the residue field of that local ring. The algebra
structure is the canonical map of Stacks 05VP. -/
@[stacks 04KF "the étale local ring is a strict henselization of a neighborhood stalk",
  sga "4½ Arcata 2.3.1" "special case"]
theorem exists_algebra_isHenselization_etaleLocalRing_chart {x : GeometricPoint B S hS X}
    (V : SmallEtaleNeighborhood x) (p : chartScheme V.chart)
    (hp : chartPoint B S hS X V = p)
    (κsep : Type u) [Field κsep]
    [Algebra (ResidueField ((chartScheme V.chart).presheaf.stalk p : Type u)) κsep]
    [IsSepClosure (ResidueField ((chartScheme V.chart).presheaf.stalk p : Type u)) κsep] :
    letI : IsLocalRing (etaleLocalRing B S hS X x : Type (u + 1)) :=
      isLocalRing_etaleLocalRing B S hS X hX x
    ∃ alg : Algebra ((chartScheme V.chart).presheaf.stalk p : Type u)
        (etaleLocalRing B S hS X x : Type (u + 1)),
      @IsHenselization ((chartScheme V.chart).presheaf.stalk p : Type u) _ _ κsep _ _
        (etaleLocalRing B S hS X x : Type (u + 1)) _
        (isLocalRing_etaleLocalRing B S hS X hX x) alg := by
  subst hp
  letI : IsLocalRing (etaleLocalRing B S hS X x : Type (u + 1)) :=
    isLocalRing_etaleLocalRing B S hS X hX x
  letI algE : Algebra ↥(chartLocalRing B S hS X V)
      (etaleLocalRing B S hS X x : Type (u + 1)) :=
    (chartLocalRingToEtaleLocalRing B S hS X hX V).toAlgebra
  refine ⟨algE, ?_⟩
  letI : IsHenselization ↥(chartLocalRing B S hS X V)
      (separableClosure (ResidueField ↥(chartLocalRing B S hS X V))
        (chartGeometricPoint V).residueField)
      (etaleLocalRing B S hS X x : Type (u + 1)) :=
    isHenselization_chartLocalRingToEtaleLocalRing B S hS X hX V
  exact IsHenselization.of_algEquiv
    (IsSepClosure.equiv (ResidueField ↥(chartLocalRing B S hS X V)) κsep
      (separableClosure (ResidueField ↥(chartLocalRing B S hS X V))
        (chartGeometricPoint V).residueField))

/-- **The étale local ring of an algebraic space is strictly henselian.** At every geometric
point it is a strict henselization of the local ring of a scheme chart (Stacks 04KF), hence a
henselian local ring whose residue field is a separable algebraic closure. -/
@[sga "4½ Arcata 2.3.1" "partial"]
theorem strictlyHenselianLocalRing_etaleLocalRing (x : GeometricPoint B S hS X) :
    StrictlyHenselianLocalRing (etaleLocalRing B S hS X x : Type (u + 1)) := by
  have : IsCofiltered (SmallEtaleNeighborhood x) :=
    isCofiltered_smallEtaleNeighborhood B S hS X hX x
  have : Nonempty (SmallEtaleNeighborhood x) := IsCofiltered.nonempty
  let V : SmallEtaleNeighborhood x := Classical.arbitrary _
  let R := ((chartScheme V.chart).presheaf.stalk (chartPoint B S hS X V) : Type u)
  letI : IsLocalRing (etaleLocalRing B S hS X x : Type (u + 1)) :=
    isLocalRing_etaleLocalRing B S hS X hX x
  obtain ⟨alg, hV⟩ := exists_algebra_isHenselization_etaleLocalRing_chart B S hS X hX V
    (chartPoint B S hS X V) rfl (SeparableClosure (ResidueField R))
  letI := alg
  have hH : HenselianLocalRing (etaleLocalRing B S hS X x : Type (u + 1)) :=
    IsHenselization.henselian (R := R) (L := SeparableClosure (ResidueField R))
  obtain ⟨e, -⟩ := IsHenselization.exists_residueFieldEquiv (R := R)
    (L := SeparableClosure (ResidueField R)) (Rh := (etaleLocalRing B S hS X x : Type (u + 1)))
  have : IsSepClosed (ResidueField (etaleLocalRing B S hS X x : Type (u + 1))) :=
    IsSepClosed.of_ringEquiv e.symm
  exact ⟨⟩

variable {x : points B S hS X} (U : ElementaryEtaleNeighborhood B S hS X hX x)
  (xbar : GeometricPoint B S hS X)

/-- The point of the chart scheme at which the stalk of the small étale neighborhood determined
by an elementary étale neighborhood is taken is the distinguished point of that neighborhood:
the lift of the geometric point factors through the residue-field point of it. -/
theorem chartPoint_smallEtaleNeighborhood (hxbar : xbar.LiesOver x) :
    chartPoint B S hS X (U.smallEtaleNeighborhood xbar hxbar) = U.point := by
  have h : (U.scheme.left.1.fromSpecResidueField U.point).base
      (((BigFppfOver.toScheme B S hS).map (U.liftResidueField xbar hxbar)).base
        (closedPoint xbar.val.carrier)) = U.point :=
    Scheme.fromSpecResidueField_apply _ _
  exact h

/-- **Stacks 04KF.** The étale local ring of an algebraic space at a geometric point `x̄` is a
strict henselization of the local ring of an elementary étale neighborhood of the point below
`x̄`, at its distinguished point, for every chosen separable algebraic closure of the residue
field of that local ring. -/
@[stacks 04KF "the étale local ring is a strict henselization of an elementary neighborhood
stalk"]
theorem exists_algebra_isHenselization_etaleLocalRing_elementary (hxbar : xbar.LiesOver x)
    (κsep : Type u) [Field κsep]
    [instAlg : Algebra (ResidueField (U.scheme.left.1.presheaf.stalk U.point : Type u)) κsep]
    [instSep : IsSepClosure (ResidueField (U.scheme.left.1.presheaf.stalk U.point : Type u))
      κsep] :
    letI : IsLocalRing (etaleLocalRing B S hS X xbar : Type (u + 1)) :=
      isLocalRing_etaleLocalRing B S hS X hX xbar
    ∃ alg : Algebra (U.scheme.left.1.presheaf.stalk U.point : Type u)
        (etaleLocalRing B S hS X xbar : Type (u + 1)),
      @IsHenselization (U.scheme.left.1.presheaf.stalk U.point : Type u) _ _ κsep _ _
        (etaleLocalRing B S hS X xbar : Type (u + 1)) _
        (isLocalRing_etaleLocalRing B S hS X hX xbar) alg :=
  @exists_algebra_isHenselization_etaleLocalRing_chart B S hS X hX xbar
    (U.smallEtaleNeighborhood xbar hxbar) U.point
    (chartPoint_smallEtaleNeighborhood B S hS X hX U xbar hxbar) κsep _ instAlg instSep

end AlgebraicGeometry.Space

end
