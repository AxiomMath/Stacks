module

public import Mathlib.RingTheory.Nullstellensatz
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Criterion
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.AffineSpaceOrbits
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.LargestOpen
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.LargestOpenEtaleSquare
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.PolynomialGeometry
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.AtPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.EtaleAffineSpace
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Examples.JacobianCriterion
public import StacksCore.Tactic.StacksAttribute

/-!
# The largest open locus in a square with smooth target morphism

Let `P` be a property of morphisms of schemes which is étale local on the source, smooth local
on the target, and stable under postcomposing with open immersions. In a commutative square of
schemes whose right vertical morphism is smooth at the relevant point and whose comparison
morphism to the fibre product is étale at the chosen point of the upper-left scheme, the two
source points lie in their respective largest open loci of `P` simultaneously.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.mem_largestOpen_iff_of_smoothAt_etaleAt` is this pointwise equivalence.

## Implementation notes

Étale locality on the source is `CategoryTheory.MorphismProperty.IsLocalAtSource` for
`AlgebraicGeometry.Scheme.etalePrecoverage`, smooth locality on the target is
`CategoryTheory.MorphismProperty.IsLocalAtTarget` for the precoverage of smooth morphisms, and
stability under postcomposing with open immersions is
`CategoryTheory.MorphismProperty.RespectsRight` for `AlgebraicGeometry.IsOpenImmersion`. The
last of these is stated for an arbitrary open immersion rather than for the inclusion of an open
subscheme; the two agree because a property local on the source is invariant under isomorphisms.

The points of the lower-left and upper-right schemes are the images of the chosen point of the
upper-left scheme, so only that one point is given. The comparison morphism to the fibre product
is `CategoryTheory.Limits.pullback.lift` applied to the commutative square.

The reduction to a cartesian square and the transport across an étale comparison morphism both
come from `AlgebraicGeometry.mem_largestOpen_iff_of_etaleAt`, which applies because the three
hypotheses on `P` make it étale local on the source and target by
`AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_of_isLocalAtSource_isLocalAtTarget`, étale
coverings being smooth coverings. For the remaining implication the target is covered by affine
spaces: after shrinking the upper-right scheme, smoothness at the point gives an étale morphism
to an affine space over the lower-right scheme, and the problem becomes the claim that the
largest open locus of the induced morphism of affine spaces over the lower-left scheme is
everything. That claim is settled fibrewise: the elementary coordinate shears and the morphism
with coordinates `xᵢ - xᵢ ^ p` are automorphisms, respectively étale morphisms, commuting with
the morphism of affine spaces, so they preserve the locus, and
`MvPolynomial.eq_univ_or_finite_compl_of_invariant_coordinateShear` leaves only the full fibre as
a possibility. The case of one coordinate is reduced to the case of two by pulling back along the
projection, and the case of no coordinates is the hypothesis itself.

## References

* [Stacks Project, Tag 0CF1](https://stacks.math.columbia.edu/tag/0CF1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry


/-- A point lies in the largest open locus of a property exactly when some open
neighbourhood of it is a locus for that property. -/
private lemma mem_largestOpen_iff_exists_open
    (P : MorphismProperty Scheme.{u}) {X Y : Scheme.{u}}
    (f : X ⟶ Y) (x : X) :
    x ∈ AlgebraicGeometry.largestOpen P f ↔
      ∃ U : X.Opens, x ∈ U ∧ P (U.ι ≫ f) := by
  simp [AlgebraicGeometry.largestOpen, and_comm]

/-- A property étale local on the source, smooth local on the target and stable under
postcomposing with open immersions is étale local on the source and target. -/
private lemma isEtaleLocalOnSourceAndTarget_of_smoothLocalAtTarget
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    [P.IsLocalAtTarget
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})] :
    IsEtaleLocalOnSourceAndTarget P := by
  let : P.IsLocalAtTarget Scheme.etalePrecoverage :=
    MorphismProperty.IsLocalAtTarget.of_le
      (Scheme.precoverage_mono (P := @Etale) (Q := @Smooth)
        (fun _ _ _ he => by
          have : Etale _ := he
          infer_instance))
  exact AlgebraicGeometry.isEtaleLocalOnSourceAndTarget_of_isLocalAtSource_isLocalAtTarget P

/-- Membership in the largest open locus is unchanged along a commutative square whose
horizontal morphisms are étale. -/
private lemma mem_largestOpen_iff_of_etale
    (P : MorphismProperty Scheme.{u}) (hP : IsEtaleLocalOnSourceAndTarget P)
    {X' X Y' Y : Scheme.{u}} (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    [Etale g] [Etale g'] (hcomm : g' ≫ f = f' ≫ g) (x' : X') :
    g'.base x' ∈ AlgebraicGeometry.largestOpen P f ↔
      x' ∈ AlgebraicGeometry.largestOpen P f' :=
  AlgebraicGeometry.mem_largestOpen_iff_of_etaleAt P hP f f' g g' hcomm x'
    ((etale_iff_forall_etaleAt g').mp inferInstance x')
    ((etale_iff_forall_etaleAt g).mp inferInstance (f'.base x'))

/-- Affine space over an open subscheme is an open subscheme of affine space, so the induced
map is étale. -/
private lemma etale_affineSpace_map_of_openImmersion {S T : Scheme.{u}}
    (j : S ⟶ T) [IsOpenImmersion j] (n : Type u) : Etale (AffineSpace.map n j) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (AffineSpace.isPullback_map (n := n) j).flip inferInstance

/-- A property local on the target for the smooth topology is preserved by base change
along a smooth morphism. -/
private lemma pullback_snd_of_smooth_local
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]
    {A B C : Scheme.{u}} (f : A ⟶ B) (g : C ⟶ B)
    [Smooth g] (hf : P f) : P (pullback.snd f g) := by
  let Z : Bool → Scheme.{u} := fun b => if b then C else B
  let a : (b : Bool) → Z b ⟶ B := fun b => by
    cases b
    · exact 𝟙 B
    · exact g
  have hcover : Presieve.ofArrows Z a ∈
      Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}) B := by
    rw [Scheme.ofArrows_mem_precoverage_iff
      (@Smooth : MorphismProperty Scheme.{u})]
    refine ⟨fun y => ⟨false, y, by simp [Z, a]⟩, fun b => ?_⟩
    cases b
    · change Smooth (𝟙 B)
      infer_instance
    · simpa [a] using (show Smooth g from inferInstance)
  exact MorphismProperty.IsLocalAtTarget.pullbackSnd hcover (⟨true⟩ : Presieve.ofArrows Z a g) hf

/-- In a cartesian square whose base morphism is smooth, the inverse image of the largest
open locus downstairs is contained in the largest open locus upstairs. -/
private lemma preimage_largestOpen_le_of_smooth_isPullback
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    [P.IsLocalAtTarget (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (h : IsPullback a b f g) [Smooth g] :
    a ⁻¹ᵁ AlgebraicGeometry.largestOpen P f ≤ AlgebraicGeometry.largestOpen P b := by
  let U := AlgebraicGeometry.largestOpen P f
  have hU : P (U.ι ≫ f) := (AlgebraicGeometry.largestOpen_isGreatest_etale P f).1
  have hp := (isPullback_morphismRestrict a U).paste_vert h
  have hV : P ((a ⁻¹ᵁ U).ι ≫ b) := by
    rw [← hp.isoPullback_hom_snd]
    exact (P.cancel_left_of_respectsIso hp.isoPullback.hom _).mpr
      (pullback_snd_of_smooth_local P (U.ι ≫ f) g hU)
  exact (AlgebraicGeometry.largestOpen_isGreatest_etale P b).2 hV

/-- A pair of automorphisms of the source and the target commuting with a morphism
preserves its largest open locus. -/
private lemma largestOpen_invariant_under_iso
    (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (eX : X ≅ X) (eY : Y ≅ Y)
    (hcomm : eX.hom ≫ f = f ≫ eY.hom) :
    eX.hom ⁻¹ᵁ AlgebraicGeometry.largestOpen P f = AlgebraicGeometry.largestOpen P f := by
  ext x
  change eX.hom.base x ∈ AlgebraicGeometry.largestOpen P f ↔
    x ∈ AlgebraicGeometry.largestOpen P f
  exact mem_largestOpen_iff_of_etale P hP f f eY.hom eX.hom hcomm x

/-- The largest open locus of the induced morphism of affine spaces is invariant under every
elementary coordinate shear. -/
private lemma affineSpace_largestOpen_invariant_under_coordinateShear
    (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) {n : Type u} [DecidableEq n]
    (i j : n) (hij : i ≠ j) (d : ℕ) :
    affineSpaceCoordinateShear i j hij d ⁻¹ᵁ
        AlgebraicGeometry.largestOpen P (AffineSpace.map n f) =
      AlgebraicGeometry.largestOpen P (AffineSpace.map n f) :=
  largestOpen_invariant_under_iso P hP (AffineSpace.map n f)
    (affineSpaceCoordinateShearIso i j hij d)
    (affineSpaceCoordinateShearIso i j hij d)
    (affineSpace_map_comm_coordinateShear f i j hij d).symm

/-- The fibre over a point of the base of the largest open locus of the induced morphism of
affine spaces, viewed as an open of affine space over the residue field of that point. -/
private noncomputable def affineSpace_fiber_largestOpen
    (P : MorphismProperty Scheme.{u})
    {X Y : Scheme.{u}} {n : Type u}
    (f : X ⟶ Y) (x : X) :
    (AffineSpace n (Spec (X.residueField x))).Opens :=
  (AffineSpace.map n (X.fromSpecResidueField x)) ⁻¹ᵁ
    AlgebraicGeometry.largestOpen P (AffineSpace.map n f)

/-- The fibre of the largest open locus is invariant under an endomorphism of affine space over
the residue field which commutes with an endomorphism of affine space over `X` preserving the
locus on the image of the fibre. -/
private lemma affineSpace_fiber_largestOpen_preimage_eq
    (P : MorphismProperty Scheme.{u})
    {X Y : Scheme.{u}} {n : Type u} (f : X ⟶ Y) (x : X)
    (φ : AffineSpace n (Spec (X.residueField x)) ⟶ AffineSpace n (Spec (X.residueField x)))
    (ψ : AffineSpace n X ⟶ AffineSpace n X)
    (hcomm : AffineSpace.map n (X.fromSpecResidueField x) ≫ ψ =
      φ ≫ AffineSpace.map n (X.fromSpecResidueField x))
    (h : ∀ z : AffineSpace n (Spec (X.residueField x)),
      ψ.base ((AffineSpace.map n (X.fromSpecResidueField x)).base z) ∈
          AlgebraicGeometry.largestOpen P (AffineSpace.map n f) ↔
        (AffineSpace.map n (X.fromSpecResidueField x)).base z ∈
          AlgebraicGeometry.largestOpen P (AffineSpace.map n f)) :
    φ ⁻¹ᵁ affineSpace_fiber_largestOpen P f x = affineSpace_fiber_largestOpen P f x := by
  ext z
  have hpoint : (AffineSpace.map n (X.fromSpecResidueField x)).base (φ.base z) =
      ψ.base ((AffineSpace.map n (X.fromSpecResidueField x)).base z) := by
    simpa using (congrArg
      (fun k : AffineSpace n (Spec (X.residueField x)) ⟶ AffineSpace n X => k.base z) hcomm).symm
  change (AffineSpace.map n (X.fromSpecResidueField x)).base (φ.base z) ∈
      AlgebraicGeometry.largestOpen P (AffineSpace.map n f) ↔
    (AffineSpace.map n (X.fromSpecResidueField x)).base z ∈
      AlgebraicGeometry.largestOpen P (AffineSpace.map n f)
  rw [hpoint]
  exact h z

/-- The fibre of the largest open locus is invariant under every elementary coordinate
shear. -/
private lemma affineSpace_fiber_largestOpen_shear_preimage
    (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y : Scheme.{u}} {n : Type u} [DecidableEq n]
    (f : X ⟶ Y) (x : X)
    (i j : n) (hij : i ≠ j) (d : ℕ) :
    affineSpaceCoordinateShear i j hij d ⁻¹ᵁ
        affineSpace_fiber_largestOpen P f x =
      affineSpace_fiber_largestOpen P f x :=
  affineSpace_fiber_largestOpen_preimage_eq P f x _ _
    (affineSpace_map_comm_coordinateShear (X.fromSpecResidueField x) i j hij d) fun z => by
    simpa using congrArg
      (fun U : (AffineSpace n X).Opens =>
        (AffineSpace.map n (X.fromSpecResidueField x)).base z ∈ U)
      (affineSpace_largestOpen_invariant_under_coordinateShear P hP f i j hij d)

/-- For `d ≥ 2`, a nonempty fibre of the largest open locus which in positive characteristic
is invariant under the endomorphism with coordinates `xᵢ - xᵢ ^ p` for `p` the
characteristic is all of affine space over the residue field. -/
private lemma affineSpace_fiber_largestOpen_eq_top_of_sub_pow_invariant
    (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (d : ℕ) (hd : 2 ≤ d)
    (hnonempty : Nonempty (affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) P f x))
    (hfrob : 0 < ringChar (X.residueField x) →
      affineSpaceSubPow (ringChar (X.residueField x)) ⁻¹ᵁ
        affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) P f x =
        affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) P f x) :
    affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) P f x = ⊤ := by
  classical
  let U := affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) P f x
  let e := AffineSpace.SpecIso (ULift.{u} (Fin d)) (X.residueField x)
  let W : Set (PrimeSpectrum
      (MvPolynomial (ULift.{u} (Fin d)) (↑(X.residueField x)))) :=
    (e.inv ⁻¹ᵁ U).carrier
  have hopen : IsOpen W := U.2.preimage e.inv.continuous
  have he : ∀ z, e.inv.base (e.hom.base z) = z := by simp [e]
  have hnonemptyW : W.Nonempty := by
    obtain ⟨z, hz⟩ := hnonempty
    refine ⟨e.hom.base z, ?_⟩
    change e.inv.base (e.hom.base z) ∈ U
    rwa [he]
  have hWpre : ∀ (φ : MvPolynomial (ULift.{u} (Fin d)) (↑(X.residueField x)) →+*
        MvPolynomial (ULift.{u} (Fin d)) (↑(X.residueField x)))
      (ψ : AffineSpace (ULift.{u} (Fin d)) (Spec (X.residueField x)) ⟶
        AffineSpace (ULift.{u} (Fin d)) (Spec (X.residueField x))),
      Spec.map (CommRingCat.ofHom φ) ≫ e.inv = e.inv ≫ ψ → ψ ⁻¹ᵁ U = U →
        PrimeSpectrum.comap φ ⁻¹' W = W := by
    intro φ ψ hcomm hψ
    ext q
    change e.inv.base ((Spec.map (CommRingCat.ofHom φ)).base q) ∈ U ↔ e.inv.base q ∈ U
    rw [show e.inv.base ((Spec.map (CommRingCat.ofHom φ)).base q) =
      ψ.base (e.inv.base q) from congrArg (fun g => g.base q) hcomm]
    exact Iff.of_eq (congrArg (fun V => e.inv.base q ∈ V) hψ)
  have hWinv : ∀ (i j : Fin d) (hij : i ≠ j) (r : ℕ),
      PrimeSpectrum.comap
        (coordinateShearULift (R := ↑(X.residueField x)) i j hij r).toRingHom ⁻¹' W = W :=
    fun i j hij r => hWpre _ _
      (affineSpace_fiberSpecIso_inv_shear (.of (X.residueField x)) d i j hij r)
      (affineSpace_fiber_largestOpen_shear_preimage P hP f x (ULift.up i) (ULift.up j)
        (fun h => hij (congrArg ULift.down h)) r)
  have hfrobW : 0 < ringChar (X.residueField x) → PrimeSpectrum.comap
      (MvPolynomial.aeval (R := ↑(X.residueField x))
        (fun i : ULift.{u} (Fin d) => MvPolynomial.X i -
          MvPolynomial.X i ^ ringChar (X.residueField x))).toRingHom ⁻¹' W = W :=
    fun hchar => hWpre _ _
      (affineSpace_specIso_inv_sub_pow (X.residueField x) (ULift.{u} (Fin d))
        (ringChar (X.residueField x))) (hfrob hchar)
  have hfull := affineOpen_eq_univ_of_shear_and_sub_pow_invariant_ulift
    d hd W hopen hnonemptyW hWinv hfrobW
  apply top_unique
  intro z _
  have hz : e.hom.base z ∈ W := by rw [hfull]; trivial
  change e.inv.base (e.hom.base z) ∈ U at hz
  rwa [he] at hz

/-- If the endomorphism with coordinates `xᵢ - xᵢ ^ p` is étale at a point of affine space
and at its image, it does not change membership in the largest open locus. -/
private lemma largestOpen_mem_iff_of_subPow_etaleAt
    (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) {n : Type u}
    (p : ℕ) (x : AffineSpace n X)
    (hx : EtaleAt (affineSpaceSubPow p) x)
    (hfx : EtaleAt (affineSpaceSubPow p)
      ((AffineSpace.map n f).base x)) :
    (affineSpaceSubPow p).base x ∈
        AlgebraicGeometry.largestOpen P (AffineSpace.map n f) ↔
      x ∈ AlgebraicGeometry.largestOpen P (AffineSpace.map n f) :=
  AlgebraicGeometry.mem_largestOpen_iff_of_etaleAt P hP
    (AffineSpace.map n f) (AffineSpace.map n f)
    (affineSpaceSubPow p) (affineSpaceSubPow p)
    (affineSpace_map_comm_subPow f p).symm x hx hfx

/-- The fibre of the largest open locus over a point is invariant under the endomorphism
with coordinates `xᵢ - xᵢ ^ p` as soon as the latter is étale along the two fibres
involved. -/
private lemma affineSpace_fiber_largestOpen_subPow_preimage
    (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y : Scheme.{u}} {n : Type u}
    (f : X ⟶ Y) (x : X) (p : ℕ)
    (htarget : ∀ z : AffineSpace n X,
      (AffineSpace n X ↘ X).base z = x →
        EtaleAt (affineSpaceSubPow p) z)
    (htargetY : ∀ z : AffineSpace n Y,
      (AffineSpace n Y ↘ Y).base z = f.base x →
        EtaleAt (affineSpaceSubPow p) z) :
    affineSpaceSubPow p ⁻¹ᵁ affineSpace_fiber_largestOpen (n := n) P f x =
      affineSpace_fiber_largestOpen (n := n) P f x := by
  refine affineSpace_fiber_largestOpen_preimage_eq P f x _ _
    (affineSpace_map_comm_subPow (n := n) (X.fromSpecResidueField x) p) fun z => ?_
  have hbase : (AffineSpace n X ↘ X).base
      ((AffineSpace.map n (X.fromSpecResidueField x)).base z) = x :=
    calc
      (AffineSpace n X ↘ X).base ((AffineSpace.map n
          (X.fromSpecResidueField x)).base z) =
          (X.fromSpecResidueField x).base
            ((AffineSpace n (Spec (X.residueField x)) ↘
              Spec (X.residueField x)).base z) :=
        congrArg (fun k : AffineSpace n (Spec (X.residueField x)) ⟶ X => k.base z)
          (AffineSpace.map_over (n := n) (X.fromSpecResidueField x))
      _ = x := Scheme.fromSpecResidueField_apply x _
  exact largestOpen_mem_iff_of_subPow_etaleAt P hP f p
    ((AffineSpace.map n (X.fromSpecResidueField x)).base z)
    (htarget ((AffineSpace.map n (X.fromSpecResidueField x)).base z) hbase)
    (htargetY ((AffineSpace.map n f).base
      ((AffineSpace.map n (X.fromSpecResidueField x)).base z)) (by
      calc
        (AffineSpace n Y ↘ Y).base ((AffineSpace.map n f).base
            ((AffineSpace.map n (X.fromSpecResidueField x)).base z)) =
            f.base ((AffineSpace n X ↘ X).base
              ((AffineSpace.map n (X.fromSpecResidueField x)).base z)) :=
          congrArg (fun k : AffineSpace n X ⟶ Y =>
            k.base ((AffineSpace.map n (X.fromSpecResidueField x)).base z))
              (AffineSpace.map_over (n := n) f)
        _ = f.base x := congrArg f.base hbase))

/-- For `d ≥ 2`, a nonempty fibre of the largest open locus over a point of the base is all
of affine space over the residue field of that point. -/
private lemma affineSpace_fiber_largestOpen_eq_top
    (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) (d : ℕ) (hd : 2 ≤ d)
    (hnonempty : Nonempty (affineSpace_fiber_largestOpen
      (n := ULift.{u} (Fin d)) P f x)) :
    affineSpace_fiber_largestOpen (n := ULift.{u} (Fin d)) P f x = ⊤ := by
  apply affineSpace_fiber_largestOpen_eq_top_of_sub_pow_invariant P hP f x d hd hnonempty
  intro _
  apply affineSpace_fiber_largestOpen_subPow_preimage P hP f x
  · intro z hz
    apply affineSpace_subPow_etaleAt
    rw [hz]
    exact CharP.cast_eq_zero _ _
  · intro z hz
    apply affineSpace_subPow_etaleAt
    rw [hz]
    apply (f.residueFieldMap x).hom.injective
    simp

/-- For `d ≥ 2`, the largest open locus of the induced morphism of affine spaces contains the
whole fibre of each of its points. -/
private lemma affineSpace_largestOpen_saturated
    (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) (hd : 2 ≤ d)
    (z w : AffineSpace (ULift.{u} (Fin d)) X)
    (he : (AffineSpace (ULift.{u} (Fin d)) X ↘ X) z =
      (AffineSpace (ULift.{u} (Fin d)) X ↘ X) w)
    (hz : z ∈ AlgebraicGeometry.largestOpen P (AffineSpace.map (ULift.{u} (Fin d)) f)) :
    w ∈ AlgebraicGeometry.largestOpen P (AffineSpace.map (ULift.{u} (Fin d)) f) := by
  let x := (AffineSpace (ULift.{u} (Fin d)) X ↘ X) w
  have hzlift := affineSpace_exists_fiber_point z
  rw [he] at hzlift
  obtain ⟨z', hz'⟩ := hzlift
  obtain ⟨w', hw'⟩ := affineSpace_exists_fiber_point w
  have hn : Nonempty (affineSpace_fiber_largestOpen
      (n := ULift.{u} (Fin d)) P f x) := by
    refine ⟨z', ?_⟩
    change (AffineSpace.map _ (X.fromSpecResidueField x)) z' ∈
      AlgebraicGeometry.largestOpen P (AffineSpace.map _ f)
    rwa [hz']
  have hw : w' ∈ affineSpace_fiber_largestOpen
      (n := ULift.{u} (Fin d)) P f x :=
    (affineSpace_fiber_largestOpen_eq_top P hP f x d hd hn).ge trivial
  change (AffineSpace.map _ (X.fromSpecResidueField x)) w' ∈
    AlgebraicGeometry.largestOpen P (AffineSpace.map _ f) at hw
  rwa [hw'] at hw

/-- A property local on the target for the smooth topology descends along a surjective
smooth base change. -/
private lemma of_smooth_surjective_isPullback
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtTarget (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (h : IsPullback a b f g)
    [Smooth g] [Surjective g] (hb : P b) : P f := by
  have hc : Presieve.ofArrows (fun _ : Unit => Y') (fun _ => g) ∈
      Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}) Y := by
    rw [Scheme.ofArrows_mem_precoverage_iff (P := @Smooth)]
    exact ⟨fun y => ⟨(), g.surjective y⟩, fun _ => inferInstance⟩
  apply MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hc
  rintro _ _ _ ⟨i⟩
  rw [← h.isoPullback_inv_snd]
  exact (P.cancel_left_of_respectsIso h.isoPullback.inv _).mpr hb

/-- For `d ≥ 2`, the image in `X` of the largest open locus of the induced morphism of affine
`d`-spaces lies in the largest open locus of the original morphism. -/
private lemma mem_largestOpen_of_affineSpace
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    [P.IsLocalAtTarget (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) (hd : 2 ≤ d)
    (z : AffineSpace (ULift.{u} (Fin d)) X)
    (hz : z ∈ AlgebraicGeometry.largestOpen P (AffineSpace.map (ULift.{u} (Fin d)) f)) :
    (AffineSpace (ULift.{u} (Fin d)) X ↘ X) z ∈ AlgebraicGeometry.largestOpen P f := by
  let n := ULift.{u} (Fin d)
  let W := AlgebraicGeometry.largestOpen P (AffineSpace.map n f)
  let q := (AffineSpace n X ↘ X)
  let U : X.Opens := ⟨q '' (W : Set (AffineSpace n X)),
    AffineSpace.isOpenMap_over (n := n) X W W.isOpen⟩
  apply (mem_largestOpen_iff_exists_open P f (q z)).mpr
  refine ⟨U, ⟨z, hz, rfl⟩, ?_⟩
  have : Smooth (AffineSpace n Y ↘ Y) := affineSpace_smooth_over
  apply of_smooth_surjective_isPullback P (AffineSpace.isPullback_map (n := n) (U.ι ≫ f)).flip
  have := etale_affineSpace_map_of_openImmersion U.ι n
  have hall : AlgebraicGeometry.largestOpen P (AffineSpace.map n (U.ι ≫ f)) = ⊤ := by
    apply top_unique
    intro w _
    rw [AffineSpace.map_comp, ← AlgebraicGeometry.preimage_largestOpen_etale]
    change (AffineSpace.map n U.ι) w ∈ W
    have hw : q ((AffineSpace.map n U.ι) w) ∈ U := by
      have he := congrArg (fun k => k w) (AffineSpace.map_over (n := n) U.ι)
      change q ((AffineSpace.map n U.ι) w) = U.ι ((AffineSpace n U.toScheme ↘ U.toScheme) w) at he
      rw [he]
      exact ((AffineSpace n U.toScheme ↘ U.toScheme) w).property
    obtain ⟨v, hv, he⟩ := hw
    exact affineSpace_largestOpen_saturated P
      (isEtaleLocalOnSourceAndTarget_of_smoothLocalAtTarget P) f d hd v
      ((AffineSpace.map n U.ι) w) he hv
  have hp := (AlgebraicGeometry.largestOpen_isGreatest_etale P
    (AffineSpace.map n (U.ι ≫ f))).1
  rw [hall] at hp
  change P ((AffineSpace n U.toScheme).topIso.hom ≫ AffineSpace.map n (U.ι ≫ f)) at hp
  exact (P.cancel_left_of_respectsIso (AffineSpace n U.toScheme).topIso.hom _).mp hp


/-- For every `d`, the image in `X` of the largest open locus of the induced morphism of
affine `d`-spaces lies in the largest open locus of the original morphism. -/
private lemma mem_largestOpen_of_affineSpace_any
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    [P.IsLocalAtTarget (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    (z : AffineSpace (ULift.{u} (Fin d)) X)
    (hz : z ∈ AlgebraicGeometry.largestOpen P (AffineSpace.map (ULift.{u} (Fin d)) f)) :
    (AffineSpace (ULift.{u} (Fin d)) X ↘ X) z ∈ AlgebraicGeometry.largestOpen P f := by
  let i := fun i : ULift.{u} (Fin d) => (ULift.up (Fin.castAdd 2 i.down) : ULift.{u} (Fin (d + 2)))
  let qX := AffineSpace.reindex i X
  let qY := AffineSpace.reindex i Y
  have hq : ∀ Z : Scheme.{u}, AffineSpace.reindex i Z = (affineSpaceAddTwoIso d Z).hom ≫
      (AffineSpace (ULift.{u} (Fin 2)) (AffineSpace (ULift.{u} (Fin d)) Z) ↘
        AffineSpace (ULift.{u} (Fin d)) Z) := fun Z => (affineSpaceAddTwoIso_hom_over d Z).symm
  have : Smooth qY := by
    rw [show qY = _ from hq Y]
    have : Smooth (AffineSpace (ULift.{u} (Fin 2))
        (AffineSpace (ULift.{u} (Fin d)) Y) ↘ AffineSpace (ULift.{u} (Fin d)) Y) :=
      affineSpace_smooth_over
    infer_instance
  have : Surjective qX := by
    rw [show qX = _ from hq X]
    infer_instance
  have h : IsPullback qX (AffineSpace.map (ULift.{u} (Fin (d + 2))) f)
      (AffineSpace.map (ULift.{u} (Fin d)) f) qY := by
    apply IsPullback.of_right _ (AffineSpace.map_reindex i f).symm
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin d)) f).flip
    simpa [qX, qY] using
      (AffineSpace.isPullback_map (n := ULift.{u} (Fin (d + 2))) f).flip
  obtain ⟨w, hw⟩ := qX.surjective z
  have hwW : w ∈ AlgebraicGeometry.largestOpen P
      (AffineSpace.map (ULift.{u} (Fin (d + 2))) f) :=
    preimage_largestOpen_le_of_smooth_isPullback P h (by simpa [hw] using hz)
  have hm := mem_largestOpen_of_affineSpace P f (d + 2) (by omega) w hwW
  have he : (AffineSpace (ULift.{u} (Fin (d + 2))) X ↘ X) w =
      (AffineSpace (ULift.{u} (Fin d)) X ↘ X) z := by
    rw [← AffineSpace.reindex_over i X]
    change (AffineSpace (ULift.{u} (Fin d)) X ↘ X) (qX w) = _
    rw [hw]
  rwa [he] at hm

/-- In a cartesian square whose base morphism is smooth at the relevant point, a point whose
image lies in the largest open locus downstairs lies in the largest open locus upstairs. -/
private lemma mem_largestOpen_of_smoothAt_isPullback
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    [P.IsLocalAtTarget (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})]
    {X' X Y' Y : Scheme.{u}} {a : X' ⟶ X} {b : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (h : IsPullback a b f g)
    (z : X') (hg : InfinitesimalLifting.SmoothAt g (b z))
    (hz : a z ∈ AlgebraicGeometry.largestOpen P f) : z ∈ AlgebraicGeometry.largestOpen P b := by
  obtain ⟨V, hzV, hV⟩ := smoothAt_has_smooth_open_neighborhood g (b z) hg
  have : Smooth (V.ι ≫ g) := hV
  let zV : (b ⁻¹ᵁ V).toScheme := ⟨z, hzV⟩
  have hz' : zV ∈ AlgebraicGeometry.largestOpen P (b ∣_ V) :=
    preimage_largestOpen_le_of_smooth_isPullback P
      ((isPullback_morphismRestrict b V).paste_vert h.flip).flip hz
  exact (mem_largestOpen_iff_of_etale P (isEtaleLocalOnSourceAndTarget_of_smoothLocalAtTarget P)
    b (b ∣_ V) V.ι (b ⁻¹ᵁ V).ι (by simp) zV).mpr hz'

/-- Membership in the largest open locus is unchanged by a comparison morphism to the fibre
product which is étale at the given point. -/
private lemma mem_largestOpen_iff_of_comparison_etaleAt
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    [P.IsLocalAtTarget
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})]
    {X' X Y' Y : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (hcomm : g' ≫ f = f' ≫ g) (x' : X')
    (hg' : EtaleAt
      (pullback.lift g' f' hcomm) x') :
    (pullback.lift g' f' hcomm).base x' ∈
        AlgebraicGeometry.largestOpen P (pullback.snd f g) ↔
      x' ∈ AlgebraicGeometry.largestOpen P f' := by
  simpa only [Category.id_comp] using AlgebraicGeometry.mem_largestOpen_iff_of_etaleAt P
    (isEtaleLocalOnSourceAndTarget_of_smoothLocalAtTarget P)
    (pullback.snd f g) f' (𝟙 Y') (pullback.lift g' f' hcomm)
    (by simp only [Category.comp_id, pullback.lift_snd]) x' hg'
    ((etale_iff_forall_etaleAt (𝟙 Y')).mp inferInstance (f'.base x'))

/-- For the cartesian square attached to `f` and `g`, the two source points lie in their
largest open loci simultaneously as soon as `g` is smooth at the image point. -/
private lemma mem_largestOpen_iff_of_smooth_pullback
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    [P.IsLocalAtTarget
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (z : (pullback f g : Scheme.{u}))
    (hg : InfinitesimalLifting.SmoothAt g
      ((pullback.snd f g).base z)) :
    (pullback.fst f g).base z ∈ AlgebraicGeometry.largestOpen P f ↔
      z ∈ AlgebraicGeometry.largestOpen P (pullback.snd f g) := by
  constructor
  · exact mem_largestOpen_of_smoothAt_isPullback P (IsPullback.of_hasPullback f g) z hg
  · intro hz
    let a := pullback.fst f g
    let b := pullback.snd f g
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g (b z))) isOpen_univ
    let VY : Y.Opens := V
    obtain ⟨d, U, hU, hzU, hUV, π, hπ, hπover⟩ :=
      AlgebraicGeometry.exists_affine_open_etale_affineSpace g (b z) VY hV (by simpa using hyV) hg
    let n := ULift.{u} (Fin d)
    have : Etale π := hπ
    have := etale_affineSpace_map_of_openImmersion VY.ι n
    let π' := π ≫ AffineSpace.map n VY.ι
    have : Etale π' := by dsimp [π']; infer_instance
    have hπ' : π' ≫ (AffineSpace n Y ↘ Y) = U.ι ≫ g := by
      dsimp [π']
      rw [Category.assoc, AffineSpace.map_over, ← Category.assoc, hπover]
      exact Scheme.Hom.resLE_comp_ι g hUV
    let j := (b ⁻¹ᵁ U).ι
    let c := b ∣_ U
    let zU : (b ⁻¹ᵁ U).toScheme := ⟨z, hzU⟩
    have hzUW : zU ∈ AlgebraicGeometry.largestOpen P c :=
      preimage_largestOpen_le_of_smooth_isPullback P
        (isPullback_morphismRestrict b U).flip hz
    have hbc : IsPullback (j ≫ a) c f (U.ι ≫ g) :=
      ((isPullback_morphismRestrict b U).paste_vert
        (IsPullback.of_hasPullback f g).flip).flip
    let hA := (AffineSpace.isPullback_map (n := n) f).flip
    have hc : (j ≫ a) ≫ f = (c ≫ π') ≫ (AffineSpace n Y ↘ Y) := by
      rw [Category.assoc c π', hπ']
      exact hbc.w
    let r := hA.lift (j ≫ a) (c ≫ π') hc
    have hr₁ : r ≫ (AffineSpace n X ↘ X) = j ≫ a := hA.lift_fst _ _ _
    have hr₂ : r ≫ AffineSpace.map n f = c ≫ π' := hA.lift_snd _ _ _
    have houter : IsPullback c (r ≫ (AffineSpace n X ↘ X))
        (π' ≫ (AffineSpace n Y ↘ Y)) f := by
      rw [hr₁, hπ']
      exact hbc.flip
    have hsmall : IsPullback r c (AffineSpace.map n f) π' :=
      (houter.of_bot hr₂.symm hA.flip).flip
    have : Etale r :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hsmall.flip inferInstance
    have hrW : r zU ∈ AlgebraicGeometry.largestOpen P (AffineSpace.map n f) :=
      (mem_largestOpen_iff_of_etale P (isEtaleLocalOnSourceAndTarget_of_smoothLocalAtTarget P)
        (AffineSpace.map n f) c π' r hr₂ zU).mpr hzUW
    have hx := mem_largestOpen_of_affineSpace_any P f d (r zU) hrW
    have he : (AffineSpace n X ↘ X) (r zU) = a z :=
      congrArg (fun k => k zU) hr₁
    rwa [he] at hx

/-- **Stacks Project, Tag 0CF1.** If the right vertical morphism of a commutative square is
smooth at the relevant point and the comparison morphism to the fibre product is étale at the
chosen point, the two source points lie in their largest open loci simultaneously. -/
@[stacks 0CF1]
public theorem mem_largestOpen_iff_of_smoothAt_etaleAt
    (P : MorphismProperty Scheme.{u})
    [P.IsLocalAtSource Scheme.etalePrecoverage]
    [P.IsLocalAtTarget
      (Scheme.precoverage (@Smooth : MorphismProperty Scheme.{u}))]
    [P.RespectsRight (@IsOpenImmersion : MorphismProperty Scheme.{u})]
    {X' X Y' Y : Scheme.{u}}
    (f : X ⟶ Y) (f' : X' ⟶ Y') (g : Y' ⟶ Y) (g' : X' ⟶ X)
    (hcomm : g' ≫ f = f' ≫ g) (x' : X')
    (hg : InfinitesimalLifting.SmoothAt g (f'.base x'))
    (hg' : EtaleAt
      (pullback.lift g' f' hcomm) x') :
    g'.base x' ∈ AlgebraicGeometry.largestOpen P f ↔
      x' ∈ AlgebraicGeometry.largestOpen P f' := by
  let c := pullback.lift g' f' hcomm
  have hc : (pullback.fst f g).base (c.base x') = g'.base x' :=
    congrArg (fun k : X' ⟶ X => k.base x') (pullback.lift_fst g' f' hcomm)
  have hs : (pullback.snd f g).base (c.base x') = f'.base x' :=
    congrArg (fun k : X' ⟶ Y' => k.base x') (pullback.lift_snd g' f' hcomm)
  simpa only [hc] using (mem_largestOpen_iff_of_smooth_pullback P f g (c.base x')
    (by rwa [hs])).trans (mem_largestOpen_iff_of_comparison_etaleAt P f f' g g' hcomm x' hg')

end AlgebraicGeometry

end
