module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleOverAlgebraicExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.LimitDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.FirstVanishing.GaloisObjectCover

/-!
# A Galois cover of a scheme base changed to an algebraic extension comes from a finite stage

Let `K` be a field, let `Kbar/K` be an algebraic extension and let `X` be a quasi-compact
quasi-separated scheme over `K`.
`AlgebraicGeometry.AlgebraicExtensionLimit.exists_finiteEtale_model_of_isAlgebraic` descends a
finite étale cover of `X_{Kbar}` to a finite étale cover of `X_L` for a single finite subextension
`L = K(s)`. This file does the same for a finite étale *Galois* cover: the cover, its action of
the finite group `G` and the torsor condition all descend to one finite subextension, by a
cartesian square whose top map is `G`-equivariant.

The descent is `AlgebraicGeometry.GaloisCoverLimits.exists_galoisCover_model` applied to the limit
presentation `AlgebraicGeometry.AdjoinFinset.isLimitBcCone` of `X_{Kbar}` as the limit of the
`X_{K(s)}`. Beyond the hypotheses on the index category, the transition morphisms and the stages
which `exists_finiteEtale_model_of_isAlgebraic` already discharges, that theorem asks for the
projections `X_{Kbar} ⟶ X_{K(s)}` to be flat, surjective and quasi-compact. All three hold because
the projection is the base change along `X ⟶ Spec K` of `Spec Kbar ⟶ Spec K(s)`, which is

* flat, `K(s)` being a field, so that `Kbar` is a free and hence flat `K(s)`-module;
* surjective, `Kbar` being integral over the subalgebra `K(s)` of an algebraic extension;
* quasi-compact, being a morphism of affine schemes.

## Main results

* `AlgebraicGeometry.AlgebraicExtensionLimit.flat_and_surjective_and_quasiCompact_bcProj` — the
  three properties of the projection `X_{Kbar} ⟶ X_{K(s)}`, proved together because they come
  from one cartesian square.
* `AlgebraicGeometry.AlgebraicExtensionLimit.exists_finiteEtaleGaloisCover_model_of_isAlgebraic` —
  a finite étale Galois cover of `X_{Kbar}` with group `G` is the base change, `G`-equivariantly,
  of a finite étale Galois cover of `X_{K(s)}` with group `G`, for a single finite subset `s` of
  `Kbar`.
* `AlgebraicGeometry.AlgebraicExtensionLimit.exists_finiteEtaleGaloisCover_model_of_isAlgClosure` —
  the case of a geometric fibre, `Kbar` an algebraic closure of `K`.
* `AlgebraicGeometry.AlgebraicExtensionLimit.exists_finiteEtaleGaloisCover_model_of_isGalois` — the
  same for a cover presented as a Galois *object* of `FÉt_{X_{Kbar}}`, with the conclusion as an
  isomorphism of covers rather than a cartesian square.

## Implementation notes

The cartesian square exhibiting `AlgebraicGeometry.AdjoinFinset.bcProj` as a base change of
`Spec Kbar ⟶ Spec K(s)` is built inside the proof rather than exported: it is already available
privately in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.GeometricArithmeticExactSequence`, where the same
square gives connectedness of the stages.

## References

* [Stacks Project, Tag 0BTV](https://stacks.math.columbia.edu/tag/0BTV)
* [Stacks Project, Tag 0BID](https://stacks.math.columbia.edu/tag/0BID)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry

namespace AlgebraicExtensionLimit

variable (K Kbar : Type u) [Field K] [Field Kbar] [Algebra K Kbar]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of K))

/-- **The projection `X_{Kbar} ⟶ X_{K(s)}` is flat, surjective and quasi-compact.** It is the
base change along `f` of `Spec Kbar ⟶ Spec K[s]`, and `K[s]` is a field over which `Kbar` is free,
`Kbar` is integral over `K[s]`, and a morphism of affine schemes is quasi-compact. The three
conclusions are proved together because they are read off the one cartesian square. -/
theorem flat_and_surjective_and_quasiCompact_bcProj [Algebra.IsAlgebraic K Kbar]
    (i : (Finset Kbar)ᵒᵖ) :
    Flat (AdjoinFinset.bcProj K Kbar f i) ∧ Surjective (AdjoinFinset.bcProj K Kbar f i) ∧
      QuasiCompact (AdjoinFinset.bcProj K Kbar f i) := by
  let : Field ↥(Algebra.adjoin K (i.unop : Set Kbar)) := (isField_adjoin K Kbar i.unop).toField
  have : Module.Free ↥(Algebra.adjoin K (i.unop : Set Kbar)) Kbar := Module.Free.of_divisionRing _ _
  -- `Spec Kbar ⟶ Spec K[s]` is flat, surjective and quasi-compact.
  have hflat : Flat (Spec.map (CommRingCat.ofHom
      (Algebra.adjoin K (i.unop : Set Kbar)).val.toRingHom)) := by
    rw [Flat.SpecMap_iff, CommRingCat.hom_ofHom]
    exact RingHom.flat_algebraMap_iff.mpr Module.Flat.of_free
  have hsurj : Surjective (Spec.map (CommRingCat.ofHom
      (Algebra.adjoin K (i.unop : Set Kbar)).val.toRingHom)) := by
    have hint : ((Algebra.adjoin K (i.unop : Set Kbar)).val.toRingHom :
        Algebra.adjoin K (i.unop : Set Kbar) →+* Kbar).IsIntegral := fun x ↦
      (Algebra.IsAlgebraic.isAlgebraic (R := K) x).isIntegral.tower_top
    exact ⟨RingHom.IsIntegral.comap_surjective hint Subtype.val_injective⟩
  have hqc : QuasiCompact (Spec.map (CommRingCat.ofHom
      (Algebra.adjoin K (i.unop : Set Kbar)).val.toRingHom)) := inferInstance
  -- the projection is the base change of that morphism along `f`
  have hsq : IsPullback (AdjoinFinset.bcProj K Kbar f i)
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) f)
      (pullback.fst (Spec.map (CommRingCat.ofHom
        (algebraMap K (Algebra.adjoin K (i.unop : Set Kbar))))) f)
      (Spec.map (CommRingCat.ofHom
        (Algebra.adjoin K (i.unop : Set Kbar)).val.toRingHom)) := by
    have hcomp : Spec.map (CommRingCat.ofHom
          (Algebra.adjoin K (i.unop : Set Kbar)).val.toRingHom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap K (Algebra.adjoin K (i.unop : Set Kbar)))) =
        Spec.map (CommRingCat.ofHom (algebraMap K Kbar)) := by
      rw [← Spec.map_comp]
      rfl
    refine IsPullback.of_right (h₁₂ := pullback.snd _ f) (v₁₃ := f)
      (h₂₂ := Spec.map (CommRingCat.ofHom
        (algebraMap K (Algebra.adjoin K (i.unop : Set Kbar)))))
      ?_ (AdjoinFinset.bcProj_fst K Kbar f i) (IsPullback.of_hasPullback _ _).flip
    rw [AdjoinFinset.bcProj_snd, hcomp]
    exact (IsPullback.of_hasPullback _ _).flip
  exact ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip hflat,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip hsurj,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip hqc⟩

/-- **A finite étale Galois cover of `X_{Kbar}` comes from a finite subextension.** Let `Kbar/K`
be an algebraic extension of fields, let `X` be a quasi-compact quasi-separated scheme over `K`
and let `Z` be a finite étale Galois cover of `X_{Kbar}` with finite group `G`. Then there is a
finite subset `s ⊆ Kbar` and a finite étale Galois cover `V` of `X_{K(s)}` with the same group `G`
such that `Z` is the base change of `V` along the projection `X_{Kbar} ⟶ X_{K(s)}` by a cartesian
square whose top map is `G`-equivariant.

This is the Galois form of
`AlgebraicGeometry.AlgebraicExtensionLimit.exists_finiteEtale_model_of_isAlgebraic`, namely
`AlgebraicGeometry.GaloisCoverLimits.exists_galoisCover_model` for the limit presentation of
`X_{Kbar}` by the finite subextensions, with the hypotheses on the projections supplied by
`AlgebraicGeometry.AlgebraicExtensionLimit.flat_and_surjective_and_quasiCompact_bcProj`. -/
theorem exists_finiteEtaleGaloisCover_model_of_isAlgebraic [Algebra.IsAlgebraic K Kbar]
    [CompactSpace X] [QuasiSeparatedSpace X] (G : Type v) [Group G] [Finite G]
    (Z : FiniteEtaleGaloisCover
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) f) G) :
    ∃ (s : Finset Kbar) (V : FiniteEtaleGaloisCover (pullback (Spec.map (CommRingCat.ofHom
        (algebraMap K (Algebra.adjoin K (s : Set Kbar))))) f) G)
      (P : Z.obj.left ⟶ V.obj.left),
      IsPullback P Z.obj.hom V.obj.hom (AdjoinFinset.bcProj K Kbar f (Opposite.op s)) ∧
        ∀ g : Gᵐᵒᵖ, (Z.action g).hom.left ≫ P = P ≫ (V.action g).hom.left := by
  have : ∀ i, CompactSpace ((AdjoinFinset.bcDiagram K Kbar f).obj i) :=
    compactSpace_bcDiagram_obj K Kbar f
  have : ∀ i, QuasiSeparatedSpace ((AdjoinFinset.bcDiagram K Kbar f).obj i) :=
    quasiSeparatedSpace_bcDiagram_obj K Kbar f
  have : ∀ {i j : (Finset Kbar)ᵒᵖ} (e : i ⟶ j),
      IsAffineHom ((AdjoinFinset.bcDiagram K Kbar f).map e) := fun e ↦
    isAffineHom_bcDiagram_map K Kbar f e
  have : ∀ i, Flat ((AdjoinFinset.bcCone K Kbar f).π.app i) := fun i ↦
    (flat_and_surjective_and_quasiCompact_bcProj K Kbar f i).1
  have : ∀ i, Surjective ((AdjoinFinset.bcCone K Kbar f).π.app i) := fun i ↦
    (flat_and_surjective_and_quasiCompact_bcProj K Kbar f i).2.1
  have : ∀ i, QuasiCompact ((AdjoinFinset.bcCone K Kbar f).π.app i) := fun i ↦
    (flat_and_surjective_and_quasiCompact_bcProj K Kbar f i).2.2
  obtain ⟨i, V, P, hP, hact⟩ :=
    GaloisCoverLimits.exists_galoisCover_model (AdjoinFinset.bcDiagram K Kbar f)
      (AdjoinFinset.bcCone K Kbar f) (AdjoinFinset.isLimitBcCone K Kbar f) Z
  exact ⟨i.unop, V, P, hP, hact⟩

/-- **A finite étale Galois cover of a geometric fibre comes from a finite subextension.** The
case of
`AlgebraicGeometry.AlgebraicExtensionLimit.exists_finiteEtaleGaloisCover_model_of_isAlgebraic` in
which `Kbar` is an algebraic closure of `K`. -/
theorem exists_finiteEtaleGaloisCover_model_of_isAlgClosure [IsAlgClosure K Kbar]
    [CompactSpace X] [QuasiSeparatedSpace X] (G : Type v) [Group G] [Finite G]
    (Z : FiniteEtaleGaloisCover
      (pullback (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) f) G) :
    ∃ (s : Finset Kbar) (V : FiniteEtaleGaloisCover (pullback (Spec.map (CommRingCat.ofHom
        (algebraMap K (Algebra.adjoin K (s : Set Kbar))))) f) G)
      (P : Z.obj.left ⟶ V.obj.left),
      IsPullback P Z.obj.hom V.obj.hom (AdjoinFinset.bcProj K Kbar f (Opposite.op s)) ∧
        ∀ g : Gᵐᵒᵖ, (Z.action g).hom.left ≫ P = P ≫ (V.action g).hom.left :=
  have : Algebra.IsAlgebraic K Kbar := IsAlgClosure.isAlgebraic
  exists_finiteEtaleGaloisCover_model_of_isAlgebraic K Kbar f G Z

/-- **A Galois object of `FÉt_{X_{Kbar}}` comes from a finite subextension, as a Galois cover.**
Let `Kbar/K` be an algebraic extension of fields, let `X` be a quasi-compact quasi-separated
scheme over `K` with `X_{Kbar}` connected, and let `A` be a finite étale cover of `X_{Kbar}` which
is a Galois object of `FÉt_{X_{Kbar}}`. Then for a single finite subset `s ⊆ Kbar` there is a
finite étale Galois cover `V` of `X_{K(s)}` with group `Aut A` whose base change along
`X_{Kbar} ⟶ X_{K(s)}` is isomorphic to `A` as a cover of `X_{Kbar}`.

This is
`AlgebraicGeometry.AlgebraicExtensionLimit.exists_finiteEtaleGaloisCover_model_of_isAlgebraic`
applied to `AlgebraicGeometry.FiniteEtaleGaloisCover.ofIsGalois`, with the cartesian square turned
into an isomorphism of covers by
`AlgebraicGeometry.GaloisCoverLimits.exists_equivariant_iso_of_isPullback`. It is the form in
which the residual input of [Stacks, Tag 0C0Q] presents the cover it has to descend: that input
quantifies over the Galois objects of the geometric generic fibre, and the extension theorems for
a cover of a generic fibre consume a `AlgebraicGeometry.FiniteEtaleGaloisCover`. -/
theorem exists_finiteEtaleGaloisCover_model_of_isGalois [Algebra.IsAlgebraic K Kbar]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [ConnectedSpace ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) f)]
    (A : FiniteEtaleOver (pullback (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) f))
    [CategoryTheory.PreGaloisCategory.IsGalois A] :
    ∃ (s : Finset Kbar) (V : FiniteEtaleGaloisCover (pullback (Spec.map (CommRingCat.ofHom
        (algebraMap K (Algebra.adjoin K (s : Set Kbar))))) f) (Aut A)),
      Nonempty ((finiteEtaleBaseChange
        (AdjoinFinset.bcProj K Kbar f (Opposite.op s))).obj V.obj ≅ A) := by
  obtain ⟨s, V, P, hP, hact⟩ :=
    exists_finiteEtaleGaloisCover_model_of_isAlgebraic K Kbar f (Aut A)
      (FiniteEtaleGaloisCover.ofIsGalois A)
  obtain ⟨e, -⟩ := GaloisCoverLimits.exists_equivariant_iso_of_isPullback
    (AdjoinFinset.bcProj K Kbar f (Opposite.op s)) V.obj
    (FiniteEtaleGaloisCover.ofIsGalois A).obj P hP
    (fun g : (Aut A)ᵐᵒᵖ ↦ (V.action g).hom)
    (fun g : (Aut A)ᵐᵒᵖ ↦ ((FiniteEtaleGaloisCover.ofIsGalois A).action g).hom) hact
  exact ⟨s, V, ⟨e⟩⟩

end AlgebraicExtensionLimit

end AlgebraicGeometry

end
