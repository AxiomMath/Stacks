module

public import StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BaseChangeFiberMap
public import StacksCore.Tactic.StacksAttribute

/-!
# Restriction of a family of cycles to an open subscheme

Let `f : X ⟶ S` be locally of finite type, let `V ⊆ S` and `U ⊆ X` be open subschemes with
`f(U) ⊆ V`, and let `α` be a family of `r`-cycles on the fibres of `X/S`. The *restriction* of
`α` to `U/V` is the family whose member over `t ∈ V` is the restriction of `α_t` along the
canonical open immersion `U_t ⟶ X_t`. This file constructs that family and identifies it with
the base change of `α` to `V` followed by flat pullback of relative dimension zero along
`U ⟶ X ×_S V`: that is, restriction is a combination of base change and flat pullback.

The identification rests on the fact that flat pullback along an open immersion changes no
coefficient, because the inverse image of the reduced closure of a point is reduced and
irreducible with the same generic point, so its multiplicity is one.

## Main definitions

* `Stacks.Chow.restrictedFamily` — the restriction of a family of cycles, together with its
  coefficientwise specification.
* `Stacks.Chow.baseChangedFlatPullbackFamily` — the same family, specified instead by the
  coefficients of a fibrewise flat pullback.
* `Stacks.Chow.IsFibrewiseRestriction`, `Stacks.Chow.IsBaseChangedFlatPullback` — the two
  descriptions of the restricted family, each stated by its own defining property.

## Main results

* `Stacks.Chow.relativeDimension_eq_of_openImmersion`,
  `Stacks.Chow.relativeDimension_eq_of_openImmersion_over_iso` — relative dimension is
  unchanged by an open immersion, also over an isomorphism of bases.
* `Stacks.Chow.trdeg_le_of_fieldEquivs`, `Stacks.Chow.trdeg_eq_of_fieldEquivs` —
  transcendence degree is invariant under compatible isomorphisms of the base and top fields.
* `Stacks.Chow.flatPullbackCoeff_open` — flat pullback along an open immersion preserves every
  coefficient.
* `Stacks.Chow.restriction_eq_flatPullback_after_baseChange` — the two constructions agree.
* `Stacks.Chow.isFibrewiseRestriction_iff_isBaseChangedFlatPullback`,
  `Stacks.Chow.IsFibrewiseRestriction.eq_of_isBaseChangedFlatPullback` — the two descriptions
  pick out the same family, so restriction is a combination of base change and flat pullback.

## Implementation notes

Both families are returned as elements of a subtype recording their coefficients on the
canonical fibre map, so that no identification of the two fibres has to be chosen; the stated
equality is then between the underlying families. The residue fields of corresponding points of
`U` and `X` are canonically isomorphic, and transcendence degree is transported along that
isomorphism rather than along a choice of transcendence basis.

Since `baseChangedFlatPullbackFamily` is built from `restrictedFamily`, the equality of the two
underlying families is definitional and carries no information. The comparison with content is
the one between the two *specifications*: `IsFibrewiseRestriction` and
`IsBaseChangedFlatPullback` describe a family of cycles on the fibres of `U/V` without
reference to each other, and `IsFibrewiseRestriction.eq_of_isBaseChangedFlatPullback` shows
they are descriptions of the same family.

## References

* [Stacks Project, Tag 0H4P](https://stacks.math.columbia.edu/tag/0H4P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Relative dimension along open immersions -/

/-- Relative dimension is unchanged by an open immersion over the base: the residue fields at
corresponding points agree. -/
theorem relativeDimension_eq_of_openImmersion {X Y S : Scheme.{u}}
    (j : X ⟶ Y) [IsOpenImmersion j] (f : Y ⟶ S) (g : X ⟶ S)
    (h : j ≫ f = g) (δ : DimensionFunction S) (x : X) :
    relativeDimension δ g x = relativeDimension δ f (j x) := by
  let e : Y.residueField (j x) ≃+* X.residueField x :=
    (asIso (j.residueFieldMap x)).commRingCatIsoToRingEquiv
  let : Algebra (S.residueField (f (j x))) (Y.residueField (j x)) :=
    (f.residueFieldMap (j x)).hom.toAlgebra
  cases h
  let : Algebra (S.residueField (f (j x))) (X.residueField x) :=
    ((j ≫ f).residueFieldMap x).hom.toAlgebra
  have he : ∀ a : S.residueField (f (j x)), e (algebraMap _ _ a) = algebraMap _ _ a := by
    intro a
    change (j.residueFieldMap x).hom ((f.residueFieldMap (j x)).hom a) =
      ((j ≫ f).residueFieldMap x).hom a
    rw [Scheme.residueFieldMap_comp j f x]
    rfl
  let eA : Y.residueField (j x) ≃ₐ[S.residueField (f (j x))] X.residueField x :=
    AlgEquiv.ofRingEquiv (f := e) he
  change δ (f (j x)) +
      (Cardinal.toNat (Algebra.trdeg (S.residueField (f (j x))) (X.residueField x)) : ℤ) =
      δ (f (j x)) +
        (Cardinal.toNat (Algebra.trdeg (S.residueField (f (j x)))
          (Y.residueField (j x))) : ℤ)
  rw [← AlgEquiv.trdeg_eq eA]

/-! ### Transcendence degree along compatible field isomorphisms -/

/-- Transcendence degree does not increase along a pair of ring isomorphisms of the base and
the top field that commute with the structure maps: an algebraically independent family is
carried to an algebraically independent family. -/
theorem trdeg_le_of_fieldEquivs
    {R R' A A' : Type u} [Field R] [Field R'] [Field A] [Field A']
    [Algebra R A] [Algebra R' A']
    (eR : R ≃+* R') (eA : A ≃+* A')
    (hcompat : ∀ r : R, eA (algebraMap R A r) = algebraMap R' A' (eR r)) :
    Algebra.trdeg R A ≤ Algebra.trdeg R' A' := by
  have hAI (ι : Type u) (x : ι → A) :
      AlgebraicIndependent R x ↔ AlgebraicIndependent R' (eA ∘ x) := by
    rw [algebraicIndependent_iff_injective_aeval, algebraicIndependent_iff_injective_aeval]
    let F := MvPolynomial.mapEquiv ι eR
    have heval (p : MvPolynomial ι R) :
        eA (MvPolynomial.aeval x p) = MvPolynomial.aeval (eA ∘ x) (F p) := by
      induction p using MvPolynomial.induction_on with
      | add p q hp hq => simp [hp, hq]
      | mul_X p n hp =>
          calc
            eA (MvPolynomial.aeval x (p * MvPolynomial.X n)) =
                eA (MvPolynomial.aeval x p) * eA (x n) := by simp
            _ = MvPolynomial.aeval (eA ∘ x) (F p) * (eA ∘ x) n := by
              rw [hp]
              rfl
            _ = MvPolynomial.aeval (eA ∘ x) (F (p * MvPolynomial.X n)) := by simp [F]
      | C r =>
          calc
            eA (MvPolynomial.aeval x (MvPolynomial.C r)) = eA (algebraMap R A r) := by simp
            _ = algebraMap R' A' (eR r) := hcompat r
            _ = MvPolynomial.aeval (eA ∘ x) (F (MvPolynomial.C r)) := by simp [F]
    constructor
    · intro h p q hpq
      have hpq' : MvPolynomial.aeval x (F.symm p) = MvPolynomial.aeval x (F.symm q) := by
        apply eA.injective
        simpa only [heval, F.apply_symm_apply] using hpq
      simpa using congrArg F (h hpq')
    · intro h p q hpq
      exact F.injective (h (by rw [← heval p, ← heval q, hpq]))
  unfold Algebra.trdeg
  apply ciSup_le'
  intro s
  let t : Set A' := eA '' s.1
  have hti : AlgebraicIndepOn R' id t := by
    change AlgebraicIndependent R' (fun y : t => (y : A'))
    have hx : AlgebraicIndependent R' (eA ∘ fun x : s.1 => (x : A)) := (hAI _ _).mp s.2
    let g : t → s.1 := fun y => by
      refine ⟨eA.symm y.1, ?_⟩
      rcases y.2 with ⟨z, hz, hzy⟩
      rwa [← hzy, eA.symm_apply_apply]
    have hg : Function.Injective g := by
      intro a b hab
      apply Subtype.ext
      have hab' : eA.symm a.1 = eA.symm b.1 := congrArg Subtype.val hab
      simpa using congrArg eA hab'
    have hx' := hx.comp g hg
    convert hx' using 1
    ext y
    simp [g]
  calc
    Cardinal.mk s.1 = Cardinal.mk t :=
      (Cardinal.mk_image_eq_of_injOn eA s.1 eA.injective.injOn).symm
    _ ≤ ⨆ ι : {q : Set A' // AlgebraicIndepOn R' id q}, Cardinal.mk ι.1 :=
      le_ciSup Cardinal.bddAbove_of_small
        (⟨t, hti⟩ : {q : Set A' // AlgebraicIndepOn R' id q})

/-- Transcendence degree is invariant under a pair of ring isomorphisms of the base and the top
field that commute with the structure maps. -/
theorem trdeg_eq_of_fieldEquivs
    {R R' A A' : Type u} [Field R] [Field R'] [Field A] [Field A']
    [Algebra R A] [Algebra R' A']
    (eR : R ≃+* R') (eA : A ≃+* A')
    (hcompat : ∀ r : R, eA (algebraMap R A r) = algebraMap R' A' (eR r)) :
    Algebra.trdeg R A = Algebra.trdeg R' A' := by
  refine le_antisymm (trdeg_le_of_fieldEquivs eR eA hcompat) ?_
  apply trdeg_le_of_fieldEquivs eR.symm eA.symm
  intro r
  apply eA.injective
  simpa using (hcompat (eR.symm r)).symm

/-- Relative dimension is preserved by an open immersion over an isomorphism of bases. -/
theorem relativeDimension_eq_of_openImmersion_over_iso
    {X Y S T : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
    (sX : X ⟶ S) (sY : Y ⟶ T) (e : S ≅ T)
    (h : sX ≫ e.hom = j ≫ sY)
    (δS : DimensionFunction S) (δT : DimensionFunction T)
    (hδ : ∀ x : X, δS (sX x) = δT (e.hom (sX x))) (x : X) :
    relativeDimension δS sX x = relativeDimension δT sY (j x) := by
  let R := T.residueField (e.hom (sX x))
  let R' := S.residueField (sX x)
  let A := X.residueField x
  let : Algebra R' A := (sX.residueFieldMap x).hom.toAlgebra
  let : Algebra R A := ((sX ≫ e.hom).residueFieldMap x).hom.toAlgebra
  let : Algebra (T.residueField (sY (j x))) (Y.residueField (j x)) :=
    (sY.residueFieldMap (j x)).hom.toAlgebra
  have : IsIso e.hom := by infer_instance
  have : IsIso (e.hom.residueFieldMap (sX x)) := by infer_instance
  let eR : R ≃+* R' := (asIso (e.hom.residueFieldMap (sX x))).commRingCatIsoToRingEquiv
  have hcompat : ∀ a : R, (RingEquiv.refl A) (algebraMap R A a) = algebraMap R' A (eR a) := by
    intro a
    change ((sX ≫ e.hom).residueFieldMap x).hom a =
      (sX.residueFieldMap x).hom ((e.hom.residueFieldMap (sX x)).hom a)
    rw [Scheme.residueFieldMap_comp]
    rfl
  have htrdeg := trdeg_eq_of_fieldEquivs eR (RingEquiv.refl A) hcompat
  have hopen := relativeDimension_eq_of_openImmersion j sY (sX ≫ e.hom) h.symm δT x
  rw [relativeDimension, relativeDimension]
  rw [hδ x]
  have htrNat : (Cardinal.toNat (Algebra.trdeg R A) : ℤ) =
      (Cardinal.toNat (Algebra.trdeg R' A) : ℤ) :=
    congrArg (fun d : Cardinal => (Cardinal.toNat d : ℤ)) htrdeg
  rw [← htrNat]
  change relativeDimension δT (sX ≫ e.hom) x = relativeDimension δT sY (j x)
  exact hopen

/-! ### Flat pullback along an open immersion -/

/-- Flat pullback along an open immersion preserves the coefficient at each point: the inverse
image of the reduced closure of the image point is reduced and irreducible with the same
generic point, hence has multiplicity one. -/
theorem flatPullbackCoeff_open
    (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (f : X ⟶ Y) [IsOpenImmersion f] (hbase : f ≫ sY = sX)
    (k : ℤ) (c : CycleGroup C sY k) (x : X) :
    flatPullbackCoeff C sX sY f 0 k c x = c.1 (f x) := by
  classical
  by_cases hc : c.1 (f x) = 0
  · simp [flatPullbackCoeff, flatPullbackWeight, hc]
  · let T : IrreducibleCloseds Y :=
      ⟨closure ({f x} : Set Y), isIrreducible_singleton.closure, isClosed_closure⟩
    let J : Y.IdealSheafData :=
      Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({f x} : Set Y))
    let JX : X.IdealSheafData := J.comap f
    let Z := JX.subscheme
    let i : Z ⟶ X := JX.subschemeι
    have hpre : f ⁻¹' closure ({f x} : Set Y) = closure ({x} : Set X) := by
      rw [f.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage f.continuous]
      have hsingleton : f ⁻¹' ({f x} : Set Y) = ({x} : Set X) := by
        ext z
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact ⟨fun hz => f.isOpenEmbedding.injective hz, fun hz => hz ▸ rfl⟩
      rw [hsingleton]
    have hsupp : (JX.support : Set X) = closure ({x} : Set X) := by
      rw [Scheme.IdealSheafData.support_comap]
      simp [J, Scheme.IdealSheafData.coe_support_vanishingIdeal, hpre]
    have hrange : Set.range i.base = closure ({x} : Set X) := by
      change Set.range JX.subschemeι.base = _
      rw [JX.range_subschemeι, hsupp]
    have : IsReduced J.subscheme :=
      Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal
        (Closeds.closure ({f x} : Set Y))
    have : IsReduced (pullback f J.subschemeι) :=
      isReduced_of_isOpenImmersion (pullback.snd f J.subschemeι)
    have : IsReduced Z := isReduced_of_isOpenImmersion (J.comapIso f).hom
    have hEmb : Topology.IsEmbedding i.base := IsPreimmersion.isEmbedding i
    let homeo : Z ≃ₜ Set.range i.base := hEmb.toHomeomorph
    have : IrreducibleSpace (Set.range i.base) := isIrreducible_iff_irreducibleSpace.mp <| by
      rw [hrange]
      exact isIrreducible_singleton.closure
    have : IrreducibleSpace Z := homeo.symm.surjective.irreducibleSpace homeo.symm.continuous
    let : IsIntegral Z := isIntegral_of_irreducibleSpace_of_isReduced Z
    let ξ : genericPoints Z :=
      genericPoints.ofComponent ⟨Set.univ, by rw [irreducibleComponents_eq_singleton]; simp⟩
    have hclosure : closure ({i ξ.1} : Set X) = closure ({x} : Set X) := by
      calc
        closure ({i ξ.1} : Set X) = i.base '' closure ({ξ.1} : Set Z) := by
          rw [← Set.image_singleton, i.isClosedEmbedding.closure_image_eq]
        _ = Set.range i.base := by
          rw [genericPoints.isGenericPoint ξ]
          simp [ξ]
        _ = closure ({x} : Set X) := hrange
    have hmap : i ξ.1 = x := isGenericPoint_closure.eq (hclosure ▸ isGenericPoint_closure)
    have hdimY : relativeDimension C.dimensionFunction sY (f x) = k := by
      have hgeneric : IsGenericPoint (f x) (T : Set Y) := by
        change closure ({f x} : Set Y) = _
        rfl
      have hpoint : T.isIrreducible.genericPoint = f x :=
        (T.isIrreducible.isGenericPoint_genericPoint T.isClosed).eq hgeneric
      have hdim := (mem_cyclesOfDimension C sY k c.1).mp c.2 T (by simpa [hpoint] using hc)
      simpa [deltaDimension, hpoint] using hdim
    have hdimX : relativeDimension C.dimensionFunction sX x = k := by
      rw [relativeDimension_eq_of_openImmersion f sY sX hbase C.dimensionFunction x]
      exact hdimY
    have hcoeff : ∃ ξ : genericPoints Z,
        i ξ.1 = x ∧ relativeDimension C.dimensionFunction sX x = k := ⟨ξ, hmap, hdimX⟩
    have hmult : closedSubschemeCycleCoeff C sX
        ((Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({f x} : Set Y))).comap f).subschemeι k x = 1 := by
      change closedSubschemeCycleCoeff C sX i k x = 1
      unfold closedSubschemeCycleCoeff
      rw [dite_eq_left hcoeff]
      exact componentMultiplicity_eq_one_of_reduced i (Classical.choose hcoeff)
    simp [flatPullbackCoeff, flatPullbackWeight, hmult]

/-! ### Restriction of a family of cycles -/

/-- The restriction of a family of cycles to the fibres of an open subscheme, specified by
restriction of the coefficients along the canonical fibre map. -/
@[stacks 0H4N "restriction of a family of cycles on fibres to open subschemes"]
def restrictedFamily {X S U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ V) [LocallyOfFiniteType fU]
    (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i]
    (h : j ≫ f = fU ≫ i) (r : ℕ) (α : FamilyOfCycles f r) :
    {β : FamilyOfCycles fU r //
      ∀ (t : V) (x : fU.fiber t),
        (β t : AlgebraicCycle (fU.fiber t) ℤ) x =
          (α (i t) : AlgebraicCycle (f.fiber (i t)) ℤ)
            (restrictedFiberMap f fU j i h t x)} := by
  classical
  refine ⟨fun t => ?_, ?_⟩
  · let g := restrictedFiberMap f fU j i h t
    let sX := fU.fiberToSpecResidueField t
    let sY := f.fiberToSpecResidueField (i t)
    letI : LocallyOfFiniteType sX :=
      (show LocallyOfFiniteType (pullback.snd fU (V.fromSpecResidueField t)) from
        inferInstance)
    letI : LocallyOfFiniteType sY :=
      (show LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (i t))) from
        inferInstance)
    let Cx := fieldChowSituation (V.residueField t)
    let Cy := fieldChowSituation (S.residueField (i t))
    let c := α (i t)
    let d : fU.fiber t → ℤ := fun x => c.1 (g x)
    letI : IsIso (i.residueFieldMap t) := by
      let : IsIso (i.stalkMap t) :=
        (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion i)).2 t
      exact (IsLocalRing.ResidueField.mapEquiv
        (asIso (i.stalkMap t)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
    letI : IsOpenImmersion (Spec.map (i.residueFieldMap t)) := inferInstance
    letI : Mono (Spec.map (i.residueFieldMap t)) := inferInstance
    haveI : Mono i := inferInstance
    haveI : IsOpenImmersion g := by
      change IsOpenImmersion (pullback.map fU (V.fromSpecResidueField t)
        f (S.fromSpecResidueField (i t)) j (Spec.map (i.residueFieldMap t)) i
        h.symm (by simp))
      infer_instance
    let e := asIso (Spec.map (i.residueFieldMap t))
    have hbase : g ≫ sY = sX ≫ e.hom := by
      change (pullback.lift
        (pullback.fst fU (V.fromSpecResidueField t) ≫ j)
        (pullback.snd fU (V.fromSpecResidueField t) ≫ Spec.map (i.residueFieldMap t))
        _) ≫ pullback.snd f (S.fromSpecResidueField (i t)) =
        pullback.snd fU (V.fromSpecResidueField t) ≫ Spec.map (i.residueFieldMap t)
      rw [pullback.lift_snd]
    have hlf : LocallyFiniteSupport d := by
      intro x
      obtain ⟨W, hW, hfin⟩ := c.1.locallyFiniteSupport (g x)
      refine ⟨g ⁻¹' W, g.continuous.continuousAt (x := x) hW, ?_⟩
      exact Set.Finite.of_injOn (f := g) (t := W ∩ Function.support c.1)
        (fun a ha ↦ ⟨ha.1, by simpa [d] using ha.2⟩)
        (fun a _ b _ hab ↦ (show Function.Injective g from g.isOpenEmbedding.injective) hab) hfin
    change CycleGroup Cx sX (r : ℤ)
    refine ⟨⟨d, by intro x hx; trivial, fun x _ => hlf x⟩, ?_⟩
    rw [mem_cyclesOfDimension]
    intro Z hZ
    let x := Z.isIrreducible.genericPoint
    have hcx : c.1 (g x) ≠ 0 := by simpa [d, x] using hZ
    let T : IrreducibleCloseds (f.fiber (i t)) :=
      ⟨closure ({g x} : Set (f.fiber (i t))), isIrreducible_singleton.closure, isClosed_closure⟩
    have hgeneric : IsGenericPoint (g x) (T : Set (f.fiber (i t))) := by
      change closure ({g x} : Set _) = _
      rfl
    have hpoint : T.isIrreducible.genericPoint = g x :=
      (T.isIrreducible.isGenericPoint_genericPoint T.isClosed).eq hgeneric
    have hdimY : relativeDimension Cy.dimensionFunction sY (g x) = r := by
      have hdim' := (mem_cyclesOfDimension Cy sY (r : ℤ) c.1).mp c.2 T
        (by simpa [hpoint] using hcx)
      simpa [deltaDimension, hpoint] using hdim'
    have hδ : ∀ z : fU.fiber t,
        Cx.dimensionFunction (sX z) = Cy.dimensionFunction (e.hom (sX z)) := by
      intro z
      rw [fieldChowSituation_dimensionFunction_eq_zero,
        fieldChowSituation_dimensionFunction_eq_zero]
    have hdimX := relativeDimension_eq_of_openImmersion_over_iso
      g sX sY e hbase.symm Cx.dimensionFunction Cy.dimensionFunction hδ x
    simpa [deltaDimension, x] using hdimX.trans hdimY
  · intro t x
    rfl

/-- The base change of a family of cycles to the open subscheme `V`, followed by fibrewise flat
pullback of relative dimension zero along the open immersion into `X ×_S V`. -/
def baseChangedFlatPullbackFamily {X S U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ V) [LocallyOfFiniteType fU]
    (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i]
    (h : j ≫ f = fU ≫ i) (r : ℕ) (α : FamilyOfCycles f r) :
    {β : FamilyOfCycles fU r //
      ∀ (t : V) (x : fU.fiber t),
        (β t : AlgebraicCycle (fU.fiber t) ℤ) x =
          letI : LocallyOfFiniteType (fU.fiberToSpecResidueField t) := by
            change LocallyOfFiniteType (pullback.snd fU (V.fromSpecResidueField t))
            infer_instance
          letI : LocallyOfFiniteType (Spec.map (i.residueFieldMap t)) := inferInstance
          letI : LocallyOfFiniteType (f.fiberToSpecResidueField (i t)) := by
            change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (i t)))
            infer_instance
          flatPullbackCoeff (fieldChowSituation (S.residueField (i t)))
            (fU.fiberToSpecResidueField t ≫ Spec.map (i.residueFieldMap t))
            (f.fiberToSpecResidueField (i t))
            (restrictedFiberMap f fU j i h t) 0 (r : ℤ) (α (i t)) x} := by
  classical
  let ρ := restrictedFamily f fU j i h r α
  refine ⟨ρ.1, ?_⟩
  intro t x
  let g := restrictedFiberMap f fU j i h t
  let sX := fU.fiberToSpecResidueField t
  let sY := f.fiberToSpecResidueField (i t)
  let : LocallyOfFiniteType sX := by
    change LocallyOfFiniteType (pullback.snd fU (V.fromSpecResidueField t))
    infer_instance
  let : LocallyOfFiniteType sY := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (i t)))
    infer_instance
  let : IsIso (i.residueFieldMap t) := by
    let : IsIso (i.stalkMap t) :=
      (IsOpenImmersion.iff_isIso_stalkMap.mp (inferInstance : IsOpenImmersion i)).2 t
    exact (IsLocalRing.ResidueField.mapEquiv
      (asIso (i.stalkMap t)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  let : LocallyOfFiniteType (Spec.map (i.residueFieldMap t)) := inferInstance
  let sX' := sX ≫ Spec.map (i.residueFieldMap t)
  let : LocallyOfFiniteType sX' := inferInstance
  let : IsOpenImmersion (Spec.map (i.residueFieldMap t)) := inferInstance
  let : Mono (Spec.map (i.residueFieldMap t)) := inferInstance
  have : Mono i := inferInstance
  have : IsOpenImmersion g := by
    change IsOpenImmersion (pullback.map fU (V.fromSpecResidueField t)
      f (S.fromSpecResidueField (i t)) j (Spec.map (i.residueFieldMap t)) i
      h.symm (by simp))
    infer_instance
  have hbase : g ≫ sY = sX' := by
    change (pullback.lift
      (pullback.fst fU (V.fromSpecResidueField t) ≫ j)
      (pullback.snd fU (V.fromSpecResidueField t) ≫ Spec.map (i.residueFieldMap t))
      _) ≫ pullback.snd f (S.fromSpecResidueField (i t)) =
      pullback.snd fU (V.fromSpecResidueField t) ≫ Spec.map (i.residueFieldMap t)
    rw [pullback.lift_snd]
  let C := fieldChowSituation (S.residueField (i t))
  change (ρ.1 t : AlgebraicCycle (fU.fiber t) ℤ) x =
    flatPullbackCoeff C sX' sY g 0 (r : ℤ) (α (i t)) x
  exact (ρ.2 t x).trans (flatPullbackCoeff_open C sX' sY g hbase (r : ℤ) (α (i t)) x).symm

/-- **Stacks Project, Tag 0H4P.** Restricting a family of cycles to an open subscheme is the
same as base changing it to the open subscheme of the base and pulling back along the open
immersion `U ⟶ X ×_S V`.

This equality is `rfl`, because `baseChangedFlatPullbackFamily` is constructed with
`restrictedFamily`'s underlying family as its first component. It therefore carries **no**
`@[stacks 0H4P]` attribute: an identity true by construction states nothing, whatever its
name says. The mathematical content of the tag is the *second* component of each subtype —
that these coefficients are the restriction of `α`, and that they are a fibrewise flat
pullback of its base change — and that second fact is what `flatPullbackCoeff_open` is for.
Part (2) of the tag is registered on
`Stacks.Chow.restrictedFamily_eq_flatPullbackFamily_baseChangeFamily`, which compares the
restriction with the library's base change and flat pullback of families, neither being defined
from the other. -/
theorem restriction_eq_flatPullback_after_baseChange
    {X S U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ V) [LocallyOfFiniteType fU]
    (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i]
    (h : j ≫ f = fU ≫ i) (r : ℕ) (α : FamilyOfCycles f r) :
    (restrictedFamily f fU j i h r α).1 = (baseChangedFlatPullbackFamily f fU j i h r α).1 :=
  rfl

/-! ### The two descriptions of the restricted family, stated independently -/

/-- `β` is the fibrewise restriction of `α` to `U/V`: on the fibre over each `t ∈ V` the
coefficient of `β` at a point `x` is the coefficient of `α_{i t}` at the image of `x` under the
canonical open immersion of fibres. This is the description of `α|_U` in the Stacks Project
discussion preceding Tag 0H4P. -/
def IsFibrewiseRestriction {X S U V : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ V) [LocallyOfFiniteType fU] (j : U ⟶ X) (i : V ⟶ S)
    (h : j ≫ f = fU ≫ i) {r : ℕ} (α : FamilyOfCycles f r) (β : FamilyOfCycles fU r) : Prop :=
  ∀ (t : V) (x : fU.fiber t),
    (β t : AlgebraicCycle (fU.fiber t) ℤ) x =
      (α (i t) : AlgebraicCycle (f.fiber (i t)) ℤ) (restrictedFiberMap f fU j i h t x)

/-- `β` is the fibrewise flat pullback, of relative dimension zero, of the base change of `α`
to `V`: on the fibre over each `t ∈ V` the coefficient of `β` at a point `x` is the flat
pullback coefficient of `α_{i t}` along the canonical morphism of fibres, computed over the
residue field of `i t`. This is the description of `α|_U` as a flat pullback in Tag 0H4P. -/
def IsBaseChangedFlatPullback {X S U V : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (fU : U ⟶ V) [LocallyOfFiniteType fU] (j : U ⟶ X) (i : V ⟶ S) [IsOpenImmersion i]
    (h : j ≫ f = fU ≫ i) {r : ℕ} (α : FamilyOfCycles f r) (β : FamilyOfCycles fU r) : Prop :=
  ∀ (t : V) (x : fU.fiber t),
    (β t : AlgebraicCycle (fU.fiber t) ℤ) x =
      letI : LocallyOfFiniteType (fU.fiberToSpecResidueField t) := by
        change LocallyOfFiniteType (pullback.snd fU (V.fromSpecResidueField t))
        infer_instance
      letI : LocallyOfFiniteType (Spec.map (i.residueFieldMap t)) := inferInstance
      letI : LocallyOfFiniteType (f.fiberToSpecResidueField (i t)) := by
        change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (i t)))
        infer_instance
      flatPullbackCoeff (fieldChowSituation (S.residueField (i t)))
        (fU.fiberToSpecResidueField t ≫ Spec.map (i.residueFieldMap t))
        (f.fiberToSpecResidueField (i t))
        (restrictedFiberMap f fU j i h t) 0 (r : ℤ) (α (i t)) x

/-- The two descriptions of the restricted family single out the same families: a family of
cycles on the fibres of `U/V` restricts `α` coefficientwise exactly when its coefficients are
the fibrewise flat pullback of the base change of `α`. The equivalence is not formal — it holds
because flat pullback along the open immersion of fibres multiplies every coefficient by the
multiplicity one, which is `Stacks.Chow.flatPullbackCoeff_open`. -/
theorem isFibrewiseRestriction_iff_isBaseChangedFlatPullback {X S U V : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (fU : U ⟶ V) [LocallyOfFiniteType fU]
    (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i]
    (h : j ≫ f = fU ≫ i) {r : ℕ} (α : FamilyOfCycles f r) (β : FamilyOfCycles fU r) :
    IsFibrewiseRestriction f fU j i h α β ↔ IsBaseChangedFlatPullback f fU j i h α β := by
  have key : ∀ (t : V) (x : fU.fiber t),
      let : LocallyOfFiniteType (fU.fiberToSpecResidueField t) := by
        change LocallyOfFiniteType (pullback.snd fU (V.fromSpecResidueField t))
        infer_instance
      let : LocallyOfFiniteType (Spec.map (i.residueFieldMap t)) := inferInstance
      let : LocallyOfFiniteType (f.fiberToSpecResidueField (i t)) := by
        change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (i t)))
        infer_instance
      flatPullbackCoeff (fieldChowSituation (S.residueField (i t)))
          (fU.fiberToSpecResidueField t ≫ Spec.map (i.residueFieldMap t))
          (f.fiberToSpecResidueField (i t))
          (restrictedFiberMap f fU j i h t) 0 (r : ℤ) (α (i t)) x =
        (α (i t) : AlgebraicCycle (f.fiber (i t)) ℤ) (restrictedFiberMap f fU j i h t x) := by
    intro t x
    have : IsOpenImmersion (restrictedFiberMap f fU j i h t) :=
      restrictedFiberMap_isOpenImmersion f fU j i h t
    have : LocallyOfFiniteType (fU.fiberToSpecResidueField t) := by
      change LocallyOfFiniteType (pullback.snd fU (V.fromSpecResidueField t))
      infer_instance
    have : LocallyOfFiniteType (f.fiberToSpecResidueField (i t)) := by
      change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (i t)))
      infer_instance
    exact flatPullbackCoeff_open (fieldChowSituation (S.residueField (i t))) _ _ _
      (restrictedFiberMap_comp_fiberToSpecResidueField f fU j i h t) (r : ℤ) (α (i t)) x
  constructor
  · intro H t x
    exact (H t x).trans (key t x).symm
  · intro H t x
    exact (H t x).trans (key t x)

/-- The restriction of a family of cycles, as constructed by `Stacks.Chow.restrictedFamily`,
satisfies the coefficientwise description of restriction. -/
theorem isFibrewiseRestriction_restrictedFamily {X S U V : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (fU : U ⟶ V) [LocallyOfFiniteType fU]
    (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i]
    (h : j ≫ f = fU ≫ i) (r : ℕ) (α : FamilyOfCycles f r) :
    IsFibrewiseRestriction f fU j i h α (restrictedFamily f fU j i h r α).1 :=
  (restrictedFamily f fU j i h r α).2

/-- The family constructed by `Stacks.Chow.baseChangedFlatPullbackFamily` satisfies the
coefficientwise description of a fibrewise flat pullback of the base change. -/
theorem isBaseChangedFlatPullback_baseChangedFlatPullbackFamily {X S U V : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (fU : U ⟶ V) [LocallyOfFiniteType fU]
    (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i]
    (h : j ≫ f = fU ≫ i) (r : ℕ) (α : FamilyOfCycles f r) :
    IsBaseChangedFlatPullback f fU j i h α (baseChangedFlatPullbackFamily f fU j i h r α).1 :=
  (baseChangedFlatPullbackFamily f fU j i h r α).2

/-- **Stacks Project, Tag 0H4P**, part (2): restriction of a family of cycles to an open
subscheme is a combination of base change and flat pullback.

Each of the two operations is given here by its own defining property, neither being read off
the other's construction: `β` is any family whose coefficients restrict those of `α`, and `γ`
is any family whose coefficients are the fibrewise flat pullback, of relative dimension zero,
of the base change of `α` to `V`. The conclusion is that there is only one such family, so the
two operations agree. Both hypotheses are satisfiable — by
`Stacks.Chow.isFibrewiseRestriction_restrictedFamily` and
`Stacks.Chow.isBaseChangedFlatPullback_baseChangedFlatPullbackFamily` — so the statement is not
vacuous.

Part (2) of Tag 0H4P, stated with the library's own base change `Stacks.Chow.baseChangeFamily`
and flat pullback `Stacks.Chow.flatPullbackFamily`, is
`Stacks.Chow.restrictedFamily_eq_flatPullbackFamily_baseChangeFamily`, which carries the
attribute. -/
theorem IsFibrewiseRestriction.eq_of_isBaseChangedFlatPullback {X S U V : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (fU : U ⟶ V) [LocallyOfFiniteType fU]
    (j : U ⟶ X) [IsOpenImmersion j] (i : V ⟶ S) [IsOpenImmersion i]
    (h : j ≫ f = fU ≫ i) {r : ℕ} {α : FamilyOfCycles f r} {β γ : FamilyOfCycles fU r}
    (hβ : IsFibrewiseRestriction f fU j i h α β)
    (hγ : IsBaseChangedFlatPullback f fU j i h α γ) :
    β = γ := by
  funext t
  apply Subtype.ext
  ext x
  exact ((isFibrewiseRestriction_iff_isBaseChangedFlatPullback f fU j i h α β).mp hβ t x).trans
    (hγ t x).symm

end Stacks.Chow
