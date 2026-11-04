module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Restriction
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.TrdegLift
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BaseChangeFiberMap
public import StacksFrontier.FieldTheory.Separable.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.Support

/-!
# Base change of families of cycles along a bijection on points

Let `f : X ⟶ S` be locally of finite type and let `g : S' ⟶ S` be bijective on points and an
isomorphism on every residue field. Then each scheme-theoretic fibre of the base change
`X ×_S S' ⟶ S'` is isomorphic to the fibre of `f` over the image point, so the two groups of
families of `r`-cycles on fibres are identified. This file builds that identification as an
additive equivalence and records its effect on coefficients.

The file also carries the base change of families of `r`-cycles on fibres along an
arbitrary morphism `g : S' ⟶ S` of bases, defined by the fibrewise coefficient formula, and
the injectivity of that operation when `g` is surjective on points.

## Main definitions

* `Stacks.Chow.baseChangeFamily`: the base change of a family of `r`-cycles on fibres along an
  arbitrary morphism of bases.
* `Stacks.Chow.HasSeparableResidueFieldPoints`: every point of the base is the image of a point
  with separable residue field extension.
* `Stacks.Chow.baseChangeFamilyOfCyclesAddEquiv`: the additive equivalence of groups of families
  of cycles.

## Main results

* `Stacks.Chow.baseChangeFamilyOfCyclesAddEquiv_apply`: its coefficients on each fibre.
* `Stacks.Chow.baseChangeFamily_apply`: the fibrewise coefficient formula for a general base
  change.
* `Stacks.Chow.baseChangeFamily_injective`: base change of families of cycles on fibres is
  injective along a surjective morphism of bases.

## References

* [Stacks Project, Tag 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
* [Stacks Project, Tag 0H4X](https://stacks.math.columbia.edu/tag/0H4X)
* [Stacks Project, Tag 0H4Y](https://stacks.math.columbia.edu/tag/0H4Y)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-- An isomorphism of schemes has residue degree one at every point. -/
theorem residueDegree_iso {X Y : Scheme.{u}} (i : Y ⟶ X) [IsIso i] (y : Y) :
    i.residueDegree y = 1 := by
  let R := X.residueField (i y)
  let S := Y.residueField y
  let : Algebra R S := (i.residueFieldMap y).hom.toAlgebra
  let e : R ≃ₐ[R] S :=
    AlgEquiv.ofRingEquiv (f := (asIso (i.residueFieldMap y)).commRingCatIsoToRingEquiv)
      fun _ ↦ rfl
  change Module.finrank R S = 1
  rw [← e.toLinearEquiv.finrank_eq, Module.finrank_self]

/-- Transporting a cycle along an isomorphism of schemes with zero dimension shift reindexes
its coefficients by the inverse isomorphism. -/
theorem algebraicCycle_map_iso_apply {A B : Scheme.{u}} (i : A ⟶ B)
    [IsIso i] (c : AlgebraicCycle A ℤ) (y : B) :
    AlgebraicCycle.map i (fun _ : A => 0) (fun _ : B => 0) c y =
      c (inv i y) := by
  classical
  rw [AlgebraicCycle.map, Function.locallyFinsupp.map_apply]
  have hleft (x : A) : inv i (i x) = x := by
    change ((i ≫ inv i) x) = x
    rw [IsIso.hom_inv_id]
    rfl
  have hright (x : B) : i (inv i x) = x := by
    change ((inv i ≫ i) x) = x
    rw [IsIso.inv_hom_id]
    rfl
  have hpre : i ⁻¹' ({y} : Set B) = {inv i y} := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun hxy ↦ by simpa only [hleft] using congrArg (inv i) hxy,
      fun hxy ↦ by simpa only [hright] using congrArg i hxy⟩
  rw [hpre]
  simp [AlgebraicCycle.mapCoeff, residueDegree_iso i (inv i y)]

/-- The additive equivalence of fibrewise cycle groups induced by base change at a point whose
residue-field map is an isomorphism. -/
def fiberCycleAddEquiv
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (t : S') (hres : IsIso (g.residueFieldMap t)) (r : ℕ) :
    FiberCycleGroup f (g t) r ≃+
      FiberCycleGroup
        (pullback.snd f g) t r := by
  classical
  let f' := pullback.snd f g
  let j := restrictedFiberMap
    f f' (pullback.fst f g) g pullback.condition t
  haveI : IsIso j := @AlgebraicGeometry.isIso_baseChangeFiberMap _ _ _ f g t hres
  let sX := f'.fiberToSpecResidueField t
  let sY := f.fiberToSpecResidueField (g t)
  letI : LocallyOfFiniteType sX := by
    change LocallyOfFiniteType (pullback.snd f' (S'.fromSpecResidueField t))
    infer_instance
  letI : LocallyOfFiniteType sY := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (g t)))
    infer_instance
  haveI : IsIso (g.residueFieldMap t) := hres
  haveI : IsIso (Spec.map (g.residueFieldMap t)) := by infer_instance
  let e := asIso (Spec.map (g.residueFieldMap t))
  let Cx := fieldChowSituation
    (S'.residueField t)
  let Cy := fieldChowSituation
    (S.residueField (g t))
  have hbase : j ≫ sY = sX ≫ e.hom := by
    change (pullback.lift
        (pullback.fst f' (S'.fromSpecResidueField t) ≫ pullback.fst f g)
        (pullback.snd f' (S'.fromSpecResidueField t) ≫
          Spec.map (g.residueFieldMap t)) _ ≫
        pullback.snd f (S.fromSpecResidueField (g t))) =
      pullback.snd f' (S'.fromSpecResidueField t) ≫ Spec.map (g.residueFieldMap t)
    rw [pullback.lift_snd]
  have hδ : ∀ z, Cx.dimensionFunction (sX z) =
      Cy.dimensionFunction (e.hom (sX z)) := by
    intro z
    rw [fieldChowSituation_dimensionFunction_eq_zero,
      fieldChowSituation_dimensionFunction_eq_zero]
  have hdim (z : f'.fiber t) :
      relativeDimension Cx.dimensionFunction sX z =
        relativeDimension Cy.dimensionFunction sY (j z) :=
    relativeDimension_eq_of_openImmersion_over_iso
      j sX sY e hbase.symm Cx.dimensionFunction Cy.dimensionFunction hδ z
  have hleft (z : f'.fiber t) : inv j (j z) = z := by
    change ((j ≫ inv j) z) = z
    rw [IsIso.hom_inv_id]
    rfl
  have hright (z : f.fiber (g t)) : j (inv j z) = z := by
    change ((inv j ≫ j) z) = z
    rw [IsIso.inv_hom_id]
    rfl
  let η : FiberCycleGroup
      (pullback.snd f g) t r →+
      FiberCycleGroup f (g t) r := {
    toFun := fun c => ⟨
      AlgebraicCycle.map j (fun _ : f'.fiber t => 0)
        (fun _ : f.fiber (g t) => 0) c.1,
      by
        rw [mem_cyclesOfDimension]
        intro Z hZ
        let z := Z.isIrreducible.genericPoint
        have hc : c.1 (inv j z) ≠ 0 := by
          simpa [algebraicCycle_map_iso_apply] using hZ
        let Z' : IrreducibleCloseds (f'.fiber t) :=
          ⟨closure ({inv j z} : Set (f'.fiber t)),
            isIrreducible_singleton.closure, isClosed_closure⟩
        have hgp : IsGenericPoint (inv j z) (Z' : Set (f'.fiber t)) := by
          change closure ({inv j z} : Set (f'.fiber t)) = _
          rfl
        have hpoint : Z'.isIrreducible.genericPoint = inv j z :=
          (Z'.isIrreducible.isGenericPoint_genericPoint Z'.isClosed).eq hgp
        have hc' : c.1 Z'.isIrreducible.genericPoint ≠ 0 := by
          simpa [hpoint] using hc
        have hdimold : relativeDimension Cx.dimensionFunction sX (inv j z) = r := by
          rw [← deltaDimension_eq_of_isGenericPoint Cx sX Z' (inv j z) hgp]
          exact (mem_cyclesOfDimension Cx sX r c.1).mp c.2 Z' hc'
        rw [deltaDimension_eq_of_isGenericPoint Cy sY Z z
          (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed)]
        simpa [hright] using (hdim (inv j z)).symm.trans hdimold
      ⟩
    map_zero' := by
      ext z
      simp [algebraicCycle_map_iso_apply]
    map_add' a b := by
      ext z
      simp [algebraicCycle_map_iso_apply]
  }
  let θ : FiberCycleGroup f (g t) r →+
      FiberCycleGroup
        (pullback.snd f g) t r := {
    toFun := fun c => ⟨
      AlgebraicCycle.map (asIso j).inv (fun _ : f.fiber (g t) => 0)
        (fun _ : f'.fiber t => 0) c.1,
      by
        rw [mem_cyclesOfDimension]
        intro Z hZ
        let z := Z.isIrreducible.genericPoint
        have hc : c.1 (j z) ≠ 0 := by
          simpa [algebraicCycle_map_iso_apply] using hZ
        let Z' : IrreducibleCloseds (f.fiber (g t)) :=
          ⟨closure ({j z} : Set (f.fiber (g t))),
            isIrreducible_singleton.closure, isClosed_closure⟩
        have hgp : IsGenericPoint (j z) (Z' : Set (f.fiber (g t))) := by
          change closure ({j z} : Set (f.fiber (g t))) = _
          rfl
        have hpoint : Z'.isIrreducible.genericPoint = j z :=
          (Z'.isIrreducible.isGenericPoint_genericPoint Z'.isClosed).eq hgp
        have hc' : c.1 Z'.isIrreducible.genericPoint ≠ 0 := by
          simpa [hpoint] using hc
        have hdimold : relativeDimension Cy.dimensionFunction sY (j z) = r := by
          rw [← deltaDimension_eq_of_isGenericPoint Cy sY Z' (j z) hgp]
          exact (mem_cyclesOfDimension Cy sY r c.1).mp c.2 Z' hc'
        rw [deltaDimension_eq_of_isGenericPoint Cx sX Z z
          (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed)]
        exact (hdim z).trans hdimold
      ⟩
    map_zero' := by
      ext z
      simp [algebraicCycle_map_iso_apply]
    map_add' a b := by
      ext z
      simp [algebraicCycle_map_iso_apply]
  }
  have hηθ (c : FiberCycleGroup
      (pullback.snd f g) t r) : θ (η c) = c := by
    apply Subtype.ext
    ext z
    simp [θ, η, algebraicCycle_map_iso_apply, hleft]
  have hθη (c : FiberCycleGroup
      f (g t) r) : η (θ c) = c := by
    apply Subtype.ext
    ext z
    simp [θ, η, algebraicCycle_map_iso_apply, hright]
  exact {
    toFun := θ
    invFun := η
    left_inv := hθη
    right_inv := hηθ
    map_add' := θ.map_add
  }

/-- The fibrewise base-change equivalence transports coefficients along the canonical map of
fibres. -/
theorem fiberCycleAddEquiv_apply
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (t : S') (hres : IsIso (g.residueFieldMap t)) (r : ℕ)
    (c : FiberCycleGroup f (g t) r)
    (x : (pullback.snd f g).fiber t) :
    ((fiberCycleAddEquiv f g t hres r c :
      FiberCycleGroup
        (pullback.snd f g) t r) : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
      (c : AlgebraicCycle (f.fiber (g t)) ℤ)
        (restrictedFiberMap f
          (pullback.snd f g) (pullback.fst f g) g pullback.condition t x) := by
  classical
  let j := restrictedFiberMap f
    (pullback.snd f g) (pullback.fst f g) g pullback.condition t
  have : IsIso j := @AlgebraicGeometry.isIso_baseChangeFiberMap _ _ _ f g t hres
  change (AlgebraicCycle.map (asIso j).inv (fun _ => 0) (fun _ => 0) c.1) x =
    c.1 (j x)
  simp [algebraicCycle_map_iso_apply]

/-- Reindexing a family of fibrewise cycles along a bijection of base points: a family indexed
by points of `S` is the same as a family indexed by points of `S'`. -/
def familyReindexAddEquiv
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (hg : Function.Bijective g) (r : ℕ) :
    FamilyOfCycles f r ≃+ (∀ t : S', FiberCycleGroup f (g t) r) := by
  let eg : S' ≃ S := Equiv.ofBijective g hg
  let P (s : S) := FiberCycleGroup f s r
  let eidx : (∀ s : S, P s) ≃ ∀ t : S', P (g t) := by
    change (∀ s : S, P s) ≃ ∀ t : S', P (eg t)
    exact (Equiv.piCongrLeft P eg).symm
  exact {
    toFun := eidx
    invFun := eidx.symm
    left_inv := eidx.left_inv
    right_inv := eidx.right_inv
    map_add' _ _ := rfl }

/-- Reindexing evaluates a family at the image point. -/
theorem familyReindexAddEquiv_apply
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (hg : Function.Bijective g) (r : ℕ)
    (α : FamilyOfCycles f r) (t : S') :
    familyReindexAddEquiv f g hg r α t = α (g t) := by
  change (Equiv.piCongrLeft (fun s : S => FiberCycleGroup f s r)
    (Equiv.ofBijective g hg)).symm α t = α (g t)
  rw [Equiv.piCongrLeft_symm_apply]
  rfl

/-- Base change along a morphism that is bijective on points and
induces isomorphisms of residue fields identifies the groups of families of cycles on the
fibres. -/
@[stacks 0H4Y "the additive equivalence"]
def baseChangeFamilyOfCyclesAddEquiv
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (hg : Function.Bijective g)
    (hres : ∀ t : S', IsIso (g.residueFieldMap t)) (r : ℕ) :
    FamilyOfCycles f r ≃+ FamilyOfCycles (pullback.snd f g) r :=
  (familyReindexAddEquiv f g hg r).trans
    (AddEquiv.piCongrRight fun t => fiberCycleAddEquiv f g t (hres t) r)

/-- The base-changed family has, on each fibre, the coefficients
of the original family transported along the canonical map of fibres. -/
@[stacks 0H4Y "the coefficient formula"]
theorem baseChangeFamilyOfCyclesAddEquiv_apply
    {X S S' : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (hg : Function.Bijective g)
    (hres : ∀ t : S', IsIso (g.residueFieldMap t)) (r : ℕ)
    (α : FamilyOfCycles f r) (t : S') (x : (pullback.snd f g).fiber t) :
    ((baseChangeFamilyOfCyclesAddEquiv f g hg hres r α) t :
      AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
        (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ)
          (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
            pullback.condition t x) := by
  change ((fiberCycleAddEquiv f g t (hres t) r (familyReindexAddEquiv f g hg r α t) :
    FiberCycleGroup (pullback.snd f g) t r) :
      AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x = _
  rw [familyReindexAddEquiv_apply]
  exact fiberCycleAddEquiv_apply f g t (hres t) r (α (g t)) x

/-! ### Base change of families of cycles along an arbitrary morphism of bases -/

variable {X S S' : Scheme.{u}}

/-- The structure morphism from a scheme-theoretic fibre to the spectrum of the residue
field of the base point is locally of finite type. -/
@[ega "I 6.4.11" "partial"]
instance locallyOfFiniteType_fiberToSpecResidueField_baseChange {A B : Scheme.{u}} (p : A ⟶ B)
    [LocallyOfFiniteType p] (b : B) : LocallyOfFiniteType (p.fiberToSpecResidueField b) := by
  change LocallyOfFiniteType (pullback.snd p (B.fromSpecResidueField b))
  infer_instance

/-- A coefficient function of the shape "coefficient of a cycle at the image point times the
multiplicity of the point in the inverse image of the reduced closure of that image" has
locally finite support. -/
private theorem locallyFiniteSupport_mul_comapClosureCoeff (C : ChowSituation.{u})
    {X' Y : Scheme.{u}} (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (q : X' ⟶ Y) (j : ℤ)
    (c : AlgebraicCycle Y ℤ) :
    LocallyFiniteSupport (fun x' ↦ c (q.base x') * closedSubschemeCycleCoeff C sX'
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({q.base x'} : Set Y))).comap q).subschemeι) j x') := by
  classical
  intro x'
  obtain ⟨V, hV, hVfinite⟩ := Function.locallyFinsupp.locallyFiniteSupport c (q.base x')
  set I : Finset Y := hVfinite.toFinset with hI
  set a : Y → X' → ℤ := fun y z ↦ closedSubschemeCycleCoeff C sX'
    (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set Y))).comap q).subschemeι) j z with ha
  have hloc : ∀ y ∈ I, ∃ t ∈ nhds x', (t ∩ Function.support (a y)).Finite := fun y _ ↦
    closedSubschemeCycleCoeff_locallyFiniteSupport C sX'
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set Y))).comap q).subschemeι) j x'
  choose! t ht hfin using hloc
  refine ⟨q.base ⁻¹' V ∩ ⋂ y ∈ I, t y,
    Filter.inter_mem (q.continuous.continuousAt hV)
      ((Filter.biInter_finset_mem I).2 ht), ?_⟩
  refine (Set.Finite.biUnion I.finite_toSet fun y hy ↦ hfin y hy).subset fun z hz ↦ ?_
  have hprod := mul_ne_zero_iff.1 (Function.mem_support.1 hz.2)
  have hmemI : q.base z ∈ I := (Set.Finite.mem_toFinset hVfinite).2 ⟨hz.1.1, hprod.1⟩
  exact Set.mem_biUnion hmemI ⟨Set.mem_iInter₂.1 hz.1.2 _ hmemI,
    Function.mem_support.2 hprod.2⟩

/-- A point carrying a nonzero coefficient of the cycle of a closed subscheme has the
prescribed relative dimension. -/
private theorem relativeDimension_of_closedSubschemeCycleCoeff_ne_zero (C : ChowSituation.{u})
    {Y Z : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q] (i : Z ⟶ Y) [IsClosedImmersion i]
    (j : ℤ) (y : Y) (h : closedSubschemeCycleCoeff C q i j y ≠ 0) :
    relativeDimension C.dimensionFunction q y = j := by
  unfold closedSubschemeCycleCoeff at h
  split at h
  · rename_i hex
    exact hex.choose_spec.2
  · exact absurd rfl h

/-- The coefficient at `x` of the base change along `g : S' ⟶ S` of a family of `r`-cycles on
the fibres of `X/S`: the coefficient of the family at the image of `x` in the fibre over `g t`,
times the multiplicity of `x` in the inverse image of the reduced closure of that image. -/
def baseChangeFamilyCoeff (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ)
    (α : FamilyOfCycles f r) (t : S') (x : (pullback.snd f g).fiber t) : ℤ :=
  (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ)
      (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x) *
    closedSubschemeCycleCoeff (fieldChowSituation ↥(S'.residueField t))
      ((pullback.snd f g).fiberToSpecResidueField t)
      (((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
        ({restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x} :
          Set (f.fiber (g t))))).comap
        (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
          pullback.condition t)).subschemeι) (r : ℤ) x

/-- The coefficient function of a base-changed family has locally finite support. -/
theorem baseChangeFamilyCoeff_locallyFiniteSupport (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) (t : S') :
    LocallyFiniteSupport (baseChangeFamilyCoeff f g r α t) :=
  locallyFiniteSupport_mul_comapClosureCoeff (fieldChowSituation ↥(S'.residueField t))
    ((pullback.snd f g).fiberToSpecResidueField t)
    (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t) (r : ℤ)
    (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ)

/-- A point carrying a nonzero coefficient of a base-changed family has relative dimension `r`
in its fibre. -/
theorem relativeDimension_of_baseChangeFamilyCoeff_ne_zero (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (r : ℕ) (α : FamilyOfCycles f r) (t : S')
    (x : (pullback.snd f g).fiber t) (hx : baseChangeFamilyCoeff f g r α t x ≠ 0) :
    relativeDimension (fieldChowSituation ↥(S'.residueField t)).dimensionFunction
      ((pullback.snd f g).fiberToSpecResidueField t) x = (r : ℤ) :=
  relativeDimension_of_closedSubschemeCycleCoeff_ne_zero
    (fieldChowSituation ↥(S'.residueField t))
    ((pullback.snd f g).fiberToSpecResidueField t) _ (r : ℤ) x
    (right_ne_zero_of_mul (a := (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ)
      (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x)) hx)

/-- The base change along an arbitrary morphism `g : S' ⟶ S` of a family of `r`-cycles on the
fibres of `X/S`: the cycle on the fibre over `t` is the base change of the cycle over `g t` along
the residue field extension `κ(t)/κ(g t)`. -/
def baseChangeFamily (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ)
    (α : FamilyOfCycles f r) : FamilyOfCycles (pullback.snd f g) r := fun t =>
  ⟨⟨baseChangeFamilyCoeff f g r α t, fun _ _ ↦ trivial, fun x _ ↦
      baseChangeFamilyCoeff_locallyFiniteSupport f g r α t x⟩,
    (mem_cyclesOfDimension_iff_forall_point _ _ _ _).2 fun x hx ↦
      relativeDimension_of_baseChangeFamilyCoeff_ne_zero f g r α t x hx⟩

/-- The fibrewise coefficient formula for the base change of a family of cycles on fibres: the
coefficient of `α` at the image point, times the multiplicity with which the point occurs in the
residue-field base change of the reduced closure of that image. -/
theorem baseChangeFamily_apply (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ)
    (α : FamilyOfCycles f r) (t : S') (x : (pullback.snd f g).fiber t) :
    (baseChangeFamily f g r α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
      (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ)
          (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t x) *
        closedSubschemeCycleCoeff (fieldChowSituation ↥(S'.residueField t))
          ((pullback.snd f g).fiberToSpecResidueField t)
          (((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
            ({restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
              pullback.condition t x} : Set (f.fiber (g t))))).comap
            (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
              pullback.condition t)).subschemeι) (r : ℤ) x :=
  rfl

/-- For every point `s` of `S` there is a point `s'` of `S'` with `g s' = s` such that `κ(s')` is
a separable extension of `κ(s)`, the extension being the one given by the induced map on residue
fields. -/
def HasSeparableResidueFieldPoints (g : S' ⟶ S) : Prop :=
  ∀ s : S, ∃ s' : S', g s' = s ∧
    letI : Algebra (S.residueField (g s')) (S'.residueField s') :=
      (g.residueFieldMap s').hom.toAlgebra
    Algebra.IsSeparableExtension (S.residueField (g s')) (S'.residueField s')

/-- A morphism `g` satisfying `Stacks.Chow.HasSeparableResidueFieldPoints` is surjective. -/
theorem surjective_of_hasSeparableResidueFieldPoints {g : S' ⟶ S}
    (hg : HasSeparableResidueFieldPoints g) : Surjective g :=
  ⟨fun s ↦ ⟨(hg s).choose, (hg s).choose_spec.1⟩⟩

/-- The dimension function of the Chow situation of a field vanishes at every point of the
spectrum of that field. -/
private alias fieldChowDimensionZero := fieldChowSituation_dimensionFunction_eq_zero

/-- A point carrying a nonzero coefficient of a cycle of delta-dimension `r` has relative
dimension `r`. -/
lemma relativeDimension_of_cycle_coeff_ne_zero
    (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (q : Y ⟶ C.S) [LocallyOfFiniteType q] (r : ℤ)
    (c : Stacks.Chow.CycleGroup C q r) (y : Y) (hy : c.1 y ≠ 0) :
    relativeDimension C.dimensionFunction q y = r := by
  let Z : TopologicalSpace.IrreducibleCloseds Y :=
    ⟨closure ({y} : Set Y), isIrreducible_singleton.closure, isClosed_closure⟩
  have he : Z.isIrreducible.genericPoint = y :=
    (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).eq (isGenericPoint_closure)
  have hd := c.2 Z (by simpa only [he] using hy)
  simpa only [Stacks.Chow.deltaDimension, he] using hd

/-- Over a field, a point of relative dimension `r` has residue field of transcendence degree
`r` over that field. -/
private lemma trdeg_eq_of_relativeDimension_aux
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of k)) (hq : LocallyOfFiniteType q) (r : ℕ) (y : Y)
    (hrel : relativeDimension
      (fieldChowSituation k).dimensionFunction
      q y = r) :
    (letI := (q.residueFieldMap y).hom.toAlgebra
     Algebra.trdeg ((Spec (.of k)).residueField (q y)) (Y.residueField y) = r) := by
  let := hq
  let k' := (Spec (.of k)).residueField (q y)
  let : Algebra k' (Y.residueField y) := (q.residueFieldMap y).hom.toAlgebra
  have hnat : Cardinal.toNat (Algebra.trdeg k' (Y.residueField y)) = r := by
    rw [relativeDimension] at hrel
    dsimp only at hrel
    rw [fieldChowDimensionZero k (q y), zero_add] at hrel
    exact_mod_cast hrel
  let : Algebra.EssFiniteType k' (Y.residueField y) :=
    RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap q y)
  exact (Cardinal.toNat_eq_iff_of_lt_aleph0 r (trdeg_lt_aleph0 _ _)).mp hnat

/-- Over a field, a point carrying a nonzero coefficient of an `r`-cycle has residue field of
transcendence degree `r` over that field. -/
lemma trdeg_eq_of_cycle_coeff_ne_zero
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of k)) (hq : LocallyOfFiniteType q) (r : ℕ) (y : Y)
    (c : Stacks.Chow.CycleGroup
      (fieldChowSituation k) q (r : ℤ))
    (hy : c.1 y ≠ 0) :
    (letI := (q.residueFieldMap y).hom.toAlgebra
     Algebra.trdeg ((Spec (.of k)).residueField (q y)) (Y.residueField y) = r) := by
  let := hq
  exact trdeg_eq_of_relativeDimension_aux q hq r y
    (relativeDimension_of_cycle_coeff_ne_zero (fieldChowSituation k) q (r : ℤ) c y hy)

/-- Over a field, a point whose residue field has transcendence degree `r` has relative
dimension `r`. -/
lemma relativeDimension_eq_of_trdeg
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of k)) [LocallyOfFiniteType q] (r : ℕ) (y : Y)
    (htr : letI := (q.residueFieldMap y).hom.toAlgebra
      Algebra.trdeg ((Spec (.of k)).residueField (q y)) (Y.residueField y) = r) :
      relativeDimension
        (fieldChowSituation k).dimensionFunction
        q y = r := by
  let k' := (Spec (.of k)).residueField (q y)
  let : Algebra k' (Y.residueField y) := (q.residueFieldMap y).hom.toAlgebra
  have hnat : Cardinal.toNat (Algebra.trdeg k' (Y.residueField y)) = r :=
    mod_cast congrArg Cardinal.toNat htr
  rw [relativeDimension]
  dsimp only
  rw [fieldChowDimensionZero k (q y), zero_add]
  exact_mod_cast hnat

/-- Over a field, a point of relative dimension `r` has residue field of transcendence degree
`r` over that field. -/
lemma trdeg_eq_of_relativeDimension
    {k : Type u} [Field k] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (.of k)) (hq : LocallyOfFiniteType q) (r : ℕ) (y : Y)
    (hrel : relativeDimension
      (fieldChowSituation k).dimensionFunction
      q y = r) :
    (letI := (q.residueFieldMap y).hom.toAlgebra
     Algebra.trdeg ((Spec (.of k)).residueField (q y)) (Y.residueField y) = r) :=
  trdeg_eq_of_relativeDimension_aux q hq r y hrel

/-- At the image of a generic point of a closed subscheme, the coefficient of the associated
cycle is nonzero as soon as that point has the prescribed relative dimension. -/
lemma closedSubschemeCycleCoeff_ne_zero_of_genericPoint
    (C : ChowSituation.{u}) {Y Z : Scheme.{u}}
    (q : Y ⟶ C.S) [LocallyOfFiniteType q]
    (i : Z ⟶ Y) [IsClosedImmersion i] (r : ℤ) (ξ : genericPoints Z)
    (hξ : relativeDimension C.dimensionFunction q (i ξ.1) = r) :
    closedSubschemeCycleCoeff C q i r (i ξ.1) ≠ 0 := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian q
  let : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian (i ≫ q)
  have hm := Stacks.Chow.componentMultiplicity_ne_zero i ξ
  unfold closedSubschemeCycleCoeff
  let h : ∃ η : genericPoints Z,
      i η.1 = i ξ.1 ∧ relativeDimension C.dimensionFunction q (i ξ.1) = r :=
    ⟨ξ, rfl, hξ⟩
  rw [dite_eq_left h]
  have hchoose : Classical.choose h = ξ :=
    Subtype.ext (i.isClosedEmbedding.injective (Classical.choose_spec h).1)
  rwa [hchoose]

/-- In a sober `T0` space a point is a generic point of an irreducible component exactly when
it has no proper generalisation. -/
private lemma mem_genericPoints_iff_no_strict_generalization
    {Y : Type*} [TopologicalSpace Y] [T0Space Y] [QuasiSober Y] (y : Y) :
    y ∈ genericPoints Y ↔ ∀ y' : Y, Specializes y' y → y' = y := by
  refine ⟨fun hy y' hy'y ↦ (hy'y.antisymm (specializes_iff_closure_subset.mpr
    ((genericPoints.component ⟨y, hy⟩).2.2 isIrreducible_singleton.closure
      hy'y.closure_subset))).eq, fun h ↦ ?_⟩
  let Z : irreducibleComponents Y :=
    ⟨irreducibleComponent y, irreducibleComponent_mem_irreducibleComponents y⟩
  let ξ := genericPoints.ofComponent Z
  exact h ξ.1 ((genericPoints.isGenericPoint_ofComponent Z).specializes
    mem_irreducibleComponent) ▸ ξ.2

/-- Let `Y' = Y ×_k K` be the base change of a scheme locally of finite type over a field `k`
along a field extension `K/k`. A point `y` of `Y'` whose residue field has the same
transcendence degree over `K` as that of its image `x` has over `k` is a generic point of the
base change of the reduced closure of `x`. -/
lemma pullbackPoint_generic_in_pointClosure
    {k K : Type u} [Field k] [Field K]
    {Y Y' : Scheme.{u}} (q : Y ⟶ Spec (.of k)) (q' : Y' ⟶ Spec (.of K))
    (m : Y' ⟶ Y) (φ : Spec (.of K) ⟶ Spec (.of k))
    (hPB : IsPullback m q' q φ) [LocallyOfFiniteType q] [LocallyOfFiniteType q']
    (x : Y) (y : Y') (hxy : m y = x)
    (htr : (letI := (q.residueFieldMap x).hom.toAlgebra
      letI := (q'.residueFieldMap y).hom.toAlgebra
      Algebra.trdeg ((Spec (.of k)).residueField (q x)) (Y.residueField x)) =
      (letI := (q'.residueFieldMap y).hom.toAlgebra
      Algebra.trdeg ((Spec (.of K)).residueField (q' y)) (Y'.residueField y))) :
    ∃ ξ : genericPoints (((Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({x} : Set Y))).comap m).subscheme),
      ((Scheme.IdealSheafData.vanishingIdeal
        (TopologicalSpace.Closeds.closure ({x} : Set Y))).comap m).subschemeι ξ.1 = y := by
  classical
  subst x
  let J := (Scheme.IdealSheafData.vanishingIdeal
    (TopologicalSpace.Closeds.closure ({m y} : Set Y))).comap m
  let : Algebra ((Spec (.of k)).residueField (q (m y))) (Y.residueField (m y)) :=
    (q.residueFieldMap (m y)).hom.toAlgebra
  let : Algebra ((Spec (.of K)).residueField (q' y)) (Y'.residueField y) :=
    (q'.residueFieldMap y).hom.toAlgebra
  have hyJ : y ∈ J.support := by
    rw [Scheme.IdealSheafData.support_comap]
    change m y ∈ (Scheme.IdealSheafData.vanishingIdeal
      (TopologicalSpace.Closeds.closure ({m y} : Set Y))).support
    exact (Set.ext_iff.mp (Scheme.IdealSheafData.coe_support_vanishingIdeal
      (TopologicalSpace.Closeds.closure ({m y} : Set Y))) (m y)).mpr
      (subset_closure (Set.mem_singleton (m y)))
  obtain ⟨yJ, hyEq⟩ : y ∈ Set.range J.subschemeι := by
    rwa [Scheme.IdealSheafData.range_subschemeι]
  have hyJGeneric : yJ ∈ genericPoints J.subscheme := by
    apply (mem_genericPoints_iff_no_strict_generalization yJ).2
    intro z hzy
    let z' := J.subschemeι z
    have hspec : z' ⤳ y := specializes_iff_mem_closure.mpr <| by
      simpa [z', hyEq] using mem_closure_image J.subschemeι.continuous.continuousAt
        (specializes_iff_mem_closure.mp hzy)
    have hzSupport : z' ∈ J.support := by
      change z' ∈ (J.support : Set Y')
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨z, rfl⟩
    have hzm : m z' ∈ TopologicalSpace.Closeds.closure ({m y} : Set Y) := by
      rwa [Scheme.IdealSheafData.support_comap] at hzSupport
    have hmz : m z' = m y :=
      ((hspec.map m.continuous).antisymm (specializes_iff_mem_closure.mpr hzm)).eq
    have hbase : φ (q' y) = q (m y) := by
      simpa using (congrArg (fun f : Y' ⟶ Spec (.of k) => f y) hPB.w).symm
    let xFiber := (q.fiberHomeo (φ (q' y))).symm ⟨m y, hbase.symm⟩
    have hxFiber : q.fiberι (φ (q' y)) xFiber = m y := by
      simp [xFiber]
    let ψ := AlgebraicGeometry.fiberMap q' m φ q hPB.w (q' y)
    let yFiber := q'.asFiber y
    let zFiber := (q'.fiberHomeo (q' y)).symm ⟨z', Subsingleton.elim _ _⟩
    have hψ_under (a : q'.fiber (q' y)) :
        q.fiberι (φ (q' y)) (ψ a) = m (q'.fiberι (q' y) a) := by
      change (ψ ≫ q.fiberι (φ (q' y))) a =
        (q'.fiberι (q' y) ≫ m) a
      rw [show ψ ≫ q.fiberι (φ (q' y)) = q'.fiberι (q' y) ≫ m by
        dsimp only [ψ, AlgebraicGeometry.fiberMap]
        apply pullback.lift_fst]
    have hψy : ψ yFiber = xFiber := by
      apply (q.fiberι (φ (q' y))).isEmbedding.injective
      rw [hψ_under, Scheme.Hom.fiberι_asFiber, hxFiber]
    have hψz : ψ zFiber = xFiber := by
      apply (q.fiberι (φ (q' y))).isEmbedding.injective
      rw [hψ_under, show q'.fiberι (q' y) zFiber = z' by simp [zFiber], hmz, hxFiber]
    have hzero :
        ringKrullDim ((ψ.fiber (ψ yFiber)).presheaf.stalk (ψ.asFiber yFiber)) = 0 := by
      let d := ringKrullDim ((ψ.fiber (ψ yFiber)).presheaf.stalk (ψ.asFiber yFiber))
      let c := (Cardinal.toENat
        (Algebra.trdeg ( (Spec (.of K)).residueField (q' y)) (Y'.residueField y)) : WithBot ℕ∞)
      have hdim :=
        AlgebraicGeometry.fiberMap_ringKrullDim_stalk_add_trdeg_eq hPB y
      have htr' := congrArg Cardinal.toENat htr
      have hdim' : d + c = c := by
        simpa [ψ, yFiber, d, c, htr'] using hdim
      let : Algebra.EssFiniteType ((Spec (.of K)).residueField (q' y))
          (Y'.residueField y) :=
        RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap q' y)
      have hcTop : c ≠ ⊤ := by
        dsimp [c]
        rw [WithBot.coe_eq_top]
        exact (Cardinal.toENat_lt_top.mpr (trdeg_lt_aleph0 _ _)).ne
      exact add_right_cancel_of_ne_top_of_ne_bot hcTop WithBot.coe_ne_bot
        (by simpa using hdim')
    have hspecFiber : zFiber ⤳ yFiber :=
      ((q'.fiberHomeo (q' y)).symm.isInducing.specializes_iff).mpr <|
        (subtype_specializes_iff _ _).2 (by simpa [zFiber, yFiber] using hspec)
    let d := (ψ.fiberHomeo (ψ yFiber)).symm ⟨yFiber, rfl⟩
    let d' := (ψ.fiberHomeo (ψ yFiber)).symm ⟨zFiber, hψz.trans hψy.symm⟩
    have hspecD : d' ⤳ d :=
      ((ψ.fiberHomeo (ψ yFiber)).symm.isInducing.specializes_iff).mpr <|
        (subtype_specializes_iff _ _).2 (by simpa [d, d'] using hspecFiber)
    have hzFiber : zFiber = yFiber := by
      simpa [d, d'] using congrArg (ψ.fiberι (ψ yFiber))
        (eq_of_specializes_of_ringKrullDim_stalk_eq_zero hspecD hzero)
    have hzyPoint : z' = y := by
      simpa [yFiber, zFiber] using congrArg (q'.fiberι (q' y)) hzFiber
    apply J.subschemeι.isEmbedding.injective
    simpa [z', hyEq] using hzyPoint
  exact ⟨⟨yJ, hyJGeneric⟩, hyEq⟩

/-- A point `x` of the fibre of `f` over `g t` of relative dimension `r` is the image of a point
`y` of the fibre of the base change over `t` at which the multiplicity entering the coefficient
formula `Stacks.Chow.baseChangeFamily_apply` is nonzero. -/
private theorem exists_fiber_point_coeff_ne_zero_aux (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ) (t : S') (x : f.fiber (g t))
    (hx : relativeDimension (fieldChowSituation ↥(S.residueField (g t))).dimensionFunction
      (f.fiberToSpecResidueField (g t)) x = (r : ℤ)) :
    ∃ y : (pullback.snd f g).fiber t,
      restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t y = x ∧
        closedSubschemeCycleCoeff (fieldChowSituation ↥(S'.residueField t))
          ((pullback.snd f g).fiberToSpecResidueField t)
          (((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
            ({x} : Set (f.fiber (g t))))).comap
            (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
              pullback.condition t)).subschemeι) (r : ℤ) y ≠ 0 := by
  classical
  let f' := pullback.snd f g
  let q := f.fiberToSpecResidueField (g t)
  let q' := f'.fiberToSpecResidueField t
  let m := restrictedFiberMap f f' (pullback.fst f g) g pullback.condition t
  let φ := Spec.map (g.residueFieldMap t)
  have hq : LocallyOfFiniteType q := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (g t)))
    infer_instance
  have hq' : LocallyOfFiniteType q' := by
    change LocallyOfFiniteType (pullback.snd f' (S'.fromSpecResidueField t))
    infer_instance
  have hPB : IsPullback m q' q φ :=
    isPullback_fiberToSpecResidueField_of_isPullback (IsPullback.of_hasPullback f g) t
  have hsurj : Surjective φ := ⟨fun _ ↦ ⟨⟨⊥, Ideal.isPrime_bot⟩, Subsingleton.elim _ _⟩⟩
  have htr := @trdeg_eq_of_relativeDimension ↥(S.residueField (g t)) inferInstance
    (f.fiber (g t)) q hq r x hx
  obtain ⟨y, hy, hyr⟩ :=
    @AlgebraicGeometry.exists_preimage_preserving_residueField_trdeg _ _ _ _ m q' q φ hPB hq
      hsurj r x htr
  subst hy
  refine ⟨y, rfl, ?_⟩
  obtain ⟨ξ, hξ⟩ := @pullbackPoint_generic_in_pointClosure ↥(S.residueField (g t))
    ↥(S'.residueField t) inferInstance inferInstance (f.fiber (g t)) (f'.fiber t) q q' m φ hPB
    hq hq' (m y) y rfl (htr.trans hyr.symm)
  have hdim := @relativeDimension_eq_of_trdeg ↥(S'.residueField t) inferInstance (f'.fiber t)
    q' hq' r y hyr
  have hcoeff := @closedSubschemeCycleCoeff_ne_zero_of_genericPoint
    (fieldChowSituation ↥(S'.residueField t)) (f'.fiber t) _ q' hq'
    (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({m y} : Set (f.fiber (g t))))).comap m).subschemeι) inferInstance
    (r : ℤ) ξ (by rwa [hξ])
  rwa [hξ] at hcoeff

/-- Base change of families of `r`-cycles on the fibres of `X / S` along a surjective morphism
`g : S' ⟶ S` is injective: if `g^*α₁ = g^*α₂` then `α₁ = α₂`. -/
@[stacks 0H4X "injectivity of base change on families of cycles on fibres"]
theorem baseChangeFamily_injective (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S)
    [Surjective g] (r : ℕ) (α₁ α₂ : FamilyOfCycles f r)
    (h : baseChangeFamily f g r α₁ = baseChangeFamily f g r α₂) :
    α₁ = α₂ := by
  classical
  funext s
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  obtain ⟨t, ht⟩ := Scheme.Hom.surjective g s
  subst s
  by_cases hx : relativeDimension (fieldChowSituation ↥(S.residueField (g t))).dimensionFunction
      (f.fiberToSpecResidueField (g t)) x = (r : ℤ)
  · obtain ⟨y, hy, hcoeff⟩ := exists_fiber_point_coeff_ne_zero_aux f g r t x hx
    have hpoint : ((baseChangeFamily f g r α₁) t).1 y = ((baseChangeFamily f g r α₂) t).1 y :=
      congrArg (fun c : FiberCycleGroup (pullback.snd f g) t r ↦ c.1 y) (congrFun h t)
    rw [baseChangeFamily_apply f g r α₁ t y, baseChangeFamily_apply f g r α₂ t y, hy] at hpoint
    exact mul_right_cancel₀ hcoeff hpoint
  · have hzero (c : FiberCycleGroup f (g t) r) : c.1 x = 0 :=
      of_not_not fun hne ↦ hx (relativeDimension_of_cycle_coeff_ne_zero _ _ _ c x hne)
    rw [hzero (α₁ (g t)), hzero (α₂ (g t))]


/-- A point `x` of the fibre of `f` over `g t` of relative dimension `r` is the image of a point
`y` of the fibre of the base change over `t` at which the multiplicity entering the coefficient
formula `Stacks.Chow.baseChangeFamily_apply` is nonzero. -/
theorem exists_fiber_point_closedSubschemeCycleCoeff_ne_zero (f : X ⟶ S)
    [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ) (t : S') (x : f.fiber (g t))
    (hx : relativeDimension (fieldChowSituation ↥(S.residueField (g t))).dimensionFunction
      (f.fiberToSpecResidueField (g t)) x = (r : ℤ)) :
    ∃ y : (pullback.snd f g).fiber t,
      restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t y = x ∧
        closedSubschemeCycleCoeff (fieldChowSituation ↥(S'.residueField t))
          ((pullback.snd f g).fiberToSpecResidueField t)
          (((Scheme.IdealSheafData.vanishingIdeal (Closeds.closure
            ({x} : Set (f.fiber (g t))))).comap
            (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g
              pullback.condition t)).subschemeι) (r : ℤ) y ≠ 0 :=
  exists_fiber_point_coeff_ne_zero_aux f g r t x hx

end Stacks.Chow
