module

public import StacksCore.Tactic.StacksAttribute
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.FiniteOverStrictHenselization
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.SpecializationMorphism
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianRings.StrictHenselizationComponentLift

/-!
# The variety of vanishing cycles

Let `f : X ⟶ S` be a morphism of schemes, let `x` be a geometric point of `X` and let `s = f(x)`
be its image in `S`. The morphism `f` induces a unique morphism
`Spec(𝒪^sh_{X,x}) ⟶ Spec(𝒪^sh_{S,s})` of strict henselizations which lies over `f` and carries
the canonical geometric point of its source to the canonical geometric point of its target. For a
geometric point `t` of `Spec(𝒪^sh_{S,s})` the **variety of vanishing cycles** is the fibre

`F_{x,t} = t ×_{Spec(𝒪^sh_{S,s})} Spec(𝒪^sh_{X,x}) = Spec(𝒪^sh_{X,x} ⊗_{𝒪^sh_{S,s}} κ(t))`,

which sits in the commutative diagram `F_{x,t} ⟶ Spec(𝒪^sh_{X,x}) ⟶ X` over
`t ⟶ Spec(𝒪^sh_{S,s}) ⟶ S`.

## Main definitions

* `AlgebraicGeometry.etaleResidueFieldToGeometricField` embeds the residue field of the étale
  local ring at a geometric point into the residue field of that point.
* `AlgebraicGeometry.etaleResidueFieldSeparableClosureEquiv` identifies the residue field of the
  étale local ring with the separable closure of the residue field of the ordinary local ring
  inside the residue field of the geometric point.
* `AlgebraicGeometry.etaleLocalRingHom` is the induced homomorphism of étale local rings and
  `AlgebraicGeometry.strictHenselizationSquareMap` the induced morphism of strict henselizations.
  `AlgebraicGeometry.StrictHenselizationSquare` records that morphism together with its two
  compatibilities, and `AlgebraicGeometry.strictHenselizationSquare` is its canonical element.
* `AlgebraicGeometry.vanishingCyclesFibre` is the variety of vanishing cycles, with its
  projections `AlgebraicGeometry.vanishingCyclesFibreToGeometricPoint`,
  `AlgebraicGeometry.vanishingCyclesFibreToStrictHenselization` and
  `AlgebraicGeometry.vanishingCyclesFibreToSource`.

## Main results

* `AlgebraicGeometry.existsUnique_etaleLocalRingHom`: there is exactly one homomorphism of étale
  local rings compatible with the ordinary-to-étale germ maps and with evaluation of germs in the
  residue field of the geometric point.
* `AlgebraicGeometry.existsUnique_strictHenselizationSquareMap` is its geometric form, and
  `AlgebraicGeometry.StrictHenselizationSquare.eq_strictHenselizationSquare` says the canonical
  square is the only one.
* `AlgebraicGeometry.vanishingCyclesFibreToSource_comp` is the commutativity of the displayed
  diagram, and `AlgebraicGeometry.vanishingCyclesFibre_condition` of its left-hand square.

## Implementation notes

The residue field of the étale local ring is handled through its embedding into the residue field
of the geometric point: that embedding is injective and its range is exactly the separable closure
of the residue field of the ordinary local ring. The induced map on residue fields is therefore
pinned down by the two embeddings, and no choice of separable closure enters. This is also what
lets the characterization of the morphism of strict henselizations use only the two canonical maps
out of the étale local ring rather than a residue datum.

The homomorphism of étale local rings comes from the lifting property of a henselian local ring
along an ind-étale algebra: the étale local ring at `x` is strictly henselian and the étale local
ring at `s` is ind-étale over the ordinary local ring at `s`, which is what that property
consumes. The morphism of strict henselizations is its spectrum.

## References

* [Stacks Project, Tag 04HX](https://stacks.math.columbia.edu/tag/04HX)
* [Stacks Project, Tag 0GJM](https://stacks.math.columbia.edu/tag/0GJM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

attribute [local instance] structureSheafStalkToGeometricField_isLocalHom

/-! ### The residue field of an étale local ring -/

section ResidueField

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (s : GeometricPoint S)

/-- Evaluation of étale germs in the residue field of a geometric point, read on the residue
field of the étale local ring there. It is an embedding of fields. -/
public def etaleResidueFieldToGeometricField :
    ResidueField ↥(etaleLocalRing B S hS s) →+* s.residueField :=
  ResidueField.lift (structureSheafStalkToGeometricField B S hS s)

/-- The embedding of the residue field of the étale local ring into the residue field of the
geometric point recovers evaluation of étale germs. -/
public theorem etaleResidueFieldToGeometricField_residue (a : ↥(etaleLocalRing B S hS s)) :
    etaleResidueFieldToGeometricField B S hS s (residue ↥(etaleLocalRing B S hS s) a) =
      structureSheafStalkToGeometricField B S hS s a :=
  ResidueField.lift_residue_apply _ a

/-- The embedding of the residue field of the étale local ring into the residue field of the
geometric point is injective, being a homomorphism of fields. -/
public theorem etaleResidueFieldToGeometricField_injective :
    Function.Injective (etaleResidueFieldToGeometricField B S hS s) :=
  (etaleResidueFieldToGeometricField B S hS s).injective

/-- The residue field of the étale local ring at a geometric point is the separable closure of
the residue field of the ordinary local ring inside the residue field of that point. -/
public def etaleResidueFieldSeparableClosureEquiv :
    ↥(separableClosure
        (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
        s.residueField) ≃+* ResidueField ↥(etaleLocalRing B S hS s) :=
  (geometricHenselizationTower S s).strictHenselizationResidueEquiv.trans
    (ResidueField.mapEquiv (etaleLocalRingEquivStrictHenselization B S hS s))

/-- The identification of the residue field of the étale local ring with a separable closure is
the inclusion of that separable closure in the residue field of the geometric point. -/
public theorem etaleResidueFieldToGeometricField_separableClosureEquiv
    (u : ↥(separableClosure
      (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
      s.residueField)) :
    etaleResidueFieldToGeometricField B S hS s
        (etaleResidueFieldSeparableClosureEquiv B S hS s u) = (u : s.residueField) := by
  have hloc : IsLocalHom
      (etaleLocalRingEquivStrictHenselization B S hS s).toRingHom :=
    IsLocalHom.of_surjective _ (etaleLocalRingEquivStrictHenselization B S hS s).surjective
  obtain ⟨a, ha⟩ := residue_surjective
    (R := (geometricHenselizationTower S s).strictHenselization)
    ((geometricHenselizationTower S s).strictHenselizationResidueEquiv u)
  have h1 : etaleResidueFieldSeparableClosureEquiv B S hS s u =
      residue ↥(etaleLocalRing B S hS s)
        (etaleLocalRingEquivStrictHenselization B S hS s a) := by
    change ResidueField.mapEquiv (etaleLocalRingEquivStrictHenselization B S hS s)
      ((geometricHenselizationTower S s).strictHenselizationResidueEquiv u) = _
    rw [← ha]
    exact ResidueField.map_residue
      (etaleLocalRingEquivStrictHenselization B S hS s).toRingHom a
  rw [h1, etaleResidueFieldToGeometricField_residue,
    (etaleLocalRing_strictHenselization_canonical B S hS s
      (geometricHenselizationTower S s)).property.2 a, ha, RingEquiv.symm_apply_apply]

/-- Evaluation of an étale germ in the residue field of a geometric point lands in the separable
closure of the residue field of the ordinary local ring. -/
public theorem structureSheafStalkToGeometricField_mem_separableClosure
    (a : ↥(etaleLocalRing B S hS s)) :
    structureSheafStalkToGeometricField B S hS s a ∈
      separableClosure
        (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
        s.residueField := by
  obtain ⟨u, hu⟩ := (etaleResidueFieldSeparableClosureEquiv B S hS s).surjective
    (residue ↥(etaleLocalRing B S hS s) a)
  have h := etaleResidueFieldToGeometricField_separableClosureEquiv B S hS s u
  rw [hu, etaleResidueFieldToGeometricField_residue] at h
  rw [h]
  exact u.2

/-- The range of the embedding of the residue field of the étale local ring is the separable
closure of the residue field of the ordinary local ring in the residue field of the geometric
point. -/
@[ega "IV 18.8.6" "18.8.6.2"]
public theorem mem_range_etaleResidueFieldToGeometricField_iff (c : s.residueField) :
    c ∈ Set.range (etaleResidueFieldToGeometricField B S hS s) ↔
      c ∈ separableClosure
        (ResidueField ↥(S.presheaf.stalk (s.hom (closedPoint s.residueField))))
        s.residueField := by
  constructor
  · rintro ⟨d, rfl⟩
    obtain ⟨a, ha⟩ := residue_surjective (R := ↥(etaleLocalRing B S hS s)) d
    rw [← ha, etaleResidueFieldToGeometricField_residue]
    exact structureSheafStalkToGeometricField_mem_separableClosure B S hS s a
  · intro hc
    exact ⟨etaleResidueFieldSeparableClosureEquiv B S hS s ⟨c, hc⟩,
      etaleResidueFieldToGeometricField_separableClosureEquiv B S hS s ⟨c, hc⟩⟩

end ResidueField

/-! ### Factoring one field embedding through another -/

section Factor

variable {K L M : Type u} [Field K] [Field L] [Field M] (i : K →+* M) (j : L →+* M)
  (h : ∀ a, i a ∈ Set.range j)

/-- A choice of preimage under `j` of each value of `i`, available when every value of `i` is a
value of `j`. -/
private def rangeFactorFun : K → L := fun a => (h a).choose

/-- The chosen preimage has the prescribed image. -/
private theorem rangeFactorFun_spec (a : K) : j (rangeFactorFun i j h a) = i a :=
  (h a).choose_spec

/-- A homomorphism of fields all of whose values are attained by a second one factors through
that second homomorphism, uniquely since a homomorphism of fields is injective. -/
private def ringHomFactorOfRange : K →+* L where
  toFun := rangeFactorFun i j h
  map_one' := j.injective (((rangeFactorFun_spec i j h 1).trans (map_one i)).trans
    (map_one j).symm)
  map_mul' a b := j.injective ((((rangeFactorFun_spec i j h (a * b)).trans
    (map_mul i a b)).trans (congrArg₂ (· * ·) (rangeFactorFun_spec i j h a).symm
      (rangeFactorFun_spec i j h b).symm)).trans (map_mul j _ _).symm)
  map_zero' := j.injective (((rangeFactorFun_spec i j h 0).trans (map_zero i)).trans
    (map_zero j).symm)
  map_add' a b := j.injective ((((rangeFactorFun_spec i j h (a + b)).trans
    (map_add i a b)).trans (congrArg₂ (· + ·) (rangeFactorFun_spec i j h a).symm
      (rangeFactorFun_spec i j h b).symm)).trans (map_add j _ _).symm)

/-- The factorization of a field embedding through a second one composes back to the first. -/
private theorem ringHomFactorOfRange_spec (a : K) :
    j (ringHomFactorOfRange i j h a) = i a :=
  rangeFactorFun_spec i j h a

end Factor

/-! ### The induced homomorphism of étale local rings -/

section Square

variable (B : BigEtaleSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : X ⟶ S) (x : GeometricPoint X)

/-- An element of the residue field of a geometric point separable over the residue field of the
local ring at the image of that point is separable over the residue field at the point itself. -/
private theorem mem_separableClosure_of_mem_separableClosure_image
    (c : (x.map f).residueField)
    (hc : c ∈ separableClosure
      (ResidueField ↥(S.presheaf.stalk ((x.map f).hom (closedPoint (x.map f).residueField))))
      (x.map f).residueField) :
    c ∈ separableClosure
      (ResidueField ↥(X.presheaf.stalk (x.hom (closedPoint x.residueField))))
      x.residueField := by
  let KS := ResidueField
    ↥(S.presheaf.stalk ((x.map f).hom (closedPoint (x.map f).residueField)))
  let KX := ResidueField ↥(X.presheaf.stalk (x.hom (closedPoint x.residueField)))
  let _ : Algebra KS x.residueField := geometricResidueAlgebra S (x.map f)
  let _ : Algebra KS KX :=
    (f.residueFieldMap (x.hom (closedPoint x.residueField))).hom.toAlgebra
  have _ : IsScalarTower KS KX x.residueField :=
    IsScalarTower.of_algebraMap_eq fun r => ConcreteCategory.congr_hom
      (Scheme.descResidueField_stalkClosedPointTo_comp f x.hom) r
  exact separableClosure.le_restrictScalars KS KX x.residueField hc

/-- The homomorphism of residue fields of étale local rings induced by a morphism of schemes at a
geometric point of its source: the only one compatible with the two embeddings into the residue
field of that point. -/
private def etaleResidueFieldMap :
    ResidueField ↥(etaleLocalRing B S hS (x.map f)) →+*
      ResidueField ↥(etaleLocalRing B X hX x) :=
  ringHomFactorOfRange (etaleResidueFieldToGeometricField B S hS (x.map f))
    (etaleResidueFieldToGeometricField B X hX x) fun c => by
      have hc := (mem_range_etaleResidueFieldToGeometricField_iff B S hS (x.map f)
        (etaleResidueFieldToGeometricField B S hS (x.map f) c)).1 ⟨c, rfl⟩
      refine (mem_range_etaleResidueFieldToGeometricField_iff B X hX x _).2 ?_
      exact mem_separableClosure_of_mem_separableClosure_image f x _ hc

/-- The induced homomorphism of residue fields is compatible with the embeddings into the residue
field of the geometric point. -/
private theorem etaleResidueFieldToGeometricField_etaleResidueFieldMap
    (c : ResidueField ↥(etaleLocalRing B S hS (x.map f))) :
    etaleResidueFieldToGeometricField B X hX x (etaleResidueFieldMap B hX hS f x c) =
      etaleResidueFieldToGeometricField B S hS (x.map f) c :=
  ringHomFactorOfRange_spec _ _ _ c

/-- Evaluating an ordinary germ at the image of a geometric point in the residue field of that
point is evaluating its image under the stalk map. -/
private theorem toGeometricField_comp_fromLocalRing_stalkMap :
    (structureSheafStalkToGeometricField B S hS (x.map f)).comp
        (structureSheafStalkFromLocalRing B S hS (x.map f)) =
      ((structureSheafStalkToGeometricField B X hX x).comp
        (structureSheafStalkFromLocalRing B X hX x)).comp
          (f.stalkMap (x.hom (closedPoint x.residueField))).hom := by
  refine RingHom.ext fun r => ?_
  have h1 := ConcreteCategory.congr_hom
    (ofHom_toGeometricField_comp_fromLocalRing B S hS (x.map f)) r
  have h2 := ConcreteCategory.congr_hom (Scheme.stalkClosedPointTo_comp x.hom f) r
  have h3 := ConcreteCategory.congr_hom
    (ofHom_toGeometricField_comp_fromLocalRing B X hX x)
    ((f.stalkMap (x.hom (closedPoint x.residueField))).hom r)
  exact h1.trans (h2.trans h3.symm)

/-- **The homomorphism of étale local rings induced by a morphism of schemes.** There is exactly
one homomorphism from the étale local ring at the image of a geometric point to the étale local
ring at that point which is compatible with the ordinary-to-étale germ maps and with evaluation
of germs in the residue field of the point. -/
public theorem existsUnique_etaleLocalRingHom :
    ∃! g : ↥(etaleLocalRing B S hS (x.map f)) →+* ↥(etaleLocalRing B X hX x),
      g.comp (structureSheafStalkFromLocalRing B S hS (x.map f)) =
          (structureSheafStalkFromLocalRing B X hX x).comp
            (f.stalkMap (x.hom (closedPoint x.residueField))).hom ∧
        (structureSheafStalkToGeometricField B X hX x).comp g =
          structureSheafStalkToGeometricField B S hS (x.map f) := by
  let z : X := x.hom (closedPoint x.residueField)
  let RS := ↥(S.presheaf.stalk ((x.map f).hom (closedPoint (x.map f).residueField)))
  let AS := ↥(etaleLocalRing B S hS (x.map f))
  let AX := ↥(etaleLocalRing B X hX x)
  let φ := etaleResidueFieldMap B hX hS f x
  let εS := structureSheafStalkToGeometricField B S hS (x.map f)
  let εX := structureSheafStalkToGeometricField B X hX x
  let ηS := structureSheafStalkFromLocalRing B S hS (x.map f)
  let ηX := structureSheafStalkFromLocalRing B X hX x
  let σ := (f.stalkMap z).hom
  let _ : Algebra RS AX := (ηX.comp σ).toAlgebra
  have halg : algebraMap RS AX = ηX.comp σ := RingHom.algebraMap_toAlgebra _
  let _ : Algebra RS (ResidueField AX) := ((residue AX).comp (algebraMap RS AX)).toAlgebra
  have halgK : algebraMap RS (ResidueField AX) = (residue AX).comp (algebraMap RS AX) :=
    RingHom.algebraMap_toAlgebra _
  have hbaseres : ∀ r : RS, φ (residue AS (ηS r)) = residue AX (algebraMap RS AX r) := by
    intro r
    refine etaleResidueFieldToGeometricField_injective B X hX x ?_
    rw [etaleResidueFieldToGeometricField_etaleResidueFieldMap,
      etaleResidueFieldToGeometricField_residue, etaleResidueFieldToGeometricField_residue,
      halg]
    exact congrArg (fun k : RS →+* x.residueField => k r)
      (toGeometricField_comp_fromLocalRing_stalkMap B hX hS f x)
  let p : AS →ₐ[RS] ResidueField AX :=
    { toRingHom := φ.comp (residue AS)
      commutes' := fun r => by rw [halgK]; exact hbaseres r }
  let p' : AX →ₐ[RS] ResidueField AX :=
    { toRingHom := residue AX, commutes' := fun r => by rw [halgK]; rfl }
  have hind : (CommAlgCat.etale.{u} RS).ind.{u} (CommAlgCat.of RS AS) :=
    StacksDraft.indEtale_iff.mp (indEtale_etaleLocalRing B S hS (x.map f))
  obtain ⟨g, hg, hgu⟩ := HenselianLocalRing.existsUnique_algHom_comp_of_ind_etale
    hind p p' residue_surjective
  have hiff : ∀ k : AS →+* AX, (residue AX).comp k = φ.comp (residue AS) ↔ εX.comp k = εS := by
    intro k
    have hεX : εX = (etaleResidueFieldToGeometricField B X hX x).comp (residue AX) :=
      RingHom.ext fun a => (etaleResidueFieldToGeometricField_residue B X hX x a).symm
    have hεS : εS = (etaleResidueFieldToGeometricField B X hX x).comp (φ.comp (residue AS)) :=
      RingHom.ext fun a =>
        ((etaleResidueFieldToGeometricField_etaleResidueFieldMap B hX hS f x _).trans
          (etaleResidueFieldToGeometricField_residue B S hS (x.map f) a)).symm
    rw [hεX, hεS, RingHom.comp_assoc,
      RingHom.cancel_left (etaleResidueFieldToGeometricField_injective B X hX x)]
  refine ⟨(g : AS →+* AX), ⟨RingHom.ext fun r => g.commutes r,
    (hiff _).1 (congrArg AlgHom.toRingHom hg)⟩, ?_⟩
  rintro k ⟨hkbase, hkpoint⟩
  have hkres := (hiff k).2 hkpoint
  let kAlg : AS →ₐ[RS] AX :=
    { toRingHom := k, commutes' := fun r => congrArg (fun m : RS →+* AX => m r) hkbase }
  have hcomp : p'.comp kAlg = p := AlgHom.ext fun a =>
    congrArg (fun m : AS →+* ResidueField AX => m a) hkres
  exact congrArg AlgHom.toRingHom (hgu kAlg hcomp)

/-- The homomorphism of étale local rings induced by a morphism of schemes at a geometric point
of its source. -/
public def etaleLocalRingHom :
    ↥(etaleLocalRing B S hS (x.map f)) →+* ↥(etaleLocalRing B X hX x) :=
  (existsUnique_etaleLocalRingHom B hX hS f x).choose

/-- The induced homomorphism of étale local rings is compatible with the ordinary-to-étale germ
maps. -/
public theorem etaleLocalRingHom_comp_fromLocalRing :
    (etaleLocalRingHom B hX hS f x).comp (structureSheafStalkFromLocalRing B S hS (x.map f)) =
      (structureSheafStalkFromLocalRing B X hX x).comp
        (f.stalkMap (x.hom (closedPoint x.residueField))).hom :=
  (existsUnique_etaleLocalRingHom B hX hS f x).choose_spec.1.1

/-- The induced homomorphism of étale local rings is compatible with evaluation of germs in the
residue field of the geometric point. -/
public theorem toGeometricField_comp_etaleLocalRingHom :
    (structureSheafStalkToGeometricField B X hX x).comp (etaleLocalRingHom B hX hS f x) =
      structureSheafStalkToGeometricField B S hS (x.map f) :=
  (existsUnique_etaleLocalRingHom B hX hS f x).choose_spec.1.2

/-! ### The canonical square of strict henselizations -/

/-- The morphism of strict henselizations induced by a morphism of schemes at a geometric point
of its source: the spectrum of the induced homomorphism of étale local rings. -/
@[sga "4 XV 1.10", sga "4½ Th_finitude 2.11", sga "7 XIII 2.1.3" "partial"]
public def strictHenselizationSquareMap :
    strictHenselization B X hX x ⟶ strictHenselization B S hS (x.map f) :=
  Spec.map (CommRingCat.ofHom (etaleLocalRingHom B hX hS f x))

/-- The induced morphism of strict henselizations lies over the morphism of schemes. -/
public theorem strictHenselizationSquareMap_comp :
    strictHenselizationSquareMap B hX hS f x ≫ strictHenselizationToBase B S hS (x.map f) =
      strictHenselizationToBase B X hX x ≫ f := by
  have hb : CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS (x.map f)) ≫
      CommRingCat.ofHom (etaleLocalRingHom B hX hS f x) =
      f.stalkMap (x.hom (closedPoint x.residueField)) ≫
        CommRingCat.ofHom (structureSheafStalkFromLocalRing B X hX x) :=
    CommRingCat.hom_ext_iff.mpr (etaleLocalRingHom_comp_fromLocalRing B hX hS f x)
  calc strictHenselizationSquareMap B hX hS f x ≫ strictHenselizationToBase B S hS (x.map f)
      = Spec.map (CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS (x.map f)) ≫
            CommRingCat.ofHom (etaleLocalRingHom B hX hS f x)) ≫
          S.fromSpecStalk ((x.map f).hom (closedPoint (x.map f).residueField)) := by
        simp only [strictHenselizationSquareMap, strictHenselizationToBase]
        rw [← Spec.map_comp_assoc]
    _ = Spec.map (f.stalkMap (x.hom (closedPoint x.residueField)) ≫
            CommRingCat.ofHom (structureSheafStalkFromLocalRing B X hX x)) ≫
          S.fromSpecStalk ((x.map f).hom (closedPoint (x.map f).residueField)) :=
        congrArg (fun k => Spec.map k ≫
          S.fromSpecStalk ((x.map f).hom (closedPoint (x.map f).residueField))) hb
    _ = strictHenselizationToBase B X hX x ≫ f := by
        simp only [strictHenselizationToBase, Category.assoc]
        exact (Spec.map_comp_assoc _ _ _).trans
          (congrArg (fun m => Spec.map (CommRingCat.ofHom
            (structureSheafStalkFromLocalRing B X hX x)) ≫ m)
            (Scheme.SpecMap_stalkMap_fromSpecStalk f))

/-- The induced morphism of strict henselizations carries the canonical geometric point of its
source to the canonical geometric point of its target. -/
public theorem geometricPointToStrictHenselization_strictHenselizationSquareMap :
    geometricPointToStrictHenselization B X hX x ≫ strictHenselizationSquareMap B hX hS f x =
      geometricPointToStrictHenselization B S hS (x.map f) := by
  simp only [strictHenselizationSquareMap, geometricPointToStrictHenselization]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, toGeometricField_comp_etaleLocalRingHom]

/-- **The canonical square of strict henselizations.** The morphism of strict henselizations
induced by a morphism of schemes at a geometric point of its source is the unique morphism which
lies over that morphism and carries the canonical geometric point of its source to the canonical
geometric point of its target. -/
public theorem existsUnique_strictHenselizationSquareMap :
    ∃! m : strictHenselization B X hX x ⟶ strictHenselization B S hS (x.map f),
      m ≫ strictHenselizationToBase B S hS (x.map f) =
          strictHenselizationToBase B X hX x ≫ f ∧
        geometricPointToStrictHenselization B X hX x ≫ m =
          geometricPointToStrictHenselization B S hS (x.map f) := by
  refine ⟨strictHenselizationSquareMap B hX hS f x,
    ⟨strictHenselizationSquareMap_comp B hX hS f x,
      geometricPointToStrictHenselization_strictHenselizationSquareMap B hX hS f x⟩, ?_⟩
  rintro m ⟨hmbase, hmpoint⟩
  let mCat := Spec.preimage m
  have hmCat : Spec.map mCat = m := Spec.map_preimage m
  have hq : CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS (x.map f)) ≫ mCat =
      CommRingCat.ofHom (structureSheafStalkFromLocalRing B S hS (x.map f)) ≫
        CommRingCat.ofHom (etaleLocalRingHom B hX hS f x) := by
    have hc : Spec.map mCat ≫ strictHenselizationToBase B S hS (x.map f) =
        strictHenselizationSquareMap B hX hS f x ≫
          strictHenselizationToBase B S hS (x.map f) := by
      rw [hmCat, hmbase, strictHenselizationSquareMap_comp]
    simp only [strictHenselizationToBase, strictHenselizationSquareMap] at hc
    rw [← Spec.map_comp_assoc, ← Spec.map_comp_assoc] at hc
    exact Spec.map_injective ((cancel_mono _).mp hc)
  have hbase : mCat.hom.comp (structureSheafStalkFromLocalRing B S hS (x.map f)) =
      (structureSheafStalkFromLocalRing B X hX x).comp
        (f.stalkMap (x.hom (closedPoint x.residueField))).hom :=
    (CommRingCat.hom_ext_iff.mp hq).trans (etaleLocalRingHom_comp_fromLocalRing B hX hS f x)
  have hpoint : (structureSheafStalkToGeometricField B X hX x).comp mCat.hom =
      structureSheafStalkToGeometricField B S hS (x.map f) := by
    have hc : Spec.map (mCat ≫ CommRingCat.ofHom
          (structureSheafStalkToGeometricField B X hX x)) =
        Spec.map (CommRingCat.ofHom
          (structureSheafStalkToGeometricField B S hS (x.map f))) := by
      rw [Spec.map_comp, hmCat]
      simpa only [geometricPointToStrictHenselization] using hmpoint
    exact CommRingCat.hom_ext_iff.mp (Spec.map_injective hc)
  have hring : mCat.hom = etaleLocalRingHom B hX hS f x :=
    (existsUnique_etaleLocalRingHom B hX hS f x).unique ⟨hbase, hpoint⟩
      ⟨etaleLocalRingHom_comp_fromLocalRing B hX hS f x,
        toGeometricField_comp_etaleLocalRingHom B hX hS f x⟩
  rw [← hmCat, strictHenselizationSquareMap]
  exact congrArg Spec.map (CommRingCat.hom_ext_iff.mpr hring)

/-- **The canonical square of strict henselizations attached to a morphism of schemes and a
geometric point of its source.** It records the morphism of strict henselizations lying over the
morphism of schemes and compatible with the canonical geometric points. -/
public structure StrictHenselizationSquare (B : BigEtaleSite.{u}) {X S : Scheme.{u}}
    (hX : B.Contains X) (hS : B.Contains S) (f : X ⟶ S) (x : GeometricPoint X) where
  /-- The morphism of strict henselizations. -/
  map : strictHenselization B X hX x ⟶ strictHenselization B S hS (x.map f)
  /-- The morphism lies over the given morphism of schemes. -/
  map_comp : map ≫ strictHenselizationToBase B S hS (x.map f) =
    strictHenselizationToBase B X hX x ≫ f
  /-- The morphism carries the canonical geometric point of its source to the canonical geometric
  point of its target. -/
  point_comp : geometricPointToStrictHenselization B X hX x ≫ map =
    geometricPointToStrictHenselization B S hS (x.map f)

/-- The canonical square of strict henselizations. -/
public def strictHenselizationSquare : StrictHenselizationSquare B hX hS f x where
  map := strictHenselizationSquareMap B hX hS f x
  map_comp := strictHenselizationSquareMap_comp B hX hS f x
  point_comp := geometricPointToStrictHenselization_strictHenselizationSquareMap B hX hS f x

/-- There is only one square of strict henselizations. -/
public theorem StrictHenselizationSquare.eq_strictHenselizationSquare
    (d : StrictHenselizationSquare B hX hS f x) : d = strictHenselizationSquare B hX hS f x := by
  obtain ⟨m, hm1, hm2⟩ := d
  have h : m = strictHenselizationSquareMap B hX hS f x :=
    (existsUnique_strictHenselizationSquareMap B hX hS f x).unique ⟨hm1, hm2⟩
      ⟨strictHenselizationSquareMap_comp B hX hS f x,
        geometricPointToStrictHenselization_strictHenselizationSquareMap B hX hS f x⟩
  subst h
  rfl

/-! ### The variety of vanishing cycles -/

variable (t : GeometricPoint (strictHenselization B S hS (x.map f)))

/-- **The variety of vanishing cycles** of a morphism of schemes at a geometric point `x` of its
source and a geometric point `t` of the strict henselization of its target at the image of `x`:
the fibre of the induced morphism of strict henselizations over `t`, that is
`Spec(𝒪^sh_{X,x} ⊗_{𝒪^sh_{S,f(x)}} κ(t))`. -/
@[sga "4½ Arcata 5.1.3", sga "4½ Th_finitude 2.11"]
public def vanishingCyclesFibre : Scheme.{u} :=
  pullback t.hom (strictHenselizationSquareMap B hX hS f x)

/-- The variety of vanishing cycles is affine, being a fibre product of spectra. -/
public instance isAffine_vanishingCyclesFibre : IsAffine (vanishingCyclesFibre B hX hS f x t) :=
  inferInstanceAs (IsAffine (pullback t.hom (strictHenselizationSquareMap B hX hS f x)))

/-- The projection from the variety of vanishing cycles to the geometric point `t`. -/
public def vanishingCyclesFibreToGeometricPoint :
    vanishingCyclesFibre B hX hS f x t ⟶ t.source :=
  pullback.fst t.hom (strictHenselizationSquareMap B hX hS f x)

/-- The projection from the variety of vanishing cycles to the strict henselization at `x`. -/
public def vanishingCyclesFibreToStrictHenselization :
    vanishingCyclesFibre B hX hS f x t ⟶ strictHenselization B X hX x :=
  pullback.snd t.hom (strictHenselizationSquareMap B hX hS f x)

/-- The canonical morphism from the variety of vanishing cycles to the source of the given
morphism of schemes. -/
public def vanishingCyclesFibreToSource : vanishingCyclesFibre B hX hS f x t ⟶ X :=
  vanishingCyclesFibreToStrictHenselization B hX hS f x t ≫ strictHenselizationToBase B X hX x

/-- The defining square of the variety of vanishing cycles commutes. -/
public theorem vanishingCyclesFibre_condition :
    vanishingCyclesFibreToGeometricPoint B hX hS f x t ≫ t.hom =
      vanishingCyclesFibreToStrictHenselization B hX hS f x t ≫
        strictHenselizationSquareMap B hX hS f x :=
  pullback.condition

/-- **The variety of vanishing cycles is the spectrum of
`𝒪^sh_{X,x} ⊗_{𝒪^sh_{S,f(x)}} κ(t)`**, as in the displayed formula of the source. The residue
field of `t` is an algebra over the étale local ring at the image of `x` because `t` is a point
of its spectrum, and the étale local ring at `x` is one through the induced homomorphism. -/
public def vanishingCyclesFibreIsoSpecTensor :
    letI : Algebra ↥(etaleLocalRing B S hS (x.map f)) t.residueField :=
      (Spec.preimage t.hom).hom.toAlgebra
    letI : Algebra ↥(etaleLocalRing B S hS (x.map f)) ↥(etaleLocalRing B X hX x) :=
      (etaleLocalRingHom B hX hS f x).toAlgebra
    vanishingCyclesFibre B hX hS f x t ≅
      Spec (.of (TensorProduct ↥(etaleLocalRing B S hS (x.map f)) t.residueField
        ↥(etaleLocalRing B X hX x))) :=
  let : Algebra ↥(etaleLocalRing B S hS (x.map f)) t.residueField :=
    (Spec.preimage t.hom).hom.toAlgebra
  let : Algebra ↥(etaleLocalRing B S hS (x.map f)) ↥(etaleLocalRing B X hX x) :=
    (etaleLocalRingHom B hX hS f x).toAlgebra
  pullback.congrHom (Spec.map_preimage t.hom).symm rfl ≪≫
    pullbackSpecIso ↥(etaleLocalRing B S hS (x.map f)) t.residueField
      ↥(etaleLocalRing B X hX x)

/-- **The diagram of the variety of vanishing cycles commutes**: its morphism to the source of
`f`, followed by `f`, is its projection to the geometric point `t` followed by the structure
morphism of the strict henselization of the target. -/
public theorem vanishingCyclesFibreToSource_comp :
    vanishingCyclesFibreToSource B hX hS f x t ≫ f =
      vanishingCyclesFibreToGeometricPoint B hX hS f x t ≫
        t.hom ≫ strictHenselizationToBase B S hS (x.map f) := by
  rw [vanishingCyclesFibreToSource, Category.assoc,
    ← strictHenselizationSquareMap_comp B hX hS f x, ← Category.assoc,
    ← vanishingCyclesFibre_condition, Category.assoc]

end Square

end AlgebraicGeometry

end
