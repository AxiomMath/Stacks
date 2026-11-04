module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.StalkTransitionStrictHenselizationRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.LocalConnectedness.PuncturedSpectrumDescent
public import StacksFrontier.CategoryTheory.Abelian.ExtTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.AffineAnalogProper.FiniteCoverKilling

/-!
# Germs at the centers come from the levels

This file proves `AlgebraicGeometry.Scheme.ZariskiRiemann.CenterLevelStalkCompat` (Steps 1
and 3 of the limit argument at the centers) from the compatibility of the stalk transition with
Stacks 03Q9,
`AlgebraicGeometry.Scheme.ZariskiRiemann.StalkTransitionStrictHenselizationRestriction`.

Fix a geometric point `v̄ : Spec Ω ⟶ Spec V` at the closed point, `Ω` algebraically closed, and
the system `A_Y^{sh}` of strict henselizations of the center ranges `A_Y ⊆ V` with respect to the
separable closure `κ` of `κ(V)` (`exists_isStrictHenselization_directLimit_centerRanges`), with a
map `ε : V^{sh} = colim A_Y^{sh} → Ω` over `v̄` (through `κ ⟶ Ω`). Write `y = c_Y(v̄)` and
`𝒪^{sh}_Y = 𝒪^{sh}_{Y, v̄ ≫ c_Y}`.

* For every model `Y` there is a local homomorphism `ρ_Y : 𝒪^{sh}_Y → A_Y^{sh}` over
  `𝒪_{Y,y} ↠ A_Y` compatible with the maps to `Ω` (Stacks 04GU: the residue fields have the
  same image in `Ω`, the separable closure of `κ(y)`); it gives `X_{A_Y} ⟶ P_Y`.
* For `Y'` with `𝒪_{Y',y'} ≅ A_{Y'}` there is `σ_{Y'} : A_{Y'}^{sh} → 𝒪^{sh}_{Y'}` over that
  isomorphism, compatible with the maps to `Ω`; it gives `P_{Y'} ⟶ X_{A_{Y'}}`.
* The composite `σ_{Y'} ∘ (A_Y^{sh} → A_{Y'}^{sh}) ∘ ρ_Y` lies over `π` and is compatible with the
  geometric points, and `P_{Y'} ⟶ X_{A_{Y'}} ⟶ X_{A_Y} ⟶ P_Y` is the morphism `ρ_m` of
  `StalkTransitionStrictHenselizationRestriction` for it.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.centerLevelStalkCompat_of_restriction`.

## References

* [Stacks Project, Tag 04GU](https://stacks.math.columbia.edu/tag/04GU)
* [Stacks Project, Tag 03Q9](https://stacks.math.columbia.edu/tag/03Q9)
* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology Stacks.StrictHenselization.DirectLimit

/-! ### Roots of separable polynomials -/

section SepRoot

/-- `z ∈ Ω` is a root of a separable polynomial over `k`, read in `Ω` along `g : k → Ω`. -/
def IsSepRootAlong {k Ω : Type*} [Field k] [Field Ω] (g : k →+* Ω) (z : Ω) : Prop :=
  ∃ P : Polynomial k, P.Separable ∧ (P.map g).IsRoot z

/-- A root of a separable polynomial along `g' ∘ e` is one along `g'`. -/
theorem IsSepRootAlong.of_comp {k k' Ω : Type*} [Field k] [Field k'] [Field Ω] {g' : k' →+* Ω}
    (e : k →+* k') {z : Ω} (h : IsSepRootAlong (g'.comp e) z) : IsSepRootAlong g' z := by
  obtain ⟨P, hP, hz⟩ := h
  exact ⟨P.map e, hP.map, by rwa [Polynomial.map_map]⟩

/-- **Roots of separable polynomials come from a separably closed intermediate field**: if
`g = j ∘ i` with `i : k → L`, `L` separably closed, then every root in `Ω` of a separable
polynomial over `k` is in the image of `j`. -/
theorem IsSepRootAlong.mem_range {k L Ω : Type*} [Field k] [Field L] [IsSepClosed L] [Field Ω]
    (i : k →+* L) (j : L →+* Ω) {z : Ω} (h : IsSepRootAlong (j.comp i) z) : z ∈ j.range := by
  obtain ⟨P, hP, hz⟩ := h
  have hs : (P.map i).Splits := IsSepClosed.splits_of_separable _ hP.map
  have hne : (P.map i).map j ≠ 0 := Polynomial.map_ne_zero (Polynomial.map_ne_zero hP.ne_zero)
  have hmem : z ∈ ((P.map i).map j).roots := by
    rwa [Polynomial.mem_roots hne, Polynomial.map_map]
  rw [hs.roots_map j] at hmem
  obtain ⟨y, -, rfl⟩ := Multiset.mem_map.1 hmem
  exact ⟨y, rfl⟩

/-- A separable element is a root of a separable polynomial along the structure map. -/
theorem isSepRootAlong_of_isSeparable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] {z : Ω}
    (h : IsSeparable k z) : IsSepRootAlong (algebraMap k Ω) z :=
  ⟨minpoly k z, h, by rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def,
    minpoly.aeval]⟩

/-- Roots of separable polynomials are carried along field homomorphisms. -/
theorem IsSepRootAlong.map {k Ω Ω' : Type*} [Field k] [Field Ω] [Field Ω'] {g : k →+* Ω}
    (f : Ω →+* Ω') {z : Ω} (h : IsSepRootAlong g z) : IsSepRootAlong (f.comp g) (f z) := by
  obtain ⟨P, hP, hz⟩ := h
  exact ⟨P, hP, by simpa only [Polynomial.map_map] using hz.map⟩

end SepRoot

/-! ### Lifting along strict henselizations, compatibly with a map to `Ω` -/

section Lift

/-- A local map `f : R → K` to a field kills the maximal ideal and sends its complement to units,
so it extends to `Ideal.ResidueField.lift`. -/
private theorem maximalIdeal_le_ker_and_primeCompl_le {R K : Type*} [CommRing R] [IsLocalRing R]
    [Field K] (f : R →+* K) [IsLocalHom f] :
    maximalIdeal R ≤ RingHom.ker f ∧
      (maximalIdeal R).primeCompl ≤ (IsUnit.submonoid K).comap f :=
  ⟨fun x hx => by
    rw [RingHom.mem_ker]
    by_contra h0
    exact (mem_maximalIdeal x).1 hx (IsUnit.of_map f x (isUnit_iff_ne_zero.2 h0)),
  fun x hx => (not_not.1 (mt (mem_maximalIdeal x).2 hx)).map f⟩

/-- **A value of a strict henselization in a field is separable over the base.** For a strict
henselization `A → R` and a local map `e : R → Ω` to a field, every `e y` is a root of a separable
polynomial over `κ(A)`, read along `κ(A) → Ω`: the residue field of `R` is a separable closure of
`κ(A)`. -/
theorem isSepRootAlong_of_isStrictHenselization {A R : Type u} [CommRing A] [IsLocalRing A]
    {κsep : Type u} [Field κsep] [Algebra (maximalIdeal A).ResidueField κsep]
    [IsSepClosure (maximalIdeal A).ResidueField κsep] [CommRing R] [IsLocalRing R] [Algebra A R]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization A κsep R) {Ω : Type u} [Field Ω]
    (e : R →+* Ω) [IsLocalHom e] (y : R) :
    haveI := hsh.isLocalHom
    IsSepRootAlong (ResidueField.lift (e.comp (algebraMap A R))) (e y) := by
  have := hsh.isLocalHom
  let jI := Ideal.ResidueField.lift (maximalIdeal R) e (maximalIdeal_le_ker_and_primeCompl_le e).1
      (maximalIdeal_le_ker_and_primeCompl_le e).2
  let e' := Ideal.ResidueField.lift (maximalIdeal A) (IsLocalRing.residue A)
    (maximalIdeal_le_ker_and_primeCompl_le _).1 (maximalIdeal_le_ker_and_primeCompl_le _).2
  let t := hsh.residueFieldEquiv.symm (algebraMap R (maximalIdeal R).ResidueField y)
  have ht : IsSeparable (maximalIdeal A).ResidueField t := Algebra.IsSeparable.isSeparable _ t
  have key := (isSepRootAlong_of_isSeparable ht).map (jI.comp hsh.residueFieldEquiv.toRingHom)
  have hval : (jI.comp hsh.residueFieldEquiv.toRingHom) t = e y := by
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, t,
      RingEquiv.apply_symm_apply, jI, Ideal.ResidueField.lift_algebraMap]
  rw [hval] at key
  refine IsSepRootAlong.of_comp e' ?_
  convert key using 1
  refine RingHom.ext fun z => ?_
  obtain ⟨x, rfl⟩ := Ideal.algebraMap_residueField_surjective (maximalIdeal A) z
  have hc := congrArg (fun φ => φ (algebraMap A (maximalIdeal A).ResidueField x))
    hsh.residueFieldEquiv_comp
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at hc ⊢
  rw [hc, Ideal.ResidueField.map_algebraMap, Ideal.ResidueField.lift_algebraMap]
  simp only [jI, Ideal.ResidueField.lift_algebraMap, ResidueField.lift_residue_apply,
    RingHom.comp_apply]

/-- **The lift through the strict henselization compatible with a map to `Ω`** (Stacks 04GU).
Let `E` be a local `O`-algebra, ind-étale over `O`, with a local map `ε_E : E → Ω` to a field
whose values are roots of separable polynomials over `κ(O)`; let `R` be a henselian local ring
with separably closed residue field, `ψ : O → R` local and `ε_R : R → Ω` local with
`ε_R ∘ ψ = ε_E ∘ (O → E)`. Then there is `ρ : E → R` over `ψ` with `ε_R ∘ ρ = ε_E`: the residue
field of `R` contains, in `Ω`, the values of `ε_E`, which gives the map of residue fields. -/
theorem exists_ringHom_comp_eq_of_isSepRootAlong {O E R : Type u} [CommRing O] [IsLocalRing O]
    [CommRing E] [IsLocalRing E] [Algebra O E] [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (ResidueField R)] {Ω : Type u} [Field Ω]
    (hind : StacksDraft.IndEtale O E) (εE : E →+* Ω) [IsLocalHom εE]
    (ψ : O →+* R) [IsLocalHom ψ] (εR : R →+* Ω) [IsLocalHom εR]
    (hcomm : εR.comp ψ = εE.comp (algebraMap O E))
    (hsep : ∀ y, IsSepRootAlong (ResidueField.lift (εR.comp ψ)) (εE y)) :
    ∃ ρ : E →+* R, ρ.comp (algebraMap O E) = ψ ∧ εR.comp ρ = εE := by
  let jR := ResidueField.lift εR
  let jE := ResidueField.lift εE
  let i := ResidueField.map ψ
  have hji : jR.comp i = ResidueField.lift (εR.comp ψ) := by
    refine RingHom.ext fun z => ?_
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    simp only [RingHom.comp_apply, i, jR, ResidueField.map_residue,
      ResidueField.lift_residue_apply]
  have hrange : ∀ z : ResidueField E, jE z ∈ jR.range := fun z => by
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    simpa only [jE, ResidueField.lift_residue_apply] using
      IsSepRootAlong.mem_range i jR (by rw [hji]; exact hsep y)
  let eR : ResidueField R ≃+* jR.range :=
    RingEquiv.ofBijective jR.rangeRestrict
      ⟨fun _ _ h => jR.injective (congrArg Subtype.val h), jR.rangeRestrict_surjective⟩
  let φ : ResidueField E →+* ResidueField R :=
    eR.symm.toRingHom.comp (jE.codRestrict jR.range hrange)
  have hφ : ∀ z, jR (φ z) = jE z := fun z =>
    congrArg Subtype.val (eR.apply_symm_apply (jE.codRestrict jR.range hrange z))
  let : Algebra O R := ψ.toAlgebra
  have hφ' : φ.comp ((IsLocalRing.residue E).comp (algebraMap O E)) =
      (IsLocalRing.residue R).comp (algebraMap O R) := by
    refine RingHom.ext fun x => jR.injective ?_
    simp only [RingHom.comp_apply, hφ, jE, jR, ResidueField.lift_residue_apply]
    exact (congrArg (fun f => f x) hcomm).symm
  refine ⟨_, (HenselianLocalRing.indEtaleAlgHomOfResidue hind φ hφ').comp_algebraMap,
    RingHom.ext fun y => ?_⟩
  have h := congrArg (fun f => f y)
    (HenselianLocalRing.comp_residue_indEtaleAlgHomOfResidue hind φ hφ')
  simp only [RingHom.comp_apply] at h
  calc εR (HenselianLocalRing.indEtaleAlgHomOfResidue hind φ hφ' y)
      = jR (IsLocalRing.residue R (HenselianLocalRing.indEtaleAlgHomOfResidue hind φ hφ' y)) :=
        (ResidueField.lift_residue_apply _ _).symm
    _ = jR (φ (IsLocalRing.residue E y)) := congrArg jR h
    _ = εE y := (hφ _).trans (ResidueField.lift_residue_apply _ _)

/-- **A map from a strict henselization to an algebraically closed field over a given one.** For
a strict henselization `A → C` and a local map `w : A → Ω` to an algebraically closed field there
is a local map `ε : C → Ω` with `ε ∘ (A → C) = w`: embed the separable closure `κ(C)` of `κ(A)`
into `Ω` over `κ(A) → Ω`. -/
theorem exists_isLocalHom_comp_eq_of_isStrictHenselization {A C : Type u} [CommRing A]
    [IsLocalRing A] {κ : Type u} [Field κ] [Algebra (maximalIdeal A).ResidueField κ]
    [IsSepClosure (maximalIdeal A).ResidueField κ] [CommRing C] [IsLocalRing C] [Algebra A C]
    (hsh : Stacks.StrictHenselization.IsStrictHenselization A κ C) {Ω : Type u} [Field Ω]
    [IsAlgClosed Ω] (w : A →+* Ω) [IsLocalHom w] :
    ∃ ε : C →+* Ω, IsLocalHom ε ∧ ε.comp (algebraMap A C) = w := by
  have := hsh.isLocalHom
  let : Algebra (maximalIdeal A).ResidueField Ω :=
    (Ideal.ResidueField.lift (maximalIdeal A) w (maximalIdeal_le_ker_and_primeCompl_le w).1
      (maximalIdeal_le_ker_and_primeCompl_le w).2).toAlgebra
  have : Algebra.IsSeparable (maximalIdeal A).ResidueField κ := IsSepClosure.separable
  let ι : κ →ₐ[(maximalIdeal A).ResidueField] Ω := IsAlgClosed.lift
  let ε : C →+* Ω := (ι.toRingHom.comp hsh.residueFieldEquiv.symm.toRingHom).comp
    (algebraMap C (maximalIdeal C).ResidueField)
  refine ⟨ε, ⟨fun x hx => ?_⟩, RingHom.ext fun x => ?_⟩
  · by_contra hxu
    have : algebraMap C (maximalIdeal C).ResidueField x = 0 := by
      rw [← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]
      exact (mem_maximalIdeal x).2 hxu
    simp only [ε, RingHom.comp_apply, this, map_zero] at hx
    exact not_isUnit_zero hx
  · have hc := congrArg (fun φ => φ (algebraMap A (maximalIdeal A).ResidueField x))
      hsh.residueFieldEquiv_comp
    simp only [RingHom.comp_apply] at hc
    rw [Ideal.ResidueField.map_algebraMap] at hc
    simp only [ε, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe]
    have hss : ∀ t : κ, hsh.residueFieldEquiv.symm
        ((hsh.residueFieldEquiv : κ →+* (maximalIdeal C).ResidueField) t) = t :=
      hsh.residueFieldEquiv.symm_apply_apply
    rw [← hc, hss, ι.commutes, RingHom.algebraMap_toAlgebra, Ideal.ResidueField.lift_algebraMap]

/-- **Values of the étale local ring at a geometric point are separable over the residue
field.** Evaluation of étale germs at an algebraically closed geometric point `s` takes values
in the separable closure of `κ(s(pt))` in the field of `s`. -/
theorem isSepRootAlong_structureSheafStalkToGeometricField (Bs : BigEtaleSite.{u})
    (X : Scheme.{u}) (hX : Bs.Contains X) (s : GeometricPoint X)
    (f : X.presheaf.stalk (s.hom (closedPoint s.residueField)) →+* s.residueField)
    [IsLocalHom f]
    (hf : f = (structureSheafStalkToGeometricField Bs X hX s).comp
      (algebraMap (X.presheaf.stalk (s.hom (closedPoint s.residueField)))
        ↥(etaleLocalRing Bs X hX s)))
    (y : ↥(etaleLocalRing Bs X hX s)) :
    IsSepRootAlong (ResidueField.lift f) (structureSheafStalkToGeometricField Bs X hX s y) := by
  let O := ↥(X.presheaf.stalk (s.hom (closedPoint s.residueField)))
  let c := etaleLocalRing_strictHenselization_canonical Bs X hX s (geometricHenselizationTower X s)
  have hmem : structureSheafStalkToGeometricField Bs X hX s y ∈
      separableClosure (ResidueField O) s.residueField := by
    obtain ⟨a, rfl⟩ := c.val.surjective y
    rw [c.property.2 a]
    exact SetLike.coe_mem _
  have key := isSepRootAlong_of_isSeparable (mem_separableClosure_iff.1 hmem)
  convert key using 1
  refine RingHom.ext fun z => ?_
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective z
  rw [ResidueField.lift_residue_apply, hf, RingHom.comp_apply, algebraMap_etaleLocalRing]
  have h₁ := congrArg (fun φ : X.presheaf.stalk (s.hom (closedPoint s.residueField)) ⟶
      CommRingCat.of s.residueField => φ.hom r)
    (ofHom_toGeometricField_comp_fromLocalRing Bs X hX s)
  simp only [CommRingCat.hom_ofHom, RingHom.comp_apply] at h₁
  rw [h₁]
  change _ = (algebraMap (ResidueField O) s.residueField) (IsLocalRing.residue O r)
  exact (congrArg (fun φ : X.presheaf.stalk (s.hom (closedPoint s.residueField)) ⟶
      CommRingCat.of s.residueField => φ r)
    (Scheme.residue_descResidueField (f := Scheme.stalkClosedPointTo s.hom))).symm

end Lift

/-! ### The local ring at the image of a geometric point of `Spec V` -/

namespace ProperModel

variable {B : Type u} [CommRing B] [IsDomain B] (M : ProperModel B)
  (V : ValuationSubring (FractionRing B)) (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V)
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ Spec (.of V))

/-- The image `c_Y(v̄)` of the closed point under a point `v̄ : Spec Ω ⟶ Spec V` followed by the
center, written as the image point of the geometric point `v̄ ≫ c_Y`. -/
abbrev centerImagePoint : M.Y :=
  (geometricPointOf (v ≫ M.center V hV)).hom
    (closedPoint (geometricPointOf (v ≫ M.center V hV)).residueField)

/-- If `v̄` hits the closed point, `c_Y(v̄)` is the center point. -/
theorem centerImagePoint_eq (hv : v (closedPoint Ω) = closedPoint V) :
    M.centerImagePoint V hV v = M.centerPoint V hV := by
  change M.center V hV (v (closedPoint Ω)) = _
  rw [hv]
  rfl

/-- **The map `𝒪_{Y, c_Y(v̄)} ↠ A_Y`**: the stalk map at the center, read at `c_Y(v̄)`. -/
def centerStalkToRange (hv : v (closedPoint Ω) = closedPoint V) :
    M.Y.presheaf.stalk (M.centerImagePoint V hV v) →+* M.centerRange V hV :=
  (M.Y.presheaf.stalkSpecializes ((M.centerImagePoint_eq V hV v hv).symm ▸ specializes_rfl) ≫
    M.centerStalkMap V hV).hom.codRestrict (M.centerRange V hV) fun _ => ⟨_, rfl⟩

/-- `centerStalkToRange` followed by the inclusion `A_Y ⊆ V` is the specialization map of stalks
followed by the stalk map at the center. -/
theorem subtype_comp_centerStalkToRange (hv : v (closedPoint Ω) = closedPoint V) :
    (M.centerRange V hV).subtype.comp (M.centerStalkToRange V hV v hv) =
      (M.Y.presheaf.stalkSpecializes ((M.centerImagePoint_eq V hV v hv).symm ▸ specializes_rfl) ≫
        M.centerStalkMap V hV).hom :=
  rfl

/-- `Spec (𝒪_{Y, c_Y(v̄)} ↠ A_Y ⊆ V)` followed by `Spec 𝒪_{Y, c_Y(v̄)} ⟶ Y` is the center. -/
theorem specMap_centerStalkToRange (hv : v (closedPoint Ω) = closedPoint V) :
    Spec.map (CommRingCat.ofHom ((M.centerRange V hV).subtype.comp
        (M.centerStalkToRange V hV v hv))) ≫ M.Y.fromSpecStalk (M.centerImagePoint V hV v) =
      M.center V hV := by
  rw [subtype_comp_centerStalkToRange, CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc,
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk, specMap_centerStalkMap_fromSpecStalk]

/-- `specMap_centerStalkToRange` with the two spectra separated. -/
@[reassoc]
theorem specMap_subtype_specMap_centerStalkToRange (hv : v (closedPoint Ω) = closedPoint V) :
    Spec.map (CommRingCat.ofHom (M.centerRange V hV).subtype) ≫
        Spec.map (CommRingCat.ofHom (M.centerStalkToRange V hV v hv)) ≫
          M.Y.fromSpecStalk (M.centerImagePoint V hV v) =
      M.center V hV := by
  rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact M.specMap_centerStalkToRange V hV v hv

/-- `Spec (𝒪_{Y, c_Y(v̄)} ↠ A_Y ⊆ K)` followed by `Spec 𝒪_{Y, c_Y(v̄)} ⟶ Y` is the point `j`. -/
theorem specMap_toFractionRing_comp_centerStalkToRange (hv : v (closedPoint Ω) = closedPoint V) :
    Spec.map (CommRingCat.ofHom ((CenterRangeSystem.toFractionRing (M.centerRangeMem V hV)).comp
        (M.centerStalkToRange V hV v hv))) ≫ M.Y.fromSpecStalk (M.centerImagePoint V hV v) =
      M.j := by
  have : (CenterRangeSystem.toFractionRing (M.centerRangeMem V hV)).comp
      (M.centerStalkToRange V hV v hv) = (algebraMap V (FractionRing B)).comp
        ((M.centerRange V hV).subtype.comp (M.centerStalkToRange V hV v hv)) := rfl
  rw [this, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, specMap_centerStalkToRange,
    specMap_comp_center]

/-- **The residue map of the geometric point `v̄ ≫ c_Y`** is `𝒪_{Y, c_Y(v̄)} ↠ A_Y ⊆ V → Ω`. -/
theorem stalkClosedPointTo_comp_center (w : V →+* Ω) (hw : Spec.map (CommRingCat.ofHom w) = v)
    (hv : v (closedPoint Ω) = closedPoint V) :
    Scheme.stalkClosedPointTo (v ≫ M.center V hV) = CommRingCat.ofHom
      (w.comp ((M.centerRange V hV).subtype.comp (M.centerStalkToRange V hV v hv))) := by
  apply Spec.map_injective
  rw [← cancel_mono (M.Y.fromSpecStalk (M.centerImagePoint V hV v)),
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc, specMap_centerStalkToRange, hw]

/-- The specializations of stalks along `x ⤳ y` and `y ⤳ x` compose to the identity. -/
private theorem stalkSpecializes_comp_eq_id {Y : Scheme.{u}} {x y : Y} (h₁ : x ⤳ y) (h₂ : y ⤳ x) :
    Y.presheaf.stalkSpecializes h₁ ≫ Y.presheaf.stalkSpecializes h₂ = 𝟙 _ := by
  rw [TopCat.Presheaf.stalkSpecializes_comp]
  exact TopCat.Presheaf.stalkSpecializes_refl _ _

/-- `𝒪_{Y, c_Y(v̄)} ↠ A_Y` is surjective. -/
theorem centerStalkToRange_surjective (hv : v (closedPoint Ω) = closedPoint V) :
    Function.Surjective (M.centerStalkToRange V hV v hv) := by
  have h₁ : M.centerPoint V hV ⤳ M.centerImagePoint V hV v :=
    (M.centerImagePoint_eq V hV v hv).symm ▸ specializes_rfl
  have h₂ : M.centerImagePoint V hV v ⤳ M.centerPoint V hV :=
    (M.centerImagePoint_eq V hV v hv) ▸ specializes_rfl
  rintro ⟨_, t, rfl⟩
  refine ⟨(M.Y.presheaf.stalkSpecializes h₂).hom t, Subtype.ext ?_⟩
  have ht : (M.Y.presheaf.stalkSpecializes h₁).hom
      ((M.Y.presheaf.stalkSpecializes h₂).hom t) = t := by
    rw [← CommRingCat.comp_apply, stalkSpecializes_comp_eq_id h₂ h₁, CommRingCat.id_apply]
  change (M.centerStalkMap V hV).hom ((M.Y.presheaf.stalkSpecializes h₁).hom
    ((M.Y.presheaf.stalkSpecializes h₂).hom t)) = (M.centerStalkMap V hV).hom t
  rw [ht]

/-- On a model whose stalk map at the center is injective, `𝒪_{Y, c_Y(v̄)} ↠ A_Y` is bijective. -/
theorem centerStalkToRange_bijective (hv : v (closedPoint Ω) = closedPoint V)
    (hinj : Function.Injective (M.centerStalkMap V hV).hom) :
    Function.Bijective (M.centerStalkToRange V hV v hv) := by
  have h₁ : M.centerPoint V hV ⤳ M.centerImagePoint V hV v :=
    (M.centerImagePoint_eq V hV v hv).symm ▸ specializes_rfl
  have h₂ : M.centerImagePoint V hV v ⤳ M.centerPoint V hV :=
    (M.centerImagePoint_eq V hV v hv) ▸ specializes_rfl
  refine ⟨fun x y hxy => ?_, M.centerStalkToRange_surjective V hV v hv⟩
  have hxy' := congrArg (fun z : M.centerRange V hV => (z : V)) hxy
  change (M.centerStalkMap V hV).hom ((M.Y.presheaf.stalkSpecializes h₁).hom x) =
    (M.centerStalkMap V hV).hom ((M.Y.presheaf.stalkSpecializes h₁).hom y) at hxy'
  have := congrArg (M.Y.presheaf.stalkSpecializes h₂).hom (hinj hxy')
  rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, stalkSpecializes_comp_eq_id h₁ h₂,
    CommRingCat.id_apply, CommRingCat.id_apply] at this

/-- `𝒪_{Y, c_Y(v̄)} ↠ A_Y` with target the member `A_Y` of
`AlgebraicGeometry.Scheme.ZariskiRiemann.centerRanges` (the same map, typed as it is used with the
system of strict henselizations). -/
def centerStalkToRangeMem (hv : v (closedPoint Ω) = closedPoint V) :
    M.Y.presheaf.stalk (M.centerImagePoint V hV v) →+* (M.centerRangeMem V hV).1 :=
  M.centerStalkToRange V hV v hv

/-- `specMap_toFractionRing_comp_centerStalkToRange` for `centerStalkToRangeMem`. -/
theorem specMap_toFractionRing_comp_centerStalkToRangeMem
    (hv : v (closedPoint Ω) = closedPoint V) :
    Spec.map (CommRingCat.ofHom ((CenterRangeSystem.toFractionRing (M.centerRangeMem V hV)).comp
        (M.centerStalkToRangeMem V hV v hv))) ≫ M.Y.fromSpecStalk (M.centerImagePoint V hV v) =
      M.j :=
  M.specMap_toFractionRing_comp_centerStalkToRange V hV v hv

/-- On a model with injective stalk map at the center, `centerStalkToRangeMem` is an isomorphism. -/
private theorem isIso_ofHom_centerStalkToRangeMem (hv : v (closedPoint Ω) = closedPoint V)
    (hinj : Function.Injective (M.centerStalkMap V hV).hom) :
    IsIso (CommRingCat.ofHom (M.centerStalkToRangeMem V hV v hv)) :=
  (RingEquiv.ofBijective (M.centerStalkToRangeMem V hV v hv)
    (M.centerStalkToRange_bijective V hV v hv hinj :
      Function.Bijective (M.centerStalkToRangeMem V hV v hv))).toCommRingCatIso.isIso_hom

end ProperModel

/-! ### Restriction and transport along an isomorphism of sheaves -/

/-- A class transported along an isomorphism of sheaves restricts to zero exactly when the class
does. -/
theorem etaleCohomologyRestrictionMap_comp_mk₀_eq_zero_iff {X Y : Scheme.{u}} (f : Y ⟶ X)
    {G G' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : G ≅ G') {q : ℕ}
    (y : Sheaf.H.{u + 1} G q) :
    etaleCohomologyRestrictionMap.{u, 0, u + 1} f G' q
        (y.comp (Abelian.Ext.mk₀ e.hom) (add_zero q)) = 0 ↔
      etaleCohomologyRestrictionMap.{u, 0, u + 1} f G q y = 0 := by
  rw [etaleCohomologyRestrictionMap_eq_zero_iff, etaleCohomologyRestrictionMap_eq_zero_iff,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  exact Stacks.ExtTransport.comp_mk₀_eq_zero_iff
    ((etaleAbelianInverseImage.{u, 0} f).mapIso e) _

/-- Restriction to zero along equal morphisms. -/
theorem etaleCohomologyRestrictionMap_eq_zero_of_eq {X Y : Scheme.{u}} {f g : Y ⟶ X} (h : f = g)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) {q : ℕ} {y : Sheaf.H.{u + 1} G q}
    (hy : etaleCohomologyRestrictionMap.{u, 0, u + 1} g G q y = 0) :
    etaleCohomologyRestrictionMap.{u, 0, u + 1} f G q y = 0 := by
  subst h
  exact hy

/-! ### The maps between the strict henselizations at the centers and the system -/

section Maps

/-- A composite of local homomorphisms is local (with the instances passed explicitly, for
composites whose middle ring is written in two defeq ways). -/
theorem isLocalHom_comp_of {R S T : Type*} [Semiring R] [Semiring S] [Semiring T]
    (g : S →+* T) (f : R →+* S) (hg : IsLocalHom g) (hf : IsLocalHom f) :
    IsLocalHom (g.comp f) :=
  ⟨fun x hx => hf.map_nonunit x (hg.map_nonunit (f x) hx)⟩

/-- Rewriting the base of `IsSepRootAlong (ResidueField.lift f)`. -/
theorem isSepRootAlong_lift_congr {R Ω : Type*} [CommRing R] [IsLocalRing R] [Field Ω]
    {f g : R →+* Ω} [IsLocalHom f] [IsLocalHom g] (h : f = g) {z : Ω}
    (hf : IsSepRootAlong (ResidueField.lift f) z) : IsSepRootAlong (ResidueField.lift g) z := by
  subst h
  exact hf

variable {B : Type u} [CommRing B] [IsDomain B] {V : ValuationSubring (FractionRing B)}
  {hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V}
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] {v : Spec (.of Ω) ⟶ Spec (.of V)}
  (hv : v (closedPoint Ω) = closedPoint V) {w : V →+* Ω}
  (hw : Spec.map (CommRingCat.ofHom w) = v)
  (S : CenterRangeSystem V hV) [Algebra V S.colimit]
  (hpin : ∀ (a : centerRanges V hV) (x : a.1), algebraMap V S.colimit x =
      Ring.DirectLimit.of S.R (fun a b h => S.f a b h) a (algebraMap a.1 (S.R a) x))
  (ε : S.colimit →+* Ω) (hε : ε.comp (algebraMap V S.colimit) = w)

/-- The étale local ring `𝒪^{sh}_{Y, v̄ ≫ c_Y}` at the geometric point `v̄ ≫ c_Y` of a model. -/
abbrev ProperModel.centerEtaleLocalRing (M : ProperModel B) (V : ValuationSubring (FractionRing B))
    (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (v : Spec (.of Ω) ⟶ Spec (.of V)) : Type u :=
  ↥(etaleLocalRing (BigEtaleSite.containing M.Y) M.Y (BigEtaleSite.contains_containing M.Y)
    (geometricPointOf (v ≫ M.center V hV)))

/-- The `𝒪_{Y, c_Y(v̄)}`-algebra structure of `𝒪^{sh}_{Y, v̄ ≫ c_Y}`
(`AlgebraicGeometry.etaleLocalRingAlgebra`, stated at the spelled-out point so that instance
search finds it). -/
instance ProperModel.centerEtaleLocalRingAlgebra (M : ProperModel B)
    (V : ValuationSubring (FractionRing B)) (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (v : Spec (.of Ω) ⟶ Spec (.of V)) :
    Algebra (M.Y.presheaf.stalk (M.centerImagePoint V hV v)) (M.centerEtaleLocalRing V hV v) :=
  etaleLocalRingAlgebra _ _ _ _

/-- Evaluation of germs `𝒪^{sh}_{Y, v̄ ≫ c_Y} → Ω`. -/
abbrev ProperModel.centerEtaleEval (M : ProperModel B) (V : ValuationSubring (FractionRing B))
    (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V) {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (v : Spec (.of Ω) ⟶ Spec (.of V)) : M.centerEtaleLocalRing V hV v →+* Ω :=
  structureSheafStalkToGeometricField (BigEtaleSite.containing M.Y) M.Y
    (BigEtaleSite.contains_containing M.Y) (geometricPointOf (v ≫ M.center V hV))

include hpin hε hw in
/-- **The two maps `𝒪_{Y, c_Y(v̄)} → Ω` agree**: through `A_Y → A_Y^{sh} → V^{sh} → Ω` and through
`𝒪^{sh}_{Y, v̄ ≫ c_Y}`. -/
theorem centerLevel_comm (M : ProperModel B) :
    (ε.comp (Ring.DirectLimit.of S.R (fun a b h => S.f a b h) (M.centerRangeMem V hV))).comp
        ((algebraMap (M.centerRangeMem V hV).1 (S.R (M.centerRangeMem V hV))).comp
          (M.centerStalkToRangeMem V hV v hv)) =
      (M.centerEtaleEval V hV v).comp
        (algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
          (M.centerEtaleLocalRing V hV v)) := by
  refine RingHom.ext fun x => ?_
  have h₁ := congrArg (fun φ => φ.hom x) (ofHom_toGeometricField_comp_fromLocalRing
    (BigEtaleSite.containing M.Y) M.Y (BigEtaleSite.contains_containing M.Y)
    (geometricPointOf (v ≫ M.center V hV)))
  have h₂ := congrArg (fun φ => φ.hom x) (M.stalkClosedPointTo_comp_center V hV v w hw hv)
  simp only [CommRingCat.hom_ofHom, RingHom.comp_apply] at h₁ h₂
  calc ε (Ring.DirectLimit.of S.R (fun a b h => S.f a b h) (M.centerRangeMem V hV)
        (algebraMap (M.centerRangeMem V hV).1 (S.R (M.centerRangeMem V hV))
          (M.centerStalkToRangeMem V hV v hv x)))
      = ε (algebraMap V S.colimit
          ((M.centerStalkToRangeMem V hV v hv x : (M.centerRangeMem V hV).1) : V)) :=
      congrArg ε (hpin (M.centerRangeMem V hV) (M.centerStalkToRangeMem V hV v hv x)).symm
    _ = w ((M.centerStalkToRangeMem V hV v hv x : (M.centerRangeMem V hV).1) : V) :=
      congrArg (fun f : V →+* Ω =>
        f ((M.centerStalkToRangeMem V hV v hv x : (M.centerRangeMem V hV).1) : V)) hε
    _ = _ := (h₁.trans h₂).symm

variable {κsep : centerRanges V hV → Type u} [∀ a, Field (κsep a)]
  [∀ a, Algebra (maximalIdeal a.1).ResidueField (κsep a)]
  [∀ a, IsSepClosure (maximalIdeal a.1).ResidueField (κsep a)] [∀ a, IsLocalRing (S.R a)]
  (hsh : ∀ a, Stacks.StrictHenselization.IsStrictHenselization a.1 (κsep a) (S.R a))
  (hof : ∀ a, IsLocalHom (Ring.DirectLimit.of S.R (fun a b h => S.f a b h) a))

include hpin hε hw hsh hof in
/-- **`ρ_Y : 𝒪^{sh}_{Y, v̄ ≫ c_Y} → A_Y^{sh}`**, over `𝒪_{Y, c_Y(v̄)} ↠ A_Y` and compatible with
the maps to `Ω` (Stacks 04GU). -/
theorem exists_centerLevelRho [IsLocalHom ε] (M : ProperModel B) :
    ∃ ρ : M.centerEtaleLocalRing V hV v →+* S.R (M.centerRangeMem V hV),
      ρ.comp (algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
          (M.centerEtaleLocalRing V hV v)) =
        (algebraMap (M.centerRangeMem V hV).1 (S.R (M.centerRangeMem V hV))).comp
          (M.centerStalkToRangeMem V hV v hv) ∧
      (ε.comp (Ring.DirectLimit.of S.R (fun a b h => S.f a b h) (M.centerRangeMem V hV))).comp ρ =
        M.centerEtaleEval V hV v := by
  let a := M.centerRangeMem V hV
  have hSH := strictlyHenselianLocalRing_of_isStrictHenselization _ _ _ (hsh a)
  have h₁ : IsLocalHom (algebraMap a.1 (S.R a)) := (hsh a).isLocalHom
  have h₂ := hof a
  have h₃ : IsLocalHom (M.centerStalkToRangeMem V hV v hv) :=
    IsLocalHom.of_surjective _ (M.centerStalkToRange_surjective V hV v hv :
      Function.Surjective (M.centerStalkToRangeMem V hV v hv))
  have h₄ := structureSheafStalkToGeometricField_isLocalHom (BigEtaleSite.containing M.Y) M.Y
    (BigEtaleSite.contains_containing M.Y) (geometricPointOf (v ≫ M.center V hV))
  have h₅ : IsLocalHom ((algebraMap a.1 (S.R a)).comp (M.centerStalkToRangeMem V hV v hv)) :=
    isLocalHom_comp_of _ _ h₁ h₃
  have h₆ : IsLocalHom (ε.comp (Ring.DirectLimit.of S.R (fun a b h => S.f a b h) a)) :=
    isLocalHom_comp_of _ _ inferInstance h₂
  exact exists_ringHom_comp_eq_of_isSepRootAlong
    (indEtale_etaleLocalRing (BigEtaleSite.containing M.Y) M.Y
      (BigEtaleSite.contains_containing M.Y) (geometricPointOf (v ≫ M.center V hV)))
    (M.centerEtaleEval V hV v) _ _ (centerLevel_comm hv hw S hpin ε hε M)
    (fun y => isSepRootAlong_structureSheafStalkToGeometricField _ _ _ _ _
      (centerLevel_comm hv hw S hpin ε hε M) y)

include hpin hε hw hsh hof in
/-- **`σ_{Y'} : A_{Y'}^{sh} → 𝒪^{sh}_{Y', v̄ ≫ c_{Y'}}`** on a model with injective stalk map at
the center, over `A_{Y'} ≅ 𝒪_{Y', c_{Y'}(v̄)}` and compatible with the maps to `Ω`
(Stacks 04GU). -/
theorem exists_centerLevelSigma [IsLocalHom ε] (M : ProperModel B)
    (hinj : Function.Injective (M.centerStalkMap V hV).hom) :
    ∃ σ : S.R (M.centerRangeMem V hV) →+* M.centerEtaleLocalRing V hV v,
      (σ.comp (algebraMap (M.centerRangeMem V hV).1 (S.R (M.centerRangeMem V hV)))).comp
          (M.centerStalkToRangeMem V hV v hv) =
        algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
          (M.centerEtaleLocalRing V hV v) ∧
      (M.centerEtaleEval V hV v).comp σ =
        ε.comp (Ring.DirectLimit.of S.R (fun a b h => S.f a b h) (M.centerRangeMem V hV)) := by
  let a := M.centerRangeMem V hV
  let e : M.Y.presheaf.stalk (M.centerImagePoint V hV v) ≃+* a.1 :=
    RingEquiv.ofBijective (M.centerStalkToRangeMem V hV v hv)
      (M.centerStalkToRange_bijective V hV v hv hinj :
        Function.Bijective (M.centerStalkToRangeMem V hV v hv))
  have hSH := etaleLocalRing_strictHenselian (BigEtaleSite.containing M.Y) M.Y
    (BigEtaleSite.contains_containing M.Y) (geometricPointOf (v ≫ M.center V hV))
  have h₁ : IsLocalHom (algebraMap a.1 (S.R a)) := (hsh a).isLocalHom
  have h₂ := hof a
  have h₃ := structureSheafStalkToGeometricField_isLocalHom (BigEtaleSite.containing M.Y) M.Y
    (BigEtaleSite.contains_containing M.Y) (geometricPointOf (v ≫ M.center V hV))
  have h₄ : IsLocalHom (algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
      (M.centerEtaleLocalRing V hV v)) :=
    isLocalHom_algebraMap_etaleLocalRing _ _ _ _
  have h₅ : IsLocalHom (e.symm : a.1 →+* M.Y.presheaf.stalk (M.centerImagePoint V hV v)) :=
    IsLocalHom.of_surjective _ e.symm.surjective
  let ψ : a.1 →+* M.centerEtaleLocalRing V hV v :=
    (algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
      (M.centerEtaleLocalRing V hV v)).comp
        (e.symm : a.1 →+* M.Y.presheaf.stalk (M.centerImagePoint V hV v))
  have h₆ : IsLocalHom ψ := isLocalHom_comp_of _ _ h₄ h₅
  have h₇ : IsLocalHom (ε.comp (Ring.DirectLimit.of S.R (fun a b h => S.f a b h) a)) :=
    isLocalHom_comp_of _ _ inferInstance h₂
  have hcomm : (M.centerEtaleEval V hV v).comp ψ =
      (ε.comp (Ring.DirectLimit.of S.R (fun a b h => S.f a b h) a)).comp
        (algebraMap a.1 (S.R a)) := by
    refine RingHom.ext fun x => ?_
    have hx : M.centerStalkToRangeMem V hV v hv (e.symm x) = x := e.apply_symm_apply x
    have h := congrArg (fun f => f (e.symm x)) (centerLevel_comm hv hw S hpin ε hε M)
    exact h.symm.trans
      (congrArg (fun t => ε (Ring.DirectLimit.of S.R (fun a b h => S.f a b h) a
        (algebraMap a.1 (S.R a) t))) hx)
  obtain ⟨σ, hσ₁, hσ₂⟩ := exists_ringHom_comp_eq_of_isSepRootAlong (hsh a).isFilteredColimitEtale
    (ε.comp (Ring.DirectLimit.of S.R (fun a b h => S.f a b h) a)) ψ (M.centerEtaleEval V hV v)
    hcomm (fun y => isSepRootAlong_lift_congr hcomm.symm
      (isSepRootAlong_of_isStrictHenselization (hsh a) _ y))
  refine ⟨σ, RingHom.ext fun y => ?_, hσ₂⟩
  have h := congrArg (fun f => f (M.centerStalkToRangeMem V hV v hv y)) hσ₁
  exact h.trans (congrArg (algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
    (M.centerEtaleLocalRing V hV v)) (e.symm_apply_apply y))

/-- `A_Y ⊆ A_{Y'}` for a refinement, as members of
`AlgebraicGeometry.Scheme.ZariskiRiemann.centerRanges`. -/
theorem ProperModel.Refinement.centerRangeMem_mono {M' M : ProperModel B}
    (φ : ProperModel.Refinement M' M) (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V) :
    M.centerRangeMem V hV ≤ M'.centerRangeMem V hV :=
  φ.centerRange_mono hV

omit [Algebra V S.colimit] [∀ a, IsLocalRing (S.R a)] in
/-- **The map `X_{A_Y} ⟶ P_Y`** of a lift `ρ_Y : 𝒪^{sh}_{Y, v̄ ≫ c_Y} → A_Y^{sh}` over
`𝒪_{Y, c_Y(v̄)} ↠ A_Y`: the projection to `η` and `Spec ρ_Y`. -/
theorem centerLevel_lam_cond (M : ProperModel B)
    (ρ : M.centerEtaleLocalRing V hV v →+* S.R (M.centerRangeMem V hV))
    (hρ₁ : ρ.comp (algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
        (M.centerEtaleLocalRing V hV v)) =
      (algebraMap (M.centerRangeMem V hV).1 (S.R (M.centerRangeMem V hV))).comp
        (M.centerStalkToRangeMem V hV v hv)) :
    S.levelToGeneric (M.centerRangeMem V hV) ≫ M.j =
      (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ρ)) ≫
        strictHenselizationToBase (BigEtaleSite.containing M.Y) M.Y
          (BigEtaleSite.contains_containing M.Y) (geometricPointOf (v ≫ M.center V hV)) := by
  rw [strictHenselizationToBase]
  change S.levelToGeneric (M.centerRangeMem V hV) ≫ M.j =
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ρ)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
      (M.centerEtaleLocalRing V hV v))) ≫ M.Y.fromSpecStalk (M.centerImagePoint V hV v)
  rw [Category.assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hρ₁,
    CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, ← pullback.condition_assoc,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    M.specMap_toFractionRing_comp_centerStalkToRangeMem V hV v hv]
  rfl

/-- The morphism `X_{A_Y} ⟶ P_Y` of `centerLevel_lam_cond`. -/
def centerLevelToBaseChange (M : ProperModel B)
    (ρ : M.centerEtaleLocalRing V hV v →+* S.R (M.centerRangeMem V hV))
    (hρ₁ : ρ.comp (algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
        (M.centerEtaleLocalRing V hV v)) =
      (algebraMap (M.centerRangeMem V hV).1 (S.R (M.centerRangeMem V hV))).comp
        (M.centerStalkToRangeMem V hV v hv)) :
    S.level (M.centerRangeMem V hV) ⟶ strictHenselizationBaseChange
      (BigEtaleSite.containing M.Y) (BigEtaleSite.contains_containing M.Y) M.j
      (geometricPointOf (v ≫ M.center V hV)) :=
  pullback.lift (S.levelToGeneric _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom ρ))
    (centerLevel_lam_cond hv S M ρ hρ₁)

omit [Algebra V S.colimit] [∀ a, IsLocalRing (S.R a)] in
/-- **The map `P_{Y'} ⟶ X_{A_{Y'}}`** of a lift `σ_{Y'} : A_{Y'}^{sh} → 𝒪^{sh}_{Y', v̄ ≫ c_{Y'}}`
over `A_{Y'} ≅ 𝒪_{Y', c_{Y'}(v̄)}`: the projection to `η` and `Spec σ_{Y'}`. -/
theorem centerLevel_mu_cond (M : ProperModel B)
    (hinj : Function.Injective (M.centerStalkMap V hV).hom)
    (σ : S.R (M.centerRangeMem V hV) →+* M.centerEtaleLocalRing V hV v)
    (hσ₁ : (σ.comp (algebraMap (M.centerRangeMem V hV).1 (S.R (M.centerRangeMem V hV)))).comp
        (M.centerStalkToRangeMem V hV v hv) =
      algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
        (M.centerEtaleLocalRing V hV v)) :
    pullback.fst M.j (strictHenselizationToBase (BigEtaleSite.containing M.Y) M.Y
        (BigEtaleSite.contains_containing M.Y) (geometricPointOf (v ≫ M.center V hV))) ≫
        Spec.map (CommRingCat.ofHom (CenterRangeSystem.toFractionRing (M.centerRangeMem V hV))) =
      (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (M.centerRangeMem V hV).1
          (S.R (M.centerRangeMem V hV)))) := by
  have := M.isIso_ofHom_centerStalkToRangeMem V hV v hv hinj
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (M.centerStalkToRangeMem V hV v hv)) ≫
    M.Y.fromSpecStalk (M.centerImagePoint V hV v))]
  simp only [Category.assoc]
  rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    M.specMap_toFractionRing_comp_centerStalkToRangeMem V hV v hv, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hσ₁]
  exact pullback.condition

/-- The morphism `P_{Y'} ⟶ X_{A_{Y'}}` of `centerLevel_mu_cond`. -/
def centerBaseChangeToLevel (M : ProperModel B)
    (hinj : Function.Injective (M.centerStalkMap V hV).hom)
    (σ : S.R (M.centerRangeMem V hV) →+* M.centerEtaleLocalRing V hV v)
    (hσ₁ : (σ.comp (algebraMap (M.centerRangeMem V hV).1 (S.R (M.centerRangeMem V hV)))).comp
        (M.centerStalkToRangeMem V hV v hv) =
      algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
        (M.centerEtaleLocalRing V hV v)) :
    strictHenselizationBaseChange (BigEtaleSite.containing M.Y)
      (BigEtaleSite.contains_containing M.Y) M.j (geometricPointOf (v ≫ M.center V hV)) ⟶
      S.level (M.centerRangeMem V hV) :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom σ))
    (centerLevel_mu_cond hv S M hinj σ hσ₁)

/-- The stalk maps of a refinement at the centers, read in the center ranges, are the
inclusions `A_Y ⊆ A_{Y'}`. -/
theorem centerStalkToRangeMem_comp_stalkMap {M' M : ProperModel B}
    (φ : ProperModel.Refinement M' M)
    (hk : φ.π (M'.centerImagePoint V hV v) ⤳ M.centerImagePoint V hV v) :
    (M'.centerStalkToRangeMem V hV v hv).comp
        ((φ.π.stalkMap (M'.centerImagePoint V hV v)).hom.comp
          (M.Y.presheaf.stalkSpecializes hk).hom) =
      (subringInclusion (fun a : centerRanges V hV => a.1) (centerRanges_monotone V hV)
        (M.centerRangeMem V hV) (M'.centerRangeMem V hV) (φ.centerRangeMem_mono hV)).comp
        (M.centerStalkToRangeMem V hV v hv) := by
  have hX₁ : Spec.map (CommRingCat.ofHom ((M'.centerRange V hV).subtype.comp
      ((M'.centerStalkToRange V hV v hv).comp ((φ.π.stalkMap (M'.centerImagePoint V hV v)).hom.comp
        (M.Y.presheaf.stalkSpecializes hk).hom)))) ≫ M.Y.fromSpecStalk (M.centerImagePoint V hV v) =
      M.center V hV := by
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Category.assoc]
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk,
      M'.specMap_subtype_specMap_centerStalkToRange_assoc V hV v hv, ← φ.center_eq hV]
  have hX₂ : Spec.map (CommRingCat.ofHom ((M'.centerRange V hV).subtype.comp
      ((subringInclusion (fun a : centerRanges V hV => a.1) (centerRanges_monotone V hV)
        (M.centerRangeMem V hV) (M'.centerRangeMem V hV) (φ.centerRangeMem_mono hV)).comp
        (M.centerStalkToRangeMem V hV v hv)))) ≫
        M.Y.fromSpecStalk (M.centerImagePoint V hV v) = M.center V hV :=
    M.specMap_centerStalkToRange V hV v hv
  have h := hX₁.trans hX₂.symm
  rw [cancel_mono] at h
  have h' := CommRingCat.hom_ext_iff.mp (Spec.map_injective h)
  simp only [CommRingCat.hom_ofHom] at h'
  exact RingHom.ext fun x => Subtype.ext (congrArg (fun f => f x) h')

omit [Algebra V S.colimit] [∀ a, IsLocalRing (S.R a)] in
/-- **The composite `σ_{Y'} ∘ (A_Y^{sh} → A_{Y'}^{sh}) ∘ ρ_Y` lies over `π`.** -/
theorem centerLevel_over {M' M : ProperModel B} (φ : ProperModel.Refinement M' M)
    (hinj : Function.Injective (M'.centerStalkMap V hV).hom)
    (ρ : M.centerEtaleLocalRing V hV v →+* S.R (M.centerRangeMem V hV))
    (hρ₁ : ρ.comp (algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
        (M.centerEtaleLocalRing V hV v)) =
      (algebraMap (M.centerRangeMem V hV).1 (S.R (M.centerRangeMem V hV))).comp
        (M.centerStalkToRangeMem V hV v hv))
    (σ : S.R (M'.centerRangeMem V hV) →+* M'.centerEtaleLocalRing V hV v)
    (hσ₁ : (σ.comp (algebraMap (M'.centerRangeMem V hV).1 (S.R (M'.centerRangeMem V hV)))).comp
        (M'.centerStalkToRangeMem V hV v hv) =
      algebraMap (M'.Y.presheaf.stalk (M'.centerImagePoint V hV v))
        (M'.centerEtaleLocalRing V hV v)) :
    strictHenselizationToBase (BigEtaleSite.containing M'.Y) M'.Y
        (BigEtaleSite.contains_containing M'.Y) (geometricPointOf (v ≫ M'.center V hV)) ≫ φ.π =
      Spec.map (CommRingCat.ofHom (σ.comp ((S.f _ _ (φ.centerRangeMem_mono hV)).comp ρ))) ≫
        strictHenselizationToBase (BigEtaleSite.containing M.Y) M.Y
          (BigEtaleSite.contains_containing M.Y) (geometricPointOf (v ≫ M.center V hV)) := by
  let a := M.centerRangeMem V hV
  let a' := M'.centerRangeMem V hV
  have hab : a ≤ a' := φ.centerRangeMem_mono hV
  let e' : M'.Y.presheaf.stalk (M'.centerImagePoint V hV v) ≃+* a'.1 :=
    RingEquiv.ofBijective _ (M'.centerStalkToRange_bijective V hV v hv hinj :
      Function.Bijective (M'.centerStalkToRangeMem V hV v hv))
  have := M'.isIso_ofHom_centerStalkToRangeMem V hV v hv hinj
  have hpp : φ.π (M'.centerImagePoint V hV v) = M.centerImagePoint V hV v := by
    rw [M'.centerImagePoint_eq V hV v hv, M.centerImagePoint_eq V hV v hv, φ.π_centerPoint hV]
  have hk : φ.π (M'.centerImagePoint V hV v) ⤳ M.centerImagePoint V hV v := hpp ▸ specializes_rfl
  let g : M.Y.presheaf.stalk (M.centerImagePoint V hV v) →+*
      M'.Y.presheaf.stalk (M'.centerImagePoint V hV v) :=
    (e'.symm : a'.1 →+* _).comp ((subringInclusion (fun a : centerRanges V hV => a.1)
      (centerRanges_monotone V hV) a a' hab).comp (M.centerStalkToRangeMem V hV v hv))
  have hmg : (σ.comp ((S.f a a' hab).comp ρ)).comp
      (algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
        (M.centerEtaleLocalRing V hV v)) = (algebraMap (M'.Y.presheaf.stalk
          (M'.centerImagePoint V hV v)) (M'.centerEtaleLocalRing V hV v)).comp g := by
    refine RingHom.ext fun x => ?_
    have h₁ := congrArg (fun f => f x) hρ₁
    have h₂ := congrArg (fun f => f (e'.symm ((subringInclusion (fun a : centerRanges V hV => a.1)
      (centerRanges_monotone V hV) a a' hab) (M.centerStalkToRangeMem V hV v hv x)))) hσ₁
    simp only [RingHom.comp_apply] at h₁ h₂ ⊢
    rw [h₁, S.f_algebraMap]
    refine Eq.trans ?_ h₂
    congr 2
    exact (e'.apply_symm_apply _).symm
  have hX : M'.Y.fromSpecStalk (M'.centerImagePoint V hV v) ≫ φ.π =
      Spec.map (CommRingCat.ofHom g) ≫ M.Y.fromSpecStalk (M.centerImagePoint V hV v) := by
    rw [← cancel_epi (Spec.map (CommRingCat.ofHom (M'.centerStalkToRangeMem V hV v hv))),
      ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    have hrg : (M'.centerStalkToRangeMem V hV v hv).comp g =
        (subringInclusion (fun a : centerRanges V hV => a.1) (centerRanges_monotone V hV) a a'
          hab).comp (M.centerStalkToRangeMem V hV v hv) :=
      RingHom.ext fun x => e'.apply_symm_apply _
    rw [hrg, ← centerStalkToRangeMem_comp_stalkMap hv φ hk,
      ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk hk]
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom]
  rw [strictHenselizationToBase, strictHenselizationToBase]
  change (Spec.map (CommRingCat.ofHom (algebraMap (M'.Y.presheaf.stalk
      (M'.centerImagePoint V hV v)) (M'.centerEtaleLocalRing V hV v))) ≫
      M'.Y.fromSpecStalk (M'.centerImagePoint V hV v)) ≫ φ.π =
    Spec.map (CommRingCat.ofHom (σ.comp ((S.f a a' hab).comp ρ))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
        (M.centerEtaleLocalRing V hV v))) ≫ M.Y.fromSpecStalk (M.centerImagePoint V hV v)
  rw [Category.assoc, hX, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, hmg]

omit [Algebra V S.colimit] [∀ a, IsLocalRing (S.R a)] in
/-- **The composite is compatible with the geometric points.** -/
theorem centerLevel_geom {M' M : ProperModel B} (φ : ProperModel.Refinement M' M)
    (ρ : M.centerEtaleLocalRing V hV v →+* S.R (M.centerRangeMem V hV))
    (hρ₂ : (ε.comp (Ring.DirectLimit.of S.R (fun a b h => S.f a b h) (M.centerRangeMem V hV))).comp
      ρ = M.centerEtaleEval V hV v)
    (σ : S.R (M'.centerRangeMem V hV) →+* M'.centerEtaleLocalRing V hV v)
    (hσ₂ : (M'.centerEtaleEval V hV v).comp σ =
      ε.comp (Ring.DirectLimit.of S.R (fun a b h => S.f a b h) (M'.centerRangeMem V hV))) :
    geometricPointToStrictHenselization (BigEtaleSite.containing M'.Y) M'.Y
        (BigEtaleSite.contains_containing M'.Y) (geometricPointOf (v ≫ M'.center V hV)) ≫
        Spec.map (CommRingCat.ofHom (σ.comp ((S.f _ _ (φ.centerRangeMem_mono hV)).comp ρ))) =
      geometricPointToStrictHenselization (BigEtaleSite.containing M.Y) M.Y
        (BigEtaleSite.contains_containing M.Y) (geometricPointOf (v ≫ M.center V hV)) := by
  have hds := S.directedSystem
  rw [geometricPointToStrictHenselization, geometricPointToStrictHenselization,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  refine RingHom.ext fun y => ?_
  have h₁ := congrArg (fun f => f ((S.f _ _ (φ.centerRangeMem_mono hV)) (ρ y))) hσ₂
  have h₂ := congrArg (fun f => f y) hρ₂
  simp only [RingHom.comp_apply] at h₁ h₂
  exact h₁.trans ((congrArg ε (Ring.DirectLimit.of_f (φ.centerRangeMem_mono hV) (ρ y))).trans h₂)

omit [Algebra V S.colimit] [∀ a, IsLocalRing (S.R a)] in
/-- **The morphism `ρ_m : P_{Y'} ⟶ P_Y` factors through the levels**:
`P_{Y'} ⟶ X_{A_{Y'}} ⟶ X_{A_Y} ⟶ P_Y`. -/
theorem centerLevel_fac {M' M : ProperModel B} (φ : ProperModel.Refinement M' M)
    (hinj : Function.Injective (M'.centerStalkMap V hV).hom)
    (ρ : M.centerEtaleLocalRing V hV v →+* S.R (M.centerRangeMem V hV))
    (hρ₁ : ρ.comp (algebraMap (M.Y.presheaf.stalk (M.centerImagePoint V hV v))
        (M.centerEtaleLocalRing V hV v)) =
      (algebraMap (M.centerRangeMem V hV).1 (S.R (M.centerRangeMem V hV))).comp
        (M.centerStalkToRangeMem V hV v hv))
    (σ : S.R (M'.centerRangeMem V hV) →+* M'.centerEtaleLocalRing V hV v)
    (hσ₁ : (σ.comp (algebraMap (M'.centerRangeMem V hV).1 (S.R (M'.centerRangeMem V hV)))).comp
        (M'.centerStalkToRangeMem V hV v hv) =
      algebraMap (M'.Y.presheaf.stalk (M'.centerImagePoint V hV v))
        (M'.centerEtaleLocalRing V hV v)) :
    φ.strictHenselizationBaseChangeMap (v ≫ M.center V hV) (v ≫ M'.center V hV)
        (σ.comp ((S.f _ _ (φ.centerRangeMem_mono hV)).comp ρ))
        (centerLevel_over hv S φ hinj ρ hρ₁ σ hσ₁) =
      centerBaseChangeToLevel hv S M' hinj σ hσ₁ ≫
        S.levelMap _ _ (φ.centerRangeMem_mono hV) ≫ centerLevelToBaseChange hv S M ρ hρ₁ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, centerLevelToBaseChange, pullback.lift_fst,
      S.levelMap_levelToGeneric, centerBaseChangeToLevel]
    exact ((pullback.lift_fst _ _ _).trans (Category.comp_id _)).trans
      (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, Category.assoc, centerLevelToBaseChange, pullback.lift_snd,
      CenterRangeSystem.levelMap, pullback.lift_snd_assoc, centerBaseChangeToLevel]
    simp only [Category.assoc]
    rw [pullback.lift_snd_assoc]
    refine (pullback.lift_snd _ _ _).trans ?_
    simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]

include hv hpin hε hw hsh hof in
/-- **Germs at the centers come from the levels**, for a fixed system of strict henselizations
with a map to `Ω`: the core of
`AlgebraicGeometry.Scheme.ZariskiRiemann.centerLevelStalkCompat_of_restriction`. -/
theorem centerLevelStalkCompat_core [IsLocalHom ε]
    (h : StalkTransitionStrictHenselizationRestriction.{u})
    (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
    (M : ProperModel B) (γ : (smallEtaleStalkAb (v ≫ M.center V hV)).obj
      (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F)) :
    ∃ c : Sheaf.H.{u + 1} (S.levelSheaf F (M.centerRangeMem V hV)) q,
      ∀ (M' : ProperModel B) (φ : ProperModel.Refinement M' M),
        Function.Injective (M'.centerStalkMap V hV).hom →
        etaleCohomologyRestrictionMap.{u, 0, u + 1}
            (S.levelMap (M.centerRangeMem V hV) (M'.centerRangeMem V hV)
              (φ.centerRangeMem_mono hV)) _ q c = 0 →
          (eqToHom (by rw [φ.center_eq hV, Category.assoc]) ≫
            φ.stalkTransition F q (v ≫ M'.center V hV)) γ = 0 := by
  obtain ⟨ξ, hξ⟩ := h B F q M Ω (v ≫ M.center V hV) γ
  obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_centerLevelRho hv hw S hpin ε hε hsh hof M
  have hlam : centerLevelToBaseChange hv S M ρ hρ₁ ≫ strictHenselizationBaseChangeToSource
      (BigEtaleSite.containing M.Y) (BigEtaleSite.contains_containing M.Y) M.j
      (geometricPointOf (v ≫ M.center V hV)) = S.levelToGeneric (M.centerRangeMem V hV) :=
    pullback.lift_fst _ _ _
  let τ := etaleAbelianInverseImageCompIso'.{u, 0} (centerLevelToBaseChange hv S M ρ hρ₁)
    (strictHenselizationBaseChangeToSource (BigEtaleSite.containing M.Y)
      (BigEtaleSite.contains_containing M.Y) M.j (geometricPointOf (v ≫ M.center V hV)))
    (S.levelToGeneric (M.centerRangeMem V hV)) hlam.symm
  refine ⟨(etaleCohomologyRestrictionMap.{u, 0, u + 1} (centerLevelToBaseChange hv S M ρ hρ₁) _ q
    ξ).comp (Abelian.Ext.mk₀ (τ.inv.app F)) (add_zero q), fun M' φ hinj hc => ?_⟩
  obtain ⟨σ, hσ₁, hσ₂⟩ := exists_centerLevelSigma hv hw S hpin ε hε hsh hof M' hinj
  refine hξ M' φ (v ≫ M'.center V hV) (by rw [φ.center_eq hV, Category.assoc])
    (σ.comp ((S.f _ _ (φ.centerRangeMem_mono hV)).comp ρ))
    (centerLevel_over hv S φ hinj ρ hρ₁ σ hσ₁)
    (centerLevel_geom S ε φ ρ hρ₂ σ hσ₂)
    (etaleCohomologyRestrictionMap_eq_zero_of_eq (centerLevel_fac hv S φ hinj ρ hρ₁ σ hσ₁) _ ?_)
  have h' := (etaleCohomologyRestrictionMap_comp_mk₀_eq_zero_iff
    (S.levelMap _ _ (φ.centerRangeMem_mono hV)) (τ.app F).symm
    (etaleCohomologyRestrictionMap.{u, 0, u + 1} (centerLevelToBaseChange hv S M ρ hρ₁) _ q ξ)).1 hc
  have h₁ := (etaleCohomologyRestrictionMap_restrictionMap_eq_zero_iff
    (centerLevelToBaseChange hv S M ρ hρ₁) (S.levelMap _ _ (φ.centerRangeMem_mono hV)) _ ξ).1 h'
  exact (etaleCohomologyRestrictionMap_restrictionMap_eq_zero_iff
    (S.levelMap _ _ (φ.centerRangeMem_mono hV) ≫ centerLevelToBaseChange hv S M ρ hρ₁)
    (centerBaseChangeToLevel hv S M' hinj σ hσ₁) _ ξ).1 ((congrArg _ h₁).trans (map_zero _))

end Maps

/-- **`CenterLevelStalkCompat` from the 03Q9 compatibility of the stalk transition**
(Steps 1 and 3 of the limit argument at the centers). Take the system of strict henselizations
`A_Y^{sh}` of the center ranges with respect to a separable closure `κ` of `κ(V)`, whose colimit
is a strict henselization of `V` (`exists_isStrictHenselization_directLimit_centerRanges`), and
a local map `ε : V^{sh} → Ω` over `v̄` (embedding `κ` into `Ω`). For a model `Y` and a germ `γ`,
`StalkTransitionStrictHenselizationRestriction` gives a class `ξ` on `P_Y`; its restriction `c`
along `X_{A_Y} ⟶ P_Y` (from `ρ_Y`) is the class on the level. For a refinement `Y' ⟶ Y` with
injective stalk map at the center on whose level `c` dies, `ρ_m : P_{Y'} ⟶ P_Y` for
`m = σ_{Y'} ∘ (A_Y^{sh} → A_{Y'}^{sh}) ∘ ρ_Y` factors as `P_{Y'} ⟶ X_{A_{Y'}} ⟶ X_{A_Y} ⟶ P_Y`, so
`ξ` dies along `ρ_m` and the germ dies. -/
theorem centerLevelStalkCompat_of_restriction
    (h : StalkTransitionStrictHenselizationRestriction.{u}) : CenterLevelStalkCompat.{u} := by
  intro B _ _ F q V hV hloc Ω _ _ v hv
  have : Subsingleton ↥(Spec (CommRingCat.of Ω)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have hv' : v (closedPoint Ω) = closedPoint V := (congrArg v (Subsingleton.elim _ _)).trans hv
  let w : V →+* Ω := (Spec.preimage v).hom
  have hw : Spec.map (CommRingCat.ofHom w) = v := by
    simp only [w, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hwloc : IsLocalHom w := by
    refine (IsLocalRing.isLocalHom_iff_comap_closedPoint w).2 ?_
    rw [← hv', ← hw]
    rfl
  obtain ⟨κ, _, _, _⟩ := exists_isSepClosure_residueField V
  obtain ⟨Rsh, _, _, _, κsep, _, _, _, fsh, hds, hlocC, algV, hsh, hcomm, hpin, ⟨hVsh⟩⟩ :=
    exists_isStrictHenselization_directLimit_centerRanges V hV κ
  let S : CenterRangeSystem V hV :=
    { R := Rsh, f := fsh, directedSystem := hds, f_algebraMap := hcomm }
  have hloctr := isLocalHom_transition
    (subringInclusion (fun a : centerRanges V hV => a.1) (fun _ _ h => h)) fsh
    (isLocalHom_subringInclusion_centerRanges V hV) (fun a => (hsh a).some) hcomm
  have hof : ∀ a, IsLocalHom (Ring.DirectLimit.of S.R (fun a b h => S.f a b h) a) :=
    fun a => part1_of_isLocalHom Rsh fsh hloctr a
  obtain ⟨ε, hεloc, hε⟩ := exists_isLocalHom_comp_eq_of_isStrictHenselization hVsh w
  exact ⟨S, algV, hpin, strictlyHenselianLocalRing_of_isStrictHenselization _ _ _ hVsh,
    hVsh.isLocalHom, hVsh.isFilteredColimitEtale, fun M γ =>
      centerLevelStalkCompat_core hv' hw S hpin ε hε (fun a => (hsh a).some) hof h F q M γ⟩

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
