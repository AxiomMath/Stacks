module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ProperModelCofiltered
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.ZariskiRiemannLineModel
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.DirectLimit
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.Transport

/-!
# The strict henselization of a valuation ring at the centers of the proper models

Let `B` be a domain with fraction field `K` and `V ⊆ K` a valuation ring containing `B`. For each
proper model `Y` of `Spec K` over `Spec B`, the image `A_Y ⊆ V` of the local ring
`𝒪_{Y, y_Y(V)} → V` at the center is a local ring, and `A_Y → V` is local. The family of the
`A_Y` is directed — two models are refined by their fibre product, and the images grow along
refinements — and its union is `V` (Zariski's theorem,
`AlgebraicGeometry.Scheme.ZariskiRiemann.iSup_centerRange`). Hence (Stacks 04GI, and
`Stacks.StrictHenselization.DirectLimit.isStrictHenselization_directLimit`) the direct limit of
strict henselizations `A_Y^{sh}`, along compatible maps `A_Y^{sh} → A_{Y'}^{sh}`, is a strict
henselization of `V`: `V^{sh} = colim_Y A_Y^{sh}`. This is the step of Gabber's Zariski–Riemann
argument for Travaux de Gabber, Exposé XVIII-A, Corollary 1.2 (last remark of §2) identifying the
stalk at a point of the Zariski–Riemann space.

The index is the set of the images `A_Y`, ordered by inclusion: it is a directed poset in the
universe of `B`, whereas the category of models is large and has non-trivial hom-sets.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.centerRanges`: the set of the images `A_Y`.

## Main results

* `AlgebraicGeometry.Scheme.ZariskiRiemann.isDirected_centerRanges`,
  `AlgebraicGeometry.Scheme.ZariskiRiemann.iSup_centerRanges`: the `A_Y` form a directed family
  with union `V`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.isLocalRing_centerRange`,
  `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.isLocalHom_centerRange_subtype`: `A_Y` is
  local, and `A_Y → V` is local.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.exists_isStrictHenselization_colimit_centerRanges`:
  **the direct limit of strict henselizations of the `A_Y` is a strict henselization of `V`.**

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* [StacksProject 04GI](https://stacks.math.columbia.edu/tag/04GI)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing Stacks.StrictHenselization Stacks.StrictHenselization.DirectLimit

universe u

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

variable {B : Type u} [CommRing B] [IsDomain B] (V : ValuationSubring (FractionRing B))
  (hV : ∀ b : B, algebraMap B (FractionRing B) b ∈ V)

omit [IsDomain B] in
/-- The residue field of a local ring has a separable algebraic closure in the same universe. -/
theorem exists_isSepClosure_residueField (S : Type u) [CommRing S] [IsLocalRing S] :
    ∃ (κ : Type u) (_ : Field κ) (_ : Algebra (maximalIdeal S).ResidueField κ),
      IsSepClosure (maximalIdeal S).ResidueField κ :=
  ⟨SeparableClosure (maximalIdeal S).ResidueField, inferInstance, inferInstance, inferInstance⟩

namespace ProperModel

variable (M : ProperModel B)

/-- The image `A_Y` of the local ring at the center is a local ring. -/
theorem isLocalRing_centerRange : IsLocalRing (M.centerRange V hV) :=
  IsLocalRing.of_surjective' (M.centerStalkMap V hV).hom.rangeRestrict
    (M.centerStalkMap V hV).hom.rangeRestrict_surjective

/-- The inclusion `A_Y ⊆ V` is a local homomorphism. -/
theorem isLocalHom_centerRange_subtype : IsLocalHom (M.centerRange V hV).subtype := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨s, hs⟩ := x.2
  have hfs : IsUnit ((M.centerStalkMap V hV).hom s) := by
    rw [hs]
    exact hx
  have hsu := (IsUnit.of_map (M.centerStalkMap V hV).hom s hfs).map
    (M.centerStalkMap V hV).hom.rangeRestrict
  have hx' : (M.centerStalkMap V hV).hom.rangeRestrict s = x := Subtype.ext hs
  rwa [hx'] at hsu

end ProperModel

/-- The images `A_Y ⊆ V` of the local rings at the centers, over all proper models `Y`. -/
def centerRanges : Set (Subring V) :=
  Set.range fun M : ProperModel B => M.centerRange V hV

/-- Each `A_Y` is a local ring. -/
instance isLocalRing_centerRanges (a : centerRanges V hV) : IsLocalRing a.1 := by
  obtain ⟨M, hM⟩ := a.2
  exact hM ▸ M.isLocalRing_centerRange V hV

/-- Each `A_Y ⊆ V` is local. -/
theorem isLocalHom_centerRanges_subtype (a : centerRanges V hV) : IsLocalHom a.1.subtype := by
  obtain ⟨M, hM⟩ := a.2
  exact hM ▸ M.isLocalHom_centerRange_subtype V hV

/-- The images `A_Y` form a directed family: `A_{Y₁}` and `A_{Y₂}` are contained in
`A_{Y₁ ×_B Y₂}`. -/
instance isDirected_centerRanges : IsDirected (centerRanges V hV) (· ≤ ·) := by
  refine ⟨?_⟩
  rintro ⟨_, M₁, rfl⟩ ⟨_, M₂, rfl⟩
  exact ⟨⟨_, ProperModel.prod M₁ M₂, rfl⟩,
    ProperModel.Refinement.centerRange_mono hV (ProperModel.prodFst M₁ M₂),
    ProperModel.Refinement.centerRange_mono hV (ProperModel.prodSnd M₁ M₂)⟩

/-- The family of images `A_Y` is nonempty: it contains `A_Y` for the model `Y = Spec B`. -/
instance nonempty_centerRanges : Nonempty (centerRanges V hV) :=
  ⟨⟨_, ProperModel.base, rfl⟩⟩

/-- The images `A_Y` exhaust `V` (Zariski's theorem). -/
theorem iSup_centerRanges : ⨆ a : centerRanges V hV, a.1 = ⊤ := by
  refine eq_top_iff.mpr ?_
  rw [← iSup_centerRange V hV]
  exact iSup_le fun M => le_iSup (fun a : centerRanges V hV => a.1) ⟨_, M, rfl⟩

/-- The inclusions `A_Y ⊆ A_{Y'}` are local. -/
theorem isLocalHom_subringInclusion_centerRanges (a b : centerRanges V hV) (hab : a ≤ b) :
    IsLocalHom (subringInclusion (fun a : centerRanges V hV => a.1) (fun _ _ h => h) a b hab) := by
  have := isLocalHom_centerRanges_subtype V hV a
  have hc : b.1.subtype.comp
      (subringInclusion (fun a : centerRanges V hV => a.1) (fun _ _ h => h) a b hab) =
      a.1.subtype :=
    RingHom.ext fun _ => rfl
  have : IsLocalHom (b.1.subtype.comp
      (subringInclusion (fun a : centerRanges V hV => a.1) (fun _ _ h => h) a b hab)) := by
    rw [hc]
    infer_instance
  exact isLocalHom_of_comp _ b.1.subtype

/-- **The strict henselization of `V` is the direct limit of the strict henselizations of the
local rings at the centers.** Let `A_Y^{sh}` be strict henselizations of the images `A_Y ⊆ V` of
the local rings `𝒪_{Y, y_Y(V)}`, and `A_Y^{sh} → A_{Y'}^{sh}` ring maps over the inclusions
`A_Y ⊆ A_{Y'}` forming a directed system. Then their direct limit is a local ring and carries a
`V`-algebra structure, compatible with the maps `A_Y → A_Y^{sh}`, for which it is a strict
henselization of `V`, with respect to any separable algebraic closure `κ` of the residue field of
`V`. -/
theorem exists_isStrictHenselization_colimit_centerRanges
    {Rsh : centerRanges V hV → Type u} [∀ a, CommRing (Rsh a)] [∀ a, IsLocalRing (Rsh a)]
    [∀ a, Algebra a.1 (Rsh a)]
    (fsh : ∀ a b, a ≤ b → Rsh a →+* Rsh b) [DirectedSystem Rsh fun a b h => fsh a b h]
    {κsep : centerRanges V hV → Type*} [∀ a, Field (κsep a)]
    [∀ a, Algebra (maximalIdeal a.1).ResidueField (κsep a)]
    [∀ a, IsSepClosure (maximalIdeal a.1).ResidueField (κsep a)]
    (hsh : ∀ a, IsStrictHenselization a.1 (κsep a) (Rsh a))
    (hcomm : ∀ a b (hab : a ≤ b) x, fsh a b hab (algebraMap a.1 (Rsh a) x) =
      algebraMap b.1 (Rsh b)
        (subringInclusion (fun a : centerRanges V hV => a.1) (fun _ _ h => h) a b hab x))
    (κ : Type*) [Field κ] [Algebra (maximalIdeal V).ResidueField κ]
    [IsSepClosure (maximalIdeal V).ResidueField κ] :
    ∃ (_ : IsLocalRing (colimitRing Rsh fsh)) (_ : Algebra V (colimitRing Rsh fsh)),
      (∀ a (x : a.1), algebraMap V (colimitRing Rsh fsh) x =
        colimitOf Rsh fsh a (algebraMap a.1 (Rsh a) x)) ∧
      Nonempty (IsStrictHenselization V κ (colimitRing Rsh fsh)) := by
  let A : centerRanges V hV → Subring V := fun a => a.1
  have hA : Monotone A := fun _ _ h => h
  have := directedSystem_subringInclusion A hA
  have hf := isLocalHom_subringInclusion_centerRanges V hV
  have hlocS := part1_isLocalRing (fun a => A a) (subringInclusion A hA) hf
  have hlocT := part1_isLocalRing Rsh fsh (isLocalHom_transition _ fsh hf hsh hcomm)
  let φ : colimitRing (fun a => A a) (subringInclusion A hA) →+* colimitRing Rsh fsh :=
    Ring.DirectLimit.map (fun a => algebraMap (A a) (Rsh a))
      (fun a b h => RingHom.ext fun x => (hcomm a b h x).symm)
  let : Algebra (colimitRing (fun a => A a) (subringInclusion A hA)) (colimitRing Rsh fsh) :=
    φ.toAlgebra
  have halg : ∀ a x, algebraMap (colimitRing (fun a => A a) (subringInclusion A hA))
      (colimitRing Rsh fsh) (colimitOf (fun a => A a) (subringInclusion A hA) a x) =
      colimitOf Rsh fsh a (algebraMap (A a) (Rsh a) x) :=
    fun a x => by
      rw [RingHom.algebraMap_toAlgebra]
      exact Ring.DirectLimit.map_apply_of (fun a => algebraMap (A a) (Rsh a))
        (fun a b h => RingHom.ext fun x => (hcomm a b h x).symm) x
  obtain ⟨κS, _, _, _⟩ :=
    exists_isSepClosure_residueField (colimitRing (fun a => A a) (subringInclusion A hA))
  obtain ⟨H⟩ := isStrictHenselization_directLimit (subringInclusion A hA) fsh hf hsh hcomm halg κS
  obtain ⟨algV, algκ, hsepV, ⟨H'⟩, hpin⟩ := exists_isStrictHenselization_of_ringEquiv H
    (subringDirectLimitEquiv A hA (iSup_centerRanges V hV))
  refine ⟨hlocT, algV, fun a x => ?_, ⟨H'.reindex (IsSepClosure.equiv _ κ _)⟩⟩
  have hx : subringDirectLimitEquiv A hA (iSup_centerRanges V hV)
      (colimitOf (fun a => A a) (subringInclusion A hA) a x) = x :=
    subringDirectLimitEquiv_of A hA (iSup_centerRanges V hV) a x
  rw [← hx, hpin, halg]

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
