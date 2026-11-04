module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.SpecializationInjective.GaloisAlgClosureDescent
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverOverAlgebraicExtension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCoverLimits.GenericFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveEssentialImage
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A Galois cover of a geometric generic fibre over the finite subextensions

Let `R` be a domain with fraction field `K`, let `h : Y ⟶ Spec R` be proper with geometrically
connected fibres and let `η` be a geometric point of `Spec R` lying over the generic point. The
residue field `Ω` of `η` is then an extension of `K`, hence of the algebraic closure `k̄` of `K`
inside it, and `AlgebraicGeometry.exists_isGalois_model_of_isAlgClosed_base` descends a Galois
object of `FÉt_{Y_Ω}` to a Galois object of `FÉt_{Y_{k̄}}`.

This file carries that descent over to the limit argument along the finite subextensions of
`k̄/K`, and assembles the data which the extension theorem for a Galois cover of a generic fibre
([Stacks, Tag 0EYJ]) asks for over such a base.

* The base change `Y_{k̄}`, presented as `Y ×_{Spec R} Spec k̄`, is re-associated into
  `Spec k̄ ×_{Spec K} Y_K`, which is the shape
  `AlgebraicGeometry.AlgebraicExtensionLimit.exists_finiteEtaleGaloisCover_model_of_isGalois`
  consumes; the embedding `k̄ ⊆ Ω` producing the factorization comes from `IsAlgClosed.lift`.
* A section of `f : X ⟶ Spec K` base changes to compatible sections of all the stages
  `X_{K(s)} ⟶ Spec K(s)`, and a Galois cover of one stage acquires a `K(t)`-rational point over
  that section at some later stage `t ⊇ s`.
* The normality of the spectrum of a discrete valuation ring and the invertibility of the order
  of the Galois group in every residue field are the two hypotheses of [Stacks, Tag 0EYJ] which
  are not instances.

## Main results

* `AlgebraicGeometry.exists_isIso_pullback_comp_reassoc` — the base change of `f : X ⟶ S` along a
  two-step base `T ⟶ Z ⟶ S`, re-associated as a base change of `X_Z ⟶ Z` along `T ⟶ Z`, with both
  projections recorded.
* `AlgebraicGeometry.exists_ringHom_algebraicClosure_of_liesOver_genericPoint` — the residue field
  of a geometric point over the generic point of the spectrum of a domain receives the algebraic
  closure of the fraction field, compatibly with the structure morphisms.
* `AlgebraicGeometry.exists_isGalois_model_reassoc_of_isAlgClosed_tower` — a Galois object of
  `FÉt_{X_Ω}` is the base change of a Galois object of `FÉt_{Spec k̄ ×_Z X_Z}`, along a morphism
  lying over `X`.
* `AlgebraicGeometry.AlgebraicExtensionLimit.stageSection` and
  `AlgebraicGeometry.AlgebraicExtensionLimit.stageSection_naturality` — the sections of the stages
  induced by a section of `f`, and their compatibility with the transition morphisms.
* `AlgebraicGeometry.AlgebraicExtensionLimit.bcProj_comp_stageTransition` — the projection from
  `X_{k̄}` factors through every transition morphism of the stages.
* `AlgebraicGeometry.AlgebraicExtensionLimit.exists_stage_point_of_finiteEtaleGaloisCover` — a
  Galois cover of a stage has a rational point over the section at a later stage.
* `AlgebraicGeometry.AlgebraicExtensionLimit.connectedSpace_pullback_stageHom` — the stages are
  connected as soon as `X_{k̄}` is.
* `AlgebraicGeometry.isNormal_spec_of_isDiscreteValuationRing` and
  `AlgebraicGeometry.isUnit_natCast_specResidueField_of_isUnit` — the two non-instance hypotheses
  of [Stacks, Tag 0EYJ] over a strictly henselian discrete valuation ring whose residue field has
  characteristic zero. That a nonzero integer is a unit in such a ring is
  `Stacks.KummerExtension.isUnit_natCast_of_coprime_ringChar`.

## References

* [Stacks Project, Tag 0A49](https://stacks.math.columbia.edu/tag/0A49)
* [Stacks Project, Tag 0C0Q](https://stacks.math.columbia.edu/tag/0C0Q)
* [Stacks Project, Tag 0EYJ](https://stacks.math.columbia.edu/tag/0EYJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry

/-! ### Re-associating a base change along a two-step base -/

/-- **A base change along a two-step base, re-associated.** For `f : X ⟶ S` and morphisms
`b : T ⟶ Z` and `a : Z ⟶ S`, the scheme `T ×_Z (X ×_S Z)` is isomorphic to `X ×_S T`, and the
isomorphism matches the projection to `X` with the projection to `X ×_S Z` followed by the
projection to `X`, and the projection to `T` with the projection to `T`.

This is the pasting isomorphism `pullbackLeftPullbackSndIso` preceded by `pullbackSymmetry`; the
symmetry is there because the limit presentation of a base change along an algebraic extension
takes the extension as the *first* factor. -/
theorem exists_isIso_pullback_comp_reassoc {X S Z T : Scheme.{u}} (f : X ⟶ S) (a : Z ⟶ S)
    (b : T ⟶ Z) :
    ∃ m : pullback b (pullback.snd f a) ⟶ pullback f (b ≫ a), IsIso m ∧
      m ≫ pullback.fst f (b ≫ a)
        = pullback.snd b (pullback.snd f a) ≫ pullback.fst f a ∧
      m ≫ pullback.snd f (b ≫ a) = pullback.fst b (pullback.snd f a) := by
  refine ⟨(pullbackSymmetry b (pullback.snd f a)).hom ≫ (pullbackLeftPullbackSndIso f a b).hom,
    inferInstance, ?_, ?_⟩
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_fst, ← Category.assoc,
      pullbackSymmetry_hom_comp_fst]
  · rw [Category.assoc, pullbackLeftPullbackSndIso_hom_snd, pullbackSymmetry_hom_comp_snd]

/-! ### The algebraic closure of the fraction field inside a geometric point -/

/-- **The algebraic closure of the fraction field sits inside the residue field of a geometric
point over the generic point.** Let `R` be a domain and let `w : Spec Ω ⟶ Spec R` be a morphism
from the spectrum of an algebraically closed field whose image is the generic point. Then there is
a ring homomorphism `k̄ = AlgebraicClosure (FractionRing R) ⟶ Ω` through which `w` factors as
`Spec Ω ⟶ Spec k̄ ⟶ Spec K ⟶ Spec R`.

The residue field is an extension of the fraction field `K` by
`AlgebraicGeometry.exists_ringHom_fractionRing_of_liesOver_genericPoint`, and `Ω` is algebraically
closed, so `IsAlgClosed.lift` extends that embedding over the algebraic extension `k̄/K`. -/
theorem exists_ringHom_algebraicClosure_of_liesOver_genericPoint {R : Type u} [CommRing R]
    [IsDomain R] {Omega : Type u} [Field Omega] [IsAlgClosed Omega]
    (w : Spec (.of Omega) ⟶ Spec (.of R)) (hw : w default = genericPoint (Spec (.of R))) :
    ∃ χ : AlgebraicClosure (FractionRing R) →+* Omega,
      Spec.map (CommRingCat.ofHom χ) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R)))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))) = w := by
  obtain ⟨ψ, hψ⟩ := exists_ringHom_fractionRing_of_liesOver_genericPoint w hw
  let : Algebra (FractionRing R) Omega := ψ.toAlgebra
  let χ : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R] Omega := IsAlgClosed.lift
  refine ⟨χ.toRingHom, ?_⟩
  have hχ : χ.toRingHom.comp
      (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) = ψ :=
    RingHom.ext fun x ↦ χ.commutes x
  rw [← Spec.map_comp, ← Spec.map_comp, Category.assoc]
  have : CommRingCat.ofHom (algebraMap R (FractionRing R)) ≫
      CommRingCat.ofHom (algebraMap (FractionRing R) (AlgebraicClosure (FractionRing R))) ≫
      CommRingCat.ofHom χ.toRingHom = Spec.preimage w := by
    refine CommRingCat.hom_ext ?_
    rw [← hψ, ← hχ]
    rfl
  rw [this, Spec.map_preimage]

/-! ### The descent, in the shape the limit argument consumes -/

/-- **A Galois cover of `X_Ω` is the base change of a Galois cover of `T ×_Z X_Z`.** Let
`f : X ⟶ S` be proper with geometrically connected fibres, let `a : Z ⟶ S`, let
`b : Spec k̄ ⟶ Z` with `k̄` algebraically closed and let `w : Spec Ω ⟶ S` factor as
`Spec Ω ⟶ Spec k̄ ⟶ Z ⟶ S` along a ring homomorphism `χ : k̄ ⟶ Ω` with `Ω` algebraically closed.
Then every Galois object of `FÉt_{X_Ω}` is the base change of a Galois object of
`FÉt_{Spec k̄ ×_Z X_Z}` along a morphism which lies over `X`.

This is `AlgebraicGeometry.exists_isGalois_model_of_isAlgClosed_base` for the factorization
`Spec Ω ⟶ Spec k̄ ⟶ S` followed by the re-association
`AlgebraicGeometry.exists_isIso_pullback_comp_reassoc`, the Galois object being carried across the
latter by `AlgebraicGeometry.exists_isGalois_essImage_of_isEquivalence`. -/
theorem exists_isGalois_model_reassoc_of_isAlgClosed_tower {S X Z : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [GeometricallyConnected f] (a : Z ⟶ S)
    {kbar Omega : Type u} [Field kbar] [Field Omega] [IsAlgClosed kbar] [IsAlgClosed Omega]
    (b : Spec (.of kbar) ⟶ Z) (w : Spec (.of Omega) ⟶ S) (χ : kbar →+* Omega)
    (hw : Spec.map (CommRingCat.ofHom χ) ≫ b ≫ a = w)
    [ConnectedSpace ↥(pullback f w)] [ConnectedSpace ↥(pullback b (pullback.snd f a))]
    (A : FiniteEtaleOver (pullback f w)) [PreGaloisCategory.IsGalois A] :
    ∃ (q : pullback f w ⟶ pullback b (pullback.snd f a))
      (B : FiniteEtaleOver (pullback b (pullback.snd f a))), PreGaloisCategory.IsGalois B ∧
      Nonempty ((finiteEtaleBaseChange q).obj B ≅ A) ∧
      q ≫ pullback.snd b (pullback.snd f a) ≫ pullback.fst f a = pullback.fst f w := by
  let : Algebra kbar Omega := χ.toAlgebra
  have : ConnectedSpace ↥(pullback f (b ≫ a)) :=
    GeometricallyConnected.geometrically_connectedSpace (f := f) (b ≫ a) _ _
      (IsPullback.of_hasPullback f (b ≫ a))
  obtain ⟨m, hmiso, hmfst, hmsnd⟩ := exists_isIso_pullback_comp_reassoc f a b
  have := hmiso
  -- the descent of the Galois object to `X_{k̄}`
  obtain ⟨B₀, hB₀gal, ⟨e₁⟩⟩ :=
    exists_isGalois_model_of_isAlgClosed_base f (b ≫ a) w
      (by rw [← hw])
      (pullbackBaseChangeMap f w (b ≫ a) (Spec.map (CommRingCat.ofHom χ)) hw)
      (pullbackBaseChangeMap_fst f w (b ≫ a) _ hw)
      (pullbackBaseChangeMap_snd f w (b ≫ a) _ hw) A
  have := hB₀gal
  -- carry it across the re-association
  obtain ⟨B, hBgal, ⟨e₂⟩⟩ :=
    exists_isGalois_essImage_of_isEquivalence (inv m)
      (isEquivalence_finiteEtaleBaseChange_of_isIso _) B₀
  refine ⟨pullbackBaseChangeMap f w (b ≫ a) (Spec.map (CommRingCat.ofHom χ)) hw ≫ inv m,
    B, hBgal, nonempty_iso_finiteEtaleBaseChange_comp _ _ _ rfl e₁ e₂, ?_⟩
  rw [← hmfst, Category.assoc, IsIso.inv_hom_id_assoc,
    pullbackBaseChangeMap_fst f w (b ≫ a) _ hw]

/-! ### Sections of the stages of a base change along an algebraic extension -/

namespace AlgebraicExtensionLimit

variable (K Kbar : Type u) [Field K] [Field Kbar] [Algebra K Kbar]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (σ : Spec (.of K) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

/-- The structure morphism `Spec K(s) ⟶ Spec K` of a stage. -/
abbrev stageHom (s : Finset Kbar) :
    Spec (.of (Algebra.adjoin K (s : Set Kbar))) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (Algebra.adjoin K (s : Set Kbar))))

/-- The transition morphism `Spec K(t) ⟶ Spec K(s)` for `s ⊆ t`, with both spectra written
explicitly; it is the transition morphism of
`AlgebraicGeometry.AdjoinFinset.specDiagram`. -/
def stageSpecMap {s t : Finset Kbar} (e : Opposite.op t ⟶ Opposite.op s) :
    Spec (.of (Algebra.adjoin K (t : Set Kbar))) ⟶
      Spec (.of (Algebra.adjoin K (s : Set Kbar))) :=
  Spec.map (CommRingCat.ofHom (Subalgebra.inclusion
    (Algebra.adjoin_mono (Finset.coe_subset.mpr (leOfHom e.unop)))).toRingHom)

/-- `AlgebraicGeometry.AlgebraicExtensionLimit.stageSpecMap` is the transition morphism of
`AlgebraicGeometry.AdjoinFinset.specDiagram`. -/
theorem stageSpecMap_eq {s t : Finset Kbar} (e : Opposite.op t ⟶ Opposite.op s) :
    stageSpecMap K Kbar e = (AdjoinFinset.specDiagram K Kbar).map e :=
  rfl

/-- The projection `Spec Kbar ⟶ Spec K(s)`, written explicitly; it is the leg of
`AlgebraicGeometry.AdjoinFinset.specCone`. -/
def stageSpecProj (s : Finset Kbar) :
    Spec (.of Kbar) ⟶ Spec (.of (Algebra.adjoin K (s : Set Kbar))) :=
  Spec.map (CommRingCat.ofHom (Algebra.adjoin K (s : Set Kbar)).val.toRingHom)

/-- `AlgebraicGeometry.AlgebraicExtensionLimit.stageSpecProj` is the leg of
`AlgebraicGeometry.AdjoinFinset.specCone`. -/
theorem stageSpecProj_eq (s : Finset Kbar) :
    stageSpecProj K Kbar s = (AdjoinFinset.specCone K Kbar).π.app (Opposite.op s) :=
  rfl

/-- The transition morphisms of the stages lie over `Spec K`. -/
theorem stageSpecMap_comp_stageHom {s t : Finset Kbar}
    (e : Opposite.op t ⟶ Opposite.op s) :
    stageSpecMap K Kbar e ≫ stageHom K Kbar s = stageHom K Kbar t := by
  rw [stageSpecMap, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (by ext x; rfl))

/-- The projections of `Spec Kbar` to the stages are compatible with the transition
morphisms. -/
theorem stageSpecProj_comp_stageSpecMap {s t : Finset Kbar}
    (e : Opposite.op t ⟶ Opposite.op s) :
    stageSpecProj K Kbar t ≫ stageSpecMap K Kbar e = stageSpecProj K Kbar s := by
  rw [stageSpecMap, stageSpecProj, stageSpecProj, ← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext (by ext x; rfl))

/-- The section of the stage `X_{K(s)} ⟶ Spec K(s)` obtained by base change from a section `σ`
of `f : X ⟶ Spec K`. -/
def stageSection (s : Finset Kbar) :
    Spec (.of (Algebra.adjoin K (s : Set Kbar))) ⟶ pullback (stageHom K Kbar s) f :=
  pullback.lift (𝟙 _) (stageHom K Kbar s ≫ σ) (by
    rw [Category.id_comp, Category.assoc, hσ, Category.comp_id])

/-- `AlgebraicGeometry.AlgebraicExtensionLimit.stageSection` is a section of the structure
morphism of the stage. -/
theorem stageSection_fst (s : Finset Kbar) :
    stageSection K Kbar f σ hσ s ≫ pullback.fst (stageHom K Kbar s) f = 𝟙 _ :=
  pullback.lift_fst _ _ _

/-- `AlgebraicGeometry.AlgebraicExtensionLimit.stageSection` lies over `σ`. -/
theorem stageSection_snd (s : Finset Kbar) :
    stageSection K Kbar f σ hσ s ≫ pullback.snd (stageHom K Kbar s) f
      = stageHom K Kbar s ≫ σ :=
  pullback.lift_snd _ _ _

/-- The transition morphism `X_{K(t)} ⟶ X_{K(s)}` of the system of stages, with both base
changes presented as pullbacks. -/
def stageTransition {s t : Finset Kbar} (e : Opposite.op t ⟶ Opposite.op s) :
    pullback (stageHom K Kbar t) f ⟶ pullback (stageHom K Kbar s) f :=
  pullback.lift (pullback.fst (stageHom K Kbar t) f ≫ stageSpecMap K Kbar e)
    (pullback.snd (stageHom K Kbar t) f) (by
    rw [Category.assoc, stageSpecMap_comp_stageHom]
    exact pullback.condition)

/-- `AlgebraicGeometry.AlgebraicExtensionLimit.stageTransition` lies over the transition
morphism of the bases. -/
theorem stageTransition_fst {s t : Finset Kbar} (e : Opposite.op t ⟶ Opposite.op s) :
    stageTransition K Kbar f e ≫ pullback.fst (stageHom K Kbar s) f
      = pullback.fst (stageHom K Kbar t) f ≫ stageSpecMap K Kbar e :=
  pullback.lift_fst _ _ _

/-- `AlgebraicGeometry.AlgebraicExtensionLimit.stageTransition` lies over `X`. -/
theorem stageTransition_snd {s t : Finset Kbar} (e : Opposite.op t ⟶ Opposite.op s) :
    stageTransition K Kbar f e ≫ pullback.snd (stageHom K Kbar s) f
      = pullback.snd (stageHom K Kbar t) f :=
  pullback.lift_snd _ _ _

/-- **The sections of the stages are compatible with the transition morphisms**, both being base
changes of the one section `σ`. -/
theorem stageSection_naturality {s t : Finset Kbar} (e : Opposite.op t ⟶ Opposite.op s) :
    stageSection K Kbar f σ hσ t ≫ stageTransition K Kbar f e
      = stageSpecMap K Kbar e ≫ stageSection K Kbar f σ hσ s := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, stageTransition_fst, ← Category.assoc, stageSection_fst,
      Category.id_comp, Category.assoc, stageSection_fst, Category.comp_id]
  · rw [Category.assoc, stageTransition_snd, stageSection_snd, Category.assoc,
      stageSection_snd, ← Category.assoc, stageSpecMap_comp_stageHom]

/-- **The projection from `X_{Kbar}` factors through every transition morphism of the stages.** -/
theorem bcProj_comp_stageTransition {s t : Finset Kbar}
    (e : Opposite.op t ⟶ Opposite.op s) :
    AdjoinFinset.bcProj K Kbar f (Opposite.op t) ≫ stageTransition K Kbar f e
      = AdjoinFinset.bcProj K Kbar f (Opposite.op s) := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, stageTransition_fst, ← Category.assoc,
      AdjoinFinset.bcProj_fst, AdjoinFinset.bcProj_fst, Category.assoc]
    exact congrArg _ (stageSpecProj_comp_stageSpecMap K Kbar e)
  · rw [Category.assoc, stageTransition_snd, AdjoinFinset.bcProj_snd,
      AdjoinFinset.bcProj_snd]

/-! ### A rational point of a Galois cover at a later stage -/

/-- **A Galois cover of a stage acquires a rational point over the section at a later stage.**
Let `Kbar/K` be an algebraic extension with `Kbar` algebraically closed, let `f : X ⟶ Spec K`
have a section `σ`, and let `V` be a finite étale Galois cover of a stage `X_{K(s)}` whose base
is connected. Then for some larger finite subset `t ⊆ Kbar` there is a `K(t)`-rational point of
`V` lying over the section of the stage `s`.

The structure morphism of `V` is finite étale with connected total space, so its image is a
nonempty clopen subset of the connected `X_{K(s)}`, i.e. everything. Hence the fibre of `V` over
the `Kbar`-point given by the section is a nonempty scheme, finite over the algebraically closed
`Kbar`, and so has a `Kbar`-rational point
(`AlgebraicGeometry.exists_section_of_isIntegralHom_spec`). That `Kbar`-point of `V` lies over the
section, and `Spec Kbar` is the limit of the `Spec K(t)`, so it comes from a finite stage by
`AlgebraicGeometry.GaloisCoverLimits.exists_point_at_stage`. -/
theorem exists_stage_point_of_finiteEtaleGaloisCover [IsAlgClosed Kbar] (s : Finset Kbar)
    [ConnectedSpace ↥(pullback (stageHom K Kbar s) f)]
    {G : Type u} [Group G] [Finite G]
    (V : FiniteEtaleGaloisCover (pullback (stageHom K Kbar s) f) G) :
    ∃ (t : Finset Kbar) (e : Opposite.op t ⟶ Opposite.op s)
      (w : Spec (.of (Algebra.adjoin K (t : Set Kbar))) ⟶ V.obj.left),
      w ≫ (V.obj.hom : V.obj.left ⟶ pullback (stageHom K Kbar s) f)
        = stageSpecMap K Kbar e ≫ stageSection K Kbar f σ hσ s := by
  set g : V.obj.left ⟶ pullback (stageHom K Kbar s) f := V.obj.hom with hg
  have : IsFinite g := V.obj.prop.1
  have : Etale g := V.obj.prop.2
  have : ConnectedSpace ↥V.obj.left := V.connected
  -- the structure morphism of a connected cover of a connected base is surjective
  have hsurj : Surjective g := by
    have hcl : IsClopen (Set.range g.base) :=
      ⟨g.isClosedMap.isClosed_range, g.isOpenMap.isOpen_range⟩
    rw [surjective_iff, ← Set.range_eq_univ]
    exact (isClopen_iff.mp hcl).resolve_left
      (Set.Nonempty.ne_empty (Set.range_nonempty _))
  -- the `Kbar`-point of the base given by the section
  set τ := stageSpecProj K Kbar s ≫ stageSection K Kbar f σ hσ s with hτ
  obtain ⟨x, hx⟩ := hsurj.1 (τ.base default)
  obtain ⟨p, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := g) (g := τ) x default hx
  have : Nonempty ↥(pullback g τ) := ⟨p⟩
  obtain ⟨z, hz⟩ := exists_section_of_isIntegralHom_spec Kbar (pullback.snd g τ)
  -- the instances of the limit presentation of `Spec Kbar` by the `Spec K(t)`
  have hIsAff : ∀ i : (Finset Kbar)ᵒᵖ,
      IsAffine ((AdjoinFinset.specDiagram K Kbar).obj i) := by
    intro i
    dsimp [AdjoinFinset.specDiagram, AdjoinFinset.diagram]; infer_instance
  obtain ⟨j, e, w, hw⟩ := GaloisCoverLimits.exists_point_at_stage
    (AdjoinFinset.specDiagram K Kbar) (AdjoinFinset.specCone K Kbar)
    (AdjoinFinset.isLimitSpecCone K Kbar) (Opposite.op s) g
    (stageSection K Kbar f σ hσ s) (z ≫ pullback.fst g τ)
    (show (z ≫ pullback.fst g τ) ≫ g = τ by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hz, Category.id_comp])
  exact ⟨j.unop, e, w, by rw [stageSpecMap_eq]; exact hw⟩

/-- **Every stage of a base change along an algebraic extension is connected** as soon as the
base change itself is: the projection `X_{Kbar} ⟶ X_{K(s)}` is surjective
(`AlgebraicGeometry.AlgebraicExtensionLimit.flat_and_surjective_and_quasiCompact_bcProj`), and a
continuous surjective image of a connected space is connected. -/
@[ega "III 4.3.4" "special case"]
theorem connectedSpace_pullback_stageHom [Algebra.IsAlgebraic K Kbar]
    [ConnectedSpace ↥(pullback (Spec.map (CommRingCat.ofHom (algebraMap K Kbar))) f)]
    (s : Finset Kbar) : ConnectedSpace ↥(pullback (stageHom K Kbar s) f) := by
  have hs : Surjective (AdjoinFinset.bcProj K Kbar f (Opposite.op s)) :=
    (flat_and_surjective_and_quasiCompact_bcProj K Kbar f (Opposite.op s)).2.1
  rw [connectedSpace_iff_univ, ← Set.range_eq_univ.mpr hs.1]
  exact isConnected_range (AdjoinFinset.bcProj K Kbar f (Opposite.op s)).continuous

end AlgebraicExtensionLimit

/-! ### The base of the extension step: a strictly henselian discrete valuation ring -/

/-- **The spectrum of a discrete valuation ring is a normal scheme.** A discrete valuation ring
is a unique factorization domain, hence integrally closed, hence a normal ring
(`IsNormalRing.of_isIntegrallyClosed`), and the spectrum of a normal ring is normal
(`AlgebraicGeometry.isNormal_spec_of_isNormalRing`).

`IsNormal` is not an instance, so it has to be produced by hand before
[Stacks, Tag 0EYJ] can be applied over such a base. -/
theorem isNormal_spec_of_isDiscreteValuationRing (B : Type u) [CommRing B] [IsDomain B]
    [IsDiscreteValuationRing B] : IsNormal (Spec (.of B)) :=
  isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed B)

/-- **An integer invertible in a ring is invertible in every residue field of its spectrum.**
This is the form in which the order of the Galois group is "invertible on `S`" in
[Stacks, Tag 0EYJ] over an affine base; for a local ring with residue field of characteristic
zero the hypothesis is `Stacks.KummerExtension.isUnit_natCast_of_coprime_ringChar`. -/
theorem isUnit_natCast_specResidueField_of_isUnit {A : Type u} [CommRing A] {n : ℕ}
    (hn : IsUnit (n : A)) (x : Spec (.of A)) :
    IsUnit (n : (Spec (.of A)).residueField x) := by
  let := specResidueFieldAlgebra (CommRingCat.of A) x
  have h : (n : (Spec (.of A)).residueField x)
      = algebraMap (CommRingCat.of A) ((Spec (.of A)).residueField x) (n : A) :=
    (map_natCast (algebraMap (CommRingCat.of A) ((Spec (.of A)).residueField x)) n).symm
  rw [h]
  exact hn.map (algebraMap (CommRingCat.of A) ((Spec (.of A)).residueField x))

end AlgebraicGeometry

end
