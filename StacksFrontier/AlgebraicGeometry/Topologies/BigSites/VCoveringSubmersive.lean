module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.Valuative.Specialization
public import StacksFrontier.AlgebraicGeometry.Topologies.V.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.V.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Vtopology.Permanence
public import StacksFrontier.AlgebraicGeometry.Topologies.Vtopology.QuasiCompactCoverings
public import StacksFrontier.RingTheory.Spectrum.Prime.Specialization

/-!
# V coverings are universally submersive

The morphism from the disjoint union of a V covering of a scheme to that scheme is
universally submersive: its underlying continuous map is a quotient map, and so is the
underlying map of every base change.

## Main results

* `AlgebraicGeometry.isVCovering_universallySubmersive` — the coproduct morphism of a V
  covering is universally submersive.

## Implementation notes

Submersiveness of a morphism of schemes is `Topology.IsQuotientMap` on the underlying map, and
universal submersiveness is `CategoryTheory.MorphismProperty.universally` applied to it, so
the statement quantifies over every base change without fixing a model for the fibre product.

The proof has three layers. For a *standard* V covering of an affine scheme the valuative
criterion gives lifting of specializations along the coproduct morphism, and lifting of
specializations plus surjectivity gives that a set with closed preimage is closed, which is
the quotient-map condition: the scheme-theoretic image of the closed subscheme cut out by the
preimage is exactly that set, and it is closed because it is stable under specialization. A
general V covering is standard over each affine open, and being a quotient map is Zariski-local
on the target. Universality is then base change of V coverings.

## References

* [Stacks Project, Tag 0ETP](https://stacks.math.columbia.edu/tag/0ETP)
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- A quasi-compact morphism of schemes along which specializations lift is a quotient map
on underlying spaces. -/
theorem Scheme.Hom.isQuotientMap_of_lift_specializes {X Y : Scheme.{u}} (g : X ⟶ Y)
    [QuasiCompact g] (hg : ∀ y' y : Y, y' ⤳ y → ∃ x' x : X, x' ⤳ x ∧ g x' = y' ∧ g x = y) :
    Topology.IsQuotientMap g.base := by
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨_, x, _, _, hx⟩ := hg y y (specializes_refl y)
    exact ⟨x, hx⟩
  refine Topology.isQuotientMap_iff_isClosed.mpr
    ⟨hsurj, fun s ↦ ⟨fun hs ↦ hs.preimage g.continuous, fun hs ↦ ?_⟩⟩
  let Z : TopologicalSpace.Closeds X := ⟨g ⁻¹' s, hs⟩
  let W := (Scheme.IdealSheafData.vanishingIdeal Z).subscheme
  let j : W ⟶ X := (Scheme.IdealSheafData.vanishingIdeal Z).subschemeι
  let gW : W ⟶ Y := j ≫ g
  have hrangej' : Set.range (j : W → X) = g ⁻¹' s := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  have hstable : StableUnderSpecialization s := by
    intro y y' hyy' hy
    obtain ⟨x', x, hxx', rfl, rfl⟩ := hg y y' hyy'
    exact hs.stableUnderSpecialization hxx' hy
  have hrangegW : Set.range (gW : W → Y) = s := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact hrangej'.subset ⟨w, rfl⟩
    · intro hy
      obtain ⟨x, rfl⟩ := hsurj y
      obtain ⟨w, rfl⟩ := hrangej'.symm.subset hy
      exact ⟨w, rfl⟩
  simpa [hrangegW] using
    (isClosed_range_iff_stableUnderSpecialization gW).2 (hrangegW ▸ hstable)

/-- The two projections of a pullback agree after composing with the structure maps. -/
private theorem pullback_condition_apply {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    (p : (pullback f g : Scheme.{u})) : f (pullback.fst f g p) = g (pullback.snd f g p) := by
  simpa [Scheme.Hom.comp_apply] using congrArg (fun k : pullback f g ⟶ Z ↦ k p)
    (pullback.condition (f := f) (g := g))

/-- If `c ≫ f' = h` is a quotient map, then so is `f'`. -/
private theorem isQuotientMap_of_comp_eq {X Y Z : Scheme.{u}} (c : X ⟶ Y) (f' : Y ⟶ Z)
    (h : X ⟶ Z) (hh : c ≫ f' = h) (hq : Topology.IsQuotientMap h) :
    Topology.IsQuotientMap f' :=
  Topology.IsQuotientMap.of_comp c.continuous f'.continuous (by
    subst hh
    exact hq)

private theorem standardVCovering_quotientMap {T : Scheme.{u}} [IsAffine T]
    {I : Type v} [Finite I] (X : I → Scheme.{u}) [∀ i, IsAffine (X i)]
    (f : ∀ i, X i ⟶ T) (hf : IsStandardVCovering X f) :
    Topology.IsQuotientMap (Sigma.desc f).base := by
  let q : Scheme := ∐ X
  let fq : q ⟶ T := Sigma.desc f
  have hstd : IsStandardVCovering (fun _ : Unit ↦ q) (fun _ ↦ fq) :=
    ((isStandardVCovering_tfae X f).out 1 3).mp hf
  have hval : ∀ (V : Type u) [CommRing V] [IsDomain V] [ValuationRing V]
      (g : Spec (.of V) ⟶ T),
      ∃ (W : Type u) (_ : CommRing W) (_ : IsDomain W) (_ : ValuationRing W)
        (e : V →+* W),
        IsExtensionOfValuationRings e ∧
          ∃ (h : Spec (.of W) ⟶ q),
            Spec.map (CommRingCat.ofHom e) ≫ g = h ≫ fq := by
    intro V hVring hVdom hVval g
    simpa [IsStandardVCovering] using hstd V g
  have hspec := (valuation_lifting_iff_specialization_lifting fq).mp hval
  refine Scheme.Hom.isQuotientMap_of_lift_specializes fq fun x' x hxx' ↦ ?_
  obtain ⟨w', w, hww', hw'x', hwx⟩ := hspec T (𝟙 T) x' x hxx'
  have hpr (z : (pullback (𝟙 T) fq : Scheme.{u})) : fq (pullback.snd (𝟙 T) fq z) =
      pullback.fst (𝟙 T) fq z := by
    simpa using (pullback_condition_apply (𝟙 T) fq z).symm
  exact ⟨pullback.snd (𝟙 T) fq w', pullback.snd (𝟙 T) fq w,
    hww'.map (pullback.snd (𝟙 T) fq).continuous, (hpr w').trans hw'x', (hpr w).trans hwx⟩

/-- A morphism of schemes whose base change to every affine open of the target is a quotient
map is itself a quotient map. -/
theorem Scheme.Hom.isQuotientMap_of_affineOpens {X T : Scheme.{u}} (g : X ⟶ T)
    (hg : ∀ U : T.affineOpens, Topology.IsQuotientMap (pullback.snd g U.1.ι)) :
    Topology.IsQuotientMap g := by
  have hsurj : Function.Surjective g := by
    intro x
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, _⟩ :=
      T.isBasis_affineOpens.exists_subset_of_mem_open (by simp) isOpen_univ
    let U : T.affineOpens := ⟨V, hV⟩
    obtain ⟨p, hp⟩ := (hg U).surjective ⟨x, hxV⟩
    refine ⟨pullback.fst g U.1.ι p, ?_⟩
    rw [pullback_condition_apply]
    simpa using congrArg U.1.ι hp
  refine Topology.isQuotientMap_iff_isClosed.mpr
    ⟨hsurj, fun s ↦ ⟨fun hs ↦ hs.preimage g.continuous, fun hs ↦ ?_⟩⟩
  rw [TopologicalSpace.IsOpenCover.isClosed_iff_coe_preimage (iSup_affineOpens_eq_top T)]
  intro U
  have hpre : (pullback.snd g U.1.ι) ⁻¹' (U.1.ι ⁻¹' s) =
      (pullback.fst g U.1.ι) ⁻¹' (g ⁻¹' s) := by
    ext p
    simp [pullback_condition_apply]
  exact ((Topology.isQuotientMap_iff_isClosed.mp (hg U)).2 _).mpr
    (hpre ▸ hs.preimage (pullback.fst g U.1.ι).continuous)

private theorem vCovering_quotientMap {T : Scheme.{u}} {I : Type v} [Small.{u} I]
    (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : IsVCovering X f) : Topology.IsQuotientMap (Sigma.desc f) := by
  let q : Scheme := ∐ X
  refine Scheme.Hom.isQuotientMap_of_affineOpens _ fun U ↦ ?_
  obtain ⟨𝒰, hfinite, haffine, hstd, ⟨φ⟩⟩ := hf U.1 U.2
  have : Finite 𝒰.I₀ := hfinite
  have : ∀ j, IsAffine (𝒰.X j) := haffine
  let fam : PreZeroHypercover U.1.toScheme :=
    ({ I₀ := I, X := X, f := f } : PreZeroHypercover T).pullback₂ U.1.ι
  have : Small.{u} fam.I₀ := inferInstanceAs (Small.{u} I)
  let qU : (∐ fam.X) ⟶ U.1.toScheme := Sigma.desc fam.f
  let h : (∐ 𝒰.X) ⟶ ∐ fam.X :=
    Sigma.desc (f := 𝒰.X) fun j ↦ φ.h₀ j ≫ Sigma.ι fam.X (φ.s₀ j)
  have hfactor : Sigma.desc 𝒰.f = h ≫ qU := Sigma.hom_ext _ _ fun j ↦ by
    calc
      Sigma.ι 𝒰.X j ≫ Sigma.desc 𝒰.f = 𝒰.f j := Sigma.ι_desc _ _
      _ = φ.h₀ j ≫ fam.f (φ.s₀ j) := (φ.w₀ j).symm
      _ = Sigma.ι 𝒰.X j ≫ h ≫ qU := by
        simp [h, qU, Category.assoc]
  have hqU : Topology.IsQuotientMap qU :=
    isQuotientMap_of_comp_eq h qU _ hfactor.symm (standardVCovering_quotientMap 𝒰.X 𝒰.f hstd)
  let a : (∐ fam.X) ⟶ q :=
    Sigma.desc (f := fam.X) fun i ↦ by
      simpa [fam, PreZeroHypercover.pullback₂] using
        (pullback.fst (f i) U.1.ι ≫ Sigma.ι X i)
  have hcomm : a ≫ Sigma.desc f = qU ≫ U.1.ι := by
    apply Sigma.hom_ext
    intro i
    dsimp only [a, qU]
    rw [← Category.assoc, Sigma.ι_desc, ← Category.assoc, Sigma.ι_desc]
    simpa [fam, PreZeroHypercover.pullback₂] using
      (pullback.condition (f := f i) (g := U.1.ι))
  exact isQuotientMap_of_comp_eq (pullback.lift a qU hcomm) _ qU (pullback.lift_snd _ _ _) hqU

/-- **Stacks Project, Tag 0ETP.** The morphism from the disjoint union of a
V covering to its target is universally submersive. -/
@[stacks 0ETP]
public theorem isVCovering_universallySubmersive {T : Scheme.{u}} {I : Type v}
    [Small.{u} I] (X : I → Scheme.{u}) (f : ∀ i, X i ⟶ T)
    (hf : IsVCovering X f) :
    universally (topologically @Topology.IsQuotientMap) (Sigma.desc f) := by
  intro X' Y' i₁ i₂ f' H
  let P : I → Scheme.{u} := fun i ↦ pullback (f i) i₂
  let gP : ∀ i, P i ⟶ Y' := fun i ↦ pullback.snd (f i) i₂
  have hcompat (i : I) : gP i ≫ i₂ =
      (pullback.fst (f i) i₂ ≫ Sigma.ι X i) ≫ Sigma.desc f := by
    simpa [gP, Category.assoc] using
      (pullback.condition (f := f i) (g := i₂)).symm
  let l : ∀ i, P i ⟶ X' := fun i ↦
    H.lift (gP i) (pullback.fst (f i) i₂ ≫ Sigma.ι X i) (hcompat i)
  let c : (∐ P) ⟶ X' := Sigma.desc l
  have hfactor : Sigma.desc gP = c ≫ f' :=
    Sigma.hom_ext _ _ fun i ↦ by simp [c, l, gP, H.lift_fst]
  exact isQuotientMap_of_comp_eq c f' _ hfactor.symm
    (vCovering_quotientMap P gP (isVCovering_pullback X f i₂ hf))

end AlgebraicGeometry
