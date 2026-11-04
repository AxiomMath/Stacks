module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.FieldExtensionFlatPullback
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.FiniteLocallyFreeFibreDegree
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeCompositeResidueIso
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.GeneralBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeSquare
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SeparableMultiplicityOne
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import StacksFrontier.AlgebraicGeometry.Chow.EnvelopeCycleLift
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.ResidueFieldSpecMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FlatPullbackFamily

/-!
# Base change of a zero-cycle along a finite residue field extension

Let `f : X ⟶ S` be locally of finite type, let `g : S' ⟶ S` be a morphism and let `t` be a point
of `S'` such that the residue field extension `κ(t)/κ(g t)` is finite of degree `d`. The fibre of
`X ×_S S'` over `t` is the base change of the fibre of `f` over `g t` along `κ(t)/κ(g t)`, so the
induced morphism of fibres is finite locally free of degree `d`, and the base change multiplicities
of the points above a given point of the fibre of `f`, weighted by their residue degrees, add up
to `d` (Stacks 02RH). Consequently, if the base change `g^*α` of a family of `0`-cycles is, over
`t`, the cycle `m [P]` at a single point `P` whose residue field extension over its image is
trivial, then `d` divides `m`.

This is the computation behind both counterexamples of Stacks Remark 0H5Y: in each, a cycle
which is `1` or `2` times a rational point after a purely inseparable extension of degree `2` or
`4` cannot come from below.

## Main results

* `Stacks.Chow.finrank_dvd_of_baseChangeFamily_eq_single` — if `(g^*α)_t = m [P]` with `P` of
  residue degree one over its image, then `[κ(t) : κ(g t)]` divides `m`.

## References

* [Stacks Project, Remark 0H5Y](https://stacks.math.columbia.edu/tag/0H5Y)
* [Stacks Project, Tag 02RH](https://stacks.math.columbia.edu/tag/02RH)
* [Stacks Project, Tag 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

variable {X S S' : Scheme.{u}}

/-- A finite sum over `s` of a function vanishing on `s` away from `a ∈ s` is its value at `a`. -/
theorem finsum_mem_eq_of_forall_ne_eq_zero {A M : Type*} [AddCommMonoid M] {F : A → M}
    {s : Set A} {a : A} (ha : a ∈ s) (h : ∀ x ∈ s, x ≠ a → F x = 0) :
    ∑ᶠ x ∈ s, F x = F a := by
  rw [finsum_mem_inter_support_eq F s {a}, finsum_mem_singleton]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Function.mem_support]
  refine ⟨fun ⟨hx, hFx⟩ => ⟨by_contra fun hxa => hFx (h x hx hxa), hFx⟩, ?_⟩
  rintro ⟨rfl, hFx⟩
  exact ⟨ha, hFx⟩

/-- If the coefficients `c (π x) * w x` of a cycle are `m` at `P` and zero elsewhere, and the
weighted sum of the `w x * r x` over the fibre of `π` through `P` is `d`, where `r P = 1`, then `d`
divides `m`. -/
theorem dvd_of_mul_eq_ite {A B : Type*} (π : A → B) (c : B → ℤ) (w r : A → ℤ) (P : A)
    (m d : ℤ) (hr : r P = 1) (hdeg : c (π P) ≠ 0 → ∑ᶠ x ∈ π ⁻¹' {π P}, w x * r x = d)
    (h : ∀ x, c (π x) * w x = open Classical in if x = P then m else 0) : d ∣ m := by
  have hm : c (π P) * w P = m := by simpa using h P
  by_cases hc : c (π P) = 0
  · simp [← hm, hc]
  have hsum : ∑ᶠ x ∈ π ⁻¹' {π P}, w x * r x = w P * r P :=
    finsum_mem_eq_of_forall_ne_eq_zero (s := π ⁻¹' {π P}) (a := P) rfl fun x hx hxP => by
      have h₁ := h x
      rw [ite_eq_right hxP, show π x = π P from hx] at h₁
      simp [(mul_eq_zero.mp h₁).resolve_left hc]
  rw [← hm, ← hdeg hc, hsum, hr, mul_one]
  exact dvd_mul_left _ _

/-- **Base change of a zero-cycle concentrated at a rational point.** Let `κ(t)/κ(g t)` be finite
of degree `d`. If the base change `g^*α` of a family of `0`-cycles on the fibres of `X/S` is,
on the fibre over `t`, the cycle `m [P]` supported at a single point `P` whose residue field is
that of its image in the fibre of `f` over `g t`, then `d` divides `m`. -/
theorem finrank_dvd_of_baseChangeFamily_eq_single (f : X ⟶ S) [LocallyOfFiniteType f]
    (g : S' ⟶ S) (t : S') (α : FamilyOfCycles f 0) (P : (pullback.snd f g).fiber t) (m : ℤ)
    [hfin : letI := (g.residueFieldMap t).hom.toAlgebra
      FiniteDimensional (S.residueField (g t)) (S'.residueField t)]
    (hP : (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition
      t).residueDegree P = 1)
    (h : ∀ x, (baseChangeFamily f g 0 α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
      open Classical in if x = P then m else 0) :
    letI := (g.residueFieldMap t).hom.toAlgebra
    (Module.finrank (S.residueField (g t)) (S'.residueField t) : ℤ) ∣ m := by
  let : Algebra (S.residueField (g t)) (S'.residueField t) := (g.residueFieldMap t).hom.toAlgebra
  set K := S.residueField (g t)
  set L := S'.residueField t
  set d := Module.finrank K L
  set π := restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t
  set sXL := (pullback.snd f g).fiberToSpecResidueField t
  set sY := f.fiberToSpecResidueField (g t)
  set gg := (fieldExtensionBaseChangeSituation K L).g
  have hsq : IsPullback π sXL sY gg := isPullback_restrictedFiberMap_baseChange f g t
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank gg d :=
    Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_of_field
  have : Stacks.Morphisms.IsFiniteLocallyFreeOfRank π d :=
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank.of_isPullback hsq.flip
  have : LocallyOfFiniteType gg :=
    Stacks.Morphisms.locallyOfFiniteType_of_isFiniteLocallyFreeOfRank gg d
  have : LocallyOfFiniteType sXL := by
    change LocallyOfFiniteType (pullback.snd (pullback.snd f g) (S'.fromSpecResidueField t))
    infer_instance
  have : LocallyOfFiniteType sY := by
    change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField (g t)))
    infer_instance
  -- the multiplicity of `g^*α` at a point, read for the two Chow situations
  have hw (x : (pullback.snd f g).fiber t) :
      flatPullbackWeight (fieldChowSituation L) sXL π ((0 : ℕ) : ℤ) x =
        flatPullbackWeight (fieldChowSituation K) (sXL ≫ gg) π
          (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) x := by
    refine flatPullbackWeight_congr_chowSituation _ _ _ _ _ _ _ x ?_
    rw [relativeDimension_comp_fieldExtension K L sXL x]
    simp
  have hcoeff (x : (pullback.snd f g).fiber t) :
      (baseChangeFamily f g 0 α t : AlgebraicCycle ((pullback.snd f g).fiber t) ℤ) x =
        (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ) (π x) *
          flatPullbackWeight (fieldChowSituation K) (sXL ≫ gg) π
            (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)) x := by
    rw [← hw x, baseChangeFamily_apply]
    rfl
  refine dvd_of_mul_eq_ite π.base (fun y => (α (g t) : AlgebraicCycle (f.fiber (g t)) ℤ) y)
    (flatPullbackWeight (fieldChowSituation K) (sXL ≫ gg) π (((0 : ℕ) : ℤ) + ((0 : ℕ) : ℤ)))
    (fun x => π.residueDegree x) P m d (by simp [hP]) (fun hαy => ?_)
    fun x => (hcoeff x).symm.trans (h x)
  exact fibreDegreeIsRank_of_isFiniteLocallyFreeOfRank (fieldChowSituation K) (sXL ≫ gg) sY π d
    hsq.w ((0 : ℕ) : ℤ) (π P) (relativeDimension_of_cycle_coeff_ne_zero (fieldChowSituation K) sY
      ((0 : ℕ) : ℤ) (α (g t)) (π P) hαy)

/-! ### Residue fields along fibres and sections -/

/-- The inclusion of a scheme-theoretic fibre induces a surjection on the residue field at every
point of the fibre: it is a preimmersion, so it is surjective on stalks. -/
theorem surjective_residueFieldMap_fiberι {P T : Scheme.{u}} (p : P ⟶ T) (t : T)
    (y : p.fiber t) : Function.Surjective ((p.fiberι t).residueFieldMap y) := by
  have hsurj : Function.Surjective ((p.fiberι t).stalkMap y ≫ (p.fiber t).residue y).hom := by
    rw [CommRingCat.hom_comp]
    exact ((p.fiber t).residue_surjective y).comp ((p.fiberι t).stalkMap_surjective y)
  rw [← Scheme.residue_residueFieldMap (p.fiberι t) y, CommRingCat.hom_comp,
    RingHom.coe_comp] at hsurj
  exact Function.Surjective.of_comp hsurj

/-- The residue field map of a composite, applied to an element, factors through the residue field
maps of the two factors. -/
theorem residueFieldMap_comp_apply {X Y Z : Scheme.{u}} (g : X ⟶ Y) (p : Y ⟶ Z) (x : X)
    (w : Z.residueField (p (g x))) :
    g.residueFieldMap x (p.residueFieldMap (g x) w) = (g ≫ p).residueFieldMap x w := by
  rw [Scheme.residueFieldMap_comp]
  rfl

/-- **A section with a rational image point has residue degree one.** Let a commutative square
`a ≫ f = p ≫ g` be given and a section `σ` of `p` such that `σ ≫ a` induces a surjection
`κ(a (σ t)) ⟶ κ(t)` on residue fields. Then the morphism of fibres over `t` has residue degree
one at the point of the fibre sitting over `σ t`. -/
theorem residueDegree_restrictedFiberMap_eq_one_of_section {X S P T : Scheme.{u}} (f : X ⟶ S)
    (p : P ⟶ T) (a : P ⟶ X) (g : T ⟶ S) (hw : a ≫ f = p ≫ g) (t : T) (σ : T ⟶ P)
    (hsurj : Function.Surjective ((σ ≫ a).residueFieldMap t)) (Q : p.fiber t)
    (hQ : p.fiberι t Q = σ t) :
    (restrictedFiberMap f p a g hw t).residueDegree Q = 1 := by
  set ψ := restrictedFiberMap f p a g hw t
  -- the residue map of `a` at `σ t` is surjective
  have ha : Function.Surjective (a.residueFieldMap (σ t)) := by
    intro z
    obtain ⟨w, hw⟩ := hsurj ((σ.residueFieldMap t) z)
    exact ⟨w, (σ.residueFieldMap t).hom.injective ((residueFieldMap_comp_apply σ a t w).trans hw)⟩
  have hcomp : Function.Surjective ((p.fiberι t ≫ a).residueFieldMap Q) := by
    rw [← hQ] at ha
    intro z
    obtain ⟨w, rfl⟩ := surjective_residueFieldMap_fiberι p t Q z
    obtain ⟨v, rfl⟩ := ha w
    exact ⟨v, (residueFieldMap_comp_apply (p.fiberι t) a Q v).symm⟩
  rw [← restrictedFiberMap_fiberι f p a g hw t] at hcomp
  have hψ : Function.Surjective (ψ.residueFieldMap Q) := by
    intro z
    obtain ⟨w, hw⟩ := hcomp z
    exact ⟨_, (residueFieldMap_comp_apply ψ (f.fiberι (g t)) Q w).trans hw⟩
  exact residueDegree_eq_one_of_residueFieldMap_isIso ψ Q
    ((ConcreteCategory.isIso_iff_bijective _).mpr ⟨(ψ.residueFieldMap Q).hom.injective, hψ⟩)

/-! ### The cycle of a section -/

/-- A nonempty subsingleton space is its own unique generic point: the closure of the point is
the whole space, which is irreducible. -/
theorem mem_genericPoints_of_subsingleton {Z : Type*} [TopologicalSpace Z] [Subsingleton Z]
    (z : Z) : z ∈ genericPoints Z := by
  have huniv : ({z} : Set Z) = Set.univ := Set.eq_univ_of_forall fun w => Subsingleton.elim w z
  change closure ({z} : Set Z) ∈ irreducibleComponents Z
  rw [huniv, closure_univ]
  exact ⟨huniv ▸ isIrreducible_singleton, fun T _ _ => Set.subset_univ T⟩

/-- The cycle of a reduced closed subscheme consisting of a single point `z` is the point `i z`
with coefficient one, provided `i z` has the relevant relative dimension. -/
theorem closedSubschemeCycleCoeff_eq_ite_of_subsingleton (C : ChowSituation.{u})
    {Y Z : Scheme.{u}} (q : Y ⟶ C.S) [LocallyOfFiniteType q] (i : Z ⟶ Y) [IsClosedImmersion i]
    [Subsingleton Z] [IsReduced Z] (z : Z) (k : ℤ)
    (hz : relativeDimension C.dimensionFunction q (i z) = k) (x : Y) :
    closedSubschemeCycleCoeff C q i k x = open Classical in if x = i z then 1 else 0 := by
  classical
  unfold closedSubschemeCycleCoeff
  by_cases hx : x = i z
  · subst hx
    rw [dite_eq_left ⟨⟨z, mem_genericPoints_of_subsingleton z⟩, rfl, hz⟩, ite_eq_left rfl]
    exact componentMultiplicity_eq_one_of_isReduced i _
  · rw [ite_eq_right hx, dite_eq_right]
    rintro ⟨ξ, hξ, -⟩
    exact hx (by rw [← hξ, Subsingleton.elim ξ.1 z])

/-- The relative dimension of a point at which a morphism to the spectrum of a field is an
isomorphism vanishes. -/
theorem relativeDimension_eq_zero_of_isIso {K : Type u} [Field K] {Z : Scheme.{u}}
    (h : Z ⟶ Spec (.of K)) [IsIso h] (z : Z) :
    relativeDimension (fieldChowSituation K).dimensionFunction h z = 0 := by
  unfold relativeDimension
  rw [fieldChowSituation_dimensionFunction_eq_zero, zero_add]
  let := (h.residueFieldMap z).hom.toAlgebra
  rw [trdeg_zero_of_surjective_algebraMap]
  · simp
  · exact ((ConcreteCategory.isIso_iff_bijective (h.residueFieldMap z)).mp inferInstance).2

/-- **The cycle of a section.** For a section `σ` of `p : P ⟶ T` which is a closed immersion,
the member over `t` of the family `[σ(T)/P/T]_0` is the point of the fibre lying over `σ t`, with
coefficient one. -/
theorem familyAssociatedToClosedSubscheme_apply_of_section {P T : Scheme.{u}} (p : P ⟶ T)
    [LocallyOfFiniteType p] (σ : T ⟶ P) [IsClosedImmersion σ] (hσ : σ ≫ p = 𝟙 T) (t : T)
    (x : p.fiber t) :
    ((familyAssociatedToClosedSubscheme p σ 0 t : FiberCycleGroup p t 0) :
        AlgebraicCycle (p.fiber t) ℤ) x =
      open Classical in if p.fiberι t x = σ t then 1 else 0 := by
  classical
  rw [familyAssociatedToClosedSubscheme_apply]
  change closedSubschemeCycleCoeff (fieldChowSituation (T.residueField t))
    (p.fiberToSpecResidueField t) (fiberClosedImmersion p σ t) ((0 : ℕ) : ℤ) x = _
  set r := T.fromSpecResidueField t
  -- the closed subscheme of the fibre is the spectrum of `κ(t)`
  let e : pullback σ (p.fiberι t) ≅ Spec (T.residueField t) :=
    (pullbackRightPullbackFstIso p r σ ≪≫ pullback.congrHom hσ rfl ≪≫
      asIso (pullback.snd (𝟙 T) r) : pullback σ (pullback.fst p r) ≅ Spec (T.residueField t))
  have he' : (pullbackRightPullbackFstIso p r σ).hom ≫ (pullback.congrHom hσ rfl).hom ≫
      pullback.snd (𝟙 T) r = pullback.snd σ (pullback.fst p r) ≫ pullback.snd p r := by
    simp only [pullback.congrHom_hom, pullback.map, pullback.lift_snd, Category.comp_id,
      pullbackRightPullbackFstIso_hom_snd]
  have he : e.hom = fiberClosedImmersion p σ t ≫ p.fiberToSpecResidueField t := he'
  have : Subsingleton ↥(pullback σ (p.fiberι t)) := e.hom.homeomorph.injective.subsingleton
  have : IsReduced (pullback σ (p.fiberι t)) := isReduced_of_isOpenImmersion e.hom
  let z : ↥(pullback σ (p.fiberι t)) := e.inv (Nonempty.some inferInstance)
  -- the point of the closed subscheme lies over `σ t`
  have hz : p.fiberι t (fiberClosedImmersion p σ t z) = σ t := by
    have h1 : p.fiberι t (fiberClosedImmersion p σ t z) = σ (pullback.fst σ (p.fiberι t) z) := by
      change (fiberClosedImmersion p σ t ≫ p.fiberι t) z = (pullback.fst σ (p.fiberι t) ≫ σ) z
      rw [fiberClosedImmersion, ← pullback.condition]
    have h2 : pullback.fst σ (p.fiberι t) z = t := by
      have hp : p (σ (pullback.fst σ (p.fiberι t) z)) = pullback.fst σ (p.fiberι t) z := by
        change (σ ≫ p) _ = _
        rw [hσ]
        rfl
      rw [← hp, ← h1, Scheme.Hom.apply_fiberι]
    rw [h1, h2]
  have hdim : relativeDimension (fieldChowSituation (T.residueField t)).dimensionFunction
      (p.fiberToSpecResidueField t) (fiberClosedImmersion p σ t z) = ((0 : ℕ) : ℤ) := by
    rw [← relativeDimension_comp_closedImmersion, ← he]
    exact @relativeDimension_eq_zero_of_isIso _ _ _ e.hom (Iso.isIso_hom e) z
  rw [closedSubschemeCycleCoeff_eq_ite_of_subsingleton _ _ _ z _ hdim x]
  congr 1
  exact propext ⟨fun h => h ▸ hz, fun h => (p.fiberι t).isEmbedding.injective (h.trans hz.symm)⟩

/-! ### Residue fields of the spectrum of a field -/

/-- The residue field of a prime of a field is the field. -/
theorem bijective_algebraMap_residueField_of_field (F : Type u) [Field F] (y : PrimeSpectrum F) :
    Function.Bijective (algebraMap F y.asIdeal.ResidueField) := by
  have hmax : y.asIdeal.IsMaximal := by
    rw [Ideal.eq_bot_of_prime y.asIdeal]
    exact Ideal.bot_isMaximal
  have hb := y.asIdeal.bijective_algebraMap_quotient_residueField
  rw [IsScalarTower.algebraMap_eq F (F ⧸ y.asIdeal) y.asIdeal.ResidueField, RingHom.coe_comp]
  exact hb.comp ⟨RingHom.injective _, Ideal.Quotient.mk_surjective⟩

/-- The residue field map of `Spec L ⟶ Spec C` at the point of `Spec L` sends the image of `c` to
the image of `φ c`. -/
private theorem residueFieldMap_specMap_residueFieldIso_inv {C L : Type u} [CommRing C] [Field L]
    (φ : C →+* L) (t : Spec (.of L)) (c : C) :
    haveI : t.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := L) t
    (Spec.map (CommRingCat.ofHom φ)).residueFieldMap t
      ((Scheme.Spec.residueFieldIso (.of C) (PrimeSpectrum.comap φ t)).inv
        (algebraMap C (PrimeSpectrum.comap φ t).asIdeal.ResidueField c)) =
    (Scheme.Spec.residueFieldIso (.of L) t).inv (algebraMap L t.asIdeal.ResidueField (φ c)) := by
  have : t.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := L) t
  set x : PrimeSpectrum C := PrimeSpectrum.comap φ t
  apply (Scheme.Spec.residueFieldIso (.of L) t).commRingCatIsoToRingEquiv.injective
  have h1 := residueFieldMap_specMap_apply (CommRingCat.ofHom φ) t
    ((Scheme.Spec.residueFieldIso (.of C) x).inv (algebraMap C x.asIdeal.ResidueField c))
  have h2 : (Scheme.Spec.residueFieldIso (.of C) x).hom ((Scheme.Spec.residueFieldIso (.of C) x).inv
      (algebraMap C x.asIdeal.ResidueField c)) = algebraMap C x.asIdeal.ResidueField c :=
    Iso.inv_hom_id_apply _ _
  have h3 := Ideal.ResidueField.map_algebraMap x.asIdeal t.asIdeal φ rfl c
  have h4 : (Scheme.Spec.residueFieldIso (.of L) t).hom ((Scheme.Spec.residueFieldIso (.of L) t).inv
      (algebraMap L t.asIdeal.ResidueField (φ c))) = algebraMap L t.asIdeal.ResidueField (φ c) :=
    Iso.inv_hom_id_apply _ _
  exact h1.trans (((congrArg _ h2).trans h3).trans h4.symm)

/-- The degree of the residue field extension of `Spec L ⟶ Spec K` at the point of `Spec L` is
the degree of `L` over `K`. -/
theorem finrank_residueFieldMap_specMap (K L : Type u) [Field K] [Field L] [Algebra K L]
    (t : Spec (.of L)) :
    letI := ((Spec.map (CommRingCat.ofHom (algebraMap K L))).residueFieldMap t).hom.toAlgebra
    Module.finrank ((Spec (.of K)).residueField ((Spec.map (CommRingCat.ofHom (algebraMap K L))) t))
      ((Spec (.of L)).residueField t) = Module.finrank K L := by
  set φ : CommRingCat.of K ⟶ CommRingCat.of L := CommRingCat.ofHom (algebraMap K L)
  let := ((Spec.map φ).residueFieldMap t).hom.toAlgebra
  set x : PrimeSpectrum K := PrimeSpectrum.comap φ.hom t
  have : t.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := L) t
  let eK : K ≃+* x.asIdeal.ResidueField :=
    RingEquiv.ofBijective _ (bijective_algebraMap_residueField_of_field K x)
  let eL : L ≃+* t.asIdeal.ResidueField :=
    RingEquiv.ofBijective _ (bijective_algebraMap_residueField_of_field L t)
  let iK : K ≃+* (Spec (.of K)).residueField ((Spec.map φ) t) :=
    eK.trans (Scheme.Spec.residueFieldIso (.of K) x).symm.commRingCatIsoToRingEquiv
  let iL : L ≃+* (Spec (.of L)).residueField t :=
    eL.trans (Scheme.Spec.residueFieldIso (.of L) t).symm.commRingCatIsoToRingEquiv
  refine (Algebra.finrank_eq_of_equiv_equiv iK iL ?_).symm
  ext a
  change ((Spec.map φ).residueFieldMap t) ((Scheme.Spec.residueFieldIso (.of K) x).inv
      (algebraMap K x.asIdeal.ResidueField a)) =
    (Scheme.Spec.residueFieldIso (.of L) t).inv (algebraMap L t.asIdeal.ResidueField
      (algebraMap K L a))
  exact residueFieldMap_specMap_residueFieldIso_inv φ.hom t a

/-- **Base change through a square of a zero-cycle concentrated at a rational point.** The form
of `Stacks.Chow.finrank_dvd_of_baseChangeFamily_eq_single` for the base change through an
arbitrary cartesian square `a ≫ f = p ≫ g`: if `(g^*α)_t = m [Q]` with `Q` of residue degree one
over its image in the fibre of `f`, then `[κ(t) : κ(g t)]` divides `m`. -/
theorem finrank_dvd_of_baseChangeFamilyOfIsPullback_eq_single (f : X ⟶ S)
    [LocallyOfFiniteType f] {T P : Scheme.{u}} {g : T ⟶ S} {a : P ⟶ X} {p : P ⟶ T}
    [LocallyOfFiniteType p] (sq : IsPullback a p f g) (t : T) (α : FamilyOfCycles f 0)
    (Q : p.fiber t) (m : ℤ)
    [hfin : letI := (g.residueFieldMap t).hom.toAlgebra
      FiniteDimensional (S.residueField (g t)) (T.residueField t)]
    (hQ : (restrictedFiberMap f p a g sq.w t).residueDegree Q = 1)
    (h : ∀ x, (baseChangeFamilyOfIsPullback f sq 0 α t : AlgebraicCycle (p.fiber t) ℤ) x =
      open Classical in if x = Q then m else 0) :
    letI := (g.residueFieldMap t).hom.toAlgebra
    (Module.finrank (S.residueField (g t)) (T.residueField t) : ℤ) ∣ m := by
  classical
  set φ := sq.isoPullback.hom
  set ρ := fiberRestrict (pullback.snd f g) p φ sq.isoPullback_hom_snd t
  have hρ : IsIso ρ := (isPullback_pullbackRestrict (pullback.snd f g) p φ
    sq.isoPullback_hom_snd (T.fromSpecResidueField t)).flip.isIso_fst_of_isIso
  have hρx (y) : ρ (inv ρ y) = y := Scheme.inv_hom_apply (asIso ρ) y
  have hρx' (y) : inv ρ (ρ y) = y := Scheme.hom_inv_apply (asIso ρ) y
  have hfac : restrictedFiberMap f p a g sq.w t =
      ρ ≫ restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t := by
    refine pullback.hom_ext (?_ : _ ≫ f.fiberι (g t) = _ ≫ f.fiberι (g t))
        (?_ : _ ≫ f.fiberToSpecResidueField (g t) = _ ≫ f.fiberToSpecResidueField (g t))
    · rw [Category.assoc, restrictedFiberMap_fiberι, restrictedFiberMap_fiberι,
        fiberRestrict_fiberι_assoc, sq.isoPullback_hom_fst]
    · rw [Category.assoc, restrictedFiberMap_comp_fiberToSpecResidueField,
        restrictedFiberMap_comp_fiberToSpecResidueField, ← Category.assoc,
        fiberRestrict_fiberToSpecResidueField]
  refine finrank_dvd_of_baseChangeFamily_eq_single f g t α (ρ Q) m ?_ ?_
  · have hc := residueDegree_comp ρ
      (restrictedFiberMap f (pullback.snd f g) (pullback.fst f g) g pullback.condition t) Q
    rw [← hfac, hQ, residueDegree_eq_one_of_residueFieldMap_isIso ρ Q inferInstance,
      mul_one] at hc
    exact hc.symm
  · intro y
    have hy := h (inv ρ y)
    change (fiberCycleRestrict (pullback.snd f g) p φ sq.isoPullback_hom_snd t 0
      (baseChangeFamily f g 0 α t) : AlgebraicCycle (p.fiber t) ℤ) (inv ρ y) = _ at hy
    rw [fiberCycleRestrict_apply, hρx] at hy
    rw [hy]
    congr 1
    exact propext ⟨fun h => by rw [← h, hρx], fun h => by rw [h, hρx']⟩

/-! ### Images of residue field maps -/

/-- The residue field of the spectrum of a field at its point is the field. -/
def specFieldResidueEquiv (L : Type u) [Field L] (t : Spec (.of L)) :
    L ≃+* (Spec (.of L)).residueField t :=
  haveI : t.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := L) t
  (RingEquiv.ofBijective (algebraMap L t.asIdeal.ResidueField)
    (bijective_algebraMap_residueField_of_field L t)).trans
    (Scheme.Spec.residueFieldIso (.of L) t).symm.commRingCatIsoToRingEquiv

/-- The residue field map of `Spec C ⟶ Spec L` at the point of `Spec L` hits the image of every
element of `C`. -/
theorem exists_residueFieldMap_specMap_eq {C L : Type u} [CommRing C] [Field L] (φ : C →+* L)
    (t : Spec (.of L)) (c : C) :
    ∃ z, (Spec.map (CommRingCat.ofHom φ)).residueFieldMap t z =
      specFieldResidueEquiv L t (φ c) := by
  have : t.asIdeal.IsPrime := PrimeSpectrum.isPrime (R := L) t
  refine ⟨(Scheme.Spec.residueFieldIso (.of C) (PrimeSpectrum.comap φ t)).inv
    (algebraMap C (PrimeSpectrum.comap φ t).asIdeal.ResidueField c), ?_⟩
  exact residueFieldMap_specMap_residueFieldIso_inv φ t c

/-- The image of the residue field map of a composite lies in the image of the residue field
map of its first factor. -/
theorem exists_residueFieldMap_eq_of_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (p : Y ⟶ Z) (x : X)
    (w : Z.residueField (p (g x))) :
    ∃ z, g.residueFieldMap x z = (g ≫ p).residueFieldMap x w :=
  ⟨_, residueFieldMap_comp_apply g p x w⟩

end Stacks.Chow

end
