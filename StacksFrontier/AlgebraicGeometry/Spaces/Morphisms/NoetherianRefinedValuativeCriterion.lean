module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Valuation.ValuationSubring
public import Mathlib.SetTheory.Cardinal.Subfield
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.RefinedProperness
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.SeparatedFiniteType
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineNoetherianEtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.SiteObjectBase
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleOpenOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSplitQuasiFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RefinedValuativeProperness
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedEtaleFamily
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Valuative.Properness

/-!
# The refined Noetherian valuative criterion of properness for algebraic spaces

Let `f : X ⟶ Y` and `h : U ⟶ X` be morphisms of algebraic spaces over a scheme `S`, with `Y`
locally Noetherian, `f` and `h` of finite type, `f` separated and the image of `|h|` dense in
`|X|`. Stacks 0CMD asserts that if every commutative solid diagram with `Spec K ⟶ U ⟶ X` along
the top and `Spec A ⟶ Y` along the bottom, for `A` a discrete valuation ring with fraction field
`K`, admits a dotted arrow `Spec A ⟶ X`, then `f` is proper.

## Main results

* `AlgebraicGeometry.Space.isProper_of_denseRange_of_exists_discreteLift`
  (`StacksFrontier.AlgebraicGeometry.Spaces.RefinedValuativeProperness`): **Stacks 0CMD**,
  registered here.
* `AlgebraicGeometry.Space.universallyClosed_of_exists_discreteLift_of_spec`: the case of a
  target represented by the spectrum of a Noetherian ring.
* `AlgebraicGeometry.ValuativeCommSq.hasLift_of_forall_cardinalMk_le`: for a morphism of
  schemes into an affine scheme, valuative diagrams with generic point in an affine scheme need
  only be checked over discrete valuation rings with fraction field of bounded cardinality.
* `IsDiscreteValuationRing.exists_subfield_valuationSubring`: the algebra behind the previous
  item, cutting a discrete valuation ring down to a small subfield of its fraction field.

## Implementation notes

The diagrams of the hypothesis are the valuative squares of the chapter
(`AlgebraicGeometry.Space.ValuativeSquare`), whose valuation rings have their spectra in the
chosen big fppf site; the factorization of the top edge through `h` is a morphism `g` from the
fraction field to `U` with `g ≫ h` the top edge.

The proof is the source's. Universal closedness is tested on a covering family of étale charts
of `Y` by spectra of Noetherian rings (Stacks 03IT, in the form of
`AlgebraicGeometry.Space.universallyClosed_of_etale_covering_family`), and the hypotheses pass
to each base change, density by Stacks 03IR and 03H4. Over the spectrum of a Noetherian ring,
Chow's lemma (Stacks 089J) gives a proper surjective `h_{X'} ⟶ X` from a scheme; an affine étale
chart `W` of `h_{X'} ×_X U` replaces the source's affine `U`, and the scheme-theoretic image `Z`
of `W ⟶ X'` replaces `X'`. Then `h_Z ⟶ X` is proper, and surjective since its image is closed
and contains the image of `h`. A valuative diagram for `Z ⟶ Spec A` with generic point in `W`
yields a valuative square for `f` with generic point in `U`; the dotted arrow it receives lifts
to `Z` by the valuative criterion for `h_Z ⟶ X` (Stacks 0A40). So `Z ⟶ Spec A` is proper by
the case of schemes (Stacks 0CM3), and `f` is universally closed by Stacks 08AJ.

The case of schemes quantifies over all discrete valuation rings, while the hypothesis here
only provides dotted arrows over those whose spectra lie in the site. The two are reconciled by
`AlgebraicGeometry.ValuativeCommSq.hasLift_of_forall_cardinalMk_le`: a diagram over a discrete
valuation ring `R` restricts to one over `R ∩ K₀`, for `K₀` the subfield of the fraction field
generated by the images of the two coordinate rings and a uniformizer, which is a discrete
valuation ring of bounded size, and a dotted arrow over it gives one over `R`.

## References

* [Stacks Project, Tag 0CMD](https://stacks.math.columbia.edu/tag/0CMD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Cardinal

universe u

namespace IsDiscreteValuationRing

/-- **A discrete valuation ring cut down to a small subfield.** Let `R` be a discrete valuation
ring with fraction field `K`, and let `α : A →+* R` and `φ : P →+* K` be ring homomorphisms. There
are a subfield `K₀` of `K` of cardinality at most `max (max #A #P) ℵ₀` containing the images of `α`
and `φ`, and a valuation subring `O₀` of `K₀` which is a discrete valuation ring, with a
homomorphism `O₀ →+* R` compatible with the inclusions into `K`, through which `α` factors.

`O₀` is `R ∩ K₀`, where `K₀` is generated by the two images and a uniformizer of `R`; a
uniformizer of `R` lying in `K₀` is a uniformizer of `O₀`, because the unit relating a nonzero
element of `O₀` to a power of it lies in `K₀`. -/
theorem exists_subfield_valuationSubring {R K : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {A P : Type u} [CommRing A] [CommRing P] (α : A →+* R) (φ : P →+* K) :
    ∃ (K₀ : Subfield K) (O₀ : ValuationSubring K₀) (_ : IsDiscreteValuationRing O₀)
      (i : O₀ →+* R) (α₀ : A →+* O₀) (φ₀ : P →+* K₀),
      #K₀ ≤ max (max #A #P) ℵ₀ ∧
      (algebraMap R K).comp i = K₀.subtype.comp (algebraMap O₀ K₀) ∧
      i.comp α₀ = α ∧ K₀.subtype.comp φ₀ = φ := by
  classical
  have hinj := IsFractionRing.injective R K
  -- The image of `R` in `K`, as a valuation subring.
  let Vo : ValuationSubring K := ValuationSubring.ofSubring (algebraMap R K).range (fun x => by
    rcases ValuationRing.isInteger_or_isInteger R x with h | h
    · obtain ⟨r, hr⟩ := h
      exact Or.inl ⟨r, hr⟩
    · obtain ⟨r, hr⟩ := h
      exact Or.inr ⟨r, hr⟩)
  let e : R ≃+* Vo := RingEquiv.ofBijective
    ((algebraMap R K).codRestrict Vo (fun r => ⟨r, rfl⟩))
    ⟨fun a b h => hinj (congrArg Subtype.val h), fun ⟨x, ⟨r, hr⟩⟩ => ⟨r, Subtype.ext hr⟩⟩
  have he : ∀ y : Vo, algebraMap R K (e.symm y) = y := fun y =>
    congrArg Subtype.val (e.apply_symm_apply y)
  have : IsDiscreteValuationRing Vo := RingEquivClass.isDiscreteValuationRing e
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible Vo
  let s : Set K := insert (ϖ : K) (Set.range (algebraMap R K ∘ α) ∪ Set.range φ)
  let K₀ : Subfield K := Subfield.closure s
  have hϖK₀ : (ϖ : K) ∈ K₀ := Subfield.subset_closure (Set.mem_insert _ _)
  let O₀ : ValuationSubring K₀ := Vo.comap K₀.subtype
  let ρ : O₀ →+* Vo :=
    (K₀.subtype.comp (algebraMap O₀ K₀)).codRestrict Vo (fun x => x.2)
  have hρ : ∀ x : O₀, ((ρ x : Vo) : K) = ((x : K₀) : K) := fun _ => rfl
  have hρinj : Function.Injective ρ := fun x y h =>
    Subtype.ext (Subtype.ext (by simpa only [hρ] using congrArg Subtype.val h))
  have hρunit : ∀ x : O₀, IsUnit (ρ x) → IsUnit x := by
    intro x hx
    obtain ⟨w, hw⟩ := hx.exists_right_inv
    have hwK : (w : K) = ((x : K₀) : K)⁻¹ := by
      have h1 : ((ρ x : Vo) : K) * (w : K) = 1 := by
        simpa using congrArg Subtype.val hw
      rw [hρ] at h1
      exact eq_inv_of_mul_eq_one_right h1
    let z : O₀ := ⟨(x : K₀)⁻¹, by
      show ((((x : K₀)⁻¹ : K₀)) : K) ∈ Vo
      rw [Subfield.coe_inv, ← hwK]
      exact w.2⟩
    refine isUnit_iff_exists_inv.mpr ⟨z, hρinj ?_⟩
    apply Subtype.ext
    rw [map_mul, map_one]
    show ((ρ x : Vo) : K) * ((ρ z : Vo) : K) = 1
    rw [hρ, hρ]
    show ((x : K₀) : K) * (((x : K₀)⁻¹ : K₀) : K) = 1
    rw [Subfield.coe_inv]
    refine mul_inv_cancel₀ ?_
    intro h0
    have : ρ x = 0 := Subtype.ext h0
    rw [this] at hx
    exact not_isUnit_zero hx
  let ϖ₀ : O₀ := ⟨⟨ϖ, hϖK₀⟩, ϖ.2⟩
  have hρϖ : ρ ϖ₀ = ϖ := rfl
  have hirr : Irreducible ϖ₀ := by
    refine ⟨fun h => hϖ.not_isUnit (hρϖ ▸ h.map ρ), fun a b hab => ?_⟩
    have := congrArg ρ hab
    rw [map_mul, hρϖ] at this
    exact (hϖ.isUnit_or_isUnit this).imp (hρunit a) (hρunit b)
  have hDVR : IsDiscreteValuationRing O₀ := by
    refine ofHasUnitMulPowIrreducibleFactorization ⟨ϖ₀, hirr, fun {x} hx => ?_⟩
    have hx' : ρ x ≠ 0 := fun h => hx (hρinj (h.trans (map_zero ρ).symm))
    obtain ⟨n, hn⟩ := associated_pow_irreducible hx' hϖ
    obtain ⟨u, hu⟩ := hn.symm
    have hϖ0 : (ϖ : K) ≠ 0 := fun h => hϖ.ne_zero (Subtype.ext h)
    have huK : ((u : Vo) : K) = ((x : K₀) : K) * ((ϖ : K) ^ n)⁻¹ := by
      have h1 : (ϖ : K) ^ n * ((u : Vo) : K) = ((x : K₀) : K) := by
        rw [← hρ x, ← hu]
        simp
      rw [← h1, mul_comm, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hϖ0), one_mul]
    let v : O₀ := ⟨⟨(u : Vo), by
      rw [huK]
      exact K₀.mul_mem (x : K₀).2 (K₀.inv_mem (K₀.pow_mem hϖK₀ n))⟩, (u : Vo).2⟩
    have hv : IsUnit v := hρunit v u.isUnit
    refine ⟨n, hv.unit, hρinj ?_⟩
    rw [IsUnit.unit_spec, map_mul, map_pow, hρϖ]
    exact hu
  let i : O₀ →+* R := e.symm.toRingHom.comp ρ
  have hi : (algebraMap R K).comp i = K₀.subtype.comp (algebraMap O₀ K₀) := by
    ext x
    exact he (ρ x)
  have hαK₀ : ∀ a, (algebraMap R K).comp α a ∈ K₀ := fun a =>
    Subfield.subset_closure (Set.mem_insert_of_mem _ (Or.inl ⟨a, rfl⟩))
  let α₁ : A →+* K₀ := ((algebraMap R K).comp α).codRestrict K₀ hαK₀
  let α₀ : A →+* O₀ := α₁.codRestrict O₀ (fun a => ⟨α a, rfl⟩)
  let φ₀ : P →+* K₀ := φ.codRestrict K₀ (fun p =>
    Subfield.subset_closure (Set.mem_insert_of_mem _ (Or.inr ⟨p, rfl⟩)))
  refine ⟨K₀, O₀, hDVR, i, α₀, φ₀, ?_, hi, ?_, rfl⟩
  · have hs : #s ≤ max (max #A #P) ℵ₀ := by
      have hM : ℵ₀ ≤ max (max #A #P) ℵ₀ := le_max_right _ _
      refine Cardinal.mk_insert_le.trans (Cardinal.add_le_of_le hM ?_
        (Cardinal.one_le_aleph0.trans hM))
      refine (Cardinal.mk_union_le _ _).trans (Cardinal.add_le_of_le hM ?_ ?_)
      · exact Cardinal.mk_range_le.trans ((le_max_left _ _).trans (le_max_left _ _))
      · exact Cardinal.mk_range_le.trans ((le_max_right _ _).trans (le_max_left _ _))
    exact (Subfield.cardinalMk_closure_le_max s).trans (max_le hs (le_max_right _ _))
  · ext a
    exact hinj (congrArg (fun g => g (α₀ a)) hi)

end IsDiscreteValuationRing

namespace AlgebraicGeometry

/-- Two morphisms from the spectrum of a ring `R` to an affine scheme agree as soon as they agree
after precomposition with the spectrum of an injective ring homomorphism `R →+* T`. -/
theorem Spec_map_cancel_of_injective {R T : Type u} [CommRing R] [CommRing T]
    {A : CommRingCat.{u}} (j : R →+* T) (hj : Function.Injective j)
    {u v : Spec (.of R) ⟶ Spec A}
    (h : Spec.map (CommRingCat.ofHom j) ≫ u = Spec.map (CommRingCat.ofHom j) ≫ v) : u = v := by
  rw [← Spec.map_preimage u, ← Spec.map_preimage v] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp] at h
  congr 1
  ext x
  exact hj (congrArg (fun g => g.hom x) (Spec.map_injective h))

/-- **Valuative diagrams over small discrete valuation rings suffice.** Let `τ : W ⟶ Z` and
`ζ : Z ⟶ Spec A` be morphisms of schemes with `W` affine. If every valuative diagram for `ζ` over
a discrete valuation ring whose fraction field has cardinality at most
`max (max #A #Γ(W, ⊤)) ℵ₀`, and whose generic point factors through `τ`, has a dotted arrow, then
so has every valuative diagram for `ζ` over a discrete valuation ring whose generic point factors
through `τ`.

The given diagram is restricted to the discrete valuation ring `R ∩ K₀`, for `K₀` the subfield of
the fraction field generated by the images of `A` and of `Γ(W, ⊤)` and by a uniformizer; a dotted
arrow over `R ∩ K₀` composed with `Spec R ⟶ Spec (R ∩ K₀)` is a dotted arrow for the given
diagram. -/
theorem ValuativeCommSq.hasLift_of_forall_cardinalMk_le {W Z : Scheme.{u}} [IsAffine W]
    {A : CommRingCat.{u}} (τ : W ⟶ Z) (ζ : Z ⟶ Spec A)
    (h : ∀ (D : ValuativeCommSq ζ), IsDiscreteValuationRing D.R →
      #D.K ≤ max (max #A #Γ(W, ⊤)) ℵ₀ →
        ∀ g : Spec (.of D.K) ⟶ W, g ≫ τ = D.i₁ → D.commSq.HasLift)
    (D : ValuativeCommSq ζ) (hD : IsDiscreteValuationRing D.R) (g : Spec (.of D.K) ⟶ W)
    (hg : g ≫ τ = D.i₁) : D.commSq.HasLift := by
  classical
  let φ : Γ(W, ⊤) →+* D.K := (Spec.preimage (g ≫ W.isoSpec.hom)).hom
  let α : A →+* D.R := (Spec.preimage D.i₂).hom
  obtain ⟨K₀, O₀, hO₀, i, α₀, φ₀, hcard, hi, hα, hφ⟩ :=
    IsDiscreteValuationRing.exists_subfield_valuationSubring α φ
  have hgφ : Spec.map (CommRingCat.ofHom φ) = g ≫ W.isoSpec.hom := by
    simp only [φ, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hαi : Spec.map (CommRingCat.ofHom α) = D.i₂ := by
    simp only [α, CommRingCat.ofHom_hom, Spec.map_preimage]
  let g₀ : Spec (.of K₀) ⟶ W := Spec.map (CommRingCat.ofHom φ₀) ≫ W.isoSpec.inv
  have hjg : Spec.map (CommRingCat.ofHom K₀.subtype) ≫ g₀ = g := by
    simp only [g₀]
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hφ, hgφ, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hbottom : Spec.map (CommRingCat.ofHom K₀.subtype) ≫
      Spec.map (CommRingCat.ofHom (algebraMap O₀ K₀)) ≫ Spec.map (CommRingCat.ofHom α₀) =
      Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ := by
    rw [← hαi, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, ← hi,
      RingHom.comp_assoc, hα]
  have hw : (g₀ ≫ τ) ≫ ζ = Spec.map (CommRingCat.ofHom (algebraMap O₀ K₀)) ≫
      Spec.map (CommRingCat.ofHom α₀) := by
    refine Spec_map_cancel_of_injective K₀.subtype Subtype.val_injective ?_
    rw [hbottom, ← D.commSq.w, ← hg, ← hjg]
    simp only [Category.assoc]
  let D₀ : ValuativeCommSq ζ :=
    { R := O₀, K := K₀, i₁ := g₀ ≫ τ, i₂ := Spec.map (CommRingCat.ofHom α₀), commSq := ⟨hw⟩ }
  obtain ⟨⟨l₀⟩⟩ := h D₀ hO₀ hcard g₀ rfl
  refine ⟨⟨{ l := Spec.map (CommRingCat.ofHom i) ≫ l₀.l, fac_left := ?_, fac_right := ?_ }⟩⟩
  · have hl := l₀.fac_left
    change Spec.map (CommRingCat.ofHom (algebraMap O₀ K₀)) ≫ l₀.l = g₀ ≫ τ at hl
    rw [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hi, CommRingCat.ofHom_comp,
      Spec.map_comp, Category.assoc, hl, ← Category.assoc, hjg, hg]
  · have hr := l₀.fac_right
    change l₀.l ≫ ζ = Spec.map (CommRingCat.ofHom α₀) at hr
    rw [Category.assoc, hr, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hα, hαi]

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The refined criterion over the spectrum of a Noetherian ring.** Let `f : X ⟶ h_T` and
`h : U ⟶ X` be morphisms of algebraic spaces over `S`, where `T` is the spectrum of a Noetherian
ring `A` regarded as an object of the site, with `f` separated and of finite type, `h` of finite
type and the image of `|h|` dense in `|X|`. If every valuative square for `f` over a discrete
valuation ring whose generic point factors through `h` has a dotted arrow, then `f` is universally
closed.

This is the case of an affine base in the proof of Stacks 0CMD. By Chow's lemma (Stacks 089J)
there is a proper surjective morphism `p : h_{X'} ⟶ X` from a scheme `X'` H-quasi-projective
over `Spec A`. An affine étale chart `W` of `h_{X'} ×_X U` maps to `X'`, and `p` restricted to
the scheme-theoretic image `Z` of `W ⟶ X'` is still proper and surjective, its image being
closed and containing the image of `h`. The morphism `Z ⟶ Spec A` is separated and of finite
type, and `W ⟶ Z` is of finite type with dense image; a valuative diagram for `Z ⟶ Spec A` over
a small discrete valuation ring with generic point in `W` gives a valuative square for `f`
with generic point in `U`, whose dotted arrow lifts to `Z` by the valuative criterion for the
proper morphism `h_Z ⟶ X` (Stacks 0A40). So `Z ⟶ Spec A` is proper by the case of schemes
(Stacks 0CM3), and `f` is universally closed by Stacks 08AJ. -/
@[ega "II 7.3.8" "(b) ⇒ (a)"]
theorem universallyClosed_of_exists_discreteLift_of_spec (A : CommRingCat.{u})
    [IsNoetherianRing A] (hA : B.Contains (Spec A)) (a : Spec A ⟶ S)
    {U X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B S hS U) (hX : IsAlgebraicSpace B S hS X)
    (h : U ⟶ X) (f : X ⟶ yoneda.obj (siteObject B S hS hA a))
    (hf : IsFiniteType B S hS f) (hsep : IsSeparated B S hS f) (hh : IsFiniteType B S hS h)
    (hdense : letI := pointTopology B S hS X
      DenseRange (pointsMap B S hS U h))
    (hlift : ∀ (q : ValuativeSquare f), IsDiscreteValuationRing q.R →
      ∀ (g : yoneda.obj (siteObject B S hS q.field_mem
        (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) ⟶ U),
      g ≫ h = q.generic → Nonempty q.Lift) :
    UniversallyClosed B S hS f := by
  classical
  let G := BigFppfOver.toScheme B S hS
  let T := siteObject B S hS hA a
  have hT := isAlgebraicSpace_yoneda B S hS T
  -- Chow's lemma.
  obtain ⟨X', ψ, p, hp, hpsurj, hpf, hψ⟩ :=
    exists_chowSchemeCover_over_spec B S hS A hA a hX f hsep hf
  have hX' := isAlgebraicSpace_yoneda B S hS X'
  have : _root_.AlgebraicGeometry.IsSeparated (G.map ψ) := hψ.isSeparated
  have : LocallyOfFiniteType (G.map ψ) := hψ.locallyOfFiniteType
  have : QuasiCompact (G.map ψ) := hψ.quasiCompact
  have : CompactSpace (G.obj T) := (inferInstance : CompactSpace (Spec A))
  have : QuasiSeparatedSpace (G.obj T) := (inferInstance : QuasiSeparatedSpace (Spec A))
  have : CompactSpace (G.obj X') := QuasiCompact.compactSpace_of_compactSpace (G.map ψ)
  -- An affine étale chart of `h_{X'} ×_X U`.
  have hU' := isAlgebraicSpace_pullback B S hS p h hX' hU hX
  have hqc : IsQuasiCompactSpace B S hS (pullback p h) :=
    hh.2 (yoneda.obj X') hX' (isQuasiCompact_yoneda_of_compact B S hS X' inferInstance) p
  obtain ⟨W, b, hWaff, hbsurj, hbet⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS _ hU').mp hqc
  have : IsAffine (G.obj W) := hWaff
  let κ : W ⟶ X' := yoneda.preimage (b ≫ pullback.fst p h)
  have hκ : yoneda.map κ = b ≫ pullback.fst p h := yoneda.map_preimage _
  have hfst : IsFiniteType B S hS (pullback.fst p h) :=
    IsFiniteType.of_isPullback B S hS (IsPullback.of_hasPullback p h) hU hX hh
  have : LocallyOfFiniteType (G.map κ) :=
    hfst.1 W X' b (𝟙 _) κ (presheaf_etale_of_isEtale B S hS hbet)
      (presheaf_id_of_iso B S hS _ (fun {_ _} g hg => by
        have := hg
        have : IsIso (G.map g) := inferInstance
        exact inferInstanceAs (Etale (G.map g))) X')
      (by rw [Category.comp_id, hκ])
  have : QuasiCompact (G.map κ ≫ G.map ψ) :=
    (quasiCompact_iff_compactSpace (G.map κ ≫ G.map ψ)).mpr inferInstance
  have : QuasiCompact (G.map κ) := QuasiCompact.of_comp (G.map κ) (G.map ψ)
  -- The scheme-theoretic image `Z` of `W ⟶ X'`.
  let κs := G.map κ
  have hZ : B.Contains κs.image :=
    Scheme.size_lt_of_isClosedImmersion κs.imageι X'.left.2
  let ιsite : B.obj hZ ⟶ X'.left := ObjectProperty.homMk κs.imageι
  let Z : BigFppfOver B S hS := Over.mk (ιsite ≫ X'.hom)
  let ι : Z ⟶ X' := Over.homMk ιsite
  have hτsite : (ObjectProperty.homMk κs.toImage : W.left ⟶ B.obj hZ) ≫ ιsite = κ.left :=
    ObjectProperty.hom_ext _ κs.toImage_imageι
  let τ : W ⟶ Z := Over.homMk (ObjectProperty.homMk κs.toImage : W.left ⟶ B.obj hZ) (by
    show _ ≫ ιsite ≫ X'.hom = W.hom
    rw [← Category.assoc, hτsite]
    exact Over.w κ)
  have hτι : τ ≫ ι = κ := Over.OverMorphism.ext hτsite
  have hGτ : G.map τ = κs.toImage := rfl
  have hGι : G.map ι = κs.imageι := rfl
  have hZalg := isAlgebraicSpace_yoneda B S hS Z
  -- `h_Z ⟶ X` is proper.
  let p' : yoneda.obj Z ⟶ X := yoneda.map ι ≫ p
  have hιprop : IsProper B S hS (yoneda.map ι) :=
    isProper_yoneda_map B S hS ι (by rw [hGι]; infer_instance)
  have hp' : IsProper B S hS p' := isProper_comp' B S hS (yoneda.map ι) p hX' hX hιprop hp
  have hτp' : yoneda.map τ ≫ p' = b ≫ pullback.snd p h ≫ h := by
    simp only [p', ← Category.assoc, ← Functor.map_comp, hτι, hκ]
    simp only [Category.assoc, pullback.condition]
  -- `h_Z ⟶ X` is surjective: its image is closed and contains the image of `h`.
  have hp'surj : IsSurjective B S hS p' := by
    let := pointTopology B S hS X
    let := pointTopology B S hS (yoneda.obj Z)
    have hclosed : IsClosed (Set.range (pointsMap B S hS (yoneda.obj Z) p')) :=
      (isClosed_of_universallyClosed B S hS hX p' hp'.2.2).isClosed_range
    have hsub : Set.range (pointsMap B S hS U h) ⊆
        Set.range (pointsMap B S hS (yoneda.obj Z) p') := by
      rintro _ ⟨x, rfl⟩
      obtain ⟨x', hx'⟩ := hpsurj (pointsMap B S hS U h x)
      obtain ⟨u', -, hu'⟩ := exists_points_of_isPullback B S hS
        (IsPullback.of_hasPullback p h) x' x hx'
      obtain ⟨w, hw⟩ := (surjective_iff_surjective_pointsMap B S hS _ hU' W b).mp hbsurj u'
      refine ⟨pointsMap B S hS (yoneda.obj W) (yoneda.map τ) w, ?_⟩
      rw [← pointsMap_comp_apply, hτp', pointsMap_comp_apply, pointsMap_comp_apply, hw, hu']
    intro x
    exact closure_minimal hsub hclosed (hdense x)
  have he : p' ≫ f = yoneda.map (ι ≫ ψ) := by
    simp only [p', Category.assoc, hpf, Functor.map_comp]
  -- The scheme case.
  have : IsLocallyNoetherian (Spec A) := inferInstance
  let ζ : κs.image ⟶ Spec A := κs.imageι ≫ G.map ψ
  have : LocallyOfFiniteType (κs.toImage ≫ κs.imageι) := by
    rw [Scheme.Hom.toImage_imageι]
    infer_instance
  have : LocallyOfFiniteType κs.toImage := locallyOfFiniteType_of_comp κs.toImage κs.imageι
  have hdenseτ : DenseRange κs.toImage := IsDominant.denseRange
  have hsmall : ∀ (D : ValuativeCommSq ζ), IsDiscreteValuationRing D.R →
      #D.K ≤ max (max #A #Γ(G.obj W, ⊤)) ℵ₀ →
        ∀ g : Spec (.of D.K) ⟶ G.obj W, g ≫ κs.toImage = D.i₁ → D.commSq.HasLift := by
    intro D hD hcard g hg
    -- The discrete valuation ring and its fraction field are small enough for the site.
    have hAcard : #A < B.cutoff := by
      have h1 : (Spec A).size < B.cutoff := hA
      rw [Scheme.size_Spec] at h1
      exact (le_max_right _ _).trans_lt h1
    have hWcard : #Γ(G.obj W, ⊤) < B.cutoff := by
      have h1 : (G.obj W).size < B.cutoff := W.left.2
      rw [Scheme.size_of_isAffine] at h1
      exact (le_max_right _ _).trans_lt h1
    have hM : max (max #A #Γ(G.obj W, ⊤)) ℵ₀ < B.cutoff :=
      max_lt (max_lt hAcard hWcard) B.aleph0_lt_cutoff
    have hKmem : B.Contains (Spec (.of D.K)) := by
      show (Spec (.of D.K)).size < B.cutoff
      rw [Scheme.size_Spec]
      exact max_lt B.aleph0_lt_cutoff (hcard.trans_lt hM)
    have hRmem : B.Contains (Spec (.of D.R)) :=
      Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hKmem
        ((Cardinal.mk_le_of_injective (IsFractionRing.injective D.R D.K)).trans
          (le_max_right _ _))
    -- The diagram as a valuative square for `f` with generic point in `U`.
    let base : Spec (.of D.R) ⟶ S := D.i₂ ≫ a
    let Kbase : Spec (.of D.K) ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ base
    let i₂site : siteObject B S hS hRmem base ⟶ T :=
      Over.homMk (ObjectProperty.homMk D.i₂ : B.obj hRmem ⟶ B.obj hA) rfl
    let fracHom : siteObject B S hS hKmem Kbase ⟶ siteObject B S hS hRmem base :=
      Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (algebraMap D.R D.K))) :
        B.obj hKmem ⟶ B.obj hRmem)
    have hgD : g ≫ G.map κ ≫ G.map ψ =
        Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ := by
      have h1 : g ≫ G.map κ ≫ G.map ψ = (g ≫ κs.toImage) ≫ ζ := by
        simp only [ζ, Category.assoc, Scheme.Hom.toImage_imageι_assoc]
        rfl
      rw [h1, hg]
      exact D.commSq.w
    have hW : W.hom.hom = G.map κ ≫ G.map ψ ≫ a := by
      rw [← Over.w κ, ← Over.w ψ]
      rfl
    let gsite : siteObject B S hS hKmem Kbase ⟶ W :=
      Over.homMk (ObjectProperty.homMk g : B.obj hKmem ⟶ W.left) (by
        apply ObjectProperty.hom_ext
        show g ≫ W.hom.hom = Spec.map (CommRingCat.ofHom (algebraMap D.R D.K)) ≫ D.i₂ ≫ a
        rw [hW]
        simpa only [Category.assoc] using congrArg (· ≫ a) hgD)
    have hsite : gsite ≫ κ ≫ ψ = fracHom ≫ i₂site :=
      Over.OverMorphism.ext (ObjectProperty.hom_ext _ hgD)
    let gU : yoneda.obj (siteObject B S hS hKmem Kbase) ⟶ U :=
      yoneda.map gsite ≫ b ≫ pullback.snd p h
    let q : ValuativeSquare f :=
      { R := D.R, K := D.K, ring_mem := hRmem, field_mem := hKmem, base := base
        generic := gU ≫ h
        special := yoneda.map i₂site
        comm := by
          have e1 : yoneda.map fracHom ≫ yoneda.map i₂site = yoneda.map (gsite ≫ κ ≫ ψ) := by
            rw [← Functor.map_comp, hsite]
          refine Eq.trans ?_ e1.symm
          simp only [gU, Functor.map_comp, Category.assoc, hκ, ← hpf, pullback.condition_assoc] }
    obtain ⟨l⟩ := hlift q hD gU rfl
    -- Its dotted arrow lifts to `Z`, by the valuative criterion for the proper `h_Z ⟶ X`.
    let q' : ValuativeSquare p' :=
      { R := D.R, K := D.K, ring_mem := hRmem, field_mem := hKmem, base := base
        generic := yoneda.map (gsite ≫ τ)
        special := l.map
        comm := by
          refine Eq.trans ?_ l.generic_comm.symm
          rw [Functor.map_comp, Category.assoc, hτp']
          simp only [q, gU, Category.assoc] }
    obtain ⟨⟨m⟩, -⟩ := (isProper_iff_forall_unique_lift_of_isFiniteType_of_isQuasiSeparated
      hZalg hX p' hp'.2.1 (isQuasiSeparated_of_isSeparated B S hS hp'.1)).mp hp' q'
    let μ : siteObject B S hS hRmem base ⟶ Z := yoneda.preimage m.map
    have hμ : yoneda.map μ = m.map := yoneda.map_preimage _
    have h1 : fracHom ≫ μ = gsite ≫ τ := yoneda.map_injective (by
      rw [Functor.map_comp, hμ]
      exact m.generic_comm)
    have h2 : μ ≫ ι ≫ ψ = i₂site := yoneda.map_injective (by
      rw [Functor.map_comp, hμ, ← he, ← Category.assoc, m.special_comm, l.special_comm])
    refine ⟨⟨{ l := G.map μ, fac_left := ?_, fac_right := ?_ }⟩⟩
    · have h3 := congrArg G.map h1
      rw [G.map_comp, G.map_comp] at h3
      exact h3.trans hg
    · have h3 := congrArg G.map h2
      rw [G.map_comp, G.map_comp] at h3
      exact h3
  have hP : _root_.AlgebraicGeometry.IsProper ζ :=
    _root_.AlgebraicGeometry.isProper_of_denseRange_of_exists_discreteLift κs.toImage ζ hdenseτ
      (fun D hD g hg => ValuativeCommSq.hasLift_of_forall_cardinalMk_le κs.toImage ζ hsmall
        D hD g hg)
  have huc : UniversallyClosed B S hS (p' ≫ f) := by
    rw [he]
    refine universallyClosed_yoneda_map B S hS (ι ≫ ψ) ?_
    rw [G.map_comp, hGι]
    exact hP.toUniversallyClosed
  exact universallyClosed_of_isSurjective_comp B S hS hZalg hX hT p' f huc hp'surj

end AlgebraicGeometry.Space

add_to_stacks 0CMD "Let `f : X ⟶ Y` and `h : U ⟶ X` be morphisms of algebraic spaces over `S`, with
  `Y` locally Noetherian, `f` and `h` of finite type, `f` separated and the image of
  `|h| : |U| → |X|` dense in `|X|`. If every commutative valuative diagram for `f` over a discrete
  valuation ring whose generic arrow factors through `h` has a dotted arrow, then `f` is proper."
  AlgebraicGeometry.Space.isProper_of_denseRange_of_exists_discreteLift
