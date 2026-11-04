module

public import StacksFrontier.AlgebraicGeometry.Divisors.RegularImmersion.ContainingDivisorFibre
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.ResidueFieldClosedImmersion

/-!
# Lifting a divisor of a fibre to a finite relative effective Cartier divisor

Let `π : N ⟶ S` be flat and locally of finite presentation, `w ∈ N`, and `Z ⊆ N` a
closed subscheme through `w` whose fibre over `π w` is an effective Cartier divisor near `w`, with
`w` isolated in `Z ∩ π⁻¹(π w)`. After an elementary étale base change `U ⟶ S` there is an open
`O'` of `N ×_S U` carrying a relative effective Cartier divisor `D` over `U` which is finite over
`U`, has the same fibre as `Z` over the distinguished point of `U`, and meets that fibre in exactly
one point, lying over `w` with the same residue field.

This is the first step of the proof that a family of curves is a scheme étale locally on the
base (Stacks 0E6F): it lifts a divisor of the closed fibre, read on an elementary étale chart of
the total space, to the base.

## Main results

* `AlgebraicGeometry.C1590Private.exists_elementary_finite_relativeEffectiveCartier`.

## Proof

Stacks 062Y (`Stacks.Divisors.exists_isRelativeEffectiveCartierDivisor_containing`) gives a
relative effective Cartier divisor `D₁` on an open `O ∋ w` with the fibre of `Z`. Its point over
`w` is isolated in its fibre, so Stacks 02LK (`Stacks.Flatness.exists_etaleNeighborhood_finiteAt`)
gives an elementary étale neighbourhood `U` and an open `V` of `D₁ ×_S U` finite over `U`. As
`D₁ ×_S U ⟶ U` is separated, `V` is also closed, and `O'` is the complement in `O ×_S U` of the
rest of `D₁ ×_S U`.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 062Y](https://stacks.math.columbia.edu/tag/062Y)
* [Stacks Project, Tag 02LK](https://stacks.math.columbia.edu/tag/02LK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.C1590Private

universe u

open Stacks.Divisors

section

variable {N S : Scheme.{u}} (π : N ⟶ S) [Flat π] [LocallyOfFinitePresentation π]

/-- The point of the subscheme of a divisor containing a point of its support. -/
theorem exists_subschemeι_eq {X : Scheme.{u}} (I : X.IdealSheafData) {x : X}
    (hx : x ∈ I.support) : ∃ y : I.subscheme, I.subschemeι y = x := by
  have : x ∈ Set.range I.subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι]; exact hx
  exact this

/-- A point of a divisor on an open `O` lying over `w` maps to `f w`. -/
private theorem subschemeι_comp_apply_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (w : X) (O : X.Opens)
    (hwO : w ∈ O) (D : O.toScheme.IdealSheafData) (w₁ : D.subscheme)
    (hw₁ : D.subschemeι w₁ = ⟨w, hwO⟩) : (D.subschemeι ≫ O.ι ≫ f) w₁ = f w := by
  simp only [Scheme.Hom.comp_apply, hw₁]
  rfl

omit [Flat π] [LocallyOfFinitePresentation π] in
/-- **Isolatedness passes to a containing divisor with the same fibre.** If `D` is an ideal sheaf
on an open `O` of `N` containing `Z` (that is, `D ≤ Z|_O`) with the same fibre over `π w`, and `w`
is isolated in `Z ∩ π⁻¹(π w)`, then the point of `D` over `w` is isolated in its fibre. -/
theorem isIsolatedPoint_asFiber_of_fibre_eq (Z : N.IdealSheafData) (w : N) (O : N.Opens)
    (hwO : w ∈ O) (D : O.toScheme.IdealSheafData)
    (hfibeq : (Z.comap O.ι).comap ((O.ι ≫ π).fiberι (π w)) =
      D.comap ((O.ι ≫ π).fiberι (π w)))
    (hisol : ∃ O₀ : N.Opens, w ∈ O₀ ∧ ∀ y ∈ O₀, y ∈ Z.support → π y = π w → y = w)
    (w₁ : D.subscheme) (hw₁ : D.subschemeι w₁ = ⟨w, hwO⟩) :
    IsIsolatedPoint ((D.subschemeι ≫ O.ι ≫ π).asFiber w₁) := by
  obtain ⟨O₀, hwO₀, hO₀⟩ := hisol
  set g := D.subschemeι ≫ O.ι ≫ π with hg
  set F := (O.ι ≫ π).fiberι (π w) with hF
  have hgw : g w₁ = π w := subschemeι_comp_apply_eq π w O hwO D w₁ hw₁
  -- the points of `D` over `π w` near `w₁` are `w₁`
  have key : ∀ y : D.subscheme, g y = g w₁ → O.ι (D.subschemeι y) ∈ O₀ → y = w₁ := by
    intro y hy hyO₀
    have hy' : (O.ι ≫ π) (D.subschemeι y) = π w := by
      rw [← hgw, ← hy]; rfl
    have hmem : D.subschemeι y ∈ Set.range F := by
      rw [hF, Scheme.Hom.range_fiberι]; exact hy'
    obtain ⟨z, hz⟩ := hmem
    have hzD : z ∈ (D.comap F).support := by
      rw [Scheme.IdealSheafData.support_comap]
      change F z ∈ (D.support : Set _)
      rw [hz, ← Scheme.IdealSheafData.range_subschemeι]; exact ⟨y, rfl⟩
    rw [← hfibeq, Scheme.IdealSheafData.support_comap] at hzD
    change F z ∈ ((Z.comap O.ι).support : Set _) at hzD
    rw [Scheme.IdealSheafData.support_comap, hz] at hzD
    have hw' := hO₀ _ hyO₀ hzD (by simpa using hy')
    have h1 : D.subschemeι y = D.subschemeι w₁ := by
      rw [hw₁]; exact Subtype.ext hw'
    exact D.subschemeι.isEmbedding.injective h1
  rw [isIsolatedPoint_iff]
  have hopen : IsOpen ((g.fiberι (g w₁)) ⁻¹' ((D.subschemeι ≫ O.ι) ⁻¹' (O₀ : Set N))) :=
    (O₀.isOpen.preimage (D.subschemeι ≫ O.ι).continuous).preimage (g.fiberι _).continuous
  convert hopen using 1
  ext z
  simp only [Set.mem_singleton_iff, Set.mem_preimage]
  refine ⟨?_, fun hz => ?_⟩
  · rintro rfl
    rw [Scheme.Hom.fiberι_asFiber]
    simpa [hw₁] using hwO₀
  · apply (g.fiberHomeo (g w₁)).injective
    apply Subtype.ext
    simp only [Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberι_asFiber]
    refine key _ ?_ hz
    have := (g.fiberHomeo (g w₁) z).2
    simpa [Scheme.Hom.fiberHomeo_apply] using this

/-- **A finite neighbourhood over an affine elementary étale neighbourhood.** Restricting the
neighbourhood of Stacks 02LK to an affine open around its distinguished point keeps it
elementary and keeps the finite open. -/
theorem exists_affine_finiteNeighborhoodAt {X : Scheme.{u}} (f : X ⟶ S) (x : X)
    (F : Stacks.Flatness.FiniteNeighborhoodAt f x) :
    ∃ (U : EtaleNeighborhood S (f x)) (_ : U.IsElementary) (_ : IsAffine U.scheme)
      (V : (pullback f U.toBase).Opens), Stacks.Flatness.IsFiniteNeighborhoodAt f x U V := by
  obtain ⟨U, hU, V, hV⟩ := F
  obtain ⟨A, hA, hpA, -⟩ : ∃ A : U.scheme.Opens, IsAffineOpen A ∧ U.point ∈ A ∧ A ≤ ⊤ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp U.scheme.isBasis_affineOpens
    (show U.point ∈ (⊤ : U.scheme.Opens) from trivial)
  let U' : EtaleNeighborhood U.scheme U.point :=
    { scheme := A.toScheme
      point := ⟨U.point, hpA⟩
      toBase := A.ι
      map_point := rfl }
  have hU' : U'.IsElementary := by
    rw [EtaleNeighborhood.isElementary_iff]
    change IsIso (A.ι.residueFieldMap _)
    infer_instance
  have : IsAffine U'.scheme := hA
  exact ⟨U.comp U', hU.comp hU', this, _,
    Stacks.Flatness.isFiniteNeighborhoodAt_baseChange f x U V hV U' hU'⟩

/-- **The finite lift.** Let `π : N ⟶ S` be flat and locally of finite presentation,
`w ∈ N`, and `Z ⊆ N` a closed subscheme through `w` whose fibre over `π w` is an effective
Cartier divisor near `w`, with `w` isolated in `Z ∩ π⁻¹(π w)`. Then there are an elementary
étale neighbourhood `U` of `π w` with affine underlying scheme, a scheme `O'` with an open
immersion into `N ×_S U`, given by `a : O' ⟶ N` and `b : O' ⟶ U`, and a relative effective Cartier
divisor `D` on `O'` over `U`, finite over `U`, with the fibre of `Z` over the distinguished point
`u` of `U`, and with exactly one point over `u`; that point lies over `w`, with the residue field
of `w`. -/
theorem exists_elementary_finite_relativeEffectiveCartier (w : N)
    (Z : N.IdealSheafData) (hw : w ∈ Z.support)
    (hfib : ∃ O : (π.fiber (π w)).Opens, π.asFiber w ∈ O ∧
      IsEffectiveCartierDivisor ((Z.comap (π.fiberι (π w))).comap O.ι))
    (hisol : ∃ O₀ : N.Opens, w ∈ O₀ ∧ ∀ y ∈ O₀, y ∈ Z.support → π y = π w → y = w) :
    ∃ (U : EtaleNeighborhood S (π w)) (_ : U.IsElementary) (_ : IsAffine U.scheme)
      (O' : Scheme.{u}) (a : O' ⟶ N)
      (b : O' ⟶ U.scheme) (h : a ≫ π = b ≫ U.toBase) (_ : IsOpenImmersion (pullback.lift a b h))
      (D : O'.IdealSheafData),
      IsRelativeEffectiveCartierDivisor b D ∧ IsFinite (D.subschemeι ≫ b) ∧
      (Z.comap a).comap (b.fiberι U.point) = D.comap (b.fiberι U.point) ∧
      (∃ d : D.subscheme, b (D.subschemeι d) = U.point ∧ a (D.subschemeι d) = w ∧
        IsIso (a.residueFieldMap (D.subschemeι d))) ∧
      ∀ d d' : D.subscheme, b (D.subschemeι d) = U.point → b (D.subschemeι d') = U.point →
        d = d' := by
  classical
  obtain ⟨O, hwO, D₁, hrel, hle, hfibeq⟩ :=
    exists_isRelativeEffectiveCartierDivisor_containing π Z w (by simpa using hw) hfib
  have hwD₁ : (⟨w, hwO⟩ : O.toScheme) ∈ D₁.support := by
    have h1 : (⟨w, hwO⟩ : O.toScheme) ∈ (Z.comap O.ι).support := by
      rw [Scheme.IdealSheafData.support_comap]; exact hw
    exact Scheme.IdealSheafData.support_antitone hle h1
  obtain ⟨w₁, hw₁⟩ := exists_subschemeι_eq D₁ hwD₁
  set g := D₁.subschemeι ≫ O.ι ≫ π with hg
  have hgw : g w₁ = π w := subschemeι_comp_apply_eq π w O hwO D₁ w₁ hw₁
  have hiso := isIsolatedPoint_asFiber_of_fibre_eq π Z w O hwO D₁ hfibeq hisol w₁ hw₁
  have : LocallyOfFiniteType g := by rw [hg]; infer_instance
  rw [show π w = g w₁ from hgw.symm]
  obtain ⟨U₀, hel, hUaff, V, hspec⟩ := exists_affine_finiteNeighborhoodAt g w₁
    (Stacks.Flatness.exists_etaleNeighborhood_finiteAt g w₁ hiso).some
  set f := O.ι ≫ π with hf
  -- the base change of `D₁` to `U₀`, and its comparison with `D₁ ×_S U₀`
  set D₁Q := D₁.comap (pullback.fst f U₀.toBase) with hD₁Q
  let e : D₁Q.subscheme ≅ pullback g U₀.toBase :=
    D₁.comapIso _ ≪≫ pullbackSymmetry _ _ ≪≫
      pullbackRightPullbackFstIso f U₀.toBase D₁.subschemeι
  have hgf : g = D₁.subschemeι ≫ f := rfl
  have he_snd : e.hom ≫ pullback.snd g U₀.toBase =
      D₁Q.subschemeι ≫ pullback.snd f U₀.toBase := by
    rw [show pullback.snd g U₀.toBase = pullback.snd (D₁.subschemeι ≫ f) U₀.toBase from rfl]
    simp only [e, Iso.trans_hom, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
      pullbackSymmetry_hom_comp_snd_assoc, D₁Q]
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have he_fst : e.hom ≫ pullback.fst g U₀.toBase ≫ D₁.subschemeι =
      D₁Q.subschemeι ≫ pullback.fst f U₀.toBase := by
    rw [show pullback.fst g U₀.toBase = pullback.fst (D₁.subschemeι ≫ f) U₀.toBase from rfl]
    simp only [e, Iso.trans_hom, Category.assoc, pullbackRightPullbackFstIso_hom_fst_assoc,
      pullbackSymmetry_hom_comp_fst_assoc, D₁Q]
    rw [← pullback.condition, ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have : Flat g := hrel.2
  have hflatQ : Flat (D₁Q.subschemeι ≫ pullback.snd f U₀.toBase) := by
    rw [← he_snd]; infer_instance
  have hrelQ : IsRelativeEffectiveCartierDivisor (pullback.snd f U₀.toBase) D₁Q :=
    ⟨isPullbackDefined_of_flat _ _ hrel.1, hflatQ⟩
  -- the open `W` of `D₁Q` corresponding to `V`, finite and closed
  set W := e.hom ⁻¹ᵁ V with hW
  have hWfin : IsFinite (W.ι ≫ D₁Q.subschemeι ≫ pullback.snd f U₀.toBase) := by
    have hfinV : IsFinite (V.ι ≫ pullback.snd g U₀.toBase) := hspec.1
    have : W.ι ≫ D₁Q.subschemeι ≫ pullback.snd f U₀.toBase =
        (e.hom ∣_ V) ≫ V.ι ≫ pullback.snd g U₀.toBase := by
      rw [← he_snd, morphismRestrict_ι_assoc]
    rw [this]; infer_instance
  -- the open `O'` of `Q` meeting `D₁Q` in `W`
  let C : Set ↥(pullback f U₀.toBase) := ⇑D₁Q.subschemeι '' (W : Set D₁Q.subscheme)ᶜ
  let O' : (pullback f U₀.toBase).Opens :=
    ⟨Cᶜ, (D₁Q.subschemeι.isClosedEmbedding.isClosedMap _ W.isOpen.isClosed_compl).isOpen_compl⟩
  have hO'W : D₁Q.subschemeι ⁻¹ᵁ O' = W := by
    ext x
    simp only [Scheme.Hom.mem_preimage, O', TopologicalSpace.Opens.mem_mk, Set.mem_compl_iff, C,
      Set.mem_image, not_exists, not_and, SetLike.mem_coe]
    exact ⟨fun hx => of_not_not fun hxW => hx x hxW rfl,
      fun hx y hy hyx => hy (D₁Q.subschemeι.isEmbedding.injective hyx ▸ hx)⟩
  set a : O'.toScheme ⟶ N := O'.ι ≫ pullback.fst f U₀.toBase ≫ O.ι with ha
  set b : O'.toScheme ⟶ U₀.scheme := O'.ι ≫ pullback.snd f U₀.toBase with hb
  have hab : a ≫ π = b ≫ U₀.toBase := by
    simp only [ha, hb, Category.assoc]
    rw [← pullback.condition]
  set D := D₁Q.comap O'.ι with hD
  -- the subscheme of `D` is the open `D₁Q.subschemeι ⁻¹ᵁ O' = W` of `D₁Q`
  let ε : D.subscheme ≅ (D₁Q.subschemeι ⁻¹ᵁ O').toScheme :=
    D₁Q.comapIso O'.ι ≪≫ pullbackSymmetry _ _ ≪≫ pullbackRestrictIsoRestrict D₁Q.subschemeι O'
  have hε : ε.hom ≫ (D₁Q.subschemeι ⁻¹ᵁ O').ι ≫ D₁Q.subschemeι = D.subschemeι ≫ O'.ι := by
    simp only [ε, Iso.trans_hom, Category.assoc, pullbackRestrictIsoRestrict_hom_ι_assoc,
      pullbackSymmetry_hom_comp_fst_assoc, D]
    rw [← pullback.condition, ← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  refine ⟨U₀, hel, hUaff, O'.toScheme, a, b, hab, ?_, D, ?_, ?_, ?_, ?_⟩
  · -- `O' ⟶ N ×_S U₀` is an open immersion
    have : pullback.lift a b hab = O'.ι ≫ pullback.map f U₀.toBase π U₀.toBase O.ι (𝟙 _) (𝟙 _)
        (by simp [hf]) (by simp) := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Category.assoc, pullback.lift_fst, ha]
      · rw [pullback.lift_snd, Category.assoc, pullback.lift_snd, hb, Category.comp_id]
    rw [this]; infer_instance
  · exact isRelativeEffectiveCartierDivisor_comap_of_flat _ D₁Q O'.ι hrelQ
  · have hfinW' : IsFinite ((D₁Q.subschemeι ⁻¹ᵁ O').ι ≫ D₁Q.subschemeι ≫
        pullback.snd f U₀.toBase) := by
      rw [hO'W]; exact hWfin
    have : D.subschemeι ≫ b =
        ε.hom ≫ (D₁Q.subschemeι ⁻¹ᵁ O').ι ≫ D₁Q.subschemeι ≫ pullback.snd f U₀.toBase := by
      rw [hb, ← Category.assoc D.subschemeι, ← hε]; simp only [Category.assoc]
    rw [this]; infer_instance
  · -- the fibre of `D` over `U₀.point` is that of `Z`
    have hfibeq' := hfibeq
    rw [← hgw] at hfibeq'
    let ψ : b.fiber U₀.point ⟶ (pullback.snd f U₀.toBase).fiber U₀.point :=
      pullback.map b (U₀.scheme.fromSpecResidueField U₀.point) (pullback.snd f U₀.toBase)
        (U₀.scheme.fromSpecResidueField U₀.point) O'.ι (𝟙 _) (𝟙 _) (by simp [hb]) (by simp)
    have hψ : ψ ≫ (pullback.snd f U₀.toBase).fiberι U₀.point = b.fiberι U₀.point ≫ O'.ι :=
      pullback.lift_fst _ _ _
    let φ := ψ ≫ (Stacks.Flatness.fiberAfterElementaryEtaleIso f (g w₁) U₀ hel).hom
    have hφ : φ ≫ f.fiberι (g w₁) = b.fiberι U₀.point ≫ O'.ι ≫ pullback.fst f U₀.toBase := by
      simp only [φ, Category.assoc, Stacks.Flatness.fiberAfterElementaryEtaleIso_fiberι]
      rw [← Category.assoc, hψ, Category.assoc]
    have h1 : b.fiberι U₀.point ≫ a = (φ ≫ f.fiberι (g w₁)) ≫ O.ι := by
      rw [hφ, ha]; simp only [Category.assoc]
    have h2 : b.fiberι U₀.point ≫ O'.ι ≫ pullback.fst f U₀.toBase = φ ≫ f.fiberι (g w₁) :=
      hφ.symm
    rw [← Scheme.IdealSheafData.comap_comp, h1, hD, ← Scheme.IdealSheafData.comap_comp, hD₁Q,
      ← Scheme.IdealSheafData.comap_comp,
      show (b.fiberι U₀.point ≫ O'.ι) ≫ pullback.fst f U₀.toBase = φ ≫ f.fiberι (g w₁) by
        rw [Category.assoc, h2]]
    simp only [Scheme.IdealSheafData.comap_comp, hfibeq']
  · -- the points over `U₀.point`
    let isoW : (D₁Q.subschemeι ⁻¹ᵁ O').toScheme ≅ W.toScheme :=
      IsOpenImmersion.isoOfRangeEq (D₁Q.subschemeι ⁻¹ᵁ O').ι W.ι (by rw [hO'W])
    let θ : D.subscheme ≅ V.toScheme := ε ≪≫ isoW ≪≫ asIso (e.hom ∣_ V)
    have hθV : θ.hom ≫ V.ι = ε.hom ≫ (D₁Q.subschemeι ⁻¹ᵁ O').ι ≫ e.hom := by
      simp only [θ, Iso.trans_hom, asIso_hom, Category.assoc, morphismRestrict_ι]
      rw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
    have hθb : θ.hom ≫ V.ι ≫ pullback.snd g U₀.toBase = D.subschemeι ≫ b := by
      rw [← Category.assoc, hθV, Category.assoc, Category.assoc, he_snd, hb,
        ← Category.assoc D.subschemeι, ← hε]
      simp only [Category.assoc]
    have he_fst' : e.hom ≫ pullback.fst g U₀.toBase ≫ D₁.subschemeι ≫ O.ι =
        D₁Q.subschemeι ≫ pullback.fst f U₀.toBase ≫ O.ι := by
      simpa only [Category.assoc] using congrArg (· ≫ O.ι) he_fst
    have hε' : ε.hom ≫ (D₁Q.subschemeι ⁻¹ᵁ O').ι ≫ D₁Q.subschemeι ≫ pullback.fst f U₀.toBase ≫
        O.ι = D.subschemeι ≫ a := by
      rw [ha]; simpa only [Category.assoc] using congrArg (· ≫ pullback.fst f U₀.toBase ≫ O.ι) hε
    have hθa : θ.hom ≫ V.ι ≫ pullback.fst g U₀.toBase ≫ D₁.subschemeι ≫ O.ι =
        D.subschemeι ≫ a := by
      rw [← Category.assoc, hθV, Category.assoc, Category.assoc, he_fst', hε']
    obtain ⟨v₀', hv₀', huniq'⟩ := hspec.2.1
    let v₀ : V.toScheme := v₀'
    have hv₀ : (V.ι ≫ pullback.snd g U₀.toBase) v₀ = U₀.point := hv₀'
    have huniq : ∀ y : V.toScheme, (V.ι ≫ pullback.snd g U₀.toBase) y = U₀.point → y = v₀ :=
      fun y hy => huniq' y hy
    obtain ⟨hv₀w, hv₀res⟩ := hspec.2.2 v₀' hv₀'
    have hv₀w' : (V.ι ≫ pullback.fst g U₀.toBase) v₀ = w₁ := hv₀w
    have hθinv : θ.hom (θ.inv v₀) = v₀ := by
      rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]; rfl
    have hy : b (D.subschemeι (θ.inv v₀)) = U₀.point := by
      have key := congrArg (fun y => y (θ.inv v₀)) hθb
      simp only [hb, Scheme.Hom.comp_apply, hθinv] at key hv₀ ⊢
      rw [← key]; exact hv₀
    refine ⟨⟨θ.inv v₀, hy, ?_, ?_⟩, ?_⟩
    · have key := congrArg (fun y => y (θ.inv v₀)) hθa
      have hw2 := congrArg (fun y => (D₁.subschemeι ≫ O.ι) y) hv₀w'
      simp only [Scheme.Hom.comp_apply, hθinv] at key hw2 ⊢
      rw [← key, hw2, hw₁]; rfl
    · have h1 := Stacks.Flatness.pullback_fst_residueFieldMap_isIso_of_elementary f (g w₁) U₀
        hel _ hy
      rw [ha, Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp]
      have h2 : IsIso (O.ι.residueFieldMap
          (pullback.fst f U₀.toBase (O'.ι (D.subschemeι (θ.inv v₀))))) :=
        inferInstanceAs (IsIso (Scheme.Hom.residueFieldMap O.ι _))
      have h3 : IsIso (O'.ι.residueFieldMap (D.subschemeι (θ.inv v₀))) :=
        inferInstanceAs (IsIso (Scheme.Hom.residueFieldMap O'.ι _))
      exact IsIso.comp_isIso' (IsIso.comp_isIso' h2 h1) h3
    · intro d d' hd hd'
      have hθ : ∀ d, b (D.subschemeι d) = U₀.point → θ.hom d = v₀ := fun d hd =>
        huniq _ (by rw [← Scheme.Hom.comp_apply, hθb]; exact hd)
      have : ∀ y, θ.inv (θ.hom y) = y := fun y => by
        rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]; rfl
      rw [← this d, ← this d', hθ d hd, hθ d' hd']

end

end AlgebraicGeometry.C1590Private

end
