module

public import StacksFrontier.AlgebraicGeometry.Descent.CubeLocalTriviality
public import StacksFrontier.AlgebraicGeometry.Descent.DescentLocusComparison0BF1
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ReducedProduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleFinitePresentation

/-!
# Triviality near a fibre in the theorem of the cube

Let `X`, `Y` be proper, flat, of finite presentation, with geometrically integral fibres over
`Spec A`, with sections `σ`, `τ`, and let `L` be an invertible module on `P = X ×_A Y` which is
trivial along the two faces `Y ⟶ P` and `X ⟶ P` through the sections. If `L` is trivial on the
fibre of `P` over a prime `p`, then there are `a ∉ p` and a global section of `L` vanishing at no
point of `P` over `D(a)`. This is the openness step of the proof of [Stacks, Tag 0BF4]
(through [Stacks, Tag 0BF3]).

The fibre data required by `Stacks.Cube.exists_section_pullback_ne_zero` is built here: the
fibres `X_p`, `Y_p` and `P_p = X_p ×_{κ(p)} Y_p` with their faces, and `Γ(𝒪) = κ(p)` on each of
them ([Stacks, Tag 0BUG] (8), with [Stacks, Tag 035Z] for the product). The nonvanishing of the
resulting section on the fibre is then spread over a neighbourhood by properness.

## Main results

* `Stacks.Cube.bijective_globalRingHom_pullback_fst_comp`: `Γ(𝒪) = K` for a product of two
  proper geometrically integral schemes over a field `K`.
* `Stacks.Cube.exists_basicOpen_nonvanishing`: the openness step.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProperFlatGlobalSections AlgebraicGeometry.DescentLocusComparison

universe u

namespace Stacks.Cube

/-- **Global functions on a product of geometrically integral proper schemes over a field.**
For `f : X ⟶ Spec K`, `g : Y ⟶ Spec K` proper, flat, locally of finite presentation and
geometrically integral, `K ⟶ Γ(X ×_K Y, 𝒪)` is bijective: the product is geometrically reduced
([Stacks, Tag 035Z]) and geometrically irreducible, hence geometrically integral, and proper. -/
theorem bijective_globalRingHom_pullback_fst_comp {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (g : Y ⟶ Spec (.of K))
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f] [GeometricallyIntegral f]
    [IsProper g] [Flat g] [LocallyOfFinitePresentation g] [GeometricallyIntegral g] :
    Function.Bijective (Stacks.Cech.globalRingHom (pullback.fst f g ≫ f)).hom := by
  have : GeometricallyReduced (pullback.fst f g ≫ f) :=
    geometricallyReduced_pullback_over_field f g
  have : GeometricallyIrreducible (pullback.fst f g ≫ f) :=
    GeometricallyIrreducible.comp _ _
  have : GeometricallyIntegral (pullback.fst f g ≫ f) :=
    GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible _
  exact bijective_globalRingHom_of_geometricallyIntegral _

variable {A : Type u} [CommRing A] {X Y P : Scheme.{u}}
  {fX : X ⟶ Spec (.of A)} {fY : Y ⟶ Spec (.of A)} {r : P ⟶ X} {q : P ⟶ Y}

/-- A finite affine cover of a proper scheme over an affine base, with all finite intersections
affine, can be taken to contain any given affine open. -/
private theorem exists_finiteAffineCover_with_affine {A : Type u} [CommRing A] {Z : Scheme.{u}}
    (f : Z ⟶ Spec (.of A)) [IsProper f] (U₀ : Z.Opens) (hU₀ : IsAffineOpen U₀) :
    ∃ (I : Type u) (_ : Fintype I) (_ : LinearOrder I) (U : I → Z.Opens),
      (⊤ : Z.Opens) = ⨆ i, U i ∧ (∀ i, IsAffineOpen (U i)) ∧
        (∀ (m : ℕ) (a : Fin (m + 1) → I), IsAffineOpen (⨅ k, U (a k))) ∧ ∃ i₀, U i₀ = U₀ := by
  obtain ⟨I, _, _, U, hU, hUaff, -⟩ := exists_finiteAffineCover_of_isProper f
  let U' : WithBot I → Z.Opens := fun o => WithBot.recBotCoe U₀ U o
  have hUaff' : ∀ o, IsAffineOpen (U' o) := by
    intro o
    induction o using WithBot.recBotCoe with
    | bot => exact hU₀
    | coe i => exact hUaff i
  exact ⟨WithBot I, inferInstance, inferInstance, U',
    le_antisymm (hU.le.trans (iSup_le fun i => le_iSup U' (i : WithBot I))) le_top, hUaff',
    fun _ a => Stacks.Cech.inter_isAffineOpen f U' hUaff' a, ⊥, rfl⟩

/-- **The openness step of the theorem of the cube, over an affine base.** Let `P = X ×_A Y`
with `X`, `Y` proper, flat, locally of finite presentation and geometrically integral over `A`,
with sections `σ`, `τ` landing in affine opens `U₀`, `V₀`, and faces `j₁ : Y ⟶ P`,
`j₂ : X ⟶ P` through them. Let `L` be invertible on `P`, trivial along both faces, and trivial
on the fibre of `P` over a prime `p` (presented by any pullback square). Then there are `a ∉ p`
and a global section of `L` vanishing at no point of `P` lying over `D(a)`. -/
theorem exists_basicOpen_nonvanishing (H : IsPullback r q fX fY)
    [IsProper fX] [Flat fX] [LocallyOfFinitePresentation fX] [GeometricallyIntegral fX]
    [IsProper fY] [Flat fY] [LocallyOfFinitePresentation fY] [GeometricallyIntegral fY]
    (σ : Spec (.of A) ⟶ X) (τ : Spec (.of A) ⟶ Y) (hσ : σ ≫ fX = 𝟙 _) (hτ : τ ≫ fY = 𝟙 _)
    (j₁ : Y ⟶ P) (hj₁r : j₁ ≫ r = fY ≫ σ) (hj₁q : j₁ ≫ q = 𝟙 Y)
    (j₂ : X ⟶ P) (hj₂r : j₂ ≫ r = 𝟙 X) (hj₂q : j₂ ≫ q = fX ≫ τ)
    (L : P.Modules) [Stacks.SheafOfModules.IsInvertible P.presheaf P.ringCatSheaf.2 L]
    (e₁ : (Scheme.Modules.pullback j₁).obj L ≅ Scheme.unitModule Y)
    (e₂ : (Scheme.Modules.pullback j₂).obj L ≅ Scheme.unitModule X)
    (U₀ : X.Opens) (hU₀ : IsAffineOpen U₀) (hσU₀ : σ ⁻¹ᵁ U₀ = ⊤)
    (V₀ : Y.Opens) (hV₀ : IsAffineOpen V₀) (hτV₀ : τ ⁻¹ᵁ V₀ = ⊤)
    (p : Ideal A) [p.IsPrime] {P' : Scheme.{u}} {g' : P' ⟶ P}
    {π' : P' ⟶ Spec (.of p.ResidueField)}
    (hsq' : IsPullback g' π' (r ≫ fX)
      (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))
    (e' : Nonempty ((Scheme.Modules.pullback g').obj L ≅ Scheme.unitModule P')) :
    ∃ a : A, a ∉ p ∧ ∃ s : Γ(L, ⊤), ∀ x : P,
      (r ≫ fX).base x ∈ PrimeSpectrum.basicOpen a → x ∈ Stacks.Ample.nonvanishingLocus L s := by
  classical
  obtain ⟨e'⟩ := e'
  set κ := p.ResidueField
  set χ := algebraMap A κ
  set sp : Spec (.of κ) ⟶ Spec (.of A) := Spec.map (CommRingCat.ofHom χ) with hsp
  have : IsProper r := MorphismProperty.of_isPullback H.flip inferInstance
  have : LocallyOfFinitePresentation r := MorphismProperty.of_isPullback H.flip inferInstance
  have : Flat r := MorphismProperty.of_isPullback H.flip inferInstance
  have : L.IsFinitePresentation :=
    Stacks.SheafOfModules.isFinitePresentation_of_isInvertible_ringedSpace P.toRingedSpace L
      inferInstance
  have hL : IsFlatOver (r ≫ fX).toLRSHom.toShHom L := isFlatOver_of_isInvertible (r ≫ fX) L
  -- covers adapted to the sections
  obtain ⟨I, _, _, U', hU', hUaff', haffU', a₀, rfl⟩ :=
    exists_finiteAffineCover_with_affine fX U₀ hU₀
  obtain ⟨J, _, _, V', hV', hVaff', haffV', b₀, rfl⟩ :=
    exists_finiteAffineCover_with_affine fY V₀ hV₀
  -- the fibres
  set gX := pullback.fst fX sp
  set fX₀ := pullback.snd fX sp
  set gY := pullback.fst fY sp
  set fY₀ := pullback.snd fY sp
  have hsqX : IsPullback gX fX₀ fX sp := IsPullback.of_hasPullback _ _
  have hsqY : IsPullback gY fY₀ fY sp := IsPullback.of_hasPullback _ _
  set r₀ := pullback.fst fX₀ fY₀
  set q₀ := pullback.snd fX₀ fY₀
  have H₀ : IsPullback r₀ q₀ fX₀ fY₀ := IsPullback.of_hasPullback _ _
  have hw : (r₀ ≫ gX) ≫ fX = (q₀ ≫ gY) ≫ fY := by
    rw [Category.assoc, Category.assoc, hsqX.w, hsqY.w, ← Category.assoc, ← Category.assoc,
      pullback.condition]
  set gP := H.lift (r₀ ≫ gX) (q₀ ≫ gY) hw
  have hr₀ : r₀ ≫ gX = gP ≫ r := (H.lift_fst _ _ _).symm
  have hq₀ : q₀ ≫ gY = gP ≫ q := (H.lift_snd _ _ _).symm
  have hbig : IsPullback (q₀ ≫ gY) r₀ fY (fX₀ ≫ sp) := H₀.flip.paste_horiz hsqY
  have hA : IsPullback gP r₀ r gX :=
    IsPullback.of_right (by rw [← hq₀, hsqX.w]; exact hbig) hr₀.symm H.flip
  have hsqP : IsPullback gP (r₀ ≫ fX₀) (r ≫ fX) sp := hA.paste_vert hsqX
  -- sections and faces on the fibres
  set σ₀ : Spec (.of κ) ⟶ pullback fX sp := pullback.lift (sp ≫ σ) (𝟙 _)
    (by rw [Category.assoc, hσ, Category.comp_id, Category.id_comp])
  have hσ₀ : σ₀ ≫ fX₀ = 𝟙 _ := pullback.lift_snd _ _ _
  have hσ₀g : σ₀ ≫ gX = sp ≫ σ := pullback.lift_fst _ _ _
  set τ₀ : Spec (.of κ) ⟶ pullback fY sp := pullback.lift (sp ≫ τ) (𝟙 _)
    (by rw [Category.assoc, hτ, Category.comp_id, Category.id_comp])
  have hτ₀ : τ₀ ≫ fY₀ = 𝟙 _ := pullback.lift_snd _ _ _
  have hτ₀g : τ₀ ≫ gY = sp ≫ τ := pullback.lift_fst _ _ _
  set j₁₀ : pullback fY sp ⟶ pullback fX₀ fY₀ := pullback.lift (fY₀ ≫ σ₀) (𝟙 _)
    (by rw [Category.assoc, hσ₀, Category.comp_id, Category.id_comp])
  have hj₁₀r : j₁₀ ≫ r₀ = fY₀ ≫ σ₀ := pullback.lift_fst _ _ _
  have hj₁₀q : j₁₀ ≫ q₀ = 𝟙 _ := pullback.lift_snd _ _ _
  have hj₁₀g : j₁₀ ≫ gP = gY ≫ j₁ := by
    refine H.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, ← hr₀, reassoc_of% hj₁₀r, hσ₀g, hj₁r,
        reassoc_of% hsqY.w]
    · rw [Category.assoc, Category.assoc, ← hq₀, reassoc_of% hj₁₀q, hj₁q, Category.comp_id]
  set j₂₀ : pullback fX sp ⟶ pullback fX₀ fY₀ := pullback.lift (𝟙 _) (fX₀ ≫ τ₀)
    (by rw [Category.assoc, hτ₀, Category.comp_id, Category.id_comp])
  have hj₂₀r : j₂₀ ≫ r₀ = 𝟙 _ := pullback.lift_fst _ _ _
  have hj₂₀q : j₂₀ ≫ q₀ = fX₀ ≫ τ₀ := pullback.lift_snd _ _ _
  have hj₂₀g : j₂₀ ≫ gP = gX ≫ j₂ := by
    refine H.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, ← hr₀, reassoc_of% hj₂₀r, hj₂r, Category.comp_id]
    · rw [Category.assoc, Category.assoc, ← hq₀, reassoc_of% hj₂₀q, hτ₀g, hj₂q,
        reassoc_of% hsqX.w]
  -- `Γ(𝒪) = κ` on the three fibres
  have hΓX₀ : Function.Bijective (Stacks.Cech.globalRingHom fX₀).hom :=
    bijective_globalRingHom_of_geometricallyIntegral _
  have hΓY₀ : Function.Bijective (Stacks.Cech.globalRingHom fY₀).hom :=
    bijective_globalRingHom_of_geometricallyIntegral _
  have hΓP₀ : Function.Bijective (Stacks.Cech.globalRingHom (r₀ ≫ fX₀)).hom :=
    bijective_globalRingHom_pullback_fst_comp fX₀ fY₀
  -- the triviality on the fibre, transported to this presentation of it
  set i : pullback fX₀ fY₀ ⟶ P' := hsq'.lift gP (r₀ ≫ fX₀) hsqP.w
  have hi : i ≫ g' = gP := hsq'.lift_fst _ _ _
  let e₀ : (Scheme.Modules.pullback gP).obj L ≅ Scheme.unitModule (pullback fX₀ fY₀) :=
    ((Scheme.Modules.pullbackCongr hi).app L).symm ≪≫
      ((Scheme.Modules.pullbackComp i g').app L).symm ≪≫
      (Scheme.Modules.pullback i).mapIso e' ≪≫ Scheme.Modules.pullbackUnitIso i
  -- a global section nonzero on the fibre
  obtain ⟨s, hs⟩ := exists_section_pullback_ne_zero H σ τ hσ hτ j₁ hj₁r hj₁q j₂ hj₂r hj₂q L hL
    e₁ e₂ U' hU' hUaff' haffU' V' hV' hVaff' haffV' a₀ hσU₀ b₀ hτV₀ p hsqX hsqY hsqP H₀ rfl
    hr₀ hq₀ σ₀ hσ₀ hσ₀g τ₀ hτ₀ hτ₀g j₁₀ hj₁₀r hj₁₀q hj₁₀g j₂₀ hj₂₀r hj₂₀q hj₂₀g hΓX₀ hΓY₀ hΓP₀ e₀
  -- it vanishes nowhere on the fibre
  set N := Stacks.Ample.nonvanishingLocus L s
  have hNopen : IsOpen N := Stacks.NonvanishingOpen.isOpen_nonvanishingLocus P L s
  set Zc := (r ≫ fX).base '' Nᶜ
  have hZc : IsClosed Zc := (r ≫ fX).isClosedMap _ hNopen.isClosed_compl
  have hfib : gP.base ⁻¹' N = Set.univ := by
    rw [Stacks.NonvanishingPullback.preimage_nonvanishingLocus gP L s]
    exact nonvanishingLocus_eq_univ_of_ne_zero
      (bijective_baseRingHom_of_eq_top (r₀ ≫ fX₀) rfl hΓP₀) e₀ _
      (show Stacks.NonvanishingPullback.pullbackGlobalSection gP L s ≠ 0 from hs)
  -- a basic open neighbourhood of `p` avoiding the bad locus
  obtain ⟨ξ⟩ : Nonempty (Spec (CommRingCat.of κ)) := inferInstance
  have hs₀ : sp.base ξ ∉ Zc := by
    rintro ⟨x, hxN, hx⟩
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback hsqP x ξ hx
    exact hxN (hy ▸ (Set.ext_iff.1 hfib y).2 trivial)
  obtain ⟨_, ⟨t, rfl⟩, hst, htZ⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hs₀ hZc.isOpen_compl
  refine ⟨t, fun htp => hst ?_, s, fun x hx => ?_⟩
  · change t ∈ Ideal.comap χ ξ.asIdeal
    rw [Ideal.mem_comap, Ideal.algebraMap_residueField_eq_zero.mpr htp]
    exact Ideal.zero_mem _
  · by_contra hxN
    exact htZ hx ⟨x, hxN, rfl⟩

end Stacks.Cube

end
