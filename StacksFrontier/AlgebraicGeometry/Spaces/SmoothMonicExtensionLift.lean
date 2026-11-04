module

public import Mathlib.FieldTheory.PrimitiveElement
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Smooth.SmoothFormallySmoothTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Smooth
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseChangeLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.NormalizationChartObject
public import StacksFrontier.RingTheory.Artinian.EtaleResidueLift
public import StacksFrontier.RingTheory.Artinian.MonicExtensionRetraction
public import StacksFrontier.Deformation.Artin.AlgebraicSpaceCriterion

/-!
# Lifting through a smooth algebraic space after a monogenic extension

Let `G` be an algebraic space over a scheme `S` whose structure morphism is smooth, let
`B → A` be a surjection of Artinian local rings with square-zero kernel, and let `α` be a point of
`G` with values in `Spec A`. An étale chart `W ⟶ G` need not have a point over `α`: it only
acquires one after a finite separable extension of the residue field. This file shows that there is
a monic polynomial `ḡ` over the residue field of `A` such that, for *every* monic lift `g` of `ḡ`
to `B`, the point `α` lifts along `Spec (A[X]/(g)) ⟶ Spec (B[X]/(g))`, after pulling it back to
`Spec (A[X]/(g))`.

## Main results

* `AlgebraicGeometry.Space.exists_monic_lift_of_isSmooth`: the statement above.

## Implementation notes

The chart point is produced on an affine open of the base change `E = W ×_G Spec A`, which is étale
over `Spec A`, by `Stacks.EtaleResidueLift.exists_ringHom_adjoinRoot`; the lift is then
formal smoothness of the smooth scheme `W ⟶ S` along the first-order thickening
`Spec (A[X]/(g)) ⟶ Spec (B[X]/(g))`. The polynomial `ḡ` is the minimal polynomial of a primitive
element of the residue field of a point of `E`, which is finite separable over the residue field
of `A`. The objects of the site carrying the two spectra are supplied by the caller, who needs them
again to descend the lift (`Stacks.MonicExtension.retraction`).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial IsLocalRing

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The terminal presheaf of the site is a chart of itself. -/
theorem etale_terminalYonedaIso :
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
      (((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso
        terminalIsTerminal).hom := by
  have hEtale : MorphismProperty.ContainsIdentities
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsMultiplicative.toContainsIdentities
  have hEtaleIso : MorphismProperty.RespectsIso
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : MorphismProperty.ContainsIdentities
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
  have : MorphismProperty.RespectsIso
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
  exact MorphismProperty.presheaf_of_isIso _ _

/-- An étale chart of an algebraic space smooth over `S` is smooth over `S`. -/
theorem smooth_of_etale_of_isSmooth {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hsm : IsSmooth B S hS (terminal.from G)) {W : BigFppfOver B S hS} {c : yoneda.obj W ⟶ G}
    (hc : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c) :
    Smooth (B.inclusion.map W.hom) :=
  let t : yoneda.obj (Over.mk (𝟙 (B.obj hS)) : BigFppfOver B S hS) ⟶
      ⊤_ ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    (((Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _).uniqueUpToIso
      terminalIsTerminal).hom
  hsm W _ c t (Over.homMk W.hom (by simp)) hc (etale_terminalYonedaIso B S hS)
    (terminalIsTerminal.hom_ext _ _)

/-- A morphism of the site whose underlying morphism of schemes factors a morphism of the site
through another lifts to the site. -/
theorem exists_comp_eq_of_toScheme {X Y Z : BigFppfOver B S hS} (g : Y ⟶ Z) {p : X ⟶ Z}
    (t : (BigFppfOver.toScheme B S hS).obj X ⟶ (BigFppfOver.toScheme B S hS).obj Y)
    (ht : t ≫ (BigFppfOver.toScheme B S hS).map g = (BigFppfOver.toScheme B S hS).map p) :
    ∃ t' : X ⟶ Y, t' ≫ g = p :=
  ⟨siteHom B S hS t (by
      rw [← BigFppfOver.toScheme_map_comp_hom g, ← Category.assoc, ht,
        BigFppfOver.toScheme_map_comp_hom]),
    Deformation.Artin.BigFppfOver.hom_ext_of_toScheme (by
      rw [Functor.map_comp, toScheme_map_siteHom, ht])⟩

/-- A morphism of the site into an object smooth over `S` extends along a first-order thickening
with affine source and target. -/
theorem exists_lift_of_smooth_of_isFirstOrderThickening {W X Y : BigFppfOver B S hS}
    (hW : Smooth (B.inclusion.map W.hom)) (i : X ⟶ Y)
    (hi : Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj X)]
    (hY : IsAffine ((BigFppfOver.toScheme B S hS).obj Y)) (s : X ⟶ W) :
    ∃ ℓ : Y ⟶ W, i ≫ ℓ = s := by
  obtain ⟨g, hg₁, hg₂⟩ := Stacks.Smooth.formallySmoothScheme_of_smooth
    (B.inclusion.map W.hom) inferInstance hY ((BigFppfOver.toScheme B S hS).map i) hi
    ((BigFppfOver.toScheme B S hS).map s) (B.inclusion.map Y.hom) (by
      rw [BigFppfOver.toScheme_map_comp_hom, BigFppfOver.toScheme_map_comp_hom])
  exact ⟨siteHom B S hS g hg₁, Deformation.Artin.BigFppfOver.hom_ext_of_toScheme (by
    rw [Functor.map_comp, toScheme_map_siteHom, hg₂])⟩

/-- **Lifting through a smooth algebraic space after a monogenic extension.** Let `G` be an
algebraic space over `S` with smooth structure morphism, `A` a local ring with nilpotent maximal
ideal, and `α` a point of `G` over an object `T_A` of the site with underlying scheme `Spec A`.
There is a monic `ḡ` of positive degree over the residue field of `A` such that for every monic
lift `g ∈ A[X]` of `ḡ`, every object `T_A''` with underlying scheme `Spec (A[X]/(g))` over `T_A`,
and every first-order thickening `T_A'' ⟶ T_B''` with affine target, the pullback of `α` to
`T_A''` extends to `T_B''`. -/
theorem exists_monic_lift_of_isSmooth
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hG : IsAlgebraicSpace B S hS G)
    (hsm : IsSmooth B S hS (terminal.from G))
    {RA : CommRingCat.{u}} [IsLocalRing RA] (hmA : IsNilpotent (maximalIdeal RA))
    (TA : BigFppfOver B S hS) (eA : (BigFppfOver.toScheme B S hS).obj TA ≅ Spec RA)
    (α : yoneda.obj TA ⟶ G) :
    ∃ gbar : (ResidueField RA)[X], gbar.Monic ∧ 0 < gbar.natDegree ∧
      ∀ (gA : RA[X]), gA.Monic → gA.map (residue RA) = gbar →
      ∀ (TA'' TB'' : BigFppfOver B S hS)
        (eA'' : (BigFppfOver.toScheme B S hS).obj TA'' ≅ Spec (.of (AdjoinRoot gA)))
        (pA : TA'' ⟶ TA),
        (BigFppfOver.toScheme B S hS).map pA =
          eA''.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap RA (AdjoinRoot gA))) ≫ eA.inv →
        ∀ (i'' : TA'' ⟶ TB''),
          Stacks.Thickenings.IsFirstOrderThickening ((BigFppfOver.toScheme B S hS).map i'') →
          IsAffine ((BigFppfOver.toScheme B S hS).obj TB'') →
        ∃ γ : yoneda.obj TB'' ⟶ G, yoneda.map i'' ≫ γ = yoneda.map pA ≫ α := by
  classical
  let V := BigFppfOver.toScheme B S hS
  obtain ⟨W, c, hcs, hce⟩ := hG.exists_atlas
  have hrep := hce.rep
  let E := hrep.pullback α
  let snd : E ⟶ TA := hrep.snd α
  let fst : E ⟶ W := hrep.fst' α
  have hw : yoneda.map fst ≫ c = yoneda.map snd ≫ α := by
    rw [hrep.map_fst']
    exact hrep.w α
  have hsndE : Etale (V.map snd) := hce.property_snd α
  obtain ⟨e, -⟩ := (show Surjective (V.map snd) from hcs.property_snd α).surj
    (eA.inv (IsLocalRing.closedPoint RA))
  obtain ⟨R, f, hf, hef, -⟩ :=
    Scheme.exists_affine_mem_range_and_range_subset (U := (⊤ : (V.obj E).Opens))
      (x := e) trivial
  have : Nontrivial R := PrimeSpectrum.nontrivial hef.choose
  let φ : RA ⟶ R := Spec.preimage (f ≫ V.map snd ≫ eA.hom)
  have hφ : Spec.map φ = f ≫ V.map snd ≫ eA.hom := Spec.map_preimage _
  have hφE : RingHom.Etale φ.hom := by
    rw [← HasRingHomProperty.Spec_iff (P := @Etale), hφ]
    infer_instance
  obtain ⟨gbar, hgm, hgd, hlift⟩ :=
    Stacks.EtaleResidueLift.exists_monic_ringHom_adjoinRoot_of_etale hmA φ.hom hφE
  refine ⟨gbar, hgm, hgd, fun gA hgA hgAbar TA'' TB'' eA'' pA hpA i'' hi'' hTB => ?_⟩
  obtain ⟨ℓ, hℓ⟩ := hlift gA hgA hgAbar
  let tsch : V.obj TA'' ⟶ V.obj E := eA''.hom ≫ Spec.map (CommRingCat.ofHom ℓ) ≫ f
  have htsch : tsch ≫ V.map snd = V.map pA := by
    have h1 : Spec.map (CommRingCat.ofHom ℓ) ≫ Spec.map φ =
        Spec.map (CommRingCat.ofHom (algebraMap RA (AdjoinRoot gA))) := by
      rw [← Spec.map_comp]
      congr 1
      ext x
      exact RingHom.congr_fun hℓ x
    have hfs : f ≫ V.map snd = Spec.map φ ≫ eA.inv := by simp [hφ]
    rw [hpA]
    simp only [tsch, Category.assoc, hfs]
    rw [← Category.assoc (Spec.map (CommRingCat.ofHom ℓ)), h1]
  obtain ⟨tE, htE⟩ := exists_comp_eq_of_toScheme B S hS snd tsch htsch
  have : IsAffine (V.obj TA'') := IsAffine.of_isIso eA''.hom
  obtain ⟨ℓW, hℓW⟩ := exists_lift_of_smooth_of_isFirstOrderThickening B S hS
    (smooth_of_etale_of_isSmooth B S hS hsm hce) i'' hi'' hTB (tE ≫ fst)
  refine ⟨yoneda.map ℓW ≫ c, ?_⟩
  rw [← Category.assoc, ← yoneda.map_comp, hℓW, yoneda.map_comp, Category.assoc, hw,
    ← Category.assoc, ← yoneda.map_comp, htE]

end AlgebraicGeometry.Space

end
