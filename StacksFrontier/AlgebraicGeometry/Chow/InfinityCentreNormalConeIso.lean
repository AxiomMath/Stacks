module

public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreCharts
public import StacksFrontier.AlgebraicGeometry.Chow.InfinityCentreModification
public import StacksFrontier.AlgebraicGeometry.Descent.RelativeGluingOverBasis
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.NormalConeInNormalBundle
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Divisors.NormalCone.ConormalAlgebraSheafSections

/-!
# The normal cone inside the blowup at infinity (Stacks 0FBH)

Let `X` be a scheme, `i : Z ⟶ X` a closed immersion with quasi-coherent ideal sheaf
`ℐ = ker i`, and let
`b : W ⟶ 𝐏¹_X` be the blowup of `𝐏¹_X` in the centre `∞(Z)`, with exceptional divisor `E`,
fibre at infinity `W_∞` and strict transform `X' ⊆ W` of `X`. Clause (7) of Stacks 0FBG, which is
Stacks 0FBH, reads

  `E ∖ X' = E ∖ (X' ∩ E) = Spec_Z(𝒞_{Z/X,*}) = C_ZX`.

This file proves it: the normal cone `C_ZX = Spec_Z(𝒞_{Z/X,*})` of
`Stacks.Conormal.normalCone` is isomorphic over `X` to the open subscheme `E ∖ X'` of `E`, and
hence (through `E ∖ X' = W_∞ ∖ X'`, `Stacks.Chow.exceptionalComplIsoFibreCompl`) it is an open
subscheme of the fibre at infinity `W_∞` with image `W_∞ ∖ X'`. The latter is the open immersion
`j : C_ZX ⟶ W_∞` of Stacks 0FBK.

## Main definitions

* `Stacks.Chow.normalConeIsoExceptionalCompl`: **`C_ZX ≅ E ∖ X'`**, over `X`.
* `Stacks.Chow.normalConeToExceptionalDivisor`: the open immersion `C_ZX ⟶ E`.
* `Stacks.Chow.normalConeToFibreAtInfinity`: the open immersion `j : C_ZX ⟶ W_∞` into the fibre
  at infinity of the blowup at infinity read as a modification of `X ×_S 𝐏¹_S`.

## Main results

* `Stacks.Chow.normalConeToExceptionalDivisor_spec`: **Stacks 0FBH.** `C_ZX ⟶ E` is an open
  immersion with image `E ∖ (X' ∩ E) = E ∖ X'`, over `X`.
* `Stacks.Chow.normalConeToFibreAtInfinity_spec`: **Stacks 0FBH, on the fibre at infinity.**
  `j : C_ZX ⟶ W_∞` is an open immersion with image `W_∞ ∖ X'`, through `E`, over `X`.

## Implementation notes

The closed subscheme is an arbitrary closed immersion `i : Z ⟶ X`, and the blowup is that of the
centre cut out by its ideal sheaf `ker i`. The normal cone `C_ZX` is the relative spectrum over `Z`
itself, so no identification of `Z` with the closed subscheme `V(ker i)` is needed.

## References

* [Stacks Project, Tag 0FBH](https://stacks.math.columbia.edu/tag/0FBH)
* [Stacks Project, Tag 0FBG](https://stacks.math.columbia.edu/tag/0FBG)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}} (ℐ : X.IdealSheafData)

/-! ### The normal cone, glued over the affine opens of `X` -/

section NormalConeGluing

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The relative-spectrum situation of the conormal algebra of the closed immersion `i : Z ⟶ X`,
whose relative spectrum is the normal cone `C_ZX`. -/
abbrev conormalSituation : Stacks.RelativeSpec.RelativeSpecSituation.{u} :=
  { base := Z, algebra := Stacks.Conormal.conormalAlgebraSheaf i }

/-- The affine open `Z ∩ U` of `Z`, for an affine open `U` of `X`. -/
def subschemeAffineOpen (U : X.affineOpens) : Z.affineOpens :=
  ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩

/-- The spectrum of the sections of the conormal algebra over `Z ∩ U`. -/
abbrev normalConeChartSource (U : X.affineOpens) : Scheme.{u} :=
  Spec ((conormalSituation i).algebra.sections (subschemeAffineOpen i U).1)

/-- The structure morphism of the chart of `C_ZX` over `U`, to `U`. -/
def normalConeChartProj (U : X.affineOpens) : normalConeChartSource i U ⟶ U.1.toScheme :=
  Stacks.RelativeSpec.specSectionsToOpen (conormalSituation i) (subschemeAffineOpen i U) ≫
    (i ∣_ U.1)

/-- The chart of `C_ZX` over an affine open `U` of `X`. -/
def normalConeChart (U : X.affineOpens) :
    normalConeChartSource i U ⟶ Stacks.Conormal.normalCone i :=
  (Stacks.RelativeSpec.gluedSpectrum (conormalSituation i)).chart (subschemeAffineOpen i U)

/-- The structure morphism `C_ZX ⟶ X`. -/
abbrev normalConeToX : Stacks.Conormal.normalCone i ⟶ X :=
  Stacks.Conormal.normalConeToBase i ≫ i

/-- **The chart of `C_ZX` over `U` is the part of `C_ZX` lying over `U`.** -/
theorem isPullback_normalConeChart (U : X.affineOpens) :
    IsPullback (normalConeChartProj i U) (normalConeChart i U) U.1.ι (normalConeToX i) := by
  have h1 := (Stacks.RelativeSpec.gluedSpectrum (conormalSituation i)).chart_isPullback
    (subschemeAffineOpen i U)
  have h2 := isPullback_morphismRestrict i U.1
  exact h1.flip.paste_horiz h2

/-- If `V ≤ U` then `Z ∩ V ≤ Z ∩ U`. -/
theorem subschemeAffineOpen_mono {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    (subschemeAffineOpen i V).1 ≤ (subschemeAffineOpen i U).1 :=
  fun _ hx => h hx

/-- The charts of `C_ZX` over affine opens `V ≤ U` of `X` are compatible with the spectrum of the
restriction map of the conormal algebra. -/
theorem normalConeChart_naturality {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    Spec.map ((conormalSituation i).algebra.right.obj.map
        (homOfLE (subschemeAffineOpen_mono i h)).op) ≫ normalConeChart i U =
      normalConeChart i V :=
  (Stacks.RelativeSpec.gluedSpectrum (conormalSituation i)).chart_naturality
    (U := subschemeAffineOpen i V) (V := subschemeAffineOpen i U) (subschemeAffineOpen_mono i h)

/-- The open cover of `C_ZX` by its parts over the affine opens of `X`. -/
abbrev normalConeCover : (Stacks.Conormal.normalCone i).OpenCover :=
  X.directedAffineCover.pullback₁ (normalConeToX i)

/-- The identification of the chart of `C_ZX` over `U` with the part of `C_ZX` over `U`. -/
def normalConeChartIso (U : X.affineOpens) :
    normalConeChartSource i U ≅ pullback (normalConeToX i) U.1.ι :=
  (isPullback_normalConeChart i U).flip.isoPullback

/-- The identification of the chart of `C_ZX` over `U` with the part of `C_ZX` over `U` is
compatible with the maps to `C_ZX`. -/
@[reassoc (attr := simp)]
theorem normalConeChartIso_hom_fst (U : X.affineOpens) :
    (normalConeChartIso i U).hom ≫ pullback.fst _ _ = normalConeChart i U :=
  (isPullback_normalConeChart i U).flip.isoPullback_hom_fst

/-- The identification of the chart of `C_ZX` over `U` with the part of `C_ZX` over `U` is
compatible with the maps to `U`. -/
@[reassoc (attr := simp)]
theorem normalConeChartIso_hom_snd (U : X.affineOpens) :
    (normalConeChartIso i U).hom ≫ pullback.snd _ _ = normalConeChartProj i U :=
  (isPullback_normalConeChart i U).flip.isoPullback_hom_snd

/-- The chart of `C_ZX` over an affine open of `X` is an open immersion. -/
instance (U : X.affineOpens) : IsOpenImmersion (normalConeChart i U) :=
  MorphismProperty.of_isPullback (isPullback_normalConeChart i U) inferInstance

/-- The structure morphisms of the charts of `C_ZX` over affine opens `V ≤ U` of `X` are
compatible with restriction. -/
private theorem spec_map_restrict_comp_normalConeChartProj {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    Spec.map ((conormalSituation i).algebra.right.obj.map
        (homOfLE (subschemeAffineOpen_mono i h)).op) ≫ normalConeChartProj i U =
      normalConeChartProj i V ≫ X.homOfLE h := by
  rw [← cancel_mono U.1.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
    (isPullback_normalConeChart i U).w, (isPullback_normalConeChart i V).w, ← Category.assoc,
    normalConeChart_naturality i h]

/-- The identifications of the charts of `C_ZX` with the parts of `C_ZX` over affine opens
`V ≤ U` of `X` are compatible with restriction. -/
theorem normalConeChartIso_naturality {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    (normalConeChartIso i V).hom ≫ pullback.map (normalConeToX i) V.1.ι (normalConeToX i) U.1.ι
        (𝟙 _) (X.homOfLE h) (𝟙 X) (by simp) (by simp) =
      Spec.map ((conormalSituation i).algebra.right.obj.map
        (homOfLE (subschemeAffineOpen_mono i h)).op) ≫ (normalConeChartIso i U).hom := by
  refine pullback.hom_ext ?_ ?_
  · simp only [Category.assoc, pullback.lift_fst, Category.comp_id, normalConeChartIso_hom_fst]
    exact (normalConeChart_naturality i h).symm
  · rw [Category.assoc, pullback.lift_snd, ← Category.assoc, normalConeChartIso_hom_snd,
      Category.assoc, normalConeChartIso_hom_snd]
    exact (spec_map_restrict_comp_normalConeChartProj i h).symm

/-- A family of morphisms out of the charts of `C_ZX`, compatible with restriction, gives a family
of morphisms out of the parts of `C_ZX` over the affine opens of `X`, compatible with the
inclusions. -/
theorem map_comp_normalConeChartIso_inv_comp {T : Scheme.{u}}
    (g : ∀ U : X.affineOpens, normalConeChartSource i U ⟶ T)
    (hg : ∀ {U V : X.affineOpens} (h : V.1 ≤ U.1),
      Spec.map ((conormalSituation i).algebra.right.obj.map
        (homOfLE (subschemeAffineOpen_mono i h)).op) ≫ g U = g V)
    {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    pullback.map (normalConeToX i) V.1.ι (normalConeToX i) U.1.ι (𝟙 _) (X.homOfLE h) (𝟙 X)
        (by simp) (by simp) ≫ (normalConeChartIso i U).inv ≫ g U =
      (normalConeChartIso i V).inv ≫ g V := by
  rw [← cancel_epi (normalConeChartIso i V).hom, ← Category.assoc,
    normalConeChartIso_naturality i h]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  exact hg h

/-- **Gluing morphisms out of `C_ZX` over the affine opens of `X`.** A family of morphisms out of
the charts of `C_ZX` over the affine opens of `X`, compatible with restriction, glues to a
morphism out of `C_ZX`. -/
def normalConeGlue {T : Scheme.{u}} (g : ∀ U : X.affineOpens, normalConeChartSource i U ⟶ T)
    (hg : ∀ {U V : X.affineOpens} (h : V.1 ≤ U.1),
      Spec.map ((conormalSituation i).algebra.right.obj.map
        (homOfLE (subschemeAffineOpen_mono i h)).op) ≫ g U = g V) :
    Stacks.Conormal.normalCone i ⟶ T :=
  (normalConeCover i).glueMorphismsOfLocallyDirected (fun U => (normalConeChartIso i U).inv ≫ g U)
    fun f => map_comp_normalConeChartIso_inv_comp i g hg (leOfHom f)

/-- The glued morphism `Stacks.Chow.normalConeGlue` restricts to the given morphism on each
chart of `C_ZX`. -/
theorem normalConeChart_normalConeGlue {T : Scheme.{u}}
    (g : ∀ U : X.affineOpens, normalConeChartSource i U ⟶ T)
    (hg : ∀ {U V : X.affineOpens} (h : V.1 ≤ U.1),
      Spec.map ((conormalSituation i).algebra.right.obj.map
        (homOfLE (subschemeAffineOpen_mono i h)).op) ≫ g U = g V) (U : X.affineOpens) :
    normalConeChart i U ≫ normalConeGlue i g hg = g U := by
  have := Scheme.OpenCover.map_glueMorphismsOfLocallyDirected (normalConeCover i)
    (fun U => (normalConeChartIso i U).inv ≫ g U)
    (fun f => map_comp_normalConeChartIso_inv_comp i g hg (leOfHom f)) U
  rw [← normalConeChartIso_hom_fst, Category.assoc]
  exact (congrArg ((normalConeChartIso i U).hom ≫ ·) this).trans (Iso.hom_inv_id_assoc _ _)

/-- Two morphisms out of `C_ZX` agreeing on the charts over all affine opens of `X` are equal. -/
theorem normalCone_hom_ext {T : Scheme.{u}} {a b : Stacks.Conormal.normalCone i ⟶ T}
    (h : ∀ U : X.affineOpens, normalConeChart i U ≫ a = normalConeChart i U ≫ b) : a = b := by
  refine (normalConeCover i).hom_ext _ _ fun (U : X.affineOpens) => ?_
  have e : pullback.fst (normalConeToX i) U.1.ι ≫ a = pullback.fst (normalConeToX i) U.1.ι ≫ b := by
    rw [← cancel_epi (normalConeChartIso i U).hom, normalConeChartIso_hom_fst_assoc,
      normalConeChartIso_hom_fst_assoc]
    exact h U
  exact e

end NormalConeGluing

/-! ### The exceptional divisor over the charts `D₊(S)` -/

section ExceptionalChart

/-- The coordinate ring `Γ(X, U)[s][J/s] ⧸ (s)` of `E ∩ D₊(S)` over `U`. -/
abbrev exceptionalChartRing (U : X.affineOpens) : CommRingCat.{u} :=
  CommRingCat.of (infinityChartAlgebra (ℐ.ideal U) ⧸ infinityChartFibreIdeal (ℐ.ideal U))

/-- The quotient map `Γ(X, U)[s][J/s] ⟶ Γ(X, U)[s][J/s] ⧸ (s)`. -/
abbrev exceptionalChartQuotient (U : X.affineOpens) :
    CommRingCat.of (infinityChartAlgebra (ℐ.ideal U)) ⟶ exceptionalChartRing ℐ U :=
  CommRingCat.ofHom (Ideal.Quotient.mk (infinityChartFibreIdeal (ℐ.ideal U)))

/-- The exceptional divisor pulled back to the chart `D₊(S)` is the ideal sheaf of `(s)`. -/
theorem comap_exceptionalIdealAtInfinity_chartS (U : X.affineOpens) :
    (exceptionalIdealAtInfinity ℐ).comap (blowupAtInfinityChartS ℐ U) =
      (Spec.map (exceptionalChartQuotient ℐ U)).ker := by
  refine Scheme.IdealSheafData.ext_of_isAffine ?_
  refine (ideal_comap_exceptionalIdealAtInfinity_polyChart ℐ U Polynomial.X
      (X_mem_infinityChartIdeal _)).trans ?_
  refine Eq.trans ?_ (Scheme.Hom.ker_apply _ ⟨⊤, isAffineOpen_top _⟩).symm
  refine Eq.trans ?_ (Stacks.Smooth.ker_specMap_appTop (exceptionalChartQuotient ℐ U)).symm
  have hk : RingHom.ker (exceptionalChartQuotient ℐ U).hom =
      infinityChartFibreIdeal (ℐ.ideal U) := Ideal.mk_ker
  refine Eq.trans ?_ (congrArg (Ideal.comap _) hk).symm
  refine Eq.trans ?_ (Stacks.Blowup.comap_inv_eq_map_hom
    (Scheme.ΓSpecIso (CommRingCat.of (infinityChartAlgebra (ℐ.ideal U)))).symm _).symm
  exact ((Ideal.map_span _ _).trans (congrArg Ideal.span Set.image_singleton)).symm

/-- **The part of `E` over `D₊(S)`**: the morphism `Spec(Γ(X, U)[s][J/s] ⧸ (s)) ⟶ E`. -/
def exceptionalChartS (U : X.affineOpens) :
    Spec (exceptionalChartRing ℐ U) ⟶ (exceptionalIdealAtInfinity ℐ).subscheme :=
  IsClosedImmersion.lift (exceptionalIdealAtInfinity ℐ).subschemeι
    (Spec.map (exceptionalChartQuotient ℐ U) ≫ blowupAtInfinityChartS ℐ U) (by
      rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_comp,
        ← comap_exceptionalIdealAtInfinity_chartS]
      exact Scheme.IdealSheafData.le_map_comap _ _)

/-- The part of `E` over `D₊(S)` followed by `E ⟶ W` is the closed subscheme `(s)` of the chart
`D₊(S)` followed by the chart. -/
@[reassoc (attr := simp)]
theorem exceptionalChartS_subschemeι (U : X.affineOpens) :
    exceptionalChartS ℐ U ≫ (exceptionalIdealAtInfinity ℐ).subschemeι =
      Spec.map (exceptionalChartQuotient ℐ U) ≫ blowupAtInfinityChartS ℐ U :=
  IsClosedImmersion.lift_fac _ _ _

/-- **`E ∩ D₊(S)` is the closed subscheme `(s)` of the chart `D₊(S)`.** -/
theorem isPullback_exceptionalChartS (U : X.affineOpens) :
    IsPullback (Spec.map (exceptionalChartQuotient ℐ U)) (exceptionalChartS ℐ U)
      (blowupAtInfinityChartS ℐ U) (exceptionalIdealAtInfinity ℐ).subschemeι := by
  have : IsClosedImmersion (Spec.map (exceptionalChartQuotient ℐ U)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine isPullback_of_isClosedImmersion _ _ _ _ (exceptionalChartS_subschemeι ℐ U).symm ?_
  rw [Scheme.IdealSheafData.ker_subschemeι, comap_exceptionalIdealAtInfinity_chartS]

/-- The part of `E` over `D₊(S)` is an open immersion into `E`. -/
instance (U : X.affineOpens) : IsOpenImmersion (exceptionalChartS ℐ U) :=
  MorphismProperty.of_isPullback (isPullback_exceptionalChartS ℐ U) inferInstance

/-- The image of `Spec(Γ(X, U)[s][J/s] ⧸ (s)) ⟶ E` is the inverse image in `E` of the chart
`D₊(S)`. -/
theorem opensRange_exceptionalChartS (U : X.affineOpens) :
    (exceptionalChartS ℐ U).opensRange =
      (exceptionalIdealAtInfinity ℐ).subschemeι ⁻¹ᵁ (blowupAtInfinityChartS ℐ U).opensRange :=
  Proj.opensRange_eq_preimage_of_isPullback (isPullback_exceptionalChartS ℐ U)

end ExceptionalChart

/-! ### `E ∖ X'` over the affine opens of `X` -/

section Complement

/-- **`E ∖ X'`**, the open subscheme of the exceptional divisor off the strict transform. -/
abbrev exceptionalCompl : (exceptionalIdealAtInfinity ℐ).subscheme.Opens :=
  (exceptionalIdealAtInfinity ℐ).subschemeι ⁻¹ᵁ strictTransformComplAtInfinity ℐ

/-- The morphism `E ∖ X' ⟶ X`. -/
abbrev exceptionalComplToX : (exceptionalCompl ℐ).toScheme ⟶ X :=
  (exceptionalCompl ℐ).ι ≫ (exceptionalIdealAtInfinity ℐ).subschemeι ≫ blowupAtInfinityToBase ℐ

/-- The points of `D₊(S)` over `U` lie over the chart at infinity over `U`. -/
theorem blowupAtInfinityToLine_mem_of_mem_range_chartS (U : X.affineOpens)
    {w : blowupAtInfinity ℐ} (hw : w ∈ Set.range (blowupAtInfinityChartS ℐ U)) :
    blowupAtInfinityToLine ℐ w ∈ (infinityChartAffineOpen U).1 := by
  obtain ⟨z, rfl⟩ := hw
  rw [← Scheme.Hom.comp_apply, blowupAtInfinityChartS, blowupAtInfinityPolyChart_comp,
    Scheme.Hom.comp_apply]
  exact ⟨_, trivial, rfl⟩

/-- The points of `D₊(S)` over `U` lie off the strict transform. -/
theorem notMem_strictTransform_of_mem_range_chartS (U : X.affineOpens)
    {w : blowupAtInfinity ℐ} (hw : w ∈ Set.range (blowupAtInfinityChartS ℐ U)) :
    w ∉ (strictTransformIdealAtInfinity ℐ).support :=
  (mem_range_blowupAtInfinityChartS_iff_notMem ℐ U w
    (blowupAtInfinityToLine_mem_of_mem_range_chartS ℐ U hw)).mp hw

/-- **The part of `E ∖ X'` over `D₊(S)`**: `Spec(Γ(X, U)[s][J/s] ⧸ (s)) ⟶ E ∖ X'`. -/
def exceptionalComplChart (U : X.affineOpens) :
    Spec (exceptionalChartRing ℐ U) ⟶ (exceptionalCompl ℐ).toScheme :=
  IsOpenImmersion.lift (exceptionalCompl ℐ).ι (exceptionalChartS ℐ U) (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    change (exceptionalIdealAtInfinity ℐ).subschemeι (exceptionalChartS ℐ U z) ∈
      strictTransformComplAtInfinity ℐ
    rw [← Scheme.Hom.comp_apply, exceptionalChartS_subschemeι, Scheme.Hom.comp_apply]
    exact notMem_strictTransform_of_mem_range_chartS ℐ U ⟨_, rfl⟩)

/-- The part of `E ∖ X'` over `D₊(S)` followed by `E ∖ X' ⊆ E` is the part of `E` over
`D₊(S)`. -/
@[reassoc (attr := simp)]
theorem exceptionalComplChart_ι (U : X.affineOpens) :
    exceptionalComplChart ℐ U ≫ (exceptionalCompl ℐ).ι = exceptionalChartS ℐ U :=
  IsOpenImmersion.lift_fac _ _ _

/-- The part of `E ∖ X'` over `D₊(S)` is an open immersion into `E ∖ X'`. -/
instance (U : X.affineOpens) : IsOpenImmersion (exceptionalComplChart ℐ U) := by
  have : IsOpenImmersion (exceptionalComplChart ℐ U ≫ (exceptionalCompl ℐ).ι) := by
    rw [exceptionalComplChart_ι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (exceptionalCompl ℐ).ι

/-- The part of `E ∖ X'` over `D₊(S)` lies over `U`: its composite to `X` is `Spec` of the
structure map followed by the affine identification of `U`. -/
theorem exceptionalComplChart_toX (U : X.affineOpens) :
    exceptionalComplChart ℐ U ≫ exceptionalComplToX ℐ =
      Spec.map (CommRingCat.ofHom (Polynomial.C : Γ(X, U.1) →+* Polynomial Γ(X, U.1)) ≫
        CommRingCat.ofHom (algebraMap _ (infinityChartAlgebra (ℐ.ideal U))) ≫
          exceptionalChartQuotient ℐ U) ≫ U.2.fromSpec := by
  rw [exceptionalComplToX, exceptionalComplChart_ι_assoc, exceptionalChartS_subschemeι_assoc,
    blowupAtInfinityToBase, blowupAtInfinityChartS, blowupAtInfinityPolyChart_comp_assoc,
    infinityChartOver_comp, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]

/-- **`E ∖ X'` over `U` is the part of `E` over `D₊(S)`.** -/
theorem opensRange_exceptionalComplChart (U : X.affineOpens) :
    (exceptionalComplChart ℐ U).opensRange = exceptionalComplToX ℐ ⁻¹ᵁ U.1 := by
  ext e
  constructor
  · rintro ⟨z, rfl⟩
    show (exceptionalComplChart ℐ U ≫ exceptionalComplToX ℐ) z ∈ U.1
    rw [exceptionalComplChart_toX, Scheme.Hom.comp_apply]
    exact (IsAffineOpen.range_fromSpec (U.2 : IsAffineOpen U.1)).le ⟨_, rfl⟩
  · intro he
    set w := (exceptionalIdealAtInfinity ℐ).subschemeι ((exceptionalCompl ℐ).ι e) with hwdef
    have hwE : blowupAtInfinityToLine ℐ w ∈ ((infinityCentreIdeal ℐ).support :
        Set (relativeProjectiveLine X)) := by
      have h : w ∈ ((exceptionalIdealAtInfinity ℐ).support : Set _) := by
        rw [← Scheme.IdealSheafData.range_subschemeι]
        exact ⟨_, rfl⟩
      have h2 := Scheme.IdealSheafData.support_comap (infinityCentreIdeal ℐ)
        (blowupAtInfinityToLine ℐ)
      have h3 : w ∈ (((infinityCentreIdeal ℐ).comap (blowupAtInfinityToLine ℐ)).support :
          Set (blowupAtInfinity ℐ)) := h
      rw [h2] at h3
      exact h3
    have hD : blowupAtInfinityToLine ℐ w ∈ ((lineInfinityDivisor X).support :
        Set (relativeProjectiveLine X)) :=
      Scheme.IdealSheafData.support_antitone (lineInfinityDivisor_le_infinityCentreIdeal ℐ) hwE
    rw [coe_support_lineInfinityDivisor] at hD
    obtain ⟨x, hx⟩ := hD
    have hxU : x ∈ U.1 := by
      have h1 : exceptionalComplToX ℐ e = x := by
        show (relativeProjectiveLine X ↘ X) (blowupAtInfinityToLine ℐ w) = x
        rw [← hx, ← Scheme.Hom.comp_apply, lineInfinitySection_comp]
        rfl
      rw [← h1]
      exact he
    obtain ⟨y, hy⟩ := (IsAffineOpen.range_fromSpec (U.2 : IsAffineOpen U.1)).ge hxU
    have hwU : blowupAtInfinityToLine ℐ w ∈ (infinityChartAffineOpen U).1 := by
      refine ⟨Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : Γ(X, U.1)))) y,
        trivial, ?_⟩
      have := congrArg (fun φ => φ y) (congrArg (fun g => (g.base : _ → _))
        (specMap_evalZero_infinityChartOver U))
      simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at this
      show (infinityChartOver U) _ = blowupAtInfinityToLine ℐ w
      rw [this, hy, hx]
    have hwX' : w ∉ (strictTransformIdealAtInfinity ℐ).support := e.2
    have hwS := (mem_range_blowupAtInfinityChartS_iff_notMem ℐ U w hwU).mpr hwX'
    have hmem : (exceptionalCompl ℐ).ι e ∈ (exceptionalChartS ℐ U).opensRange := by
      rw [opensRange_exceptionalChartS]
      exact hwS
    obtain ⟨z, hz⟩ := hmem
    refine ⟨z, (exceptionalCompl ℐ).ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, exceptionalComplChart_ι, hz]

end Complement

/-! ### The fibre of the chart `D₊(S)` is the conormal algebra, naturally -/

section ConormalRing

open Polynomial

/-- The identification of the associated graded rings of two equal ideals. -/
def _root_.AssociatedGraded.gradedRingEquivOfEq {A : Type*} [CommRing A] {I I' : Ideal A}
    (h : I = I') : AssociatedGraded.gradedRing I ≃+* AssociatedGraded.gradedRing I' := by
  subst h
  exact RingEquiv.refl _

/-- The identification of the associated graded rings of two equal ideals is the map induced by
the identity of the ring. -/
theorem _root_.AssociatedGraded.gradedRingEquivOfEq_apply {A : Type*} [CommRing A]
    {I I' : Ideal A} (h : I = I') (z : AssociatedGraded.gradedRing I) :
    AssociatedGraded.gradedRingEquivOfEq h z =
      AssociatedGraded.gradedRingMapOfRingHom (RingHom.id A) (by rw [Ideal.map_id, h]) z := by
  subst h
  induction z using DirectSum.induction_on with
  | zero => rw [map_zero, map_zero]
  | of n x =>
    rw [AssociatedGraded.gradedRingMapOfRingHom_of]
    induction x using Quotient.inductionOn with
    | _ y => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

variable {A A' : Type*} [CommRing A] [CommRing A'] (f : A →+* A') {I : Ideal A} {I' : Ideal A'}
  (hI : I.map f ≤ I')

/-- The map of fibres `A[s][J/s] ⧸ (s) ⟶ A'[s][J'/s] ⧸ (s)` induced by `f`. -/
def infinityChartFibreMap :
    (infinityChartAlgebra I ⧸ infinityChartFibreIdeal I) →+*
      (infinityChartAlgebra I' ⧸ infinityChartFibreIdeal I') :=
  Ideal.quotientMap _ (infinityChartAlgebraMap f hI)
    (Ideal.map_le_iff_le_comap.mp (map_infinityChartFibreIdeal_le f hI))

/-- The map of fibres `A[s][J/s] ⧸ (s) ⟶ A'[s][J'/s] ⧸ (s)` on the class of an element. -/
theorem infinityChartFibreMap_mk (b : infinityChartAlgebra I) :
    infinityChartFibreMap f hI (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (infinityChartAlgebraMap f hI b) := rfl

/-- The identification of the conormal algebra with the fibre of `D₊(S)` is
`conormalToInfinityChartFibre`. -/
theorem conormalEquivInfinityChartFibre_apply' (J : Ideal A) (z : AssociatedGraded.gradedRing J) :
    conormalEquivInfinityChartFibre J z = conormalToInfinityChartFibre J z := rfl

/-- **The identification of the fibre of `D₊(S)` with the conormal algebra is natural in
`(A, I)`.** -/
theorem infinityChartFibreMap_conormalEquiv (z : AssociatedGraded.gradedRing I) :
    infinityChartFibreMap f hI (conormalEquivInfinityChartFibre I z) =
      conormalEquivInfinityChartFibre I' (AssociatedGraded.gradedRingMapOfRingHom f hI z) := by
  rw [conormalEquivInfinityChartFibre_apply', conormalEquivInfinityChartFibre_apply']
  induction z using DirectSum.induction_on with
  | zero =>
    rw [(conormalToInfinityChartFibre I).map_zero, (infinityChartFibreMap f hI).map_zero,
      (AssociatedGraded.gradedRingMapOfRingHom f hI).map_zero,
      (conormalToInfinityChartFibre I').map_zero]
  | of n x =>
    induction x using Quotient.inductionOn with
    | _ y =>
      rw [AssociatedGraded.gradedRingMapOfRingHom_of, conormalToInfinityChartFibre_of,
        conormalToInfinityChartFibre_of]
      show infinityChartFibreMap f hI (conormalPieceToInfinityChartFibre I n
          (AssociatedGraded.mk I n y)) =
        conormalPieceToInfinityChartFibre I' n
          (AssociatedGraded.pieceMapOfRingHom f hI n (AssociatedGraded.mk I n y))
      rw [AssociatedGraded.pieceMapOfRingHom_mk, conormalPieceToInfinityChartFibre_mk,
        conormalPieceToInfinityChartFibre_mk, infinityChartClass, infinityChartClass,
        infinityChartFibreMap_mk, infinityChartAlgebraMap_infinityChartMk]
      congr 1
      exact infinityChartMk_congr rfl (by simp)
  | add x y hx hy =>
    rw [(conormalToInfinityChartFibre I).map_add, (infinityChartFibreMap f hI).map_add, hx, hy,
      (AssociatedGraded.gradedRingMapOfRingHom f hI).map_add,
      (conormalToInfinityChartFibre I').map_add]

/-- **The degree-zero part of the conormal algebra is the image of the base.** -/
theorem conormalEquivInfinityChartFibre_gradeZeroMk (a : A) :
    conormalEquivInfinityChartFibre I
        (DirectSum.of (fun k => AssociatedGraded.piece (M := A) I k) 0
          (AssociatedGraded.gradeZeroMk I a)) =
      Ideal.Quotient.mk _ (algebraMap A[X] (infinityChartAlgebra I) (C a)) := by
  rw [conormalEquivInfinityChartFibre_apply', conormalToInfinityChartFibre_of]
  show conormalPieceToInfinityChartFibre I 0 (AssociatedGraded.mk I 0 _) = _
  rw [conormalPieceToInfinityChartFibre_mk, infinityChartClass]
  congr 1

end ConormalRing

/-! ### `E ∖ X'` over `U` is the chart of `C_ZX` over `U` -/

section ComplementCharts

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The restriction of a closed immersion `i` to `i⁻¹U ⟶ U` is a closed immersion. -/
instance isClosedImmersion_resLE_of_isClosedImmersion (U : X.affineOpens) :
    IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl) := by
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  infer_instance

/-- On an affine open `U` of `X`, the kernel ideal of the closed immersion `i` on the chart is the
ideal of `U` cut out by the ideal sheaf `ker i` of `i`. -/
theorem chartIdeal_eq_ker_ideal (U : X.affineOpens) :
    Stacks.Conormal.chartIdeal i U = i.ker.ideal U :=
  (Scheme.Hom.ker_apply i U).symm

/-- **The coordinate ring of `E ∩ D₊(S)` over `U` is the ring of sections of the conormal algebra
over `Z ∩ U`**: `Γ(X, U)[s][J/s] ⧸ (s) ≅ Gr_{i.ker(U)} Γ(X, U) ≅ Γ(Z ∩ U, 𝒞_{Z/X,*})`. -/
def exceptionalChartSectionsEquiv (U : X.affineOpens) :
    (infinityChartAlgebra (i.ker.ideal U) ⧸ infinityChartFibreIdeal (i.ker.ideal U)) ≃+*
      (Stacks.Conormal.conormalAlgebraSheaf i).right.obj.obj
        (op (i ⁻¹ᵁ U.1)) :=
  (conormalEquivInfinityChartFibre (i.ker.ideal U)).symm.trans
    ((AssociatedGraded.gradedRingEquivOfEq (chartIdeal_eq_ker_ideal i U).symm).trans
      (Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance))

/-- On the image of `z ∈ Gr_{(ker i)(U)} Γ(X, U)` under `conormalEquivInfinityChartFibre`,
`exceptionalChartSectionsEquiv` is `conormalAlgebraSheafSectionsEquiv` applied to `z` read in the
associated graded ring of the chart ideal. -/
theorem exceptionalChartSectionsEquiv_conormalEquiv (U : X.affineOpens)
    (z : AssociatedGraded.gradedRing (i.ker.ideal U)) :
    exceptionalChartSectionsEquiv i U (conormalEquivInfinityChartFibre (i.ker.ideal U) z) =
      Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance
        (AssociatedGraded.gradedRingMapOfRingHom (RingHom.id _)
          (by rw [Ideal.map_id, chartIdeal_eq_ker_ideal]) z) := by
  show Stacks.Conormal.conormalAlgebraSheafSectionsEquiv i U inferInstance
      (AssociatedGraded.gradedRingEquivOfEq (chartIdeal_eq_ker_ideal i U).symm
        ((conormalEquivInfinityChartFibre (i.ker.ideal U)).symm
          (conormalEquivInfinityChartFibre (i.ker.ideal U) z))) = _
  rw [RingEquiv.symm_apply_apply, AssociatedGraded.gradedRingEquivOfEq_apply]

/-- `exceptionalChartSectionsEquiv` as an isomorphism of commutative rings. -/
def exceptionalChartSectionsIso (U : X.affineOpens) :
    exceptionalChartRing i.ker U ≅
      (conormalSituation i).algebra.sections (subschemeAffineOpen i U).1 :=
  (exceptionalChartSectionsEquiv i U).toCommRingCatIso

/-- **The chart of `E ∖ X'` over `U`**, with source the chart of `C_ZX` over `U`. -/
def exceptionalComplChartT (U : X.affineOpens) :
    normalConeChartSource i U ⟶ (exceptionalCompl i.ker).toScheme :=
  Spec.map (exceptionalChartSectionsIso i U).hom ≫ exceptionalComplChart i.ker U

/-- The chart of `E ∖ X'` over `U` is an open immersion. -/
instance (U : X.affineOpens) : IsOpenImmersion (exceptionalComplChartT i U) := by
  dsimp only [exceptionalComplChartT]
  infer_instance

/-- The image of the chart of `E ∖ X'` over `U` is the part of `E ∖ X'` lying over `U`. -/
theorem opensRange_exceptionalComplChartT (U : X.affineOpens) :
    (exceptionalComplChartT i U).opensRange = exceptionalComplToX i.ker ⁻¹ᵁ U.1 := by
  rw [← opensRange_exceptionalComplChart]
  ext x
  show x ∈ Set.range (exceptionalComplChartT i U) ↔ x ∈ Set.range (exceptionalComplChart i.ker U)
  rw [exceptionalComplChartT, Stacks.Chow.range_isIso_comp]

/-- The map `Γ(X, U) ⟶ Γ(X, U)[s][J/s] ⧸ (s)` followed by the identification with the sections of
the conormal algebra over `Z ∩ U` is `Γ(X, U) ⟶ Γ(Z ∩ U, 𝒪_Z)` followed by the structure map of
the conormal algebra. -/
theorem exceptionalChartSectionsEquiv_structure (U : X.affineOpens) :
    (CommRingCat.ofHom (Polynomial.C : Γ(X, U.1) →+* Polynomial Γ(X, U.1)) ≫
        CommRingCat.ofHom (algebraMap _ (infinityChartAlgebra (i.ker.ideal U))) ≫
          exceptionalChartQuotient i.ker U) ≫
        (exceptionalChartSectionsIso i U).hom =
      i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl ≫
        (conormalSituation i).algebra.hom.hom.app (op (subschemeAffineOpen i U).1) := by
  apply CommRingCat.hom_ext
  refine RingHom.ext fun r => ?_
  show exceptionalChartSectionsEquiv i U (Ideal.Quotient.mk _ (algebraMap _ _ (Polynomial.C r))) =
    _
  rw [← conormalEquivInfinityChartFibre_gradeZeroMk, exceptionalChartSectionsEquiv_conormalEquiv,
    AssociatedGraded.gradedRingMapOfRingHom_of]
  have h := Stacks.Conormal.conormalAlgebraSheafSectionsEquiv_of_gradeZeroMk i U
    inferInstance r
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · rw [Scheme.Hom.appLE_eq_app]
    rfl

/-- **The chart of `E ∖ X'` over `U` lies over `U` as the chart of `C_ZX` does.** -/
theorem exceptionalComplChartT_toX (U : X.affineOpens) :
    exceptionalComplChartT i U ≫ exceptionalComplToX i.ker = normalConeChartProj i U ≫ U.1.ι := by
  have hL : exceptionalComplChartT i U ≫ exceptionalComplToX i.ker =
      Spec.map ((conormalSituation i).algebra.hom.hom.app (op (subschemeAffineOpen i U).1)) ≫
        Spec.map (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl) ≫ U.2.fromSpec := by
    rw [exceptionalComplChartT, Category.assoc, exceptionalComplChart_toX, ← Category.assoc,
      ← Spec.map_comp]
    rw [exceptionalChartSectionsEquiv_structure]
    exact (congrArg (· ≫ U.2.fromSpec) (Spec.map_comp _ _)).trans (Category.assoc _ _ _)
  have hR : normalConeChartProj i U ≫ U.1.ι =
      Spec.map ((conormalSituation i).algebra.hom.hom.app (op (subschemeAffineOpen i U).1)) ≫
        (subschemeAffineOpen i U).2.fromSpec ≫ i := by
    refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (Stacks.RelativeSpec.specSectionsToOpen (conormalSituation i)
      (subschemeAffineOpen i U) ≫ ·) (morphismRestrict_ι i U.1)).trans ?_
    exact Category.assoc _ _ _
  exact hL.trans ((congrArg (_ ≫ ·) (IsAffineOpen.SpecMap_appLE_fromSpec i U.2
    (subschemeAffineOpen i U).2 le_rfl)).trans hR.symm)

end ComplementCharts

/-! ### The charts of `E ∖ X'` are compatible with restriction -/

section ComplementNaturality

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The map of associated graded rings induced by a composite of ring maps is the composite of the
induced maps. -/
theorem _root_.AssociatedGraded.gradedRingMapOfRingHom_comp_apply {A B D : Type*} [CommRing A]
    [CommRing B] [CommRing D] (f : A →+* B) (g : B →+* D) {I : Ideal A} {I' : Ideal B}
    {I'' : Ideal D} (h₁ : I.map f ≤ I') (h₂ : I'.map g ≤ I'') (h₃ : I.map (g.comp f) ≤ I'')
    (z : AssociatedGraded.gradedRing I) :
    AssociatedGraded.gradedRingMapOfRingHom g h₂ (AssociatedGraded.gradedRingMapOfRingHom f h₁ z) =
      AssociatedGraded.gradedRingMapOfRingHom (g.comp f) h₃ z := by
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of n x =>
    rw [AssociatedGraded.gradedRingMapOfRingHom_of, AssociatedGraded.gradedRingMapOfRingHom_of,
      AssociatedGraded.gradedRingMapOfRingHom_of]
    induction x using Quotient.inductionOn with
    | _ y => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The restriction map of the conormal algebra sheaf from `Z ∩ U` to `Z ∩ V`. -/
abbrev conormalSectionsRestrict {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    (conormalSituation i).algebra.sections (subschemeAffineOpen i U).1 ⟶
      (conormalSituation i).algebra.sections (subschemeAffineOpen i V).1 :=
  (conormalSituation i).algebra.right.obj.map (homOfLE (subschemeAffineOpen_mono i h)).op

/-- The map of fibres of the charts `D₊(S)` from `U` to `V`. -/
abbrev exceptionalChartRestrict {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    exceptionalChartRing ℐ U ⟶ exceptionalChartRing ℐ V :=
  CommRingCat.ofHom (infinityChartFibreMap (affineRestrict h) (map_ideal_infinityChart_le ℐ h))

/-- **The identification of the fibre of `D₊(S)` with the sections of the conormal algebra
commutes with restriction.** -/
theorem exceptionalChartSectionsIso_naturality {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    (exceptionalChartSectionsIso i U).hom ≫ conormalSectionsRestrict i h =
      exceptionalChartRestrict i.ker h ≫ (exceptionalChartSectionsIso i V).hom := by
  apply CommRingCat.hom_ext
  refine RingHom.ext fun w => ?_
  obtain ⟨z, rfl⟩ := (conormalEquivInfinityChartFibre (i.ker.ideal U)).surjective w
  show (conormalSectionsRestrict i h).hom (exceptionalChartSectionsEquiv i U
      (conormalEquivInfinityChartFibre (i.ker.ideal U) z)) =
    exceptionalChartSectionsEquiv i V (infinityChartFibreMap (affineRestrict h)
      (map_ideal_infinityChart_le i.ker h) (conormalEquivInfinityChartFibre (i.ker.ideal U) z))
  rw [infinityChartFibreMap_conormalEquiv, exceptionalChartSectionsEquiv_conormalEquiv,
    exceptionalChartSectionsEquiv_conormalEquiv]
  refine (Stacks.Conormal.conormalAlgebraSheafSectionsEquiv_restrict i U
    inferInstance V inferInstance h _).trans ?_
  congr 1
  rw [AssociatedGraded.gradedRingMapOfRingHom_comp_apply,
    AssociatedGraded.gradedRingMapOfRingHom_comp_apply]
  · rfl
  · rw [← Ideal.map_map, Ideal.map_id]
    exact (map_ideal_infinityChart_le i.ker h).trans (chartIdeal_eq_ker_ideal i V).ge

/-- The charts of `E ∖ X'` over `D₊(S)` are compatible with restriction. -/
theorem specMap_exceptionalChartRestrict_exceptionalComplChart {U V : X.affineOpens}
    (h : V.1 ≤ U.1) :
    Spec.map (exceptionalChartRestrict ℐ h) ≫ exceptionalComplChart ℐ U =
      exceptionalComplChart ℐ V := by
  rw [← cancel_mono ((exceptionalCompl ℐ).ι ≫ (exceptionalIdealAtInfinity ℐ).subschemeι),
    Category.assoc, exceptionalComplChart_ι_assoc, exceptionalComplChart_ι_assoc,
    exceptionalChartS_subschemeι, exceptionalChartS_subschemeι, ← Category.assoc,
    ← Spec.map_comp, ← specMap_infinityChartAlgebraMap_blowupAtInfinityChartS ℐ h,
    ← Category.assoc, ← Spec.map_comp]
  rfl

/-- **The charts of `E ∖ X'` with source the charts of `C_ZX` are compatible with
restriction.** -/
theorem specMap_conormalSectionsRestrict_exceptionalComplChartT {U V : X.affineOpens}
    (h : V.1 ≤ U.1) :
    Spec.map (conormalSectionsRestrict i h) ≫ exceptionalComplChartT i U =
      exceptionalComplChartT i V := by
  rw [exceptionalComplChartT, exceptionalComplChartT, ← Category.assoc, ← Spec.map_comp,
    exceptionalChartSectionsIso_naturality, Spec.map_comp, Category.assoc,
    specMap_exceptionalChartRestrict_exceptionalComplChart]

end ComplementNaturality

/-! ### `C_ZX ≅ E ∖ X'` over `X` -/

section Iso

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- The structure morphisms of the charts of `C_ZX` over affine opens `V ≤ U` of `X` are
compatible with restriction. -/
theorem normalConeChartProj_naturality {U V : X.affineOpens} (h : V.1 ≤ U.1) :
    Spec.map (conormalSectionsRestrict i h) ≫ normalConeChartProj i U =
      normalConeChartProj i V ≫ X.homOfLE h :=
  spec_map_restrict_comp_normalConeChartProj i h

/-- **The gluing datum of `C_ZX` over the affine opens of `X`** (Stacks 01LH): the charts of
`C_ZX` over the affine opens of `X` with the spectra of the restriction maps of the conormal
algebra. -/
abbrev normalConeBasisGluingData : Scheme.BasisGluingData X X.affineOpens where
  obj U := normalConeChartSource i U
  proj U := normalConeChartProj i U
  res h := Spec.map (conormalSectionsRestrict i h)
  isPullback_res {V U} h := by
    refine IsPullback.of_right (h₁₂ := normalConeChart i U) (h₂₂ := U.1.ι)
      (v₁₃ := normalConeToX i) ?_ (normalConeChartProj_naturality i h)
      (isPullback_normalConeChart i U).flip
    rw [normalConeChart_naturality i h, Scheme.homOfLE_ι]
    exact (isPullback_normalConeChart i V).flip
  res_trans {W V U} hWV hVU := by
    rw [← Spec.map_comp]
    congr 1
    rw [← Functor.map_comp]
    rfl

/-- `C_ZX` as a solution of its gluing problem over the affine opens of `X`. -/
abbrev normalConeGluing : (normalConeBasisGluingData i).Gluing where
  base := Stacks.Conormal.normalCone i
  toBase := normalConeToX i
  chart := normalConeChart i
  isPullback_chart := isPullback_normalConeChart i
  res_comp_chart h := normalConeChart_naturality i h

/-- **`E ∖ X'` as a solution of the gluing problem of `C_ZX`**: over each affine open `U` of `X`
the part of `E ∖ X'` over `U` is the chart `D₊(S) ∩ E`, whose coordinate ring is the ring of
sections of the conormal algebra over `Z ∩ U`. -/
abbrev exceptionalComplGluing : (normalConeBasisGluingData i).Gluing where
  base := (exceptionalCompl i.ker).toScheme
  toBase := exceptionalComplToX i.ker
  chart := exceptionalComplChartT i
  isPullback_chart U := by
    have : IsOpenImmersion (exceptionalComplChartT i U) := inferInstance
    exact IsOpenImmersion.isPullback (normalConeChartProj i U) (exceptionalComplChartT i U)
      U.1.ι (exceptionalComplToX i.ker) (exceptionalComplChartT_toX i U) (by
        rw [Scheme.Opens.opensRange_ι, opensRange_exceptionalComplChartT])
  res_comp_chart h := specMap_conormalSectionsRestrict_exceptionalComplChartT i h

/-- **`C_ZX ≅ E ∖ X'`**, as schemes over `X`. -/
def normalConeIsoExceptionalCompl :
    Stacks.Conormal.normalCone i ≅ (exceptionalCompl i.ker).toScheme :=
  (normalConeGluing i).isoOfGluing X.isBasis_affineOpens (exceptionalComplGluing i)

/-- The isomorphism `C_ZX ≅ E ∖ X'` carries the chart of `C_ZX` over `U` to the chart of
`E ∖ X'` over `U`. -/
@[reassoc (attr := simp)]
theorem normalConeChart_normalConeIsoExceptionalCompl_hom (U : X.affineOpens) :
    normalConeChart i U ≫ (normalConeIsoExceptionalCompl i).hom = exceptionalComplChartT i U :=
  (normalConeGluing i).chart_comp_desc X.isBasis_affineOpens (exceptionalComplGluing i) U

/-- The isomorphism `C_ZX ≅ E ∖ X'` lies over `X`. -/
@[reassoc (attr := simp)]
theorem normalConeIsoExceptionalCompl_hom_toX :
    (normalConeIsoExceptionalCompl i).hom ≫ exceptionalComplToX i.ker = normalConeToX i :=
  (normalConeGluing i).desc_comp_toBase X.isBasis_affineOpens (exceptionalComplGluing i)

end Iso

/-! ### Stacks 0FBH -/

section Tag

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The open immersion `C_ZX ⟶ E` of Stacks 0FBH**: the normal cone `C_ZX = Spec_Z(𝒞_{Z/X,*})`
identified with the open subscheme `E ∖ X'` of the exceptional divisor `E` of the blowup at
infinity. -/
def normalConeToExceptionalDivisor :
    Stacks.Conormal.normalCone i ⟶ (exceptionalIdealAtInfinity i.ker).subscheme :=
  (normalConeIsoExceptionalCompl i).hom ≫ (exceptionalCompl i.ker).ι

/-- `C_ZX ⟶ E` is an open immersion. -/
instance : IsOpenImmersion (normalConeToExceptionalDivisor i) := by
  dsimp only [normalConeToExceptionalDivisor]
  infer_instance

/-- The image of `C_ZX ⟶ E` is `E ∖ X'`. -/
theorem opensRange_normalConeToExceptionalDivisor :
    (normalConeToExceptionalDivisor i).opensRange = exceptionalCompl i.ker := by
  show ((normalConeIsoExceptionalCompl i).hom ≫ (exceptionalCompl i.ker).ι).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]

/-- `C_ZX ⟶ E ⟶ W ⟶ X` is `C_ZX ⟶ Z ⟶ X`. -/
theorem normalConeToExceptionalDivisor_comp_toBase :
    normalConeToExceptionalDivisor i ≫ (exceptionalIdealAtInfinity i.ker).subschemeι ≫
        blowupAtInfinityToBase i.ker =
      Stacks.Conormal.normalConeToBase i ≫ i := by
  rw [normalConeToExceptionalDivisor, Category.assoc]
  exact normalConeIsoExceptionalCompl_hom_toX i

/-- Let `Z ⊆ X` be the closed subscheme of a quasi-coherent ideal `i.ker`, let `W` be the blowup
of `𝐏¹_X` in `∞(Z)`, with exceptional divisor `E` and strict transform `X'` of `X`. Then

  `E ∖ X' = E ∖ (X' ∩ E) = Spec_Z(𝒞_{Z/X,*}) = C_ZX`:

the morphism `normalConeToExceptionalDivisor : C_ZX ⟶ E` is an open immersion whose image is
`E ∖ (X' ∩ E)`, which is the inverse image `E ∖ X'` of `W ∖ X'`, and it is a morphism over `X`
(so the identification is one of schemes over `Z`). -/
@[stacks 0FBH "E ∖ X' = E ∖ (X' ∩ E) = Spec_Z(C_{Z/X,*}) = C_ZX: an open immersion C_ZX → E \
with image E ∖ (X' ∩ E) = E ∖ X', over X"]
theorem normalConeToExceptionalDivisor_spec :
    IsOpenImmersion (normalConeToExceptionalDivisor i) ∧
      (normalConeToExceptionalDivisor i).opensRange =
        (strictTransformIdealOnExceptional i.ker).support.compl ∧
      (strictTransformIdealOnExceptional i.ker).support.compl =
        (exceptionalIdealAtInfinity i.ker).subschemeι ⁻¹ᵁ
          (strictTransformIdealAtInfinity i.ker).support.compl ∧
      normalConeToExceptionalDivisor i ≫ (exceptionalIdealAtInfinity i.ker).subschemeι ≫
          blowupAtInfinityToBase i.ker =
        Stacks.Conormal.normalConeToBase i ≫ i :=
  ⟨inferInstance, (opensRange_normalConeToExceptionalDivisor i).trans
      (support_compl_strictTransformIdealOnExceptional i.ker).symm,
    support_compl_strictTransformIdealOnExceptional i.ker,
    normalConeToExceptionalDivisor_comp_toBase i⟩

variable {S : Scheme.{u}} (f : X ⟶ S)

/-- **The open immersion `j : C_ZX ⟶ W_∞` of Stacks 0FBH**, into the fibre at infinity of the
blowup at infinity read as a modification of `X ×_S 𝐏¹_S` (the fibre on which the class of
Stacks 0F9J lives): the identification `C_ZX ≅ E ∖ X'` followed by `E ∖ X' = W_∞ ∖ X' ⊆ W_∞`. -/
def normalConeToFibreAtInfinity :
    Stacks.Conormal.normalCone i ⟶
      modificationFibreAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f) :=
  (normalConeIsoExceptionalCompl i).hom ≫ exceptionalComplToModificationFibreAtInfinity i.ker f

/-- `j : C_ZX ⟶ W_∞` is an open immersion. -/
instance : IsOpenImmersion (normalConeToFibreAtInfinity i f) := by
  dsimp only [normalConeToFibreAtInfinity]
  infer_instance

/-- The image of `j : C_ZX ⟶ W_∞` is `W_∞ ∖ X'`. -/
theorem opensRange_normalConeToFibreAtInfinity :
    (normalConeToFibreAtInfinity i f).opensRange =
      modificationFibreAtInfinityComplStrictTransform i.ker f := by
  show ((normalConeIsoExceptionalCompl i).hom ≫
    exceptionalComplToModificationFibreAtInfinity i.ker f).opensRange = _
  rw [Scheme.Hom.opensRange_comp_of_isIso,
    opensRange_exceptionalComplToModificationFibreAtInfinity]

/-- `j : C_ZX ⟶ W_∞` factors through the exceptional divisor: `j` followed by `W_∞ ⟶ W` is
`C_ZX ⟶ E ⟶ W`. -/
theorem normalConeToFibreAtInfinity_inclusion :
    normalConeToFibreAtInfinity i f ≫
        modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f) =
      normalConeToExceptionalDivisor i ≫ (exceptionalIdealAtInfinity i.ker).subschemeι := by
  rw [normalConeToFibreAtInfinity, normalConeToExceptionalDivisor, Category.assoc,
    exceptionalComplToModificationFibreAtInfinity_inclusion, Category.assoc]

/-- `j : C_ZX ⟶ W_∞` lies over `X`: `C_ZX ⟶ W_∞ ⟶ X` is `C_ZX ⟶ Z ⟶ X`. -/
theorem normalConeToFibreAtInfinity_comp_projection :
    normalConeToFibreAtInfinity i f ≫
        modificationProjectionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f) =
      Stacks.Conormal.normalConeToBase i ≫ i := by
  rw [modificationProjectionAtInfinity, ← Category.assoc, normalConeToFibreAtInfinity_inclusion,
    modificationProjection_blowupAtInfinityToProjectiveLineProduct, Category.assoc,
    normalConeToExceptionalDivisor_comp_toBase]

/-- The morphism `j : C_ZX ⟶ W_∞` of Stacks 0FBK is an open immersion with image `W_∞ ∖ X'`, it
factors through the exceptional divisor as `C_ZX ≅ E ∖ X' ⊆ E`, and it lies over `X`:
`C_ZX ⟶ W_∞ ⟶ X` is `C_ZX ⟶ Z ⟶ X`. -/
@[stacks 0FBH "the open immersion j : C_ZX → W_∞ of 0FBK: image W_∞ ∖ X', through E, over X"]
theorem normalConeToFibreAtInfinity_spec :
    IsOpenImmersion (normalConeToFibreAtInfinity i f) ∧
      (normalConeToFibreAtInfinity i f).opensRange =
        modificationFibreAtInfinityComplStrictTransform i.ker f ∧
      normalConeToFibreAtInfinity i f ≫
          modificationInclusionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f) =
        normalConeToExceptionalDivisor i ≫ (exceptionalIdealAtInfinity i.ker).subschemeι ∧
      normalConeToFibreAtInfinity i f ≫
          modificationProjectionAtInfinity f (blowupAtInfinityToProjectiveLineProduct i.ker f) =
        Stacks.Conormal.normalConeToBase i ≫ i :=
  ⟨inferInstance, opensRange_normalConeToFibreAtInfinity i f,
    normalConeToFibreAtInfinity_inclusion i f, normalConeToFibreAtInfinity_comp_projection i f⟩

end Tag

end Stacks.Chow

end
