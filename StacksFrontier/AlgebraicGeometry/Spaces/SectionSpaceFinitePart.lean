module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SurjectiveEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteAffineProper
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeFiniteFlat
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.AlgebraicSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralFiniteTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SectionOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiLocallyQuasiSeparatedTfae

/-!
# The space of sections as a locus in the finite part

Let `Z ⟶ U` be a finite morphism of the big fppf site of `U` and let `w : W ⟶ h_Z` be a
morphism of presheaves on that site with `W` an algebraic space and `w` étale. A section of
`W_T ⟶ Z_T` over a test object `T / U` is a morphism `σ : T × Z ⟶ W` over `Z`; such a `σ` is a
section of the base change `T ×_U W ⟶ T × Z` of `w`, hence an open immersion, and its image is
an open subspace of `T ×_U W` isomorphic to `T × Z` and therefore finite over `T`. So every
section determines a pair of Stacks 04PC for the structure morphism `W ⟶ U`, that is a section
of the finite part `(W/U)_fin`.

This file carries out that construction and records its two properties: the pair attached to a
restricted section is the base change of the pair attached to the section, and a section is
determined by its pair.

## Main definitions

* `AlgebraicGeometry.Space.sectionLift`: a section `σ` of `W_T ⟶ Z_T`, read as a morphism
  `T × Z ⟶ T ×_U W`.
* `AlgebraicGeometry.Space.sectionPair`: the pair of Stacks 04PC attached to `σ`.

## Main results

* `AlgebraicGeometry.Space.isEtale_of_isPullback_of_isAlgebraicSpace`: étaleness of a morphism
  of algebraic spaces passes to its base change along an arbitrary morphism of presheaves.
* `AlgebraicGeometry.Space.isOpenImmersion_sectionLift`: `sectionLift σ` is an open immersion.
* `AlgebraicGeometry.Space.isBaseChange_sectionPair`: the pair attached to a restriction of `σ`
  is the base change of the pair attached to `σ`.
* `AlgebraicGeometry.Space.sectionPair_injective`: a section is determined by its pair.

## Implementation notes

The target of the structure morphism `W ⟶ U` is the terminal presheaf rather than the presheaf
represented by the final object `U / U` of the site, so that the structure morphism is literally
`CategoryTheory.Limits.terminal.from` and the ambient fibre product of a pair is literally
`CategoryTheory.Limits.pullback (terminal.from _) (terminal.from _)`. The terminal presheaf is
an algebraic space by `AlgebraicGeometry.Space.isAlgebraicSpace_terminal`.

The finiteness of `Z ⟶ U` is used only through finiteness of the projection `T × Z ⟶ T`, and no
flatness or local freeness of it is needed here.

## References

* [Stacks Project, Tag 03KP](https://stacks.math.columbia.edu/tag/03KP)
* [Stacks Project, Tag 03ZQ](https://stacks.math.columbia.edu/tag/03ZQ)
* [Stacks Project, Tag 03ZS](https://stacks.math.columbia.edu/tag/03ZS)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### Base change of étaleness along an arbitrary morphism -/

/-- **Étaleness passes to a base change along an arbitrary morphism of presheaves.** Étaleness
of morphisms of schemes is stable under base change and composition, holds for the étale
morphisms and descends along a surjective étale morphism of sources, so the every-étale-chart
form of étaleness is inherited by an arbitrary base change. -/
theorem isEtale_of_isPullback_of_isAlgebraicSpace (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {A C D E : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : A ⟶ C} {b : A ⟶ D} {g : C ⟶ E} {f : D ⟶ E} (sq : IsPullback a b g f)
    (hA : IsAlgebraicSpace B S hS A) (hC : IsAlgebraicSpace B S hS C)
    (hD : IsAlgebraicSpace B S hS D) (hE : IsAlgebraicSpace B S hS E)
    (hf : IsEtale B S hS f) : IsEtale B S hS a :=
  (isEtale_iff_holdsOnEveryEtaleChart B S hS hA hC a).2
    (holdsOnEveryEtaleChart_of_isPullback_of_descent B S hS
      AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
      ⟨fun f g hf hg => by have := hf; have := hg; infer_instance⟩ (fun _ hi => hi)
      (fun α k hα hαet h => by
        have := hα
        have := hαet
        have := h
        exact Stacks.Etale.etale_of_comp_surjective_etale α k)
      sq hD hE ((isEtale_iff_holdsOnEveryEtaleChart B S hS hD hE f).1 hf))

/-! ### The terminal algebraic space and the structure morphisms -/

variable (B : BigFppfSite.{u}) (U : Scheme.{u}) (hU : B.Contains U)

/-- Pullbacks of presheaves on `BigFppfOver B U hU`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_SectionSpaceFinitePart :
    HasPullbacks ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_SectionSpaceFinitePart
    {X Y Z : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_SectionSpaceFinitePart B U hU).has_limit _

/-- The terminal presheaf on the big fppf site of `U`, as an algebraic space over `U`. -/
noncomputable def terminalPresheafSpace : AlgebraicSpaces B U hU :=
  ⟨⊤_ ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u), isAlgebraicSpace_terminal B U hU⟩

/-- The structure morphism of an algebraic space over `U` to the terminal presheaf. -/
noncomputable def toTerminalPresheaf {X : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B U hU X) :
    (⟨X, hX⟩ : AlgebraicSpaces B U hU) ⟶ terminalPresheafSpace B U hU :=
  ObjectProperty.homMk (terminal.from X)

/-- The underlying morphism of presheaves of the structure morphism to the terminal presheaf is
the canonical morphism to the terminal presheaf. -/
@[simp]
theorem toTerminalPresheaf_hom {X : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B U hU X) :
    (toTerminalPresheaf B U hU hX).hom = terminal.from X :=
  rfl

/-- The structure morphism of an object of the site to the terminal presheaf. -/
noncomputable def schemeToTerminalPresheaf (T : BigFppfOver B U hU) :
    schemeSpace T ⟶ terminalPresheafSpace B U hU :=
  ObjectProperty.homMk (terminal.from (yoneda.obj T))

/-- The underlying morphism of presheaves of `schemeToTerminalPresheaf`. -/
@[simp]
theorem schemeToTerminalPresheaf_hom (T : BigFppfOver B U hU) :
    (schemeToTerminalPresheaf B U hU T).hom = terminal.from (yoneda.obj T) :=
  rfl

/-! ### Finiteness of the projection `T × Z ⟶ T` -/

section Finiteness

variable {B U hU}

/-- The product of two representable presheaves on the big fppf site of `U` is an algebraic
space: the Yoneda embedding preserves the binary product, which the site has. -/
theorem isAlgebraicSpace_yoneda_prod_yoneda (T Z : BigFppfOver B U hU) :
    IsAlgebraicSpace B U hU (yoneda.obj T ⨯ yoneda.obj Z) :=
  haveI : HasBinaryProducts (BigFppfOver B U hU) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  (isAlgebraicSpace_yoneda B U hU (T ⨯ Z)).of_iso (PreservesLimitPair.iso yoneda T Z)

/-- The structure morphism `h_Z ⟶ U` of an object of the site, as a morphism to the terminal
presheaf, is finite as soon as the underlying morphism of schemes is. -/
theorem isFinite_terminal_from_yoneda (Z : BigFppfOver B U hU)
    (hZ : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsFinite B U hU (terminal.from (yoneda.obj Z)) := by
  set O : BigFppfOver B U hU := Over.mk (𝟙 (B.obj hU)) with hO
  set τ : Z ⟶ O := Over.homMk Z.hom (Category.comp_id _) with hτ
  have hτmap : _root_.AlgebraicGeometry.IsFinite
      ((BigFppfOver.toScheme B U hU).map τ) := hZ
  have hPbc : MorphismProperty.IsStableUnderBaseChange
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u}) := inferInstance
  have hpres := presheaf_yoneda_map_of_inverseImage B U hU hPbc τ hτmap
  have hterm : IsTerminal (yoneda.obj O) :=
    (Over.mkIdTerminal (X := B.obj hU)).isTerminalObj yoneda _
  set e : yoneda.obj O ≅ ⊤_ ((BigFppfOver B U hU)ᵒᵖ ⥤ Type u) :=
    hterm.uniqueUpToIso terminalIsTerminal with he
  have hpost := MorphismProperty.RespectsIso.postcomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B U hU))) e.hom (yoneda.map τ) hpres
  rw [show yoneda.map τ ≫ e.hom = terminal.from (yoneda.obj Z) from terminal.hom_ext _ _] at hpost
  exact (isFinite_iff_representable B U hU _ (isAlgebraicSpace_yoneda B U hU Z)
    (isAlgebraicSpace_terminal B U hU)).2 ⟨hpost.rep, hpost⟩

/-- The first projection `T × Z ⟶ T` is finite as soon as `Z ⟶ U` is: it is the base change of
the structure morphism of `Z` along that of `T`. -/
theorem isFinite_prod_fst (T Z : BigFppfOver B U hU)
    (hZ : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom)) :
    IsFinite B U hU (prod.fst : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj T) :=
  isFinite_of_isPullback B U hU
    (IsPullback.of_hasBinaryProduct' (yoneda.obj T) (yoneda.obj Z)).flip
    (isFinite_terminal_from_yoneda Z hZ)

end Finiteness

/-! ### The pair of Stacks 04PC attached to a section -/

section SectionPair

variable {B U hU}
variable {Z : BigFppfOver B U hU} {W : (BigFppfOver B U hU)ᵒᵖ ⥤ Type u}

/-- The base change `T ×_U W ⟶ T × Z` of `w : W ⟶ h_Z` along the projection `T × Z ⟶ h_Z`. -/
noncomputable def sectionAmbientProjection (T : BigFppfOver B U hU) (w : W ⟶ yoneda.obj Z) :
    pullback (terminal.from (yoneda.obj T)) (terminal.from W) ⟶
      yoneda.obj T ⨯ yoneda.obj Z :=
  prod.lift (pullback.fst (terminal.from (yoneda.obj T)) (terminal.from W))
    (pullback.snd (terminal.from (yoneda.obj T)) (terminal.from W) ≫ w)

/-- The first component of `sectionAmbientProjection` is the first projection of the ambient fibre
product. -/
theorem sectionAmbientProjection_comp_fst (T : BigFppfOver B U hU) (w : W ⟶ yoneda.obj Z) :
    sectionAmbientProjection T w ≫ prod.fst =
      pullback.fst (terminal.from (yoneda.obj T)) (terminal.from W) :=
  prod.lift_fst _ _

/-- The second component of `sectionAmbientProjection` is the second projection of the ambient
fibre product followed by `w`. -/
theorem sectionAmbientProjection_comp_snd (T : BigFppfOver B U hU) (w : W ⟶ yoneda.obj Z) :
    sectionAmbientProjection T w ≫ prod.snd =
      pullback.snd (terminal.from (yoneda.obj T)) (terminal.from W) ≫ w :=
  prod.lift_snd _ _

/-- `sectionAmbientProjection` is a base change of `w`: the square it forms with the second
projection of the ambient fibre product and the projection `T × Z ⟶ h_Z` is cartesian. -/
theorem isPullback_sectionAmbientProjection (T : BigFppfOver B U hU) (w : W ⟶ yoneda.obj Z) :
    IsPullback (sectionAmbientProjection T w)
      (pullback.snd (terminal.from (yoneda.obj T)) (terminal.from W))
      (prod.snd : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj Z) w := by
  refine IsPullback.mk' (sectionAmbientProjection_comp_snd T w) ?_ ?_
  · intro A φ φ' h₁ h₂
    refine pullback.hom_ext ?_ h₂
    have h := congrArg
      (fun t => t ≫ (prod.fst : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj T)) h₁
    simpa only [Category.assoc, sectionAmbientProjection_comp_fst] using h
  · intro A a b hab
    refine ⟨pullback.lift (a ≫ prod.fst) b (terminal.hom_ext _ _), ?_,
      pullback.lift_snd _ _ _⟩
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, sectionAmbientProjection_comp_fst, pullback.lift_fst]
    · rw [Category.assoc, sectionAmbientProjection_comp_snd, ← Category.assoc, pullback.lift_snd]
      exact hab.symm

/-- The ambient fibre product `T ×_U W` is an algebraic space. -/
private theorem isAlgebraicSpace_pullback_terminal_from (hW : IsAlgebraicSpace B U hU W)
    (T : BigFppfOver B U hU) :
    IsAlgebraicSpace B U hU
      (pullback (terminal.from (yoneda.obj T)) (terminal.from W)) :=
  isAlgebraicSpace_pullback B U hU (terminal.from (yoneda.obj T)) (terminal.from W)
    (isAlgebraicSpace_yoneda B U hU T) hW (isAlgebraicSpace_terminal B U hU)

/-- The base change of an étale `w` along the projection `T × Z ⟶ h_Z` is étale. -/
theorem isEtale_sectionAmbientProjection (hW : IsAlgebraicSpace B U hU W) {w : W ⟶ yoneda.obj Z}
    (hw : IsEtale B U hU w) (T : BigFppfOver B U hU) :
    IsEtale B U hU (sectionAmbientProjection T w) :=
  isEtale_of_isPullback_of_isAlgebraicSpace B U hU (isPullback_sectionAmbientProjection T w)
    (isAlgebraicSpace_pullback_terminal_from hW T)
    (isAlgebraicSpace_yoneda_prod_yoneda T Z) hW (isAlgebraicSpace_yoneda B U hU Z) hw

/-- A section of `W_T ⟶ Z_T`, read as a morphism `T × Z ⟶ T ×_U W`: the first projection on
the first component and the section itself on the second. -/
noncomputable def sectionLift {T : BigFppfOver B U hU} {w : W ⟶ yoneda.obj Z}
    (σ : SectionsOver B U hU Z T W w) :
    yoneda.obj T ⨯ yoneda.obj Z ⟶
      pullback (terminal.from (yoneda.obj T)) (terminal.from W) :=
  pullback.lift prod.fst σ.1 (terminal.hom_ext _ _)

/-- The first component of `sectionLift` is the first projection. -/
theorem sectionLift_comp_fst {T : BigFppfOver B U hU} {w : W ⟶ yoneda.obj Z}
    (σ : SectionsOver B U hU Z T W w) :
    sectionLift σ ≫ pullback.fst (terminal.from (yoneda.obj T)) (terminal.from W) =
      prod.fst :=
  pullback.lift_fst _ _ _

/-- The second component of `sectionLift` is the section. -/
theorem sectionLift_comp_snd {T : BigFppfOver B U hU} {w : W ⟶ yoneda.obj Z}
    (σ : SectionsOver B U hU Z T W w) :
    sectionLift σ ≫ pullback.snd (terminal.from (yoneda.obj T)) (terminal.from W) = σ.1 :=
  pullback.lift_snd _ _ _

/-- `sectionLift σ` is a section of the base change of `w`. -/
theorem sectionLift_comp_sectionAmbientProjection {T : BigFppfOver B U hU} {w : W ⟶ yoneda.obj Z}
    (σ : SectionsOver B U hU Z T W w) :
    sectionLift σ ≫ sectionAmbientProjection T w = 𝟙 (yoneda.obj T ⨯ yoneda.obj Z) := by
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, sectionAmbientProjection_comp_fst, sectionLift_comp_fst, Category.id_comp]
  · rw [Category.assoc, sectionAmbientProjection_comp_snd, ← Category.assoc, sectionLift_comp_snd,
      σ.2, Category.id_comp]

/-- `sectionLift σ` is a monomorphism, being a section. -/
theorem mono_sectionLift {T : BigFppfOver B U hU} {w : W ⟶ yoneda.obj Z}
    (σ : SectionsOver B U hU Z T W w) : Mono (sectionLift σ) :=
  mono_of_section B U hU (sectionAmbientProjection T w) (sectionLift σ)
    (sectionLift_comp_sectionAmbientProjection σ)

/-- `sectionLift σ` is an open immersion: it is a section of the étale base change of `w`. -/
theorem isOpenImmersion_sectionLift (hW : IsAlgebraicSpace B U hU W) {w : W ⟶ yoneda.obj Z}
    (hw : IsEtale B U hU w) {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W w) :
    IsOpenImmersion B U hU (sectionLift σ) :=
  isOpenImmersion_of_isEtale_of_section B U hU
    (isAlgebraicSpace_pullback_terminal_from hW T)
    (isAlgebraicSpace_yoneda_prod_yoneda T Z) (sectionAmbientProjection T w)
    (isEtale_sectionAmbientProjection hW hw T) (sectionLift σ)
    (sectionLift_comp_sectionAmbientProjection σ)

/-- **`T × Z` is isomorphic to the image of `sectionLift σ` in `T ×_U W`**: `sectionLift σ` is
a monomorphism, so the comparison with its image is an isomorphism. -/
noncomputable def sectionLiftRangeIso {T : BigFppfOver B U hU} {w : W ⟶ yoneda.obj Z}
    (σ : SectionsOver B U hU Z T W w) :
    (yoneda.obj T ⨯ yoneda.obj Z) ≅ (Subfunctor.range (sectionLift σ)).toFunctor :=
  haveI := mono_sectionLift σ
  asIso (Subfunctor.toRange (sectionLift σ))

/-- The comparison of `T × Z` with the image of `sectionLift σ`, followed by the inclusion of
the image, is `sectionLift σ`. -/
@[simp]
theorem sectionLiftRangeIso_hom_comp_ι {T : BigFppfOver B U hU} {w : W ⟶ yoneda.obj Z}
    (σ : SectionsOver B U hU Z T W w) :
    (sectionLiftRangeIso σ).hom ≫ (Subfunctor.range (sectionLift σ)).ι = sectionLift σ :=
  Subfunctor.toRange_ι _

/-- The comparison with the image of `sectionLift σ`, followed by the image's projection to `T`,
is the first projection. -/
private theorem sectionLiftRangeIso_hom_comp_ι_comp_fst {T : BigFppfOver B U hU}
    {w : W ⟶ yoneda.obj Z} (σ : SectionsOver B U hU Z T W w) :
    (sectionLiftRangeIso σ).hom ≫ (Subfunctor.range (sectionLift σ)).ι ≫
      pullback.fst (terminal.from (yoneda.obj T)) (terminal.from W) = prod.fst := by
  rw [← Category.assoc, sectionLiftRangeIso_hom_comp_ι, sectionLift_comp_fst]

/-- The comparison with the image of `sectionLift σ`, followed by the image's projection to `W`,
is the section. -/
private theorem sectionLiftRangeIso_hom_comp_ι_comp_snd {T : BigFppfOver B U hU}
    {w : W ⟶ yoneda.obj Z} (σ : SectionsOver B U hU Z T W w) :
    (sectionLiftRangeIso σ).hom ≫ (Subfunctor.range (sectionLift σ)).ι ≫
      pullback.snd (terminal.from (yoneda.obj T)) (terminal.from W) = σ.1 := by
  rw [← Category.assoc, sectionLiftRangeIso_hom_comp_ι, sectionLift_comp_snd]

/-- The image of `sectionLift σ` is an algebraic space, being isomorphic to `T × Z`. -/
theorem isAlgebraicSpace_range_sectionLift {T : BigFppfOver B U hU} {w : W ⟶ yoneda.obj Z}
    (σ : SectionsOver B U hU Z T W w) :
    IsAlgebraicSpace B U hU (Subfunctor.range (sectionLift σ)).toFunctor :=
  (isAlgebraicSpace_yoneda_prod_yoneda T Z).of_iso (sectionLiftRangeIso σ)

/-- The image of `sectionLift σ` is an open subspace of the ambient fibre product. -/
theorem isOpenImmersion_range_sectionLift (hW : IsAlgebraicSpace B U hU W)
    {w : W ⟶ yoneda.obj Z} (hw : IsEtale B U hU w) {T : BigFppfOver B U hU}
    (σ : SectionsOver B U hU Z T W w) :
    IsOpenImmersion B U hU (Subfunctor.range (sectionLift σ)).ι := by
  change (MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B U hU)).presheaf (Subfunctor.range (sectionLift σ)).ι
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (P := (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B U hU)).presheaf) (sectionLiftRangeIso σ).hom]
  simpa using isOpenImmersion_sectionLift hW hw σ

/-- The projection of the image of `sectionLift σ` to `T` is finite: through the isomorphism
with `T × Z` it is the first projection, which is a base change of the finite `Z ⟶ U`. -/
theorem isFinite_range_sectionLift_projection
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T : BigFppfOver B U hU} {w : W ⟶ yoneda.obj Z}
    (σ : SectionsOver B U hU Z T W w) :
    IsFinite B U hU ((Subfunctor.range (sectionLift σ)).ι ≫
      pullback.fst (terminal.from (yoneda.obj T)) (terminal.from W)) := by
  have halg := isAlgebraicSpace_range_sectionLift σ
  have hprod := (isFinite_iff_representable B U hU
    (prod.fst : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj T)
    (isAlgebraicSpace_yoneda_prod_yoneda T Z) (isAlgebraicSpace_yoneda B U hU T)).1
    (isFinite_prod_fst T Z hZfin)
  have heq : (sectionLiftRangeIso σ).inv ≫
      (prod.fst : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj T) =
      (Subfunctor.range (sectionLift σ)).ι ≫
        pullback.fst (terminal.from (yoneda.obj T)) (terminal.from W) := by
    rw [← sectionLiftRangeIso_hom_comp_ι_comp_fst σ, ← Category.assoc, Iso.inv_hom_id,
      Category.id_comp]
  have hpre := MorphismProperty.RespectsIso.precomp
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsFinite.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B U hU)))
    (sectionLiftRangeIso σ).inv prod.fst hprod.2
  rw [heq] at hpre
  exact (isFinite_iff_representable B U hU _ halg (isAlgebraicSpace_yoneda B U hU T)).2
    ⟨hpre.1, hpre⟩

/-- **The pair of Stacks 04PC attached to a section of `W_T ⟶ Z_T`**: the structure morphism of
`T` to `U` together with the image of the section in `T ×_U W`, which is an open subspace finite
over `T`. -/
noncomputable def sectionPair (hW : IsAlgebraicSpace B U hU W) {w : W ⟶ yoneda.obj Z}
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W w) :
    FiniteOpenSubspace B U hU (toTerminalPresheaf B U hU hW) (schemeSpace T) where
  toBase := schemeToTerminalPresheaf B U hU T
  subspace := Subfunctor.range (sectionLift σ)
  isOpen := ⟨isAlgebraicSpace_range_sectionLift σ, isOpenImmersion_range_sectionLift hW hw σ⟩
  finite_projection := isFinite_range_sectionLift_projection hZfin σ

/-- The base morphism of the pair attached to a section is the structure morphism of `T`. -/
theorem sectionPair_toBase (hW : IsAlgebraicSpace B U hU W) {w : W ⟶ yoneda.obj Z}
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W w) :
    (sectionPair hW hw hZfin σ).toBase = schemeToTerminalPresheaf B U hU T :=
  rfl

/-- The open subspace of the pair attached to a section is the image of `sectionLift σ`. -/
theorem sectionPair_subspace (hW : IsAlgebraicSpace B U hU W) {w : W ⟶ yoneda.obj Z}
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T : BigFppfOver B U hU} (σ : SectionsOver B U hU Z T W w) :
    (sectionPair hW hw hZfin σ).subspace = Subfunctor.range (sectionLift σ) :=
  rfl

/-! ### Naturality and injectivity of the pair -/

/-- The projection `T' × Z ⟶ T'` is a base change of the projection `T × Z ⟶ T` along a
morphism `h : T' ⟶ T` of the site. -/
theorem isPullback_prod_map_fst {T T' : BigFppfOver B U hU} (h : T' ⟶ T)
    (Z : BigFppfOver B U hU) :
    IsPullback (prod.fst : yoneda.obj T' ⨯ yoneda.obj Z ⟶ yoneda.obj T')
      (prod.map (yoneda.map h) (𝟙 (yoneda.obj Z))) (yoneda.map h)
      (prod.fst : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj T) := by
  refine IsPullback.mk' (prod.map_fst _ _).symm ?_ ?_
  · intro A φ φ' h₁ h₂
    refine prod.hom_ext h₁ ?_
    have hs := congrArg
      (fun t => t ≫ (prod.snd : yoneda.obj T ⨯ yoneda.obj Z ⟶ yoneda.obj Z)) h₂
    simpa only [Category.assoc, prod.map_snd, Category.comp_id] using hs
  · intro A a b hab
    refine ⟨prod.lift a (b ≫ prod.snd), prod.lift_fst _ _, ?_⟩
    refine prod.hom_ext ?_ ?_
    · rw [Category.assoc, prod.map_fst, ← Category.assoc, prod.lift_fst, hab]
    · rw [Category.assoc, prod.map_snd, Category.comp_id, prod.lift_snd]

/-- The inclusion of the image of `sectionLift σ` followed by the base change of `w` is the
inverse of the comparison of `T × Z` with that image. -/
theorem range_sectionLift_ι_comp_sectionAmbientProjection {T : BigFppfOver B U hU}
    {w : W ⟶ yoneda.obj Z} (σ : SectionsOver B U hU Z T W w) :
    (Subfunctor.range (sectionLift σ)).ι ≫ sectionAmbientProjection T w =
      (sectionLiftRangeIso σ).inv := by
  apply (Iso.cancel_iso_hom_left (sectionLiftRangeIso σ) _ _).1
  rw [← Category.assoc, sectionLiftRangeIso_hom_comp_ι, sectionLift_comp_sectionAmbientProjection,
    Iso.hom_inv_id]

/-- **The pair attached to a restriction of a section is the base change of the pair attached to
the section.** Through the comparisons of `T × Z` and `T' × Z` with the two images, the square
of the base change is the one exhibiting `T' × Z ⟶ T'` as a base change of `T × Z ⟶ T`. -/
theorem isBaseChange_sectionPair (hW : IsAlgebraicSpace B U hU W) {w : W ⟶ yoneda.obj Z}
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T T' : BigFppfOver B U hU} (h : T' ⟶ T) (σ : SectionsOver B U hU Z T W w) :
    FiniteOpenSubspace.IsBaseChange B U hU (toTerminalPresheaf B U hU hW) h
      (sectionPair hW hw hZfin σ)
      (sectionPair hW hw hZfin (SectionsOver.restrict h σ)) := by
  refine ⟨terminal.hom_ext _ _,
    (sectionLiftRangeIso (SectionsOver.restrict h σ)).inv ≫
      prod.map (yoneda.map h) (𝟙 (yoneda.obj Z)) ≫ (sectionLiftRangeIso σ).hom, ?_, ?_⟩
  · change IsPullback ((Subfunctor.range (sectionLift (SectionsOver.restrict h σ))).ι ≫
        pullback.fst (terminal.from (yoneda.obj T')) (terminal.from W))
      ((sectionLiftRangeIso (SectionsOver.restrict h σ)).inv ≫
        prod.map (yoneda.map h) (𝟙 (yoneda.obj Z)) ≫ (sectionLiftRangeIso σ).hom)
      (yoneda.map h)
      ((Subfunctor.range (sectionLift σ)).ι ≫
        pullback.fst (terminal.from (yoneda.obj T)) (terminal.from W))
    refine (isPullback_prod_map_fst h Z).of_iso
      (sectionLiftRangeIso (SectionsOver.restrict h σ)) (Iso.refl _)
      (sectionLiftRangeIso σ) (Iso.refl _) ?_ ?_ ?_ ?_
    · simpa only [Iso.refl_hom, Category.comp_id] using
        (sectionLiftRangeIso_hom_comp_ι_comp_fst (SectionsOver.restrict h σ)).symm
    · simp
    · simp
    · simpa only [Iso.refl_hom, Category.comp_id] using
        (sectionLiftRangeIso_hom_comp_ι_comp_fst σ).symm
  · change ((sectionLiftRangeIso (SectionsOver.restrict h σ)).inv ≫
        prod.map (yoneda.map h) (𝟙 (yoneda.obj Z)) ≫ (sectionLiftRangeIso σ).hom) ≫
        (Subfunctor.range (sectionLift σ)).ι ≫
          pullback.snd (terminal.from (yoneda.obj T)) (terminal.from W) =
      (Subfunctor.range (sectionLift (SectionsOver.restrict h σ))).ι ≫
        pullback.snd (terminal.from (yoneda.obj T')) (terminal.from W)
    apply (Iso.cancel_iso_hom_left (sectionLiftRangeIso (SectionsOver.restrict h σ)) _ _).1
    rw [sectionLiftRangeIso_hom_comp_ι_comp_snd, SectionsOver.restrict_coe]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [sectionLiftRangeIso_hom_comp_ι_comp_snd]

/-- **A section is determined by the pair it defines.** The pair determines the image of
`sectionLift σ` inside `T ×_U W`, and the comparison of that image with `T × Z` is recovered
from it as the base change of `w` restricted to the image, so `σ` itself is recovered. -/
theorem sectionPair_injective (hW : IsAlgebraicSpace B U hU W) {w : W ⟶ yoneda.obj Z}
    (hw : IsEtale B U hU w)
    (hZfin : _root_.AlgebraicGeometry.IsFinite (B.inclusion.map Z.hom))
    {T : BigFppfOver B U hU} :
    Function.Injective (fun σ : SectionsOver B U hU Z T W w => sectionPair hW hw hZfin σ) := by
  intro σ τ hστ
  have hR : Subfunctor.range (sectionLift σ) = Subfunctor.range (sectionLift τ) :=
    eq_of_heq (congr_arg_heq FiniteOpenSubspace.subspace hστ)
  set l := (sectionLiftRangeIso τ).hom ≫ Subfunctor.homOfLe hR.ge with hl
  have hlι : l ≫ (Subfunctor.range (sectionLift σ)).ι = sectionLift τ := by
    rw [hl, Category.assoc, Subfunctor.homOfLe_ι, sectionLiftRangeIso_hom_comp_ι]
  have hlinv : l = (sectionLiftRangeIso σ).hom := (Iso.comp_inv_eq_id _).1 (by
    rw [← range_sectionLift_ι_comp_sectionAmbientProjection σ, ← Category.assoc, hlι,
      sectionLift_comp_sectionAmbientProjection])
  exact Subtype.ext (by
    rw [← sectionLift_comp_snd σ, ← sectionLift_comp_snd τ, ← hlι, hlinv,
      sectionLiftRangeIso_hom_comp_ι])

end SectionPair

end AlgebraicGeometry.Space

end
