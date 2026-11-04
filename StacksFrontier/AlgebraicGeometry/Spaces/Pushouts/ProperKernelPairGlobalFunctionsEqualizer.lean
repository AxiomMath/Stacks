module

public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairChartEqualizer

/-!
# The equalizer of global functions over the affine realizations of the Čech nerve

Let `g : Y ⟶ X` be a proper morphism of algebraic spaces over `S` with `X` locally Noetherian,
`X' = \underline{Spec}_X(𝒜)` the relative spectrum of
`𝒜 = Equalizer(g_* 𝒪_Y ⇉ h_* 𝒪_{Y ×_X Y})` and `π : Y ⟶ X'`.  The last paragraph of the proof of
Stacks 0AGG reads off from `𝒪_{X'} = Equalizer(π_* 𝒪_Y ⇉ π_* 𝒪_{Y ×_{X'} Y})` that for an affine
`U` étale over `X'` the global functions of `U` are the equalizer of those of `U ×_{X'} Y` and
`U ×_{X'} Y ×_{X'} Y`.  This file proves that statement,
`AlgebraicGeometry.Space.KernelPairSpecGlobalFunctionsEqualizer`, and with it Stacks 0AGG from
étale descent along proper surjective morphisms alone.

## Main definitions

* `AlgebraicGeometry.Space.cechOneIso`: the degree-one term `Y ×_{X'} Y` of the Čech nerve of `π`
  is the kernel pair `Y ×_X Y`.
* `AlgebraicGeometry.Space.realizationFibreIso`: the members of a compatible étale family over a
  diagram, realized over an algebraic space represented by a scheme, are the fibres over the
  attached chart.

## Main results

* `AlgebraicGeometry.Space.chartBaseChangeSpaceTransIso`: for `ν : X' ⟶ X`, a chart `V` of `X`
  and a chart `W` of `X'` identified with `X' ×_X V`, the fibre `C ×_{X'} W` of `p : C ⟶ X'` is
  `C ×_X V`.
* `AlgebraicGeometry.Space.globalFunctionsEqualizer_kernelPairSpec`: over an étale chart `V` of
  `X`, `Γ(X' ×_X V) ⟶ Γ(Y ×_X V) ⇉ Γ(Y ×_X Y ×_X V)` is an equalizer; this is the definition of
  `𝒜`, read on global functions.
* `AlgebraicGeometry.Space.chartGlobalFunctionsEqualizer_of_isPullback`: the same over the chart
  `X' ×_X V` of `X'`, for the terms of the Čech nerve of `π`.
* `AlgebraicGeometry.Space.kernelPairSpecGlobalFunctionsEqualizer`: the statement above.
* `AlgebraicGeometry.Space.properKernelPairCoequalizers`: **Stacks 0AGG**,
  from étale descent of algebraic spaces along proper surjective morphisms.

## Implementation notes

The kernel pair is always referred to through `AlgebraicGeometry.Space.kernelPairOver` and its
projections, never through a fresh `CategoryTheory.Limits.pullback`: this file imports the
finite-limit instance of `StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairCech`, so
a fresh fibre product would be found through a different instance from the one of
`StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.ProperKernelPairSpec`.  For the same reason the
direct-image maps of the two projections are compared, once, with their `CategoryTheory.Over.mk`
spellings by `rfl` (`AlgebraicGeometry.Space.pushforwardAlgebraMap_kernelPairSndOver_eq_mk`);
across the bare definitions the kernel does not finish in the default budget.

## References

* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
* [Stacks Project, Tag 0GHL](https://stacks.math.columbia.edu/tag/0GHL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Fibres over a chart of `X'` identified with a fibre over a chart of `X` -/

section Trans

variable {X X' C C₀ C₁ : AlgebraicSpaces B S hS} (ν : X' ⟶ X) (V : SmallEtale B S hS X.1)
  (W : SmallEtale B S hS X'.1)
  (θ : (SpacesEtale.toSpaces B S hS X').obj ((comparisonFunctor B S hS X').obj W) ≅
    chartBaseChangeSpace B S hS ν V)
  (hθ : θ.hom ≫ chartBaseChangeInclusion B S hS ν V = chartToSpace B S hS X' W)

include hθ in
/-- The fibre `C ×_X V` of `p ≫ ν` is the fibre product of `p` with `W ⟶ X'`. -/
theorem isPullback_chartBaseChangeTrans (p : C ⟶ X') :
    IsPullback (chartBaseChangeInclusion B S hS (p ≫ ν) V)
      (chartBaseChangeSpaceMap B S hS p rfl V ≫ θ.inv) p (chartToSpace B S hS X' W) := by
  have hleft : IsPullback (chartBaseChangeSpaceMap B S hS p rfl V)
      (chartBaseChangeInclusion B S hS (p ≫ ν) V) (chartBaseChangeInclusion B S hS ν V) p :=
    IsPullback.of_right (by
      rw [chartBaseChangeSpaceMap_projection]
      exact (isPullback_chartBaseChangeInclusion B S hS (p ≫ ν) V).flip)
      (chartBaseChangeSpaceMap_inclusion B S hS p rfl V)
      (isPullback_chartBaseChangeInclusion B S hS ν V).flip
  have hiso : IsPullback θ.inv (chartBaseChangeInclusion B S hS ν V) (chartToSpace B S hS X' W)
      (𝟙 X') :=
    IsPullback.of_horiz_isIso ⟨by rw [← hθ, Iso.inv_hom_id_assoc, Category.comp_id]⟩
  simpa only [Category.comp_id] using (hleft.paste_horiz hiso).flip

/-- **`C ×_{X'} W ≅ C ×_X V`** for `p : C ⟶ X'`, when `W ≅ X' ×_X V` over `X'`. -/
def chartBaseChangeSpaceTransIso (p : C ⟶ X') :
    chartBaseChangeSpace B S hS p W ≅ chartBaseChangeSpace B S hS (p ≫ ν) V :=
  (isPullback_chartBaseChangeInclusion B S hS p W).isoIsPullback _ _
    (isPullback_chartBaseChangeTrans ν V W θ hθ p)

/-- The identification `C ×_{X'} W ≅ C ×_X V` commutes with the inclusions of the fibres into
`C`. -/
@[reassoc (attr := simp)]
theorem chartBaseChangeSpaceTransIso_hom_inclusion (p : C ⟶ X') :
    (chartBaseChangeSpaceTransIso ν V W θ hθ p).hom ≫
        chartBaseChangeInclusion B S hS (p ≫ ν) V =
      chartBaseChangeInclusion B S hS p W :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The identification carries the projection to `W` to the projection to `X' ×_X V`. -/
theorem chartBaseChangeProjection_trans (p : C ⟶ X') :
    chartBaseChangeProjection B S hS p W ≫ θ.hom =
      (chartBaseChangeSpaceTransIso ν V W θ hθ p).hom ≫
        chartBaseChangeSpaceMap B S hS p rfl V := by
  have h := IsPullback.isoIsPullback_hom_snd _ _ (isPullback_chartBaseChangeInclusion B S hS p W)
    (isPullback_chartBaseChangeTrans ν V W θ hθ p)
  change (chartBaseChangeSpaceTransIso ν V W θ hθ p).hom ≫
      chartBaseChangeSpaceMap B S hS p rfl V ≫ θ.inv = chartBaseChangeProjection B S hS p W at h
  rw [← h, Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The identification is natural in morphisms over `X'`. -/
theorem chartBaseChangeSpaceMap_trans {p₀ : C₀ ⟶ X'} {p₁ : C₁ ⟶ X'} (δ : C₁ ⟶ C₀)
    (hδ : δ ≫ p₀ = p₁) :
    chartBaseChangeSpaceMap B S hS δ hδ W ≫ (chartBaseChangeSpaceTransIso ν V W θ hθ p₀).hom =
      (chartBaseChangeSpaceTransIso ν V W θ hθ p₁).hom ≫
        chartBaseChangeSpaceMap B S hS δ (by rw [← hδ, Category.assoc]) V := by
  refine (isPullback_chartBaseChangeInclusion B S hS (p₀ ≫ ν) V).hom_ext ?_ ?_
  · simp only [Category.assoc, chartBaseChangeSpaceTransIso_hom_inclusion,
      chartBaseChangeSpaceMap_inclusion, chartBaseChangeSpaceTransIso_hom_inclusion_assoc]
  · rw [Category.assoc, Category.assoc, chartBaseChangeSpaceMap_projection,
      ← chartBaseChangeSpaceMap_projection B S hS p₀ (rfl : p₀ ≫ ν = p₀ ≫ ν) V,
      ← chartBaseChangeSpaceMap_projection B S hS p₁ (rfl : p₁ ≫ ν = p₁ ≫ ν) V,
      ← Category.assoc _ (chartBaseChangeSpaceMap B S hS p₀ rfl V),
      ← chartBaseChangeProjection_trans ν V W θ hθ p₀,
      ← Category.assoc _ (chartBaseChangeSpaceMap B S hS p₁ rfl V),
      ← chartBaseChangeProjection_trans ν V W θ hθ p₁, ← Category.assoc,
      ← Category.assoc, chartBaseChangeSpaceMap_projection]

end Trans

/-! ### The definition of `𝒜`, read on global functions -/

section Spec

variable {X Y : AlgebraicSpaces B S hS} {g : Y ⟶ X}

variable (g) in
/-- The first projection `s : Y ×_X Y ⟶ Y`, as a morphism over `X` between objects of the form
`CategoryTheory.Over.mk`. -/
abbrev kernelPairFstOverMk : Over.mk (kernelPairOver g).hom ⟶ Over.mk g :=
  Over.homMk (kernelPairFstOver g).left (Over.w (kernelPairFstOver g))

variable (g) in
/-- The second projection `t : Y ×_X Y ⟶ Y`, as a morphism over `X` between objects of the form
`CategoryTheory.Over.mk`. -/
abbrev kernelPairSndOverMk : Over.mk (kernelPairOver g).hom ⟶ Over.mk g :=
  Over.homMk (kernelPairSndOver g).left (Over.w (kernelPairSndOver g))

/-- On sections over `V`, the morphism `𝒜 ≅ ν_* 𝒪_{X'} ⟶ g_* 𝒪_Y` attached to `π : Y ⟶ X'` is the
inclusion of `𝒜`. -/
theorem pushforwardAlgebraMap_kernelPairSpecπOver_apply (hg : IsProper B S hS g.hom)
    (V : SmallEtale B S hS X.1)
    (r : (pushforwardAlgebra B S hS (kernelPairSpec hg).obj).right.obj.obj (op V)) :
    ((pushforwardAlgebraMap B S hS (kernelPairSpecπOver hg)).right.hom.app (op V)).hom r =
      ((((kernelPairSpecIso hg).hom.right.hom.app (op V)).hom r :
        (kernelPairAlgebra g).right.obj.obj (op V)) :
          (AlgebraSheaf.equalizerSections (kernelPairFstMap g) (kernelPairSndMap g) (op V))).1 := by
  rw [pushforwardAlgebraMap_kernelPairSpecπOver]
  rfl

/-- **On sections over a chart, `𝒪_{X'}` maps isomorphically onto `𝒜`**: the map
`ν_* 𝒪_{X'} ⟶ g_* 𝒪_Y` attached to `π : Y ⟶ X'` is injective on sections over `V`, with image
the equalizer of `s♯` and `t♯`. -/
theorem isEqualizer_pushforwardAlgebraMap_kernelPairSpecπOver (hg : IsProper B S hS g.hom)
    (V : SmallEtale B S hS X.1) :
    Function.Injective
        ((pushforwardAlgebraMap B S hS (kernelPairSpecπOver hg)).right.hom.app (op V)).hom ∧
      ∀ a, ((pushforwardAlgebraMap B S hS (kernelPairFstOver g)).right.hom.app (op V)).hom a =
          ((pushforwardAlgebraMap B S hS (kernelPairSndOver g)).right.hom.app (op V)).hom a →
        ∃ r, ((pushforwardAlgebraMap B S hS (kernelPairSpecπOver hg)).right.hom.app
          (op V)).hom r = a := by
  let e := kernelPairSpecIso hg
  have hι := pushforwardAlgebraMap_kernelPairSpecπOver_apply hg V
  have hinv : ∀ x, (e.inv.right.hom.app (op V)).hom ((e.hom.right.hom.app (op V)).hom x) = x :=
    fun x => congrArg (fun φ : _ ⟶ _ => (φ.right.hom.app (op V)).hom x) e.hom_inv_id
  have hinv' : ∀ y, (e.hom.right.hom.app (op V)).hom ((e.inv.right.hom.app (op V)).hom y) = y :=
    fun y => congrArg (fun φ : _ ⟶ _ => (φ.right.hom.app (op V)).hom y) e.inv_hom_id
  refine ⟨fun r₁ r₂ h => ?_, fun a ha => ?_⟩
  · rw [hι, hι] at h
    rw [← hinv r₁, ← hinv r₂, Subtype.ext h]
  · have ha' : a ∈ AlgebraSheaf.equalizerSections (kernelPairFstMap g) (kernelPairSndMap g)
        (op V) := by
      show ((kernelPairFstMap g).right.hom.app (op V)).hom a =
        ((kernelPairSndMap g).right.hom.app (op V)).hom a
      rwa [kernelPairFstMap_def, kernelPairSndMap_def]
    refine ⟨(e.inv.right.hom.app (op V)).hom ⟨a, ha'⟩, ?_⟩
    rw [hι]
    exact congrArg Subtype.val (hinv' ⟨a, ha'⟩)

/-- The map `s♯` is the direct-image map of `kernelPairFstOverMk`.  Stated so that the kernel
compares the two spellings of the projection once, by `rfl`, rather than inside a larger term. -/
theorem pushforwardAlgebraMap_kernelPairFstOver_eq_mk :
    pushforwardAlgebraMap B S hS (kernelPairFstOver g) =
      pushforwardAlgebraMap B S hS (kernelPairFstOverMk g) :=
  rfl

/-- The map `t♯` is the direct-image map of `kernelPairSndOverMk`. -/
theorem pushforwardAlgebraMap_kernelPairSndOver_eq_mk :
    pushforwardAlgebraMap B S hS (kernelPairSndOver g) =
      pushforwardAlgebraMap B S hS (kernelPairSndOverMk g) :=
  rfl

/-- The map `s♯` on sections over `V`, read on global functions of the fibres, is pullback along
`s : Y ×_X Y ×_X V ⟶ Y ×_X V`. -/
theorem directImageSectionsToGlobalFunctions_kernelPairFstOver (V : SmallEtale B S hS X.1)
    (a : (pushforwardAlgebra B S hS (Over.mk g)).right.obj.obj (op V)) :
    directImageSectionsToGlobalFunctions B S hS (kernelPairOver g).hom V
        (((pushforwardAlgebraMap B S hS (kernelPairFstOver g)).right.hom.app (op V)).hom a) =
      globalFunctionsMap B S hS (chartBaseChangeSpaceMap B S hS (kernelPairFstOver g).left
        (Over.w (kernelPairFstOver g)) V) (directImageSectionsToGlobalFunctions B S hS g V a) := by
  rw [pushforwardAlgebraMap_kernelPairFstOver_eq_mk]
  exact directImageSectionsToGlobalFunctions_pushforwardAlgebraMap B S hS _ V a

/-- The map `t♯` on sections over `V`, read on global functions of the fibres, is pullback along
`t : Y ×_X Y ×_X V ⟶ Y ×_X V`. -/
theorem directImageSectionsToGlobalFunctions_kernelPairSndOver (V : SmallEtale B S hS X.1)
    (a : (pushforwardAlgebra B S hS (Over.mk g)).right.obj.obj (op V)) :
    directImageSectionsToGlobalFunctions B S hS (kernelPairOver g).hom V
        (((pushforwardAlgebraMap B S hS (kernelPairSndOver g)).right.hom.app (op V)).hom a) =
      globalFunctionsMap B S hS (chartBaseChangeSpaceMap B S hS (kernelPairSndOver g).left
        (Over.w (kernelPairSndOver g)) V) (directImageSectionsToGlobalFunctions B S hS g V a) := by
  rw [pushforwardAlgebraMap_kernelPairSndOver_eq_mk]
  exact directImageSectionsToGlobalFunctions_pushforwardAlgebraMap B S hS _ V a

/-- **`Γ(X' ×_X V) ⟶ Γ(Y ×_X V) ⇉ Γ(Y ×_X Y ×_X V)` is an equalizer** over every étale chart `V`
of `X`: on the sections over `V` of the direct images, `𝒪_{X'}` maps isomorphically onto `𝒜`, the
equalizer of `s♯, t♯ : g_* 𝒪_Y ⇉ h_* 𝒪_R`, and the sections of the direct images are the global
functions of the fibres, naturally. -/
theorem globalFunctionsEqualizer_kernelPairSpec (hg : IsProper B S hS g.hom)
    (V : SmallEtale B S hS X.1) :
    GlobalFunctionsEqualizer
      (chartBaseChangeSpaceMap B S hS (kernelPairSpecπOver hg).left
        (Over.w (kernelPairSpecπOver hg)) V)
      (chartBaseChangeSpaceMap B S hS (kernelPairFstOver g).left
        (Over.w (kernelPairFstOver g)) V)
      (chartBaseChangeSpaceMap B S hS (kernelPairSndOver g).left
        (Over.w (kernelPairSndOver g)) V) :=
  (isEqualizerDiagram_iff_of_bijective
    ((pushforwardAlgebraMap B S hS (kernelPairSpecπOver hg)).right.hom.app (op V)).hom
    ((pushforwardAlgebraMap B S hS (kernelPairFstOver g)).right.hom.app (op V)).hom
    ((pushforwardAlgebraMap B S hS (kernelPairSndOver g)).right.hom.app (op V)).hom _ _ _
    (directImageSectionsToGlobalFunctions B S hS (kernelPairSpecToTarget hg) V)
    (directImageSectionsToGlobalFunctions B S hS g V)
    (directImageSectionsToGlobalFunctions B S hS (kernelPairOver g).hom V)
    (bijective_directImageSectionsToGlobalFunctions B S hS _ V)
    (bijective_directImageSectionsToGlobalFunctions B S hS g V)
    (injective_directImageSectionsToGlobalFunctions B S hS _ V)
    (directImageSectionsToGlobalFunctions_pushforwardAlgebraMap B S hS _ V)
    (directImageSectionsToGlobalFunctions_kernelPairFstOver V)
    (directImageSectionsToGlobalFunctions_kernelPairSndOver V)).1
    (isEqualizer_pushforwardAlgebraMap_kernelPairSpecπOver hg V)

end Spec

/-! ### The terms of the Čech nerve of `π` in degrees `0` and `1` -/

section Cech

variable {X Y : AlgebraicSpaces B S hS} {g : Y ⟶ X} (hg : IsProper B S hS g.hom)

/-- The face map of the Čech nerve of `π : Y ⟶ X'` from degree `1` to degree `0` missing the
vertex `1 - i`, as a morphism over `X'`. -/
abbrev cechFace (i : Fin 2) :
    Over.mk (cechBase (kernelPairSpecπ hg) (op ⦋1⦌)) ⟶
      Over.mk (cechBase (kernelPairSpecπ hg) (op ⦋0⦌)) :=
  Over.homMk ((cechNerveSpace (kernelPairSpecπ hg)).map (SimplexCategory.const ⦋0⦌ ⦋1⦌ i).op)
    (cechNerveSpace_map_cechBase _ _)

/-- The morphism `Y ×_{X'} Y ⟶ Y ×_X Y` from the degree-one term of the Čech nerve of `π` to the
kernel pair of `g`. -/
def cechOneHom : (cechNerveSpace (kernelPairSpecπ hg)).obj (op ⦋1⦌) ⟶ (kernelPairOver g).left :=
  (isPullback_kernelPairOver g).lift (cechProj (kernelPairSpecπ hg) 0)
    (cechProj (kernelPairSpecπ hg) 1) (by
      have e : kernelPairSpecπ hg ≫ kernelPairSpecToTarget hg = g :=
        kernelPairSpecπ_comp_toTarget hg
      exact (congrArg (cechProj (kernelPairSpecπ hg) 0 ≫ ·) e).symm.trans
        ((Category.assoc _ _ _).symm.trans
          ((congrArg (· ≫ kernelPairSpecToTarget hg)
              ((cechProj_comp (kernelPairSpecπ hg) (n := op ⦋1⦌) 0).trans
                (cechProj_comp (kernelPairSpecπ hg) (n := op ⦋1⦌) 1).symm)).trans
            ((Category.assoc _ _ _).trans (congrArg (cechProj (kernelPairSpecπ hg) 1 ≫ ·) e)))))

/-- The morphism `cechOneHom` followed by the first projection of the kernel pair is the
projection `cechProj _ 0` of the Čech nerve. -/
@[reassoc (attr := simp)]
theorem cechOneHom_fst :
    cechOneHom hg ≫ (kernelPairFstOver g).left = cechProj (kernelPairSpecπ hg) 0 :=
  (isPullback_kernelPairOver g).lift_fst _ _ _

/-- The morphism `cechOneHom` followed by the second projection of the kernel pair is the
projection `cechProj _ 1` of the Čech nerve. -/
@[reassoc (attr := simp)]
theorem cechOneHom_snd :
    cechOneHom hg ≫ (kernelPairSndOver g).left = cechProj (kernelPairSpecπ hg) 1 :=
  (isPullback_kernelPairOver g).lift_snd _ _ _

/-- The degree-one term `Y ×_{X'} Y` of the Čech nerve of `π` is the kernel pair
`Y ×_X Y`: a pair of points of `Y` with the same image in `X` has the same image in `X'`, because
`π` equalizes the two projections. -/
def cechOneIso : (cechNerveSpace (kernelPairSpecπ hg)).obj (op ⦋1⦌) ≅ (kernelPairOver g).left where
  hom := cechOneHom hg
  inv := ObjectProperty.homMk (cechPt (kernelPairSpecπ hg)
    ((kernelPairFstOver g).left ≫ kernelPairSpecπ hg).hom
    ![(kernelPairFstOver g).left.hom, (kernelPairSndOver g).left.hom] (fun i => by
      fin_cases i
      · rfl
      · exact congrArg (fun k => k.hom) (kernelPairSpecπ_equalizes hg).symm))
  hom_inv_id := ObjectProperty.hom_ext _ (cech_hom_ext _ fun i => by
    fin_cases i
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (cechPt_proj _ _ _ _ 0)).trans
        ((congrArg (fun k => k.hom) (cechOneHom_fst hg)).trans (Category.id_comp _).symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (cechPt_proj _ _ _ _ 1)).trans
        ((congrArg (fun k => k.hom) (cechOneHom_snd hg)).trans (Category.id_comp _).symm)))
  inv_hom_id := (isPullback_kernelPairOver g).hom_ext
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (cechOneHom_fst hg)).trans
      ((ObjectProperty.hom_ext _ (cechPt_proj _ _ _ _ 0)).trans (Category.id_comp _).symm)))
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (cechOneHom_snd hg)).trans
      ((ObjectProperty.hom_ext _ (cechPt_proj _ _ _ _ 1)).trans (Category.id_comp _).symm)))

/-- **Over a chart `V` of `X`, `Γ(X' ×_X V) ⟶ Γ(C₀ ×_X V) ⇉ Γ(C₁ ×_X V)` is an equalizer**, for
the terms `C₀ = Y` and `C₁ = Y ×_{X'} Y` of the Čech nerve of `π` and its two face maps: this is
`AlgebraicGeometry.Space.globalFunctionsEqualizer_kernelPairSpec` across `C₀ ≅ Y` and
`C₁ ≅ Y ×_X Y`. -/
theorem globalFunctionsEqualizer_cech (V : SmallEtale B S hS X.1) :
    GlobalFunctionsEqualizer
      (chartBaseChangeSpaceMap B S hS (cechBase (kernelPairSpecπ hg) (op ⦋0⦌)) rfl V)
      (chartBaseChangeSpaceMap B S hS
        (p₁ := cechBase (kernelPairSpecπ hg) (op ⦋1⦌) ≫ kernelPairSpecToTarget hg)
        (p₂ := cechBase (kernelPairSpecπ hg) (op ⦋0⦌) ≫ kernelPairSpecToTarget hg)
        (cechFace hg 0).left
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (cechNerveSpace_map_cechBase _ _))) V)
      (chartBaseChangeSpaceMap B S hS
        (p₁ := cechBase (kernelPairSpecπ hg) (op ⦋1⦌) ≫ kernelPairSpecToTarget hg)
        (p₂ := cechBase (kernelPairSpecπ hg) (op ⦋0⦌) ≫ kernelPairSpecToTarget hg)
        (cechFace hg 1).left
        ((Category.assoc _ _ _).symm.trans
          (congrArg (· ≫ _) (cechNerveSpace_map_cechBase _ _))) V) := by
  have e : kernelPairSpecπ hg ≫ kernelPairSpecToTarget hg = g := kernelPairSpecπ_comp_toTarget hg
  let α₀ := asIso (cechProj (kernelPairSpecπ hg) (n := op ⦋0⦌) 0)
  have hα₀ : α₀.hom ≫ g = cechBase (kernelPairSpecπ hg) (op ⦋0⦌) ≫ kernelPairSpecToTarget hg := by
    rw [← cechProj_comp (kernelPairSpecπ hg) (n := op ⦋0⦌) 0, Category.assoc, e]
    rfl
  have hα₁ : (cechOneIso hg).hom ≫ (kernelPairOver g).hom =
      cechBase (kernelPairSpecπ hg) (op ⦋1⦌) ≫ kernelPairSpecToTarget hg := by
    show cechOneHom hg ≫ (kernelPairFstOver g).left ≫ g = _
    rw [cechOneHom_fst_assoc, ← cechProj_comp (kernelPairSpecπ hg) (n := op ⦋1⦌) 0,
      Category.assoc, e]
  refine GlobalFunctionsEqualizer.of_iso (Iso.refl _) (chartBaseChangeSpaceIso B S hS α₀ hα₀ V)
    (chartBaseChangeSpaceIso B S hS (cechOneIso hg) hα₁ V) ?_ ?_ ?_
    (globalFunctionsEqualizer_kernelPairSpec hg V)
  · rw [Iso.refl_hom, Category.comp_id, chartBaseChangeSpaceIso_hom]
    exact chartBaseChangeSpaceMap_comp B S hS _ _ _ _ _ _
      (cechProj_comp (kernelPairSpecπ hg) (n := op ⦋0⦌) 0) V
  · rw [chartBaseChangeSpaceIso_hom, chartBaseChangeSpaceIso_hom,
      ← chartBaseChangeSpaceMap_comp B S hS _ _ (cechProj (kernelPairSpecπ hg) 0) _ _
        ((congrArg (cechProj (kernelPairSpecπ hg) 0 ≫ ·) e).symm.trans
          (cechProj_comp_assoc _ _ _))
        (cechNerveSpace_map_cechProj (kernelPairSpecπ hg) _ 0) V]
    exact chartBaseChangeSpaceMap_comp B S hS _ _ _ _ _ _ (cechOneHom_fst hg) V
  · rw [chartBaseChangeSpaceIso_hom, chartBaseChangeSpaceIso_hom,
      ← chartBaseChangeSpaceMap_comp B S hS _ _ (cechProj (kernelPairSpecπ hg) 1) _ _
        ((congrArg (cechProj (kernelPairSpecπ hg) 1 ≫ ·) e).symm.trans
          (cechProj_comp_assoc _ _ _))
        (cechNerveSpace_map_cechProj (kernelPairSpecπ hg) _ 0) V]
    exact chartBaseChangeSpaceMap_comp B S hS _ _ _ _ _ _ (cechOneHom_snd hg) V

/-- The structure morphism of the degree-zero term of the Čech nerve of `π` to `X'` is proper. -/
theorem isProper_cechBase_zero
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    IsProper B S hS (cechBase (kernelPairSpecπ hg) (op ⦋0⦌)).hom := by
  have : IsIso (cechProj (kernelPairSpecπ hg) (n := op ⦋0⦌) 0).hom :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).map (cechProj (kernelPairSpecπ hg) 0)))
  rw [← cechProj_comp (kernelPairSpecπ hg) (n := op ⦋0⦌) 0]
  exact (isProper_isIso_comp_iff B S hS _ _).2 (isProper_kernelPairSpecπ hg hX)

/-- The structure morphism of the degree-one term of the Čech nerve of `π` to `X'` is proper. -/
theorem isProper_cechBase_one
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} ↦ IsLocallyNoetherian V)) :
    IsProper B S hS (cechBase (kernelPairSpecπ hg) (op ⦋1⦌)).hom := by
  have : IsIso (cechOneIso hg).hom.hom :=
    inferInstanceAs (IsIso ((ObjectProperty.ι _).map (cechOneIso hg).hom))
  have hfst : IsProper B S hS (kernelPairFstOver g).left.hom :=
    (isProper_isStableUnderBaseChange B S hS).of_isPullback (isPullback_kernelPairOver g).flip hg
  rw [← cechProj_comp (kernelPairSpecπ hg) (n := op ⦋1⦌) 0, ← cechOneHom_fst hg]
  show IsProper B S hS ((cechOneIso hg).hom.hom ≫ (kernelPairFstOver g).left.hom ≫
    (kernelPairSpecπ hg).hom)
  exact (isProper_isIso_comp_iff B S hS _ _).2 (isProper_comp B S hS
    (kernelPairOver g).left.property Y.property (kernelPairSpec hg).obj.left.property _ _ hfst
    (isProper_kernelPairSpecπ hg hX))

end Cech

/-! ### The equalizer over the affine realizations -/

section Realization

variable {X' : AlgebraicSpaces B S hS} {I : Type*} [Category I] {D : I ⥤ Over X'}
  {c : Cocone D} {E : CompatibleEtaleDiagram B S hS D} (r : EtaleRealization B S hS c E)
  {T : BigFppfOver B S hS} (e : r.U.obj ≅ yoneda.obj T)

/-- The étale chart of the vertex attached to a realization whose total space is represented. -/
def realizationChart : SmallEtale B S hS c.pt.left.1 :=
  ⟨CostructuredArrow.mk (e.inv ≫ r.toX.hom),
    presheaf_etale_of_isEtale B S hS (isEtale_comp B S hS (isEtale_of_isIso B S hS e.inv) r.etale)⟩

/-- The total space of the realization is the algebraic space of its chart. -/
def realizationChartIso :
    r.U ≅ (SpacesEtale.toSpaces B S hS c.pt.left).obj
      ((comparisonFunctor B S hS c.pt.left).obj (realizationChart r e)) :=
  isoSchemeSpace e

/-- The identification `realizationChartIso` of the total space with the algebraic space of the
chart commutes with the maps to `c.pt.left`. -/
theorem realizationChartIso_hom_comp :
    (realizationChartIso r e).hom ≫ chartToSpace B S hS c.pt.left (realizationChart r e) =
      r.toX :=
  ObjectProperty.hom_ext _ (e.hom_inv_id_assoc r.toX.hom)

/-- The members of a realized compatible family are the fibres of the cocone legs over the
chart attached to the realization. -/
theorem isPullback_realizationChart (i : I) :
    IsPullback (E.projection.app i) (r.baseChange.app i ≫ (realizationChartIso r e).hom)
      (c.ι.app i).left (chartToSpace B S hS c.pt.left (realizationChart r e)) := by
  refine (r.isPullback i).of_iso (Iso.refl _) (Iso.refl _) (realizationChartIso r e)
    (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp [realizationChartIso_hom_comp]

/-- The identification of a member of the family with a fibre over the chart. -/
def realizationFibreIso (i : I) :
    E.U.obj i ≅ chartBaseChangeSpace B S hS (c.ι.app i).left (realizationChart r e) :=
  (isPullback_realizationChart r e i).isoIsPullback _ _
    (isPullback_chartBaseChangeInclusion B S hS (c.ι.app i).left (realizationChart r e))

/-- The identification `realizationFibreIso` carries the inclusion of the fibre into the source
of the cocone leg to the projection `E.projection.app i`. -/
@[reassoc (attr := simp)]
theorem realizationFibreIso_hom_inclusion (i : I) :
    (realizationFibreIso r e i).hom ≫
        chartBaseChangeInclusion B S hS (c.ι.app i).left (realizationChart r e) =
      E.projection.app i :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The identification `realizationFibreIso` carries the projection of the fibre to the chart to
the base change map of the realization. -/
@[reassoc (attr := simp)]
theorem realizationFibreIso_hom_projection (i : I) :
    (realizationFibreIso r e i).hom ≫
        chartBaseChangeProjection B S hS (c.ι.app i).left (realizationChart r e) =
      r.baseChange.app i ≫ (realizationChartIso r e).hom :=
  IsPullback.isoIsPullback_hom_snd _ _ _ _

/-- The identifications are compatible with the transition maps of the family. -/
theorem realizationFibreIso_naturality {i j : I} (θ : i ⟶ j) :
    E.U.map θ ≫ (realizationFibreIso r e j).hom =
      (realizationFibreIso r e i).hom ≫
        chartBaseChangeSpaceMap B S hS (D.map θ).left
          (by rw [← Over.comp_left, c.w]) (realizationChart r e) := by
  refine (isPullback_chartBaseChangeInclusion B S hS (c.ι.app j).left
    (realizationChart r e)).hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    refine (congrArg (E.U.map θ ≫ ·) (realizationFibreIso_hom_inclusion r e j)).trans
      (Eq.trans ?_ (congrArg ((realizationFibreIso r e i).hom ≫ ·)
        (chartBaseChangeSpaceMap_inclusion B S hS (D.map θ).left _
          (realizationChart r e))).symm)
    exact (E.projection.naturality θ).trans
      (congrArg (· ≫ (D.map θ).left) (realizationFibreIso_hom_inclusion r e i).symm |>.trans
        (Category.assoc _ _ _))
  · refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    refine (congrArg (E.U.map θ ≫ ·) (realizationFibreIso_hom_projection r e j)).trans
      (Eq.trans ?_ (congrArg ((realizationFibreIso r e i).hom ≫ ·)
        (chartBaseChangeSpaceMap_projection B S hS (D.map θ).left _
          (realizationChart r e))).symm)
    refine (Category.assoc _ _ _).symm.trans (Eq.trans ?_
      (realizationFibreIso_hom_projection r e i).symm)
    exact congrArg (· ≫ (realizationChartIso r e).hom)
      ((r.baseChange.naturality θ).trans (Category.comp_id _))

end Realization


/-! ### The equalizer of global functions over the affine realizations of the Čech nerve -/

section Final

variable {X Y : AlgebraicSpaces B S hS} {g : Y ⟶ X} (hg : IsProper B S hS g.hom)

/-- **Over a chart `W₀ = X' ×_X V` of `X'`, the global functions are an equalizer**:
`AlgebraicGeometry.Space.globalFunctionsEqualizer_cech` read over `W₀`. -/
theorem chartGlobalFunctionsEqualizer_of_isPullback (Vc : SmallEtale B S hS X.1)
    (W₀ : SmallEtale B S hS (kernelPairSpec hg).obj.left.1) (q₀ : W₀.obj.left ⟶ Vc.obj.left)
    (hW : IsPullback W₀.obj.hom (yoneda.map q₀) (kernelPairSpecToTarget hg).hom Vc.obj.hom) :
    ChartGlobalFunctionsEqualizer (cechFace hg 0) (cechFace hg 1) W₀ := by
  have hWsp : IsPullback (chartToSpace B S hS (kernelPairSpec hg).obj.left W₀)
      (ObjectProperty.homMk (yoneda.map q₀) :
        (SpacesEtale.toSpaces B S hS (kernelPairSpec hg).obj.left).obj
            ((comparisonFunctor B S hS (kernelPairSpec hg).obj.left).obj W₀) ⟶
          (SpacesEtale.toSpaces B S hS X).obj ((comparisonFunctor B S hS X).obj Vc))
      (kernelPairSpecToTarget hg) (chartToSpace B S hS X Vc) :=
    IsPullback.of_map (ObjectProperty.ι _) (ObjectProperty.hom_ext _ hW.w) hW
  let θ := hWsp.isoIsPullback _ _ (isPullback_chartBaseChangeInclusion B S hS
    (kernelPairSpecToTarget hg) Vc)
  have hθ : θ.hom ≫ chartBaseChangeInclusion B S hS (kernelPairSpecToTarget hg) Vc =
      chartToSpace B S hS (kernelPairSpec hg).obj.left W₀ :=
    IsPullback.isoIsPullback_hom_fst _ _ _ _
  exact GlobalFunctionsEqualizer.of_iso θ
    (chartBaseChangeSpaceTransIso (kernelPairSpecToTarget hg) Vc W₀ θ hθ _)
    (chartBaseChangeSpaceTransIso (kernelPairSpecToTarget hg) Vc W₀ θ hθ _)
    (chartBaseChangeProjection_trans _ Vc W₀ θ hθ _)
    (chartBaseChangeSpaceMap_trans _ Vc W₀ θ hθ (cechFace hg 0).left (Over.w (cechFace hg 0)))
    (chartBaseChangeSpaceMap_trans _ Vc W₀ θ hθ (cechFace hg 1).left (Over.w (cechFace hg 1)))
    (globalFunctionsEqualizer_cech hg Vc)

/-- **The equalizer over an affine realization, from the equalizer over its chart.** -/
theorem globalFunctionsEqualizer_of_chartGlobalFunctionsEqualizer
    (E : CompatibleEtaleDiagram B S hS
      (cechDiagram (kernelPairSpecπ hg) (kernelPairSpecToTarget hg)))
    (r : EtaleRealization B S hS
      (cechCocone (kernelPairSpecπ hg) (kernelPairSpecToTarget hg)) E)
    {T : BigFppfOver B S hS} (e : r.U.obj ≅ yoneda.obj T)
    (h : ChartGlobalFunctionsEqualizer (cechFace hg 0) (cechFace hg 1) (realizationChart r e)) :
    GlobalFunctionsEqualizer (r.baseChange.app (op ⦋0⦌))
      (E.U.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op)
      (E.U.map (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op) :=
  GlobalFunctionsEqualizer.of_iso (realizationChartIso r e)
    (realizationFibreIso r e (op ⦋0⦌)) (realizationFibreIso r e (op ⦋1⦌))
    (realizationFibreIso_hom_projection r e (op ⦋0⦌)).symm
    (realizationFibreIso_naturality r e (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0).op)
    (realizationFibreIso_naturality r e (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1).op) h

end Final

/-- **The equalizer of global functions over the affine realizations of the Čech nerve of
`π : Y ⟶ X'`** (the last paragraph of the proof of Stacks 0AGG).  For an affine `B'` étale over
`X` and an affine realization `U` over `X' ×_X B'` of a compatible étale family over the Čech
nerve, `Γ(U) ⟶ Γ(U ×_{X'} Y) ⇉ Γ(U ×_{X'} Y ×_{X'} Y)` is an equalizer.

Over the affine chart `W₀ = X' ×_X B'` of `X'` this is the definition of
`𝒜 = Equalizer(g_* 𝒪_Y ⇉ h_* 𝒪_R)` together with `ν_* 𝒪_{X'} ≅ 𝒜`
(`AlgebraicGeometry.Space.chartGlobalFunctionsEqualizer_of_isPullback`); it passes to the affine
chart `U` above `W₀` by quasi-coherence
(`AlgebraicGeometry.Space.ChartGlobalFunctionsEqualizer.of_hom`), and the members of the family
are the fibres over `U`
(`AlgebraicGeometry.Space.globalFunctionsEqualizer_of_chartGlobalFunctionsEqualizer`). -/
theorem kernelPairSpecGlobalFunctionsEqualizer : KernelPairSpecGlobalFunctionsEqualizer B S hS := by
  intro X Y g hX hg B' b hB' hb E r hr u hu
  obtain ⟨V₀, hV₀, ⟨eB⟩⟩ := hB'
  obtain ⟨VU, hVU, ⟨eU⟩⟩ := hr
  have hbV : IsEtale B S hS (eB.inv ≫ b.hom) :=
    isEtale_comp B S hS (isEtale_of_isIso B S hS eB.inv) hb
  obtain ⟨W, p₀, q₀, hW⟩ := (kernelPairSpec hg).property ⟨V₀, hV₀⟩ (eB.inv ≫ b.hom)
  let W₀ : SmallEtale B S hS (kernelPairSpec hg).obj.left.1 :=
    ⟨CostructuredArrow.mk p₀,
      presheaf_etale_of_isEtale B S hS (isEtale_of_isPullback_yoneda B S hS hW.flip hbV)⟩
  have hℓ : (eU.inv ≫ r.toX.hom) ≫ (kernelPairSpec hg).obj.hom.hom =
      (eU.inv ≫ u.hom ≫ eB.hom) ≫ (eB.inv ≫ b.hom) := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact congrArg (eU.inv ≫ ·) (congrArg (fun k => k.hom) hu)
  let m : realizationChart r eU ⟶ W₀ :=
    ObjectProperty.homMk (CostructuredArrow.homMk (yoneda.preimage (hW.lift _ _ hℓ))
      ((congrArg (· ≫ p₀) (yoneda.map_preimage (hW.lift _ _ hℓ))).trans (hW.lift_fst _ _ hℓ)))
  exact globalFunctionsEqualizer_of_chartGlobalFunctionsEqualizer hg E r eU
    (ChartGlobalFunctionsEqualizer.of_hom (W := W₀) (W' := realizationChart r eU)
      (cechFace hg 0) (cechFace hg 1)
      (isProper_cechBase_zero hg hX).2.1.2
      (isQuasiSeparated_of_isSeparated B S hS (isProper_cechBase_zero hg hX).1)
      (isProper_cechBase_one hg hX).2.1.2
      (isQuasiSeparated_of_isSeparated B S hS (isProper_cechBase_one hg hX).1)
      W.property hVU m
      (chartGlobalFunctionsEqualizer_of_isPullback hg
        ⟨CostructuredArrow.mk (eB.inv ≫ b.hom), presheaf_etale_of_isEtale B S hS hbV⟩ W₀ q₀ hW))

/-- **Stacks 0AGG**, from étale descent of algebraic spaces along proper surjective morphisms
alone: the coequalizer property of `X' = \underline{Spec}_X(𝒜)` is Stacks 0GHL for the Čech nerve
of `π : Y ⟶ X'`, whose condition (1) is that descent and whose condition (2) is
`AlgebraicGeometry.Space.kernelPairSpecGlobalFunctionsEqualizer`. -/
theorem properKernelPairCoequalizers
    (h : EtaleSpaceDescentAlongProperSurjective B S hS) :
    ProperKernelPairCoequalizers B S hS :=
  properKernelPairCoequalizers_of_etaleSpaceDescent_of_globalFunctionsEqualizer h
    kernelPairSpecGlobalFunctionsEqualizer

end AlgebraicGeometry.Space

end
