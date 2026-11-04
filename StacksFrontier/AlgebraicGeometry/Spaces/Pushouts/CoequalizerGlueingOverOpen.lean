module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.CoproductCountable
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteMorphismSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.CoequalizerGlueing
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingSpacesGraph
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedCriteria

/-!
# The glueing coequalizer is proper over the target and an isomorphism over the open part

In the proper-modification situation of Stacks 0AGH put `Y = X' ⨿ Z`, let `g : Y ⟶ X` be `f` on
`X'` and the closed immersion `i` on `Z`, and let `π : Y ⟶ X₁` be a coequalizer of the kernel
pair `R = Y ×_X Y ⇉ Y`, with induced morphism `X₁ ⟶ X`. This file proves the two inputs of
Stacks 0AGI which do not come out of the statement of Stacks 0AGG:

* the morphism `g` is proper, so that Stacks 0AGG applies to it;
* the morphism `X₁ ⟶ X` is an isomorphism over the open complement `U` of `Z`, as soon as
  `X₁ ⟶ X` is separated and `π` is quasi-compact. Both are consequences of Stacks 0AGG (the first
  of its clause (1), the second of its clause (2)), so this is an unconditional clause of
  Stacks 0AGI once Stacks 0AGG is.

## Main results

* `AlgebraicGeometry.Space.CoequalizerGlueSituation.isProper_glueMap`: `g : X' ⨿ Z ⟶ X` is
  proper.
* `AlgebraicGeometry.Space.KernelPairCoequalizer.schemeTheoreticImageSubfunctor_π_eq_top`: the
  quotient morphism of a coequalizer of a kernel pair is scheme-theoretically dominant.
* `AlgebraicGeometry.Space.CoequalizerGlueSituation.isIso_pullback_snd_toTarget`: `X₁ ⟶ X` is an
  isomorphism over `U` when it is separated and `π` is quasi-compact.

## Implementation notes

Properness of `g` is `AlgebraicGeometry.Space.isProper_of_isColimit_cofan`, applied to the
binary coproduct read as a cofan indexed by `ULift Bool`: the inclusion of the algebraic spaces
into the fppf sheaves creates countable coproducts, so the coproduct of the category of algebraic
spaces is a coproduct of sheaves.

The source proves "isomorphism over `U`" from the construction of `X₁` inside the proof of
Stacks 0AGG (its formation commutes with étale localization on `X`). The argument here uses only
the universal property of the coequalizer, through scheme-theoretic images:

1. `π` factors through its scheme-theoretic image, a closed subspace of `X₁`; the corestriction
   still coequalizes the kernel pair, so the universal property splits the inclusion of the image
   and the image is all of `X₁`.
2. Write `V = X₁ ×_X U` and `p : V ⟶ U`. The scheme-theoretic image of the quasi-compact `π`
   commutes with the étale base change `V ⟶ X₁` (Stacks 082Z, part (3)), so the base change
   `π_V : Y ×_{X₁} V ⟶ V` is scheme-theoretically dominant too.
3. Since `f` is an isomorphism over `U`, the composite `U ≅ X' ×_X U ⟶ X' ⟶ Y ⟶ X₁` lifts to a
   section `σ : U ⟶ V` of `p`, a closed immersion because `p` is separated (Stacks 03KP).
4. `π_V` factors through `σ`: for a section `(y, v)` of `Y ×_{X₁} V`, the pair formed by `y` and
   the point of `X'` over `p(v)` is a section of the kernel pair `R`, which `π` coequalizes. So
   the range of `σ` contains the scheme-theoretic image of `π_V`, which is `V`; `σ` is then an
   isomorphism and so is `p`.

## References

* [Stacks Project, Tag 0AGH](https://stacks.math.columbia.edu/tag/0AGH)
* [Stacks Project, Tag 0AGI](https://stacks.math.columbia.edu/tag/0AGI)
* [Stacks Project, Tag 0AGG](https://stacks.math.columbia.edu/tag/0AGG)
* [Stacks Project, Tag 082Z](https://stacks.math.columbia.edu/tag/082Z)
* [Stacks Project, Tag 03KP](https://stacks.math.columbia.edu/tag/03KP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Scheme-theoretic dominance of the quotient morphism -/

namespace KernelPairCoequalizer

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS} {g : Y ⟶ X} (D : KernelPairCoequalizer B S hS g)

/-- The quotient morphism `π : Y ⟶ X'` of a coequalizer of the kernel pair of `g` is
scheme-theoretically dominant: its scheme-theoretic image is all of `X'`. The corestriction of
`π` to its scheme-theoretic image still coequalizes the kernel pair, so the universal property of
the coequalizer splits the inclusion of the image. -/
theorem schemeTheoreticImageSubfunctor_π_eq_top :
    schemeTheoreticImageSubfunctor B S hS D.π.hom = ⊤ := by
  let W := schemeTheoreticImageSubfunctor B S hS D.π.hom
  have hle : Subfunctor.range D.π.hom ≤ W :=
    range_le_schemeTheoreticImageSubfunctor B S hS D.π.hom
  let Wsp : AlgebraicSpaces B S hS := ⟨W.toFunctor,
    (isClosedSubspace_schemeTheoreticImageSubfunctor B S hS D.π.hom D.space.property).1⟩
  let ιW : Wsp ⟶ D.space := ObjectProperty.homMk W.ι
  let ℓ : Y ⟶ Wsp := ObjectProperty.homMk (Subfunctor.lift (G := W) D.π.hom hle)
  have hℓ : ℓ ≫ ιW = D.π := ObjectProperty.hom_ext _ (Subfunctor.lift_ι D.π.hom hle)
  have hmono : ∀ {A : AlgebraicSpaces B S hS} (a b : A ⟶ Wsp), a ≫ ιW = b ≫ ιW → a = b :=
    fun a b h => ObjectProperty.hom_ext _ ((cancel_mono W.ι).1
      (congrArg InducedCategory.Hom.hom h))
  have heq : pullback.fst g g ≫ ℓ = pullback.snd g g ≫ ℓ :=
    hmono _ _ (by rw [Category.assoc, Category.assoc, hℓ, D.equalizes])
  let r : D.space ⟶ Wsp := D.isColimit.desc (Cofork.ofπ ℓ heq)
  have hr : D.π ≫ r = ℓ := Cofork.IsColimit.π_desc (s := Cofork.ofπ D.π D.equalizes)
    (t := Cofork.ofπ ℓ heq) D.isColimit
  have hrι : r ≫ ιW = 𝟙 _ := by
    refine Cofork.IsColimit.hom_ext D.isColimit ?_
    show D.π ≫ r ≫ ιW = D.π ≫ 𝟙 _
    rw [← Category.assoc, hr, hℓ, Category.comp_id]
  have hrι' : r.hom ≫ W.ι = 𝟙 _ := congrArg InducedCategory.Hom.hom hrι
  exact (Subfunctor.eq_top_iff_isIso W).2 ⟨⟨r.hom, (cancel_mono W.ι).1 (by
    rw [Category.assoc, hrι', Category.comp_id, Category.id_comp]), hrι'⟩⟩

end KernelPairCoequalizer

namespace CoequalizerGlueSituation

variable (T : CoequalizerGlueSituation.{u})

/-! ### Properness of the glueing morphism -/

/-- The two summands `X'` and `Z` of `Y = X' ⨿ Z`, as a family indexed by `ULift Bool`. -/
def summand : ULift.{u} Bool → AlgebraicSpaces T.B T.S T.hS
  | ⟨false⟩ => T.modificationSpace
  | ⟨true⟩ => T.closedSpace

/-- The two coproduct inclusions into `Y = X' ⨿ Z`, as a cofan of
`AlgebraicGeometry.Space.CoequalizerGlueSituation.summand`. -/
def summandIncl : ∀ b, T.summand b ⟶ T.glueSource
  | ⟨false⟩ => coprod.inl
  | ⟨true⟩ => coprod.inr

/-- `Y = X' ⨿ Z` is the colimit of the two-member cofan of its coproduct inclusions. -/
def isColimitSummandCofan : IsColimit (Cofan.mk T.glueSource T.summandIncl) := by
  refine Cofan.IsColimit.mk _ (fun s => coprod.desc (s.inj ⟨false⟩) (s.inj ⟨true⟩)) ?_ ?_
  · rintro s ⟨_ | _⟩
    · exact coprod.inl_desc _ _
    · exact coprod.inr_desc _ _
  · exact fun s m hm => coprod.hom_ext ((hm ⟨false⟩).trans (coprod.inl_desc _ _).symm)
      ((hm ⟨true⟩).trans (coprod.inr_desc _ _).symm)

/-- **The glueing morphism `g : X' ⨿ Z ⟶ X` is proper.** It is `f` on `X'`, which is proper by
the hypotheses of Stacks 0AGH, and the closed immersion `i` on `Z`, which is proper by
Stacks 04XZ; a morphism out of a finite coproduct of algebraic spaces whose restrictions to the
summands are proper is proper. -/
theorem isProper_glueMap : IsProper T.B T.S T.hS T.glueMap.hom := by
  let A := algebraicSpacesToSheaf T.B T.S T.hS
  refine isProper_of_isColimit_cofan T.B T.S T.hS (fun b => A.map (T.summandIncl b))
    (isColimitCofanMkObjOfIsColimit A T.summand T.summandIncl T.isColimitSummandCofan)
    (fun b => (T.summand b).property) T.glueSource.property T.hX T.glueMap.hom ?_
  rintro ⟨_ | _⟩
  · show IsProper T.B T.S T.hS ((coprod.inl : T.modificationSpace ⟶ T.glueSource).hom ≫
      T.glueMap.hom)
    exact T.inl_comp_glueMap ▸ T.hf
  · show IsProper T.B T.S T.hS ((coprod.inr : T.closedSpace ⟶ T.glueSource).hom ≫
      T.glueMap.hom)
    exact T.inr_comp_glueMap ▸ isProper_of_isClosedImmersion T.B T.S T.hS T.hZ T.hX T.i T.hi

/-! ### The coequalizer is an isomorphism over the open part -/

/-- The inverse of `f` over `U`: the morphism `U ≅ X' ×_X U ⟶ X'`. -/
def sectionOverU : T.U.toFunctor ⟶ T.X' :=
  have := T.f_iso_over_U
  inv (pullback.snd T.f T.U.ι) ≫ pullback.fst T.f T.U.ι

/-- The morphism `U ⟶ X'` is a section of `f` over `U`: composed with `f` it is the inclusion
`U ⟶ X`. -/
theorem sectionOverU_comp_f : T.sectionOverU ≫ T.f = T.U.ι := by
  have := T.f_iso_over_U
  rw [sectionOverU, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

variable {T} (D : KernelPairCoequalizer T.B T.S T.hS T.glueMap)

/-- The quotient morphism `Y ⟶ X₁` followed by the induced morphism `X₁ ⟶ X` is the glueing
morphism `g : Y ⟶ X`. -/
theorem π_comp_toTarget : D.π.hom ≫ D.toTarget.hom = T.glueMap.hom :=
  congrArg InducedCategory.Hom.hom D.fac

/-- The section `U ⟶ X₁ ×_X U` of the projection to `U`, given on the first factor by
`U ≅ X' ×_X U ⟶ X' ⟶ Y ⟶ X₁`. -/
def openSection : T.U.toFunctor ⟶ pullback D.toTarget.hom T.U.ι :=
  pullback.lift (T.sectionOverU ≫ (coprod.inl : T.modificationSpace ⟶ T.glueSource).hom ≫
      D.π.hom) (𝟙 _) (by
    rw [Category.assoc, Category.assoc, π_comp_toTarget, T.inl_comp_glueMap,
      T.sectionOverU_comp_f, Category.id_comp])

/-- `AlgebraicGeometry.Space.CoequalizerGlueSituation.openSection` is a section of the projection
`X₁ ×_X U ⟶ U`. -/
@[simp]
theorem openSection_snd : openSection D ≫ pullback.snd D.toTarget.hom T.U.ι = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The fibre product `X₁ ×_X U` is an algebraic space. -/
private theorem isAlgebraicSpace_pullback_toTarget_U :
    IsAlgebraicSpace T.B T.S T.hS (pullback D.toTarget.hom T.U.ι) :=
  isAlgebraicSpace_pullback T.B T.S T.hS _ _ D.space.property T.hU.1 T.hX

/-- The base change `Y ×_{X₁} V ⟶ V` of the quotient morphism to `V = X₁ ×_X U` factors through
the section `AlgebraicGeometry.Space.CoequalizerGlueSituation.openSection`: a section `(y, v)` of
`Y ×_{X₁} V` and the point of `X'` over the image of `v` in `U` form a section of the kernel
pair `R = Y ×_X Y`, which the quotient morphism coequalizes. -/
theorem pullback_snd_π_eq :
    pullback.snd D.π.hom (pullback.fst D.toTarget.hom T.U.ι) =
      (pullback.snd D.π.hom (pullback.fst D.toTarget.hom T.U.ι) ≫
        pullback.snd D.toTarget.hom T.U.ι) ≫ openSection D := by
  set j := pullback.fst D.toTarget.hom T.U.ι
  set p := pullback.snd D.toTarget.hom T.U.ι
  set a := pullback.fst D.π.hom j
  set b := pullback.snd D.π.hom j
  let incl := (coprod.inl : T.modificationSpace ⟶ T.glueSource).hom
  have hV := isAlgebraicSpace_pullback_toTarget_U D
  let Wsp : AlgebraicSpaces T.B T.S T.hS := ⟨pullback D.π.hom j,
    isAlgebraicSpace_pullback T.B T.S T.hS _ _ T.glueSource.property hV D.space.property⟩
  let c : pullback D.π.hom j ⟶ T.glueSource.obj := b ≫ p ≫ T.sectionOverU ≫ incl
  have hab : a ≫ T.glueMap.hom = c ≫ T.glueMap.hom := by
    rw [← π_comp_toTarget D, ← Category.assoc, pullback.condition, Category.assoc,
      pullback.condition]
    simp only [c, incl, Category.assoc, π_comp_toTarget, T.inl_comp_glueMap,
      T.sectionOverU_comp_f]
    rfl
  let L : Wsp ⟶ T.relation := pullback.lift (ObjectProperty.homMk a : Wsp ⟶ T.glueSource)
    (ObjectProperty.homMk c) (ObjectProperty.hom_ext _ hab)
  have hac : a ≫ D.π.hom = c ≫ D.π.hom := by
    have h1 : L ≫ pullback.fst T.glueMap T.glueMap = ObjectProperty.homMk a :=
      pullback.lift_fst _ _ _
    have h2 : L ≫ pullback.snd T.glueMap T.glueMap = ObjectProperty.homMk c :=
      pullback.lift_snd _ _ _
    have h : (L ≫ pullback.fst T.glueMap T.glueMap) ≫ D.π =
        (L ≫ pullback.snd T.glueMap T.glueMap) ≫ D.π := by
      rw [Category.assoc, Category.assoc, D.equalizes]
    rw [h1, h2] at h
    exact congrArg InducedCategory.Hom.hom h
  refine pullback.hom_ext ?_ ?_
  · show b ≫ j = (b ≫ p) ≫ openSection D ≫ j
    rw [openSection, pullback.lift_fst, ← pullback.condition, hac]
    simp only [c, incl, Category.assoc]
  · rw [Category.assoc, openSection_snd, Category.comp_id]

/-- **The morphism `X₁ ⟶ X` is an isomorphism over the open complement `U` of `Z`**, provided
`X₁ ⟶ X` is separated and the quotient morphism `Y ⟶ X₁` is quasi-compact; both hold by
Stacks 0AGG. -/
theorem isIso_pullback_snd_toTarget
    (hsep : IsSeparated T.B T.S T.hS D.toTarget.hom)
    (hqc : IsQuasiCompact T.B T.S T.hS D.π.hom) :
    IsIso (pullback.snd D.toTarget.hom T.U.ι) := by
  set j := pullback.fst D.toTarget.hom T.U.ι
  set p := pullback.snd D.toTarget.hom T.U.ι
  set σ := openSection D
  have hV := isAlgebraicSpace_pullback_toTarget_U D
  have hj : IsEtale T.B T.S T.hS j :=
    isEtale_pullback_fst T.B T.S T.hS D.space.property T.hX T.hU.1 _ _
      (isEtale_of_isOpenImmersion T.B T.S T.hS T.hU.2)
  have himage : schemeTheoreticImageSubfunctor T.B T.S T.hS (pullback.snd D.π.hom j) = ⊤ := by
    rw [schemeTheoreticImageSubfunctor_pullback_snd_of_isEtale_of_isQuasiCompact' T.B T.S T.hS
      D.π.hom j T.glueSource.property D.space.property hV hqc hj,
      D.schemeTheoreticImageSubfunctor_π_eq_top]
    rfl
  have hσp : σ ≫ p = 𝟙 _ := openSection_snd D
  have hσci : IsClosedImmersion T.B T.S T.hS σ :=
    isClosedImmersion_of_isSeparated_of_section T.B T.S T.hS p (isSeparated_of_isPullback T.B T.S
      T.hS (IsPullback.of_hasPullback D.toTarget.hom T.U.ι) hsep) σ hσp
  have hrange : Subfunctor.range σ = ⊤ := by
    rw [← top_le_iff, ← himage]
    refine schemeTheoreticImageSubfunctor_le T.B T.S T.hS _
      (isClosedSubspace_range_of_isClosedImmersion T.B T.S T.hS σ T.hU.1 hσci) ?_
    rw [pullback_snd_π_eq D]
    exact Subfunctor.range_comp_le _ _
  have : IsSplitMono σ := IsSplitMono.mk' { retraction := p, id := hσp }
  have : IsIso (Subfunctor.range σ).ι := (Subfunctor.eq_top_iff_isIso _).1 hrange
  have : IsIso σ := by
    rw [← Subfunctor.toRange_ι σ]
    infer_instance
  have : IsIso (σ ≫ p) := by rw [hσp]; infer_instance
  exact IsIso.of_isIso_comp_left σ p

/-! ### Assembling the clauses of Stacks 0AGI from the conclusion of Stacks 0AGG -/

/-- The clauses of **Stacks 0AGI** for an arbitrary coequalizer `X₁` of the kernel pair of
`g : X' ⨿ Z ⟶ X`, derived from the conclusion of Stacks 0AGG: `X₁ ⟶ X` is finite, a universal
homeomorphism, and an isomorphism over `U`, and `Z ⟶ X` lifts to `X₁`. -/
theorem glueCoequalizer_clauses_of_properKernelPairCoequalizers
    (hAGG : ProperKernelPairCoequalizers T.B T.S T.hS) :
    IsFinite T.B T.S T.hS D.toTarget.hom ∧
      UniversalHomeomorphism T.B T.S T.hS D.toTarget.hom ∧
      IsIso (pullback.snd D.toTarget.hom T.U.ι) ∧
      ∃ l : T.closedSpace ⟶ D.space, l ≫ D.toTarget = ObjectProperty.homMk T.i := by
  have hfin : IsFinite T.B T.S T.hS D.toTarget.hom :=
    hAGG.isFinite_toTarget T.glueMap T.locallyNoetherian T.isProper_glueMap D
  exact ⟨hfin, hAGG.universalHomeomorphism_toTarget T.glueMap T.locallyNoetherian
    T.isProper_glueMap T.isSurjective_glueMap D, isIso_pullback_snd_toTarget D
    (isSeparated_of_isFinite T.B T.S T.hS _ D.space.property T.hX hfin)
    (hAGG.isProper_π T.glueMap T.locallyNoetherian T.isProper_glueMap D).2.1.2,
    ⟨coprod.inr ≫ D.π, T.glueCoequalizer_closedSubspace_lift D⟩⟩

/-- **Stacks 0AGI**, from the conclusion of Stacks 0AGG: the kernel pair of
`g : X' ⨿ Z ⟶ X` has a coequalizer `X₁`, and `X₁ ⟶ X` is a finite universal homeomorphism and an
isomorphism over `U`, through which `Z ⟶ X` lifts. -/
theorem exists_glueCoequalizer_of_properKernelPairCoequalizers
    (hAGG : ProperKernelPairCoequalizers T.B T.S T.hS) :
    ∃ D : KernelPairCoequalizer T.B T.S T.hS T.glueMap,
      IsFinite T.B T.S T.hS D.toTarget.hom ∧
      UniversalHomeomorphism T.B T.S T.hS D.toTarget.hom ∧
      IsIso (pullback.snd D.toTarget.hom T.U.ι) ∧
      ∃ l : T.closedSpace ⟶ D.space, l ≫ D.toTarget = ObjectProperty.homMk T.i := by
  obtain ⟨D⟩ := hAGG.nonempty_coequalizer T.glueMap T.locallyNoetherian T.isProper_glueMap
  exact ⟨D, glueCoequalizer_clauses_of_properKernelPairCoequalizers D hAGG⟩

end CoequalizerGlueSituation

end AlgebraicGeometry.Space

end
