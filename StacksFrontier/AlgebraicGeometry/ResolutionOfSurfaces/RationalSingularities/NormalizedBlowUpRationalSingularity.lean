module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedBlowUpReduction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.LocalBirationalExtensions
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.HigherDirectImageBoundedness
public import StacksFrontier.AlgebraicGeometry.Variety.GeometricFieldChange.QuasiFiniteCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.BirationalIsIso
public import StacksFrontier.AlgebraicGeometry.Morphisms.ModificationProperties
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.Projective
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.QuasiProjectiveOverAmpleBase
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.Basic
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdeals
public import StacksFrontier.AlgebraicGeometry.HProjective.AmpleBase
public import StacksCore.Tactic.StacksAttribute

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

noncomputable section

/-! ### Projectivity: elementary consequences of the H-form of Tag 0BCL -/

/-- A finite morphism is quasi-projective: it is of finite type, and its structure sheaf is
relatively ample because the inverse image of an affine open is affine. -/
public theorem isQuasiProjective_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] :
    IsQuasiProjective f := by
  refine ⟨⟨inferInstance, inferInstance⟩, Stacks.Ample.unitModule X,
    Stacks.Ample.isInvertibleModule_unit X, ?_⟩
  refine (Stacks.AmpleBridge.isRelativelyAmple_iff_isRelativelyAmple f
    (Stacks.Ample.unitModule X)).mp ?_
  refine (Stacks.RelativeAmple.isRelativelyAmple_unitModule_iff f).mpr ?_
  intro V hV
  have : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
  infer_instance

/-- A finite morphism to a base carrying an ample invertible module is H-projective. -/
public theorem isProjectiveMorphism_of_isFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f]
    (M : S.Modules) [Stacks.Ample.IsInvertibleModule S M] (hM : Stacks.Ample.IsAmple S M) :
    IsProjectiveMorphism f :=
  isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
    ⟨isHQuasiProjective_of_isQuasiProjective f M hM (isQuasiProjective_of_isFinite f),
      inferInstance⟩

/-- A proper quasi-projective morphism to a base carrying an ample invertible module is
H-projective: Tag 087S part (2) and the H-form of Tag 0BCL, both unconditional. -/
public theorem isProjectiveMorphism_of_isQuasiProjective {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
    (M : S.Modules) [Stacks.Ample.IsInvertibleModule S M] (hM : Stacks.Ample.IsAmple S M)
    (hf : IsQuasiProjective f) : IsProjectiveMorphism f :=
  isProjectiveMorphism_iff_isHQuasiProjective_and_isProper.mpr
    ⟨isHQuasiProjective_of_isQuasiProjective f M hM hf, inferInstance⟩

/-- The source of an H-projective morphism to a base carrying an ample invertible module again
carries one. -/
public theorem exists_isAmple_of_isProjectiveMorphism {X S : Scheme.{u}} (f : X ⟶ S)
    (M : S.Modules) [Stacks.Ample.IsInvertibleModule S M] (hM : Stacks.Ample.IsAmple S M)
    (hf : IsProjectiveMorphism f) :
    ∃ (L : X.Modules) (hL : Stacks.Ample.IsInvertibleModule X L),
      letI := hL; Stacks.Ample.IsAmple X L :=
  exists_isAmple_of_isQuasiProjective f M hM
    (isQuasiProjective_of_isHQuasiProjective f hf.isHQuasiProjective)

/-! ### The hypothesis standing for Tag 02NS -/

/-- **[Stacks, Tag 02NS] for the blowup of a finite-type ideal sheaf, as a proposition.**
The blowup morphism of a quasi-coherent ideal sheaf of finite type is quasi-projective.

It is proved as `AlgebraicGeometry.blowUpIsQuasiProjective`. -/
public def BlowUpIsQuasiProjective : Prop :=
  ∀ ⦃X : Scheme.{u}⦄ (I : X.IdealSheafData), Scheme.IdealSheafData.IsFiniteType I →
    IsQuasiProjective (blowUpToBase I)

/-- On a locally Noetherian scheme every quasi-coherent ideal sheaf is of finite type. -/
public theorem isFiniteType_of_isLocallyNoetherian {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData) : Scheme.IdealSheafData.IsFiniteType I := by
  intro U
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  exact IsNoetherian.noetherian (I.ideal U)

/-- **The structure morphism of a sequence of normalized blowups is H-projective.**  Each stage
carries an ample invertible module because it is H-projective over the base; over such a stage
the blowup step is H-projective by Tag 02NS, given as `h02NS`, and the normalization step is
H-projective because it is finite. -/
public theorem NormalizedBlowUpSeq.isProjectiveMorphism (h02NS : BlowUpIsQuasiProjective.{u})
    {S X : Scheme.{u}} {f : X ⟶ S} (hseq : NormalizedBlowUpSeq S X f)
    (hS : IsNagataScheme S) [IsLocallyNoetherian S] [IsNormal S]
    (M : S.Modules) [Stacks.Ample.IsInvertibleModule S M] (hM : Stacks.Ample.IsAmple S M) :
    IsProjectiveMorphism f := by
  induction hseq with
  | refl => exact isProjectiveMorphism_of_isFinite (CategoryTheory.CategoryStruct.id S) M hM
  | blowUp prev hX x hx ih =>
    obtain ⟨hNagataX, hNoethX, -, -⟩ := prev.properties hS
    have := hNoethX
    obtain ⟨L, hLinv, hLample⟩ := exists_isAmple_of_isProjectiveMorphism _ M hM ih
    have := hLinv
    set I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds _)
    -- the blowup step
    have hblow : IsProjectiveMorphism (blowUpToBase I) :=
      isProjectiveMorphism_of_isQuasiProjective _ L hLample
        (h02NS I (isFiniteType_of_isLocallyNoetherian I))
    obtain ⟨N, hNinv, hNample⟩ := exists_isAmple_of_isProjectiveMorphism _ L hLample hblow
    have := hNinv
    -- the normalization step
    have hNagataBlow : IsNagataScheme (AlgebraicGeometry.blowUp I) :=
      isNagataScheme_of_locallyOfFiniteType (blowUpToBase I) hNagataX
    have hfin := Stacks.Blowup.finite_irreducibleComponents_blowUp I hX
    have : IsFinite (Scheme.normalization (AlgebraicGeometry.blowUp I) hfin) :=
      Scheme.isFinite_normalization hNagataBlow hfin
    have hnorm : IsProjectiveMorphism (Scheme.normalization (AlgebraicGeometry.blowUp I) hfin) :=
      isProjectiveMorphism_of_isFinite _ N hNample
    exact (hnorm.comp hblow).comp ih

/-! ### Propositions for Tags 0AXF (1), 02KH, 0AB7 and Step 4 of Tag 0BG0 -/

open GlueingNearPoint in
/-- **The first conclusion of [Stacks, Tag 0AXF], as a proposition.**  For two modifications
`f : X ⟶ Spec(A)` and `g ≫ f : X' ⟶ Spec(A)` of the spectrum of a two-dimensional normal local
Nagata domain, with `X` and `X'` normal, the Leray sequence
`0 ⟶ H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'}) ⟶ H⁰(X, R¹g_*𝒪_{X'}) ⟶ 0`
is exact.  Only the two consequences the source's proof uses are asked for: the first map is
injective, and if it is also surjective then `R¹g_*𝒪_{X'}` has no global sections.

Both follow from the exactness of that one sequence, so this is a weakening of the tag's first
conclusion, not a strengthening.  The tag's second and third conclusions are available here, as
`topologicalKrullDim_supp_rightDerived_one_pushforward_le_zero` and
`nonempty_generatingSections_rightDerived_one_pushforward` in the namespace
`AlgebraicGeometry.SemistableReduction.TwoModifications`; this proposition is proved, for a
two-dimensional base, as `AlgebraicGeometry.lerayFirstCohomologyExact_of_ringKrullDim_eq_two`. -/
public def LerayFirstCohomologyExact (A : Type u) [CommRing A] [IsDomain A] : Prop :=
  ∀ ⦃X X' : Scheme.{u}⦄ (f : X ⟶ Spec (.of A)) (g : X' ⟶ X), IsNormal X → IsNormal X' →
    IsModification f → IsModification (g ≫ f) →
      ∃ φ : firstCohomologyAsBaseModule X f →ₗ[A] firstCohomologyAsBaseModule X' (g ≫ f),
        Function.Injective φ ∧ (Function.Surjective φ →
          Subsingleton (((Scheme.Modules.pushforward g).rightDerived 1).obj
            (SheafOfModules.unit X'.ringCatSheaf)).sections)

/-- **[Stacks, Tag 02KH], flat base change for the first higher direct image, as a
proposition.**  If `g : X' ⟶ X` is proper and `Y` is its base change along the flat morphism
`Spec 𝒪_{X, x} ⟶ X`, then the vanishing of `R¹g_*𝒪_{X'}` forces the vanishing of
`H¹(Y, 𝒪_Y)`: flat base change identifies the stalk of `R¹g_*𝒪_{X'}` at `x` with
`H¹(Y, 𝒪_Y)`, the base `Spec 𝒪_{X, x}` being affine.

It is proved as `AlgebraicGeometry.flatBaseChangeFirstCohomologyVanishing`. -/
public def FlatBaseChangeFirstCohomologyVanishing : Prop :=
  ∀ ⦃X X' Y : Scheme.{u}⦄ (x : X) (g : X' ⟶ X) (p : Y ⟶ Spec (X.presheaf.stalk x))
    (q : Y ⟶ X'), IsPullback q p g (X.fromSpecStalk x) → IsProper g →
      IsZero (((Scheme.Modules.pushforward g).rightDerived 1).obj
        (SheafOfModules.unit X'.ringCatSheaf)) →
      IsZeroFirstStructureSheafCohomology Y

open GlueingNearPoint in
/-- **A normal modification of a two-dimensional normal local ring is an isomorphism over the
punctured spectrum, as a proposition.**  The punctured spectrum of such a ring is a
one-dimensional normal scheme, over which a proper birational morphism is an isomorphism by
[Stacks, Tag 0AB7] together with
`AlgebraicGeometry.isIso_of_isIntegralHom_of_isBirational_of_isNormal`.  It is proved, for a
base of dimension at most two, as `AlgebraicGeometry.normalModificationIsIsoAwayFromClosedPoint`.

This is the isomorphism half of the hypothesis
`AlgebraicGeometry.ModificationIsFinitePresentationAway` of
`AlgebraicGeometry.definesRationalSingularity_stalk`, quantified over the base.  Its
finite-presentation half is not part of this proposition: a modification is of finite type over
the Noetherian base `Spec 𝒪_{X, x}`, hence of finite presentation, and that is proved below. -/
public def NormalModificationIsIsoAwayFromClosedPoint (A : Type u) [CommRing A]
    [IsDomain A] : Prop :=
  ∀ ⦃X : Scheme.{u}⦄ (f : X ⟶ Spec (.of A)), IsNormal X → IsModification f →
    ∀ (x : X) (hx : IsClosed ({x} : Set X)) (hint : IsIntegral (Spec (X.presheaf.stalk x))),
      letI := hint
      ∀ ⦃Y : Scheme.{u}⦄ (p : Y ⟶ Spec (X.presheaf.stalk x)), IsNormal Y → IsModification p →
        IsIso ((Over.pullback ((X.fromSpecStalk x) ⁻¹ᵁ puncturedOpen hx).ι).obj (Over.mk p)).hom

open GlueingNearPoint in
/-- **Step 4 of the source's proof of [Stacks, Tag 0BG0], as a proposition.**  If a proper
morphism `g : X' ⟶ X` has a normal base change `Y` along `Spec 𝒪_{X, x} ⟶ X`, with `X` normal and
a modification of `Spec(A)`, then `X'` is normal and `g ≫ f` is again a modification.

This is `AlgebraicGeometry.SpreadOutIsNormalModification` quantified over the base.  As stated it
is false, for every `A`: the source's Step 4 takes `Y` to be a normal *modification* of
`Spec 𝒪_{X, x}`, and this proposition asks only that `Y` be normal.  For `X = Spec(A)`, `f = 𝟙`,
`x` a closed point and `X' = Spec(A) ⊔ Spec κ(x)` mapping by the identity and the closed point,
`g` is finite, an isomorphism over `X ∖ {x}`, and its base change
`Y = Spec 𝒪_{X, x} ⊔ Spec κ(x)` is normal, but `X'` is not integral.  The form of Step 4 that
asks, as the source does, that `Y ⟶ Spec 𝒪_{X, x}` be a modification is
`AlgebraicGeometry.isNormal_and_isModification_of_isPullback_fromSpecStalk`. -/
public def SpreadOutIsNormalModificationOverSpec (A : Type u) [CommRing A] [IsDomain A] : Prop :=
  ∀ ⦃X : Scheme.{u}⦄ (f : X ⟶ Spec (.of A)), IsNormal X → IsModification f →
    ∀ (x : X) (hx : IsClosed ({x} : Set X)),
      ∀ ⦃X' Y : Scheme.{u}⦄ (g : X' ⟶ X) (p : Y ⟶ Spec (X.presheaf.stalk x)) (q : Y ⟶ X'),
        IsPullback q p g (X.fromSpecStalk x) → IsProper g →
          IsFinitePresentationAway (puncturedOpen hx) (Over.mk g) → IsNormal Y →
            IsNormal X' ∧ IsModification (g ≫ f)

/-! ### Two elementary lemmas -/

/-- An injective map of modules of finite length onto a module of no greater length is
surjective. -/
public theorem surjective_of_injective_of_length_le {R : Type u} [Ring R] {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (φ : M →ₗ[R] N)
    (hφ : Function.Injective φ) (hfin : Module.length R M ≠ ⊤)
    (hle : Module.length R N ≤ Module.length R M) : Function.Surjective φ := by
  have hEq := Module.length_eq_add_of_exact φ (LinearMap.range φ).mkQ hφ
    (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range φ)
  have hzero : Module.length R (N ⧸ LinearMap.range φ) = 0 := by
    have h := hle
    rw [hEq] at h
    exact le_antisymm ((ENat.add_le_add_iff_left hfin).mp
      (show Module.length R M + Module.length R (N ⧸ LinearMap.range φ) ≤
        Module.length R M + 0 by simpa only [add_zero] using h)) zero_le
  have hss : Subsingleton (N ⧸ LinearMap.range φ) := Module.length_eq_zero_iff.mp hzero
  intro y
  have hy : (LinearMap.range φ).mkQ y = 0 := hss.elim _ _
  exact (Submodule.Quotient.mk_eq_zero _).mp hy

/-- A quasi-coherent module generated by global sections with no global sections is zero. -/
public theorem isZero_of_generatingSections_of_subsingleton_sections {X : Scheme.{u}}
    {M : SheafOfModules.{u} X.ringCatSheaf} (G : M.GeneratingSections)
    [Subsingleton M.sections] : IsZero M := by
  apply IsZero.of_epi_eq_zero G.π
  apply M.freeHomEquiv.injective
  funext i
  exact Subsingleton.elim _ _

/-- The situation of [Stacks, Tag 0AX8] attached to a modification of the spectrum of a
two-dimensional Noetherian normal local domain: the special fibre of a modification is a
Noetherian space, so its irreducible components are finite in number and can be enumerated. -/
public def vanishingSituationOfModification (A : Type u) [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] [IsNormalDomain A] (hdim : ringKrullDim A = 2) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) (hf : IsModification f) : VanishingSituation.{u} :=
  letI := hf.isProper
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  letI : IsNoetherian X := AlgebraicGeometry.IsNoetherian.mk
  letI : NoetherianSpace (f.fiber (IsLocalRing.closedPoint A)) :=
    (f.fiberHomeo _).isEmbedding.noetherianSpace
  letI : Fintype {Z : Set (f.fiber (IsLocalRing.closedPoint A)) //
      Z ∈ irreducibleComponents (f.fiber (IsLocalRing.closedPoint A))} :=
    (NoetherianSpace.finite_irreducibleComponents
      (α := f.fiber (IsLocalRing.closedPoint A))).fintype
  { A := A
    dimension_two := hdim
    X := X
    f := f
    modification := hf
    numberOfComponents := Fintype.card _
    components := (Fintype.equivFin _).symm }

/-! ### Tag 0B4P -/

/-- The argument of [Stacks, Tag 0B4P] over five propositions taken as hypotheses: for a local
normal Nagata domain `A` of dimension two for which reduction to rational singularities is
possible, there is a finite sequence of normalized blowups at closed points
`X = Xₙ → ⋯ → X₁ → X₀ = Spec(A)` whose total space `X` is normal, whose structure morphism is a
projective modification, and such that the local ring of `X` at every closed point defines a
rational singularity.

Step 1 is `AlgebraicGeometry.exists_maximal_length_normal_modification`; Step 2 replaces the
maximal modification by a sequence of normalized blowups dominating it, which is Tag 0BBT in the
form `AlgebraicGeometry.exists_normalizedBlowUpSeq_isModification_dominating`, and the
replacement stays maximal because the first cohomology injects along the domination.  Step 3
fixes a closed point `x` of the sequence and a normal modification `Y ⟶ Spec 𝒪_{X, x}`, spreads
it out to a proper `g : X' ⟶ X` which is an isomorphism away from `x` (Tag 0B3X, as
`AlgebraicGeometry.exists_isPullback_fromSpecStalk_of_isProper`) and concludes from maximality
that the Leray map `H¹(X, 𝒪_X) ⟶ H¹(X', 𝒪_{X'})` is onto, so that `R¹g_*𝒪_{X'}` has no global
sections; being generated by global sections, by the third conclusion of Tag 0AXF, it vanishes,
and flat base change carries the vanishing to `Y`.

The hypotheses `h0AXF`, `h02KH`, `h02NS` and `h0AB7` are proved in this development, as
`AlgebraicGeometry.lerayFirstCohomologyExact_of_ringKrullDim_eq_two`,
`AlgebraicGeometry.flatBaseChangeFirstCohomologyVanishing`,
`AlgebraicGeometry.blowUpIsQuasiProjective` and
`AlgebraicGeometry.normalModificationIsIsoAwayFromClosedPoint`; [Stacks, Tag 0B4P] itself is
`AlgebraicGeometry.exists_normalizedBlowUpSeq_definesRationalSingularity_stalk_unconditional`,
which discharges them and replaces `hStep4` by
`AlgebraicGeometry.isNormal_and_isModification_of_isPullback_fromSpecStalk`.  The hypothesis
`hStep4` is false as stated (see `AlgebraicGeometry.SpreadOutIsNormalModificationOverSpec`), so
this theorem records the shape of the argument and is not a proof of the tag. -/
public theorem exists_normalizedBlowUpSeq_definesRationalSingularity_stalk
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    (hNagata : IsNagataRing A) (hdim : ringKrullDim A = 2)
    (hReduction : IsReductionToRationalSingularitiesPossible A)
    (h0AXF : LerayFirstCohomologyExact A)
    (h02KH : FlatBaseChangeFirstCohomologyVanishing.{u})
    (h02NS : BlowUpIsQuasiProjective.{u})
    (h0AB7 : NormalModificationIsIsoAwayFromClosedPoint A)
    (hStep4 : SpreadOutIsNormalModificationOverSpec A) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)) (hX : IsNormal X),
      letI := hX
      NormalizedBlowUpSeq (Spec (.of A)) X f ∧ IsModification f ∧
        IsProjectiveMorphism f ∧
        ∀ x : X, IsClosed ({x} : Set X) →
          DefinesRationalSingularity (X.presheaf.stalk x) := by
  classical
  have hNoethA : IsNoetherianRing A := hNagata.1
  have hSpecNormal : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  have hNagataSpec : IsNagataScheme (Spec (.of A)) := isNagataScheme_spec_of_isNagataRing A hNagata
  -- Step 1: a normal modification of maximal first-cohomology length.
  obtain ⟨X₀, hX₀, f₀, hf₀, hmax⟩ := exists_maximal_length_normal_modification A hReduction
  -- Step 2: dominate it by a sequence of normalized blowups at closed points.
  obtain ⟨W, g, dom, hseq, hWnormal, hgmod, hcomm⟩ :=
    exists_normalizedBlowUpSeq_isModification_dominating A hNagata hdim f₀ hf₀
  have hWmod : IsModification (dom ≫ f₀) := by rw [hcomm]; exact hgmod
  -- the sequence is itself of maximal length: `H¹` injects along the domination.
  obtain ⟨φ₀, hφ₀, -⟩ := h0AXF f₀ dom hX₀ hWnormal hf₀ hWmod
  have htransfer : Module.length A (firstCohomologyAsBaseModule X₀ f₀) ≤
      Module.length A (firstCohomologyAsBaseModule W g) := by
    refine (Module.length_le_of_injective φ₀ hφ₀).trans_eq ?_
    exact congrArg (fun k => Module.length A (firstCohomologyAsBaseModule W k)) hcomm
  have hWmax : ∀ (Y : Scheme.{u}) (_ : IsNormal Y) (p : Y ⟶ Spec (.of A)), IsModification p →
      Module.length A (firstCohomologyAsBaseModule Y p) ≤
        Module.length A (firstCohomologyAsBaseModule W g) :=
    fun Y hY p hp => (hmax Y hY p hp).trans htransfer
  obtain ⟨bound, hBound⟩ := hReduction
  have hWfinite : Module.length A (firstCohomologyAsBaseModule W g) ≠ ⊤ :=
    ne_of_lt (lt_of_le_of_lt (hBound W g hgmod) (ENat.natCast_lt_top bound))
  -- Properties of the total space of the sequence.
  obtain ⟨-, hNoethLocW, -, hProperW⟩ := hseq.properties hNagataSpec
  have := hNoethLocW
  have := hProperW
  have : CompactSpace W := QuasiCompact.compactSpace_of_compactSpace g
  have hNoethW : IsNoetherian W := AlgebraicGeometry.IsNoetherian.mk
  refine ⟨W, g, hWnormal, hseq, hgmod, ?_, ?_⟩
  · -- Projectivity, by the H-form of Tag 0BCL along the sequence.
    obtain ⟨M, hMinv, hMample⟩ := Stacks.HProjective.exists_isAmple_of_isAffine (Spec (.of A))
    have := hMinv
    exact hseq.isProjectiveMorphism h02NS hNagataSpec M hMample
  · -- Rational singularities at the closed points.
    intro x hx Y hY p hp
    have := hY
    -- spread the normal modification `p` of `Spec 𝒪_{W, x}` out to a proper `g' : X' ⟶ W`
    have hemb := (GlueingNearPoint.puncturedOpen hx).isOpen.isOpenEmbedding_subtypeVal
    have : NoetherianSpace (GlueingNearPoint.puncturedOpen hx).toScheme :=
      hemb.isEmbedding.noetherianSpace
    have hqc : QuasiCompact (GlueingNearPoint.puncturedOpen hx).ι :=
      quasiCompact_of_noetherianSpace_source _
    have hfp : FinitePresentation p := by
      have := hp.isProper
      have : IsDomain ↥(W.presheaf.stalk x) := hWnormal.stalk_isDomain x
      exact ⟨inferInstance, inferInstance, inferInstance⟩
    obtain ⟨X', g', q, hg'away, hg'proper, hsq⟩ :=
      exists_isPullback_fromSpecStalk_of_isProper W x hx hqc p
        ⟨hfp, h0AB7 g hWnormal hgmod x hx inferInstance p hY hp⟩ hp.isProper
    obtain ⟨hX'normal, hX'mod⟩ :=
      hStep4 g hWnormal hgmod x hx g' p q hsq hg'proper hg'away hY
    -- maximality forces the Leray edge map to be onto, so `R¹g'_*𝒪_{X'}` has no sections
    obtain ⟨φ, hφinj, hφzero⟩ := h0AXF g g' hWnormal hX'normal hgmod hX'mod
    have hsurj := surjective_of_injective_of_length_le φ hφinj hWfinite
      (hWmax X' hX'normal _ hX'mod)
    -- and it is generated by global sections, by the third conclusion of Tag 0AXF
    let T : SemistableReduction.TwoModifications.{u} :=
      { situation := vanishingSituationOfModification A hdim g hgmod
        X' := X'
        g := g'
        modification' := hX'mod
        normal := hWnormal }
    obtain ⟨G⟩ := T.nonempty_generatingSections_rightDerived_one_pushforward
    have hzero : IsZero (((Scheme.Modules.pushforward g').rightDerived 1).obj
        (SheafOfModules.unit X'.ringCatSheaf)) :=
      @isZero_of_generatingSections_of_subsingleton_sections _ _ G (hφzero hsurj)
    -- flat base change transports the vanishing to `Y`
    exact h02KH x g' p q hsq hg'proper hzero

end

end AlgebraicGeometry
