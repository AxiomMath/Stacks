module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineOfEtaleEqualizerChart
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.SpecialCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Spaces.PullbackIdealChartGeneration
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.FirstOrderFunctionsLift
public import StacksFrontier.RingTheory.Etale.NilpotentThickening

/-!
# A first-order thickening of an affine algebraic space is affine

Let `Z ⊂ X` be a first-order thickening of algebraic spaces over a scheme `S` whose closed member
`Z` is affine.  Then `X` is affine.  This is the case of the proof for finite order thickenings of
Stacks 05ZR in which the closed member is affine, and the argument is the source's.

Choose a surjective étale chart `U' ⟶ X` with `U'` affine and let `R' = U' ×_X U'`.  Their base
changes `U = Z ×_X U'` and `R = Z ×_X R'` are affine, `R = U ×_Z U`, and `R ⊂ R'` is a first-order
thickening of schemes, so `R'` is affine too (Stacks 06AD).  Write `B' = Γ(U')`, `C' = Γ(R')`,
`B = Γ(U)`, `A = Γ(Z)` and let `A'' ⊆ B'` be the functions equalized by the two projections.

* `A'' → A` is surjective, with kernel `I` of square zero: every regular function on `Z` lifts to
  `X` (`AlgebraicGeometry.Space.exists_lift_of_isFirstOrderThickening`).
* `J = ker(B' → B)` is `I ⊗_A B`: `J` is the module of sections over `U` of the conormal module of
  `Z`, which is quasi-coherent, and `I` its module of global sections.
* Hence `A'' → B'` is étale (Stacks 05YT), `Spec B' → Spec A''` is surjective, and
  `C' = B' ⊗_{A''} B'` because both are étale over `B'` and agree modulo `I`.  So `X = Spec A''`
  (`AlgebraicGeometry.Space.isAffineSpace_of_isPushout_eqLocus`).

## Main results

* `AlgebraicGeometry.Space.isLimitSmallBaseChangeProd`: small-chart base change preserves binary
  products of étale charts.
* `AlgebraicGeometry.Space.isBaseChange_kerRestrict_of_isFirstOrderThickening`: `J = I ⊗_{A''} B'`.
* `AlgebraicGeometry.Space.isAffineSpace_of_isFirstOrderThickening`: a first-order thickening of an
  affine algebraic space is affine.

## References

* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 05YT](https://stacks.math.columbia.edu/tag/05YT)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Base change of charts preserves binary products -/

section Products

variable {X Y : AlgebraicSpaces B S hS} (f : Y ⟶ X) (hf : yoneda.relativelyRepresentable f.hom)

/-- **Small-chart base change preserves binary products.**  For a representable morphism
`f : Y ⟶ X` of algebraic spaces and two étale charts `Q, Q'` of `X`, the base changes of the two
projections of `Q ×_X Q'` exhibit `(Q ×_X Q') ×_X Y` as the product of `Q ×_X Y` and `Q' ×_X Y` in
the small étale site of `Y`. -/
def isLimitSmallBaseChangeProd (Q Q' : SmallEtale B S hS X.1) :
    IsLimit (BinaryFan.mk ((smallBaseChange B S hS f hf).map (SmallEtale.prodFst B S hS X.1 Q Q'))
      ((smallBaseChange B S hS f hf).map (SmallEtale.prodSnd B S hS X.1 Q Q'))) := by
  refine BinaryFan.isLimitMk (fun s ↦ smallBaseChangeProdLift B S hS f hf s.fst s.snd)
    (fun s ↦ smallBaseChangeProdLift_fst B S hS f hf s.fst s.snd)
    (fun s ↦ smallBaseChangeProdLift_snd B S hS f hf s.fst s.snd) ?_
  intro s m h₁ h₂
  refine bc_hom_ext B S hS f hf ?_
  rw [smallBaseChangeProdLift_proj]
  refine Functor.relativelyRepresentable.hom_ext' _ ?_ ?_
  · have e1 := bcProj_comp B S hS f hf m (SmallEtale.prodFst B S hS X.1 Q Q')
    rw [h₁] at e1
    exact e1.symm.trans (Functor.relativelyRepresentable.lift'_fst _ _ _ _).symm
  · have e2 := bcProj_comp B S hS f hf m (SmallEtale.prodSnd B S hS X.1 Q Q')
    rw [h₂] at e2
    exact e2.symm.trans (Functor.relativelyRepresentable.lift'_snd _ _ _ _).symm

end Products


/-! ### Gluing along the base change of a chart over an affine closed member -/

section Glue

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1} (hG : IsThickening B S hS X G)
  {T₀ : BigFppfOver B S hS} (e : yoneda.obj T₀ ≅ G.toFunctor)

/-- The terminal chart of the closed member of a thickening, when that member is isomorphic to a
representable presheaf. -/
abbrev thickeningTerminalChart : SmallEtale B S hS (IsThickening.space B S hS hG).1 :=
  thickeningIsoChart B S hS (Y := (IsThickening.space B S hS hG).1) e

/-- The terminal chart is terminal. -/
abbrev thickeningTerminalChartIsTerminal : IsTerminal (thickeningTerminalChart B S hS hG e) :=
  isTerminalIsoChart B S hS (Y := (IsThickening.space B S hS hG).1) e

/-- The base change of a surjective chart of the ambient space maps onto the terminal chart of the
closed member: its morphism of schemes to `T₀` is surjective. -/
theorem surjective_thickeningTerminalChart_from (V : SmallEtale B S hS X.1)
    (hV : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf V.obj.hom) :
    Surjective ((BigFppfOver.toScheme B S hS).map ((thickeningTerminalChartIsTerminal B S hS hG
        e).from
      ((thickeningChartBaseChange B S hS hG).obj V)).hom.left) := by
  let W := (thickeningChartBaseChange B S hS hG).obj V
  let m := ((thickeningTerminalChartIsTerminal B S hS hG e).from W).hom.left
  have hm : yoneda.map m = W.obj.hom ≫ e.inv :=
    (Iso.eq_comp_inv e).2
      (CostructuredArrow.w ((thickeningTerminalChartIsTerminal B S hS hG e).from W).hom)
  have hWs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf W.obj.hom :=
    (MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).of_isPullback
      ((isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.isPullback V.obj.hom).flip hV
  have hms : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map m) := by
    rw [hm]
    have hSurj : MorphismProperty.ContainsIdentities
        (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    have hSurjIso : MorphismProperty.RespectsIso
        (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hSurj' : MorphismProperty.ContainsIdentities
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.ContainsIdentities.inverseImage (BigFppfOver.toScheme B S hS)
    have hSurjIso' : MorphismProperty.RespectsIso
        (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) :=
      MorphismProperty.RespectsIso.inverseImage _ (BigFppfOver.toScheme B S hS)
    exact MorphismProperty.comp_mem _ _ _ hWs (MorphismProperty.presheaf_of_isIso _ e.inv)
  exact (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ m).1 hms

/-- The base change of a surjective chart of the ambient space covers the terminal chart of the
closed member. -/
theorem singleton_mem_topology_thickeningTerminalChart (V : SmallEtale B S hS X.1)
    (hV : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf V.obj.hom) :
    Sieve.generate (Presieve.singleton ((thickeningTerminalChartIsTerminal B S hS hG e).from
      ((thickeningChartBaseChange B S hS hG).obj V))) ∈
        SmallEtale.topology B S hS (IsThickening.space B S hS hG).1
          (thickeningTerminalChart B S hS hG e) := by
  rw [← Presieve.ofArrows_pUnit.{0}]
  refine SmallEtale.ofArrows_mem_topology B S hS _ _ _ ?_
  refine (Scheme.ofArrows_mem_precoverage_iff _).2 ⟨fun x ↦ ⟨PUnit.unit, ?_⟩,
    fun _ ↦ etale_toScheme_toOver_map B S hS _ _⟩
  exact (surjective_thickeningTerminalChart_from B S hS hG e V hV).surj x

/-- **Gluing along the base change of a surjective chart.**  Let `G ⊂ X` be a thickening whose
closed member is isomorphic to a representable `yoneda T₀`, and let `V` be a surjective étale
chart of `X`.  A section over `G ×_X V` of a sheaf of types on the small étale site of `G` which
has the same restrictions along the base changes of the two projections of `V ×_X V` is the
restriction of exactly one section over the terminal chart `T₀`. -/
theorem existsUnique_glue_thickeningTerminalChart (V : SmallEtale B S hS X.1)
    (hV : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf V.obj.hom)
    {P : (SmallEtale B S hS (IsThickening.space B S hS hG).1)ᵒᵖ ⥤ Type*}
    (hP : Presieve.IsSheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1) P)
    (x : P.obj (op ((thickeningChartBaseChange B S hS hG).obj V)))
    (hx : P.map ((thickeningChartBaseChange B S hS hG).map
        (SmallEtale.prodFst B S hS X.1 V V)).op x =
      P.map ((thickeningChartBaseChange B S hS hG).map
        (SmallEtale.prodSnd B S hS X.1 V V)).op x) :
    ∃! y : P.obj (op (thickeningTerminalChart B S hS hG e)),
      P.map ((thickeningTerminalChartIsTerminal B S hS hG e).from
        ((thickeningChartBaseChange B S hS hG).obj V)).op y = x := by
  have hfor := (Presieve.isSheafFor_iff_generate _).2
    (hP _ (singleton_mem_topology_thickeningTerminalChart B S hS hG e V hV))
  refine Presieve.isSheafFor_singleton.1 hfor x fun {Z} p₁ p₂ _ ↦ ?_
  let hlim := isLimitSmallBaseChangeProd B S hS (IsThickening.inclusion B S hS hG)
    (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep V V
  let ℓ := hlim.lift (BinaryFan.mk p₁ p₂)
  have h₁ : ℓ ≫ (thickeningChartBaseChange B S hS hG).map
      (SmallEtale.prodFst B S hS X.1 V V) = p₁ := hlim.fac (BinaryFan.mk p₁ p₂) ⟨.left⟩
  have h₂ : ℓ ≫ (thickeningChartBaseChange B S hS hG).map
      (SmallEtale.prodSnd B S hS X.1 V V) = p₂ := hlim.fac (BinaryFan.mk p₁ p₂) ⟨.right⟩
  rw [← h₁, ← h₂, op_comp, op_comp, P.map_comp, P.map_comp, types_comp_apply,
    types_comp_apply, hx]

end Glue

section GlueIff

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1} (hG : IsThickening B S hS X G)
  {T₀ : BigFppfOver B S hS} (e : yoneda.obj T₀ ≅ G.toFunctor)

/-- A section of a sheaf over the base change `G ×_X V` of a surjective chart is the restriction
of a section over the terminal chart of the closed member exactly when its two restrictions to the
base change of `V ×_X V` agree. -/
theorem exists_map_thickeningTerminalChart_eq_iff (V : SmallEtale B S hS X.1)
    (hV : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf V.obj.hom)
    {P : (SmallEtale B S hS (IsThickening.space B S hS hG).1)ᵒᵖ ⥤ Type*}
    (hP : Presieve.IsSheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1) P)
    (x : P.obj (op ((thickeningChartBaseChange B S hS hG).obj V))) :
    (∃ y : P.obj (op (thickeningTerminalChart B S hS hG e)),
      P.map ((thickeningTerminalChartIsTerminal B S hS hG e).from
        ((thickeningChartBaseChange B S hS hG).obj V)).op y = x) ↔
    P.map ((thickeningChartBaseChange B S hS hG).map
        (SmallEtale.prodFst B S hS X.1 V V)).op x =
      P.map ((thickeningChartBaseChange B S hS hG).map
        (SmallEtale.prodSnd B S hS X.1 V V)).op x := by
  refine ⟨?_, fun hx ↦ (existsUnique_glue_thickeningTerminalChart B S hS hG e V hV hP x hx).exists⟩
  rintro ⟨y, rfl⟩
  have h := (thickeningTerminalChartIsTerminal B S hS hG e).hom_ext
    ((thickeningChartBaseChange B S hS hG).map (SmallEtale.prodFst B S hS X.1 V V) ≫
      (thickeningTerminalChartIsTerminal B S hS hG e).from
        ((thickeningChartBaseChange B S hS hG).obj V))
    ((thickeningChartBaseChange B S hS hG).map (SmallEtale.prodSnd B S hS X.1 V V) ≫
      (thickeningTerminalChartIsTerminal B S hS hG e).from
        ((thickeningChartBaseChange B S hS hG).obj V))
  simp only [← Functor.map_comp_apply, ← op_comp, h]

/-- Restriction of sections of a sheaf from the terminal chart of the closed member to the base
change of a surjective chart is injective. -/
theorem injective_map_thickeningTerminalChart (V : SmallEtale B S hS X.1)
    (hV : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf V.obj.hom)
    {P : (SmallEtale B S hS (IsThickening.space B S hS hG).1)ᵒᵖ ⥤ Type*}
    (hP : Presieve.IsSheaf (SmallEtale.topology B S hS (IsThickening.space B S hS hG).1) P) :
    Function.Injective (P.map ((thickeningTerminalChartIsTerminal B S hS hG e).from
        ((thickeningChartBaseChange B S hS hG).obj V)).op) := fun _ y₂ h ↦
  (existsUnique_glue_thickeningTerminalChart B S hS hG e V hV hP _
    ((exists_map_thickeningTerminalChart_eq_iff B S hS hG e V hV hP _).1 ⟨y₂, rfl⟩)).unique h rfl

end GlueIff

/-! ### The charts of a thickening over an affine closed member -/

section Charts

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1} (hG : IsThickening B S hS X G)
  {T₀ : BigFppfOver B S hS} (e : yoneda.obj T₀ ≅ G.toFunctor) (V : SmallEtale B S hS X.1)

/-- The base change of a chart of the ambient space of a thickening is affine when the chart is:
it is a closed subscheme of it. -/
theorem isAffine_thickeningChartBaseChange
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.obj.left)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((thickeningChartBaseChange B S hS hG).obj V).obj.left) := by
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj V.obj.left) := hV
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      ((isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd V.obj.hom)) :=
    (isClosedImmersion_inclusion_of_isThickening B S hS hG).property_snd V.obj.hom
  exact (_root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine
    ((BigFppfOver.toScheme B S hS).map
      ((isClosedImmersion_inclusion_of_isThickening B S hS hG).rep.snd V.obj.hom))).1

/-- **The base change of `V ×_X V` is the fibre square of the base change of `V` over the
terminal chart**, as a cartesian square of schemes. -/
theorem isPullback_thickeningChartBaseChange_prod :
    IsPullback
      ((BigFppfOver.toScheme B S hS).map ((thickeningChartBaseChange B S hS hG).map
        (SmallEtale.prodFst B S hS X.1 V V)).hom.left)
      ((BigFppfOver.toScheme B S hS).map ((thickeningChartBaseChange B S hS hG).map
        (SmallEtale.prodSnd B S hS X.1 V V)).hom.left)
      ((BigFppfOver.toScheme B S hS).map ((thickeningTerminalChartIsTerminal B S hS hG e).from
        ((thickeningChartBaseChange B S hS hG).obj V)).hom.left)
      ((BigFppfOver.toScheme B S hS).map ((thickeningTerminalChartIsTerminal B S hS hG e).from
        ((thickeningChartBaseChange B S hS hG).obj V)).hom.left) := by
  set W := (IsThickening.space B S hS hG).1
  set U := (thickeningChartBaseChange B S hS hG).obj V
  have hlim := isLimitSmallBaseChangeProd B S hS (IsThickening.inclusion B S hS hG)
    (isClosedImmersion_inclusion_of_isThickening B S hS hG).rep V V
  have hprod := SmallEtale.prodIsLimit B S hS W U U
  let c := hlim.conePointUniqueUpToIso hprod
  have hc₁ : c.hom ≫ SmallEtale.prodFst B S hS W U U =
      (thickeningChartBaseChange B S hS hG).map (SmallEtale.prodFst B S hS X.1 V V) :=
    hlim.conePointUniqueUpToIso_hom_comp hprod ⟨.left⟩
  have hc₂ : c.hom ≫ SmallEtale.prodSnd B S hS W U U =
      (thickeningChartBaseChange B S hS hG).map (SmallEtale.prodSnd B S hS X.1 V V) :=
    hlim.conePointUniqueUpToIso_hom_comp hprod ⟨.right⟩
  -- the presheaf square of the product chart
  have h0 : IsPullback (yoneda.map (SmallEtale.prodFst B S hS W U U).hom.left)
      (yoneda.map (SmallEtale.prodSnd B S hS W U U).hom.left) U.obj.hom U.obj.hom :=
    U.property.rep.isPullback' U.obj.hom
  let cl : ((thickeningChartBaseChange B S hS hG).obj
      (SmallEtale.prodObj B S hS X.1 V V)).obj.left ≅ (SmallEtale.prodObj B S hS W U U).obj.left :=
    (SmallEtale.toOver B S hS W).mapIso c
  set g := ((thickeningTerminalChartIsTerminal B S hS hG e).from U).hom.left
  have hg : yoneda.map g ≫ e.hom = U.obj.hom :=
    CostructuredArrow.w ((thickeningTerminalChartIsTerminal B S hS hG e).from U).hom
  have h1 : IsPullback
      (yoneda.map ((thickeningChartBaseChange B S hS hG).map
        (SmallEtale.prodFst B S hS X.1 V V)).hom.left)
      (yoneda.map ((thickeningChartBaseChange B S hS hG).map
        (SmallEtale.prodSnd B S hS X.1 V V)).hom.left)
      (yoneda.map g) (yoneda.map g) := by
    refine IsPullback.of_iso h0 (yoneda.mapIso cl).symm (Iso.refl _) (Iso.refl _) e.symm ?_ ?_ ?_ ?_
    · rw [← hc₁]
      simp [cl, ← Functor.map_comp]
    · rw [← hc₂]
      simp [cl, ← Functor.map_comp]
    · rw [← hg]; exact (Iso.comp_inv_eq e).2 rfl
    · rw [← hg]; exact (Iso.comp_inv_eq e).2 rfl
  have hw : ((thickeningChartBaseChange B S hS hG).map
      (SmallEtale.prodFst B S hS X.1 V V)).hom.left ≫ g = ((thickeningChartBaseChange B S hS hG).map
      (SmallEtale.prodSnd B S hS X.1 V V)).hom.left ≫ g :=
    yoneda.map_injective (by simpa using h1.w)
  exact (IsPullback.of_map yoneda hw (by simpa using h1)).map _

end Charts


/-! ### The ideal of a first-order thickening as the direct image of its conormal module -/

section Conormal

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1} (hG : IsFirstOrderThickening B S hS X G)

/-- The defining ideal of a first-order thickening `G ⊂ X`, as a sheaf of `𝒪_X`-modules, is the
direct image along base change of étale charts of the conormal module of `G`: Stacks 04CJ in the
form `𝓘 ≅ i_*i^*𝓘`, with the direct image read as base change of charts. -/
def thickeningIdealConormalIso :
    (definingIdealSheaf B S hS X (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules ≅
      (smallBaseChangeModulePushforward.{u, u} B S hS
        (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
        (firstOrderThickeningSubspace B S hS hG).2.2.rep).obj
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)) :=
  firstOrderConormalModuleIso B S hS (firstOrderThickeningSubspace B S hS hG) hG ≪≫
    (modulePushforwardChartIso B S hS
      (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
      (firstOrderThickeningSubspace B S hS hG).2.2.rep).app
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG))

/-- The inverse of `thickeningIdealConormalIso` followed by it is the identity on sections. -/
theorem thickeningIdealConormalIso_inv_hom (Q : SmallEtale B S hS X.1)
    (y : ((smallBaseChangeModulePushforward.{u, u} B S hS
        (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
        (firstOrderThickeningSubspace B S hS hG).2.2.rep).obj
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG))).val.obj (op Q)) :
    ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom
      (((thickeningIdealConormalIso B S hS hG).inv.val.app (op Q)).hom y) = y :=
  congrArg (fun f ↦ (f.val.app (op Q)).hom y) (thickeningIdealConormalIso B S hS hG).inv_hom_id

/-- `thickeningIdealConormalIso` followed by its inverse is the identity on sections. -/
theorem thickeningIdealConormalIso_hom_inv (Q : SmallEtale B S hS X.1)
    (y : (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.obj (op Q)) :
    ((thickeningIdealConormalIso B S hS hG).inv.val.app (op Q)).hom
      (((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom y) = y :=
  congrArg (fun f ↦ (f.val.app (op Q)).hom y) (thickeningIdealConormalIso B S hS hG).hom_inv_id

/-- The action of `𝒪_X` on the direct image of the conormal module over a chart `Q` is the action
of `𝒪_G` over `G ×_X Q`, through pullback of regular functions. -/
theorem thickeningIdealConormalIso_smul (Q : SmallEtale B S hS X.1)
    (b : (structureRingSheaf B S hS X).obj.obj (op Q))
    (x : (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.obj (op Q)) :
    ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom (b • x) =
      b • ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom x :=
  ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom.map_smul b x

/-- The action of `𝒪_X(Q)` on the sections of the direct image of the conormal module is the
action of `𝒪_G(G ×_X Q)` through pullback of regular functions. -/
theorem smallBaseChangeModulePushforward_conormal_smul (Q : SmallEtale B S hS X.1)
    (b : (smallEtaleRingSheaf B S hS X.1 X.2).obj.obj (op Q))
    (m : ((smallBaseChangeModulePushforward.{u, u} B S hS
        (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
        (firstOrderThickeningSubspace B S hS hG).2.2.rep).obj
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG))).val.obj (op Q)) :
    b • m = (show (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS
          (firstOrderThickeningSubspace B S hS hG).1.toFunctor
          (firstOrderThickeningSubspace B S hS hG).2.1).O).obj.obj
        (op ((smallBaseChange B S hS
          (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
          (firstOrderThickeningSubspace B S hS hG).2.2.rep).obj Q)) from
          ((BigFppfOver.toScheme B S hS).map
            ((isClosedImmersion_inclusion_of_isThickening B S hS hG.1).rep.snd
              Q.obj.hom)).appTop b) •
      (show (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.obj
          (op ((smallBaseChange B S hS
          (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
          (firstOrderThickeningSubspace B S hS hG).2.2.rep).obj Q)) from m) :=
  rfl

/-- The module structure of the sections of the conormal module over a base-changed chart, over
the regular functions of that chart. -/
abbrev conormalChartModule (Q : SmallEtale B S hS X.1) :
    Module Γ((BigFppfOver.toScheme B S hS).obj
        ((thickeningChartBaseChange B S hS hG.1).obj Q).obj.left, ⊤)
      ((conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.obj
        (op ((thickeningChartBaseChange B S hS hG.1).obj Q))) :=
  inferInstanceAs (Module ((Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedSite B S hS (firstOrderThickeningSubspace B S hS hG).1.toFunctor
      (firstOrderThickeningSubspace B S hS hG).2.1).O).obj.obj
      (op ((thickeningChartBaseChange B S hS hG.1).obj Q))) _)

/-- The identification, over an étale chart `Q` of `X`, of the defining ideal with the sections of
the conormal module over `G ×_X Q`. -/
def conormalChartEquiv (Q : SmallEtale B S hS X.1) :
    definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) (op Q) ≃+
      (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.obj
        (op ((thickeningChartBaseChange B S hS hG.1).obj Q)) where
  toFun x := ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom x
  invFun m := ((thickeningIdealConormalIso B S hS hG).inv.val.app (op Q)).hom m
  left_inv x := thickeningIdealConormalIso_hom_inv B S hS hG Q x
  right_inv m := thickeningIdealConormalIso_inv_hom B S hS hG Q m
  map_add' x y := ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom.map_add x y

/-- `thickeningIdealConormalIso` commutes with restriction of sections. -/
theorem conormalChartEquiv_naturality {Q Q' : SmallEtale B S hS X.1} (k : Q ⟶ Q')
    (x : (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.obj (op Q')) :
    ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom
        ((definingIdealSheaf B S hS X
          (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.map k.op x) =
      ((smallBaseChangeModulePushforward.{u, u} B S hS
        (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
        (firstOrderThickeningSubspace B S hS hG).2.2.rep).obj
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG))).val.map k.op
        (((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q')).hom x) :=
  PresheafOfModules.naturality_apply (thickeningIdealConormalIso B S hS hG).hom.val k.op x

/-- Restriction of regular functions from an étale chart `Q` of `X` to its base change
`G ×_X Q`. -/
abbrev thickeningChartRestrict (Q : SmallEtale B S hS X.1) :
    Γ((BigFppfOver.toScheme B S hS).obj Q.obj.left, ⊤) ⟶
      Γ((BigFppfOver.toScheme B S hS).obj
        ((thickeningChartBaseChange B S hS hG.1).obj Q).obj.left, ⊤) :=
  ((BigFppfOver.toScheme B S hS).map
    ((isClosedImmersion_inclusion_of_isThickening B S hS hG.1).rep.snd Q.obj.hom)).appTop

/-- A function on a chart lies in the defining ideal exactly when it restricts to zero on the
base change of the chart. -/
theorem mem_definingIdealAt_iff_thickeningChartRestrict (Q : SmallEtale B S hS X.1)
    (x : Γ((BigFppfOver.toScheme B S hS).obj Q.obj.left, ⊤)) :
    x ∈ definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) (op Q) ↔
      thickeningChartRestrict B S hS hG Q x = 0 := by
  rw [← ker_thickeningStructureSharp_app B S hS hG Q]
  exact Iff.rfl

/-- The kernel of restriction to the base change of a chart is the defining ideal at that chart. -/
def thickeningKerDefiningIdealEquiv (Q : SmallEtale B S hS X.1) :
    RingHom.ker (thickeningChartRestrict B S hS hG Q).hom ≃+
      definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) (op Q) where
  toFun j := ⟨j.1, (mem_definingIdealAt_iff_thickeningChartRestrict B S hS hG Q j.1).2 j.2⟩
  invFun x := ⟨x.1, (mem_definingIdealAt_iff_thickeningChartRestrict B S hS hG Q x.1).1 x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- The kernel of restriction to the base change `G ×_X Q` of a chart is the module of sections of
the conormal module over `G ×_X Q`. -/
def thickeningKerConormalEquiv (Q : SmallEtale B S hS X.1) :
    RingHom.ker (thickeningChartRestrict B S hS hG Q).hom ≃+
      (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.obj
        (op ((thickeningChartBaseChange B S hS hG.1).obj Q)) :=
  (thickeningKerDefiningIdealEquiv B S hS hG Q).trans (conormalChartEquiv B S hS hG Q)

/-- Multiplication in the kernel is the module action on the sections of the ideal sheaf. -/
theorem thickeningKerDefiningIdealEquiv_smul (Q : SmallEtale B S hS X.1)
    (b : Γ((BigFppfOver.toScheme B S hS).obj Q.obj.left, ⊤))
    (j : RingHom.ker (thickeningChartRestrict B S hS hG Q).hom) :
    (thickeningKerDefiningIdealEquiv B S hS hG Q (b • j) : (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.obj (op Q)) =
      (@id ((structureRingSheaf B S hS X).obj.obj (op Q)) b) •
        (thickeningKerDefiningIdealEquiv B S hS hG Q j : (definingIdealSheaf B S hS X
          (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.obj (op Q)) := rfl

/-- `thickeningKerConormalEquiv` is `thickeningIdealConormalIso` on sections. -/
theorem thickeningKerConormalEquiv_apply (Q : SmallEtale B S hS X.1)
    (j : RingHom.ker (thickeningChartRestrict B S hS hG Q).hom) :
    thickeningKerConormalEquiv B S hS hG Q j =
      ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom
        (thickeningKerDefiningIdealEquiv B S hS hG Q j) := rfl

/-- `thickeningKerConormalEquiv` carries multiplication by a function on the chart to the action
of the structure sheaf of `X` on the direct image of the conormal module. -/
theorem thickeningKerConormalEquiv_smul_eq_structureRing_smul (Q : SmallEtale B S hS X.1)
    (b : Γ((BigFppfOver.toScheme B S hS).obj Q.obj.left, ⊤))
    (j : RingHom.ker (thickeningChartRestrict B S hS hG Q).hom) :
    thickeningKerConormalEquiv B S hS hG Q (b • j) =
      (@id ((structureRingSheaf B S hS X).obj.obj (op Q)) b) •
        ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom
          (thickeningKerDefiningIdealEquiv B S hS hG Q j) :=
  (thickeningKerConormalEquiv_apply B S hS hG Q (b • j)).trans
    ((congrArg ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom
      (thickeningKerDefiningIdealEquiv_smul B S hS hG Q b j)).trans
      (((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom.map_smul _ _))

/-- The action of a function on the chart on the direct image of the conormal module is the action
of its restriction to the base change of the chart. -/
theorem thickeningIdealConormalIso_structureRing_smul (Q : SmallEtale B S hS X.1)
    (b : Γ((BigFppfOver.toScheme B S hS).obj Q.obj.left, ⊤))
    (j : RingHom.ker (thickeningChartRestrict B S hS hG Q).hom) :
    letI := conormalChartModule B S hS hG Q
    (@id ((structureRingSheaf B S hS X).obj.obj (op Q)) b) •
        ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom
          (thickeningKerDefiningIdealEquiv B S hS hG Q j) =
      thickeningChartRestrict B S hS hG Q b • thickeningKerConormalEquiv B S hS hG Q j :=
  smallBaseChangeModulePushforward_conormal_smul B S hS hG Q b _

/-- **Semilinearity of `thickeningKerConormalEquiv`**: it carries multiplication by a function `b`
on the chart to the action of the restriction of `b` to the base change of the chart. -/
theorem thickeningKerConormalEquiv_smul (Q : SmallEtale B S hS X.1)
    (b : Γ((BigFppfOver.toScheme B S hS).obj Q.obj.left, ⊤))
    (j : RingHom.ker (thickeningChartRestrict B S hS hG Q).hom) :
    letI := conormalChartModule B S hS hG Q
    thickeningKerConormalEquiv B S hS hG Q (b • j) =
      thickeningChartRestrict B S hS hG Q b • thickeningKerConormalEquiv B S hS hG Q j :=
  (thickeningKerConormalEquiv_smul_eq_structureRing_smul B S hS hG Q b
      j).trans (thickeningIdealConormalIso_structureRing_smul B S hS hG Q b j)

/-- Restriction in the direct image of the conormal module is restriction along base-changed
charts. -/
theorem smallBaseChangeModulePushforward_conormal_map {Q Q' : SmallEtale B S hS X.1} (k : Q ⟶ Q')
    (m : (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.obj
        (op ((thickeningChartBaseChange B S hS hG.1).obj Q'))) :
    ((smallBaseChangeModulePushforward.{u, u} B S hS
        (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
        (firstOrderThickeningSubspace B S hS hG).2.2.rep).obj
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG))).val.map k.op m =
      (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.map
        ((thickeningChartBaseChange B S hS hG.1).map k).op m := rfl

/-- Restriction in the defining ideal sheaf is pullback of regular functions. -/
theorem definingIdealSheaf_map_val {Q Q' : SmallEtale B S hS X.1} (k : Q ⟶ Q')
    (x : (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.obj (op Q')) :
    (@id Γ((BigFppfOver.toScheme B S hS).obj Q.obj.left, ⊤) ((definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.map k.op x).1) =
      ((BigFppfOver.toScheme B S hS).map k.hom.left).appTop x.1 := rfl

/-- `thickeningIdealConormalIso` is injective on sections. -/
theorem thickeningIdealConormalIso_hom_injective (Q : SmallEtale B S hS X.1) :
    Function.Injective ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom :=
  fun x y h ↦ (thickeningIdealConormalIso_hom_inv B S hS hG Q x).symm.trans
    ((congrArg ((thickeningIdealConormalIso B S hS hG).inv.val.app (op Q)).hom h).trans
      (thickeningIdealConormalIso_hom_inv B S hS hG Q y))

/-- Two restrictions of a section of the defining ideal sheaf agree exactly when the pullbacks of
the underlying function agree. -/
theorem definingIdealSheaf_map_eq_iff {Q Q' : SmallEtale B S hS X.1} (k₁ k₂ : Q ⟶ Q')
    (x : (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.obj (op Q')) :
    (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.map k₁.op x =
      (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.map k₂.op x ↔
    ((BigFppfOver.toScheme B S hS).map k₁.hom.left).appTop x.1 =
        ((BigFppfOver.toScheme B S hS).map k₂.hom.left).appTop x.1 :=
  ⟨fun h ↦ (definingIdealSheaf_map_val B S hS hG k₁ x).symm.trans
      ((congrArg (fun y ↦ @id Γ((BigFppfOver.toScheme B S hS).obj Q.obj.left, ⊤) y.1) h).trans
        (definingIdealSheaf_map_val B S hS hG k₂ x)),
    fun h ↦ Subtype.ext ((definingIdealSheaf_map_val B S hS hG k₁ x).trans (h.trans
        (definingIdealSheaf_map_val B S hS hG k₂ x).symm))⟩

/-- Two pullbacks of an element of the kernel agree exactly when its two restrictions in the
defining ideal sheaf agree. -/
theorem thickeningKerDefiningIdealEquiv_map_eq_iff {Q Q' : SmallEtale B S hS X.1} (k₁ k₂ : Q ⟶ Q')
    (j : RingHom.ker (thickeningChartRestrict B S hS hG Q').hom) :
    ((BigFppfOver.toScheme B S hS).map k₁.hom.left).appTop j.1 =
        ((BigFppfOver.toScheme B S hS).map k₂.hom.left).appTop j.1 ↔
      (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS
          hG)).toSheafOfModules.val.map k₁.op (thickeningKerDefiningIdealEquiv B S hS hG Q' j) =
      (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS
          hG)).toSheafOfModules.val.map k₂.op (thickeningKerDefiningIdealEquiv B S hS hG Q' j) :=
  (definingIdealSheaf_map_eq_iff B S hS hG k₁ k₂ (thickeningKerDefiningIdealEquiv B S hS hG Q'
      j)).symm

/-- `thickeningIdealConormalIso` respects equalities of restrictions. -/
theorem thickeningIdealConormalIso_map_congr {Q Q' : SmallEtale B S hS X.1} (k₁ k₂ : Q ⟶ Q')
    (x : (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS
          hG)).toSheafOfModules.val.obj (op Q')) (h : (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS
          hG)).toSheafOfModules.val.map k₁.op x = (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.map k₂.op x) :
    ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom ((definingIdealSheaf B S hS X
        (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.map k₁.op x) =
      ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom ((definingIdealSheaf B S hS X
        (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.map k₂.op x) :=
  congrArg ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom h

/-- Equal restrictions in the ideal sheaf give equal restrictions in the conormal module. -/
theorem conormal_map_eq_of_definingIdealSheaf_map_eq {Q Q' : SmallEtale B S hS X.1} (k₁ k₂ : Q ⟶ Q')
    (x : (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS
          hG)).toSheafOfModules.val.obj (op Q')) (h : (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS
          hG)).toSheafOfModules.val.map k₁.op x = (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.map k₂.op x) :
      ((smallBaseChangeModulePushforward.{u, u} B S hS
        (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
        (firstOrderThickeningSubspace B S hS hG).2.2.rep).obj
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS
            hG))).val.map k₁.op (((thickeningIdealConormalIso B S hS hG).hom.val.app (op
            Q')).hom x) =
        ((smallBaseChangeModulePushforward.{u, u} B S hS
        (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
        (firstOrderThickeningSubspace B S hS hG).2.2.rep).obj
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS
            hG))).val.map k₂.op (((thickeningIdealConormalIso B S hS hG).hom.val.app (op
            Q')).hom x) :=
  (conormalChartEquiv_naturality B S hS hG k₁ x).symm.trans
      ((thickeningIdealConormalIso_map_congr B S hS hG k₁ k₂ x h).trans
          (conormalChartEquiv_naturality B S hS hG k₂ x))

/-- Equal restrictions in the conormal module give equal images of the restrictions in the ideal
sheaf. -/
theorem thickeningIdealConormalIso_map_eq_of_conormal_map_eq {Q Q' : SmallEtale B S hS X.1} (k₁ k₂ :
    Q ⟶ Q')
    (x : (definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.obj (op Q'))
    (h : ((smallBaseChangeModulePushforward.{u, u} B S hS
        (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
        (firstOrderThickeningSubspace B S hS hG).2.2.rep).obj
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS
            hG))).val.map k₁.op (((thickeningIdealConormalIso B S hS hG).hom.val.app (op
            Q')).hom x) =
        ((smallBaseChangeModulePushforward.{u, u} B S hS
        (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
        (firstOrderThickeningSubspace B S hS hG).2.2.rep).obj
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS
            hG))).val.map k₂.op (((thickeningIdealConormalIso B S hS hG).hom.val.app (op
            Q')).hom x)) :
    ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom ((definingIdealSheaf B S hS X
        (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.map k₁.op x) =
      ((thickeningIdealConormalIso B S hS hG).hom.val.app (op Q)).hom ((definingIdealSheaf B S hS X
        (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules.val.map k₂.op x) :=
  (conormalChartEquiv_naturality B S hS hG k₁ x).trans
        (h.trans (conormalChartEquiv_naturality B S hS hG k₂ x).symm)

/-- Restriction of `thickeningKerConormalEquiv` in the direct image is restriction in the conormal
module along the base-changed chart map. -/
theorem thickeningKerConormalEquiv_pushforward_map {Q Q' : SmallEtale B S hS X.1} (k : Q ⟶ Q')
    (j : RingHom.ker (thickeningChartRestrict B S hS hG Q').hom) :
    ((smallBaseChangeModulePushforward.{u, u} B S hS
        (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
        (firstOrderThickeningSubspace B S hS hG).2.2.rep).obj
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS
            hG))).val.map k.op (((thickeningIdealConormalIso B S hS hG).hom.val.app (op
            Q')).hom (thickeningKerDefiningIdealEquiv B S hS hG Q' j)) =
      (conormalModule B S hS X (firstOrderThickeningSubspace B S hS
          hG)).val.map ((thickeningChartBaseChange B S hS hG.1).map k).op
        (thickeningKerConormalEquiv B S hS hG Q' j) :=
  (smallBaseChangeModulePushforward_conormal_map B S hS hG k _).trans
    (congrArg ((conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.map
      ((thickeningChartBaseChange B S hS hG.1).map
          k).op) (thickeningKerConormalEquiv_apply B S hS hG Q' j).symm)

/-- Restriction of the image of `thickeningKerConormalEquiv` along a base-changed chart map. -/
theorem thickeningKerConormalEquiv_map {Q Q' : SmallEtale B S hS X.1} (k : Q ⟶ Q')
    (j : RingHom.ker (thickeningChartRestrict B S hS hG Q').hom) :
    (conormalModule B S hS X (firstOrderThickeningSubspace B S hS
        hG)).val.presheaf.map ((thickeningChartBaseChange B S hS hG.1).map k).op
        (thickeningKerConormalEquiv B S hS hG Q' j) =
      ((smallBaseChangeModulePushforward.{u, u} B S hS
        (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
        (firstOrderThickeningSubspace B S hS hG).2.2.rep).obj
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS
            hG))).val.map k.op (((thickeningIdealConormalIso B S hS hG).hom.val.app (op
            Q')).hom (thickeningKerDefiningIdealEquiv B S hS hG Q' j)) :=
  (thickeningKerConormalEquiv_pushforward_map B S hS hG k j).symm

/-- Equal pullbacks of a kernel element give equal restrictions of its conormal section. -/
theorem thickeningKerConormalEquiv_map_eq_of_appTop_eq {Q Q' : SmallEtale B S hS X.1} (k₁ k₂ : Q ⟶
    Q')
    (j : RingHom.ker (thickeningChartRestrict B S hS hG Q').hom)
    (h : ((BigFppfOver.toScheme B S hS).map k₁.hom.left).appTop j.1 =
        ((BigFppfOver.toScheme B S hS).map
            k₂.hom.left).appTop j.1) : (conormalModule B S hS X (firstOrderThickeningSubspace B S hS
            hG)).val.presheaf.map ((thickeningChartBaseChange B S hS hG.1).map k₁).op
          (thickeningKerConormalEquiv B S hS hG Q' j) =
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS
            hG)).val.presheaf.map ((thickeningChartBaseChange B S hS hG.1).map k₂).op
          (thickeningKerConormalEquiv B S hS hG Q' j) :=
  (thickeningKerConormalEquiv_map B S hS hG k₁
      j).trans ((conormal_map_eq_of_definingIdealSheaf_map_eq B S hS hG k₁ k₂ _
      ((thickeningKerDefiningIdealEquiv_map_eq_iff B S hS hG k₁ k₂ j).1
          h)).trans (thickeningKerConormalEquiv_map B S hS hG k₂ j).symm)

/-- Equal restrictions of the conormal section of a kernel element give equal pullbacks. -/
theorem appTop_eq_of_thickeningKerConormalEquiv_map_eq {Q Q' : SmallEtale B S hS X.1} (k₁ k₂ : Q ⟶
    Q')
    (j : RingHom.ker (thickeningChartRestrict B S hS hG Q').hom)
    (h : (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.presheaf.map
        ((thickeningChartBaseChange B S hS hG.1).map k₁).op
          (thickeningKerConormalEquiv B S hS hG Q' j) =
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS
            hG)).val.presheaf.map ((thickeningChartBaseChange B S hS hG.1).map k₂).op
          (thickeningKerConormalEquiv B S hS hG Q' j)) : ((BigFppfOver.toScheme B S
              hS).map k₁.hom.left).appTop j.1 =
        ((BigFppfOver.toScheme B S hS).map k₂.hom.left).appTop j.1 :=
  (thickeningKerDefiningIdealEquiv_map_eq_iff B S hS hG k₁ k₂
      j).2 (thickeningIdealConormalIso_hom_injective B S hS hG Q
      (thickeningIdealConormalIso_map_eq_of_conormal_map_eq B S hS hG k₁ k₂ _
        ((thickeningKerConormalEquiv_map B S hS hG k₁ j).symm.trans (h.trans
            (thickeningKerConormalEquiv_map B S hS hG k₂ j)))))

/-- Two pullbacks of an element `j` of the kernel agree exactly when the two restrictions of its
conormal section along the base-changed chart maps agree. -/
theorem thickeningKerConormalEquiv_map_eq_iff {Q Q' : SmallEtale B S hS X.1} (k₁ k₂ : Q ⟶ Q')
    (j : RingHom.ker (thickeningChartRestrict B S hS hG Q').hom) :
    ((BigFppfOver.toScheme B S hS).map k₁.hom.left).appTop j.1 =
        ((BigFppfOver.toScheme B S hS).map k₂.hom.left).appTop j.1 ↔ (conormalModule B S hS X
            (firstOrderThickeningSubspace B S hS hG)).val.presheaf.map ((thickeningChartBaseChange B
            S hS hG.1).map k₁).op
          (thickeningKerConormalEquiv B S hS hG Q' j) =
        (conormalModule B S hS X (firstOrderThickeningSubspace B S hS
            hG)).val.presheaf.map ((thickeningChartBaseChange B S hS hG.1).map k₂).op
          (thickeningKerConormalEquiv B S hS hG Q' j) :=
  ⟨thickeningKerConormalEquiv_map_eq_of_appTop_eq B S hS hG k₁ k₂ j,
      appTop_eq_of_thickeningKerConormalEquiv_map_eq B S hS hG k₁ k₂ j⟩

end Conormal


/-- The regular functions on an étale chart `V` equalized by the two projections of `V ×_X V`. -/
abbrev chartEqLocus {X : AlgebraicSpaces B S hS} (V : SmallEtale B S hS X.1) :
    Subring Γ((BigFppfOver.toScheme B S hS).obj V.obj.left, ⊤) :=
  ((BigFppfOver.toScheme B S hS).map
    (SmallEtale.prodFst B S hS X.1 V V).hom.left).appTop.hom.eqLocus
    ((BigFppfOver.toScheme B S hS).map (SmallEtale.prodSnd B S hS X.1 V V).hom.left).appTop.hom

section EqLocus

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1} (hG : IsFirstOrderThickening B S hS X G)

/-- An element of the kernel of restriction to `U = G ×_X V` is equalized by the two projections of
`V ×_X V` exactly when its conormal section over `U` is the restriction of a section over the
terminal chart `T₀`. -/
theorem mem_chartEqLocus_iff_exists_conormal {T₀ : BigFppfOver B S hS}
    (e : yoneda.obj T₀ ≅ G.toFunctor) (V : SmallEtale B S hS X.1)
    (hVs : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).presheaf
        V.obj.hom)
    (j : RingHom.ker (thickeningChartRestrict B S hS hG V).hom) :
    j.1 ∈ chartEqLocus B S hS V ↔
      ∃ n : (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.obj
          (op (thickeningTerminalChart B S hS hG.1 e)),
        chartRestrictLinear (hF := (IsThickening.space B S hS hG.1).2)
          (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG))
          ((thickeningTerminalChartIsTerminal B S hS hG.1 e).from
            ((thickeningChartBaseChange B S hS hG.1).obj V)) n =
        thickeningKerConormalEquiv B S hS hG V j :=
  (thickeningKerConormalEquiv_map_eq_iff B S hS hG (SmallEtale.prodFst B S hS X.1 V V)
    (SmallEtale.prodSnd B S hS X.1 V V) j).trans
    (exists_map_thickeningTerminalChart_eq_iff B S hS hG.1 e V hVs
      (P := (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.presheaf ⋙
        forget AddCommGrpCat.{u})
      (Stacks.SheafOfModules.isSheaf_forget _) _).symm

end EqLocus

/-- **The ideal of a first-order thickening over an affine chart is the base change of its global
sections.**  Let `G ⊂ X` be a first-order thickening whose closed member is represented by an
affine `T₀`, let `V` be an affine surjective étale chart of `X` with base change `U` to `G`, and
let `A'' ⊆ Γ(V)` be the functions equalized by the two projections of `V ×_X V`, mapping onto
`Γ(T₀)` by `κ` over the restriction to `U`.  Then `ker(Γ(V) → Γ(U))` is the base change along
`A'' → Γ(V)` of `ker κ`.

The ideal is the direct image of the conormal module `𝒞` of `G`, which is quasi-coherent, so
`𝒞(U) = Γ(U) ⊗_{Γ(T₀)} 𝒞(T₀)`; and `𝒞(T₀)` is `ker κ`, by gluing along `U ⟶ T₀`. -/
theorem isBaseChange_kerRestrict_of_isFirstOrderThickening
    {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1} (hG : IsFirstOrderThickening B S hS X G)
    {T₀ : BigFppfOver B S hS} (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (e : yoneda.obj T₀ ≅ G.toFunctor) (V : SmallEtale B S hS X.1)
    (hV : IsAffine ((BigFppfOver.toScheme B S hS).obj V.obj.left))
    (hVs : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf V.obj.hom)
    (κ : chartEqLocus B S hS V →+* Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤))
    (hκ : ∀ x, ((BigFppfOver.toScheme B S hS).map ((thickeningTerminalChartIsTerminal B S hS hG.1
        e).from ((thickeningChartBaseChange B S hS hG.1).obj V)).hom.left).appTop (κ x) =
      thickeningChartRestrict B S hS hG V x)
    (hκs : Function.Surjective κ)
    (hgA : Function.Injective ((BigFppfOver.toScheme B S hS).map
      ((thickeningTerminalChartIsTerminal B S hS hG.1 e).from
        ((thickeningChartBaseChange B S hS hG.1).obj V)).hom.left).appTop)
    (hJ : RingHom.ker (thickeningChartRestrict B S hS hG V).hom ^ 2 = ⊥) :
    letI : Algebra (chartEqLocus B S hS V) Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤) :=
      κ.toAlgebra
    letI : Algebra (chartEqLocus B S hS V) Γ((BigFppfOver.toScheme B S hS).obj V.obj.left, ⊤) :=
      (chartEqLocus B S hS V).subtype.toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((thickeningChartBaseChange B S hS hG.1).obj
          V).obj.left, ⊤) :=
      ((BigFppfOver.toScheme B S hS).map ((thickeningTerminalChartIsTerminal B S hS hG.1
        e).from ((thickeningChartBaseChange B S hS hG.1).obj V)).hom.left).appTop.hom.toAlgebra
    letI : Algebra Γ((BigFppfOver.toScheme B S hS).obj V.obj.left, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((thickeningChartBaseChange B S hS hG.1).obj
          V).obj.left, ⊤) :=
      (thickeningChartRestrict B S hS hG V).hom.toAlgebra
    letI : Algebra (chartEqLocus B S hS V) Γ((BigFppfOver.toScheme B S hS).obj
        ((thickeningChartBaseChange B S hS hG.1).obj V).obj.left, ⊤) :=
      ((thickeningChartRestrict B S hS hG V).hom.comp (chartEqLocus B S hS V).subtype).toAlgebra
    haveI : IsScalarTower (chartEqLocus B S hS V) Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((thickeningChartBaseChange B S hS hG.1).obj
          V).obj.left, ⊤) := IsScalarTower.of_algebraMap_eq fun x ↦ (hκ x).symm
    haveI : IsScalarTower (chartEqLocus B S hS V) Γ((BigFppfOver.toScheme B S hS).obj V.obj.left, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj ((thickeningChartBaseChange B S hS hG.1).obj
          V).obj.left, ⊤) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
    IsBaseChange Γ((BigFppfOver.toScheme B S hS).obj V.obj.left, ⊤)
      (kerRestrict (A' := chartEqLocus B S hS V) (A := Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤))
        (B' := Γ((BigFppfOver.toScheme B S hS).obj V.obj.left, ⊤))
        (B := Γ((BigFppfOver.toScheme B S hS).obj
          ((thickeningChartBaseChange B S hS hG.1).obj V).obj.left, ⊤))) := by
  classical
  let : Algebra (chartEqLocus B S hS V) Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤) :=
    κ.toAlgebra
  let : Algebra (chartEqLocus B S hS V) Γ((BigFppfOver.toScheme B S hS).obj V.obj.left, ⊤) :=
    (chartEqLocus B S hS V).subtype.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((thickeningChartBaseChange B S hS hG.1).obj
        V).obj.left, ⊤) :=
    ((BigFppfOver.toScheme B S hS).map ((thickeningTerminalChartIsTerminal B S hS hG.1
      e).from ((thickeningChartBaseChange B S hS hG.1).obj V)).hom.left).appTop.hom.toAlgebra
  let : Algebra Γ((BigFppfOver.toScheme B S hS).obj V.obj.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((thickeningChartBaseChange B S hS hG.1).obj
        V).obj.left, ⊤) :=
    (thickeningChartRestrict B S hS hG V).hom.toAlgebra
  let : Algebra (chartEqLocus B S hS V) Γ((BigFppfOver.toScheme B S hS).obj
      ((thickeningChartBaseChange B S hS hG.1).obj V).obj.left, ⊤) :=
    ((thickeningChartRestrict B S hS hG V).hom.comp (chartEqLocus B S hS V).subtype).toAlgebra
  have : IsScalarTower (chartEqLocus B S hS V) Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((thickeningChartBaseChange B S hS hG.1).obj
        V).obj.left, ⊤) := IsScalarTower.of_algebraMap_eq fun x ↦ (hκ x).symm
  have : IsScalarTower (chartEqLocus B S hS V) Γ((BigFppfOver.toScheme B S hS).obj V.obj.left, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((thickeningChartBaseChange B S hS hG.1).obj
        V).obj.left, ⊤) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let iU := conormalChartModule B S hS hG V
  let iT : Module Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤)
      ((conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.obj
        (op (thickeningTerminalChart B S hS hG.1 e))) :=
    inferInstanceAs (Module ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS (firstOrderThickeningSubspace B S hS hG).1.toFunctor
        (firstOrderThickeningSubspace B S hS hG).2.1).O).obj.obj
        (op (thickeningTerminalChart B S hS hG.1 e))) _)
  let iA : Module (chartEqLocus B S hS V)
      ((conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.obj
        (op (thickeningTerminalChart B S hS hG.1 e))) := Module.compHom _ κ
  have : IsScalarTower (chartEqLocus B S hS V) Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤)
      ((conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.obj
        (op (thickeningTerminalChart B S hS hG.1 e))) := ⟨fun a b n ↦ mul_smul (κ a) b n⟩
  let iTM : Module Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤)
      ((conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.obj
        (op ((thickeningChartBaseChange B S hS hG.1).obj V))) :=
    Module.compHom _ ((BigFppfOver.toScheme B S hS).map ((thickeningTerminalChartIsTerminal B S hS
      hG.1 e).from ((thickeningChartBaseChange B S hS hG.1).obj V)).hom.left).appTop.hom
  have : IsScalarTower Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((thickeningChartBaseChange B S hS hG.1).obj
        V).obj.left, ⊤)
      ((conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.obj
        (op ((thickeningChartBaseChange B S hS hG.1).obj V))) :=
    ⟨fun a b m ↦ mul_smul (((BigFppfOver.toScheme B S hS).map ((thickeningTerminalChartIsTerminal
      B S hS hG.1 e).from ((thickeningChartBaseChange B S hS hG.1).obj V)).hom.left).appTop a) b m⟩
  let res : (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.obj
        (op (thickeningTerminalChart B S hS hG.1 e)) →ₗ[Γ((BigFppfOver.toScheme B S hS).obj T₀, ⊤)]
      (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.obj
        (op ((thickeningChartBaseChange B S hS hG.1).obj V)) :=
    chartRestrictLinear (hF := (IsThickening.space B S hS hG.1).2)
    (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG))
    ((thickeningTerminalChartIsTerminal B S hS hG.1 e).from
      ((thickeningChartBaseChange B S hS hG.1).obj V))
  have hres : IsBaseChange Γ((BigFppfOver.toScheme B S hS).obj
      ((thickeningChartBaseChange B S hS hG.1).obj V).obj.left, ⊤) res :=
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS
      (IsThickening.space B S hS hG.1).1 (IsThickening.space B S hS hG.1).2
      (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG))).1
      (isQuasicoherentOnSite_modulePullback_of_isClosedImmersion B S hS
        (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
        (firstOrderThickeningSubspace B S hS hG).2.2 _
        (isQuasicoherentOnSite_definingIdealSheaf B S hS X
          (firstOrderThickeningSubspace B S hS hG)))
      (thickeningTerminalChart B S hS hG.1 e) ((thickeningChartBaseChange B S hS hG.1).obj V)
      hT₀ (isAffine_thickeningChartBaseChange B S hS hG.1 V hV)
      ((thickeningTerminalChartIsTerminal B S hS hG.1 e).from
        ((thickeningChartBaseChange B S hS hG.1).obj V))
  exact isBaseChange_ker_of_isBaseChange_of_glue Subtype.val_injective hgA hκs
    (surjective_thickeningStructureSharp_app_of_isAffine B S hS hG V hV) hJ kerRestrict
    (fun _ ↦ rfl) res hres
    (injective_map_thickeningTerminalChart B S hS hG.1 e V hVs
      (P := (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)).val.presheaf ⋙
        forget AddCommGrpCat.{u}) (Stacks.SheafOfModules.isSheaf_forget _))
    (thickeningKerConormalEquiv B S hS hG V) (thickeningKerConormalEquiv_smul B S hS hG V)
    fun j ↦ ⟨fun ⟨a, ha⟩ ↦ (mem_chartEqLocus_iff_exists_conormal B S hS hG e V hVs j).1
        (ha ▸ a.2),
      fun h ↦ ⟨⟨j.1, (mem_chartEqLocus_iff_exists_conormal B S hS hG e V hVs j).2 h⟩, rfl⟩⟩


/-! ### The first-order case -/

section FirstOrder

attribute [local instance] AlgebraicGeometry.preservesPullbacks_bigFppfOverToScheme

variable {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-- An algebraic space whose points are the image of a quasi-compact closed member of a
thickening is quasi-compact. -/
theorem isQuasiCompactSpace_of_isThickening (hG : IsThickening B S hS X G)
    (hGqc : IsQuasiCompactSpace B S hS G.toFunctor) : IsQuasiCompactSpace B S hS X.1 :=
  isQuasiCompactSpace_of_finite_jointly_surjective B S hS (I := PUnit.{1})
    (Fi := fun _ ↦ G.toFunctor) (fun _ ↦ hG.1.1) X.2 (fun _ ↦ G.ι)
    (Set.eq_univ_of_forall fun y ↦ Set.mem_iUnion.2 ⟨PUnit.unit, hG.2 y⟩) fun _ ↦ hGqc

/-- **A first-order thickening of an affine algebraic space is affine.**  Let `G ⊂ X` be a
first-order thickening of algebraic spaces over `S` whose closed member `G` is affine.  Then `X`
is affine.  This is the case of an affine closed member in the proof for finite order
thickenings of Stacks 05ZR. -/
theorem isAffineSpace_of_isFirstOrderThickening (hG : IsFirstOrderThickening B S hS X G)
    (hGa : IsAffineSpace B S hS G.toFunctor) : IsAffineSpace B S hS X.1 := by
  classical
  obtain ⟨T₀, hT₀, ⟨e₀⟩⟩ := hGa
  let e := e₀.symm
  have hXqc := isQuasiCompactSpace_of_isThickening B S hS hG.1
    (IsAffineSpace.isQuasiCompactSpace ⟨T₀, hT₀, ⟨e₀⟩⟩)
  obtain ⟨U₀, u', hU₀, hu's, hu'e⟩ :=
    (isQuasiCompactSpace_iff_exists_affine_etale_surjective_cover B S hS X.1 X.2).1 hXqc
  have hu'e' := (isEtale_iff_presheaf_of_yoneda B S hS u').1 hu'e
  let V : SmallEtale B S hS X.1 := ⟨CostructuredArrow.mk u', hu'e'⟩
  let P := SmallEtale.prodObj B S hS X.1 V V
  let t := SmallEtale.prodFst B S hS X.1 V V
  let s := SmallEtale.prodSnd B S hS X.1 V V
  have hpb : IsPullback (yoneda.map t.hom.left) (yoneda.map s.hom.left) u' u' :=
    V.property.rep.isPullback' V.obj.hom
  let W := IsThickening.space B S hS hG.1
  let bc := thickeningChartBaseChange B S hS hG.1
  let U := bc.obj V
  let RZ := bc.obj P
  let tT := thickeningTerminalChartIsTerminal B S hS hG.1 e
  let gU := tT.from U
  let rep := (isClosedImmersion_inclusion_of_isThickening B S hS hG.1).rep
  -- the schemes and their affineness
  let sV := (BigFppfOver.toScheme B S hS).obj V.obj.left
  let sP := (BigFppfOver.toScheme B S hS).obj P.obj.left
  let sU := (BigFppfOver.toScheme B S hS).obj U.obj.left
  let sZ := (BigFppfOver.toScheme B S hS).obj RZ.obj.left
  let sT := (BigFppfOver.toScheme B S hS).obj T₀
  have : IsAffine sV := hU₀
  have : IsAffine sT := hT₀
  have : IsAffine sU := isAffine_thickeningChartBaseChange B S hS hG.1 V hU₀
  have hsq := isPullback_thickeningChartBaseChange_prod B S hS hG.1 e V
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj
      (thickeningTerminalChart B S hS hG.1 e).obj.left) := hT₀
  have : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map gU.hom.left) :=
    isAffineHom_of_isAffine _
  have : IsAffine sZ := IsAffine.of_isPullback hsq
  have : IsAffine sP := by
    have hci : _root_.AlgebraicGeometry.IsClosedImmersion
        ((BigFppfOver.toScheme B S hS).map (rep.snd P.obj.hom)) :=
      (isClosedImmersion_inclusion_of_isThickening B S hS hG.1).property_snd P.obj.hom
    exact Stacks.Thickenings.isAffine_of_isThickening (X := sZ) (X' := sP)
      ⟨hci, (surjective_projection_of_isThickening B S hS hG.1 P).surj⟩
  -- the rings and maps
  let pB : Γ(sV, ⊤) ⟶ Γ(sU, ⊤) := ((BigFppfOver.toScheme B S hS).map (rep.snd V.obj.hom)).appTop
  let pC : Γ(sP, ⊤) ⟶ Γ(sZ, ⊤) := ((BigFppfOver.toScheme B S hS).map (rep.snd P.obj.hom)).appTop
  let τ : Γ(sV, ⊤) ⟶ Γ(sP, ⊤) := ((BigFppfOver.toScheme B S hS).map t.hom.left).appTop
  let σ : Γ(sV, ⊤) ⟶ Γ(sP, ⊤) := ((BigFppfOver.toScheme B S hS).map s.hom.left).appTop
  let aZ : Γ(sU, ⊤) ⟶ Γ(sZ, ⊤) := ((BigFppfOver.toScheme B S hS).map (bc.map t).hom.left).appTop
  let bZ : Γ(sU, ⊤) ⟶ Γ(sZ, ⊤) := ((BigFppfOver.toScheme B S hS).map (bc.map s).hom.left).appTop
  let gA : Γ(sT, ⊤) ⟶ Γ(sU, ⊤) := ((BigFppfOver.toScheme B S hS).map gU.hom.left).appTop
  have hcomm : ∀ f : P ⟶ V,
      pB ≫ ((BigFppfOver.toScheme B S hS).map (bc.map f).hom.left).appTop =
        ((BigFppfOver.toScheme B S hS).map f.hom.left).appTop ≫ pC := fun f ↦ by
    have k2 : (BigFppfOver.toScheme B S hS).map (bc.map f).hom.left ≫
        (BigFppfOver.toScheme B S hS).map (rep.snd V.obj.hom) =
        (BigFppfOver.toScheme B S hS).map (rep.snd P.obj.hom) ≫
          (BigFppfOver.toScheme B S hS).map f.hom.left :=
      ((BigFppfOver.toScheme B S hS).map_comp _ _).symm.trans ((congrArg _
        (smallBaseChange_map_snd B S hS (IsThickening.inclusion B S hS hG.1) rep f)).trans
          ((BigFppfOver.toScheme B S hS).map_comp _ _))
    have k := congrArg Scheme.Hom.appTop k2
    rwa [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at k
  have hτ : pB ≫ aZ = τ ≫ pC := hcomm t
  have hσ : pB ≫ bZ = σ ≫ pC := hcomm s
  have hpoZ : IsPushout gA gA aZ bZ := isPushout_appTop_of_isPullback hsq
  -- gluing of regular functions over the terminal chart
  have hglue : ∀ x : Γ(sU, ⊤), aZ x = bZ x → ∃! y : Γ(sT, ⊤), gA y = x := fun x hx ↦
    existsUnique_glue_thickeningTerminalChart B S hS hG.1 e V hu's
      (P := (SheafOfModules.unit (structureRingSheaf B S hS W)).val.presheaf ⋙
        forget AddCommGrpCat.{u})
      (Stacks.SheafOfModules.isSheaf_forget _) x hx
  let A'' := τ.hom.eqLocus σ.hom
  let eqZ := aZ.hom.eqLocus bZ.hom
  have hgA_mem : ∀ y, gA y ∈ eqZ := fun y ↦ by
    show (gA ≫ aZ) y = (gA ≫ bZ) y
    rw [hpoZ.w]
  let gA' : Γ(sT, ⊤) →+* eqZ := gA.hom.codRestrict eqZ hgA_mem
  have hgA'bij : Function.Bijective gA' := by
    refine ⟨fun y₁ y₂ h ↦ ?_, fun x ↦ ?_⟩
    · exact (hglue (gA y₂) (hgA_mem y₂)).unique (congrArg Subtype.val h) rfl
    · obtain ⟨y, hy, -⟩ := hglue x.1 x.2
      exact ⟨y, Subtype.ext hy⟩
  let eA : Γ(sT, ⊤) ≃+* eqZ := RingEquiv.ofBijective gA' hgA'bij
  have hpB_mem : ∀ x : A'', pB x ∈ eqZ := fun x ↦ by
    show (pB ≫ aZ) x = (pB ≫ bZ) x
    rw [hτ, hσ]
    exact congrArg pC.hom x.2
  let κ : A'' →+* Γ(sT, ⊤) :=
    eA.symm.toRingHom.comp ((pB.hom.comp A''.subtype).codRestrict eqZ hpB_mem)
  have hκ : ∀ x, gA (κ x) = pB x := fun x ↦
    congrArg Subtype.val (eA.apply_symm_apply ⟨pB x, hpB_mem x⟩)
  have hgAinj : Function.Injective gA := fun y₁ y₂ h ↦ hgA'bij.1 (Subtype.ext h)
  -- every regular function on the closed member lifts
  have hS1 : Function.Surjective κ := by
    intro a
    obtain ⟨φ, hφc, hφr⟩ := exists_lift_of_isFirstOrderThickening B S hS hG hT₀ e a
    have hb : (φ (op V) : Γ(sV, ⊤)) ∈ A'' := (hφc t.op).trans (hφc s.op).symm
    exact ⟨⟨φ (op V), hb⟩, hgAinj ((hκ _).trans (hφr (op V)))⟩
  -- the algebra structures of the deformation argument
  let : Algebra A'' Γ(sT, ⊤) := κ.toAlgebra
  let : Algebra A'' Γ(sV, ⊤) := A''.subtype.toAlgebra
  let : Algebra Γ(sT, ⊤) Γ(sU, ⊤) := gA.hom.toAlgebra
  let : Algebra Γ(sV, ⊤) Γ(sU, ⊤) := pB.hom.toAlgebra
  let : Algebra A'' Γ(sU, ⊤) := (pB.hom.comp A''.subtype).toAlgebra
  let : Algebra Γ(sV, ⊤) Γ(sP, ⊤) := τ.hom.toAlgebra
  let : Algebra A'' Γ(sP, ⊤) := (τ.hom.comp A''.subtype).toAlgebra
  have : IsScalarTower A'' Γ(sT, ⊤) Γ(sU, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (hκ x).symm
  have : IsScalarTower A'' Γ(sV, ⊤) Γ(sU, ⊤) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A'' Γ(sV, ⊤) Γ(sP, ⊤) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hetA : Algebra.Etale Γ(sT, ⊤) Γ(sU, ⊤) := by
    have : Etale ((BigFppfOver.toScheme B S hS).map gU.hom.left) :=
      etale_toScheme_toOver_map B S hS _ gU
    exact HasRingHomProperty.appTop (P := @Etale) _ this
  have hetτ : Algebra.FormallySmooth Γ(sV, ⊤) Γ(sP, ⊤) := by
    have : Etale ((BigFppfOver.toScheme B S hS).map t.hom.left) :=
      etale_toScheme_toOver_map B S hS _ t
    have : Algebra.Etale Γ(sV, ⊤) Γ(sP, ⊤) := HasRingHomProperty.appTop (P := @Etale) _ this
    infer_instance
  let σ' : Γ(sV, ⊤) →ₐ[A''] Γ(sP, ⊤) :=
    { σ.hom with commutes' := fun x ↦ (x.2 : τ x = σ x).symm }
  have hJ : RingHom.ker (algebraMap Γ(sV, ⊤) Γ(sU, ⊤)) ^ 2 = ⊥ := by
    have h1 := ker_thickeningStructureSharp_app B S hS hG V
    have h2 := definingIdealAt_mul_self_eq_bot B S hS hG V
    rw [sq]
    exact h1.symm ▸ h2
  have hspec : Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(sT, ⊤) Γ(sU, ⊤))) := by
    have := surjective_thickeningTerminalChart_from B S hS hG.1 e V hu's
    have hnat := Scheme.isoSpec_hom_naturality ((BigFppfOver.toScheme B S hS).map gU.hom.left)
    have : Surjective (sU.isoSpec.hom ≫ Spec.map gA) := by
      show Surjective (sU.isoSpec.hom ≫ Spec.map
        ((BigFppfOver.toScheme B S hS).map gU.hom.left).appTop)
      rw [hnat]
      infer_instance
    have : Surjective (Spec.map gA) := Surjective.of_comp sU.isoSpec.hom _
    exact (Spec.map gA).surjective
  have hbc : IsBaseChange Γ(sV, ⊤)
      (kerRestrict (A' := A'') (A := Γ(sT, ⊤)) (B' := Γ(sV, ⊤)) (B := Γ(sU, ⊤))) :=
    isBaseChange_kerRestrict_of_isFirstOrderThickening B S hS hG hT₀ e V hU₀ hu's κ hκ hS1
      hgAinj hJ
  have hjR : RingHom.ker pC.hom ≤
      (RingHom.ker (algebraMap Γ(sV, ⊤) Γ(sU, ⊤))).map (algebraMap Γ(sV, ⊤) Γ(sP, ⊤)) := by
    intro x hx
    have hxI : x ∈ definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) (op P) := by
      rwa [← ker_thickeningStructureSharp_app B S hS hG P]
    obtain ⟨y, hy⟩ := (bijective_sectionsBaseChange_definingIdealSheaf B S hS X
      (firstOrderThickeningSubspace B S hS hG) t hU₀ (inferInstanceAs (IsAffine sP))).2 ⟨x, hxI⟩
    have key : ∀ y, Subtype.val (sectionsBaseChange (definingIdealSheaf B S hS X
        (firstOrderThickeningSubspace B S hS hG)).toSheafOfModules t y) ∈
          (RingHom.ker (algebraMap Γ(sV, ⊤) Γ(sU, ⊤))).map (algebraMap Γ(sV, ⊤) Γ(sP, ⊤)) := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => exact zero_mem _
      | tmul c j =>
        refine Ideal.mul_mem_left _ c (Ideal.mem_map_of_mem _ ?_)
        have hj : Subtype.val j ∈ definingIdealAt B S hS X
            (firstOrderThickeningSubspace B S hS hG) (op V) := j.2
        rwa [← ker_thickeningStructureSharp_app B S hS hG V] at hj
      | add y z hy hz =>
        rw [map_add]
        exact add_mem hy hz
    have := key y
    rwa [hy] at this
  obtain ⟨hetB, hspecB, hbij⟩ := etale_and_bijective_lift_of_isBaseChange
    (A' := A'') (A := Γ(sT, ⊤)) (B' := Γ(sV, ⊤)) (B := Γ(sU, ⊤)) (C' := Γ(sP, ⊤))
    (E := Γ(sZ, ⊤)) Subtype.val_injective hS1
    (surjective_thickeningStructureSharp_app_of_isAffine B S hS hG V hU₀) hJ hspec hbc σ'
    pC.hom aZ.hom bZ.hom hpoZ (fun b ↦ congrArg (fun f ↦ f.hom b) hτ.symm)
    (fun b ↦ congrArg (fun f ↦ f.hom b) hσ.symm) hjR
  -- the descent
  let φ := Algebra.TensorProduct.lift (Algebra.ofId Γ(sV, ⊤) Γ(sP, ⊤)) σ' fun _ _ ↦ Commute.all _ _
  let φe : CommRingCat.of (Γ(sV, ⊤) ⊗[A''] Γ(sV, ⊤)) ≅ Γ(sP, ⊤) :=
    (RingEquiv.ofBijective (φ : Γ(sV, ⊤) ⊗[A''] Γ(sV, ⊤) →+* Γ(sP, ⊤)) hbij).toCommRingCatIso
  have hpo : IsPushout (CommRingCat.ofHom A''.subtype) (CommRingCat.ofHom A''.subtype) τ σ := by
    refine (CommRingCat.isPushout_tensorProduct A'' Γ(sV, ⊤) Γ(sV, ⊤)).of_iso (Iso.refl _)
      (Iso.refl _) (Iso.refl _) φe rfl rfl ?_ ?_
    · ext b
      show φ (b ⊗ₜ 1) = τ b
      rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
      rfl
    · ext b
      show φ (1 ⊗ₜ b) = σ b
      rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      rfl
  have hEt : Etale (Spec.map (CommRingCat.ofHom A''.subtype)) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).2 hetB
  have hSurj : Surjective (Spec.map (CommRingCat.ofHom A''.subtype)) := ⟨hspecB⟩
  have : IsAffine sP := inferInstance
  exact isAffineSpace_of_isPushout_eqLocus B S hS X.2 hU₀ this u' t.hom.left s.hom.left hpb
    hu's hu'e' hEt hSurj hpo

end FirstOrder

end AlgebraicGeometry.Space

end
