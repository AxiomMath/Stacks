module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProductRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AtlasChartCountablyIndexed
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductFormalBase
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.PullbackChartCover
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Types

/-!
# Types of fibre products of formal algebraic spaces

If `X ⟶ Y ⟵ Z` are morphisms of formal algebraic spaces and `X` and `Z` are locally countably
indexed, locally countably indexed and classical, locally weakly adic, locally adic\*, or
locally Noetherian (the last under a condition on `X_red ⟶ Y_red`), then so is `X ×_Y Z`. Each
statement here strengthens the unprimed declaration of the same name in
`StacksFrontier.AlgebraicGeometry.FormalSpace.FibreProductTypes`.

## Main definitions

* `HasAffineEtaleChartPropertyOfAtlas'`: condition (2) implies condition (1) of Stacks 0AKX
  for a property of fppf sheaves.

## Main results

* `hasAffineEtaleAtlasWithProperty_pullback'`: chart fibre products form an atlas of `X ×_Y Z`
  whose members satisfy a given property.
* `isLocallyCountablyIndexed_pullback'`, `isLocallyCountablyIndexedAndClassical_pullback'`,
  `isLocallyWeaklyAdic_pullback'`, `isLocallyAdicStar_pullback'`,
  `isLocallyNoetherian_pullback'`: the five clauses of Stacks 0GBB.
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AKX, condition (2) implies condition (1)**, for a property `P` of fppf sheaves:
if a formal algebraic space has an atlas as in Definition 0AIM all of whose members satisfy
`P`, then every affine formal algebraic space representable étale over it satisfies `P`.

That `T` be a formal algebraic space is the standing hypothesis of Stacks 0AKX, which is
stated for a formal algebraic space over `S`; it is not implied by the atlas data alone, which
additionally carries the set-theoretic condition of Stacks 0AIS. Carrying it makes this
predicate the implication the library proves at `P = IsCountablyIndexed`,
`hasAffineEtaleChartProperty_iff_hasAffineEtaleAtlasWithProperty_isCountablyIndexed`. -/
abbrev HasAffineEtaleChartPropertyOfAtlas' (P : FppfSheaf B S hS → Prop) : Prop :=
  ∀ T : FppfSheaf B S hS, IsFormalAlgebraicSpace B S hS T →
    HasAffineEtaleAtlasWithProperty B S hS T P →
    ∀ (U : FppfSheaf B S hS) (a : U ⟶ T), IsAffineFormalAlgebraicSpace B S hS U →
      IsRepresentableEtale B S hS a → P U

/-- The common content of the five clauses of **Stacks 0GBB**: the chart fibre products
`Uⱼᵢ ×_{Vⱼ} Wⱼₖ` form an atlas of `X ×_Y Z` as in Definition 0AIM all of whose members satisfy
`P`, so condition (2) of Stacks 0AKX for `P` passes from `X` and `Z` to `X ×_Y Z`. -/
theorem hasAffineEtaleAtlasWithProperty_pullback' (P : FppfSheaf B S hS → Prop)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z)
    (hXatlas : HasAffineEtaleAtlasWithProperty B S hS X P)
    (hZatlas : HasAffineEtaleAtlasWithProperty B S hS Z P)
    (h0AKX : HasAffineEtaleChartPropertyOfAtlas' B S hS P)
    (hPaff : AffineChartFibreProductStable B S hS P)
    (hcover : HasChartPullbackCover B S hS f g) :
    HasAffineEtaleAtlasWithProperty B S hS (pullback f g) P := by
  classical
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨-, J, V, v, hVaff, hVet, hVsurj⟩ := id hY
  choose I U a hUaff hUet hUsurj using fun j ↦
    (isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS (v j) f hY
      (hVaff j) hX).2
  choose K W b hWaff hWet hWsurj using fun j ↦
    (isFormalAlgebraicSpace_pullback_chart_of_isFormalAlgebraicSpace B S hS (v j) g hY
      (hVaff j) hZ).2
  refine ⟨Σ j, I j × K j,
    fun p ↦ pullback (a p.1 p.2.1 ≫ pullback.fst (v p.1) f)
      (b p.1 p.2.2 ≫ pullback.fst (v p.1) g),
    fun p ↦ chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1) (b p.1 p.2.2),
    fun p ↦ ?_, fun p ↦ ?_, ?_, fun p ↦ ?_⟩
  · exact isAffineFormalAlgebraicSpace_pullback B S hS _ _
      (hasRepresentableRelativeProducts_of_isAffineFormalAlgebraicSpace B S hS (hVaff p.1))
      (IsAffineFormalAlgebraicSpace.isSeparated B S hS (hVaff p.1))
      (hUaff p.1 p.2.1) (hWaff p.1 p.2.2)
  · exact isRepresentableEtale_chartPullbackMap B S hS f g (v p.1) (a p.1 p.2.1)
      (b p.1 p.2.2) (hVet p.1) (hUet p.1 p.2.1) (hWet p.1 p.2.2)
  · exact hcover v ⟨hVaff, hVet, hVsurj⟩ a (fun j ↦ ⟨hUaff j, hUet j, hUsurj j⟩) b
      fun j ↦ ⟨hWaff j, hWet j, hWsurj j⟩
  · have key : ∀ {T : FppfSheaf B S hS} (h : T ⟶ Y), IsFormalAlgebraicSpace B S hS T →
        HasAffineEtaleAtlasWithProperty B S hS T P → ∀ {U : FppfSheaf B S hS}
        (c : U ⟶ pullback (v p.1) h), IsAffineFormalAlgebraicSpace B S hS U →
        IsRepresentableEtale B S hS c → P U := fun {_} h hT hat {_} c hU hc ↦
      h0AKX _ hT hat _ (c ≫ pullback.snd (v p.1) h) hU
        (IsRepresentableEtale.comp B S hS hc
          (isRepresentableEtale_pullback_snd B S hS (v p.1) h (hVet p.1)))
    exact hPaff _ _ (hUaff p.1 p.2.1) (hVaff p.1) (hWaff p.1 p.2.2)
      (key f hX hXatlas (a p.1 p.2.1) (hUaff p.1 p.2.1) (hUet p.1 p.2.1))
      (key g hZ hZatlas (b p.1 p.2.2) (hWaff p.1 p.2.2) (hWet p.1 p.2.2))

/-- The atlas of `hasAffineEtaleAtlasWithProperty_pullback'` together with formality of
`X ×_Y Z`, which is the shape of the five clauses of Stacks 0GBB. -/
private theorem isFormalAlgebraicSpace_and_atlas_pullback (P : FppfSheaf B S hS → Prop)
    {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsFormalAlgebraicSpace B S hS X ∧ HasAffineEtaleAtlasWithProperty B S hS X P)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsFormalAlgebraicSpace B S hS Z ∧ HasAffineEtaleAtlasWithProperty B S hS Z P)
    (h0AKX : HasAffineEtaleChartPropertyOfAtlas' B S hS P)
    (hPaff : AffineChartFibreProductStable B S hS P)
    (hcover : HasChartPullbackCover B S hS f g) :
    IsFormalAlgebraicSpace B S hS (pullback f g) ∧
      HasAffineEtaleAtlasWithProperty B S hS (pullback f g) P :=
  ⟨isFormalAlgebraicSpace_pullback_of_isFormalAlgebraicSpace B S hS f g hY hX.1 hZ.1,
    hasAffineEtaleAtlasWithProperty_pullback' B S hS P f g hX.1 hY hZ.1 hX.2 hZ.2 h0AKX hPaff
      hcover⟩

/-- **Stacks 0GBB, clause (1).** If `X` and `Z` are locally countably indexed, then so is
`X ×_Y Z`. The hypotheses `hPaff` and `hcover` are the inputs of the source which the
library does not carry; the implication (2) ⟹ (1) of Stacks 0AKX, which the other four clauses
carry as `h0AKX`, is a theorem at countable indexing and is discharged here, as is
separatedness of the chart. -/
@[stacks 0GBB "clause (1), locally countably indexed; the affine case (0AN3 with 0GB4) \
and the 0AIM covering condition for the chart cover are named hypotheses"]
theorem isLocallyCountablyIndexed_pullback' {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyCountablyIndexed B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyCountablyIndexed B S hS Z)
    (hPaff : AffineChartFibreProductStable B S hS (IsCountablyIndexed B S hS))
    (hcover : HasChartPullbackCover B S hS f g) :
    IsLocallyCountablyIndexed B S hS (pullback f g) :=
  isFormalAlgebraicSpace_and_atlas_pullback B S hS (IsCountablyIndexed B S hS) f g hX hY hZ
    (fun T hT hatlas U a hU ha ↦
      isCountablyIndexed_of_isRepresentableEtale_of_isLocallyCountablyIndexed B S hS T
        ⟨hT, hatlas⟩ U a hU ha)
    hPaff hcover

/-- **Stacks 0GBB, clause (2).** If `X` and `Z` are locally countably indexed and classical,
then so is `X ×_Y Z`. The hypotheses `h0AKX`, `hPaff` and `hcover` are the
inputs of the source which the library does not carry. -/
theorem isLocallyCountablyIndexedAndClassical_pullback' {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y)
    (g : Z ⟶ Y) (hX : IsLocallyCountablyIndexedAndClassical B S hS X)
    (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyCountablyIndexedAndClassical B S hS Z)
    (h0AKX : HasAffineEtaleChartPropertyOfAtlas' B S hS
      fun T ↦ IsCountablyIndexed B S hS T ∧ IsClassical B S hS T)
    (hPaff : AffineChartFibreProductStable B S hS
      fun T ↦ IsCountablyIndexed B S hS T ∧ IsClassical B S hS T)
    (hcover : HasChartPullbackCover B S hS f g) :
    IsLocallyCountablyIndexedAndClassical B S hS (pullback f g) :=
  isFormalAlgebraicSpace_and_atlas_pullback B S hS
    (fun T ↦ IsCountablyIndexed B S hS T ∧ IsClassical B S hS T) f g hX hY hZ h0AKX hPaff hcover

/-- **Stacks 0GBB, clause (3).** If `X` and `Z` are locally weakly adic, then so is `X ×_Y Z`.
The hypotheses `h0AKX`, `hPaff` and `hcover` are the inputs of the source
which the library does not carry. -/
theorem isLocallyWeaklyAdic_pullback' {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyWeaklyAdic B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyWeaklyAdic B S hS Z)
    (h0AKX : HasAffineEtaleChartPropertyOfAtlas' B S hS (IsWeaklyAdic B S hS))
    (hPaff : AffineChartFibreProductStable B S hS (IsWeaklyAdic B S hS))
    (hcover : HasChartPullbackCover B S hS f g) :
    IsLocallyWeaklyAdic B S hS (pullback f g) :=
  isFormalAlgebraicSpace_and_atlas_pullback B S hS _ f g hX hY hZ h0AKX hPaff hcover

/-- **Stacks 0GBB, clause (4).** If `X` and `Z` are locally adic\*, then so is `X ×_Y Z`. The
hypotheses `h0AKX`, `hPaff` and `hcover` are the inputs of the source which
the library does not carry. -/
theorem isLocallyAdicStar_pullback' {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyAdicStar B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyAdicStar B S hS Z)
    (h0AKX : HasAffineEtaleChartPropertyOfAtlas' B S hS (IsAdicStar B S hS))
    (hPaff : AffineChartFibreProductStable B S hS (IsAdicStar B S hS))
    (hcover : HasChartPullbackCover B S hS f g) :
    IsLocallyAdicStar B S hS (pullback f g) :=
  isFormalAlgebraicSpace_and_atlas_pullback B S hS _ f g hX hY hZ h0AKX hPaff hcover

/-- **Stacks 0GBB, clause (5).** If `X` and `Z` are locally Noetherian and `X_red ⟶ Y_red` is
locally of finite type, then `X ×_Y Z` is locally Noetherian. The affine input `hPaff` is
assumed relative to the finite type condition, which the source transfers to the chart maps by
Stacks 0GB7 and Morphisms of Spaces Lemma 67.23.4. -/
theorem isLocallyNoetherian_pullback' {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hX : IsLocallyNoetherian B S hS X) (hY : IsFormalAlgebraicSpace B S hS Y)
    (hZ : IsLocallyNoetherian B S hS Z)
    (hfin : HasLocallyOfFiniteTypeReduction B S hS f)
    (h0AKX : HasAffineEtaleChartPropertyOfAtlas' B S hS (IsNoetherian B S hS))
    (hPaff : HasLocallyOfFiniteTypeReduction B S hS f →
      AffineChartFibreProductStable B S hS (IsNoetherian B S hS))
    (hcover : HasChartPullbackCover B S hS f g) :
    IsLocallyNoetherian B S hS (pullback f g) :=
  isFormalAlgebraicSpace_and_atlas_pullback B S hS (IsNoetherian B S hS) f g hX hY hZ h0AKX
    (hPaff hfin) hcover

end AlgebraicGeometry.FormalSpace

end
