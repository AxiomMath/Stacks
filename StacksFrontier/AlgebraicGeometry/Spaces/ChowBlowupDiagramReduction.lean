module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupAlongClopen
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupRelativelyAmple
public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSite
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowBlowupDiagram
public import StacksFrontier.AlgebraicGeometry.Spaces.ClopenPointSetDecomposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionDenseOpenInSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveSpaceOverRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemma.ProjectiveCompactification
import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionProper
import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSupport
import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent

/-!
# Stacks 088R from Stacks 088Q

Let `f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over `S`, with `Y`
quasi-compact and quasi-separated.  Let `U ⊆ X` be a quasi-compact open subspace and let
`i : U ⟶ ℙⁿ_Y` be an immersion over `Y`.  Stacks 088R produces the diagram
`AlgebraicGeometry.Space.HasChowBlowupDiagram`:
```
        U
     ↙  ↓  ↘  ↘
   X ← X' → Z' → Z
     ↘  ↓  ↙    ↓
        Y  ←  ℙⁿ_Y
```
This file proves that conclusion from one input that is not yet available in this library: the
conclusion of **Stacks 088Q**, in exactly the shape of
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion`, which
still carries some of its inputs as hypotheses.

The clause "`Z' ⟶ Y` is representable" needs the representability of admissible blowups of
algebraic spaces, which Stacks gets from the description of a blowup as a relative `Proj`
(Stacks 085Q, 084B).  Here it is
`AlgebraicGeometry.Space.relativelyRepresentable_of_isAdmissibleBlowup`: an admissible blowup
carries a relatively ample invertible module (Stacks 0D34).

## The proof, and where it departs from the source

Let `Z ⊆ ℙⁿ_Y` be the scheme-theoretic image of `i`.  As `i` is quasi-compact, `U ⟶ Z` is an
open immersion (Stacks 088G).  Stacks 088Q, applied to `U ⟶ X` and `U ⟶ Z`, gives
`U`-admissible blowups `X₁' ⟶ X` and `Z' ⟶ Z` together with open immersions
`i₁ : X₁' ⟶ W` and `i₂ : Z' ⟶ W` into a space `W` that is separated over `Y`.  The composite
`Z' ⟶ Z ⟶ ℙⁿ_Y ⟶ Y` is proper, so `i₂` has closed image (Stacks 04NX).  So the image of `Z'` is
open and closed in `|W|`.

The source concludes from Stacks 085T and 083S that "`U` is scheme theoretically dense in
`X₁'`", and hence that `X₁' ⊆ Z'`.  This is not right in general: the centre of a
`U`-admissible blowup is only disjoint from `U`.  For example, if `X = U ⊔ V` with `V` nonempty
then the identity of `X` is a `U`-admissible blowup in which `U` is not dense.  The argument is
completed as follows.  The set `T` of points of `X₁'` that land in `Z'` is open and closed, and
it contains the image of `U`.  Its complement `C` is a closed subspace of finite presentation,
and the inclusion `X' = X₁' ∖ C ⟶ X₁'` is the blowup of `X₁'` in `C`
(`AlgebraicGeometry.Space.isBlowupAlong_openComplement_ι_of_isOpen`).  This blowup is admissible
for the inverse image of `U`, because `X₁' ⟶ X` is an isomorphism over `U` (Stacks 085T).  By
Stacks 086C the composite `X' ⟶ X₁' ⟶ X` is a `U`-admissible blowup, and `X' ⟶ W` factors
through the open subspace `Z'`.

## Main results

* `AlgebraicGeometry.Space.hasChowBlowupDiagram_of_commonAdmissibleBlowup`: the conclusion of
  Stacks 088R, from the conclusion of Stacks 088Q.  It carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 088R](https://stacks.math.columbia.edu/tag/088R)
* [Stacks Project, Tag 088Q](https://stacks.math.columbia.edu/tag/088Q)
* [Stacks Project, Tag 088G](https://stacks.math.columbia.edu/tag/088G)
* [Stacks Project, Tag 04NX](https://stacks.math.columbia.edu/tag/04NX)
* [Stacks Project, Tag 085T](https://stacks.math.columbia.edu/tag/085T)
* [Stacks Project, Tag 086C](https://stacks.math.columbia.edu/tag/086C)
-/

/- `hasChowBlowupDiagram_of_commonAdmissibleBlowup` is Stacks
088R over one input: `hcommon`, the conclusion of Stacks 088Q in the shape of
`exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion`.  Once that theorem holds without
its hypotheses `h07VR` and `h0873`, instantiating `hcommon` with it gives Stacks 088R
outright. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The points of the range of a monomorphism are the image of the points of its source. -/
theorem range_pointsMap_ι_range_of_mono {A G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : A ⟶ G)
    [Mono p] :
    Set.range (pointsMap B S hS (Subfunctor.range p).toFunctor (Subfunctor.range p).ι) =
      Set.range (pointsMap B S hS A p) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨pointsMap B S hS _ (asIso (Subfunctor.toRange p)).inv y, ?_⟩
    rw [← pointsMap_comp_apply, inv_toRange_comp]
  · rintro ⟨y, rfl⟩
    refine ⟨pointsMap B S hS _ (Subfunctor.toRange p) y, ?_⟩
    rw [← pointsMap_comp_apply, Subfunctor.toRange_ι]

/-- **Stacks 088R, from Stacks 088Q.**  Let
`f : X ⟶ Y` be a separated morphism of finite type of algebraic spaces over `S`, with `Y`
quasi-compact and quasi-separated.  Let `U ⊆ X` be a quasi-compact open subspace and let
`i : U ⟶ ℙⁿ_Y` be an immersion over `Y`.  Then the diagram of Stacks 088R exists
(`AlgebraicGeometry.Space.HasChowBlowupDiagram`).

The input `hcommon` is the conclusion of Stacks 088Q, in the shape of
`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_isOpenImmersion_of_isOpenImmersion`.
See the module documentation for the proof, which completes a step of the
source's argument. -/
theorem hasChowBlowupDiagram_of_commonAdmissibleBlowup (hZ : B.Contains (⊤_ Scheme.{u}))
    (hcommon : ∀ {Y U X₁ X₂ : AlgebraicSpaces B S hS}
      (f₁ : X₁ ⟶ Y) (f₂ : X₂ ⟶ Y) (j₁ : U ⟶ X₁) (j₂ : U ⟶ X₂),
      IsQuasiCompactSpace B S hS Y.1 → IsAbsolutelyQuasiSeparated B S hS hZ Y.1 →
      ∀ (hj₁ : IsOpenImmersion B S hS j₁.hom) (hj₂ : IsOpenImmersion B S hS j₂.hom),
      j₁ ≫ f₁ = j₂ ≫ f₂ →
      IsFiniteType B S hS (j₁ ≫ f₁).hom → IsSeparated B S hS (j₁ ≫ f₁).hom →
      IsFiniteType B S hS f₁.hom → IsSeparated B S hS f₁.hom →
      IsFiniteType B S hS f₂.hom → IsSeparated B S hS f₂.hom →
      ∃ (X₁' X₂' X : AlgebraicSpaces B S hS) (b₁ : X₁' ⟶ X₁) (b₂ : X₂' ⟶ X₂)
        (i₁ : X₁' ⟶ X) (i₂ : X₂' ⟶ X) (g : X ⟶ Y) (u₁ : U ⟶ X₁') (u₂ : U ⟶ X₂'),
        IsAdmissibleBlowup B S hS ⟨Subfunctor.range j₁.hom, @isOpenSubspace_range_of_open B S hS
          _ _ j₁.hom (mono_of_isOpenImmersion B S hS _ hj₁) U.2 hj₁⟩ b₁ ∧
        IsAdmissibleBlowup B S hS ⟨Subfunctor.range j₂.hom, @isOpenSubspace_range_of_open B S hS
          _ _ j₂.hom (mono_of_isOpenImmersion B S hS _ hj₂) U.2 hj₂⟩ b₂ ∧
        IsOpenImmersion B S hS i₁.hom ∧ IsOpenImmersion B S hS i₂.hom ∧
        IsSeparated B S hS g.hom ∧ IsFiniteType B S hS g.hom ∧
        i₁ ≫ g = b₁ ≫ f₁ ∧ i₂ ≫ g = b₂ ≫ f₂ ∧
        u₁ ≫ b₁ = j₁ ∧ u₂ ≫ b₂ = j₂ ∧ u₁ ≫ i₁ = u₂ ≫ i₂ ∧
        IsOpenImmersion B S hS u₁.hom ∧ IsOpenImmersion B S hS u₂.hom)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (U : Subfunctor X) (hU : IsOpenSubspace B S hS U)
    (hUqc : IsQuasiCompactSpace B S hS U.toFunctor)
    (hYqc : IsQuasiCompactSpace B S hS Y) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (n : ℕ) (i : U.toFunctor ⟶ projectiveSpaceOver B S hS Y n) (hi : IsImmersion B S hS i)
    (hiY : i ≫ prod.fst = U.ι ≫ f)
    (hft : IsFiniteType B S hS f) (hsep : IsSeparated B S hS f) :
    HasChowBlowupDiagram B S hS hX f U hU n i := by
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) := hasSheafify_bigFppfOver B S hS
  -- Projective space over `Y`.
  have hP : IsAlgebraicSpace B S hS (projectiveSpaceOver B S hS Y n) :=
    isAlgebraicSpace_projectiveSpaceOver B S hS hY n
  have hPY : IsProper B S hS (prod.fst : projectiveSpaceOver B S hS Y n ⟶ Y) :=
    isProper_projectiveSpaceOver_fst B S hS hY n
  have hPqs : IsAbsolutelyQuasiSeparated B S hS hZ (projectiveSpaceOver B S hS Y n) :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hP hYqs
      (isQuasiSeparated_of_isSeparated B S hS hPY.1)
  -- `X` is quasi-compact and quasi-separated.
  have hXqc : IsQuasiCompactSpace B S hS X :=
    isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 Y) f)) (hft.2 Y hY hYqc (𝟙 Y))
  have hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hX hYqs
      (isQuasiSeparated_of_isSeparated B S hS hsep)
  -- The scheme-theoretic image `Z` of `i`, by Stacks 088G.
  have hiqc : IsQuasiCompact B S hS i :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hP hPqs hUqc i
  obtain ⟨hjopen, -, hrange, -, -⟩ :=
    isOpenImmersion_and_dense_toSchemeTheoreticImage_of_qc_or_reduced B S hS hU.1 hP i hi
      (Or.inl hiqc)
  set Zs := schemeTheoreticImageSubfunctor B S hS i with hZsdef
  have hZcl : IsClosedSubspace B S hS Zs :=
    isClosedSubspace_schemeTheoreticImageSubfunctor B S hS i hP
  set uZ := toSchemeTheoreticImage B S hS i with huZdef
  have huZk : uZ ≫ Zs.ι = i := toSchemeTheoreticImage_ι B S hS i
  -- The four algebraic spaces and four morphisms to which Stacks 088Q is applied.
  let Xsp : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ysp : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let Usp : AlgebraicSpaces B S hS := ⟨U.toFunctor, hU.1⟩
  let Zsp : AlgebraicSpaces B S hS := ⟨Zs.toFunctor, hZcl.1⟩
  let f₁ : Xsp ⟶ Ysp := ObjectProperty.homMk f
  let f₂ : Zsp ⟶ Ysp := ObjectProperty.homMk (Zs.ι ≫ prod.fst)
  let j₁ : Usp ⟶ Xsp := ObjectProperty.homMk U.ι
  let j₂ : Usp ⟶ Zsp := ObjectProperty.homMk uZ
  have hj : j₁ ≫ f₁ = j₂ ≫ f₂ := by
    refine ObjectProperty.hom_ext _ ?_
    change U.ι ≫ f = uZ ≫ Zs.ι ≫ prod.fst
    rw [← Category.assoc, huZk, hiY]
  have hUιqc : IsQuasiCompact B S hS U.ι :=
    isQuasiCompact_of_isQuasiCompactSpace B S hS hZ hX hXqs hUqc U.ι
  have hUιft : IsFiniteType B S hS U.ι :=
    ⟨isLocallyOfFiniteType_of_isImmersion B S hS U.ι
      (isImmersion_of_isOpenImmersion B S hS hU.2), hUιqc⟩
  have hUft : IsFiniteType B S hS (j₁ ≫ f₁).hom :=
    isFiniteType_comp B S hS hU.1 hX hY U.ι f hUιft hft
  have hUsep : IsSeparated B S hS (j₁ ≫ f₁).hom :=
    isSeparated_comp B S hS U.ι f (isSeparated_of_mono U.ι inferInstance) hsep
  have hX₂ft : IsFiniteType B S hS f₂.hom :=
    isFiniteType_comp B S hS hZcl.1 hP hY _ _ (isFiniteType_of_isClosedImmersion B S hS _ hZcl.2)
      hPY.2.1
  have hX₂sep : IsSeparated B S hS f₂.hom :=
    isSeparated_comp B S hS _ _ (isSeparated_of_isClosedImmersion B S hS _ hZcl.2) hPY.1
  obtain ⟨X₁', X₂', W, b₁, b₂, i₁, i₂, g, u₁, u₂, hb₁, hb₂, hi₁, hi₂, hgsep, -, hc₁, hc₂, hu₁b,
    hu₂b, hu, hu₁, hu₂⟩ :=
    hcommon f₁ f₂ j₁ j₂ hYqc hYqs hU.2 hjopen hj hUft hUsep hft hsep hX₂ft hX₂sep
  have hb₁' : IsAdmissibleBlowup B S hS ⟨U, hU⟩ b₁ := by
    have e : (⟨U, hU⟩ : OpenSubspaces B S hS X) = ⟨Subfunctor.range U.ι,
        @isOpenSubspace_range_of_open B S hS _ _ U.ι (mono_of_isOpenImmersion B S hS _ hU.2)
          hU.1 hU.2⟩ :=
      Subtype.ext (Subfunctor.range_ι U).symm
    rw [e]
    exact hb₁
  have hu₁bh : u₁.hom ≫ b₁.hom = U.ι := congrArg (·.hom) hu₁b
  have hu₂bh : u₂.hom ≫ b₂.hom = uZ := congrArg (·.hom) hu₂b
  have huh : u₁.hom ≫ i₁.hom = u₂.hom ≫ i₂.hom := congrArg (·.hom) hu
  have hc₁h : i₁.hom ≫ g.hom = b₁.hom ≫ f := congrArg (·.hom) hc₁
  have hc₂h : i₂.hom ≫ g.hom = b₂.hom ≫ Zs.ι ≫ prod.fst := congrArg (·.hom) hc₂
  have : Mono i₂.hom := mono_of_isOpenImmersion B S hS _ hi₂
  -- `Z' ⟶ Y` is proper.
  have hb₂proper : IsProper B S hS b₂.hom := IsAdmissibleBlowup.isProper B S hS hb₂
  have hZ'Y : IsProper B S hS (b₂.hom ≫ Zs.ι ≫ prod.fst) :=
    isProper_comp B S hS X₂'.2 hZcl.1 hY _ _ hb₂proper
      (isProper_comp B S hS hZcl.1 hP hY _ _
        (isProper_of_isClosedImmersion B S hS hZcl.1 hP _ hZcl.2) hPY)
  -- The image of `Z'` in `W` is open and closed (Stacks 04NX).
  have hZ'closed : IsClosed (Set.range (pointsMap B S hS X₂'.1 i₂.hom)) := by
    refine isClosed_range_of_comp_of_isSeparated B S hS X₂'.2 W.2 hY i₂.hom g.hom ?_ hgsep
    rw [hc₂h]
    exact hZ'Y.2.2
  have hZ'open : IsOpen (Set.range (pointsMap B S hS X₂'.1 i₂.hom)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS i₂.hom hi₂
  -- The points `T` of `X₁'` landing in `Z'`, and the complementary closed subspace `C`.
  set T : Set (points B S hS X₁'.1) :=
    pointsMap B S hS X₁'.1 i₁.hom ⁻¹' Set.range (pointsMap B S hS X₂'.1 i₂.hom) with hTdef
  have hTo : IsOpen T := hZ'open.preimage (continuous_pointsMap B S hS i₁.hom)
  have hTc : IsClosed T := hZ'closed.preimage (continuous_pointsMap B S hS i₁.hom)
  set C := openSubspaceOfPoints B S hS X₁'.1 Tᶜ with hCdef
  have hCcl : IsClosedSubspace B S hS C :=
    isClosedSubspace_openSubspaceOfPoints B S hS X₁'.2 Tᶜ hTc.isOpen_compl hTo.isClosed_compl
  have hCop : IsOpenSubspace B S hS C :=
    isOpenSubspace_openSubspaceOfPoints B S hS X₁'.2 Tᶜ hTc.isOpen_compl
  have hCpts : subspacePointSet B S hS X₁'.1 C = Tᶜ :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS Tᶜ
  set O := openComplement B S hS C with hOdef
  have hO : IsOpenSubspace B S hS O := isOpenSubspace_openComplement B S hS X₁'.2 C hCcl
  have hOpts : subspacePointSet B S hS X₁'.1 O = T := by
    refine (range_pointsMap_ι_openComplement B S hS C).trans ?_
    change (subspacePointSet B S hS X₁'.1 C)ᶜ = T
    rw [hCpts, compl_compl]
  -- `C` is of finite presentation over `X₁'`.
  have hX₁'proper : IsProper B S hS b₁.hom := IsAdmissibleBlowup.isProper B S hS hb₁'
  have hX₁'qc : IsQuasiCompactSpace B S hS X₁'.1 :=
    isQuasiCompactSpace_of_iso B S hS (asIso (pullback.snd (𝟙 X) b₁.hom))
      (hX₁'proper.2.1.2 X hX hXqc (𝟙 X))
  have hX₁'qs : IsAbsolutelyQuasiSeparated B S hS hZ X₁'.1 :=
    isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ X₁'.2 hXqs
      (isQuasiSeparated_of_isSeparated B S hS hX₁'proper.1)
  have hCqc : IsQuasiCompactSpace B S hS C.toFunctor :=
    isQuasiCompactSpace_of_isClosedImmersion B S hS hX₁'qc C.ι hCcl.2
  have hCfp : IsFinitePresentation B S hS C.ι :=
    ⟨isLocallyOfFinitePresentation_of_presheafEtale B S hS
      (presheaf_etale_of_isOpenImmersion B S hS hCop.2),
      isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X₁'.2 hX₁'qs hCqc C.ι,
      isQuasiSeparated_of_isSeparated B S hS (isSeparated_of_mono C.ι inferInstance)⟩
  -- The new source `X' = X₁' ∖ C` and the blowup `c : X' ⟶ X₁'` in `C`.
  let X'' : AlgebraicSpaces B S hS := ⟨O.toFunctor, hO.1⟩
  let c : X'' ⟶ X₁' := ObjectProperty.homMk O.ι
  have hcbl : IsBlowupAlong B S hS ⟨C, hCcl⟩ c :=
    isBlowupAlong_openComplement_ι_of_isOpen X₁' ⟨C, hCcl⟩ (by
      change IsOpen (subspacePointSet B S hS X₁'.1 C)
      rw [hCpts]
      exact hTc.isOpen_compl)
  -- `X₁' ⟶ X` is an isomorphism over `U`, so the inverse image of `U` lands in `T`.
  obtain ⟨Zc, hZcfp, hZcdisj, hZcbl⟩ := hb₁'
  set OZ := openComplementOfClosedSubspace B S hS Xsp Zc with hOZdef
  have hOZpts : subspacePointSet B S hS X OZ.1 = (subspacePointSet B S hS X Zc.1)ᶜ :=
    subspacePointSet_openComplement B S hS Xsp Zc
  have hUOZ : U ≤ OZ.1 := by
    refine le_of_range_pointsMap_ι_subset B S hS OZ.2 ?_
    change subspacePointSet B S hS X U ⊆ subspacePointSet B S hS X OZ.1
    rw [hOZpts]
    exact Set.disjoint_left.1 hZcdisj
  have hiso : IsIso (OZ.1.fromPreimage b₁.hom) := isIso_fromPreimage_openComplement hZcbl
  have hpre : (U.preimage b₁.hom).ι ≫ i₁.hom = (U.fromPreimage b₁.hom ≫ u₂.hom) ≫ i₂.hom := by
    have hsec : U.fromPreimage b₁.hom ≫ u₁.hom = (U.preimage b₁.hom).ι := by
      ext T' a
      have hinj := ((isIso_iff_bijective ((OZ.1.fromPreimage b₁.hom).app T')).1
        inferInstance).1
      have ha : b₁.hom.app T' a.1 ∈ U.obj T' := a.2
      have hb : b₁.hom.app T' (u₁.hom.app T' ⟨b₁.hom.app T' a.1, ha⟩) = b₁.hom.app T' a.1 :=
        congrFun (congrArg (fun φ => φ.app T') hu₁bh) ⟨b₁.hom.app T' a.1, ha⟩
      have h₁ : u₁.hom.app T' ⟨b₁.hom.app T' a.1, ha⟩ ∈ (OZ.1.preimage b₁.hom).obj T' := by
        change b₁.hom.app T' (u₁.hom.app T' ⟨b₁.hom.app T' a.1, ha⟩) ∈ OZ.1.obj T'
        rw [hb]
        exact hUOZ _ ha
      have h₂ : a.1 ∈ (OZ.1.preimage b₁.hom).obj T' := hUOZ _ ha
      have := @hinj ⟨_, h₁⟩ ⟨_, h₂⟩ (Subtype.ext hb)
      exact congrArg Subtype.val this
    rw [Category.assoc, ← huh, ← Category.assoc, hsec]
  have hdisj : Disjoint (subspacePointSet B S hS X₁'.1 (U.preimage b₁.hom))
      (subspacePointSet B S hS X₁'.1 C) := by
    rw [hCpts, Set.disjoint_compl_right_iff_subset]
    rintro _ ⟨p, rfl⟩
    refine ⟨pointsMap B S hS _ (U.fromPreimage b₁.hom ≫ u₂.hom) p, ?_⟩
    rw [← pointsMap_comp_apply, ← hpre, pointsMap_comp_apply]
  have hcadm : IsAdmissibleBlowup B S hS
      ⟨U.preimage b₁.hom, isOpenSubspace_preimage B S hS b₁.hom U hX X₁'.2 hU⟩ c :=
    isAdmissibleBlowup_of_isBlowupAlong hCfp hdisj hcbl
  have hπ : IsAdmissibleBlowup B S hS ⟨U, hU⟩ (c ≫ b₁) :=
    isAdmissibleBlowup_comp_of_isQuasiCompactSpace (X := Xsp) (X' := X₁') (X'' := X'')
      (b := b₁) (c := c) hZ hXqc hXqs ⟨U, hU⟩
      ⟨Zc, hZcfp, hZcdisj, hZcbl⟩ hcadm
  -- The open immersion `X' ⟶ Z'`.
  have hW' : IsOpenSubspace B S hS (Subfunctor.range i₂.hom) :=
    isOpenSubspace_range_of_open B S hS i₂.hom X₂'.2 hi₂
  obtain ⟨j₀, hj₀⟩ := (factorsThrough_openSubspace_iff_points B S hS W.2 hO.1
    (Subfunctor.range i₂.hom) hW' (O.ι ≫ i₁.hom)).2 (by
      rw [range_pointsMap_ι_range_of_mono B S hS i₂.hom]
      rintro _ ⟨p, rfl⟩
      have hp : pointsMap B S hS _ O.ι p ∈ T := by
        rw [← hOpts]
        exact ⟨p, rfl⟩
      rw [pointsMap_comp_apply]
      exact hp)
  let j : O.toFunctor ⟶ X₂'.1 := j₀ ≫ (asIso (Subfunctor.toRange i₂.hom)).inv
  have hji : j ≫ i₂.hom = O.ι ≫ i₁.hom := by
    change (j₀ ≫ (asIso (Subfunctor.toRange i₂.hom)).inv) ≫ i₂.hom = _
    rw [← hj₀, Category.assoc, inv_toRange_comp]
  have hjopen' : IsOpenImmersion B S hS j := by
    refine isOpenImmersion_of_comp_mono B S hS j i₂.hom ?_
    rw [hji]
    exact isOpenImmersion_comp B S hS _ _ hO.2 hi₁
  -- The open immersion `U ⟶ X'`.
  obtain ⟨uX', huX'⟩ := (factorsThrough_openSubspace_iff_points B S hS X₁'.2 hU.1 O hO
    u₁.hom).2 (by
      rintro _ ⟨y, rfl⟩
      have hOpts' : Set.range (pointsMap B S hS O.toFunctor O.ι) = T := hOpts
      rw [hOpts']
      change pointsMap B S hS _ i₁.hom (pointsMap B S hS _ u₁.hom y) ∈
        Set.range (pointsMap B S hS X₂'.1 i₂.hom)
      rw [← pointsMap_comp_apply, huh, pointsMap_comp_apply]
      exact ⟨_, rfl⟩)
  have huX'open : IsOpenImmersion B S hS uX' := by
    refine isOpenImmersion_of_comp_mono B S hS uX' O.ι ?_
    rw [huX']
    exact hu₁
  -- Assemble the diagram.
  refine ⟨X'', X₂', Zsp, c ≫ b₁, ObjectProperty.homMk j, b₂, Zs.ι, uX', u₂.hom, uZ, hrange,
    huX'open, hu₂, hjopen, hπ, hjopen', hZ'Y, ?_, hb₂, hZcl.2, ?_, ?_, hu₂bh, huZk, ?_⟩
  · exact MorphismProperty.comp_mem _ _ _ (relativelyRepresentable_of_isAdmissibleBlowup _ b₂ hb₂)
      (MorphismProperty.comp_mem _ _ _ hZcl.2.rep
        (relativelyRepresentable_projectiveSpaceOver_fst B S hS Y n))
  · change uX' ≫ O.ι ≫ b₁.hom = U.ι
    rw [← Category.assoc, huX', hu₁bh]
  · change uX' ≫ j = u₂.hom
    refine (cancel_mono i₂.hom).1 ?_
    rw [Category.assoc, hji, ← Category.assoc, huX', huh]
  · change (O.ι ≫ b₁.hom) ≫ f = j ≫ b₂.hom ≫ Zs.ι ≫ prod.fst
    rw [Category.assoc, ← hc₁h, ← Category.assoc, ← hji, Category.assoc, hc₂h]

end AlgebraicGeometry.Space

end
