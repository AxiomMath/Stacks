module

public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Sheaf
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Modules.AffineGlobalSplitShortExact
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.UnramifiedConormal
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Thickenings.Affine
public import StacksFrontier.AlgebraicGeometry.Thickenings.BaseChange
public import StacksFrontier.AlgebraicGeometry.Thickenings.SummandSubschemeConormal
public import StacksFrontier.AlgebraicGeometry.Thickenings.TransitivityConormalShortExact

/-!
# Local complete intersection morphisms are locally unobstructed

Let `U ⊆ U'` be a first-order thickening of affine schemes, let `X'` be flat over `U'` and set
`X = U ×_{U'} X'`.  Let `Z ⟶ U` be finite locally free of degree `d` and let `f : Z ⟶ X` be
formally unramified and a local complete intersection morphism.  Then `f` extends across the
thickening: there is a first-order thickening `Z ⊆ Z'` with `Z' ⟶ U'` finite locally free of
degree `d`, with `Z = U ×_{U'} Z'`, and with a morphism `Z' ⟶ X'` extending `f`.

This is [Stacks Project, Tag 06D8], at the level of schemes.  The source states it for an
algebraic space `X'`; the hypothesis there is that `f` be *unramified*, and only formal
unramifiedness is used, so the statement proved here is the scheme-level case of the tag with
that hypothesis weakened.

## Main results

* `Stacks.Thickenings.selfUniversalFirstOrderThickening`: a first-order thickening `X ⟶ X'` is a
  universal first-order thickening of `X` over `X'`.  This is the datum that reads the conormal
  sequence of [Stacks Project, Tag 06BA] as the sequence
  `0 → f^* 𝒞_{X/X'} → 𝒞_{Z/X'} → 𝒞_{Z/X} → 0` of the source.
* `Stacks.Thickenings.exists_isFirstOrderThickening_isFiniteLocallyFreeOfRank_of_splitting`: the
  proof of the tag from the splitting onwards, with the split conormal sequence as a hypothesis
  and no affineness, local complete intersection or universality hypothesis at all.
* `Stacks.Thickenings.exists_finiteLocallyFreeOfRank_deformation`: the tag itself, for schemes.

## Implementation notes

The ambient scheme `Z''` of the source is the universal first-order thickening of `Z` over `X'`,
`Stacks.Thickenings.universalFirstOrderThickening` of [Stacks Project, Tag 04F3]; it exists
because `f` and the closed immersion `X ⟶ X'` are formally unramified, hence so is the composite.
The conormal sequence of the source is then the sequence of [Stacks Project, Tag 06BA] for the
pair of universal first-order thickenings `(Z ⊆ Z'')` over `(X ⊆ X')`, where the second is
`Stacks.Thickenings.selfUniversalFirstOrderThickening`;
`Stacks.Thickenings.transitivityConormalShortComplex_shortExact` is its short exactness and
`AlgebraicGeometry.isFiniteLocallyFree_universalConormalSheaf_of_isLocalCompleteIntersection`
([Stacks Project, Tag 06B9]) the finite local freeness of its third term.

Two comparisons are needed to join those two inputs.  The third term of the sequence is the
conormal sheaf of the *relative* universal first-order thickening
`Stacks.Thickenings.relativeThickening`, while Tag 06B9 speaks of
`Stacks.Thickenings.universalConormalSheaf`, the conormal sheaf of the universal first-order
thickening that `Stacks.Thickenings.universalFirstOrderThickening` chooses; the two are compared
by the canonical isomorphism `Stacks.Thickenings.UniversalFirstOrderThickening.canonicalMap`
between any two universal first-order thickenings of the same morphism, read through
[Stacks Project, Tag 0473] — `Stacks.Immersion.isIso_immersionConormalSheafMap_of_flat`, whose
flatness hypothesis is satisfied because that canonical morphism is an isomorphism.  And
quasi-coherence of the second and third terms is `Stacks.Conormal.conormalSheaf_isQuasicoherent`,
which is stated for the same term under a different name.

`Z` is affine because it is finite over the affine `U`, which is what makes the sequence split
globally
(`AlgebraicGeometry.Scheme.Modules.nonempty_splitting_of_shortExact_of_isFiniteLocallyFree`);
`U'` is affine too, by [Stacks Project, Tag 06AD], but that is not needed.

## References

* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 04F3](https://stacks.math.columbia.edu/tag/04F3)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 06AD](https://stacks.math.columbia.edu/tag/06AD)
* [Stacks Project, Tag 06B9](https://stacks.math.columbia.edu/tag/06B9)
* [Stacks Project, Tag 06BA](https://stacks.math.columbia.edu/tag/06BA)
* [Stacks Project, Tag 09ZU](https://stacks.math.columbia.edu/tag/09ZU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open Stacks.Immersion Stacks.ClosedImmersion

universe u

namespace Stacks.Thickenings

/-! ### A first-order thickening is its own universal first-order thickening -/

/-- **A first-order thickening `i : X ⟶ X'` is a universal first-order thickening of `X` over
`X'`**, with ambient scheme `X'` and structure morphism the identity of `X'`.

The universal property is trivial in this case: a lift `T' ⟶ X'` over `X'` is forced to be the
given morphism `T' ⟶ X'`, and it satisfies the compatibility with the inclusion by hypothesis. -/
def selfUniversalFirstOrderThickening {X X' : Scheme.{u}} (i : X ⟶ X')
    (hi : IsFirstOrderThickening i) : UniversalFirstOrderThickening i where
  ambient := X'
  inclusion := i
  toBase := 𝟙 X'
  isUniversal :=
    { isFirstOrderThickening := hi
      inclusion_toBase := Category.comp_id _
      existsUnique_lift := fun {T T'} j _ a b hcomm =>
        ⟨b, ⟨hcomm, Category.comp_id _⟩, fun a' ha' => by rw [← ha'.2, Category.comp_id]⟩ }

/-! ### The deformation produced by a split conormal sequence -/

section Splitting

variable {Z W X X' U U' : Scheme.{u}} (i : Z ⟶ W) [IsClosedImmersion i] (hsq : i.ker ^ 2 = ⊥)

/-- **The identification of the summand that was cut out with the conormal sheaf of the subscheme
it cuts out, followed by the inclusion into `𝒪_W`, is the summand's own inclusion.**  This is
`Stacks.Thickenings.conormalSheafIsoOfMono_hom_ι` read in the conormal spelling of
[Stacks Project, Tag 01R2], which is the one
`Stacks.Thickenings.isIso_immersionConormalSheafMap_of_splitting` consumes. -/
theorem conormalSheafIsoOfMono_trans_selfIso_hom_comp_firstOrderImmersionConormalSheafι
    {M : SheafOfModules.{u} (structureSheafRing W.toLocallyRingedSpace.toRingedSpace)}
    (κ : M ⟶ SheafOfModules.unit (structureSheafRing W.toLocallyRingedSpace.toRingedSpace))
    (hκ : Mono κ) [M.IsQuasicoherent]
    (hvan : κ ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0) :
    (conormalSheafIsoOfMono κ hκ i hsq hvan ≪≫
          (modulePushforward (monoSubschemeι κ hκ).toLRSHom.toShHom).mapIso
            (Stacks.Immersion.conormalSheafSelfIso (monoSubschemeι κ hκ))).hom ≫
        firstOrderImmersionConormalSheafι (monoSubschemeι κ hκ)
          (ker_monoSubschemeι_sq_eq_bot κ hκ i hsq hvan) = κ := by
  rw [Iso.trans_hom, Functor.mapIso_hom, firstOrderImmersionConormalSheafι, Category.assoc,
    ← Category.assoc ((modulePushforward _).map _), ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.id_comp,
    conormalSheafIsoOfMono_hom_ι κ hκ i hsq hvan]

variable (iX : X ⟶ X') [IsClosedImmersion iX] (hsqX : iX.ker ^ 2 = ⊥)
  (iU : U ⟶ U') [IsClosedImmersion iU] (hsqU : iU.ker ^ 2 = ⊥)
  (fZ : Z ⟶ X) (g : W ⟶ X') (comm : i ≫ g = fZ ≫ iX)
  (pX : X ⟶ U) (pX' : X' ⟶ U') [Flat pX']

include hsq hsqX hsqU in
/-- **The deformation of a finite locally free morphism produced by a split conormal sequence.**

Let `i : Z ⟶ W` be a first-order thickening, let `(fZ, g) : (Z ⊆ W) → (X ⊆ X')` be a morphism to a
first-order thickening which is in turn cartesian and flat over a first-order thickening
`iU : U ⟶ U'`, and let `Z ⟶ U` be finite locally free of degree `d`.  Suppose the conormal
sequence of the upper square splits, that is, the canonical map
`fZ^* 𝒞_{X/X'} ⟶ 𝒞_{Z/W}` of [Stacks Project, Tag 01R4] is the inclusion of a direct summand with
quasi-coherent complement `C`.

Then the summand `C`, read as a quasi-coherent sheaf of ideals inside `𝒪_W`, cuts out of `W` a
first-order thickening `Z ⟶ Z'` of `Z` with `Z' ⟶ U'` finite locally free of degree `d` and
`Z = U ×_{U'} Z'`.

This is the proof of [Stacks Project, Tag 06D8] from the splitting onwards: the subscheme is
`StacksFrontier.AlgebraicGeometry.Thickenings.SummandSubscheme`, the conormal identification is
`Stacks.Thickenings.isIso_immersionConormalSheafMap_of_splitting`, and the transfer of degree and
cartesianness is
`Stacks.Thickenings.isFiniteLocallyFreeOfRank_and_isPullback_of_isIso_conormalSheafMap_factor`. -/
theorem exists_isFirstOrderThickening_isFiniteLocallyFreeOfRank_of_splitting
    (hsqXU : IsPullback iX pX pX' iU) (d : ℕ)
    (hZU : Stacks.Morphisms.IsFiniteLocallyFreeOfRank (fZ ≫ pX) d)
    {C : SheafOfModules.{u} (structureSheafRing Z.toLocallyRingedSpace.toRingedSpace)}
    (hC : C.IsQuasicoherent) (γ : immersionConormalSheaf i ⟶ C)
    (hzero : immersionConormalSheafMap i iX fZ g (toShHom_square comm) ≫ γ = 0)
    (σ : (ShortComplex.mk (immersionConormalSheafMap i iX fZ g (toShHom_square comm)) γ
      hzero).Splitting) :
    ∃ (Z' : Scheme.{u}) (iZ : Z ⟶ Z') (q : Z' ⟶ W), IsFirstOrderThickening iZ ∧
      IsClosedImmersion q ∧ iZ ≫ q = i ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((q ≫ g) ≫ pX') d ∧
      IsPullback iZ (fZ ≫ pX) ((q ≫ g) ≫ pX') iU := by
  let := isQuasicoherent_modulePushforward i hC
  have hsmono : Mono σ.s := by
    have : IsSplitMono σ.s := ⟨⟨⟨γ, σ.s_g⟩⟩⟩
    infer_instance
  obtain ⟨κ, hκ, hvan, hκeq⟩ : ∃ (κ : (modulePushforward i.toLRSHom.toShHom).obj C ⟶
      SheafOfModules.unit (structureSheafRing W.toLocallyRingedSpace.toRingedSpace))
      (_ : Mono κ), (κ ≫ structureSheafModuleHom i.toLRSHom.toShHom = 0) ∧
        κ = (modulePushforward i.toLRSHom.toShHom).map σ.s ≫
          firstOrderImmersionConormalSheafι i hsq :=
    ⟨immersionConormalSummandι i hsq σ.s, mono_immersionConormalSummandι i hsq σ.s hsmono,
      immersionConormalSummandι_comp_structureSheafModuleHom i hsq σ.s, rfl⟩
  have hiZ := isFirstOrderThickening_toMonoSubscheme κ hκ i hsq hvan
  have := hiZ.1
  have hiso := isIso_immersionConormalSheafMap_of_splitting
    (toMonoSubscheme κ hκ i hvan) (monoSubschemeι κ hκ) i (toMonoSubscheme_comp κ hκ i hvan) hsq
    (ker_monoSubschemeι_sq_eq_bot κ hκ i hsq hvan) iX fZ g comm γ hzero σ
    (conormalSheafIsoOfMono κ hκ i hsq hvan ≪≫
      (modulePushforward (monoSubschemeι κ hκ).toLRSHom.toShHom).mapIso
        (Stacks.Immersion.conormalSheafSelfIso (monoSubschemeι κ hκ)))
    ((conormalSheafIsoOfMono_trans_selfIso_hom_comp_firstOrderImmersionConormalSheafι i hsq κ hκ
      hvan).trans hκeq)
  obtain ⟨hfl, hpb⟩ := isFiniteLocallyFreeOfRank_and_isPullback_of_isIso_conormalSheafMap_factor
    hiZ ⟨inferInstance, hsqX⟩ ⟨inferInstance, hsqU⟩
    (Arrow.homMk (f := Arrow.mk (toMonoSubscheme κ hκ i hvan)) (g := Arrow.mk iX)
      (𝟙 Z ≫ fZ) (monoSubschemeι κ hκ ≫ g)
      (by
        show (𝟙 Z ≫ fZ) ≫ iX = toMonoSubscheme κ hκ i hvan ≫ (monoSubschemeι κ hκ ≫ g)
        rw [Category.id_comp, ← comm, ← Category.assoc, toMonoSubscheme_comp κ hκ i hvan]))
    (Arrow.homMk (f := Arrow.mk iX) (g := Arrow.mk iU) pX pX' hsqXU.w.symm)
    (inferInstanceAs (Flat pX')) hsqXU d
    (by
      show Stacks.Morphisms.IsFiniteLocallyFreeOfRank ((𝟙 Z ≫ fZ) ≫ pX) d
      rw [Category.id_comp]
      exact hZU) hiso
  have hpb' : IsPullback (toMonoSubscheme κ hκ i hvan) ((𝟙 Z ≫ fZ) ≫ pX)
      ((monoSubschemeι κ hκ ≫ g) ≫ pX') iU := hpb
  rw [Category.id_comp] at hpb'
  exact ⟨monoSubscheme κ hκ, toMonoSubscheme κ hκ i hvan, monoSubschemeι κ hκ, hiZ,
    inferInstance, toMonoSubscheme_comp κ hκ i hvan, hfl, hpb'⟩

end Splitting

/-! ### Tag 06D8 for schemes -/

/-- **[Stacks Project, Tag 06D8], for schemes: a formally unramified local complete intersection
morphism out of a finite locally free scheme is unobstructed.**

Let `iU : U ⟶ U'` be a first-order thickening with `U` affine, let `pX' : X' ⟶ U'` be flat, and
let `X = U ×_{U'} X'` be exhibited by the cartesian square `hX`.  Let `pZ : Z ⟶ U` be finite
locally free of degree `d` and let `fZ : Z ⟶ X` be a morphism over `U` which is formally
unramified and a local complete intersection morphism.  Then there is a first-order thickening
`iZ : Z ⟶ Z'` together with `pZ' : Z' ⟶ U'` finite locally free of degree `d` and `f' : Z' ⟶ X'`
extending `fZ`, such that `Z = U ×_{U'} Z'` and `f'` lies over `pZ'`.

Two deliberate differences from the source.  The source states the lemma for an *algebraic space*
`X'`; this is its case of a scheme.  And the source assumes `f` *unramified*, while only formal
unramifiedness is used — the local complete intersection hypothesis is what supplies the finite
local freeness of `𝒞_{Z/X}` ([Stacks Project, Tag 06B9]) — so the hypothesis is weakened here and
the statement implies the tag's.  Affineness of `U'`, which the source also assumes, is a
consequence of affineness of `U` by [Stacks Project, Tag 06AD] and is not carried.

The proof is the source's.  `Z''` is the universal first-order thickening of `Z` over `X'`; the
conormal sequence `0 → fZ^* 𝒞_{X/X'} → 𝒞_{Z/X'} → 𝒞_{Z/X} → 0` of [Stacks Project, Tag 06BA] is
short exact with finite locally free third term, and `Z` is affine, so it splits; the summand
`𝒞_{Z/X}`, read as a sheaf of ideals inside `𝒪_{Z''}`, cuts out `Z'`.  Everything after the
splitting is
`Stacks.Thickenings.exists_isFirstOrderThickening_isFiniteLocallyFreeOfRank_of_splitting`.

No `@[stacks 06D8]` attribute is attached.  The weakening of `unramified` to formal
unramifiedness would be harmless — it makes this statement imply the tag's — but restricting
`X'` from an algebraic space to a scheme does not: the tag's conclusion is a diagram of
algebraic spaces over `U'`, and this theorem is its special case where the space is a scheme.
The space-level statement is `AlgebraicGeometry.Stack.FiniteHilbert.exists_coverDeformation` of
`StacksFrontier/AlgebraicGeometry/Stacks/FiniteHilbert/CoverDeformationExists.lean`, which carries the
attribute. It does not go through a space-level conormal sequence. It realizes the universal
first-order thickening of `Z` over `X'` as an affine scheme, and runs the argument of this
theorem through one étale chart of `X'`, as
`Stacks.Thickenings.exists_finiteLocallyFreeOfRank_deformation_of_etaleChart`. -/
theorem exists_finiteLocallyFreeOfRank_deformation
    {U U' X X' Z : Scheme.{u}} (iU : U ⟶ U') (hiU : IsFirstOrderThickening iU) [IsAffine U]
    (pX' : X' ⟶ U') [Flat pX'] (iX : X ⟶ X') (pX : X ⟶ U) (hX : IsPullback iX pX pX' iU)
    (pZ : Z ⟶ U) (d : ℕ) (hpZ : Stacks.Morphisms.IsFiniteLocallyFreeOfRank pZ d)
    (fZ : Z ⟶ X) [FormallyUnramified fZ] (hlci : IsLocalCompleteIntersectionMorphism fZ)
    (hfZ : fZ ≫ pX = pZ) :
    ∃ (Z' : Scheme.{u}) (iZ : Z ⟶ Z') (pZ' : Z' ⟶ U') (f' : Z' ⟶ X'),
      IsFirstOrderThickening iZ ∧
      Stacks.Morphisms.IsFiniteLocallyFreeOfRank pZ' d ∧
      IsPullback iZ pZ pZ' iU ∧ iZ ≫ f' = fZ ≫ iX ∧ f' ≫ pX' = pZ' := by
  have := hiU.1
  have hiX : IsFirstOrderThickening iX := isFirstOrderThickening_of_isPullback hX hiU
  have := hiX.1
  have := hpZ
  have : IsAffine Z := AlgebraicGeometry.Space.isAffine_of_isFiniteLocallyFree pZ
    (Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree pZ d) inferInstance
  have : FormallyUnramified (fZ ≫ iX) :=
    MorphismProperty.comp_mem @FormallyUnramified fZ iX inferInstance inferInstance
  obtain ⟨tZ⟩ : Nonempty (UniversalFirstOrderThickening (fZ ≫ iX)) :=
    ⟨universalFirstOrderThickening (fZ ≫ iX)⟩
  let tX := selfUniversalFirstOrderThickening iX hiX
  let tR := relativeThickening fZ iX tZ tX
  let tU := universalFirstOrderThickening fZ
  have hSE := transitivityConormalShortComplex_shortExact fZ iX tZ tX hlci
  have hqc2 : (transitivityConormalShortComplex fZ iX tZ tX).X₂.IsQuasicoherent :=
    inferInstanceAs (Stacks.Conormal.conormalSheaf tZ.inclusion).IsQuasicoherent
  have hqc3 : (transitivityConormalShortComplex fZ iX tZ tX).X₃.IsQuasicoherent :=
    inferInstanceAs (Stacks.Conormal.conormalSheaf (relativeInclusion fZ iX tZ tX)).IsQuasicoherent
  have h06B9 :=
    AlgebraicGeometry.isFiniteLocallyFree_universalConormalSheaf_of_isLocalCompleteIntersection
      fZ hlci
  have hcan : IsIso (UniversalFirstOrderThickening.canonicalMap tR tU) :=
    ⟨UniversalFirstOrderThickening.canonicalMap _ _,
      UniversalFirstOrderThickening.canonicalMap_comp_canonicalMap _ _,
      UniversalFirstOrderThickening.canonicalMap_comp_canonicalMap _ _⟩
  have hsqrel : IsPullback tR.inclusion (𝟙 Z) (UniversalFirstOrderThickening.canonicalMap tR tU)
      tU.inclusion :=
    IsPullback.of_vert_isIso_mono (CommSq.mk (by
      rw [Category.id_comp, UniversalFirstOrderThickening.canonicalMap_inclusion]))
  have e : universalConormalSheaf fZ ≅ (transitivityConormalShortComplex fZ iX tZ tX).X₃ :=
    ((modulePullbackId Z.toLocallyRingedSpace.toRingedSpace).app
        (universalConormalSheaf fZ)).symm ≪≫
      @asIso _ _ _ _ _ (isIso_immersionConormalSheafMap_of_flat tR.inclusion tU.inclusion (𝟙 Z)
        (UniversalFirstOrderThickening.canonicalMap tR tU) hsqrel)
  have hfl3 : SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (transitivityConormalShortComplex fZ iX tZ tX).X₃ :=
    @SheafOfModules.IsFiniteLocallyFree.of_iso Z _ _ e h06B9
  obtain ⟨σ⟩ :=
    @AlgebraicGeometry.Scheme.Modules.nonempty_splitting_of_shortExact_of_isFiniteLocallyFree
      Z inferInstance (transitivityConormalShortComplex fZ iX tZ tX) hSE hqc2 hqc3 hfl3
  obtain ⟨Z', iZ, q, hiZ, hq, hqi, hflZ', hpbZ'⟩ :=
    exists_isFirstOrderThickening_isFiniteLocallyFreeOfRank_of_splitting
      tZ.inclusion tZ.isUniversal.isFirstOrderThickening.2 iX hiX.2 iU hiU.2 fZ
      (transitivityMap fZ iX tZ tX) (inclusion_comp_transitivityMap fZ iX tZ tX).symm
      pX pX' hX d (hfZ ▸ hpZ) hqc3 (transitivityConormalRightMap fZ iX tZ tX)
      (transitivityConormalLeftMap_comp_rightMap fZ iX tZ tX) σ
  refine ⟨Z', iZ, (q ≫ transitivityMap fZ iX tZ tX) ≫ pX', q ≫ transitivityMap fZ iX tZ tX, hiZ,
    hflZ', hfZ ▸ hpbZ', ?_, rfl⟩
  exact (Category.assoc iZ q _).symm.trans
    ((congrArg (· ≫ transitivityMap fZ iX tZ tX) hqi).trans
      (inclusion_comp_transitivityMap fZ iX tZ tX).symm)

end Stacks.Thickenings

end
