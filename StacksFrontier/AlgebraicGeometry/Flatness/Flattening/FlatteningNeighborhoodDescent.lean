module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.EtaleLocalFlatteningDescent
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.FlatteningNeighborhood
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeCover

/-!
# Flattening a module by a blowup, from local data at every point

Let `S` be quasi-compact and quasi-separated, let `f : X ⟶ S` be a morphism with `X`
quasi-compact, let `F` be a quasi-coherent `𝒪_X`-module and let `U ⊆ S` be a quasi-compact open.
The étale-local-to-global step [Stacks, Tag 0814]
(`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf`) consumes a
*finite* family of étale squares over which the strict transform of the pullback of `F` is
already flat. The induction of [Stacks, Tag 0815] produces such a square at every point of `X`
instead, so what is needed between them is a finiteness reduction. That is what this file
provides, in three successively more convenient forms:

* from an arbitrary family of étale squares whose source legs cover `X`;
* from an open neighbourhood of each point of the base carrying a centre;
* from an `AlgebraicGeometry.FlatteningNeighborhood` at each point of the source.

## Main results

All three live in the `AlgebraicGeometry` namespace and have the same conclusion, the flatness
assertion of [Stacks, Tag 0815] for `F`, `f` and `U`; they differ in the local data assumed.

* `exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_etaleCover`: the index type of
  the family of étale squares need not be finite.
* `exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_baseOpens`: the squares may be
  taken to be the restrictions of `f` over a family of quasi-compact opens covering `S`.
* `exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_flatteningNeighborhoods`: a
  flattening neighbourhood at every point of `X` suffices.

## Implementation notes

The reduction is a single application of compactness of `X`: an étale morphism is open
([Stacks, Tag 03WT], `AlgebraicGeometry.Scheme.Hom.isOpenMap`), so the ranges of the source legs
form an open cover of `X`, and finitely many of them already cover it. The subfamily indexed by
that finite set is what [Stacks, Tag 0814] is applied to.

Compactness of `S` is *not* used for a second finiteness reduction, and no family is required to
cover `S`: the library's form of [Stacks, Tag 0814] drops the surjectivity half of its condition
(1), so only the cover of `X` has to be made finite. The hypothesis `[CompactSpace S]` below is
the one [Stacks, Tag 0814] itself carries. This is why the last statement below can index its
family of squares by the points of `X` directly, rather than having to adjoin the identity of `S`
to the family in order to cover the base.

The three statements are stated in the vocabulary of
`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/FlatteningNeighborhood.lean`: the strict
transform is `Stacks.StrictTransform.sheaf` at `b = AlgebraicGeometry.blowUpToBase` and
`E = AlgebraicGeometry.exceptionalIdeal`, and finite presentation of a centre is
`AlgebraicGeometry.FinitePresentation` of its closed immersion, the conjunctive predicate of
[Stacks, Tag 01TP] that `Stacks.Blowup.IsAdmissibleBlowup` also uses.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 0814](https://stacks.math.columbia.edu/tag/0814)
* [Stacks Project, Tag 03WT](https://stacks.math.columbia.edu/tag/03WT)
* [Stacks Project, Tag 01TP](https://stacks.math.columbia.edu/tag/01TP)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **The index type of the family of étale squares in [Stacks, Tag 0814] need not be finite**
when `X` is quasi-compact. Let `S` be a quasi-compact and quasi-separated scheme, let `f : X ⟶ S`
be a morphism with `X` quasi-compact, let `F` be a quasi-coherent `𝒪_X`-module and let `U ⊆ S` be
a quasi-compact open. Assume given commutative squares `jᵢ ≫ f = fᵢ ≫ eᵢ`, indexed by an
arbitrary type, with `eᵢ : Sᵢ ⟶ S` quasi-compact and étale, with `jᵢ : Xᵢ ⟶ X` étale and jointly
surjective, and with a centre `Iᵢ` on `Sᵢ` which is finitely presented as a closed subscheme and
supported away from `eᵢ⁻¹(U)`, such that the strict transform of `jᵢ^* F` along the blowup of `Sᵢ`
in `Iᵢ` is flat over it. Then there is a centre `I` on `S`, finitely presented and supported away
from `U`, exhibiting the blowup of `S` in `I` as a `U`-admissible blowup, such that the strict
transform of `F` along that blowup is flat over it.

An étale morphism is open, so the ranges of the `jᵢ` form an open cover of the quasi-compact `X`;
finitely many of them cover it, and the subfamily they index is handed to
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf`. -/
theorem exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_etaleCover
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X] (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] (U : S.Opens) (hU : IsCompact (U : Set S)) {ι : Type*}
    (Sᵢ Xᵢ : ι → Scheme.{u}) (e : ∀ i, Sᵢ i ⟶ S) (j : ∀ i, Xᵢ i ⟶ X)
    (fᵢ : ∀ i, Xᵢ i ⟶ Sᵢ i) (Iᵢ : ∀ i, (Sᵢ i).IdealSheafData)
    (he : ∀ i, Etale (e i) ∧ QuasiCompact (e i)) (hj : ∀ i, Etale (j i))
    (hcoverX : ∀ x : X, ∃ i : ι, ∃ y : Xᵢ i, (j i).base y = x)
    (hcomm : ∀ i, j i ≫ f = fᵢ i ≫ e i)
    (hadm : ∀ i, FinitePresentation (Iᵢ i).subschemeι ∧
      Disjoint (e i ⁻¹ᵁ U : Set (Sᵢ i)) ((Iᵢ i).support : Set (Sᵢ i)))
    (hflat : ∀ i, IsFlatOver
      (pullback.snd (fᵢ i) (blowUpToBase (Iᵢ i))).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf (fᵢ i) (blowUpToBase (Iᵢ i)) (exceptionalIdeal (Iᵢ i))
        ((Scheme.Modules.pullback (j i)).obj F))) :
    ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
      Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
      IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) := by
  classical
  have hjinst (i : ι) : Etale (j i) := hj i
  obtain ⟨c, hc⟩ := isCompact_univ.elim_finite_subcover
    (fun i : ι ↦ Set.range (j i).base) (fun i ↦ (j i).isOpenMap.isOpen_range)
    fun x _ ↦ by
      obtain ⟨i, y, hy⟩ := hcoverX x
      exact Set.mem_iUnion.mpr ⟨i, y, hy⟩
  refine exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf f F U hU
    (ι := {i : ι // i ∈ c}) (fun i ↦ Sᵢ i.1) (fun i ↦ Xᵢ i.1) (fun i ↦ e i.1) (fun i ↦ j i.1)
    (fun i ↦ fᵢ i.1) (fun i ↦ Iᵢ i.1) (fun i ↦ he i.1) (fun i ↦ hj i.1) ?_
    (fun i ↦ hcomm i.1) (fun i ↦ hadm i.1) fun i ↦ hflat i.1
  intro x
  obtain ⟨i, hi, y, hy⟩ := Set.mem_iUnion₂.mp (hc (Set.mem_univ x))
  exact ⟨⟨i, hi⟩, y, hy⟩

/-- **A centre over an open neighbourhood of each point of the base suffices.** Let `S` be a
quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be a morphism with `X` quasi-compact,
let `F` be a quasi-coherent `𝒪_X`-module and let `U ⊆ S` be a quasi-compact open. Assume that
every point of `S` has a quasi-compact open neighbourhood `W` carrying a centre `I`, finitely
presented as a closed subscheme and supported away from `W ∩ U`, such that the strict transform
of `F|_{f⁻¹(W)}` along the blowup of `W` in `I` is flat over it. Then there is a centre `I` on
`S`, finitely presented and supported away from `U`, exhibiting the blowup of `S` in `I` as a
`U`-admissible blowup, such that the strict transform of `F` along that blowup is flat over it.

The inclusion of a quasi-compact open of a quasi-separated scheme is étale and quasi-compact, and
the inclusions of the preimages `f⁻¹(W)` cover `X` because the `W` cover `S`; the restrictions
`f ∣_ W` complete the squares that
`AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_etaleCover`
descends along. -/
theorem exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_baseOpens
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X] (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] (U : S.Opens) (hU : IsCompact (U : Set S))
    (hlocal : ∀ s : S, ∃ W : S.Opens, s ∈ W ∧ IsCompact (W : Set S) ∧
      ∃ I : W.toScheme.IdealSheafData,
        FinitePresentation I.subschemeι ∧
        Disjoint (W.ι ⁻¹ᵁ U : Set W.toScheme) (I.support : Set W.toScheme) ∧
        IsFlatOver (pullback.snd (f ∣_ W) (blowUpToBase I)).toLRSHom.toShHom
          (Stacks.StrictTransform.sheaf (f ∣_ W) (blowUpToBase I) (exceptionalIdeal I)
            ((Scheme.Modules.pullback (f ⁻¹ᵁ W).ι).obj F))) :
    ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
      Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
      IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) := by
  classical
  choose W hsW hWc I hIfp hIdisj hIflat using hlocal
  exact exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_etaleCover f F U hU
    (fun s : S ↦ (W s).toScheme) (fun s : S ↦ (f ⁻¹ᵁ W s).toScheme) (fun s ↦ (W s).ι)
    (fun s ↦ (f ⁻¹ᵁ W s).ι) (fun s ↦ f ∣_ W s) I
    (fun s ↦ ⟨inferInstance, quasiCompact_ι_of_isCompact (W s) (hWc s)⟩)
    (fun _ ↦ inferInstance) (fun x ↦ ⟨f.base x, ⟨x, hsW (f.base x)⟩, rfl⟩)
    (fun s ↦ (morphismRestrict_ι f (W s)).symm) (fun s ↦ ⟨hIfp s, hIdisj s⟩) hIflat

/-- **A flattening neighbourhood at every point of the source suffices.** Let `S` be a
quasi-compact and quasi-separated scheme, let `f : X ⟶ S` be a morphism with `X` quasi-compact,
let `F` be a quasi-coherent `𝒪_X`-module and let `U ⊆ S` be a quasi-compact open. If every point
of `X` admits an `AlgebraicGeometry.FlatteningNeighborhood` of `f`, `F` and `U`, then there is a
centre `I` on `S`, finitely presented and supported away from `U`, exhibiting the blowup of `S`
in `I` as a `U`-admissible blowup, such that the strict transform of `F` along that blowup is
flat over it.

This is the shape in which the induction of [Stacks, Tag 0815] feeds its local output into the
étale-local-to-global step: the family of étale squares is indexed by the points of `X`, each
square being the one recorded in the flattening neighbourhood at that point, and the
distinguished points witness that the source legs cover `X`. -/
theorem exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_flatteningNeighborhoods
    {S X : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [CompactSpace X] (f : X ⟶ S)
    (F : X.Modules) [F.IsQuasicoherent] (U : S.Opens) (hU : IsCompact (U : Set S))
    (hlocal : ∀ x : X, Nonempty (FlatteningNeighborhood f F U x)) :
    ∃ I : S.IdealSheafData,
      FinitePresentation I.subschemeι ∧
      Disjoint (U : Set S) (I.support : Set S) ∧
      Stacks.Blowup.IsAdmissibleBlowup U (blowUpToBase I) ∧
      IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) F) := by
  classical
  let D (x : X) := (hlocal x).some
  exact exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf_of_etaleCover f F U hU
    (fun x : X ↦ (D x).base) (fun x : X ↦ (D x).source) (fun x ↦ (D x).toBase)
    (fun x ↦ (D x).toSource) (fun x ↦ (D x).map) (fun x ↦ (D x).center)
    (fun x ↦ ⟨(D x).etale_base, (D x).quasiCompact_base⟩) (fun x ↦ (D x).etale_source)
    (fun x ↦ ⟨x, (D x).point, (D x).point_eq⟩) (fun x ↦ (D x).commutes)
    (fun x ↦ (D x).admissible) fun x ↦ (D x).flat

end AlgebraicGeometry

end
