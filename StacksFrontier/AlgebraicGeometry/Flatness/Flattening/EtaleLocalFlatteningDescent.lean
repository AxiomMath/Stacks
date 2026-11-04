module

public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.EtaleLocalCentreDivisibility
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFlatnessTransport
import StacksFrontier.AlgebraicGeometry.Picard.HilbertFunctorFpqcSheaf

/-!
# Flattening a module by a blowup, from étale-local flattenings

Let `S` be quasi-compact and quasi-separated, let `f : X ⟶ S` be a morphism of schemes, let `F`
be a quasi-coherent `𝒪_X`-module and let `U ⊆ S` be a quasi-compact open. Suppose given finitely
many commutative squares

```
Xᵢ --jᵢ--> X
|          |
fᵢ         f
v          v
Sᵢ --eᵢ--> S
```

with `eᵢ` quasi-compact étale, with the `jᵢ` étale and jointly surjective, and with a centre
`Iᵢ` on `Sᵢ`, finitely presented and supported away from `eᵢ⁻¹(U)`, such that the strict
transform of `jᵢ^* F` along the blowup of `Sᵢ` in `Iᵢ` is flat over that blowup. Then there is a
centre `I` on `S`, finitely presented and supported away from `U` — so the blowup of `S` in `I`
is a `U`-admissible blowup — such that the strict transform of `F` along it is flat over it.

## Main results

* `AlgebraicGeometry.exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf`:
  **[Stacks, Tag 0814].**

## Implementation notes

The proof is the one of the source, with the reductions of [Stacks, Tag 080Y] removed. Those
reductions serve only to produce, on an affine base, a nonzerodivisor cutting out `S ∖ U`, so
that [Stacks, Tag 0813] applies; the library's form of [Stacks, Tag 0813] has no nonzerodivisor
hypothesis, so the centre can be built directly over a cover of `U` by basic opens. That
construction is
`Stacks.EtaleCentre.exists_global_center_locallyDvd`
(`StacksFrontier/AlgebraicGeometry/Flatness/Flattening/EtaleLocalCentreDivisibility.lean`); it
delivers a centre `I` whose inverse image on each `Sᵢ` is *locally* divisible by `Iᵢ`, which is
all the flatness argument needs, since flatness is checked one point at a time.

Given that centre, flatness of the strict transform of `F` is checked at a point `x` of the base
change `X ×_S Bl_I S`. Choose `i` and a point `y` of `Xᵢ` above the image of `x` in `X`, and a
neighbourhood `W` of the image of `y` in `Sᵢ` on which `I·𝒪 = Iᵢ·𝒪 · K`. Over `W` the given
flatness restricts (`AlgebraicGeometry.isFlatOver_strictTransformSheaf_restrict`), survives the
enlargement of the centre by `K` (`AlgebraicGeometry.isFlatOver_strictTransformSheaf_mul`, which
is [Stacks, Tag 080A] with [Stacks, Tag 080I] and [Stacks, Tag 080F]), and transfers back down to
`x` along the étale `W ⟶ Sᵢ ⟶ S` and the flat `Xᵢ|_W ⟶ Xᵢ ⟶ X`
(`AlgebraicGeometry.exists_isFlatOverAt_strictTransformSheaf_iff_of_etale`, which is
[Stacks, Tag 0805] with [Stacks, Tag 05B9] and [Stacks, Tag 02JZ]).

Condition (1) of the tag has two halves, that the `eᵢ` are quasi-compact étale and that they
cover `S`. The covering half is **not** assumed: nothing in the argument uses it — the centre is
constructed from a cover of `S` by affine opens, not from the `Sᵢ` — so the statement below is
stronger than the tag in that one respect. Condition (2) is used in full: the `jᵢ` have to cover
`X`, since that is how a point of the base change is reached.

## References

* [Stacks Project, Tag 0814](https://stacks.math.columbia.edu/tag/0814)
* [Stacks Project, Tag 0813](https://stacks.math.columbia.edu/tag/0813)
* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
* [Stacks Project, Tag 080F](https://stacks.math.columbia.edu/tag/080F)
* [Stacks Project, Tag 080I](https://stacks.math.columbia.edu/tag/080I)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 05B9](https://stacks.math.columbia.edu/tag/05B9)
* [Stacks Project, Tag 02JZ](https://stacks.math.columbia.edu/tag/02JZ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- In a cartesian square of schemes, a point of the upper-left factor is hit by the fibre
product as soon as its image in the corner agrees with the image of some point of the other
factor. -/
private alias exists_preimage_fst_of_isPullback := Stacks.Hilbert.exists_preimage_of_isPullback

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent. -/
private theorem isQuasicoherent_pullback_obj {X Y : Scheme.{u}} (g : Y ⟶ X) (F : X.Modules)
    [F.IsQuasicoherent] : ((Scheme.Modules.pullback g).obj F).IsQuasicoherent :=
  @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _ g.toLRSHom.toShHom F
    ‹F.IsQuasicoherent›

/-- **Stacks Project, Tag 0814.** Let `S` be a quasi-compact and quasi-separated scheme, let
`f : X ⟶ S` be a morphism of schemes, let `F` be a quasi-coherent `𝒪_X`-module and let `U ⊆ S` be
a quasi-compact open. Assume given finitely many commutative squares `jᵢ ≫ f = fᵢ ≫ eᵢ` with

1. `eᵢ : Sᵢ ⟶ S` quasi-compact and étale,
2. `jᵢ : Xᵢ ⟶ X` étale and jointly surjective,
3. a centre `Iᵢ` on `Sᵢ` which is finitely presented as a closed subscheme and supported away
   from `eᵢ⁻¹(U)` — so the blowup of `Sᵢ` in `Iᵢ` is an `eᵢ⁻¹(U)`-admissible blowup — such that
   the strict transform of `jᵢ^* F` along it is flat over it.

Then there is a centre `I` on `S`, finitely presented and supported away from `U`, exhibiting the
blowup of `S` in `I` as a `U`-admissible blowup, such that the strict transform of `F` along that
blowup is flat over it. -/
@[stacks 0814 "the surjectivity half of condition (1) is not assumed; it is unused"]
theorem exists_isAdmissibleBlowup_isFlatOver_strictTransformSheaf {S X : Scheme.{u}}
    [CompactSpace S] [QuasiSeparatedSpace S] (f : X ⟶ S) (F : X.Modules) [F.IsQuasicoherent]
    (U : S.Opens) (hU : IsCompact (U : Set S)) {ι : Type*} [Finite ι]
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
  obtain ⟨I, hIfp, hIdisj, hIdiv⟩ :=
    Stacks.EtaleCentre.exists_global_center_locallyDvd U hU Sᵢ e Iᵢ he hadm
  refine ⟨I, hIfp, hIdisj, (Stacks.Blowup.isAdmissibleBlowup_iff U (blowUpToBase I)).mpr
    ⟨I, hIfp, hIdisj, Iso.refl _, Category.id_comp _⟩, fun x ↦ ?_⟩
  obtain ⟨i, y, hy⟩ := hcoverX ((pullback.fst f (blowUpToBase I)).base x)
  have _ : Etale (e i) := (he i).1
  have _ : Etale (j i) := hj i
  have hFi := isQuasicoherent_pullback_obj (j i) F
  obtain ⟨W, htW, K, hK⟩ := hIdiv i ((fᵢ i).base y)
  set a : (fᵢ i ⁻¹ᵁ W).toScheme ⟶ Xᵢ i := (fᵢ i ⁻¹ᵁ W).ι with ha
  set fw : (fᵢ i ⁻¹ᵁ W).toScheme ⟶ W.toScheme := fᵢ i ∣_ W with hfw
  set jw : (fᵢ i ⁻¹ᵁ W).toScheme ⟶ X := a ≫ j i with hjw
  set ew : W.toScheme ⟶ S := W.ι ≫ e i with hew
  have hcommW : jw ≫ f = fw ≫ ew := by
    rw [hjw, hew, hfw, Category.assoc, hcomm i, ← Category.assoc, ← morphismRestrict_ι,
      Category.assoc]
  have hFw := isQuasicoherent_pullback_obj jw F
  have hFa := isQuasicoherent_pullback_obj a ((Scheme.Modules.pullback (j i)).obj F)
  have hW := isFlatOver_strictTransformSheaf_restrict (fᵢ i) (Iᵢ i)
    ((Scheme.Modules.pullback (j i)).obj F) W (hflat i)
  have hW' := isFlatOver_strictTransformSheaf_of_iso fw ((Iᵢ i).comap W.ι)
    ((Scheme.Modules.pullbackComp a (j i)).app F) hW
  have hprod := isFlatOver_strictTransformSheaf_mul fw ((Iᵢ i).comap W.ι) K
    ((Scheme.Modules.pullback jw).obj F) hW'
  have hcenter : I.comap ew = (Iᵢ i).comap W.ι * K := by
    simpa only [hew, Scheme.IdealSheafData.comap_comp] using hK
  have hlocal : IsFlatOver (pullback.snd fw (blowUpToBase (I.comap ew))).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf fw (blowUpToBase (I.comap ew))
        (exceptionalIdeal (I.comap ew)) ((Scheme.Modules.pullback jw).obj F)) := by
    rw [hcenter]
    exact hprod
  obtain ⟨k, hk, hiff⟩ :=
    exists_isFlatOverAt_strictTransformSheaf_iff_of_etale f fw ew jw hcommW I F
  obtain ⟨z, hz⟩ := exists_preimage_fst_of_isPullback hk.flip x ⟨y, htW⟩
    (show (pullback.fst f (blowUpToBase I)) x = jw ⟨y, htW⟩ from hy.symm)
  rw [← hz]
  exact (hiff z).mpr (hlocal z)

end AlgebraicGeometry

end
