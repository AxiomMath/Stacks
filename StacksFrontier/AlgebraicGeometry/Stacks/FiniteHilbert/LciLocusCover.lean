module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciHilbertFormallySmooth
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusAlgebraic
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciLocusSurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LciQuintupleOverField
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Stacks.FormallySmoothAtlas

/-!
# The loci `ℋ_{d,lci}(𝒳/𝒴)` as a cover of `𝒴`

Let `F : 𝒳 ⟶ 𝒴` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`
with `𝒳` representable by an algebraic space and `F` representable by algebraic spaces,
surjective, flat and locally of finite presentation. The proof of **Stacks 06DC** covers `𝒴` by
the family of 1-morphisms `ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴`, `d ≥ 1`. This file collects what that proof
reads off the family, apart from formal smoothness on objects, which is **Stacks 06D9**:

* every locus has a scheme atlas which is formally smooth on objects
  (`AlgebraicGeometry.Stack.hasFormallySmoothAtlas_lciFiniteHilbertFibered`);
* every member is limit preserving on objects
  (`AlgebraicGeometry.Stack.isLimitPreservingOnObjects_lciFiniteHilbertToTargetFibered`), which
  is **Stacks 06CH** combined with **Stacks 06CL**, **Stacks 06CY** and **Stacks 06CW**, as in
  item (1) of the source's proof;
* the family is jointly surjective on objects
  (`AlgebraicGeometry.Stack.isJointlySurjectiveOnObjects_lciFiniteHilbertToTarget`), which is
  **Stacks 06DA** read one degree at a time.

## Implementation notes

The source applies Stacks 04AM to the atlas of `∐_d ℋ_{d,lci}(𝒳/𝒴)` to see that it is formally
smooth. That direction of Stacks 04AM is not available here for morphisms of algebraic spaces
which are not representable, so the atlas is instead built to be formally smooth on objects:
following the construction of the algebraic structure of `ℋ_{d,lci}(𝒳/𝒴)` — the universal atlas
of `ℋ_d` (Stacks 05YQ), base changed along `ℋ_d(𝒳) ⟶ ℋ_d` (Stacks 05YS), along
`ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` (the square of Stacks 06CI) and along the open immersion of Stacks 06CL —
with `AlgebraicGeometry.Stack.HasFormallySmoothAtlas` carried at every step.

## References

* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
* [Stacks Project, Tag 05YS](https://stacks.math.columbia.edu/tag/05YS)
* [Stacks Project, Tag 06CH](https://stacks.math.columbia.edu/tag/06CH)
* [Stacks Project, Tag 06CI](https://stacks.math.columbia.edu/tag/06CI)
* [Stacks Project, Tag 06CL](https://stacks.math.columbia.edu/tag/06CL)
* [Stacks Project, Tag 06DA](https://stacks.math.columbia.edu/tag/06DA)
* [Stacks Project, Tag 06DC](https://stacks.math.columbia.edu/tag/06DC)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry.Stack

/-- The category `ℋ_d` of degree-`d` finite locally free covers has a formally smooth atlas: the
universal atlas out of the scheme of structure constants, which is limit preserving, formally
smooth and surjective on objects. -/
theorem hasFormallySmoothAtlas_finiteCoverFibered (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (d : ℕ) [NeZero d] :
    HasFormallySmoothAtlas B S hS (finiteCoverFibered B S hS d) :=
  hasFormallySmoothAtlas_of_onObjects_schemePoint B S hS
    (hasRepresentableDiagonal_finiteCoverFibered B S hS d) _ (finiteCoverUniversalAtlas B S hS d)
    (isLimitPreservingOnObjects_finiteCoverUniversalAtlas B S hS d)
    (isFormallySmoothOnObjects_finiteCoverUniversalAtlas B S hS d)
    (isSurjectiveOnObjects_finiteCoverUniversalAtlas B S hS d)

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳 𝒴 : StackInGroupoids.{w, u, u, u + 1, u + 1} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}

/-- The finite Hilbert stack `ℋ_d(𝒳)` of an algebraic space has a formally smooth atlas: the
forgetful 1-morphism to `ℋ_d` is representable by algebraic spaces (Stacks 05YF). -/
theorem hasFormallySmoothAtlas_absoluteHilbertFibered [NeZero d]
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS (targetCFG (𝒴 := 𝒳))) :
    HasFormallySmoothAtlas B S hS (absoluteHilbertFibered 𝒳 d) :=
  hasFormallySmoothAtlas_of_isRepresentableByAlgebraicSpaces B S hS
    (forgetAbsoluteStructureFibered 𝒳 d)
    (isRepresentableByAlgebraicSpaces_forgetAbsoluteStructure_of_space 𝒳 d h𝒳)
    (hasFormallySmoothAtlas_finiteCoverFibered B S hS d)

/-- The relative finite Hilbert stack `ℋ_d(𝒳/𝒴)` has a formally smooth atlas, for positive `d`:
the formally smooth atlas of `ℋ_d(𝒳)` base changes along `ℋ_d(𝒳/𝒴) ⟶ ℋ_d(𝒳)` to the square of
the proof of Stacks 06CI, whose apex is representable by an algebraic space. -/
theorem hasFormallySmoothAtlas_finiteHilbertFibered (hd : 0 < d)
    (h𝒴 : Functor.IsStack 𝒴.toBasedCategory.p (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS (targetCFG (𝒴 := 𝒳)))
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F)) :
    HasFormallySmoothAtlas B S hS (finiteHilbertFibered B S hS d 𝒳 𝒴 F) := by
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨U, g, hg, hgsurj, hgsmooth, hgfs⟩ :=
    hasFormallySmoothAtlas_absoluteHilbertFibered (d := d) h𝒳
  obtain ⟨-, ⟨hHd, -⟩, -⟩ := isAlgebraicStack_absoluteHilbertFibered.{u, w} B S hS d 𝒳 h𝒳
  have hℋ := isStack_finiteHilbertCategory hHd h𝒴
    (isRepresentableByAlgebraicSpacesForgetToProduct_of_flatPresentation h𝒴 h𝒳 hF hFprops)
  exact hasFormallySmoothAtlas_of_isTwoFibreProduct B S hS g
    (forgetRelativeStructureFibered (B := B) (S := S) (hS := hS) (d := d) (𝒳 := 𝒳) (𝒴 := 𝒴)
      (F := F)) hg hgsurj hgsmooth hgfs (hilbertAtlasSquare g)
    (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, u, u + 1, u + 1} _ g)
    (isRepresentableByAlgebraicSpace_hilbertAtlasSquare hd h𝒴 h𝒳 hF hFprops
      hHd hℋ
      (isRepresentableByAlgebraicSpace_schemeFibredCategory B S hS U) g hg hgsurj hgsmooth)

/-- The inclusion `ℋ_{d,lci}(𝒳/𝒴) ⟶ ℋ_d(𝒳/𝒴)` is representable by algebraic spaces under the
flat presentation hypotheses on `F` (Stacks 06CL). -/
private theorem isRepresentableByAlgebraicSpaces_lciInclusion_of_flatPresentation
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F)) :
    IsRepresentableByAlgebraicSpaces B S hS
      (lciFiniteHilbertInclusion (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)) :=
  isRepresentableByAlgebraicSpaces_lciFiniteHilbertInclusion_of_flat hF
    (fun U y hy P hP he => (hFprops U y hy P hP he).2.1)
    (fun U y hy P hP he => (hFprops U y hy P hP he).2.2)

/-- **The local complete intersection locus `ℋ_{d,lci}(𝒳/𝒴)` has a formally smooth atlas**, for
positive `d`: its inclusion into `ℋ_d(𝒳/𝒴)` is representable by algebraic spaces (Stacks 06CL).
This is the atlas the proof of Stacks 06DC composes with `ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴`. -/
theorem hasFormallySmoothAtlas_lciFiniteHilbertFibered (hd : 0 < d)
    (h𝒴 : Functor.IsStack 𝒴.toBasedCategory.p (BigFppfOver.topology B S hS))
    (h𝒳 : IsRepresentableByAlgebraicSpace B S hS (targetCFG (𝒴 := 𝒳)))
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F))
    (h : (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p.IsFiberedInGroupoids) :
    HasFormallySmoothAtlas B S hS (lciFiniteHilbertFibered h) :=
  hasFormallySmoothAtlas_of_isRepresentableByAlgebraicSpaces B S hS
    (lciFiniteHilbertInclusionFibered h)
    (isRepresentableByAlgebraicSpaces_lciInclusion_of_flatPresentation hF hFprops)
    (hasFormallySmoothAtlas_finiteHilbertFibered hd h𝒴 h𝒳 hF hFprops)

open FiniteHilbert in
/-- **The 1-morphism `ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴` is limit preserving on objects.** It is the open
immersion of Stacks 06CL, limit preserving on objects by Stacks 06CY, followed by
`ℋ_d(𝒳/𝒴) ⟶ 𝒴`, limit preserving on objects by Stacks 06CH; Stacks 06CW composes them. This is
item (1) of the proof of Stacks 06DC. -/
theorem isLimitPreservingOnObjects_lciFiniteHilbertToTargetFibered
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F))
    (h : (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p.IsFiberedInGroupoids) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS (lciFiniteHilbertFibered h)
      (targetCFG (𝒴 := 𝒴)) (lciFiniteHilbertToTargetFibered h) := by
  have hflat := fun U y hy P hP he => (hFprops U y hy P hP he).2.1
  have hlfp := fun U y hy P hP he => (hFprops U y hy P hP he).2.2
  have h06CH : BigFppfOver.IsLimitPreservingOnObjects.{u, u, u} B S hS
      (finiteHilbertFibered B S hS d 𝒳 𝒴 F) (stackFibered B S hS 𝒴)
      (forgetTargetFibered B S hS d 𝒳 𝒴 F) :=
    isLimitPreservingOnObjects_finiteHilbertToTargetCFG.{u, u, u, w} B S hS 𝒳 𝒴 F d hF hlfp
  exact BigFppfOver.isLimitPreservingOnObjects_comp B S hS _ _ _
    (lciFiniteHilbertInclusionFibered h) (forgetTargetFibered B S hS d 𝒳 𝒴 F)
    (isLimitPreservingOnObjects_of_isOpenImmersion B S hS (lciFiniteHilbertInclusionFibered h)
      (isRepresentableByAlgebraicSpaces_lciInclusion_of_flatPresentation hF hFprops)
      (isOpenImmersion_lciFiniteHilbertInclusion_of_flat hF hflat hlfp)) h06CH

/-- **The loci `ℋ_{d,lci}(𝒳/𝒴) ⟶ 𝒴`, `d ≥ 1`, are jointly surjective on objects.** This is
**Stacks 06DA** read one degree at a time: an object of `𝒴` over the spectrum of a field is the
object of `𝒴` of an object of the locus of *some* positive degree over that same spectrum
(`AlgebraicGeometry.Stack.FiniteHilbert.exists_lciLocus_object_of_isFieldObject`), so no field
extension is needed. -/
theorem isJointlySurjectiveOnObjects_lciFiniteHilbertToTarget
    (hF : IsRepresentableByAlgebraicSpaces B S hS F)
    (hFprops : RelativeFlatPresentation (F := F)) :
    IsJointlySurjectiveOnObjects B S hS
      (fun d : {n : ℕ // 0 < n} => (lciFiniteHilbertCategory (B := B) (S := S) (hS := hS)
        (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d.1)).p)
      𝒴.toBasedCategory.p
      (fun d => (lciFiniteHilbertToTarget (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴)
        (F := F) (d := d.1)).toFunctor) := by
  intro U hU y hy
  obtain ⟨d, hd, P, hP, hPy⟩ := FiniteHilbert.exists_lciLocus_object_of_isFieldObject hF
    (fun V y hy G hG he => (hFprops V y hy G hG he).1)
    (fun V y hy G hG he => (hFprops V y hy G hG he).2.2) U hU y hy
  subst hPy
  exact ⟨⟨d, hd⟩, U, hU, 𝟙 U, ⟨P, hP⟩, P.y_over.symm.trans hy, 𝟙 P.y, IsHomLift.id hy⟩

end AlgebraicGeometry.Stack

end
