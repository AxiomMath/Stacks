module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatFibreEulerCharacteristic
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenUniversal
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.Descent.VectorBundleCodimensionOne
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeTFAE

/-!
# The locus where the derived direct image is locally free in one degree (Stacks 0B9S)

Let `π : Y ⟶ T` be proper and of finite presentation and let `ℱ` be an `𝒪_Y`-module of finite
presentation, flat over `T`. For an integer `i` and a natural number `r` this file constructs the
open subscheme `U ⊆ T` of [Stacks, Tag 0B9S]: a morphism `h : T' ⟶ T` factors through `U` exactly
when `Rπ'_*(h'^*ℱ)` is isomorphic to a finite locally free `𝒪_{T'}`-module of rank `r` placed in
degree `i`, where `π' : Y' ⟶ T'` is the base change of `π` along `h`.

The open is `AlgebraicGeometry.Scheme.Modules.singleDegreeRankOpen (Rπ_*ℱ) i r`, the open of
[Stacks, Tag 0BDK] for the perfect object `Rπ_*ℱ` ([Stacks, Tag 0B91]).

## Main definitions

* `HasDerivedPushforwardRank`: the condition that `Rπ_*ℱ` is finite locally free of rank `r`
  placed in degree `i`.

## Main results

* `exists_opens_factorsThrough_iff_of_baseChange`: the open `U ⊆ T` of [Stacks, Tag 0B9S] and its
  universal property, with the two halves of [Stacks, Tag 0B91] — the named propositions
  `PerfectDerivedPushforward` and `BaseChangeDerivedPushforward` — as hypotheses.
* `exists_opens_factorsThrough_iff_invertible_of_baseChange`: the same for an invertible module,
  in degree `0` and rank `1`.

## References

* [Stacks Project, Tag 0B9S](https://stacks.math.columbia.edu/tag/0B9S)
* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)

universe u

namespace AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

attribute [local instance 10000] HasDerivedCategory.standard

/-- `Rπ_*ℱ` is a finite locally free module of rank `r` placed in degree `i`. -/
def HasDerivedPushforwardRank {Y T : Scheme.{u}} (π : Y ⟶ T) (F : Y.Modules) (i : ℤ) (r : ℕ) :
    Prop :=
  ∃ M : T.Modules, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
    Nonempty (derivedPushforwardModule π F ≅ (DerivedCategory.singleFunctor T.Modules i).obj M)

/-- The condition only depends on the isomorphism class of the module. -/
theorem HasDerivedPushforwardRank.of_iso {Y T : Scheme.{u}} {π : Y ⟶ T} {F G : Y.Modules}
    (e : F ≅ G) {i : ℤ} {r : ℕ} (h : HasDerivedPushforwardRank π F i r) :
    HasDerivedPushforwardRank π G i r := by
  obtain ⟨M, hM, ⟨φ⟩⟩ := h
  exact ⟨M, hM, ⟨(derivedPushforward π.toLRSHom.toShHom).mapIso
    ((DerivedCategory.singleFunctor Y.Modules 0).mapIso e.symm) ≪≫ φ⟩⟩

/-- Isomorphic modules satisfy the same rank condition on their derived direct image. -/
theorem hasDerivedPushforwardRank_congr {Y T : Scheme.{u}} {π : Y ⟶ T} {F G : Y.Modules}
    (e : F ≅ G) {i : ℤ} {r : ℕ} :
    HasDerivedPushforwardRank π F i r ↔ HasDerivedPushforwardRank π G i r :=
  ⟨HasDerivedPushforwardRank.of_iso e, HasDerivedPushforwardRank.of_iso e.symm⟩

/-- **[Stacks, Tag 0B9S], given [Stacks, Tag 0B91].** Let `π : Y ⟶ T` be proper and of finite
presentation, `ℱ` an `𝒪_Y`-module of finite presentation flat over `T`, `i` an integer and `r` a
natural number. There is an open `U ⊆ T` such that a morphism `h : T' ⟶ T` factors through `U`
exactly when `Rπ'_*(h'^*ℱ)` is finite locally free of rank `r` in degree `i` for the base change
`π'` of `π` along `h`. -/
theorem exists_opens_factorsThrough_iff_of_baseChange (h0B91 : PerfectDerivedPushforward.{u})
    (hbc : BaseChangeDerivedPushforward.{u}) {Y T : Scheme.{u}} (π : Y ⟶ T)
    (hfp : FinitePresentation π) [IsProper π] (F : Y.Modules) (hF : F.IsFinitePresentation)
    (hflat : IsFlatOver π.toLRSHom.toShHom F) (i : ℤ) (r : ℕ) :
    ∃ U : T.Opens, ∀ {Y' T' : Scheme.{u}} (h : T' ⟶ T) (π' : Y' ⟶ T') (h' : Y' ⟶ Y),
      IsPullback h' π' π h →
      ((∃ g : T' ⟶ U.toScheme, g ≫ U.ι = h) ↔
        HasDerivedPushforwardRank π' ((Scheme.Modules.pullback h').obj F) i r) := by
  have hperf := h0B91 π hfp inferInstance F hF hflat
  refine ⟨Scheme.Modules.singleDegreeRankOpen (derivedPushforwardModule π F) i r,
    fun {Y' T'} h π' h' hpb => ?_⟩
  obtain ⟨e⟩ := hbc π h π' h' hpb hfp inferInstance F hF hflat
  rw [Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff_derivedPullback _ i r hperf h]
  exact ⟨fun ⟨M, hM, ⟨φ⟩⟩ => ⟨M, hM, ⟨e.symm ≪≫ φ⟩⟩,
    fun ⟨M, hM, ⟨φ⟩⟩ => ⟨M, hM, ⟨e ≪≫ φ⟩⟩⟩

/-- An invertible module on a scheme flat over `T` is of finite presentation and flat over `T`. -/
theorem isFinitePresentation_and_isFlatOver_of_isInvertible {Y T : Scheme.{u}} (π : Y ⟶ T)
    [Flat π] (L : Y.Modules)
    (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    L.IsFinitePresentation ∧ IsFlatOver π.toLRSHom.toShHom L := by
  have : L.IsQuasicoherent := Stacks.Picard.isQuasicoherent_of_isInvertible L hL
  have h0 : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L :=
    (Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
      Y.presheaf _ _).mp hL
  have h1 : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    Stacks.ModuleDescent.isFiniteLocallyFreeOfRank_one_of_isInvertible Y L h0
  have hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree L 1
  have hpair : AlgebraicGeometry.SheafOfModules.IsFlat L ∧ L.IsFinitePresentation :=
    ((Stacks.FiniteLocallyFree.ModuleTFAE.finiteLocallyFree_tfae L).out 4 1).mp hflf
  have hfp : L.IsFinitePresentation := hpair.2
  exact ⟨hfp, VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree π L⟩

/-- **[Stacks, Tag 0B9S] for an invertible module, in degree `0` and rank `1`, given
[Stacks, Tag 0B91].** For `π : Y ⟶ T` flat, proper and of finite presentation and `ℒ` invertible
on `Y`, there is an open `U ⊆ T` through which a morphism `h : T' ⟶ T` factors exactly when
`Rπ'_*(h'^*ℒ)` is an invertible module placed in degree `0`. -/
theorem exists_opens_factorsThrough_iff_invertible_of_baseChange
    (h0B91 : PerfectDerivedPushforward.{u}) (hbc : BaseChangeDerivedPushforward.{u})
    {Y T : Scheme.{u}} (π : Y ⟶ T) [Flat π] (hfp : FinitePresentation π) [IsProper π]
    (L : Y.Modules) (hL : Stacks.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2 L) :
    ∃ U : T.Opens, ∀ {Y' T' : Scheme.{u}} (h : T' ⟶ T) (π' : Y' ⟶ T') (h' : Y' ⟶ Y),
      IsPullback h' π' π h →
      ((∃ g : T' ⟶ U.toScheme, g ≫ U.ι = h) ↔
        HasDerivedPushforwardRank π' ((Scheme.Modules.pullback h').obj L) 0 1) :=
  exists_opens_factorsThrough_iff_of_baseChange h0B91 hbc π hfp L
    (isFinitePresentation_and_isFlatOver_of_isInvertible π L hL).1
    (isFinitePresentation_and_isFlatOver_of_isInvertible π L hL).2 0 1

end AlgebraicGeometry.ProperFlatFibreEulerCharacteristic

end
