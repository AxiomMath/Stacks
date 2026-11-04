module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatRankOpen
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatDirectImagePerfectBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.SingleDegreeRankOpenUniversal
import StacksCore.Tactic.StacksAttribute

/-!
# The locus where the direct image of a proper flat family is locally free in one degree

Let `f : X ⟶ S` be a proper morphism of finite presentation, let `ℱ` be an `𝒪_X`-module of finite
presentation, flat over `S`, and fix `i, r ∈ ℤ`. [Stacks, Tag 0B9S] asserts that there is an open
subscheme `U ⊆ S` such that a morphism `T ⟶ S` factors through `U` if and only if `Rf_{T,*}ℱ_T`
is isomorphic to a finite locally free module of rank `r` placed in degree `i`. Here `X_T` is the
base change of `X` along `T ⟶ S`, `f_T : X_T ⟶ T` its projection and `ℱ_T` the pullback of `ℱ` to
`X_T`.

## Main definitions

* `AlgebraicGeometry.ProperFlatRankOpen.IsFiniteLocallyFreeOfIntRank`: a module is finite locally
  free of rank `r ∈ ℤ` when every point has an open neighbourhood on which it is `𝒪^{⊕ n}` with
  `n : ℕ` equal to `r`. For `r ≥ 0` this is finite local freeness of rank `r`
  (`isFiniteLocallyFreeOfIntRank_natCast_iff`); for `r < 0` it holds exactly on the empty scheme.

## Main results

* `AlgebraicGeometry.ProperFlatRankOpen.factorsThrough_rankOpen_iff_baseChange`: for `r : ℕ`,
  the open subscheme `AlgebraicGeometry.ProperFlatRankOpen.rankOpen f ℱ i r` has the property,
  for every morphism `T ⟶ S` and every cartesian square over it.
* `AlgebraicGeometry.ProperFlatRankOpen.exists_opens_factorsThrough_iff_derivedPushforward`:
  **[Stacks, Tag 0B9S]**, for `i, r ∈ ℤ`.

## Implementation notes

The proof is the source's. By [Stacks, Tag 0B91], clause (2), `K = Rf_*ℱ` is perfect
(`AlgebraicGeometry.ProperFlatDirectImage.isPerfect_derivedPushforwardModule`) and
`Lg^*K ≅ Rf_{T,*}ℱ_T` for every cartesian square
(`AlgebraicGeometry.ProperFlatDirectImage.nonempty_derivedPullback_derivedPushforwardModule_iso`),
so the assertion is description (2) of [Stacks, Tag 0BDK] for `K`
(`factorsThrough_singleDegreeRankOpen_iff_derivedPullback` of the namespace
`AlgebraicGeometry.Scheme.Modules`).
Nothing is assumed beyond the hypotheses of the tag, and `T ⟶ S` is arbitrary.

**The rank is an integer**, as in the source. For `r ≥ 0` the open subscheme is `rankOpen` and the
statement is the one for the natural number `r`. For `r < 0` the open subscheme is `∅`: a
morphism factors through `∅` exactly when its source is empty, and a finite locally free module of
negative rank exists only on the empty scheme, where the direct image is a module of rank `0`
placed in degree `i` by the case `r = 0`.

## References

* [Stacks Project, Tag 0B9S](https://stacks.math.columbia.edu/tag/0B9S)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0BDK](https://stacks.math.columbia.edu/tag/0BDK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProperFlatFibreEulerCharacteristic (derivedPushforwardModule)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.ProperFlatRankOpen

variable {X S : Scheme.{u}}

/-- **The open subscheme `rankOpen f ℱ i r` has the property of [Stacks, Tag 0B9S].** Let
`f : X ⟶ S` be proper of finite presentation and `ℱ` an `𝒪_X`-module of finite presentation, flat
over `S`. For every morphism `g : T ⟶ S` and every cartesian square

```
X_T --g'--> X
 |          |
f_T         f
 v          v
 T  --g---> S
```

`g` factors through `rankOpen f ℱ i r` exactly when `Rf_{T,*}(g')^*ℱ` is isomorphic to a finite
locally free `𝒪_T`-module of rank `r` placed in degree `i`. -/
public theorem factorsThrough_rankOpen_iff_baseChange
    (f : X ⟶ S) (hf : FinitePresentation f) (hproper : IsProper f)
    (F : X.Modules) (hfp : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (i : ℤ) (r : ℕ)
    {T XT : Scheme.{u}} (g : T ⟶ S) (fT : XT ⟶ T) (g' : XT ⟶ X)
    (hsq : IsPullback g' fT f g) :
    (∃ h : T ⟶ (rankOpen f F i r).toScheme, h ≫ (rankOpen f F i r).ι = g) ↔
      ∃ M : T.Modules,
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
          Nonempty (derivedPushforwardModule fT ((Scheme.Modules.pullback g').obj F) ≅
            (DerivedCategory.singleFunctor T.Modules i).obj M) := by
  obtain ⟨e⟩ := ProperFlatDirectImage.nonempty_derivedPullback_derivedPushforwardModule_iso f hf F
    hfp hflat g fT g' hsq
  rw [Scheme.Modules.factorsThrough_singleDegreeRankOpen_iff_derivedPullback
    (derivedPushforwardModule f F) i r
    (ProperFlatDirectImage.isPerfect_derivedPushforwardModule f hf hproper F hfp hflat) g]
  exact exists_congr fun M => and_congr_right fun _ =>
    ⟨fun ⟨w⟩ => ⟨e.symm ≪≫ w⟩, fun ⟨w⟩ => ⟨e ≪≫ w⟩⟩

/-- **[Stacks, Tag 0B9S] for a natural-number rank.** Let `f : X ⟶ S` be a proper morphism of
finite presentation, let `ℱ` be an `𝒪_X`-module of finite presentation, flat over `S`, and fix
`i ∈ ℤ` and `r ∈ ℕ`. Then there
exists an open subscheme `U ⊆ S` with the following property: a morphism `g : T ⟶ S` factors
through `U` if and only if `Rf_{T,*}ℱ_T` is isomorphic to a finite locally free module of rank
`r` placed in degree `i`. Here, for any cartesian square

```
X_T --g'--> X
 |          |
f_T         f
 v          v
 T  --g---> S
```

`ℱ_T = (g')^*ℱ` and `Rf_{T,*}ℱ_T` is the derived direct image of `ℱ_T` placed in degree `0`; the
property holds for every such square.

The open subscheme is `rankOpen f ℱ i r`, and the property is
`factorsThrough_rankOpen_iff_baseChange`. -/
public theorem exists_opens_factorsThrough_iff_derivedPushforward_natRank
    (f : X ⟶ S) (hf : FinitePresentation f) (hproper : IsProper f)
    (F : X.Modules) (hfp : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (i : ℤ) (r : ℕ) :
    ∃ U : S.Opens, ∀ {T XT : Scheme.{u}} (g : T ⟶ S) (fT : XT ⟶ T) (g' : XT ⟶ X),
      IsPullback g' fT f g →
        ((∃ h : T ⟶ U.toScheme, h ≫ U.ι = g) ↔
          ∃ M : T.Modules,
            AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M r ∧
              Nonempty (derivedPushforwardModule fT ((Scheme.Modules.pullback g').obj F) ≅
                (DerivedCategory.singleFunctor T.Modules i).obj M)) :=
  ⟨rankOpen f F i r, fun g fT g' hsq =>
    factorsThrough_rankOpen_iff_baseChange f hf hproper F hfp hflat i r g fT g' hsq⟩

/-! ### The integer rank -/

/-- **A module finite locally free of rank `r ∈ ℤ`**: every point has an open neighbourhood on
which the module is free on `n` generators, for a natural number `n` equal to `r`. This is
`AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFreeOfRank` with the rank read in `ℤ`. -/
@[ega "II 6.5.1" "(I), special case"]
public def IsFiniteLocallyFreeOfIntRank {T : Scheme.{u}} (M : T.Modules) (r : ℤ) : Prop :=
  ∀ t : T, ∃ n : ℕ, (n : ℤ) = r ∧ ∃ (V : T.Opens) (_ : t ∈ V),
    Nonempty (M.restrict V.ι ≅ SheafOfModules.free.{u} (ULift (Fin n)))

/-- For a natural number `n`, finite local freeness of integer rank `n` is finite local freeness of
rank `n`. -/
public theorem isFiniteLocallyFreeOfIntRank_natCast_iff {T : Scheme.{u}} (M : T.Modules)
    (n : ℕ) :
    IsFiniteLocallyFreeOfIntRank M n ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} M n := by
  refine Iff.trans ?_ (Scheme.Modules.isFiniteLocallyFreeOfRank_iff M n)
  refine ⟨fun h t => ?_, fun h t => ?_⟩
  · obtain ⟨m, hm, V, hV, e⟩ := h t
    obtain rfl : m = n := by exact_mod_cast hm
    exact ⟨V, hV, e⟩
  · obtain ⟨V, hV, e⟩ := h t
    exact ⟨n, rfl, V, hV, e⟩

/-- A module finite locally free of negative rank lives on the empty scheme. -/
public theorem isEmpty_of_isFiniteLocallyFreeOfIntRank {T : Scheme.{u}} {M : T.Modules} {r : ℤ}
    (hr : r < 0) (h : IsFiniteLocallyFreeOfIntRank M r) : IsEmpty T :=
  ⟨fun t => by
    obtain ⟨n, hn, -⟩ := h t
    omega⟩

/-- On the empty scheme every module is finite locally free of every rank. -/
public theorem isFiniteLocallyFreeOfIntRank_of_isEmpty {T : Scheme.{u}} [IsEmpty T]
    (M : T.Modules) (r : ℤ) : IsFiniteLocallyFreeOfIntRank M r :=
  fun t => isEmptyElim t

/-- Every morphism from an empty scheme factors through any open subscheme. -/
private theorem exists_factorsThrough_of_isEmpty {T : Scheme.{u}} [IsEmpty T] (U : S.Opens)
    (g : T ⟶ S) : ∃ h : T ⟶ U.toScheme, h ≫ U.ι = g :=
  ⟨IsOpenImmersion.lift U.ι g (by rintro _ ⟨t, -⟩; exact isEmptyElim t),
    IsOpenImmersion.lift_fac _ _ _⟩

/-- A morphism factors through the empty open subscheme exactly when its source is empty. -/
public theorem factorsThrough_bot_iff {T : Scheme.{u}} (g : T ⟶ S) :
    (∃ h : T ⟶ (⊥ : S.Opens).toScheme, h ≫ (⊥ : S.Opens).ι = g) ↔ IsEmpty T := by
  refine ⟨fun ⟨h, _⟩ => ⟨fun t => by simpa using (h.base t).2⟩,
    fun _ => exists_factorsThrough_of_isEmpty _ g⟩

/-- **[Stacks, Tag 0B9S].** Let `f : X ⟶ S` be a proper morphism of finite presentation, let `ℱ`
be an `𝒪_X`-module of finite presentation, flat over `S`, and fix `i, r ∈ ℤ`. Then there exists an
open subscheme `U ⊆ S` with the following property: a morphism `g : T ⟶ S` factors through `U`
if and only if `Rf_{T,*}ℱ_T` is isomorphic to a finite locally free module of rank `r` placed in
degree `i`. Here, for any cartesian square

```
X_T --g'--> X
 |          |
f_T         f
 v          v
 T  --g---> S
```

`ℱ_T = (g')^*ℱ` and `Rf_{T,*}ℱ_T` is the derived direct image of `ℱ_T` placed in degree `0`; the
property holds for every such square.

For `r ≥ 0` the open subscheme is `rankOpen f ℱ i r` and the property is
`factorsThrough_rankOpen_iff_baseChange`. For `r < 0` it is `∅`: both sides say that `T` is
empty, by `factorsThrough_bot_iff` and `isEmpty_of_isFiniteLocallyFreeOfIntRank`, and on an empty
`T` the case of rank `0` supplies the module. -/
@[stacks 0B9S]
public theorem exists_opens_factorsThrough_iff_derivedPushforward
    (f : X ⟶ S) (hf : FinitePresentation f) (hproper : IsProper f)
    (F : X.Modules) (hfp : F.IsFinitePresentation)
    (hflat : IsFlatOver f.toLRSHom.toShHom F) (i r : ℤ) :
    ∃ U : S.Opens, ∀ {T XT : Scheme.{u}} (g : T ⟶ S) (fT : XT ⟶ T) (g' : XT ⟶ X),
      IsPullback g' fT f g →
        ((∃ h : T ⟶ U.toScheme, h ≫ U.ι = g) ↔
          ∃ M : T.Modules, IsFiniteLocallyFreeOfIntRank M r ∧
            Nonempty (derivedPushforwardModule fT ((Scheme.Modules.pullback g').obj F) ≅
              (DerivedCategory.singleFunctor T.Modules i).obj M)) := by
  rcases le_or_gt 0 r with hr | hr
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hr
    refine ⟨rankOpen f F i n, fun g fT g' hsq => ?_⟩
    rw [factorsThrough_rankOpen_iff_baseChange f hf hproper F hfp hflat i n g fT g' hsq]
    exact exists_congr fun M => and_congr_left' (isFiniteLocallyFreeOfIntRank_natCast_iff M n).symm
  · refine ⟨⊥, fun g fT g' hsq => ?_⟩
    rw [factorsThrough_bot_iff]
    refine ⟨fun hT => ?_, fun ⟨_, hM, _⟩ => isEmpty_of_isFiniteLocallyFreeOfIntRank hr hM⟩
    obtain ⟨M, -, he⟩ := (factorsThrough_rankOpen_iff_baseChange f hf hproper F hfp hflat i 0
      g fT g' hsq).1
      (exists_factorsThrough_of_isEmpty _ g)
    exact ⟨M, isFiniteLocallyFreeOfIntRank_of_isEmpty M r, he⟩

end AlgebraicGeometry.ProperFlatRankOpen

end
