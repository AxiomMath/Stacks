module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.SplittingTowerRecovery
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.PositiveRankSurjectivity
public import StacksFrontier.AlgebraicGeometry.Chow.AffineBundle.ZeroSectionProjectionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.BaseChange

/-!
# Injectivity of flat pullback along a tower of projective bundles, after any base change

Let `(S, δ)` be as in Situation 02QL, `X` locally of finite type over `S` and `π : P ⟶ X` a finite
composition of projective space bundles `𝐏(ℰ) ⟶ X` of finite locally free modules of constant
rank (`Stacks.Chow.IsProjectiveBundleTower`). For every morphism `f : Y ⟶ X` with `Y` locally of
finite type over `S`, the base change `π_Y : Y ×_X P ⟶ Y` has injective flat pullback
`π_Y^* : CH_k(Y) ⟶ CH_{k+d}(Y ×_X P)` in every degree. This is clause (1) of Stacks 02UL.

The proof is the one the source indicates: the base change of the projective bundle of `ℰ` along
`f` is the projective bundle of `f^*ℰ` (Stacks 01O3,
`AlgebraicGeometry.projectiveBundleBaseChangeComparison`), along whose projection flat pullback
is injective by the projective bundle formula (Stacks 02TX,
`Stacks.Chow.BundleStep.injective_pullbackChow`); the base change of the rest of the tower is a
base change along the base-changed bundle, so an induction on the tower and Stacks 02RD
(`Stacks.Chow.flatPullbackChow_comp`) conclude.

## Main results

* `Stacks.Chow.flatPullbackChow_injective_of_isIso` — flat pullback along an isomorphism is
  injective.
* `Stacks.Chow.IsProjectiveBundleTower.injective_flatPullbackChow_of_isPullback` — injectivity of
  flat pullback along every base change of a tower of projective bundles.
* `Stacks.Chow.IsProjectiveBundleTower.injective_flatPullbackChow_pullbackFst` — the same, for
  the chosen fibre product `Y ×_X P`.

## References

* [Stacks Project, Tag 02UL](https://stacks.math.columbia.edu/tag/02UL)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 01O3](https://stacks.math.columbia.edu/tag/01O3)
* [Stacks Project, Tag 02RD](https://stacks.math.columbia.edu/tag/02RD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### Injectivity of flat pullback along isomorphisms and composites -/

/-- **Flat pullback along an isomorphism is injective.** Up to the transport `A_k = A_{k+0}` of
degrees it is proper pushforward along the inverse isomorphism, which has a left inverse. -/
theorem flatPullbackChow_injective_of_isIso (C : ChowSituation.{u}) {A B : Scheme.{u}}
    (sA : A ⟶ C.S) [LocallyOfFiniteType sA] (sB : B ⟶ C.S) [LocallyOfFiniteType sB]
    (f : A ⟶ B) [IsIso f] [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sB = sA)
    (hdim : AlgebraicGeometry.RelativeDimension f 0) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sB f hf 0 hdim k) :
    Function.Injective (flatPullbackChow C sA sB f hf 0 hdim k hfac) := by
  have hg : inv f ≫ sA = sB := by rw [IsIso.inv_comp_eq, hf]
  have key : ∀ α, flatPullbackChow C sA sB f hf 0 hdim k hfac α =
      chowGroupCast C sA (show k = k + ((0 : ℕ) : ℤ) from by simp)
        (chowPushforwardOfIso C sB sA (inv f) hg k α) :=
    fun α ↦ flatPullbackChowOfRelativeDimension_of_isIso C sA sB f hf hdim (inv f)
      (IsIso.inv_hom_id f) hg k α
  intro x y h
  rw [key, key] at h
  rw [← chowPushforwardOfIso_inv_comp C sB sA (inv f) hg k x,
    ← chowPushforwardOfIso_inv_comp C sB sA (inv f) hg k y, (chowGroupCast C sA _).injective h]

/-! ### Clause (1) of Stacks 02UL after an arbitrary base change -/

/-- Relative dimension `d` passes to the first projection of a fibre product. -/
private theorem relativeDimension_pullback_fst {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
    [LocallyOfFiniteType g] {d : ℕ} (hg : AlgebraicGeometry.RelativeDimension g d) :
    AlgebraicGeometry.RelativeDimension (pullback.fst f g) d :=
  AlgebraicGeometry.RelativeDimension.of_isPullback (IsPullback.of_hasPullback f g).flip hg

/-- Flat pullback along the base change `Y ×_X 𝐏(ℰ) ⟶ Y` of a projective bundle is injective. -/
private theorem injective_flatPullbackChow_pullbackFst_projectiveBundleStep
    (C : ChowSituation.{u}) {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
    (E : X.Modules) (m : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (m + 1 + 1))
    {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : Y ⟶ X) (j : ℤ) :
    Function.Injective (flatPullbackChow C
      (pullback.fst f (projectiveBundleStep C sX E m hE).π ≫ sY) sY
      (pullback.fst f (projectiveBundleStep C sX E m hE).π) rfl (m + 1)
      (relativeDimension_pullback_fst f _ (projectiveBundleStep C sX E m hE).relDim) j
      (flatPullbackFactorsThroughRationalEquivalence_general C _ sY _ rfl _ _ j)) := by
  let D := projectiveBundleStep C sX E m hE
  -- the layer over `Y`: the projective bundle of `f^*ℰ`
  have hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) (m + 1 + 1) :=
    @AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback _ _ f E (m + 1 + 1) hE
  let D' := projectiveBundleStep C sY ((Scheme.Modules.pullback f).obj E) m hE'
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree E
      (m + 1 + 1)
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree _
      (m + 1 + 1)
  have : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  have : ((Scheme.Modules.pullback f).obj E).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree _
  obtain ⟨e₀, he₀⟩ := projectiveBundleBaseChangeComparison f E (bundlePieces E)
    ((Scheme.Modules.pullback f).obj E) (bundlePieces _) (Iso.refl _)
  -- the base change of the bottom layer
  let a : pullback f D.π ⟶ Y := pullback.fst f D.π
  let e : D'.P ≅ pullback f D.π := e₀
  have he : e.hom ≫ a = D'.π := he₀
  have : IsOpenImmersion e.inv := IsOpenImmersion.of_isIso e.inv
  have hrela := relativeDimension_pullback_fst f D.π D.relDim
  have he' : e.inv ≫ D'.π = a := e.inv_comp_eq.2 he.symm
  have hebase : e.inv ≫ D'.sP = a ≫ sY := by
    rw [← he', Category.assoc]
    rfl
  exact flatPullbackChow_injective_of_comp_eq C (a ≫ sY) D'.sP sY e.inv D'.π a he'
    hebase D'.hsP rfl 0 (m + 1) (m + 1) (Nat.zero_add _).symm
    (relativeDimension_of_isIso e.inv) D'.relDim hrela j
    (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _) (D'.hfac j) _
    (flatPullbackChow_injective_of_isIso C (a ≫ sY) D'.sP e.inv hebase
      (relativeDimension_of_isIso e.inv) _ _)
    (D'.injective_pullbackChow j)

/-- **Flat pullback along any base change of a tower of projective bundles is injective.** Let
`T : P ⟶ X` be a tower of projective bundles of relative dimension `d`, let `f : Y ⟶ X` be a
morphism with `Y` locally of finite type over the base, and let `π' : Y' ⟶ Y` be a base change of
`T.π` along `f`. Then `π'^* : A_k(Y) ⟶ A_{k+d}(Y')` is injective for every `k`. The structure
morphism `Y ⟶ S` is arbitrary: it need not factor through `X`.

Induction on the tower. For the identity, `π'` is an isomorphism. For a tower `T' ≫ 𝐏(ℰ) ⟶ X`,
the base change of `𝐏(ℰ) ⟶ X` along `f` is isomorphic over `Y` to `𝐏(f^*ℰ) ⟶ Y` (Stacks 01O3),
whose flat pullback is injective by Stacks 02TX; and `π'` factors through `Y ×_X 𝐏(ℰ)` by a base
change of `T'`, to which the inductive hypothesis applies. -/
theorem IsProjectiveBundleTower.injective_flatPullbackChow_of_isPullback
    {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {d : ℕ}
    {T : SplittingMorphism C sX d} (hT : IsProjectiveBundleTower C sX d T) :
    ∀ {Y : Scheme.{u}} (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : Y ⟶ X)
      {Y' : Scheme.{u}} (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY'] (π' : Y' ⟶ Y)
      [LocallyOfFiniteType π'] [Flat π'] (hπ' : π' ≫ sY = sY') (q : Y' ⟶ T.P)
      (_ : IsPullback q π' T.π f) (hrel : AlgebraicGeometry.RelativeDimension π' d) (k : ℤ)
      (hfac : FlatPullbackFactorsThroughRationalEquivalence C sY' sY π' hπ' d hrel k),
      Function.Injective (flatPullbackChow C sY' sY π' hπ' d hrel k hfac) := by
  induction hT with
  | id sX =>
    intro Y sY _ f Y' sY' _ π' _ _ hπ' q sq hrel k hfac
    have : IsIso (SplittingMorphism.id C sX).π := inferInstanceAs (IsIso (𝟙 _))
    have : IsIso π' := sq.isIso_snd_of_isIso
    exact flatPullbackChow_injective_of_isIso C sY' sY π' hπ' hrel k hfac
  | compStep sX E m hE n T _ ih =>
    intro Y sY _ f Y' sY' _ π' _ _ hπ' q sq hrel k hfac
    let D := projectiveBundleStep C sX E m hE
    -- the base change of the bottom layer
    let a : pullback f D.π ⟶ Y := pullback.fst f D.π
    let b : pullback f D.π ⟶ D.P := pullback.snd f D.π
    have hab : IsPullback b a D.π f := (IsPullback.of_hasPullback f D.π).flip
    have hrela := relativeDimension_pullback_fst f D.π D.relDim
    -- the factorization of `π'` through the base change of the bottom layer
    let q' : Y' ⟶ T.P := q
    have sq₀ : IsPullback q' π' (T.π ≫ D.π) f := sq
    have hw : π' ≫ f = (q' ≫ T.π) ≫ D.π := sq₀.w.symm.trans (Category.assoc _ _ _).symm
    let h : Y' ⟶ pullback f D.π := pullback.lift π' (q' ≫ T.π) hw
    have hha : h ≫ a = π' := pullback.lift_fst _ _ _
    have hhb : h ≫ b = q' ≫ T.π := pullback.lift_snd _ _ _
    have sq' : IsPullback q' h T.π b := IsPullback.of_bot (by rwa [hha]) hhb.symm hab
    have : LocallyOfFiniteType h := MorphismProperty.of_isPullback sq' T.locallyOfFiniteType_π
    have : Flat h := MorphismProperty.of_isPullback sq' T.flat_π
    have hrelh : AlgebraicGeometry.RelativeDimension h n :=
      @AlgebraicGeometry.RelativeDimension.of_isPullback _ _ _ _ _ _ _ _ sq'
        T.locallyOfFiniteType_π n T.relDim
    have hhbase : h ≫ a ≫ sY = sY' := by rw [← Category.assoc, hha, hπ']
    exact flatPullbackChow_injective_of_comp_eq C sY' (a ≫ sY) sY h a π' hha hhbase rfl hπ'
      n (m + 1) (n + (m + 1)) rfl hrelh hrela hrel k _ _ hfac
      (ih (a ≫ sY) b sY' h hhbase q' sq' hrelh (k + ((m + 1 : ℕ) : ℤ))
        (flatPullbackFactorsThroughRationalEquivalence_general C _ _ _ _ _ _ _))
      (injective_flatPullbackChow_pullbackFst_projectiveBundleStep C sX E m hE sY f k)

/-- **Clause (1) of Stacks 02UL for a tower of projective bundles.** For every morphism
`f : Y ⟶ X` with `Y` locally of finite type over the base, flat pullback along the projection
`Y ×_X P ⟶ Y` of the chosen fibre product is injective in every degree. -/
theorem IsProjectiveBundleTower.injective_flatPullbackChow_pullbackFst
    {C : ChowSituation.{u}} {X : Scheme.{u}} {sX : X ⟶ C.S} [LocallyOfFiniteType sX] {d : ℕ}
    {T : SplittingMorphism C sX d} (hT : IsProjectiveBundleTower C sX d T) {Y : Scheme.{u}}
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : Y ⟶ X) (k : ℤ) :
    Function.Injective (flatPullbackChow C (pullback.fst f T.π ≫ sY) sY (pullback.fst f T.π) rfl d
      (AlgebraicGeometry.RelativeDimension.of_isPullback (IsPullback.of_hasPullback f T.π).flip
        T.relDim) k
      (flatPullbackFactorsThroughRationalEquivalence_general C _ sY _ rfl d _ k)) :=
  hT.injective_flatPullbackChow_of_isPullback sY f _ (pullback.fst f T.π) rfl
    (pullback.snd f T.π) (IsPullback.of_hasPullback f T.π).flip _ k _

end Stacks.Chow

end
