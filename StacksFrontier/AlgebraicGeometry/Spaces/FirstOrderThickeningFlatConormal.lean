module

public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Properties
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FirstOrderThickeningConormalConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderThickening
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderThickeningSupplement
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleOfImmersionChartReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleOfImmersionRepresentedReflect
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# Flatness of a morphism of first-order thickenings of algebraic spaces

Let
```
X --⊆--→ X'
|f       |g
↓        ↓
Y --⊆--→ Y'
```
be a morphism of first-order thickenings of algebraic spaces over a scheme `S`, with `f` flat.
[Stacks Project, Tag 06BH] asserts that the two conditions

1. `g` is flat and `X = Y ×_{Y'} X'`,
2. the canonical map `f^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 04CP] is an isomorphism,

are equivalent.  This file proves (2) ⟹ (1) and registers the equivalence.

## Main results

* `AlgebraicGeometry.Space.exists_charts_of_isIso_conormalMapOfImmersions`: under (2), a square
  of étale charts `U' → V'` of `g` whose closed subschemes `U₀ ⊆ U'`, `V₀ ⊆ V'` cut out by `X` and
  `Y` form a cartesian square of schemes with `U' → V'` flat.
* `AlgebraicGeometry.Space.isFlat_and_isPullback_of_isIso_conormalMapOfImmersions`: (2) ⟹ (1).
* `AlgebraicGeometry.Space.isFlat_and_isPullback_iff_isIso_conormalMapOfImmersions`:
  **[Stacks Project, Tag 06BH]**.

## Route

This is the source's proof.  Choose an étale atlas `V' → Y'` and an étale atlas `U'` of
`X' ×_{Y'} V'`, and let `U₀ = X ×_{X'} U'` and `V₀ = Y ×_{Y'} V'`, closed subschemes which are
first-order thickenings of schemes
(`AlgebraicGeometry.Space.exists_nthOrderThickening_chart_pullback`).
The induced `U₀ → V₀` is flat because `f` is.  Condition (2) passes to the square of charts by
the 04G2 (3) stacking lemmas and 04CO
(`AlgebraicGeometry.Space.isIso_conormalMapOfImmersions_chart_of_isIso`), then to the square of
schemes by 04G2 (2)
(`AlgebraicGeometry.Space.isIso_immersionConormalSheafMap_of_isIso_conormalMapOfImmersions`),
where the scheme case [Stacks Project, Tag 063Y]
(`Stacks.Thickenings.flat_and_isPullback_of_isIso_immersionConormalSheafMap`) makes `U' → V'`
flat and the square of charts cartesian.  Flatness of `g` is then [Stacks Project, Tag 03MJ]
for the étale local property of being flat.  For the cartesian square, `X` is contained in the
inverse image `g⁻¹(Y)` and the inclusion is locally surjective: a section of `g⁻¹(Y)` lifts
locally to `U'`, where it lands in `V₀` after `U' → V'` and hence in `U₀ = V₀ ×_{V'} U'`.  A
monomorphism of sheaves that is locally surjective is an isomorphism, so `X = g⁻¹(Y)`, which
is the fibre product of [Stacks Project, Tag 083Q].

The direction (1) ⟹ (2) is the flat clause of [Stacks Project, Tag 04CQ],
`AlgebraicGeometry.Space.isIso_conormalMapOfImmersions_of_isPullback_of_isFlat`.

## References

* [Stacks Project, Tag 06BH](https://stacks.math.columbia.edu/tag/06BH)
* [Stacks Project, Tag 063Y](https://stacks.math.columbia.edu/tag/063Y)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' Y' : AlgebraicSpaces B S hS} (X : ClosedSubspaces B S hS X'.1)
    (Y : ClosedSubspaces B S hS Y'.1) (g : X' ⟶ Y')
    (f : (⟨X.1.toFunctor, X.2.1⟩ : AlgebraicSpaces B S hS) ⟶
      (⟨Y.1.toFunctor, Y.2.1⟩ : AlgebraicSpaces B S hS))

/-- A chart pullback square of a closed subspace, read in the category of algebraic spaces. -/
private theorem isPullback_homMk_subspaceInclusion {U' U₀ : BigFppfOver B S hS}
    (j : U₀ ⟶ U') (a' : yoneda.obj U' ⟶ X'.1) (p : yoneda.obj U₀ ⟶ X.1.toFunctor)
    (hp : IsPullback p (yoneda.map j) X.1.ι a') :
    IsPullback
      (ObjectProperty.homMk p : (⟨yoneda.obj U₀, isAlgebraicSpace_yoneda B S hS U₀⟩ :
        AlgebraicSpaces B S hS) ⟶ ⟨X.1.toFunctor, X.2.1⟩) (representedSpaceMap B S hS j)
      (subspaceInclusion B S hS X' X)
      (ObjectProperty.homMk a' : (⟨yoneda.obj U', isAlgebraicSpace_yoneda B S hS U'⟩ :
        AlgebraicSpaces B S hS) ⟶ X') :=
  IsPullback.of_map_of_faithful (ObjectProperty.ι _) hp

/-- **The charts of the proof of Stacks 06BH.**  For a morphism of first-order thickenings of
algebraic spaces `(f, g) : (X ⊆ X') → (Y ⊆ Y')` with `f` flat whose canonical map of conormal
modules of [Stacks Project, Tag 04CP] is an isomorphism, there are a surjective étale chart
`a' : U' → X'`, an étale chart `b' : V' → Y'` and `α : U' → V'` over `g`, together with the
closed subschemes `j : U₀ → U'` and `k : V₀ → V'` cut out by `X` and `Y` and a morphism
`f₀ : U₀ → V₀` over `f`, such that `α` is flat and the square `(j, f₀, α, k)` of schemes is
cartesian.  This is the scheme case [Stacks Project, Tag 063Y] applied on charts. -/
theorem exists_charts_of_isIso_conormalMapOfImmersions
    (hsq : subspaceInclusion B S hS X' X ≫ g = f ≫ subspaceInclusion B S hS Y' Y)
    (hX : IsFirstOrderThickening B S hS X' X.1) (hY : IsFirstOrderThickening B S hS Y' Y.1)
    (hf : IsFlat B S hS f.hom)
    (h : IsIso (conormalMapOfImmersions B S hS (subspaceInclusion B S hS X' X)
        (subspaceInclusion B S hS Y' Y) f g (isImmersion_subspaceInclusion B S hS X' X)
        (isImmersion_subspaceInclusion B S hS Y' Y) hsq)) :
    ∃ (U' V' U₀ V₀ : BigFppfOver B S hS) (a' : yoneda.obj U' ⟶ X'.1)
      (b' : yoneda.obj V' ⟶ Y'.1) (α : U' ⟶ V') (j : U₀ ⟶ U') (k : V₀ ⟶ V') (f₀ : U₀ ⟶ V₀)
      (p : yoneda.obj U₀ ⟶ X.1.toFunctor) (q : yoneda.obj V₀ ⟶ Y.1.toFunctor),
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a' ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf a' ∧
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf b' ∧
      a' ≫ g.hom = yoneda.map α ≫ b' ∧
      IsPullback p (yoneda.map j) X.1.ι a' ∧ IsPullback q (yoneda.map k) Y.1.ι b' ∧
      f₀ ≫ k = j ≫ α ∧ yoneda.map f₀ ≫ q = p ≫ f.hom ∧
      Flat ((BigFppfOver.toScheme B S hS).map α) ∧
      IsPullback ((BigFppfOver.toScheme B S hS).map j) ((BigFppfOver.toScheme B S hS).map f₀)
        ((BigFppfOver.toScheme B S hS).map α) ((BigFppfOver.toScheme B S hS).map k) := by
  let T := BigFppfOver.toScheme B S hS
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) T)).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  obtain ⟨V', b', hb'S, hb'E⟩ := Y'.2.exists_atlas
  obtain ⟨U', a', α, hα, ha'S, ha'E⟩ :=
    exists_surjective_etale_presentation_lift B S hS X'.2 Y'.2 g.hom V' b' hb'S hb'E
  obtain ⟨U₀, j, p, hpU, hjc, hj2⟩ := exists_nthOrderThickening_chart_pullback B S hS hX U' a' ha'E
  obtain ⟨V₀, k, q, hpV, hkc, hk2⟩ := exists_nthOrderThickening_chart_pullback B S hS hY V' b' hb'E
  have h1 : X.1.ι ≫ g.hom = f.hom ≫ Y.1.ι := congrArg (fun m => m.hom) hsq
  have hw : (p ≫ f.hom) ≫ Y.1.ι = yoneda.map (j ≫ α) ≫ b' := by
    rw [Category.assoc, ← h1, ← Category.assoc, hpU.w, Category.assoc, hα, Functor.map_comp,
      Category.assoc]
  let f₀ : U₀ ⟶ V₀ := yoneda.preimage (hpV.lift (p ≫ f.hom) (yoneda.map (j ≫ α)) hw)
  have hf₀q : yoneda.map f₀ ≫ q = p ≫ f.hom := by
    simp only [f₀, Functor.map_preimage, IsPullback.lift_fst]
  have hf₀k : f₀ ≫ k = j ≫ α := by
    apply yoneda.map_injective
    simp only [f₀, Functor.map_comp, Functor.map_preimage, IsPullback.lift_snd]
  have hflat₀ : Flat (T.map f₀) := hf U₀ V₀ p q f₀ (MorphismProperty.of_isPullback hpU.flip ha'E)
    (MorphismProperty.of_isPullback hpV.flip hb'E) hf₀q
  have : _root_.AlgebraicGeometry.IsClosedImmersion (T.map j) := hjc
  have : _root_.AlgebraicGeometry.IsClosedImmersion (T.map k) := hkc
  have hsqU : representedSpaceMap B S hS j ≫ representedSpaceMap B S hS α =
      representedSpaceMap B S hS f₀ ≫ representedSpaceMap B S hS k :=
    ObjectProperty.hom_ext _ (by
      show yoneda.map j ≫ yoneda.map α = yoneda.map f₀ ≫ yoneda.map k
      rw [← Functor.map_comp, ← Functor.map_comp, hf₀k])
  have hc := isIso_conormalMapOfImmersions_chart_of_isIso B S hS
    (subspaceInclusion B S hS X' X) (subspaceInclusion B S hS Y' Y) f g
    (isImmersion_subspaceInclusion B S hS X' X) (isImmersion_subspaceInclusion B S hS Y' Y) hsq
    (representedSpaceMap B S hS j) _ _
    (isPullback_homMk_subspaceInclusion B S hS X j a' p hpU)
    (isEtale_of_presheaf_etale' B S hS a' ha'E)
    (representedSpaceMap B S hS k) _ _
    (isPullback_homMk_subspaceInclusion B S hS Y k b' q hpV)
    (isEtale_of_presheaf_etale' B S hS b' hb'E)
    (representedSpaceMap B S hS f₀) (representedSpaceMap B S hS α) hsqU
    (ObjectProperty.hom_ext _ hf₀q) (ObjectProperty.hom_ext _ hα.symm)
    (isImmersion_representedSpaceMap B S hS j) (isImmersion_representedSpaceMap B S hS k) h
  have hs := isIso_immersionConormalSheafMap_of_isIso_conormalMapOfImmersions B S hS j k f₀ α
    hf₀k.symm hc
  have hcomm : T.map j ≫ T.map α = T.map f₀ ≫ T.map k := by
    rw [← Functor.map_comp, ← Functor.map_comp, hf₀k]
  obtain ⟨hflatα, hpb⟩ := Stacks.Thickenings.flat_and_isPullback_of_isIso_immersionConormalSheafMap
    (T.map j) (T.map k) (T.map f₀) (T.map α) hcomm hj2 hk2 hs
  exact ⟨U', V', U₀, V₀, a', b', α, j, k, f₀, p, q, ha'S, ha'E, hb'E, hα, hpU, hpV, hf₀k, hf₀q,
    hflatα, hpb⟩

/-- **(2) ⟹ (1) of [Stacks Project, Tag 06BH].**  Let `(f, g) : (X ⊆ X') → (Y ⊆ Y')` be a
morphism of first-order thickenings of algebraic spaces with `f` flat.  If the canonical map
`f^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 04CP] is an isomorphism, then `g` is flat and
the square is cartesian, `X = Y ×_{Y'} X'`. -/
theorem isFlat_and_isPullback_of_isIso_conormalMapOfImmersions
    (hsq : subspaceInclusion B S hS X' X ≫ g = f ≫ subspaceInclusion B S hS Y' Y)
    (hX : IsFirstOrderThickening B S hS X' X.1) (hY : IsFirstOrderThickening B S hS Y' Y.1)
    (hf : IsFlat B S hS f.hom)
    (h : IsIso (conormalMapOfImmersions B S hS (subspaceInclusion B S hS X' X)
        (subspaceInclusion B S hS Y' Y) f g (isImmersion_subspaceInclusion B S hS X' X)
        (isImmersion_subspaceInclusion B S hS Y' Y) hsq)) :
    IsFlat B S hS g.hom ∧
      IsPullback (subspaceInclusion B S hS X' X) f g (subspaceInclusion B S hS Y' Y) := by
  obtain ⟨U', V', U₀, V₀, a', b', α, j, k, f₀, p, q, ha'S, ha'E, hb'E, hα, hpU, hpV, hf₀k, hf₀q,
    hflatα, hpb⟩ := exists_charts_of_isIso_conormalMapOfImmersions B S hS X Y g f hsq hX hY hf h
  refine ⟨(holdsOnEveryEtaleChart_iff_surjectiveChart B S hS _
    isEtaleLocalOnSourceAndTarget_flat X'.2 Y'.2 g.hom).2
      ⟨U', V', a', b', α, ha'E, hb'E, ha'S, hα.symm, hflatα⟩, ?_⟩
  -- The square of charts, read in the big fppf category.
  have hpbB : IsPullback j f₀ α k := by
    have _ : ReflectsLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
      reflectsLimitsOfShape_of_reflectsIsomorphisms
    exact IsPullback.of_map_of_faithful (BigFppfOver.toScheme B S hS) hpb
  have h1 : X.1.ι ≫ g.hom = f.hom ≫ Y.1.ι := congrArg (fun m => m.hom) hsq
  -- `X` lies in the inverse image of `Y`.
  have hle : X.1 ≤ Y.1.preimage g.hom := by
    intro T x hx
    have := congrFun (congrArg (fun m => m.app T) h1) ⟨x, hx⟩
    change g.hom.app T x = (f.hom.app T ⟨x, hx⟩).1 at this
    show g.hom.app T x ∈ Y.1.obj T
    exact this ▸ (f.hom.app T ⟨x, hx⟩).2
  -- The inclusion `X ⊆ g⁻¹(Y)` is locally surjective, by lifting along the atlas of `X'`.
  let φ := Subfunctor.homOfLe hle
  have hloc : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) φ := by
    have ha'loc := isLocallySurjective_of_surjective_etale B S hS a' ha'S ha'E
    refine ⟨fun {T} s => (BigFppfOver.topology B S hS).superset_covering ?_
      (ha'loc.imageSieve_mem s.1)⟩
    rintro T' e ⟨u, hu⟩
    have hgu : (b'.app (Opposite.op T') (u ≫ α)) ∈ Y.1.obj (Opposite.op T') := by
      have h2 := congrFun (congrArg (fun m => m.app (Opposite.op T')) hα) u
      change g.hom.app _ (a'.app _ u) = b'.app _ (u ≫ α) at h2
      rw [← h2, hu]
      exact ((Y.1.preimage g.hom).toFunctor.map e.op s).2
    obtain ⟨v, -, hv⟩ := Types.exists_of_isPullback
      (hpV.map ((evaluation _ _).obj (Opposite.op T')))
      (⟨b'.app (Opposite.op T') (u ≫ α), hgu⟩ : Y.1.toFunctor.obj (Opposite.op T'))
      (u ≫ α) rfl
    change v ≫ k = u ≫ α at hv
    let w : T' ⟶ U₀ := hpbB.lift u v hv.symm
    refine ⟨p.app (Opposite.op T') w, Subtype.ext ?_⟩
    have h3 := congrFun (congrArg (fun m => m.app (Opposite.op T')) hpU.w) w
    change (p.app (Opposite.op T') w).1 = a'.app (Opposite.op T') (w ≫ j) at h3
    show (p.app (Opposite.op T') w).1 = X'.1.map e.op s.1
    rwa [h3, hpbB.lift_fst]
  have hiso : IsIso φ := by
    let J := BigFppfOver.topology B S hS
    have hF : Presheaf.IsSheaf J X.1.toFunctor := X.2.1.isSheaf
    have hG : Presheaf.IsSheaf J (Y.1.preimage g.hom).toFunctor :=
      (isClosedSubspace_preimage B S hS g.hom Y.1 Y'.2 X'.2 Y.2).1.isSheaf
    let ψ : (⟨_, hF⟩ : Sheaf J (Type u)) ⟶ ⟨_, hG⟩ := ObjectProperty.homMk φ
    have hi : Sheaf.IsLocallyInjective ψ :=
      Presheaf.isLocallyInjective_of_injective J φ fun T x y hxy =>
        Subtype.ext (congrArg (fun z : (Y.1.preimage g.hom).toFunctor.obj T => z.1) hxy)
    have _ : IsIso ψ := (Sheaf.isLocallyBijective_iff_isIso ψ).1 ⟨hi, hloc⟩
    exact (sheafToPresheaf J (Type u)).map_isIso ψ
  -- Hence `X` is the fibre product.
  have hcart : IsPullback X.1.ι f.hom g.hom Y.1.ι := by
    refine (Subfunctor.isPullback_preimage g.hom Y.1).flip.of_iso (asIso φ).symm (Iso.refl _)
      (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv]
      rw [IsIso.eq_inv_comp]
      exact Subfunctor.homOfLe_ι hle
    · simp only [Iso.refl_hom, Category.comp_id, Iso.symm_hom, asIso_inv]
      rw [IsIso.eq_inv_comp, ← cancel_mono Y.1.ι, Category.assoc,
        (Subfunctor.isPullback_preimage g.hom Y.1).w, ← Category.assoc]
      simpa only [φ, Subfunctor.homOfLe_ι] using h1
    · simp
    · simp
  exact IsPullback.of_map_of_faithful (ObjectProperty.ι _) hcart

/-- **[Stacks Project, Tag 06BH].**  Let `(f, g) : (X ⊆ X') → (Y ⊆ Y')` be a morphism of
first-order thickenings of algebraic spaces over `S` (a commutative square of inclusions of
closed subspaces which are first-order thickenings, [Stacks Project, Tag 05ZK]), and assume
that `f` is flat.  Then the following are equivalent:

1. `g` is flat and `X = Y ×_{Y'} X'`;
2. the canonical map `f^*𝒞_{Y/Y'} ⟶ 𝒞_{X/X'}` of [Stacks Project, Tag 04CP] is an isomorphism.

Flatness is that of [Stacks Project, Tag 03ML], the equality `X = Y ×_{Y'} X'` is the square
being cartesian, and the canonical map is that of the two inclusions read as immersions. -/
@[stacks 06BH]
theorem isFlat_and_isPullback_iff_isIso_conormalMapOfImmersions
    (hsq : subspaceInclusion B S hS X' X ≫ g = f ≫ subspaceInclusion B S hS Y' Y)
    (hX : IsFirstOrderThickening B S hS X' X.1) (hY : IsFirstOrderThickening B S hS Y' Y.1)
    (hf : IsFlat B S hS f.hom) :
    (IsFlat B S hS g.hom ∧
        IsPullback (subspaceInclusion B S hS X' X) f g (subspaceInclusion B S hS Y' Y)) ↔
      IsIso (conormalMapOfImmersions B S hS (subspaceInclusion B S hS X' X)
        (subspaceInclusion B S hS Y' Y) f g (isImmersion_subspaceInclusion B S hS X' X)
        (isImmersion_subspaceInclusion B S hS Y' Y) hsq) :=
  ⟨fun ⟨hg, hcart⟩ => isIso_conormalMapOfImmersions_of_isPullback_of_isFlat B S hS _ _ f g
      (isImmersion_subspaceInclusion B S hS X' X) (isImmersion_subspaceInclusion B S hS Y' Y)
      hcart hg,
    fun h => isFlat_and_isPullback_of_isIso_conormalMapOfImmersions B S hS X Y g f hsq hX hY hf h⟩

end AlgebraicGeometry.Space

end
