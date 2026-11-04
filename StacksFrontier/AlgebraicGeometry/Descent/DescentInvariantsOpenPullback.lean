module

public import StacksFrontier.AlgebraicGeometry.Descent.DescentInvariantsSpecSquare
public import StacksFrontier.AlgebraicGeometry.Descent.IntersectionOpenImmersion

/-!
# An invariant open of a descent datum as a base change of an open of the invariants

Let `f : X ⟶ S` be a morphism of affine schemes, let `V` be an ind-quasi-affine scheme over `X`,
let `E ⊆ V` be an intersection of a nonempty family of quasi-compact opens and let `W ⊆ E` be
open. Write `C = Γ(E, 𝒪_V|_E)` and suppose `C` is the base change to `Γ(X, ⊤)` of a
`Γ(S, ⊤)`-algebra `C₀`, so that `Spec C` is the fibre product `Spec C₀ ×_S X` by
`AlgebraicGeometry.isPullback_specMap_algebraMap_of_isPushout`.

If an open `W₀` of `Spec C₀` pulls back to the image `j(W)` of `W` under the canonical embedding
of [Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API), then that square restricts to
one exhibiting `W` as `W₀ ×_S X`. Applied to a descent datum and the subalgebra of invariants of
the transition isomorphism it induces on functions, this is the fibre-product condition of
`AlgebraicGeometry.DescentDatum.Descended` for the restriction of the datum to `W`, which is the
first of the two conditions making `W₀` a scheme descending that restriction.

## Main definitions

* `AlgebraicGeometry.liftOpenPreimage`: the morphism to an open induced by an open immersion whose
  range is the preimage of that open.

## Main results

* `AlgebraicGeometry.liftOpenPreimage_comp_ι`: that morphism, followed by the inclusion of the
  open, is the open immersion followed by the morphism along which the preimage was taken.
* `AlgebraicGeometry.isPullback_liftOpenPreimage`: **a fibre-product square restricts to an open
  of its lower-left corner and an open immersion onto the preimage of that open.**
* `AlgebraicGeometry.exists_isPullback_subsetΓSpecImage_of_isPushout`: **an open of `V` whose image
  under the canonical embedding of Stacks 0API descends to an open `W₀` of `Spec C₀` is the fibre
  product `W₀ ×_S X`,** compatibly with that embedding.
* `AlgebraicGeometry.DescentDatum.exists_isPullback_restrictOpen_descentInvariants`: the same at
  the invariants of a descent datum — **the scheme of the restriction of the datum to an invariant
  open `W` is the base change of the open of `Spec C₀` that `j(W)` descends to.**

## Implementation notes

*How the two squares are spliced.* `AlgebraicGeometry.isPullback_morphismRestrict` is the square
cutting `Spec C ⟶ Spec C₀` down to `W₀`; its upper-left corner is the preimage of `W₀`, and the
canonical embedding of `W` identifies `W` with that preimage because the two have the same range,
by hypothesis. Pasting it vertically onto the square of
`AlgebraicGeometry.isPullback_specMap_algebraMap_of_isPushout` gives the square over `X` and `S`.

*How the upper edge is identified.* The canonical embedding `k` of
`AlgebraicGeometry.exists_isOpenImmersion_range_eq_subsetΓSpecImage` satisfies
`k ≫ Spec (Γ(V, ⊤) ⟶ C) = W.ι ≫ V.toSpecΓ`, and the hypothesis `hAC` factors
`algebraMap Γ(X, ⊤) C` as the map on global functions of the morphism `V ⟶ X` followed by
restriction to `E`. So `AlgebraicGeometry.Scheme.toSpecΓ_naturality` at that morphism, together
with the affineness of `X`, turns `k` followed by the morphism to `X` into the inclusion of `W`
followed by the morphism `V ⟶ X`. That computation is isolated as
`AlgebraicGeometry.comp_specMap_appTop_isoSpec_inv_eq`, whose variables are a bare morphism of
rings and a bare morphism of schemes, so that the two spellings `Γ(V, ⊤) ⟶ R` and
`CommRingCat.of ↥Γ(V, ⊤) ⟶ CommRingCat.of ↥R` of the restriction map cannot both appear in one
rewrite.

*What is not proved here.* The second condition of `AlgebraicGeometry.DescentDatum.Descended`,
that the projection onto `W₀` equalises the two legs of the gluing isomorphism. That is a
statement about morphisms into `Spec C₀`, and the invariance of `C₀` which would give it,
`ModuleCat.descentInvariants_comp_transition`, is an identity of ring maps out of `C₀` into the
functions on `X ×_S E`; transporting it needs the canonical embedding of `X ×_S E` compared with
that of `E` as *morphisms of schemes*, whereas
`AlgebraicGeometry.preimage_specMap_sectionsRingOnSubsetMap_subsetΓSpecImage` compares them only
as maps of sets.

*No tag is placed.* These are steps in the proof of
[Stacks, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK), which is stated for arbitrary fpqc
covering families.

## References

* [Stacks Project, Tag 0API](https://stacks.math.columbia.edu/tag/0API)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The morphism to an open induced by an open immersion onto the preimage of that open.** For
`q : P ⟶ Y`, an open `W₀` of `Y` and an open immersion `k : V ⟶ P` whose range is `q⁻¹(W₀)`, this
is the morphism `V ⟶ W₀` through which `k ≫ q` factors. -/
def liftOpenPreimage {V P Y : Scheme.{u}} (k : V ⟶ P) [IsOpenImmersion k] (q : P ⟶ Y)
    (W₀ : Y.Opens) (hk : Set.range k.base = ((q ⁻¹ᵁ W₀ : P.Opens) : Set P)) :
    V ⟶ W₀.toScheme :=
  (IsOpenImmersion.isoOfRangeEq k (q ⁻¹ᵁ W₀).ι
    (by rw [hk, ← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι])).hom ≫ (q ∣_ W₀)

/-- `AlgebraicGeometry.liftOpenPreimage`, followed by the inclusion of the open, is the open
immersion followed by the morphism along which the preimage was taken. -/
@[reassoc]
lemma liftOpenPreimage_comp_ι {V P Y : Scheme.{u}} (k : V ⟶ P) [IsOpenImmersion k] (q : P ⟶ Y)
    (W₀ : Y.Opens) (hk : Set.range k.base = ((q ⁻¹ᵁ W₀ : P.Opens) : Set P)) :
    liftOpenPreimage k q W₀ hk ≫ W₀.ι = k ≫ q := by
  rw [liftOpenPreimage, Category.assoc, morphismRestrict_ι, ← Category.assoc,
    IsOpenImmersion.isoOfRangeEq_hom_fac]

/-- **A fibre-product square restricts to an open of its lower-left corner.** If
`IsPullback fst snd f g` and `k : V ⟶ P` is an open immersion whose range is the preimage under
`snd` of an open `W₀` of the lower-left corner, then `V` is the fibre product of `W₀` with the
upper-right corner. -/
theorem isPullback_liftOpenPreimage {P X Y Z V : Scheme.{u}} {fst : P ⟶ X} {snd : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (H : IsPullback fst snd f g) (W₀ : Y.Opens) (k : V ⟶ P)
    [IsOpenImmersion k] (hk : Set.range k.base = ((snd ⁻¹ᵁ W₀ : P.Opens) : Set P)) :
    IsPullback (k ≫ fst) (liftOpenPreimage k snd W₀ hk) f (W₀.ι ≫ g) := by
  have s : IsPullback (liftOpenPreimage k snd W₀ hk) k W₀.ι snd :=
    (isPullback_morphismRestrict snd W₀).of_iso'
      (IsOpenImmersion.isoOfRangeEq k (snd ⁻¹ᵁ W₀).ι
        (by rw [hk, ← Scheme.Hom.coe_opensRange, Scheme.Opens.opensRange_ι]))
      (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by rw [Iso.refl_hom, Category.comp_id]; rfl)
      (by rw [Iso.refl_hom, Category.comp_id]; exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _)
      (by simp) (by simp)
  exact (s.paste_vert H.flip).flip

/-- **A morphism to the spectrum of a ring of functions, read through an affine target.** Let
`φ : V ⟶ X` with `X` affine, let `t : Γ(V, ⊤) ⟶ R` be a morphism of rings and let `k` be a
morphism from an open `W` of `V` to `Spec R` compatible with `t` and the canonical morphism
`V ⟶ Spec Γ(V, ⊤)`. Then `k`, followed by the morphism to `X` induced by `φ.appTop ≫ t`, is the
inclusion of `W` followed by `φ`. -/
lemma comp_specMap_appTop_isoSpec_inv_eq {X V : Scheme.{u}} [IsAffine X] (φ : V ⟶ X)
    {R : CommRingCat.{u}} (t : Γ(V, ⊤) ⟶ R) (W : V.Opens) {k : W.toScheme ⟶ Spec R}
    (hk : k ≫ Spec.map t = W.ι ≫ V.toSpecΓ) :
    k ≫ Spec.map (φ.appTop ≫ t) ≫ X.isoSpec.inv = W.ι ≫ φ :=
  calc k ≫ Spec.map (φ.appTop ≫ t) ≫ X.isoSpec.inv
      = (k ≫ Spec.map t) ≫ Spec.map φ.appTop ≫ X.isoSpec.inv := by
        rw [Spec.map_comp]; simp only [Category.assoc]
    _ = W.ι ≫ V.toSpecΓ ≫ Spec.map φ.appTop ≫ X.isoSpec.inv := by
        rw [hk]; simp only [Category.assoc]
    _ = W.ι ≫ φ ≫ X.toSpecΓ ≫ X.isoSpec.inv := by rw [← Scheme.toSpecΓ_naturality_assoc]
    _ = W.ι ≫ φ := by rw [Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

/-- **An open whose image under the canonical embedding of Stacks 0API descends to an open of
`Spec C₀` is a base change of that open.** Let `f : X ⟶ S` be a morphism of affine schemes, let
`φ : V ⟶ X` with `V` ind-quasi-affine, let `E ⊆ V` be an intersection of a nonempty family of
quasi-compact opens and let `W ⊆ E` be open. Suppose `C = Γ(E, 𝒪_V|_E)` is the base change to
`Γ(X, ⊤)` of a `Γ(S, ⊤)`-algebra `C₀`, and that an open `W₀` of `Spec C₀` pulls back to the image
of `W` under the canonical embedding of
[Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API). Then that embedding identifies `W`
with the fibre product `W₀ ×_S X`. -/
theorem exists_isPullback_subsetΓSpecImage_of_isPushout {S X V : Scheme.{u}} [IsAffine S]
    [IsAffine X] [IsIndQuasiAffine V] (f : X ⟶ S) (φ : V ⟶ X) (E : Set V) (C₀ : Type u)
    [CommRing C₀] [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)] [Algebra ↥Γ(S, ⊤) ↥(V.sectionsRingOnSubset E)]
    [Algebra ↥Γ(X, ⊤) ↥(V.sectionsRingOnSubset E)] [Algebra ↥Γ(S, ⊤) C₀]
    [Algebra C₀ ↥(V.sectionsRingOnSubset E)]
    [IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(V.sectionsRingOnSubset E)]
    [IsScalarTower ↥Γ(S, ⊤) C₀ ↥(V.sectionsRingOnSubset E)]
    (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
    (hAC : CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(V.sectionsRingOnSubset E)) =
      φ.appTop ≫ V.topToSubset E)
    (hpo : Algebra.IsPushout ↥Γ(S, ⊤) ↥Γ(X, ⊤) C₀ ↥(V.sectionsRingOnSubset E))
    {I : Type u} [Nonempty I] (U : I → V.Opens) (hU : ∀ i, IsCompact (U i : Set V))
    (hE : E = ⋂ i, (U i : Set V)) (W : V.Opens) (hWE : (W : Set V) ⊆ E)
    (W₀ : (Spec (CommRingCat.of C₀)).Opens)
    (hW₀ : ((Spec.map (CommRingCat.ofHom
            (algebraMap C₀ ↥(V.sectionsRingOnSubset E))) ⁻¹ᵁ W₀ :
          (Spec (CommRingCat.of ↥(V.sectionsRingOnSubset E))).Opens) :
        Set (Spec (CommRingCat.of ↥(V.sectionsRingOnSubset E)))) =
      subsetΓSpecImage V E (W : Set V)) :
    ∃ (k : W.toScheme ⟶ Spec (V.sectionsRingOnSubset E)) (p : W.toScheme ⟶ W₀.toScheme),
      IsOpenImmersion k ∧
      Set.range k.base = subsetΓSpecImage V E (W : Set V) ∧
      p ≫ W₀.ι =
        k ≫ Spec.map (CommRingCat.ofHom (algebraMap C₀ ↥(V.sectionsRingOnSubset E))) ∧
      IsPullback (W.ι ≫ φ) p f
        (W₀.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) C₀)) ≫ S.isoSpec.inv) := by
  obtain ⟨k, hkoi, -, hkrange, hkcomp⟩ :=
    exists_isOpenImmersion_range_eq_subsetΓSpecImage V U hU E hE W hWE
  have _ : IsOpenImmersion k := hkoi
  have hpre : Set.range k.base =
      ((Spec.map (CommRingCat.ofHom (algebraMap C₀ ↥(V.sectionsRingOnSubset E))) ⁻¹ᵁ W₀ :
          (Spec (CommRingCat.of ↥(V.sectionsRingOnSubset E))).Opens) :
        Set (Spec (CommRingCat.of ↥(V.sectionsRingOnSubset E)))) :=
    hkrange.trans hW₀.symm
  refine ⟨k, liftOpenPreimage k _ W₀ hpre, hkoi, hkrange,
    liftOpenPreimage_comp_ι k _ W₀ hpre, ?_⟩
  have hsq := isPullback_liftOpenPreimage
    (isPullback_specMap_algebraMap_of_isPushout f C₀ ↥(V.sectionsRingOnSubset E) hRA hpo) W₀ k
    hpre
  refine hsq.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ (by simp) (by simp)
    (by simp)
  rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp]
  exact (congrArg (fun ψ ↦ k ≫ Spec.map ψ ≫ X.isoSpec.inv) hAC).trans
    (comp_specMap_appTop_isoSpec_inv_eq φ (V.topToSubset E) W hkcomp)

namespace DescentDatum

variable {S X : Scheme.{u}} {f : X ⟶ S} (D : DescentDatum f) (E : Set D.over.left)
    [Algebra ↥Γ(S, ⊤) ↥Γ(X, ⊤)] [Algebra ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    [Algebra ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    [IsScalarTower ↥Γ(S, ⊤) ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)]
    (hRA : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥Γ(X, ⊤)) = f.appTop)
    (hRC : CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      (D.over.hom ≫ f).appTop ≫ D.over.left.topToSubset E)
    (hAC : CommRingCat.ofHom (algebraMap ↥Γ(X, ⊤) ↥(D.over.left.sectionsRingOnSubset E)) =
      D.over.hom.appTop ≫ D.over.left.topToSubset E)
    [IsAffine S] [IsAffine X] [Flat f] [Surjective f] [QuasiSeparatedSpace D.over.left]
    [IsIndQuasiAffineHom D.over.hom]
    {I : Type u} [Nonempty I] (U : I → D.over.left.Opens)
    (hU : ∀ i, IsCompact (U i : Set D.over.left)) (hE : E = ⋂ i, (U i : Set D.over.left))
    (h₁ : (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.hom ⁻¹' (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E))
    (h₂ : (⇑(pullback.snd f (D.over.hom ≫ f)) ⁻¹' E) ⊆
      ⇑D.transitionPullbackIso.inv ⁻¹' (⇑(pullback.fst (D.over.hom ≫ f) f) ⁻¹' E))
    (W : D.over.left.Opens) (hWinv : D.IsTransitionInvariant W)
    (hWE : (W : Set D.over.left) ⊆ E)

include hRA hRC hAC hU hE hWE in
/-- **The scheme of the restriction of a descent datum to an invariant open is the base change of
the open of `Spec C₀` that the open descends to.** Let `f : X ⟶ S` be a surjective flat morphism
of affine schemes, let `D` be a descent datum relative to `f` whose scheme `V` is ind-quasi-affine
over `X` and quasi-separated, let `E ⊆ V` be an intersection of a nonempty family of quasi-compact
opens whose two preimages are carried into one another by the gluing isomorphism, and let `W ⊆ E`
be an invariant open of `V`. If an open `W₀` of `Spec C₀`, for `C₀` the subalgebra of invariants of
the transition isomorphism the datum induces on functions, pulls back to the image of `W` under
the canonical embedding of [Stacks, Tag 0API](https://stacks.math.columbia.edu/tag/0API), then the
structure morphism of the restricted datum and a projection `W ⟶ W₀` exhibit `W` as the fibre
product `W₀ ×_S X`.

This is the field `isPullback` of `AlgebraicGeometry.DescentDatum.Descended` for the restricted
datum, with `W₀` as the descended scheme; the projection is the canonical embedding of `W`
followed by the morphism induced by the inclusion of the invariants. -/
theorem exists_isPullback_restrictOpen_descentInvariants
    (W₀ : (Spec (CommRingCat.of ↥(ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤)
        ↥(D.over.left.sectionsRingOnSubset E)
        (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂)))).Opens)
    (hW₀ : ((Spec.map (CommRingCat.ofHom (algebraMap
          (ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤)
            ↥(D.over.left.sectionsRingOnSubset E)
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
          ↥(D.over.left.sectionsRingOnSubset E))) ⁻¹ᵁ W₀ :
          (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E))).Opens) :
        Set (Spec (CommRingCat.of ↥(D.over.left.sectionsRingOnSubset E)))) =
      subsetΓSpecImage D.over.left E (W : Set D.over.left)) :
    ∃ (k : W.toScheme ⟶ Spec (D.over.left.sectionsRingOnSubset E))
      (p : W.toScheme ⟶ W₀.toScheme),
      IsOpenImmersion k ∧
      Set.range k.base = subsetΓSpecImage D.over.left E (W : Set D.over.left) ∧
      p ≫ W₀.ι = k ≫ Spec.map (CommRingCat.ofHom (algebraMap
        (ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤)
          ↥(D.over.left.sectionsRingOnSubset E)
          (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
        ↥(D.over.left.sectionsRingOnSubset E))) ∧
      IsPullback (D.restrictOpen W hWinv).over.hom p f
        (W₀.ι ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥Γ(S, ⊤)
          (ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤)
            ↥(D.over.left.sectionsRingOnSubset E)
            (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂)))) ≫ S.isoSpec.inv) := by
  have _ : IsIndQuasiAffine D.over.left := isIndQuasiAffine_of_isIndQuasiAffineHom_hom D.over
  exact
    exists_isPullback_subsetΓSpecImage_of_isPushout f D.over.hom E
      ↥(ModuleCat.descentInvariants ↥Γ(S, ⊤) ↥Γ(X, ⊤)
        ↥(D.over.left.sectionsRingOnSubset E)
        (D.descentAlgebraTransition E hRA hRC hAC U hU hE h₁ h₂))
      hRA hAC (D.isPushout_descentInvariants E hRA hRC hAC U hU hE h₁ h₂) U hU hE W hWE W₀ hW₀

end DescentDatum

end AlgebraicGeometry

end

end
