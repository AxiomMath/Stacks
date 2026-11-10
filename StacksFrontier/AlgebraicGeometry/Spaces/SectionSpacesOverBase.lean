module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget

/-!
# A section of a surjective étale space over a base object of the site (Stacks 05XQ)

Let `S` be a scheme of a big fppf site, let `U` and `Z` be objects of the big fppf site of `S`
and let `ζ : Z ⟶ U` have finite underlying morphism of schemes. Let `W` be an algebraic space
over `S` equipped with a surjective étale morphism `w : W ⟶ h_Z`. Stacks 05XQ asserts that `w`
admits a section after a surjective étale base change of `U`: there is an object `T` of the big
fppf site of `S` and a morphism `r : T ⟶ U`, surjective and étale on underlying schemes,
together with a section of `W ×_{h_Z} h_{T ×_U Z} ⟶ h_{T ×_U Z}`, recorded as a morphism
`h_{T ×_U Z} ⟶ W` over `h_Z`.

`AlgebraicGeometry.Space.exists_surjective_etale_sectionsOver` is the same statement with `U`
taken to be the base scheme of the site itself, so that `T ×_U Z` is the product `T ⨯ Z` in the
site. Neither form is an instance of the other: there the base morphism of `Z` is the structure
morphism `B.inclusion.map Z.hom`, here it is an arbitrary morphism `ζ` of the site, and the
fibre product over `U` is not the product over the base. The form over a base object is what
the restriction of scalars of Stacks 05YA consumes, because the fibre of a morphism of
restrictions of scalars sits over a representable base and not over the final algebraic space.

## The shape of the argument

Both forms have the same proof, and all of its mathematics is base-independent. Choosing a
scheme atlas `p : h_V ⟶ W` replaces `w` by a surjective étale morphism of schemes `V ⟶ Z`;
`AlgebraicGeometry.exists_contains_surjective_etale_section_of_isFinite`, which is the content
of Stacks 05XQ for schemes, then produces the surjective étale `τ : T ⟶ Z ×_U U` together with
a morphism `Z ×_U T ⟶ V` over `Z`. What remains is to read that scheme morphism back as a
morphism `T ×_U Z ⟶ V` of the site, which is
`AlgebraicGeometry.BigFppfOver.exists_map_of_toScheme_map_over`, and to compose with the atlas.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_map_of_toScheme_map_over`: a morphism of the underlying
  schemes of two objects of the site which lies over a morphism of the site comes from a
  morphism of the site.
* `AlgebraicGeometry.Space.exists_surjective_etale_sectionOverBase`: **Stacks 05XQ** over a base
  object of the site.

## References

* [Stacks Project, Tag 05XQ](https://stacks.math.columbia.edu/tag/05XQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **A morphism of the underlying schemes which lies over a morphism of the site comes from a
morphism of the site.** The inclusion of a big fppf site is full and faithful, so a morphism
`m₀` of underlying schemes is the image of a unique morphism of the underlying category; it is
a morphism of the slice over `S` because it factors the structure morphism of `P` through that
of `V`, which is what lying over `k` gives. -/
theorem BigFppfOver.exists_map_of_toScheme_map_over (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {P V Z : BigFppfOver B S hS} (k : V ⟶ Z) (q : P ⟶ Z)
    (m₀ : (BigFppfOver.toScheme B S hS).obj P ⟶ (BigFppfOver.toScheme B S hS).obj V)
    (hm₀ : m₀ ≫ (BigFppfOver.toScheme B S hS).map k = (BigFppfOver.toScheme B S hS).map q) :
    ∃ m : P ⟶ V, (BigFppfOver.toScheme B S hS).map m = m₀ ∧ m ≫ k = q := by
  have hn : B.inclusion.map (B.inclusion.preimage m₀) = m₀ := B.inclusion.map_preimage m₀
  have key : ∀ {X Y : BigFppfOver B S hS} (g : X ⟶ Y),
      (BigFppfOver.toScheme B S hS).map g ≫ B.inclusion.map Y.hom = B.inclusion.map X.hom := by
    intro X Y g
    rw [← Over.w g, B.inclusion.map_comp]
    rfl
  have hw : B.inclusion.preimage m₀ ≫ V.hom = P.hom := by
    refine B.inclusion.map_injective ?_
    rw [B.inclusion.map_comp, hn, ← key k, ← Category.assoc, hm₀, key q]
  refine ⟨Over.homMk (B.inclusion.preimage m₀) hw, hn, ?_⟩
  refine (BigFppfOver.forget B S hS).map_injective ?_
  refine B.inclusion.map_injective ?_
  change B.inclusion.map (B.inclusion.preimage m₀ ≫ k.left) = B.inclusion.map q.left
  rw [B.inclusion.map_comp, hn]
  exact hm₀

/-- **Stacks 05XQ over a base object of the site.** Let `ζ : Z ⟶ U` be a morphism of the big
fppf site of `S` whose underlying morphism of schemes is finite, let `W` be an algebraic space
over `S` and let `w : W ⟶ h_Z` be surjective and étale. Then there is an object `T` of the big
fppf site of `S` and a morphism `r : T ⟶ U`, surjective and étale on underlying schemes,
together with a section of `W ⟶ h_Z` over `T ×_U Z`, that is a morphism `h_{T ×_U Z} ⟶ W`
whose composite with `w` is the projection to `h_Z`. -/
@[stacks 05XQ]
theorem Space.exists_surjective_etale_sectionOverBase (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (U Z : BigFppfOver B S hS) (ζ : Z ⟶ U)
    (hζ : IsFinite ((BigFppfOver.toScheme B S hS).map ζ))
    (W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (w : W ⟶ yoneda.obj Z)
    (hW : IsAlgebraicSpace B S hS W) (hw_surjective : Space.IsSurjective B S hS w)
    (hw_etale : Space.IsEtale B S hS w) :
    ∃ (T : BigFppfOver B S hS) (r : T ⟶ U),
      Surjective ((BigFppfOver.toScheme B S hS).map r) ∧
      Etale ((BigFppfOver.toScheme B S hS).map r) ∧
      ∃ σ : pullback (yoneda.map r) (yoneda.map ζ) ⟶ W,
        σ ≫ w = pullback.snd (yoneda.map r) (yoneda.map ζ) := by
  classical
  let G := BigFppfOver.toScheme B S hS
  obtain ⟨V, p, hp_surjective, hp_etale⟩ := hW.exists_atlas
  have hpw_surjective : Space.IsSurjective B S hS (p ≫ w) :=
    Space.isSurjective_comp B S hS
      ((Space.presheafSurjective_iff_isSurjective_yoneda B S hS W hW V p).mp hp_surjective)
      hw_surjective
  let f : V ⟶ Z := yoneda.preimage (p ≫ w)
  have hf : yoneda.map f = p ≫ w := yoneda.map_preimage (p ≫ w)
  let π : G.obj Z ⟶ G.obj U := G.map ζ
  let fₛ : G.obj V ⟶ G.obj Z := G.map f
  have : IsFinite π := hζ
  have hmap : ∀ Q : MorphismProperty Scheme.{u},
      (MorphismProperty.inverseImage Q G).presheaf (p ≫ w) → Q (G.map f) := fun Q hg ↦
    hg.property (𝟙 (yoneda.obj Z)) (𝟙 (yoneda.obj V)) f
      (by simpa [hf] using (IsPullback.of_id_fst (f := yoneda.map f)))
  have : Etale fₛ := hmap @Etale (hw_etale V p hp_etale)
  have : Surjective fₛ := hmap @Surjective
    ((Space.presheafSurjective_iff_isSurjective_yoneda B S hS (yoneda.obj Z)
      (isAlgebraicSpace_yoneda B S hS Z) V (p ≫ w)).mpr hpw_surjective)
  obtain ⟨T₀, hT₀, τ, hτ_surjective, hτ_etale, t, ht⟩ :=
    exists_contains_surjective_etale_section_of_isFinite B (G.obj U) U.left.2 π fₛ
  let τB : B.inclusion.obj (B.obj hT₀) ⟶ B.inclusion.obj U.left := τ
  let T : BigFppfOver B S hS := Over.mk (B.inclusion.preimage τB ≫ U.hom)
  let r : T ⟶ U := Over.homMk (B.inclusion.preimage τB) rfl
  have hr : G.map r = τ := B.inclusion.map_preimage τB
  have hcond : G.map (pullback.snd r ζ) ≫ π = G.map (pullback.fst r ζ) ≫ τ := by
    rw [← hr]
    simp only [π, ← G.map_comp]
    exact congrArg G.map (pullback.condition (f := r) (g := ζ)).symm
  have hm₀ : (pullback.lift (G.map (pullback.snd r ζ)) (G.map (pullback.fst r ζ)) hcond ≫ t) ≫
      G.map f = G.map (pullback.snd r ζ) := by
    rw [Category.assoc]
    change _ ≫ t ≫ fₛ = _
    rw [ht]
    exact pullback.lift_fst _ _ _
  obtain ⟨m, -, hmf⟩ := BigFppfOver.exists_map_of_toScheme_map_over B S hS f (pullback.snd r ζ)
    (pullback.lift (G.map (pullback.snd r ζ)) (G.map (pullback.fst r ζ)) hcond ≫ t) hm₀
  have hP : IsPullback (yoneda.map (pullback.fst r ζ)) (yoneda.map (pullback.snd r ζ))
      (yoneda.map r) (yoneda.map ζ) := (IsPullback.of_hasPullback r ζ).map yoneda
  refine ⟨T, r, by rwa [hr], by rwa [hr],
    hP.lift (pullback.fst (yoneda.map r) (yoneda.map ζ))
      (pullback.snd (yoneda.map r) (yoneda.map ζ)) pullback.condition ≫ yoneda.map m ≫ p, ?_⟩
  rw [Category.assoc, Category.assoc, ← hf, ← yoneda.map_comp, hmf]
  exact hP.lift_snd _ _ _

end AlgebraicGeometry

end
