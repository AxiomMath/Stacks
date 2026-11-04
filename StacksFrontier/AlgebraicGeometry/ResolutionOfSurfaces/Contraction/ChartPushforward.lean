module

public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleTransport.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleQuotients.Basic

/-!
# Direct images and ampleness over the charts of a scheme

Two transport statements used to build and test an invertible module on a scheme assembled from
open charts, as in the proof of [Stacks, Tag 0C2N].

* `AlgebraicGeometry.Scheme.Modules.nonempty_restrict_pushforward_iso`: if `b : X ⟶ X'`
  restricts, over the image of an open immersion `j : V' ⟶ X'`, to `c : U ⟶ V'` with
  `U = b⁻¹(j(V'))`, then the restriction of `b_* F` along `j` is `c_*(F|_U)`. This is
  `Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso` with the open subscheme
  `j(V')` replaced by the chart `j` itself.
* `AlgebraicGeometry.Scheme.Modules.isAmple_pullback_of_range_eq`: ampleness of the restriction
  of an invertible module to an open subscheme may be read through any open immersion with the
  same image.

## References

* [Stacks Project, Tag 0C2N](https://stacks.math.columbia.edu/tag/0C2N)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **The direct image along a morphism, restricted to a chart of the target.** Let
`b : X ⟶ X'`, let `j : V' ⟶ X'` be an open immersion and `U ⊆ X` the open `b⁻¹(j(V'))`, and let
`c : U ⟶ V'` be the morphism through which `b` restricts, `U.ι ≫ b = c ≫ j`. Then for every
`𝒪_X`-module `F` the restriction of `b_* F` along `j` is `c_* (F|_U)`. -/
theorem nonempty_restrict_pushforward_iso {X X' V' : Scheme.{u}} (b : X ⟶ X') (U₀ : X.Opens)
    (c : U₀.toScheme ⟶ V') (j : V' ⟶ X') [IsOpenImmersion j] (hjc : U₀.ι ≫ b = c ≫ j)
    (hpre : b ⁻¹ᵁ j.opensRange = U₀) (F : X.Modules) :
    Nonempty (((pushforward b).obj F).restrict j ≅ (pushforward c).obj (F.restrict U₀.ι)) := by
  set R := j.opensRange
  let e₁ : (b ⁻¹ᵁ R).toScheme ≅ U₀.toScheme := X.isoOfEq hpre
  let φ : V' ≅ R.toScheme := j.isoOpensRange
  have hres : b ∣_ R = e₁.hom ≫ c ≫ φ.hom := by
    rw [← cancel_mono R.ι, morphismRestrict_ι, Category.assoc, Category.assoc,
      Scheme.Hom.isoOpensRange_hom_ι, ← hjc, ← Category.assoc, Scheme.isoOfEq_hom_ι]
  have hj : j = φ.hom ≫ R.ι := (Scheme.Hom.isoOpensRange_hom_ι j).symm
  let N : (b ⁻¹ᵁ R).toScheme.Modules := F.restrict (b ⁻¹ᵁ R).ι
  have i₁ : ((pushforward b).obj F).restrict j ≅
      (((pushforward b).obj F).restrict R.ι).restrict φ.hom :=
    (restrictFunctorCongr hj).app _ ≪≫ (restrictFunctorComp φ.hom R.ι).app _
  have i₂ : ((pushforward b).obj F).restrict R.ι ≅ (pushforward (b ∣_ R)).obj N :=
    (Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso b R).app F
  have i₃ : (pushforward (b ∣_ R)).obj N ≅
      (pushforward φ.hom).obj ((pushforward c).obj ((pushforward e₁.hom).obj N)) :=
    (pushforwardCongr hres).app N ≪≫ ((pushforwardComp e₁.hom (c ≫ φ.hom)).app N).symm ≪≫
      ((pushforwardComp c φ.hom).app _).symm
  have i₄ : ((pushforward φ.hom).obj ((pushforward c).obj ((pushforward e₁.hom).obj N))).restrict
      φ.hom ≅ (pushforward c).obj ((pushforward e₁.hom).obj N) :=
    (restrictFunctorAdjCounitIso φ.hom).app _
  have i₅ : (pushforward e₁.hom).obj N ≅ F.restrict U₀.ι := by
    have k₁ : (pushforward e₁.inv).obj ((pushforward e₁.hom).obj N) ≅ N :=
      (pushforwardComp e₁.hom e₁.inv).app N ≪≫ (pushforwardCongr e₁.hom_inv_id).app N ≪≫
        (pushforwardId _).app N
    have k₂ : N.restrict e₁.inv ≅ (pushforward e₁.hom).obj N :=
      ((restrictFunctor e₁.inv).mapIso k₁).symm ≪≫ (restrictFunctorAdjCounitIso e₁.inv).app _
    exact k₂.symm ≪≫ ((restrictFunctorComp e₁.inv (b ⁻¹ᵁ R).ι).app F).symm ≪≫
      (restrictFunctorCongr (Scheme.isoOfEq_inv_ι X hpre)).app F
  exact ⟨i₁ ≪≫ (restrictFunctor φ.hom).mapIso (i₂ ≪≫ i₃) ≪≫ i₄ ≪≫ (pushforward c).mapIso i₅⟩

variable {A B Z : Scheme.{u}}

/-- The pullback of an invertible module along a morphism of schemes is invertible, in the
spelling `Stacks.Ample.IsInvertibleModule` that ampleness is stated with. -/
theorem isInvertibleModule_pullback_obj (g : A ⟶ Z) (F : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z F] :
    Stacks.Ample.IsInvertibleModule A ((pullback g).obj F) :=
  have : Stacks.SheafOfModules.IsInvertible Z.presheaf Z.ringCatSheaf.2 F :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ ‹_›
  (Stacks.ProjectiveBundleQuotients.isInvertible_pullback_obj g F).toAlgebraicGeometry

/-- **Ampleness read through two open immersions with the same image.** If `p : A ⟶ Z` and
`q : B ⟶ Z` are open immersions with the same image, an invertible `𝒪_Z`-module pulls back to an
ample module along `p` as soon as it does along `q`: the two pullbacks are identified along the
isomorphism `A ≅ B` over `Z`. -/
theorem isAmple_pullback_of_range_eq (p : A ⟶ Z) (q : B ⟶ Z) [IsOpenImmersion p]
    [IsOpenImmersion q] (h : Set.range p.base = Set.range q.base) (F : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z F]
    (hq : haveI := isInvertibleModule_pullback_obj q F; IsAmple B ((pullback q).obj F)) :
    haveI := isInvertibleModule_pullback_obj p F; IsAmple A ((pullback p).obj F) := by
  have := isInvertibleModule_pullback_obj q F
  have := isInvertibleModule_pullback_obj p F
  let φ := IsOpenImmersion.isoOfRangeEq p q h
  have := isInvertibleModule_pullback_obj φ.hom ((pullback q).obj F)
  have e : (pullback φ.hom).obj ((pullback q).obj F) ≅ (pullback p).obj F :=
    (pullbackComp φ.hom q).app F ≪≫
      (pullbackCongr (IsOpenImmersion.isoOfRangeEq_hom_fac p q h)).app F
  exact isAmple_of_iso e (isAmple_pullback_of_isIso φ.hom _ hq)

end AlgebraicGeometry.Scheme.Modules

end
