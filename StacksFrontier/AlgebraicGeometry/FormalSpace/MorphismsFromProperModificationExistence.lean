module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationAgreementOverAdicCompletion
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationCompletionAffineReduction
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationCompletionFpqcGlueing
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpectrumOfAdicCompletion
public import StacksFrontier.AlgebraicGeometry.Spaces.PrimeResidueFieldSite
public import StacksFrontier.RingTheory.AdicCompletion.NoetherianRing

/-!
# Morphisms out of an algebraic space with a proper modification: existence and Stacks 0GI3

Let `S` be a scheme, let `X` be a locally Noetherian algebraic space over `S`, let `T ⊆ |X|` be
a closed subset with complementary open subspace `U ⊆ X`, and let `f : X' ⟶ X` be a proper
morphism of algebraic spaces whose base change `f⁻¹(U) ⟶ U` is an isomorphism. For an algebraic
space `W` over `S` this file shows that every pair `(w', ŵ)` of morphisms `w' : X' ⟶ W` and
`ŵ : X_{/T} ⟶ W` inducing the same morphism `X'_{/T} ⟶ W` comes from a morphism `X ⟶ W`.
Together with the injectivity proved in
`StacksFrontier.AlgebraicGeometry.FormalSpace.MorphismsFromProperModification` this is
[Stacks, Tag 0GI3]: the comparison map
`Mor_S(X, W) ⟶ Mor_S(X', W) ×_{Mor_S(X'_{/T}, W)} Mor_S(X_{/T}, W)` is bijective.

## Main results

* `AlgebraicGeometry.Space.exists_morToModificationCompletion_eq_of_affine_chart`: the affine
  case, for `X` an affine Noetherian object of the site and `ŵ` factoring through an affine
  object `W₀` of the site lying with `X` over a common affine open of `S`.
* `AlgebraicGeometry.Space.exists_morToModificationCompletion_eq`: the existence half.
* `AlgebraicGeometry.Space.morToModificationCompletion_codRestrict_bijective`: **Stacks 0GI3**.

## Implementation notes

*The route.* The source proves existence with the coequalizers of Stacks 0AGG and the
essential constancy of Stacks 0AGK, neither of which is available here unconditionally. The
proof here is by fpqc glueing instead. Existence is étale local on `X`
(`AlgebraicGeometry.Space.exists_morToModificationCompletion_eq_of_forall_affine`, using the
uniqueness of Stacks 0GI1), which reduces it to the affine case: `X = Spec A` with `A`
Noetherian and `ŵ` factoring through an affine `W₀ = Spec C`. There, with `I ⊆ A` an ideal
cutting out `T` (`AlgebraicGeometry.Space.exists_ideal_mem_iff_mem_zeroLocus`) and `Â` the
`I`-adic completion:

* the ring maps `C ⟶ A / Iⁿ` given by `ŵ` define `h : Spec Â ⟶ W` inducing `ŵ`
  (`AlgebraicGeometry.Space.exists_adicCompletionObj_hom_app_eq`);
* `h` agrees with `w'` on `X' ×_X Spec Â`
  (`AlgebraicGeometry.Space.comp_eq_comp_of_isProper_of_adicCompletionObj`, which uses that `Â`
  is `I`-adically complete and `X'` is proper);
* `h` satisfies the cocycle condition on `Spec (Â ⊗_A Â)`
  (`AlgebraicGeometry.Space.yoneda_map_comp_eq_of_comp_eq_of_flat_spectrum`, from the flatness
  of `Â` over the Noetherian ring `A`);
* `h` and the morphism `U ≅ f⁻¹(U) ⟶ W` glue along the fpqc covering `{U ⟶ X, Spec Â ⟶ X}`
  (`AlgebraicGeometry.Space.exists_morToModificationCompletion_eq_of_flat_cover`, using that `W`
  is an fpqc sheaf, Stacks 0APL).

*The statement.* The fibre product of the source is the set of pairs `(w', ŵ)` satisfying the
compatibility of `AlgebraicGeometry.Space.morToModificationCompletion_compatible`, and the
comparison map into it is the corestriction `Set.codRestrict` of
`AlgebraicGeometry.Space.morToModificationCompletion` to that set. The hypotheses are those of
the source: `X` locally Noetherian, `T` closed with complement the open subspace
`openSubspaceOfPoints X Tᶜ`, `f` a proper morphism of algebraic spaces with `f⁻¹(U) ⟶ U` an
isomorphism, `W` an algebraic space.

## References

* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
* [Stacks Project, Tag 0GI1](https://stacks.math.columbia.edu/tag/0GI1)
* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **The affine case of the existence half of Stacks 0GI3.** Let `V` be an affine Noetherian
object of the site and `W₀` an affine object of the site, both lying over an affine open `O` of
`S`, let `T₁` be a closed set of points of `V`, `f₁ : X'₁ ⟶ V` a proper morphism of algebraic
spaces which is an isomorphism over the complement of `T₁`, and let `w'₁ : X'₁ ⟶ W` and
`ŵ₀ : V_{/T₁} ⟶ W₀` be such that `w'₁` and `π ∘ ŵ₀` induce the same morphism `X'₁_{/T₁} ⟶ W`,
for a morphism `π : W₀ ⟶ W` to an algebraic space. Then some `w₁ : V ⟶ W` restricts to `w'₁` on
`X'₁` and to `π ∘ ŵ₀` on `V_{/T₁}`. -/
theorem exists_morToModificationCompletion_eq_of_affine_chart
    {W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hW : IsAlgebraicSpace B S hS W)
    (V W₀ : BigFppfOver B S hS) (O : S.Opens) (hO : IsAffineOpen O)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj V)]
    [AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj W₀)]
    (hVO : Set.range (B.inclusion.map V.hom).base ⊆ (O : Set S))
    (hWO : Set.range (B.inclusion.map W₀.hom).base ⊆ (O : Set S))
    {X'₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX'₁ : IsAlgebraicSpace B S hS X'₁)
    {T₁ : Set (points B S hS (yoneda.obj V))} (hT₁ : IsClosed T₁)
    (f₁ : X'₁ ⟶ yoneda.obj V) (hf₁ : IsProper B S hS f₁)
    (hfU₁ : IsIso (pullback.snd f₁ (openSubspaceOfPoints B S hS (yoneda.obj V) T₁ᶜ).ι))
    (π : yoneda.obj W₀ ⟶ W) (w'₁ : X'₁ ⟶ W)
    (ŵ₀ : (completionSubfunctor B S hS (yoneda.obj V) T₁).toFunctor ⟶
      yoneda.obj W₀ ⋙ uliftFunctor.{u + 1})
    (hcompat : completionMap B S hS f₁ T₁ ≫ ŵ₀ ≫ Functor.whiskerRight π uliftFunctor.{u + 1} =
      (completionSubfunctor B S hS X'₁ (pointsMap B S hS X'₁ f₁ ⁻¹' T₁)).ι ≫
        Functor.whiskerRight w'₁ uliftFunctor.{u + 1}) :
    ∃ w₁ : yoneda.obj V ⟶ W, morToModificationCompletion B S hS f₁ T₁ W w₁ =
      (w'₁, ŵ₀ ≫ Functor.whiskerRight π uliftFunctor.{u + 1}) := by
  have : IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj V, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩
  obtain ⟨I, hTI⟩ := exists_ideal_mem_iff_mem_zeroLocus B S hS V hT₁
  obtain ⟨h, hh⟩ := exists_adicCompletionObj_hom_app_eq B S hS V W₀ I hTI O hO hVO hWO π ŵ₀
  have hX'h : ∀ {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g₁ : Z ⟶ X'₁)
      (g₂ : Z ⟶ yoneda.obj (adicCompletionObj B S hS V I)),
      g₁ ≫ f₁ = g₂ ≫ yoneda.map (adicCompletionObjHom B S hS V I) → g₁ ≫ w'₁ = g₂ ≫ h :=
    fun g₁ g₂ hg => comp_eq_comp_of_isProper_of_adicCompletionObj B S hS hX'₁ hW V I hTI f₁ hf₁
      w'₁ _ hcompat h hh g₁ g₂ hg
  have hκ := toScheme_map_adicCompletionObjHom B S hS V I
  have hÂ : B.Contains (Spec (.of (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤)))) :=
    (adicCompletionObj B S hS V I).left.2
  refine exists_morToModificationCompletion_eq_of_flat_cover B S hS hW V hT₁ f₁ hfU₁ w'₁ _ hcompat
    (adicCompletionObjHom B S hS V I) ?_ ?_ ?_ h hh hX'h ?_
  · rw [hκ]
    exact flat_specAdicCompletion _ I
  · rw [hκ]
    exact quasiCompact_specAdicCompletion _ I
  · intro x hx
    rw [hκ]
    exact zeroLocus_subset_range_specAdicCompletion _ I ((hTI x).mp hx)
  · intro Zo z₁ z₂ hz
    exact yoneda_map_comp_eq_of_comp_eq_of_flat_spectrum B S hS hX'₁ hW V I hTI f₁ hf₁ hfU₁ w'₁ _
      (adicCompletionObjHom B S hS V I)
      (Iso.refl _ : _ ≅ Spec (.of (AdicCompletion I Γ((BigFppfOver.toScheme B S hS).obj V, ⊤))))
      (by rw [hκ]; exact (Category.id_comp _).symm)
      (BigFppfSite.contains_spec_tensorProduct B hÂ hÂ) h hh hX'h Zo z₁ z₂ hz

/-- **The existence half of Stacks 0GI3.** Let `X` be a locally Noetherian algebraic space over
`S`, `T ⊆ |X|` a closed subset with complementary open subspace `U`, `f : X' ⟶ X` a proper
morphism of algebraic spaces with `f⁻¹(U) ⟶ U` an isomorphism, and `W` an algebraic space over
`S`. If `w' : X' ⟶ W` and `ŵ : X_{/T} ⟶ W` induce the same morphism `X'_{/T} ⟶ W`, then some
`w : X ⟶ W` restricts to `w'` on `X'` and induces `ŵ` on `X_{/T}`. -/
theorem exists_morToModificationCompletion_eq
    {X' X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hW : IsAlgebraicSpace B S hS W)
    (hXnoeth : HasEtaleLocalProperty B S hS X (fun V : Scheme.{u} => IsLocallyNoetherian V))
    {T : Set (points B S hS X)} (hT : IsClosed T)
    (f : X' ⟶ X) (hfproper : IsProper B S hS f)
    (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι))
    (w' : X' ⟶ W)
    (ŵ : (completionSubfunctor B S hS X T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    (hcompat : completionMap B S hS f T ≫ ŵ =
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).ι ≫
        Functor.whiskerRight w' uliftFunctor.{u + 1}) :
    ∃ w : X ⟶ W, morToModificationCompletion B S hS f T W w = (w', ŵ) :=
  exists_morToModificationCompletion_eq_of_forall_affine B S hS hX hX' hW hXnoeth hT f hfproper
    hfU (fun V W₀ O hO hVa hVn hW₀a hVO hWO X'₁ hX'₁ T₁ hT₁ f₁ hf₁ hfU₁ π w'₁ ŵ₀ hc => by
      have := hVa
      have := hVn
      have := hW₀a
      exact exists_morToModificationCompletion_eq_of_affine_chart B S hS hW V W₀ O hO hVO hWO
        hX'₁ hT₁ f₁ hf₁ hfU₁ π w'₁ ŵ₀ hc)
    w' ŵ hcompat

/-- **Stacks 0GI3.** Let `S` be a scheme, `X` a locally Noetherian algebraic space over `S`,
`T ⊆ |X|` a closed subset with complementary open subspace `U ⊆ X`, and `f : X' ⟶ X` a proper
morphism of algebraic spaces such that `f⁻¹(U) ⟶ U` is an isomorphism. For any algebraic space
`W` over `S` the map
`Mor_S(X, W) ⟶ Mor_S(X', W) ×_{Mor_S(X'_{/T}, W)} Mor_S(X_{/T}, W)`, sending `w` to its
restriction to `X'` and the morphism it induces on the completion `X_{/T}`, is bijective. -/
@[stacks 0GI3]
theorem morToModificationCompletion_codRestrict_bijective
    {X' X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hW : IsAlgebraicSpace B S hS W)
    (hXnoeth : HasEtaleLocalProperty B S hS X (fun V : Scheme.{u} => IsLocallyNoetherian V))
    {T : Set (points B S hS X)} (hT : IsClosed T)
    (f : X' ⟶ X) (hfproper : IsProper B S hS f)
    (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι)) :
    Function.Bijective (Set.codRestrict (morToModificationCompletion B S hS f T W)
      {p | completionMap B S hS f T ≫ p.2 =
        (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).ι ≫
          Functor.whiskerRight p.1 uliftFunctor.{u + 1}}
      (morToModificationCompletion_compatible B S hS f T W)) := by
  refine ⟨fun a b hab => morToModificationCompletion_injective B S hS hX hX' hW hXnoeth hT f
    hfproper hfU (congrArg Subtype.val hab), ?_⟩
  rintro ⟨⟨w', ŵ⟩, hp⟩
  obtain ⟨w, hw⟩ := exists_morToModificationCompletion_eq B S hS hX hX' hW hXnoeth hT f hfproper
    hfU w' ŵ hp
  exact ⟨w, Subtype.ext hw⟩

end Space

end AlgebraicGeometry

end
