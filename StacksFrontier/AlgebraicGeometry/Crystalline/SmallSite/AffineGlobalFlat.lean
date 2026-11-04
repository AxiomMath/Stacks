module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.AffineGlobalConnected
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChaoticHigherDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.LowerShriekExactnessFlat

/-!
# The inclusion of the chaotic subsite is representably flat

Fix a global crystalline situation `(p, (S, I, γ), X)` with `X` and `S` affine, and let
`u = wholeToAffineSubsite : 𝒞 ⥤ AffineCris(X/S)` be the inclusion of the chaotic subsite of
thickenings of the whole of `X`. The comma categories `I^u_{(U,T,δ)}` are cofiltered, so `u` is
representably flat and the restriction `(-)|_𝒞` of abelian sheaves to `𝒞` preserves injective
objects.

## Main results

All declarations are in the namespace `Crystalline.GlobalCrystallineSituation`.

* `SmallSite.exists_equalizing_wholeToAffineSubsite`: given two morphisms `f, g : T₁ ⟶ T₂` of
  `𝒞` and a morphism `b : (U, T, δ) ⟶ T₁` out of an affine object with `b ≫ f = b ≫ g`, there is
  an object `T₃` of `𝒞`, a morphism `q : T₃ ⟶ T₁` with `q ≫ f = q ≫ g`, and a morphism
  `c : (U, T, δ) ⟶ T₃` with `c ≫ q = b`.
* `SmallSite.isCofiltered_structuredArrow_wholeToAffineSubsite`: the comma categories
  `I^u_{(U,T,δ)}` are cofiltered.
* `SmallSite.representablyFlat_wholeToAffineSubsite`: `u` is representably flat.
* `SmallSite.preservesInjectiveObjects_restrictAffineToWhole`: the restriction `(-)|_𝒞` to the
  chaotic subsite preserves injective abelian sheaves.

## References

* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

noncomputable section

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} (hp : IsNilpotent (S.p : Γ(S.X, ⊤)))
  [IsAffine S.X] [IsAffine S.S.scheme]

include hp in
/-- Let `(U, T, δ)` be an object of `AffineCris(X/S)`, let `f, g : T₁ ⟶ T₂` be morphisms of the
chaotic subsite `𝒞`, and let `b : (U, T, δ) ⟶ T₁` be a morphism with `b ≫ f = b ≫ g`. Then there
is an object `T₃` of `𝒞`, a morphism `q : T₃ ⟶ T₁` with `q ≫ f = q ≫ g`, and a morphism
`c : (U, T, δ) ⟶ T₃` with `c ≫ q = b`. -/
theorem SmallSite.exists_equalizing_wholeToAffineSubsite
    (A : SmallSite.AffineCrystallineThickening S)
    (T₁ T₂ : SmallSite.WholeSpaceThickening S) (f g : T₁ ⟶ T₂)
    (b : A.obj.obj ⟶ (wholeToBig S).obj T₁)
    (hb : b ≫ (wholeToBig S).map f = b ≫ (wholeToBig S).map g) :
    ∃ (T₃ : SmallSite.WholeSpaceThickening S) (q : T₃ ⟶ T₁)
      (c : A.obj.obj ⟶ (wholeToBig S).obj T₃),
      c ≫ (wholeToBig S).map q = b ∧ q ≫ f = q ≫ g := by
  have := A.property.1
  have h1 : IsIso ((wholeToBig S).obj T₁).toX := T₁.property
  have h2 : IsIso ((wholeToBig S).obj T₂).toX := T₂.property
  obtain ⟨D, hD, ψ, π, hcoeq, hψ⟩ :
      ∃ (D : DividedPowerThickening.{u, u, u} (affineSituation S hp))
        (_ : Function.Bijective D.toQuotient)
        (ψ : D ⟶ wholeThickeningToAffine hp A.obj.obj)
        (π : wholeThickeningToAffine hp ((wholeToBig S).obj T₁) ⟶ D),
        wholeHomToAffine hp ((wholeToBig S).map f) ≫ π =
            wholeHomToAffine hp ((wholeToBig S).map g) ≫ π ∧
          π ≫ ψ = wholeHomToAffine hp b := by
    have hcond : wholeHomToAffine hp ((wholeToBig S).map f) ≫ wholeHomToAffine hp b =
        wholeHomToAffine hp ((wholeToBig S).map g) ≫ wholeHomToAffine hp b := by
      rw [← wholeHomToAffine_comp, ← wholeHomToAffine_comp, hb]
    have : HasCoequalizers (affineIsCrystalline hp).FullSubcategory :=
      HasNonemptyFiniteColimits.out WalkingParallelPair
    obtain ⟨ψ, hψ⟩ := Cofork.IsColimit.desc'
      (isColimitOfHasCoequalizerOfPreservesColimit (affineIsCrystalline hp).ι
        ((wholeSiteToLittleAffine hp).map f.op) ((wholeSiteToLittleAffine hp).map g.op))
      (wholeHomToAffine hp b) hcond
    refine ⟨_, (coequalizer ((wholeSiteToLittleAffine hp).map f.op)
      ((wholeSiteToLittleAffine hp).map g.op)).property, ψ, _, ?_, hψ⟩
    exact (affineIsCrystalline hp).ι.congr_map (coequalizer.condition _ _)
  have hiso : IsIso (specThickeningOfAffine hp D).toX := isIso_specToX hp D hD
  have h3 : IsIso ((wholeToBig S).obj (specWholeSpaceThickening hp D hD)).toX := hiso
  obtain ⟨q, hq⟩ := exists_hom_of_affineHom hp (specWholeSpaceThickening hp D hD) T₁
    (π ≫ (wholeThickeningToAffineSpecIso hp D).inv)
  have hc : wholeHomToAffine hp
      (homOfAffineHom hp A.obj.obj D ψ hD :
        A.obj.obj ⟶ (wholeToBig S).obj (specWholeSpaceThickening hp D hD)) =
      (wholeThickeningToAffineSpecIso hp D).hom ≫ ψ :=
    wholeHomToAffine_homOfAffineHom hp A.obj.obj D ψ hD
  refine ⟨specWholeSpaceThickening hp D hD, q, homOfAffineHom hp A.obj.obj D ψ hD, ?_, ?_⟩
  · exact comp_eq_of_wholeHomToAffine hp A.obj.obj (specWholeSpaceThickening hp D hD) T₁ D
      (wholeThickeningToAffineSpecIso hp D) ψ _ hc π b hψ q hq
  · refine (wholeToBig S).map_injective (wholeHomToAffine_injective hp ?_)
    rw [(wholeToBig S).map_comp, (wholeToBig S).map_comp,
      wholeHomToAffine_comp, wholeHomToAffine_comp, hq]
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (wholeThickeningToAffineSpecIso hp D).inv) hcoeq).trans
        (Category.assoc _ _ _))

include hp in
/-- For every object `(U, T, δ)` of `AffineCris(X/S)`, the comma category `I^u_{(U,T,δ)}` of the
inclusion `u : 𝒞 ⥤ AffineCris(X/S)`, of pairs `(T', (U, T, δ) ⟶ T')` with `T'` in `𝒞`, is
cofiltered. -/
theorem SmallSite.isCofiltered_structuredArrow_wholeToAffineSubsite
    (A : SmallSite.AffineCrystallineThickening S) :
    IsCofiltered (StructuredArrow A (SmallSite.wholeToAffineSubsite (S := S))) where
  cone_objs X Y := by
    obtain ⟨T₃, q₁, q₂, c, h₁, h₂⟩ := SmallSite.exists_refinement_wholeToAffineSubsite hp A
      X.right Y.right X.hom.hom.hom Y.hom.hom.hom
    exact ⟨StructuredArrow.mk (ObjectProperty.homMk (ObjectProperty.homMk c)),
      StructuredArrow.homMk q₁ (ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ h₁)),
      StructuredArrow.homMk q₂ (ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ h₂)),
      trivial⟩
  cone_maps {X Y} f g := by
    obtain ⟨T₃, q, c, h₁, h₂⟩ := SmallSite.exists_equalizing_wholeToAffineSubsite hp A
      X.right Y.right f.right g.right X.hom.hom.hom
      (congrArg (fun t ↦ t.hom.hom) ((StructuredArrow.w f).trans (StructuredArrow.w g).symm))
    exact ⟨StructuredArrow.mk (ObjectProperty.homMk (ObjectProperty.homMk c)),
      StructuredArrow.homMk q (ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ h₁)),
      StructuredArrow.hom_ext _ _ h₂⟩
  nonempty := by
    obtain ⟨C, ⟨hC⟩⟩ := SmallSite.exists_hom_to_wholeToAffineSubsite hp A
    exact ⟨StructuredArrow.mk hC⟩

include hp in
/-- The inclusion `𝒞 ⥤ AffineCris(X/S)` of the chaotic subsite is representably flat. -/
theorem SmallSite.representablyFlat_wholeToAffineSubsite :
    RepresentablyFlat (SmallSite.wholeToAffineSubsite (S := S)) :=
  ⟨fun A ↦ SmallSite.isCofiltered_structuredArrow_wholeToAffineSubsite hp A⟩

include hp in
/-- The restriction `(-)|_𝒞` of abelian sheaves to the chaotic subsite preserves injective
objects. -/
theorem SmallSite.preservesInjectiveObjects_restrictAffineToWhole :
    (SmallSite.restrictAffineToWhole S).PreservesInjectiveObjects :=
  have := SmallSite.representablyFlat_wholeToAffineSubsite hp
  Stacks.Sites.LowerShriek.preservesInjectiveObjects_sheafPushforward_of_representablyFlat.{u + 1}
    (SmallSite.wholeToAffineSubsite (S := S)) (SmallSite.chaoticTopology S)
    (SmallSite.affineTopology S)

end Crystalline.GlobalCrystallineSituation

end

end
