module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductChowCover
public import StacksFrontier.AlgebraicGeometry.Spaces.CohomologyVanishingSeparatedMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SeparationAxioms
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.Scheme
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedDiagonal

/-!
# Assembling and descending an integral scheme cover

The last step of the proof of [Stacks, Tag 09YB] produces its cover of a space `Y` as a
coproduct `Z' ⨿ T` of two schemes integral over `Y` whose point sets cover `|Y|`, and then
pushes that cover along an integral surjection `Y ⟶ X`. Both halves are carried out here,
together with the two subsidiary facts the step needs about the pieces it glues: that a
subspace of a quasi-separated algebraic space is quasi-separated, and that a closed subspace
contained in a representable subfunctor is representable.

Nothing here is the tag, and nothing here is tagged.

## Main results

* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_subfunctor`: a subspace of a
  quasi-separated algebraic space over `S` is quasi-separated.
* `AlgebraicGeometry.Space.isRepresentable_of_le_of_isClosedSubspace`: a closed subspace
  contained in a representable subfunctor is representable.
* `AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_of_isIntegralHom_pair`:
  **the glueing.** Two objects of the site integral over an algebraic space whose point sets
  cover it assemble into a single surjective integral morphism from an object of the site.
* `AlgebraicGeometry.Space.existsIntegralSurjectiveSchemeCover_comp`: **the descent.** A
  surjective integral scheme cover of `Y` is one of `X` along a surjective integral
  `Y ⟶ X`.

## Implementation notes

*The glueing.* This is `AlgebraicGeometry.Space.hasChowSchemeCover_of_isProper_pair` with
integrality in place of properness and H-quasi-projectivity: the binary coproduct of the site
is read as a two-member cofan by `AlgebraicGeometry.Space.coprodPairIncl`, the representable
sheaf of that coproduct is the coproduct of the two representable sheaves by
`AlgebraicGeometry.BigFppfOver.isColimit_yoneda_cofan`, and the two morphisms assemble into
one by the universal property. Integrality of the assembled morphism is
`AlgebraicGeometry.Space.isIntegralHom_coproduct` — the integral form of Stacks 0CZ2 — and its
surjectivity is `AlgebraicGeometry.Space.isSurjective_of_iUnion_range_pointsMap_eq_univ`,
which needs no coproduct structure at all.

*The descent* is composition: integrality and surjectivity are both stable under it, by
Stacks 03ZR and Stacks 03MG.

*Quasi-separatedness of a subspace* needs only that the inclusion of a subfunctor is a
monomorphism, hence a quasi-separated morphism; openness of the subspace is used nowhere, and
the hypothesis is that the subspace is an algebraic space. The same two-line composite occurs
twice in the trees as a `private` lemma — in
`StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePointsQuasiSeparated` and in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple` — and is stated publicly
here because the inductive step of Stacks 09YB recurses into an open subspace and has to carry
quasi-separatedness across the recursion.

*Representability of a closed subspace inside a representable one* is
`AlgebraicGeometry.Space.isRepresentable_of_le_of_isRepresentable` with the closed half of
Stacks 02YX in place of the open half: the smaller subspace is a closed subspace of the larger
one, so its inclusion is relatively representable, and pulling that inclusion back along the
representing isomorphism of the larger one produces an object of the site. The inductive step
of Stacks 09YB uses it for the reduced closed complement `T = Y ∖ V`, which is closed in `Y`
— not a scheme — but contained in the image of the chart, which is one.

## References

* [Stacks Project, Tag 09YB](https://stacks.math.columbia.edu/tag/09YB)
* [Stacks Project, Tag 0CZ2](https://stacks.math.columbia.edu/tag/0CZ2)
* [Stacks Project, Tag 03ZR](https://stacks.math.columbia.edu/tag/03ZR)
* [Stacks Project, Tag 03MG](https://stacks.math.columbia.edu/tag/03MG)
* [Stacks Project, Tag 02YX](https://stacks.math.columbia.edu/tag/02YX)
* [Stacks Project, Tag 04ZH](https://stacks.math.columbia.edu/tag/04ZH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Quasi-separatedness of a subspace -/

/-- **A subspace of a quasi-separated algebraic space over `S` is quasi-separated.** The
inclusion of a subfunctor is a monomorphism, hence a quasi-separated morphism, so Stacks 04ZH
part (2) transports quasi-separatedness from the ambient space to the subspace. -/
theorem isAbsolutelyQuasiSeparated_subfunctor (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X) (V : Subfunctor X)
    (hV : IsAlgebraicSpace B S hS V.toFunctor) :
    IsAbsolutelyQuasiSeparated B S hS hZ V.toFunctor :=
  isAbsolutelyQuasiSeparated_of_isQuasiSeparated B S hS hZ hV hXqs
    (isQuasiSeparated_of_mono B S hS V.ι inferInstance)

/-! ### Representability of a closed subspace inside a representable one -/

/-- **A closed subspace contained in a representable subfunctor is representable.**

By the closed half of Stacks 02YX the smaller subspace is a closed subspace of the larger one,
so its inclusion into `L.toFunctor` is a relatively representable closed immersion. Pulling
that inclusion back along the representing isomorphism of `L.toFunctor` produces an object of
the site, and the pullback is isomorphic to the source itself because the isomorphism is
one. -/
theorem isRepresentable_of_le_of_isClosedSubspace
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {H L : Subfunctor X}
    (hH : IsClosedSubspace B S hS H) (hle : H ≤ L) (hL : L.toFunctor.IsRepresentable) :
    H.toFunctor.IsRepresentable := by
  have hmono : Mono (Subfunctor.homOfLe hle) := mono_of_mono_fac (Subfunctor.homOfLe_ι hle)
  set H' := Subfunctor.range (Subfunctor.homOfLe hle) with hH'def
  have hH' : IsClosedSubspace B S hS H' := isClosedSubspace_of_le B S hS H L hH hle
  set e := L.toFunctor.reprW with hedef
  have hpb := hH'.2.rep.isPullback e.hom
  have hiso : IsPullback (𝟙 H'.toFunctor) (H'.ι ≫ e.inv) H'.ι e.hom :=
    IsPullback.of_horiz_isIso ⟨by simp⟩
  exact Functor.IsRepresentable.mk' (hpb.isoIsPullback _ _ hiso ≪≫
    (asIso (Subfunctor.toRange (Subfunctor.homOfLe hle))).symm)

/-! ### The glueing of two integral covers -/

/-- **Two objects of the site integral over an algebraic space whose point sets cover it
assemble into one surjective integral cover.** This is the step "then `Z' ⨿ T ⟶ Y` works"
with which the inductive step of [Stacks, Tag 09YB] finishes.

The representable sheaf of the binary coproduct of the site is the coproduct of the two
representable sheaves by `AlgebraicGeometry.BigFppfOver.isColimit_yoneda_cofan`, so the two
morphisms assemble into one; that morphism is integral by
`AlgebraicGeometry.Space.isIntegralHom_coproduct` and surjective because its point map has
both given point maps as factors. -/
theorem existsIntegralSurjectiveSchemeCover_of_isIntegralHom_pair
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (X₁ X₂ : BigFppfOver B S hS) (p₁ : yoneda.obj X₁ ⟶ X) (p₂ : yoneda.obj X₂ ⟶ X)
    (hp₁ : IsIntegralHom B S hS p₁) (hp₂ : IsIntegralHom B S hS p₂)
    (hcov : ∀ x : points B S hS X,
      x ∈ Set.range (pointsMap B S hS (yoneda.obj X₁) p₁) ∪
        Set.range (pointsMap B S hS (yoneda.obj X₂) p₂)) :
    ExistsIntegralSurjectiveSchemeCover B S hS X := by
  classical
  let J := BigFppfOver.topology B S hS
  let _ : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let Xs : Sheaf J (Type u) := ⟨X, hX.isSheaf⟩
  have hV : IsColimit (Cofan.mk (X₁ ⨿ X₂) (coprodPairIncl B S hS X₁ X₂)) :=
    isColimit_cofan_coprodPair B S hS X₁ X₂
  have hY : IsColimit (Cofan.mk (J.yoneda.obj (X₁ ⨿ X₂))
      fun b => J.yoneda.map (coprodPairIncl B S hS X₁ X₂ b)) :=
    BigFppfOver.isColimit_yoneda_cofan B S hS (coprodPairObj B S hS X₁ X₂)
      (coprodPairIncl B S hS X₁ X₂) hV
  let tgt : ∀ b, J.yoneda.obj (coprodPairObj B S hS X₁ X₂ b) ⟶ Xs := fun b =>
    match b with
    | ⟨false⟩ => ⟨p₁⟩
    | ⟨true⟩ => ⟨p₂⟩
  let h : J.yoneda.obj (X₁ ⨿ X₂) ⟶ Xs := Cofan.IsColimit.desc hY tgt
  -- the two morphisms to `X`, as a family indexed by the two-member index type
  let fam : ∀ b : ULift.{u} Bool, yoneda.obj (coprodPairObj B S hS X₁ X₂ b) ⟶ X := fun b =>
    (tgt b).hom
  have hfac : ∀ b, yoneda.map (coprodPairIncl B S hS X₁ X₂ b) ≫ h.hom = fam b := fun b =>
    congrArg (fun k => k.hom) (Cofan.IsColimit.fac hY tgt b)
  refine ⟨X₁ ⨿ X₂, h.hom, ?_, ?_⟩
  · refine isSurjective_of_iUnion_range_pointsMap_eq_univ B S hS
      (fun b => yoneda.map (coprodPairIncl B S hS X₁ X₂ b)) h.hom fam hfac ?_
    refine Set.eq_univ_of_forall fun x => ?_
    rcases hcov x with hx | hx
    · exact Set.mem_iUnion.2 ⟨⟨false⟩, hx⟩
    · exact Set.mem_iUnion.2 ⟨⟨true⟩, hx⟩
  · refine isIntegralHom_coproduct B S hS
      (fun b => yoneda.obj (coprodPairObj B S hS X₁ X₂ b))
      (fun b => isAlgebraicSpace_yoneda B S hS (coprodPairObj B S hS X₁ X₂ b)) hX
      (J.yoneda.obj (X₁ ⨿ X₂))
      (fun b => J.yoneda.map (coprodPairIncl B S hS X₁ X₂ b)) hY fam h.hom hfac ?_
    rintro ⟨_ | _⟩
    exacts [hp₁, hp₂]

/-! ### The descent along an integral surjection -/

/-- **A surjective integral scheme cover descends along a surjective integral morphism.** If
`Y` has one and `π : Y ⟶ X` is surjective and integral, then `X` has one: compose.

This is the last line of the inductive step of [Stacks, Tag 09YB], where the cover of the
relative compactification `Y` is pushed to `X` along the integral `π`. -/
theorem existsIntegralSurjectiveSchemeCover_comp
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (π : Y ⟶ X)
    (hπ : IsIntegralHom B S hS π) (hπsurj : IsSurjective B S hS π)
    (h : ExistsIntegralSurjectiveSchemeCover B S hS Y) :
    ExistsIntegralSurjectiveSchemeCover B S hS X := by
  obtain ⟨W, g, hgsurj, hgint⟩ := h
  exact ⟨W, g ≫ π, isSurjective_comp B S hS hgsurj hπsurj,
    isIntegralHom_comp B S hS hgint hπ⟩

end AlgebraicGeometry.Space

end
