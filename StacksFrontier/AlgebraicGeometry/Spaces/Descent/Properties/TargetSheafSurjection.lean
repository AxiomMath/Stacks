module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringSieveStepOne
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFpqcLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFppfCovering
public import StacksFrontier.CategoryTheory.MorphismProperty.BaseChangeCommSquare
public import StacksFrontier.CategoryTheory.Sites.LocallySurjectiveBaseChange

/-!
# Descent at the target along a surjection of fppf sheaves

Let `ψ : B' ⟶ B` be a morphism of algebraic spaces over `S` which is surjective as a map of
fppf sheaves. A morphism `q : G ⟶ B` whose base change along `ψ` is flat, or locally of finite
presentation, has that property itself.

This is the half of fppf descent at the target that
`StacksFrontier.AlgebraicGeometry.Spaces.Descent.Properties.MorphismFiniteness` does not cover:
**Stacks 06NR** descends a property from a *composite* `f ≫ g` to its second factor when `f` is
a surjection of fppf sheaves, which says nothing about a base change whose base map is only a
sheaf surjection and not itself flat. The two together are what the proof of the converse half
of **Stacks 06PL** uses, in that order.

A sheaf surjection is not an fppf covering, so the locality statements of **Stacks 041W** and
**Stacks 041T** do not apply to `ψ` directly. What local surjectivity does give is that `B` is
covered, fppf-locally, by objects that factor through `B'`: a surjective étale scheme atlas
`U ⟶ B` is a section of `B` over `U`, and local surjectivity refines `U` by a covering family of
the site whose members lift to `B'`. Composing that family with the atlas is an fppf covering of
`B` in the sense of **Stacks 03Y8** every member of which factors through `ψ`, which is exactly
the covering the source's proof chooses, and now Stacks 041W and Stacks 041T do apply.

## Main results

* `AlgebraicGeometry.Space.exists_fppfCovering_factorization_of_locallySurjective`: the fppf
  covering of the target all of whose members factor through a sheaf surjection.
* `AlgebraicGeometry.Space.holdsAtTarget_of_isPullback_of_locallySurjective`: the descent, for an
  arbitrary property of morphisms of algebraic spaces which is stable under base change and local
  at the target for the fppf precoverage of **Stacks 03YH**.
* `AlgebraicGeometry.Space.isFlat_of_isPullback_of_locallySurjective` and
  `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_isPullback_of_locallySurjective`: the
  two instances, stated for morphisms of presheaves, which is the shape in which flatness
  (**Stacks 03ML**) and local finite presentation (**Stacks 03XP**) of morphisms of algebraic
  spaces are used.

## Implementation notes

The covering family is indexed by `Σ _ : PUnit, E.I₀` because it is produced by
`AlgebraicGeometry.Space.isFppfCovering_comp` out of the one-member atlas family and the
refining family `E` of the site, and that is the index type of a composite of two families. The
existential statement hands back the factorisations through `ψ` rather than the members
`V i ⟶ B`, so that the covering morphisms are *syntactically* `k i ≫ ψ`; stating it with both
and an equation between them would leave a rewrite under the `HasPullback` instance argument of
`CategoryTheory.Limits.pullback.snd`, whose motive is not type correct.

Nothing here is given a Stacks tag. The source carries out this descent inline, inside the proof
of Stacks 06PL, and does not state it; the statements it does cite — Stacks 06NR, Stacks 041W and
Stacks 041T — are all already in the library, and are used below.

## References

* [Stacks Project, Tag 03Y8](https://stacks.math.columbia.edu/tag/03Y8)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 041T](https://stacks.math.columbia.edu/tag/041T)
* [Stacks Project, Tag 041W](https://stacks.math.columbia.edu/tag/041W)
* [Stacks Project, Tag 06NR](https://stacks.math.columbia.edu/tag/06NR)
* [Stacks Project, Tag 06PL](https://stacks.math.columbia.edu/tag/06PL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- An fppf covering of an algebraic space over `S`, every member of which factors through a
given morphism which is surjective as a map of fppf sheaves.

A surjective étale scheme atlas `U ⟶ B` is a section of `B` over the object `U` of the site;
local surjectivity of `ψ` refines `U` by a covering family of the site every member of which
carries a lift of that section to `B'`, and the composite of the two families is the covering.
Its members are `k i ≫ ψ` on the nose. -/
theorem exists_fppfCovering_factorization_of_locallySurjective
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B B' : AlgebraicSpaces C S hS} (ψ : B' ⟶ B)
    (hψ : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) ψ.hom) :
    ∃ (I : Type (u + 1)) (V : I → AlgebraicSpaces C S hS) (k : ∀ i, V i ⟶ B'),
      Presieve.ofArrows V (fun i => k i ≫ ψ) ∈
        Topology.fppf.precoverage.{u, u + 1} C S hS B := by
  obtain ⟨U, p, hpSurj, hpEtale⟩ := B.property.exists_atlas
  let aElem : B.obj.obj (Opposite.op U) := yonedaEquiv p
  obtain ⟨E, hE, hEimage⟩ :=
    BigFppfOver.exists_isCovering_of_mem_topology C S hS (hψ.imageSieve_mem aElem)
  choose xiElem hxi using hEimage
  let xi : (i : E.I₀) → yoneda.obj (E.X i) ⟶ B'.obj :=
    fun i => (yonedaEquiv (X := E.X i) (F := B'.obj)).symm (xiElem i)
  have htri (i : E.I₀) : yoneda.map (E.f i) ≫ p = xi i ≫ ψ.hom := by
    apply (yonedaEquiv (X := E.X i) (F := B.obj)).injective
    rw [← yonedaEquiv_naturality p (E.f i), yonedaEquiv_comp]
    simpa [aElem, xi] using (hxi i).symm
  obtain ⟨hsurjE, hgeomE⟩ :=
    BigFppfSite.jointlySurjective_flat_locallyOfFinitePresentation_of_isCovering C hE
  have hcovE : IsFppfCovering C S hS (fun i => yoneda.obj (E.X i))
      (fun i => yoneda.map (E.f i)) :=
    isFppfCovering_yoneda_map C S hS E.X E.f (fun i => (hgeomE i).1) (fun i => (hgeomE i).2)
      hsurjE
  have hcovAtlas : IsFppfCovering C S hS (fun _ : PUnit.{u + 2} => yoneda.obj U)
      (fun _ => p) :=
    isFppfCovering_atlas.{u, u + 1} C S hS B.property hpSurj hpEtale
  have hcomp := isFppfCovering_comp C S hS (X := B.obj) PUnit.{u + 2}
    (fun _ => E.I₀) (fun _ => yoneda.obj U) (fun _ i => yoneda.obj (E.X i))
    (fun _ => p) (fun _ i => yoneda.map (E.f i)) hcovAtlas (fun _ => hcovE)
  refine ⟨Σ _ : PUnit.{u + 2}, E.I₀,
    fun j => ⟨yoneda.obj (E.X j.2), isAlgebraicSpace_yoneda C S hS (E.X j.2)⟩,
    fun j => ObjectProperty.homMk (xi j.2), _, _, _, rfl,
    B.property, fun j => isAlgebraicSpace_yoneda C S hS (E.X j.2), ?_⟩
  have hfun : (fun j : Σ _ : PUnit.{u + 2}, E.I₀ => yoneda.map (E.f j.2) ≫ p) =
      (fun j : Σ _ : PUnit.{u + 2}, E.I₀ => xi j.2 ≫ ψ.hom) :=
    funext fun j => htri j.2
  rwa [hfun] at hcomp

/-- **Descent at the target along a surjection of fppf sheaves.** Let `ψ : B' ⟶ B` be a morphism
of algebraic spaces over `S` which is surjective as a map of fppf sheaves, and let `q : G ⟶ B` be
a morphism whose base change along `ψ` is the left edge `pB` of a cartesian square. Any property
of morphisms of algebraic spaces over `S` which is stable under base change and local at the
target for the fppf precoverage of **Stacks 03YH** holds for `q` as soon as it holds for `pB`.

The covering of `B` by members factoring through `ψ` is
`AlgebraicGeometry.Space.exists_fppfCovering_factorization_of_locallySurjective`; over the member
`k i ≫ ψ` the base change of `q` is the base change along `k i` of the base change along `ψ`, by
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`. -/
theorem holdsAtTarget_of_isPullback_of_locallySurjective
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (Q : MorphismProperty (AlgebraicSpaces C S hS))
    [Q.IsStableUnderBaseChange]
    [Q.IsLocalAtTarget (Topology.fppf.precoverage.{u, u + 1} C S hS)]
    {B G B' P : AlgebraicSpaces C S hS} {q : G ⟶ B} {ψ : B' ⟶ B}
    {pG : P ⟶ G} {pB : P ⟶ B'} (hsq : IsPullback pG pB q ψ)
    (hψ : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) ψ.hom)
    (hbc : Q pB) : Q q := by
  obtain ⟨I, V, k, hmem⟩ := exists_fppfCovering_factorization_of_locallySurjective C S hS ψ hψ
  have hsnd : Q (pullback.snd q ψ) :=
    (Q.cancel_left_of_respectsIso hsq.isoPullback.hom _).mp (by rwa [hsq.isoPullback_hom_snd])
  refine MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd hmem ?_
  rintro _ _ _ ⟨i⟩
  apply (Q.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso q ψ (k i)).hom _).mp
  simpa only [pullbackLeftPullbackSndIso_hom_snd] using
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := Q)
      (IsPullback.of_hasPullback (pullback.snd q ψ) (k i)) hsnd

/-- `AlgebraicGeometry.Space.holdsAtTarget_of_isPullback_of_locallySurjective` for a pullback
square of the underlying presheaves. -/
private theorem holdsAtTarget_of_isPullback_of_locallySurjective_of_map
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    (Q : MorphismProperty (AlgebraicSpaces C S hS))
    [Q.IsStableUnderBaseChange]
    [Q.IsLocalAtTarget (Topology.fppf.precoverage.{u, u + 1} C S hS)]
    {B G B' P : AlgebraicSpaces C S hS} {q : G.obj ⟶ B.obj} {ψ : B'.obj ⟶ B.obj}
    {pG : P.obj ⟶ G.obj} {pB : P.obj ⟶ B'.obj} (hsq : IsPullback pG pB q ψ)
    (hψ : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) ψ)
    (hbc : Q (ObjectProperty.homMk pB)) : Q (ObjectProperty.homMk q) :=
  holdsAtTarget_of_isPullback_of_locallySurjective C S hS Q
    (IsPullback.of_map_of_faithful (ObjectProperty.ι _) hsq) hψ hbc

/-- Flatness of a morphism of algebraic spaces over `S` descends along a base change whose base
morphism is surjective as a map of fppf sheaves. This is
`AlgebraicGeometry.Space.holdsAtTarget_of_isPullback_of_locallySurjective` at flatness, which is
local at the target for the fpqc precoverage by **Stacks 041W** and hence for the fppf one. -/
theorem isFlat_of_isPullback_of_locallySurjective
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B G B' P : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hB : IsAlgebraicSpace C S hS B) (hG : IsAlgebraicSpace C S hS G)
    (hB' : IsAlgebraicSpace C S hS B') (hP : IsAlgebraicSpace C S hS P)
    {q : G ⟶ B} {ψ : B' ⟶ B} {pG : P ⟶ G} {pB : P ⟶ B'}
    (hsq : IsPullback pG pB q ψ)
    (hψ : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) ψ)
    (hbc : IsFlat C S hS pB) : IsFlat C S hS q := by
  let Q : MorphismProperty (AlgebraicSpaces C S hS) :=
    fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) => IsFlat C S hS f.hom
  let _ : Q.IsStableUnderBaseChange := isFlat_isStableUnderBaseChange C S hS
  let _ : Q.IsLocalAtTarget (Topology.fppf.precoverage.{u, u + 1} C S hS) :=
    MorphismProperty.IsLocalAtTarget.of_le (fppfPrecoverage_le_fpqcPrecoverage C S hS)
  exact holdsAtTarget_of_isPullback_of_locallySurjective_of_map C S hS Q
    (B := ⟨B, hB⟩) (G := ⟨G, hG⟩) (B' := ⟨B', hB'⟩) (P := ⟨P, hP⟩) hsq hψ hbc

/-- Local finite presentation of a morphism of algebraic spaces over `S` descends along a base
change whose base morphism is surjective as a map of fppf sheaves. This is
`AlgebraicGeometry.Space.holdsAtTarget_of_isPullback_of_locallySurjective` at local finite
presentation, which is local at the target for the fpqc precoverage by **Stacks 041T** and hence
for the fppf one. -/
theorem isLocallyOfFinitePresentation_of_isPullback_of_locallySurjective
    (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
    {B G B' P : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    (hB : IsAlgebraicSpace C S hS B) (hG : IsAlgebraicSpace C S hS G)
    (hB' : IsAlgebraicSpace C S hS B') (hP : IsAlgebraicSpace C S hS P)
    {q : G ⟶ B} {ψ : B' ⟶ B} {pG : P ⟶ G} {pB : P ⟶ B'}
    (hsq : IsPullback pG pB q ψ)
    (hψ : Presheaf.IsLocallySurjective (BigFppfOver.topology C S hS) ψ)
    (hbc : IsLocallyOfFinitePresentation C S hS pB) :
    IsLocallyOfFinitePresentation C S hS q := by
  let Q : MorphismProperty (AlgebraicSpaces C S hS) :=
    fun ⦃X Y : AlgebraicSpaces C S hS⦄ (f : X ⟶ Y) =>
      IsLocallyOfFinitePresentation C S hS f.hom
  let _ : Q.IsStableUnderBaseChange := isLocallyOfFinitePresentation_isStableUnderBaseChange C S hS
  let _ : Q.IsLocalAtTarget (Topology.fppf.precoverage.{u, u + 1} C S hS) :=
    isLocallyOfFinitePresentation_isLocalAtTarget_fppf C S hS
  exact holdsAtTarget_of_isPullback_of_locallySurjective_of_map C S hS Q
    (B := ⟨B, hB⟩) (G := ⟨G, hG⟩) (B' := ⟨B', hB'⟩) (P := ⟨P, hP⟩) hsq hψ hbc

end AlgebraicGeometry.Space

end
