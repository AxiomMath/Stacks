module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.LocalOnSource.Fppf
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceFinitePart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformEtaleChartSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# Flatness of a strict transform descends along an étale cover of the source

Let `b : A' ⟶ A` be the blowup of an algebraic space `A` in a closed subspace `Z`, let
`f : X ⟶ A` be a morphism of algebraic spaces and let `u : V ⟶ X` be surjective and étale.
By part (2) of Stacks 0863 the strict transform `V'` of `V` is `X' ×_X V`, where `X'` is the
strict transform of `X`, so `V' ⟶ X'` is surjective and étale.  Flatness and local finite
presentation are local on the source in the étale topology (Stacks 06ET, 06EV), so if `V' ⟶ A'`
is flat and locally of finite presentation then so is `X' ⟶ A'`.  This is the first reduction
in the proof of Stacks 087E.

## Main results

* `isLocallyOfFinitePresentation_of_comp_of_isEtale_of_isSurjective`:
  local finite presentation descends along a surjective étale morphism of the source.
* `isFlat_and_isLocallyOfFinitePresentation_strictTransformSpaceToBlowUp_of_comp`:
  if the strict transform of `V` is flat and locally of finite presentation over `A'`, so is the
  strict transform of `X`.

## References

* [Stacks Project, Tag 087E](https://stacks.math.columbia.edu/tag/087E)
* [Stacks Project, Tag 0863](https://stacks.math.columbia.edu/tag/0863)
* [Stacks Project, Tag 06ET](https://stacks.math.columbia.edu/tag/06ET)
* [Stacks Project, Tag 06EV](https://stacks.math.columbia.edu/tag/06EV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- A morphism of algebraic spaces is locally of finite presentation as soon as its composite with
a surjective étale morphism is: local finite presentation is local on the source in the fppf
topology (Stacks 06EV), and a surjective étale morphism is an fppf covering. -/
theorem isLocallyOfFinitePresentation_of_comp_of_isEtale_of_isSurjective
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) {q : X ⟶ Y} (hq : IsEtale B S hS q)
    (hqs : IsSurjective B S hS q) {f : Y ⟶ Z}
    (hf : IsLocallyOfFinitePresentation B S hS (q ≫ f)) :
    IsLocallyOfFinitePresentation B S hS f := by
  let Xs : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Ys : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let Zs : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let P : MorphismProperty (AlgebraicSpaces B S hS) :=
    fun ⦃_ _ : AlgebraicSpaces B S hS⦄ k => IsLocallyOfFinitePresentation B S hS k.hom
  let _ : P.IsLocalAtSource (Topology.precoverage.{u, 0} .fppf B S hS) :=
    isLocallyOfFinitePresentation_isLocalAtSource_fppf.{u, 0} B S hS
  have hR : Presieve.ofArrows (fun _ : PUnit.{1} => Xs) (fun _ => (ObjectProperty.homMk q :
      Xs ⟶ Ys)) ∈ Topology.precoverage.{u, 0} .fppf B S hS Ys :=
    ⟨PUnit.{1}, _, _, rfl, hY, fun _ => hX, isFppfCovering_of_isEtaleCovering B S hS
      ⟨hY, fun _ => hX, fun _ => hq,
        Set.eq_univ_iff_forall.mpr fun y => Set.mem_iUnion.mpr ⟨⟨⟩, hqs y⟩⟩⟩
  show P (ObjectProperty.homMk f : Ys ⟶ Zs)
  exact MorphismProperty.IsLocalAtSource.of_forall_comp (P := P) hR fun _ _ ⟨_⟩ => hf

/-- The inverse image of a closed subspace along the identity is the closed subspace itself. -/
@[simp]
theorem preimageClosedSubspace_id {A : AlgebraicSpaces B S hS}
    (Z : ClosedSubspaces B S hS A.1) : preimageClosedSubspace (𝟙 A) Z = Z :=
  Subtype.ext (Subfunctor.preimage_id Z.1)

/-- The comparison map `G.fromPreimage can` of a subfunctor `G` of `Y` is surjective whenever
`can : X ⟶ Y` is, being a base change of `can`. -/
private theorem isSurjective_fromPreimage_of_isSurjective {X Y : AlgebraicSpaces B S hS}
    (can : X ⟶ Y) (G : Subfunctor Y.1) (hG : IsAlgebraicSpace B S hS G.toFunctor)
    (hGp : IsAlgebraicSpace B S hS (G.preimage can.hom).toFunctor)
    (hcan : IsSurjective B S hS can.hom) :
    IsSurjective B S hS (G.fromPreimage can.hom) := by
  let Gs : AlgebraicSpaces B S hS := ⟨G.toFunctor, hG⟩
  let Gps : AlgebraicSpaces B S hS := ⟨(G.preimage can.hom).toFunctor, hGp⟩
  have hsq : IsPullback (ObjectProperty.homMk (G.preimage can.hom).ι : Gps ⟶ X)
      (ObjectProperty.homMk (G.fromPreimage can.hom) : Gps ⟶ Gs) can
      (ObjectProperty.homMk G.ι : Gs ⟶ Y) :=
    IsPullback.of_map (ObjectProperty.ι _)
      (ObjectProperty.hom_ext _ (Subfunctor.fromPreimage_ι G can.hom).symm)
      (Subfunctor.isPullback_preimage can.hom G).flip
  exact isSurjective_of_isPullback B S hS hsq hcan

/-- **Flatness and local finite presentation of a strict transform descend along a surjective
étale morphism of the source.**  Let `b : A' ⟶ A` be the blowup of `A` in a closed subspace `Z`,
let `f : X ⟶ A` be a morphism of algebraic spaces and let `u : V ⟶ X` be surjective and étale.
If the strict transform of `V` is flat and locally of finite presentation over `A'`, then so is
the strict transform of `X`.

By part (2) of Stacks 0863, `exists_strictTransformSubfunctor_eq_preimage` at the identity of
`A`, the strict transform `V'` of `V` is the inverse image of the strict transform `X'` of `X`
along an étale morphism `V ×_A A' ⟶ X ×_A A'` which is a base change of `u`; so `V' ⟶ X'` is
surjective and étale, and the two properties descend along it (Stacks 06ET, 06EV). -/
theorem isFlat_and_isLocallyOfFinitePresentation_strictTransformSpaceToBlowUp_of_comp
    {A X V A' : AlgebraicSpaces B S hS} {Z : ClosedSubspaces B S hS A.1} {b : A' ⟶ A}
    (hb : IsBlowupAlong B S hS Z b) (f : X ⟶ A) (u : V ⟶ X) (hu : IsEtale B S hS u.hom)
    (hus : IsSurjective B S hS u.hom)
    (hflat : IsFlat B S hS
      (strictTransformSpaceToBlowUp B S hS (u ≫ f) b (Z.1.preimage b.hom)).hom)
    (hlfp : IsLocallyOfFinitePresentation B S hS
      (strictTransformSpaceToBlowUp B S hS (u ≫ f) b (Z.1.preimage b.hom)).hom) :
    IsFlat B S hS (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom ∧
      IsLocallyOfFinitePresentation B S hS
        (strictTransformSpaceToBlowUp B S hS f b (Z.1.preimage b.hom)).hom := by
  obtain ⟨m, can, hpbm, hcan, -, h2, hpb, heq⟩ :=
    exists_strictTransformSubfunctor_eq_preimage hb (v := 𝟙 A)
      (isEtale_of_isIso B S hS (𝟙 A.1) : IsEtale B S hS (show A ⟶ A from 𝟙 A).hom) hu
      (w := u ≫ f) (Category.comp_id _).symm (by rwa [preimageClosedSubspace_id])
  rw [preimageClosedSubspace_id] at heq
  change strictTransformSubfunctor B S hS (u ≫ f) b (Z.1.preimage b.hom) =
    (strictTransformSubfunctor B S hS f b (Z.1.preimage b.hom)).preimage can.hom at heq
  set G := strictTransformSubfunctor B S hS f b (Z.1.preimage b.hom) with hG
  have hGcl : IsClosedSubspace B S hS G :=
    strictTransformSubfunctor_isClosedSubspace B S hS f b _
  have hGpcl : IsClosedSubspace B S hS (G.preimage can.hom) :=
    isClosedSubspace_preimage B S hS can.hom G (strictTransformPullback B S hS f b).2
      (strictTransformPullback B S hS (u ≫ f) b).2 hGcl
  show IsFlat B S hS (G.ι ≫ (strictTransformPullbackToBlowUp B S hS f b).hom) ∧
    IsLocallyOfFinitePresentation B S hS
      (G.ι ≫ (strictTransformPullbackToBlowUp B S hS f b).hom)
  -- the morphism `m : A' ⟶ A'` of part (1) is an isomorphism, being a base change of `𝟙 A`
  have : IsIso m := hpbm.isIso_snd_of_isIso
  have : IsIso m.hom := (inferInstance : IsIso ((ObjectProperty.ι _).map m))
  -- `V' ⟶ X'` is the base change of `can` along `X' ⟶ X ×_A A'`
  have hsq := Subfunctor.isPullback_preimage can.hom G
  have hcomp : (G.preimage can.hom).ι ≫
      (strictTransformPullbackToBlowUp B S hS (u ≫ f) b).hom ≫ m.hom =
      G.fromPreimage can.hom ≫ G.ι ≫ (strictTransformPullbackToBlowUp B S hS f b).hom := by
    have h2' : can.hom ≫ (strictTransformPullbackToBlowUp B S hS f b).hom =
        (strictTransformPullbackToBlowUp B S hS (u ≫ f) b).hom ≫ m.hom :=
      congrArg (fun k => k.hom) h2
    rw [← h2', ← Category.assoc, ← Category.assoc, ← Subfunctor.fromPreimage_ι]
  have hr : IsEtale B S hS (G.fromPreimage can.hom) :=
    isEtale_of_isPullback_of_isAlgebraicSpace B S hS hsq hGpcl.1 hGcl.1
      (strictTransformPullback B S hS (u ≫ f) b).2 (strictTransformPullback B S hS f b).2 hcan
  have hrs := isSurjective_fromPreimage_of_isSurjective can G hGcl.1 hGpcl.1
    (isSurjective_of_isPullback B S hS hpb.flip hus)
  -- both properties transfer from `V' ⟶ A'` to `V' ⟶ X' ⟶ A'` along the isomorphism `m`
  have key : ∀ P : MorphismProperty Scheme.{u}, HoldsOnEveryEtaleChart B S hS P
      ((strictTransformSubfunctor B S hS (u ≫ f) b (Z.1.preimage b.hom)).ι ≫
        (strictTransformPullbackToBlowUp B S hS (u ≫ f) b).hom) →
      HoldsOnEveryEtaleChart B S hS P (G.fromPreimage can.hom ≫
        (G.ι ≫ (strictTransformPullbackToBlowUp B S hS f b).hom)) := fun P h => by
    rw [heq] at h
    rw [← hcomp]
    exact (holdsOnEveryEtaleChart_comp_iso_iff B S hS _ _ m.hom).2 h
  exact ⟨isFlat_of_comp_of_isSurjective_of_isFlat B S hS hGpcl.1 hGcl.1 _ _ hrs
      (isFlat_of_isEtale B S hS hr) (key _ hflat),
    isLocallyOfFinitePresentation_of_comp_of_isEtale_of_isSurjective hGpcl.1 hGcl.1 A'.2 hr hrs
      (key _ hlfp)⟩

end AlgebraicGeometry.Space

end
