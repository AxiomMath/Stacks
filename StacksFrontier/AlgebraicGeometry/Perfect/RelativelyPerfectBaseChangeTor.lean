module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChangeTorAffine
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseOpen
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentPerfectInduction
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOpenLocality

/-!
# Base change of relative perfectness

Let `f : X ⟶ S` be flat and locally of finite presentation, `g : S' ⟶ S` any morphism of
schemes, `X' = X ×_S S'` with projections `g' : X' ⟶ X` and `f' : X' ⟶ S'`. If `K` in `D(𝒪_X)`
is `S`-perfect then `L(g')^*K` is `S'`-perfect (Stacks 0DI5).

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_derivedPullback_pullbackFst`: Stacks 0DI5.
* `AlgebraicGeometry.RelativeDescentSituation.isPerfectRelativeTo_transition`: the transition
  maps of a relative descent situation preserve relative perfectness.

## References

* [Stacks Project, Lemma 36.35.6 (Tag 0DI5)](https://stacks.math.columbia.edu/tag/0DI5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Scheme.Hom

section Local

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
  {W : S.Opens} (hW : IsAffineOpen W) {V : X.Opens} (hV : IsAffineOpen V) (hVW : V ≤ f ⁻¹ᵁ W)
  {W' : S'.Opens} (hW' : IsAffineOpen W') (hW'W : W' ≤ g ⁻¹ᵁ W)

/-- The open immersion `V ×_W W' ⟶ X ×_S S'` attached to affine opens `V ⊆ f⁻¹W` and
`W' ⊆ g⁻¹W`. -/
abbrev pullbackAffineChart : pullback (f.resLE W V hVW) (g.resLE W W' hW'W) ⟶ pullback f g :=
  pullback.map (f.resLE W V hVW) (g.resLE W W' hW'W) f g V.ι W'.ι W.ι
    (resLE_comp_ι f hVW) (resLE_comp_ι g hW'W)

include hW hV hW' in
/-- **Base change of relative perfectness on an affine chart.** If the restriction of `K` to an
affine open `V ⊆ f⁻¹W` over an affine open `W` is `W`-perfect, then the restriction of `L(g')^*K`
to the chart `V ×_W W' ⊆ X ×_S S'` is `S'`-perfect. -/
theorem isPerfectRelativeTo_pullbackAffineChart
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hK : (f.resLE W V hVW).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback V.ι.toLRSHom.toShHom).obj K)) :
    (pullbackAffineChart f g hVW hW'W ≫ pullback.snd f g).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback (pullbackAffineChart f g hVW hW'W).toLRSHom.toShHom).obj
        ((derivedPullback (pullback.fst f g).toLRSHom.toShHom).obj K)) := by
  have : IsAffine W.toScheme := hW
  have : IsAffine V.toScheme := hV
  have : IsAffine W'.toScheme := hW'
  have hb := (isPerfectRelativeTo_baseOpen_iff (pullback.snd (f.resLE W V hVW) (g.resLE W W' hW'W))
    W'.ι (f := pullbackAffineChart f g hVW hW'W ≫ pullback.snd f g)
    (pullback.lift_snd _ _ _).symm _).2
      (isPerfectRelativeTo_derivedPullback_fst_of_isAffine _ _ _ hK)
  refine isPerfectRelativeTo_canonical_of_iso _ ?_ hb
  exact (Stacks.DerivedPullback.schemeFactorIso _ V.ι _ rfl).app K ≪≫
    ((Stacks.DerivedPullback.schemeFactorIso _ (pullback.fst f g) _
      (pullback.lift_fst _ _ _)).app K).symm

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- The chart `V ×_W W' ⟶ X ×_S S'` contains every point lying over `V` and `W'`. -/
theorem mem_range_pullbackAffineChart (x : ↥(pullback f g)) (hx₁ : pullback.fst f g x ∈ V)
    (hx₂ : pullback.snd f g x ∈ W') :
    x ∈ Set.range (pullbackAffineChart f g hVW hW'W) := by
  rw [Scheme.Pullback.range_map]
  exact ⟨by simpa using hx₁, by simpa using hx₂⟩

omit [Flat f] [LocallyOfFinitePresentation f] in
/-- **Every point of `X ×_S S'` lies on an affine chart `V ×_W W'`.** -/
theorem exists_mem_range_pullbackAffineChart (x : ↥(pullback f g)) :
    ∃ (W : S.Opens) (_ : IsAffineOpen W) (V : X.Opens) (_ : IsAffineOpen V)
      (hVW : V ≤ f ⁻¹ᵁ W) (W' : S'.Opens) (_ : IsAffineOpen W') (hW'W : W' ≤ g ⁻¹ᵁ W),
      x ∈ Set.range (pullbackAffineChart f g hVW hW'W) := by
  obtain ⟨-, ⟨W, hW, rfl⟩, hxW, -⟩ := (Scheme.isBasis_affineOpens S).exists_subset_of_mem_open
    (Set.mem_univ (f (pullback.fst f g x))) isOpen_univ
  obtain ⟨-, ⟨V, hV, rfl⟩, hxV, hVW⟩ := (Scheme.isBasis_affineOpens X).exists_subset_of_mem_open
    (show pullback.fst f g x ∈ (f ⁻¹ᵁ W : X.Opens) from hxW) (f ⁻¹ᵁ W).2
  have hgx : g (pullback.snd f g x) ∈ W := by
    rwa [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
  obtain ⟨-, ⟨W', hW', rfl⟩, hxW', hW'W⟩ :=
    (Scheme.isBasis_affineOpens S').exists_subset_of_mem_open
      (show pullback.snd f g x ∈ (g ⁻¹ᵁ W : S'.Opens) from hgx) (g ⁻¹ᵁ W).2
  exact ⟨W, hW, V, hV, hVW, W', hW', hW'W,
    mem_range_pullbackAffineChart f g hVW hW'W x hxV hxW'⟩

end Local

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme.Hom

/-- **Stacks 0DI5.** Let `f : X ⟶ S` be flat and locally of finite presentation and `g : S' ⟶ S`
any morphism. The derived pullback along `X ×_S S' ⟶ X` of an `S`-perfect object of `D(𝒪_X)` is
`S'`-perfect. Both clauses of relative perfectness are local on `X ×_S S'`, which is covered by
the affine charts `V ×_W W'`, where the statement is Stacks 0DHW. -/
theorem isPerfectRelativeTo_derivedPullback_pullbackFst {X S S' : Scheme.{u}} (f : X ⟶ S)
    (g : S' ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hK : f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) K) :
    (pullback.snd f g).IsPerfectRelativeTo
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback (pullback.fst f g).toLRSHom.toShHom).obj K) := by
  choose W hW V hV hVW W' hW' hW'W hx using exists_mem_range_pullbackAffineChart f g
  refine isPerfectRelativeTo_of_openImmersion_cover (pullback.snd f g)
    (fun x => pullback (f.resLE (W x) (V x) (hVW x)) (g.resLE (W x) (W' x) (hW'W x)))
    (fun x => pullbackAffineChart f g (hVW x) (hW'W x)) (fun x => ⟨x, hx x⟩) _ (fun x => ?_)
  refine isPerfectRelativeTo_pullbackAffineChart f g (hW x) (hV x) (hVW x) (hW' x) (hW'W x) K ?_
  have : IsAffine (V x).toScheme := hV x
  exact (isPerfectRelativeTo_baseOpen_iff (f.resLE (W x) (V x) (hVW x)) (W x).ι
    (f := (V x).ι ≫ f) (resLE_comp_ι f (hVW x)) _).1 (isPerfectRelativeTo_opens_ι f (V x) K hK)

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.RelativeDescentSituation

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] (D : RelativeDescentSituation.{u, u} I)

/-- The stage `Xⱼ` is the base change of the stage `Xᵢ` along `Sⱼ ⟶ Sᵢ`. -/
def schemeAtIsoPullback {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    pullback (D.structureMapAt i) (D.descent.system.map (homOfLE h).op) ≅ D.schemeAt j :=
  pullbackLeftPullbackSndIso D.X₀.hom (D.baseMap i) (D.descent.system.map (homOfLE h).op) ≪≫
    pullback.congrHom rfl (by
      rw [← D.descent.system.map_comp]
      exact congrArg D.descent.system.map (Subsingleton.elim _ _))

/-- Under `schemeAtIsoPullback`, the structure morphism `Xⱼ ⟶ Sⱼ` corresponds to the second
projection of the pullback of `Xᵢ ⟶ Sᵢ` along `Sⱼ ⟶ Sᵢ`. -/
theorem schemeAtIsoPullback_hom_structureMapAt {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    (D.schemeAtIsoPullback h).hom ≫ D.structureMapAt j =
      pullback.snd (D.structureMapAt i) (D.descent.system.map (homOfLE h).op) := by
  dsimp only [schemeAtIsoPullback, Iso.trans_hom, pullback.congrHom, asIso_hom, structureMapAt]
  rw [Category.assoc, pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]

/-- Under `schemeAtIsoPullback`, the transition morphism `Xⱼ ⟶ Xᵢ` corresponds to the first
projection of the pullback of `Xᵢ ⟶ Sᵢ` along `Sⱼ ⟶ Sᵢ`. -/
theorem schemeAtIsoPullback_hom_transition {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    (D.schemeAtIsoPullback h).hom ≫ D.transition h =
      pullback.fst (D.structureMapAt i) (D.descent.system.map (homOfLE h).op) := by
  dsimp only [schemeAtIsoPullback, Iso.trans_hom, pullback.congrHom, asIso_hom, transition,
    structureMapAt]
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, pullback.lift_fst, pullback.lift_fst,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
      Category.comp_id, pullbackLeftPullbackSndIso_hom_snd_assoc]
    exact pullback.condition.symm

/-- The structure morphism of the stage `Xⱼ`, as the base change of that of `Xᵢ`. -/
def structureMapAtArrowIso {i j : D.LaterIndex} (h : i.1 ≤ j.1) :
    Scheme.Hom.ringedArrow
        (pullback.snd (D.structureMapAt i) (D.descent.system.map (homOfLE h).op)) ≅
      Scheme.Hom.ringedArrow (D.structureMapAt j) :=
  Arrow.isoMk (Scheme.forgetToRingedSpace.mapIso (D.schemeAtIsoPullback h)) (Iso.refl _)
    ((Scheme.forgetToRingedSpace.map_comp _ _).symm.trans
      ((congrArg Scheme.forgetToRingedSpace.map (D.schemeAtIsoPullback_hom_structureMapAt h)).trans
        (Category.comp_id _).symm))

/-- **The transition maps of a relative descent situation preserve relative perfectness.** For
`i ≤ j` and an object `E` of `D(𝒪_{Xᵢ})` perfect relative to `Sᵢ`, the derived pullback of `E`
along `Xⱼ ⟶ Xᵢ` is perfect relative to `Sⱼ`. -/
theorem isPerfectRelativeTo_transition {i j : D.LaterIndex} (h : i.1 ≤ j.1)
    (E : DerivedCategory (OXMod.{u, u} (D.schemeAt i).toRingedSpace))
    (hE : letI : Flat D.X₀.hom := D.flat
      letI : LocallyOfFinitePresentation D.X₀.hom :=
        D.finitePresentation.locallyOfFinitePresentation
      (D.structureMapAt i).IsPerfectRelativeTo (D.canonicalStageCertificates i) E) :
    letI : Flat D.X₀.hom := D.flat
    letI : LocallyOfFinitePresentation D.X₀.hom :=
      D.finitePresentation.locallyOfFinitePresentation
    (D.structureMapAt j).IsPerfectRelativeTo (D.canonicalStageCertificates j)
      ((derivedPullback (D.transition h).toLRSHom.toShHom).obj E) := by
  let : Flat D.X₀.hom := D.flat
  let : LocallyOfFinitePresentation D.X₀.hom :=
    D.finitePresentation.locallyOfFinitePresentation
  have : QuasiCompact D.X₀.hom := D.finitePresentation.quasiCompact
  have : CompactSpace (D.descent.system.obj (op j.1)) := D.descent.quasiCompact j.1
  have : CompactSpace
      (pullback (D.structureMapAt i) (D.descent.system.map (homOfLE h).op)).carrier :=
    QuasiCompact.compactSpace_of_compactSpace
      (pullback.snd (D.structureMapAt i) (D.descent.system.map (homOfLE h).op))
  have hb := Scheme.Hom.isPerfectRelativeTo_derivedPullback_pullbackFst (D.structureMapAt i)
    (D.descent.system.map (homOfLE h).op) E hE
  refine (Scheme.Hom.isPerfectRelativeTo_arrowIso_iff _ _ (D.structureMapAtArrowIso h) _).1 ?_
  refine Scheme.Hom.isPerfectRelativeTo_canonical_of_iso _ ?_ hb
  exact ((Stacks.DerivedPullback.schemeFactorIso (D.schemeAtIsoPullback h).hom (D.transition h)
    _ (D.schemeAtIsoPullback_hom_transition h)).app E).symm

end AlgebraicGeometry.RelativeDescentSituation

end
