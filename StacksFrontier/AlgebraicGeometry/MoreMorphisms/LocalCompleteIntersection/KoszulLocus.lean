module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnTarget.RegularImmersionFpqc
public import StacksFrontier.AlgebraicGeometry.Divisors.Relative.SmoothSection
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Defs
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.ImmersionIntoSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.FlatBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SmoothEmbeddingIndependence
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeRegularImmersion.EqualityFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.AffineSpaceImmersion
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Independence
public import StacksFrontier.AlgebraicGeometry.RegularImmersion.BaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularImmersionComposition
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Koszul locus of a morphism of schemes flat over a base

For a morphism of schemes `f : X ⟶ Y` the set of points at which `f` is Koszul is open, and when
`X` and `Y` are both flat and locally of finite presentation over a base `S` the formation of that
set commutes with an arbitrary base change `S' ⟶ S`.

## Main results

* `AlgebraicGeometry.isOpen_koszulAt`: the Koszul locus is open.
* `AlgebraicGeometry.koszulAt_baseChange_iff`: the base change of `f` is Koszul at a point exactly
  when `f` is Koszul at its image.
* `AlgebraicGeometry.preimage_setOf_koszulAt`: the same, as an equality of subsets.

## Implementation notes

The inclusion that carries the content goes through the fibres. Stacks 069E compares the
Koszul-regular immersion supplied by the Koszul hypothesis with a chosen immersion into a scheme
smooth over the target; the resulting local regularity is quasi-regular after Stacks 063K, and
quasi-regularity is what survives the two remaining steps — restriction to the fibre over the
image point (Stacks 063R) and descent along the extension of residue fields (Stacks 0694) — and
is what the fibrewise criterion of Stacks 063W consumes. The reverse inclusion needs none of
this: it is the base-change clause of Stacks 063U applied to the Koszul-regular immersion of the
witness.

## References

* [The Stacks Project, Lemma 37.62.11 (06B8)](https://stacks.math.columbia.edu/tag/06B8)
-/

public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

namespace AlgebraicGeometry

universe u

private theorem locallyOfFiniteType_of_common_base {X Y S : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S)
    (q : Y ⟶ S) (h : f ≫ q = p) [LocallyOfFinitePresentation p]
    [LocallyOfFinitePresentation q] : LocallyOfFiniteType f := by
  have : LocallyOfFinitePresentation (f ≫ q) := by
    simpa only [h] using (inferInstance : LocallyOfFinitePresentation p)
  have : LocallyOfFiniteType q := inferInstance
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation_of_comp f q
  infer_instance

/-- A point in the range of an open immersion is hit. -/
private theorem exists_point_over_openImmersion {X Y : Scheme.{u}} (e : X ⟶ Y) [IsOpenImmersion e]
    (y : Y) (hy : y ∈ e.opensRange) : ∃ x : X, e.base x = y := by
  have hrange : Set.range (Y.fromSpecResidueField y) ⊆ Set.range e := by
    rw [Scheme.range_fromSpecResidueField]
    rintro z rfl
    exact (Scheme.Hom.coe_opensRange e).symm ▸ hy
  refine ⟨IsOpenImmersion.lift e _ hrange (IsLocalRing.closedPoint _), ?_⟩
  have hfac := IsOpenImmersion.lift_fac e (Y.fromSpecResidueField y) hrange
  change (IsOpenImmersion.lift e _ hrange ≫ e).base (IsLocalRing.closedPoint _) = y
  rw [hfac]
  exact Scheme.fromSpecResidueField_apply y _

/-- Being Koszul at a point of an open subscheme of the source is inherited by the restriction
of the morphism to that open subscheme. -/
theorem koszulAt_precomp_openImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (e : Z ⟶ X) [IsOpenImmersion e] (z : Z)
    (hx : KoszulAt f (e z)) : KoszulAt (e ≫ f) z := by
  obtain ⟨-, U, hxU, P, i, π, hi, hK, hπ, hfac⟩ := hx
  have : IsImmersion i := hi
  have : Smooth π := hπ
  refine ⟨finiteTypeAt_of_locallyOfFiniteType (e ≫ f) z, e ⁻¹ᵁ U, hxU, P, (e ∣_ U) ≫ i, π,
    inferInstance, Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp _ _
      (isKoszulRegularImmersion_of_isOpenImmersion (e ∣_ U)) hK, hπ, ?_⟩
  rw [← Category.assoc, ← morphismRestrict_ι e U, Category.assoc, hfac, Category.assoc]

/-- An immersion of the source into a scheme smooth over the target is `H₁`-regular over a
neighbourhood of the image of any point at which the morphism is Koszul.  The Koszul witness
supplies a second immersion over the target, and Stacks 069E compares the two. -/
private theorem exists_h1RegularImmersion_restrict_of_koszulAt {X Y P : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (i : X ⟶ P) [IsImmersion i] (π : P ⟶ Y) [Smooth π]
    (hfac : i ≫ π = f) (x : X) (hx : KoszulAt f x) :
    ∃ W : P.Opens, i x ∈ W ∧ IsH1RegularImmersion (i ∣_ W) := by
  obtain ⟨-, U, hxU, Q, j, ρ, hj, hK, hρ, hfacU⟩ := hx
  have : IsImmersion j := hj
  have : Smooth ρ := hρ
  have ha : (U.ι ≫ i) ≫ π = U.ι ≫ f := by rw [Category.assoc, hfac]
  have hb : j ≫ ρ = U.ι ≫ f := hfacU.symm
  have hcmp : ∃ V : U.toScheme.Opens, (⟨x, hxU⟩ : U.toScheme) ∈ V ∧
      IsKoszulRegularImmersion (V.ι ≫ j) :=
    ⟨⊤, trivial, Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp _ _
      (isKoszulRegularImmersion_of_isOpenImmersion (⊤ : U.toScheme.Opens).ι) hK⟩
  obtain ⟨V, hxV, hVreg⟩ :=
    (exists_opens_isKoszulRegularImmersion_comp_iff (U.ι ≫ f) π ρ (U.ι ≫ i) j ha hb
      ⟨x, hxU⟩).mpr hcmp
  set O : X.Opens := (V.ι ≫ U.ι).opensRange with hO
  have hxO : x ∈ O := ⟨⟨⟨x, hxU⟩, hxV⟩, rfl⟩
  set c := (V.ι ≫ U.ι).isoOpensRange with hc
  have hOi : O.ι ≫ i = c.inv ≫ ((V.ι ≫ U.ι) ≫ i) := by
    rw [← Category.assoc, hc, Scheme.Hom.isoOpensRange_inv_comp]
  have hXreg : IsH1RegularImmersion (O.ι ≫ i) :=
    isH1RegularImmersion_of_isKoszulRegularImmersion _
      (isKoszulRegularImmersion_of_eq hOi.symm
        (Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp c.inv ((V.ι ≫ U.ι) ≫ i)
          (isKoszulRegularImmersion_of_isOpenImmersion c.inv)
          (isKoszulRegularImmersion_of_eq (Category.assoc _ _ _).symm hVreg)))
  obtain ⟨W, hW, hpre⟩ := i.isEmbedding.isInducing.isOpen_iff.mp O.isOpen
  set W' : P.Opens := ⟨W, hW⟩ with hW'
  have hWeq : i ⁻¹ᵁ W' = O := TopologicalSpace.Opens.ext hpre
  refine ⟨W', ?_, ?_⟩
  · change x ∈ i ⁻¹ᵁ W'
    rw [hWeq]
    exact hxO
  · have hcomp : IsH1RegularImmersion ((i ⁻¹ᵁ W').ι ≫ i) := by rw [hWeq]; exact hXreg
    exact isH1RegularImmersion_of_comp_of_smooth (i ∣_ W') W'.ι
      (isH1RegularImmersion_of_eq (morphismRestrict_ι i W').symm hcomp)

private theorem koszulAt_of_openImmersion_factorization {X Y Z P : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (e : Z ⟶ X) [IsOpenImmersion e] (i : Z ⟶ P) [IsImmersion i]
    (π : P ⟶ Y) (hi : IsKoszulRegularImmersion i) (hπ : Smooth π)
    (hfac : e ≫ f = i ≫ π) (z : Z) : KoszulAt f (e z) := by
  refine ⟨finiteTypeAt_of_locallyOfFiniteType f _, e.opensRange, ⟨z, rfl⟩, P,
    e.isoOpensRange.inv ≫ i, π, inferInstance,
    Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp _ _
      (isKoszulRegularImmersion_of_isOpenImmersion e.isoOpensRange.inv) hi, hπ, ?_⟩
  rw [← cancel_epi e.isoOpensRange.hom]
  simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp,
    Scheme.Hom.isoOpensRange_hom_ι] using hfac

/-- Base changing a morphism over `S` along `g : T ⟶ S` is taking a fibre product: the projection
`X ×_S T ⟶ X` and the induced map `X ×_S T ⟶ Y ×_S T` form a cartesian square over `f`. -/
private theorem isPullback_baseChange_map {X Y S T : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S)
    (q : Y ⟶ S) (h : f ≫ q = p) (g : T ⟶ S) :
    IsPullback (pullback.fst p g)
      (pullback.map p g q g f (𝟙 _) (𝟙 _)
        (by simpa only [Category.comp_id] using h.symm) (by simp))
      f (pullback.fst q g) := by
  refine IsPullback.flip (IsPullback.of_right ?_
    (by simp [pullback.map]) ((IsPullback.of_hasPullback q g).flip))
  have hsnd : pullback.map p g q g f (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using h.symm) (by simp) ≫ pullback.snd q g =
      pullback.snd p g := by
    simp [pullback.map]
  rw [hsnd, h]
  exact (IsPullback.of_hasPullback p g).flip

/-- A morphism locally of finite type factors, near any point of its source, as a closed immersion
into an affine scheme smooth over the target: embed an affine neighbourhood into affine space,
make the immersion closed over its coborder, and shrink to an affine open there. -/
@[sga "5 III 1.7.4" "partial"]
private theorem exists_closed_smooth_factorization {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (x : X) :
    ∃ (Z P : Scheme.{u}) (e : Z ⟶ X) (i : Z ⟶ P) (π : P ⟶ Y),
      IsOpenImmersion e ∧ IsClosedImmersion i ∧ Smooth π ∧ IsAffine P ∧
      e ≫ f = i ≫ π ∧ ∃ z : Z, e z = x := by
  obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens, x ∈ U.1 := by
    obtain ⟨-, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨U, hU⟩, hxU⟩
  have : IsAffine U.1.toScheme := U.2
  obtain ⟨n, j, hj, hjf⟩ := exists_immersion_affineSpace (U.1.ι ≫ f)
  have : IsImmersion j := hj
  have hπ₀ : Smooth (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y) :=
    smooth_affineSpace_over (ULift.{u} (Fin n)) Y
  have hπ₁ : Smooth (j.coborderRange.ι ≫ (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y)) :=
    inferInstance
  obtain ⟨V, hzV⟩ : ∃ V : j.coborderRange.toScheme.affineOpens,
      j.liftCoborder (⟨x, hxU⟩ : U.1.toScheme) ∈ V.1 := by
    obtain ⟨-, ⟨V, hV, rfl⟩, hzV, -⟩ :=
      j.coborderRange.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
        (Set.mem_univ (j.liftCoborder (⟨x, hxU⟩ : U.1.toScheme))) isOpen_univ
    exact ⟨⟨V, hV⟩, hzV⟩
  refine ⟨_, _, (j.liftCoborder ⁻¹ᵁ V.1).ι ≫ U.1.ι, j.liftCoborder ∣_ V.1,
    V.1.ι ≫ (j.coborderRange.ι ≫ (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y)),
    inferInstance, inferInstance, inferInstance, V.2, ?_, ⟨⟨⟨x, hxU⟩, hzV⟩, rfl⟩⟩
  have hlocal : j.liftCoborder ≫ (j.coborderRange.ι ≫
      (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y)) = U.1.ι ≫ f := by
    rw [← Category.assoc, j.liftCoborder_ι]
    exact hjf
  calc ((j.liftCoborder ⁻¹ᵁ V.1).ι ≫ U.1.ι) ≫ f
      = (j.liftCoborder ⁻¹ᵁ V.1).ι ≫ (j.liftCoborder ≫ (j.coborderRange.ι ≫
          (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y))) := by rw [hlocal, Category.assoc]
    _ = (j.liftCoborder ∣_ V.1) ≫ V.1.ι ≫ (j.coborderRange.ι ≫
          (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y)) := by
        rw [← Category.assoc, ← morphismRestrict_ι, Category.assoc]

/-- Being Koszul at a point descends along an open immersion: if `e ≫ f` is Koszul at `z`, then
`f` is Koszul at `e z`. -/
private theorem koszulAt_of_precomp_openImmersion {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (e : Z ⟶ X) [IsOpenImmersion e] (z : Z)
    (hz : KoszulAt (e ≫ f) z) : KoszulAt f (e z) := by
  obtain ⟨-, U, hzU, P, i, π, hi, hK, hπ, hfac⟩ := hz
  have : IsImmersion i := hi
  exact koszulAt_of_openImmersion_factorization f (U.ι ≫ e) i π hK hπ
    (by simpa only [Category.assoc] using hfac) (⟨z, hzU⟩ : U.toScheme)

/-- A point of `X ×_S S'` whose image in `X` lies in an open `U` is hit by the pullback of `U`
along the first projection. -/
private theorem exists_point_over_open_in_pullback
    {X S S' : Scheme.{u}} (p : X ⟶ S) (g : S' ⟶ S)
    (U : X.Opens) (x' : (pullback p g : Scheme.{u}))
    (hx : (pullback.fst p g).base x' ∈ U) :
    ∃ z : (pullback (pullback.fst p g) U.ι : Scheme.{u}),
      (pullback.fst (pullback.fst p g) U.ι).base z = x' := by
  let e := pullback.fst (pullback.fst p g) U.ι
  have hmem : x' ∈ e.opensRange := by
    rw [Scheme.Hom.opensRange_pullbackFst, Scheme.Opens.opensRange_ι]
    exact hx
  exact exists_point_over_openImmersion e x' hmem

/-- A Koszul-regular immersion `i : U ⟶ P` with `P` flat and locally of finite presentation over
`S` and with `U` flat over `S` is a relative quasi-regular immersion over `S`, so every base
change of it along `S' ⟶ S` is a regular immersion. -/
private theorem regularImmersion_baseChange_of_koszulRegular
    {U P S S' : Scheme.{u}} (i : U ⟶ P) [IsImmersion i]
    (r : P ⟶ S) [Flat r] [LocallyOfFinitePresentation r] (hflat : Flat (i ≫ r))
    (hi : IsKoszulRegularImmersion i) (g : S' ⟶ S) :
    IsRegularImmersion (pullback.fst (pullback.snd g r) i) := by
  have hqreg : IsQuasiRegularImmersion i :=
    isQuasiRegularImmersion_of_isH1RegularImmersion i
      (isH1RegularImmersion_of_isKoszulRegularImmersion i hi)
  exact Stacks.AlgebraicGeometry.isRegularImmersion_baseChange_of_isRelativeQuasiRegularImmersion
    r i ⟨hflat, hqreg⟩ g

/-- In the situation of `regularImmersion_baseChange_of_koszulRegular`, the base change of a
Koszul-regular immersion is again Koszul-regular, since a regular immersion is Koszul-regular. -/
private theorem koszulRegularImmersion_baseChange_of_koszulRegular
    {U P S S' : Scheme.{u}} (i : U ⟶ P) [IsImmersion i]
    (r : P ⟶ S) [Flat r] [LocallyOfFinitePresentation r] (hflat : Flat (i ≫ r))
    (hi : IsKoszulRegularImmersion i) (g : S' ⟶ S) :
    IsKoszulRegularImmersion (pullback.fst (pullback.snd g r) i) :=
  isKoszulRegularImmersion_of_isRegularImmersion _
    (regularImmersion_baseChange_of_koszulRegular i r hflat hi g)

/-- For a morphism `f : X ⟶ Y` of schemes flat and locally of finite presentation over `S`, the
base change of `f` along `S' ⟶ S` is Koszul at any point lying over a point where `f` is Koszul.
This is the easy implication of Stacks 06B8. -/
@[sga "6 VIII 1.6" "special case"]
private theorem koszulAt_baseChange_forward {X Y S S' : Scheme.{u}}
    (f : X ⟶ Y) (p : X ⟶ S) (q : Y ⟶ S) (h : f ≫ q = p)
    [Flat p] [Flat q] [LocallyOfFinitePresentation p]
    [LocallyOfFinitePresentation q] (g : S' ⟶ S)
    (x' : (pullback p g : Scheme.{u}))
    (hx : KoszulAt f ((pullback.fst p g).base x')) :
    KoszulAt
      (pullback.map p g q g f (𝟙 _) (𝟙 _)
        (by simpa only [Category.comp_id] using h.symm) (by simp)) x' := by
  let f' : pullback p g ⟶ pullback q g :=
    pullback.map p g q g f (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using h.symm) (by simp)
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_common_base f p q h
  rcases hx with ⟨_, U, hxU, P, i, π, hi, hk, hsm, hfac⟩
  have : IsImmersion i := hi
  let r : P ⟶ S := π ≫ q
  have hbase : i ≫ r = U.ι ≫ p := by
    dsimp [r]
    rw [← Category.assoc, hfac.symm, Category.assoc, h]
  let vIso := (pullbackSymmetry (pullback.fst p g) U.ι) ≪≫
    pullbackRightPullbackFstIso p g U.ι
  let wHom :=
    (pullbackSymmetry (pullback.snd g r) i).hom ≫
      pullback.map i (pullback.snd g r) i (pullback.fst r g)
        (𝟙 _) (pullbackSymmetry g r).hom (𝟙 _)
        (by simp) (by simp) ≫ (pullbackRightPullbackFstIso r g i).hom
  have : IsIso wHom := inferInstance
  let wIso := asIso wHom
  let midIso := pullback.congrHom hbase (rfl : g = g)
  let eIso : pullback (pullback.snd g r) i ≅
      pullback (pullback.fst p g) U.ι := wIso ≪≫ midIso ≪≫ vIso.symm
  let e : pullback (pullback.snd g r) i ⟶ pullback p g :=
    eIso.hom ≫ pullback.fst (pullback.fst p g) U.ι
  have hWfst : wIso.hom ≫ pullback.fst (i ≫ r) g =
      pullback.snd (pullback.snd g r) i := by
    dsimp [wIso, wHom]
    simp [pullback.map, Category.assoc, pullbackRightPullbackFstIso_hom_fst,
      pullbackSymmetry_hom_comp_fst]
  have hWsnd : wIso.hom ≫ pullback.snd (i ≫ r) g =
      pullback.fst (pullback.snd g r) i ≫ pullback.fst g r := by
    dsimp [wIso, wHom]
    simp [pullback.map, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
      pullbackSymmetry_hom_comp_snd]
  have hmFst : midIso.hom ≫ pullback.fst (U.ι ≫ p) g =
      pullback.fst (i ≫ r) g := by
    dsimp [midIso, pullback.congrHom]
    simp only [pullback.map, pullback.lift_fst, Category.comp_id]
  have hmSnd : midIso.hom ≫ pullback.snd (U.ι ≫ p) g =
      pullback.snd (i ≫ r) g := by
    dsimp [midIso, pullback.congrHom]
    simp only [pullback.map, pullback.lift_snd, Category.comp_id]
  have hvFst : vIso.symm.hom ≫ pullback.fst (pullback.fst p g) U.ι ≫
      pullback.fst p g = pullback.fst (U.ι ≫ p) g ≫ U.ι := by
    simp [vIso, Category.assoc, pullbackRightPullbackFstIso_inv_snd_fst]
  have hvSnd : vIso.symm.hom ≫ pullback.fst (pullback.fst p g) U.ι ≫
      pullback.snd p g = pullback.snd (U.ι ≫ p) g := by
    simp [vIso, Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd]
  have he : e ≫ pullback.fst p g =
      pullback.snd (pullback.snd g r) i ≫ U.ι := by
    dsimp [e]
    simp only [eIso, Iso.trans_hom, Category.assoc]
    rw [hvFst]
    change wIso.hom ≫ (midIso.hom ≫ pullback.fst (U.ι ≫ p) g) ≫ U.ι = _
    rw [hmFst]
    exact congrArg (fun k => k ≫ U.ι) hWfst
  have heSnd : e ≫ pullback.snd p g =
      pullback.fst (pullback.snd g r) i ≫ pullback.fst g r := by
    dsimp [e]
    simp only [eIso, Iso.trans_hom, Category.assoc]
    rw [hvSnd]
    change wIso.hom ≫ (midIso.hom ≫ pullback.snd (U.ι ≫ p) g) = _
    rw [hmSnd, hWsnd]
  have : IsOpenImmersion e := by
    dsimp [e]
    infer_instance
  rcases exists_point_over_open_in_pullback p g U x' hxU with ⟨zV, hzV⟩
  let z := eIso.inv zV
  have hz : e.base z = x' := by
    change (eIso.hom ≫ pullback.fst (pullback.fst p g) U.ι).base
      (eIso.inv zV) = x'
    rw [Scheme.Hom.comp_base]
    change (pullback.fst (pullback.fst p g) U.ι).base
      ((eIso.inv ≫ eIso.hom).base zV) = x'
    simp [hzV]
  let U' : (pullback p g).Opens := e.opensRange
  have hxU' : x' ∈ U' := ⟨z, hz⟩
  let eU : (pullback (pullback.snd g r) i) ≅ U'.toScheme := e.isoOpensRange
  have hflat : Flat (i ≫ r) := by
    rw [hbase]
    infer_instance
  have hK : IsKoszulRegularImmersion (pullback.fst (pullback.snd g r) i) :=
    koszulRegularImmersion_baseChange_of_koszulRegular i r hflat hk g
  have : IsImmersion (pullback.fst (pullback.snd g r) i) := inferInstance
  have hregU : IsRegularImmersion eU.inv :=
    Stacks.AlgebraicGeometry.isRegularImmersion_of_smooth_section eU.hom eU.inv (by simp)
  have hKU : IsKoszulRegularImmersion eU.inv :=
    isKoszulRegularImmersion_of_isRegularImmersion eU.inv hregU
  have hK' : IsKoszulRegularImmersion (eU.inv ≫ pullback.fst (pullback.snd g r) i) :=
    Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp eU.inv _ hKU hK
  let π' : pullback g r ⟶ pullback q g :=
    (pullbackSymmetry g r).hom ≫
      (pullbackRightPullbackFstIso q g π).inv ≫
      pullback.snd π (pullback.fst q g)
  have hsm' : Smooth π' := by
    have : MorphismProperty.RespectsIso (@Smooth) :=
      MorphismProperty.IsStableUnderBaseChange.respectsIso
    have hπ : Smooth (pullback.snd π (pullback.fst q g)) := inferInstance
    exact MorphismProperty.RespectsIso.precomp (@Smooth) (pullbackSymmetry g r).hom _
      (MorphismProperty.RespectsIso.precomp (@Smooth)
        (pullbackRightPullbackFstIso q g π).inv _ hπ)
  have hf'fst : f' ≫ pullback.fst q g = pullback.fst p g ≫ f := by
    simp [f', pullback.map]
  have hf'snd : f' ≫ pullback.snd q g = pullback.snd p g := by
    simp [f', pullback.map]
  have hπfst : π' ≫ pullback.fst q g = pullback.snd g r ≫ π := by
    dsimp [π', r]
    simp only [Category.assoc]
    rw [pullbackRightPullbackFstIso_inv_snd_fst]
    exact congrArg (fun k => k ≫ π) (pullbackSymmetry_hom_comp_fst g (π ≫ q))
  have hπsnd : π' ≫ pullback.snd q g = pullback.fst g r := by
    dsimp [π', r]
    simp only [Category.assoc, pullbackRightPullbackFstIso_inv_snd_snd,
      pullbackSymmetry_hom_comp_snd]
  have hfacE : e ≫ f' = pullback.fst (pullback.snd g r) i ≫ π' := by
    apply pullback.hom_ext
    · calc
        e ≫ f' ≫ pullback.fst q g = e ≫ pullback.fst p g ≫ f := by
          simpa only [Category.assoc] using congrArg (fun k => e ≫ k) hf'fst
        _ = (pullback.snd (pullback.snd g r) i ≫ U.ι) ≫ f :=
          congrArg (fun k => k ≫ f) he
        _ = pullback.snd (pullback.snd g r) i ≫ (i ≫ π) := by
          rw [Category.assoc, hfac]
        _ = pullback.fst (pullback.snd g r) i ≫ pullback.snd g r ≫ π :=
          congrArg (fun k => k ≫ π) pullback.condition.symm
        _ = pullback.fst (pullback.snd g r) i ≫ π' ≫ pullback.fst q g := by
          simpa only [Category.assoc] using congrArg
            (fun k => pullback.fst (pullback.snd g r) i ≫ k) hπfst.symm
    · calc
        e ≫ f' ≫ pullback.snd q g = e ≫ pullback.snd p g := by
          simpa only [Category.assoc] using congrArg (fun k => e ≫ k) hf'snd
        _ = pullback.fst (pullback.snd g r) i ≫ pullback.fst g r := heSnd
        _ = pullback.fst (pullback.snd g r) i ≫ π' ≫ pullback.snd q g := by
          simpa only [Category.assoc] using congrArg
            (fun k => pullback.fst (pullback.snd g r) i ≫ k) hπsnd.symm
  have hfac' : U'.ι ≫ f' =
      (eU.inv ≫ pullback.fst (pullback.snd g r) i) ≫ π' := by
    rw [← e.isoOpensRange_inv_comp, Category.assoc, hfacE, Category.assoc]
  have : LocallyOfFinitePresentation (pullback.snd p g) := inferInstance
  have : LocallyOfFinitePresentation (pullback.snd q g) := inferInstance
  have : LocallyOfFiniteType f' :=
    locallyOfFiniteType_of_common_base f' (pullback.snd p g) (pullback.snd q g) hf'snd
  refine ⟨finiteTypeAt_of_locallyOfFiniteType f' x', U', hxU',
    pullback g r, eU.inv ≫ pullback.fst (pullback.snd g r) i,
    π', ?_, hK', hsm', hfac'⟩
  infer_instance

/-- Quasi-regularity of an immersion is unchanged by precomposing with an isomorphism. -/
private theorem quasiRegularImmersion_of_isIso_comp {A B C : Scheme.{u}} (e : A ⟶ B) [IsIso e]
    (i : B ⟶ C) [IsImmersion i] (hi : IsQuasiRegularImmersion (e ≫ i)) :
    IsQuasiRegularImmersion i := by
  have h : ∃ hh : IsImmersion (inv e ≫ e ≫ i),
      @IsQuasiRegularImmersion _ _ (inv e ≫ e ≫ i) hh :=
    ⟨inferInstance, Stacks.AlgebraicGeometry.isQuasiRegularImmersion_comp_of_isH1RegularImmersion
      (inv e) (e ≫ i) (isH1RegularImmersion_of_isOpenImmersion (inv e)) hi⟩
  rw [IsIso.inv_hom_id_assoc] at h
  exact h.2

/-- The defining ideal of a base change of a closed immersion is the inverse image of the
defining ideal of the immersion. -/
private theorem ker_eq_comap_of_isPullback {Z P Z' P' : Scheme.{u}} {i : Z ⟶ P} {i' : Z' ⟶ P'}
    {a : Z' ⟶ Z} {b : P' ⟶ P} [IsClosedImmersion i] (sq : IsPullback a i' i b) :
    i'.ker = i.ker.comap b := by
  calc
    i'.ker = (pullback.snd i b).ker := by
      rw [← sq.isoPullback_hom_snd, Scheme.Hom.ker_comp_of_isIso]
    _ = (pullback.fst b i).ker := by
      rw [← Scheme.Hom.ker_comp_of_isIso (pullbackSymmetry i b).hom,
        pullbackSymmetry_hom_comp_fst]
    _ = i.ker.comap b := Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i b

/-- Quasi-regularity passes from a closed immersion to the closed immersion of the subscheme cut
out by its defining ideal. -/
private theorem quasiRegularImmersion_subscheme_ker {Z P : Scheme.{u}} (i : Z ⟶ P)
    [IsClosedImmersion i] (hi : IsQuasiRegularImmersion i) :
    IsQuasiRegularImmersion i.ker.subschemeι := by
  apply quasiRegularImmersion_of_isIso_comp i.toImage
  simpa only [Scheme.Hom.toImage_imageι] using hi

/-- Quasi-regularity of the subscheme cut out on an open of a base change, read off
quasi-regularity of the restricted base-changed immersion. -/
private theorem quasiRegularImmersion_comap_of_restrict {Z P P' : Scheme.{u}} (i : Z ⟶ P)
    [IsClosedImmersion i] (b : P' ⟶ P) (V : P'.Opens)
    (hi : IsQuasiRegularImmersion (pullback.snd i b ∣_ V)) :
    IsQuasiRegularImmersion ((i.ker.comap b).comap V.ι).subschemeι := by
  have hk : (pullback.snd i b ∣_ V).ker = (i.ker.comap b).comap V.ι := by
    rw [ker_eq_comap_of_isPullback (isPullback_morphismRestrict (pullback.snd i b) V).flip,
      ker_eq_comap_of_isPullback (IsPullback.of_hasPullback i b)]
  have hH : ∃ h : IsImmersion (pullback.snd i b ∣_ V).ker.subschemeι,
      @IsQuasiRegularImmersion _ _ (pullback.snd i b ∣_ V).ker.subschemeι h :=
    ⟨inferInstance, quasiRegularImmersion_subscheme_ker _ hi⟩
  rw [hk] at hH
  exact hH.2

/-- **The fibrewise criterion for being Koszul.**  Let `i : X ⟶ P` be a closed immersion over `Y`
with `P` smooth over `Y`, and let `P` be flat and locally of finite presentation over a base `S`
with `X` likewise.  If the fibre of `X` over the image of `x` in `S` is a quasi-regular immersion
near `x`, then the morphism is Koszul at `x`. -/
private theorem koszulAt_of_fiber_quasiRegular {X Y P S : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (i : X ⟶ P) [IsClosedImmersion i] (π : P ⟶ Y) [Smooth π]
    (hfac : i ≫ π = f) (r : P ⟶ S) [Flat r] [LocallyOfFinitePresentation r] [Flat (i ≫ r)]
    [LocallyOfFinitePresentation (i ≫ r)] (x : X)
    (hq : ∃ V : (r.fiber (r (i x))).Opens, r.asFiber (i x) ∈ V ∧
      IsQuasiRegularImmersion (((i.ker.comap (r.fiberι (r (i x)))).comap V.ι).subschemeι)) :
    KoszulAt f x := by
  have hiImage : i.toImage ≫ i.ker.subschemeι = i := i.toImage_imageι
  have himage : i.ker.subschemeι = inv i.toImage ≫ i :=
    ((IsIso.inv_comp_eq i.toImage).2 hiImage.symm).symm
  have : Flat (i.ker.subschemeι ≫ r) := by
    rw [himage, Category.assoc]
    infer_instance
  have : LocallyOfFinitePresentation (i.ker.subschemeι ≫ r) := by
    rw [himage, Category.assoc]
    infer_instance
  have : LocallyOfFinitePresentation i.ker.subschemeι :=
    locallyOfFinitePresentation_of_comp i.ker.subschemeι r
  have hxI : i x ∈ i.ker.support := i.range_subset_ker_support ⟨x, rfl⟩
  obtain ⟨W, hxW, -, hreg⟩ :=
    Stacks.AlgebraicGeometry.exists_mem_isRelativeQuasiRegularImmersion_of_flatAt
      r i.ker (i x) hxI hq (Flat.stalkMap _ _)
  set e : (i.ker.comap W.ι).subscheme ⟶ X :=
    (i.ker.comapIso W.ι).hom ≫ pullback.snd W.ι i.ker.subschemeι ≫ inv i.toImage with he'
  have : IsOpenImmersion e := by
    rw [he']
    infer_instance
  have he : e ≫ i = (i.ker.comap W.ι).subschemeι ≫ W.ι := by
    rw [he', Category.assoc, Category.assoc, ← himage, ← pullback.condition]
    simp
  have hz : e ⟨⟨i x, hxW⟩, by rw [Scheme.IdealSheafData.support_comap]; exact hxI⟩ = x := by
    refine i.isEmbedding.injective ?_
    change (e ≫ i) _ = i x
    rw [he]
    rfl
  have hresult := koszulAt_of_openImmersion_factorization f e (i.ker.comap W.ι).subschemeι
    (W.ι ≫ π)
    (isKoszulRegularImmersion_of_isRegularImmersion _ hreg) inferInstance
    (by rw [← hfac, ← Category.assoc, he, Category.assoc])
    ⟨⟨i x, hxW⟩, by rw [Scheme.IdealSheafData.support_comap]; exact hxI⟩
  rwa [hz] at hresult

/-- The fibrewise criterion of `koszulAt_of_fiber_quasiRegular`, stated at an arbitrary point of
the fibre over an arbitrary point of the base identified with the image of `x`. -/
private theorem koszulAt_of_fiber_quasiRegular_at_point {X Y P S : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (i : X ⟶ P) [IsClosedImmersion i] (π : P ⟶ Y) [Smooth π]
    (hfac : i ≫ π = f) (r : P ⟶ S) [Flat r] [LocallyOfFinitePresentation r] [Flat (i ≫ r)]
    [LocallyOfFinitePresentation (i ≫ r)] (x : X) (s : S) (y : r.fiber s) (hs : s = r (i x))
    (hy : r.fiberι s y = i x)
    (hq : ∃ V : (r.fiber s).Opens, y ∈ V ∧
      IsQuasiRegularImmersion ((i.ker.comap (r.fiberι s)).comap V.ι).subschemeι) :
    KoszulAt f x := by
  subst hs
  have heq : y = r.asFiber (i x) := by
    refine (r.fiberι _).isEmbedding.injective ?_
    simpa only [Scheme.Hom.fiberι_asFiber] using hy
  subst heq
  exact koszulAt_of_fiber_quasiRegular f i π hfac r x hq

-- ===== BLOCK B =====

/-- Being a quasi-compact quasi-regular immersion, as a property of morphisms of schemes. -/
private abbrev quasiRegularImmersionProperty : MorphismProperty Scheme.{u} :=
  (fun _ _ f => ∃ hf : IsImmersion f,
      @Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion _ _ f hf) ⊓
    (@QuasiCompact : MorphismProperty Scheme.{u})

/-- Quasi-regularity transports along an equality of immersions. -/
private theorem quasiRegularImmersion_of_eq {A B : Scheme.{u}} {a b : A ⟶ B} [IsImmersion a]
    [IsImmersion b] (h : a = b)
    (ha : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion a) :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion b := by
  subst h
  exact ha

/-- Quasi-regularity of an immersion descends along a surjective flat quasi-compact
morphism. -/
private theorem quasiRegularImmersion_of_fpqc
    {Z X X' : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (g : X' ⟶ X) [Flat g] [Surjective g] [QuasiCompact g]
    (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion (pullback.snd i g))
    [QuasiCompact (pullback.snd i g)] :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion i := by
  have : MorphismProperty.IsLocalAtTarget quasiRegularImmersionProperty.{u}
      Scheme.fpqcPrecoverage :=
    isLocalAtTarget_quasiRegularImmersion_inf_quasiCompact_fpqc
  have hprop : quasiRegularImmersionProperty i :=
    MorphismProperty.IsLocalAtTarget.of_forall_pullbackSnd
      (K := Scheme.fpqcPrecoverage) g.singleton_mem_fpqcPrecoverage (by
        rintro _ _ _ ⟨⟩
        exact ⟨⟨inferInstance, hi⟩, inferInstance⟩)
  obtain ⟨⟨_, h⟩, _⟩ := hprop
  exact h

/-- Quasi-regularity of an immersion is inherited by a base change along a flat morphism. -/
@[ega "IV 19.1.5" "(ii)"]
private theorem quasiRegularImmersion_of_isPullback_flat
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    {a : Z' ⟶ Z} {b : X' ⟶ X} [Flat b] [IsImmersion i]
    [IsImmersion i'] (sq : IsPullback a i' i b)
    (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion i) :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion i' := by
  have hpb := Stacks.AlgebraicGeometry.isQuasiRegularImmersion_pullback_snd_of_flat i b hi
  exact quasiRegularImmersion_of_eq sq.isoPullback_hom_snd
    (Stacks.AlgebraicGeometry.isQuasiRegularImmersion_comp_of_isH1RegularImmersion
      sq.isoPullback.hom (pullback.snd i b)
      (isH1RegularImmersion_of_isOpenImmersion _) hpb)

/-- Quasi-regularity of the restriction of an immersion to an open is inherited by smaller
opens. -/
private theorem quasiRegularImmersion_restrict_le
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    {U V : X.Opens} (hVU : V ≤ U)
    (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion (i ∣_ U)) :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion (i ∣_ V) := by
  let a := Z.homOfLE (show i ⁻¹ᵁ V ≤ i ⁻¹ᵁ U from fun _ hx => hVU hx)
  let b := X.homOfLE hVU
  have sq : IsPullback a (i ∣_ V) (i ∣_ U) b := by
    apply IsPullback.of_right (h₁₂ := (i ⁻¹ᵁ U).ι) (h₂₂ := U.ι)
    · simpa only [a, b, Scheme.homOfLE_ι] using (isPullback_morphismRestrict i V).flip
    · rw [← cancel_mono U.ι]
      simp only [Category.assoc, morphismRestrict_ι]
      simp [a, b, morphismRestrict_ι]
    · exact (isPullback_morphismRestrict i U).flip
  exact quasiRegularImmersion_of_isPullback_flat sq hi

/-- Quasi-regularity of a quasi-compact immersion descends along a cartesian square whose
base morphism is flat, surjective and quasi-compact. -/
private theorem quasiRegularImmersion_of_isPullback_fpqc
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    {a : Z' ⟶ Z} {b : X' ⟶ X}
    [Flat b] [Surjective b] [QuasiCompact b]
    [IsImmersion i] [IsImmersion i'] [QuasiCompact i']
    (sq : IsPullback a i' i b)
    (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion i') :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion i := by
  have : MorphismProperty.IsLocalAtTarget quasiRegularImmersionProperty.{u}
      Scheme.fpqcPrecoverage :=
    isLocalAtTarget_quasiRegularImmersion_inf_quasiCompact_fpqc
  have hprop : quasiRegularImmersionProperty i' := ⟨⟨inferInstance, hi⟩, inferInstance⟩
  have hpb : quasiRegularImmersionProperty (pullback.snd i b) := by
    rw [← quasiRegularImmersionProperty.cancel_left_of_respectsIso sq.isoPullback.hom,
      sq.isoPullback_hom_snd]
    exact hprop
  have : QuasiCompact (pullback.snd i b) := hpb.2
  obtain ⟨⟨_, h⟩, _⟩ := hpb
  exact quasiRegularImmersion_of_fpqc i b h

/-- Descent of a local quasi-regularity statement along a flat universally open morphism:
an open neighbourhood on which the base change is quasi-regular produces one downstairs. -/
private theorem exists_quasiRegularImmersion_restrict_of_flat_open
    {Z X Z' X' : Scheme.{u}} {i : Z ⟶ X} {i' : Z' ⟶ X'}
    {a : Z' ⟶ Z} {b : X' ⟶ X}
    [Flat b] [UniversallyOpen b] [QuasiSeparatedSpace X]
    [IsClosedImmersion i] [IsClosedImmersion i']
    (sq : IsPullback a i' i b) (x' : X')
    (hx : ∃ W : X'.Opens, x' ∈ W ∧
      Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion (i' ∣_ W)) :
    ∃ U : X.Opens, b x' ∈ U ∧
      Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion (i ∣_ U) := by
  obtain ⟨W, hxW, hW⟩ := hx
  obtain ⟨V, hV, hxV, hVW⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X'.isBasis_affineOpens hxW
  change X'.Opens at V
  have hregV := quasiRegularImmersion_restrict_le i' hVW hW
  let U : X.Opens := ⟨b '' V, b.isOpenMap _ V.isOpen⟩
  have hVU : V ≤ b ⁻¹ᵁ U := fun z hz => ⟨z, hz, rfl⟩
  let c := b.resLE U V hVU
  have : Flat c := inferInstance
  have : IsAffine V.toScheme := hV
  have : QuasiSeparatedSpace U.toScheme :=
    QuasiSeparatedSpace.of_isOpenEmbedding U.ι.isOpenEmbedding
  have : QuasiCompact c := inferInstance
  have : Surjective c := ⟨by
    rintro ⟨y, z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, Subtype.ext (b.coe_resLE_apply hVU _)⟩⟩
  have hsource : i' ⁻¹ᵁ V = a ⁻¹ᵁ (i ⁻¹ᵁ U) ⊓ i' ⁻¹ᵁ V := by
    apply (inf_eq_right.mpr _).symm
    intro z hz
    change i (a z) ∈ U
    have hz' : b (i' z) ∈ U := hVU hz
    simpa only [← Scheme.Hom.comp_apply, sq.w] using hz'
  have sq' := Scheme.Hom.isPullback_resLE sq hVU le_rfl hsource
  refine ⟨U, ⟨x', hxV, rfl⟩, ?_⟩
  exact quasiRegularImmersion_of_isPullback_fpqc (i := i ∣_ U) (i' := i' ∣_ V) (b := c)
    (a := a.resLE (i ⁻¹ᵁ U) (i' ⁻¹ᵁ V) (hsource.trans_le inf_le_left))
    (by simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using sq') hregV

/-- Base change of a quasi-regular closed immersion whose source is flat over the base. -/
private theorem quasiRegularImmersion_relative_baseChange
    {Z P S Z' P' S' : Scheme.{u}} {i : Z ⟶ P} {r : P ⟶ S}
    {i' : Z' ⟶ P'} {r' : P' ⟶ S'} {a : Z' ⟶ Z} {b : P' ⟶ P} {g : S' ⟶ S}
    [IsClosedImmersion i] [IsClosedImmersion i'] [Flat (i ≫ r)]
    (sq : IsPullback a i' i b) (sr : IsPullback b r' r g)
    (hi : Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion i) :
    Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion i' :=
  Stacks.AlgebraicGeometry.isQuasiRegularImmersion_of_isPullback sr.flip sq.flip hi

/-- A local quasi-regularity statement is carried along base change of the base scheme. -/
private theorem exists_quasiRegularImmersion_restrict_baseChange
    {Z P S Z' P' S' : Scheme.{u}} {i : Z ⟶ P} {r : P ⟶ S}
    {i' : Z' ⟶ P'} {r' : P' ⟶ S'} {a : Z' ⟶ Z} {b : P' ⟶ P} {g : S' ⟶ S}
    [IsClosedImmersion i] [IsClosedImmersion i'] [Flat (i ≫ r)]
    (sq : IsPullback a i' i b) (sr : IsPullback b r' r g) (y' : P')
    (hi : ∃ W : P.Opens, b y' ∈ W ∧
      Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion (i ∣_ W)) :
    ∃ W' : P'.Opens, y' ∈ W' ∧
      Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion (i' ∣_ W') := by
  obtain ⟨W, hyW, hW⟩ := hi
  have hsource : i' ⁻¹ᵁ (b ⁻¹ᵁ W) = a ⁻¹ᵁ (i ⁻¹ᵁ W) ⊓ i' ⁻¹ᵁ (b ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← sq.w, Scheme.Hom.comp_preimage, inf_idem]
  have sq' := Scheme.Hom.isPullback_resLE sq (le_rfl : b ⁻¹ᵁ W ≤ b ⁻¹ᵁ W)
    (le_rfl : i ⁻¹ᵁ W ≤ i ⁻¹ᵁ W) hsource
  have : Flat ((i ∣_ W) ≫ W.ι ≫ r) := by
    rw [← Category.assoc, morphismRestrict_ι, Category.assoc]
    infer_instance
  refine ⟨b ⁻¹ᵁ W, hyW, ?_⟩
  exact quasiRegularImmersion_relative_baseChange (i := i ∣_ W) (r := W.ι ≫ r)
    (r' := (b ⁻¹ᵁ W).ι ≫ r') (g := g) (b := b ∣_ W)
    (a := a.resLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (b ⁻¹ᵁ W)) (hsource.trans_le inf_le_left))
    (by simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using sq')
    ((isPullback_morphismRestrict b W).paste_vert sr) hW

/-- A local quasi-regularity statement on a base change descends to the fibre of the original
morphism over the image point. -/
private theorem exists_quasiRegularImmersion_restrict_fiber_descend
    {Z P S Z' P' S' : Scheme.{u}} {i : Z ⟶ P} {r : P ⟶ S}
    {i' : Z' ⟶ P'} {r' : P' ⟶ S'} {a : Z' ⟶ Z} {b : P' ⟶ P} {g : S' ⟶ S}
    [IsClosedImmersion i] [IsClosedImmersion i'] [Flat (i' ≫ r')]
    [QuasiSeparated r]
    (sq : IsPullback a i' i b) (sr : IsPullback b r' r g) (y' : P')
    (hi : ∃ W : P'.Opens, y' ∈ W ∧
      Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion (i' ∣_ W)) :
    ∃ V : (r.fiber (g (r' y'))).Opens,
      (pullback.map r' (S'.fromSpecResidueField (r' y')) r
        (S.fromSpecResidueField (g (r' y'))) b (Spec.map (g.residueFieldMap (r' y'))) g
        sr.w.symm (by simp)) (r'.asFiber y') ∈ V ∧
      Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion
        (pullback.snd i (r.fiberι (g (r' y'))) ∣_ V) := by
  let s' := r' y'
  let c : r'.fiber s' ⟶ r.fiber (g s') :=
    pullback.map r' (S'.fromSpecResidueField s') r (S.fromSpecResidueField (g s'))
      b (Spec.map (g.residueFieldMap s')) g sr.w.symm (by simp)
  have hc : c ≫ r.fiberι (g s') = r'.fiberι s' ≫ b := pullback.lift_fst _ _ _
  have sc := isPullback_fiberToSpecResidueField_of_isPullback sr s'
  have : Flat (Spec.map (g.residueFieldMap s')) := inferInstance
  have : UniversallyOpen (Spec.map (g.residueFieldMap s')) := inferInstance
  have : Flat c := MorphismProperty.of_isPullback sc.flip inferInstance
  have : UniversallyOpen c := MorphismProperty.of_isPullback sc.flip inferInstance
  have : QuasiSeparated (r.fiberToSpecResidueField (g s')) :=
    MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback r (S.fromSpecResidueField (g s'))) ‹_›
  have : QuasiSeparatedSpace (r.fiber (g s')) :=
    quasiSeparatedSpace_of_quasiSeparated (r.fiberToSpecResidueField (g s'))
  let j := pullback.snd i (r.fiberι (g s'))
  let j' := pullback.snd i' (r'.fiberι s')
  let d : pullback i' (r'.fiberι s') ⟶ pullback i (r.fiberι (g s')) :=
    pullback.lift (pullback.fst i' (r'.fiberι s') ≫ a) (j' ≫ c) (by
      simp only [Category.assoc, hc]
      rw [sq.w, ← Category.assoc, pullback.condition]
      simp [j', Category.assoc])
  have sd : IsPullback d j' j c := by
    apply IsPullback.of_right (h₁₂ := pullback.fst i (r.fiberι (g s')))
      (h₂₂ := r.fiberι (g s'))
    · simpa only [d, pullback.lift_fst, hc] using
        ((IsPullback.of_hasPullback i' (r'.fiberι s')).paste_horiz sq)
    · simp [d, j]
    · exact IsPullback.of_hasPullback i (r.fiberι (g s'))
  have hf : ∃ V : (r'.fiber s').Opens, r'.asFiber y' ∈ V ∧
      Stacks.AlgebraicGeometry.RegularIdealSheaf.IsQuasiRegularImmersion (j' ∣_ V) :=
    exists_quasiRegularImmersion_restrict_baseChange
      (IsPullback.of_hasPullback i' (r'.fiberι s'))
      (IsPullback.of_hasPullback r' (S'.fromSpecResidueField s'))
      (r'.asFiber y') (by simpa only [s', Scheme.Hom.fiberι_asFiber] using hi)
  exact exists_quasiRegularImmersion_restrict_of_flat_open sd (r'.asFiber y') hf

/-- **The base-change step of Stacks 06B8.**  In a pair of cartesian squares exhibiting
`i' : X' ⟶ P'` over `S'` as the base change of a closed immersion `i : X ⟶ P` over `S`, with `P`
smooth over `Y` and flat and locally of finite presentation over `S`, a point at which the
base-changed morphism is Koszul lies over a point at which the original morphism is Koszul. -/
private theorem koszulAt_of_closed_baseChange {X Y P S X' Y' P' S' : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (i : X ⟶ P) [IsClosedImmersion i] (π : P ⟶ Y) [Smooth π]
    (hfac : i ≫ π = f) (r : P ⟶ S) [Flat r] [LocallyOfFinitePresentation r] [QuasiSeparated r]
    [Flat (i ≫ r)] [LocallyOfFinitePresentation (i ≫ r)] (f' : X' ⟶ Y') [LocallyOfFiniteType f']
    (i' : X' ⟶ P') [IsClosedImmersion i'] (π' : P' ⟶ Y') [Smooth π'] (hfac' : i' ≫ π' = f')
    (r' : P' ⟶ S') [Flat (i' ≫ r')] (a : X' ⟶ X) (b : P' ⟶ P) (g : S' ⟶ S)
    (sq : IsPullback a i' i b) (sr : IsPullback b r' r g) (x' : X') (hx : KoszulAt f' x') :
    KoszulAt f (a x') := by
  obtain ⟨W, hxW, hWreg⟩ := exists_h1RegularImmersion_restrict_of_koszulAt f' i' π' hfac' x' hx
  obtain ⟨V, hyV, hV⟩ := exists_quasiRegularImmersion_restrict_fiber_descend sq sr (i' x')
    ⟨W, hxW, isQuasiRegularImmersion_of_isH1RegularImmersion _ hWreg⟩
  let y : r.fiber (g (r' (i' x'))) :=
    (pullback.map r' (S'.fromSpecResidueField (r' (i' x'))) r
      (S.fromSpecResidueField (g (r' (i' x')))) b
      (Spec.map (g.residueFieldMap (r' (i' x')))) g sr.w.symm (by simp))
      (r'.asFiber (i' x'))
  have hy : r.fiberι (g (r' (i' x'))) y = i (a x') := by
    change (pullback.map r' (S'.fromSpecResidueField (r' (i' x'))) r
        (S.fromSpecResidueField (g (r' (i' x')))) b
        (Spec.map (g.residueFieldMap (r' (i' x')))) g sr.w.symm (by simp) ≫
      r.fiberι (g (r' (i' x')))) (r'.asFiber (i' x')) = _
    simp only [Scheme.Hom.fiberι, pullback.map, pullback.lift_fst]
    change b (r'.fiberι (r' (i' x')) (r'.asFiber (i' x'))) = i (a x')
    rw [Scheme.Hom.fiberι_asFiber]
    exact (congrArg (fun k : X' ⟶ P => k x') sq.w).symm
  have hs : g (r' (i' x')) = r (i (a x')) := by
    rw [← hy]
    exact (Set.mem_preimage.mp ((r.range_fiberι (g (r' (i' x')))) ▸ Set.mem_range_self y)).symm
  exact koszulAt_of_fiber_quasiRegular_at_point f i π hfac r (a x') (g (r' (i' x'))) y hs hy
    ⟨V, hyV, quasiRegularImmersion_comap_of_restrict i (r.fiberι (g (r' (i' x')))) V hV⟩

/-- The inclusion of Stacks 06B8 that needs the fibrewise criterion: if the base change of `f`
along `S' ⟶ S` is Koszul at `x'`, then `f` is Koszul at the image of `x'`. -/
private theorem koszulAt_baseChange_backward {X Y S S' : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S)
    (q : Y ⟶ S) (h : f ≫ q = p) [Flat p] [Flat q] [LocallyOfFinitePresentation p]
    [LocallyOfFinitePresentation q] (g : S' ⟶ S) (x' : (pullback p g : Scheme.{u}))
    (hx : KoszulAt (pullback.map p g q g f (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using h.symm) (by simp)) x') :
    KoszulAt f ((pullback.fst p g).base x') := by
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_common_base f p q h
  have sf := isPullback_baseChange_map f p q h g
  have hf'snd : pullback.map p g q g f (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using h.symm) (by simp) ≫ pullback.snd q g =
      pullback.snd p g := by
    simp [pullback.map]
  have : LocallyOfFiniteType (pullback.map p g q g f (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using h.symm) (by simp)) :=
    locallyOfFiniteType_of_common_base _ (pullback.snd p g) (pullback.snd q g) hf'snd
  obtain ⟨Z, P, e, i, π, he, hi, hπ, hP, hfac, z, hz⟩ :=
    exists_closed_smooth_factorization f ((pullback.fst p g).base x')
  have := he
  have := hi
  have := hπ
  have := hP
  have hit : i ≫ (π ≫ q) = e ≫ p := by rw [← Category.assoc, ← hfac, Category.assoc, h]
  have se : IsPullback (pullback.fst (e ≫ p) g)
      (pullback.map (e ≫ p) g p g e (𝟙 _) (𝟙 _) (by simp) (by simp)) e (pullback.fst p g) :=
    isPullback_baseChange_map e (e ≫ p) p rfl g
  have si : IsPullback (pullback.fst (e ≫ p) g)
      (pullback.map (e ≫ p) g (π ≫ q) g i (𝟙 _) (𝟙 _)
        (by simpa only [Category.comp_id] using hit.symm) (by simp)) i
      (pullback.fst (π ≫ q) g) :=
    isPullback_baseChange_map i (e ≫ p) (π ≫ q) hit g
  have sp : IsPullback (pullback.fst (π ≫ q) g)
      (pullback.map (π ≫ q) g q g π (𝟙 _) (𝟙 _) (by simp) (by simp)) π (pullback.fst q g) :=
    isPullback_baseChange_map π (π ≫ q) q rfl g
  have : IsOpenImmersion (pullback.map (e ≫ p) g p g e (𝟙 _) (𝟙 _) (by simp) (by simp)) :=
    MorphismProperty.of_isPullback se inferInstance
  have : IsClosedImmersion (pullback.map (e ≫ p) g (π ≫ q) g i (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using hit.symm) (by simp)) :=
    MorphismProperty.of_isPullback si inferInstance
  have : Smooth (pullback.map (π ≫ q) g q g π (𝟙 _) (𝟙 _) (by simp) (by simp)) :=
    MorphismProperty.of_isPullback sp inferInstance
  have hxrange : x' ∈ (pullback.fst (pullback.fst p g) e).opensRange := by
    rw [Scheme.Hom.opensRange_pullbackFst]
    exact ⟨z, hz⟩
  obtain ⟨w, hw⟩ := exists_point_over_openImmersion _ x' hxrange
  set z' := se.flip.isoPullback.inv w with hz'def
  have hz' : (pullback.map (e ≫ p) g p g e (𝟙 _) (𝟙 _) (by simp) (by simp)) z' = x' := by
    rw [hz'def]
    change (se.flip.isoPullback.inv ≫ _) w = x'
    rw [se.flip.isoPullback_inv_fst]
    exact hw
  have hfac' : (pullback.map (e ≫ p) g (π ≫ q) g i (𝟙 _) (𝟙 _)
        (by simpa only [Category.comp_id] using hit.symm) (by simp)) ≫
      (pullback.map (π ≫ q) g q g π (𝟙 _) (𝟙 _) (by simp) (by simp)) =
      (pullback.map (e ≫ p) g p g e (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫
      (pullback.map p g q g f (𝟙 _) (𝟙 _)
        (by simpa only [Category.comp_id] using h.symm) (by simp)) := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [← sp.w, ← sf.w]
      simp only [← Category.assoc]
      rw [← si.w, ← se.w]
      simp only [Category.assoc, hfac]
    · simp [pullback.map, Category.assoc]
  have hflat : Flat (i ≫ (π ≫ q)) := by rw [hit]; infer_instance
  have hfp : LocallyOfFinitePresentation (i ≫ (π ≫ q)) := by rw [hit]; infer_instance
  have hisnd : (pullback.map (e ≫ p) g (π ≫ q) g i (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using hit.symm) (by simp)) ≫
      pullback.snd (π ≫ q) g = pullback.snd (e ≫ p) g := by
    simp [pullback.map]
  have hflat' : Flat ((pullback.map (e ≫ p) g (π ≫ q) g i (𝟙 _) (𝟙 _)
      (by simpa only [Category.comp_id] using hit.symm) (by simp)) ≫
      pullback.snd (π ≫ q) g) := by rw [hisnd]; infer_instance
  have hx' : KoszulAt ((pullback.map (e ≫ p) g p g e (𝟙 _) (𝟙 _) (by simp) (by simp)) ≫
      (pullback.map p g q g f (𝟙 _) (𝟙 _)
        (by simpa only [Category.comp_id] using h.symm) (by simp))) z' :=
    koszulAt_precomp_openImmersion _ _ z' (by rwa [hz'])
  have hloc := koszulAt_of_closed_baseChange (e ≫ f) i π hfac.symm (π ≫ q) _ _ _ hfac'
    (pullback.snd (π ≫ q) g) (pullback.fst (e ≫ p) g) (pullback.fst (π ≫ q) g) g si
    (IsPullback.of_hasPullback (π ≫ q) g) z' hx'
  have hresult := koszulAt_of_precomp_openImmersion f e
    ((pullback.fst (e ≫ p) g) z') hloc
  have hpoint : e ((pullback.fst (e ≫ p) g) z') = (pullback.fst p g) x' := by
    change (pullback.fst (e ≫ p) g ≫ e) z' = _
    rw [se.w]
    change (pullback.fst p g) ((pullback.map (e ≫ p) g p g e (𝟙 _) (𝟙 _)
      (by simp) (by simp)) z') = _
    rw [hz']
  rwa [hpoint] at hresult

/-- **The Koszul locus is open.** A witness for `KoszulAt f x` — an open `U ∋ x` on which `f`
factors through a Koszul-regular immersion into a scheme smooth over the target — witnesses
`KoszulAt f z` for every `z` in `U`, because Koszul-regularity is a condition on the immersion
and not on the point. Intersecting `U` with the affine open witnessing finite type at `x` gives
a neighbourhood of `x` inside the locus. -/
@[stacks 06B8 "the Koszul locus is open"]
public theorem isOpen_koszulAt {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsOpen {x : X | KoszulAt f x} := by
  rw [isOpen_iff_mem_nhds]
  intro x hx
  obtain ⟨⟨V, W, hxW, hWV, hfinite⟩, U, hxU, P, i, π, hi, hkos, hsm, hfac⟩ := hx
  refine mem_nhds_iff.mpr ⟨(U : Set X) ∩ (W.1 : Set X), ?_, U.isOpen.inter W.1.isOpen, hxU, hxW⟩
  intro z hz
  exact ⟨⟨V, W, hz.2, hWV, hfinite⟩, U, hz.1, P, i, π, hi, hkos, hsm, hfac⟩

/-- **The formation of the Koszul locus commutes with arbitrary base change.** Let `f : X ⟶ Y`
be a morphism of schemes over `S` with `X` and `Y` both flat and locally of finite presentation
over `S`. For any `g : S' ⟶ S`, the base change of `f` is Koszul at a point of `X ×_S S'`
exactly when `f` is Koszul at its image in `X`. -/
@[stacks 06B8 "formation of the Koszul locus commutes with arbitrary base change"]
public theorem koszulAt_baseChange_iff {X Y S S' : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S)
    (q : Y ⟶ S) (h : f ≫ q = p) [Flat p] [Flat q] [LocallyOfFinitePresentation p]
    [LocallyOfFinitePresentation q] (g : S' ⟶ S) (x' : (pullback p g : Scheme.{u})) :
    KoszulAt (pullback.map p g q g f (𝟙 _) (𝟙 _)
        (by simpa only [Category.comp_id] using h.symm) (by simp)) x' ↔
      KoszulAt f ((pullback.fst p g).base x') :=
  ⟨koszulAt_baseChange_backward f p q h g x', koszulAt_baseChange_forward f p q h g x'⟩

/-- The Koszul locus of the base change of `f` along `g : S' ⟶ S` is the preimage of the Koszul
locus of `f`, which is `AlgebraicGeometry.koszulAt_baseChange_iff` read as an equality of sets. -/
public theorem preimage_setOf_koszulAt {X Y S S' : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ S)
    (q : Y ⟶ S) (h : f ≫ q = p) [Flat p] [Flat q] [LocallyOfFinitePresentation p]
    [LocallyOfFinitePresentation q] (g : S' ⟶ S) :
    {x' : (pullback p g : Scheme.{u}) | KoszulAt (pullback.map p g q g f (𝟙 _) (𝟙 _)
        (by simpa only [Category.comp_id] using h.symm) (by simp)) x'} =
      (pullback.fst p g).base ⁻¹' {x : X | KoszulAt f x} :=
  Set.ext fun x' => koszulAt_baseChange_iff f p q h g x'

end AlgebraicGeometry

end
