module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Limits.EtalePullbackMap
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentationAffine

/-!
# Shrinking a common étale neighbourhood to affine opens

Let `fX : X ⟶ S` and `gY : Y ⟶ T` be locally of finite type, let `bS : Z ⟶ S` and `bT : Z ⟶ T`
with `Z` affine and Noetherian, and let `Usch` be a scheme étale over both base changes
`X ×_S Z` and `Y ×_T Z`, with the two structure morphisms agreeing over `Z` and inducing
isomorphisms on the residue field at a point `u`. Replacing `X` and `Y` by affine open
neighbourhoods of the images of `u`, and `Usch` by an affine open neighbourhood of `u`, one may
assume in addition that everything in sight is of *finite* presentation.

This is the step "after replacing `X`, `S`, `T`, `Y` by affine open subschemes we may assume …"
of the proof of Stacks Tag 0GDX. The reduction is needed because the descent lemmas of Tag 01ZM
ask their input to be of finite presentation, not merely locally so.

## Main results

* `AlgebraicGeometry.isPullback_pullbackMapOver`: the base change over `B` of a morphism
  `a : U ⟶ A` along `i : V ⟶ B` sits in a pullback square over `a`.
* `AlgebraicGeometry.exists_preimage_pullbackMapOver`: consequently a point of `A ×_B V` whose
  image in `A` lifts to `U` lifts to `U ×_B V`.
* `AlgebraicGeometry.exists_affine_shrink_common_neighborhood`: the reduction itself.

## Implementation notes

The point membership of step 2 of the reduction — that `al u` lies in the open range of the base
change of the affine open immersion `X₀ ⟶ X` — is produced from
`AlgebraicGeometry.Scheme.exists_preimage_of_isPullback` rather than from a range computation;
the pullback square it needs is `AlgebraicGeometry.isPullback_pullbackMapOver`, obtained from
`AlgebraicGeometry.pullbackMapOver_eq` and
`CategoryTheory.Limits.pullbackRightPullbackFstIso_inv_fst`.

The two lifted morphisms are built with `AlgebraicGeometry.IsOpenImmersion.lift`, so the two
factorization identities are `AlgebraicGeometry.IsOpenImmersion.lift_fac` and every other
property of the lifts is deduced from them: étaleness by cancelling the open immersion on the
right, the residue field isomorphisms by
`AlgebraicGeometry.isIso_residueFieldMap_left_of_isIso_residueFieldMap_comp`, and the commuting
square over `Z` by `AlgebraicGeometry.pullbackMapOver_snd`.

Finite presentation of the structure morphism of the shrunk neighbourhood over `Z` uses that both
its source and `Z` are affine, so that the locally finite type hypothesis suffices by
`AlgebraicGeometry.finitePresentation_of_isAffine_of_locallyOfFiniteType`; this is where `Z` is
required to be affine and Noetherian.

## References

* [Stacks Project, Tag 0GDX](https://stacks.math.columbia.edu/tag/0GDX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **The base change over `B` of `a : U ⟶ A` along `i : V ⟶ B` sits in a pullback square over
`a`.** Writing `U ×_B V` as `U ×_A (A ×_B V)` is exactly this square. -/
public theorem isPullback_pullbackMapOver {B U A V : Scheme.{u}} (pA : A ⟶ B) (a : U ⟶ A)
    (i : V ⟶ B) :
    IsPullback (pullback.fst (a ≫ pA) i) (pullbackMapOver pA (a ≫ pA) a rfl i) a
      (pullback.fst pA i) :=
  IsPullback.of_iso_pullback ⟨(pullbackMapOver_fst ..).symm⟩
    (pullbackRightPullbackFstIso pA i a).symm (pullbackRightPullbackFstIso_inv_fst ..)
    (pullbackMapOver_eq pA a i).symm

/-- A point of `A ×_B V` whose image under the first projection lifts along `a : U ⟶ A` lifts to
a point of `U ×_B V`. This is how one checks that a point of a base change lies in the open
range of the base change of an open immersion. -/
public theorem exists_preimage_pullbackMapOver {B U A V : Scheme.{u}} (pA : A ⟶ B) (a : U ⟶ A)
    (i : V ⟶ B) (w : ↥(pullback pA i)) (x : U) (hx : a x = pullback.fst pA i w) :
    ∃ p : ↥(pullback (a ≫ pA) i), pullbackMapOver pA (a ≫ pA) a rfl i p = w :=
  let ⟨p, _, hp⟩ := Scheme.exists_preimage_of_isPullback (isPullback_pullbackMapOver pA a i) x w hx
  ⟨p, hp⟩

/-- A point of `A ×_B V` over a point of an open `O ⊆ A` lies in the range of the base change
of `O.ι`. -/
private theorem mem_range_pullbackMapOver_opensι {B A V : Scheme.{u}} (pA : A ⟶ B) (i : V ⟶ B)
    (O : A.Opens) (z : ↥(pullback pA i)) (hz : pullback.fst pA i z ∈ O) :
    z ∈ Set.range (pullbackMapOver pA (O.ι ≫ pA) O.ι rfl i) :=
  let ⟨p, hp⟩ := exists_preimage_pullbackMapOver pA O.ι i z ⟨_, hz⟩ rfl
  ⟨p, hp⟩

/-- An open immersion `m` with a morphism `j ≫ f` landing in its range: the lift of `j ≫ f`
through `m` is étale and trivial on residue fields at `w`, if `f` is trivial at `j w`. -/
private theorem exists_lift_etale_isIso_residueFieldMap {V A U W : Scheme.{u}} (m : V ⟶ A)
    [IsOpenImmersion m] (j : W ⟶ U) [IsOpenImmersion j] (f : U ⟶ A) [Etale f]
    (hsub : ∀ w, f (j w) ∈ Set.range m) (w : W) (h : IsIso (f.residueFieldMap (j w))) :
    ∃ g : W ⟶ V, g ≫ m = j ≫ f ∧ Etale g ∧ IsIso (g.residueFieldMap w) := by
  have hsub' : Set.range (j ≫ f) ⊆ Set.range m := by
    rintro _ ⟨w, rfl⟩
    exact hsub w
  have hg := IsOpenImmersion.lift_fac m (j ≫ f) hsub'
  have : Etale (IsOpenImmersion.lift m (j ≫ f) hsub' ≫ m) := by
    rw [hg]
    infer_instance
  refine ⟨IsOpenImmersion.lift m (j ≫ f) hsub', hg, Etale.of_comp _ m, ?_⟩
  refine isIso_residueFieldMap_left_of_isIso_residueFieldMap_comp _ m w ?_
  rw [hg]
  exact isIso_residueFieldMap_isOpenImmersion_comp j f w h

/-- **After replacing `X` and `Y` by affine open subschemes, and the common étale neighbourhood by
an affine open neighbourhood of its marked point, everything in sight is of finite
presentation.**

This is the reduction to affine opens at the start of the proof of Stacks Tag 0GDX. The data
`al`, `be` is a scheme `Usch` étale over both `X ×_S Z` and `Y ×_T Z`, agreeing over `Z` and
trivial on the residue field at `u`; the conclusion produces affine open neighbourhoods
`X' ⊆ X`, `Y' ⊆ Y` of the images of `u` and an affine open neighbourhood `U' ⊆ Usch` of `u`
carrying the same data over the shrunk schemes, compatibly with the open immersions, and with
`X' ⟶ S`, `Y' ⟶ T` and `U' ⟶ Z` of finite presentation. -/
public theorem exists_affine_shrink_common_neighborhood
    {S T X Y Z : Scheme.{u}} [IsLocallyNoetherian S] [IsLocallyNoetherian T]
    [IsAffine Z] [IsNoetherian Z]
    (fX : X ⟶ S) (gY : Y ⟶ T) [LocallyOfFiniteType fX] [LocallyOfFiniteType gY]
    (bS : Z ⟶ S) (bT : Z ⟶ T)
    (Usch : Scheme.{u}) (u : Usch)
    (al : Usch ⟶ pullback fX bS) (be : Usch ⟶ pullback gY bT)
    (hale : Etale al) (hbee : Etale be)
    (hcomm : al ≫ pullback.snd fX bS = be ≫ pullback.snd gY bT)
    (halres : IsIso (al.residueFieldMap u)) (hberes : IsIso (be.residueFieldMap u)) :
    ∃ (X' Y' : Scheme.{u}) (jX : X' ⟶ X) (jY : Y' ⟶ Y),
      IsOpenImmersion jX ∧ IsOpenImmersion jY ∧
      FinitePresentation (jX ≫ fX) ∧ FinitePresentation (jY ≫ gY) ∧
      ∃ (U' : Scheme.{u}) (u' : U') (jU : U' ⟶ Usch),
        IsOpenImmersion jU ∧ jU u' = u ∧
        ∃ (al' : U' ⟶ pullback (jX ≫ fX) bS) (be' : U' ⟶ pullback (jY ≫ gY) bT),
          Etale al' ∧ Etale be' ∧
          IsIso (al'.residueFieldMap u') ∧ IsIso (be'.residueFieldMap u') ∧
          FinitePresentation (al' ≫ pullback.snd (jX ≫ fX) bS) ∧
          al' ≫ pullback.snd (jX ≫ fX) bS = be' ≫ pullback.snd (jY ≫ gY) bT ∧
          al' ≫ pullbackMapOver fX (jX ≫ fX) jX rfl bS = jU ≫ al ∧
          be' ≫ pullbackMapOver gY (jY ≫ gY) jY rfl bT = jU ≫ be := by
  have := hale
  have := hbee
  -- Step 1: affine open neighbourhoods of the two images of `u`.
  obtain ⟨X₀, hX₀aff, hX₀mem, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (x := pullback.fst fX bS (al u)) (U := ⊤) trivial
  obtain ⟨Y₀, hY₀aff, hY₀mem, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := Y) (x := pullback.fst gY bT (be u)) (U := ⊤) trivial
  have : IsAffine X₀.toScheme := hX₀aff
  have : IsAffine Y₀.toScheme := hY₀aff
  -- Step 2: the base changes of the two open immersions, and the point `u` in their ranges.
  set mX := pullbackMapOver fX (X₀.ι ≫ fX) X₀.ι rfl bS with hmX
  set mY := pullbackMapOver gY (Y₀.ι ≫ gY) Y₀.ι rfl bT with hmY
  have : IsOpenImmersion mX := isOpenImmersion_pullbackMapOver fX _ X₀.ι rfl bS
  have : IsOpenImmersion mY := isOpenImmersion_pullbackMapOver gY _ Y₀.ι rfl bT
  have hrangeX : al u ∈ Set.range mX := mem_range_pullbackMapOver_opensι fX bS X₀ _ hX₀mem
  have hrangeY : be u ∈ Set.range mY := mem_range_pullbackMapOver_opensι gY bT Y₀ _ hY₀mem
  -- Step 3: an affine open neighbourhood of `u` inside both preimages.
  set W₀ : Usch.Opens := al ⁻¹ᵁ mX.opensRange ⊓ be ⁻¹ᵁ mY.opensRange with hW₀
  have huW : u ∈ W₀ := ⟨hrangeX, hrangeY⟩
  obtain ⟨U₀, hU₀aff, hU₀mem, hU₀le⟩ := exists_isAffineOpen_mem_and_subset huW
  have : IsAffine U₀.toScheme := hU₀aff
  have hιmem : ∀ w : U₀.toScheme, (U₀.ι w : Usch) ∈ W₀ := fun w => hU₀le w.2
  -- Step 4: lifting `al` and `be` to the shrunk base changes.
  obtain ⟨al', hal', _, hresX⟩ := exists_lift_etale_isIso_residueFieldMap mX U₀.ι al
    (fun w => (hιmem w).1) ⟨u, hU₀mem⟩ halres
  obtain ⟨be', hbe', _, hresY⟩ := exists_lift_etale_isIso_residueFieldMap mY U₀.ι be
    (fun w => (hιmem w).2) ⟨u, hU₀mem⟩ hberes
  -- Step 6: finite presentation, and the commuting square over `Z`.
  have hfpX : FinitePresentation (X₀.ι ≫ fX) := finitePresentation_opens_ι_comp fX X₀ hX₀aff
  have hfpY : FinitePresentation (Y₀.ι ≫ gY) := finitePresentation_opens_ι_comp gY Y₀ hY₀aff
  have hfp : FinitePresentation (al' ≫ pullback.snd (X₀.ι ≫ fX) bS) := by
    have : LocallyOfFiniteType (pullback.snd (X₀.ι ≫ fX) bS) := inferInstance
    have : LocallyOfFiniteType (al' ≫ pullback.snd (X₀.ι ≫ fX) bS) := inferInstance
    exact finitePresentation_of_isAffine_of_locallyOfFiniteType _
  have hsq : al' ≫ pullback.snd (X₀.ι ≫ fX) bS = be' ≫ pullback.snd (Y₀.ι ≫ gY) bT := by
    rw [← pullbackMapOver_snd fX (X₀.ι ≫ fX) X₀.ι rfl bS,
      ← pullbackMapOver_snd gY (Y₀.ι ≫ gY) Y₀.ι rfl bT, ← hmX, ← hmY,
      ← Category.assoc, ← Category.assoc, hal', hbe', Category.assoc, Category.assoc, hcomm]
  exact ⟨X₀.toScheme, Y₀.toScheme, X₀.ι, Y₀.ι, inferInstance, inferInstance, hfpX, hfpY,
    U₀.toScheme, ⟨u, hU₀mem⟩, U₀.ι, inferInstance, rfl, al', be', inferInstance, inferInstance,
    hresX, hresY, hfp, hsq, hal', hbe'⟩

end AlgebraicGeometry

end
