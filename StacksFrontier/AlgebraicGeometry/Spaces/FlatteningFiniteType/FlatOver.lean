module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatteningFiniteType.Local
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcOpenSubspaceDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatIsomorphismLocusOnBase

/-!
# Flatness of a morphism over an open subspace of its target

For a morphism `f : X ⟶ A` of algebraic spaces and an open subspace `N ⊆ A`, `f` is *flat and
locally of finite presentation over `N`* when its restriction `f⁻¹(N) ⟶ N` is.  This file
records how that condition behaves: it may be read on any cartesian square over a morphism into
`N`, it passes to smaller open subspaces and to base changes, and it glues over a cover of `N`
by two open subspaces.

## Main definitions

* `AlgebraicGeometry.Space.FlatOver`: the condition above.

## Main results

* `AlgebraicGeometry.Space.FlatOver.isFlat_and_isLocallyOfFinitePresentation_of_isPullback`:
  every base change of `f⁻¹(N) ⟶ N` is flat and locally of finite presentation.
* `AlgebraicGeometry.Space.flatOver_iff_of_isPullback`: the condition read on one cartesian
  square over `N ⟶ A`.
* `AlgebraicGeometry.Space.FlatOver.mono`, `AlgebraicGeometry.Space.FlatOver.baseChange`,
  `AlgebraicGeometry.Space.FlatOver.of_cover`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Local finite presentation is inherited by base changes: in a cartesian square of algebraic
spaces whose right-hand morphism `f` is locally of finite presentation, so is the left-hand
morphism `a`. -/
theorem isLocallyOfFinitePresentation_of_isPullback_of_isAlgebraicSpace
    {W X' Y' Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {a : W ⟶ Z'} {b : W ⟶ X'} {g : Z' ⟶ Y'} {f : X' ⟶ Y'}
    (sq : IsPullback a b g f) (hW : IsAlgebraicSpace B S hS W) (hX' : IsAlgebraicSpace B S hS X')
    (hY' : IsAlgebraicSpace B S hS Y') (hZ' : IsAlgebraicSpace B S hS Z')
    (hf : IsLocallyOfFinitePresentation B S hS f) :
    IsLocallyOfFinitePresentation B S hS a := by
  let Wa : AlgebraicSpaces B S hS := ⟨W, hW⟩
  let Xa : AlgebraicSpaces B S hS := ⟨X', hX'⟩
  let Ya : AlgebraicSpaces B S hS := ⟨Y', hY'⟩
  let Za : AlgebraicSpaces B S hS := ⟨Z', hZ'⟩
  have sqa : IsPullback (ObjectProperty.homMk b : Wa ⟶ Xa) (ObjectProperty.homMk a : Wa ⟶ Za)
      (ObjectProperty.homMk f : Xa ⟶ Ya) (ObjectProperty.homMk g : Za ⟶ Ya) :=
    IsPullback.of_map_of_faithful (F := ObjectProperty.ι (fun F :
      (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)) sq.flip
  exact (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback sqa hf

/-- `f : X ⟶ A` is flat and locally of finite presentation over the subspace `N ⊆ A`: its
restriction `f⁻¹(N) ⟶ N` is flat and locally of finite presentation. -/
abbrev FlatOver {A X : AlgebraicSpaces B S hS} (f : X ⟶ A) (N : Subfunctor A.1) : Prop :=
  IsFlat B S hS (N.fromPreimage f.hom) ∧ IsLocallyOfFinitePresentation B S hS (N.fromPreimage f.hom)

section FlatOver

variable {A X : AlgebraicSpaces B S hS} {f : X ⟶ A} {N : Subfunctor A.1}

/-- **Every base change of `f⁻¹(N) ⟶ N` is flat and locally of finite presentation**: if `f` is
flat and locally of finite presentation over the open subspace `N`, then so is the left-hand
morphism of any cartesian square over `σ ≫ N.ι` for a morphism `σ` into `N`. -/
theorem FlatOver.isFlat_and_isLocallyOfFinitePresentation_of_isPullback
    (hN : IsOpenSubspace B S hS N) (h : FlatOver f N) {Q R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hQ : IsAlgebraicSpace B S hS Q) (hR : IsAlgebraicSpace B S hS R) (σ : Q ⟶ N.toFunctor)
    {a : R ⟶ X.1} {q : R ⟶ Q} (hsq : IsPullback a q f.hom (σ ≫ N.ι)) :
    IsFlat B S hS q ∧ IsLocallyOfFinitePresentation B S hS q := by
  have hP := (isOpenSubspace_preimage B S hS f.hom N A.2 X.2 hN).1
  have sqN : IsPullback (N.preimage f.hom).ι (N.fromPreimage f.hom) f.hom N.ι :=
    (Subfunctor.isPullback_preimage f.hom N).flip
  have hw : a ≫ f.hom = (q ≫ σ) ≫ N.ι := hsq.w.trans (Category.assoc _ _ _).symm
  have hsq' : IsPullback (sqN.lift a (q ≫ σ) hw) q (N.fromPreimage f.hom) σ :=
    IsPullback.of_right (by rwa [sqN.lift_fst]) (sqN.lift_snd _ _ _) sqN
  exact ⟨isFlat_of_isPullback_of_isAlgebraicSpace B S hS hsq'.flip hP hN.1 h.1,
    isLocallyOfFinitePresentation_of_isPullback_of_isAlgebraicSpace hsq'.flip hR hP hN.1 hQ h.2⟩

/-- **The condition read on one cartesian square**: `f` is flat and locally of finite
presentation over the open subspace `N` exactly when the left-hand morphism of one (equivalently
every) cartesian square over `N.ι` is. -/
theorem flatOver_iff_of_isPullback (hN : IsOpenSubspace B S hS N)
    {R : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hR : IsAlgebraicSpace B S hS R) {a : R ⟶ X.1}
    {q : R ⟶ N.toFunctor} (hsq : IsPullback a q f.hom N.ι) :
    FlatOver f N ↔ IsFlat B S hS q ∧ IsLocallyOfFinitePresentation B S hS q := by
  have hP := (isOpenSubspace_preimage B S hS f.hom N A.2 X.2 hN).1
  refine ⟨fun h => h.isFlat_and_isLocallyOfFinitePresentation_of_isPullback hN hN.1 hR (𝟙 _)
    (by rwa [Category.id_comp]), fun h => ?_⟩
  have sqN : IsPullback (N.preimage f.hom).ι (N.fromPreimage f.hom) f.hom N.ι :=
    (Subfunctor.isPullback_preimage f.hom N).flip
  change IsFlat B S hS (N.fromPreimage f.hom) ∧
    IsLocallyOfFinitePresentation B S hS (N.fromPreimage f.hom)
  rw [← sqN.isoIsPullback_hom_snd _ _ hsq]
  exact ⟨isFlat_comp B S hS hP hR hN.1 _ _ (isFlat_of_isEtale B S hS (isEtale_of_isIso B S hS _))
      h.1,
    isLocallyOfFinitePresentation_comp B S hS hP hR hN.1 _ _
      (isLocallyOfFinitePresentation_of_isEtale B S hS (isEtale_of_isIso B S hS _)) h.2⟩

/-- **The condition passes to smaller open subspaces.** -/
theorem FlatOver.mono (hN : IsOpenSubspace B S hS N) (h : FlatOver f N) {N' : Subfunctor A.1}
    (hN' : IsOpenSubspace B S hS N') (hle : N' ≤ N) : FlatOver f N' := by
  have hP := (isOpenSubspace_preimage B S hS f.hom N' A.2 X.2 hN').1
  exact h.isFlat_and_isLocallyOfFinitePresentation_of_isPullback hN hN'.1 hP
    (Subfunctor.homOfLe hle)
    (by rw [Subfunctor.homOfLe_ι]; exact (Subfunctor.isPullback_preimage f.hom N').flip)

/-- **The condition passes to base changes**: if `f` is flat and locally of finite presentation
over the open subspace `N`, then for a cartesian square `X' = X ×_A A'` the base change
`w : X' ⟶ A'` is flat and locally of finite presentation over the inverse image of `N`. -/
theorem FlatOver.baseChange (hN : IsOpenSubspace B S hS N) (h : FlatOver f N)
    {A' X' : AlgebraicSpaces B S hS} {u : X' ⟶ X} {w : X' ⟶ A'} {v : A' ⟶ A}
    (hU : IsPullback u.hom w.hom f.hom v.hom) : FlatOver w (N.preimage v.hom) := by
  have hN' := isOpenSubspace_preimage B S hS v.hom N A.2 A'.2 hN
  have hP := (isOpenSubspace_preimage B S hS w.hom (N.preimage v.hom) A'.2 X'.2 hN').1
  refine h.isFlat_and_isLocallyOfFinitePresentation_of_isPullback hN hN'.1 hP
    (N.fromPreimage v.hom) (a := ((N.preimage v.hom).preimage w.hom).ι ≫ u.hom) ?_
  rw [Subfunctor.fromPreimage_ι]
  exact (Subfunctor.isPullback_preimage w.hom (N.preimage v.hom)).flip.paste_horiz hU

/-- **The condition glues over a cover by two open subspaces**: if `f` is flat and locally of
finite presentation over open subspaces `N₁, N₂ ⊆ N` whose points cover those of `N`, it is so
over `N`. -/
theorem FlatOver.of_cover (hN : IsOpenSubspace B S hS N) {N₁ N₂ : Subfunctor A.1}
    (hN₁ : IsOpenSubspace B S hS N₁) (hN₂ : IsOpenSubspace B S hS N₂) (h₁ : N₁ ≤ N)
    (h₂ : N₂ ≤ N)
    (hcov : subspacePointSet B S hS A.1 N ⊆
      subspacePointSet B S hS A.1 N₁ ∪ subspacePointSet B S hS A.1 N₂)
    (hf₁ : FlatOver f N₁) (hf₂ : FlatOver f N₂) : FlatOver f N := by
  have hP := (isOpenSubspace_preimage B S hS f.hom N A.2 X.2 hN).1
  let Ni : Bool → Subfunctor A.1 := fun | false => N₁ | true => N₂
  have hNi : ∀ j, IsOpenSubspace B S hS (Ni j) := fun | false => hN₁ | true => hN₂
  have hle : ∀ j, Ni j ≤ N := fun | false => h₁ | true => h₂
  have hfi : ∀ j, FlatOver f (Ni j) := fun | false => hf₁ | true => hf₂
  have hQ : ∀ j, IsOpenSubspace B S hS ((Ni j).preimage N.ι) := fun j =>
    isOpenSubspace_preimage B S hS N.ι (Ni j) A.2 hN.1 (hNi j)
  let Q : Bool → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u := fun j => ((Ni j).preimage N.ι).toFunctor
  let e : ∀ j, Q j ⟶ N.toFunctor := fun j => ((Ni j).preimage N.ι).ι
  have hcov' : IsFppfCovering B S hS Q e := by
    refine ⟨hN.1, fun j => (hQ j).1, fun j => isFlat_of_isEtale B S hS
      (isEtale_of_isOpenImmersion B S hS (hQ j).2),
      fun j => isLocallyOfFinitePresentation_of_isEtale B S hS
        (isEtale_of_isOpenImmersion B S hS (hQ j).2), ?_⟩
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨j, hj⟩ : ∃ j, pointsMap B S hS N.toFunctor N.ι x ∈
        subspacePointSet B S hS A.1 (Ni j) := by
      rcases hcov ⟨x, rfl⟩ with hx | hx
      exacts [⟨false, hx⟩, ⟨true, hx⟩]
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    change x ∈ Set.range (pointsMap B S hS ((Ni j).preimage N.ι).toFunctor
      ((Ni j).preimage N.ι).ι)
    rwa [range_pointsMap_preimage_ι]
  refine isFlat_and_isLocallyOfFinitePresentation_of_boolCovering
    (P := ⟨(N.preimage f.hom).toFunctor, hP⟩) (Y := ⟨N.toFunctor, hN.1⟩)
    (ObjectProperty.homMk (N.fromPreimage f.hom)) Q e hcov' fun j => ?_
  have hR := (isOpenSubspace_preimage B S hS (N.fromPreimage f.hom) ((Ni j).preimage N.ι)
    hN.1 hP (hQ j)).1
  refine ⟨_, hR, _, _, (Subfunctor.isPullback_preimage (N.fromPreimage f.hom)
    ((Ni j).preimage N.ι)).flip, ?_⟩
  refine (hfi j).isFlat_and_isLocallyOfFinitePresentation_of_isPullback (hNi j) (hQ j).1 hR
    ((Ni j).fromPreimage N.ι)
    (a := (((Ni j).preimage N.ι).preimage (N.fromPreimage f.hom)).ι ≫ (N.preimage f.hom).ι) ?_
  rw [Subfunctor.fromPreimage_ι]
  exact (Subfunctor.isPullback_preimage (N.fromPreimage f.hom)
    ((Ni j).preimage N.ι)).flip.paste_horiz (Subfunctor.isPullback_preimage f.hom N).flip

end FlatOver

end AlgebraicGeometry.Space

end
