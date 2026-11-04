module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.PseudoCoherentFrom
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineSpaceSiteObject
public import StacksFrontier.AlgebraicGeometry.Spaces.RestrictSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemePointsAffineHom
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteObjectBaseChangeAffine
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts

/-!
# The affine-space bundles of Stacks 0F9U and the chain between them

Step 2 of the proof of Stacks 0F9U takes the affine-space bundles `T₁ → V` and `T' → Y'` of
Stacks 0F82 for two components of a glueing triple and identifies the two affine spaces
`A^{n'}_{T₁}` and `A^{n₁}_{T'}` after base change to `U'`, through the chain

```
A^{n'}_{T₁ ×_V V'} ≅ T₁ ×_V V' ×_{Y'} T' ≅ A^{n₁}_{V' ×_{Y'} T'}.
```

This module does that inside the big fppf site, where the components of a glueing triple live:
the bundles are morphisms of the site, the base changes are `CategoryTheory.Over.pullback`, and
the chain is an isomorphism of objects of the site over `U'` compatible with the two maps down to
the middle component of the triple.

## Main definitions

* `AlgebraicGeometry.IsAffineSpaceBundle`: the conclusion of Stacks 0F82 for a morphism of
  schemes, that its base change along every morphism from an affine scheme is affine `n`-space.
* `AlgebraicGeometry.BigFppfOver.isoOfToScheme`: an isomorphism of the big fppf category over
  `S` from an isomorphism of underlying schemes compatible with the structure morphisms.

## Main results

* `AlgebraicGeometry.IsAffineSpaceBundle.of_isPullback`: the property is stable under base change.
* `AlgebraicGeometry.IsAffineSpaceBundle.flat`,
  `AlgebraicGeometry.IsAffineSpaceBundle.locallyOfFinitePresentation` and
  `AlgebraicGeometry.IsAffineSpaceBundle.surjective`: an affine-space bundle is flat, locally of
  finite presentation and surjective.
* `AlgebraicGeometry.BigFppfOver.exists_affineSpacePullbackIso`: affine space commutes with base
  change of the site.
* `AlgebraicGeometry.BigFppfOver.exists_isPullback_affineSpace_of_isAffineSpaceBundle`: affine
  `n`-space over an affine object `L` is the fibre product of `L` with an affine `n`-space bundle.
* `AlgebraicGeometry.BigFppfOver.exists_affineSpace_chain`: **Stacks 0F9U, step 2**, the chain
  between the two base changes, compatible with the maps to the middle component.

## References

* [Stacks Project, Tag 0F82](https://stacks.math.columbia.edu/tag/0F82)
* [Stacks Project, Tag 0F9U](https://stacks.math.columbia.edu/tag/0F9U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Affine-space bundles -/

/-- **The conclusion of Stacks 0F82 for a morphism.** A morphism `p : T ⟶ X` is an *affine
`n`-space bundle* when its base change along every morphism from an affine scheme `X'` is affine
`n`-space over `X'`. -/
abbrev IsAffineSpaceBundle (n : ℕ) {T X : Scheme.{u}} (p : T ⟶ X) : Prop :=
  ∀ (X' : Scheme.{u}) (_ : IsAffine X') (k : X' ⟶ X),
    Nonempty (Over.mk (pullback.fst k p) ≅
      Over.mk (AffineSpace.over (ULift.{u} (Fin n)) X').hom)

namespace IsAffineSpaceBundle

/-- **Base change of an affine-space bundle is an affine-space bundle.** -/
theorem of_isPullback {n : ℕ} {T X T' X' : Scheme.{u}} {p : T ⟶ X} {p' : T' ⟶ X'}
    {a : T' ⟶ T} {k : X' ⟶ X} (sq : IsPullback a p' p k) (hp : IsAffineSpaceBundle n p) :
    IsAffineSpaceBundle n p' := by
  intro X'' hX'' k'
  obtain ⟨e⟩ := hp X'' hX'' (k' ≫ k)
  have hpb : IsPullback (pullback.fst k' p') (pullback.snd k' p' ≫ a) (k' ≫ k) p :=
    ((IsPullback.of_hasPullback k' p').flip.paste_horiz sq).flip
  exact ⟨Over.isoMk (g := Over.mk (pullback.fst (k' ≫ k) p)) hpb.isoPullback
    hpb.isoPullback_hom_fst ≪≫ e⟩

/-- **Post-composing an affine-space bundle with an isomorphism.** -/
theorem comp_iso {n : ℕ} {T X Y : Scheme.{u}} {p : T ⟶ X} (hp : IsAffineSpaceBundle n p)
    (i : X ≅ Y) : IsAffineSpaceBundle n (p ≫ i.hom) :=
  of_isPullback (a := 𝟙 T) (k := i.inv) (IsPullback.of_horiz_isIso ⟨by simp⟩) hp

/-- A property local on the target for the Zariski topology which holds for the projection of
affine space over every affine scheme holds for every affine-space bundle. -/
theorem prop {n : ℕ} (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    [IsZariskiLocalAtTarget P]
    (hP : ∀ (V : Scheme.{u}), IsAffine V → P (𝔸(ULift.{u} (Fin n); V) ↘ V))
    {T X : Scheme.{u}} {p : T ⟶ X} (hp : IsAffineSpaceBundle n p) : P p := by
  refine IsZariskiLocalAtTarget.of_iSup_eq_top
    (fun V : X.affineOpens => (V : X.Opens)) (iSup_affineOpens_eq_top X) fun V => ?_
  have hVaff : IsAffine (V.1 : Scheme.{u}) := V.2
  obtain ⟨e⟩ := hp (V.1 : Scheme.{u}) hVaff V.1.ι
  have : IsIso e.hom.left := ((Over.forget (V.1 : Scheme.{u})).mapIso e).isIso_hom
  have hw : e.hom.left ≫ (𝔸(ULift.{u} (Fin n); (V.1 : Scheme.{u})) ↘ (V.1 : Scheme.{u})) =
      pullback.fst V.1.ι p := Over.w e.hom
  have hfst : P (pullback.fst V.1.ι p) := by
    rw [← hw]
    exact (MorphismProperty.cancel_left_of_respectsIso (P := P) e.hom.left _).mpr
      (hP _ hVaff)
  have hsnd : P (pullback.snd p V.1.ι) := by
    rw [← pullbackSymmetry_hom_comp_fst p V.1.ι]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (P := P) (pullbackSymmetry p V.1.ι).hom _).mpr hfst
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict p V.1] at hsnd
  exact (MorphismProperty.cancel_left_of_respectsIso
    (P := P) (pullbackRestrictIsoRestrict p V.1).hom _).mp hsnd

/-- `prop` for a base-change stable property given by a local ring-hom property. -/
private theorem prop_of_hasRingHomProperty {n : ℕ} (P : MorphismProperty Scheme.{u})
    {Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    [HasRingHomProperty P Q] [P.IsStableUnderBaseChange]
    (hP : ∀ (V : Scheme.{u}), IsAffine V → P (𝔸(ULift.{u} (Fin n); V) ↘ V))
    {T X : Scheme.{u}} {p : T ⟶ X} (hp : IsAffineSpaceBundle n p) : P p :=
  have := MorphismProperty.IsStableUnderBaseChange.respectsIso (P := P)
  prop P hP hp

/-- An affine-space bundle is flat. -/
theorem flat {n : ℕ} {T X : Scheme.{u}} {p : T ⟶ X} (hp : IsAffineSpaceBundle n p) : Flat p :=
  prop_of_hasRingHomProperty (@Flat.{u}) (fun V _ => flat_affineSpace _ V) hp

/-- An affine-space bundle is locally of finite presentation. -/
theorem locallyOfFinitePresentation {n : ℕ} {T X : Scheme.{u}} {p : T ⟶ X}
    (hp : IsAffineSpaceBundle n p) : LocallyOfFinitePresentation p :=
  prop_of_hasRingHomProperty (@LocallyOfFinitePresentation.{u}) (fun _ _ => inferInstance) hp

/-- An affine-space bundle is surjective. -/
theorem surjective {n : ℕ} {T X : Scheme.{u}} {p : T ⟶ X} (hp : IsAffineSpaceBundle n p) :
    Surjective p :=
  prop (@Surjective.{u}) (fun _ _ => inferInstance) hp

end IsAffineSpaceBundle

/-! ### Isomorphisms and fibre products of the site from those of schemes -/

namespace BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An isomorphism of the big fppf category over `S` from one of underlying schemes** which
commutes with the two structure morphisms. -/
noncomputable def isoOfToScheme {T W : BigFppfOver B S hS}
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ (BigFppfOver.toScheme B S hS).obj W)
    (he : e.hom ≫ B.inclusion.map W.hom = B.inclusion.map T.hom) : T ≅ W where
  hom := BigFppfOver.homOfCompEq B S hS e.hom he
  inv := BigFppfOver.homOfCompEq B S hS e.inv (by rw [← he, e.inv_hom_id_assoc])
  hom_inv_id := by
    apply BigFppfOver.map_toScheme_injective B S hS
    dsimp only
    rw [Functor.map_comp, toScheme_map_homOfCompEq, toScheme_map_homOfCompEq, e.hom_inv_id,
      CategoryTheory.Functor.map_id]
  inv_hom_id := by
    apply BigFppfOver.map_toScheme_injective B S hS
    dsimp only
    rw [Functor.map_comp, toScheme_map_homOfCompEq, toScheme_map_homOfCompEq, e.inv_hom_id,
      CategoryTheory.Functor.map_id]

/-- The morphism of schemes underlying `isoOfToScheme B S hS e he` is `e.hom`. -/
@[simp]
theorem toScheme_map_isoOfToScheme_hom {T W : BigFppfOver B S hS}
    (e : (BigFppfOver.toScheme B S hS).obj T ≅ (BigFppfOver.toScheme B S hS).obj W)
    (he : e.hom ≫ B.inclusion.map W.hom = B.inclusion.map T.hom) :
    (BigFppfOver.toScheme B S hS).map (isoOfToScheme B S hS e he).hom = e.hom :=
  BigFppfOver.toScheme_map_homOfCompEq B S hS e.hom he

/-- The square of schemes underlying the base change of an object of the site along a morphism
of the site is cartesian. -/
theorem isPullback_toScheme_pullback {S' : Scheme.{u}} {hS' : B.Contains S'}
    (g : B.obj hS' ⟶ B.obj hS) (A : BigFppfOver B S hS) :
    IsPullback (B.inclusion.map (pullback.fst A.hom g)) (B.inclusion.map (pullback.snd A.hom g))
      (B.inclusion.map A.hom) (B.inclusion.map g) :=
  Functor.map_isPullback B.inclusion (IsPullback.of_hasPullback A.hom g)

/-- The square of schemes underlying the base change of a morphism of the site is cartesian:
`CategoryTheory.Over.pullback` acts on a morphism by base change. -/
theorem isPullback_toScheme_pullback_map {S' : Scheme.{u}} {hS' : B.Contains S'}
    (g : B.obj hS' ⟶ B.obj hS) {A A' : BigFppfOver B S hS} (k : A ⟶ A') :
    IsPullback ((BigFppfOver.toScheme B S' hS').map ((Over.pullback g).map k))
      (B.inclusion.map (pullback.fst A.hom g))
      (B.inclusion.map (pullback.fst A'.hom g)) ((BigFppfOver.toScheme B S hS).map k) :=
  Functor.map_isPullback B.inclusion (OverShriek.isPullback_pullback_map g k)

/-! ### Affine space and base change -/

/-- **Affine space commutes with base change of the site.** For an affine object `T` over `S`
and a morphism `g : S' ⟶ S` of the site along which `T` stays affine, the base change of
`A^n_T` along `g` is `A^n` over the base change of `T`, compatibly with the two projections. -/
theorem exists_affineSpacePullbackIso (n : ℕ) {S' : Scheme.{u}} {hS' : B.Contains S'}
    (g : B.obj hS' ⟶ B.obj hS) (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T))
    (hT' : IsAffine ((BigFppfOver.toScheme B S' hS').obj ((Over.pullback g).obj T))) :
    ∃ e : (Over.pullback g).obj (BigFppfOver.affineSpace B S hS n T hT) ≅
        BigFppfOver.affineSpace B S' hS' n ((Over.pullback g).obj T) hT',
      e.hom ≫ BigFppfOver.affineSpaceProj B S' hS' n _ hT' =
        (Over.pullback g).map (BigFppfOver.affineSpaceProj B S hS n T hT) := by
  let Ts := BigFppfOver.toScheme B S' hS'
  let A := BigFppfOver.affineSpace B S hS n T hT
  have hT0 := isPullback_toScheme_pullback B S hS g T
  have hA := isPullback_affineSpace_paste (n := ULift.{u} (Fin n)) _ _ _ _ hT0
  have hB := isPullback_toScheme_pullback B S hS g A
  let P := Ts.obj ((Over.pullback g).obj T)
  let e₀ : Ts.obj ((Over.pullback g).obj A) ≅ 𝔸(ULift.{u} (Fin n); P) :=
    hB.isoIsPullback _ _ hA
  have hfst : e₀.hom ≫ AffineSpace.map (ULift.{u} (Fin n))
      (B.inclusion.map (pullback.fst T.hom g)) = B.inclusion.map (pullback.fst A.hom g) :=
    hB.isoIsPullback_hom_fst _ _ hA
  have hsnd : e₀.hom ≫ ((𝔸(ULift.{u} (Fin n); P) ↘ P) ≫
      B.inclusion.map (pullback.snd T.hom g)) = B.inclusion.map (pullback.snd A.hom g) :=
    hB.isoIsPullback_hom_snd _ _ hA
  have hgoal : e₀.hom ≫ (𝔸(ULift.{u} (Fin n); P) ↘ P) =
      Ts.map ((Over.pullback g).map (BigFppfOver.affineSpaceProj B S hS n T hT)) := by
    apply hT0.hom_ext
    · calc (e₀.hom ≫ (𝔸(ULift.{u} (Fin n); P) ↘ P)) ≫ B.inclusion.map (pullback.fst T.hom g)
          = e₀.hom ≫ ((𝔸(ULift.{u} (Fin n); P) ↘ P) ≫
              B.inclusion.map (pullback.fst T.hom g)) := Category.assoc _ _ _
        _ = e₀.hom ≫ (AffineSpace.map (ULift.{u} (Fin n))
              (B.inclusion.map (pullback.fst T.hom g)) ≫
              (𝔸(ULift.{u} (Fin n); B.inclusion.obj T.left) ↘ B.inclusion.obj T.left)) :=
            congrArg (e₀.hom ≫ ·) (AffineSpace.map_over (n := ULift.{u} (Fin n))
              (B.inclusion.map (pullback.fst T.hom g))).symm
        _ = B.inclusion.map (pullback.fst A.hom g) ≫
              (𝔸(ULift.{u} (Fin n); B.inclusion.obj T.left) ↘ B.inclusion.obj T.left) :=
            (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hfst)
        _ = _ := ((isPullback_toScheme_pullback_map B S hS g
            (BigFppfOver.affineSpaceProj B S hS n T hT)).w).symm
    · rw [Category.assoc, hsnd]
      exact (BigFppfOver.toScheme_map_comp_hom
        ((Over.pullback g).map (BigFppfOver.affineSpaceProj B S hS n T hT))).symm
  refine ⟨isoOfToScheme B S' hS' e₀ hsnd, ?_⟩
  apply BigFppfOver.map_toScheme_injective B S' hS'
  dsimp only
  rw [Functor.map_comp]
  exact (congrArg (fun x => x ≫ _) (toScheme_map_isoOfToScheme_hom B S' hS' _ hsnd)).trans hgoal

/-! ### Affine space over `L` as a fibre product with a bundle -/

/-- **Stacks 0F82, read in the site.** Let `r : R ⟶ Q` be a morphism of the big fppf category
over `S` whose underlying morphism of schemes is an affine `n`-space bundle, and let `l : L ⟶ Q`
have affine source. Then `A^n_L`, with its projection to `L`, is the fibre product of `l` and
`r`. -/
theorem exists_isPullback_affineSpace_of_isAffineSpaceBundle (n : ℕ)
    {L R Q : BigFppfOver B S hS} (l : L ⟶ Q) (r : R ⟶ Q)
    (hL : IsAffine ((BigFppfOver.toScheme B S hS).obj L))
    (hr : IsAffineSpaceBundle n ((BigFppfOver.toScheme B S hS).map r)) :
    ∃ β : BigFppfOver.affineSpace B S hS n L hL ⟶ R,
      IsPullback (BigFppfOver.affineSpaceProj B S hS n L hL) β l r := by
  let Ts := BigFppfOver.toScheme B S hS
  obtain ⟨e⟩ := hr (Ts.obj L) hL (Ts.map l)
  have hw : e.inv.left ≫ pullback.fst (Ts.map l) (Ts.map r) =
      𝔸(ULift.{u} (Fin n); Ts.obj L) ↘ Ts.obj L := Over.w e.inv
  let v : Ts.obj (BigFppfOver.affineSpace B S hS n L hL) ⟶ Ts.obj R :=
    e.inv.left ≫ pullback.snd (Ts.map l) (Ts.map r)
  have hβ : v ≫ B.inclusion.map R.hom =
      B.inclusion.map (BigFppfOver.affineSpace B S hS n L hL).hom := by
    change (e.inv.left ≫ pullback.snd (Ts.map l) (Ts.map r)) ≫ B.inclusion.map R.hom = _
    rw [← BigFppfOver.toScheme_map_comp_hom r, Category.assoc, ← Category.assoc
      (pullback.snd _ _), ← pullback.condition, Category.assoc, ← Category.assoc, hw,
      BigFppfOver.toScheme_map_comp_hom]
    rfl
  let β := BigFppfOver.homOfCompEq B S hS v hβ
  have hsq : IsPullback (𝔸(ULift.{u} (Fin n); Ts.obj L) ↘ Ts.obj L)
      (e.inv.left ≫ pullback.snd (Ts.map l) (Ts.map r)) (Ts.map l) (Ts.map r) := by
    refine IsPullback.of_iso_pullback ⟨?_⟩ ((Over.forget _).mapIso e.symm) hw rfl
    rw [← hw, Category.assoc, Category.assoc, pullback.condition]
  have hβ' : Ts.map β = v := BigFppfOver.toScheme_map_homOfCompEq B S hS v hβ
  refine ⟨β, IsPullback.of_map (BigFppfOver.toScheme B S hS) ?_ ?_⟩
  · apply BigFppfOver.map_toScheme_injective B S hS
    dsimp only
    rw [Functor.map_comp, Functor.map_comp, hβ']
    exact hsq.w
  · rwa [hβ']

/-! ### The chain of step 2 -/

/-- **Stacks 0F9U, step 2: the chain.** Let `g : U' ⟶ U` and `g' : U' ⟶ X'` be morphisms of the
site, `A` over `U` and `A'` over `X'` objects with an identification `c` of their base changes to
`U'`, and `p : T₁ ⟶ A`, `q : T' ⟶ A'` affine-space bundles of ranks `n₁` and `n'` with affine
sources whose base changes to `U'` stay affine. Then the base changes to `U'` of `A^{n'}_{T₁}`
and of `A^{n₁}_{T'}` are identified, compatibly with the two maps down to the base change of
`A'`. -/
theorem exists_affineSpace_chain {U' U X' : Scheme.{u}} {hU' : B.Contains U'}
    {hU : B.Contains U} {hX' : B.Contains X'} (g : B.obj hU' ⟶ B.obj hU)
    (g' : B.obj hU' ⟶ B.obj hX') {A : BigFppfOver B U hU} {A' : BigFppfOver B X' hX'}
    (c : (Over.pullback g).obj A ≅ (Over.pullback g').obj A') {n₁ n' : ℕ}
    {T₁ : BigFppfOver B U hU} {T' : BigFppfOver B X' hX'} (p : T₁ ⟶ A) (q : T' ⟶ A')
    (hT₁ : IsAffine ((BigFppfOver.toScheme B U hU).obj T₁))
    (hT' : IsAffine ((BigFppfOver.toScheme B X' hX').obj T'))
    (hL : IsAffine ((BigFppfOver.toScheme B U' hU').obj ((Over.pullback g).obj T₁)))
    (hR : IsAffine ((BigFppfOver.toScheme B U' hU').obj ((Over.pullback g').obj T')))
    (hp : IsAffineSpaceBundle n₁ ((BigFppfOver.toScheme B U hU).map p))
    (hq : IsAffineSpaceBundle n' ((BigFppfOver.toScheme B X' hX').map q)) :
    ∃ chain : (Over.pullback g).obj (BigFppfOver.affineSpace B U hU n' T₁ hT₁) ≅
        (Over.pullback g').obj (BigFppfOver.affineSpace B X' hX' n₁ T' hT'),
      chain.hom ≫ (Over.pullback g').map
          (BigFppfOver.affineSpaceProj B X' hX' n₁ T' hT' ≫ q) =
        (Over.pullback g).map (BigFppfOver.affineSpaceProj B U hU n' T₁ hT₁ ≫ p) ≫ c.hom := by
  let L := (Over.pullback g).obj T₁
  let R := (Over.pullback g').obj T'
  let l : L ⟶ (Over.pullback g').obj A' := (Over.pullback g).map p ≫ c.hom
  let r : R ⟶ (Over.pullback g').obj A' := (Over.pullback g').map q
  -- `r` is a bundle of rank `n'`, as a base change of `q`.
  obtain ⟨β₁, h₁⟩ := exists_isPullback_affineSpace_of_isAffineSpaceBundle B U' hU' n' l r hL
    (hq.of_isPullback (isPullback_toScheme_pullback_map B X' hX' g' q).flip)
  -- `(Over.pullback g).map p ≫ c.hom ≫ c.inv` is a bundle of rank `n₁`, as a base change of `p`.
  obtain ⟨β₂, h₂⟩ := exists_isPullback_affineSpace_of_isAffineSpaceBundle B U' hU' n₁
    (r ≫ c.inv) ((Over.pullback g).map p) hR
    (hp.of_isPullback (isPullback_toScheme_pullback_map B U hU g p).flip)
  have h₂' : IsPullback β₂ (BigFppfOver.affineSpaceProj B U' hU' n₁ R hR) l r := by
    refine IsPullback.of_iso h₂.flip (Iso.refl _) (Iso.refl _) (Iso.refl _) c ?_ ?_ ?_ ?_ <;>
      simp [l]
  let χ := h₁.isoIsPullback _ _ h₂'
  obtain ⟨e₁, he₁⟩ := exists_affineSpacePullbackIso B U hU n' g T₁ hT₁ hL
  obtain ⟨e₂, he₂⟩ := exists_affineSpacePullbackIso B X' hX' n₁ g' T' hT' hR
  refine ⟨e₁ ≪≫ χ ≪≫ e₂.symm, ?_⟩
  have hχ : χ.hom ≫ BigFppfOver.affineSpaceProj B U' hU' n₁ R hR = β₁ :=
    h₁.isoIsPullback_hom_snd _ _ h₂'
  have he₂' : e₂.inv ≫ (Over.pullback g').map
      (BigFppfOver.affineSpaceProj B X' hX' n₁ T' hT') =
      BigFppfOver.affineSpaceProj B U' hU' n₁ R hR := by
    rw [← he₂, Iso.inv_hom_id_assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Functor.map_comp]
  rw [reassoc_of% he₂', reassoc_of% hχ, ← h₁.w, ← reassoc_of% he₁]

end BigFppfOver

end AlgebraicGeometry

end
