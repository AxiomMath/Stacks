module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae

/-!
# The local criterion for quasi-separatedness of a morphism of algebraic spaces

A morphism of algebraic spaces is quasi-separated when its relative diagonal is quasi-compact,
tested against morphisms from quasi-compact algebraic spaces. When the relative diagonal is
representable this is the same as quasi-compactness of the relative diagonal after every
represented base change, and the latter is local on the target. This gives the equivalence of
six conditions characterising quasi-separated morphisms of algebraic spaces.

## Main results

* `AlgebraicGeometry.quasiCompact_of_compactSpace_of_isAffine`: a morphism from a quasi-compact
  scheme to an affine scheme is quasi-compact.
* `AlgebraicGeometry.Space.compactSpace_of_isQuasiCompactSpace_yoneda_obj`: a representable
  presheaf which is a quasi-compact algebraic space has quasi-compact underlying scheme.
* `AlgebraicGeometry.Space.isQuasiSeparated_iff_diagonalProp_quasiCompact`: for a morphism whose
  relative diagonal is representable, quasi-separatedness is quasi-compactness of the relative
  diagonal after every represented base change.
* `AlgebraicGeometry.Space.isQuasiSeparated_iff_affine`,
  `AlgebraicGeometry.Space.isQuasiSeparated_iff_exists_etaleChart` and
  `AlgebraicGeometry.Space.isQuasiSeparated_iff_exists_zariskiCover`: quasi-separatedness may be
  tested on the base changes along affine test objects, along one surjective étale chart of the
  target, or along the members of one Zariski covering of the target.
* `AlgebraicGeometry.Space.diagonalProp_quasiCompact_comp`,
  `AlgebraicGeometry.Space.diagonalProp_quasiCompact_of_isQuasiSeparatedOver` and
  `AlgebraicGeometry.Space.isQuasiSeparatedOver_iff_diagonalProp_quasiCompact_of_isTerminal`:
  the represented reading is stable under composition, every morphism out of a space which is
  quasi-separated over its base has it, and for a space it is the same as having it for the
  morphism to a terminal presheaf.
* `AlgebraicGeometry.Space.diagonalProp_quasiCompact_yoneda_map_iff` and
  `AlgebraicGeometry.Space.diagonalProp_quasiCompact_yoneda_map_of_isAffine`: for a represented
  morphism the represented reading is quasi-separatedness of the underlying morphism of schemes,
  which holds as soon as the source is affine.
* `AlgebraicGeometry.Space.isQuasiSeparated_yoneda_map_iff`: a represented morphism is
  quasi-separated exactly when the underlying morphism of schemes is.
* `AlgebraicGeometry.Space.diagonalProp_quasiCompact_relocalize` and
  `AlgebraicGeometry.Space.diagonalProp_quasiCompact_of_relocalize`: the represented reading is
  unchanged by relocalization of the base, in both directions.
* `AlgebraicGeometry.Space.isQuasiSeparated_pullbackSnd_iff_isAbsolutelyQuasiSeparated`: at an
  affine test object, the base change is quasi-separated exactly when the fibre product is a
  quasi-separated algebraic space.
* `AlgebraicGeometry.Space.isQuasiSeparated_tfae`: the six equivalent conditions for
  `AlgebraicGeometry.Space.IsQuasiSeparated`.

## References

* [Stacks Project, Tag 03KM](https://stacks.math.columbia.edu/tag/03KM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Quasi-compactness of a morphism of schemes is Zariski local on the base. -/
private theorem isZariskiLocalAtTarget_quasiCompact :
    IsZariskiLocalAtTarget (@AlgebraicGeometry.QuasiCompact.{u}) :=
  MorphismProperty.IsLocalAtTarget.of_le Scheme.zariskiPrecoverage_le_fppfPrecoverage

/-- Quasi-compactness of a morphism of schemes is Zariski local on the base. -/
alias isZariskiLocalAtTarget_quasiCompact' := isZariskiLocalAtTarget_quasiCompact

/-- A morphism from a quasi-compact scheme to an affine scheme is quasi-compact. -/
theorem quasiCompact_of_compactSpace_of_isAffine {W T : Scheme.{u}} (q : W ⟶ T)
    (hT : IsAffine T) (hW : CompactSpace W) : QuasiCompact q := by
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro U hU
  obtain ⟨s, hs, hUs⟩ := (isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen
    (X := T) (U := (U : Set T))).1 ⟨hU.isCompact, U.2⟩
  have hpre : (q ⁻¹ᵁ U : Set W) = ⋃ i ∈ s, (W.basicOpen (q.appTop i) : Set W) := by
    simp only [Scheme.Hom.coe_preimage, hUs, Set.preimage_iUnion₂,
      ← Scheme.preimage_basicOpen_top]
  rw [hpre]
  exact hs.isCompact_biUnion fun i _ ↦ isCompact_basicOpen _ isCompact_univ _

end AlgebraicGeometry

namespace AlgebraicGeometry.Space

open Stacks.SeparationLocal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The bridge between the two readings of quasi-compactness of the relative diagonal -/

/-- A representable quasi-compact algebraic space has quasi-compact underlying scheme. -/
theorem compactSpace_of_isQuasiCompactSpace_yoneda_obj {U : BigFppfOver B S hS}
    (h : IsQuasiCompactSpace B S hS (yoneda.obj U)) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := by
  obtain ⟨V, a, hV, hsurj, -⟩ := h
  obtain ⟨m, rfl⟩ := (yoneda (C := BigFppfOver B S hS)).map_surjective a
  have hs : Surjective ((BigFppfOver.toScheme B S hS).map m) :=
    (BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS _ m).1 hsurj
  exact Function.Surjective.compactSpace
    (Scheme.Hom.continuous ((BigFppfOver.toScheme B S hS).map m)) hs.surj

/-- The relative diagonal of a base change of a morphism with algebraic source is
representable. -/
theorem relativelyRepresentable_diagonal_pullbackSnd (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ Y) {Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : Z ⟶ Y) :
    yoneda.relativelyRepresentable (pullback.diagonal (pullback.snd f g)) :=
  (Functor.relativelyRepresentable.isStableUnderBaseChange
    (yoneda (C := BigFppfOver B S hS))).of_isPullback
      (isPullback_diagonal_pullbackSnd f g)
      (relativelyRepresentable_diagonal B S hS hX f)

/-- Let `k : h_a ⟶ X ×[Y] X` be a test morphism out of a representable quasi-compact algebraic
space, and let `g` be the composite of `k` with the projection to `Y`. If the base change of `f`
along `g` is quasi-separated, then the represented fibre product of `k` with the relative
diagonal of `f` has quasi-compact underlying scheme. -/
theorem compactSpace_pullback_diagonal_of_isQuasiSeparated_pullbackSnd {f : X ⟶ Y}
    (hu : yoneda.relativelyRepresentable (pullback.diagonal f)) {a : BigFppfOver B S hS}
    (ha : IsQuasiCompactSpace B S hS (yoneda.obj a)) (k : yoneda.obj a ⟶ pullback f f)
    (hP : IsQuasiSeparated B S hS (pullback.snd f (k ≫ pullback.fst f f ≫ f))) :
    CompactSpace ((BigFppfOver.toScheme B S hS).obj (hu.pullback k)) := by
  obtain ⟨h', hfac⟩ := exists_lift_diagonalObjMap f (k ≫ pullback.fst f f ≫ f) k
    (𝟙 (yoneda.obj a)) (Category.id_comp _).symm
  have key := hP (yoneda.obj a) (isAlgebraicSpace_yoneda B S hS a) ha h'
  have h1 := key.of_iso B S hS
    (isPullback_of_lift_diagonalObjMap f (k ≫ pullback.fst f f ≫ f) hfac).isoPullback
  exact compactSpace_of_isQuasiCompactSpace_yoneda_obj B S hS
    (h1.of_iso B S hS ((hu.isPullback k).flip.isoPullback).symm)

/-- If the base change of `f` along every object of the site with affine underlying scheme is
quasi-separated, then the relative diagonal of `f` is quasi-compact after every represented base
change. -/
theorem diagonalProp_quasiCompact_of_affine (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (H : ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ (g : yoneda.obj T ⟶ Y), IsQuasiSeparated B S hS (pullback.snd f g)) :
    DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) f := by
  have := isZariskiLocalAtTarget_quasiCompact.{u}
  have hu := relativelyRepresentable_diagonal B S hS hX f
  refine presheaf_of_affine B S hS hu fun a ha k ↦ ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj a) := ha
  exact quasiCompact_of_compactSpace_of_isAffine _ ha
    (compactSpace_pullback_diagonal_of_isQuasiSeparated_pullbackSnd B S hS hu
      (isQuasiCompactSpace_yoneda_obj B S hS inferInstance) k (H a ha _))

/-- If the relative diagonal of `f` is representable and `f` is quasi-separated, then its
relative diagonal is quasi-compact after every represented base change. -/
theorem diagonalProp_quasiCompact_of_isQuasiSeparated {f : X ⟶ Y}
    (hu : yoneda.relativelyRepresentable (pullback.diagonal f))
    (h : IsQuasiSeparated B S hS f) :
    DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) f := by
  have := isZariskiLocalAtTarget_quasiCompact.{u}
  refine presheaf_of_affine B S hS hu fun a ha k ↦ ?_
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj a) := ha
  exact quasiCompact_of_compactSpace_of_isAffine _ ha
    (compactSpace_pullback_diagonal_of_isQuasiSeparated_pullbackSnd B S hS hu
      (isQuasiCompactSpace_yoneda_obj B S hS inferInstance) k
      (isQuasiSeparated_pullbackSnd B S hS _ h))

/-- If the relative diagonal of `f` is quasi-compact after every represented base change, then
`f` is quasi-separated. -/
theorem isQuasiSeparated_of_diagonalProp_quasiCompact {f : X ⟶ Y}
    (h : DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) f) :
    IsQuasiSeparated B S hS f := by
  intro Z _ hqc g₀
  obtain ⟨U, a, hU, hasurj, haetale⟩ := hqc
  have hU' : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := hU
  have hqcm : AlgebraicGeometry.QuasiCompact
      ((BigFppfOver.toScheme B S hS).map (h.rep.snd (a ≫ g₀))) := h.property_snd (a ≫ g₀)
  have hcs : CompactSpace
      ((BigFppfOver.toScheme B S hS).obj (h.rep.pullback (a ≫ g₀))) :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      ((BigFppfOver.toScheme B S hS).map (h.rep.snd (a ≫ g₀)))
  have hqc1 : IsQuasiCompactSpace B S hS (pullback (a ≫ g₀) (pullback.diagonal f)) :=
    (isQuasiCompactSpace_yoneda_obj B S hS hcs).of_iso B S hS
      ((h.rep.isPullback (a ≫ g₀)).flip.isoPullback)
  have sqA := IsPullback.of_right'
    (IsPullback.of_hasPullback (a ≫ g₀) (pullback.diagonal f)).flip
    (IsPullback.of_hasPullback g₀ (pullback.diagonal f)).flip
  exact IsQuasiCompactSpace.of_surjective_etale B S hS
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sqA.flip hasurj)
    ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback sqA.flip
      (presheaf_etale_of_isEtale B S hS haetale)) hqc1

/-- For a morphism of presheaves on the big fppf site of `S` whose relative diagonal is
representable, quasi-separatedness is the same as quasi-compactness of the relative diagonal
after every represented base change. -/
theorem isQuasiSeparated_iff_diagonalProp_quasiCompact {f : X ⟶ Y}
    (hu : yoneda.relativelyRepresentable (pullback.diagonal f)) :
    IsQuasiSeparated B S hS f ↔
      DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) f :=
  ⟨diagonalProp_quasiCompact_of_isQuasiSeparated B S hS hu,
    isQuasiSeparated_of_diagonalProp_quasiCompact B S hS⟩

/-! ### Testing on affine objects, on an étale chart and on a Zariski covering -/

/-- A morphism of presheaves with algebraic source is quasi-separated if its base change along
every object of the site with affine underlying scheme is. -/
theorem isQuasiSeparated_of_affine (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    (H : ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
      ∀ (g : yoneda.obj T ⟶ Y), IsQuasiSeparated B S hS (pullback.snd f g)) :
    IsQuasiSeparated B S hS f :=
  isQuasiSeparated_of_diagonalProp_quasiCompact B S hS
    (diagonalProp_quasiCompact_of_affine B S hS hX H)

/-- A morphism of presheaves with algebraic source is quasi-separated exactly when its base
change along every object of the site with affine underlying scheme is. -/
theorem isQuasiSeparated_iff_affine (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) :
    IsQuasiSeparated B S hS f ↔
      ∀ (T : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
        ∀ (g : yoneda.obj T ⟶ Y), IsQuasiSeparated B S hS (pullback.snd f g) :=
  ⟨fun h _ _ g ↦ isQuasiSeparated_pullbackSnd B S hS g h,
    isQuasiSeparated_of_affine B S hS hX⟩

/-- A morphism of presheaves with algebraic source is quasi-separated if its base change along a
surjective étale scheme chart of the target is. -/
theorem isQuasiSeparated_of_etaleChart (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y}
    (hsurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (hetale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) g)
    (h : IsQuasiSeparated B S hS (pullback.snd f g)) :
    IsQuasiSeparated B S hS f :=
  isQuasiSeparated_of_diagonalProp_quasiCompact B S hS
    (DiagonalProp.of_etaleChart B S hS hX hsurj hetale
      ((isQuasiSeparated_iff_diagonalProp_quasiCompact B S hS
        (relativelyRepresentable_diagonal_pullbackSnd B S hS hX f g)).1 h))

/-- A morphism of algebraic spaces over `S` is quasi-separated exactly when there is a surjective
étale scheme chart of the target along which its base change is quasi-separated. -/
theorem isQuasiSeparated_iff_exists_etaleChart (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsQuasiSeparated B S hS f ↔
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        IsQuasiSeparated B S hS (pullback.snd f g) :=
  ⟨isQuasiSeparated_exists_etaleChart B S hS hY,
    fun ⟨_, _, hsurj, hetale, h⟩ ↦ isQuasiSeparated_of_etaleChart B S hS hX hsurj hetale h⟩

/-- A morphism of presheaves with algebraic source is quasi-separated if its base changes to the
members of a Zariski covering of the target are. -/
theorem isQuasiSeparated_of_zariskiCover (hX : IsAlgebraicSpace B S hS X) {f : X ⟶ Y}
    {I : Type u} {U : I → Subfunctor Y} (hU : IsZariskiCover B S hS I U)
    (h : ∀ i, IsQuasiSeparated B S hS (pullback.snd f (U i).ι)) :
    IsQuasiSeparated B S hS f :=
  have := isZariskiLocalAtTarget_quasiCompact.{u}
  isQuasiSeparated_of_diagonalProp_quasiCompact B S hS
    (DiagonalProp.of_zariskiCover B S hS hX hU fun i ↦
      (isQuasiSeparated_iff_diagonalProp_quasiCompact B S hS
        (relativelyRepresentable_diagonal_pullbackSnd B S hS hX f (U i).ι)).1 (h i))

/-- A morphism of algebraic spaces over `S` is quasi-separated exactly when there is a Zariski
covering of the target over whose members its base changes are quasi-separated. -/
theorem isQuasiSeparated_iff_exists_zariskiCover (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsQuasiSeparated B S hS f ↔
      ∃ (I : Type u) (U : I → Subfunctor Y), IsZariskiCover B S hS I U ∧
        ∀ i, IsQuasiSeparated B S hS (pullback.snd f (U i).ι) :=
  ⟨isQuasiSeparated_exists_zariskiCover B S hS hY,
    fun ⟨_, _, hU, h⟩ ↦ isQuasiSeparated_of_zariskiCover B S hS hX hU h⟩

/-! ### Quasi-separatedness over the terminal scheme

For an affine test object, the base change is compared with quasi-separatedness of the fibre
product over the terminal scheme `Spec ℤ`, through the relocalization functor
`AlgebraicGeometry.Space.viewOverIntegers` at the structure morphism of `S`. -/

/-- The representable quasi-compactness property of morphisms of presheaves on the big fppf site
of `S`. -/
private abbrev quasiCompactProp : MorphismProperty ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  MorphismProperty.presheaf (MorphismProperty.inverseImage
    (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
    (BigFppfOver.toScheme B S hS))

/-- Quasi-compact morphisms of schemes are stable under composition. -/
@[ega "IV 1.1.2"]
private instance isStableUnderComposition_quasiCompact :
    MorphismProperty.IsStableUnderComposition
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toIsStableUnderComposition

/-- Isomorphisms of schemes are quasi-compact. -/
private instance containsIdentities_quasiCompact :
    MorphismProperty.ContainsIdentities
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
  MorphismProperty.IsMultiplicative.toContainsIdentities

/-- Quasi-compactness of a morphism of schemes respects isomorphisms. -/
private instance respectsIso_quasiCompact :
    MorphismProperty.RespectsIso (@AlgebraicGeometry.QuasiCompact.{u}) :=
  MorphismProperty.IsStableUnderBaseChange.respectsIso

/-- Quasi-compactness of a morphism of the site is stable under base change. -/
@[ega "I 6.6.4" "(iii)"]
private instance isStableUnderBaseChange_inverseImage_quasiCompact :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
  BigFppfOver.isStableUnderBaseChange_inverseImage B S hS _

/-- Quasi-compactness of a morphism of the site contains the identities. -/
private instance containsIdentities_inverseImage_quasiCompact :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).ContainsIdentities :=
  MorphismProperty.ContainsIdentities.inverseImage _

/-- Quasi-compactness of a morphism of the site is stable under composition. -/
private instance isStableUnderComposition_inverseImage_quasiCompact :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
  MorphismProperty.IsStableUnderComposition.inverseImage _

/-- Quasi-compactness of a morphism of the site is multiplicative. -/
private instance isMultiplicative_inverseImage_quasiCompact :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsMultiplicative := ⟨⟩

/-- The representable quasi-compactness property is stable under base change. -/
private instance isStableUnderBaseChange_quasiCompactProp :
    (quasiCompactProp B S hS).IsStableUnderBaseChange :=
  MorphismProperty.relative_isStableUnderBaseChange _

/-- Quasi-compactness of the relative diagonal after every represented base change is stable
under composition. -/
theorem diagonalProp_quasiCompact_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (p : F ⟶ G)
    (q : G ⟶ H) (hp : DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) p)
    (hq : DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) q) :
    DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) (p ≫ q) :=
  MorphismProperty.comp_mem (quasiCompactProp B S hS).diagonal p q hp hq

/-- An isomorphism of presheaves on the big fppf site of `S` has quasi-compact relative
diagonal. -/
theorem diagonalProp_quasiCompact_of_isIso {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (e : F ⟶ G)
    [IsIso e] : DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) e := by
  have : IsIso (pullback.diagonal e) := (pullback.isIso_diagonal_iff e).2 inferInstance
  exact MorphismProperty.of_isIso (quasiCompactProp B S hS) (pullback.diagonal e)

/-- Every morphism out of an algebraic space which is quasi-separated over `S` has quasi-compact
relative diagonal. -/
theorem diagonalProp_quasiCompact_of_isQuasiSeparatedOver
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsQuasiSeparatedOver B S hS F) (p : F ⟶ G) :
    DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) p :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := quasiCompactProp B S hS) (isPullback_diagonal_diag p).flip hF

/-- An algebraic space is quasi-separated over `S` exactly when its morphism to a terminal
presheaf has quasi-compact relative diagonal. -/
theorem isQuasiSeparatedOver_iff_diagonalProp_quasiCompact_of_isTerminal
    {F H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hH : IsTerminal H) (t : F ⟶ H) :
    IsQuasiSeparatedOver B S hS F ↔
      DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) t := by
  have hd : diag F = pullback.diagonal (terminal.from F) ≫ (prodIsoPullback F F).inv := by
    refine prod.hom_ext ?_ ?_ <;> simp
  refine ⟨fun h ↦ diagonalProp_quasiCompact_of_isQuasiSeparatedOver B S hS h t, fun h ↦ ?_⟩
  have h' : DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u})
      (terminal.from F ≫ (terminalIsTerminal.uniqueUpToIso hH).hom) := by
    rwa [← hH.hom_ext t (terminal.from F ≫ (terminalIsTerminal.uniqueUpToIso hH).hom)]
  have h'' : DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) (terminal.from F) :=
    (MorphismProperty.cancel_right_of_respectsIso (quasiCompactProp B S hS).diagonal
      (terminal.from F) (terminalIsTerminal.uniqueUpToIso hH).hom).1 h'
  change quasiCompactProp B S hS (diag F)
  rw [hd]
  exact MorphismProperty.RespectsIso.postcomp (quasiCompactProp B S hS) _ _ h''

/-- A represented morphism has quasi-compact relative diagonal after every represented base
change exactly when the underlying morphism of schemes is quasi-separated. -/
theorem diagonalProp_quasiCompact_yoneda_map_iff {a b : BigFppfOver B S hS} (m : a ⟶ b) :
    DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) (yoneda.map m) ↔
      _root_.AlgebraicGeometry.QuasiSeparated ((BigFppfOver.toScheme B S hS).map m) := by
  have hyoneda : DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) (yoneda.map m) ↔
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (pullback.diagonal m)) := by
    rw [← MorphismProperty.cancel_right_of_respectsIso
      (MorphismProperty.inverseImage
        (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf _
      (PreservesPullback.iso (yoneda (C := BigFppfOver B S hS)) m m).hom,
      map_pullback_diagonal]
  have hscheme : _root_.AlgebraicGeometry.QuasiCompact
        ((BigFppfOver.toScheme B S hS).map (pullback.diagonal m)) ↔
      _root_.AlgebraicGeometry.QuasiSeparated ((BigFppfOver.toScheme B S hS).map m) := by
    rw [← MorphismProperty.cancel_right_of_respectsIso
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u}) _
      (PreservesPullback.iso (BigFppfOver.toScheme B S hS) m m).hom,
      map_pullback_diagonal, _root_.AlgebraicGeometry.quasiSeparated_iff]
  exact hyoneda.trans ((BigFppfOver.presheaf_inverseImage_yoneda_map_iff B S hS
    (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
    (pullback.diagonal m)).trans hscheme)

/-- A represented morphism is quasi-separated exactly when the underlying morphism of schemes
is. -/
theorem isQuasiSeparated_yoneda_map_iff {a b : BigFppfOver B S hS} (m : a ⟶ b) :
    IsQuasiSeparated B S hS (yoneda.map m) ↔
      _root_.AlgebraicGeometry.QuasiSeparated ((BigFppfOver.toScheme B S hS).map m) :=
  (isQuasiSeparated_iff_diagonalProp_quasiCompact B S hS
    (relativelyRepresentable_diagonal B S hS (isAlgebraicSpace_yoneda B S hS a)
      (yoneda.map m))).trans (diagonalProp_quasiCompact_yoneda_map_iff B S hS m)

/-- A morphism of the site out of an object with affine underlying scheme has quasi-compact
relative diagonal after every represented base change. -/
theorem diagonalProp_quasiCompact_yoneda_map_of_isAffine {a b : BigFppfOver B S hS} (m : a ⟶ b)
    (ha : IsAffine ((BigFppfOver.toScheme B S hS).obj a)) :
    DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) (yoneda.map m) :=
  (diagonalProp_quasiCompact_yoneda_map_iff B S hS m).2 <|
    have := ha
    inferInstance

section Relocalize

variable {S' : Scheme.{u}} (hS' : B.Contains S') (k : B.obj hS ⟶ B.obj hS')

/-- A quasi-compact morphism of the site stays quasi-compact after relocalization to a larger
base. -/
theorem presheafQuasiCompact_relocalize {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F ⟶ G}
    (h : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S' hS')).presheaf
        ((OverShriek.relocalizePresheafFunctor k).map p) :=
  OverShriek.presheaf_map_relocalize _ (fun _ hk ↦ hk) h

/-- A representable morphism which becomes quasi-compact after relocalization is
quasi-compact. -/
theorem presheafQuasiCompact_of_relocalize {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F ⟶ G}
    (hrep : yoneda.relativelyRepresentable p)
    (h : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S' hS')).presheaf
        ((OverShriek.relocalizePresheafFunctor k).map p)) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p :=
  OverShriek.presheaf_of_presheaf_map_relocalize _ (fun _ hk ↦ hk) hrep h

/-- A morphism with quasi-compact relative diagonal keeps it after relocalization to a larger
base. -/
theorem diagonalProp_quasiCompact_relocalize {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {p : F ⟶ G}
    (h : DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) p) :
    DiagonalProp B S' hS' (@AlgebraicGeometry.QuasiCompact.{u})
      ((OverShriek.relocalizePresheafFunctor k).map p) := by
  have h1 := presheafQuasiCompact_relocalize B S hS hS' k (p := pullback.diagonal p) h
  change quasiCompactProp B S' hS'
    (pullback.diagonal ((OverShriek.relocalizePresheafFunctor k).map p))
  rw [← OverShriek.relocalize_map_diagonal]
  exact MorphismProperty.RespectsIso.postcomp (quasiCompactProp B S' hS') _ _ h1

/-- A morphism with representable relative diagonal whose relocalization has quasi-compact
relative diagonal has one itself. -/
theorem diagonalProp_quasiCompact_of_relocalize {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {p : F ⟶ G} (hrep : yoneda.relativelyRepresentable (pullback.diagonal p))
    (h : DiagonalProp B S' hS' (@AlgebraicGeometry.QuasiCompact.{u})
      ((OverShriek.relocalizePresheafFunctor k).map p)) :
    DiagonalProp B S hS (@AlgebraicGeometry.QuasiCompact.{u}) p := by
  have h1 : quasiCompactProp B S' hS'
      (pullback.diagonal ((OverShriek.relocalizePresheafFunctor k).map p)) := h
  rw [← OverShriek.relocalize_map_diagonal] at h1
  exact presheafQuasiCompact_of_relocalize B S hS hS' k hrep
    ((MorphismProperty.cancel_right_of_respectsIso
      (quasiCompactProp B S' hS') _ _).1 h1)

end Relocalize

section Absolute

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- For an affine test object `T` of the big fppf site of `S` and `g : h_T ⟶ Y`, the base change
`X ×_Y h_T ⟶ h_T` of `f` is quasi-separated over `S` exactly when the algebraic space
`X ×_Y h_T`, viewed over the terminal scheme, is quasi-separated. -/
@[sga "4 VIII 5.1" "partial"]
theorem isQuasiSeparated_pullbackSnd_iff_isAbsolutelyQuasiSeparated
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y) (T : BigFppfOver B S hS)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (g : yoneda.obj T ⟶ Y) :
    IsQuasiSeparated B S hS (pullback.snd f g) ↔
      IsAbsolutelyQuasiSeparated B S hS hZ (pullback f g) := by
  have hterm : IsTerminal (Over.mk (𝟙 (B.obj hZ))) := Over.mkIdTerminal
  have haffT : IsAffine ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      ((Over.map (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).obj T)) := hT
  have hm : DiagonalProp B (⊤_ Scheme.{u}) hZ (@AlgebraicGeometry.QuasiCompact.{u})
      (yoneda.map (hterm.from
        ((Over.map (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).obj T))) :=
    diagonalProp_quasiCompact_yoneda_map_of_isAffine B (⊤_ Scheme.{u}) hZ _ haffT
  have hiso := (OverShriek.relocalizeYonedaIso
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ)).app T
  have hterm' :=
    IsTerminal.isTerminalObj (yoneda (C := BigFppfOver B (⊤_ Scheme.{u}) hZ)) _ hterm
  have hrep : yoneda.relativelyRepresentable (pullback.diagonal (pullback.snd f g)) :=
    relativelyRepresentable_diagonal_pullbackSnd B S hS hX f g
  rw [isQuasiSeparated_iff_diagonalProp_quasiCompact B S hS hrep]
  refine ⟨fun h ↦ ?_, fun h ↦ diagonalProp_quasiCompact_of_relocalize B S hS hZ
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) hrep
    (diagonalProp_quasiCompact_of_isQuasiSeparatedOver B (⊤_ Scheme.{u}) hZ h _)⟩
  have h1 := diagonalProp_quasiCompact_relocalize B S hS hZ
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) h
  exact (isQuasiSeparatedOver_iff_diagonalProp_quasiCompact_of_isTerminal
    B (⊤_ Scheme.{u}) hZ hterm' _).2
    (diagonalProp_quasiCompact_comp B (⊤_ Scheme.{u}) hZ _ _
      (diagonalProp_quasiCompact_comp B (⊤_ Scheme.{u}) hZ _ _ h1
        (diagonalProp_quasiCompact_of_isIso B (⊤_ Scheme.{u}) hZ hiso.hom)) hm)

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S` the following six conditions are equivalent: `f` is quasi-separated; the base change of
`f` along every morphism from a representable presheaf is quasi-separated; the same for the test
objects with affine underlying scheme; for every affine test object the fibre product is a
quasi-separated algebraic space, that is quasi-separated over the terminal scheme; there is a
surjective étale scheme chart of the target along which the base change of `f` is quasi-separated;
and there is a Zariski covering of the target over whose members the base changes of `f` are
quasi-separated. -/
@[stacks 03KM "quasi-separated"]
theorem isQuasiSeparated_tfae (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    List.TFAE [
      IsQuasiSeparated B S hS f,
      (∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
        IsQuasiSeparated B S hS (pullback.snd f g)),
      (∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
          IsQuasiSeparated B S hS (pullback.snd f g)),
      (∀ (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj T) →
          IsAbsolutelyQuasiSeparated B S hS hZ (pullback f g)),
      (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Surjective.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        (MorphismProperty.presheaf (MorphismProperty.inverseImage
          (@Etale.{u} : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS))) g ∧
        IsQuasiSeparated B S hS (pullback.snd f g)),
      (∃ (I : Type u) (U : I → Subfunctor Y),
        IsZariskiCover B S hS I U ∧
        ∀ i, IsQuasiSeparated B S hS (pullback.snd f (U i).ι))
    ] := by
  tfae_have 1 → 2 := fun h T g ↦ isQuasiSeparated_pullbackSnd B S hS g h
  tfae_have 2 → 3 := fun h T g _ ↦ h T g
  tfae_have 3 → 4 := fun h T g hT ↦
    (isQuasiSeparated_pullbackSnd_iff_isAbsolutelyQuasiSeparated
      B S hS hZ hX f T hT g).1 (h T g hT)
  tfae_have 4 → 3 := fun h T g hT ↦
    (isQuasiSeparated_pullbackSnd_iff_isAbsolutelyQuasiSeparated
      B S hS hZ hX f T hT g).2 (h T g hT)
  tfae_have 3 → 1 := fun h ↦
    isQuasiSeparated_of_affine B S hS hX fun T hT g ↦ h T g hT
  tfae_have 1 → 5 := isQuasiSeparated_exists_etaleChart B S hS hY
  tfae_have 5 → 1 := fun ⟨_, _, hsurj, hetale, h⟩ ↦
    isQuasiSeparated_of_etaleChart B S hS hX hsurj hetale h
  tfae_have 1 → 6 := isQuasiSeparated_exists_zariskiCover B S hS hY
  tfae_have 6 → 1 := fun ⟨_, _, hU, h⟩ ↦ isQuasiSeparated_of_zariskiCover B S hS hX hU h
  tfae_finish

end Absolute

end AlgebraicGeometry.Space

end
