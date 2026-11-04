module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Closed immersions of algebraic spaces on points

Properness of a closed immersion of algebraic spaces over a scheme `S` — **Stacks 04XZ** —
is `AlgebraicGeometry.Space.isProper_of_isClosedImmersion` of
`StacksFrontier/AlgebraicGeometry/Spaces/ProperClosedImmersion.lean`, which this module
re-exports. What is proved here is the point-level half of the same circle of ideas: how a
closed immersion acts on the points of Stacks 03BX, which is the one place where the
topology of Stacks 03BX genuinely enters, together with the two structural facts about
closed immersions of algebraic spaces that go with it.

## Main results

* `AlgebraicGeometry.Space.isSchemeOpen_iff_preimage` and
  `AlgebraicGeometry.Space.isClosed_image_pointsToScheme`: on a represented presheaf, a
  set of points is cut out by an open subset of the representing scheme exactly when it is
  the preimage of that subset, and a set of points closed for the topology of Stacks 03BX
  has closed image in the representing scheme. Together these are clause (1) of Stacks 03BX
  read on open and on closed sets.
* `AlgebraicGeometry.Space.isClosedMorphism_of_isClosedImmersion`: a closed immersion is
  closed on points.
* `AlgebraicGeometry.Space.isClosedImmersion_isStableUnderBaseChange`: being a closed
  immersion of algebraic spaces over `S` is stable under base change.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isClosedImmersion`: the source of a closed
  immersion into a quasi-compact algebraic space is quasi-compact.

## Implementation notes

Each of these transfers a property of morphisms of schemes through all represented base
changes, in the manner of Stacks 02YO; in every case the input is Mathlib's corresponding
fact about `AlgebraicGeometry.IsClosedImmersion` for schemes.

* *Stability under base change* is stability of
  `CategoryTheory.MorphismProperty.presheaf` under base change, which holds for any
  property of the site.
* *Quasi-compactness of the source* uses that the base change of a quasi-compact étale atlas
  of the target is an étale atlas of the source, whose scheme is a closed subscheme of a
  quasi-compact one.
* *Closedness on points* is proved against the *constructed* topology
  `AlgebraicGeometry.Space.pointTopology` of
  `StacksFrontier/AlgebraicGeometry/Spaces/PointsTopology.lean`, as the library's Stacks 03HI
  and 03ZM are. A set of points of the target is closed exactly when its preimage under
  every scheme-valued point is cut out by a closed subset of that scheme, so closedness of
  the image of a closed set `W` is tested on one scheme-valued point `c` of the target at a
  time. The base change of the morphism along `c` is a closed immersion of schemes
  `U' ⟶ U`, and the candidate closed set is the image in `U` of the part of `W` seen by
  `U'`; the two inclusions are the bijection of clause (1) of Stacks 03BX
  (`AlgebraicGeometry.Space.pointsToScheme`) in one direction and Stacks 03H4,
  surjectivity of the points of a fibre product onto the fibre product of the point sets, in
  the other.

Quasi-compactness of a closed immersion itself, as a morphism, is Stacks 04CG:
`AlgebraicGeometry.Space.isQuasiCompact_of_isClosedImmersion` of
`StacksFrontier/AlgebraicGeometry/Spaces/ClosedImmersionQC.lean`, with
`AlgebraicGeometry.Space.isQuasiCompact_of_isClosedImmersion'` the version without the
algebraicity hypotheses that the argument does not use.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 02YO](https://stacks.math.columbia.edu/tag/02YO)
* [Stacks Project, Tag 01W5](https://stacks.math.columbia.edu/tag/01W5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Closed sets of points of a represented presheaf -/

/-- A set of points of a represented presheaf is cut out by an open subset of the
representing scheme exactly when it is the preimage of that subset along
`AlgebraicGeometry.Space.pointsToScheme`. -/
theorem isSchemeOpen_iff_preimage (U : BigFppfOver B S hS)
    (W : Set (points B S hS (yoneda.obj U))) :
    IsSchemeOpen B S hS U W ↔
      ∃ V : Set ((BigFppfOver.toScheme B S hS).obj U), IsOpen V ∧
        W = pointsToScheme B S hS U ⁻¹' V := by
  constructor
  · rintro ⟨V, hV, hmem⟩
    refine ⟨V, hV, ?_⟩
    ext x
    induction x using Quot.ind with
    | _ p => exact hmem p
  · rintro ⟨V, hV, rfl⟩
    exact ⟨V, hV, fun _ ↦ Iff.rfl⟩

/-- A set of points of a represented presheaf which is closed for the topology of Stacks
03BX has closed image in the representing scheme.

This is clause (1) of Stacks 03BX read on closed sets: the bijection
`AlgebraicGeometry.Space.pointsToScheme` identifies the two topologies. -/
theorem isClosed_image_pointsToScheme (U : BigFppfOver B S hS)
    {W : Set (points B S hS (yoneda.obj U))}
    (hW : @IsClosed _ (pointTopology B S hS (yoneda.obj U)) W) :
    IsClosed (pointsToScheme B S hS U '' W) := by
  have h := hW.isOpen_compl
  rw [isOpen_yoneda_iff_isSchemeOpen, isSchemeOpen_iff_preimage] at h
  obtain ⟨V, hV, hcompl⟩ := h
  have himg : pointsToScheme B S hS U '' W = Vᶜ := by
    apply Set.eq_of_subset_of_subset
    · rintro y ⟨w, hw, rfl⟩
      intro hmem
      exact (hcompl ▸ (Set.mem_preimage.2 hmem) : w ∈ Wᶜ) hw
    · intro y hy
      obtain ⟨w, rfl⟩ := surjective_pointsToScheme B S hS U y
      refine ⟨w, ?_, rfl⟩
      by_contra hw
      exact hy (Set.mem_preimage.1 (hcompl ▸ hw : w ∈ pointsToScheme B S hS U ⁻¹' V))
  rw [himg]
  exact hV.isClosed_compl

/-- **Stacks 03H4** for a cartesian square of presheaves whose four corners are algebraic
spaces, rather than for a square in the category of algebraic spaces over `S`. -/
private theorem exists_point_of_isPullback_presheaf
    {P Z X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hP : IsAlgebraicSpace B S hS P) (hZ : IsAlgebraicSpace B S hS Z)
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    {p : P ⟶ Z} {q : P ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y}
    (sq : IsPullback p q g f)
    (z : points B S hS Z) (x : points B S hS X)
    (h : pointsMap B S hS Z g z = pointsMap B S hS X f x) :
    ∃ w : points B S hS P,
      pointsMap B S hS P p w = z ∧ pointsMap B S hS P q w = x := by
  have sq' : IsPullback
      (ObjectProperty.homMk p : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩)
      (ObjectProperty.homMk q : (⟨P, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩)
      (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩)
      (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) sq
  exact exists_point_of_isPullback B S hS sq' z x h

/-! ### Closed immersions -/

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Being a closed immersion of algebraic spaces over `S` is stable under base change, as
being a closed immersion of schemes is. -/
theorem isClosedImmersion_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) :=
  MorphismProperty.relative_isStableUnderBaseChange _

/-! ### Quasi-compactness and closedness on points -/

/-- The source of a closed immersion into a quasi-compact algebraic space over `S` is
quasi-compact: the base change of a quasi-compact étale atlas of the target is an étale
atlas of the source whose scheme is a closed subscheme of a quasi-compact one. -/
theorem isQuasiCompactSpace_of_isClosedImmersion
    (hY : IsQuasiCompactSpace B S hS Y) (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f) :
    IsQuasiCompactSpace B S hS X := by
  obtain ⟨V, a, _, hasurj, haetale⟩ := hY
  have sq : IsPullback (hf.1.fst a) (yoneda.map (hf.1.snd a)) f a := hf.1.isPullback a
  have hci : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hf.1.snd a)) :=
    hf.2 a (hf.1.fst a) (hf.1.snd a) sq
  have hsurj : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  have hetale : MorphismProperty.IsStableUnderBaseChange
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) :=
    MorphismProperty.relative_isStableUnderBaseChange _
  refine ⟨hf.1.pullback a, hf.1.fst a, hci.isClosedEmbedding.compactSpace,
    hsurj.of_isPullback sq.flip hasurj, ?_⟩
  exact (isEtale_iff_presheaf_of_yoneda B S hS _).2
    (hetale.of_isPullback sq.flip ((isEtale_iff_presheaf_of_yoneda B S hS a).1 haetale))

/-- A closed immersion of algebraic spaces over `S` is closed on points.

A set of points of the target is closed exactly when its preimage under each scheme-valued
point `c` of the target is cut out by a closed subset of that scheme; that subset is the
image of the part of the given closed set seen by the base change of the morphism along
`c`, which is a closed immersion of schemes and hence a closed map. -/
theorem isClosedMorphism_of_isClosedImmersion (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) (hf : IsClosedImmersion B S hS f) :
    IsClosedMorphism B S hS f := by
  let _ := pointTopology B S hS X
  let _ := pointTopology B S hS Y
  intro W hW
  rw [← isOpen_compl_iff]
  intro U c
  let _ := pointTopology B S hS (yoneda.obj (hf.1.pullback c))
  let _ := pointTopology B S hS (yoneda.obj U)
  have sq : IsPullback (hf.1.fst c) (yoneda.map (hf.1.snd c)) f c := hf.1.isPullback c
  have hci : AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (hf.1.snd c)) :=
    hf.2 c (hf.1.fst c) (hf.1.snd c) sq
  have hW' : @IsClosed _ (pointTopology B S hS (yoneda.obj (hf.1.pullback c)))
      (pointsMap B S hS (yoneda.obj (hf.1.pullback c)) (hf.1.fst c) ⁻¹' W) :=
    hW.preimage (continuous_pointsMap B S hS (hf.1.fst c))
  have hclosed : IsClosed ((BigFppfOver.toScheme B S hS).map (hf.1.snd c) ''
      (pointsToScheme B S hS (hf.1.pullback c) ''
        (pointsMap B S hS (yoneda.obj (hf.1.pullback c)) (hf.1.fst c) ⁻¹' W))) :=
    hci.isClosedEmbedding.isClosedMap _
      (isClosed_image_pointsToScheme B S hS _ hW')
  rw [isSchemeOpen_iff_preimage]
  refine ⟨_, hclosed.isOpen_compl, ?_⟩
  ext x
  simp only [Set.mem_preimage, Set.mem_compl_iff, not_iff_not]
  constructor
  · rintro ⟨w, hwW, hwx⟩
    obtain ⟨v, hv₁, hv₂⟩ := exists_point_of_isPullback_presheaf B S hS
      (isAlgebraicSpace_yoneda B S hS _) hX (isAlgebraicSpace_yoneda B S hS U) hY sq
      w x (by rw [hwx])
    refine ⟨pointsToScheme B S hS _ v, ⟨v, ?_, rfl⟩, ?_⟩
    · rw [Set.mem_preimage, hv₁]
      exact hwW
    · have hmap := pointsToScheme_pointsMap B S hS (hf.1.snd c) v
      rw [hv₂] at hmap
      exact hmap.symm
  · rintro ⟨y, ⟨v, hv, rfl⟩, hy⟩
    have hxv : pointsMap B S hS (yoneda.obj (hf.1.pullback c))
        (yoneda.map (hf.1.snd c)) v = x :=
      injective_pointsToScheme B S hS U
        (by rw [pointsToScheme_pointsMap]; exact hy)
    refine ⟨pointsMap B S hS (yoneda.obj (hf.1.pullback c)) (hf.1.fst c) v, hv, ?_⟩
    rw [← hxv, ← Function.comp_apply (f := pointsMap B S hS (yoneda.obj U) c),
      ← pointsMap_comp, ← Function.comp_apply (f := pointsMap B S hS X f),
      ← pointsMap_comp, sq.w]

end AlgebraicGeometry.Space

end
