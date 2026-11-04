module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.Fpqc.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Open

/-!
# Universal openness of morphisms of algebraic spaces is fpqc local on the base

A morphism of algebraic spaces over `S` is *open* when the map it induces on the space of points
of Stacks 03BX is an open map, and *universally open* when all of its base changes are
(Stacks 03Z2). This file proves that universal openness is local on the base for the fpqc
topology of Stacks 03YH, which is **Stacks 041P**.

Universal openness is being universally an open morphism, so the ascent half of the locality is
formal. For the descent half, condition (3) of Stacks 03Z5 reduces the assertion to openness of
the base changes along morphisms from the *affine* objects of the site. Over such an affine `T`
the fpqc condition of Stacks 03MQ supplies a finite affine family covering `T` and refining the
given covering, and a set of points of a representable algebraic space is open as soon as its
preimages along such a family are open — the presheaf of continuous maps to the Sierpiński space
being an fpqc sheaf. Each of those preimages is the image of an open set of points computed in
the base change over the corresponding member, which is open because that member factors through
a member of the given covering.

## Main definitions

* `AlgebraicGeometry.Space.isOpenMorphismProperty`: being an open morphism as a
  `CategoryTheory.MorphismProperty` on `AlgebraicGeometry.AlgebraicSpaces`, the open counterpart
  of `AlgebraicGeometry.Space.isClosedMorphismProperty`.
* `AlgebraicGeometry.Space.universallyOpenMorphismProperty`: universal openness as a
  `CategoryTheory.MorphismProperty` on `AlgebraicGeometry.AlgebraicSpaces`.

## Main results

* `CategoryTheory.MorphismProperty.universally_of_factorization`: if the base change of `f`
  along `g : V ⟶ Y` is universally in `Q`, then every cartesian square over a morphism
  `T ⟶ Y` which factors through `g` has its first projection in `Q`.
* `AlgebraicGeometry.Space.universallyOpen_iff_universally_isOpenMorphism`: universal openness
  is being universally an open morphism.
* `AlgebraicGeometry.Space.isOpen_points_of_fpqc_schemeCover`: a set of points of a
  representable algebraic space is open as soon as its preimage along every member of an fpqc
  covering family of the representing scheme is open.
* `AlgebraicGeometry.Space.isOpen_preimage_image_pointsMap_of_isPullback`: in a cartesian square
  whose first projection is an open morphism, the preimage of the image of an open set of points
  is open.
* `AlgebraicGeometry.Space.universallyOpen_isLocalAtTarget_fpqc`: **Stacks 041P**.
* `AlgebraicGeometry.Space.universallyOpen_isStableUnderBaseChange` and
  `AlgebraicGeometry.Space.universallyOpen_isStableUnderComposition`: **Stacks 03Z3** and
  **Stacks 03Z4** at the packaged property, so that the three instances
  `CategoryTheory.MorphismProperty.IsStableUnderBaseChange`,
  `CategoryTheory.MorphismProperty.IsLocalAtTarget` and
  `CategoryTheory.MorphismProperty.IsStableUnderComposition` that the Stacks 03YK notion asks of
  a property are all available at universal openness.

## Implementation notes

`AlgebraicGeometry.Space.IsOpenMorphism` is a statement about the topology
`AlgebraicGeometry.Space.pointTopology` on `AlgebraicGeometry.Space.points`, which is not an
instance; it is made a local instance here, as in the files where that topology is introduced.
The identification of the points of a representable algebraic space with the points of the
representing scheme is `AlgebraicGeometry.Space.schemePointsHomeomorph`, clause (1) of
Stacks 03BX.

Everything here is the open counterpart of the closed statements in
`StacksFrontier/AlgebraicGeometry/Spaces/ProperBaseChange.lean` and of the fpqc descent of
closedness in `StacksFrontier/AlgebraicGeometry/Spaces/Descent/Fpqc/UniversallyClosed.lean`; the
two are kept apart because the descent of openness runs on the open sets of points directly,
while the descent of closedness runs on the images of closed sets.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 03YH](https://stacks.math.columbia.edu/tag/03YH)
* [Stacks Project, Tag 03Z2](https://stacks.math.columbia.edu/tag/03Z2)
* [Stacks Project, Tag 03Z5](https://stacks.math.columbia.edu/tag/03Z5)
* [Stacks Project, Tag 041P](https://stacks.math.columbia.edu/tag/041P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CategoryTheory.MorphismProperty

/-- Let `g : V ⟶ Y` and let `b : T ⟶ Y` factor as `a ≫ g`. If the base change of `f : X ⟶ Y`
along `g` is universally in `Q`, then the first projection of any cartesian square over `b` and
`f` is in `Q`: that projection is a base change of the base change along `g`, the comparison
morphism being the lift of the square's projections through `a`. -/
theorem universally_of_factorization {C : Type*} [Category* C] [HasPullbacks C]
    (Q : MorphismProperty C) {X Y T W V : C} {f : X ⟶ Y} {b : T ⟶ Y} {f' : W ⟶ T} {p : W ⟶ X}
    (sq : IsPullback f' p b f) (g : V ⟶ Y) (a : T ⟶ V) (ha : a ≫ g = b)
    (hf : Q.universally (pullback.snd f g)) : Q f' := by
  let m : W ⟶ pullback f g := pullback.lift p (f' ≫ a) (by
    rw [Category.assoc, ha]
    exact sq.w.symm)
  have hm₁ : m ≫ pullback.fst f g = p := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd f g = f' ≫ a := pullback.lift_snd _ _ _
  have houter : IsPullback f' (m ≫ pullback.fst f g) (a ≫ g) f := by
    simpa only [hm₁, ha] using sq
  exact hf m a f' (houter.of_bot hm₂.symm (IsPullback.of_hasPullback f g).flip)

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Being an open morphism as a property of morphisms of algebraic spaces -/

/-- Being an open morphism of algebraic spaces over `S` is unchanged by precomposing with an
isomorphism, the map on points of an isomorphism being a homeomorphism. -/
theorem isOpenMorphism_iso_hom_comp {F G H : AlgebraicSpaces B S hS} (e : F ≅ G) (f : G ⟶ H)
    (hf : IsOpenMorphism B S hS f.hom) :
    IsOpenMorphism B S hS (e.hom ≫ f).hom := by
  exact IsOpenMorphism.comp B S hS hf (pointsMapHomeomorph B S hS e).isOpenMap

/-- Being an open morphism of algebraic spaces over `S` is unchanged by postcomposing with an
isomorphism, the map on points of an isomorphism being a homeomorphism. -/
theorem isOpenMorphism_comp_iso_hom {F G H : AlgebraicSpaces B S hS} (e : G ≅ H) (f : F ⟶ G)
    (hf : IsOpenMorphism B S hS f.hom) :
    IsOpenMorphism B S hS (f ≫ e.hom).hom := by
  exact IsOpenMorphism.comp B S hS (pointsMapHomeomorph B S hS e).isOpenMap hf

/-- Being an open morphism (**Stacks 03Z2**, part (1)), as a property of morphisms in the
category of algebraic spaces over `S`. -/
abbrev isOpenMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f ↦ IsOpenMorphism B S hS f.hom

/-- Being an open morphism of algebraic spaces over `S` respects isomorphisms. -/
instance isOpenMorphismProperty_respectsIso :
    (isOpenMorphismProperty B S hS).RespectsIso :=
  MorphismProperty.RespectsIso.mk _ (isOpenMorphism_iso_hom_comp B S hS)
    (isOpenMorphism_comp_iso_hom B S hS)

/-- Universal openness (**Stacks 03Z2**, part (2)), as a property of morphisms in the category
of algebraic spaces over `S`. -/
abbrev universallyOpenMorphismProperty : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f ↦ UniversallyOpen B S hS f.hom

/-- Being universally open (**Stacks 03Z2**, part (2)) is being universally an open morphism:
the chosen fibre product of Stacks 02X2 realises each of the base changes that the definition
tests, and the comparison isomorphism of two cartesian squares on one cospan carries the
property between them. -/
theorem universallyOpen_iff_universally_isOpenMorphism {X T : AlgebraicSpaces B S hS}
    (g : X ⟶ T) :
    UniversallyOpen B S hS g.hom ↔ (isOpenMorphismProperty B S hS).universally g := by
  refine ⟨fun hg Y' T' i₁ i₂ k sq ↦ ?_, fun hg Z hZ k ↦ hg _ _ _
    (AlgebraicSpaces.isPullback_fiberProduct B S hS
      (ObjectProperty.homMk (X := (⟨Z, hZ⟩ : AlgebraicSpaces B S hS)) k) g)⟩
  have hcan : isOpenMorphismProperty B S hS
      (ObjectProperty.homMk (pullback.fst i₂.hom g.hom) :
        AlgebraicSpaces.fiberProduct B S hS i₂ g ⟶ T') :=
    hg T'.obj T'.property i₂.hom
  refine ((isOpenMorphismProperty B S hS).arrow_mk_iso_iff
    (Arrow.isoMk (f := Arrow.mk (ObjectProperty.homMk (pullback.fst i₂.hom g.hom)))
      (g := Arrow.mk k)
      ((AlgebraicSpaces.isPullback_fiberProduct B S hS i₂ g).isoIsPullback T' X sq)
      (Iso.refl _) ?_)).mp hcan
  exact (AlgebraicSpaces.isPullback_fiberProduct B S hS i₂ g).isoIsPullback_hom_fst T' X sq

/-! ### Openness of a set of points, descended along an fpqc covering -/

/-- A set of points of a representable algebraic space over `S` whose preimage along every
member of an fpqc covering family of the representing scheme is open is itself open: the
identification of the two point spaces carries the question to the representing scheme, where
`AlgebraicGeometry.Space.isOpen_of_fpqc_preimages` applies. -/
theorem isOpen_points_of_fpqc_schemeCover {T : BigFppfOver B S hS} {I : Type v}
    (Tᵢ : I → BigFppfOver B S hS) (g : ∀ i, Tᵢ i ⟶ T)
    (hcover : Presieve.ofArrows (fun i ↦ (BigFppfOver.toScheme B S hS).obj (Tᵢ i))
        (fun i ↦ (BigFppfOver.toScheme B S hS).map (g i)) ∈
      Scheme.fpqcPrecoverage ((BigFppfOver.toScheme B S hS).obj T))
    (A : Set (points B S hS (yoneda.obj T)))
    (hA : ∀ i, IsOpen (pointsMap B S hS (yoneda.obj (Tᵢ i)) (yoneda.map (g i)) ⁻¹' A)) :
    IsOpen A := by
  refine ((schemePointsHomeomorph B S hS T).symm.isOpen_preimage).mp
    (isOpen_of_fpqc_preimages _ hcover _ fun i ↦ ?_)
  have hnat : ∀ x : (BigFppfOver.toScheme B S hS).obj (Tᵢ i),
      (schemePointsHomeomorph B S hS T).symm ((BigFppfOver.toScheme B S hS).map (g i) x) =
        pointsMap B S hS (yoneda.obj (Tᵢ i)) (yoneda.map (g i))
          ((schemePointsHomeomorph B S hS (Tᵢ i)).symm x) := by
    intro x
    refine (schemePointsHomeomorph B S hS T).injective ?_
    rw [Homeomorph.apply_symm_apply, schemePointsHomeomorph_apply,
      pointsToScheme_pointsMap, ← schemePointsHomeomorph_apply,
      Homeomorph.apply_symm_apply]
  have heq : (BigFppfOver.toScheme B S hS).map (g i) ⁻¹'
        ((schemePointsHomeomorph B S hS T).symm ⁻¹' A) =
      (schemePointsHomeomorph B S hS (Tᵢ i)).symm ⁻¹'
        (pointsMap B S hS (yoneda.obj (Tᵢ i)) (yoneda.map (g i)) ⁻¹' A) := by
    ext x
    simp only [Set.mem_preimage, hnat]
  rw [heq]
  exact (hA i).preimage (schemePointsHomeomorph B S hS (Tᵢ i)).symm.continuous

/-- In a cartesian square of algebraic spaces over `S` whose projection to the base is an open
morphism, the preimage along the other base morphism of the image of an open set of points is
open: by Stacks 03H4 that preimage is the image, under the open projection, of the preimage of
the set along the remaining projection. -/
theorem isOpen_preimage_image_pointsMap_of_isPullback {X Y X' Y' : AlgebraicSpaces B S hS}
    {f : X ⟶ Y} {q : Y' ⟶ Y} {f' : X' ⟶ Y'} {p : X' ⟶ X} (sq : IsPullback f' p q f)
    (hf' : IsOpenMorphism B S hS f'.hom) (V : Set (points B S hS X.obj)) (hV : IsOpen V) :
    IsOpen (pointsMap B S hS Y'.obj q.hom ⁻¹' (pointsMap B S hS X.obj f.hom '' V)) := by
  rw [pointsMap_preimage_image_of_isPullback B S hS sq.flip V]
  exact hf' _ (hV.preimage (continuous_pointsMap B S hS p.hom))

/-! ### Stacks 041P -/

/-- **Stacks 041P.** Universal openness of morphisms of algebraic spaces over `S` is local on
the base for the fpqc topology. -/
@[stacks 041P, sga "4 IV 8.5.5" "more general"]
instance universallyOpen_isLocalAtTarget_fpqc :
    (universallyOpenMorphismProperty B S hS).IsLocalAtTarget
      (Topology.precoverage.{u, v} .fpqc B S hS) := by
  have heq : universallyOpenMorphismProperty B S hS =
      (isOpenMorphismProperty B S hS).universally := by
    funext X T g
    exact propext (universallyOpen_iff_universally_isOpenMorphism B S hS g)
  rw [heq]
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff fun X Y f R hR ↦ ⟨fun hf U g _ _ ↦
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback f g) hf,
    fun hlocal ↦ ?_⟩
  refine (universallyOpen_iff_universally_isOpenMorphism B S hS f).mp
    (((universallyOpen_tfae B S hS X.property Y.property f.hom).out 3 1).mp ?_)
  intro T hT h
  obtain ⟨I, Yi, gi, rfl, hcover⟩ := hR
  obtain ⟨U, hfinite, hU, hfactor⟩ := hcover.2.2.2 ⟨T, hT⟩ h
  let h' : schemeSpace T ⟶ Y := ObjectProperty.homMk h
  let A := AlgebraicSpaces.fiberProduct B S hS h' f
  let fT : A ⟶ schemeSpace T := ObjectProperty.homMk (pullback.fst h f.hom)
  let pX : A ⟶ X := ObjectProperty.homMk (pullback.snd h f.hom)
  change IsOpenMorphism B S hS fT.hom
  intro V hV
  refine isOpen_points_of_fpqc_schemeCover B S hS
    (fun j ↦ (BigAffineFppf.inclusion B S hS).obj (U.X j))
    (fun j ↦ (BigAffineFppf.inclusion B S hS).map (U.f j)) ?_ _ fun j ↦ ?_
  · simp only [PreZeroHypercover.presieve₀, Presieve.map_ofArrows] at hU
    exact hU
  · obtain ⟨i, b, hb⟩ := hfactor j
    let q : schemeSpace ((BigAffineFppf.inclusion B S hS).obj (U.X j)) ⟶
        schemeSpace T :=
      schemeSpaceMap ((BigAffineFppf.inclusion B S hS).map (U.f j))
    let b' : schemeSpace ((BigAffineFppf.inclusion B S hS).obj (U.X j)) ⟶ Yi i :=
      ObjectProperty.homMk b
    have hs := AlgebraicSpaces.isPullback_fiberProduct B S hS q fT
    exact isOpen_preimage_image_pointsMap_of_isPullback B S hS hs
      (MorphismProperty.universally_of_factorization (isOpenMorphismProperty B S hS)
        (hs.paste_vert (AlgebraicSpaces.isPullback_fiberProduct B S hS h' f)) (gi i) b'
        (ObjectProperty.hom_ext _ hb) (hlocal (gi i) (.mk i))) V hV

/-! ### Stability of the packaged property -/

/-- **Stacks 03Z3** at the packaged property: universal openness of morphisms of algebraic spaces
over `S` is stable under base change. The unpackaged statement is
`AlgebraicGeometry.Space.universallyOpen_pullback`; the route taken here is
`AlgebraicGeometry.Space.universallyOpen_iff_universally_isOpenMorphism` instead, since
`CategoryTheory.MorphismProperty.universally` is stable under base change for any property at
all. -/
instance universallyOpen_isStableUnderBaseChange :
    (universallyOpenMorphismProperty B S hS).IsStableUnderBaseChange := by
  have heq : universallyOpenMorphismProperty B S hS =
      (isOpenMorphismProperty B S hS).universally := by
    funext X T g
    exact propext (universallyOpen_iff_universally_isOpenMorphism B S hS g)
  rw [heq]
  infer_instance

/-- **Stacks 03Z4** at the packaged property: a composition of universally open morphisms of
algebraic spaces over `S` is universally open. This registers
`AlgebraicGeometry.Space.universallyOpen_comp`, which is a theorem rather than an instance, as an
instance at the packaged property, so that instance search finds it as it finds the base-change
and target-locality instances beside it. -/
instance universallyOpen_isStableUnderComposition :
    (universallyOpenMorphismProperty B S hS).IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg :=
    universallyOpen_comp B S hS X.property Y.property Z.property f.hom g.hom hf hg

end AlgebraicGeometry.Space

end
