module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.SliceSituation
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.Splittings
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.SplittingSituations

/-!
# The stabilizer part of a source fibre, and strong splittings as splittings

Étale localization of a groupoid scheme at a point `u` of its object scheme starts from a
decomposition of the fibre `F_u = R ×_{s, U} Spec κ(u)` of the source morphism: the arrows from
`u` to itself form a piece `Z_u` of `F_u` which is open and finite over `κ(u)`, while the rest
of the fibre is discarded.  This file proves that decomposition from the standing hypotheses of
the two splitting situations, and records that a strong splitting of a groupoid in algebraic
spaces is a splitting.

The input is purely local: a *finite* set of points of a fibre at each of which the morphism is
quasi-finite is automatically open, and the open subscheme it cuts out is finite over the
residue field.  Both splitting situations supply exactly such a set — in the strong splitting
situation of Stacks 04RL it is the set of arrows with both endpoints at `u`, in the splitting
situation of Stacks 0DTB it is the set of arrows underlying the points of the stabilizer group
scheme lying over `u`.

## Main definitions

* `AlgebraicGeometry.Space.StrongSplittingSituation.toSplittingSituation`: the strong splitting
  situation of Stacks 04RL is a splitting situation in the sense of Stacks 0DTB.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.StrongSplitting.toSplitting`: a strong splitting
  at a point of the object space is a splitting there.

## Main results

* `AlgebraicGeometry.isClopen_singleton_fiber_of_quasiFiniteAt`: a point of a fibre at which the
  morphism is quasi-finite is an open and closed point of that fibre.
* `AlgebraicGeometry.exists_fiberOpens_of_finite_of_quasiFiniteAt`: a finite set of points of a
  fibre at each of which the morphism is quasi-finite is open and closed, and the open subscheme
  of the fibre it cuts out is finite over the residue field.
* `AlgebraicGeometry.stabilizerArrow_comp_source_etaleLocal`,
  `AlgebraicGeometry.stabilizerArrow_comp_target_etaleLocal` and their pointwise forms
  `AlgebraicGeometry.stabilizerArrow_source_apply`,
  `AlgebraicGeometry.stabilizerArrow_target_apply`: the arrow underlying a point of the
  stabilizer scheme has both endpoints at the point it lies over.
* `AlgebraicGeometry.stabilizerArrow_injective`: distinct points of the stabilizer scheme carry
  distinct arrows.
* `AlgebraicGeometry.Space.StrongSplittingSituation.exists_fiberOpens_stabilizer`: in the
  strong splitting situation of Stacks 04RL the arrows from `u` to itself form an open and
  closed subscheme of the fibre of the source over `u` which is finite over `κ(u)`.
* `AlgebraicGeometry.Space.SplittingSituation.exists_fiberOpens_stabilizer`: the same in the
  splitting situation of Stacks 0DTB, for the arrows underlying the points of the stabilizer
  over `u`.
* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.isSplitAt_of_isStronglySplitAt`: a groupoid in
  algebraic spaces strongly split at a point is split there.

## Implementation notes

Quasi-finiteness of `f` at `x` gives openness of the singleton `{x}` inside the fibre
`f.fiber (f x)` by `AlgebraicGeometry.Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber`.
Transporting that to the fibre `f.fiber y` over a point `y` with `f x = y` is done through the
homeomorphism `AlgebraicGeometry.Scheme.Hom.fiberHomeo` onto the set-theoretic preimage, where
the two fibres become the same set.  Finiteness over the residue field is then
`AlgebraicGeometry.IsFinite.of_locallyQuasiFinite`: the open subscheme has finitely many points,
each of them open, so it is discrete and quasi-compact over the residue field.

That a strong splitting is a splitting is the observation that the arrow underlying a point of
the stabilizer over `u` has source and target `u`, so it is one of the arrows that a strong
splitting contains.  No property of the open finite subgroupoid is used, and the two structures
share it unchanged.

## References

* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RL](https://stacks.math.columbia.edu/tag/04RL)
* [Stacks Project, Tag 0DTB](https://stacks.math.columbia.edu/tag/0DTB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- A homeomorphism carries open and closed subsets to open and closed subsets. -/
private theorem isClopen_image_homeomorph {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] (h : α ≃ₜ β) {s : Set α} : IsClopen (h '' s) ↔ IsClopen s :=
  ⟨fun hc => ⟨h.isClosed_image.mp hc.1, h.isOpen_image.mp hc.2⟩,
    fun hc => ⟨h.isClosed_image.mpr hc.1, h.isOpen_image.mpr hc.2⟩⟩

/-- A point of the fibre of `f` over `y` at which `f` is quasi-finite is an open and closed
point of that fibre. -/
theorem isClopen_singleton_fiber_of_quasiFiniteAt (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y)
    (x : f.fiber y) (hx : f.QuasiFiniteAt (f.fiberι y x)) :
    IsClopen ({x} : Set (f.fiber y)) := by
  have hfx : f (f.fiberι y x) = y := (f.fiberHomeo y x).2
  have h₁ : IsClopen ({(⟨f.fiberι y x, rfl⟩ : f ⁻¹' {f (f.fiberι y x)})} :
      Set (f ⁻¹' {f (f.fiberι y x)})) := by
    have himage : (f.fiberHomeo (f (f.fiberι y x))) '' {f.asFiber (f.fiberι y x)} =
        {(⟨f.fiberι y x, rfl⟩ : f ⁻¹' {f (f.fiberι y x)})} := by
      rw [Set.image_singleton]
      exact congrArg _ (Subtype.ext (by simp))
    exact himage ▸ (isClopen_image_homeomorph (f.fiberHomeo (f (f.fiberι y x)))).mpr
      (Scheme.Hom.QuasiFiniteAt.isClopen_singleton_asFiber f hx)
  let e : (f ⁻¹' {y} : Set X) ≃ₜ (f ⁻¹' {f (f.fiberι y x)} : Set X) :=
    Homeomorph.setCongr (by rw [hfx])
  have h₂ : IsClopen ({f.fiberHomeo y x} : Set (f ⁻¹' {y})) := by
    have himage : e '' {f.fiberHomeo y x} =
        {(⟨f.fiberι y x, rfl⟩ : f ⁻¹' {f (f.fiberι y x)})} := by
      ext z
      simp [e, Homeomorph.setCongr]
    exact (isClopen_image_homeomorph e).mp (himage ▸ h₁)
  rw [← isClopen_image_homeomorph (f.fiberHomeo y), Set.image_singleton]
  exact h₂

/-- A finite set of points of the fibre of `f` over `y`, at each of which `f` is quasi-finite,
is open and closed, and the open subscheme of the fibre which it cuts out is finite over the
residue field of `y`.

This is the decomposition `F_u = Z_u ⨿ (F_u ∖ Z_u)` which starts the étale localization of a
groupoid at a point: `Z_u` is the finite set in question, and it is a summand because it is open
and closed. -/
theorem exists_fiberOpens_of_finite_of_quasiFiniteAt (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Y) (A : Set (f.fiber y)) (hA : A.Finite)
    (hqf : ∀ x ∈ A, f.QuasiFiniteAt (f.fiberι y x)) :
    ∃ W : (f.fiber y).Opens, (W : Set (f.fiber y)) = A ∧ IsClosed A ∧
      IsFinite (W.ι ≫ f.fiberToSpecResidueField y) := by
  classical
  have hsingle : ∀ x ∈ A, IsClopen ({x} : Set (f.fiber y)) := fun x hx =>
    isClopen_singleton_fiber_of_quasiFiniteAt f y x (hqf x hx)
  have hAopen : IsOpen A := by
    rw [← Set.biUnion_of_singleton A]
    exact isOpen_biUnion fun x hx => (hsingle x hx).2
  have hAclosed : IsClosed A := by
    rw [← Set.biUnion_of_singleton A]
    exact hA.isClosed_biUnion fun x hx => (hsingle x hx).1
  let W : (f.fiber y).Opens := ⟨A, hAopen⟩
  refine ⟨W, rfl, hAclosed, ?_⟩
  have : Finite W.toScheme := hA.to_subtype
  have : LocallyOfFiniteType (f.fiberToSpecResidueField y) := by
    change LocallyOfFiniteType (pullback.snd f (Y.fromSpecResidueField y))
    infer_instance
  have : QuasiCompact (W.ι ≫ f.fiberToSpecResidueField y) :=
    ⟨fun _ _ _ => (Set.toFinite _).isCompact⟩
  have : DiscreteTopology W.toScheme := by
    refine discreteTopology_iff_isOpen_singleton.2 fun z => ?_
    have hz : IsOpen ((Subtype.val : W.toScheme → f.fiber y) ⁻¹' {z.1}) :=
      (hsingle z.1 z.2).2.preimage continuous_subtype_val
    have heq : ({z} : Set W.toScheme) =
        (Subtype.val : W.toScheme → f.fiber y) ⁻¹' {z.1} :=
      Set.ext fun _ => Subtype.ext_iff
    exact heq ▸ hz
  have : LocallyQuasiFinite (W.ι ≫ f.fiberToSpecResidueField y) :=
    locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr fun _ =>
      _root_.isDiscrete_iff_discreteTopology.mpr inferInstance
  exact IsFinite.of_locallyQuasiFinite (W.ι ≫ f.fiberToSpecResidueField y)

variable {S : Scheme.{u}}

/-- The arrow underlying a point of the stabilizer scheme has source the point of the object
scheme it lies over. -/
theorem stabilizerArrow_comp_source_etaleLocal (G : Stacks.Groupoids.GroupoidScheme S) :
    stabilizerArrow G ≫ G.source.left = (stabilizer G).hom := by
  simpa [stabilizerArrowHom] using
    congrArg Over.Hom.left (stabilizerArrowHom_source G (𝟙 (stabilizer G)))

/-- The arrow underlying a point of the stabilizer scheme has target the point of the object
scheme it lies over. -/
theorem stabilizerArrow_comp_target_etaleLocal (G : Stacks.Groupoids.GroupoidScheme S) :
    stabilizerArrow G ≫ G.target.left = (stabilizer G).hom := by
  simpa [stabilizerArrowHom] using
    congrArg Over.Hom.left (stabilizerArrowHom_target G (𝟙 (stabilizer G)))

/-- On points: the arrow underlying a point of the stabilizer scheme has source the point of the
object scheme it lies over. -/
theorem stabilizerArrow_source_apply (G : Stacks.Groupoids.GroupoidScheme S)
    (g : (stabilizer G).left) :
    G.source.left (stabilizerArrow G g) = (stabilizer G).hom g := by
  rw [← stabilizerArrow_comp_source_etaleLocal G, Scheme.Hom.comp_apply]

/-- On points: the arrow underlying a point of the stabilizer scheme has target the point of the
object scheme it lies over. -/
theorem stabilizerArrow_target_apply (G : Stacks.Groupoids.GroupoidScheme S)
    (g : (stabilizer G).left) :
    G.target.left (stabilizerArrow G g) = (stabilizer G).hom g := by
  rw [← stabilizerArrow_comp_target_etaleLocal G, Scheme.Hom.comp_apply]

/-- The stabilizer scheme is a subscheme of the arrow scheme, so distinct points of it carry
distinct arrows. -/
theorem stabilizerArrow_injective (G : Stacks.Groupoids.GroupoidScheme S) :
    Function.Injective fun g : (stabilizer G).left => stabilizerArrow G g := by
  have : IsImmersion (stabilizerArrow G) := stabilizerArrow_isImmersion G
  exact (stabilizerArrow G).isEmbedding.injective

namespace Space

/-- In the strong splitting situation of Stacks 04RL the arrows whose source and target are both
the chosen point `u` cut out an open and closed subscheme of the fibre of the source morphism
over `u` which is finite over the residue field `κ(u)`.

This is the summand `Z_u` of the fibre `F_u` from which the étale neighbourhood of Stacks 03FM
is built; it is produced here from the finiteness of the stabilizer of `u` and the
quasi-finiteness of the source along it, which are the two standing hypotheses of Stacks
04RL. -/
theorem StrongSplittingSituation.exists_fiberOpens_stabilizer
    (D : StrongSplittingSituation.{u}) :
    ∃ W : (D.groupoid.source.left.fiber D.u).Opens,
      (∀ x : D.groupoid.source.left.fiber D.u,
        x ∈ W ↔
          D.groupoid.target.left (D.groupoid.source.left.fiberι D.u x) = D.u) ∧
      IsClosed (W : Set (D.groupoid.source.left.fiber D.u)) ∧
      _root_.AlgebraicGeometry.IsFinite
        (W.ι ≫ D.groupoid.source.left.fiberToSpecResidueField D.u) := by
  classical
  have hinj : Function.Injective (D.groupoid.source.left.fiberι D.u) := fun a b h =>
    (D.groupoid.source.left.fiberHomeo D.u).injective (Subtype.ext h)
  set A : Set (D.groupoid.source.left.fiber D.u) :=
    D.groupoid.source.left.fiberι D.u ⁻¹'
      {r : D.groupoid.arrows.left |
        D.groupoid.source.left r = D.u ∧ D.groupoid.target.left r = D.u}
  obtain ⟨W, hW, hclosed, hfin⟩ := exists_fiberOpens_of_finite_of_quasiFiniteAt
    D.groupoid.source.left D.u A (Set.Finite.preimage hinj.injOn D.stabilizer_finite)
    (fun x hx => (D.source_quasiFiniteAt _ hx).2)
  refine ⟨W, fun x => ?_, hW ▸ hclosed, hfin⟩
  rw [← SetLike.mem_coe, hW]
  exact ⟨fun h => h.2, fun h => ⟨(D.groupoid.source.left.fiberHomeo D.u x).2, h⟩⟩

/-- The strong splitting situation of Stacks 04RL is in particular a splitting situation in the
sense of Stacks 0DTB: the stabilizer scheme is a subscheme of the arrow scheme, so its points
over `u` are among the arrows with both endpoints at `u`.

The converse fails.  A point of the arrow scheme with both endpoints at `u` need not lie on the
stabilizer: the stabilizer is the fibre product of `(t, s) : R ⟶ U ×_S U` with the diagonal, and
a point of `U ×_S U` whose two projections are both `u` need not be the image of `u` under the
diagonal.  So Stacks 0DTB is strictly the weaker standing hypothesis and Stacks 0DTC is not a
formal consequence of Stacks 03FM. -/
def StrongSplittingSituation.toSplittingSituation (D : StrongSplittingSituation.{u}) :
    SplittingSituation.{u} where
  S := D.S
  groupoid := D.groupoid
  u := D.u
  stabilizer_finite :=
    (D.stabilizer_finite.preimage (stabilizerArrow_injective D.groupoid).injOn).subset
      fun g hg => ⟨(stabilizerArrow_source_apply D.groupoid g).trans hg,
        (stabilizerArrow_target_apply D.groupoid g).trans hg⟩
  source_quasiFiniteAt := fun g hg =>
    D.source_quasiFiniteAt (stabilizerArrow D.groupoid g)
      ⟨(stabilizerArrow_source_apply D.groupoid g).trans hg,
        (stabilizerArrow_target_apply D.groupoid g).trans hg⟩

/-- In the splitting situation of Stacks 0DTB the arrows underlying the points of the stabilizer
group scheme lying over the chosen point `u` cut out an open and closed subscheme of the fibre of
the source morphism over `u` which is finite over the residue field `κ(u)`.

This is the summand `Z_u` of the fibre `F_u` from which the étale neighbourhood of Stacks 0DTC
is built; it is produced here from the finiteness of the fibre of the stabilizer over `u` and
the quasi-finiteness of the source along it, which are the two standing hypotheses of Stacks
0DTB.  The second conclusion says that every point of the stabilizer over `u` is accounted
for. -/
theorem SplittingSituation.exists_fiberOpens_stabilizer (D : SplittingSituation.{u}) :
    ∃ W : (D.groupoid.source.left.fiber D.u).Opens,
      (∀ x : D.groupoid.source.left.fiber D.u,
        x ∈ W ↔ ∃ g : (stabilizer D.groupoid).left,
          (stabilizer D.groupoid).hom g = D.u ∧
            stabilizerArrow D.groupoid g =
              D.groupoid.source.left.fiberι D.u x) ∧
      (∀ g : (stabilizer D.groupoid).left, (stabilizer D.groupoid).hom g = D.u →
        ∃ x : D.groupoid.source.left.fiber D.u, x ∈ W ∧
          D.groupoid.source.left.fiberι D.u x = stabilizerArrow D.groupoid g) ∧
      IsClosed (W : Set (D.groupoid.source.left.fiber D.u)) ∧
      _root_.AlgebraicGeometry.IsFinite
        (W.ι ≫ D.groupoid.source.left.fiberToSpecResidueField D.u) := by
  classical
  have hinj : Function.Injective (D.groupoid.source.left.fiberι D.u) := fun a b h =>
    (D.groupoid.source.left.fiberHomeo D.u).injective (Subtype.ext h)
  set A : Set (D.groupoid.source.left.fiber D.u) :=
    D.groupoid.source.left.fiberι D.u ⁻¹'
      (stabilizerArrow D.groupoid ''
        {g : (stabilizer D.groupoid).left | (stabilizer D.groupoid).hom g = D.u})
  obtain ⟨W, hW, hclosed, hfin⟩ := exists_fiberOpens_of_finite_of_quasiFiniteAt
    D.groupoid.source.left D.u A
    (Set.Finite.preimage hinj.injOn (D.stabilizer_finite.image _))
    (fun x hx => by
      obtain ⟨g, hg, hgx⟩ := hx
      exact hgx ▸ (D.source_quasiFiniteAt g hg).2)
  have hWA : ∀ x : D.groupoid.source.left.fiber D.u, (x ∈ W) = (x ∈ A) := fun x =>
    congrArg (x ∈ ·) hW
  refine ⟨W, fun x => (hWA x) ▸ Iff.rfl, fun g hg => ?_, hW ▸ hclosed, hfin⟩
  have hx := Scheme.Hom.fiberι_fiberHomeo_symm D.groupoid.source.left D.u
    ⟨stabilizerArrow D.groupoid g, (stabilizerArrow_source_apply D.groupoid g).trans hg⟩
  refine ⟨_, ?_, hx⟩
  rw [hWA]
  exact ⟨g, hg, hx.symm⟩

end Space

namespace GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {hS : C.Contains S} {B : AlgebraicSpaces C S hS}

/-- A strong splitting of a groupoid in algebraic spaces at a point of its object space is a
splitting there: the arrow underlying a point of the stabilizer over the point has both
endpoints at that point, so a strong splitting already contains it. -/
def StrongSplitting.toSplitting {G : GroupoidInAlgebraicSpaces C S hS B}
    {u : Space.points C S hS G.objects.obj} (H : StrongSplitting G u) : Splitting G u :=
  { H.toOpenFiniteSubgroupoid with
    contains_stabilizer := fun g hg =>
      H.contains_arrows (Space.pointsMap C S hS (stabilizer G).left (stabilizerArrow G) g)
        ⟨by rwa [← stabilizerArrow_source G, Space.pointsMap_comp] at hg,
          by rwa [← stabilizerArrow_target G, Space.pointsMap_comp] at hg⟩ }

/-- A groupoid in algebraic spaces which is strongly split at a point of its object space is
split there. -/
theorem isSplitAt_of_isStronglySplitAt {G : GroupoidInAlgebraicSpaces C S hS B}
    {u : Space.points C S hS G.objects.obj} (h : IsStronglySplitAt G u) : IsSplitAt G u :=
  ⟨h.some.toSplitting⟩

end GroupoidInAlgebraicSpaces

end AlgebraicGeometry

end
