module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Compose
public import StacksCore.Tactic.StacksAttribute

/-!
# The stabilizer group scheme of a groupoid scheme

The inverse image of the diagonal under the source-target morphism of a groupoid scheme is a
group scheme over its object scheme.  Its multiplication is induced by composition in the
groupoid.

## Main definitions

* `AlgebraicGeometry.stabilizerOverBase` is the pullback of the source-target morphism along
  the diagonal, viewed over the original base.
* `AlgebraicGeometry.stabilizer` is the same scheme viewed over the object scheme.
* `AlgebraicGeometry.stabilizerGroupStructure` equips the stabilizer with its canonical
  group-scheme structure.
* `AlgebraicGeometry.stabilizerMap` is the canonical morphism between the stabilizers induced
  by a morphism of groupoid schemes.

## Main results

* `AlgebraicGeometry.stabilizer_mul_comp_arrow` identifies multiplication in the stabilizer
  with composition in the groupoid.

## Implementation notes

The fibre product in the displayed square is formed in `Over S`; its second projection makes
it an object of `Over G.objects.left`.  A group scheme over the object scheme is represented by
a `GrpObj` structure on this object.  The multiplication compatibility is stated on generalized
points, where the projection to the arrow scheme turns multiplication into
`Stacks.Groupoids.GroupoidScheme.compose`.

## References

* [Stacks Project, Tag 0235](https://stacks.math.columbia.edu/tag/0235)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CartesianMonoidalCategory MonoidalCategory MonObj
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- The source-target morphism `(target, source)` of a groupoid scheme. -/
noncomputable abbrev sourceTarget {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.arrows ⟶ G.objects ⊗ G.objects :=
  lift G.target G.source

/-- The diagonal of the object scheme, formed in schemes over the base. -/
noncomputable abbrev diagonal {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.objects ⟶ G.objects ⊗ G.objects :=
  lift (𝟙 G.objects) (𝟙 G.objects)

/-- The stabilizer scheme over the original base: the pullback of `(target, source)` along the
diagonal. -/
@[sga "3 V 10.2.1" "more general"]
noncomputable abbrev stabilizerOverBase {S : Scheme.{u}} (G : GroupoidScheme S) : Over S :=
  pullback (sourceTarget G) (diagonal G)

/-- The stabilizer scheme, regarded as a scheme over the object scheme. -/
noncomputable abbrev stabilizer {S : Scheme.{u}} (G : GroupoidScheme S) :
    Over G.objects.left :=
  Over.mk (pullback.snd (sourceTarget G) (diagonal G)).left

/-- The canonical projection from the stabilizer to the arrow scheme. -/
noncomputable abbrev stabilizerArrow {S : Scheme.{u}} (G : GroupoidScheme S) :
    (stabilizer G).left ⟶ G.arrows.left :=
  (pullback.fst (sourceTarget G) (diagonal G)).left

/-- The canonical morphism between the stabilizers induced by a morphism of groupoid schemes:
the map on arrows carries an arrow with equal source and target to one with equal source and
target, so it lifts to the two fibre products defining the stabilizers. -/
noncomputable def stabilizerMap {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : GroupoidScheme.Hom G' G) : stabilizerOverBase G' ⟶ stabilizerOverBase G :=
  pullback.lift
    (pullback.fst (sourceTarget G') (diagonal G') ≫ F.mapArrows)
    (pullback.snd (sourceTarget G') (diagonal G') ≫ F.mapObjects) (by
      have h := pullback.condition (f := sourceTarget G') (g := diagonal G')
      have ht : pullback.fst (sourceTarget G') (diagonal G') ≫ G'.target =
          pullback.snd (sourceTarget G') (diagonal G') := by
        rw [← Category.comp_id (pullback.snd (sourceTarget G') (diagonal G')),
          ← CartesianMonoidalCategory.lift_fst (𝟙 G'.objects) (𝟙 G'.objects),
          ← Category.assoc, ← h]
        simp [sourceTarget]
      have hs : pullback.fst (sourceTarget G') (diagonal G') ≫ G'.source =
          pullback.snd (sourceTarget G') (diagonal G') := by
        rw [← Category.comp_id (pullback.snd (sourceTarget G') (diagonal G')),
          ← CartesianMonoidalCategory.lift_snd (𝟙 G'.objects) (𝟙 G'.objects),
          ← Category.assoc, ← h]
        simp [sourceTarget]
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, CartesianMonoidalCategory.lift_fst]
        rw [F.map_target, ← Category.assoc, ht]
        simp [diagonal]
      · simp only [Category.assoc, CartesianMonoidalCategory.lift_snd]
        rw [F.map_source, ← Category.assoc, hs]
        simp [diagonal])

/-- The map of stabilizers followed by the projection to arrows is the map induced from the
arrow component of the groupoid morphism. -/
@[reassoc]
theorem stabilizerMap_fst {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : GroupoidScheme.Hom G' G) :
    stabilizerMap F ≫ pullback.fst (sourceTarget G) (diagonal G) =
      pullback.fst (sourceTarget G') (diagonal G') ≫ F.mapArrows :=
  pullback.lift_fst _ _ _

/-- The map of stabilizers followed by the projection to objects is the map induced from the
object component of the groupoid morphism. -/
@[reassoc]
theorem stabilizerMap_snd {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : GroupoidScheme.Hom G' G) :
    stabilizerMap F ≫ pullback.snd (sourceTarget G) (diagonal G) =
      pullback.snd (sourceTarget G') (diagonal G') ≫ F.mapObjects :=
  pullback.lift_snd _ _ _

/-- On underlying schemes, the map of stabilizers carries the arrow underlying a point of the
stabilizer of `G'` to the image of that arrow under the map on arrow schemes. -/
@[reassoc]
theorem stabilizerMap_left_comp_stabilizerArrow {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : GroupoidScheme.Hom G' G) :
    (stabilizerMap F).left ≫ stabilizerArrow G = stabilizerArrow G' ≫ F.mapArrows.left := by
  simpa only [Over.comp_left] using congrArg Over.Hom.left (stabilizerMap_fst F)

/-- On underlying schemes, the map of stabilizers lies over the map on object schemes. -/
@[reassoc]
theorem stabilizerMap_left_comp_hom {S : Scheme.{u}} {G G' : GroupoidScheme S}
    (F : GroupoidScheme.Hom G' G) :
    (stabilizerMap F).left ≫ (stabilizer G).hom =
      (stabilizer G').hom ≫ F.mapObjects.left := by
  have h := congrArg Over.Hom.left (stabilizerMap_snd F)
  simp only [Over.comp_left] at h
  exact h

/-- A generalized point of the stabilizer, regarded as a generalized arrow of the groupoid. -/
noncomputable def stabilizerArrowHom {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (f : T ⟶ stabilizer G) :
    (Over.map G.objects.hom).obj T ⟶ G.arrows :=
  Over.homMk (f.left ≫ stabilizerArrow G) (by
    calc
      (f.left ≫ stabilizerArrow G) ≫ G.arrows.hom =
          f.left ≫ (pullback (sourceTarget G) (diagonal G)).hom := by
            rw [Category.assoc]
            exact congrArg (f.left ≫ ·)
              (pullback.fst (sourceTarget G) (diagonal G)).w
      _ = f.left ≫ (pullback.snd (sourceTarget G) (diagonal G)).left ≫
          G.objects.hom := by
            rw [(pullback.snd (sourceTarget G) (diagonal G)).w]
      _ = T.hom ≫ G.objects.hom := by
            rw [← Category.assoc]
            congr 1
            simpa [stabilizer] using f.w)

/-- A generalized stabilizer arrow composed with `s` is its object over `G.objects`, where `s` is
a projection of the source-target morphism. -/
private lemma stabilizerArrowHom_comp_eq {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (f : T ⟶ stabilizer G) (s : G.arrows ⟶ G.objects)
    (π : G.objects ⊗ G.objects ⟶ G.objects) (h₁ : sourceTarget G ≫ π = s)
    (h₂ : diagonal G ≫ π = 𝟙 _) : stabilizerArrowHom G f ≫ s = Over.homMk T.hom := by
  ext
  have hs : pullback.fst (sourceTarget G) (diagonal G) ≫ s =
      pullback.snd (sourceTarget G) (diagonal G) := by
    rw [← h₁, ← Category.assoc, pullback.condition, Category.assoc, h₂, Category.comp_id]
  have hl := congrArg Over.Hom.left hs
  simp only [Over.comp_left] at hl
  change (f.left ≫ (pullback.fst (sourceTarget G) (diagonal G)).left) ≫ s.left = T.hom
  rw [Category.assoc, hl]
  simpa [stabilizer] using f.w

/-- A generalized stabilizer arrow has source equal to its object over `G.objects`. -/
lemma stabilizerArrowHom_source {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (f : T ⟶ stabilizer G) :
    stabilizerArrowHom G f ≫ G.source = Over.homMk T.hom :=
  stabilizerArrowHom_comp_eq G f _ (snd _ _) (by simp [sourceTarget]) (by simp [diagonal])

/-- A generalized stabilizer arrow has target equal to its object over `G.objects`. -/
lemma stabilizerArrowHom_target {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (f : T ⟶ stabilizer G) :
    stabilizerArrowHom G f ≫ G.target = Over.homMk T.hom :=
  stabilizerArrowHom_comp_eq G f _ (fst _ _) (by simp [sourceTarget]) (by simp [diagonal])

/-- Two generalized stabilizer arrows over the same object are composable in the groupoid. -/
lemma stabilizerArrowHom_composable {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (f g : T ⟶ stabilizer G) :
    stabilizerArrowHom G f ≫ G.source = stabilizerArrowHom G g ≫ G.target :=
  (stabilizerArrowHom_source G f).trans (stabilizerArrowHom_target G g).symm

/-- A generalized point of the stabilizer is determined by the generalized arrow it induces. -/
lemma stabilizerArrowHom_injective {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} {f g : T ⟶ stabilizer G}
    (h : stabilizerArrowHom G f = stabilizerArrowHom G g) : f = g := by
  apply Over.OverMorphism.ext
  let T' : Over S := Over.mk (T.hom ≫ G.objects.hom)
  let F (k : T ⟶ stabilizer G) : T' ⟶ pullback (sourceTarget G) (diagonal G) :=
    Over.homMk k.left (by
      change k.left ≫ (pullback (sourceTarget G) (diagonal G)).hom =
        T.hom ≫ G.objects.hom
      simpa [stabilizer, Category.assoc] using
        congrArg (fun k => k ≫ G.objects.hom) k.w)
  have e : F f = F g := by
    apply pullback.hom_ext
    · exact Over.OverMorphism.ext (congrArg Over.Hom.left h)
    · apply Over.OverMorphism.ext
      simpa [F, stabilizer] using f.w.trans g.w.symm
  simpa [F] using congrArg Over.Hom.left e

/-- A group-object structure on the stabilizer whose multiplication is induced by composition
in the groupoid. -/
def IsStabilizerGroupStructure {S : Scheme.{u}} (G : GroupoidScheme S)
    (h : GrpObj (stabilizer G)) : Prop :=
  letI := h
  ∀ (T : Over G.objects.left) (f g : T ⟶ stabilizer G),
    stabilizerArrowHom G (lift f g ≫ μ[stabilizer G]) =
      G.compose (stabilizerArrowHom G f) (stabilizerArrowHom G g)
        (stabilizerArrowHom_composable G f g)

/-- Multiplication of the stabilizer: on generalized points it is composition in the
groupoid. -/
noncomputable def stabilizerMul {S : Scheme.{u}} (G : GroupoidScheme S) :
    (stabilizer G ⊗ stabilizer G) ⟶ stabilizer G := by
  let P := stabilizer G ⊗ stabilizer G
  let f : (Over.map G.objects.hom).obj P ⟶ G.arrows :=
    stabilizerArrowHom G (fst (stabilizer G) (stabilizer G))
  let g : (Over.map G.objects.hom).obj P ⟶ G.arrows :=
    stabilizerArrowHom G (snd (stabilizer G) (stabilizer G))
  let u : (Over.map G.objects.hom).obj P ⟶ G.arrows :=
    G.compose f g (stabilizerArrowHom_composable G
      (fst (stabilizer G) (stabilizer G)) (snd (stabilizer G) (stabilizer G)))
  let v : (Over.map G.objects.hom).obj P ⟶ G.objects :=
    Over.homMk P.hom (by simp [P])
  exact Over.homMk (pullback.lift u v (by
    apply hom_ext
    · simp only [Category.assoc, sourceTarget, diagonal, lift_fst]
      dsimp [u, v]
      simp only [GroupoidScheme.compose, Category.assoc, G.target_comp,
        pullback.lift_fst_assoc, Category.comp_id]
      exact stabilizerArrowHom_target G (fst (stabilizer G) (stabilizer G))
    · simp only [Category.assoc, sourceTarget, diagonal, lift_snd]
      dsimp [u, v]
      simp only [GroupoidScheme.compose, Category.assoc, G.source_comp,
        pullback.lift_snd_assoc, Category.comp_id]
      exact stabilizerArrowHom_source G (snd (stabilizer G) (stabilizer G)))).left (by
    change (pullback.lift u v _).left ≫
      (pullback.snd (sourceTarget G) (diagonal G)).left = P.hom
    calc
      (pullback.lift u v _).left ≫
          (pullback.snd (sourceTarget G) (diagonal G)).left = v.left :=
        congrArg Over.Hom.left (pullback.lift_snd u v _)
      _ = P.hom := rfl)

/-- The unit of the stabilizer: the identity arrow at an object. -/
noncomputable def stabilizerOne {S : Scheme.{u}} (G : GroupoidScheme S) :
    𝟙_ (Over G.objects.left) ⟶ stabilizer G := by
  let u : (Over.map G.objects.hom).obj (𝟙_ (Over G.objects.left)) ⟶ G.arrows :=
    Over.homMk (𝟙 G.objects.left ≫ G.identity.left) (by simp)
  let v : (Over.map G.objects.hom).obj (𝟙_ (Over G.objects.left)) ⟶ G.objects :=
    Over.homMk (𝟙 G.objects.left) (by simp)
  exact Over.homMk (pullback.lift u v (by
    apply hom_ext
    · ext
      simpa [u, v] using congrArg Over.Hom.left G.target_identity
    · ext
      simpa [u, v] using congrArg Over.Hom.left G.source_identity)).left (by
    change (pullback.lift u v _).left ≫
      (pullback.snd (sourceTarget G) (diagonal G)).left = 𝟙 G.objects.left
    simpa [v] using congrArg Over.Hom.left (pullback.lift_snd u v _))

/-- Inversion of the stabilizer: on generalized points it is inversion in the groupoid. -/
noncomputable def stabilizerInv {S : Scheme.{u}} (G : GroupoidScheme S) :
    stabilizer G ⟶ stabilizer G := by
  let P := stabilizer G
  let u : (Over.map G.objects.hom).obj P ⟶ G.arrows :=
    stabilizerArrowHom G (𝟙 P) ≫ G.inverse
  let v : (Over.map G.objects.hom).obj P ⟶ G.objects :=
    Over.homMk P.hom (by simp [P])
  exact Over.homMk (pullback.lift u v (by
    simp only [sourceTarget, diagonal]
    apply hom_ext
    · dsimp [u, v]
      simp only [lift_fst, Category.assoc, Category.comp_id]
      simpa only [Category.assoc, G.target_inverse] using
        stabilizerArrowHom_source G (𝟙 P)
    · dsimp [u, v]
      simp only [lift_snd, Category.assoc, Category.comp_id]
      simpa only [Category.assoc, G.source_inverse] using
        stabilizerArrowHom_target G (𝟙 P))).left (by
    change (pullback.lift u v _).left ≫
      (pullback.snd (sourceTarget G) (diagonal G)).left = P.hom
    simpa [v] using congrArg Over.Hom.left (pullback.lift_snd u v _))

/-- The generalized arrow attached to a product of two generalized points of the stabilizer is
their groupoid composite. -/
private lemma stabilizerArrowHom_mul {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (f g : T ⟶ stabilizer G) :
    stabilizerArrowHom G (lift f g ≫ stabilizerMul G) =
      G.compose (stabilizerArrowHom G f) (stabilizerArrowHom G g)
        (stabilizerArrowHom_composable G f g) := by
  let P := stabilizer G ⊗ stabilizer G
  let a : (Over.map G.objects.hom).obj P ⟶ G.arrows :=
    stabilizerArrowHom G (fst (stabilizer G) (stabilizer G))
  let b : (Over.map G.objects.hom).obj P ⟶ G.arrows :=
    stabilizerArrowHom G (snd (stabilizer G) (stabilizer G))
  have ab : a ≫ G.source = b ≫ G.target :=
    stabilizerArrowHom_composable G (fst (stabilizer G) (stabilizer G))
      (snd (stabilizer G) (stabilizer G))
  let c : (Over.map G.objects.hom).obj P ⟶ G.arrows :=
    G.compose a b ab
  let p : (Over.map G.objects.hom).obj P ⟶ G.objects := Over.homMk P.hom (by simp [P])
  have cp : c ≫ sourceTarget G = p ≫ diagonal G := by
    apply hom_ext
    · simp only [Category.assoc, sourceTarget, diagonal, lift_fst]
      dsimp [c, p, a, b]
      simp only [GroupoidScheme.compose, Category.assoc, G.target_comp,
        pullback.lift_fst_assoc, Category.comp_id]
      exact stabilizerArrowHom_target G (fst (stabilizer G) (stabilizer G))
    · simp only [Category.assoc, sourceTarget, diagonal, lift_snd]
      dsimp [c, p, a, b]
      simp only [GroupoidScheme.compose, Category.assoc, G.source_comp,
        pullback.lift_snd_assoc, Category.comp_id]
      exact stabilizerArrowHom_source G (snd (stabilizer G) (stabilizer G))
  apply Over.OverMorphism.ext
  change (lift f g).left ≫ (stabilizerMul G).left ≫ stabilizerArrow G =
    (G.compose (stabilizerArrowHom G f) (stabilizerArrowHom G g) _).left
  dsimp only [stabilizerMul]
  have hc := congrArg Over.Hom.left (pullback.lift_fst c p cp)
  change (pullback.lift c p cp).left ≫ stabilizerArrow G = c.left at hc
  change (lift f g).left ≫ (pullback.lift c p cp).left ≫ stabilizerArrow G = _
  rw [hc]
  have e := groupoidCompose_pre G
    (k := (Over.map G.objects.hom).map (lift f g)) (f := a) (g := b) ab
  have em : ∀ p : stabilizer G ⊗ stabilizer G ⟶ stabilizer G, (Over.map G.objects.hom).map
      (lift f g) ≫ stabilizerArrowHom G p = stabilizerArrowHom G (lift f g ≫ p) := fun p => by
    apply Over.OverMorphism.ext
    rfl
  have e' : (Over.map G.objects.hom).map (lift f g) ≫ G.compose a b ab =
      G.compose (stabilizerArrowHom G f) (stabilizerArrowHom G g)
        (stabilizerArrowHom_composable G f g) := by
    simpa only [a, b, em, lift_fst, lift_snd] using e
  simpa [c, a, b, stabilizerArrowHom, Over.comp_left] using congrArg Over.Hom.left e'

/-- The generalized arrow attached to the unit of the stabilizer is the identity arrow. -/
lemma stabilizerArrowHom_stabilizerOne {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (k : T ⟶ 𝟙_ (Over G.objects.left)) :
    stabilizerArrowHom G (k ≫ stabilizerOne G) =
      Over.homMk T.hom ≫ G.identity := by
  apply Over.OverMorphism.ext
  change k.left ≫ (stabilizerOne G).left ≫ stabilizerArrow G =
    T.hom ≫ G.identity.left
  have h : (stabilizerOne G).left ≫ stabilizerArrow G = G.identity.left := by
    have hh : (stabilizerOne G).left ≫ stabilizerArrow G =
        𝟙 G.objects.left ≫ G.identity.left :=
      congrArg Over.Hom.left (pullback.lift_fst _ _ _)
    simpa only [Category.id_comp] using hh
  rw [h]
  simpa using congrArg (fun z => z ≫ G.identity.left) k.w

/-- The generalized arrow attached to the inverse of a generalized point of the stabilizer is
the groupoid inverse. -/
private lemma stabilizerArrowHom_inv {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (f : T ⟶ stabilizer G) :
    stabilizerArrowHom G (f ≫ stabilizerInv G) =
      stabilizerArrowHom G f ≫ G.inverse := by
  apply Over.OverMorphism.ext
  change f.left ≫ (stabilizerInv G).left ≫ stabilizerArrow G =
    (f.left ≫ stabilizerArrow G) ≫ G.inverse.left
  have h : (stabilizerInv G).left ≫ stabilizerArrow G =
      stabilizerArrow G ≫ G.inverse.left := by
    have hh : (stabilizerInv G).left ≫ stabilizerArrow G =
        (stabilizerArrowHom G (𝟙 (stabilizer G)) ≫ G.inverse).left :=
      congrArg Over.Hom.left (pullback.lift_fst _ _ _)
    refine hh.trans ?_
    change (𝟙 (stabilizer G).left ≫ stabilizerArrow G) ≫ G.inverse.left =
      stabilizerArrow G ≫ G.inverse.left
    rw [Category.id_comp]
  rw [h]
  simp only [Category.assoc]

/-- Multiplication of the stabilizer is associative on generalized points. -/
private lemma stabilizerArrowHom_mul_assoc {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (f g h : T ⟶ stabilizer G) :
    stabilizerArrowHom G
        (lift (lift f g ≫ stabilizerMul G) h ≫ stabilizerMul G) =
      stabilizerArrowHom G
        (lift f (lift g h ≫ stabilizerMul G) ≫ stabilizerMul G) := by
  let a := stabilizerArrowHom G f
  let b := stabilizerArrowHom G g
  let c := stabilizerArrowHom G h
  have wab : a ≫ G.source = b ≫ G.target := stabilizerArrowHom_composable G f g
  have wbc : b ≫ G.source = c ≫ G.target := stabilizerArrowHom_composable G g h
  have w₁ : G.compose a b wab ≫ G.source = c ≫ G.target := by
    simpa only [GroupoidScheme.compose, Category.assoc, G.source_comp,
      pullback.lift_snd_assoc] using wbc
  have w₂ : a ≫ G.source = G.compose b c wbc ≫ G.target := by
    simpa only [GroupoidScheme.compose, Category.assoc, G.target_comp,
      pullback.lift_fst_assoc] using wab
  simp only [stabilizerArrowHom_mul]
  simpa only [GroupoidScheme.compose, a, b, c] using G.assoc _ a b c wab wbc w₁ w₂

/-- **Stacks Project, Tag 0235.** The stabilizer of a groupoid scheme is canonically a group
scheme over its object scheme, with multiplication induced by groupoid composition. -/
@[stacks 0235,
  stacks 0236 "the stabilizer group scheme of a groupoid scheme",
  sga "3 V 10.2.1" "X-group scheme"]
noncomputable def stabilizerGroupStructure {S : Scheme.{u}} (G : GroupoidScheme S) :
    { h : GrpObj (stabilizer G) // IsStabilizerGroupStructure G h } := by
  let h : GrpObj (stabilizer G) :=
    { one := stabilizerOne G
      mul := stabilizerMul G
      inv := stabilizerInv G
      one_mul := by
        rw [← lift_comp_fst_snd (stabilizerOne G ▷ stabilizer G)]
        simp only [whiskerRight_fst, whiskerRight_snd]
        apply stabilizerArrowHom_injective G
        rw [stabilizerArrowHom_mul]
        let f := snd (𝟙_ (Over G.objects.left)) (stabilizer G)
        have hu : stabilizerArrowHom G
            (fst (𝟙_ (Over G.objects.left)) (stabilizer G) ≫ stabilizerOne G) =
            stabilizerArrowHom G f ≫ G.target ≫ G.identity := by
          rw [stabilizerArrowHom_stabilizerOne]
          simpa only [Category.assoc] using
            congrArg (fun z => z ≫ G.identity) (stabilizerArrowHom_target G f).symm
        simpa only [GroupoidScheme.compose, hu, f, leftUnitor_hom] using
          (G.left_identity _ (stabilizerArrowHom G f) (by
            simp only [Category.assoc, G.source_identity, Category.comp_id]))
      mul_one := by
        rw [← lift_comp_fst_snd (stabilizer G ◁ stabilizerOne G)]
        simp only [whiskerLeft_fst, whiskerLeft_snd]
        apply stabilizerArrowHom_injective G
        rw [stabilizerArrowHom_mul]
        let f := fst (stabilizer G) (𝟙_ (Over G.objects.left))
        have hu : stabilizerArrowHom G
            (snd (stabilizer G) (𝟙_ (Over G.objects.left)) ≫ stabilizerOne G) =
            stabilizerArrowHom G f ≫ G.source ≫ G.identity := by
          rw [stabilizerArrowHom_stabilizerOne]
          simpa only [Category.assoc] using
            congrArg (fun z => z ≫ G.identity) (stabilizerArrowHom_source G f).symm
        simpa only [GroupoidScheme.compose, hu, f, rightUnitor_hom] using
          (G.right_identity _ (stabilizerArrowHom G f) (by
            simp only [Category.assoc, G.target_identity, Category.comp_id]))
      mul_assoc := by
        let H := stabilizer G
        let f : (H ⊗ H) ⊗ H ⟶ H := fst (H ⊗ H) H ≫ fst H H
        let g : (H ⊗ H) ⊗ H ⟶ H := fst (H ⊗ H) H ≫ snd H H
        let h : (H ⊗ H) ⊗ H ⟶ H := snd (H ⊗ H) H
        have hfg : lift f g = fst (H ⊗ H) H := by
          dsimp [f, g]
          rw [← comp_lift, lift_fst_snd, Category.comp_id]
        have hgh : lift g h = (α_ H H H).hom ≫ snd H (H ⊗ H) := by
          apply hom_ext
          · simp only [lift_fst, Category.assoc, associator_hom_snd_fst]
            rfl
          · simp only [lift_snd, Category.assoc, associator_hom_snd_snd]
            rfl
        have eL : lift (lift f g ≫ stabilizerMul G) h =
            stabilizerMul G ▷ H := by
          apply hom_ext
          · simp only [lift_fst, whiskerRight_fst, hfg]
            rfl
          · simp only [lift_snd, whiskerRight_snd]
            rfl
        have eR : lift f (lift g h ≫ stabilizerMul G) =
            (α_ H H H).hom ≫ H ◁ stabilizerMul G := by
          apply hom_ext
          · simp only [lift_fst, Category.assoc, whiskerLeft_fst,
              associator_hom_fst]
            rfl
          · simp only [lift_snd, Category.assoc, whiskerLeft_snd, hgh]
        apply stabilizerArrowHom_injective G
        simpa only [eL, eR, Category.assoc, H] using
          stabilizerArrowHom_mul_assoc G f g h
      left_inv := by
        apply stabilizerArrowHom_injective G
        rw [stabilizerArrowHom_mul]
        let f := stabilizerArrowHom G (𝟙 (stabilizer G))
        have hi : stabilizerArrowHom G (stabilizerInv G) = f ≫ G.inverse := by
          simpa only [Category.id_comp] using stabilizerArrowHom_inv G (𝟙 (stabilizer G))
        have hu : stabilizerArrowHom G (toUnit (stabilizer G) ≫ stabilizerOne G) =
            f ≫ G.source ≫ G.identity := by
          rw [stabilizerArrowHom_stabilizerOne]
          simpa only [Category.assoc] using
            congrArg (fun z => z ≫ G.identity)
              (stabilizerArrowHom_source G (𝟙 (stabilizer G))).symm
        simpa only [GroupoidScheme.compose, hi, hu, f] using
          (G.left_inverse _ (stabilizerArrowHom G (𝟙 (stabilizer G))) (by
            simp only [Category.assoc, G.source_inverse]))
      right_inv := by
        apply stabilizerArrowHom_injective G
        rw [stabilizerArrowHom_mul]
        let f := stabilizerArrowHom G (𝟙 (stabilizer G))
        have hi : stabilizerArrowHom G (stabilizerInv G) = f ≫ G.inverse := by
          simpa only [Category.id_comp] using stabilizerArrowHom_inv G (𝟙 (stabilizer G))
        have hu : stabilizerArrowHom G (toUnit (stabilizer G) ≫ stabilizerOne G) =
            f ≫ G.target ≫ G.identity := by
          rw [stabilizerArrowHom_stabilizerOne]
          simpa only [Category.assoc] using
            congrArg (fun z => z ≫ G.identity)
              (stabilizerArrowHom_target G (𝟙 (stabilizer G))).symm
        simpa only [GroupoidScheme.compose, hi, hu, f] using
          (G.right_inverse _ (stabilizerArrowHom G (𝟙 (stabilizer G))) (by
            simp only [Category.assoc, G.target_inverse])) }
  exact ⟨h, by
    let _ := h
    intro T f g
    exact stabilizerArrowHom_mul G f g⟩

/-- The canonical group-object structure on the stabilizer. -/
noncomputable instance {S : Scheme.{u}} (G : GroupoidScheme S) :
    GrpObj (stabilizer G) :=
  (stabilizerGroupStructure G).1

/-- Multiplication in the stabilizer is composition in the groupoid. -/
lemma stabilizer_mul_comp_arrow {S : Scheme.{u}} (G : GroupoidScheme S)
    (T : Over G.objects.left) (f g : T ⟶ stabilizer G) :
    stabilizerArrowHom G (lift f g ≫ μ[stabilizer G]) =
      G.compose (stabilizerArrowHom G f) (stabilizerArrowHom G g)
        (stabilizerArrowHom_composable G f g) :=
  (stabilizerGroupStructure G).2 T f g

end AlgebraicGeometry

end
