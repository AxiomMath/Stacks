module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.LargestTargetOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantSubscheme.Basic
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Properties.InvariantLargestOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.GroupoidInverse
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Action

/-!
# Invariance of the largest open on which the stabilizer has a target-local property

Let `G` be a groupoid scheme whose source and target maps are both coverings for one of the
fppf, syntomic, smooth or étale topologies, and let `P` be a property of morphisms of schemes
which is local on the target for that topology. Then the largest open of the object scheme over
which the stabilizer group scheme has `P` is invariant under the arrows of `G`.

## Main results

* `AlgebraicGeometry.isInvariantOpen_largestTargetOpen_stabilizer`: **Stacks 06QQ**.

## Implementation notes

The largest open is `AlgebraicGeometry.largestTargetOpen` applied to the structure morphism of
`AlgebraicGeometry.stabilizer`, and the four topologies are named uniformly by
`AlgebraicGeometry.IsDescentMorphismClass`. Each covering is a one-member family, represented by
`CategoryTheory.Presieve.ofArrows` on `Unit`.

The proof runs the conjugation `(g, r) ↦ (r, r⁻¹ ∘ g ∘ r)` on generalized points. It is an
isomorphism from the base change of the stabilizer along the target map to its base change along
the source map, commuting with the projection to the arrow scheme, so the two inverse images of
the largest open agree; that is exactly invariance. Conjugation is assembled from
`Stacks.Groupoids.GroupoidScheme.compose`, and that conjugating by `r⁻¹` undoes it is checked in
the groupoid `Stacks.Groupoids.GroupoidScheme.evaluationGroupoid` of generalized points, where
it is the corresponding identity of a groupoid.

## References

* [Stacks Project, Tag 06QQ](https://stacks.math.columbia.edu/tag/06QQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- Conjugating an endomorphism of a groupoid by an arrow and then by its inverse returns the
original endomorphism. -/
private theorem conjugate_inv_conjugate {C : Type*} [Groupoid C] {x y : C} (r : x ⟶ y)
    (g : y ⟶ y) :
    Groupoid.inv r ≫ (r ≫ g ≫ Groupoid.inv r) ≫ Groupoid.inv (Groupoid.inv r) = g := by
  simp only [Groupoid.inv_eq_inv, IsIso.inv_inv]
  simp [Category.assoc]

/-- The inverse morphism of a groupoid scheme is an involution, read on underlying schemes. -/
private theorem comp_inverse_left_comp_inverse_left {S : Scheme.{u}} (G : GroupoidScheme S)
    {X : Scheme.{u}} (f : X ⟶ G.arrows.left) :
    (f ≫ G.inverse.left) ≫ G.inverse.left = f := by
  rw [Category.assoc, ← Over.comp_left, groupoidInverse_involutive G, Over.id_left,
    Category.comp_id]

/-- The target of the inverse is the source, read on underlying schemes. -/
private theorem inverse_left_comp_target_left {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.inverse.left ≫ G.target.left = G.source.left :=
  congrArg Over.Hom.left G.target_inverse

/-- The source of the inverse is the target, read on underlying schemes. -/
private theorem inverse_left_comp_source_left {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.inverse.left ≫ G.source.left = G.target.left :=
  congrArg Over.Hom.left G.source_inverse

/-- The source of a generalized arrow lying over the target has the same image in `S` as the
test object. -/
private theorem comp_source_left_comp_objects_hom {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (r : T ⟶ arrowsOverTarget G) :
    (r.left ≫ G.source.left) ≫ G.objects.hom = T.hom ≫ G.objects.hom :=
  calc
    (r.left ≫ G.source.left) ≫ G.objects.hom = r.left ≫ G.arrows.hom := by
      rw [Category.assoc, G.source.w]
    _ = (r.left ≫ G.target.left) ≫ G.objects.hom := by
      rw [Category.assoc, G.target.w]
    _ = T.hom ≫ G.objects.hom := congrArg (fun f => f ≫ G.objects.hom) r.w

/-- The inverse of a generalized arrow lying over the target has source the test object. -/
private theorem comp_inverse_left_comp_source_left {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (r : T ⟶ arrowsOverTarget G) :
    (r.left ≫ G.inverse.left) ≫ G.source.left = T.hom := by
  rw [Category.assoc, inverse_left_comp_source_left]
  exact r.w

/-- The generalized arrow underlying a composite in the groupoid of generalized points. -/
private theorem evaluationHom_comp_arrow {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    {x y z : G.Evaluation T} (f : G.EvaluationHom x y) (g : G.EvaluationHom y z) :
    ((G.evaluationGroupoid T).comp f g).arrow =
      G.compose g.arrow f.arrow (g.source_eq.trans f.target_eq.symm) := rfl

/-- The conjugate `r⁻¹ ∘ g ∘ r` of a generalized arrow `g` by a generalized arrow `r`. -/
private noncomputable def groupoidConjugate {S : Scheme.{u}} {T : Over S}
    (G : GroupoidScheme S) (r g : T ⟶ G.arrows) (w : g ≫ G.source = r ≫ G.target)
    (w' : (r ≫ G.inverse) ≫ G.source = G.compose g r w ≫ G.target) :
    T ⟶ G.arrows :=
  G.compose (r ≫ G.inverse) (G.compose g r w) w'

/-- The conjugate of a generalized arrow may equally be bracketed as `(r⁻¹ ∘ g) ∘ r`. -/
private theorem groupoidConjugate_assoc {S : Scheme.{u}} {T : Over S} (G : GroupoidScheme S)
    (r g : T ⟶ G.arrows) (wfg : (r ≫ G.inverse) ≫ G.source = g ≫ G.target)
    (wgh : g ≫ G.source = r ≫ G.target) :
    G.compose (G.compose (r ≫ G.inverse) g wfg) r
        (by rw [groupoidCompose_source]; exact wgh) =
      groupoidConjugate G r g wgh (by rw [groupoidCompose_target]; exact wfg) :=
  G.assoc T (r ≫ G.inverse) g r wfg wgh
    (by change G.compose (r ≫ G.inverse) g wfg ≫ G.source = _
        rwa [groupoidCompose_source])
    (by change (r ≫ G.inverse) ≫ G.source = G.compose g r wgh ≫ G.target
        rwa [groupoidCompose_target])

/-- In the groupoid of generalized points, the arrow of a conjugate is the conjugate of the
arrows. -/
private theorem evaluationHom_conj_arrow {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    {x y : G.Evaluation T} (a : x ⟶ y) (b : y ⟶ y) :
    (a ≫ b ≫ Groupoid.inv a).arrow =
      groupoidConjugate G a.arrow b.arrow (b.source_eq.trans a.target_eq.symm) (by
        rw [groupoidCompose_target, Category.assoc, G.source_inverse, a.target_eq,
          b.target_eq]) :=
  groupoidConjugate_assoc G a.arrow b.arrow
    (by rw [Category.assoc, G.source_inverse, a.target_eq, b.target_eq])
    (b.source_eq.trans a.target_eq.symm)

/-- In the groupoid of generalized points, conjugating `b` by `a` and then by an inverse of `a`
returns the arrow of `b`. -/
private theorem evaluationHom_conjugate_conjugate {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} {x y : G.Evaluation T} (a : x ⟶ y) (a' : y ⟶ x) (b c : y ⟶ y) (h : x ⟶ x)
    (ha : a'.arrow = a.arrow ≫ G.inverse) (hh : h.arrow = (a ≫ b ≫ Groupoid.inv a).arrow)
    (hc : c.arrow = (a' ≫ h ≫ Groupoid.inv a').arrow) : c.arrow = b.arrow := by
  obtain rfl : a' = Groupoid.inv a := GroupoidScheme.EvaluationHom.ext ha
  obtain rfl : h = a ≫ b ≫ Groupoid.inv a := GroupoidScheme.EvaluationHom.ext hh
  exact hc.trans (congrArg GroupoidScheme.EvaluationHom.arrow (conjugate_inv_conjugate a b))

/-- Conjugation of generalized arrows commutes with precomposition in the test object. -/
private theorem groupoidConjugate_pre {S : Scheme.{u}} (G : GroupoidScheme S) {T U : Over S}
    (k : T ⟶ U) (r g : U ⟶ G.arrows) (w : g ≫ G.source = r ≫ G.target)
    (w' : (r ≫ G.inverse) ≫ G.source = G.compose g r w ≫ G.target) :
    k ≫ groupoidConjugate G r g w w' =
      groupoidConjugate G (k ≫ r) (k ≫ g)
        (by simpa only [Category.assoc] using congrArg (fun f => k ≫ f) w)
        (by
          simpa only [Category.assoc, ← groupoidCompose_pre G k g r w] using
            congrArg (fun f => k ≫ f) w') := by
  unfold groupoidConjugate
  calc
    k ≫ G.compose (r ≫ G.inverse) (G.compose g r w) w' =
        G.compose (k ≫ (r ≫ G.inverse)) (k ≫ G.compose g r w) _ :=
          groupoidCompose_pre G k (r ≫ G.inverse) (G.compose g r w) w'
    _ = G.compose ((k ≫ r) ≫ G.inverse) (G.compose (k ≫ g) (k ≫ r) _) _ := by
        simp only [Category.assoc, groupoidCompose_pre G k g r w]

/-- The generalized arrow `r⁻¹ ∘ g ∘ r` obtained by conjugating a generalized point `g` of the
stabilizer by a generalized arrow `r` lying over the target. -/
private noncomputable def conjugateStabilizerArrow {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (r : T ⟶ arrowsOverTarget G) (g : T ⟶ stabilizer G) :
    (Over.map G.objects.hom).obj T ⟶ G.arrows := by
  let r' := arrowOverTargetHom G r
  let g' := stabilizerArrowHom G g
  let w : g' ≫ G.source = r' ≫ G.target :=
    stabilizerArrowHom_arrowOverTarget_composable G g r
  let a := G.compose g' r' w
  let w' : (r' ≫ G.inverse) ≫ G.source = a ≫ G.target := by
    calc
      (r' ≫ G.inverse) ≫ G.source = r' ≫ G.target := by
        simp [Category.assoc, G.source_inverse]
      _ = g' ≫ G.target :=
        (arrowOverTargetHom_target G r).trans (stabilizerArrowHom_target G g).symm
      _ = a ≫ G.target := (groupoidCompose_target G g' r' w).symm
  exact groupoidConjugate G r' g' w w'

/-- The conjugate generalized arrow is natural in the test object. -/
private theorem conjugateStabilizerArrow_pre {S : Scheme.{u}} (G : GroupoidScheme S)
    {T U : Over G.objects.left} (k : T ⟶ U) (r : U ⟶ arrowsOverTarget G)
    (g : U ⟶ stabilizer G) :
    (Over.map G.objects.hom).map k ≫ conjugateStabilizerArrow G r g =
      conjugateStabilizerArrow G (k ≫ r) (k ≫ g) := by
  let k' := (Over.map G.objects.hom).map k
  have hr : k' ≫ arrowOverTargetHom G r = arrowOverTargetHom G (k ≫ r) :=
    Over.OverMorphism.ext rfl
  have hg : k' ≫ stabilizerArrowHom G g = stabilizerArrowHom G (k ≫ g) :=
    Over.OverMorphism.ext rfl
  dsimp only [conjugateStabilizerArrow]
  rw [groupoidConjugate_pre G k']
  simp only [hr, hg]

/-- The conjugate generalized arrow has the source of `r` as its source. -/
private theorem conjugateStabilizerArrow_source {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (r : T ⟶ arrowsOverTarget G) (g : T ⟶ stabilizer G) :
    conjugateStabilizerArrow G r g ≫ G.source = arrowOverTargetHom G r ≫ G.source := by
  simp [conjugateStabilizerArrow, groupoidConjugate, groupoidCompose_source]

/-- The conjugate generalized arrow has the source of `r` as its target, so it is again a
generalized point of the stabilizer. -/
private theorem conjugateStabilizerArrow_target {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (r : T ⟶ arrowsOverTarget G) (g : T ⟶ stabilizer G) :
    conjugateStabilizerArrow G r g ≫ G.target = arrowOverTargetHom G r ≫ G.source := by
  simp [conjugateStabilizerArrow, groupoidConjugate, groupoidCompose_target, Category.assoc,
    G.target_inverse]

/-- The conjugate `r⁻¹ ∘ g ∘ r` of a generalized point of the stabilizer, as a generalized point
of the stabilizer over the source of `r`. -/
private noncomputable def conjugateStabilizer {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (r : T ⟶ arrowsOverTarget G) (g : T ⟶ stabilizer G) :
    Over.mk (r.left ≫ G.source.left) ⟶ stabilizer G := by
  let Tsrc : Over G.objects.left := Over.mk (r.left ≫ G.source.left)
  let x : (Over.map G.objects.hom).obj T ⟶ G.objects :=
    Over.homMk Tsrc.hom (comp_source_left_comp_objects_hom G r)
  have hs : conjugateStabilizerArrow G r g ≫ G.source = x := by
    rw [conjugateStabilizerArrow_source]
    exact Over.OverMorphism.ext rfl
  have ht : conjugateStabilizerArrow G r g ≫ G.target = x := by
    rw [conjugateStabilizerArrow_target]
    exact Over.OverMorphism.ext rfl
  have hp : conjugateStabilizerArrow G r g ≫ sourceTarget G = x ≫ diagonal G := by
    change conjugateStabilizerArrow G r g ≫
        CartesianMonoidalCategory.lift G.target G.source =
      x ≫ CartesianMonoidalCategory.lift (𝟙 G.objects) (𝟙 G.objects)
    apply CartesianMonoidalCategory.hom_ext <;> simp [hs, ht]
  let q := pullback.lift (conjugateStabilizerArrow G r g) x hp
  exact Over.homMk q.left (by
    change q.left ≫ (pullback.snd (sourceTarget G) (diagonal G)).left = Tsrc.hom
    exact (congrArg Over.Hom.left
      (pullback.lift_snd (conjugateStabilizerArrow G r g) x hp)).trans rfl)

/-- The generalized arrow attached to the conjugate of a generalized point of the stabilizer is
the conjugate generalized arrow. -/
private theorem stabilizerArrowHom_conjugateStabilizer {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (r : T ⟶ arrowsOverTarget G) (g : T ⟶ stabilizer G) :
    (stabilizerArrowHom G (conjugateStabilizer G r g)).left =
      (conjugateStabilizerArrow G r g).left := by
  change (conjugateStabilizer G r g).left ≫ stabilizerArrow G =
    (conjugateStabilizerArrow G r g).left
  unfold conjugateStabilizer
  change (pullback.lift (conjugateStabilizerArrow G r g) _ _).left ≫
      (pullback.fst (sourceTarget G) (diagonal G)).left =
    (conjugateStabilizerArrow G r g).left
  exact congrArg Over.Hom.left (pullback.lift_fst _ _ _)

/-- Conjugation of generalized points of the stabilizer is natural in the test object. -/
private theorem conjugateStabilizer_pre {S : Scheme.{u}} (G : GroupoidScheme S)
    {T U : Over G.objects.left} (k : T ⟶ U) (r : U ⟶ arrowsOverTarget G)
    (g : U ⟶ stabilizer G) :
    let Tsrc : Over G.objects.left := Over.mk ((k ≫ r).left ≫ G.source.left)
    let Usrc : Over G.objects.left := Over.mk (r.left ≫ G.source.left)
    let ksrc : Tsrc ⟶ Usrc := Over.homMk k.left (by
      change (k.left ≫ r.left) ≫ G.source.left = k.left ≫ (r.left ≫ G.source.left)
      exact Category.assoc _ _ _)
    ksrc ≫ conjugateStabilizer G r g = conjugateStabilizer G (k ≫ r) (k ≫ g) := by
  dsimp only
  apply stabilizerArrowHom_injective G
  apply Over.OverMorphism.ext
  change (k.left ≫ (conjugateStabilizer G r g).left) ≫ stabilizerArrow G =
    (conjugateStabilizer G (k ≫ r) (k ≫ g)).left ≫ stabilizerArrow G
  calc
    _ = k.left ≫ (conjugateStabilizerArrow G r g).left := by
      have h := stabilizerArrowHom_conjugateStabilizer G r g
      change (conjugateStabilizer G r g).left ≫ stabilizerArrow G = _ at h
      simpa only [Category.assoc] using congrArg (fun f => k.left ≫ f) h
    _ = (conjugateStabilizerArrow G (k ≫ r) (k ≫ g)).left :=
      congrArg Over.Hom.left (conjugateStabilizerArrow_pre G k r g)
    _ = _ := (stabilizerArrowHom_conjugateStabilizer G (k ≫ r) (k ≫ g)).symm

/-- Conjugation depends only on the underlying morphisms of schemes of its two arguments. -/
private theorem conjugateStabilizer_left_congr {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} {r r' : T ⟶ arrowsOverTarget G} {g g' : T ⟶ stabilizer G}
    (hr : r.left = r'.left) (hg : g.left = g'.left) :
    (conjugateStabilizer G r g).left = (conjugateStabilizer G r' g').left := by
  obtain rfl : r = r' := Over.OverMorphism.ext hr
  obtain rfl : g = g' := Over.OverMorphism.ext hg
  rfl

/-- The inverse of a generalized arrow lying over the target, as a generalized arrow over the
target based at the source of the original one. -/
private noncomputable def inverseOverTarget {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (r : T ⟶ arrowsOverTarget G) :
    Over.mk (r.left ≫ G.source.left) ⟶ arrowsOverTarget G :=
  Over.homMk (r.left ≫ G.inverse.left) (by
    change (r.left ≫ G.inverse.left) ≫ G.target.left = r.left ≫ G.source.left
    rw [Category.assoc, inverse_left_comp_target_left])

/-- Conjugating by `r` and then by `r⁻¹` returns the original generalized point of the
stabilizer. -/
private theorem conjugateStabilizer_roundtrip {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over G.objects.left} (r : T ⟶ arrowsOverTarget G) (g : T ⟶ stabilizer G) :
    let Tsrc : Over G.objects.left := Over.mk (r.left ≫ G.source.left)
    let rInv : Tsrc ⟶ arrowsOverTarget G := inverseOverTarget G r
    (conjugateStabilizer G rInv (conjugateStabilizer G r g)).left = g.left := by
  let Tsrc : Over G.objects.left := Over.mk (r.left ≫ G.source.left)
  let rInv : Tsrc ⟶ arrowsOverTarget G := inverseOverTarget G r
  let g1 := conjugateStabilizer G r g
  let g2 := conjugateStabilizer G rInv g1
  let g2T : T ⟶ stabilizer G :=
    Over.homMk g2.left (g2.w.trans (comp_inverse_left_comp_source_left G r))
  have hbase := comp_source_left_comp_objects_hom G r
  let D := (Over.map G.objects.hom).obj Tsrc
  let k : D ⟶ (Over.map G.objects.hom).obj T := Over.homMk (𝟙 T.left) hbase.symm
  let x : G.Evaluation D := Over.homMk Tsrc.hom
  let y : G.Evaluation D := Over.homMk T.hom hbase.symm
  let rH : x ⟶ y :=
    ⟨k ≫ arrowOverTargetHom G r, Over.OverMorphism.ext rfl, Over.OverMorphism.ext r.w⟩
  let pointH : (T ⟶ stabilizer G) → (y ⟶ y) := fun p => ⟨k ≫ stabilizerArrowHom G p,
    by rw [Category.assoc, stabilizerArrowHom_source]; exact Over.OverMorphism.ext rfl,
    by rw [Category.assoc, stabilizerArrowHom_target]; exact Over.OverMorphism.ext rfl⟩
  let gH : y ⟶ y := pointH g
  let riH : y ⟶ x := ⟨arrowOverTargetHom G rInv,
    Over.OverMorphism.ext (comp_inverse_left_comp_source_left G r),
    Over.OverMorphism.ext (congrArg Over.Hom.left (arrowOverTargetHom_target G rInv))⟩
  let hH : x ⟶ x := ⟨stabilizerArrowHom G g1,
    Over.OverMorphism.ext (congrArg Over.Hom.left (stabilizerArrowHom_source G g1)),
    Over.OverMorphism.ext (congrArg Over.Hom.left (stabilizerArrowHom_target G g1))⟩
  let g2H : y ⟶ y := pointH g2T
  have hh : hH.arrow = (rH ≫ gH ≫ Groupoid.inv rH).arrow := by
    rw [evaluationHom_conj_arrow]
    calc
      hH.arrow = k ≫ conjugateStabilizerArrow G r g := by
        apply Over.OverMorphism.ext
        change (stabilizerArrowHom G g1).left = (k ≫ conjugateStabilizerArrow G r g).left
        rw [stabilizerArrowHom_conjugateStabilizer]
        rfl
      _ = _ := groupoidConjugate_pre G k _ _ _ _
  have hc : g2H.arrow = (riH ≫ hH ≫ Groupoid.inv riH).arrow := by
    rw [evaluationHom_conj_arrow]
    apply Over.OverMorphism.ext
    change (conjugateStabilizer G rInv g1).left ≫ stabilizerArrow G =
      (conjugateStabilizerArrow G rInv g1).left
    exact stabilizerArrowHom_conjugateStabilizer G rInv g1
  have hst : stabilizerArrowHom G g2T = stabilizerArrowHom G g := by
    have : IsIso k := ⟨⟨Over.homMk (𝟙 T.left) hbase, Over.OverMorphism.ext rfl,
      Over.OverMorphism.ext rfl⟩⟩
    exact (cancel_epi k).mp (evaluationHom_conjugate_conjugate G rH riH gH g2H hH rfl hh hc)
  exact congrArg Over.Hom.left (stabilizerArrowHom_injective G hst)

/-- If `k` carries `r₂` to `r⁻¹` and `g₂` to the conjugate of `g` by `r`, then conjugating `g₂`
by `r₂` recovers `g` along `k`. -/
private theorem conjugateStabilizer_roundtrip_of_comp {S : Scheme.{u}} (G : GroupoidScheme S)
    {T U : Over G.objects.left} (r : T ⟶ arrowsOverTarget G) (g : T ⟶ stabilizer G)
    (k : Over.mk (r.left ≫ G.source.left) ⟶ U) (r₂ : U ⟶ arrowsOverTarget G)
    (g₂ : U ⟶ stabilizer G) (hr : k ≫ r₂ = inverseOverTarget G r)
    (hg : k ≫ g₂ = conjugateStabilizer G r g) :
    k.left ≫ (conjugateStabilizer G r₂ g₂).left = g.left := by
  have hround := conjugateStabilizer_roundtrip G r g
  dsimp only at hround
  exact (congrArg Over.Hom.left (conjugateStabilizer_pre G k r₂ g₂)).trans
    ((conjugateStabilizer_left_congr G
      (congrArg Over.Hom.left hr) (congrArg Over.Hom.left hg)).trans hround)

/-- The tautological generalized arrow over the target on the base change of the stabilizer
along the target map. -/
private noncomputable def targetPullbackArrow {S : Scheme.{u}} (G : GroupoidScheme S) :
    Over.mk (pullback.snd (stabilizer G).hom G.target.left ≫ G.target.left) ⟶
      arrowsOverTarget G :=
  Over.homMk (pullback.snd (stabilizer G).hom G.target.left)

/-- The tautological generalized point of the stabilizer on its base change along the target
map. -/
private noncomputable def targetPullbackPoint {S : Scheme.{u}} (G : GroupoidScheme S) :
    Over.mk (pullback.snd (stabilizer G).hom G.target.left ≫ G.target.left) ⟶ stabilizer G :=
  Over.homMk (pullback.fst (stabilizer G).hom G.target.left) pullback.condition

/-- The inverse of the tautological generalized arrow on the base change of the stabilizer along
the source map, as a generalized arrow over the target. -/
private noncomputable def sourcePullbackArrow {S : Scheme.{u}} (G : GroupoidScheme S) :
    Over.mk (pullback.snd (stabilizer G).hom G.source.left ≫ G.source.left) ⟶
      arrowsOverTarget G :=
  Over.homMk (pullback.snd (stabilizer G).hom G.source.left ≫ G.inverse.left) (by
    change (pullback.snd (stabilizer G).hom G.source.left ≫ G.inverse.left) ≫
        G.target.left = pullback.snd (stabilizer G).hom G.source.left ≫ G.source.left
    rw [Category.assoc, inverse_left_comp_target_left])

/-- The tautological generalized point of the stabilizer on its base change along the source
map. -/
private noncomputable def sourcePullbackPoint {S : Scheme.{u}} (G : GroupoidScheme S) :
    Over.mk (pullback.snd (stabilizer G).hom G.source.left ≫ G.source.left) ⟶ stabilizer G :=
  Over.homMk (pullback.fst (stabilizer G).hom G.source.left) pullback.condition

/-- Conjugation as a morphism from the base change of the stabilizer along the target map to its
base change along the source map. -/
private noncomputable def stabilizerPullbackConjugation {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback (stabilizer G).hom G.target.left ⟶ pullback (stabilizer G).hom G.source.left :=
  pullback.lift (conjugateStabilizer G (targetPullbackArrow G) (targetPullbackPoint G)).left
    (pullback.snd (stabilizer G).hom G.target.left)
    (conjugateStabilizer G (targetPullbackArrow G) (targetPullbackPoint G)).w

/-- Conjugation by the inverse, as a morphism from the base change of the stabilizer along the
source map to its base change along the target map. -/
private noncomputable def stabilizerPullbackUnconjugation {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    pullback (stabilizer G).hom G.source.left ⟶ pullback (stabilizer G).hom G.target.left :=
  pullback.lift (conjugateStabilizer G (sourcePullbackArrow G) (sourcePullbackPoint G)).left
    (pullback.snd (stabilizer G).hom G.source.left)
    (by
      refine (conjugateStabilizer G (sourcePullbackArrow G) (sourcePullbackPoint G)).w.trans ?_
      change (pullback.snd (stabilizer G).hom G.source.left ≫ G.inverse.left) ≫
        G.source.left = _
      rw [Category.assoc, inverse_left_comp_source_left])

/-- Conjugation acts on the stabilizer factor by conjugating. -/
private theorem stabilizerPullbackConjugation_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    stabilizerPullbackConjugation G ≫ pullback.fst (stabilizer G).hom G.source.left =
      (conjugateStabilizer G (targetPullbackArrow G) (targetPullbackPoint G)).left :=
  pullback.lift_fst _ _ _

/-- Conjugation does not change the arrow factor. -/
private theorem stabilizerPullbackConjugation_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    stabilizerPullbackConjugation G ≫ pullback.snd (stabilizer G).hom G.source.left =
      pullback.snd (stabilizer G).hom G.target.left :=
  pullback.lift_snd _ _ _

/-- Unconjugation acts on the stabilizer factor by conjugating by the inverse. -/
private theorem stabilizerPullbackUnconjugation_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    stabilizerPullbackUnconjugation G ≫ pullback.fst (stabilizer G).hom G.target.left =
      (conjugateStabilizer G (sourcePullbackArrow G) (sourcePullbackPoint G)).left :=
  pullback.lift_fst _ _ _

/-- Unconjugation does not change the arrow factor. -/
private theorem stabilizerPullbackUnconjugation_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    stabilizerPullbackUnconjugation G ≫ pullback.snd (stabilizer G).hom G.target.left =
      pullback.snd (stabilizer G).hom G.source.left :=
  pullback.lift_snd _ _ _

/-- Unconjugation undoes conjugation on the stabilizer factor. -/
private theorem stabilizerPullbackConjugation_comp_unconjugation_fst {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    (stabilizerPullbackConjugation G ≫ stabilizerPullbackUnconjugation G) ≫
        pullback.fst (stabilizer G).hom G.target.left =
      𝟙 _ ≫ pullback.fst (stabilizer G).hom G.target.left := by
  rw [Category.assoc, stabilizerPullbackUnconjugation_fst]
  have hkSnd := stabilizerPullbackConjugation_snd G
  let k : Over.mk ((targetPullbackArrow G).left ≫ G.source.left) ⟶
      Over.mk (pullback.snd (stabilizer G).hom G.source.left ≫ G.source.left) :=
    Over.homMk (stabilizerPullbackConjugation G) (by
      change stabilizerPullbackConjugation G ≫
          pullback.snd (stabilizer G).hom G.source.left ≫ G.source.left =
        pullback.snd (stabilizer G).hom G.target.left ≫ G.source.left
      rw [← Category.assoc, hkSnd])
  have hr : k ≫ sourcePullbackArrow G = inverseOverTarget G (targetPullbackArrow G) := by
    apply Over.OverMorphism.ext
    change stabilizerPullbackConjugation G ≫
        pullback.snd (stabilizer G).hom G.source.left ≫ G.inverse.left =
      pullback.snd (stabilizer G).hom G.target.left ≫ G.inverse.left
    rw [← Category.assoc, hkSnd]
  have hg : k ≫ sourcePullbackPoint G =
      conjugateStabilizer G (targetPullbackArrow G) (targetPullbackPoint G) :=
    Over.OverMorphism.ext (stabilizerPullbackConjugation_fst G)
  exact conjugateStabilizer_roundtrip_of_comp G _ _ k _ _ hr hg

/-- Conjugation undoes unconjugation on the stabilizer factor. -/
private theorem stabilizerPullbackUnconjugation_comp_conjugation_fst {S : Scheme.{u}}
    (G : GroupoidScheme S) :
    (stabilizerPullbackUnconjugation G ≫ stabilizerPullbackConjugation G) ≫
        pullback.fst (stabilizer G).hom G.source.left =
      𝟙 _ ≫ pullback.fst (stabilizer G).hom G.source.left := by
  rw [Category.assoc, stabilizerPullbackConjugation_fst]
  have hkSnd := stabilizerPullbackUnconjugation_snd G
  let k : Over.mk ((sourcePullbackArrow G).left ≫ G.source.left) ⟶
      Over.mk (pullback.snd (stabilizer G).hom G.target.left ≫ G.target.left) :=
    Over.homMk (stabilizerPullbackUnconjugation G) (by
      change stabilizerPullbackUnconjugation G ≫
          pullback.snd (stabilizer G).hom G.target.left ≫ G.target.left =
        (pullback.snd (stabilizer G).hom G.source.left ≫ G.inverse.left) ≫ G.source.left
      rw [← Category.assoc, hkSnd, Category.assoc, inverse_left_comp_source_left])
  have hr : k ≫ targetPullbackArrow G = inverseOverTarget G (sourcePullbackArrow G) := by
    apply Over.OverMorphism.ext
    change stabilizerPullbackUnconjugation G ≫ pullback.snd (stabilizer G).hom G.target.left =
      (pullback.snd (stabilizer G).hom G.source.left ≫ G.inverse.left) ≫ G.inverse.left
    rw [hkSnd, comp_inverse_left_comp_inverse_left]
  have hg : k ≫ targetPullbackPoint G =
      conjugateStabilizer G (sourcePullbackArrow G) (sourcePullbackPoint G) :=
    Over.OverMorphism.ext (stabilizerPullbackUnconjugation_fst G)
  exact conjugateStabilizer_roundtrip_of_comp G _ _ k _ _ hr hg

/-- Conjugation identifies the base change of the stabilizer along the target map with its base
change along the source map, compatibly with the projection to the arrow scheme. -/
private noncomputable def stabilizerPullbackIso {S : Scheme.{u}} (G : GroupoidScheme S) :
    pullback (stabilizer G).hom G.target.left ≅ pullback (stabilizer G).hom G.source.left where
  hom := stabilizerPullbackConjugation G
  inv := stabilizerPullbackUnconjugation G
  hom_inv_id := by
    apply pullback.hom_ext
    · exact stabilizerPullbackConjugation_comp_unconjugation_fst G
    · rw [Category.assoc, stabilizerPullbackUnconjugation_snd, stabilizerPullbackConjugation_snd,
        Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · exact stabilizerPullbackUnconjugation_comp_conjugation_fst G
    · rw [Category.assoc, stabilizerPullbackConjugation_snd, stabilizerPullbackUnconjugation_snd,
        Category.id_comp]

/-- The two base changes of the stabilizer, along the target map and along the source map, have
the same largest open. -/
private theorem largestTargetOpen_stabilizer_pullback (P : MorphismProperty Scheme.{u})
    [P.RespectsIso] {S : Scheme.{u}} (G : GroupoidScheme S) :
    largestTargetOpen P (pullback.snd (stabilizer G).hom G.target.left) =
      largestTargetOpen P (pullback.snd (stabilizer G).hom G.source.left) := by
  rw [← show (stabilizerPullbackIso G).hom ≫
      pullback.snd (stabilizer G).hom G.source.left =
      pullback.snd (stabilizer G).hom G.target.left from stabilizerPullbackConjugation_snd G]
  exact largestTargetOpen_precomp_iso P (stabilizerPullbackIso G)
    (pullback.snd (stabilizer G).hom G.source.left)

/-- **Stacks Project, Tag 06QQ.** For a groupoid scheme whose source and target maps are
coverings for one of the fppf, syntomic, smooth or étale topologies, the largest open of the
object scheme over which the stabilizer group scheme has a target-local property is
invariant. -/
@[stacks 06QQ]
theorem isInvariantOpen_largestTargetOpen_stabilizer {S : Scheme.{u}} (G : GroupoidScheme S)
    (P Q : MorphismProperty Scheme.{u}) (hQ : IsDescentMorphismClass Q)
    [P.IsLocalAtTarget (Scheme.precoverage Q)]
    (hs : Presieve.ofArrows (fun _ : Unit => G.arrows.left)
      (fun _ => G.source.left) ∈ Scheme.precoverage Q G.objects.left)
    (ht : Presieve.ofArrows (fun _ : Unit => G.arrows.left)
      (fun _ => G.target.left) ∈ Scheme.precoverage Q G.objects.left) :
    IsInvariantOpen G (largestTargetOpen P (stabilizer G).hom) := by
  rw [Scheme.ofArrows_mem_precoverage_iff] at hs ht
  have hpre : G.target.left ⁻¹ᵁ largestTargetOpen P (stabilizer G).hom =
      G.source.left ⁻¹ᵁ largestTargetOpen P (stabilizer G).hom := by
    rw [← largestTargetOpen_baseChange P Q hQ _ _ (ht.2 ()),
      ← largestTargetOpen_baseChange P Q hQ _ _ (hs.2 ())]
    exact largestTargetOpen_stabilizer_pullback P G
  intro r hr
  have hr' : r ∈ G.source.left ⁻¹ᵁ largestTargetOpen P (stabilizer G).hom := by simpa using hr
  rw [← hpre] at hr'
  simpa using hr'

end AlgebraicGeometry

end
