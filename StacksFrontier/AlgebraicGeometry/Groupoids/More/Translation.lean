module

public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksCore.Tactic.StacksAttribute

/-!
# Translation by an arrow in a groupoid scheme

For a groupoid scheme whose object scheme is the spectrum of a field, a point of the arrow
scheme whose source and target maps induce residue-field isomorphisms can be represented by an
arrow family with identity source.  Translation by this family is an automorphism of the arrow
scheme and carries the identity point to the given point.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.leftTranslation` is translation by a family of arrows with
  fixed source section.
* `AlgebraicGeometry.GroupoidScheme.sourceNormalizedArrow` is the arrow family canonically
  attached (up to the specified normalization) to the given point.
* `AlgebraicGeometry.GroupoidScheme.translationByPoint` is the resulting named endomorphism of
  the arrow scheme.

## Main results

* `AlgebraicGeometry.GroupoidScheme.sourceNormalizedArrow_source` and
  `AlgebraicGeometry.GroupoidScheme.sourceNormalizedArrow_apply` characterize the family
  attached to the field-valued point.
* `AlgebraicGeometry.GroupoidScheme.translationByPoint_isIso` says that this endomorphism is an
  automorphism.
* `AlgebraicGeometry.GroupoidScheme.identity_image_translationByPoint` identifies the image of
  the identity point.

## Implementation notes

The hypotheses that the source and target induce isomorphisms from the ground field are
expressed invariantly by requiring their canonical residue-field maps at `r` to be
isomorphisms; when the object scheme is `Spec k`, their domains are canonically `k`.  The
definition `sourceNormalizedArrow` records the representative `a` supplied by the source
residue-field isomorphism, together with both its normalization and the fact that it represents
`r`.  Thus `translationByPoint` names the map attached to `r`, rather than merely asserting
that some suitable map exists.  It is the composite of `a` pulled back along the target map
with the variable arrow, expressed using the pullback which represents composable pairs.  The
final equality states that the identity at the source of `r` is mapped to `r`.

## References

* [Stacks Project, Tag 04LS](https://stacks.math.columbia.edu/tag/04LS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- Left translation on the arrow scheme by a family of arrows whose source is the identity.
On generalized arrows it sends `f` to the composite of `a` over the target of `f` with `f`. -/
public noncomputable def leftTranslation {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : G.objects ⟶ G.arrows) (ha : a ≫ G.source = 𝟙 G.objects) :
    G.arrows ⟶ G.arrows :=
  pullback.lift (G.target ≫ a) (𝟙 G.arrows) (by simp [Category.assoc, ha]) ≫ G.comp

/-- Evaluation of the global sections of the spectrum of a field at a point is an
isomorphism onto the residue field there, because the field has a single prime. -/
private lemma isIso_Γevaluation {k : Type u} [Field k] (x : Spec (.of k)) :
    IsIso ((Spec (.of k)).Γevaluation x) := by
  let p : Ideal k := x.asIdeal
  have : p.IsPrime := x.isPrime
  let e₀ : CommRingCat.of k ≅ CommRingCat.of p.ResidueField :=
    p.algEquivResidueFieldOfField.toRingEquiv.toCommRingCatIso
  let e := e₀ ≪≫ (Scheme.Spec.residueFieldIso (.of k) x).symm
  have he₀ : e₀.hom = CommRingCat.ofHom (algebraMap k p.ResidueField) := by
    ext z
    simp [e₀, Ideal.algEquivResidueFieldOfField_apply]
  have heq : (Spec (.of k)).Γevaluation x = (Scheme.ΓSpecIso (.of k)).hom ≫ e.hom := by
    dsimp [e]
    rw [he₀]
    calc
      (Spec (.of k)).Γevaluation x = (Scheme.ΓSpecIso (.of k)).hom ≫
          ((Scheme.ΓSpecIso (.of k)).inv ≫ (Spec (.of k)).Γevaluation x) := by
            simp
      _ = (Scheme.ΓSpecIso (.of k)).hom ≫
          (CommRingCat.ofHom (algebraMap k x.asIdeal.ResidueField) ≫
            (Scheme.Spec.residueFieldIso (.of k) x).inv) := by
              congr 1
              show (Scheme.ΓSpecIso (.of k)).inv ≫
                  ((Spec (.of k)).presheaf.germ ⊤ x trivial ≫
                    (Spec (.of k)).residue x) = _
              rw [← Scheme.Spec.algebraMap_residueFieldIso_inv]
      _ = (Scheme.ΓSpecIso (.of k)).hom ≫
          (CommRingCat.ofHom (algebraMap k p.ResidueField) ≫
            (Scheme.Spec.residueFieldIso (.of k) x).symm.hom) := by rfl
      _ = (Scheme.ΓSpecIso (.of k)).hom ≫ e.hom := by rfl
  rw [heq]
  infer_instance

/-- The source-normalized family of arrows representing `r`, together with its normalization
and the fact that it represents `r`. -/
public noncomputable def sourceNormalizedArrowData {S : Scheme.{u}} (G : GroupoidScheme S)
    (k : Type u) [Field k] (hU : G.objects.left = Spec (.of k))
    (r : G.arrows.left) [IsIso (G.source.left.residueFieldMap r)] :
    { a : G.objects ⟶ G.arrows //
      a ≫ G.source = 𝟙 G.objects ∧ a.left (G.source.left r) = r } := by
  classical
  let f₀ : G.arrows.left ⟶ Spec (.of k) := G.source.left ≫ eqToHom hU
  let f : G.arrows.left ⟶ Spec (.of k) := f₀.copyBase
    (fun z => (eqToHom hU) (G.source.left z)) (by ext z; rfl)
  have hf : f = f₀ := Scheme.Hom.copyBase_eq f₀ _ _
  let x : Spec (.of k) := f r
  let p : Ideal k := x.asIdeal
  haveI : p.IsPrime := x.isPrime
  let e₀ : CommRingCat.of k ≅ CommRingCat.of p.ResidueField :=
    p.algEquivResidueFieldOfField.toRingEquiv.toCommRingCatIso
  let e : CommRingCat.of k ≅ (Spec (.of k)).residueField x :=
    e₀ ≪≫ (Scheme.Spec.residueFieldIso (.of k) x).symm
  haveI : IsOpenImmersion (eqToHom hU) := inferInstance
  haveI : IsIso ((eqToHom hU).residueFieldMap (G.source.left r)) := by infer_instance
  haveI : IsIso (G.source.left.residueFieldMap r) := inferInstance
  let q : (Spec (.of k)).residueField x ⟶ G.arrows.left.residueField r :=
    f.residueFieldMap r
  haveI : IsIso q := by
    change IsIso (f.residueFieldMap r)
    rw [hf]
    dsimp [f₀]
    rw [Scheme.residueFieldMap_comp]
    exact IsIso.comp_isIso
  let q₀ : CommRingCat.of k ≅ G.arrows.left.residueField r := e ≪≫ asIso q
  let a₀ : Spec (.of k) ⟶ G.arrows.left :=
    Spec.map q₀.inv ≫ G.arrows.left.fromSpecResidueField r
  have ha₀ : a₀ ≫ f = 𝟙 (Spec (.of k)) := by
    have hres : Spec.map q ≫ (Spec (.of k)).fromSpecResidueField x =
        G.arrows.left.fromSpecResidueField r ≫ f :=
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f r
    have hcomp : q ≫ q₀.inv = e.inv := by simp [q₀]
    have he₀ : e₀.hom = CommRingCat.ofHom (algebraMap k p.ResidueField) := by
      ext z
      simp [e₀, Ideal.algEquivResidueFieldOfField_apply]
    have he₀' : e₀.hom = CommRingCat.ofHom (algebraMap k x.asIdeal.ResidueField) := by
      simpa [p] using he₀
    have hfrom : (Spec (.of k)).fromSpecResidueField x = Spec.map e.hom := by
      rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField, ← Spec.map_comp, ← he₀']
      rfl
    change (Spec.map q₀.inv ≫ G.arrows.left.fromSpecResidueField r) ≫ f = _
    rw [Category.assoc, ← hres, ← Spec.map_comp_assoc, hcomp, hfrom, ← Spec.map_comp,
      Iso.hom_inv_id, Spec.map_id]
  have hsec : a₀ ≫ G.source.left = inv (eqToHom hU) :=
    IsIso.eq_inv_of_inv_hom_id (by simpa [hf, f₀, Category.assoc] using ha₀)
  let a : G.objects ⟶ G.arrows := Over.homMk (eqToHom hU ≫ a₀) (by
    rw [← G.source.w, Category.assoc, reassoc_of% hsec, IsIso.hom_inv_id_assoc])
  refine ⟨a, ?_, ?_⟩
  · ext
    change (eqToHom hU ≫ a₀) ≫ G.source.left = 𝟙 _
    simp [Category.assoc, hsec]
  · change a₀ (f r) = r
    rw [Subsingleton.elim (f r) default]
    dsimp [a₀]
    rw [Subsingleton.elim (Spec.map q₀.inv default) default]
    simp

/-- The source-normalized family of arrows representing `r`.  Its existence is the
scheme-theoretic content of the assertion that the source map induces an isomorphism from the
ground field to the residue field at `r`. -/
public noncomputable def sourceNormalizedArrow {S : Scheme.{u}} (G : GroupoidScheme S)
    (k : Type u) [Field k] (hU : G.objects.left = Spec (.of k))
    (r : G.arrows.left) [IsIso (G.source.left.residueFieldMap r)] :
    G.objects ⟶ G.arrows :=
  (sourceNormalizedArrowData G k hU r).1

/-- The source-normalized family of arrows at `r` is a section of the source map. -/
@[reassoc]
public lemma sourceNormalizedArrow_source {S : Scheme.{u}} (G : GroupoidScheme S)
    (k : Type u) [Field k] (hU : G.objects.left = Spec (.of k))
    (r : G.arrows.left) [IsIso (G.source.left.residueFieldMap r)] :
    sourceNormalizedArrow G k hU r ≫ G.source = 𝟙 G.objects :=
  (sourceNormalizedArrowData G k hU r).2.1

/-- The source-normalized family of arrows at `r` sends the source of `r` to `r`. -/
public lemma sourceNormalizedArrow_apply {S : Scheme.{u}} (G : GroupoidScheme S)
    (k : Type u) [Field k] (hU : G.objects.left = Spec (.of k))
    (r : G.arrows.left) [IsIso (G.source.left.residueFieldMap r)] :
    (sourceNormalizedArrow G k hU r).left (G.source.left r) = r :=
  (sourceNormalizedArrowData G k hU r).2.2

/-- An endomorphism of the spectrum of a field which induces an isomorphism on the residue
field at the unique point is an isomorphism. -/
private lemma isIsoSpecFieldHom {k : Type u} [Field k]
    (f : Spec (.of k) ⟶ Spec (.of k))
    (hf : IsIso (f.residueFieldMap (default : Spec (.of k)))) : IsIso f := by
  have := isIso_Γevaluation (f default)
  have := isIso_Γevaluation (default : Spec (.of k))
  have : IsIso (f.appTop ≫ (Spec (.of k)).Γevaluation default) := by
    rw [← Scheme.Γevaluation_naturality]
    infer_instance
  have := IsIso.of_isIso_comp_right f.appTop ((Spec (.of k)).Γevaluation default)
  have : IsIso (f ≫ (Spec (.of k)).isoSpec.hom) := by
    rw [← Scheme.isoSpec_hom_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right f (Spec (.of k)).isoSpec.hom

/-- Transport of the invertibility of a residue-field map along an equality of points. -/
private lemma residueFieldMap_isIso_of_point_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    {x y : X.carrier} (h : x = y) [IsIso (f.residueFieldMap y)] :
    IsIso (f.residueFieldMap x) := by
  subst h
  infer_instance

/-- If `f` is a section of `g` and `g` induces an isomorphism of residue fields at `f x`, then
so does `f` at `x`. -/
private lemma residueFieldMap_rightFactor_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ X) (x : X.carrier) (hfg : f ≫ g = 𝟙 X)
    [IsIso (g.residueFieldMap (f x))] : IsIso (f.residueFieldMap x) := by
  have : IsIso (g.residueFieldMap (f x) ≫ f.residueFieldMap x) := by
    rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr hfg]
    simpa using Iso.isIso_hom _
  exact IsIso.of_isIso_comp_left (g.residueFieldMap (f x)) _

/-- Translation by the source-normalized arrow family attached to `r`. -/
public noncomputable def translationByPoint {S : Scheme.{u}} (G : GroupoidScheme S)
    (k : Type u) [Field k] (hU : G.objects.left = Spec (.of k))
    (r : G.arrows.left) [IsIso (G.source.left.residueFieldMap r)] :
    G.arrows ⟶ G.arrows :=
  leftTranslation G (sourceNormalizedArrow G k hU r)
    (sourceNormalizedArrow_source G k hU r)

/-- Translation by a section of the source map sends the identity family to that section. -/
private lemma identity_comp_leftTranslation {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : G.objects ⟶ G.arrows) (ha : a ≫ G.source = 𝟙 G.objects) :
    G.identity ≫ leftTranslation G a ha = a := by
  have w : a ≫ G.source = (a ≫ G.source ≫ G.identity) ≫ G.target := by
    simp [Category.assoc, ha, G.target_identity]
  have hpull : G.identity ≫
      pullback.lift (G.target ≫ a) (𝟙 G.arrows) (by simp [Category.assoc, ha]) =
        pullback.lift a (a ≫ G.source ≫ G.identity) w := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [← Category.assoc, G.target_identity, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, ha, Category.id_comp, Category.comp_id]
  rw [leftTranslation, ← Category.assoc, hpull]
  exact G.right_identity G.objects a w

/-- On generalized arrows, translation by `a` composes `a` over the target with the arrow. -/
private lemma leftTranslation_apply {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : G.objects ⟶ G.arrows) (ha : a ≫ G.source = 𝟙 G.objects)
    {T : Over S} (f : T ⟶ G.arrows) :
    f ≫ leftTranslation G a ha =
      G.compose (f ≫ G.target ≫ a) f (by simp [Category.assoc, ha]) := by
  have w : (f ≫ G.target ≫ a) ≫ G.source = f ≫ G.target := by
    simp [Category.assoc, ha]
  have hpull : f ≫ pullback.lift (G.target ≫ a) (𝟙 G.arrows)
      (by simp [Category.assoc, ha]) = pullback.lift (f ≫ G.target ≫ a) f w := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]
      simp
  dsimp [leftTranslation, Stacks.Groupoids.GroupoidScheme.compose]
  rw [← Category.assoc, hpull]

/-- Two morphisms of `Over S` which agree on every generalized point are equal. -/
private alias overHom_eq_of_points := Stacks.Groupoids.overHom_ext

/-- Composition of generalized arrows depends only on the arrows, not on the composability
witness, and so is compatible with replacing the first arrow by an equal one. -/
lemma groupoidCompose_congr_left {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} {f f' g : T ⟶ G.arrows} (h : f = f')
    (w : f ≫ G.source = g ≫ G.target) (w' : f' ≫ G.source = g ≫ G.target) :
    G.compose f g w = G.compose f' g w' := by
  cases h
  rfl

/-- The companion of `groupoidCompose_congr_left` for the second arrow. -/
lemma groupoidCompose_congr_right {S : Scheme.{u}} (G : GroupoidScheme S)
    {T : Over S} {f g g' : T ⟶ G.arrows} (h : g = g')
    (w : f ≫ G.source = g ≫ G.target) (w' : f ≫ G.source = g' ≫ G.target) :
    G.compose f g w = G.compose f g' w' := by
  cases h
  rfl

/-- The target of a composite of generalized arrows is the target of the first one. -/
private lemma compose_target {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (D f : T ⟶ G.arrows) (w : D ≫ G.source = f ≫ G.target) :
    G.compose D f w ≫ G.target = D ≫ G.target := by
  simp [Stacks.Groupoids.GroupoidScheme.compose, Category.assoc, G.target_comp,
    pullback.lift_fst_assoc]

/-- If `B` cancels `D` to the identity over the target of `f`, then composing `B` with the
composite of `D` and `f` gives back `f`. -/
private lemma compose_compose_cancel {S : Scheme.{u}} (G : GroupoidScheme S) {T : Over S}
    (f D B : T ⟶ G.arrows) (wDf : D ≫ G.source = f ≫ G.target)
    (wBD : B ≫ G.source = D ≫ G.target)
    (hcancel : G.compose B D wBD = (f ≫ G.target) ≫ G.identity) :
    G.compose B (G.compose D f wDf) (wBD.trans (compose_target G D f wDf).symm) = f := by
  have w1 : (G.compose B D wBD) ≫ G.source = f ≫ G.target := by
    rw [← wDf]
    simp [Stacks.Groupoids.GroupoidScheme.compose, G.source_comp, pullback.lift_snd_assoc]
  have wIdentity : ((f ≫ G.target) ≫ G.identity) ≫ G.source = f ≫ G.target := by
    simp [G.source_identity]
  calc
    _ = G.compose (G.compose B D wBD) f w1 :=
      (G.assoc T B D f wBD wDf w1 _).symm
    _ = G.compose ((f ≫ G.target) ≫ G.identity) f wIdentity :=
      groupoidCompose_congr_left G hcancel w1 wIdentity
    _ = f := by
      simpa [Stacks.Groupoids.GroupoidScheme.compose] using
        G.left_identity T f (by simpa using wIdentity)

/-- Translation by a section `a` of the source map is invertible as soon as there is a section
`b` of the target map which is inverse to `a` in the two displayed senses; its inverse is
translation by the inverse of `b`. -/
private lemma leftTranslation_isIso_of_sections {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : G.objects ⟶ G.arrows) (ha : a ≫ G.source = 𝟙 G.objects)
    (b : G.objects ⟶ G.arrows) (hb : b ≫ G.target = 𝟙 G.objects)
    (hba : b ≫ G.source ≫ a = b)
    (hab : a ≫ G.target ≫ b = a) :
    IsIso (leftTranslation G a ha) := by
  let d : G.objects ⟶ G.arrows := b ≫ G.inverse
  have hd : d ≫ G.source = 𝟙 G.objects := by
    dsimp [d]
    rw [Category.assoc, G.source_inverse, hb]
  have hda : d ≫ G.target ≫ a = b := by
    simp only [d, Category.assoc, reassoc_of% G.target_inverse, hba]
  have had : a ≫ G.target ≫ d = a ≫ G.inverse := by
    simp only [d, reassoc_of% hab]
  let Ld := leftTranslation G d hd
  let La := leftTranslation G a ha
  have hleft : Ld ≫ La = 𝟙 G.arrows := by
    refine overHom_eq_of_points _ _ fun T f => ?_
    let y := f ≫ G.target
    let D := y ≫ d
    have wDf : D ≫ G.source = f ≫ G.target := by simp [D, y, hd]
    let H := G.compose D f wDf
    have htargetH : H ≫ G.target = D ≫ G.target := compose_target G D f wDf
    let B := H ≫ G.target ≫ a
    have hB : B = y ≫ b := by
      simp only [B, ← Category.assoc, htargetH]
      simp [D, hda]
    have hD : D = B ≫ G.inverse := by
      rw [hB]
      simp [D, d]
    have wBDinv : B ≫ G.source = (B ≫ G.inverse) ≫ G.target := by
      rw [hB]
      simp [Category.assoc, G.target_inverse]
    have wBD : B ≫ G.source = D ≫ G.target := by rwa [hD]
    have hcancel : G.compose B D wBD = y ≫ G.identity :=
      (groupoidCompose_congr_right G hD wBD wBDinv).trans
        ((G.right_inverse T B wBDinv).trans (by rw [hB]; simp [reassoc_of% hb]))
    have hLd : f ≫ Ld = H := by
      simpa [H, D, y] using leftTranslation_apply G d hd f
    calc
      f ≫ (Ld ≫ La) = H ≫ La := by rw [← Category.assoc, hLd]
      _ = G.compose B H _ := leftTranslation_apply G a ha H
      _ = f := compose_compose_cancel G f D B wDf wBD hcancel
  have hright : La ≫ Ld = 𝟙 G.arrows := by
    refine overHom_eq_of_points _ _ fun T f => ?_
    let y := f ≫ G.target
    let A := y ≫ a
    have wAf : A ≫ G.source = f ≫ G.target := by simp [A, y, ha]
    let H := G.compose A f wAf
    have htargetH : H ≫ G.target = A ≫ G.target := compose_target G A f wAf
    have hD : H ≫ G.target ≫ d = A ≫ G.inverse := by
      rw [← Category.assoc, htargetH]
      simp [A, had]
    have wDA : (A ≫ G.inverse) ≫ G.source = A ≫ G.target := by
      simp [Category.assoc, G.source_inverse]
    have hcancel : G.compose (A ≫ G.inverse) A wDA = y ≫ G.identity :=
      (G.left_inverse T A (by simp [G.source_inverse])).trans (by simp [A, reassoc_of% ha])
    have hLa : f ≫ La = H := by
      simpa [H, A, y] using leftTranslation_apply G a ha f
    calc
      f ≫ (La ≫ Ld) = H ≫ Ld := by rw [← Category.assoc, hLa]
      _ = G.compose (A ≫ G.inverse) H _ :=
        (leftTranslation_apply G d hd H).trans (groupoidCompose_congr_left G hD _ _)
      _ = f := compose_compose_cancel G f A (A ≫ G.inverse) wAf wDA hcancel
  exact
 CategoryTheory.Iso.isIso_hom
    { hom := La, inv := Ld, hom_inv_id := hright, inv_hom_id := hleft }

/-- When the object scheme is the spectrum of a field and both the source and the target induce
isomorphisms of residue fields at `r`, the target of the source-normalized arrow family at `r`
is an automorphism of the object scheme. -/
private lemma sourceTargetFieldAutomorphism_isIso {S : Scheme.{u}}
    (G : GroupoidScheme S) (k : Type u) [Field k]
    (hU : G.objects.left = Spec (.of k)) (r : G.arrows.left)
    [IsIso (G.source.left.residueFieldMap r)] [IsIso (G.target.left.residueFieldMap r)] :
    IsIso ((sourceNormalizedArrow G k hU r ≫ G.target).left) := by
  let a := sourceNormalizedArrow G k hU r
  let eU : G.objects.left ≅ Spec (.of k) := asIso (eqToHom hU)
  let α := a ≫ G.target
  let αₖ : Spec (.of k) ⟶ Spec (.of k) := eU.inv ≫ α.left ≫ eU.hom
  have hinj : Function.Injective eU.hom := (TopCat.homeoOfIso (asIso eU.hom.base)).injective
  have hx : eU.inv (default : Spec (.of k)) = G.source.left r := hinj (Subsingleton.elim _ _)
  have hpoint : a.left (G.source.left r) = r := sourceNormalizedArrow_apply G k hU r
  have hsourceAt : IsIso
      (G.source.left.residueFieldMap (a.left (G.source.left r))) :=
    residueFieldMap_isIso_of_point_eq G.source.left hpoint
  have haResidue : IsIso (a.left.residueFieldMap (G.source.left r)) :=
    residueFieldMap_rightFactor_isIso a.left G.source.left (G.source.left r)
      (congrArg Over.Hom.left (sourceNormalizedArrow_source G k hU r))
  have htargetAt : IsIso
      (G.target.left.residueFieldMap (a.left (G.source.left r))) :=
    residueFieldMap_isIso_of_point_eq G.target.left hpoint
  have hαResidue : IsIso (α.left.residueFieldMap (G.source.left r)) := by
    have hres : α.left.residueFieldMap (G.source.left r) =
        G.target.left.residueFieldMap (a.left (G.source.left r)) ≫
          a.left.residueFieldMap (G.source.left r) := by
      simp [α, Scheme.residueFieldMap_comp]
    rw [hres]
    exact IsIso.comp_isIso' htargetAt haResidue
  have hαₖResidue : IsIso (αₖ.residueFieldMap (default : Spec (.of k))) := by
    have hres : αₖ.residueFieldMap (default : Spec (.of k)) =
        eU.hom.residueFieldMap (α.left (eU.inv default)) ≫
          α.left.residueFieldMap (eU.inv default) ≫ eU.inv.residueFieldMap default := by
      dsimp [αₖ]
      simp only [Scheme.residueFieldMap_comp]
      exact Category.assoc
        (eU.hom.residueFieldMap (α.left (eU.inv default)))
        (α.left.residueFieldMap (eU.inv default))
        (eU.inv.residueFieldMap default)
    have hαAt : IsIso (α.left.residueFieldMap (eU.inv default)) :=
      residueFieldMap_isIso_of_point_eq α.left hx
    have : IsIso eU.hom := CategoryTheory.Iso.isIso_hom eU
    have : IsIso eU.inv := CategoryTheory.Iso.isIso_inv eU
    have hfirst : IsIso
        (eU.hom.residueFieldMap (α.left (eU.inv default)) ≫
          α.left.residueFieldMap (eU.inv default)) := IsIso.comp_isIso
    have hcomp : IsIso
        ((eU.hom.residueFieldMap (α.left (eU.inv default)) ≫
          α.left.residueFieldMap (eU.inv default)) ≫ eU.inv.residueFieldMap default) :=
      IsIso.comp_isIso
    rw [hres]
    exact hcomp
  have hαₖ : IsIso αₖ := isIsoSpecFieldHom αₖ hαₖResidue
  have hαleft : α.left = eU.hom ≫ αₖ ≫ eU.inv := by simp [αₖ]
  rw [hαleft]
  infer_instance

/-- A section `a` of the source map whose target is an automorphism of the object scheme has
invertible left translation: the inverse of that automorphism composed with `a` provides the
section of the target map which `leftTranslation_isIso_of_sections` requires. -/
@[sga "3 VIA 0.4" "more general"]
private lemma leftTranslation_isIso_of_isIso_target {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : G.objects ⟶ G.arrows) (ha : a ≫ G.source = 𝟙 G.objects)
    [IsIso (a ≫ G.target)] : IsIso (leftTranslation G a ha) := by
  let α : G.objects ⟶ G.objects := a ≫ G.target
  let b : G.objects ⟶ G.arrows := inv α ≫ a
  have hb : b ≫ G.target = 𝟙 G.objects := by simp [b, α]
  have hba : b ≫ G.source ≫ a = b := by
    simp only [b, Category.assoc, reassoc_of% ha]
  have hab : a ≫ G.target ≫ b = a := by
    show α ≫ inv α ≫ a = a
    simp
  exact leftTranslation_isIso_of_sections G a ha b hb hba hab

/-- **Stacks Project, Tag 04LS.** Translation by a point whose source and target induce
isomorphisms on residue fields is an automorphism of the arrow scheme. -/
@[stacks 04LS "the automorphism"]
public lemma translationByPoint_isIso {S : Scheme.{u}} (G : GroupoidScheme S)
    (k : Type u) [Field k] (hU : G.objects.left = Spec (.of k))
    (r : G.arrows.left) [IsIso (G.source.left.residueFieldMap r)]
    [IsIso (G.target.left.residueFieldMap r)] :
    IsIso (translationByPoint G k hU r) := by
  have : IsIso ((Over.forget S).map (sourceNormalizedArrow G k hU r ≫ G.target)) :=
    sourceTargetFieldAutomorphism_isIso G k hU r
  have := isIso_of_reflects_iso (sourceNormalizedArrow G k hU r ≫ G.target) (Over.forget S)
  exact leftTranslation_isIso_of_isIso_target G _ (sourceNormalizedArrow_source G k hU r)

/-- **Stacks Project, Tag 04LS.** Translation by `r` maps the identity arrow at the source of
`r` to `r`. -/
@[stacks 04LS "image of the identity"]
public lemma identity_image_translationByPoint {S : Scheme.{u}} (G : GroupoidScheme S)
    (k : Type u) [Field k] (hU : G.objects.left = Spec (.of k))
    (r : G.arrows.left) [IsIso (G.source.left.residueFieldMap r)] :
    (G.identity ≫ translationByPoint G k hU r).left (G.source.left r) = r := by
  rw [translationByPoint, identity_comp_leftTranslation, sourceNormalizedArrow_apply]


end AlgebraicGeometry.GroupoidScheme
