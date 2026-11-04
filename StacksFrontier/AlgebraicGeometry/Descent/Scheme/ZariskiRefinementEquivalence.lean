module

public import Mathlib.AlgebraicGeometry.Sites.MorphismProperty
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.PullbackFpqcRefinement
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.PullbackFunctor
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.PulledBackDatum

/-!
# Descent data under a Zariski refinement of families

Let `U` and `V` be families of schemes over a base `S` and let `α` exhibit `U` as a
refinement of `V` over the identity of `S`. If the part of `U` lying over each member of `V`
is a Zariski covering of that member, then pullback of descent data along `α` is an
equivalence of categories. In particular the schemes over `S` are equivalent to the descent
data relative to any Zariski covering of `S`.

## Main results

* `AlgebraicGeometry.pullbackFunctor_isEquivalence_of_zariskiRefinement`: **Stacks 02VY**,
  pullback along a fibrewise Zariski refinement is an equivalence on descent data.
* `AlgebraicGeometry.descentData_equivalence_of_zariskiCovering`: **Stacks 02VY**, final
  sentence, the schemes over `S` are equivalent to the descent data for a Zariski covering.

## Implementation notes

The Zariski hypothesis is read through `Scheme.zariskiPrecoverage`, so each fibre is a
jointly surjective family of open immersions. Full faithfulness is inherited from the fpqc
statement `AlgebraicGeometry.pullbackFunctor_fullyFaithful_of_fpqcRefinement` along
`Scheme.zariskiPrecoverage_le_fpqcPrecoverage`; only essential surjectivity uses the
Zariski hypothesis, and it uses it twice over. Over a fixed member `V_j` the components
`V_i` of a datum `D` for `U` are glued along the transition isomorphisms into a scheme
`Y_j` over `V_j`, which is possible because the maps `U_i → V_j` are open immersions, so
the pairwise overlaps are open subschemes of the `V_i`. The gluing isomorphisms for the
`Y_j` are then produced by descending the ones of `D` along the open covering of
`Y_j ×_S V_{j'}` by the `V_i ×_S U_{i'}`, which is where `OpenCoverOver`, a covering of an
`S`-scheme by open `S`-subschemes with its descent of morphisms, is used.

Morphisms out of a product in `Over S` are handled through `transport`, which sends a pair
of maps into `(Over.map (f i)).obj (D.obj i)` and `Over.mk (f j)` to the second component
of its image under the gluing isomorphism; the cocycle condition becomes the composition
law `transport_comp`. This keeps the argument inside the product in `Over S` used by
`AlgebraicGeometry.DescentData` rather than passing to literal fibre products.

## References

* [Stacks Project, Tag 02VY](https://stacks.math.columbia.edu/tag/02VY)
* [Stacks Project, Tag 02VZ](https://stacks.math.columbia.edu/tag/02VZ)
* [Stacks Project, Tag 02VS](https://stacks.math.columbia.edu/tag/02VS)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace ZariskiRefinement


section
universe v
variable {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}
private def transport (D : DescentData f) {T : Over S} (i j : I)
    (x : T ⟶ (Over.map (f i)).obj (D.obj i)) (y : T ⟶ Over.mk (f j)) :=
  prod.lift x y ≫ (D.gluing i j).hom.left ≫ prod.snd
@[reassoc]
private lemma transport_structure (D : DescentData f) {T : Over S} (i j : I)
    (x : T ⟶ (Over.map (f i)).obj (D.obj i)) (y : T ⟶ Over.mk (f j)) :
    transport D i j x y ≫ structureMap (f j) (D.obj j) = y := by
  simp [transport]
private lemma transport_comp (D : DescentData f) {T : Over S} (i j k : I)
    (x : T ⟶ (Over.map (f i)).obj (D.obj i))
    (y : T ⟶ Over.mk (f j)) (z : T ⟶ Over.mk (f k)) :
    transport D j k (transport D i j x y) z = transport D i k x z := by
  have h := congrArg (fun m ↦ prod.lift (prod.lift x y) z ≫ m ≫ prod.snd)
    (D.cocycle i j k)
  simpa [transport, prodMapLastTwo, prodMapFirstThird, prod.comp_lift, prod.comp_lift_assoc,
    ← prod.lift_fst_comp_snd_comp, Category.assoc] using h
@[reassoc]
private lemma transport_naturality (D : DescentData f) {T T' : Over S} (a : T' ⟶ T)
    (i j : I) (x : T ⟶ (Over.map (f i)).obj (D.obj i))
    (y : T ⟶ Over.mk (f j)) :
    a ≫ transport D i j x y = transport D i j (a ≫ x) (a ≫ y) := by
  simp [transport, prod.comp_lift_assoc]
private lemma transport_self (D : DescentData f) {T : Over S} (i : I)
    (x : T ⟶ (Over.map (f i)).obj (D.obj i)) :
    transport D i i x (x ≫ structureMap (f i) (D.obj i)) = x := by
  let y := x ≫ structureMap (f i) (D.obj i)
  have h : prod.lift (transport D i i x y) y ≫ (D.gluing i i).hom.left =
      prod.lift x y ≫ (D.gluing i i).hom.left := by
    apply prod.hom_ext
    · simp [y, transport_structure]
    · exact transport_comp D i i i x y y
  have ht : IsIso (D.gluing i i).hom.left :=
    (Over.forget _).map_isIso (D.gluing i i).hom
  have h' := (cancel_mono (D.gluing i i).hom.left).mp h
  simpa using congrArg (fun m ↦ m ≫ prod.fst) h'
private lemma transport_inverse (D : DescentData f) {T : Over S} (i j : I)
    (x : T ⟶ (Over.map (f i)).obj (D.obj i))
    (y : T ⟶ Over.mk (f j)) :
    transport D j i (transport D i j x y) (x ≫ structureMap (f i) (D.obj i)) = x := by
  rw [transport_comp, transport_self]

private lemma identity_gluing {S : Scheme.{u}}
    (D : DescentData (S := S) (X := fun _ : PUnit.{v+1} ↦ S) (fun _ ↦ 𝟙 S)) :
    (D.gluing PUnit.unit PUnit.unit).hom.left = (prod.braiding _ _).hom := by
  apply prod.hom_ext
  · apply Over.mkIdTerminal.hom_ext
  · have h := transport_self D PUnit.unit (prod.fst (X :=
        (Over.map (𝟙 S)).obj (D.obj PUnit.unit)) (Y := Over.mk (𝟙 S)))
    rw [show prod.fst ≫ structureMap (𝟙 S) (D.obj PUnit.unit) =
      (prod.snd : _ ⨯ Over.mk (𝟙 S) ⟶ _) from Over.mkIdTerminal.hom_ext _ _] at h
    simpa [transport] using h

private def identityDescentFunctor (S : Scheme.{u}) :
    Over S ⥤ DescentData (S := S) (X := fun _ : PUnit.{v+1} ↦ S) (fun _ ↦ 𝟙 S) :=
{ obj := fun U ↦
    { obj := fun _ ↦ U
      gluing := fun _ _ ↦ Over.isoMk (prod.braiding _ _) (by
        apply prod.hom_ext <;> apply Over.mkIdTerminal.hom_ext)
      cocycle := by
        intros
        apply prod.hom_ext
        · apply prod.hom_ext <;> apply Over.mkIdTerminal.hom_ext
        · simp [prodMapLastTwo, prodMapFirstThird] }
  map := fun g ↦ { hom := fun _ ↦ g, comm := by intros; simp }
  map_id _ := DescentData.hom_ext fun _ ↦ rfl
  map_comp _ _ := DescentData.hom_ext fun _ ↦ rfl }

private def identityDescentEquivalence (S : Scheme.{u}) :
    Over S ≌ DescentData (S := S) (X := fun _ : PUnit.{v+1} ↦ S) (fun _ ↦ 𝟙 S) where
  functor := identityDescentFunctor S
  inverse := DescentData.evaluation PUnit.unit
  unitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro U V g
    change g ≫ 𝟙 _ = 𝟙 _ ≫ g
    simp)
  counitIso := NatIso.ofComponents (fun D ↦
    { hom :=
        { hom := fun i ↦ 𝟙 _
          comm := by
            rintro ⟨⟩ ⟨⟩
            change prod.map ((Over.map (𝟙 S)).map (𝟙 (D.obj PUnit.unit)))
                (𝟙 (Over.mk (𝟙 S))) ≫ (D.gluing PUnit.unit PUnit.unit).hom.left =
              (prod.braiding _ _).hom ≫ prod.map (𝟙 (Over.mk (𝟙 S)))
                ((Over.map (𝟙 S)).map (𝟙 (D.obj PUnit.unit)))
            simp [identity_gluing] }
      inv :=
        { hom := fun i ↦ 𝟙 _
          comm := by
            rintro ⟨⟩ ⟨⟩
            simp [identityDescentFunctor, identity_gluing] }
      hom_inv_id := DescentData.hom_ext fun _ ↦ Category.id_comp _
      inv_hom_id := DescentData.hom_ext fun _ ↦ Category.id_comp _ })
    (by
      intro D E g
      apply DescentData.hom_ext
      rintro ⟨⟩
      change g.hom PUnit.unit ≫ 𝟙 _ = 𝟙 _ ≫ g.hom PUnit.unit
      rw [Category.comp_id, Category.id_comp])
  functor_unitIso_comp := by
    intro U
    exact DescentData.hom_ext fun _ ↦ Category.id_comp _

end

section
variable {I : Type u} {S : Scheme.{u}} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}

private lemma base_hom_ext (i : I) [Mono (f i)] {T : Over S}
    (a b : T ⟶ Over.mk (f i)) : a = b := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (f i)).mp
  exact (Over.w a).trans (Over.w b).symm

private abbrev overlap (D : DescentData f) (i j : I) :=
  (Over.map (f i)).obj (D.obj i) ⨯ Over.mk (f j)
private abbrev transition (D : DescentData f) (i j : I) :
    overlap D i j ⟶ overlap D j i :=
  prod.lift (transport D i j prod.fst prod.snd)
    (prod.fst ≫ structureMap (f i) (D.obj i))
private lemma transition_id (D : DescentData f) (i : I) [Mono (f i)] :
    transition D i i = 𝟙 _ := by
  apply prod.hom_ext
  · simp only [transition, prod.lift_fst]
    rw [base_hom_ext i prod.snd (prod.fst ≫ structureMap (f i) (D.obj i)),
      transport_self, Category.id_comp]
  · apply base_hom_ext

private def overlapRotation (D : DescentData f) (i j k : I) :
    pullback (prod.fst : overlap D i j ⟶ _) (prod.fst : overlap D i k ⟶ _) ⟶
    pullback (prod.fst : overlap D j k ⟶ _) (prod.fst : overlap D j i ⟶ _) :=
  pullback.lift
    (prod.lift (pullback.fst _ _ ≫ transition D i j ≫ prod.fst)
      (pullback.snd _ _ ≫ prod.snd))
    (pullback.fst _ _ ≫ transition D i j) (by simp)

@[reassoc]
private lemma overlapRotation_snd (D : DescentData f) (i j k : I) :
    overlapRotation D i j k ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ transition D i j :=
  pullback.lift_snd _ _ _
@[reassoc]
private lemma overlapRotation_fst_fst (D : DescentData f) (i j k : I) :
    overlapRotation D i j k ≫ pullback.fst _ _ ≫ prod.fst =
      transport D i j (pullback.fst _ _ ≫ prod.fst) (pullback.fst _ _ ≫ prod.snd) := by
  dsimp only [overlapRotation]
  rw [pullback.lift_fst_assoc]
  simp [transition, transport_naturality]
@[reassoc]
private lemma overlapRotation_fst_snd (D : DescentData f) (i j k : I) :
    overlapRotation D i j k ≫ pullback.fst _ _ ≫ prod.snd =
      pullback.snd _ _ ≫ prod.snd := by
  dsimp only [overlapRotation]
  rw [pullback.lift_fst_assoc, prod.lift_snd]
private lemma overlap_fst_mono (D : DescentData f) (i j : I) [Mono (f j)] :
    Mono (prod.fst : overlap D i j ⟶ _) where
  right_cancellation _ _ h := prod.hom_ext h (base_hom_ext j _ _)

private lemma overlapRotation_cocycle (D : DescentData f) (i j k : I)
    [∀ i, Mono (f i)] :
    overlapRotation D i j k ≫ overlapRotation D j k i ≫ overlapRotation D k i j = 𝟙 _ := by
  let := overlap_fst_mono D i j
  let := overlap_fst_mono D i k
  apply (cancel_mono (pullback.fst (prod.fst : overlap D i j ⟶ _)
    (prod.fst : overlap D i k ⟶ _))).mp
  apply (cancel_mono (prod.fst : overlap D i j ⟶ _)).mp
  simp only [Category.assoc, Category.id_comp, overlapRotation_fst_fst,
    transport_naturality, overlapRotation_fst_snd]
  rw [← Category.assoc (overlapRotation D i j k), overlapRotation_snd]
  simp only [transition, Category.assoc, prod.lift_snd,
    transport_comp]
  simpa only [Category.assoc] using transport_self D i (pullback.fst _ _ ≫ prod.fst)

private def overlapFstIso (D : DescentData f) (i : I) [Mono (f i)] :
    overlap D i i ≅ (Over.map (f i)).obj (D.obj i) where
  hom := prod.fst
  inv := prod.lift (𝟙 _) (structureMap (f i) (D.obj i))
  hom_inv_id := by
    apply prod.hom_ext
    · simp
    · apply base_hom_ext
  inv_hom_id := by simp

private def overGlueData (D : DescentData f) [∀ i, Mono (f i)] :
    CategoryTheory.GlueData (Over S) where
  J := I
  U i := (Over.map (f i)).obj (D.obj i)
  V p := overlap D p.1 p.2
  f i j := prod.fst
  f_mono i j := overlap_fst_mono D i j
  f_id i := (overlapFstIso D i).isIso_hom
  t := transition D
  t_id i := transition_id D i
  t' := overlapRotation D
  t_fac := overlapRotation_snd D
  cocycle i j k := overlapRotation_cocycle D i j k
private def schemeGlueData (D : DescentData f) [hopen : ∀ i, IsOpenImmersion (f i)] :
    Scheme.GlueData.{u} where
  toGlueData := (overGlueData D).mapGlueData (Over.forget S)
  f_open i j := by
    change IsOpenImmersion (prod.fst : overlap D i j ⟶ _).left
    rw [← Over.prodLeftIsoPullback_hom_fst]
    change IsOpenImmersion (_ ≫ pullback.fst ((D.obj i).hom ≫ f i) (f j))
    have : IsOpenImmersion (f j) := hopen j
    have : IsOpenImmersion
        (Over.prodLeftIsoPullback ((Over.map (f i)).obj (D.obj i)) (Over.mk (f j))).hom :=
      IsOpenImmersion.of_isIso _
    exact IsOpenImmersion.comp _ (pullback.fst ((D.obj i).hom ≫ f i) (f j))
private def gluedToBase (D : DescentData f) [∀ i, IsOpenImmersion (f i)] :
    (schemeGlueData D).glued ⟶ S :=
  Multicoequalizer.desc (schemeGlueData D).diagram S
    (fun i ↦ (D.obj i).hom ≫ f i) (fun p ↦ by
      change (prod.fst : overlap D p.1 p.2 ⟶ _).left ≫
          ((Over.map (f p.1)).obj (D.obj p.1)).hom =
        (transition D p.1 p.2 ≫ prod.fst).left ≫
          ((Over.map (f p.2)).obj (D.obj p.2)).hom
      exact (Over.w _).trans (Over.w _).symm)
/-- The chart at `i` of the scheme glued from a descent datum, with its source named in the
index type of the family rather than in that of the glue data. -/
private def chartι (D : DescentData f) [∀ i, IsOpenImmersion (f i)] (i : I) :
    ((Over.map (f i)).obj (D.obj i)).left ⟶ (schemeGlueData D).glued :=
  (schemeGlueData D).ι i

private lemma chartι_eq (D : DescentData f) [∀ i, IsOpenImmersion (f i)] (i : I) :
    chartι D i = (schemeGlueData D).ι i := rfl

private lemma chartι_jointly_surjective (D : DescentData f)
    [∀ i, IsOpenImmersion (f i)] (x : (schemeGlueData D).glued) :
    ∃ (i : I) (y : ((Over.map (f i)).obj (D.obj i)).left), chartι D i y = x :=
  (schemeGlueData D).ι_jointly_surjective x

@[reassoc]
private lemma chart_gluedToBase (D : DescentData f) [∀ i, IsOpenImmersion (f i)]
    (i : I) :
    chartι D i ≫ gluedToBase D = (D.obj i).hom ≫ f i := by
  dsimp only [chartι, gluedToBase, Scheme.GlueData.ι, CategoryTheory.GlueData.ι]
  exact Multicoequalizer.π_desc (schemeGlueData D).diagram S
    (fun i ↦ (D.obj i).hom ≫ f i) _ i

/-- The glue condition of the glue data of a descent datum, with its indices named in the
index type of the family. -/
private lemma chartι_transition (D : DescentData f) [∀ i, IsOpenImmersion (f i)] (i j : I) :
    (transition D j i).left ≫ (prod.fst : overlap D i j ⟶ _).left ≫ chartι D i =
      (prod.fst : overlap D j i ⟶ _).left ≫ chartι D j :=
  (schemeGlueData D).glue_condition j i

private lemma chart_isPullback (D : DescentData f) [hopen : ∀ i, IsOpenImmersion (f i)]
    (i : I) :
    IsPullback (D.obj i).hom (chartι D i) (f i) (gluedToBase D) := by
  have : IsOpenImmersion (f i) := hopen i
  have : IsOpenImmersion (chartι D i) :=
    Scheme.GlueData.ι_isOpenImmersion (schemeGlueData D) i
  apply IsOpenImmersion.isPullback _ _ _ _ (chart_gluedToBase D i)
  ext y
  constructor
  · rintro ⟨ui, hui⟩
    obtain ⟨j, xj, rfl⟩ := chartι_jointly_surjective D y
    have hx : ((D.obj j).hom ≫ f j) xj = (f i) ui := by
      rw [← chart_gluedToBase D j, Scheme.Hom.comp_apply]
      exact hui.symm
    obtain ⟨z, hz, _⟩ := Scheme.Pullback.exists_preimage_pullback xj ui hx
    let e := Over.prodLeftIsoPullback ((Over.map (f j)).obj (D.obj j)) (Over.mk (f i))
    let w := e.inv z
    have hw : (prod.fst : overlap D j i ⟶ _).left w = xj := by
      rw [← Scheme.Hom.comp_apply]
      show (e.inv ≫ (prod.fst : overlap D j i ⟶ _).left) z = xj
      rw [← Over.prodLeftIsoPullback_hom_fst, Iso.inv_hom_id_assoc]
      exact hz
    refine ⟨(prod.fst : overlap D i j ⟶ _).left ((transition D j i).left w), ?_⟩
    have hc := congrArg (fun m : (overlap D j i).left ⟶ _ ↦ m w) (chartι_transition D i j)
    simp only [Scheme.Hom.comp_apply] at hc
    rw [hc, hw]
  · rintro ⟨x, rfl⟩
    exact ⟨(D.obj i).hom x,
      congrArg (fun m : (D.obj i).left ⟶ S ↦ m x) (chart_gluedToBase D i).symm⟩

end

private lemma zariskiCover_data {S : Scheme.{u}} {I : Type*}
    {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hZar : Presieve.ofArrows X f ∈ Scheme.zariskiPrecoverage S) :
    (∀ x : S, ∃ i, x ∈ Set.range (f i).base) ∧ ∀ i, IsOpenImmersion (f i) :=
  (Scheme.ofArrows_mem_precoverage_iff @IsOpenImmersion).mp hZar

private lemma refinement_maps_are_open_immersions {S : Scheme.{u}}
    (U V : PreZeroHypercover.{u} S) (α : U.HomOver V (𝟙 S))
    (hZar : ∀ j : V.I₀,
      Presieve.ofArrows
        (fun i : {i : U.I₀ // α.s₀ i = j} ↦ U.X i)
        (fun i ↦ α.h₀ i.val ≫ eqToHom (congrArg V.X i.property)) ∈
          Scheme.zariskiPrecoverage (V.X j)) :
    ∀ i : U.I₀, IsOpenImmersion (α.h₀ i) := by
  intro i
  simpa using (zariskiCover_data _ (hZar (α.s₀ i))).2 ⟨i, rfl⟩

private abbrev fibreFamily {S : Scheme.{u}} (U V : PreZeroHypercover.{u} S)
    (α : U.HomOver V (𝟙 S)) (j : V.I₀) : PreZeroHypercover.{u} (V.X j) where
  I₀ := {i : U.I₀ // α.s₀ i = j}
  X i := U.X i
  f i := α.h₀ i.val ≫ eqToHom (congrArg V.X i.property)

private abbrev fibreMorphism {S : Scheme.{u}} (U V : PreZeroHypercover.{u} S)
    (α : U.HomOver V (𝟙 S)) (j : V.I₀) : MorphismOfSchemeFamilies.{u} where
  sourceBase := V.X j
  targetBase := S
  sourceFamily := fibreFamily U V α j
  targetFamily := U
  baseHom := V.f j
  familyHom :=
    { s₀ := Subtype.val
      h₀ := fun i ↦ 𝟙 (U.X i.val)
      w₀ := by
        rintro ⟨i, hi⟩
        change 𝟙 (U.X i) ≫ U.f i =
          (α.h₀ i ≫ eqToHom (congrArg V.X hi)) ≫ V.f j
        subst j
        simpa using (α.w₀ i).symm }

private abbrev fibreComponentIso {S : Scheme.{u}} (U V : PreZeroHypercover.{u} S)
    (α : U.HomOver V (𝟙 S)) (D : DescentData U.f) (j : V.I₀)
    (i : {i : U.I₀ // α.s₀ i = j}) :
    (MorphismOfSchemeFamilies.pulledBackDatum (fibreMorphism U V α j) D).obj i ≅
      D.obj i.val :=
  MorphismOfSchemeFamilies.pulledBackDatumObjIso (fibreMorphism U V α j) D i ≪≫
    Over.pullbackId.app (D.obj i.val)


section
variable {S : Scheme.{u}} {I : Type*} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}

@[reassoc]
private lemma comp_pullbackLift {C : Type*} [Category C] {T W A B Z : C}
    {f : A ⟶ Z} {g : B ⟶ Z} [HasPullback f g]
    (p : T ⟶ W) (a : W ⟶ A) (b : W ⟶ B) (h : a ≫ f = b ≫ g) :
    p ≫ pullback.lift a b h =
      pullback.lift (p ≫ a) (p ≫ b) (by simpa only [Category.assoc] using congrArg (p ≫ ·) h) := by
  apply pullback.hom_ext <;> simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd]

private lemma transport_left (D : DescentData f) {T : Over S} (i j : I)
    (x : T ⟶ (Over.map (f i)).obj (D.obj i)) (y : T ⟶ Over.mk (f j)) :
    (transport D i j x y).left =
      pullback.lift x.left y.left ((Over.w x).trans (Over.w y).symm) ≫
        (D.gluingPullbackIso i j).hom ≫ pullback.snd _ _ := by
  have h : pullback.lift x.left y.left ((Over.w x).trans (Over.w y).symm) =
      (prod.lift x y).left ≫ (Over.prodLeftIsoPullback _ _).hom := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
        Over.prodLeftIsoPullback_hom_fst, Over.prodLeftIsoPullback_hom_snd,
        ← Over.comp_left, prod.lift_fst, prod.lift_snd]
  rw [h]
  have hp := Over.prodLeftIsoPullback_hom_snd (Over.mk (f i))
    ((Over.map (f j)).obj (D.obj j))
  change (Over.prodLeftIsoPullback (Over.mk (f i))
    ((Over.map (f j)).obj (D.obj j))).hom ≫
      pullback.snd (f i) ((D.obj j).hom ≫ f j) = _ at hp
  simp only [DescentData.gluingPullbackIso, DescentData.gluingIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Over.forget_map,
    Category.assoc, Iso.hom_inv_id_assoc, transport, Over.comp_left, hp]

private lemma pullback_transport_left (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) {T : Over F.sourceBase}
    (i j : F.sourceFamily.I₀)
    (x : T ⟶ (Over.map (F.sourceFamily.f i)).obj
      ((MorphismOfSchemeFamilies.pulledBackDatum F D).obj i))
    (y : T ⟶ Over.mk (F.sourceFamily.f j)) :
    (transport (MorphismOfSchemeFamilies.pulledBackDatum F D) i j x y).left ≫
        (MorphismOfSchemeFamilies.pulledBackDatumObjIso F D j).hom.left ≫
        pullback.fst _ _ =
      pullback.lift
        (x.left ≫ (MorphismOfSchemeFamilies.pulledBackDatumObjIso F D i).hom.left ≫
          pullback.fst _ _)
        (y.left ≫ F.familyHom.h₀ j)
        (by
          simp only [Category.assoc, pullback.condition_assoc, F.familyHom.w₀]
          rw [← Over.pullback_obj_hom, Over.w_assoc]
          simpa only [Over.map_obj_hom, Over.mk_hom, Category.assoc] using
            congrArg (fun m ↦ m ≫ F.baseHom) ((Over.w x).trans (Over.w y).symm)) ≫
        (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).hom ≫
        pullback.snd _ _ := by
  have h := congrArg
    (fun m ↦ pullback.lift x.left y.left ((Over.w x).trans (Over.w y).symm) ≫
      m ≫ pullback.snd _ _) (MorphismOfSchemeFamilies.pulledBackDatum_gluing F D i j)
  rw [transport_left]
  simpa [MorphismOfSchemeFamilies.pulledBackDatumTargetMap,
    MorphismOfSchemeFamilies.pulledBackDatumSourceMap,
    Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd_assoc,
    pullback.lift_fst, pullback.lift_snd, comp_pullbackLift_assoc] using h

end

section
variable {I : Type u} {S : Scheme.{u}} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ S}

@[reassoc]
private lemma transport_chart (D : DescentData f) [∀ i, IsOpenImmersion (f i)]
    {T : Over S} (i j : I)
    (x : T ⟶ (Over.map (f i)).obj (D.obj i)) (y : T ⟶ Over.mk (f j)) :
    (transport D i j x y).left ≫ chartι D j = x.left ≫ chartι D i := by
  have h := congrArg (fun m ↦ (prod.lift x y).left ≫ m)
    ((schemeGlueData D).glue_condition i j)
  change (prod.lift x y).left ≫ (transition D i j).left ≫
      (prod.fst : overlap D j i ⟶ _).left ≫ chartι D j =
    (prod.lift x y).left ≫ (prod.fst : overlap D i j ⟶ _).left ≫
      chartι D i at h
  change (prod.lift x y ≫ transition D i j ≫ prod.fst).left ≫
      chartι D j =
    (prod.lift x y ≫ prod.fst).left ≫ chartι D i at h
  simpa only [transition, prod.lift_fst, transport_naturality, prod.lift_snd] using h

private lemma pullbackId_hom_left {X : Scheme.{u}} (Z : Over X) :
    (Over.pullbackId.app Z).hom.left = pullback.fst Z.hom (𝟙 X) := by
  show ((conjugateEquiv (Over.mapPullbackAdj (𝟙 X)) Adjunction.id
    (Over.mapId X).inv).app Z).left = _
  rw [conjugateEquiv_adjunction_id]
  simp [Over.mapId]

@[reassoc]
private lemma fibreComponentIso_hom_left {S : Scheme.{u}}
    (U V : PreZeroHypercover.{u} S) (α : U.HomOver V (𝟙 S))
    (D : DescentData U.f) (j : V.I₀) (i : {i : U.I₀ // α.s₀ i = j}) :
    (fibreComponentIso U V α D j i).hom.left =
      (MorphismOfSchemeFamilies.pulledBackDatumObjIso
        (fibreMorphism U V α j) D i).hom.left ≫ pullback.fst _ _ := by
  dsimp only [fibreComponentIso, Iso.trans_hom, Over.comp_left]
  rw [pullbackId_hom_left]

end

section
variable {S : Scheme.{u}} (U V : PreZeroHypercover.{u} S) (α : U.HomOver V (𝟙 S))

private abbrev fibreBaseMap (j : V.I₀) (i : {i : U.I₀ // α.s₀ i = j}) :
    Over.mk (U.f i.val) ⟶ Over.mk (V.f j) :=
  Over.homMk ((fibreFamily U V α j).f i) (by
    rcases i with ⟨i, h⟩
    subst j
    simpa [fibreFamily] using α.w₀ i)

private abbrev fibreDatum (D : DescentData U.f) (j : V.I₀) :=
  MorphismOfSchemeFamilies.pulledBackDatum (fibreMorphism U V α j) D

private def gluedFibre (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i)) (j : V.I₀) : Over (V.X j) :=
  Over.mk (@gluedToBase _ _ _ _ (fibreDatum U V α D j) (H j))

/-- The chart of the glued fibre over `V_j` indexed by `i`, with its target named as the
glued fibre itself rather than as the glued scheme of the fibre's glue data. -/
private def glueι (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i))
    (j : V.I₀) (i : {i : U.I₀ // α.s₀ i = j}) :
    ((Over.map ((fibreFamily U V α j).f i)).obj ((fibreDatum U V α D j).obj i)).left ⟶
      (gluedFibre U V α D H j).left :=
  @chartι _ _ _ _ (fibreDatum U V α D j) (H j) i

private lemma glueι_comp_hom (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i))
    (j : V.I₀) (i : {i : U.I₀ // α.s₀ i = j}) :
    glueι U V α D H j i ≫ (gluedFibre U V α D H j).hom =
      ((fibreDatum U V α D j).obj i).hom ≫ (fibreFamily U V α j).f i :=
  @chart_gluedToBase _ _ _ _ (fibreDatum U V α D j) (H j) i

private lemma glueι_isPullback (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i))
    (j : V.I₀) (i : {i : U.I₀ // α.s₀ i = j}) :
    IsPullback ((fibreDatum U V α D j).obj i).hom (glueι U V α D H j i)
      ((fibreFamily U V α j).f i) (gluedFibre U V α D H j).hom :=
  @chart_isPullback _ _ _ _ (fibreDatum U V α D j) (H j) i

private lemma glueι_jointly_surjective (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i))
    (j : V.I₀) (x : (gluedFibre U V α D H j).left) :
    ∃ (i : {i : U.I₀ // α.s₀ i = j})
      (y : ((Over.map ((fibreFamily U V α j).f i)).obj ((fibreDatum U V α D j).obj i)).left),
      glueι U V α D H j i y = x :=
  @chartι_jointly_surjective _ _ _ _ (fibreDatum U V α D j) (H j) x

private lemma transport_glueι (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i))
    (j : V.I₀) {T : Over (V.X j)} (i i' : {i : U.I₀ // α.s₀ i = j})
    (x : T ⟶ (Over.map ((fibreFamily U V α j).f i)).obj ((fibreDatum U V α D j).obj i))
    (y : T ⟶ Over.mk ((fibreFamily U V α j).f i')) :
    (transport (fibreDatum U V α D j) i i' x y).left ≫ glueι U V α D H j i' =
      x.left ≫ glueι U V α D H j i :=
  @transport_chart _ _ _ _ (fibreDatum U V α D j) (H j) _ i i' x y

/-- The underlying map of a fibre chart, as the chart of the glued fibre precomposed with
the comparison of the pulled-back component with the component of the original datum. -/
private def fibreChartLeft (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i))
    (j : V.I₀) (i : {i : U.I₀ // α.s₀ i = j}) :
    ((Over.map (U.f i.val)).obj (D.obj i.val)).left ⟶ (gluedFibre U V α D H j).left :=
  (fibreComponentIso U V α D j i).inv.left ≫ glueι U V α D H j i

private lemma fibreChartLeft_comp_hom (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i))
    (j : V.I₀) (i : {i : U.I₀ // α.s₀ i = j}) :
    fibreChartLeft U V α D H j i ≫ (gluedFibre U V α D H j).hom =
      (D.obj i.val).hom ≫ (fibreFamily U V α j).f i := by
  rw [fibreChartLeft, Category.assoc, glueι_comp_hom]
  exact Over.w_assoc (fibreComponentIso U V α D j i).inv _

private def fibreChart (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i))
    (j : V.I₀) (i : {i : U.I₀ // α.s₀ i = j}) :
    (Over.map (U.f i.val)).obj (D.obj i.val) ⟶
      (Over.map (V.f j)).obj (gluedFibre U V α D H j) :=
  Over.homMk (fibreChartLeft U V α D H j i) (by
    change fibreChartLeft U V α D H j i ≫ (gluedFibre U V α D H j).hom ≫ V.f j =
      (D.obj i.val).hom ≫ U.f i.val
    rw [← Category.assoc, fibreChartLeft_comp_hom, Category.assoc,
      show (fibreFamily U V α j).f i ≫ V.f j = U.f i.val from
        Over.w (fibreBaseMap U V α j i)])

/-- The underlying map of a fibre chart. -/
private lemma fibreChart_left (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i))
    (j : V.I₀) (i : {i : U.I₀ // α.s₀ i = j}) :
    (fibreChart U V α D H j i).left = fibreChartLeft U V α D H j i :=
  rfl

@[reassoc]
private lemma fibreChart_structure (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i))
    (j : V.I₀) (i : {i : U.I₀ // α.s₀ i = j}) :
    fibreChart U V α D H j i ≫ structureMap (V.f j) (gluedFibre U V α D H j) =
      structureMap (U.f i.val) (D.obj i.val) ≫ fibreBaseMap U V α j i := by
  apply Over.OverMorphism.ext
  show (fibreChart U V α D H j i).left ≫ (gluedFibre U V α D H j).hom =
    (D.obj i.val).hom ≫ (fibreFamily U V α j).f i
  rw [fibreChart_left, fibreChartLeft_comp_hom]

private lemma fibreChart_isPullback (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i))
    (j : V.I₀) (i : {i : U.I₀ // α.s₀ i = j}) :
    IsPullback (D.obj i.val).hom (fibreChart U V α D H j i).left
      ((fibreFamily U V α j).f i) (gluedFibre U V α D H j).hom :=
  (glueι_isPullback U V α D H j i).of_iso'
    ((Over.forget _).mapIso (fibreComponentIso U V α D j i).symm)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simpa using Over.w (fibreComponentIso U V α D j i).inv)
    (by simp [fibreChart_left, fibreChartLeft]) (by simp) (by rfl)

private lemma fibreChart_open (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i))
    (j : V.I₀) (i : {i : U.I₀ // α.s₀ i = j}) :
    IsOpenImmersion (fibreChart U V α D H j i).left :=
  MorphismProperty.of_isPullback (fibreChart_isPullback U V α D H j i) (H j i)

private lemma fibreChart_surj (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i))
    (j : V.I₀) (x : (gluedFibre U V α D H j).left) :
    ∃ i : {i : U.I₀ // α.s₀ i = j}, ∃ y : (D.obj i.val).left,
      (fibreChart U V α D H j i).left y = x := by
  obtain ⟨i, y, hy⟩ := glueι_jointly_surjective U V α D H j x
  refine ⟨i, (fibreComponentIso U V α D j i).hom.left y, ?_⟩
  rw [fibreChart_left, fibreChartLeft]
  have hh := congrArg (fun m => m y)
    (congrArg Over.Hom.left (fibreComponentIso U V α D j i).hom_inv_id)
  simp only [Over.comp_left, Over.id_left, Scheme.Hom.comp_apply] at hh ⊢
  rw [hh]
  exact hy

end

private lemma fibre_transport {S : Scheme.{u}}
    (U V : PreZeroHypercover.{u} S) (α : U.HomOver V (𝟙 S))
    (D : DescentData U.f) (j : V.I₀)
    (i i' : {i : U.I₀ // α.s₀ i = j}) {T : Over (V.X j)}
    (x : T ⟶ (Over.map ((fibreFamily U V α j).f i)).obj
      ((fibreDatum U V α D j).obj i))
    (y : T ⟶ Over.mk ((fibreFamily U V α j).f i'))
    (x' : (Over.map (V.f j)).obj T ⟶ (Over.map (U.f i.val)).obj (D.obj i.val))
    (y' : (Over.map (V.f j)).obj T ⟶ Over.mk (U.f i'.val))
    (hx : x'.left = x.left ≫ (fibreComponentIso U V α D j i).hom.left)
    (hy : y'.left = y.left) :
    (transport (fibreDatum U V α D j) i i' x y).left ≫
      (fibreComponentIso U V α D j i').hom.left =
      (transport D i.val i'.val x' y').left := by
  have h := pullback_transport_left (fibreMorphism U V α j) D i i' x y
  rw [fibreComponentIso_hom_left]
  refine h.trans ?_
  rw [transport_left D]
  apply congrArg (fun m ↦ m ≫ (D.gluingPullbackIso i.val i'.val).hom ≫ pullback.snd _ _)
  apply pullback.hom_ext
  · refine (pullback.lift_fst _ _ _).trans (Eq.trans ?_ (pullback.lift_fst _ _ _).symm)
    simpa only [fibreComponentIso_hom_left, Category.assoc] using hx.symm
  · refine (pullback.lift_snd _ _ _).trans (Eq.trans ?_ (pullback.lift_snd _ _ _).symm)
    simpa using hy.symm

private lemma fibreChart_compat {S : Scheme.{u}}
    (U V : PreZeroHypercover.{u} S) (α : U.HomOver V (𝟙 S))
    (D : DescentData U.f)
    (H : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i))
    (j : V.I₀) (i i' : {i : U.I₀ // α.s₀ i = j}) {T : Over S}
    (x : T ⟶ (Over.map (U.f i.val)).obj (D.obj i.val))
    (y : T ⟶ Over.mk (U.f i'.val))
    (h : x ≫ structureMap (U.f i.val) (D.obj i.val) ≫ fibreBaseMap U V α j i =
      y ≫ fibreBaseMap U V α j i') :
    transport D i.val i'.val x y ≫ fibreChart U V α D H j i' =
      x ≫ fibreChart U V α D H j i := by
  let : ∀ i, IsOpenImmersion ((fibreMorphism U V α j).sourceFamily.f i) := H j
  let t := x ≫ structureMap (U.f i.val) (D.obj i.val) ≫ fibreBaseMap U V α j i
  let T' : Over (V.X j) := Over.mk t.left
  let e : (Over.map (V.f j)).obj T' ⟶ T :=
    Over.homMk (𝟙 T.left) (by simpa [T'] using (Over.w t).symm)
  let xR : T' ⟶ (Over.map ((fibreFamily U V α j).f i)).obj
      ((fibreDatum U V α D j).obj i) :=
    Over.homMk (x.left ≫ (fibreComponentIso U V α D j i).inv.left) (by
      show (x.left ≫ _) ≫ (_ ≫ _) = _
      rw [Category.assoc, Over.w_assoc (fibreComponentIso U V α D j i).inv]
      rfl)
  let yR : T' ⟶ Over.mk ((fibreFamily U V α j).f i') :=
    Over.homMk y.left (congrArg Over.Hom.left h.symm)
  have he := fibre_transport U V α D j i i' xR yR (e ≫ x) (e ≫ y)
    (by
      show 𝟙 _ ≫ x.left = (x.left ≫ (fibreComponentIso U V α D j i).inv.left) ≫
        (fibreComponentIso U V α D j i).hom.left
      rw [Category.id_comp, Category.assoc, ← Over.comp_left, Iso.inv_hom_id,
        Over.id_left]
      exact (Category.comp_id x.left).symm)
    (by
      show 𝟙 _ ≫ y.left = y.left
      exact Category.id_comp _)
  have ht : (transport D i.val i'.val x y).left ≫
      (fibreComponentIso U V α D j i').inv.left =
      (transport (fibreDatum U V α D j) i i' xR yR).left := by
    rw [← transport_naturality] at he
    change (transport (fibreDatum U V α D j) i i' xR yR).left ≫
      (fibreComponentIso U V α D j i').hom.left =
      𝟙 T.left ≫ (transport D i.val i'.val x y).left at he
    rw [Category.id_comp] at he
    rw [← he, Category.assoc, ← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    exact Category.comp_id _
  apply Over.OverMorphism.ext
  show (transport D i.val i'.val x y).left ≫ (fibreChart U V α D H j i').left =
    x.left ≫ (fibreChart U V α D H j i).left
  rw [fibreChart_left, fibreChart_left, fibreChartLeft, fibreChartLeft,
    ← Category.assoc, ht, transport_glueι]
  exact Category.assoc x.left _ _

private structure OpenCoverOver {S : Scheme.{u}} (B : Over S) where
  I : Type u
  obj : I → Over S
  map : ∀ i, obj i ⟶ B
  isOpen : ∀ i, IsOpenImmersion (map i).left
  surj : ∀ x : B.left, ∃ i, ∃ y : (obj i).left, (map i).left y = x

namespace OpenCoverOver
variable {S : Scheme.{u}} {B : Over S}

private abbrev toCover (c : OpenCoverOver B) : B.left.OpenCover where
  I₀ := c.I
  X i := (c.obj i).left
  f i := (c.map i).left
  mem₀ := (Scheme.ofArrows_mem_precoverage_iff @IsOpenImmersion).2
    ⟨fun x ↦ by obtain ⟨i, y, h⟩ := c.surj x; exact ⟨i, y, h⟩, c.isOpen⟩

private lemma hom_ext (c : OpenCoverOver B) {Z : Over S} (f g : B ⟶ Z)
    (h : ∀ i, c.map i ≫ f = c.map i ≫ g) : f = g :=
  Over.OverMorphism.ext (c.toCover.hom_ext _ _ fun i ↦ congrArg Over.Hom.left (h i))

private lemma overlap_compatible (c : OpenCoverOver B) {Z : Over S}
    (m : ∀ i, c.obj i ⟶ Z)
    (hm : ∀ (T : Over S) (i j : c.I) (a : T ⟶ c.obj i) (b : T ⟶ c.obj j),
      a ≫ c.map i = b ≫ c.map j → a ≫ m i = b ≫ m j) (i j : c.I) :
    pullback.fst (c.map i).left (c.map j).left ≫ (m i).left =
      pullback.snd _ _ ≫ (m j).left := by
  let T : Over S :=
    Over.mk (pullback.fst (c.map i).left (c.map j).left ≫ (c.obj i).hom)
  let a : T ⟶ c.obj i := Over.homMk (pullback.fst (c.map i).left (c.map j).left)
  let b : T ⟶ c.obj j :=
    Over.homMk (pullback.snd (c.map i).left (c.map j).left) (by
      dsimp [T]
      rw [← Over.w (c.map i), ← Over.w (c.map j)]
      exact (pullback.condition_assoc (f := (c.map i).left) (g := (c.map j).left) B.hom).symm)
  exact congrArg Over.Hom.left (hm T i j a b
    (Over.OverMorphism.ext pullback.condition))

private def desc (c : OpenCoverOver B) {Z : Over S} (m : ∀ i, c.obj i ⟶ Z)
    (hm : ∀ (T : Over S) (i j : c.I) (a : T ⟶ c.obj i) (b : T ⟶ c.obj j),
      a ≫ c.map i = b ≫ c.map j → a ≫ m i = b ≫ m j) : B ⟶ Z :=
  Over.homMk (c.toCover.glueMorphisms (fun i ↦ (m i).left) (c.overlap_compatible m hm)) (by
    apply c.toCover.hom_ext
    intro i
    rw [← Category.assoc, c.toCover.ι_glueMorphisms (fun i ↦ (m i).left)
      (c.overlap_compatible m hm) i]
    exact (Over.w (m i)).trans (Over.w (c.map i)).symm)

@[reassoc]
private lemma map_desc (c : OpenCoverOver B) {Z : Over S} (m : ∀ i, c.obj i ⟶ Z)
    (hm : ∀ (T : Over S) (i j : c.I) (a : T ⟶ c.obj i) (b : T ⟶ c.obj j),
      a ≫ c.map i = b ≫ c.map j → a ≫ m i = b ≫ m j) (i : c.I) :
    c.map i ≫ c.desc m hm = m i := by
  apply Over.OverMorphism.ext
  show (c.map i).left ≫ c.toCover.glueMorphisms
    (fun i ↦ (m i).left) (c.overlap_compatible m hm) = (m i).left
  exact c.toCover.ι_glueMorphisms (fun i ↦ (m i).left) (c.overlap_compatible m hm) i

private abbrev baseChange (c : OpenCoverOver B) {T : Over S} (h : T ⟶ B) {A : c.I → Over S}
    (p : ∀ i, A i ⟶ c.obj i) (q : ∀ i, A i ⟶ T)
    (hp : ∀ i, IsPullback (p i) (q i) (c.map i) h) : OpenCoverOver T where
  I := c.I
  obj := A
  map := q
  isOpen i := MorphismProperty.of_isPullback ((hp i).map (Over.forget S)) (c.isOpen i)
  surj x := by
    obtain ⟨i, y, hy⟩ := c.surj (h.left x)
    obtain ⟨z, _, hz⟩ := Scheme.exists_preimage_of_isPullback
      ((hp i).map (Over.forget S)) y x hy
    exact ⟨i, z, hz⟩

private abbrev prodLeft (c : OpenCoverOver B) (Z : Over S) : OpenCoverOver (B ⨯ Z) :=
  c.baseChange prod.fst (fun _ ↦ prod.fst) (fun i ↦ prod.map (c.map i) (𝟙 Z))
    (fun i ↦ IsPullback.of_prod_fst_with_id (c.map i) Z)

private abbrev prodRight (c : OpenCoverOver B) (Z : Over S) : OpenCoverOver (Z ⨯ B) :=
  c.baseChange prod.snd (fun _ ↦ prod.snd) (fun i ↦ prod.map (𝟙 Z) (c.map i))
    (fun i ↦ by
      refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _
        (fun s ↦ prod.lift (s.snd ≫ prod.fst) s.fst) ?_ ?_ ?_⟩⟩
      · intro s; simp
      · intro s
        apply prod.hom_ext
        · simp
        · simpa using s.condition
      · intro s m h₁ h₂
        apply prod.hom_ext
        · simpa using congrArg (fun k ↦ k ≫ prod.fst) h₂
        · simpa using h₁)

private lemma prod_map_eq_comp (c : OpenCoverOver B) {Z : Over S} (d : OpenCoverOver Z)
    (i : c.I) (j : d.I) :
    Limits.prod.map (c.map i) (d.map j) =
      (d.prodRight (c.obj i)).map j ≫ (c.prodLeft Z).map i := by
  dsimp [prodLeft, prodRight, baseChange]
  simp

private abbrev prod (c : OpenCoverOver B) {Z : Over S} (d : OpenCoverOver Z) :
    OpenCoverOver (B ⨯ Z) where
  I := c.I × d.I
  obj i := c.obj i.1 ⨯ d.obj i.2
  map i := Limits.prod.map (c.map i.1) (d.map i.2)
  isOpen i := by
    have hc := (c.prodLeft Z).isOpen i.1
    have hd := (d.prodRight (c.obj i.1)).isOpen i.2
    rw [prod_map_eq_comp, Over.comp_left]
    exact IsOpenImmersion.comp _ _
  surj x := by
    obtain ⟨i, y, hy⟩ := (c.prodLeft Z).surj x
    obtain ⟨j, z, hz⟩ := (d.prodRight (c.obj i)).surj y
    refine ⟨⟨i, j⟩, z, ?_⟩
    rw [prod_map_eq_comp, Over.comp_left, Scheme.Hom.comp_apply, hz, hy]

end OpenCoverOver

private structure RefinementGluing {S : Scheme.{u}} (U V : PreZeroHypercover.{u} S)
    (α : U.HomOver V (𝟙 S)) (D : DescentData U.f) where
  obj : ∀ j, Over (V.X j)
  chart : ∀ j (i : {i : U.I₀ // α.s₀ i = j}),
    (Over.map (U.f i.val)).obj (D.obj i.val) ⟶ (Over.map (V.f j)).obj (obj j)
  chart_structure : ∀ j i, chart j i ≫ structureMap (V.f j) (obj j) =
    structureMap (U.f i.val) (D.obj i.val) ≫ fibreBaseMap U V α j i
  chart_open : ∀ j i, IsOpenImmersion (chart j i).left
  chart_surj : ∀ j (x : (obj j).left), ∃ i : {i : U.I₀ // α.s₀ i = j},
    ∃ y : (D.obj i.val).left, (chart j i).left y = x
  cartesian : ∀ j i, IsPullback (D.obj i.val).hom (chart j i).left
    ((fibreFamily U V α j).f i) (obj j).hom
  base_open : ∀ j i, IsOpenImmersion ((fibreFamily U V α j).f i)
  base_surj : ∀ j (x : V.X j), ∃ i : {i : U.I₀ // α.s₀ i = j},
    ∃ y : U.X i.val, ((fibreFamily U V α j).f i) y = x
  compat : ∀ j (i i' : {i : U.I₀ // α.s₀ i = j}) (T : Over S)
    (x : T ⟶ (Over.map (U.f i.val)).obj (D.obj i.val)) (y : T ⟶ Over.mk (U.f i'.val)),
    x ≫ structureMap (U.f i.val) (D.obj i.val) ≫ fibreBaseMap U V α j i =
      y ≫ fibreBaseMap U V α j i' →
    transport D i.val i'.val x y ≫ chart j i' = x ≫ chart j i

namespace RefinementGluing
variable {S : Scheme.{u}} {U V : PreZeroHypercover.{u} S} {α : U.HomOver V (𝟙 S)}
    {D : DescentData U.f}

private abbrev total (R : RefinementGluing U V α D) (j : V.I₀) :=
  (Over.map (V.f j)).obj (R.obj j)
private abbrev base (j : V.I₀) := Over.mk (V.f j)
private abbrev structureMap (R : RefinementGluing U V α D) (j : V.I₀) :
    R.total j ⟶ base j := _root_.AlgebraicGeometry.structureMap (V.f j) (R.obj j)

private abbrev chartCover (R : RefinementGluing U V α D) (j : V.I₀) :
    OpenCoverOver (R.total j) where
  I := {i : U.I₀ // α.s₀ i = j}
  obj i := (Over.map (U.f i.val)).obj (D.obj i.val)
  map := R.chart j
  isOpen := R.chart_open j
  surj := R.chart_surj j

private abbrev baseCover (R : RefinementGluing U V α D) (j : V.I₀) :
    OpenCoverOver (base j) where
  I := {i : U.I₀ // α.s₀ i = j}
  obj i := Over.mk (U.f i.val)
  map := fibreBaseMap U V α j
  isOpen := R.base_open j
  surj := R.base_surj j

private lemma chart_mono (R : RefinementGluing U V α D) (j : V.I₀)
    (i : {i : U.I₀ // α.s₀ i = j}) : Mono (R.chart j i) := by
  have := R.chart_open j i
  exact (Over.forget S).mono_of_mono_map (inferInstance : Mono (R.chart j i).left)

private lemma chart_relation (R : RefinementGluing U V α D) (j : V.I₀)
    (i i' : {i : U.I₀ // α.s₀ i = j}) {T : Over S}
    (x : T ⟶ (Over.map (U.f i.val)).obj (D.obj i.val))
    (x' : T ⟶ (Over.map (U.f i'.val)).obj (D.obj i'.val))
    (h : x ≫ R.chart j i = x' ≫ R.chart j i') :
    transport D i.val i'.val x
      (x' ≫ _root_.AlgebraicGeometry.structureMap (U.f i'.val) (D.obj i'.val)) = x' := by
  have := R.chart_mono j i'
  apply (cancel_mono (R.chart j i')).mp
  rw [R.compat j i i' T x _]
  · exact h
  · have he := congrArg (fun m ↦ m ≫ R.structureMap j) h
    simpa only [Category.assoc, R.chart_structure] using he

private abbrev localTransition (R : RefinementGluing U V α D) (j k : V.I₀)
    (i : {i : U.I₀ // α.s₀ i = j}) (l : {i : U.I₀ // α.s₀ i = k}) :
    (Over.map (U.f i.val)).obj (D.obj i.val) ⨯ Over.mk (U.f l.val) ⟶ R.total k :=
  transport D i.val l.val prod.fst prod.snd ≫ R.chart k l

private lemma localTransition_compatible (R : RefinementGluing U V α D) (j k : V.I₀)
    (T : Over S) (p q : ((R.chartCover j).prod (R.baseCover k)).I)
    (a : T ⟶ ((R.chartCover j).prod (R.baseCover k)).obj p)
    (b : T ⟶ ((R.chartCover j).prod (R.baseCover k)).obj q)
    (h : a ≫ ((R.chartCover j).prod (R.baseCover k)).map p =
      b ≫ ((R.chartCover j).prod (R.baseCover k)).map q) :
    a ≫ R.localTransition j k p.1 p.2 = b ≫ R.localTransition j k q.1 q.2 := by
  have h₁ : (a ≫ prod.fst) ≫ R.chart j p.1 = (b ≫ prod.fst) ≫ R.chart j q.1 := by
    simpa using congrArg (fun m ↦ m ≫ prod.fst) h
  have h₂ : (a ≫ prod.snd) ≫ fibreBaseMap U V α k p.2 =
      (b ≫ prod.snd) ≫ fibreBaseMap U V α k q.2 := by
    simpa using congrArg (fun m ↦ m ≫ prod.snd) h
  have hs := R.chart_relation j p.1 q.1 (a ≫ prod.fst) (b ≫ prod.fst) h₁
  have ht := R.compat k p.2 q.2 T
    (transport D p.1.val p.2.val (a ≫ prod.fst) (a ≫ prod.snd))
    (b ≫ prod.snd) (by simpa only [Category.assoc, transport_structure_assoc] using h₂)
  dsimp only [localTransition]
  simp only [transport_naturality_assoc]
  rw [← ht, transport_comp, ← transport_comp D p.1.val q.1.val q.2.val
    (a ≫ prod.fst) ((b ≫ prod.fst) ≫
      _root_.AlgebraicGeometry.structureMap (U.f q.1.val) (D.obj q.1.val))
    (b ≫ prod.snd), hs]

private def transitionMap (R : RefinementGluing U V α D) (j k : V.I₀) :
    R.total j ⨯ base k ⟶ R.total k :=
  ((R.chartCover j).prod (R.baseCover k)).desc
    (fun p ↦ R.localTransition j k p.1 p.2) (R.localTransition_compatible j k)

@[reassoc]
private lemma chart_transitionMap (R : RefinementGluing U V α D) (j k : V.I₀)
    (i : {i : U.I₀ // α.s₀ i = j}) (l : {i : U.I₀ // α.s₀ i = k}) :
    prod.map (R.chart j i) (fibreBaseMap U V α k l) ≫ R.transitionMap j k =
      transport D i.val l.val prod.fst prod.snd ≫ R.chart k l :=
  ((R.chartCover j).prod (R.baseCover k)).map_desc _ _ (i, l)

private def transport (R : RefinementGluing U V α D) {T : Over S} (j k : V.I₀)
    (x : T ⟶ R.total j) (y : T ⟶ base k) : T ⟶ R.total k :=
  prod.lift x y ≫ R.transitionMap j k

@[reassoc]
private lemma transport_naturality (R : RefinementGluing U V α D) {T T' : Over S}
    (p : T' ⟶ T) (j k : V.I₀) (x : T ⟶ R.total j) (y : T ⟶ base k) :
    p ≫ R.transport j k x y = R.transport j k (p ≫ x) (p ≫ y) := by
  simp only [transport, prod.comp_lift_assoc]

private lemma transport_chart (R : RefinementGluing U V α D) {T : Over S} (j k : V.I₀)
    (i : {i : U.I₀ // α.s₀ i = j}) (l : {i : U.I₀ // α.s₀ i = k})
    (x : T ⟶ (Over.map (U.f i.val)).obj (D.obj i.val))
    (y : T ⟶ Over.mk (U.f l.val)) :
    R.transport j k (x ≫ R.chart j i) (y ≫ fibreBaseMap U V α k l) =
      _root_.AlgebraicGeometry.ZariskiRefinement.transport D i.val l.val x y ≫ R.chart k l := by
  have h := congrArg (fun m ↦ prod.lift x y ≫ m) (R.chart_transitionMap j k i l)
  simpa only [transport, Category.assoc, prod.lift_map_assoc, prod.lift_fst, prod.lift_snd,
    _root_.AlgebraicGeometry.ZariskiRefinement.transport_naturality_assoc] using h

@[reassoc]
private lemma transitionMap_structure (R : RefinementGluing U V α D) (j k : V.I₀) :
    R.transitionMap j k ≫ R.structureMap k = prod.snd := by
  apply ((R.chartCover j).prod (R.baseCover k)).hom_ext
  rintro ⟨i, l⟩
  show prod.map (R.chart j i) (fibreBaseMap U V α k l) ≫ _ = _
  rw [R.chart_transitionMap_assoc, R.chart_structure]
  simp only [_root_.AlgebraicGeometry.ZariskiRefinement.transport_structure_assoc, prod.map_snd]

@[reassoc]
private lemma transport_structure (R : RefinementGluing U V α D) {T : Over S}
    (j k : V.I₀) (x : T ⟶ R.total j) (y : T ⟶ base k) :
    R.transport j k x y ≫ R.structureMap k = y := by
  simp only [transport, Category.assoc, transitionMap_structure, prod.lift_snd]

private lemma transport_self (R : RefinementGluing U V α D) {T : Over S}
    (j : V.I₀) (x : T ⟶ R.total j) :
    R.transport j j x (x ≫ R.structureMap j) = x := by
  have hs : R.transport j j (𝟙 _) (R.structureMap j) = 𝟙 _ := by
    apply (R.chartCover j).hom_ext
    intro i
    show R.chart j i ≫ _ = R.chart j i ≫ 𝟙 _
    rw [transport_naturality, Category.comp_id, R.chart_structure]
    have h := R.transport_chart j j i i (𝟙 _)
      (_root_.AlgebraicGeometry.structureMap (U.f i.val) (D.obj i.val))
    have hd : _root_.AlgebraicGeometry.ZariskiRefinement.transport D i.val i.val (𝟙 _)
        (_root_.AlgebraicGeometry.structureMap (U.f i.val) (D.obj i.val)) = 𝟙 _ := by
      simpa only [Category.id_comp] using
        _root_.AlgebraicGeometry.ZariskiRefinement.transport_self D i.val (𝟙 _)
    simpa only [Category.id_comp, hd] using h
  have h := congrArg (fun m ↦ x ≫ m) hs
  simpa only [transport_naturality, Category.comp_id] using h

private lemma transport_comp (R : RefinementGluing U V α D) {T : Over S}
    (j k l : V.I₀) (x : T ⟶ R.total j) (y : T ⟶ base k) (z : T ⟶ base l) :
    R.transport k l (R.transport j k x y) z = R.transport j l x z := by
  have hs : R.transport k l
      (R.transport j k (prod.fst ≫ prod.fst) (prod.fst ≫ prod.snd))
      (prod.snd : (R.total j ⨯ base k) ⨯ base l ⟶ _) =
      R.transport j l (prod.fst ≫ prod.fst) prod.snd := by
    apply (((R.chartCover j).prod (R.baseCover k)).prod (R.baseCover l)).hom_ext
    rintro ⟨⟨i, m⟩, n⟩
    show prod.map (prod.map (R.chart j i) (fibreBaseMap U V α k m))
      (fibreBaseMap U V α l n) ≫ _ = _
    simp only [transport_naturality, prod.map_fst_assoc, prod.map_fst, prod.map_snd]
    simp only [← Category.assoc, transport_chart,
      _root_.AlgebraicGeometry.ZariskiRefinement.transport_comp]
  have h := congrArg (fun m ↦ prod.lift (prod.lift x y) z ≫ m) hs
  simpa only [transport_naturality, prod.lift_fst_assoc, prod.lift_fst, prod.lift_snd] using h

private def gluingIso (R : RefinementGluing U V α D) (j k : V.I₀) :
    R.total j ⨯ base k ≅ base j ⨯ R.total k where
  hom := prod.lift (prod.fst ≫ R.structureMap j) (R.transport j k prod.fst prod.snd)
  inv := prod.lift (R.transport k j prod.snd prod.fst) (prod.snd ≫ R.structureMap k)
  hom_inv_id := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst,
        prod.lift_snd, transport_naturality, transport_comp, transport_self, Category.id_comp]
    · simp only [Category.assoc, prod.lift_snd, prod.lift_snd_assoc,
        transport_structure, Category.id_comp]
  inv_hom_id := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.lift_fst, prod.lift_fst_assoc,
        transport_structure, Category.id_comp]
    · simp only [Category.assoc, prod.lift_snd,
        prod.lift_fst, transport_naturality, transport_comp, transport_self, Category.id_comp]

private abbrev datum (R : RefinementGluing U V α D) : DescentData V.f where
  obj := R.obj
  gluing j k := Over.isoMk (R.gluingIso j k) (by
    apply prod.hom_ext
    · simp [gluingIso]
    · simp [gluingIso, transport_structure])
  cocycle j k l := by
    apply prod.hom_ext
    · apply prod.hom_ext
      · simp [gluingIso, prodMapLastTwo, prodMapFirstThird]
      · simp [gluingIso, prodMapLastTwo, prodMapFirstThird, transport_structure]
    · simp [gluingIso, prodMapLastTwo, prodMapFirstThird, transport_naturality, transport_comp]

private lemma datum_transport (R : RefinementGluing U V α D) {T : Over S}
    (j k : V.I₀) (x : T ⟶ R.total j) (y : T ⟶ base k) :
    _root_.AlgebraicGeometry.ZariskiRefinement.transport R.datum j k x y = R.transport j k x y := by
  simp [_root_.AlgebraicGeometry.ZariskiRefinement.transport, datum, gluingIso,
    transport_naturality]

private abbrev familyMorphism : MorphismOfSchemeFamilies.{u} :=
  { sourceBase := S, targetBase := S, sourceFamily := U, targetFamily := V,
    baseHom := 𝟙 S, familyHom := α }

private abbrev pullbackDatum (R : RefinementGluing U V α D) :=
  MorphismOfSchemeFamilies.pulledBackDatum (familyMorphism (α := α)) R.datum

private abbrev projection (R : RefinementGluing U V α D) (i : U.I₀) :
    (Over.map (U.f i)).obj (R.pullbackDatum.obj i) ⟶ R.total (α.s₀ i) :=
  Over.homMk ((MorphismOfSchemeFamilies.pulledBackDatumObjIso
    (familyMorphism (α := α)) R.datum i).hom.left ≫ pullback.fst _ _) (by
      change (_ ≫ _) ≫ ((R.obj (α.s₀ i)).hom ≫ V.f (α.s₀ i)) = _
      simp only [Category.assoc, pullback.condition_assoc, α.w₀, Category.comp_id]
      rw [← Over.pullback_obj_hom, Over.w_assoc]
      rfl)

private lemma projection_isPullback (R : RefinementGluing U V α D) (i : U.I₀) :
    IsPullback (R.pullbackDatum.obj i).hom (R.projection i).left
      (α.h₀ i) (R.obj (α.s₀ i)).hom := by
  let e := MorphismOfSchemeFamilies.pulledBackDatumObjIso (familyMorphism (α := α)) R.datum i
  apply IsPullback.flip
  exact (IsPullback.of_hasPullback (R.obj (α.s₀ i)).hom (α.h₀ i)).of_iso'
    ((Over.forget _).mapIso e) (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [projection, e])
    (by simpa only [Functor.mapIso_hom, Over.forget_map, Iso.refl_hom,
      Category.comp_id, Over.pullback_obj_hom] using Over.w e.hom)
    (by simp) (by simp)

private def componentIso (R : RefinementGluing U V α D) (i : U.I₀) :
    R.pullbackDatum.obj i ≅ D.obj i := by
  have hc : IsPullback (D.obj i).hom (R.chart (α.s₀ i) ⟨i, rfl⟩).left
      (α.h₀ i) (R.obj (α.s₀ i)).hom := by
    simpa [fibreFamily] using R.cartesian (α.s₀ i) ⟨i, rfl⟩
  exact Over.isoMk ((R.projection_isPullback i).isoIsPullback _ _ hc)
    (IsPullback.isoIsPullback_hom_fst _ _ _ _)

@[reassoc]
private lemma componentIso_hom_chart (R : RefinementGluing U V α D) (i : U.I₀) :
    (Over.map (U.f i)).map (R.componentIso i).hom ≫ R.chart (α.s₀ i) ⟨i, rfl⟩ =
      R.projection i :=
  Over.OverMorphism.ext (IsPullback.isoIsPullback_hom_snd _ _ _ _)

private lemma projection_transport (R : RefinementGluing U V α D) {T : Over S}
    (i l : U.I₀) (x : T ⟶ (Over.map (U.f i)).obj (R.pullbackDatum.obj i))
    (y : T ⟶ Over.mk (U.f l)) :
    _root_.AlgebraicGeometry.ZariskiRefinement.transport R.pullbackDatum i l x y ≫ R.projection l =
      R.transport (α.s₀ i) (α.s₀ l) (x ≫ R.projection i)
        (y ≫ fibreBaseMap U V α (α.s₀ l) ⟨l, rfl⟩) := by
  rw [← datum_transport]
  apply Over.OverMorphism.ext
  have h := pullback_transport_left (familyMorphism (α := α)) R.datum i l x y
  show (_root_.AlgebraicGeometry.ZariskiRefinement.transport
    R.pullbackDatum i l x y).left ≫ _ ≫ _ = _
  rw [_root_.AlgebraicGeometry.ZariskiRefinement.transport_left R.datum]
  refine h.trans ?_
  apply congrArg (fun m ↦ m ≫ (R.datum.gluingPullbackIso (α.s₀ i) (α.s₀ l)).hom ≫
    pullback.snd _ _)
  apply pullback.hom_ext
  · exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
  · exact (pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm

private def componentHom (R : RefinementGluing U V α D) : R.pullbackDatum ⟶ D where
  hom i := (R.componentIso i).hom
  comm i l := by
    apply prod.hom_ext
    · simp only [Category.assoc, prod.map_fst, prod.map_fst_assoc,
        DescentData.gluing_hom_fst, DescentData.gluing_hom_fst_assoc]
      apply congrArg (fun m ↦ prod.fst ≫ m)
      apply Over.OverMorphism.ext
      exact Over.w (R.componentIso i).hom
    · have := R.chart_mono (α.s₀ l) ⟨l, rfl⟩
      apply (cancel_mono (R.chart (α.s₀ l) ⟨l, rfl⟩)).mp
      change (prod.map ((Over.map (U.f i)).map (R.componentIso i).hom) (𝟙 _) ≫
          (D.gluing i l).hom.left ≫ prod.snd) ≫ R.chart (α.s₀ l) ⟨l, rfl⟩ =
        ((R.pullbackDatum.gluing i l).hom.left ≫
          prod.map (𝟙 _) ((Over.map (U.f l)).map (R.componentIso l).hom) ≫ prod.snd) ≫ _
      have ht := R.transport_chart (α.s₀ i) (α.s₀ l) ⟨i, rfl⟩ ⟨l, rfl⟩
        (prod.fst ≫ (Over.map (U.f i)).map (R.componentIso i).hom) prod.snd
      simp only [Category.assoc, componentIso_hom_chart] at ht
      rw [← R.projection_transport i l prod.fst prod.snd] at ht
      have hm : prod.lift (prod.fst ≫ (Over.map (U.f i)).map (R.componentIso i).hom)
          (prod.snd : (Over.map (U.f i)).obj (R.pullbackDatum.obj i) ⨯ Over.mk (U.f l) ⟶ _) =
          prod.map ((Over.map (U.f i)).map (R.componentIso i).hom) (𝟙 (Over.mk (U.f l))) := by
        apply prod.hom_ext <;> simp
      simpa only [_root_.AlgebraicGeometry.ZariskiRefinement.transport, Category.assoc, hm,
        prod.map_snd,
        ← prod.comp_lift_assoc, prod.map_fst, prod.map_snd, Category.comp_id,
        prod.lift_fst_snd, Category.id_comp, componentIso_hom_chart] using ht.symm

private def pullbackIso (R : RefinementGluing U V α D) : R.pullbackDatum ≅ D where
  hom := R.componentHom
  inv :=
    { hom := fun i ↦ (R.componentIso i).inv
      comm := by
        intro i l
        let A := prod.mapIso ((Over.map (U.f i)).mapIso (R.componentIso i))
          (Iso.refl (Over.mk (U.f l)))
        let B := prod.mapIso (Iso.refl (Over.mk (U.f i)))
          ((Over.map (U.f l)).mapIso (R.componentIso l))
        change A.inv ≫ (R.pullbackDatum.gluing i l).hom.left =
          (D.gluing i l).hom.left ≫ B.inv
        have h : A.hom ≫ (D.gluing i l).hom.left =
            (R.pullbackDatum.gluing i l).hom.left ≫ B.hom := R.componentHom.comm i l
        apply (cancel_epi A.hom).mp
        rw [← Category.assoc, A.hom_inv_id, Category.id_comp, ← Category.assoc,
          h, Category.assoc, B.hom_inv_id]
        exact (Category.comp_id _).symm }
  hom_inv_id := by
    apply DescentData.hom_ext
    intro i
    exact (R.componentIso i).hom_inv_id
  inv_hom_id := by
    apply DescentData.hom_ext
    intro i
    exact (R.componentIso i).inv_hom_id

end RefinementGluing

end ZariskiRefinement

open ZariskiRefinement

/-- A fibrewise Zariski refinement induces an equivalence on descent data. -/
@[stacks 02VY]
public theorem pullbackFunctor_isEquivalence_of_zariskiRefinement
    {S : Scheme.{u}} (U V : PreZeroHypercover.{u} S)
    (α : U.HomOver V (𝟙 S))
    (hZar : ∀ j : V.I₀,
      Presieve.ofArrows
        (fun i : {i : U.I₀ // α.s₀ i = j} ↦ U.X i)
        (fun i ↦ α.h₀ i.val ≫ eqToHom (congrArg V.X i.property)) ∈
          Scheme.zariskiPrecoverage (V.X j)) :
    Nonempty ((MorphismOfSchemeFamilies.pullbackFunctor
      { sourceBase := S, targetBase := S,
        sourceFamily := U, targetFamily := V,
        baseHom := 𝟙 S, familyHom := α }).functor.IsEquivalence) := by
  let F : MorphismOfSchemeFamilies.{u} :=
    { sourceBase := S, targetBase := S,
      sourceFamily := U, targetFamily := V,
      baseHom := 𝟙 S, familyHom := α }
  have hfpqc : ∀ j : V.I₀,
      Presieve.ofArrows
        (fun i : {i : U.I₀ // α.s₀ i = j} ↦ U.X i)
        (fun i ↦ α.h₀ i.val ≫ eqToHom (congrArg V.X i.property)) ∈
          Scheme.fpqcPrecoverage (V.X j) :=
    fun j ↦ Scheme.zariskiPrecoverage_le_fpqcPrecoverage _ (hZar j)
  obtain ⟨hff⟩ :=
    pullbackFunctor_fullyFaithful_of_fpqcRefinement U V α hfpqc
  let G := MorphismOfSchemeFamilies.pullbackFunctor F
  have hff' : G.functor.FullyFaithful := by
    simpa [G, F] using hff
  show Nonempty (G.functor.IsEquivalence)
  refine ⟨{ faithful := hff'.faithful, full := hff'.full, essSurj := ?_ }⟩
  refine ⟨fun D ↦ ?_⟩
  let H (j : V.I₀) : ∀ i, IsOpenImmersion ((fibreFamily U V α j).f i) :=
    (zariskiCover_data _ (hZar j)).2
  let W : RefinementGluing U V α D :=
    { obj := gluedFibre U V α D H
      chart := fibreChart U V α D H
      chart_structure := fibreChart_structure U V α D H
      chart_open := fibreChart_open U V α D H
      chart_surj := fibreChart_surj U V α D H
      cartesian := fibreChart_isPullback U V α D H
      base_open := H
      base_surj := fun j x ↦ (zariskiCover_data _ (hZar j)).1 x
      compat := fun j i i' T x y h ↦ fibreChart_compat U V α D H j i i' x y h }
  exact ⟨W.datum, ⟨eqToIso (G.obj_eq W.datum) ≪≫ W.pullbackIso⟩⟩

/-- Schemes over a base are equivalent to descent data for any Zariski cover. -/
@[stacks 02VY]
public theorem descentData_equivalence_of_zariskiCovering
    {S : Scheme.{u}} (U : PreZeroHypercover.{u} S)
    (hZar : Presieve.ofArrows U.X U.f ∈ Scheme.zariskiPrecoverage S) :
    Nonempty (Over S ≌ DescentData U.f) := by
  let V : PreZeroHypercover.{u} S :=
    { I₀ := PUnit.{u+1}, X := fun _ ↦ S, f := fun _ ↦ 𝟙 S }
  let α : U.HomOver V (𝟙 S) :=
    { s₀ := fun _ ↦ PUnit.unit
      h₀ := U.f
      w₀ := fun _ ↦ by simp [V] }
  have hcover : ∀ j : V.I₀,
      Presieve.ofArrows
        (fun i : {i : U.I₀ // α.s₀ i = j} ↦ U.X i)
        (fun i ↦ α.h₀ i.val ≫ eqToHom (congrArg V.X i.property)) ∈
          Scheme.zariskiPrecoverage (V.X j) := by
    rintro ⟨⟩
    apply (Scheme.ofArrows_mem_precoverage_iff @IsOpenImmersion).2
    obtain ⟨hsurj, hopen⟩ := zariskiCover_data U.f hZar
    refine ⟨fun x ↦ ?_, fun i ↦ by simpa [α, V] using hopen i.val⟩
    obtain ⟨i, hi⟩ := hsurj x
    exact ⟨⟨i, rfl⟩, by simpa [α, V] using hi⟩
  obtain ⟨hF⟩ := pullbackFunctor_isEquivalence_of_zariskiRefinement U V α hcover
  let := hF
  exact ⟨(identityDescentEquivalence S).trans
    (MorphismOfSchemeFamilies.pullbackFunctor
      { sourceBase := S, targetBase := S,
        sourceFamily := U, targetFamily := V,
        baseHom := 𝟙 S, familyHom := α }).functor.asEquivalence⟩

end AlgebraicGeometry

end
