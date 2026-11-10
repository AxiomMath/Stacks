module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidInSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Quotients.InvariantBaseChange

/-!
# A groupoid over an invariant target

Let `G` be a groupoid in algebraic spaces over `B` and let `φ` be a morphism from its object
space to an algebraic space `X` over `B`. If `φ` is invariant under the pre-relation `(t, s)`
of `G`, then the very same spaces and structure morphisms form a groupoid over `X`: the only
thing that changes is the structure morphism to the base, which becomes `φ`, and the arrow
space maps to `X` through the source map.

## Main definitions

* `AlgebraicGeometry.GroupoidInAlgebraicSpaces.overInvariantTarget`: **Stacks 048G**, the
  groupoid over the invariant target, bundled with the two equations which identify it — its
  underlying groupoid in presheaves is unchanged, and its structure morphism on objects is
  `φ`.

## Implementation notes

The invariance hypothesis is `AlgebraicGeometry.Space.IsInvariant` of **Stacks 048E**, taken
against the pre-relation `AlgebraicGeometry.Space.groupoidPreRelation` of **Stacks 043X**,
which lives in the slice of presheaves over the underlying presheaf of `B`; invariance is
therefore an equation of presheaf morphisms obtained from `φ` by forgetting algebraicity, and
it is equivalent to the equation `G.target ≫ φ = G.source ≫ φ` of morphisms of algebraic
spaces.

The structure of a groupoid in algebraic spaces requires its composition morphism on the
*chosen* fibre product `R ×_{s, U, t} R` of **Stacks 02X2**, whereas the pointwise groupoid
law speaks about the presheaf of composable pairs. The two are compared by
`AlgebraicGeometry.composableToPullback`, which is a split epimorphism because the presheaf
pullback is computed pointwise; splitting it is what reduces the new compatibility
`comp ≫ arrowsToX = pr₁ ≫ arrowsToX` to the pointwise statement that the composite of a
composable pair has the target of its first arrow, which is
`Deformation.PointwiseGroupoid.target_comp`.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 043X](https://stacks.math.columbia.edu/tag/043X)
* [Stacks Project, Tag 048G](https://stacks.math.columbia.edu/tag/048G)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS}

/-- The composite of a composable pair of arrows of a groupoid in algebraic spaces has the
same target as the first arrow of the pair. -/
theorem target_comp (G : GroupoidInAlgebraicSpaces C S hS B)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : {p : G.arrows.obj.obj T × G.arrows.obj.obj T //
      G.source.hom.app T p.1 = G.target.hom.app T p.2}) :
    G.target.hom.app T (G.toGroupoidInFunctors.comp.app T p) =
      G.target.hom.app T p.1.1 :=
  (G.toGroupoidInFunctors.pointwiseData T).target_comp p.1.1 p.1.2 p.2

/-- **Stacks 048G.** A morphism out of the object space of a groupoid in algebraic spaces
which is invariant under the pre-relation of the groupoid makes the groupoid a groupoid over
its target: the object and arrow spaces, the source, the target and the composition are
unchanged, and the new structure morphism on objects is the invariant morphism itself. -/
@[stacks 048G "groupoid_over_x"]
noncomputable def overInvariantTarget (G : GroupoidInAlgebraicSpaces C S hS B)
    {X : AlgebraicSpaces C S hS} (XtoB : X ⟶ B) (φ : G.objects ⟶ X)
    (_hφB : φ ≫ XtoB = G.objectsToBase)
    (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom) :
    { H : GroupoidInAlgebraicSpaces C S hS X //
      H.toGroupoidInFunctors = G.toGroupoidInFunctors ∧
      ∃ hobj : H.objects = G.objects, eqToHom hobj.symm ≫ H.objectsToBase = φ } := by
  have hφ' : G.target.hom ≫ φ.hom = G.source.hom ≫ φ.hom := by
    simpa [Space.IsInvariant, Space.groupoidPreRelation] using hφ
  let arrowsToX : G.arrows ⟶ X := G.source ≫ φ
  have compOverX : G.comp ≫ arrowsToX =
      (ObjectProperty.homMk (pullback.fst G.source.hom G.target.hom) :
        AlgebraicSpaces.fiberProduct C S hS G.source G.target ⟶ G.arrows) ≫ arrowsToX := by
    apply ObjectProperty.hom_ext
    let ι := composableToPullback G.source.hom G.target.hom
    let ρ : pullback G.source.hom G.target.hom ⟶
        Deformation.composableArrows G.objects.obj G.arrows.obj G.source.hom G.target.hom :=
      { app := fun T => ↾ fun q => ⟨
          ((pullback.fst G.source.hom G.target.hom).app T q,
            (pullback.snd G.source.hom G.target.hom).app T q), by
              have hcond : pullback.fst G.source.hom G.target.hom ≫ G.source.hom =
                  pullback.snd G.source.hom G.target.hom ≫ G.target.hom := pullback.condition
              have h : ((pullback.fst G.source.hom G.target.hom ≫ G.source.hom).app T) q =
                  ((pullback.snd G.source.hom G.target.hom ≫ G.target.hom).app T) q :=
                congrArg (fun f => (f.app T) q) hcond
              simpa using h⟩
        naturality := by
          intro T T' f
          ext q
          apply Subtype.ext
          simp [Deformation.composableArrows, NatTrans.naturality_apply] }
    let π₁ : Deformation.composableArrows G.objects.obj G.arrows.obj
        G.source.hom G.target.hom ⟶ G.arrows.obj :=
      { app := fun _ => ↾ fun p => p.1.1
        naturality := by intros; ext p; rfl }
    let π₂ : Deformation.composableArrows G.objects.obj G.arrows.obj
        G.source.hom G.target.hom ⟶ G.arrows.obj :=
      { app := fun _ => ↾ fun p => p.1.2
        naturality := by intros; ext p; rfl }
    have hι₁ : ι ≫ pullback.fst G.source.hom G.target.hom = π₁ := by
      simp [π₁, ι, composableToPullback]
    have hι₂ : ι ≫ pullback.snd G.source.hom G.target.hom = π₂ := by
      simp [π₂, ι, composableToPullback]
    have hρι : ρ ≫ ι = 𝟙 _ := by
      refine pullback.hom_ext ?_ ?_
      · calc
          ρ ≫ ι ≫ pullback.fst G.source.hom G.target.hom = ρ ≫ π₁ := by rw [hι₁]
          _ = pullback.fst G.source.hom G.target.hom := by ext T q; rfl
      · calc
          ρ ≫ ι ≫ pullback.snd G.source.hom G.target.hom = ρ ≫ π₂ := by rw [hι₂]
          _ = pullback.snd G.source.hom G.target.hom := by ext T q; rfl
    have : IsSplitEpi ι := IsSplitEpi.mk' ⟨ρ, hρι⟩
    apply (cancel_epi ι).1
    ext T q
    change φ.hom.app T (G.source.hom.app T (G.comp.hom.app T (ι.app T q))) =
      φ.hom.app T (G.source.hom.app T
        ((pullback.fst G.source.hom G.target.hom).app T (ι.app T q)))
    have hφApp (a : G.arrows.obj.obj T) :
        φ.hom.app T (G.target.hom.app T a) = φ.hom.app T (G.source.hom.app T a) := by
      simpa [NatTrans.comp_app] using congrArg (fun f => (f.app T) a) hφ'
    have hfst : (pullback.fst G.source.hom G.target.hom).app T (ι.app T q) = q.1.1 := by
      simpa [π₁] using congrArg (fun f => (f.app T) q) hι₁
    calc
      φ.hom.app T (G.source.hom.app T (G.comp.hom.app T (ι.app T q))) =
          φ.hom.app T (G.target.hom.app T (G.comp.hom.app T (ι.app T q))) :=
            (hφApp (G.comp.hom.app T (ι.app T q))).symm
      _ = φ.hom.app T (G.target.hom.app T q.1.1) := congrArg (φ.hom.app T) (target_comp G T q)
      _ = φ.hom.app T (G.source.hom.app T
          ((pullback.fst G.source.hom G.target.hom).app T (ι.app T q))) := by
            rw [hfst]
            exact hφApp q.1.1
  exact ⟨{ objects := G.objects
           arrows := G.arrows
           objectsToBase := φ
           arrowsToBase := arrowsToX
           source := G.source
           target := G.target
           source_over := rfl
           target_over := by apply ObjectProperty.hom_ext; exact hφ'
           comp := G.comp
           comp_over := compOverX
           pointwiseGroupoid := G.pointwiseGroupoid }, rfl, rfl, rfl⟩

section OverInvariantTarget

variable (G : GroupoidInAlgebraicSpaces C S hS B) {X : AlgebraicSpaces C S hS}
  (XtoB : X ⟶ B) (φ : G.objects ⟶ X) (hφB : φ ≫ XtoB = G.objectsToBase)
  (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)

/-- The groupoid over the invariant target has the same object space. -/
@[simp] theorem overInvariantTarget_objects :
    (overInvariantTarget G XtoB φ hφB hφ).val.objects = G.objects := rfl

/-- The groupoid over the invariant target has the same arrow space. -/
@[simp] theorem overInvariantTarget_arrows :
    (overInvariantTarget G XtoB φ hφB hφ).val.arrows = G.arrows := rfl

/-- The structure morphism on objects of the groupoid over the invariant target is the
invariant morphism. -/
@[simp] theorem overInvariantTarget_objectsToBase :
    (overInvariantTarget G XtoB φ hφB hφ).val.objectsToBase = φ := rfl

/-- The structure morphism on arrows of the groupoid over the invariant target is the source
map followed by the invariant morphism. -/
@[simp] theorem overInvariantTarget_arrowsToBase :
    (overInvariantTarget G XtoB φ hφB hφ).val.arrowsToBase = G.source ≫ φ := rfl

/-- The groupoid over the invariant target has the same source map. -/
@[simp] theorem overInvariantTarget_source :
    (overInvariantTarget G XtoB φ hφB hφ).val.source = G.source := rfl

/-- The groupoid over the invariant target has the same target map. -/
@[simp] theorem overInvariantTarget_target :
    (overInvariantTarget G XtoB φ hφB hφ).val.target = G.target := rfl

end OverInvariantTarget

/-! ### The base-changed relation comes from the base-changed groupoid -/

/-- Transport of a first pullback projection along an equality of the morphisms pulled back. -/
private theorem eqToHom_pullback_fst {𝒟 : Type*} [Category 𝒟] [HasPullbacks 𝒟]
    {W A A' : 𝒟} (f : A ⟶ W) {g g' : A' ⟶ W} (h : g = g') :
    eqToHom (congrArg (fun k ↦ pullback f k) h) ≫ pullback.fst f g' = pullback.fst f g := by
  cases h; simp

/-- Transport of a second pullback projection along an equality of the morphisms pulled
back. -/
private theorem eqToHom_pullback_snd {𝒟 : Type*} [Category 𝒟] [HasPullbacks 𝒟]
    {W A A' : 𝒟} (f : A ⟶ W) {g g' : A' ⟶ W} (h : g = g') :
    eqToHom (congrArg (fun k ↦ pullback f k) h) ≫ pullback.snd f g' = pullback.snd f g := by
  cases h; simp

/-- **Stacks 048G.** The base change of the pre-relation of a groupoid in algebraic spaces
along a morphism to an invariant target is the pre-relation of the base change of the
groupoid over that target: the object and the arrow spaces agree, canonically through the two
projections of the pullbacks, and the identifications intertwine the source and the target
maps. -/
@[stacks 048G "base_changed_groupoid_relation"]
theorem baseChangedPreRelation_isBaseChange (G : GroupoidInAlgebraicSpaces C S hS B)
    {X X' : AlgebraicSpaces C S hS} (XtoB : X ⟶ B) (φ : G.objects ⟶ X)
    (hφB : φ ≫ XtoB = G.objectsToBase)
    (hφ : Space.IsInvariant (Space.groupoidPreRelation G) φ.hom)
    (f : X' ⟶ X) :
    let H := (overInvariantTarget G XtoB φ hφB hφ).val
    let bc := Space.baseChange H f
    let j := Space.groupoidPreRelation G
    let j' := (Space.baseChangedPreRelation j φ.hom f.hom hφ).val
    ∃ (hobj : H.objects = G.objects) (harr : H.arrows = G.arrows)
      (α : (Space.baseChangedObject (U := Over.mk G.objectsToBase.hom) φ.hom f.hom).left ≅
          bc.groupoid.objects.obj)
      (β : (Space.baseChangedArrows j φ.hom f.hom).left ≅ bc.groupoid.arrows.obj),
      (α.hom ≫ bc.groupoid.objectsToBase.hom = pullback.fst f.hom φ.hom) ∧
      (β.hom ≫ bc.groupoid.arrowsToBase.hom =
        pullback.fst f.hom (j.target.left ≫ φ.hom)) ∧
      (α.hom ≫ bc.projection.mapObjects ≫ (eqToHom hobj).hom =
        pullback.snd f.hom φ.hom) ∧
      (β.hom ≫ bc.projection.mapArrows ≫ (eqToHom harr).hom =
        pullback.snd f.hom (j.target.left ≫ φ.hom)) ∧
      (j'.source.left ≫ α.hom = β.hom ≫ bc.groupoid.source.hom) ∧
      (j'.target.left ≫ α.hom = β.hom ≫ bc.groupoid.target.hom) := by
  intro H bc j j'
  have hφ' : G.target.hom ≫ φ.hom = G.source.hom ≫ φ.hom := by
    simpa [j, Space.IsInvariant, Space.groupoidPreRelation] using hφ
  have hjt : j.target.left = G.target.hom := by simp [j, Space.groupoidPreRelation]
  have hjs : j.source.left = G.source.hom := by simp [j, Space.groupoidPreRelation]
  have harrBase : H.arrowsToBase.hom = j.target.left ≫ φ.hom :=
    hφ'.symm.trans (congrArg (· ≫ φ.hom) hjt.symm)
  -- the two cartesian squares over the object space
  have P₁ : IsPullback
      (ObjectProperty.homMk (pullback.snd f.hom H.objectsToBase.hom) :
        AlgebraicSpaces.fiberProduct C S hS f H.objectsToBase ⟶ H.objects)
      (ObjectProperty.homMk (pullback.fst f.hom H.objectsToBase.hom))
      H.objectsToBase f :=
    (AlgebraicSpaces.isPullback_fiberProduct C S hS f H.objectsToBase).flip
  have Q₁ : IsPullback
      (ObjectProperty.homMk (pullback.snd f.hom H.arrowsToBase.hom) :
        AlgebraicSpaces.fiberProduct C S hS f H.arrowsToBase ⟶ H.arrows)
      (ObjectProperty.homMk (pullback.fst f.hom H.arrowsToBase.hom))
      H.arrowsToBase f :=
    (AlgebraicSpaces.isPullback_fiberProduct C S hS f H.arrowsToBase).flip
  let α₀ := P₁.isoIsPullback _ _ bc.objects_isPullback
  let β₀ := Q₁.isoIsPullback _ _ bc.arrows_isPullback
  let α : (Space.baseChangedObject (U := Over.mk G.objectsToBase.hom) φ.hom f.hom).left ≅
      bc.groupoid.objects.obj := (ObjectProperty.ι _).mapIso α₀
  let βAux : pullback f.hom H.arrowsToBase.hom ≅ bc.groupoid.arrows.obj :=
    (ObjectProperty.ι _).mapIso β₀
  let β : (Space.baseChangedArrows j φ.hom f.hom).left ≅ bc.groupoid.arrows.obj :=
    eqToIso (congrArg (fun k ↦ pullback f.hom k) harrBase.symm) ≪≫ βAux
  have hαObj : α.hom ≫ bc.projection.mapObjects = pullback.snd f.hom φ.hom :=
    congrArg (fun k ↦ k.hom) (P₁.isoIsPullback_hom_fst _ _ bc.objects_isPullback)
  have hαBase : α.hom ≫ bc.groupoid.objectsToBase.hom = pullback.fst f.hom φ.hom :=
    congrArg (fun k ↦ k.hom) (P₁.isoIsPullback_hom_snd _ _ bc.objects_isPullback)
  have hβArrAux : βAux.hom ≫ bc.projection.mapArrows =
      pullback.snd f.hom H.arrowsToBase.hom :=
    congrArg (fun k ↦ k.hom) (Q₁.isoIsPullback_hom_fst _ _ bc.arrows_isPullback)
  have hβBaseAux : βAux.hom ≫ bc.groupoid.arrowsToBase.hom =
      pullback.fst f.hom H.arrowsToBase.hom :=
    congrArg (fun k ↦ k.hom) (Q₁.isoIsPullback_hom_snd _ _ bc.arrows_isPullback)
  have hβhom : β.hom =
      eqToHom (congrArg (fun k ↦ pullback f.hom k) harrBase.symm) ≫ βAux.hom := rfl
  have hβ {Y : _} {k : bc.groupoid.arrows.obj ⟶ Y} {m : pullback f.hom H.arrowsToBase.hom ⟶ Y}
      {m' : pullback f.hom (j.target.left ≫ φ.hom) ⟶ Y}
      (hm : βAux.hom ≫ k = m)
      (e : eqToHom (congrArg (fun k ↦ pullback f.hom k) harrBase.symm) ≫ m = m') :
      β.hom ≫ k = m' := by
    rw [hβhom]
    exact (Category.assoc _ _ _).trans ((congrArg _ hm).trans e)
  have hβArr : β.hom ≫ bc.projection.mapArrows =
      pullback.snd f.hom (j.target.left ≫ φ.hom) :=
    hβ hβArrAux (eqToHom_pullback_snd f.hom harrBase.symm)
  have hβBase : β.hom ≫ bc.groupoid.arrowsToBase.hom =
      pullback.fst f.hom (j.target.left ≫ φ.hom) :=
    hβ hβBaseAux (eqToHom_pullback_fst f.hom harrBase.symm)
  have hProjSource : bc.groupoid.source.hom ≫ bc.projection.mapObjects =
      bc.projection.mapArrows ≫ G.source.hom := by
    ext T a
    exact (bc.projection.map_source T a).symm
  have hProjTarget : bc.groupoid.target.hom ≫ bc.projection.mapObjects =
      bc.projection.mapArrows ≫ G.target.hom := by
    ext T a
    exact (bc.projection.map_target T a).symm
  have hSourceOver : bc.groupoid.source.hom ≫ bc.groupoid.objectsToBase.hom =
      bc.groupoid.arrowsToBase.hom :=
    congrArg (fun k ↦ k.hom) bc.groupoid.source_over
  have hTargetOver : bc.groupoid.target.hom ≫ bc.groupoid.objectsToBase.hom =
      bc.groupoid.arrowsToBase.hom :=
    congrArg (fun k ↦ k.hom) bc.groupoid.target_over
  have hinvFst : α.inv ≫ pullback.fst f.hom φ.hom = bc.groupoid.objectsToBase.hom := by
    rw [← hαBase]
    exact α.inv_hom_id_assoc _
  have hinvSnd : α.inv ≫ pullback.snd f.hom φ.hom = bc.projection.mapObjects := by
    rw [← hαObj]
    exact α.inv_hom_id_assoc _
  have key (s : bc.groupoid.arrows.obj ⟶ bc.groupoid.objects.obj) (e : G.arrows.obj ⟶ G.objects.obj)
      (r : (Space.baseChangedArrows j φ.hom f.hom).left ⟶
        (Space.baseChangedObject (U := Over.mk G.objectsToBase.hom) φ.hom f.hom).left)
      (hso : s ≫ bc.groupoid.objectsToBase.hom = bc.groupoid.arrowsToBase.hom)
      (hs : s ≫ bc.projection.mapObjects = bc.projection.mapArrows ≫ e)
      (h₁ : r ≫ pullback.fst f.hom φ.hom = pullback.fst f.hom (j.target.left ≫ φ.hom))
      (h₂ : r ≫ pullback.snd f.hom φ.hom = pullback.snd f.hom (j.target.left ≫ φ.hom) ≫ e) :
      r ≫ α.hom = β.hom ≫ s := by
    rw [← Iso.eq_comp_inv]
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hinvFst, Category.assoc, hso, hβBase]
      exact h₁
    · rw [h₂, Category.assoc, hinvSnd]
      exact (congrArg (· ≫ e) hβArr).symm.trans ((Category.assoc _ _ _).trans
        ((congrArg _ hs.symm).trans (Category.assoc _ _ _).symm))
  refine ⟨rfl, rfl, α, β, hαBase, hβBase, ?_, ?_, ?_, ?_⟩
  · exact (congrArg (fun k ↦ α.hom ≫ k)
      (Category.comp_id bc.projection.mapObjects)).trans hαObj
  · exact (congrArg (fun k ↦ β.hom ≫ k)
      (Category.comp_id bc.projection.mapArrows)).trans hβArr
  · exact key _ _ _ hSourceOver hProjSource
      (Space.baseChangedPreRelation_source_fst j φ.hom f.hom hφ)
      ((Space.baseChangedPreRelation_source_snd j φ.hom f.hom hφ).trans (congrArg _ hjs))
  · exact key _ _ _ hTargetOver hProjTarget
      (Space.baseChangedPreRelation_target_fst j φ.hom f.hom hφ)
      ((Space.baseChangedPreRelation_target_snd j φ.hom f.hom hφ).trans (congrArg _ hjt))

end AlgebraicGeometry.GroupoidInAlgebraicSpaces

end
