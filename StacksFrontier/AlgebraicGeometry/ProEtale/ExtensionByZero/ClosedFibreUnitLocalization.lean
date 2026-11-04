module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ExtensionByZero.OpenClosedSequence

/-!
# The unit of the closed-immersion adjunction under localization

Let `i : Z ⟶ X` be a morphism of schemes and let `V` be an object of the small pro-étale site of
`X`, with structure morphism `j : V ⟶ X`. Base change gives a cartesian square with
`i_V : V ×_X Z ⟶ V` and `j' : V ×_X Z ⟶ Z`, and `j`, `j'` are weakly étale. Restriction of
abelian sheaves along a weakly étale morphism is left adjoint to the direct image along it, so
both composites `j'^{-1} i^{-1}` and `i_V^{-1} j^{-1}` are left adjoint to the two composite
direct images, which agree because iterated base change does. The resulting comparison of the
two composite inverse images intertwines the units, and evaluating at the diagonals shows: the
unit `F ⟶ i_* i^{-1} F` is invertible on sections over `V` as soon as the unit of the base
changed adjunction `i_V^{-1} ⊣ i_{V*}` at the restriction `F|_V` is invertible on global
sections.

## Main definitions

* `AlgebraicGeometry.ProEtale.proetalePostcomposeBaseChangeAdj`: composition with a weakly étale
  morphism is left adjoint to base change along it, on small pro-étale sites.
* `AlgebraicGeometry.ProEtale.Abelian.proetaleRestrictionAdj`: restriction of abelian sheaves
  along a weakly étale morphism is left adjoint to the direct image.

## Main results

* `AlgebraicGeometry.ProEtale.isIso_proetaleUnit_app_of_isIso_baseChange`: the reduction of the
  unit at `V` to the unit of the base-changed adjunction at the final object.

## References

* [Stacks Project, Tag 09AC](https://stacks.math.columbia.edu/tag/09AC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

namespace AlgebraicGeometry.ProEtale

/-- Composition with a weakly étale morphism `j` is left adjoint to base change along `j`, on
the small pro-étale sites. -/
def proetalePostcomposeBaseChangeAdj {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    proetalePostcompose j ⊣ Scheme.proetaleBaseChange j := by
  letI : MorphismProperty.HasPullbacksAlong
      (@WeaklyEtale : MorphismProperty Scheme.{u}) j := ⟨fun _ _ ↦ inferInstance⟩
  letI : MorphismProperty.IsStableUnderBaseChangeAlong
      (@WeaklyEtale : MorphismProperty Scheme.{u}) j :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  exact MorphismProperty.Over.mapPullbackAdj (P := @WeaklyEtale) (Q := ⊤) j inferInstance trivial

/-- The counit of `proetalePostcomposeBaseChangeAdj` is the first projection. -/
theorem proetalePostcomposeBaseChangeAdj_counit_app_left {U X : Scheme.{u}} (j : U ⟶ X)
    [WeaklyEtale j] (T : X.ProEt) :
    ((proetalePostcomposeBaseChangeAdj j).counit.app T).left = pullback.fst T.hom j := by
  simp only [proetalePostcomposeBaseChangeAdj, MorphismProperty.Over.mapPullbackAdj_counit_app]
  rfl

/-- A morphism of the small pro-étale site whose underlying morphism of schemes is an
isomorphism is an isomorphism. -/
theorem Scheme.ProEt.isIso_of_isIso_left {S : Scheme.{u}} {T T' : S.ProEt} (f : T ⟶ T')
    [IsIso f.left] : IsIso f := by
  have : IsIso ((Scheme.ProEt.forget S ⋙ Over.forget S).map f) := ‹IsIso f.left›
  exact isIso_of_reflects_iso f (Scheme.ProEt.forget S ⋙ Over.forget S)

/-- The section `(f, 𝟙)` of the second projection of `pullback (𝟙 B) f` is an isomorphism. -/
theorem isIso_pullback_lift_id {A B : Scheme.{u}} (f : A ⟶ B) :
    IsIso (pullback.lift f (𝟙 A) ((Category.comp_id _).trans (Category.id_comp _).symm) :
      A ⟶ pullback (𝟙 B) f) := by
  refine ⟨⟨pullback.snd _ _, pullback.lift_snd _ _ _, ?_⟩⟩
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.id_comp, ← pullback.condition,
      Category.comp_id]
  · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]

/-- If `f : S ⟶ j^*T` is the isomorphism `g` after the first projection, then `f` followed by the
counit of `proetalePostcomposeBaseChangeAdj` is an isomorphism. -/
private theorem isIso_postcompose_map_comp_counit {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    {T : X.ProEt} {S : U.ProEt} (f : S ⟶ (Scheme.proetaleBaseChange j).obj T)
    (g : S.left ⟶ T.left) (hg : IsIso g) (hf : f.left ≫ pullback.fst T.hom j = g) :
    IsIso ((proetalePostcompose j).map f ≫ (proetalePostcomposeBaseChangeAdj j).counit.app T) := by
  have : IsIso ((proetalePostcompose j).map f ≫
      (proetalePostcomposeBaseChangeAdj j).counit.app T).left := by
    change IsIso (f.left ≫ ((proetalePostcomposeBaseChangeAdj j).counit.app T).left)
    rwa [proetalePostcomposeBaseChangeAdj_counit_app_left, hf]
  exact Scheme.ProEt.isIso_of_isIso_left _

namespace Abelian

/-- Restriction of abelian pro-étale sheaves along a weakly étale morphism `j` is left adjoint to
the direct image along `j`, restriction along base change. -/
def proetaleRestrictionAdj {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j] :
    proetaleRestriction.{u, v} j ⊣
      (Scheme.proetaleBaseChange j).sheafPushforwardContinuous AddCommGrpCat.{max (u + 1) v}
        (Scheme.ProEt.topology X) (Scheme.ProEt.topology U) := by
  letI := proetalePostcompose_isContinuous j
  exact (proetalePostcomposeBaseChangeAdj j).sheafPushforwardContinuous _ _

/-- The unit of `proetaleRestrictionAdj` is restriction along the counit of
`proetalePostcomposeBaseChangeAdj`. -/
theorem proetaleRestrictionAdj_unit_app_hom_app {U X : Scheme.{u}} (j : U ⟶ X) [WeaklyEtale j]
    (G : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}) (T : X.ProEt) :
    ((proetaleRestrictionAdj.{u, v} j).unit.app G).hom.app (op T) =
      G.obj.map ((proetalePostcomposeBaseChangeAdj j).counit.app T).op := by
  simp [proetaleRestrictionAdj]
  rfl

end Abelian

section Localization

variable {X Z : Scheme.{u}} (i : Z ⟶ X) (V : X.ProEt)

/-- The underlying scheme of a pro-étale base change is the fibre product. -/
@[simp]
theorem Scheme.proetaleBaseChange_obj_left {Y X : Scheme.{u}} (f : Y ⟶ X) (T : X.ProEt) :
    ((Scheme.proetaleBaseChange f).obj T).left = pullback T.hom f :=
  rfl

/-- The structure morphism of a pro-étale base change is the second projection. -/
@[simp]
theorem Scheme.proetaleBaseChange_obj_hom {Y X : Scheme.{u}} (f : Y ⟶ X) (T : X.ProEt) :
    ((Scheme.proetaleBaseChange f).obj T).hom = pullback.snd T.hom f :=
  rfl

/-- The underlying morphism of schemes of the base change of a morphism. -/
@[simp]
theorem Scheme.proetaleBaseChange_map_left {Y X : Scheme.{u}} (f : Y ⟶ X) {T T' : X.ProEt}
    (g : T ⟶ T') :
    ((Scheme.proetaleBaseChange f).map g).left =
      pullback.lift (pullback.fst T.hom f ≫ g.left) (pullback.snd T.hom f)
        (by rw [Category.assoc, MorphismProperty.Over.w g, pullback.condition]) :=
  rfl

/-- Iterated base change around a cartesian square, on schemes: for `t : T ⟶ X`, `j : V ⟶ X` and
`i : Z ⟶ X`, the two iterated fibre products `(T ×_X V) ×_V (V ×_X Z)` and
`(T ×_X Z) ×_Z (V ×_X Z)` are both `T ×_X (V ×_X Z)`. -/
def pullbackSquareIso {T V : Scheme.{u}} (t : T ⟶ X) (j : V ⟶ X) :
    pullback (pullback.snd t j) (pullback.fst j i) ≅
      pullback (pullback.snd t i) (pullback.snd j i) where
  hom := pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, pullback.condition, Category.assoc]))
    (pullback.snd _ _) (pullback.lift_snd _ _ _)
  inv := pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ pullback.fst _ _) (pullback.snd _ _ ≫ pullback.fst _ _)
      (by rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition,
        Category.assoc, ← pullback.condition, Category.assoc]))
    (pullback.snd _ _) (pullback.lift_snd _ _ _)
  hom_inv_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, Category.id_comp]
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, Category.id_comp]
        exact pullback.condition.symm
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, Category.id_comp]
      · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, Category.id_comp]
        exact pullback.condition.symm
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc, Category.id_comp]

/-- `pullbackSquareIso` commutes with the second projections to `V ×_X Z`. -/
@[reassoc (attr := simp)]
theorem pullbackSquareIso_hom_snd {T V : Scheme.{u}} (t : T ⟶ X) (j : V ⟶ X) :
    (pullbackSquareIso i t j).hom ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp only [pullbackSquareIso]
  exact pullback.lift_snd _ _ _

/-- Naturality of `pullbackSquareIso` in the object over `X`. -/
theorem pullbackSquareIso_naturality {T T' V : Scheme.{u}} (t : T ⟶ X) (t' : T' ⟶ X)
    (j : V ⟶ X) (g : T ⟶ T') (hg : g ≫ t' = t) :
    pullback.lift (pullback.fst _ _ ≫ pullback.lift (pullback.fst t j ≫ g) (pullback.snd t j)
        (by rw [Category.assoc, hg, pullback.condition])) (pullback.snd _ _)
        (by rw [Category.assoc, pullback.lift_snd, pullback.condition]) ≫
        (pullbackSquareIso i t' j).hom =
      (pullbackSquareIso i t j).hom ≫
        pullback.lift (pullback.fst _ _ ≫ pullback.lift (pullback.fst t i ≫ g) (pullback.snd t i)
          (by rw [Category.assoc, hg, pullback.condition])) (pullback.snd _ _)
          (by rw [Category.assoc, pullback.lift_snd, pullback.condition]) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, pullbackSquareIso]
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, pullbackSquareIso]
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, pullbackSquareIso]

/-- Iterated base change around the cartesian square of `V ⟶ X` and `i`: base change to `V` and
then to `V ×_X Z` agrees with base change to `Z` and then to `V ×_X Z`. -/
def proetaleBaseChangeSquareIso :
    Scheme.proetaleBaseChange V.hom ⋙ Scheme.proetaleBaseChange (pullback.fst V.hom i) ≅
      Scheme.proetaleBaseChange i ⋙ Scheme.proetaleBaseChange (pullback.snd V.hom i) :=
  NatIso.ofComponents
    (fun T ↦ MorphismProperty.Over.isoMk (pullbackSquareIso i T.hom V.hom)
      (pullbackSquareIso_hom_snd i T.hom V.hom))
    (fun {T T'} g ↦ MorphismProperty.Over.Hom.ext
      (pullbackSquareIso_naturality i T.hom T'.hom V.hom g.left (MorphismProperty.Over.w g)))

/-- The diagonal of `V` over `X`, as a morphism from the final object of the small pro-étale site
of `V` to the base change of `V` along its own structure morphism. -/
def proetaleDiagonal : Scheme.ProEt.mk (𝟙 V.left) ⟶ (Scheme.proetaleBaseChange V.hom).obj V :=
  MorphismProperty.Over.homMk (pullback.lift (𝟙 _) (𝟙 _) rfl) (pullback.lift_snd _ _ _)

/-- The diagonal of `V ×_X Z` over `Z`. -/
def proetaleClosedFibreDiagonal :
    Scheme.ProEt.mk (𝟙 (pullback V.hom i)) ⟶
      (Scheme.proetaleBaseChange (pullback.snd V.hom i)).obj
        ((Scheme.proetaleBaseChange i).obj V) :=
  MorphismProperty.Over.homMk (pullback.lift (𝟙 _) (𝟙 _) rfl) (pullback.lift_snd _ _ _)

/-- The final object of the small pro-étale site of `V ×_X Z` is the base change of the final
object of the small pro-étale site of `V`. -/
def proetaleBaseChangeTopHom :
    Scheme.ProEt.mk (𝟙 (pullback V.hom i)) ⟶
      (Scheme.proetaleBaseChange (pullback.fst V.hom i)).obj (Scheme.ProEt.mk (𝟙 V.left)) :=
  MorphismProperty.Over.homMk (pullback.lift (pullback.fst V.hom i) (𝟙 _)
    ((Category.comp_id _).trans (Category.id_comp _).symm)) (pullback.lift_snd _ _ _)

/-- The two diagonals are compatible with `pullbackSquareIso`, on schemes. -/
theorem pullbackSquareIso_diagonal {V : Scheme.{u}} (j : V ⟶ X) :
    pullback.lift (𝟙 (pullback j i)) (𝟙 _) rfl ≫ (pullbackSquareIso i j j).inv =
      pullback.lift (pullback.fst j i) (𝟙 _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        pullback.lift (pullback.fst (𝟙 V) (pullback.fst j i) ≫ pullback.lift (𝟙 V) (𝟙 V) rfl)
          (pullback.snd _ _)
          (by rw [Category.assoc, pullback.lift_snd, Category.comp_id, ← pullback.condition,
            Category.comp_id]) := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, pullbackSquareIso, Category.id_comp, Category.comp_id]
    · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, pullbackSquareIso, Category.id_comp, Category.comp_id]
  · simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, pullbackSquareIso, Category.id_comp, Category.comp_id]

/-- The diagonal of `V ×_X Z` over `Z`, followed by the inverse of `proetaleBaseChangeSquareIso`
at `V`, is the base change along `V ×_X Z ⟶ V` of the diagonal of `V` over `X`, precomposed with
`proetaleBaseChangeTopHom`. -/
theorem proetaleClosedFibreDiagonal_comp :
    proetaleClosedFibreDiagonal i V ≫ (proetaleBaseChangeSquareIso i V).inv.app V =
      proetaleBaseChangeTopHom i V ≫
        (Scheme.proetaleBaseChange (pullback.fst V.hom i)).map (proetaleDiagonal V) :=
  MorphismProperty.Over.Hom.ext (pullbackSquareIso_diagonal i V.hom)

/-- **The unit under localization.** For an object `V` of the small pro-étale site of `X` and an
abelian sheaf `F` on `X_proétale`, the unit `F ⟶ i_* i^{-1} F` is invertible on sections over `V`
as soon as the unit of the base-changed adjunction for `i_V : V ×_X Z ⟶ V`, at the restriction
of `F` to `V`, is invertible on global sections.

Both `j'^{-1} ∘ i^{-1}` and `i_V^{-1} ∘ j^{-1}` are left adjoint to the composite direct images,
which agree through `proetaleBaseChangeSquareIso`; the induced isomorphism of the two composite
inverse images intertwines the units, and restricting along the diagonals of `V` over `X` and of
`V ×_X Z` over `Z` turns the units at `V` into the two units of the statement. -/
theorem isIso_proetaleUnit_app_of_isIso_baseChange
    (F : Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v})
    (h : IsIso (((Abelian.proetaleInverseImageDirectImageAdj.{u, v}
      (pullback.fst V.hom i)).unit.app ((Abelian.proetaleRestriction.{u, v} V.hom).obj F)).hom.app
        (op (Scheme.ProEt.mk (𝟙 V.left))))) :
    IsIso (((Abelian.proetaleInverseImageDirectImageAdj.{u, v} i).unit.app F).hom.app (op V)) := by
  let A := AddCommGrpCat.{max (u + 1) v}
  let iV := pullback.fst V.hom i
  let j' := pullback.snd V.hom i
  let Ai := Abelian.proetaleInverseImageDirectImageAdj.{u, v} i
  let AiV := Abelian.proetaleInverseImageDirectImageAdj.{u, v} iV
  let Aj := Abelian.proetaleRestrictionAdj.{u, v} V.hom
  let Aj' := Abelian.proetaleRestrictionAdj.{u, v} j'
  let B1 := Ai.comp Aj'
  let B2 := Aj.comp AiV
  have _ : (Scheme.proetaleBaseChange V.hom).IsContinuous (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology V.left) := Scheme.proetaleBaseChange_isContinuous V.hom
  have _ : (Scheme.proetaleBaseChange i).IsContinuous (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Z) := Scheme.proetaleBaseChange_isContinuous i
  have _ : (Scheme.proetaleBaseChange j').IsContinuous (Scheme.ProEt.topology Z)
      (Scheme.ProEt.topology (pullback V.hom i)) := Scheme.proetaleBaseChange_isContinuous j'
  have _ : (Scheme.proetaleBaseChange iV).IsContinuous (Scheme.ProEt.topology V.left)
      (Scheme.ProEt.topology (pullback V.hom i)) := Scheme.proetaleBaseChange_isContinuous iV
  have _ : (Scheme.proetaleBaseChange V.hom ⋙ Scheme.proetaleBaseChange iV).IsContinuous
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology (pullback V.hom i)) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology V.left) _
  have _ : (Scheme.proetaleBaseChange i ⋙ Scheme.proetaleBaseChange j').IsContinuous
      (Scheme.ProEt.topology X) (Scheme.ProEt.topology (pullback V.hom i)) :=
    Functor.isContinuous_comp _ _ _ (Scheme.ProEt.topology Z) _
  let ρ : Abelian.proetaleDirectImage.{u, v} iV ⋙
        (Scheme.proetaleBaseChange V.hom).sheafPushforwardContinuous A
          (Scheme.ProEt.topology X) (Scheme.ProEt.topology V.left) ≅
      (Scheme.proetaleBaseChange j').sheafPushforwardContinuous A
          (Scheme.ProEt.topology Z) (Scheme.ProEt.topology (pullback V.hom i)) ⋙
        Abelian.proetaleDirectImage.{u, v} i :=
    Functor.sheafPushforwardContinuousComp' (eFG := proetaleBaseChangeSquareIso i V)
      (A := A) (J := Scheme.ProEt.topology X) (K := Scheme.ProEt.topology V.left)
      (L := Scheme.ProEt.topology (pullback V.hom i)) ≪≫
    (Functor.sheafPushforwardContinuousComp' (eFG := Iso.refl _)
      (A := A) (J := Scheme.ProEt.topology X) (K := Scheme.ProEt.topology Z)
      (L := Scheme.ProEt.topology (pullback V.hom i))).symm
  let c := Adjunction.leftAdjointUniq B1 (B2.ofNatIsoRight ρ)
  have hu := Adjunction.unit_leftAdjointUniq_hom_app B1 (B2.ofNatIsoRight ρ) F
  let E := (sheafSections (Scheme.ProEt.topology X) A).obj (op V)
  have hE := congrArg E.map hu
  simp only [B1, B2, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Adjunction.comp_unit_app, Functor.map_comp, Category.assoc] at hE
  have h1 : E.map ((Abelian.proetaleDirectImage i).map
      (Aj'.unit.app ((Abelian.proetaleInverseImage i).obj F))) =
      ((Abelian.proetaleInverseImage i).obj F).obj.map
        ((proetalePostcomposeBaseChangeAdj j').counit.app
          ((Scheme.proetaleBaseChange i).obj V)).op :=
    ProEtale.Abelian.proetaleRestrictionAdj_unit_app_hom_app j' _ _
  have h2 : E.map (Aj.unit.app F) =
      F.obj.map ((proetalePostcomposeBaseChangeAdj V.hom).counit.app V).op :=
    ProEtale.Abelian.proetaleRestrictionAdj_unit_app_hom_app V.hom _ _
  have h3 : E.map (ρ.hom.app ((Abelian.proetaleRestriction V.hom ⋙
      Abelian.proetaleInverseImage iV).obj F)) =
      ((Abelian.proetaleRestriction V.hom ⋙ Abelian.proetaleInverseImage iV).obj F).obj.map
        ((proetaleBaseChangeSquareIso i V).inv.app V).op := by
    simp only [Functor.id_obj, Functor.const_obj_obj, Functor.comp_obj, Functor.flip_obj_obj,
      ObjectProperty.ι_obj, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.flip_obj_map,
      ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
      Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
      Functor.sheafPushforwardContinuousComp'_inv_app_hom_app, Iso.refl_hom, NatTrans.id_app, op_id,
      CategoryTheory.Functor.map_id, E, ρ]
    exact Category.comp_id _
  rw [h1, h2, h3] at hE
  let G := (Abelian.proetaleInverseImage.{u, v} i).obj F
  let H := (Abelian.proetaleRestriction.{u, v} V.hom ⋙
    Abelian.proetaleInverseImage.{u, v} iV).obj F
  let cF := c.hom.app F
  let κ := proetaleClosedFibreDiagonal i V
  let δ := proetaleDiagonal V
  let εA := (proetalePostcomposeBaseChangeAdj V.hom).counit.app V
  let εQ := (proetalePostcomposeBaseChangeAdj j').counit.app ((Scheme.proetaleBaseChange i).obj V)
  let ηP := (AiV.unit.app ((Abelian.proetaleRestriction.{u, v} V.hom).obj F)).hom
  have hE2 : ((Ai.unit.app F).hom.app (op V)) ≫ G.obj.map εQ.op ≫
      cF.hom.app (op ((Scheme.proetaleBaseChange j').obj ((Scheme.proetaleBaseChange i).obj V))) =
      F.obj.map εA.op ≫ ηP.app (op ((Scheme.proetaleBaseChange V.hom).obj V)) ≫
        H.obj.map ((proetaleBaseChangeSquareIso i V).inv.app V).op := hE
  have hc : cF.hom.app (op ((Scheme.proetaleBaseChange j').obj
      ((Scheme.proetaleBaseChange i).obj V))) ≫ H.obj.map κ.op =
      G.obj.map ((proetalePostcompose j').map κ).op ≫
        cF.hom.app (op (Scheme.ProEt.mk (𝟙 (pullback V.hom i)))) :=
    (cF.hom.naturality κ.op).symm
  have hθ : H.obj.map ((proetaleBaseChangeSquareIso i V).inv.app V).op ≫ H.obj.map κ.op =
      H.obj.map ((Scheme.proetaleBaseChange iV).map δ).op ≫
        H.obj.map (proetaleBaseChangeTopHom i V).op :=
    (H.obj.map_comp _ _).symm.trans ((congrArg (fun q ↦ H.obj.map q)
      (op_comp (f := κ) (g := (proetaleBaseChangeSquareIso i V).inv.app V)).symm).trans
      ((congrArg (fun q ↦ H.obj.map q.op) (proetaleClosedFibreDiagonal_comp i V)).trans
        ((congrArg (fun q ↦ H.obj.map q) op_comp).trans (H.obj.map_comp _ _))))
  have hη : ηP.app (op ((Scheme.proetaleBaseChange V.hom).obj V)) ≫
      H.obj.map ((Scheme.proetaleBaseChange iV).map δ).op =
      F.obj.map ((proetalePostcompose V.hom).map δ).op ≫
        ηP.app (op (Scheme.ProEt.mk (𝟙 V.left))) :=
    (ηP.naturality δ.op).symm
  have key : (Ai.unit.app F).hom.app (op V) ≫ (G.obj.map εQ.op ≫
      G.obj.map ((proetalePostcompose j').map κ).op ≫
        cF.hom.app (op (Scheme.ProEt.mk (𝟙 (pullback V.hom i))))) =
      (F.obj.map εA.op ≫ F.obj.map ((proetalePostcompose V.hom).map δ).op) ≫
        ηP.app (op (Scheme.ProEt.mk (𝟙 V.left))) ≫
          H.obj.map (proetaleBaseChangeTopHom i V).op :=
    calc _ = (Ai.unit.app F).hom.app (op V) ≫ (G.obj.map εQ.op ≫
          (cF.hom.app (op ((Scheme.proetaleBaseChange j').obj
            ((Scheme.proetaleBaseChange i).obj V))) ≫ H.obj.map κ.op)) :=
          whisker_eq _ (whisker_eq _ hc.symm)
      _ = ((Ai.unit.app F).hom.app (op V) ≫ G.obj.map εQ.op ≫
          cF.hom.app (op ((Scheme.proetaleBaseChange j').obj
            ((Scheme.proetaleBaseChange i).obj V)))) ≫ H.obj.map κ.op :=
          (whisker_eq _ (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm
      _ = (F.obj.map εA.op ≫ ηP.app (op ((Scheme.proetaleBaseChange V.hom).obj V)) ≫
          H.obj.map ((proetaleBaseChangeSquareIso i V).inv.app V).op) ≫ H.obj.map κ.op :=
          hE2 =≫ _
      _ = F.obj.map εA.op ≫ ηP.app (op ((Scheme.proetaleBaseChange V.hom).obj V)) ≫
          (H.obj.map ((proetaleBaseChangeSquareIso i V).inv.app V).op ≫ H.obj.map κ.op) :=
          (Category.assoc _ _ _).trans (whisker_eq _ (Category.assoc _ _ _))
      _ = F.obj.map εA.op ≫ ηP.app (op ((Scheme.proetaleBaseChange V.hom).obj V)) ≫
          (H.obj.map ((Scheme.proetaleBaseChange iV).map δ).op ≫
            H.obj.map (proetaleBaseChangeTopHom i V).op) :=
          whisker_eq _ (whisker_eq _ hθ)
      _ = F.obj.map εA.op ≫ (ηP.app (op ((Scheme.proetaleBaseChange V.hom).obj V)) ≫
          H.obj.map ((Scheme.proetaleBaseChange iV).map δ).op) ≫
            H.obj.map (proetaleBaseChangeTopHom i V).op :=
          whisker_eq _ (Category.assoc _ _ _).symm
      _ = F.obj.map εA.op ≫ (F.obj.map ((proetalePostcompose V.hom).map δ).op ≫
          ηP.app (op (Scheme.ProEt.mk (𝟙 V.left)))) ≫
            H.obj.map (proetaleBaseChangeTopHom i V).op :=
          whisker_eq _ (hη =≫ _)
      _ = _ := (whisker_eq _ (Category.assoc _ _ _)).trans (Category.assoc _ _ _).symm
  -- the comparison maps are isomorphisms
  have hQ : IsIso ((proetalePostcompose j').map κ ≫ εQ) :=
    isIso_postcompose_map_comp_counit j' κ (𝟙 _) (IsIso.id _) (pullback.lift_fst _ _ _)
  have hA' : IsIso ((proetalePostcompose V.hom).map δ ≫ εA) :=
    isIso_postcompose_map_comp_counit V.hom δ (𝟙 _) (IsIso.id _) (pullback.lift_fst _ _ _)
  have hT : IsIso (proetaleBaseChangeTopHom i V) := by
    have : IsIso (proetaleBaseChangeTopHom i V).left := isIso_pullback_lift_id iV
    exact Scheme.ProEt.isIso_of_isIso_left _
  have hX : IsIso (G.obj.map εQ.op ≫ G.obj.map ((proetalePostcompose j').map κ).op ≫
      cF.hom.app (op (Scheme.ProEt.mk (𝟙 (pullback V.hom i))))) := by
    have eq : G.obj.map ((proetalePostcompose j').map κ ≫ εQ).op ≫
        cF.hom.app (op (Scheme.ProEt.mk (𝟙 (pullback V.hom i)))) =
        G.obj.map εQ.op ≫ G.obj.map ((proetalePostcompose j').map κ).op ≫
          cF.hom.app (op (Scheme.ProEt.mk (𝟙 (pullback V.hom i)))) :=
      ((congrArg G.obj.map op_comp).trans (G.obj.map_comp _ _) =≫ _).trans
        (Category.assoc _ _ _)
    have i1 : IsIso (G.obj.map ((proetalePostcompose j').map κ ≫ εQ).op) :=
      Functor.map_isIso _ _
    have i2 : IsIso (cF.hom.app (op (Scheme.ProEt.mk (𝟙 (pullback V.hom i))))) := by
      have : IsIso cF.hom := inferInstanceAs (IsIso ((sheafToPresheaf _ _).map cF))
      infer_instance
    exact eq ▸ (IsIso.comp_isIso' i1 i2)
  have hY : IsIso ((F.obj.map εA.op ≫ F.obj.map ((proetalePostcompose V.hom).map δ).op) ≫
      ηP.app (op (Scheme.ProEt.mk (𝟙 V.left))) ≫ H.obj.map (proetaleBaseChangeTopHom i V).op) := by
    have : IsIso (ηP.app (op (Scheme.ProEt.mk (𝟙 V.left)))) := h
    have eq : F.obj.map ((proetalePostcompose V.hom).map δ ≫ εA).op ≫
        ηP.app (op (Scheme.ProEt.mk (𝟙 V.left))) ≫ H.obj.map (proetaleBaseChangeTopHom i V).op =
        (F.obj.map εA.op ≫ F.obj.map ((proetalePostcompose V.hom).map δ).op) ≫
          ηP.app (op (Scheme.ProEt.mk (𝟙 V.left))) ≫
            H.obj.map (proetaleBaseChangeTopHom i V).op :=
      (congrArg F.obj.map op_comp).trans (F.obj.map_comp _ _) =≫ _
    have i1 : IsIso (F.obj.map ((proetalePostcompose V.hom).map δ ≫ εA).op) :=
      Functor.map_isIso _ _
    have i2 : IsIso (H.obj.map (proetaleBaseChangeTopHom i V).op) := Functor.map_isIso _ _
    exact eq ▸ (IsIso.comp_isIso' i1 (IsIso.comp_isIso' this i2))
  have hY' := key ▸ hY
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ (G.obj.map εQ.op ≫
    G.obj.map ((proetalePostcompose j').map κ).op ≫
      cF.hom.app (op (Scheme.ProEt.mk (𝟙 (pullback V.hom i))))) hX hY'

end Localization

end AlgebraicGeometry.ProEtale

end
