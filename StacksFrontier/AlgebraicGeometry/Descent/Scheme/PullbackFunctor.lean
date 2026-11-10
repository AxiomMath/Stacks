module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.PulledBackDatum

/-!
# The pullback functor on descent data for families

A morphism of families of schemes induces a functor between the categories of descent data
for the two families. On objects it is the pulled-back datum, and on morphisms it is
componentwise base change. Tag 02VT gives this functor its name.

## Main definitions

* `AlgebraicGeometry.MorphismOfSchemeFamilies.PullbackFunctor` specifies the functor
  together with its action on objects and morphisms.
* `AlgebraicGeometry.MorphismOfSchemeFamilies.pullbackFunctor` constructs it.

## Implementation notes

The specification records the action on objects as an equality of descent data and
transports along that equality when expressing the componentwise action on morphisms. The
functoriality proof checks the compatibility square of a morphism of descent data after
composing with the comparison isomorphisms to the chosen fibre products, where the pulled
back gluing isomorphism is given by `pulledBackDatum_gluing`.

## References

* [Stacks Project, Tag 02VS](https://stacks.math.columbia.edu/tag/02VS)
* [Stacks Project, Tag 02VT](https://stacks.math.columbia.edu/tag/02VT)
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.MorphismOfSchemeFamilies

private lemma overProdMapLeft
    {C : Type*} [Category C] {S : C} {A B A' B' : Over S}
    [HasPullback A.hom B.hom] [HasPullback A'.hom B'.hom]
    [HasBinaryProduct A B] [HasBinaryProduct A' B']
    (f : A ⟶ A') (g : B ⟶ B') :
    (prod.map f g).left ≫ (Over.prodLeftIsoPullback A' B').hom =
      (Over.prodLeftIsoPullback A B).hom ≫
        pullback.map A.hom B.hom A'.hom B'.hom f.left g.left (𝟙 S)
          (by simp) (by simp) := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.map, pullback.lift_fst]
    rw [Over.prodLeftIsoPullback_hom_fst (Y := A') (Z := B'),
      Over.prodLeftIsoPullback_hom_fst_assoc (Y := A) (Z := B) (h := f.left),
      ← Over.comp_left, prod.map_fst, Over.comp_left]
  · simp only [Category.assoc, pullback.map, pullback.lift_snd]
    rw [Over.prodLeftIsoPullback_hom_snd (Y := A') (Z := B'),
      Over.prodLeftIsoPullback_hom_snd_assoc (Y := A) (Z := B) (h := g.left),
      ← Over.comp_left, prod.map_snd, Over.comp_left]

private lemma pullbackMapFst
    {C : Type*} [Category C] {A B A' B' S : C}
    {f : A ⟶ S} {g : B ⟶ S} {f' : A' ⟶ S} {g' : B' ⟶ S}
    (a : A ⟶ A') (b : B ⟶ B') (c : S ⟶ S)
    (ha : f ≫ c = a ≫ f') (hb : g ≫ c = b ≫ g')
    [HasPullback f g] [HasPullback f' g'] :
    pullback.map f g f' g' a b c ha hb ≫ pullback.fst f' g' =
      pullback.fst f g ≫ a := by
  exact pullback.lift_fst _ _ _

private lemma pullbackMapSnd
    {C : Type*} [Category C] {A B A' B' S : C}
    {f : A ⟶ S} {g : B ⟶ S} {f' : A' ⟶ S} {g' : B' ⟶ S}
    (a : A ⟶ A') (b : B ⟶ B') (c : S ⟶ S)
    (ha : f ≫ c = a ≫ f') (hb : g ≫ c = b ≫ g')
    [HasPullback f g] [HasPullback f' g'] :
    pullback.map f g f' g' a b c ha hb ≫ pullback.snd f' g' =
      pullback.snd f g ≫ b := by
  exact pullback.lift_snd _ _ _

private lemma pulledBackDatum_gluingPullback_snd
    (F : MorphismOfSchemeFamilies.{u})
    (D : DescentData F.targetFamily.f) (i j : F.sourceFamily.I₀) :
    ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫
        pullback.snd (F.sourceFamily.f i)
          (((pulledBackDatum F D).obj j).hom ≫ F.sourceFamily.f j) ≫
        (pulledBackDatumObjIso F D j).hom.left ≫
        pullback.snd (D.obj (F.familyHom.s₀ j)).hom (F.familyHom.h₀ j) =
      pullback.snd (((pulledBackDatum F D).obj i).hom ≫ F.sourceFamily.f i)
        (F.sourceFamily.f j) := by
  have hObj : ((pulledBackDatum F D).obj j).hom =
      (pulledBackDatumObjIso F D j).hom.left ≫
        pullback.snd (D.obj (F.familyHom.s₀ j)).hom (F.familyHom.h₀ j) := by
    simpa only [Over.pullback_obj_hom] using
      (Over.w (pulledBackDatumObjIso F D j).hom).symm
  rw [← hObj]
  exact gluingPullback_snd (pulledBackDatum F D) i j

/-- A functorial pullback of descent data along a morphism of families, with the prescribed
action on objects and the componentwise pullback action on morphisms. -/
public structure PullbackFunctor (F : MorphismOfSchemeFamilies.{u}) where
  /-- The functor on descent data. -/
  functor : DescentData F.targetFamily.f ⥤ DescentData F.sourceFamily.f
  /-- Its value on an object is the pulled-back datum. -/
  obj_eq (D : DescentData F.targetFamily.f) :
    functor.obj D = pulledBackDatum F D
  /-- Its value on a morphism is componentwise base change. -/
  map (D E : DescentData F.targetFamily.f) (φ : D ⟶ E)
      (i : F.sourceFamily.I₀) :
    (eqToHom (obj_eq D)).hom i ≫
        (pulledBackDatumObjIso F D i).hom ≫
        (Over.pullback (F.familyHom.h₀ i)).map (φ.hom (F.familyHom.s₀ i)) =
      (functor.map φ).hom i ≫
        (eqToHom (obj_eq E)).hom i ≫
        (pulledBackDatumObjIso F E i).hom

/-- The pullback of descent data along a morphism of families is functorial. -/
@[stacks 02VS "pullback_functor"]
public noncomputable def pullbackFunctor (F : MorphismOfSchemeFamilies.{u}) :
    PullbackFunctor F :=
  let G : DescentData F.targetFamily.f ⥤ DescentData F.sourceFamily.f :=
    { obj := fun D => pulledBackDatum F D
      map := fun {D E} φ =>
        { hom := fun i =>
            (pulledBackDatumObjIso F D i).hom ≫
              (Over.pullback (F.familyHom.h₀ i)).map (φ.hom (F.familyHom.s₀ i)) ≫
          (pulledBackDatumObjIso F E i).inv
          comm := by
            intro i j
            apply Over.OverMorphism.ext
            simp only [Over.comp_left]
            let aD := (Over.map (F.sourceFamily.f i)).obj ((pulledBackDatum F D).obj i)
            let aE := (Over.map (F.sourceFamily.f i)).obj ((pulledBackDatum F E).obj i)
            let b := Over.mk (F.sourceFamily.f j)
            let c := Over.mk (F.sourceFamily.f i)
            let dD := (Over.map (F.sourceFamily.f j)).obj ((pulledBackDatum F D).obj j)
            let dE := (Over.map (F.sourceFamily.f j)).obj ((pulledBackDatum F E).obj j)
            let srcD := Over.prodLeftIsoPullback aD b
            let srcE := Over.prodLeftIsoPullback aE b
            let tgtD := Over.prodLeftIsoPullback c dD
            let tgtE := Over.prodLeftIsoPullback c dE
            let αi : (pulledBackDatum F D).obj i ⟶ (pulledBackDatum F E).obj i :=
              (pulledBackDatumObjIso F D i).hom ≫
                (Over.pullback (F.familyHom.h₀ i)).map (φ.hom (F.familyHom.s₀ i)) ≫
                (pulledBackDatumObjIso F E i).inv
            let αj : (pulledBackDatum F D).obj j ⟶ (pulledBackDatum F E).obj j :=
              (pulledBackDatumObjIso F D j).hom ≫
                (Over.pullback (F.familyHom.h₀ j)).map (φ.hom (F.familyHom.s₀ j)) ≫
                (pulledBackDatumObjIso F E j).inv
            have hMapSrc := overProdMapLeft
              ((Over.map (F.sourceFamily.f i)).map αi) (𝟙 b)
            have hMapTgt := overProdMapLeft
              (𝟙 c) ((Over.map (F.sourceFamily.f j)).map αj)
            have hGlueD : srcD.hom ≫
                ((pulledBackDatum F D).gluingPullbackIso i j).hom =
                ((pulledBackDatum F D).gluingIso i j).hom.left ≫ tgtD.hom := by
              simp [DescentData.gluingPullbackIso,
                DescentData.gluingIso, Over.map_obj_hom,
                aD, b, c, dD, srcD, tgtD]
            have hGlueE : srcE.hom ≫
                ((pulledBackDatum F E).gluingPullbackIso i j).hom =
                ((pulledBackDatum F E).gluingIso i j).hom.left ≫ tgtE.hom := by
              simp [DescentData.gluingPullbackIso,
                DescentData.gluingIso, Over.map_obj_hom,
                aE, b, c, dE, srcE, tgtE]
            have hφ := congrArg Over.Hom.left
              (φ.comm (F.familyHom.s₀ i) (F.familyHom.s₀ j))
            simp only [Over.comp_left] at hφ
            let targetPair := Over.mk (F.targetFamily.f (F.familyHom.s₀ i)) ⨯
              (Over.map (F.targetFamily.f (F.familyHom.s₀ j))).obj
                (E.obj (F.familyHom.s₀ j))
            have hφsnd := congrArg
              (fun q ↦ q ≫ (prod.snd : targetPair ⟶
                (Over.map (F.targetFamily.f (F.familyHom.s₀ j))).obj
                  (E.obj (F.familyHom.s₀ j))).left) hφ
            simp only [Category.assoc] at hφsnd
            let pSrc := pullback.map
              ((Over.map (F.sourceFamily.f i)).obj ((pulledBackDatum F D).obj i)).hom b.hom
              ((Over.map (F.sourceFamily.f i)).obj ((pulledBackDatum F E).obj i)).hom b.hom
              (((Over.map (F.sourceFamily.f i)).map αi).left) (Over.Hom.left (𝟙 b)) (𝟙 F.sourceBase)
              (by simp)
              (by simp)
            let pTgt := pullback.map c.hom
              ((Over.map (F.sourceFamily.f j)).obj ((pulledBackDatum F D).obj j)).hom c.hom
              ((Over.map (F.sourceFamily.f j)).obj ((pulledBackDatum F E).obj j)).hom
              (Over.Hom.left (𝟙 c)) (((Over.map (F.sourceFamily.f j)).map αj).left) (𝟙 F.sourceBase)
              (by simp)
              (by simp)
            have hpTgtFst : pTgt ≫ pullback.fst c.hom
                ((Over.map (F.sourceFamily.f j)).obj ((pulledBackDatum F E).obj j)).hom =
                pullback.fst c.hom
                  ((Over.map (F.sourceFamily.f j)).obj ((pulledBackDatum F D).obj j)).hom := by
              simp only [pTgt, pullback.map, Over.map_map_left, Over.map_obj_hom]
              rw [pullback.lift_fst]
              simp
            have hpSrcSnd : pSrc ≫ pullback.snd
                ((Over.map (F.sourceFamily.f i)).obj ((pulledBackDatum F E).obj i)).hom b.hom =
                pullback.snd
                  ((Over.map (F.sourceFamily.f i)).obj
                    ((pulledBackDatum F D).obj i)).hom b.hom := by
              simp only [pSrc, pullback.map, Over.map_map_left, Over.map_obj_hom]
              rw [pullback.lift_snd]
              simp
            have hpTgtSnd : pTgt ≫ pullback.snd c.hom
                ((Over.map (F.sourceFamily.f j)).obj ((pulledBackDatum F E).obj j)).hom =
                pullback.snd c.hom
                  ((Over.map (F.sourceFamily.f j)).obj
                    ((pulledBackDatum F D).obj j)).hom ≫ αj.left := by
              simp only [pTgt, pullback.map, Over.map_map_left, Over.map_obj_hom]
              rw [pullback.lift_snd]
            have hObjE : ((pulledBackDatum F E).obj j).hom =
                (pulledBackDatumObjIso F E j).hom.left ≫
                  pullback.snd (E.obj (F.familyHom.s₀ j)).hom (F.familyHom.h₀ j) := by
              simpa only [Over.pullback_obj_hom] using
                (Over.w (pulledBackDatumObjIso F E j).hom).symm
            have hInvI : (pulledBackDatumObjIso F E i).inv.left ≫
                (pulledBackDatumObjIso F E i).hom.left = 𝟙 _ := by
              simpa only [Over.comp_left, Over.id_left] using
                congrArg Over.Hom.left (Iso.inv_hom_id (pulledBackDatumObjIso F E i))
            have hInvJ : (pulledBackDatumObjIso F E j).inv.left ≫
                (pulledBackDatumObjIso F E j).hom.left = 𝟙 _ := by
              simpa only [Over.comp_left, Over.id_left] using
                congrArg Over.Hom.left (Iso.inv_hom_id (pulledBackDatumObjIso F E j))
            have hαiFst : αi.left ≫
                (pulledBackDatumObjIso F E i).hom.left ≫
                  pullback.fst (E.obj (F.familyHom.s₀ i)).hom (F.familyHom.h₀ i) =
                (pulledBackDatumObjIso F D i).hom.left ≫
                  pullback.fst (D.obj (F.familyHom.s₀ i)).hom
                    (F.familyHom.h₀ i) ≫ (φ.hom (F.familyHom.s₀ i)).left := by
              calc
                _ = (pulledBackDatumObjIso F D i).hom.left ≫
                    ((Over.pullback (F.familyHom.h₀ i)).map
                      (φ.hom (F.familyHom.s₀ i))).left ≫
                    pullback.fst (E.obj (F.familyHom.s₀ i)).hom (F.familyHom.h₀ i) := by
                      dsimp [αi]
                      simp [Category.assoc]
                _ = _ := by
                    simp only [Over.pullback_map_left, pullback.lift_fst]
            have hαjFst : αj.left ≫
                (pulledBackDatumObjIso F E j).hom.left ≫
                  pullback.fst (E.obj (F.familyHom.s₀ j)).hom (F.familyHom.h₀ j) =
                (pulledBackDatumObjIso F D j).hom.left ≫
                  pullback.fst (D.obj (F.familyHom.s₀ j)).hom
                    (F.familyHom.h₀ j) ≫ (φ.hom (F.familyHom.s₀ j)).left := by
              calc
                _ = (pulledBackDatumObjIso F D j).hom.left ≫
                    ((Over.pullback (F.familyHom.h₀ j)).map
                      (φ.hom (F.familyHom.s₀ j))).left ≫
                    pullback.fst (E.obj (F.familyHom.s₀ j)).hom (F.familyHom.h₀ j) := by
                      dsimp [αj]
                      simp [Category.assoc]
                _ = _ := by
                    simp only [Over.pullback_map_left, pullback.lift_fst]
            let qSrc := pullback.map
              ((D.obj (F.familyHom.s₀ i)).hom ≫ F.targetFamily.f (F.familyHom.s₀ i))
              (F.targetFamily.f (F.familyHom.s₀ j))
              ((E.obj (F.familyHom.s₀ i)).hom ≫ F.targetFamily.f (F.familyHom.s₀ i))
              (F.targetFamily.f (F.familyHom.s₀ j))
              (φ.hom (F.familyHom.s₀ i)).left (𝟙 (F.targetFamily.X (F.familyHom.s₀ j)))
              (𝟙 F.targetBase)
              (by
                simpa only [Category.assoc, Category.comp_id] using congrArg
                  (fun q ↦ q ≫ F.targetFamily.f (F.familyHom.s₀ i))
                  (Over.w (φ.hom (F.familyHom.s₀ i))).symm)
              (by simp)
            let qTgt := pullback.map
              (F.targetFamily.f (F.familyHom.s₀ i))
              ((D.obj (F.familyHom.s₀ j)).hom ≫ F.targetFamily.f (F.familyHom.s₀ j))
              (F.targetFamily.f (F.familyHom.s₀ i))
              ((E.obj (F.familyHom.s₀ j)).hom ≫ F.targetFamily.f (F.familyHom.s₀ j))
              (𝟙 (F.targetFamily.X (F.familyHom.s₀ i)))
              (φ.hom (F.familyHom.s₀ j)).left (𝟙 F.targetBase)
              (by simp)
              (by
                simpa only [Category.assoc, Category.comp_id] using congrArg
                  (fun q ↦ q ≫ F.targetFamily.f (F.familyHom.s₀ j))
                  (Over.w (φ.hom (F.familyHom.s₀ j))).symm)
            have hSourceMapNat : pSrc ≫ pulledBackDatumSourceMap F E i j =
                pulledBackDatumSourceMap F D i j ≫ qSrc := by
              apply pullback.hom_ext
              · have hpSrcFst : pSrc ≫ pullback.fst
                    ((Over.map (F.sourceFamily.f i)).obj ((pulledBackDatum F E).obj i)).hom
                    (F.sourceFamily.f j) =
                    pullback.fst ((Over.map (F.sourceFamily.f i)).obj
                      ((pulledBackDatum F D).obj i)).hom (F.sourceFamily.f j) ≫
                      Over.Hom.left ((Over.map (F.sourceFamily.f i)).map αi) := by
                  dsimp [pSrc]
                  apply pullbackMapFst
                have hSourceEFst : pulledBackDatumSourceMap F E i j ≫
                    pullback.fst ((E.obj (F.familyHom.s₀ i)).hom ≫
                      F.targetFamily.f (F.familyHom.s₀ i))
                      (F.targetFamily.f (F.familyHom.s₀ j)) =
                    pullback.fst (((Over.map (F.sourceFamily.f i)).obj
                      ((pulledBackDatum F E).obj i)).hom) (F.sourceFamily.f j) ≫
                      (pulledBackDatumObjIso F E i).hom.left ≫
                      pullback.fst (E.obj (F.familyHom.s₀ i)).hom (F.familyHom.h₀ i) := by
                  simp [pulledBackDatumSourceMap]
                have hSourceDFst : pulledBackDatumSourceMap F D i j ≫
                    pullback.fst ((D.obj (F.familyHom.s₀ i)).hom ≫
                      F.targetFamily.f (F.familyHom.s₀ i))
                      (F.targetFamily.f (F.familyHom.s₀ j)) =
                    pullback.fst (((Over.map (F.sourceFamily.f i)).obj
                      ((pulledBackDatum F D).obj i)).hom) (F.sourceFamily.f j) ≫
                      (pulledBackDatumObjIso F D i).hom.left ≫
                      pullback.fst (D.obj (F.familyHom.s₀ i)).hom (F.familyHom.h₀ i) := by
                  simp [pulledBackDatumSourceMap]
                have hqSrcFst : qSrc ≫ pullback.fst
                    ((E.obj (F.familyHom.s₀ i)).hom ≫
                      F.targetFamily.f (F.familyHom.s₀ i))
                      (F.targetFamily.f (F.familyHom.s₀ j)) =
                    pullback.fst ((D.obj (F.familyHom.s₀ i)).hom ≫
                      F.targetFamily.f (F.familyHom.s₀ i))
                      (F.targetFamily.f (F.familyHom.s₀ j)) ≫
                      (φ.hom (F.familyHom.s₀ i)).left := by
                  simp [qSrc, pullback.map]
                calc
                  (pSrc ≫ pulledBackDatumSourceMap F E i j) ≫
                      pullback.fst ((E.obj (F.familyHom.s₀ i)).hom ≫
                        F.targetFamily.f (F.familyHom.s₀ i))
                        (F.targetFamily.f (F.familyHom.s₀ j)) =
                      pSrc ≫ (pulledBackDatumSourceMap F E i j ≫
                        pullback.fst ((E.obj (F.familyHom.s₀ i)).hom ≫
                          F.targetFamily.f (F.familyHom.s₀ i))
                          (F.targetFamily.f (F.familyHom.s₀ j))) := by
                    simp [Category.assoc]
                  _ = pSrc ≫ (pullback.fst (((Over.map (F.sourceFamily.f i)).obj
                        ((pulledBackDatum F E).obj i)).hom) (F.sourceFamily.f j) ≫
                      (pulledBackDatumObjIso F E i).hom.left ≫
                      pullback.fst (E.obj (F.familyHom.s₀ i)).hom
                        (F.familyHom.h₀ i)) := by rw [hSourceEFst]
                  _ = pullback.fst (((Over.map (F.sourceFamily.f i)).obj
                        ((pulledBackDatum F D).obj i)).hom) (F.sourceFamily.f j) ≫
                      Over.Hom.left ((Over.map (F.sourceFamily.f i)).map αi) ≫
                      (pulledBackDatumObjIso F E i).hom.left ≫
                      pullback.fst (E.obj (F.familyHom.s₀ i)).hom
                        (F.familyHom.h₀ i) := by
                    simpa only [Category.assoc] using
                      congrArg (fun q ↦ q ≫ (pulledBackDatumObjIso F E i).hom.left ≫
                        pullback.fst (E.obj (F.familyHom.s₀ i)).hom (F.familyHom.h₀ i)) hpSrcFst
                  _ = pullback.fst (((Over.map (F.sourceFamily.f i)).obj
                        ((pulledBackDatum F D).obj i)).hom) (F.sourceFamily.f j) ≫
                      (pulledBackDatumObjIso F D i).hom.left ≫
                      pullback.fst (D.obj (F.familyHom.s₀ i)).hom
                        (F.familyHom.h₀ i) ≫ (φ.hom (F.familyHom.s₀ i)).left := by
                    simpa only [Over.map_map_left, Category.assoc] using
                      congrArg (fun q ↦ pullback.fst (((Over.map (F.sourceFamily.f i)).obj
                        ((pulledBackDatum F D).obj i)).hom) (F.sourceFamily.f j) ≫ q) hαiFst
                  _ = (pulledBackDatumSourceMap F D i j ≫
                      pullback.fst ((D.obj (F.familyHom.s₀ i)).hom ≫
                        F.targetFamily.f (F.familyHom.s₀ i))
                        (F.targetFamily.f (F.familyHom.s₀ j))) ≫
                      (φ.hom (F.familyHom.s₀ i)).left := by
                    simpa only [Category.assoc] using
                      congrArg (fun q ↦ q ≫ (φ.hom (F.familyHom.s₀ i)).left) hSourceDFst.symm
                  _ = pulledBackDatumSourceMap F D i j ≫
                      (qSrc ≫ pullback.fst ((E.obj (F.familyHom.s₀ i)).hom ≫
                        F.targetFamily.f (F.familyHom.s₀ i))
                        (F.targetFamily.f (F.familyHom.s₀ j))) := by
                    simpa only [Category.assoc] using
                      congrArg (fun q ↦ pulledBackDatumSourceMap F D i j ≫ q) hqSrcFst.symm
                  _ = _ := by simp [Category.assoc]
              · simpa [qSrc, pulledBackDatumSourceMap, pullback.map,
                  pullback.lift_snd, pullback.lift_fst_assoc,
                  pullback.lift_snd_assoc, b, Over.map_obj_hom, Category.assoc] using
                  congrArg (fun q ↦ q ≫ F.familyHom.h₀ j) hpSrcSnd
            have hTargetMapNat : pTgt ≫ pulledBackDatumTargetMap F E i j =
                pulledBackDatumTargetMap F D i j ≫ qTgt := by
              apply pullback.hom_ext
              · calc
                  (pTgt ≫ pulledBackDatumTargetMap F E i j) ≫ _ = pTgt ≫ pullback.fst c.hom
                        ((Over.map (F.sourceFamily.f j)).obj
                          ((pulledBackDatum F E).obj j)).hom ≫ F.familyHom.h₀ i := by
                    simp [pulledBackDatumTargetMap,
                      Category.assoc, c]
                  _ = pullback.fst c.hom
                        ((Over.map (F.sourceFamily.f j)).obj
                          ((pulledBackDatum F D).obj j)).hom ≫ F.familyHom.h₀ i := by
                    simpa [Category.assoc, c] using
                      congrArg (fun q ↦ q ≫ F.familyHom.h₀ i) hpTgtFst
                  _ = _ := by
                    simp [qTgt, pulledBackDatumTargetMap, pullback.map,
                      Category.assoc, c]
              · have hTargetESnd : pulledBackDatumTargetMap F E i j ≫
                    pullback.snd (F.targetFamily.f (F.familyHom.s₀ i))
                      ((E.obj (F.familyHom.s₀ j)).hom ≫
                        F.targetFamily.f (F.familyHom.s₀ j)) =
                    pullback.snd (F.sourceFamily.f i)
                      (((pulledBackDatum F E).obj j).hom ≫ F.sourceFamily.f j) ≫
                      (pulledBackDatumObjIso F E j).hom.left ≫
                      pullback.fst (E.obj (F.familyHom.s₀ j)).hom
                        (F.familyHom.h₀ j) := by
                  simp [pulledBackDatumTargetMap]
                have hTargetDSnd : pulledBackDatumTargetMap F D i j ≫
                    pullback.snd (F.targetFamily.f (F.familyHom.s₀ i))
                      ((D.obj (F.familyHom.s₀ j)).hom ≫
                        F.targetFamily.f (F.familyHom.s₀ j)) =
                    pullback.snd (F.sourceFamily.f i)
                      (((pulledBackDatum F D).obj j).hom ≫ F.sourceFamily.f j) ≫
                      (pulledBackDatumObjIso F D j).hom.left ≫
                      pullback.fst (D.obj (F.familyHom.s₀ j)).hom
                        (F.familyHom.h₀ j) := by
                  simp [pulledBackDatumTargetMap]
                have hpTgtSnd' : pTgt ≫
                    pullback.snd (F.sourceFamily.f i)
                      (((pulledBackDatum F E).obj j).hom ≫ F.sourceFamily.f j) =
                    pullback.snd (F.sourceFamily.f i)
                      (((pulledBackDatum F D).obj j).hom ≫ F.sourceFamily.f j) ≫ αj.left := by
                  simpa [c, Over.map_obj_hom, Over.mk_hom] using hpTgtSnd
                have hqTgtSnd : qTgt ≫
                    pullback.snd (F.targetFamily.f (F.familyHom.s₀ i))
                      ((E.obj (F.familyHom.s₀ j)).hom ≫
                        F.targetFamily.f (F.familyHom.s₀ j)) =
                    pullback.snd (F.targetFamily.f (F.familyHom.s₀ i))
                      ((D.obj (F.familyHom.s₀ j)).hom ≫
                        F.targetFamily.f (F.familyHom.s₀ j)) ≫
                      (φ.hom (F.familyHom.s₀ j)).left := by
                  simp [qTgt, pullback.map]
                calc
                  (pTgt ≫ pulledBackDatumTargetMap F E i j) ≫
                      pullback.snd (F.targetFamily.f (F.familyHom.s₀ i))
                        ((E.obj (F.familyHom.s₀ j)).hom ≫
                          F.targetFamily.f (F.familyHom.s₀ j)) =
                      pTgt ≫ (pulledBackDatumTargetMap F E i j ≫
                        pullback.snd (F.targetFamily.f (F.familyHom.s₀ i))
                          ((E.obj (F.familyHom.s₀ j)).hom ≫
                            F.targetFamily.f (F.familyHom.s₀ j))) := by
                    simp [Category.assoc]
                  _ = pTgt ≫ (pullback.snd (F.sourceFamily.f i)
                        (((pulledBackDatum F E).obj j).hom ≫ F.sourceFamily.f j) ≫
                      (pulledBackDatumObjIso F E j).hom.left ≫
                      pullback.fst (E.obj (F.familyHom.s₀ j)).hom
                        (F.familyHom.h₀ j)) := by rw [hTargetESnd]
                  _ = pullback.snd (F.sourceFamily.f i)
                        (((pulledBackDatum F D).obj j).hom ≫ F.sourceFamily.f j) ≫
                      Over.Hom.left αj ≫
                      (pulledBackDatumObjIso F E j).hom.left ≫
                      pullback.fst (E.obj (F.familyHom.s₀ j)).hom
                        (F.familyHom.h₀ j) := by
                    simpa only [Category.assoc] using
                      congrArg (fun q ↦ q ≫ (pulledBackDatumObjIso F E j).hom.left ≫
                        pullback.fst (E.obj (F.familyHom.s₀ j)).hom
                          (F.familyHom.h₀ j)) hpTgtSnd'
                  _ = pullback.snd (F.sourceFamily.f i)
                        (((pulledBackDatum F D).obj j).hom ≫ F.sourceFamily.f j) ≫
                      (pulledBackDatumObjIso F D j).hom.left ≫
                      pullback.fst (D.obj (F.familyHom.s₀ j)).hom
                        (F.familyHom.h₀ j) ≫ (φ.hom (F.familyHom.s₀ j)).left := by
                    simpa only [Category.assoc] using
                      congrArg (fun q ↦ pullback.snd (F.sourceFamily.f i)
                        (((pulledBackDatum F D).obj j).hom ≫ F.sourceFamily.f j) ≫ q) hαjFst
                  _ = (pulledBackDatumTargetMap F D i j ≫
                      pullback.snd (F.targetFamily.f (F.familyHom.s₀ i))
                        ((D.obj (F.familyHom.s₀ j)).hom ≫
                          F.targetFamily.f (F.familyHom.s₀ j))) ≫
                      (φ.hom (F.familyHom.s₀ j)).left := by
                    simpa only [Category.assoc] using
                      congrArg (fun q ↦ q ≫ (φ.hom (F.familyHom.s₀ j)).left) hTargetDSnd.symm
                  _ = pulledBackDatumTargetMap F D i j ≫
                      (qTgt ≫ pullback.snd (F.targetFamily.f (F.familyHom.s₀ i))
                        ((E.obj (F.familyHom.s₀ j)).hom ≫
                          F.targetFamily.f (F.familyHom.s₀ j))) := by
                    simpa only [Category.assoc] using
                      congrArg (fun q ↦ pulledBackDatumTargetMap F D i j ≫ q) hqTgtSnd.symm
                  _ = _ := by simp [Category.assoc]
            have hGlobalGlue : qSrc ≫
                (E.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).hom =
                (D.gluingPullbackIso (F.familyHom.s₀ i) (F.familyHom.s₀ j)).hom ≫ qTgt := by
              let srcD := Over.prodLeftIsoPullback
                ((Over.map (F.targetFamily.f (F.familyHom.s₀ i))).obj
                  (D.obj (F.familyHom.s₀ i)))
                (Over.mk (F.targetFamily.f (F.familyHom.s₀ j)))
              let srcE := Over.prodLeftIsoPullback
                ((Over.map (F.targetFamily.f (F.familyHom.s₀ i))).obj
                  (E.obj (F.familyHom.s₀ i)))
                (Over.mk (F.targetFamily.f (F.familyHom.s₀ j)))
              let tgtD := Over.prodLeftIsoPullback
                (Over.mk (F.targetFamily.f (F.familyHom.s₀ i)))
                ((Over.map (F.targetFamily.f (F.familyHom.s₀ j))).obj
                  (D.obj (F.familyHom.s₀ j)))
              let tgtE := Over.prodLeftIsoPullback
                (Over.mk (F.targetFamily.f (F.familyHom.s₀ i)))
                ((Over.map (F.targetFamily.f (F.familyHom.s₀ j))).obj
                  (E.obj (F.familyHom.s₀ j)))
              let mSrc := prod.map
                (((Over.map (F.targetFamily.f (F.familyHom.s₀ i))).map
                  (φ.hom (F.familyHom.s₀ i))))
                (𝟙 (Over.mk (F.targetFamily.f (F.familyHom.s₀ j))))
              let mTgt := prod.map
                (𝟙 (Over.mk (F.targetFamily.f (F.familyHom.s₀ i))))
                (((Over.map (F.targetFamily.f (F.familyHom.s₀ j))).map
                  (φ.hom (F.familyHom.s₀ j))))
              have hMapSrcG := overProdMapLeft
                ((Over.map (F.targetFamily.f (F.familyHom.s₀ i))).map
                  (φ.hom (F.familyHom.s₀ i)))
                (𝟙 (Over.mk (F.targetFamily.f (F.familyHom.s₀ j))))
              have hMapTgtG := overProdMapLeft
                (𝟙 (Over.mk (F.targetFamily.f (F.familyHom.s₀ i))))
                ((Over.map (F.targetFamily.f (F.familyHom.s₀ j))).map
                  (φ.hom (F.familyHom.s₀ j)))
              have hMapSrcGlob : srcD.hom ≫ qSrc =
                  Over.Hom.left mSrc ≫ srcE.hom := by
                simpa [srcD, srcE, qSrc, mSrc] using hMapSrcG.symm
              have hMapTgtGlob : Over.Hom.left mTgt ≫ tgtE.hom =
                  tgtD.hom ≫ qTgt := by
                simpa [tgtD, tgtE, qTgt, mTgt] using hMapTgtG
              apply (cancel_mono tgtE.inv).mp
              apply (cancel_epi srcD.hom).mp
              calc
                _ = Over.Hom.left mSrc ≫ srcE.hom ≫
                    (E.gluingPullbackIso (F.familyHom.s₀ i)
                      (F.familyHom.s₀ j)).hom ≫ tgtE.inv :=
                    congrArg (fun q ↦ q ≫
                      (E.gluingPullbackIso (F.familyHom.s₀ i)
                        (F.familyHom.s₀ j)).hom ≫ tgtE.inv) hMapSrcGlob
                _ = Over.Hom.left mSrc ≫
                    Over.Hom.left (E.gluingIso (F.familyHom.s₀ i)
                      (F.familyHom.s₀ j)).hom ≫ tgtE.hom ≫ tgtE.inv := by
                    simp [srcE, tgtE, DescentData.gluingPullbackIso,
                      DescentData.gluingIso, Category.assoc]
                _ = Over.Hom.left mSrc ≫
                    Over.Hom.left (E.gluingIso (F.familyHom.s₀ i)
                      (F.familyHom.s₀ j)).hom := by simp
                _ = Over.Hom.left (D.gluingIso (F.familyHom.s₀ i)
                    (F.familyHom.s₀ j)).hom ≫ Over.Hom.left mTgt := by
                    simpa [mSrc, mTgt] using hφ
                _ = Over.Hom.left (D.gluingIso (F.familyHom.s₀ i)
                    (F.familyHom.s₀ j)).hom ≫ Over.Hom.left mTgt ≫ tgtE.hom ≫ tgtE.inv := by
                    simp
                _ = Over.Hom.left (D.gluingIso (F.familyHom.s₀ i)
                    (F.familyHom.s₀ j)).hom ≫ tgtD.hom ≫ qTgt ≫ tgtE.inv := by
                    calc
                      _ = Over.Hom.left (D.gluingIso
                            (F.familyHom.s₀ i) (F.familyHom.s₀ j)).hom ≫
                          (Over.Hom.left mTgt ≫ tgtE.hom) ≫ tgtE.inv := by
                            simp only [Category.assoc]
                      _ = _ := by
                        rw [hMapTgtGlob]
                        simp [Category.assoc]
                _ = srcD.hom ≫
                    (D.gluingPullbackIso (F.familyHom.s₀ i)
                      (F.familyHom.s₀ j)).hom ≫ qTgt ≫ tgtE.inv := by
                    simp [srcD, tgtD, DescentData.gluingPullbackIso,
                      DescentData.gluingIso, Category.assoc]
            have hCentralTarget :
                pSrc ≫ ((pulledBackDatum F E).gluingPullbackIso i j).hom ≫
                    pulledBackDatumTargetMap F E i j =
                ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫ pTgt ≫
                    pulledBackDatumTargetMap F E i j := by
              calc
                _ = pSrc ≫ pulledBackDatumSourceMap F E i j ≫
                    (E.gluingPullbackIso (F.familyHom.s₀ i)
                      (F.familyHom.s₀ j)).hom := by
                    simpa only [Category.assoc] using congrArg
                      (fun q ↦ pSrc ≫ q)
                      (pulledBackDatum_gluing F E i j)
                _ = pulledBackDatumSourceMap F D i j ≫ qSrc ≫
                    (E.gluingPullbackIso (F.familyHom.s₀ i)
                      (F.familyHom.s₀ j)).hom := by
                    simpa only [Category.assoc] using congrArg
                      (fun q ↦ q ≫
                        (E.gluingPullbackIso (F.familyHom.s₀ i)
                          (F.familyHom.s₀ j)).hom) hSourceMapNat
                _ = pulledBackDatumSourceMap F D i j ≫
                    (D.gluingPullbackIso (F.familyHom.s₀ i)
                      (F.familyHom.s₀ j)).hom ≫ qTgt := by
                    simpa only [Category.assoc] using congrArg
                      (fun q ↦ pulledBackDatumSourceMap F D i j ≫ q) hGlobalGlue
                _ = ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫
                    pulledBackDatumTargetMap F D i j ≫ qTgt := by
                    simpa only [Category.assoc] using congrArg
                      (fun q ↦ q ≫ qTgt)
                      (pulledBackDatum_gluing F D i j).symm
                _ = ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫ pTgt ≫
                    pulledBackDatumTargetMap F E i j := by
                    simpa only [Category.assoc] using congrArg
                      (fun q ↦ ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫ q)
                      hTargetMapNat.symm
            have hCentral : pSrc ≫ ((pulledBackDatum F E).gluingPullbackIso i j).hom =
                ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫ pTgt := by
              apply pullback.hom_ext
              · calc
                  pSrc ≫ ((pulledBackDatum F E).gluingPullbackIso i j).hom ≫
                      pullback.fst _ _ =
                    pSrc ≫ pullback.fst _ _ ≫ ((pulledBackDatum F E).obj i).hom := by
                      rw [gluingPullback_fst]
                      simp [Over.map_obj_hom, b]
                  _ = pullback.fst _ _ ≫ ((pulledBackDatum F D).obj i).hom := by
                    simp only [pSrc, pullback.map, Over.map_map_left,
                      Over.map_obj_hom]
                    rw [← Category.assoc, pullback.lift_fst]
                    rw [Category.assoc, Over.w αi]
                  _ = ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫
                      pTgt ≫ pullback.fst _ _ := by
                    rw [hpTgtFst]
                    simpa [b, c, Over.map_obj_hom] using
                      (gluingPullback_fst (pulledBackDatum F D) i j).symm
              · apply (cancel_mono (pulledBackDatumObjIso F E j).hom.left).mp
                apply pullback.hom_ext
                · have hProj := congrArg
                    (fun q ↦ q ≫ pullback.snd
                      (F.targetFamily.f (F.familyHom.s₀ i))
                      ((E.obj (F.familyHom.s₀ j)).hom ≫
                        F.targetFamily.f (F.familyHom.s₀ j))) hCentralTarget
                  simpa [pulledBackDatumTargetMap, pullback.lift_snd,
                    Category.assoc] using hProj
                · have hObjD : ((pulledBackDatum F D).obj j).hom =
                    (pulledBackDatumObjIso F D j).hom.left ≫
                      pullback.snd (D.obj (F.familyHom.s₀ j)).hom
                        (F.familyHom.h₀ j) := by
                    simpa only [Over.pullback_obj_hom] using
                      (Over.w (pulledBackDatumObjIso F D j).hom).symm
                  have hαjSnd : αj.left ≫ (pulledBackDatumObjIso F E j).hom.left ≫
                      pullback.snd (E.obj (F.familyHom.s₀ j)).hom
                        (F.familyHom.h₀ j) =
                    (pulledBackDatumObjIso F D j).hom.left ≫
                      pullback.snd (D.obj (F.familyHom.s₀ j)).hom
                        (F.familyHom.h₀ j) := by
                    rw [← hObjE]
                    exact (Over.w αj).trans hObjD
                  calc
                    _ = pSrc ≫ pullback.snd
                        ((Over.map (F.sourceFamily.f i)).obj
                          ((pulledBackDatum F E).obj i)).hom
                        (F.sourceFamily.f j) := by
                      simpa [Category.assoc, Over.map_obj_hom] using congrArg
                        (fun q ↦ pSrc ≫ q)
                        (pulledBackDatum_gluingPullback_snd F E i j)
                    _ = pullback.snd
                        ((Over.map (F.sourceFamily.f i)).obj
                          ((pulledBackDatum F D).obj i)).hom
                        (F.sourceFamily.f j) := by
                      simpa [b, Over.map_obj_hom] using hpSrcSnd
                    _ = ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫
                        pTgt ≫ pullback.snd
                          (F.sourceFamily.f i)
                          (((pulledBackDatum F E).obj j).hom ≫
                            F.sourceFamily.f j) ≫
                        (pulledBackDatumObjIso F E j).hom.left ≫
                        pullback.snd (E.obj (F.familyHom.s₀ j)).hom
                          (F.familyHom.h₀ j) := by
                      have hRhs :
                          ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫
                            pTgt ≫ pullback.snd (F.sourceFamily.f i)
                              (((pulledBackDatum F E).obj j).hom ≫ F.sourceFamily.f j) ≫
                            (pulledBackDatumObjIso F E j).hom.left ≫
                            pullback.snd (E.obj (F.familyHom.s₀ j)).hom
                              (F.familyHom.h₀ j) =
                          ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫
                            pullback.snd (F.sourceFamily.f i)
                              (((pulledBackDatum F D).obj j).hom ≫ F.sourceFamily.f j) ≫
                            ((pulledBackDatum F D).obj j).hom := by
                        have hpSnd' : pTgt ≫ pullback.snd (F.sourceFamily.f i)
                            (((pulledBackDatum F E).obj j).hom ≫ F.sourceFamily.f j) =
                          pullback.snd (F.sourceFamily.f i)
                            (((pulledBackDatum F D).obj j).hom ≫ F.sourceFamily.f j) ≫
                            αj.left := by
                          simpa [c, Over.map_obj_hom] using hpTgtSnd
                        calc
                          _ = ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫
                              (pTgt ≫ pullback.snd (F.sourceFamily.f i)
                                (((pulledBackDatum F E).obj j).hom ≫ F.sourceFamily.f j)) ≫
                              (pulledBackDatumObjIso F E j).hom.left ≫
                              pullback.snd (E.obj (F.familyHom.s₀ j)).hom
                                (F.familyHom.h₀ j) := by
                            simp only [Category.assoc]
                          _ = ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫
                              pullback.snd (F.sourceFamily.f i)
                                (((pulledBackDatum F D).obj j).hom ≫ F.sourceFamily.f j) ≫
                              αj.left ≫ (pulledBackDatumObjIso F E j).hom.left ≫
                              pullback.snd (E.obj (F.familyHom.s₀ j)).hom
                                (F.familyHom.h₀ j) := by
                            simpa [Category.assoc] using congrArg
                              (fun q ↦ ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫
                                q ≫ (pulledBackDatumObjIso F E j).hom.left ≫
                                pullback.snd (E.obj (F.familyHom.s₀ j)).hom
                                  (F.familyHom.h₀ j)) hpSnd'
                          _ = _ := by
                            calc
                              _ = ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫
                                  pullback.snd (F.sourceFamily.f i)
                                    (((pulledBackDatum F D).obj j).hom ≫
                                      F.sourceFamily.f j) ≫
                                  (Over.Hom.left αj ≫
                                    (pulledBackDatumObjIso F E j).hom.left ≫
                                    pullback.snd (E.obj (F.familyHom.s₀ j)).hom
                                      (F.familyHom.h₀ j)) := by
                                simp only []
                              _ = ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫
                                  pullback.snd (F.sourceFamily.f i)
                                    (((pulledBackDatum F D).obj j).hom ≫
                                      F.sourceFamily.f j) ≫
                                  ((pulledBackDatum F D).obj j).hom := by
                                simpa only [Category.assoc, ← hObjD] using congrArg
                                  (fun q ↦ ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫
                                    pullback.snd (F.sourceFamily.f i)
                                      (((pulledBackDatum F D).obj j).hom ≫
                                        F.sourceFamily.f j) ≫ q) hαjSnd
                      calc
                        _ = ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫
                            pullback.snd (F.sourceFamily.f i)
                              (((pulledBackDatum F D).obj j).hom ≫ F.sourceFamily.f j) ≫
                            ((pulledBackDatum F D).obj j).hom := by
                          simpa [Over.map_obj_hom] using
                            (gluingPullback_snd (pulledBackDatum F D) i j).symm
                        _ = _ := hRhs.symm
            apply (cancel_mono tgtE.hom).mp
            calc
              Over.Hom.left (prod.map ((Over.map (F.sourceFamily.f i)).map αi) (𝟙 b)) ≫
                  ((pulledBackDatum F E).gluingIso i j).hom.left ≫ tgtE.hom =
                Over.Hom.left (prod.map ((Over.map (F.sourceFamily.f i)).map αi) (𝟙 b)) ≫
                  srcE.hom ≫ ((pulledBackDatum F E).gluingPullbackIso i j).hom := by
                    simpa only [Category.assoc] using
                      congrArg (fun q ↦
                        Over.Hom.left (prod.map ((Over.map (F.sourceFamily.f i)).map αi)
                          (𝟙 b)) ≫ q) hGlueE.symm
              _ = srcD.hom ≫ pSrc ≫ ((pulledBackDatum F E).gluingPullbackIso i j).hom := by
                    simpa only [Category.assoc] using
                      congrArg (fun q ↦ q ≫
                        ((pulledBackDatum F E).gluingPullbackIso i j).hom) hMapSrc
              _ = srcD.hom ≫ ((pulledBackDatum F D).gluingPullbackIso i j).hom ≫ pTgt :=
                    congrArg (fun q ↦ srcD.hom ≫ q) hCentral
              _ = Over.Hom.left ((pulledBackDatum F D).gluingIso i j).hom ≫ tgtD.hom ≫ pTgt := by
                    simpa only [Category.assoc] using
                      congrArg (fun q ↦ q ≫ pTgt) hGlueD
              _ = Over.Hom.left ((pulledBackDatum F D).gluingIso i j).hom ≫
                    Over.Hom.left (prod.map (𝟙 c)
                      ((Over.map (F.sourceFamily.f j)).map αj)) ≫ tgtE.hom := by
                    calc
                      _ = Over.Hom.left ((pulledBackDatum F D).gluingIso i j).hom ≫
                          (Over.Hom.left (prod.map (𝟙 c)
                            ((Over.map (F.sourceFamily.f j)).map αj)) ≫
                              tgtE.hom) := by
                            simpa only [Category.assoc] using
                              congrArg (fun q ↦
                                Over.Hom.left ((pulledBackDatum F D).gluingIso i j).hom ≫ q)
                                hMapTgt.symm
                      _ = _ := rfl }

      map_id := by
        intro D
        apply DescentData.hom_ext
        intro i
        simp
      map_comp := by
        intro D E H φ ψ
        apply DescentData.hom_ext
        intro i
        simp [Category.assoc] }
  { functor := G
    obj_eq := fun _ => rfl
    map := by
      intro D E φ i
      simp [G, Category.assoc] }

end AlgebraicGeometry.MorphismOfSchemeFamilies

add_to_stacks 02VT AlgebraicGeometry.MorphismOfSchemeFamilies.pullbackFunctor
