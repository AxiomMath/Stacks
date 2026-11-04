module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.SpacesOverSpaces.FamilyPullback

/-!
# The pullback functor on descent data for families of algebraic spaces

A morphism of families of algebraic spaces with fixed targets induces a functor between their
categories of descent data. On objects it is the componentwise pullback datum, and on
morphisms it is componentwise base change.

## Main definitions

* `AlgebraicGeometry.Space.Descent.PullbackFunctor` specifies the functor by its action on
  objects and on morphisms.

## Main results

* `AlgebraicGeometry.Space.Descent.pullbackFunctor` constructs the specified functor. It is
  also the functor named by Tag 0ADP.

## Implementation notes

The object equation identifies the value of the functor with the datum constructed by
`AlgebraicGeometry.Space.Descent.pullbackDatum`, which already specifies the component pullback
squares and the base-changed gluing isomorphisms. The morphism equation says that the
componentwise map is the one induced by those pullback squares.

## References

* [Stacks Project, Tag 0ADN](https://stacks.math.columbia.edu/tag/0ADN)
* [Stacks Project, Tag 0ADP](https://stacks.math.columbia.edu/tag/0ADP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry.Space.Descent

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {ι : Type v} {ι' : Type w}
variable {X : ι → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable {X' : ι' → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
variable (f : ∀ i, X i ⟶ T) (f' : ∀ i, X' i ⟶ T')
variable (hT : IsAlgebraicSpace B S hS T)
variable (hX : ∀ i, IsAlgebraicSpace B S hS (X i))
variable (hT' : IsAlgebraicSpace B S hS T')
variable (hX' : ∀ i, IsAlgebraicSpace B S hS (X' i))
variable (α : ι' → ι) (g : T' ⟶ T) (gᵢ : ∀ i, X' i ⟶ X (α i))
variable (comm : ∀ i, gᵢ i ≫ f (α i) = f' i ≫ g)

/-- A functor on descent data induced by a morphism of families, together with
its specified action on objects and morphisms. -/
public structure PullbackFunctor where
  /-- The underlying functor on categories of descent data. -/
  functor : DescentData f hT hX ⥤
    DescentData f' hT' hX'
  /-- The functor sends a descent datum to the pulled-back datum. -/
  obj_eq (D : DescentData f hT hX) :
    functor.obj D =
      (pullbackDatum
        f f' hT hX hT' hX' α gᵢ D g comm).datum
  /-- On each component the functor is the map induced by the component pullback squares. -/
  map (D E : DescentData f hT hX) (φ : D ⟶ E) (i : ι') :
    ((eqToHom (obj_eq D)).hom i).left ≫
        (pullbackDatum
          f f' hT hX hT' hX' α gᵢ D g comm).objMap i ≫
        (φ.hom (α i)).left =
      ((functor.map φ).hom i).left ≫
        ((eqToHom (obj_eq E)).hom i).left ≫
        (pullbackDatum
          f f' hT hX hT' hX' α gᵢ E g comm).objMap i

/-- Pullback along a morphism of families is functorial on descent data. This is the pullback
functor named by Tag 0ADP. -/
@[stacks 0ADN "family_pullback_functor", stacks 0ADP]
public noncomputable def pullbackFunctor :
    PullbackFunctor f f' hT hX hT' hX' α g gᵢ comm :=
  let P (D : DescentData f hT hX) :=
    pullbackDatum
      f f' hT hX hT' hX' α gᵢ D g comm
  let m (D E : DescentData f hT hX) (φ : D ⟶ E) (i : ι') :
      (P D).datum.obj i ⟶ (P E).datum.obj i :=
    Over.homMk
      ((P E).obj_isPullback i |>.lift ((P D).datum.obj i).hom
        ((P D).objMap i ≫ (φ.hom (α i)).left) (by
          calc
            ((P D).datum.obj i).hom ≫ gᵢ i =
                (P D).objMap i ≫ (D.obj (α i)).hom := (P D).obj_isPullback i |>.w
            _ = (P D).objMap i ≫
                ((φ.hom (α i)).left ≫ (E.obj (α i)).hom) := by rw [Over.w]
            _ = _ := by simp [Category.assoc]))
      (by simp only [IsPullback.lift_fst])
  let F : DescentData f hT hX ⥤
      DescentData f' hT' hX' :=
    { obj := fun D => (P D).datum
      map := fun {D E} φ =>
        { hom := fun i => m D E φ i
          comm := by
            intro i j
            cases (P D).source_eq_new i j
            cases (P D).source_eq_old i j
            cases (P E).source_eq_new i j
            cases (P E).source_eq_old i j
            cases (P D).target_eq_new i j
            cases (P D).target_eq_old i j
            cases (P E).target_eq_new i j
            cases (P E).target_eq_old i j
            apply prod.hom_ext
            · apply Over.OverMorphism.ext
              have hE := Over.w ((P E).datum.gluing i j).hom
              have hEfst := congrArg (fun z => z ≫
                (prod.fst : Over.mk (f' i) ⨯ Over.mk (f' j) ⟶ Over.mk (f' i))) hE
              simp only [Over.mk_hom, Category.assoc, prod.map_fst,
                Category.comp_id] at hEfst
              have hEfst := congrArg Over.Hom.left hEfst
              simp only [Over.comp_left] at hEfst
              have hD := Over.w ((P D).datum.gluing i j).hom
              have hDfst := congrArg (fun z => z ≫
                (prod.fst : Over.mk (f' i) ⨯ Over.mk (f' j) ⟶ Over.mk (f' i))) hD
              simp only [Over.mk_hom, Category.assoc, prod.map_fst,
                Category.comp_id] at hDfst
              have hDfst := congrArg Over.Hom.left hDfst
              simp only [Over.comp_left] at hDfst
              simp only [prod.map_fst, Over.comp_left,
                Category.assoc]
              rw [hEfst]
              simp only [Over.id_left, Category.comp_id]
              rw [hDfst]
              let m_i := m D E φ i
              have hm_i := Over.w m_i
              have hMapFst := congrArg Over.Hom.left
                (prod.map_fst ((Over.map (f' i)).map m_i) (𝟙 (Over.mk (f' j))))
              simp only [Over.comp_left] at hMapFst
              change Over.Hom.left
                  (prod.map ((Over.map (f' i)).map m_i) (𝟙 (Over.mk (f' j)))) ≫
                  Over.Hom.left prod.fst ≫
                    Over.Hom.left (structureMap (f' i) ((P E).datum.obj i)) =
                Over.Hom.left prod.fst ≫
                  Over.Hom.left (structureMap (f' i) ((P D).datum.obj i))
              calc
                _ = (Over.Hom.left
                    (prod.map ((Over.map (f' i)).map m_i) (𝟙 (Over.mk (f' j)))) ≫
                    Over.Hom.left prod.fst) ≫
                      Over.Hom.left (structureMap (f' i) ((P E).datum.obj i)) := by
                  simp [Category.assoc]
                _ = (Over.Hom.left prod.fst ≫
                    Over.Hom.left ((Over.map (f' i)).map m_i)) ≫
                      Over.Hom.left (structureMap (f' i) ((P E).datum.obj i)) := by
                  rw [hMapFst]
                _ = _ := by
                  simp only [Over.map_map_left, Category.assoc]
                  exact congrArg (fun k => Over.Hom.left prod.fst ≫ k) hm_i
            · apply Over.OverMorphism.ext
              let m_j := m D E φ j
              have hm_j := Over.w m_j
              have hm_j_objMap :
                  m_j.left ≫ (P E).objMap j =
                    (P D).objMap j ≫ (φ.hom (α j)).left := by
                simp [m_j, m, IsPullback.lift_snd]
              apply (P E).obj_isPullback j |>.hom_ext
              · have hE := Over.w ((P E).datum.gluing i j).hom
                have hEsnd := congrArg (fun z => z ≫
                  (prod.snd : Over.mk (f' i) ⨯ Over.mk (f' j) ⟶ Over.mk (f' j))) hE
                simp only [Over.mk_hom, Category.assoc, prod.map_snd,
                  Category.comp_id] at hEsnd
                have hEsnd := congrArg Over.Hom.left hEsnd
                simp only [Over.comp_left] at hEsnd
                have hD := Over.w ((P D).datum.gluing i j).hom
                have hDsnd := congrArg (fun z => z ≫
                  (prod.snd : Over.mk (f' i) ⨯ Over.mk (f' j) ⟶ Over.mk (f' j))) hD
                simp only [Over.mk_hom, Category.assoc, prod.map_snd,
                  Category.comp_id] at hDsnd
                have hDsnd := congrArg Over.Hom.left hDsnd
                simp only [Over.comp_left] at hDsnd
                let m_i := m D E φ i
                have hMapSrcSnd := congrArg Over.Hom.left
                  (prod.map_snd ((Over.map (f' i)).map m_i) (𝟙 (Over.mk (f' j))))
                simp only [Over.comp_left] at hMapSrcSnd
                have hMapTgtSnd := congrArg Over.Hom.left
                  (prod.map_snd (𝟙 (Over.mk (f' i))) ((Over.map (f' j)).map m_j))
                simp only [Over.comp_left] at hMapTgtSnd
                let srcD := (Over.map (f' i)).obj ((P D).datum.obj i) ⨯
                  Over.mk (f' j)
                let srcE := (Over.map (f' i)).obj ((P E).datum.obj i) ⨯
                  Over.mk (f' j)
                let tgtD := Over.mk (f' i) ⨯
                  (Over.map (f' j)).obj ((P D).datum.obj j)
                let tgtE := Over.mk (f' i) ⨯
                  (Over.map (f' j)).obj ((P E).datum.obj j)
                let srcSndD : srcD ⟶ Over.mk (f' j) := prod.snd
                let srcSndE : srcE ⟶ Over.mk (f' j) := prod.snd
                let tgtSndD : tgtD ⟶ (Over.map (f' j)).obj ((P D).datum.obj j) :=
                  prod.snd
                let tgtSndE : tgtE ⟶ (Over.map (f' j)).obj ((P E).datum.obj j) :=
                  prod.snd
                have hEsnd' :
                    Over.Hom.left (Over.Hom.left ((P E).datum.gluing i j).hom) ≫
                      Over.Hom.left tgtSndE ≫ ((P E).datum.obj j).hom =
                    Over.Hom.left srcSndE := by
                  simpa [structureMap, srcSndE, tgtSndE] using hEsnd
                have hDsnd' :
                    Over.Hom.left (Over.Hom.left ((P D).datum.gluing i j).hom) ≫
                      Over.Hom.left tgtSndD ≫ ((P D).datum.obj j).hom =
                    Over.Hom.left srcSndD := by
                  simpa [structureMap, srcSndD, tgtSndD] using hDsnd
                have hMapSrcSnd :
                    Over.Hom.left (prod.map ((Over.map (f' i)).map m_i)
                      (𝟙 (Over.mk (f' j)))) ≫ Over.Hom.left srcSndE =
                    Over.Hom.left srcSndD := by
                  simpa [srcSndD, srcSndE, Over.comp_left] using hMapSrcSnd
                have hMapTgtSnd :
                    Over.Hom.left (prod.map (𝟙 (Over.mk (f' i)))
                      ((Over.map (f' j)).map m_j)) ≫ Over.Hom.left tgtSndE =
                    Over.Hom.left tgtSndD ≫
                      Over.Hom.left ((Over.map (f' j)).map m_j) := by
                  simpa [tgtSndD, tgtSndE, Over.comp_left] using hMapTgtSnd
                have hTgtSndE := congrArg
                  (fun q => q ≫ ((P E).datum.obj j).hom) hMapTgtSnd
                simp only [Over.map_obj_left, Over.map_map_left,
                  Category.assoc] at hTgtSndE
                rw [hm_j] at hTgtSndE
                have hL :
                    Over.Hom.left (prod.map ((Over.map (f' i)).map m_i)
                      (𝟙 (Over.mk (f' j)))) ≫
                        Over.Hom.left (Over.Hom.left ((P E).datum.gluing i j).hom) ≫
                        Over.Hom.left tgtSndE ≫ ((P E).datum.obj j).hom =
                    Over.Hom.left srcSndD := by
                  calc
                    _ = Over.Hom.left (prod.map ((Over.map (f' i)).map m_i)
                        (𝟙 (Over.mk (f' j)))) ≫
                          (Over.Hom.left (Over.Hom.left ((P E).datum.gluing i j).hom) ≫
                            Over.Hom.left tgtSndE ≫ ((P E).datum.obj j).hom) := by
                      simp
                    _ = Over.Hom.left (prod.map ((Over.map (f' i)).map m_i)
                        (𝟙 (Over.mk (f' j)))) ≫ Over.Hom.left srcSndE := by
                      rw [hEsnd']
                    _ = Over.Hom.left srcSndD := hMapSrcSnd
                have hR :
                    Over.Hom.left (Over.Hom.left ((P D).datum.gluing i j).hom) ≫
                      Over.Hom.left (prod.map (𝟙 (Over.mk (f' i)))
                        ((Over.map (f' j)).map m_j)) ≫
                      Over.Hom.left tgtSndE ≫ ((P E).datum.obj j).hom =
                    Over.Hom.left srcSndD := by
                  calc
                    _ = Over.Hom.left (Over.Hom.left ((P D).datum.gluing i j).hom) ≫
                          (Over.Hom.left (prod.map (𝟙 (Over.mk (f' i)))
                            ((Over.map (f' j)).map m_j)) ≫
                            Over.Hom.left tgtSndE ≫ ((P E).datum.obj j).hom) := by
                      simp
                    _ = Over.Hom.left (Over.Hom.left ((P D).datum.gluing i j).hom) ≫
                          Over.Hom.left tgtSndD ≫ ((P D).datum.obj j).hom := by
                      rw [hTgtSndE]
                    _ = Over.Hom.left srcSndD := by
                      simpa only [Over.map_obj_left] using hDsnd'
                simp only [Over.comp_left, Category.assoc]
                calc
                  _ = Over.Hom.left prod.snd := by simpa [m_i] using hL
                  _ = _ := by simpa [Over.comp_left, Category.assoc] using hR.symm
              · let oldB := Over.mk (f (α j))
                let oldAD := (Over.map (f (α i))).obj (D.obj (α i))
                let oldAE := (Over.map (f (α i))).obj (E.obj (α i))
                let oldSrcD := oldAD ⨯ oldB
                let oldSrcE := oldAE ⨯ oldB
                let oldMapI := (Over.map (f (α i))).map (φ.hom (α i))
                let srcBridgeD := (P D).gluingSourceMap i j
                let srcBridgeE := (P E).gluingSourceMap i j
                let m_i := m D E φ i
                have hm_i_objMap : m_i.left ≫ (P E).objMap i =
                    (P D).objMap i ≫ (φ.hom (α i)).left := by
                  simp [m_i, m, IsPullback.lift_snd]
                have hSrcNat :
                    Over.Hom.left (prod.map ((Over.map (f' i)).map m_i)
                      (𝟙 (Over.mk (f' j)))) ≫ srcBridgeE =
                    srcBridgeD ≫ Over.Hom.left
                      (prod.map oldMapI (𝟙 oldB)) := by
                  apply (cancel_mono
                    (Over.prodLeftIsoPullback oldAE oldB).hom).mp
                  apply pullback.hom_ext
                  · have hMapFst' := congrArg Over.Hom.left
                      (prod.map_fst ((Over.map (f' i)).map m_i)
                        (𝟙 (Over.mk (f' j))))
                    simp only [Over.comp_left] at hMapFst'
                    have hOldMapFst := congrArg Over.Hom.left
                      (prod.map_fst oldMapI (𝟙 oldB))
                    simp only [Over.comp_left] at hOldMapFst
                    have hEFst := (P E).gluingSource_fst i j
                    have hDFst := (P D).gluingSource_fst i j
                    simp only [Category.assoc,
                      Over.prodLeftIsoPullback_hom_fst (Y := oldAE) (Z := oldB)]
                    rw [hEFst, reassoc_of% hMapFst', hOldMapFst]
                    change _ = (P D).gluingSourceMap i j ≫ _
                    rw [reassoc_of% hDFst]
                    exact congrArg (_ ≫ ·) hm_i_objMap
                  · have hMapSnd' := congrArg Over.Hom.left
                      (prod.map_snd ((Over.map (f' i)).map m_i)
                        (𝟙 (Over.mk (f' j))))
                    simp only [Over.comp_left] at hMapSnd'
                    have hOldMapSnd := congrArg Over.Hom.left
                      (prod.map_snd oldMapI (𝟙 oldB))
                    simp only [Over.comp_left] at hOldMapSnd
                    have hESnd := (P E).gluingSource_snd i j
                    have hDSnd := (P D).gluingSource_snd i j
                    simp only [Category.assoc,
                      Over.prodLeftIsoPullback_hom_snd (Y := oldAE) (Z := oldB)]
                    rw [hESnd, reassoc_of% hMapSnd', hOldMapSnd]
                    change _ = (P D).gluingSourceMap i j ≫ _
                    simp only [Over.id_left, Category.comp_id]
                    exact hDSnd.symm
                let oldC := Over.mk (f (α i))
                let oldDD := (Over.map (f (α j))).obj (D.obj (α j))
                let oldDE := (Over.map (f (α j))).obj (E.obj (α j))
                let oldTgtD := oldC ⨯ oldDD
                let oldTgtE := oldC ⨯ oldDE
                let oldMapJ := (Over.map (f (α j))).map (φ.hom (α j))
                let tgtBridgeD := (P D).gluingTargetMap i j
                let tgtBridgeE := (P E).gluingTargetMap i j
                let mapTgt := prod.map (𝟙 (Over.mk (f' i)))
                  ((Over.map (f' j)).map m_j)
                let oldMapTgt := prod.map (𝟙 oldC) oldMapJ
                have hMapTgtSnd := congrArg Over.Hom.left
                  (prod.map_snd (𝟙 (Over.mk (f' i))) ((Over.map (f' j)).map m_j))
                simp only [Over.comp_left] at hMapTgtSnd
                have hOldMapTgtSnd := congrArg Over.Hom.left
                  (prod.map_snd (𝟙 oldC) oldMapJ)
                simp only [Over.comp_left] at hOldMapTgtSnd
                have hTargetSndNat :
                    Over.Hom.left mapTgt ≫ tgtBridgeE ≫
                        ((prod.snd : oldTgtE ⟶ oldDE).left) =
                    tgtBridgeD ≫ Over.Hom.left oldMapTgt ≫
                        ((prod.snd : oldTgtE ⟶ oldDE).left) := by
                  change Over.Hom.left (prod.map (𝟙 (Over.mk (f' i))) ((Over.map (f' j)).map m_j)) ≫
                      (P E).gluingTargetMap i j ≫ _ = (P D).gluingTargetMap i j ≫
                        Over.Hom.left (prod.map (𝟙 oldC) oldMapJ) ≫ _
                  rw [(P E).gluingTarget_snd, reassoc_of% hMapTgtSnd, hOldMapTgtSnd,
                    reassoc_of% (P D).gluingTarget_snd i j]
                  exact congrArg (_ ≫ ·) hm_j_objMap
                have hGluePE := (P E).gluing_comm i j
                have hGluePD := (P D).gluing_comm i j
                have hPhi := congrArg Over.Hom.left (φ.comm (α i) (α j))
                simp only [Over.comp_left] at hPhi
                let gluePE := Over.Hom.left
                  (Over.Hom.left ((P E).datum.gluing i j).hom)
                let gluePD := Over.Hom.left
                  (Over.Hom.left ((P D).datum.gluing i j).hom)
                let oldGlueE := Over.Hom.left
                  (Over.Hom.left (E.gluing (α i) (α j)).hom)
                let oldGlueD := Over.Hom.left
                  (Over.Hom.left (D.gluing (α i) (α j)).hom)
                let oldSrcMap := Over.Hom.left (prod.map oldMapI (𝟙 oldB))
                let mapSrc := prod.map ((Over.map (f' i)).map m_i)
                  (𝟙 (Over.mk (f' j)))
                let oldSndE := (prod.snd : oldTgtE ⟶ oldDE).left
                let oldSndD := (prod.snd : oldTgtD ⟶ oldDD).left
                let newSndE := ((prod.snd : (Over.mk (f' i) ⨯
                  (Over.map (f' j)).obj ((P E).datum.obj j)) ⟶
                    (Over.map (f' j)).obj ((P E).datum.obj j)).left)
                let newSndD := ((prod.snd : (Over.mk (f' i) ⨯
                  (Over.map (f' j)).obj ((P D).datum.obj j)) ⟶
                    (Over.map (f' j)).obj ((P D).datum.obj j)).left)
                have hGluePE' : srcBridgeE ≫ oldGlueE = gluePE ≫ tgtBridgeE := by
                  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hGluePE
                have hGluePD' : srcBridgeD ≫ oldGlueD = gluePD ≫ tgtBridgeD := by
                  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using hGluePD
                have hPhiSnd : oldSrcMap ≫ oldGlueE ≫ oldSndE =
                    oldGlueD ≫ Over.Hom.left oldMapTgt ≫ oldSndE := by
                  simpa [oldSrcMap, oldGlueE, oldGlueD, oldSndE, oldMapTgt] using
                    congrArg (fun q => q ≫ oldSndE) hPhi
                have hLeft : Over.Hom.left mapSrc ≫ gluePE ≫ newSndE ≫
                    (P E).objMap j =
                    srcBridgeD ≫ oldGlueD ≫ oldSndD ≫ (φ.hom (α j)).left := by
                  calc
                    _ = Over.Hom.left mapSrc ≫ gluePE ≫
                        (tgtBridgeE ≫ oldSndE) := by
                      simpa only [Category.assoc] using congrArg
                        (fun q => Over.Hom.left mapSrc ≫ gluePE ≫ q)
                        ((P E).gluingTarget_snd i j).symm
                    _ = Over.Hom.left mapSrc ≫
                        (srcBridgeE ≫ oldGlueE) ≫ oldSndE := by
                      simpa only [Category.assoc] using congrArg
                        (fun q => Over.Hom.left mapSrc ≫ q ≫ oldSndE)
                        hGluePE'.symm
                    _ = srcBridgeD ≫ oldSrcMap ≫ oldGlueE ≫ oldSndE := by
                      simpa only [Category.assoc] using congrArg
                        (fun q => q ≫ oldGlueE ≫ oldSndE) hSrcNat
                    _ = srcBridgeD ≫ oldGlueD ≫
                        Over.Hom.left oldMapTgt ≫ oldSndE := by
                      simpa only [Category.assoc] using congrArg
                        (fun q => srcBridgeD ≫ q) hPhiSnd
                    _ = srcBridgeD ≫ oldGlueD ≫ oldSndD ≫
                        (φ.hom (α j)).left := by
                      rw [hOldMapTgtSnd]
                      rfl
                have hRight : gluePD ≫ Over.Hom.left mapTgt ≫ newSndE ≫
                    (P E).objMap j =
                    srcBridgeD ≫ oldGlueD ≫ oldSndD ≫ (φ.hom (α j)).left := by
                  calc
                    _ = gluePD ≫ Over.Hom.left mapTgt ≫
                        (tgtBridgeE ≫ oldSndE) := by
                      simpa only [Category.assoc] using congrArg
                        (fun q => gluePD ≫ Over.Hom.left mapTgt ≫ q)
                        ((P E).gluingTarget_snd i j).symm
                    _ = gluePD ≫ tgtBridgeD ≫
                        Over.Hom.left oldMapTgt ≫ oldSndE := by
                      simpa only [Category.assoc] using congrArg
                        (fun q => gluePD ≫ q) hTargetSndNat
                    _ = srcBridgeD ≫ oldGlueD ≫ oldSndD ≫
                        (φ.hom (α j)).left := by
                      calc
                        _ = gluePD ≫ tgtBridgeD ≫ oldSndD ≫
                            (φ.hom (α j)).left := by
                          rw [hOldMapTgtSnd]
                          rfl
                        _ = srcBridgeD ≫ oldGlueD ≫ oldSndD ≫
                            (φ.hom (α j)).left := by
                          simpa only [Category.assoc] using congrArg
                            (fun q => q ≫ oldSndD ≫ (φ.hom (α j)).left)
                            hGluePD'.symm
                simp only [Over.comp_left]
                exact hLeft.trans hRight.symm
          }
      map_id := by
        intro D
        apply DescentData.Hom.ext
        funext i
        apply Over.OverMorphism.ext
        apply (P D).obj_isPullback i |>.hom_ext
        · simp [m, DescentData.id_hom, Over.id_left,
            IsPullback.lift_fst]
        · simp [m, DescentData.id_hom,
            Over.homMk_left, IsPullback.lift_snd]
      map_comp := by
        intro D E G φ ψ
        apply DescentData.Hom.ext
        funext i
        apply Over.OverMorphism.ext
        apply (P G).obj_isPullback i |>.hom_ext
        · simp [m, DescentData.comp_hom, Over.comp_left,
            Over.homMk_left, IsPullback.lift_fst, Category.assoc]
        · simp [m, DescentData.comp_hom, Over.comp_left,
            Over.homMk_left, IsPullback.lift_snd, Category.assoc] }
  { functor := F
    obj_eq := fun D => rfl
    map := by
      intro D E φ i
      simp only [eqToHom_refl]
      have hw : ((P D).datum.obj i).hom ≫ gᵢ i =
          (P D).objMap i ≫ (φ.hom (α i)).left ≫ (E.obj (α i)).hom := by
        calc
          ((P D).datum.obj i).hom ≫ gᵢ i =
              (P D).objMap i ≫ (D.obj (α i)).hom :=
            (P D).obj_isPullback i |>.w
          _ = (P D).objMap i ≫
              ((φ.hom (α i)).left ≫ (E.obj (α i)).hom) := by rw [Over.w]
          _ = _ := by simp
      change (P D).objMap i ≫ (φ.hom (α i)).left =
        ((P E).obj_isPullback i).lift ((P D).datum.obj i).hom
          ((P D).objMap i ≫ (φ.hom (α i)).left) hw ≫ (P E).objMap i
      rw [(P E).obj_isPullback i |>.lift_snd]
  }

end AlgebraicGeometry.Space.Descent

end
