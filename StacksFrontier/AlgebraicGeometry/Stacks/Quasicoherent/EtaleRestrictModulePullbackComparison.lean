module

public import StacksFrontier.AlgebraicGeometry.Etale.SmallEtalePostcomposeBaseChangeCounit
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedSmallEtaleIsoComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangePropertySheafified
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackAlongRightAdjointSite

/-!
# The comparison of restricted modules along an étale arrow is an isomorphism

Let `φ : x ⟶ y` be an arrow of a category fibred in groupoids `p : 𝒳 ⥤ (Sch/S)_{fppf}` lying over
an *étale* morphism of schemes `a : U ⟶ V`, and let `F` be a presheaf of modules over the
structure sheaf of `𝒳`. This file proves that the comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 06WC** is an isomorphism of presheaves of
modules. This is **Stacks 075D** part (2) for modules; the library has it for sheaves of sets
(`AlgebraicGeometry.Stack.isIso_restrictionInverseImageComparison`). No sheaf condition on `F`
is needed, and no sheafification enters.

## The argument

Base change along `a` between small étale sites has post-composition with `a` as a left adjoint
(`AlgebraicGeometry.SmallEtale.postcomposeBaseChangeAdjunction`). For a module `M` on `V_ét` and a
morphism `η : M ⟶ a_* P`, the mate `a^* M ⟶ P` is an isomorphism as soon as, for every `T` étale
over `U`, the maps of rings and of sections obtained from `η` at `T` regarded over `V` followed by
restriction along the unit `T ⟶ T ×_V U` are isomorphisms
(`PresheafOfModules.isIso_pullbackPushforwardAdjunction_homEquiv_symm_of_isIso`). For the
comparison of Stacks 06W2 these maps are restriction, for any presheaf on `𝒳`, along a single
arrow of `𝒳` lying over an isomorphism of schemes, which is an isomorphism because `p` is fibred
in groupoids (`AlgebraicGeometry.Stack.isIso_restrictionPushforwardComparison_app_comp_map_unit`,
the computation made inside the proof of the sheaves-of-sets statement, here for a presheaf with
values in any category).

## Main results

* `AlgebraicGeometry.Stack.isIso_restrictionPushforwardComparison_app_comp_map_unit`.
* `AlgebraicGeometry.Stack.isIso_restrictModulePullbackComparison_of_etale`: **Stacks 075D**
  part (2) for presheaves of modules.
* `AlgebraicGeometry.Stack.isIso_sheafifiedRestrictComparison_of_etale`: the same for the
  comparison read as a morphism of sheaves
  (`AlgebraicGeometry.Stack.sheafifiedRestrictComparison`).

## References

* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u v w t s

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

section

variable {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) {x y : 𝒳} (φ : x ⟶ y)

/-- The scheme below the source of an arrow lying over an étale morphism, as an object of the
small étale site of the scheme below its target. -/
def etaleArrowSmallEtaleObject (hφ : Etale (B.inclusion.map (p.map φ).left)) :
    SmallEtale E (p.obj y).left.1 (contains_base B E h S hS p y) :=
  ⟨Over.mk (smallEtaleBaseMorphism B E h S hS p φ), by
    change Etale (E.inclusion.map (smallEtaleBaseMorphism B E h S hS p φ))
    simpa [smallEtaleBaseMorphism] using hφ⟩

/-- Post-composition with the étale morphism below `φ` is left adjoint to base change along it. -/
noncomputable def etaleArrowPostcomposeAdjunction (hφ : Etale (B.inclusion.map (p.map φ).left)) :
    (SmallEtale.postcompose E (p.obj y).left.1 (contains_base B E h S hS p y)
        (etaleArrowSmallEtaleObject B E h S hS p φ hφ) :
        SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x) ⥤ _) ⊣
      smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ) :=
  SmallEtale.postcomposeBaseChangeAdjunction E (p.obj y).left.1 (contains_base B E h S hS p y)
    (etaleArrowSmallEtaleObject B E h S hS p φ hφ)

/-- **The comparison of Stacks 06W2 along an étale arrow, read through the unit of the
post-composition adjunction, is restriction along an isomorphism.** For every presheaf `G` on
`𝒳` with values in any category and every `T` étale over the scheme `U` below `x`, the component
of the comparison at `T` regarded over `V`, followed by restriction along the unit
`T ⟶ T ×_V U`, is an isomorphism. -/
theorem isIso_restrictionPushforwardComparison_app_comp_map_unit
    (hφ : Etale (B.inclusion.map (p.map φ).left)) {A : Type t} [Category.{s} A] (G : 𝒳ᵒᵖ ⥤ A)
    (T : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x)) :
    IsIso ((restrictionPushforwardComparison B E h S hS p hp φ G).app
        (op ((SmallEtale.postcompose E (p.obj y).left.1 (contains_base B E h S hS p y)
          (etaleArrowSmallEtaleObject B E h S hS p φ hφ)).obj T)) ≫
      (restrictToSmallEtale B E h S hS p hp x G).map
        ((etaleArrowPostcomposeAdjunction B E h S hS p φ hφ).unit.app T).op) := by
  let U := E.obj (p.obj x).left.1 (contains_base B E h S hS p x)
  let V := E.obj (p.obj y).left.1 (contains_base B E h S hS p y)
  let f := smallEtaleBaseMorphism B E h S hS p φ
  let Uo := etaleArrowSmallEtaleObject B E h S hS p φ hφ
  let M := SmallEtale.postcompose E V.1 V.property Uo
  let N := smallEtaleBaseChange E f
  let siteAdj := etaleArrowPostcomposeAdjunction B E h S hS p φ hφ
  have : (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
    isEquivalence_overPost B S hS p hp x
  have : (Over.post (X := y) (p ⋙ Over.forget (B.obj hS))).IsEquivalence :=
    isEquivalence_overPost B S hS p hp y
  let Px := Over.post (X := x) (p ⋙ Over.forget (B.obj hS))
  let Py := Over.post (X := y) (p ⋙ Over.forget (B.obj hS))
  let Ix := smallEtaleInclusion B E h U.1 U.property
  let Iy := smallEtaleInclusion B E h V.1 V.property
  let W := M.obj T
  let NW := N.obj W
  let ePx := Px.asEquivalence
  let ePy := Py.asEquivalence
  let xT := ePx.inverse.obj (Ix.obj T)
  let xNW := ePx.inverse.obj (Ix.obj NW)
  let yW := ePy.inverse.obj (Iy.obj W)
  let z : Over y := Over.mk (xNW.hom ≫ φ)
  let jB : (p ⋙ Over.forget (B.obj hS)).obj x ⟶
      (p ⋙ Over.forget (B.obj hS)).obj y := (p.map φ).left
  let e₁ : Ix ⋙ Over.map jB ≅ M ⋙ Iy := Iso.refl _
  let eT : Px.obj xT ≅ Ix.obj T := ePx.counitIso.app (Ix.obj T)
  let eX : Px.obj xNW ≅ Ix.obj NW := ePx.counitIso.app (Ix.obj NW)
  let eY : Py.obj yW ≅ Iy.obj W := ePy.counitIso.app (Iy.obj W)
  have hz : Py.obj z = (Over.map jB).obj (Px.obj xNW) := by
    show Over.mk ((p.map (xNW.hom ≫ φ)).left) =
      (Over.map jB).obj (Over.mk ((p.map xNW.hom).left))
    apply congrArg Over.mk
    simp [jB, Functor.map_comp]
  let a : Py.obj z ⟶ Py.obj yW :=
    (eqToIso hz).hom ≫ (Over.map jB).map eX.hom ≫ (e₁.app NW).hom ≫
      Iy.map (siteAdj.counit.app W) ≫ eY.inv
  let alphaOver : z ⟶ yW := Py.preimage a
  let alpha := alphaOver.left
  have hAlpha : alpha ≫ yW.hom = xNW.hom ≫ φ := alphaOver.w
  let betaOver := Px.inv.map (Ix.map (siteAdj.unit.app T))
  let beta := betaOver.left
  have hAlphaBase : (p.map alpha).left ≫ eY.hom.left =
      eX.hom.left ≫ (e₁.app NW).hom.left ≫ (Iy.map (siteAdj.counit.app W)).left := by
    have hmap : Py.map alphaOver = a := by simp [alphaOver]
    let Qy := Over.forget ((p ⋙ Over.forget (B.obj hS)).obj y)
    have hmap' := congrArg Qy.map hmap
    simp only [Qy, Over.forget_map] at hmap'
    have hzleft : (Py.obj z).left = ((Over.map jB).obj (Px.obj xNW)).left := rfl
    have hmap'' : (p.map alpha).left = a.left := hmap'
    have hEq : Over.Hom.left ((eqToIso hz).hom) = eqToHom hzleft := by
      dsimp only [eqToIso]
      rw [Over.eqToHom_left]
    cases hzleft
    rw [hmap'']
    dsimp only [a]
    simp only [Over.comp_left]
    rw [hEq]
    simp [Over.map_map_left, Over.inv_left_hom_left eY]
  have hIsoLeft : ∀ {Z : B.Schemes} {X Y : Over Z} (e : X ≅ Y), IsIso e.hom.left :=
    fun e => Functor.map_isIso (Over.forget _) e.hom
  have hCompat : B.inclusion.map (p.map alpha).left ≫ B.inclusion.map eY.hom.left =
      B.inclusion.map eX.hom.left ≫ E.inclusion.map (pullback.fst W.obj.hom f) := by
    calc
      B.inclusion.map ((p.map alpha).left ≫ eY.hom.left) =
          B.inclusion.map (eX.hom.left ≫ (e₁.app NW).hom.left ≫
            (Iy.map (siteAdj.counit.app W)).left) :=
            congrArg (B.inclusion.map) hAlphaBase
      _ = B.inclusion.map eX.hom.left ≫ E.inclusion.map (pullback.fst W.obj.hom f) := by
            rw [Functor.map_comp]
            have := hIsoLeft eX
            apply (cancel_epi (B.inclusion.map eX.hom.left)).mpr
            have hR : (e₁.app NW).hom.left ≫ (Iy.map (siteAdj.counit.app W)).left =
                (Iy.map (siteAdj.counit.app W)).left := Category.id_comp _
            rw [hR]
            have hc := SmallEtale.inclusion_map_postcomposeBaseChangeAdjunction_counit_app E V.1
              V.property Uo W
            have hc' := congrArg (fun g => E.inclusion.map (Over.Hom.left g)) hc
            simp only [Over.mapPullbackAdj_counit_app, Over.homMk_left] at hc'
            exact hc'
  let delta := beta ≫ alpha
  rw [restrictionPushforwardComparison_app B E h S hS p hp φ G W alpha hAlpha hCompat]
  show IsIso (G.map alpha.op ≫ G.map beta.op)
  have hdelta : IsIso delta := by
    have hscheme : IsIso ((p.map delta).left) := by
      have hBeta : (p.map beta).left ≫ eX.hom.left =
          eT.hom.left ≫ (Ix.map (siteAdj.unit.app T)).left :=
        congrArg (Over.forget ((p ⋙ Over.forget (B.obj hS)).obj x)).map
          (ePx.counitIso.hom.naturality (Ix.map (siteAdj.unit.app T)))
      have htriangle : (Ix.map (siteAdj.unit.app T)).left ≫
          (e₁.app NW).hom.left ≫ (Iy.map (siteAdj.counit.app W)).left =
            𝟙 (Iy.obj W).left := by
        have ht := siteAdj.left_triangle_components T
        have htransport :
            (Ix.map (siteAdj.unit.app T)).left ≫ (e₁.app NW).hom.left =
              (Iy.map (M.map (siteAdj.unit.app T))).left := by
          simp only [Functor.comp_obj, Over.forget_obj, Iso.app_hom]
          exact Category.comp_id _
        rw [← Category.assoc, htransport]
        have ht' := congrArg (fun g => (Iy.map g).left) ht
        show (Iy.map (M.map (siteAdj.unit.app T) ≫ siteAdj.counit.app W)).left =
          (Iy.map (𝟙 W)).left
        exact ht'
      have hd : (p.map delta).left = (p.map beta).left ≫ (p.map alpha).left :=
        (congrArg Over.Hom.left (p.map_comp beta alpha)).trans (Over.comp_left _ _ _ _ _)
      have hconj : (p.map delta).left ≫ eY.hom.left = eT.hom.left := by
        have s1 := congrArg (fun k => k ≫ eY.hom.left) hd
        have s2 := Category.assoc (p.map beta).left (p.map alpha).left eY.hom.left
        have s3 := congrArg (fun k => (p.map beta).left ≫ k) hAlphaBase
        have s4 := (Category.assoc (p.map beta).left eX.hom.left
          ((e₁.app NW).hom.left ≫ (Iy.map (siteAdj.counit.app W)).left)).symm
        have s5 := congrArg (fun k => k ≫
          ((e₁.app NW).hom.left ≫ (Iy.map (siteAdj.counit.app W)).left)) hBeta
        have s6 := Category.assoc eT.hom.left (Ix.map (siteAdj.unit.app T)).left
          ((e₁.app NW).hom.left ≫ (Iy.map (siteAdj.counit.app W)).left)
        have s7 := congrArg (fun k => eT.hom.left ≫ k) htriangle
        have s8 := Category.comp_id eT.hom.left
        exact s1.trans (s2.trans (s3.trans (s4.trans (s5.trans (s6.trans (s7.trans s8))))))
      have hg : (p.map delta).left = eT.hom.left ≫ eY.inv.left :=
        (Category.comp_id _).symm.trans ((congrArg ((p.map delta).left ≫ ·)
          (Over.hom_left_inv_left eY).symm).trans ((Category.assoc _ _ _).symm.trans
            (congrArg (· ≫ eY.inv.left) hconj)))
      exact hg ▸ IsIso.comp_isIso' (hIsoLeft eT) (hIsoLeft eY.symm)
    have : IsIso ((Over.forget (B.obj hS)).map (p.map delta)) := hscheme
    have := Functor.ReflectsIsomorphisms.reflects (Over.forget (B.obj hS)) (p.map delta)
    have := hp.isStronglyCartesian delta
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso (p := p) (f := p.map delta) delta
  have hmap_eq : G.map delta.op = G.map alpha.op ≫ G.map beta.op := by
    rw [show delta.op = alpha.op ≫ beta.op from op_comp]
    exact G.map_comp _ _
  rw [← hmap_eq]
  exact Functor.map_isIso _ _

/-- **Stacks 075D, part (2), for presheaves of modules.** If an arrow `φ : x ⟶ y` of `𝒳` lies
over an étale morphism of schemes, the comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of Stacks 06WC is an isomorphism of presheaves of
modules, for every presheaf of modules `F` over the structure sheaf of `𝒳`. -/
theorem isIso_restrictModulePullbackComparison_of_etale
    (hφ : Etale (B.inclusion.map (p.map φ).left))
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    IsIso (restrictModulePullbackComparison B E h S hS p hp φ τ hτ F) := by
  refine PresheafOfModules.isIso_pullbackPushforwardAdjunction_homEquiv_symm_of_isIso
    (etaleArrowPostcomposeAdjunction B E h S hS p φ hφ)
    (hφ := isRightAdjoint_pushforward_smallEtaleStructureComparison B E h S hS p hp φ τ hτ)
    (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F) (fun X => ?_) (fun X => ?_)
  · let ix := localStructurePresheafIso B E h S hS p hp x τ hτ
    let iy := localStructurePresheafIso B E h S hS p hp y τ hτ
    let u := (etaleArrowPostcomposeAdjunction B E h S hS p φ hφ).unit.app X.unop
    let W := op ((SmallEtale.postcompose E (p.obj y).left.1 (contains_base B E h S hS p y)
      (etaleArrowSmallEtaleObject B E h S hS p φ hφ)).obj X.unop)
    have key := isIso_restrictionPushforwardComparison_app_comp_map_unit B E h S hS p hp φ hφ
      (ringStructureSheafCore B S hS p hp τ hτ).obj X.unop
    have hnat := ix.inv.naturality u.op
    have heq : PresheafOfModules.unitRingMap (etaleArrowPostcomposeAdjunction B E h S hS p φ hφ)
        (smallEtaleStructureComparison B E h S hS p hp φ τ hτ) X =
        iy.hom.app W ≫ ((restrictionPushforwardComparison B E h S hS p hp φ
          (ringStructureSheafCore B S hS p hp τ hτ).obj).app W ≫
            (restrictToSmallEtale B E h S hS p hp x
              (ringStructureSheafCore B S hS p hp τ hτ).obj).map u.op) ≫ ix.inv.app X := by
      simp only [PresheafOfModules.unitRingMap, smallEtaleStructureComparison, NatTrans.comp_app,
        Functor.whiskerLeft_app, Category.assoc]
      exact congrArg (iy.hom.app W ≫ ·) (congrArg (_ ≫ ·) hnat.symm)
    rw [heq]
    exact IsIso.comp_isIso' inferInstance (IsIso.comp_isIso' key (Iso.isIso_hom (ix.app X).symm))
  · exact isIso_restrictionPushforwardComparison_app_comp_map_unit B E h S hS p hp φ hφ
      F.presheaf X.unop

/-- **Stacks 075D, part (2)**, for the comparison read as a morphism of sheaves: along an arrow
lying over an étale morphism, the morphism out of the sheafified pullback induced by the
comparison map of Stacks 06WC is an isomorphism. -/
theorem isIso_sheafifiedRestrictComparison_of_etale
    (hφ : Etale (B.inclusion.map (p.map φ).left))
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hMx : Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1
        (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf) :
    IsIso (sheafifiedRestrictComparison B E h S hS p hp F φ hMx) := by
  have := isIso_restrictModulePullbackComparison_of_etale B E h S hS p hp φ hφ (etaleTopology B)
    (etaleTopology_le_topology B) F
  exact (isIso_sheafifiedRestrictModulePullbackComparison_iff B E h S hS p hp (etaleTopology B)
    (etaleTopology_le_topology B) φ F hMx).2 ⟨inferInstance, inferInstance⟩

end

end AlgebraicGeometry.Stack

end
