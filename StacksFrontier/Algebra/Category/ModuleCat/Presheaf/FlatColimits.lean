module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import Mathlib.CategoryTheory.ObjectProperty.FunctorCategory.PreservesLimits
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import StacksCore.Tactic.StacksAttribute

/-!
# Direct sums and filtered colimits of flat presheaves of modules

Let `O` be a presheaf of commutative rings on a category `C`. A presheaf of `O`-modules is flat
when tensoring on the right with it is an exact endofunctor (Stacks 03ER). This file proves that
the flat presheaves of modules are closed under direct sums and under filtered colimits.

Both proofs have the same shape. Tensoring is functorial in the *second* variable as well, so a
diagram `F` of presheaves of modules gives a diagram `j ↦ tensorRight (F j)` of endofunctors,
and the first step is that the colimit of that diagram of endofunctors is `tensorRight` of the
colimit of `F`: this is checked objectwise, where it is the fact that tensoring a module
commutes with colimits. The second step is that a colimit of exact functors is exact, which
holds because the category of presheaves of modules has exact colimits of the shape in question
— finite coproducts are exact in any abelian category, and filtered colimits are exact because
abelian groups satisfy AB5.

## Main definitions

* `Stacks.tensorRightMap`: the natural transformation `tensorRight F ⟶ tensorRight F'` induced
  by a morphism `F ⟶ F'`, i.e. the functoriality of the tensor product in the variable one
  tensors *with*.

## Main results

* `Stacks.isFlat_coproduct`: a coproduct of flat presheaves of modules is flat.
* `Stacks.isFlat_colimit`: a filtered colimit of flat presheaves of modules is flat.

## Implementation notes

Direct sums are categorical coproducts, so the indexing type is required to lie in the universe
`z` of the module carriers, which is where those coproducts of presheaves of modules exist. For
filtered colimits the index category may lie in any universe `ju` with `UnivLE.{ju, z}`; the
proof passes to an equivalent `z`-small index category in order to apply the AB5 property of
abelian groups, which is stated for small index categories.

The exactness of filtered colimits in presheaves of modules is obtained by reflecting it along
`PresheafOfModules.toPresheaf`, which is exact and faithful, from the functor category
`Cᵒᵖ ⥤ AddCommGrpCat`, where it is AB5 for abelian groups.

## References

* [Stacks Project, Tag 03EU](https://stacks.math.columbia.edu/tag/03EU)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER), flatness.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe v u w z ju jv

namespace Stacks

variable {C : Type u} [Category.{v} C]

/-- Tensoring on the right, as a functor of the presheaf one tensors with: a morphism
`F ⟶ F'` of presheaves of modules induces a natural transformation
`tensorRight F ⟶ tensorRight F'`. -/
noncomputable def tensorRightMap {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {F F' : PresheafOfModules.{z} (ringPresheaf O)} (φ : F ⟶ F') :
    tensorRight.{v, u, w, z, z} (O := O) F ⟶ tensorRight.{v, u, w, z, z} (O := O) F' where
  app G := tensorMapRight G φ
  naturality {G H} ψ := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

section Coproduct

private noncomputable def evalCoproductCocone {O : Cᵒᵖ ⥤ CommRingCat.{w}} {ι : Type z}
    [DecidableEq ι]
    (F : ι → PresheafOfModules.{z} (ringPresheaf O)) (X : Cᵒᵖ) :
    Cocone (Discrete.functor F ⋙ PresheafOfModules.evaluation (ringPresheaf O) X) where
  pt := ModuleCat.of ((ringPresheaf O).obj X) (DirectSum ι fun i => (F i).obj X)
  ι :=
    { app := fun j => ModuleCat.ofHom (DirectSum.lof
        ((ringPresheaf O).obj X) ι (fun k => (F k).obj X) j.as)
      naturality := by
        rintro ⟨i⟩ ⟨j⟩ f
        obtain rfl := f.eq
        obtain rfl : f = 𝟙 _ := Subsingleton.elim _ _
        exact (Category.id_comp _).trans (Category.comp_id _).symm }

private noncomputable def evalCoproductCoconeIsColimit
    {O : Cᵒᵖ ⥤ CommRingCat.{w}} {ι : Type z} [DecidableEq ι]
    (F : ι → PresheafOfModules.{z} (ringPresheaf O)) (X : Cᵒᵖ) :
    IsColimit (evalCoproductCocone F X) := by
  let hc := ModuleCat.coproductCoconeIsColimit fun i => (F i).obj X
  exact ⟨fun s => hc.desc (Cofan.mk s.pt fun i => s.ι.app ⟨i⟩),
    fun s j => hc.fac (Cofan.mk s.pt fun i => s.ι.app ⟨i⟩) j,
    fun s m hm => hc.uniq (Cofan.mk s.pt fun i => s.ι.app ⟨i⟩) m fun i => hm i⟩

private noncomputable def evalCoproductIso {O : Cᵒᵖ ⥤ CommRingCat.{w}} {ι : Type z}
    [DecidableEq ι]
    (F : ι → PresheafOfModules.{z} (ringPresheaf O)) (X : Cᵒᵖ) :
    (colimit (Discrete.functor F)).obj X ≅
      ModuleCat.of ((ringPresheaf O).obj X) (DirectSum ι fun i => (F i).obj X) := by
  let E := PresheafOfModules.evaluation (ringPresheaf O) X
  let D := Discrete.functor F ⋙ E
  exact (preservesColimitIso E (Discrete.functor F)) ≪≫
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit D)
      (evalCoproductCoconeIsColimit F X)

private theorem evalCoproductIso_ι {O : Cᵒᵖ ⥤ CommRingCat.{w}} {ι : Type z} [DecidableEq ι]
    (F : ι → PresheafOfModules.{z} (ringPresheaf O)) (X : Cᵒᵖ) (i : Discrete ι) :
    (colimit.ι (Discrete.functor F) i).app X ≫ (evalCoproductIso F X).hom =
      ModuleCat.ofHom
        (DirectSum.lof ((ringPresheaf O).obj X) ι (fun j => (F j).obj X) i.as) := by
  classical
  let E := PresheafOfModules.evaluation (ringPresheaf O) X
  let D := Discrete.functor F ⋙ E
  let K := evalCoproductCocone F X
  let hK := evalCoproductCoconeIsColimit F X
  let e := preservesColimitIso E (Discrete.functor F)
  let u := IsColimit.coconePointUniqueUpToIso (colimit.isColimit D) hK
  have he : E.map (colimit.ι (Discrete.functor F) i) ≫ e.hom =
      colimit.ι D i := ι_preservesColimitIso_hom (G := E) (F := Discrete.functor F) i
  have hu : colimit.ι D i ≫ u.hom = K.ι.app i :=
    IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit D) hK i
  change E.map (colimit.ι (Discrete.functor F) i) ≫ (e.hom ≫ u.hom) = _
  rw [← Category.assoc, he, hu]
  dsimp [K, evalCoproductCocone]

private noncomputable def tensorCoproductEquiv {O : Cᵒᵖ ⥤ CommRingCat.{w}} {ι : Type z}
    (F : ι → PresheafOfModules.{z} (ringPresheaf O))
    (G : PresheafOfModules.{z} (ringPresheaf O)) (X : Cᵒᵖ) :
    TensorProduct ((ringPresheaf O).obj X) (G.obj X)
      ((colimit (Discrete.functor F)).obj X) ≃ₗ[(ringPresheaf O).obj X]
    DirectSum ι (fun i => TensorProduct ((ringPresheaf O).obj X) (G.obj X) ((F i).obj X)) := by
  classical
  let R := (ringPresheaf O).obj X
  let e := (evalCoproductIso F X).toLinearEquiv
  exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl _ _) e).trans
    (TensorProduct.directSumRight R R (G.obj X) fun i => (F i).obj X)

private noncomputable def tensorCoproductCocone {O : Cᵒᵖ ⥤ CommRingCat.{w}} {ι : Type z}
    (F : ι → PresheafOfModules.{z} (ringPresheaf O))
    (G : PresheafOfModules.{z} (ringPresheaf O)) :
    Cocone (Discrete.functor (fun i => tensorObj G (F i))) := by
  classical
  refine { pt := tensorObj G (colimit (Discrete.functor F))
           ι := { app := fun i => tensorMapRight G (colimit.ι (Discrete.functor F) i)
                  naturality := ?_ } }
  rintro ⟨i⟩ ⟨j⟩ f
  obtain rfl := f.eq
  simp [tensorMapRight]

private noncomputable def tensorCoproductIsColimit {O : Cᵒᵖ ⥤ CommRingCat.{w}} {ι : Type z}
    (F : ι → PresheafOfModules.{z} (ringPresheaf O))
    (G : PresheafOfModules.{z} (ringPresheaf O)) :
    IsColimit (tensorCoproductCocone F G) := by
  classical
  let K := tensorCoproductCocone F G
  refine PresheafOfModules.evaluationJointlyReflectsColimits _ K ?_
  intro X
  let c : Cofan (fun i => (tensorObj G (F i)).obj X) :=
    Cofan.mk (ModuleCat.of ((ringPresheaf O).obj X)
      (DirectSum ι (fun i => TensorProduct ((ringPresheaf O).obj X)
        (G.obj X) ((F i).obj X))))
      (fun i => ModuleCat.ofHom (DirectSum.lof ((ringPresheaf O).obj X)
        ι (fun j => TensorProduct ((ringPresheaf O).obj X) (G.obj X)
          ((F j).obj X)) i))
  let hc : IsColimit c := ModuleCat.coproductCoconeIsColimit (fun i => (tensorObj G (F i)).obj X)
  let e := tensorCoproductEquiv F G X
  let eIso := e.toModuleIso
  let E := PresheafOfModules.evaluation (ringPresheaf O) X
  let KX : Cocone ((Discrete.functor (fun i => tensorObj G (F i))) ⋙ E) :=
    { pt := ModuleCat.of ((ringPresheaf O).obj X)
        (TensorProduct ((ringPresheaf O).obj X) (G.obj X)
          ((colimit (Discrete.functor F)).obj X))
      ι := { app := fun j => (tensorMapRight G (colimit.ι (Discrete.functor F) j)).app X
             naturality := by
               rintro ⟨i⟩ ⟨j⟩ f
               obtain rfl := f.eq
               rfl } }
  let sCofan (s : Cocone ((Discrete.functor (fun i => tensorObj G (F i))) ⋙ E)) :
      Cofan (fun i => (tensorObj G (F i)).obj X) :=
    Cofan.mk s.pt (fun i => s.ι.app ⟨i⟩)
  have hj (j : Discrete ι) : KX.ι.app j ≫ eIso.hom = c.ι.app j := by
    change (tensorMapRight G (colimit.ι (Discrete.functor F) j)).app X ≫ eIso.hom = c.ι.app j
    let q := (colimit.ι (Discrete.functor F) j).app X
    have hq (y : (F j.as).obj X) : (evalCoproductIso F X).toLinearEquiv (q y) =
        DirectSum.lof ((ringPresheaf O).obj X) ι (fun i => (F i).obj X) j.as y :=
      congrArg (fun f => f y) (evalCoproductIso_ι F X j)
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    change e (x ⊗ₜ[(ringPresheaf O).obj X] q y) =
      DirectSum.lof ((ringPresheaf O).obj X) ι
        (fun k => TensorProduct ((ringPresheaf O).obj X) (G.obj X) ((F k).obj X))
        j.as (x ⊗ₜ[(ringPresheaf O).obj X] y)
    simp [e, tensorCoproductEquiv, hq, TensorProduct.directSumRight_tmul_lof]
  have hKX : IsColimit KX := by
    refine ⟨fun s => eIso.hom ≫ hc.desc (sCofan s), ?_, ?_⟩
    · intro s j
      exact (congrArg (fun f => f ≫ hc.desc (sCofan s)) (hj j)).trans (hc.fac (sCofan s) j)
    · intro s m hm
      have hji (j : Discrete ι) : c.ι.app j ≫ eIso.inv = KX.ι.app j :=
        (Iso.comp_inv_eq _).2 (hj j).symm
      have hdesc : hc.desc (sCofan s) = eIso.inv ≫ m := by
        refine (hc.uniq (sCofan s) (eIso.inv ≫ m) fun j => ?_).symm
        change c.ι.app j ≫ eIso.inv ≫ m = s.ι.app j
        simpa [Category.assoc] using (congrArg (fun f => f ≫ m) (hji j)).trans (hm j)
      simp [hdesc]
  exact hKX.ofIsoColimit (Cocone.ext (Iso.refl _) fun _ => rfl)

set_option synthInstance.maxHeartbeats 200000 in
-- instance synthesis for `tensorRight` and coproducts of presheaves of modules is heavy
/-- **Stacks 03EU, direct sums.** A coproduct of flat presheaves of modules is flat. -/
@[stacks 03EU "part (1), direct sums"]
lemma isFlat_coproduct {O : Cᵒᵖ ⥤ CommRingCat.{w}} {ι : Type z}
    (F : ι → PresheafOfModules.{z} (ringPresheaf O))
    (hF : ∀ i, IsFlat (F i)) : IsFlat (∐ F) := by
  classical
  let A := PresheafOfModules.{z} (ringPresheaf O)
  let D : Discrete ι ⥤ (A ⥤ A) := Discrete.functor (fun i => tensorRight (O := O) (F i))
  let K : Cocone D := by
    refine { pt := tensorRight (O := O) (∐ F), ι := ?_ }
    refine { app := fun i => tensorRightMap (colimit.ι (Discrete.functor F) i),
             naturality := ?_ }
    rintro ⟨i⟩ ⟨j⟩ f
    obtain rfl := f.eq
    simp
  have hK : IsColimit K := by
    refine CategoryTheory.Limits.evaluationJointlyReflectsColimits (c := K) ?_
    intro G
    let E := (evaluation A A).obj G
    let H₀ := D ⋙ E
    let H₁ := Discrete.functor (fun i => tensorObj G (F i))
    let α : H₀ ≅ H₁ := NatIso.ofComponents (fun i => Iso.refl _) (by
      rintro ⟨i⟩ ⟨j⟩ f
      obtain rfl := f.eq
      simp [H₀, H₁, D, E])
    let c := tensorCoproductCocone F G
    let c' := (Cocone.precompose α.hom).obj c
    have w : E.mapCocone K ≅ c' := Cocone.ext (Iso.refl _) (by
      rintro ⟨i⟩
      simp [c', c, K, E, H₀, H₁, D, tensorCoproductCocone, α, tensorRightMap, tensorMapRight])
    exact ((IsColimit.precomposeHomEquiv α c).symm
      (tensorCoproductIsColimit F G)).ofIsoColimit w.symm
  have : HasColimitsOfShape (Discrete ι) AddCommGrpCat.{z} := inferInstance
  have : HasColimitsOfShape (Discrete ι) A := PresheafOfModules.hasColimitsOfShape _ _
  have : HasColimitsOfShape (Discrete ι) (Cᵒᵖ ⥤ AddCommGrpCat.{z}) :=
    functorCategoryHasColimitsOfShape
  have : HasExactColimitsOfShape (Discrete ι) A :=
    HasExactColimitsOfShape.domain_of_functor (Discrete ι)
      (PresheafOfModules.toPresheaf (ringPresheaf O))
  have : HasColimitsOfShape (Discrete ι) (A ⥤ A) := functorCategoryHasColimitsOfShape
  let : HasExactColimitsOfShape (Discrete ι) (A ⥤ A) :=
    { preservesFiniteLimits := { preservesFiniteLimits _ := inferInstance } }
  have hD (i : ι) : PreservesFiniteLimits (D.obj ⟨i⟩) ∧
      PreservesFiniteColimits (D.obj ⟨i⟩) := (exactFunctor_iff (D.obj ⟨i⟩)).mp (hF i)
  have hlim : PreservesFiniteLimits (colimit D) :=
    (ObjectProperty.preservesFiniteLimits (J := A) (C := A)).prop_colimit D
      (fun i => (hD i.as).1)
  let : PreservesFiniteColimits D.flip :=
    preservesFiniteColimits_of_evaluation D.flip (fun i => (hD i.as).2)
  have hcolim : PreservesFiniteColimits (colimit D) :=
    preservesFiniteColimits_of_natIso (colimitIsoFlipCompColim D).symm
  exact (exactFunctor A A).prop_of_iso
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit D) hK)
    ((exactFunctor_iff _).2 ⟨hlim, hcolim⟩)

end Coproduct

section Filtered

private noncomputable def tensorColimitDiagram {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {J : Type ju} [Category.{jv} J]
    (F : J ⥤ PresheafOfModules.{z} (ringPresheaf O)) :
    J ⥤ (PresheafOfModules.{z} (ringPresheaf O) ⥤ PresheafOfModules.{z} (ringPresheaf O)) where
  obj j := tensorRight (O := O) (F.obj j)
  map f := tensorRightMap (F.map f)
  map_id j := by
    apply NatTrans.ext
    funext G
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    change TensorProduct.map LinearMap.id ((F.map (𝟙 j)).app X).hom
      (x ⊗ₜ[(ringPresheaf O).obj X] y) = x ⊗ₜ y
    rw [F.map_id]
    simp
  map_comp f g := by
    apply NatTrans.ext
    funext G
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    change x ⊗ₜ[(ringPresheaf O).obj X] ((F.map (f ≫ g)).app X y) =
      x ⊗ₜ[(ringPresheaf O).obj X] ((F.map g).app X ((F.map f).app X y))
    rw [F.map_comp]
    rfl

/- `moduleTensorLeft` is defined once, in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPreservesColimits`, and reused here and from
`StacksFrontier.CategoryTheory.Sites.Modules.TensorColimits`, which both need the same
module-universe-independent left tensor functor. -/
open SheafOfModules.TensorColimits (moduleTensorLeft)

private noncomputable def moduleTensorLeftRightAdjoint {R : Type w} [CommRing R]
    (G : ModuleCat.{z} R) : ModuleCat.{z} R ⥤ ModuleCat.{z} R :=
  (CategoryTheory.linearCoyoneda R (ModuleCat.{z} R)).obj (Opposite.op G)

private noncomputable def moduleTensorLeftAdjunction {R : Type w} [CommRing R]
    (G : ModuleCat.{z} R) : moduleTensorLeft G ⊣ moduleTensorLeftRightAdjoint G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f => by
            change X ⟶
              ((CategoryTheory.linearCoyoneda R (ModuleCat.{z} R)).obj (Opposite.op G)).obj Y
            exact ModuleCat.ofHom₂ <| LinearMap.compr₂ (TensorProduct.mk R X G)
              (f.hom.comp (TensorProduct.comm R X G).toLinearMap)
          invFun := fun f => by
            change ModuleCat.of R (G ⊗[R] X) ⟶ Y
            exact ModuleCat.ofHom <| (TensorProduct.AlgebraTensorModule.lift f.hom₂).comp
              (TensorProduct.comm R G X).toLinearMap
          left_inv := fun f => by
            apply ModuleCat.hom_ext
            apply TensorProduct.ext
            ext a x
            rfl
          right_inv := fun f => by
            apply ModuleCat.hom_ext
            ext x
            rfl }
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext a x
        rfl }

private noncomputable def tensorColimitCocone {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {J : Type ju} [Category.{jv} J] [UnivLE.{ju, z}]
    (F : J ⥤ PresheafOfModules.{z} (ringPresheaf O)) :
    Cocone (tensorColimitDiagram F) where
  pt := tensorRight (O := O) (colimit F)
  ι :=
    { app j := tensorRightMap (colimit.ι F j)
      naturality := by
        intro i j f
        apply NatTrans.ext
        funext G
        apply PresheafOfModules.hom_ext
        intro X
        apply ModuleCat.hom_ext
        apply TensorProduct.ext
        ext x y
        change x ⊗ₜ[(ringPresheaf O).obj X] (colimit.ι F j).app X ((F.map f).app X y) =
          x ⊗ₜ[(ringPresheaf O).obj X] (colimit.ι F i).app X y
        rw [← colimit.w F f]
        rfl }

private noncomputable def tensorColimitCoconeIsColimit {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {J : Type ju} [Category.{jv} J] [IsFiltered J] [UnivLE.{ju, z}]
    (F : J ⥤ PresheafOfModules.{z} (ringPresheaf O)) :
    IsColimit (tensorColimitCocone F) := by
  let A := PresheafOfModules.{z} (ringPresheaf O)
  let D := tensorColimitDiagram F
  let K := tensorColimitCocone F
  apply evaluationJointlyReflectsColimits
  intro G
  let E := (evaluation A A).obj G
  refine PresheafOfModules.evaluationJointlyReflectsColimits (D ⋙ E) (E.mapCocone K) ?_
  intro X
  let PX := PresheafOfModules.evaluation (ringPresheaf O) X
  let TL := moduleTensorLeft (G.obj X)
  let : PreservesColimitsOfSize.{jv, ju} TL :=
    (moduleTensorLeftAdjunction (G.obj X)).leftAdjoint_preservesColimits
  have hc : IsColimit (TL.mapCocone (PX.mapCocone (colimit.cocone F))) :=
    isColimitOfPreserves TL (isColimitOfPreserves PX (colimit.isColimit F))
  let H₀ := D ⋙ E ⋙ PX
  let H₁ := F ⋙ PX ⋙ TL
  let α : H₀ ≅ H₁ := NatIso.ofComponents (fun j => Iso.refl _) (by
    intro i j f
    simp only [Iso.refl_hom]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl)
  let c := TL.mapCocone (PX.mapCocone (colimit.cocone F))
  let c' := (Cocone.precompose α.hom).obj c
  have hc' : IsColimit c' := (IsColimit.precomposeHomEquiv α c).symm hc
  have w : PX.mapCocone (E.mapCocone K) ≅ c' := Cocone.ext (Iso.refl _) (by
    intro j
    simp only [Iso.refl_hom]
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl)
  exact hc'.ofIsoColimit w.symm

private theorem exactPresheafModuleColimits {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {J : Type ju} [Category.{jv} J] [IsFiltered J] [UnivLE.{ju, z}] :
    HasExactColimitsOfShape J (PresheafOfModules.{z} (ringPresheaf O)) := by
  have : LocallySmall.{max jv z} J := inferInstance
  have : UnivLE.{ju, max jv z} := UnivLE.trans
  let : Category.{max jv z} (ShrinkHoms.{ju} J) := inferInstance
  let S := Shrink.{max jv z} (ShrinkHoms.{ju} J)
  let e : J ≌ S := (ShrinkHoms.equivalence.{max jv z} J).trans
    (Shrink.equivalence.{max jv z, max jv z} (ShrinkHoms.{ju} J))
  have : IsFiltered S := IsFiltered.of_equivalence e
  have : HasExactColimitsOfShape S (AddCommGrpCat.{max jv z}) :=
    CategoryTheory.AB5OfSize.ofShape S
  have : HasExactColimitsOfShape J (AddCommGrpCat.{max jv z}) :=
    HasExactColimitsOfShape.of_domain_equivalence _ e.symm
  have : HasExactColimitsOfShape J (AddCommGrpCat.{z}) :=
    HasExactColimitsOfShape.domain_of_functor J (AddCommGrpCat.uliftFunctor.{jv, z})
  have : HasExactColimitsOfShape J (Cᵒᵖ ⥤ Ab.{z}) := inferInstance
  exact HasExactColimitsOfShape.domain_of_functor J
    (PresheafOfModules.toPresheaf (ringPresheaf O))

/-- **Stacks 03EU, filtered colimits.** A filtered colimit of flat presheaves of modules is
flat. -/
@[stacks 03EU "part (1), filtered colimits"]
lemma isFlat_colimit {O : Cᵒᵖ ⥤ CommRingCat.{w}}
    {J : Type ju} [Category.{jv} J] [IsFiltered J] [UnivLE.{ju, z}]
    (F : J ⥤ PresheafOfModules.{z} (ringPresheaf O))
    (hF : ∀ j, IsFlat (F.obj j)) : IsFlat (colimit F) := by
  let A := PresheafOfModules.{z} (ringPresheaf O)
  let D := tensorColimitDiagram F
  have : HasExactColimitsOfShape J A := exactPresheafModuleColimits
  let : HasExactColimitsOfShape J (A ⥤ A) := inferInstance
  have hD (j : J) : PreservesFiniteLimits (D.obj j) ∧
      PreservesFiniteColimits (D.obj j) := (exactFunctor_iff (D.obj j)).mp (hF j)
  have hlim : PreservesFiniteLimits (colimit D) :=
    (ObjectProperty.preservesFiniteLimits (J := A) (C := A)).prop_colimit D
      (fun j => (hD j).1)
  let : PreservesFiniteColimits D.flip :=
    preservesFiniteColimits_of_evaluation D.flip (fun j => (hD j).2)
  have hcolim : PreservesFiniteColimits (colimit D) :=
    preservesFiniteColimits_of_natIso (colimitIsoFlipCompColim D).symm
  exact (exactFunctor A A).prop_of_iso
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit D) (tensorColimitCoconeIsColimit F))
    ((exactFunctor_iff _).2 ⟨hlim, hcolim⟩)

end Filtered

end Stacks

end
