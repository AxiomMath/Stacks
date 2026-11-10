module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.StalkwiseCriterion
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections
public import StacksFrontier.CategoryTheory.Sites.Point.ConstantSheafFiber
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSectionsSepClosed
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Abelian sheaves on the spectrum of a separably closed field are constant

Let `k` be a separably closed field. Every abelian sheaf `F` on the small étale site of
`Spec k` is the constant sheaf on its group of global sections: the map
`k_{const}(Γ(F)) ⟶ F` adjoint to the identity of `Γ(F)` is an isomorphism.

## Main definitions

* `Stacks.EtaleCohomology.constantSheafToSheaf` — the map `k_{const}(Γ(F)) ⟶ F`, for an
  abelian sheaf on the small étale site of any scheme.

## Main results

* `Stacks.EtaleCohomology.isIso_constantSheafToSheaf_of_isSepClosed` — over a separably closed
  field it is an isomorphism.

## References

* [Stacks Project, Tag 03PW](https://stacks.math.columbia.edu/tag/03PW)
* [Stacks Project, Tag 0F08](https://stacks.math.columbia.edu/tag/0F08)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- The morphism from an object of the small étale site of `T` to the final object `T ⟶ T`. -/
public def toEtaleMkId {T : Scheme.{u}} (U : T.Etale) : U ⟶ Scheme.Etale.mk (𝟙 T) :=
  MorphismProperty.Over.homMk U.hom (Category.comp_id _) trivial

/-- Any two morphisms to the final object `T ⟶ T` of the small étale site agree. -/
public theorem toEtaleMkId_unique {T : Scheme.{u}} {U : T.Etale}
    (a : U ⟶ Scheme.Etale.mk (𝟙 T)) : a = toEtaleMkId U :=
  MorphismProperty.Over.Hom.ext ((Category.comp_id a.left).symm.trans (MorphismProperty.Over.w a))

/-- The cone of restriction maps from global sections, read as a morphism out of the constant
presheaf on the sections over the final object. -/
public def constantPresheafToPresheaf {T : Scheme.{u}}
    (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (Functor.const (T.Etale)ᵒᵖ).obj (F.obj.obj (op (Scheme.Etale.mk (𝟙 T)))) ⟶ F.obj where
  app U := F.obj.map (toEtaleMkId U.unop).op
  naturality U V a := by
    change 𝟙 _ ≫ F.obj.map _ = F.obj.map _ ≫ F.obj.map a
    rw [Category.id_comp, ← F.obj.map_comp]
    congr 1
    exact Quiver.Hom.unop_inj ((toEtaleMkId_unique _).trans (toEtaleMkId_unique _).symm)

/-- **The comparison of an abelian sheaf with the constant sheaf on its global sections.** For
an abelian sheaf `F` on the small étale site of `T`, the map `T_{const}(Γ(F)) ⟶ F` induced by
the restriction maps from global sections, the global sections being those over the final
object. -/
public def constantSheafToSheaf {T : Scheme.{u}} (F : Sheaf (smallEtaleTopology T) Ab.{u + 1}) :
    (constantSheaf (smallEtaleTopology T) Ab.{u + 1}).obj
      (F.obj.obj (op (Scheme.Etale.mk (𝟙 T)))) ⟶ F where
  hom := sheafifyLift (smallEtaleTopology T) (constantPresheafToPresheaf F) F.property

/-- **Abelian sheaves on the spectrum of a separably closed field are constant.** For `k`
separably closed and an abelian sheaf `F` on the small étale site of `Spec k`, the comparison
`k_{const}(Γ(F)) ⟶ F` is an isomorphism. -/
@[sga "4½ Rapport 2.2" "First clause of 2.2"]
public theorem isIso_constantSheafToSheaf_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k]
    (F : Sheaf (smallEtaleTopology (Spec (.of k))) Ab.{u + 1}) :
    IsIso (constantSheafToSheaf F) := by
  rw [isIso_iff_forall_isIso_smallEtaleStalkAb]
  intro x
  let Φ := pointSmallEtale x.hom
  let T := Scheme.Etale.mk (𝟙 (Spec (.of k)))
  let M := F.obj.obj (op T)
  let P := (Functor.const (Spec (.of k)).Etaleᵒᵖ).obj M
  let q : Φ.fiber.obj T := Over.homMk x.hom (by change x.hom ≫ 𝟙 _ = x.hom; simp)
  have hP : IsIso (Φ.presheafFiber.map (toSheafify (smallEtaleTopology (Spec (.of k))) P)) :=
    Sites.isIso_presheafFiber_map_toSheafify Φ M
  let c : sheafify (smallEtaleTopology (Spec (.of k))) P ⟶ F.obj := (constantSheafToSheaf F).hom
  have hfac : Φ.presheafFiber.map (toSheafify (smallEtaleTopology (Spec (.of k))) P) ≫
      Φ.presheafFiber.map c = Φ.presheafFiber.map (constantPresheafToPresheaf F) := by
    rw [← Functor.map_comp]
    exact congrArg Φ.presheafFiber.map
      (toSheafify_sheafifyLift (smallEtaleTopology (Spec (.of k))) _ F.property)
  have hα : IsIso (Φ.presheafFiber.map (constantPresheafToPresheaf F)) := by
    have : IsIso (Φ.toPresheafFiber T q P) := by
      rw [(Iso.comp_hom_eq_id _).1 (Sites.constantPresheafFiberIso_ι Φ M T q)]
      infer_instance
    have : IsIso ((constantPresheafToPresheaf F).app (op T)) := by
      change IsIso (F.obj.map (toEtaleMkId T).op)
      rw [← toEtaleMkId_unique (𝟙 T), op_id, F.obj.map_id]
      infer_instance
    have : IsIso (Φ.toPresheafFiber T q F.obj) :=
      isIso_toPresheafFiber_etaleMkId_of_isSepClosed k x.hom F.obj
    rw [← isIso_comp_left_iff (Φ.toPresheafFiber T q P),
      Φ.toPresheafFiber_naturality (constantPresheafToPresheaf F) T q]
    infer_instance
  exact (isIso_comp_left_iff _ (Φ.presheafFiber.map c)).mp (by rwa [hfac])

end Stacks.EtaleCohomology

end
