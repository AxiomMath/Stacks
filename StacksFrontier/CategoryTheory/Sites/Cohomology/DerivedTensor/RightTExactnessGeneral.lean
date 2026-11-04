module

import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize
public import StacksFrontier.Algebra.Homology.DerivedCategory.UniformUpperBounds
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.Interface
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RightTExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.BoundedAboveFlatComplexes

/-!
# Right t-exactness of the derived tensor product, at any universes

On a ringed site `X : RingedSite.{u, v, w}`: the total tensor complex of two complexes concentrated
in degrees `≤ a` and `≤ b` is concentrated in degrees `≤ a + b`, every bounded above object has a
K-flat representative concentrated in the same degrees, and so `K ⊗^L L` lies in `D^{≤ a + b}`
when `K` lies in `D^{≤ a}` and `L` in `D^{≤ b}`: the statements of `RightTExactness.lean` without
its single-universe restriction.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u d

namespace Stacks.SheafOfModules.DerivedTensorProduct

universe v w

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X : RingedSite.{u, v, w}}
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

omit [HasDerivedCategory.{d} (RingedSite.Modules.{u, v, w} X)] in
/-- **The total tensor complex of two bounded above complexes is bounded above**, with the two
bounds added: every summand `P^p ⊗_O Q^q` of a term in degree `> a + b` has a zero factor. -/
theorem isStrictlyLE_mapBifunctor (P Q : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ)
    (a b : ℤ) [P.IsStrictlyLE a] [Q.IsStrictlyLE b] :
    CochainComplex.IsStrictlyLE (HomologicalComplex.mapBifunctor P Q
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)) (a + b) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : IsZero (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (P.X p)).obj (Q.X q)) := by
    by_cases hp : a < p
    · exact ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map_isZero
        (P.isZero_of_isStrictlyLE a p hp)).obj _
    · exact ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (P.X p)).map_isZero
        (Q.isZero_of_isStrictlyLE b q (by dsimp at hpq; omega))
  exact hz.eq_of_src _ _

/-- **A bounded above object of `D(O)` has a K-flat representative with the same bound**: a
representative is resolved by a complex of flat modules vanishing above the bound (Stacks 05T7,
every module being a quotient of a flat one), which is K-flat by Stacks 06YQ. The site universes
are free of the universe of the sections. -/
theorem exists_isKFlat_isStrictlyLE_representative (K : RingedSite.DerivedModules.{u, v, w, d} X)
    (a : ℤ) [K.IsLE a] :
    ∃ F : CochainComplex (RingedSite.Modules.{u, v, w} X) ℤ,
      Stacks.SheafOfModules.IsKFlat X.O F ∧ F.IsStrictlyLE a ∧
        Nonempty (DerivedCategory.Q.obj F ≅ K) := by
  obtain ⟨P, ⟨eP⟩⟩ : ∃ P, Nonempty (DerivedCategory.Q.obj P ≅ K) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso K⟩⟩
  have hPLE : P.IsLE a :=
    (DerivedCategory.isLE_Q_obj_iff P a).1
      (DerivedCategory.TStructure.t.isLE_of_iso eP.symm a)
  let Pflat : ObjectProperty (RingedSite.Modules.{u, v, w} X) :=
    fun M => AlgebraicGeometry.SheafOfModules.IsFlat.{v, u, w, w} (O := X.O) M
  have : Pflat.ContainsZero :=
    Stacks.SheafOfModules.FlatCoproduct.containsZero_isFlat_ofSize X.O
  obtain ⟨F, f, hf, hFflat, hFLE⟩ :=
    (CochainComplex.exists_quasiIso_prop Pflat
      (fun M => by
        obtain ⟨N, π, hflat, hepi⟩ :=
          Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize X.O M
        exact ⟨N, hflat, π, hepi⟩) a).2 P
  have : IsIso (DerivedCategory.Q.map f) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ f).2 hf
  exact ⟨F, Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat X.O F ⟨a, hFLE⟩ hFflat, hFLE,
    ⟨asIso (DerivedCategory.Q.map f) ≪≫ eP⟩⟩

/-- **The derived tensor product is right t-exact in both variables**: the derived tensor
product of an object of `D^{≤ a}(O)` with an object of `D^{≤ b}(O)` lies in `D^{≤ a + b}(O)`.
Both factors have K-flat representatives with zero terms above their bounds, on which the
derived tensor product is the total tensor complex. The site universes are free. -/
theorem isLE_tensor_general (T : DerivedTensorProduct.{u, v, w, d} X)
    (K L : RingedSite.DerivedModules.{u, v, w, d} X) (a b : ℤ) [K.IsLE a] [L.IsLE b] :
    ((T.tensor.obj K).obj L).IsLE (a + b) := by
  obtain ⟨F, hF, hFLE, ⟨eF⟩⟩ := exists_isKFlat_isStrictlyLE_representative K a
  obtain ⟨G, hG, hGLE, ⟨eG⟩⟩ := exists_isKFlat_isStrictlyLE_representative L b
  have hTot : (DerivedCategory.Q.obj
      (HomologicalComplex.mapBifunctor F G (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
        (ComplexShape.up ℤ))).IsLE (a + b) := by
    rw [DerivedCategory.isLE_Q_obj_iff]
    have := isStrictlyLE_mapBifunctor F G a b
    infer_instance
  refine DerivedCategory.TStructure.t.isLE_of_iso (X := DerivedCategory.Q.obj
    (HomologicalComplex.mapBifunctor F G
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ))) ?_ (a + b)
  exact ((T.tensor.mapIso eF.symm).app L ≪≫ (T.tensor.obj _).mapIso eG.symm ≪≫
      T.comparison F G hF hG).symm

/-- **An upper cohomological bound on each factor bounds the derived tensor product**, with the
two bounds added. -/
@[sga "6 I 2.16" "special case",
  sga "6 III 1.11" "(a), special case",
  sga "6 III 1.8" "special case"]
theorem isBoundedAboveBy_tensor_general (T : DerivedTensorProduct.{u, v, w, d} X)
    {K L : RingedSite.DerivedModules.{u, v, w, d} X} {a b : ℤ}
    (hK : Stacks.DerivedCategory.IsBoundedAboveBy K a)
    (hL : Stacks.DerivedCategory.IsBoundedAboveBy L b) :
    Stacks.DerivedCategory.IsBoundedAboveBy ((T.tensor.obj K).obj L) (a + b) := by
  rw [Stacks.DerivedCategory.isBoundedAboveBy_iff_isLE] at hK hL ⊢
  have := hK
  have := hL
  exact isLE_tensor_general T K L a b

end Stacks.SheafOfModules.DerivedTensorProduct

end
