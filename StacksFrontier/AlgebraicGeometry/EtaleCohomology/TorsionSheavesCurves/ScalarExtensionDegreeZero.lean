module

public import Mathlib.FieldTheory.IsSepClosed
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FlatSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.HenselianPairRestriction
import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.AbelianCoefficientTransfer
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Sheafification.SmallEtaleAbelian
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SubmersiveSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.ScalarExtension
import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedAffine
import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqTranspose
import StacksFrontier.RingTheory.GeometricallyConnected

/-!
# Degree-zero étale cohomology after extending a separably closed base field

Let `p : Y ⟶ X` be a morphism of schemes which is universally submersive and has geometrically
connected fibres. Tag 0EZK says that the canonical comparison `Γ(X, G) ⟶ Γ(Y, p⁻¹G)` is
bijective for every sheaf of sets `G` on the small étale site of `X`. This file reads that
statement for abelian sheaves in degree `0` of étale cohomology, where cohomology is `Ext` out of
the constant sheaf `ℤ` and the map is `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap`.
The case of the projection `X_{k'} ⟶ X` of a scalar extension of a separably closed field `k`
is Tag 0A3I for abelian sheaves, in degree `0`.

## Main results

* `CategoryTheory.Adjunction.bijective_leftAdjointUniq_inv_app_comp_map`: for adjunctions
  `L ⊣ R`, `c ⊣ e` and `c' ⊣ R ⋙ e`, the map `φ ↦ θ⁻¹ ≫ L.map φ` from `c M ⟶ A` to
  `c' M ⟶ L A`, with `θ : c ⋙ L ≅ c'` the canonical comparison of left adjoints, is bijective
  as soon as `e` inverts the unit of `L ⊣ R` at `A`.
* `Stacks.EtaleCohomology.isIso_etaleAbelianInverseImage_unit_app_final`: the unit of the
  inverse-image/direct-image adjunction of abelian sheaves is invertible on sections over the
  final object, for `p` universally submersive with geometrically connected fibres.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_zero`: restriction along such
  a `p` is bijective on `H⁰`.
* `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_zero`:
  restriction along the projection of a scalar extension of a separably closed field is
  bijective on `H⁰`.

## Implementation notes

In degree `0`, `Ext` is `Hom`, so restriction is `φ ↦ θ⁻¹ ≫ p⁻¹.map φ` with `θ` the comparison
`Stacks.EtaleCohomology.etaleAbelianInverseImageConstantIso`, which is by construction the
comparison of two left adjoints of sections over the final object. The abstract adjunction
lemma above reduces bijectivity to the unit of `p⁻¹ ⊣ p_*` being invertible over the final
object. That unit is compared with the unit for sheaves of sets through the forgetful functor,
by `Stacks.EtaleCohomology.coefficientPullbackComparison_unit`, and the set-level unit over the
final object is `Stacks.EtaleCohomology.isIso_smallEtaleInverseImageSections` at the identity of
the base change of the final object.

## References

* [Stacks Project, Tag 0A3I](https://stacks.math.columbia.edu/tag/0A3I)
* [Stacks Project, Tag 0EZK](https://stacks.math.columbia.edu/tag/0EZK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒜 : Type u₁} {ℬ : Type u₂} {𝒞 : Type u₃} [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Category.{v₃} 𝒞] {L : 𝒜 ⥤ ℬ} {R : ℬ ⥤ 𝒜} (adj : L ⊣ R) {c : 𝒞 ⥤ 𝒜} {e : 𝒜 ⥤ 𝒞}
  (adjc : c ⊣ e) {c' : 𝒞 ⥤ ℬ} (adjc' : c' ⊣ R ⋙ e)

/-- For adjunctions `L ⊣ R`, `c ⊣ e` and `c' ⊣ R ⋙ e`, transposing `θ⁻¹ ≫ L.map φ` along
`c' ⊣ R ⋙ e`, where `θ : c ⋙ L ≅ c'` is the canonical comparison of left adjoints, gives the
transpose of `φ` along `c ⊣ e` followed by `e` of the unit of `L ⊣ R`. This is
`CategoryTheory.Adjunction.homEquiv_leftAdjointUniq_inv_app_comp` for the composite adjunction
`c ⋙ L ⊣ R ⋙ e`, with the transpose of `L.map φ` along `L ⊣ R` computed. -/
theorem homEquiv_leftAdjointUniq_inv_app_comp_map (M : 𝒞) {A : 𝒜} (φ : c.obj M ⟶ A) :
    adjc'.homEquiv M (L.obj A) (((adjc.comp adj).leftAdjointUniq adjc').inv.app M ≫ L.map φ) =
      adjc.homEquiv M A φ ≫ e.map (adj.unit.app A) := by
  rw [homEquiv_leftAdjointUniq_inv_app_comp, comp_homEquiv]
  simp [homEquiv_unit]

/-- For adjunctions `L ⊣ R`, `c ⊣ e` and `c' ⊣ R ⋙ e`, with `θ : c ⋙ L ≅ c'` the canonical
comparison of left adjoints, the map `φ ↦ θ⁻¹ ≫ L.map φ` from `c M ⟶ A` to `c' M ⟶ L A` is
bijective as soon as `e` inverts the unit of `L ⊣ R` at `A`: up to the two adjunction
bijections it is postcomposition with `e` of that unit. -/
theorem bijective_leftAdjointUniq_inv_app_comp_map (M : 𝒞) (A : 𝒜)
    [IsIso (e.map (adj.unit.app A))] :
    Function.Bijective (fun φ : c.obj M ⟶ A =>
      ((adjc.comp adj).leftAdjointUniq adjc').inv.app M ≫ L.map φ) := by
  let post : (M ⟶ e.obj A) ≃ (M ⟶ e.obj (R.obj (L.obj A))) :=
    { toFun := fun g => g ≫ e.map (adj.unit.app A)
      invFun := fun g => g ≫ inv (e.map (adj.unit.app A))
      left_inv := fun g => by simp
      right_inv := fun g => by simp }
  have h : (fun φ : c.obj M ⟶ A =>
      ((adjc.comp adj).leftAdjointUniq adjc').inv.app M ≫ L.map φ) =
        (adjc'.homEquiv M (L.obj A)).symm ∘ post ∘ adjc.homEquiv M A :=
    funext fun φ => (adjc'.homEquiv M (L.obj A)).eq_symm_apply.mpr
      (homEquiv_leftAdjointUniq_inv_app_comp_map adj adjc adjc' M φ)
  rw [h]
  exact (adjc'.homEquiv _ _).symm.bijective.comp (post.bijective.comp (adjc.homEquiv _ _).bijective)

end CategoryTheory.Adjunction

namespace Stacks.EtaleCohomology

universe u v w

attribute [local instance] AlgebraicGeometry.Etale.instIsMultiplicativeScheme

/-- The forgetful functor of abelian groups in the étale coefficient universe `max (u + 1) v`
preserves left Kan extensions along the opposite of base change of étale schemes: the indexing
costructured-arrow categories are filtered, base change being representably flat, and the
forgetful functor preserves filtered colimits of that size. This generalizes
`Stacks.EtaleCohomology.preservesLeftKanExtensions_forget_smallEtaleBaseChange`, which is the
case `v = 0`. -/
instance preservesLeftKanExtensions_forget_smallEtaleBaseChange_max {X Y : Scheme.{u}}
    (i : Y ⟶ X) :
    (forget AddCommGrpCat.{max (u + 1) v}).PreservesLeftKanExtensions
      (smallEtaleBaseChange i).op := by
  intro P
  have hfil : ∀ V : Y.Etaleᵒᵖ,
      IsFiltered (CostructuredArrow (smallEtaleBaseChange i).op V) := fun V =>
    IsFiltered.of_equivalence (structuredArrowOpEquivalence (smallEtaleBaseChange i) V.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{max (u + 1) v}) :=
    preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u + 1} _
  infer_instance

/-- For `p` universally submersive with geometrically connected fibres, the unit of the
inverse-image/direct-image adjunction of abelian sheaves on the small étale sites is invertible
on sections over the final object `X` of the small étale site of `X`. Through the forgetful
functor it is the unit for sheaves of sets, followed by the invertible comparison of the two
inverse images; the former is invertible by Tag 0EZK in the form
`Stacks.EtaleCohomology.isIso_smallEtaleInverseImageSections`. -/
theorem isIso_etaleAbelianInverseImage_unit_app_final {X Y : Scheme.{u}} (p : Y ⟶ X)
    (hsub : (topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally p)
    [GeometricallyConnected p]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    IsIso (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (smallEtaleBaseChange p) AddCommGrpCat.{max (u + 1) v}
      X.smallEtaleTopology Y.smallEtaleTopology).unit.app F).hom.app
        (Opposite.op (MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)))) := by
  let V : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)
  let a : (smallEtaleBaseChange p).obj V ⟶ (smallEtaleBaseChange p).obj V := 𝟙 _
  have hid : a.left ≫ pullback.fst V.hom p =
      pullback.fst (𝟙 X) p := Category.id_comp _
  have hset := isIso_smallEtaleInverseImageSections.{u, v} p
    ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{max (u + 1) v})).obj F)
    a (hid ▸ MorphismProperty.pullback_fst (𝟙 X) p hsub)
    (hid ▸ (inferInstance : GeometricallyConnected (pullback.fst (𝟙 X) p)))
  simp only [smallEtaleInverseImageSections] at hset
  rw [show a.op = 𝟙 _ from rfl, CategoryTheory.Functor.map_id, Category.comp_id] at hset
  have hcomp : IsIso (coefficientPullbackComparison (smallEtaleBaseChange p)
      X.smallEtaleTopology Y.smallEtaleTopology (forget AddCommGrpCat.{max (u + 1) v}) F) := by
    rw [← coefficientPullbackTwoSquare_app]
    infer_instance
  have hcompV : IsIso ((coefficientPullbackComparison (smallEtaleBaseChange p)
      X.smallEtaleTopology Y.smallEtaleTopology (forget AddCommGrpCat.{max (u + 1) v}) F).hom.app
        (Opposite.op ((smallEtaleBaseChange p).obj V))) := by
    have : IsIso (coefficientPullbackComparison (smallEtaleBaseChange p)
      X.smallEtaleTopology Y.smallEtaleTopology (forget AddCommGrpCat.{max (u + 1) v}) F).hom :=
      Functor.map_isIso (sheafToPresheaf Y.smallEtaleTopology (Type (max (u + 1) v)))
        (coefficientPullbackComparison (smallEtaleBaseChange p) X.smallEtaleTopology
          Y.smallEtaleTopology (forget AddCommGrpCat.{max (u + 1) v}) F)
    infer_instance
  have h : (forget AddCommGrpCat.{max (u + 1) v}).map
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtaleBaseChange p) AddCommGrpCat.{max (u + 1) v}
        X.smallEtaleTopology Y.smallEtaleTopology).unit.app F).hom.app (Opposite.op V)) =
      smallEtaleUnitApp p
          ((sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{max (u + 1) v})).obj F) V ≫
        (coefficientPullbackComparison (smallEtaleBaseChange p) X.smallEtaleTopology
          Y.smallEtaleTopology (forget AddCommGrpCat.{max (u + 1) v}) F).hom.app
            (Opposite.op ((smallEtaleBaseChange p).obj V)) :=
    (Category.comp_id _).symm.trans (congrArg (fun φ => φ.hom.app (Opposite.op V))
      (coefficientPullbackComparison_unit (smallEtaleBaseChange p) X.smallEtaleTopology
        Y.smallEtaleTopology (forget AddCommGrpCat.{max (u + 1) v}) F)).symm
  have : IsIso ((forget AddCommGrpCat.{max (u + 1) v}).map
      (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (smallEtaleBaseChange p) AddCommGrpCat.{max (u + 1) v}
        X.smallEtaleTopology Y.smallEtaleTopology).unit.app F).hom.app (Opposite.op V))) := by
    rw [h]
    exact IsIso.comp_isIso' hset hcompV
  exact isIso_of_reflects_iso _ (forget AddCommGrpCat.{max (u + 1) v})

/-- For `p : Y ⟶ X` universally submersive with geometrically connected fibres, restriction
along `p` is bijective on degree-`0` étale cohomology of every abelian sheaf. This is Tag 0EZK
for abelian sheaves, read in degree `0` of `Ext`-cohomology. -/
theorem bijective_etaleCohomologyRestrictionMap_zero {X Y : Scheme.{u}} (p : Y ⟶ X)
    (hsub : (topologically @Topology.IsQuotientMap : MorphismProperty Scheme.{u}).universally p)
    [GeometricallyConnected p]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w} p F 0) := by
  let : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
    AlgebraicGeometry.Etale.instIsMultiplicativeScheme.toContainsIdentities
  let T : X.Etale := MorphismProperty.Over.mk ⊤ (𝟙 X) (by infer_instance)
  let hT : IsTerminal T := MorphismProperty.Over.mkIdTerminal _ _
  let hGT := hT.isTerminalObj (smallEtaleBaseChange p)
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (smallEtaleBaseChange p) AddCommGrpCat.{max (u + 1) v}
    X.smallEtaleTopology Y.smallEtaleTopology
  have : IsIso (((sheafSections X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj
      (Opposite.op T)).map (adj.unit.app F)) :=
    isIso_etaleAbelianInverseImage_unit_app_final p hsub F
  have hΦ := Adjunction.bijective_leftAdjointUniq_inv_app_comp_map adj
    (constantSheafAdj _ _ hT) (constantSheafAdj _ _ hGT) (AddCommGrpCat.of (ULift ℤ)) F
  have hcomp : etaleCohomologyRestrictionMap.{u, v, w} p F 0 ∘ Abelian.Ext.mk₀ =
      Abelian.Ext.mk₀ ∘ (fun φ => (((constantSheafAdj _ _ hT).comp adj).leftAdjointUniq
        (constantSheafAdj _ _ hGT)).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
          (etaleAbelianInverseImage.{u, v} p).map φ) := by
    funext φ
    simp only [Function.comp_apply, etaleCohomologyRestrictionMap_apply,
      Abelian.Ext.mapExactFunctor_mk₀, Abelian.Ext.mk₀_comp_mk₀]
    rfl
  exact (Function.Bijective.of_comp_iff _ (Abelian.Ext.mk₀_bijective _ _)).mp
    (hcomp ▸ (Abelian.Ext.mk₀_bijective _ _).comp hΦ)

/-- **Tag 0A3I for abelian sheaves, in degree `0`.** For a scheme `X` over a separably closed
field `k` and any field extension `k'/k`, restriction along the projection
`X_{k'} = X ×_{Spec k} Spec k' ⟶ X` is bijective on degree-`0` étale cohomology of every abelian
sheaf on the small étale site of `X`. The projection is flat and quasi-compact, hence
universally submersive, and has geometrically connected fibres, because `Spec k'` is
geometrically connected over the separably closed field `k`. -/
theorem bijective_etaleCohomologyRestrictionMap_scalarExtensionFst_zero
    (k k' : Type u) [Field k] [IsSepClosed k] [Field k'] [Algebra k k']
    {X : Scheme.{u}} (π : X ⟶ Spec (.of k))
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})]
    [HasExt.{w} (Sheaf (scalarExtension k k' π).smallEtaleTopology
      AddCommGrpCat.{max (u + 1) v})]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, v, w}
      (scalarExtensionFst k k' π) F 0) :=
  have : GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap k k'))) :=
    (AlgebraicGeometry.geometricallyConnected_spec_iff k k').2
      ((Algebra.isGeometricallyConnected_iff_connectedSpace_primeSpectrum k k').2 inferInstance)
  bijective_etaleCohomologyRestrictionMap_zero.{u, v, w} (scalarExtensionFst k k' π)
    (universally_isQuotientMap_of_flat_quasiCompact _) F

end Stacks.EtaleCohomology

end
