module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Étale inverse image preserves torsion abelian sheaves

Let `f : Y ⟶ X` be a morphism of schemes. The inverse image `f⁻¹` of abelian sheaves for the
small étale topologies carries torsion abelian sheaves to torsion abelian sheaves, and, being
exact, its extension to the derived category carries objects with torsion cohomology sheaves to
objects with torsion cohomology sheaves.

The inverse image is the sheafification of the left Kan extension along the opposite of base
change. The first half of the file proves, for an arbitrary cover-preserving functor of sites, that
this left Kan extension carries a locally torsion presheaf to a locally torsion presheaf, as soon
as its values are colimits whose elements are represented at some stage. A section of the left
Kan extension over `U'` is then the image of a section `x` of `P` over some `V` along an arrow
`U' ⟶ G V`; the section `x` is annihilated by positive integers on a covering sieve of `V`, the
image of that sieve under `G` covers `G V`, and its pullback to `U'` is a covering sieve on whose
members the given section is the image of a restriction of `x`, hence is annihilated. The
sheafification of a locally torsion presheaf is torsion, which gives the statement for sheaves.

## Main results

* `Stacks.Torsion.isLocallyTorsion_lan_obj`: the left Kan extension of a locally torsion presheaf
  along the opposite of a cover-preserving functor is locally torsion, when the forgetful functor
  preserves the colimits computing it pointwise.
* `Stacks.EtaleCohomology.torsionSheafProperty_etaleAbelianInverseImage`: étale inverse image
  carries torsion abelian sheaves to torsion abelian sheaves.
* `Stacks.EtaleCohomology.torsionCohomologyProperty_etaleAbelianDerivedInverseImage`: étale
  inverse image on derived categories carries objects with torsion cohomology sheaves to objects
  with torsion cohomology sheaves.

## Implementation notes

The site-level lemma asks that the forgetful functor of `AddCommGrpCat` preserve the colimits
over the comma categories `CostructuredArrow G.op U` rather than that these categories be
filtered: that is the only use of filteredness, and it avoids the universe bookkeeping that the
passage from filteredness to preservation needs. For the small étale site that passage is made
as in `Stacks.EtaleCohomology.etaleAbelianInverseImage_preservesFiniteLimits`: base change is
representably flat, so the comma categories are filtered, and the forgetful functor of
`AddCommGrpCat.{max (u + 1) v}` preserves filtered colimits of the relevant size.

The derived statement is reduced to the sheaf statement through
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, the identification `Hⁱ(f⁻¹K) ≅ f⁻¹Hⁱ(K)`
for the exact functor `f⁻¹`.

## References

* [Stacks Project, Tag 0DD7](https://stacks.math.columbia.edu/tag/0DD7)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.Torsion

section LanLocallyTorsion

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)

/-- **Every section of a pointwise left Kan extension comes from a stage.** If the forgetful
functor preserves the colimit computing the left Kan extension of `P` along `G.op` at `U'`, then
every section of the extension over `U'` is the image, along some arrow `U' ⟶ G V`, of the unit
applied to a section of `P` over `V`. -/
public theorem exists_leftKanExtension_obj_eq_map_unit
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) [G.op.HasPointwiseLeftKanExtension P] (U' : D)
    [PreservesColimit (CostructuredArrow.proj G.op (op U') ⋙ P) (forget AddCommGrpCat.{w})]
    (x : (G.op.leftKanExtension P).obj (op U')) :
    ∃ (V : C) (a : U' ⟶ G.obj V) (y : P.obj (op V)),
      (G.op.leftKanExtension P).map a.op ((G.op.leftKanExtensionUnit P).app (op V) y) = x := by
  let e := G.op.leftKanExtensionObjIsoColimit P (op U')
  obtain ⟨j, y, hy⟩ := Concrete.colimit_exists_rep _ (e.hom x)
  refine ⟨unop j.left, j.hom.unop, y, ?_⟩
  rw [← e.hom_inv_id_apply x, ← hy]
  change _ = (colimit.ι _ j ≫ e.inv) y
  rw [G.op.ι_leftKanExtensionObjIsoColimit_inv P (op U') j]
  rfl

/-- **The left Kan extension of a locally torsion presheaf is locally torsion.** Let `G : C ⥤ D`
carry covering sieves to covering sieves, and suppose that the forgetful functor of abelian groups
preserves the colimits over `CostructuredArrow G.op U` computing the left Kan extension along
`G.op` pointwise — as it does when these comma categories are filtered. If `P` is locally torsion,
so is `G.op.lan.obj P`: a section over `U'` is the image of a section `y` of `P` over some `V`
along an arrow `a : U' ⟶ G V`; the torsion sieve of `y` covers `V`, its image under `G` covers
`G V`, and on each member of its pullback along `a` the section is the image of a restriction of
`y`, which is annihilated by a positive integer. -/
public theorem isLocallyTorsion_lan_obj
    [∀ F : Cᵒᵖ ⥤ AddCommGrpCat.{w}, G.op.HasLeftKanExtension F]
    (hG : CoverPreserving J K G)
    (P : Cᵒᵖ ⥤ AddCommGrpCat.{w}) [G.op.HasPointwiseLeftKanExtension P]
    [∀ U : Dᵒᵖ, PreservesColimit (CostructuredArrow.proj G.op U ⋙ P) (forget AddCommGrpCat.{w})]
    (hP : IsLocallyTorsion J P) : IsLocallyTorsion K (G.op.lan.obj P) := by
  change IsLocallyTorsion K (G.op.leftKanExtension P)
  rw [isLocallyTorsion_iff_torsionSieve_mem] at hP ⊢
  intro U' x
  obtain ⟨V, a, y, rfl⟩ := exists_leftKanExtension_obj_eq_map_unit G P U' x
  refine K.superset_covering ?_ (K.pullback_stable a (hG.cover_preserve (hP V y)))
  rintro W g ⟨Z, h, k, ⟨n, hn, hkill⟩, hgk⟩
  refine ⟨n, hn, ?_⟩
  let Q := G.op.leftKanExtension P
  let η := G.op.leftKanExtensionUnit P
  have hres : Q.map g.op (Q.map a.op (η.app (op V) y)) =
      Q.map k.op (η.app (op Z) (P.map h.op y)) := by
    rw [← CategoryTheory.comp_apply, ← Q.map_comp, ← op_comp, hgk, op_comp, Q.map_comp,
      CategoryTheory.comp_apply]
    congr 1
    exact (NatTrans.naturality_apply η h.op y).symm
  rw [hres, ← _root_.map_nsmul, ← _root_.map_nsmul, hkill, map_zero, map_zero]

end LanLocallyTorsion

end Stacks.Torsion

namespace Stacks.EtaleCohomology

open Stacks.Torsion

universe u v

attribute [local instance] HasDerivedCategory.standard

/-- **Étale inverse image preserves torsion abelian sheaves.** For a morphism of schemes
`f : Y ⟶ X` and a torsion abelian sheaf `F` on `X_étale`, the inverse image `f⁻¹F` is a torsion
abelian sheaf on `Y_étale`. The inverse image is the sheafification of the left Kan extension along
the opposite of base change; base change is continuous, hence cover preserving, and
representably flat, so the colimits computing the Kan extension are filtered and the extension is
locally torsion by `Stacks.Torsion.isLocallyTorsion_lan_obj`. -/
@[sga "4 IX 1.2" "(iv)"]
public theorem torsionSheafProperty_etaleAbelianInverseImage {X Y : Scheme.{u}} (f : Y ⟶ X)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F) :
    Stacks.Torsion.torsionSheafProperty Y.smallEtaleTopology
      ((etaleAbelianInverseImage.{u, v} f).obj F) := by
  let G := smallEtaleBaseChange f
  have : ∀ U : Y.Etaleᵒᵖ, PreservesColimit (CostructuredArrow.proj G.op U ⋙ F.obj)
      (forget AddCommGrpCat.{max (u + 1) v}) := by
    intro U
    have : IsFiltered (CostructuredArrow G.op U) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence G U.unop)
    have : PreservesFilteredColimitsOfSize.{u, u + 1}
        (forget AddCommGrpCat.{max (u + 1) v}) :=
      preservesFilteredColimitsOfSize_of_univLE.{max (u + 1) v, max (u + 1) v, u, u + 1} _
    have : PreservesColimitsOfShape (CostructuredArrow G.op U)
        (forget AddCommGrpCat.{max (u + 1) v}) :=
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits _
    infer_instance
  exact torsionSheafProperty_sheafify.{max (u + 1) v} Y.smallEtaleTopology _
    (isLocallyTorsion_lan_obj.{max (u + 1) v} X.smallEtaleTopology Y.smallEtaleTopology G
      (CoverPreserving.of_isContinuous _ _ _) F.obj hF)

/-- **Étale inverse image preserves torsion cohomology.** For a morphism of schemes `f : Y ⟶ X`
and an object `K` of the derived category of abelian sheaves on `X_étale` whose cohomology sheaves
are torsion, the cohomology sheaves of `f⁻¹K` are torsion. Inverse image is exact, so
`Hⁱ(f⁻¹K) ≅ f⁻¹Hⁱ(K)`, which is torsion by
`Stacks.EtaleCohomology.torsionSheafProperty_etaleAbelianInverseImage`. -/
@[sga "4 IX 1.2" "(iv)"]
public theorem torsionCohomologyProperty_etaleAbelianDerivedInverseImage {X Y : Scheme.{u}}
    (f : Y ⟶ X)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
    (hK : Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) v} X.smallEtaleTopology K) :
    Stacks.Torsion.torsionCohomologyProperty.{max (u + 1) v} Y.smallEtaleTopology
      ((etaleAbelianDerivedInverseImage.{u, v} f).obj K) := by
  intro i
  exact torsionSheafProperty_of_iso Y.smallEtaleTopology
    (((etaleAbelianInverseImage.{u, v} f).mapDerivedCategoryHomologyIso i).app K).symm
    (torsionSheafProperty_etaleAbelianInverseImage f _ (hK i))

end Stacks.EtaleCohomology
