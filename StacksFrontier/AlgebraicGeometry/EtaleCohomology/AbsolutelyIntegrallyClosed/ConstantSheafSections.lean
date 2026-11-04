module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleRingedSite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheafAbelian
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSections

/-!
# Sections of a constant abelian sheaf on the one-universe small étale site

Let `Y` be a scheme and `M` an abelian group in the successor of the scheme universe. The
sections of the constant abelian sheaf with value `M` on
`Stacks.EtaleCohomology.MayerVietoris.topology Y`, the one-universe model of the small étale
site of `Y`, over an object coming from the size-bounded small étale site of Stacks 021B, are
the locally constant `M`-valued maps on the underlying scheme of that object.

## Main definitions

* `Stacks.EtaleCohomology.ConstantSections.boundedIsoLocallyConstant` — the identification, as a
  natural isomorphism of presheaves on the size-bounded small étale site.
* `Stacks.EtaleCohomology.ConstantSections.opensIsoLocallyConstant` — its component at an open
  subscheme, read as an isomorphism with the locally constant maps on that open subscheme.

## Main results

* `Stacks.EtaleCohomology.ConstantSections.opensIsoLocallyConstant_naturality` — the component
  isomorphisms are compatible with restriction along an inclusion of open subschemes.

## References

* [Stacks Project, Tag 03P5](https://stacks.math.columbia.edu/tag/03P5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.EtaleCohomology.ConstantTransport

universe u

namespace Stacks.EtaleCohomology.ConstantSections

variable (B : BigEtaleSite.{u}) (Y : Scheme.{u}) (hY : B.Contains Y) (M : AddCommGrpCat.{u + 1})

/-- The constant abelian presheaf on the size-bounded small étale site of `Y` is the restriction
of the constant abelian sheaf on the one-universe model of the small étale site of `Y`. -/
def boundedIsoRestriction :
    ((constantSheaf (SmallEtale.topology B Y hY) AddCommGrpCat.{u + 1}).obj M).val ≅
      (SmallEtale.toEtaleSite B Y hY ⋙ AsSmall.up).op ⋙
        ((constantSheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1}).obj M).val :=
  (sheafToPresheaf (SmallEtale.topology B Y hY) AddCommGrpCat.{u + 1}).mapIso
      ((equivCommuteConstant' (SmallEtale.topology B Y hY) AddCommGrpCat.{u + 1}
        Y.smallEtaleTopology (SmallEtale.toEtaleSite B Y hY)
        (SmallEtale.finalIsTerminal B Y hY)
        (have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
          ⟨fun _ => inferInstance⟩
        MorphismProperty.Over.mkIdTerminal _ _)).app M) ≪≫
    Functor.isoWhiskerLeft (SmallEtale.toEtaleSite B Y hY).op
      ((sheafToPresheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}).mapIso
        ((equivCommuteConstant' Y.smallEtaleTopology AddCommGrpCat.{u + 1}
          (MayerVietoris.topology Y) (AsSmall.up : Y.Etale ⥤ MayerVietoris.Site Y)
          (show IsTerminal ((AsSmall.down : MayerVietoris.Site Y ⥤ Y.Etale).obj
              (MayerVietoris.self Y)) from
            have : MorphismProperty.ContainsIdentities (@Etale : MorphismProperty Scheme.{u}) :=
              ⟨fun _ => inferInstance⟩
            MorphismProperty.Over.mkIdTerminal _ _) (MayerVietoris.selfIsTerminal Y)).app M))

/-- **The sections of a constant abelian sheaf on the one-universe model of the small étale site
are the locally constant maps**, over the objects coming from the size-bounded small étale site
of Stacks 021B. -/
def boundedIsoLocallyConstant :
    (SmallEtale.toScheme B Y hY).op ⋙ locallyConstantMapsAb.{u, u + 1} (ToType M) ≅
      (SmallEtale.toEtaleSite B Y hY ⋙ AsSmall.up).op ⋙
        ((constantSheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1}).obj M).val :=
  (constantSheafIsoLocallyConstantMapsAb_smallEtale_presheaf.{u, u + 1} B Y hY
    (ToType M)).symm ≪≫ boundedIsoRestriction B Y hY M

/-! ### Open subschemes -/

section Opens

/-- **The sections of a constant abelian sheaf over an open subscheme are the locally constant
maps on it**, on the one-universe model of the small étale site. -/
def opensIsoLocallyConstant (U : Y.Opens) :
    AddCommGrpCat.of (LocallyConstant (U : Set Y) (ToType M)) ≅
      ((constantSheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1}).obj M).val.obj
        (op ((MayerVietoris.opensToSite Y).obj U)) :=
  (boundedIsoLocallyConstant B Y hY M).app
    (op ((SmallEtale.opensToSmallEtale B Y hY).obj U))

/-- **The identifications of sections with locally constant maps are compatible with
restriction**: restricting the section attached to a locally constant map on `V` along an
inclusion `U ≤ V` gives the section attached to the composite of that map with the inclusion of
`U` into `V`. -/
theorem opensIsoLocallyConstant_naturality {U V : Y.Opens} (hUV : U ≤ V)
    (z : LocallyConstant (V : Set Y) (ToType M)) :
    ((constantSheaf (MayerVietoris.topology Y) AddCommGrpCat.{u + 1}).obj M).val.map
        ((MayerVietoris.opensToSite Y).map (homOfLE hUV)).op
        ((opensIsoLocallyConstant B Y hY M V).hom z) =
      (opensIsoLocallyConstant B Y hY M U).hom
        (LocallyConstant.comap ⟨fun p ↦ ⟨p.val, hUV p.property⟩,
          Continuous.subtype_mk continuous_subtype_val _⟩ z) := by
  have h := (boundedIsoLocallyConstant B Y hY M).hom.naturality_apply
    (Quiver.Hom.op ((SmallEtale.opensToSmallEtale B Y hY).map (homOfLE hUV))) z
  refine Eq.trans h.symm ?_
  congr 1
  exact LocallyConstant.ext fun p ↦ congrArg z (Scheme.homOfLE_apply' hUV p.val p.property)

end Opens

end Stacks.EtaleCohomology.ConstantSections

end
