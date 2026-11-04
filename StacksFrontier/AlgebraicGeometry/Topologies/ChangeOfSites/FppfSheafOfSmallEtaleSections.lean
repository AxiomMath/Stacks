module

public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.FppfSheafConditionSmallEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackSections

/-!
# The rule `X ↦ Γ(X, f_small⁻¹F)` as an fppf sheaf

Let `B` be a chosen big fppf site, let `S` be one of its schemes and let `F` be a sheaf of sets
on the small étale site of `S`. The rule sending a scheme `f : X ⟶ S` over `S` to the global
sections `Γ(X, f_small⁻¹F)` of the small étale pullback of `F` along `f`, with restriction along
a morphism `g : Y ⟶ X` over `S` the canonical map of global sections of small étale pullbacks,
is a presheaf on the big site over `S`. This file proves Stacks 0DDL for this rule: it is a
sheaf for the big fppf topology over `S`, a fortiori for the big étale topology over `S`, and as
a sheaf it is isomorphic to `π_S⁻¹F` on the big étale site and to `ε_S⁻¹π_S⁻¹F` on the big fppf
site.

## Main definitions

* `AlgebraicGeometry.smallEtalePullbackSectionsPresheaf` — the rule
  `(f : X ⟶ S) ↦ Γ(X, f_small⁻¹F)`, as a presheaf on the big site over `S`.
* `AlgebraicGeometry.smallEtalePullbackSectionsPresheafIso` — the rule is isomorphic, as a
  presheaf, to the presheaf underlying `π_S⁻¹F`.
* `AlgebraicGeometry.smallEtalePullbackSectionsEtaleSheaf`,
  `AlgebraicGeometry.smallEtalePullbackSectionsFppfSheaf` — the rule as an étale sheaf and as an
  fppf sheaf.

## Main results

* `AlgebraicGeometry.smallEtalePullbackSections_isSheaf` — **Stacks 0DDL, the sheaf
  condition**: the rule is a sheaf for the big fppf and for the big étale topology over `S`.
* `AlgebraicGeometry.smallEtalePullbackSectionsSheafIso` — **Stacks 0DDL, the
  identification**: the rule is `π_S⁻¹F` on the big étale site and `ε_S⁻¹π_S⁻¹F` on the big
  fppf site.

## Implementation notes

The functoriality of the rule is not proved by hand: by the sections formula of Stacks 09XN,
`AlgebraicGeometry.etaleInverseImageSectionsComparison`, each restriction map of the rule is the
conjugate of a restriction map of `π_S⁻¹F` by the comparison isomorphisms, so the functor laws of
the rule are those of `π_S⁻¹F`. The same comparison isomorphisms then form an isomorphism of
presheaves, which transports the sheaf conditions of
`AlgebraicGeometry.smallEtaleInverseImage_isSheaf_fppf` and of `π_S⁻¹F` itself. On the fppf side
the identification is completed by the unit isomorphism
`AlgebraicGeometry.isIso_fppfToBigEtale_unit_app`, as `ε_{S,*}` is restriction along the identity.

## References

* [Stacks Project, Tag 09XN](https://stacks.math.columbia.edu/tag/09XN)
* [Stacks Project, Tag 0DDL](https://stacks.math.columbia.edu/tag/0DDL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (S : B.Schemes)
  (F : Sheaf (SmallEtale.topology (associatedBigEtaleSite B) S.1 S.property) (Type (u + 1)))

/-- The restriction maps of the rule `X ↦ Γ(X, f_small⁻¹F)` are the restriction maps of
`π_S⁻¹F` conjugated by the sections formula of Stacks 09XN. -/
public theorem etalePullbackSectionsRestriction_eq (B : BigEtaleSite.{u}) (S : B.Scheme)
    {X Y : BigEtaleOver B S.obj S.property} (g : Y ⟶ X)
    (F : Sheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))) :
    etalePullbackSectionsRestriction B S g F =
      (etaleInverseImageSectionsIso B S X).inv.app F ≫
        ((bigEtaleToSmallEtaleMorphism B S.obj S.property).inverseImage.obj F).obj.map g.op ≫
          (etaleInverseImageSectionsIso B S Y).hom.app F := by
  rw [← etaleInverseImageSectionsIso_naturality, ← Category.assoc, ← NatTrans.comp_app,
    Iso.inv_hom_id, NatTrans.id_app, Category.id_comp]

/-- **The rule of Stacks 0DDL.** The presheaf on the big site over `S` sending a scheme
`f : X ⟶ S` over `S` to the global sections `Γ(X, f_small⁻¹F)` of the small étale pullback of
`F` along `f`, with restriction along `g : Y ⟶ X` over `S` the canonical map of global sections
`AlgebraicGeometry.etalePullbackSectionsRestriction`. -/
public def smallEtalePullbackSectionsPresheaf :
    (BigEtaleOver (associatedBigEtaleSite B) S.1 S.property)ᵒᵖ ⥤ Type (u + 1) where
  obj X :=
    (Sheaf.Γ (SmallEtale.topology (associatedBigEtaleSite B) X.unop.left.obj
      X.unop.left.property) (Type (u + 1))).obj
      (((smallEtaleBaseChange (associatedBigEtaleSite B) X.unop.hom).sheafPullback (Type (u + 1))
        (SmallEtale.topology (associatedBigEtaleSite B) S.1 S.property)
        (SmallEtale.topology (associatedBigEtaleSite B) X.unop.left.obj
          X.unop.left.property)).obj F)
  map g := etalePullbackSectionsRestriction (associatedBigEtaleSite B) S g.unop F
  map_id X := by
    rw [etalePullbackSectionsRestriction_eq]
    rw [unop_id, op_id, CategoryTheory.Functor.map_id]
    exact Iso.inv_hom_id_app (etaleInverseImageSectionsIso (associatedBigEtaleSite B) S X.unop) F
  map_comp f g := by
    rw [etalePullbackSectionsRestriction_eq, etalePullbackSectionsRestriction_eq,
      etalePullbackSectionsRestriction_eq]
    simp only [unop_comp, op_comp, CategoryTheory.Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_app_assoc]

/-- By the sections formula of Stacks 09XN, the rule `X ↦ Γ(X, f_small⁻¹F)` is isomorphic, as a
presheaf on the big site over `S`, to the presheaf underlying `π_S⁻¹F`. -/
public def smallEtalePullbackSectionsPresheafIso :
    smallEtalePullbackSectionsPresheaf B S F ≅
      ((bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite B) S.1 S.property).inverseImage.obj
        F).obj :=
  NatIso.ofComponents
    (fun X => ((etaleInverseImageSectionsIso (associatedBigEtaleSite B) S X.unop).app F).symm)
    (fun {X Y} g => by
      change etalePullbackSectionsRestriction (associatedBigEtaleSite B) S g.unop F ≫ _ = _
      rw [etalePullbackSectionsRestriction_eq]
      simp only [Category.assoc, Iso.app_inv, Iso.symm_hom, Iso.hom_inv_id_app]
      rfl)

/-- **Stacks 0DDL, the sheaf condition.** The rule `(f : X ⟶ S) ↦ Γ(X, f_small⁻¹F)` is a sheaf
for the big fppf topology over `S`, and a fortiori for the big étale topology over `S`. -/
@[stacks 0DDL "the rule X ↦ Γ(X, f_small⁻¹F) is an fppf sheaf, a fortiori an étale sheaf"]
public theorem smallEtalePullbackSections_isSheaf :
    Presheaf.IsSheaf (B.topology.over S) (smallEtalePullbackSectionsPresheaf B S F) ∧
      Presheaf.IsSheaf (BigEtaleOver.topology (associatedBigEtaleSite B) S.1 S.property)
        (smallEtalePullbackSectionsPresheaf B S F) :=
  ⟨Presheaf.isSheaf_of_iso_iff (smallEtalePullbackSectionsPresheafIso B S F) |>.2
      (smallEtaleInverseImage_isSheaf_fppf B S F),
    Presheaf.isSheaf_of_iso_iff (smallEtalePullbackSectionsPresheafIso B S F) |>.2
      ((bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite B) S.1 S.property).inverseImage.obj
        F).property⟩

/-- The rule `X ↦ Γ(X, f_small⁻¹F)` as a sheaf on the big étale site over `S`. -/
public def smallEtalePullbackSectionsEtaleSheaf :
    Sheaf (BigEtaleOver.topology (associatedBigEtaleSite B) S.1 S.property) (Type (u + 1)) :=
  ⟨smallEtalePullbackSectionsPresheaf B S F, (smallEtalePullbackSections_isSheaf B S F).2⟩

/-- The rule `X ↦ Γ(X, f_small⁻¹F)` as a sheaf on the big fppf site over `S`. -/
public def smallEtalePullbackSectionsFppfSheaf :
    Sheaf (B.topology.over S) (Type (u + 1)) :=
  ⟨smallEtalePullbackSectionsPresheaf B S F, (smallEtalePullbackSections_isSheaf B S F).1⟩

/-- **Stacks 0DDL, the identification.** The sheaf `X ↦ Γ(X, f_small⁻¹F)` is `π_S⁻¹F` on the
big étale site over `S` and `ε_S⁻¹π_S⁻¹F` on the big fppf site over `S`. -/
@[stacks 0DDL "the rule is π_S⁻¹F on (Sch/S)_étale and ε_S⁻¹π_S⁻¹F on (Sch/S)_fppf"]
public def smallEtalePullbackSectionsSheafIso :
    (smallEtalePullbackSectionsEtaleSheaf B S F ≅
        (bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite B) S.1 S.property).inverseImage.obj
          F) ×
      (smallEtalePullbackSectionsFppfSheaf B S F ≅
        (fppfToBigEtaleMorphism B S).inverseImage.obj
          ((bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite B) S.1
            S.property).inverseImage.obj F)) :=
  haveI := isIso_fppfToBigEtale_unit_app B S F
  ⟨(fullyFaithfulSheafToPresheaf _ _).preimageIso (smallEtalePullbackSectionsPresheafIso B S F),
    (fullyFaithfulSheafToPresheaf _ _).preimageIso
      (smallEtalePullbackSectionsPresheafIso B S F ≪≫
        (sheafToPresheaf _ _).mapIso (asIso ((fppfToBigEtaleMorphism B S).adj.unit.app
          ((bigEtaleToSmallEtaleMorphism (associatedBigEtaleSite B) S.1
            S.property).inverseImage.obj F))))⟩

end AlgebraicGeometry

end
