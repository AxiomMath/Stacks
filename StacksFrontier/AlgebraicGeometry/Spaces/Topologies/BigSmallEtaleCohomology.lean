module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.AbelianSheaves
public import StacksFrontier.AlgebraicGeometry.ProEtale.BigSmall.Cohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigToSmallEtalePullback
public import StacksFrontier.CategoryTheory.Sites.GrothendieckAbelianSheaves
public import StacksFrontier.Homology.Injectives.KInjective.RightDerivedCriterion

/-!
# Étale cohomology on the big and small étale sites of algebraic spaces (Stacks 0DGB)

Let `T` be a big étale site of algebraic spaces over a scheme `S` and `f : Y ⟶ X` a morphism of
its objects. Étale cohomology over `Y` of a complex of abelian sheaves on the big étale site of
`X` is the cohomology, on the spaces-étale site of `Y`, of the restriction of that complex along
`i_f`. This module proves that comparison and its two consequences for complexes pulled back
from the spaces-étale site of `X`. Each comparison is a natural isomorphism of unbounded derived
section functors, together with its image under degree-`n` homology.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.bigEtaleSections` is the sections functor at the object
  `f : Y ⟶ X` of the big étale site of `X`.
* `AlgebraicGeometry.BigEtaleSpaceSite.bigSmallEtaleSectionsIso` identifies it with global
  sections on the spaces-étale site of `Y` after restriction along `i_f`.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.bigSmallEtaleCohomologyIso` and
  `AlgebraicGeometry.BigEtaleSpaceSite.bigSmallEtaleCohomologyIsoAt`: étale cohomology over `Y`
  of a complex on the big étale site of `X` is the spaces-étale cohomology of `Y` of its
  restriction along `i_f`.
* `AlgebraicGeometry.BigEtaleSpaceSite.pulledSmallEtaleCohomologyIso` and
  `AlgebraicGeometry.BigEtaleSpaceSite.pulledSmallEtaleCohomologyIsoAt`: étale cohomology over
  `Y` of a complex pulled back from the spaces-étale site of `X` is the spaces-étale cohomology
  of `Y` of its pullback along `f_small`.
* `AlgebraicGeometry.BigEtaleSpaceSite.overXSmallEtaleCohomologyIso` and
  `AlgebraicGeometry.BigEtaleSpaceSite.overXSmallEtaleCohomologyIsoAt`: étale cohomology over
  `X` of a complex pulled back from the spaces-étale site of `X` is its spaces-étale
  cohomology.

## References

* [Stacks Project, Tag 0DGB](https://stacks.math.columbia.edu/tag/0DGB)
-/

public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard

@[expose] section

variable {X Y : T.Spaces} (f : Y ⟶ X)

/-- Sections of an abelian sheaf on the big étale site of `X` over the object `f : Y ⟶ X`. -/
public abbrev bigEtaleSections :
    Sheaf (T.bigEtaleTopology X) Ab.{u + 1} ⥤ Ab.{u + 1} :=
  (sheafSections (T.bigEtaleTopology X) Ab.{u + 1}).obj (op (Over.mk f))

local instance bigEtaleSections_additive : (bigEtaleSections T f).Additive := ⟨rfl⟩

local instance smallEtaleGlobalSections_additive :
    (Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}).Additive :=
  Functor.additive_of_preserves_binary_products _

end

attribute [local instance] bigEtaleSections_additive smallEtaleGlobalSections_additive

/-- The abelian inverse image along `π_X` is additive. -/
local instance bigToSmallAbelianInverseImage_additive (X : T.Spaces) :
    (CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T X)).Additive :=
  Functor.additive_of_preserves_binary_products _

variable {X Y : T.Spaces} (f : Y ⟶ X)

/-- Abelian sheaves on the big étale site of `X` form a Grothendieck abelian category, the site
being essentially small. -/
theorem bigEtaleSheaf_isGrothendieckAbelian (X : T.Spaces) :
    IsGrothendieckAbelian.{u + 1} (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall_of_hasSheafify.{u + 1, u + 1, u + 1, u + 2,
    u + 1} (T.bigEtaleTopology X) Ab.{u + 1}

/-- Abelian sheaves on the spaces-étale site of `X` form a Grothendieck abelian category, the
site being essentially small. -/
theorem spacesEtaleSheaf_isGrothendieckAbelian (X : T.Spaces) :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}) :=
  Sheaf.isGrothendieckAbelian_of_essentiallySmall_of_hasSheafify.{u + 1, u + 1, u + 1, u + 2,
    u + 1} (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}

/-- Sections over the object `f : Y ⟶ X` of the big étale site of `X` have a total right
derived functor on the unbounded derived categories. -/
instance bigEtaleSections_hasRightDerivedFunctor :
    ((bigEtaleSections T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) (ComplexShape.up ℤ)) :=
  Stacks.DerivedCategory.hasRightDerivedFunctor (bigEtaleSheaf_isGrothendieckAbelian T X) _

/-- Global sections on the spaces-étale site of `Y` have a total right derived functor on the
unbounded derived categories. -/
instance smallEtaleGlobalSections_hasRightDerivedFunctor (Y : T.Spaces) :
    ((Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).HasRightDerivedFunctor
        (HomotopyCategory.quasiIso
          (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
          (ComplexShape.up ℤ)) :=
  Stacks.DerivedCategory.hasRightDerivedFunctor (spacesEtaleSheaf_isGrothendieckAbelian T Y) _

/-- Sections over the object `f : Y ⟶ X` of the big étale site of `X` are global sections on
the spaces-étale site of `Y` of the restriction along `i_f`, naturally in the sheaf. -/
noncomputable def bigSmallEtaleSectionsIso :
    bigEtaleSections T f ≅
      smallEtaleRestriction T f ⋙
        Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1} := by
  let J := Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y
  let R := smallEtaleRestriction T f
  let U := Space.SpacesEtale.final T.fppfSite S T.fppf_mem Y
  have hU : IsTerminal U := Space.SpacesEtale.final_isTerminal T.fppfSite S T.fppf_mem Y
  have hobj : (inclusionFunctor T f).obj U = Over.mk f := by
    change Over.mk (𝟙 Y ≫ f) = Over.mk f
    simp
  let γ := Sheaf.ΓNatIsoSheafSections J Ab.{u + 1} hU
  let eG (G : Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) :
      G.obj.obj (op (Over.mk f)) ≅ (R.obj G).obj.obj (op U) :=
    (eqToIso (congrArg (fun Z : Over X => G.obj.obj (op Z)) hobj)).symm
  have eG_hom (G : Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) :
      (eG G).hom = G.obj.map (eqToHom hobj).op := by
    dsimp [eG]
    rw [eqToHom_op, eqToHom_map]
  refine NatIso.ofComponents (fun G => eG G ≪≫ (γ.app (R.obj G)).symm) ?_
  intro G G' φ
  have hEval : φ.hom.app (op (Over.mk f)) ≫ (eG G').hom =
      (eG G).hom ≫ (R.map φ).hom.app (op U) := by
    have hR : (R.map φ).hom.app (op U) =
        φ.hom.app (op ((inclusionFunctor T f).obj U)) := rfl
    rw [eG_hom G', eG_hom G, hR]
    exact (φ.hom.naturality (eqToHom hobj).op).symm
  change φ.hom.app (op (Over.mk f)) ≫ ((eG G').hom ≫ γ.symm.hom.app (R.obj G')) =
    ((eG G).hom ≫ γ.symm.hom.app (R.obj G)) ≫ (Sheaf.Γ J Ab.{u + 1}).map (R.map φ)
  calc
    _ = (eG G).hom ≫ ((R.map φ).hom.app (op U) ≫ γ.symm.hom.app (R.obj G')) := by
          rw [← Category.assoc, hEval, ← Category.assoc]
    _ = (eG G).hom ≫ (γ.symm.hom.app (R.obj G) ≫ (Sheaf.Γ J Ab.{u + 1}).map (R.map φ)) := by
          rw [← Category.assoc]
          change (eG G).hom ≫
            ((sheafSections J Ab.{u + 1}).obj (op U)).map (R.map φ) ≫
              γ.symm.hom.app (R.obj G') = _
          exact congrArg ((eG G).hom ≫ ·) (γ.symm.hom.naturality (R.map φ))
    _ = _ := by rw [Category.assoc]

/-! ### Part (5): cohomology over `Y` of a complex on the big étale site of `X` -/

/-- Étale cohomology over `Y` of a complex of abelian sheaves on the big étale site of `X` is
the cohomology on the spaces-étale site of `Y` of its restriction along `i_f`: the right-derived
sections functor at `f : Y ⟶ X` is restriction followed by derived global sections, naturally in
the derived coefficient object. -/
@[stacks 0DGB "part (5), big-site cohomology over Y of a big complex"]
noncomputable def bigSmallEtaleCohomologyIso :
    (((bigEtaleSections T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) (ComplexShape.up ℤ))) ≅
    ((smallEtaleRestriction T f).mapDerivedCategory ⋙
      (((Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
            (ComplexShape.up ℤ)))) := by
  let Cb := Sheaf (T.bigEtaleTopology X) Ab.{u + 1}
  let Cs := Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}
  have _ : IsGrothendieckAbelian.{u + 1} Cb := bigEtaleSheaf_isGrothendieckAbelian T X
  have _ : IsGrothendieckAbelian.{u + 1} Cs := spacesEtaleSheaf_isGrothendieckAbelian T Y
  let c := ComplexShape.up ℤ
  let Qb := DerivedCategory.Qh (C := Cb)
  let Qs := DerivedCategory.Qh (C := Cs)
  let Qa := DerivedCategory.Qh (C := Ab.{u + 1})
  let Wb := HomotopyCategory.quasiIso Cb c
  let Ws := HomotopyCategory.quasiIso Cs c
  let F := bigEtaleSections T f
  let R := smallEtaleRestriction T f
  let G := Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1}
  let Fh := F.mapHomotopyCategory c ⋙ Qa
  let Rh := R.mapHomotopyCategory c
  let Gc := G.mapHomotopyCategory c
  let Gh := Gc ⋙ Qa
  let RF := Fh.totalRightDerived Qb Wb
  let αF := Fh.totalRightDerivedUnit Qb Wb
  let RG := Gh.totalRightDerived Qs Ws
  let αG := Gh.totalRightDerivedUnit Qs Ws
  let τ : Fh ≅ Rh ⋙ Gh :=
    Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso (bigSmallEtaleSectionsIso T f).symm c).symm Qa ≪≫
      Functor.associator Rh Gc Qa
  let α : Fh ⟶ Qb ⋙ (R.mapDerivedCategory ⋙ RG) :=
    τ.hom ≫ Functor.whiskerLeft Rh αG ≫ (Functor.associator Rh Qs RG).hom ≫
      Functor.whiskerRight R.mapDerivedCategoryFactorsh.inv RG ≫
      (Functor.associator Qb R.mapDerivedCategory RG).inv
  have hα : ∀ (I : CochainComplex Cb ℤ) [I.IsKInjective],
      IsIso (α.app ((HomotopyCategory.quotient Cb c).obj I)) := by
    intro I _
    have := isKInjective_smallEtaleRestriction T f I
    have : IsIso (αG.app (Rh.obj ((HomotopyCategory.quotient Cb c).obj I))) :=
      Stacks.Injectives.rightDerivedUnit_isIso_at_kInjective Gh RG αG
        ((R.mapHomologicalComplex c).obj I)
    dsimp [α]
    infer_instance
  have := Stacks.Injectives.rightDerived_of_kInjective_units Fh (R.mapDerivedCategory ⋙ RG) α hα
  exact Functor.rightDerivedNatIso RF (R.mapDerivedCategory ⋙ RG) αF α Wb (Iso.refl Fh)

/-- In every degree, étale cohomology over `Y` of a complex on the big étale site of `X` agrees
with the cohomology on the spaces-étale site of `Y` of its restriction along `i_f`. -/
@[stacks 0DGB "part (5), in each degree"]
noncomputable def bigSmallEtaleCohomologyIsoAt
    (M : DerivedCategory (Sheaf (T.bigEtaleTopology X) Ab.{u + 1})) (n : ℤ) :
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      ((((bigEtaleSections T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) (ComplexShape.up ℤ))).obj M) ≅
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      (((smallEtaleRestriction T f).mapDerivedCategory ⋙
        (((Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
          Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
              (ComplexShape.up ℤ)))).obj M) :=
  (DerivedCategory.homologyFunctor Ab.{u + 1} n).mapIso ((bigSmallEtaleCohomologyIso T f).app M)

/-! ### Part (3): cohomology over `Y` of a complex pulled back from the small site -/

section Pulled

local instance smallEtaleAbelianInverseImage_additive :
    (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T f)).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The abelian inverse image along `π_X` followed by restriction along `i_f` is the abelian
inverse image along `f_small`. -/
noncomputable def pulledAbelianInverseImageIso :
    CategoryTheory.Sites.abelianInverseImage (bigToSmallEtaleMorphism T X) ⋙
        smallEtaleRestriction T f ≅
      CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T f) := by
  have _ : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  refine ProEtale.liftSheafNatIso
    (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) _ _ ?_
  exact Functor.isoWhiskerLeft
    (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (forget Ab.{u + 1}))
    (bigToSmall_inverseImageFactorizationIso T f)

/-- Étale cohomology over `Y` of a complex pulled back from the spaces-étale site of `X` to the
big étale site of `X` is the cohomology on the spaces-étale site of `Y` of its pullback along
`f_small`. -/
@[stacks 0DGB "part (3), cohomology of a pullback from the small site"]
noncomputable def pulledSmallEtaleCohomologyIso :
    ((CategoryTheory.Sites.abelianInverseImage
      (bigToSmallEtaleMorphism T X)).mapDerivedCategory ⋙
      (((bigEtaleSections T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) (ComplexShape.up ℤ)))) ≅
    ((CategoryTheory.Sites.abelianInverseImage
      (smallEtaleMorphism T f)).mapDerivedCategory ⋙
      (((Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
            (ComplexShape.up ℤ)))) :=
  Functor.isoWhiskerLeft _ (bigSmallEtaleCohomologyIso T f) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ProEtale.derivedCompIso (pulledAbelianInverseImageIso T f)) _

/-- In every degree, étale cohomology over `Y` of a complex pulled back from the spaces-étale
site of `X` agrees with the cohomology on the spaces-étale site of `Y` of its pullback along
`f_small`. -/
@[stacks 0DGB "part (3), in each degree"]
noncomputable def pulledSmallEtaleCohomologyIsoAt
    (K : DerivedCategory
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1})) (n : ℤ) :
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      (((CategoryTheory.Sites.abelianInverseImage
        (bigToSmallEtaleMorphism T X)).mapDerivedCategory ⋙
        (((bigEtaleSections T f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) (ComplexShape.up ℤ)))).obj K) ≅
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      (((CategoryTheory.Sites.abelianInverseImage
        (smallEtaleMorphism T f)).mapDerivedCategory ⋙
        (((Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
          Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1})
              (ComplexShape.up ℤ)))).obj K) :=
  (DerivedCategory.homologyFunctor Ab.{u + 1} n).mapIso
    ((pulledSmallEtaleCohomologyIso T f).app K)

end Pulled

/-! ### Part (1): cohomology over `X` of a complex pulled back from the small site -/

section OverX

variable (X : T.Spaces)

local instance smallEtaleAbelianInverseImageId_additive :
    (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T (𝟙 X))).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Base change of the spaces-étale site of `X` along the identity of `X` is the identity
functor. -/
noncomputable def spacesBaseChangeIdIso :
    (Space.spacesBaseChange T.fppfSite S T.fppf_mem (𝟙 X)).functor ≅
      𝟭 (Space.SpacesEtale T.fppfSite S T.fppf_mem X) := by
  let b := Space.spacesBaseChange T.fppfSite S T.fppf_mem (𝟙 X)
  refine NatIso.ofComponents (fun V => ?_) (fun {V W} g => ?_)
  · have hpb := b.isPullback V
    have hproj : IsIso (b.projection.app V) := hpb.isIso_fst_of_isIso
    exact (Space.IsEtaleOver T.fppfSite S T.fppf_mem X).isoMk
      (Over.isoMk (asIso (b.projection.app V)) (by simpa using hpb.w))
  · exact (Space.IsEtaleOver T.fppfSite S T.fppf_mem X).ι.map_injective
      (Over.OverMorphism.ext (b.projection.naturality g))

/-- The inverse image of the small étale morphism along the identity of `X` is the identity
functor on sheaves of sets. -/
noncomputable def smallEtaleMorphismIdInverseImageIso :
    (smallEtaleMorphism T (𝟙 X)).inverseImage ≅
      𝟭 (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (Type (u + 1))) :=
  (((smallEtaleMorphism T (𝟙 X)).adj.ofNatIsoRight
    (Functor.sheafPushforwardContinuousId' (spacesBaseChangeIdIso T X) (Type (u + 1))
      (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X))).leftAdjointUniq
        Adjunction.id)

/-- The abelian inverse image of the small étale morphism along the identity of `X` is the
identity functor on abelian sheaves. -/
noncomputable def abelianInverseImageIdIso :
    CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T (𝟙 X)) ≅
      𝟭 (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}) :=
  letI := (smallEtaleMorphism T (𝟙 X)).preservesFiniteLimits
  ProEtale.mapAbelianSheafIso (smallEtaleMorphismIdInverseImageIso T X) ≪≫
    ProEtale.mapAbelianSheafIdIso

/-- The abelian inverse image of the small étale morphism along the identity of `X` acts as the
identity on the unbounded derived category. -/
noncomputable def abelianInverseImageIdMapDerivedCategoryIso :
    (CategoryTheory.Sites.abelianInverseImage
        (smallEtaleMorphism T (𝟙 X))).mapDerivedCategory ≅
      𝟭 (DerivedCategory
        (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1})) :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ ProEtale.derivedIdIso.symm ≪≫
    ProEtale.derivedCompIso (Functor.rightUnitor _ ≪≫ abelianInverseImageIdIso T X) ≪≫
    ProEtale.derivedIdIso

/-- Étale cohomology over `X` of a complex pulled back from the spaces-étale site of `X` to the
big étale site of `X` is its cohomology on the spaces-étale site of `X`. -/
@[stacks 0DGB "part (1), cohomology over X of a pullback"]
noncomputable def overXSmallEtaleCohomologyIso :
    ((CategoryTheory.Sites.abelianInverseImage
      (bigToSmallEtaleMorphism T X)).mapDerivedCategory ⋙
      (((bigEtaleSections T (𝟙 X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) (ComplexShape.up ℤ)))) ≅
    (((Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
      Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
        (HomotopyCategory.quasiIso
          (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1})
          (ComplexShape.up ℤ))) :=
  pulledSmallEtaleCohomologyIso T (𝟙 X) ≪≫
    Functor.isoWhiskerRight (abelianInverseImageIdMapDerivedCategoryIso T X) _ ≪≫
    Functor.leftUnitor _

/-- In every degree, étale cohomology over `X` of a complex pulled back from the spaces-étale
site of `X` agrees with its small-site cohomology. -/
@[stacks 0DGB "part (1), in each degree"]
noncomputable def overXSmallEtaleCohomologyIsoAt
    (K : DerivedCategory
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1})) (n : ℤ) :
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      (((CategoryTheory.Sites.abelianInverseImage
        (bigToSmallEtaleMorphism T X)).mapDerivedCategory ⋙
        (((bigEtaleSections T (𝟙 X)).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
            (HomotopyCategory.quasiIso
              (Sheaf (T.bigEtaleTopology X) Ab.{u + 1}) (ComplexShape.up ℤ)))).obj K) ≅
    (DerivedCategory.homologyFunctor Ab.{u + 1} n).obj
      ((((Sheaf.Γ (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
        Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh
          (HomotopyCategory.quasiIso
            (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1})
            (ComplexShape.up ℤ))).obj K) :=
  (DerivedCategory.homologyFunctor Ab.{u + 1} n).mapIso
    ((overXSmallEtaleCohomologyIso T X).app K)

end OverX

end AlgebraicGeometry.BigEtaleSpaceSite

end
