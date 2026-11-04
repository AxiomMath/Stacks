module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.Topology.Sheaves.Modules.Exactness
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero
import StacksCore.Tactic.StacksAttribute

/-!
# The Mayer--Vietoris triangle of a cover by two opens

Let `X` be a ringed space which is the union of two open subspaces `U` and `V`. Stacks 08BU
is the distinguished triangle, functorial in the derived module `K`, which expresses `K` in
terms of the extensions by zero of its restrictions to `U`, to `V` and to `U ∩ V`:

`j_{U∩V,!} K|_{U∩V} ⟶ j_{U,!} K|_U ⊕ j_{V,!} K|_V ⟶ K ⟶ (shift)`.

## Main definitions

* `Stacks.ExtensionByZero.homotopyExtensionRestriction`: restriction followed by extension by
  zero, applied degreewise and then passed from the homotopy category to the derived
  category.
* `Stacks.ExtensionByZero.derivedExtensionRestrictionCounit`: the canonical map from the
  derived `j_! j^*` to the identity functor.

## Main results

* `Stacks.ExtensionByZero.distinguished_extensionRestriction_triangle`: the distinguished
  triangle attached to a cover of `X` by two open subspaces.

## Implementation notes

The three derived functors are specified as the derived functors of the degreewise composites
`j_! j^*`, and the maps to the identity functor are the derived adjunction counits of Stacks
08BT. The two maps out of the intersection term are pinned down by composing them with those
counits — they are the inclusion of the intersection and its negative — so the triangle's
canonical maps, its Mayer--Vietoris sign and its naturality in `K` are all retained rather
than merely asserted to exist.

Exactness of the sequences involved is checked on stalks, through Stacks 01AG
(`AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`), which is the only
place the cover hypothesis `U ⊔ V = ⊤` is used: a point of `X` lies in `U` or in `V`, and the
stalk of an extension by zero vanishes outside the open it is extended from.

## References

* [Stacks Project, Tag 08BU](https://stacks.math.columbia.edu/tag/08BU)
* [Stacks Project, Tag 08BT](https://stacks.math.columbia.edu/tag/08BT)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open scoped ZeroObject
open ExtensionByZeroModules

universe u

namespace Stacks.ExtensionByZero

attribute [local instance] HasDerivedCategory.standard

private lemma extensionRestriction_additive_and_exact {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    (jStar U O ⋙ jShriek U O).Additive ∧
      PreservesFiniteLimits (jStar U O ⋙ jShriek U O) ∧
      PreservesFiniteColimits (jStar U O ⋙ jShriek U O) := by
  obtain ⟨_, _, _⟩ := jStar_additive_and_exact O U
  obtain ⟨_, _, _⟩ := jShriek_additive_and_exact O U
  exact ⟨inferInstance, inferInstance, inferInstance⟩

private lemma extensionRestriction_isRightDerivedFunctor {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    haveI := (extensionRestriction_additive_and_exact O U).1
    haveI := (extensionRestriction_additive_and_exact O U).2.1
    haveI := (extensionRestriction_additive_and_exact O U).2.2
    ((jStar U O ⋙ jShriek U O).mapDerivedCategory).IsRightDerivedFunctor
      (jStar U O ⋙ jShriek U O).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _ _

/-- Extension by zero of sheaves of modules from an open subspace is additive. -/
local instance jShriek_additive {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    (jShriek U O).Additive :=
  (jShriekAdjunction U O).left_adjoint_additive

/-- Apply restriction to `U` and extension by zero back to `X` degreewise, then pass to
the derived category. -/
public abbrev homotopyExtensionRestriction {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} O) :=
  (jStar U O ⋙ jShriek U O).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh

/-- The canonical comparison from the functor on the homotopy category induced by the
identity functor to the identity functor. -/
public def homotopyIdentityComparison {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) :
    (𝟭 (SheafOfModules.{u} O)).mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      𝟭 (HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ)) where
  app K := 𝟙 K
  naturality := by
    rintro ⟨K⟩ ⟨L⟩ ⟨f⟩
    rfl

/-- The degreewise adjunction counit `j_!j^* ⟶ ᵀ` on the homotopy category, followed
by passage to the derived category. -/
public noncomputable def homotopyExtensionRestrictionCounit {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X) :
    homotopyExtensionRestriction O U ⟶ DerivedCategory.Qh :=
  Functor.whiskerRight
    (NatTrans.mapHomotopyCategory (jShriekAdjunction U O).counit (ComplexShape.up ℤ) ≫
      homotopyIdentityComparison O)
    DerivedCategory.Qh

/-- The canonical derived adjunction counit `R(j_!j^*) ⟶ ᵀ`. -/
public noncomputable def derivedExtensionRestrictionCounit {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    (DU : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aU : homotopyExtensionRestriction O U ⟶ DerivedCategory.Qh ⋙ DU)
    [DU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))] :
    DU ⟶ 𝟭 (DerivedCategory (SheafOfModules.{u} O)) :=
  DU.rightDerivedDesc aU
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))
    (𝟭 (DerivedCategory (SheafOfModules.{u} O)))
    (homotopyExtensionRestrictionCounit O U)

private lemma derivedExtensionRestrictionCounit_fac {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    (DU : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aU : homotopyExtensionRestriction O U ⟶ DerivedCategory.Qh ⋙ DU)
    [DU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))] :
    aU ≫ Functor.whiskerLeft DerivedCategory.Qh
        (derivedExtensionRestrictionCounit O U DU aU) =
      homotopyExtensionRestrictionCounit O U :=
  Functor.rightDerived_fac DU aU _ _ _

/-- The inclusion of the extension by zero from a smaller open into the one from a
larger open.  It is obtained from the counit for the larger open, which is invertible
on objects supported on the smaller open.

It is public, not private, because it is the filtration map out of which a system of complexes
supported stagewise on an increasing open cover is built; see
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.ComplexSystemFromGlobalComplex`. -/
noncomputable def extensionRestrictionInclusion {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (W U : Opens X) (hWU : W ≤ U) :
    (jStar W O ⋙ jShriek W O) ⟶ (jStar U O ⋙ jShriek U O) := by
  let GW := jStar W O ⋙ jShriek W O
  let GU := jStar U O ⋙ jShriek U O
  let e : (GW ⋙ GU) ≅ GW := NatIso.ofComponents
    (fun E => by
      letI : IsIso ((jShriekAdjunction U O).counit.app (GW.obj E)) :=
        counit_isIso_of_stalk_isZero U O (GW.obj E) (fun x hx =>
          isZero_stalk_jShriek W O ((jStar W O).obj E) x (fun hxW => hx (hWU hxW)))
      exact asIso ((jShriekAdjunction U O).counit.app (GW.obj E)))
    (by
      intro E E' f
      simp [Functor.comp_map])
  exact e.inv ≫ Functor.whiskerRight (jShriekAdjunction W O).counit GU ≫
    (Functor.leftUnitor GU).hom

/-- The restriction-inclusion map factors the extension-by-zero counit.  Together with the
invertibility of the counit on objects supported on the smaller open, this is what pins
`Stacks.ExtensionByZero.extensionRestrictionInclusion` down uniquely, hence makes it strictly
transitive. -/
lemma extensionRestrictionInclusion_fac {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (W U : Opens X) (hWU : W ≤ U) (E : SheafOfModules.{u} O) :
    (extensionRestrictionInclusion O W U hWU).app E ≫
        (jShriekAdjunction U O).counit.app E =
      (jShriekAdjunction W O).counit.app E := by
  let GW := jStar W O ⋙ jShriek W O
  have : IsIso ((jShriekAdjunction U O).counit.app (GW.obj E)) :=
    counit_isIso_of_stalk_isZero U O (GW.obj E) fun x hx =>
      isZero_stalk_jShriek W O ((jStar W O).obj E) x fun hxW => hx (hWU hxW)
  simp [extensionRestrictionInclusion, NatIso.ofComponents, Category.assoc]

/-- The nested-open inclusion after applying the homotopy-category and derived functors. -/
private noncomputable def homotopyExtensionRestrictionInclusion {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (W U : Opens X) (hWU : W ≤ U) :
    homotopyExtensionRestriction O W ⟶ homotopyExtensionRestriction O U :=
  Functor.whiskerRight
    (NatTrans.mapHomotopyCategory (extensionRestrictionInclusion O W U hWU)
      (ComplexShape.up ℤ)) DerivedCategory.Qh

/-- Descend a nested-open inclusion to arbitrary right-derived functors. -/
private noncomputable def derivedExtensionRestrictionInclusion {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (W U : Opens X) (hWU : W ≤ U)
    (DW DU : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aW : homotopyExtensionRestriction O W ⟶ DerivedCategory.Qh ⋙ DW)
    (aU : homotopyExtensionRestriction O U ⟶ DerivedCategory.Qh ⋙ DU)
    [DW.IsRightDerivedFunctor aW
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))] :
    DW ⟶ DU :=
  DW.rightDerivedDesc aW
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) DU
    (homotopyExtensionRestrictionInclusion O W U hWU ≫ aU)

/-- The derived inclusion is characterized by its defining comparison on the homotopy category. -/
private lemma derivedExtensionRestrictionInclusion_fac {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (W U : Opens X) (hWU : W ≤ U)
    (DW DU : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aW : homotopyExtensionRestriction O W ⟶ DerivedCategory.Qh ⋙ DW)
    (aU : homotopyExtensionRestriction O U ⟶ DerivedCategory.Qh ⋙ DU)
    [DW.IsRightDerivedFunctor aW
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))] :
    aW ≫ Functor.whiskerLeft DerivedCategory.Qh
        (derivedExtensionRestrictionInclusion O W U hWU DW DU aW aU) =
      homotopyExtensionRestrictionInclusion O W U hWU ≫ aU :=
  Functor.rightDerived_fac DW aW _ _ _

/-- The homotopy-category inclusion still factors the degreewise counit. -/
private lemma homotopyExtensionRestrictionInclusion_counit {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (W U : Opens X) (hWU : W ≤ U) :
    homotopyExtensionRestrictionInclusion O W U hWU ≫
        homotopyExtensionRestrictionCounit O U =
      homotopyExtensionRestrictionCounit O W := by
  show Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (extensionRestrictionInclusion O W U hWU)
        (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
    Functor.whiskerRight
      (NatTrans.mapHomotopyCategory (jShriekAdjunction U O).counit
        (ComplexShape.up ℤ) ≫ homotopyIdentityComparison O) DerivedCategory.Qh = _
  have hcomp : extensionRestrictionInclusion O W U hWU ≫
      (jShriekAdjunction U O).counit = (jShriekAdjunction W O).counit :=
    NatTrans.ext (funext fun E => extensionRestrictionInclusion_fac O W U hWU E)
  calc
    _ = Functor.whiskerRight
          (NatTrans.mapHomotopyCategory
            (extensionRestrictionInclusion O W U hWU ≫ (jShriekAdjunction U O).counit)
            (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
        Functor.whiskerRight (homotopyIdentityComparison O) DerivedCategory.Qh := by
          rw [Functor.whiskerRight_comp (α :=
            NatTrans.mapHomotopyCategory (jShriekAdjunction U O).counit
              (ComplexShape.up ℤ)) (β := homotopyIdentityComparison O) DerivedCategory.Qh]
          rw [← Category.assoc,
            ← Functor.whiskerRight_comp (α :=
              NatTrans.mapHomotopyCategory (extensionRestrictionInclusion O W U hWU)
                (ComplexShape.up ℤ)) (β :=
              NatTrans.mapHomotopyCategory (jShriekAdjunction U O).counit
                (ComplexShape.up ℤ)) DerivedCategory.Qh,
            ← NatTrans.mapHomotopyCategory_comp]
    _ = homotopyExtensionRestrictionCounit O W := by
      rw [hcomp]
      exact (Functor.whiskerRight_comp
        (NatTrans.mapHomotopyCategory (jShriekAdjunction W O).counit
          (ComplexShape.up ℤ)) (homotopyIdentityComparison O) DerivedCategory.Qh).symm

/-- The derived inclusion factors the canonical derived counit. -/
private lemma derivedExtensionRestrictionInclusion_counit {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (W U : Opens X) (hWU : W ≤ U)
    (DW DU : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aW : homotopyExtensionRestriction O W ⟶ DerivedCategory.Qh ⋙ DW)
    (aU : homotopyExtensionRestriction O U ⟶ DerivedCategory.Qh ⋙ DU)
    [DW.IsRightDerivedFunctor aW
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [DU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))] :
    derivedExtensionRestrictionInclusion O W U hWU DW DU aW aU ≫
    derivedExtensionRestrictionCounit O U DU aU =
      derivedExtensionRestrictionCounit O W DW aW := by
  apply DW.rightDerived_ext aW
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))
  calc
    aW ≫ Functor.whiskerLeft DerivedCategory.Qh
        (derivedExtensionRestrictionInclusion O W U hWU DW DU aW aU) ≫
          Functor.whiskerLeft DerivedCategory.Qh
            (derivedExtensionRestrictionCounit O U DU aU) =
      homotopyExtensionRestrictionInclusion O W U hWU ≫ aU ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (derivedExtensionRestrictionCounit O U DU aU) := by
            rw [← Category.assoc, derivedExtensionRestrictionInclusion_fac,
              Category.assoc]
    _ = homotopyExtensionRestrictionInclusion O W U hWU ≫
        homotopyExtensionRestrictionCounit O U := by
          rw [derivedExtensionRestrictionCounit_fac]
    _ = homotopyExtensionRestrictionCounit O W :=
      homotopyExtensionRestrictionInclusion_counit O W U hWU
    _ = aW ≫ Functor.whiskerLeft DerivedCategory.Qh
        (derivedExtensionRestrictionCounit O W DW aW) :=
      (derivedExtensionRestrictionCounit_fac O W DW aW).symm

/-- Negating the derived inclusion gives the Mayer--Vietoris sign. -/
private lemma derivedNegExtensionRestrictionInclusion_counit {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (W U : Opens X) (hWU : W ≤ U)
    (DW DU : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aW : homotopyExtensionRestriction O W ⟶ DerivedCategory.Qh ⋙ DW)
    (aU : homotopyExtensionRestriction O U ⟶ DerivedCategory.Qh ⋙ DU)
    [DW.IsRightDerivedFunctor aW
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [DU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))] :
    (-derivedExtensionRestrictionInclusion O W U hWU DW DU aW aU) ≫
      derivedExtensionRestrictionCounit O U DU aU =
      -derivedExtensionRestrictionCounit O W DW aW := by
  rw [CategoryTheory.Preadditive.neg_comp,
    derivedExtensionRestrictionInclusion_counit]

/-- The sheaf-level Mayer--Vietoris short complex for two opens. -/
private noncomputable def extensionRestrictionCoverShortComplex {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U V : Opens X) (E : SheafOfModules.{u} O) :
    ShortComplex (SheafOfModules.{u} O) where
  f := biprod.lift
    ((extensionRestrictionInclusion O (U ⊓ V) U inf_le_left).app E)
    (-((extensionRestrictionInclusion O (U ⊓ V) V inf_le_right).app E))
  g := biprod.desc ((jShriekAdjunction U O).counit.app E)
    ((jShriekAdjunction V O).counit.app E)
  zero := by
    simp only [biprod.lift_desc, CategoryTheory.Preadditive.neg_comp,
      extensionRestrictionInclusion_fac]
    abel

/-- At a point of an open, the extension-by-zero counit is an isomorphism on stalks. -/
private lemma isIso_stalk_extensionRestrictionCounit_of_mem {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    (E : SheafOfModules.{u} O) (x : X) (hx : x ∈ U) :
    IsIso ((AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor O x).map
      ((jShriekAdjunction U O).counit.app E)) := by
  let φ := (jShriekAdjunction U O).counit.app E
  have := isIso_jShriekAdjunction_unit U O
  have hR : IsIso ((jStar U O).map φ) :=
    isIso_of_hom_comp_eq_id _ ((jShriekAdjunction U O).right_triangle_components E)
  have hab : IsIso ((toAb (resRing U O)).map ((jStar U O).map φ)) :=
    Functor.map_isIso _ _
  have hwhisk : IsIso (Functor.whiskerLeft (TopCat.Presheaf.imF U).op
      ((toAb O).map φ)) := by
    rw [← toAb_jStar_map U O φ]
    exact hab
  have hw := Functor.map_isIso
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨x, hx⟩ : Usp U))
    (Functor.whiskerLeft (TopCat.Presheaf.imF U).op ((toAb O).map φ))
  have hpoint := (TopCat.Presheaf.isIso_stalkFunctor_map_whiskerLeft_iff U _ _
    ((toAb O).map φ) ⟨x, hx⟩).mp hw
  show IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((toAb O).map φ))
  simpa [toAb, Functor.comp_map] using hpoint

private lemma isZero_stalk_extensionRestriction_of_not_mem {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    (E : SheafOfModules.{u} O) (x : X) (hx : x ∉ U) :
    IsZero ((AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor O x).obj
      ((jStar U O ⋙ jShriek U O).obj E)) := by
  show IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
    ((toAb O).obj ((jShriek U O).obj ((jStar U O).obj E))))
  exact isZero_stalk_jShriek U O ((jStar U O).obj E) x hx

private lemma extensionRestrictionInclusion_stalk_isIso_of_mem {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (W U : Opens X) (hWU : W ≤ U) (E : SheafOfModules.{u} O) (x : X) (hx : x ∈ W) :
    IsIso ((AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor O x).map
      ((extensionRestrictionInclusion O W U hWU).app E)) := by
  let F := AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor O x
  let i := (extensionRestrictionInclusion O W U hWU).app E
  let cW := (jShriekAdjunction W O).counit.app E
  let cU := (jShriekAdjunction U O).counit.app E
  have hW : IsIso (F.map cW) := isIso_stalk_extensionRestrictionCounit_of_mem O W E x hx
  have hU : IsIso (F.map cU) :=
    isIso_stalk_extensionRestrictionCounit_of_mem O U E x (hWU hx)
  have hfac : i ≫ cU = cW := extensionRestrictionInclusion_fac O W U hWU E
  have hmap : F.map i ≫ F.map cU = F.map cW := by
    rw [← F.map_comp, hfac]
  exact (isIso_comp_right_iff (F.map i) (F.map cU)).mp (by
    rw [hmap]
    infer_instance)

private lemma isIso_biprod_fst_of_isZero {A B : AddCommGrpCat.{u}}
    [HasBinaryBiproduct A B] (hB : IsZero B) :
    IsIso (biprod.fst : A ⊞ B ⟶ A) := by
  apply IsIso.mk'
  refine ⟨biprod.inl, ?_, ?_⟩
  · simp
  · rw [← biprod.total]
    have hi : (biprod.inr : B ⟶ A ⊞ B) = 0 := hB.eq_of_src _ _
    have hz : biprod.snd ≫ biprod.inr = (0 : A ⊞ B ⟶ A ⊞ B) := by simp [hi]
    simp [hz]

private lemma isIso_biprod_snd_of_isZero {A B : AddCommGrpCat.{u}}
    [HasBinaryBiproduct A B] (hA : IsZero A) :
    IsIso (biprod.snd : A ⊞ B ⟶ B) := by
  apply IsIso.mk'
  refine ⟨biprod.inr, ?_, ?_⟩
  · simp
  · rw [← biprod.total]
    have hi : (biprod.inl : A ⟶ A ⊞ B) = 0 := hA.eq_of_src _ _
    have hz : biprod.fst ≫ biprod.inl = (0 : A ⊞ B ⟶ A ⊞ B) := by simp [hi]
    simp [hz]

private lemma isIso_biprod_desc_of_isZero_snd {A B C : AddCommGrpCat.{u}}
    [HasBinaryBiproduct A B] (hB : IsZero B) (f : A ⟶ C) [IsIso f] :
    IsIso (biprod.desc f (0 : B ⟶ C)) := by
  rw [biprod.desc_eq]
  simp only [comp_zero, add_zero]
  have : IsIso (biprod.fst : A ⊞ B ⟶ A) := isIso_biprod_fst_of_isZero hB
  infer_instance

private lemma isIso_biprod_desc_of_isZero_fst {A B C : AddCommGrpCat.{u}}
    [HasBinaryBiproduct A B] (hA : IsZero A) (g : B ⟶ C) [IsIso g] :
    IsIso (biprod.desc (0 : A ⟶ C) g) := by
  rw [biprod.desc_eq]
  simp only [comp_zero, zero_add]
  have : IsIso (biprod.snd : A ⊞ B ⟶ B) := isIso_biprod_snd_of_isZero hA
  infer_instance

private lemma stalkAddCommGroupFunctor_additive {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (x : X) :
    (AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor O x).Additive := by
  constructor
  intro A B f g
  show (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf O.obj).map
      ((SheafOfModules.forget O).map (f + g))) =
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf O.obj).map
        ((SheafOfModules.forget O).map f)) +
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf O.obj).map
        ((SheafOfModules.forget O).map g))
  rw [Functor.map_add (F := SheafOfModules.forget O),
    Functor.map_add (F := PresheafOfModules.toPresheaf O.obj),
    Functor.map_add (F := TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)]

private noncomputable def additiveBiprodComparisonIso
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (A B : C)
    [HasBinaryBiproduct A B] [HasBinaryBiproduct (F.obj A) (F.obj B)] :
    F.obj (A ⊞ B) ≅ F.obj A ⊞ F.obj B where
  hom := Functor.biprodComparison F A B
  inv := Functor.biprodComparison' F A B
  hom_inv_id := by
    rw [Functor.biprodComparison, Functor.biprodComparison', biprod.lift_desc,
      ← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total]
    simp
  inv_hom_id := Functor.biprodComparison'_comp_biprodComparison F A B

private lemma additiveBiprodComparison_map_lift
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (A B : C)
    [HasBinaryBiproduct A B] [HasBinaryBiproduct (F.obj A) (F.obj B)]
    {Z : C} (f : Z ⟶ A) (g : Z ⟶ B) :
    F.map (biprod.lift f g) ≫ Functor.biprodComparison F A B =
      biprod.lift (F.map f) (F.map g) := by
  apply biprod.hom_ext
  · calc
      (F.map (biprod.lift f g) ≫ Functor.biprodComparison F A B) ≫ biprod.fst =
          F.map f := by
            calc
              _ = F.map (biprod.lift f g) ≫
                  (Functor.biprodComparison F A B ≫ biprod.fst) := Category.assoc _ _ _
              _ = F.map (biprod.lift f g) ≫ F.map biprod.fst := by
                rw [Functor.biprodComparison_fst]
              _ = F.map f := by rw [← F.map_comp, biprod.lift_fst]
      _ = biprod.lift (F.map f) (F.map g) ≫ biprod.fst := by simp
  · calc
      (F.map (biprod.lift f g) ≫ Functor.biprodComparison F A B) ≫ biprod.snd =
          F.map g := by
            calc
              _ = F.map (biprod.lift f g) ≫
                  (Functor.biprodComparison F A B ≫ biprod.snd) := Category.assoc _ _ _
              _ = F.map (biprod.lift f g) ≫ F.map biprod.snd := by
                rw [Functor.biprodComparison_snd]
              _ = F.map g := by rw [← F.map_comp, biprod.lift_snd]
      _ = biprod.lift (F.map f) (F.map g) ≫ biprod.snd := by simp

private lemma additiveBiprodComparison_map_desc
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (A B : C)
    [HasBinaryBiproduct A B] [HasBinaryBiproduct (F.obj A) (F.obj B)]
    {Z : C} (f : A ⟶ Z) (g : B ⟶ Z) :
    Functor.biprodComparison F A B ≫ biprod.desc (F.map f) (F.map g) =
      F.map (biprod.desc f g) := by
  calc
    Functor.biprodComparison F A B ≫ biprod.desc (F.map f) (F.map g) =
        (Functor.biprodComparison F A B ≫ biprod.fst) ≫ F.map f +
          (Functor.biprodComparison F A B ≫ biprod.snd) ≫ F.map g := by
            rw [biprod.desc_eq, Preadditive.comp_add, ← Category.assoc, ← Category.assoc]
    _ = F.map (biprod.fst ≫ f + biprod.snd ≫ g) := by
      rw [Functor.biprodComparison_fst, Functor.biprodComparison_snd,
        ← F.map_comp, ← F.map_comp, ← F.map_add]
    _ = F.map (biprod.desc f g) := by rw [← biprod.desc_eq]

private lemma map_biprod_lift_compatibility
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {A B Z : C} {A' B' Z' : D}
    [HasBinaryBiproduct A B] [HasBinaryBiproduct (F.obj A) (F.obj B)]
    [HasBinaryBiproduct A' B']
    (f : Z ⟶ A) (g : Z ⟶ B) (a : F.obj A ⟶ A') (b : F.obj B ⟶ B')
    (z : F.obj Z ⟶ Z') (f' : Z' ⟶ A') (g' : Z' ⟶ B')
    (hf : F.map f ≫ a = z ≫ f') (hg : F.map g ≫ b = z ≫ g') :
    F.map (biprod.lift f g) ≫ (F.biprodComparison A B ≫ biprod.map a b) =
      z ≫ biprod.lift f' g' := by
  rw [← Category.assoc, additiveBiprodComparison_map_lift]
  apply biprod.hom_ext <;> simp [Category.assoc, hf, hg]

private lemma map_biprod_desc_compatibility
    {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] {A B Z : C} {A' B' Z' : D}
    [HasBinaryBiproduct A B] [HasBinaryBiproduct (F.obj A) (F.obj B)]
    [HasBinaryBiproduct A' B']
    (f : A ⟶ Z) (g : B ⟶ Z) (a : F.obj A ⟶ A') (b : F.obj B ⟶ B')
    (z : F.obj Z ⟶ Z') (f' : A' ⟶ Z') (g' : B' ⟶ Z')
    (hf : F.map f ≫ z = a ≫ f') (hg : F.map g ≫ z = b ≫ g') :
    F.map (biprod.desc f g) ≫ z =
      (F.biprodComparison A B ≫ biprod.map a b) ≫ biprod.desc f' g' := by
  rw [← additiveBiprodComparison_map_desc]
  simp only [Category.assoc]
  congr 1
  apply biprod.hom_ext' <;> simp [hf, hg]

private lemma extensionRestrictionCoverShortComplex_stalk_exact {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (E : SheafOfModules.{u} O) (x : X) :
    (AlgebraicGeometry.SheafOfModules.stalkShortComplex O
      (extensionRestrictionCoverShortComplex O U V E) x).ShortExact := by
  let F := AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor O x
  let S := AlgebraicGeometry.SheafOfModules.stalkShortComplex O
    (extensionRestrictionCoverShortComplex O U V E) x
  have : F.Additive := stalkAddCommGroupFunctor_additive O x
  have : F.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_additive F
  let B := (jStar U O ⋙ jShriek U O).obj E
  let C := (jStar V O ⋙ jShriek V O).obj E
  -- if the first term is zero and the sum map is invertible, the stalk sequence is split exact
  have key : IsZero S.X₁ → IsIso (biprod.desc (F.map ((jShriekAdjunction U O).counit.app E))
      (F.map ((jShriekAdjunction V O).counit.app E))) → S.ShortExact := fun hX₁ h => by
    have : IsIso (Functor.biprodComparison F B C) := (additiveBiprodComparisonIso F B C).isIso_hom
    have hg : IsIso S.g := by
      show IsIso (F.map (biprod.desc ((jShriekAdjunction U O).counit.app E)
        ((jShriekAdjunction V O).counit.app E)))
      rw [← additiveBiprodComparison_map_desc F B C]
      infer_instance
    exact (ShortComplex.Splitting.ofIsZeroOfIsIso S hX₁ hg).shortExact
  by_cases hxU : x ∈ U
  · by_cases hxV : x ∈ V
    · let W := U ⊓ V
      let cW := F.map ((jShriekAdjunction W O).counit.app E)
      let cU := F.map ((jShriekAdjunction U O).counit.app E)
      let cV := F.map ((jShriekAdjunction V O).counit.app E)
      let iU := F.map ((extensionRestrictionInclusion O W U inf_le_left).app E)
      let iV := F.map ((extensionRestrictionInclusion O W V inf_le_right).app E)
      have hW : IsIso cW := isIso_stalk_extensionRestrictionCounit_of_mem O W E x ⟨hxU, hxV⟩
      have hU : IsIso cU := isIso_stalk_extensionRestrictionCounit_of_mem O U E x hxU
      have hV : IsIso cV := isIso_stalk_extensionRestrictionCounit_of_mem O V E x hxV
      have hiU : iU ≫ cU = cW := by
        dsimp [iU, cU, cW]
        rw [← F.map_comp, extensionRestrictionInclusion_fac]
      have hiV : iV ≫ cV = cW := by
        dsimp [iV, cV, cW]
        rw [← F.map_comp, extensionRestrictionInclusion_fac]
      let T : ShortComplex AddCommGrpCat.{u} := {
        X₁ := F.obj ((jStar W O ⋙ jShriek W O).obj E)
        X₂ := F.obj ((jStar U O ⋙ jShriek U O).obj E) ⊞
          F.obj ((jStar V O ⋙ jShriek V O).obj E)
        X₃ := F.obj E
        f := biprod.lift iU (-iV)
        g := biprod.desc cU cV
        zero := by
          simp [iU, iV, cU, cV, ← F.map_comp, extensionRestrictionInclusion_fac]
      }
      let e₂ : F.obj (((jStar U O ⋙ jShriek U O).obj E) ⊞
          ((jStar V O ⋙ jShriek V O).obj E)) ≅ T.X₂ :=
        additiveBiprodComparisonIso F ((jStar U O ⋙ jShriek U O).obj E)
          ((jStar V O ⋙ jShriek V O).obj E)
      let e : S ≅ T := ShortComplex.isoMk (Iso.refl _) e₂ (Iso.refl _) (by
        simp only [Iso.refl_hom]
        dsimp [S, AlgebraicGeometry.SheafOfModules.stalkShortComplex, T]
        show biprod.lift iU (-iV) = F.map (biprod.lift
          ((extensionRestrictionInclusion O W U inf_le_left).app E)
          (-((extensionRestrictionInclusion O W V inf_le_right).app E))) ≫
          Functor.biprodComparison F ((jStar U O ⋙ jShriek U O).obj E)
            ((jStar V O ⋙ jShriek V O).obj E)
        rw [additiveBiprodComparison_map_lift]
        simp [iU, iV]) (by
        simp only [Iso.refl_hom]
        show Functor.biprodComparison F ((jStar U O ⋙ jShriek U O).obj E)
            ((jStar V O ⋙ jShriek V O).obj E) ≫ biprod.desc cU cV =
          F.map (biprod.desc ((jShriekAdjunction U O).counit.app E)
            ((jShriekAdjunction V O).counit.app E))
        rw [additiveBiprodComparison_map_desc]
        )
      let r : T.X₂ ⟶ T.X₁ := -(biprod.snd ≫ cV ≫ inv cW)
      let s : T.X₃ ⟶ T.X₂ := inv cU ≫ biprod.inl
      have hdesc : biprod.desc cU cV = biprod.fst ≫ cU + biprod.snd ≫ cV :=
        biprod.desc_eq
      have hs : T.Splitting := by
        refine ⟨r, s, ?_, ?_, ?_⟩
        · show biprod.lift iU (-iV) ≫
            (-(biprod.snd ≫ cV ≫ inv cW)) = 𝟙 _
          have hlift : biprod.lift iU (-iV) ≫
              (biprod.snd ≫ cV ≫ inv cW) = -iV ≫ cV ≫ inv cW := by
            simp
          calc
            biprod.lift iU (-iV) ≫ (-(biprod.snd ≫ cV ≫ inv cW)) =
                -(biprod.lift iU (-iV) ≫ (biprod.snd ≫ cV ≫ inv cW)) := by simp
            _ = -(-iV ≫ cV ≫ inv cW) := by rw [hlift]
            _ = iV ≫ cV ≫ inv cW := by simp
            _ = (iV ≫ cV) ≫ inv cW := by rw [Category.assoc]
            _ = cW ≫ inv cW := by rw [hiV]
            _ = 𝟙 _ := by simp
        · dsimp [s, T]
          simp [Category.assoc]
        · have hiU' : iU = cW ≫ inv cU := by
            calc
              iU = (iU ≫ cU) ≫ inv cU := by simp
              _ = cW ≫ inv cU := by rw [hiU]
          have hiV' : iV = cW ≫ inv cV := by
            calc
              iV = (iV ≫ cV) ≫ inv cV := by simp
              _ = cW ≫ inv cV := by rw [hiV]
          have hW_U : inv cW ≫ iU = inv cU := by
            rw [hiU']
            simp
          have hW_V : inv cW ≫ iV = inv cV := by
            rw [hiV']
            simp
          have hgcU : biprod.desc cU cV ≫ inv cU =
              biprod.fst + biprod.snd ≫ cV ≫ inv cU := by
            rw [hdesc]
            simp [Category.assoc]
          have hrf_fst : (r ≫ T.f) ≫ biprod.fst =
              -(biprod.snd ≫ cV ≫ inv cU) := by
            calc
              (r ≫ T.f) ≫ biprod.fst = r ≫ (T.f ≫ biprod.fst) := by rw [Category.assoc]
              _ = r ≫ iU := by dsimp [T]; rw [biprod.lift_fst]
              _ = -(biprod.snd ≫ cV ≫ inv cU) := by
                dsimp [r]
                calc
                  (-biprod.snd ≫ cV ≫ inv cW) ≫ iU =
                      -(biprod.snd ≫ cV ≫ (inv cW ≫ iU)) := by simp [Category.assoc]
                  _ = -(biprod.snd ≫ cV ≫ inv cU) := by rw [hW_U]
          have hrf_snd : (r ≫ T.f) ≫ biprod.snd =
              biprod.snd := by
            calc
              (r ≫ T.f) ≫ biprod.snd = r ≫ (T.f ≫ biprod.snd) := by rw [Category.assoc]
              _ = r ≫ (-iV) := by dsimp [T]; rw [biprod.lift_snd]
              _ = biprod.snd ≫ cV ≫ (inv cW ≫ iV) := by
                dsimp [r]
                simp [Category.assoc]
              _ = biprod.snd ≫ cV ≫ inv cV := by rw [hW_V]
              _ = biprod.snd := by simp
          let inlBC : F.obj B ⟶ F.obj B ⊞ F.obj C := biprod.inl
          let fstBC : F.obj B ⊞ F.obj C ⟶ F.obj B := biprod.fst
          let sndBC : F.obj B ⊞ F.obj C ⟶ F.obj C := biprod.snd
          have hgs_fst : (T.g ≫ s) ≫ biprod.fst =
              biprod.fst + biprod.snd ≫ cV ≫ inv cU := by
            show (biprod.desc cU cV ≫ (inv cU ≫ inlBC)) ≫ fstBC = _
            calc
              (biprod.desc cU cV ≫ (inv cU ≫ inlBC)) ≫ fstBC =
                  (biprod.desc cU cV ≫ inv cU) ≫
                    (inlBC ≫ fstBC) := by
                    simp [Category.assoc]
              _ = (biprod.fst + biprod.snd ≫ cV ≫ inv cU) ≫
                    (inlBC ≫ fstBC) := by rw [hgcU]
              _ = biprod.fst + biprod.snd ≫ cV ≫ inv cU := by simp [inlBC, fstBC]
          have hgs_snd : (T.g ≫ s) ≫ biprod.snd = 0 := by
            show (biprod.desc cU cV ≫ (inv cU ≫ inlBC)) ≫ sndBC = _
            calc
              (biprod.desc cU cV ≫ (inv cU ≫ inlBC)) ≫ sndBC =
                  (biprod.desc cU cV ≫ inv cU) ≫
                    (inlBC ≫ sndBC) := by
                    simp [Category.assoc]
              _ = (biprod.fst + biprod.snd ≫ cV ≫ inv cU) ≫
                    (inlBC ≫ sndBC) := by rw [hgcU]
              _ = 0 := by simp [inlBC, sndBC]
          apply biprod.hom_ext
          · rw [Preadditive.add_comp, hrf_fst, hgs_fst]
            abel
          · rw [Preadditive.add_comp, hrf_snd, hgs_snd]
            abel
      exact (ShortComplex.shortExact_iff_of_iso e).2 hs.shortExact
    · have hC : IsZero (F.obj C) := isZero_stalk_extensionRestriction_of_not_mem O V E x hxV
      have : IsIso (F.map ((jShriekAdjunction U O).counit.app E)) :=
        isIso_stalk_extensionRestrictionCounit_of_mem O U E x hxU
      refine key (isZero_stalk_extensionRestriction_of_not_mem O (U ⊓ V) E x fun hx => hxV hx.2) ?_
      rw [hC.eq_of_src (F.map ((jShriekAdjunction V O).counit.app E)) 0]
      exact isIso_biprod_desc_of_isZero_snd hC _
  · have hxV : x ∈ V := by
      have : x ∈ U ⊔ V := by simp [hUV]
      simpa [Opens.mem_sup] using this.resolve_left hxU
    have hB : IsZero (F.obj B) := isZero_stalk_extensionRestriction_of_not_mem O U E x hxU
    have : IsIso (F.map ((jShriekAdjunction V O).counit.app E)) :=
      isIso_stalk_extensionRestrictionCounit_of_mem O V E x hxV
    refine key (isZero_stalk_extensionRestriction_of_not_mem O (U ⊓ V) E x fun hx => hxU hx.1) ?_
    rw [hB.eq_of_src (F.map ((jShriekAdjunction U O).counit.app E)) 0]
    exact isIso_biprod_desc_of_isZero_fst hB _

private lemma extensionRestrictionCoverShortComplex_shortExact {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U V : Opens X) (hUV : U ⊔ V = ⊤) (E : SheafOfModules.{u} O) :
    (extensionRestrictionCoverShortComplex O U V E).ShortExact := by
  let : Abelian (SheafOfModules.{u} O) := inferInstance
  let S := extensionRestrictionCoverShortComplex O U V E
  have hS : S.Exact := (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact O S).2
    (fun x => (extensionRestrictionCoverShortComplex_stalk_exact O U V hUV E x).exact)
  have hmono : Mono S.f := by
    let L : ShortComplex (SheafOfModules.{u} O) := {
      X₁ := 0
      X₂ := S.X₁
      X₃ := S.X₂
      f := 0
      g := S.f
      zero := by simp
    }
    have hL : L.Exact :=
      (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact O L).2 (by
      intro x
      let T := AlgebraicGeometry.SheafOfModules.stalkShortComplex O S x
      let T₀ := AlgebraicGeometry.SheafOfModules.stalkShortComplex O L x
      let F := AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor O x
      have : F.Additive := stalkAddCommGroupFunctor_additive O x
      have hT : T.ShortExact := extensionRestrictionCoverShortComplex_stalk_exact O U V hUV E x
      have hzero : IsZero T₀.X₁ := by
        dsimp [T₀, L, AlgebraicGeometry.SheafOfModules.stalkShortComplex]
        exact Functor.map_isZero _ (isZero_zero _)
      have hf : T₀.f = 0 := by
        show F.map (0 : L.X₁ ⟶ L.X₂) = 0
        exact F.map_zero L.X₁ L.X₂
      have hmono' : Mono T₀.g := by
        show Mono T.f
        exact hT.mono_f
      exact (T₀.exact_iff_mono hf).2 hmono')
    exact (L.exact_iff_mono (by simp [L])).1 hL
  have epi : Epi S.g := by
    let R : ShortComplex (SheafOfModules.{u} O) := {
      X₁ := S.X₂
      X₂ := S.X₃
      X₃ := 0
      f := S.g
      g := 0
      zero := by simp
    }
    have hR : R.Exact :=
      (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact O R).2 (by
      intro x
      let T := AlgebraicGeometry.SheafOfModules.stalkShortComplex O S x
      let T₀ := AlgebraicGeometry.SheafOfModules.stalkShortComplex O R x
      let F := AlgebraicGeometry.SheafOfModules.stalkAddCommGroupFunctor O x
      have : F.Additive := stalkAddCommGroupFunctor_additive O x
      have hT : T.ShortExact := extensionRestrictionCoverShortComplex_stalk_exact O U V hUV E x
      have hzero : IsZero T₀.X₃ := by
        dsimp [T₀, R, AlgebraicGeometry.SheafOfModules.stalkShortComplex]
        exact Functor.map_isZero _ (isZero_zero _)
      have hg : T₀.g = 0 := by
        show F.map (0 : R.X₂ ⟶ R.X₃) = 0
        exact F.map_zero R.X₂ R.X₃
      have epi' : Epi T₀.f := by
        show Epi T.g
        exact hT.epi_g
      exact (T₀.exact_iff_epi hg).2 epi')
    exact (R.exact_iff_epi (by simp [R])).1 hR
  exact ShortComplex.ShortExact.mk' hS hmono epi

/-- The cover short complex applied degreewise to a cochain complex. -/
private noncomputable def extensionRestrictionCoverComplexShortComplex {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U V : Opens X) (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    ShortComplex (CochainComplex (SheafOfModules.{u} O) ℤ) := by
  let W := U ⊓ V
  let GW := jStar W O ⋙ jShriek W O
  let GU := jStar U O ⋙ jShriek U O
  let GV := jStar V O ⋙ jShriek V O
  let fU := NatTrans.mapHomologicalComplex
    (extensionRestrictionInclusion O W U inf_le_left) (ComplexShape.up ℤ)
  let fV := NatTrans.mapHomologicalComplex
    (extensionRestrictionInclusion O W V inf_le_right) (ComplexShape.up ℤ)
  let cU := NatTrans.mapHomologicalComplex (jShriekAdjunction U O).counit
    (ComplexShape.up ℤ)
  let cV := NatTrans.mapHomologicalComplex (jShriekAdjunction V O).counit
    (ComplexShape.up ℤ)
  let eId := Functor.mapHomologicalComplexIdIso (SheafOfModules.{u} O)
    (ComplexShape.up ℤ)
  let cU' := cU ≫ eId.hom
  let cV' := cV ≫ eId.hom
  refine {
    X₁ := ((jStar (U ⊓ V) O ⋙ jShriek (U ⊓ V) O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K
    X₂ := (GU.mapHomologicalComplex (ComplexShape.up ℤ)).obj K ⊞
      (GV.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    X₃ := K
    f := biprod.lift (fU.app K) (-(fV.app K))
    g := biprod.desc (cU'.app K) (cV'.app K)
    zero := ?_ }
  ext n
  simp [fU, fV, cU', cV', cU, cV, eId, NatTrans.mapHomologicalComplex,
    extensionRestrictionInclusion_fac]

private lemma extensionRestrictionCoverComplexShortComplex_X3 {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U V : Opens X)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (extensionRestrictionCoverComplexShortComplex O U V K).X₃ = K := rfl

private lemma extensionRestrictionCoverComplexShortComplex_X1 {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U V : Opens X)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (extensionRestrictionCoverComplexShortComplex O U V K).X₁ =
      ((jStar (U ⊓ V) O ⋙ jShriek (U ⊓ V) O).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K := rfl

private lemma extensionRestrictionCoverComplexShortComplex_shortExact {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (extensionRestrictionCoverComplexShortComplex O U V K).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  intro n
  let F := HomologicalComplex.eval (SheafOfModules.{u} O) (ComplexShape.up ℤ) n
  let A := ((jStar (U ⊓ V) O ⋙ jShriek (U ⊓ V) O).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let B := ((jStar U O ⋙ jShriek U O).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let C := ((jStar V O ⋙ jShriek V O).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K
  let e₂ := additiveBiprodComparisonIso F B C
  let S := (extensionRestrictionCoverComplexShortComplex O U V K).map F
  let T := extensionRestrictionCoverShortComplex O U V (K.X n)
  let fU := NatTrans.mapHomologicalComplex
    (extensionRestrictionInclusion O (U ⊓ V) U inf_le_left) (ComplexShape.up ℤ)
  let fV := NatTrans.mapHomologicalComplex
    (extensionRestrictionInclusion O (U ⊓ V) V inf_le_right) (ComplexShape.up ℤ)
  let cU := NatTrans.mapHomologicalComplex (jShriekAdjunction U O).counit
    (ComplexShape.up ℤ)
  let cV := NatTrans.mapHomologicalComplex (jShriekAdjunction V O).counit
    (ComplexShape.up ℤ)
  let eId := Functor.mapHomologicalComplexIdIso (SheafOfModules.{u} O)
    (ComplexShape.up ℤ)
  let cU' := cU ≫ eId.hom
  let cV' := cV ≫ eId.hom
  have : F.Additive := inferInstance
  have e : S ≅ T := ShortComplex.isoMk (Iso.refl _) e₂ (Iso.refl _) (by
    dsimp [S, T, extensionRestrictionCoverComplexShortComplex,
      extensionRestrictionCoverShortComplex, A, B, C, e₂]
    show biprod.lift
        ((extensionRestrictionInclusion O (U ⊓ V) U inf_le_left).app (K.X n))
        (-((extensionRestrictionInclusion O (U ⊓ V) V inf_le_right).app (K.X n))) =
      F.map (biprod.lift (fU.app K) (-fV.app K)) ≫
        Functor.biprodComparison F B C
    rw [additiveBiprodComparison_map_lift]
    simp [F, fU, fV, NatTrans.mapHomologicalComplex]) (by
    dsimp [S, T, extensionRestrictionCoverComplexShortComplex,
      extensionRestrictionCoverShortComplex, B, C, e₂]
    show Functor.biprodComparison F B C ≫ biprod.desc
        (F.map (cU'.app K)) (F.map (cV'.app K)) =
        F.map (biprod.desc (cU'.app K) (cV'.app K))
    exact additiveBiprodComparison_map_desc F B C _ _)
  exact ShortComplex.shortExact_of_iso e.symm
    (extensionRestrictionCoverShortComplex_shortExact O U V hUV (K.X n))

private def extensionRestrictionCoverComplexShortComplexMap {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U V : Opens X) {K L : CochainComplex (SheafOfModules.{u} O) ℤ} (f : K ⟶ L) :
    extensionRestrictionCoverComplexShortComplex O U V K ⟶
      extensionRestrictionCoverComplexShortComplex O U V L := by
  let GW := (jStar (U ⊓ V) O ⋙ jShriek (U ⊓ V) O).mapHomologicalComplex
    (ComplexShape.up ℤ)
  let GU := (jStar U O ⋙ jShriek U O).mapHomologicalComplex (ComplexShape.up ℤ)
  let GV := (jStar V O ⋙ jShriek V O).mapHomologicalComplex (ComplexShape.up ℤ)
  let iU := NatTrans.mapHomologicalComplex
    (extensionRestrictionInclusion O (U ⊓ V) U inf_le_left) (ComplexShape.up ℤ)
  let iV := NatTrans.mapHomologicalComplex
    (extensionRestrictionInclusion O (U ⊓ V) V inf_le_right) (ComplexShape.up ℤ)
  let cU := NatTrans.mapHomologicalComplex (jShriekAdjunction U O).counit
    (ComplexShape.up ℤ)
  let cV := NatTrans.mapHomologicalComplex (jShriekAdjunction V O).counit
    (ComplexShape.up ℤ)
  let eId := Functor.mapHomologicalComplexIdIso (SheafOfModules.{u} O)
    (ComplexShape.up ℤ)
  let cU' := cU ≫ eId.hom
  let cV' := cV ≫ eId.hom
  refine {
    τ₁ := GW.map f
    τ₂ := biprod.map (GU.map f) (GV.map f)
    τ₃ := f
    comm₁₂ := by
      change GW.map f ≫ biprod.lift (iU.app L) (-(iV.app L)) =
        biprod.lift (iU.app K) (-(iV.app K)) ≫ biprod.map (GU.map f) (GV.map f)
      apply biprod.hom_ext
      · calc
          _ = GW.map f ≫ iU.app L := by rw [Category.assoc, biprod.lift_fst]
          _ = iU.app K ≫ GU.map f :=
            NatTrans.mapHomologicalComplex_naturality
              (extensionRestrictionInclusion O (U ⊓ V) U inf_le_left) f
          _ = _ := by
            rw [Category.assoc, biprod.map_fst, ← Category.assoc, biprod.lift_fst]
      · have hn := NatTrans.mapHomologicalComplex_naturality
          (extensionRestrictionInclusion O (U ⊓ V) V inf_le_right) f
        calc
          _ = -(GW.map f ≫ iV.app L) := by rw [Category.assoc, biprod.lift_snd]; simp
          _ = -(iV.app K ≫ GV.map f) := by rw [hn]
          _ = _ := by
            rw [Category.assoc, biprod.map_snd, ← Category.assoc, biprod.lift_snd]
            simp
    comm₂₃ := by
      change biprod.map (GU.map f) (GV.map f) ≫ biprod.desc (cU'.app L) (cV'.app L) =
        biprod.desc (cU'.app K) (cV'.app K) ≫ f
      apply biprod.hom_ext'
      · have hn := cU'.naturality f
        calc
          _ = GU.map f ≫ cU'.app L := by simp
          _ = cU'.app K ≫ f := hn
          _ = _ := by simp
      · have hn := cV'.naturality f
        calc
          _ = GV.map f ≫ cV'.app L := by simp
          _ = cV'.app K ≫ f := hn
          _ = _ := by simp
  }

private noncomputable def exactExtensionRestrictionDerivedIso {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    [(jStar U O ⋙ jShriek U O).Additive]
    [PreservesFiniteLimits (jStar U O ⋙ jShriek U O)]
    [PreservesFiniteColimits (jStar U O ⋙ jShriek U O)]
    (DU : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aU : homotopyExtensionRestriction O U ⟶ DerivedCategory.Qh ⋙ DU)
    [DU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [((jStar U O ⋙ jShriek U O).mapDerivedCategory).IsRightDerivedFunctor
      (jStar U O ⋙ jShriek U O).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))] :
    (jStar U O ⋙ jShriek U O).mapDerivedCategory ≅ DU :=
  Functor.rightDerivedUnique _ _
    (jStar U O ⋙ jShriek U O).mapDerivedCategoryFactorsh.inv aU
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))

private lemma isIso_exactExtensionRestriction_comparison_app {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    [(jStar U O ⋙ jShriek U O).Additive]
    [PreservesFiniteLimits (jStar U O ⋙ jShriek U O)]
    [PreservesFiniteColimits (jStar U O ⋙ jShriek U O)]
    (DU : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aU : homotopyExtensionRestriction O U ⟶ DerivedCategory.Qh ⋙ DU)
    [DU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [((jStar U O ⋙ jShriek U O).mapDerivedCategory).IsRightDerivedFunctor
      (jStar U O ⋙ jShriek U O).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    (K : HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :
    IsIso (aU.app K) := by
  let α := (jStar U O ⋙ jShriek U O).mapDerivedCategoryFactorsh.inv
  let e := ((jStar U O ⋙ jShriek U O).mapDerivedCategory).rightDerivedDesc α
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) DU aU
  have hfac := Functor.rightDerived_fac
    ((jStar U O ⋙ jShriek U O).mapDerivedCategory) α
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) DU aU
  have h : α.app K ≫ e.app (DerivedCategory.Qh.obj K) = aU.app K := by
    show α.app K ≫
      (((jStar U O ⋙ jShriek U O).mapDerivedCategory).rightDerivedDesc α
        (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) DU aU).app
          (DerivedCategory.Qh.obj K) = aU.app K
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.comp_obj] using
      congr_app hfac K
  have : IsIso e :=
    (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
      ((jStar U O ⋙ jShriek U O).mapDerivedCategory) α
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) DU aU).1
      inferInstance
  let : IsIso α := inferInstance
  let : IsIso (α.app K) := NatIso.isIso_app_of_isIso α K
  let : IsIso (e.app (DerivedCategory.Qh.obj K)) := inferInstance
  rw [← h]
  infer_instance

private noncomputable def extensionRestrictionCoverConnectingHomotopy {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U V : Opens X)
    (hUV : U ⊔ V = ⊤)
    (DUV : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aUV : homotopyExtensionRestriction O (U ⊓ V) ⟶ DerivedCategory.Qh ⋙ DUV)
    [DUV.IsRightDerivedFunctor aUV
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))] :
    DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ DUV ⋙
      shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ) := by
  let q := HomotopyCategory.quotient (SheafOfModules.{u} O) (ComplexShape.up ℤ)
  let qIso := DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)
  let F := jStar (U ⊓ V) O ⋙ jShriek (U ⊓ V) O
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let factors := Functor.mapHomotopyCategoryFactors F (ComplexShape.up ℤ)
  refine {
    app K := by
      let S := extensionRestrictionCoverComplexShortComplex O U V K
      let hS := extensionRestrictionCoverComplexShortComplex_shortExact O U V hUV K
      let eX3 := extensionRestrictionCoverComplexShortComplex_X3 O U V K
      let eX1 := extensionRestrictionCoverComplexShortComplex_X1 O U V K
      exact DerivedCategory.Q.map (eqToHom eX3.symm) ≫
        DerivedCategory.triangleOfSESδ hS ≫
        (qIso.inv.app S.X₁)⟦(1 : ℤ)⟧' ≫
        ((DerivedCategory.Qh.map (q.map (eqToHom eX1)))⟦(1 : ℤ)⟧') ≫
        ((DerivedCategory.Qh.map (factors.inv.app K))⟦(1 : ℤ)⟧') ≫
        (aUV.app (q.obj K))⟦(1 : ℤ)⟧' ≫
        ((DUV.map (qIso.hom.app K))⟦(1 : ℤ)⟧')
    naturality := by
      intro K L f
      let S₁ := extensionRestrictionCoverComplexShortComplex O U V K
      let S₂ := extensionRestrictionCoverComplexShortComplex O U V L
      let φ := extensionRestrictionCoverComplexShortComplexMap O U V f
      let h₁ := extensionRestrictionCoverComplexShortComplex_shortExact O U V hUV K
      let h₂ := extensionRestrictionCoverComplexShortComplex_shortExact O U V hUV L
      have hδ := DerivedCategory.triangleOfSESδ_naturality h₁ h₂ φ
      have hτ₃ : φ.τ₃ = f := rfl
      let eX3K := extensionRestrictionCoverComplexShortComplex_X3 O U V K
      let eX3L := extensionRestrictionCoverComplexShortComplex_X3 O U V L
      let eX1K := extensionRestrictionCoverComplexShortComplex_X1 O U V K
      let eX1L := extensionRestrictionCoverComplexShortComplex_X1 O U V L
      -- `eX3K` and `eX3L` are equalities between definitionally equal objects, so each is
      -- `rfl` by proof irrelevance and the `eqToHom`s are identities; saying so avoids asking
      -- `simp` to transport across them.
      have hcomm : f ≫ eqToHom eX3L.symm = eqToHom eX3K.symm ≫ φ.τ₃ :=
        (Category.comp_id f).trans (Category.id_comp f).symm
      have hprefix : DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (eqToHom eX3L.symm) =
          DerivedCategory.Q.map (eqToHom eX3K.symm) ≫ DerivedCategory.Q.map φ.τ₃ := by
        rw [← Functor.map_comp, ← Functor.map_comp, hcomm]
      have hprefixδ := congrArg
        (fun g => g ≫ DerivedCategory.triangleOfSESδ h₂) hprefix
      have hconv : φ.τ₁ ≫ eqToHom eX1L = eqToHom eX1K ≫ Fc.map f := by
        rfl
      have hconvQ : q.map φ.τ₁ ≫ q.map (eqToHom eX1L) =
          q.map (eqToHom eX1K) ≫ q.map (Fc.map f) := by
        rw [← Functor.map_comp, ← Functor.map_comp, hconv]
      have hq := qIso.hom.naturality f
      have hqi := qIso.inv.naturality φ.τ₁
      have hfactor := factors.inv.naturality f
      have ha := aUV.naturality (q.map f)
      dsimp [Functor.mapHomotopyCategory_map] at hq hqi ha
      let sh := shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)
      change DerivedCategory.Q.map φ.τ₁ ≫ qIso.inv.app S₂.X₁ =
        qIso.inv.app S₁.X₁ ≫ DerivedCategory.Qh.map (q.map φ.τ₁) at hqi
      have hinput :
        q.map φ.τ₁ ≫ q.map (eqToHom eX1L) ≫ factors.inv.app L =
          q.map (eqToHom eX1K) ≫ factors.inv.app K ≫
            (F.mapHomotopyCategory (ComplexShape.up ℤ)).map (q.map f) := by
        have hfactor' := by
          simpa only [Functor.comp_map] using hfactor
        calc
          _ = (q.map φ.τ₁ ≫ q.map (eqToHom eX1L)) ≫ factors.inv.app L := by
            simp only [Category.assoc]
          _ = (q.map (eqToHom eX1K) ≫ q.map (Fc.map f)) ≫ factors.inv.app L := by
            rw [hconvQ]
          _ = q.map (eqToHom eX1K) ≫ (q.map (Fc.map f) ≫ factors.inv.app L) := by
            simp only [Category.assoc]
          _ = q.map (eqToHom eX1K) ≫
              (factors.inv.app K ≫
                (F.mapHomotopyCategory (ComplexShape.up ℤ)).map (q.map f)) := by
            rw [hfactor']
      have hinputQh := congrArg DerivedCategory.Qh.map hinput
      simp only [Functor.map_comp] at hinputQh
      have hinputA :
          (DerivedCategory.Qh.map (q.map φ.τ₁) ≫
            DerivedCategory.Qh.map (q.map (eqToHom eX1L)) ≫
            DerivedCategory.Qh.map (factors.inv.app L)) ≫ aUV.app (q.obj L) =
          DerivedCategory.Qh.map (q.map (eqToHom eX1K)) ≫
            DerivedCategory.Qh.map (factors.inv.app K) ≫ aUV.app (q.obj K) ≫
              DUV.map (DerivedCategory.Qh.map (q.map f)) := by
        calc
          _ = DerivedCategory.Qh.map
                (q.map φ.τ₁ ≫ q.map (eqToHom eX1L) ≫ factors.inv.app L) ≫
                aUV.app (q.obj L) := by simp only [Functor.map_comp, Category.assoc]
          _ = DerivedCategory.Qh.map
                (q.map (eqToHom eX1K) ≫ factors.inv.app K ≫
                  (F.mapHomotopyCategory (ComplexShape.up ℤ)).map (q.map f)) ≫
                aUV.app (q.obj L) := by rw [hinput]
          _ = (DerivedCategory.Qh.map (q.map (eqToHom eX1K)) ≫
                DerivedCategory.Qh.map (factors.inv.app K)) ≫
                (DerivedCategory.Qh.map
                  ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (q.map f)) ≫
                  aUV.app (q.obj L)) := by simp only [Functor.map_comp, Category.assoc]
          _ = DerivedCategory.Qh.map (q.map (eqToHom eX1K)) ≫
                DerivedCategory.Qh.map (factors.inv.app K) ≫
                (aUV.app (q.obj K) ≫ DUV.map (DerivedCategory.Qh.map (q.map f))) := by
                  rw [ha]
                  simp only [Category.assoc]
          _ = _ := rfl
      have hqD := congrArg DUV.map hq
      simp only [Functor.map_comp] at hqD
      have hraw :
          (DerivedCategory.Q.map φ.τ₁ ≫ qIso.inv.app S₂.X₁ ≫
            DerivedCategory.Qh.map (q.map (eqToHom eX1L)) ≫
            DerivedCategory.Qh.map (factors.inv.app L) ≫
            aUV.app (q.obj L) ≫ DUV.map (qIso.hom.app L)) =
          (qIso.inv.app S₁.X₁ ≫
            DerivedCategory.Qh.map (q.map (eqToHom eX1K)) ≫
            DerivedCategory.Qh.map (factors.inv.app K) ≫
            aUV.app (q.obj K) ≫ DUV.map (qIso.hom.app K)) ≫
            DUV.map (DerivedCategory.Q.map f) := by
        let r₁ := DerivedCategory.Qh.map (q.map (eqToHom eX1L)) ≫
          DerivedCategory.Qh.map (factors.inv.app L) ≫ aUV.app (q.obj L) ≫
            DUV.map (qIso.hom.app L)
        let r₂ := DUV.map (qIso.hom.app L)
        let r₃ := aUV.app (q.obj L) ≫ DUV.map (qIso.hom.app L)
        let p₂ := qIso.inv.app S₁.X₁
        let p₃ := qIso.inv.app S₁.X₁ ≫
          DerivedCategory.Qh.map (q.map (eqToHom eX1K))
        let p₄ := p₃ ≫ DerivedCategory.Qh.map (factors.inv.app K)
        let p₅ := p₄ ≫ aUV.app (q.obj K)
        have hqiTail := congrArg (fun g => g ≫ r₁) hqi
        have hinputTail := congrArg (fun g => p₂ ≫ g ≫ r₃) hinputQh
        have haTail := congrArg (fun g => p₄ ≫ g ≫ r₂) ha
        have hqTail := congrArg (fun g => p₅ ≫ g) hqD
        calc
          _ = (DerivedCategory.Q.map φ.τ₁ ≫ qIso.inv.app S₂.X₁) ≫ r₁ := by
            simp only [r₁, Category.assoc]
          _ = (qIso.inv.app S₁.X₁ ≫
              DerivedCategory.Qh.map (q.map φ.τ₁)) ≫ r₁ := by
            simpa only [r₁, Category.assoc] using hqiTail
          _ = p₂ ≫ (DerivedCategory.Qh.map (q.map φ.τ₁) ≫
              DerivedCategory.Qh.map (q.map (eqToHom eX1L)) ≫
              DerivedCategory.Qh.map (factors.inv.app L) ≫ r₃) := by
            simp only [p₂, r₁, r₃, Category.assoc]
          _ = p₂ ≫ (DerivedCategory.Qh.map (q.map (eqToHom eX1K)) ≫
              DerivedCategory.Qh.map (factors.inv.app K) ≫
              DerivedCategory.Qh.map
                ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (q.map f)) ≫ r₃) := by
            simpa only [p₂, r₂, r₃, Category.assoc] using hinputTail
          _ = p₄ ≫ (DerivedCategory.Qh.map
              ((F.mapHomotopyCategory (ComplexShape.up ℤ)).map (q.map f)) ≫ r₃) := by
            simp only [p₄, p₃, p₂, r₃, Category.assoc]
          _ = p₄ ≫ (aUV.app (q.obj K) ≫
              DUV.map (DerivedCategory.Qh.map (q.map f)) ≫ r₂) := by
            simpa only [p₄, r₂, r₃, Category.assoc] using haTail
          _ = p₅ ≫ (DUV.map (DerivedCategory.Qh.map (q.map f)) ≫ r₂) := by
            simp only [p₅, p₄, r₂, Category.assoc]
          _ = p₅ ≫ (DUV.map (qIso.hom.app K) ≫
              DUV.map (DerivedCategory.Q.map f)) := by
            simpa only [p₅, p₄, p₃, p₂, Category.assoc] using hqTail
          _ = _ := by simp only [p₅, p₄, p₃, Category.assoc]
      rw [hτ₃] at hδ
      change
        (DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (eqToHom eX3L.symm) ≫
          DerivedCategory.triangleOfSESδ h₂ ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (qIso.inv.app S₂.X₁) ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (DerivedCategory.Qh.map (q.map (eqToHom eX1L))) ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (DerivedCategory.Qh.map (factors.inv.app L)) ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (aUV.app (q.obj L)) ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (DUV.map (qIso.hom.app L))) =
        (DerivedCategory.Q.map (eqToHom eX3K.symm) ≫
          DerivedCategory.triangleOfSESδ h₁ ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (qIso.inv.app S₁.X₁) ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (DerivedCategory.Qh.map (q.map (eqToHom eX1K))) ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (DerivedCategory.Qh.map (factors.inv.app K)) ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (aUV.app (q.obj K)) ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (DUV.map (qIso.hom.app K))) ≫
          (DerivedCategory.Q ⋙ DUV ⋙
            shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map f
      have hprefixδ' := congrArg
        (fun g => g ≫ DerivedCategory.triangleOfSESδ h₂) hprefix
      simp only [Category.assoc] at hprefixδ'
      have hfirst :
          DerivedCategory.Q.map f ≫ DerivedCategory.Q.map (eqToHom eX3L.symm) ≫
              DerivedCategory.triangleOfSESδ h₂ =
            DerivedCategory.Q.map (eqToHom eX3K.symm) ≫
              DerivedCategory.Q.map φ.τ₃ ≫ DerivedCategory.triangleOfSESδ h₂ := by
        simpa only [Category.assoc] using hprefixδ'
      clear hprefixδ
      let tailL :=
        (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (qIso.inv.app S₂.X₁) ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (DerivedCategory.Qh.map (q.map (eqToHom eX1L))) ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (DerivedCategory.Qh.map (factors.inv.app L)) ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (aUV.app (q.obj L)) ≫
          (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
            (DUV.map (qIso.hom.app L))
      have hfirstTail := congrArg (fun g => g ≫ tailL) hfirst
      trans ((DerivedCategory.Q.map (eqToHom eX3K.symm) ≫
          DerivedCategory.Q.map φ.τ₃ ≫ DerivedCategory.triangleOfSESδ h₂) ≫ tailL)
      · simpa only [Category.assoc] using hfirstTail
      · rw [← hτ₃] at hδ
        have hδp := congrArg
          (fun g => DerivedCategory.Q.map (eqToHom eX3K.symm) ≫ g) hδ
        have hδpTail := congrArg (fun g => g ≫ tailL) hδp
        trans ((DerivedCategory.Q.map (eqToHom eX3K.symm) ≫
            (DerivedCategory.triangleOfSESδ h₁ ≫
              (shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)).map
                (DerivedCategory.Q.map φ.τ₁))) ≫ tailL)
        · simpa only [Category.assoc] using hδpTail.symm
        · have hrawSh := congrArg sh.map hraw
          simp only [Functor.map_comp] at hrawSh
          have hrawFront := congrArg
            (fun g => DerivedCategory.Q.map (eqToHom eX3K.symm) ≫
              DerivedCategory.triangleOfSESδ h₁ ≫ g) hrawSh
          have hcomp : (DerivedCategory.Q ⋙ DUV ⋙ sh).map f =
              sh.map (DUV.map (DerivedCategory.Q.map f)) := rfl
          rw [hcomp]
          simpa only [Category.assoc, Functor.map_comp] using hrawFront }

private noncomputable def derivedExtensionRestrictionConnecting {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U V : Opens X)
    (hUV : U ⊔ V = ⊤)
    (DUV : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aUV : homotopyExtensionRestriction O (U ⊓ V) ⟶ DerivedCategory.Qh ⋙ DUV)
    [DUV.IsRightDerivedFunctor aUV
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))] :
    𝟭 (DerivedCategory (SheafOfModules.{u} O)) ⟶
      DUV ⋙ shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ) :=
  Localization.liftNatTrans DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))
    DerivedCategory.Q
    (DerivedCategory.Q ⋙ DUV ⋙
      shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ))
    (𝟭 (DerivedCategory (SheafOfModules.{u} O)))
    (DUV ⋙ shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ))
    (extensionRestrictionCoverConnectingHomotopy O U V hUV DUV aUV)

private noncomputable def derivedExtensionRestrictionComparisonIso
    {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U : Opens X)
    [(jStar U O ⋙ jShriek U O).Additive]
    [PreservesFiniteLimits (jStar U O ⋙ jShriek U O)]
    [PreservesFiniteColimits (jStar U O ⋙ jShriek U O)]
    (DU : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aU : homotopyExtensionRestriction O U ⟶ DerivedCategory.Qh ⋙ DU)
    [DU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [((jStar U O ⋙ jShriek U O).mapDerivedCategory).IsRightDerivedFunctor
      (jStar U O ⋙ jShriek U O).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    DerivedCategory.Q.obj (((jStar U O ⋙ jShriek U O).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K) ≅
      DU.obj (DerivedCategory.Q.obj K) := by
  let F := jStar U O ⋙ jShriek U O
  let q := HomotopyCategory.quotient (SheafOfModules.{u} O) (ComplexShape.up ℤ)
  let qIso := DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)
  haveI : IsIso (aU.app (q.obj K)) :=
    isIso_exactExtensionRestriction_comparison_app O U DU aU (q.obj K)
  exact (qIso.symm.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)).trans
    ((asIso (aU.app (q.obj K))).trans (DU.mapIso (qIso.app K)))


/-- Pasting three commuting squares: if `α ≫ τ' = m ≫ α'`, `δ ≫ τ = τ' ≫ δ'` and
`g ≫ ι' = ι ≫ m`, then `(ι ≫ α ≫ δ) ≫ τ = g ≫ ι' ≫ α' ≫ δ'`. It is stated for an abstract
category so that it applies up to definitional unfolding of the objects. -/
private lemma comp_eq_of_three_squares {C : Type*} [Category* C]
    {x x' y y' z z' w w' : C} {ι : x ⟶ y} {ι' : x' ⟶ y'} {g : x ⟶ x'} {m : y ⟶ y'}
    {α : y ⟶ z} {α' : y' ⟶ z'} {δ : z ⟶ w} {δ' : z' ⟶ w'} {τ : w ⟶ w'} {τ' : z ⟶ z'}
    (hi : α ≫ τ' = m ≫ α') (hn : δ ≫ τ = τ' ≫ δ') (he : g ≫ ι' = ι ≫ m) :
    (ι ≫ α ≫ δ) ≫ τ = g ≫ ι' ≫ α' ≫ δ' := by
  rw [← Category.assoc g, he]
  simp [hn, reassoc_of% hi]

private lemma derivedExtensionRestrictionComparisonIso_hom_inclusion {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (W U : Opens X) (hWU : W ≤ U)
    [PreservesFiniteLimits (jStar W O ⋙ jShriek W O)]
    [PreservesFiniteColimits (jStar W O ⋙ jShriek W O)]
    [PreservesFiniteLimits (jStar U O ⋙ jShriek U O)]
    [PreservesFiniteColimits (jStar U O ⋙ jShriek U O)]
    (DW DU : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aW : homotopyExtensionRestriction O W ⟶ DerivedCategory.Qh ⋙ DW)
    (aU : homotopyExtensionRestriction O U ⟶ DerivedCategory.Qh ⋙ DU)
    [DW.IsRightDerivedFunctor aW
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [DU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [((jStar W O ⋙ jShriek W O).mapDerivedCategory).IsRightDerivedFunctor
      (jStar W O ⋙ jShriek W O).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [((jStar U O ⋙ jShriek U O).mapDerivedCategory).IsRightDerivedFunctor
      (jStar U O ⋙ jShriek U O).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (derivedExtensionRestrictionComparisonIso O W DW aW K).hom ≫
        (derivedExtensionRestrictionInclusion O W U hWU DW DU aW aU).app
          (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (extensionRestrictionInclusion O W U hWU) (ComplexShape.up ℤ)).app K) ≫
        (derivedExtensionRestrictionComparisonIso O U DU aU K).hom := by
  let i := derivedExtensionRestrictionInclusion O W U hWU DW DU aW aU
  let q := HomotopyCategory.quotient (SheafOfModules.{u} O) (ComplexShape.up ℤ)
  let e := DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)
  let f := (NatTrans.mapHomologicalComplex
    (extensionRestrictionInclusion O W U hWU) (ComplexShape.up ℤ)).app K
  let KW := ((jStar W O ⋙ jShriek W O).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  let KU := ((jStar U O ⋙ jShriek U O).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hi : aW.app (q.obj K) ≫ i.app (DerivedCategory.Qh.obj (q.obj K)) =
      DerivedCategory.Qh.map (q.map f) ≫ aU.app (q.obj K) :=
    congr_app (derivedExtensionRestrictionInclusion_fac O W U hWU DW DU aW aU) (q.obj K)
  have hn : DW.map (e.hom.app K) ≫ i.app (DerivedCategory.Q.obj K) =
      i.app (DerivedCategory.Qh.obj (q.obj K)) ≫ DU.map (e.hom.app K) :=
    i.naturality (e.hom.app K)
  have he : DerivedCategory.Q.map f ≫ e.inv.app KU =
      e.inv.app KW ≫ DerivedCategory.Qh.map (q.map f) := e.inv.naturality f
  show (e.inv.app KW ≫ aW.app (q.obj K) ≫ DW.map (e.hom.app K)) ≫
      i.app (DerivedCategory.Q.obj K) =
    DerivedCategory.Q.map f ≫ e.inv.app KU ≫ aU.app (q.obj K) ≫ DU.map (e.hom.app K)
  exact comp_eq_of_three_squares hi hn he

private lemma derivedExtensionRestrictionComparisonIso_hom_counit {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}) (U : Opens X)
    [PreservesFiniteLimits (jStar U O ⋙ jShriek U O)]
    [PreservesFiniteColimits (jStar U O ⋙ jShriek U O)]
    (DU : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aU : homotopyExtensionRestriction O U ⟶ DerivedCategory.Qh ⋙ DU)
    [DU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [((jStar U O ⋙ jShriek U O).mapDerivedCategory).IsRightDerivedFunctor
      (jStar U O ⋙ jShriek U O).mapDerivedCategoryFactorsh.inv
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    (K : CochainComplex (SheafOfModules.{u} O) ℤ) :
    (derivedExtensionRestrictionComparisonIso O U DU aU K).hom ≫
        (derivedExtensionRestrictionCounit O U DU aU).app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map
        (((NatTrans.mapHomologicalComplex (jShriekAdjunction U O).counit
          (ComplexShape.up ℤ)).app K) ≫
          (Functor.mapHomologicalComplexIdIso (SheafOfModules.{u} O)
            (ComplexShape.up ℤ)).hom.app K) := by
  let c := derivedExtensionRestrictionCounit O U DU aU
  let q := HomotopyCategory.quotient (SheafOfModules.{u} O) (ComplexShape.up ℤ)
  let e := DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)
  let f := ((NatTrans.mapHomologicalComplex (jShriekAdjunction U O).counit
    (ComplexShape.up ℤ)).app K) ≫
      (Functor.mapHomologicalComplexIdIso (SheafOfModules.{u} O)
        (ComplexShape.up ℤ)).hom.app K
  let KU := ((jStar U O ⋙ jShriek U O).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hid : q.map ((Functor.mapHomologicalComplexIdIso (SheafOfModules.{u} O)
      (ComplexShape.up ℤ)).hom.app K) = 𝟙 (q.obj K) := by
    show q.map (𝟙 K) = _
    exact q.map_id K
  have hc : aU.app (q.obj K) ≫ c.app (DerivedCategory.Qh.obj (q.obj K)) =
      DerivedCategory.Qh.map (q.map f) := by
    have h := congr_app (derivedExtensionRestrictionCounit_fac O U DU aU) (q.obj K)
    change aU.app (q.obj K) ≫ c.app (DerivedCategory.Qh.obj (q.obj K)) =
      DerivedCategory.Qh.map
        (q.map ((NatTrans.mapHomologicalComplex (jShriekAdjunction U O).counit
          (ComplexShape.up ℤ)).app K) ≫ 𝟙 (q.obj K)) at h
    rw [← hid, ← q.map_comp] at h
    exact h
  have hn : DU.map (e.hom.app K) ≫ c.app (DerivedCategory.Q.obj K) =
      c.app (DerivedCategory.Qh.obj (q.obj K)) ≫ e.hom.app K :=
    c.naturality (e.hom.app K)
  have he : DerivedCategory.Q.map f ≫ e.inv.app K =
      e.inv.app KU ≫ DerivedCategory.Qh.map (q.map f) := e.inv.naturality f
  show (e.inv.app KU ≫ aU.app (q.obj K) ≫ DU.map (e.hom.app K)) ≫
      c.app (DerivedCategory.Q.obj K) = DerivedCategory.Q.map f
  exact (comp_eq_of_three_squares (ι' := e.inv.app K) (α' := 𝟙 _) (δ' := e.hom.app K)
    (hc.trans (Category.comp_id _).symm) hn he).trans (by simp)

-- Comparing the degreewise and derived functors requires extra elaboration.
/-- **Stacks 08BU.** For a cover by two open subspaces, extension by zero of the
restrictions to their intersection and to the two opens forms a distinguished triangle,
naturally in the object of the unbounded derived category. -/
@[stacks 08BU "the whole statement: the distinguished triangle, for every choice of the three
derived functors `R(j_!j^*)` and their units — the degreewise one of Section 20.32 included — with
the two maps out of the intersection term pinned by the adjunction counits, the second with the
Mayer--Vietoris sign"]
public theorem distinguished_extensionRestriction_triangle {X : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (U V : Opens X) (hUV : U ⊔ V = ⊤)
    (DU DV DUV : DerivedCategory (SheafOfModules.{u} O) ⥤
      DerivedCategory (SheafOfModules.{u} O))
    (aU : homotopyExtensionRestriction O U ⟶ DerivedCategory.Qh ⋙ DU)
    (aV : homotopyExtensionRestriction O V ⟶ DerivedCategory.Qh ⋙ DV)
    (aUV : homotopyExtensionRestriction O (U ⊓ V) ⟶ DerivedCategory.Qh ⋙ DUV)
    [DU.IsRightDerivedFunctor aU
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [DV.IsRightDerivedFunctor aV
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))]
    [DUV.IsRightDerivedFunctor aUV
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))] :
    ∃ (iU : DUV ⟶ DU) (iV : DUV ⟶ DV)
      (δ : 𝟭 (DerivedCategory (SheafOfModules.{u} O)) ⟶
        DUV ⋙ shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)),
      (iU ≫ derivedExtensionRestrictionCounit O U DU aU =
          derivedExtensionRestrictionCounit O (U ⊓ V) DUV aUV) ∧
      (iV ≫ derivedExtensionRestrictionCounit O V DV aV =
          -derivedExtensionRestrictionCounit O (U ⊓ V) DUV aUV) ∧
      (∀ E, Triangle.mk (biprod.lift (iU.app E) (iV.app E))
        (biprod.desc ((derivedExtensionRestrictionCounit O U DU aU).app E)
          ((derivedExtensionRestrictionCounit O V DV aV).app E)) (δ.app E) ∈
          distTriang (DerivedCategory (SheafOfModules.{u} O))) :=
  by
    let iU := derivedExtensionRestrictionInclusion O (U ⊓ V) U inf_le_left
      DUV DU aUV aU
    let iV := -derivedExtensionRestrictionInclusion O (U ⊓ V) V inf_le_right
      DUV DV aUV aV
    let δ := derivedExtensionRestrictionConnecting O U V hUV DUV aUV
    refine ⟨iU, iV, δ, ?_, ?_, ?_⟩
    · exact derivedExtensionRestrictionInclusion_counit O (U ⊓ V) U inf_le_left
        DUV DU aUV aU
    · exact derivedNegExtensionRestrictionInclusion_counit O (U ⊓ V) V inf_le_right
        DUV DV aUV aV
    · intro E
      let W := U ⊓ V
      let FU := jStar U O ⋙ jShriek U O
      let FV := jStar V O ⋙ jShriek V O
      let FW := jStar W O ⋙ jShriek W O
      obtain ⟨_, _, _⟩ := extensionRestriction_additive_and_exact O U
      obtain ⟨_, _, _⟩ := extensionRestriction_additive_and_exact O V
      obtain ⟨_, _, _⟩ := extensionRestriction_additive_and_exact O W
      have := extensionRestriction_isRightDerivedFunctor O U
      have := extensionRestriction_isRightDerivedFunctor O V
      have := extensionRestriction_isRightDerivedFunctor O W
      let K : CochainComplex (SheafOfModules.{u} O) ℤ := E.1.obj
      have hE : DerivedCategory.Q.obj K = E := rfl
      clear_value K
      subst E
      let E := DerivedCategory.Q.obj K
      let S := extensionRestrictionCoverComplexShortComplex O U V K
      let hS := extensionRestrictionCoverComplexShortComplex_shortExact O U V hUV K
      let T₀ := DerivedCategory.triangleOfSES hS
      let A := (FU.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
      let B := (FV.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
      let eU := derivedExtensionRestrictionComparisonIso O U DU aU K
      let eV := derivedExtensionRestrictionComparisonIso O V DV aV K
      let eW := derivedExtensionRestrictionComparisonIso O W DUV aUV K
      let e₁ : T₀.obj₁ ≅ DUV.obj E := eW
      let e₂ : T₀.obj₂ ≅ DU.obj E ⊞ DV.obj E :=
        (additiveBiprodComparisonIso DerivedCategory.Q A B).trans
          (biprod.mapIso eU eV)
      let e₃ : T₀.obj₃ ≅ E := Iso.refl E
      let T := Triangle.mk (biprod.lift (iU.app E) (iV.app E))
        (biprod.desc ((derivedExtensionRestrictionCounit O U DU aU).app E)
          ((derivedExtensionRestrictionCounit O V DV aV).app E)) (δ.app E)
      refine isomorphic_distinguished _
        (DerivedCategory.triangleOfSES_distinguished hS) T
        (Triangle.isoMk T₀ T e₁ e₂ e₃ ?_ ?_ ?_).symm
      · let fU := (NatTrans.mapHomologicalComplex
          (extensionRestrictionInclusion O W U inf_le_left) (ComplexShape.up ℤ)).app K
        let fV := (NatTrans.mapHomologicalComplex
          (extensionRestrictionInclusion O W V inf_le_right) (ComplexShape.up ℤ)).app K
        show DerivedCategory.Q.map (biprod.lift fU (-fV)) ≫
            (Functor.biprodComparison DerivedCategory.Q A B ≫ biprod.map eU.hom eV.hom) =
          eW.hom ≫ biprod.lift (iU.app E) (iV.app E)
        refine map_biprod_lift_compatibility DerivedCategory.Q fU (-fV)
          eU.hom eV.hom eW.hom (iU.app E) (iV.app E) ?_ ?_
        · exact (derivedExtensionRestrictionComparisonIso_hom_inclusion
            O W U inf_le_left DUV DU aUV aU K).symm
        · show DerivedCategory.Q.map (-fV) ≫ eV.hom = eW.hom ≫
            (-((derivedExtensionRestrictionInclusion O W V inf_le_right
              DUV DV aUV aV).app E))
          simpa only [Functor.map_neg, Preadditive.neg_comp, Preadditive.comp_neg] using
            congrArg Neg.neg (derivedExtensionRestrictionComparisonIso_hom_inclusion
              O W V inf_le_right DUV DV aUV aV K).symm
      · let cU := ((NatTrans.mapHomologicalComplex (jShriekAdjunction U O).counit
          (ComplexShape.up ℤ)).app K) ≫
          (Functor.mapHomologicalComplexIdIso (SheafOfModules.{u} O)
            (ComplexShape.up ℤ)).hom.app K
        let cV := ((NatTrans.mapHomologicalComplex (jShriekAdjunction V O).counit
          (ComplexShape.up ℤ)).app K) ≫
          (Functor.mapHomologicalComplexIdIso (SheafOfModules.{u} O)
            (ComplexShape.up ℤ)).hom.app K
        show DerivedCategory.Q.map (biprod.desc cU cV) ≫ 𝟙 E =
          (Functor.biprodComparison DerivedCategory.Q A B ≫ biprod.map eU.hom eV.hom) ≫
            biprod.desc ((derivedExtensionRestrictionCounit O U DU aU).app E)
              ((derivedExtensionRestrictionCounit O V DV aV).app E)
        refine map_biprod_desc_compatibility DerivedCategory.Q cU cV
          eU.hom eV.hom (𝟙 E)
          ((derivedExtensionRestrictionCounit O U DU aU).app E)
          ((derivedExtensionRestrictionCounit O V DV aV).app E) ?_ ?_
        · exact (Category.comp_id _).trans
            (derivedExtensionRestrictionComparisonIso_hom_counit O U DU aU K).symm
        · exact (Category.comp_id _).trans
            (derivedExtensionRestrictionComparisonIso_hom_counit O V DV aV K).symm
      · let q := HomotopyCategory.quotient (SheafOfModules.{u} O) (ComplexShape.up ℤ)
        let qe := DerivedCategory.quotientCompQhIso (SheafOfModules.{u} O)
        let sh := shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)
        let factors := Functor.mapHomotopyCategoryFactors FW (ComplexShape.up ℤ)
        let KW := (FW.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
        let a₁ := qe.inv.app KW
        let a₂ := DerivedCategory.Qh.map
          (q.map (eqToHom (extensionRestrictionCoverComplexShortComplex_X1 O U V K)))
        let a₃ := DerivedCategory.Qh.map (factors.inv.app K)
        let a₄ := aUV.app (q.obj K)
        let a₅ := DUV.map (qe.hom.app K)
        show DerivedCategory.triangleOfSESδ hS ≫ sh.map eW.hom =
          𝟙 (DerivedCategory.Q.obj K) ≫
            (derivedExtensionRestrictionConnecting O U V hUV DUV aUV).app
              (DerivedCategory.Q.obj K)
        -- The connecting transformation is the lift of
        -- `extensionRestrictionCoverConnectingHomotopy`, and both `Localization.Lifting`
        -- isomorphisms occurring in `Localization.liftNatTrans_app` are identities here, so at
        -- `Q.obj K` the lift is the homotopy-level transformation itself.
        have hlift : (derivedExtensionRestrictionConnecting O U V hUV DUV aUV).app
            (DerivedCategory.Q.obj K) =
            (extensionRestrictionCoverConnectingHomotopy O U V hUV DUV aUV).app K := by
          unfold derivedExtensionRestrictionConnecting
          rw [Localization.liftNatTrans_app]
          exact (Category.id_comp _).trans (Category.comp_id _)
        have hcomp : (extensionRestrictionCoverConnectingHomotopy O U V hUV DUV aUV).app K =
            DerivedCategory.Q.map (eqToHom
                (extensionRestrictionCoverComplexShortComplex_X3 O U V K).symm) ≫
              DerivedCategory.triangleOfSESδ hS ≫
                sh.map a₁ ≫ sh.map a₂ ≫ sh.map a₃ ≫ sh.map a₄ ≫ sh.map a₅ := rfl
        -- The two `eqToHom`s and the factorisation isomorphism of
        -- `Functor.mapHomotopyCategoryFactors` are identities, being induced by equalities
        -- between definitionally equal complexes; each is recognised by term elaboration,
        -- which unifies at default transparency where `rw` and `simp` do not.
        have h₀ : DerivedCategory.Q.map (eqToHom
            (extensionRestrictionCoverComplexShortComplex_X3 O U V K).symm) =
            𝟙 (DerivedCategory.Q.obj K) := DerivedCategory.Q.map_id K
        have h₂ : a₂ = 𝟙 _ := by
          show DerivedCategory.Qh.map (q.map (eqToHom
            (extensionRestrictionCoverComplexShortComplex_X1 O U V K))) = _
          have hq : q.map (eqToHom
              (extensionRestrictionCoverComplexShortComplex_X1 O U V K)) =
              𝟙 (q.obj (extensionRestrictionCoverComplexShortComplex O U V K).X₁) :=
            q.map_id _
          rw [hq]
          exact DerivedCategory.Qh.map_id _
        have h₃ : a₃ = 𝟙 _ := by
          show DerivedCategory.Qh.map (factors.inv.app K) = _
          exact DerivedCategory.Qh.map_id _
        have hs₂ : sh.map a₂ = 𝟙 _ := by rw [h₂]; exact sh.map_id _
        have hs₃ : sh.map a₃ = 𝟙 _ := by rw [h₃]; exact sh.map_id _
        have hsplit : sh.map a₁ ≫ sh.map a₄ ≫ sh.map a₅ = sh.map eW.hom := by
          show sh.map a₁ ≫ sh.map a₄ ≫ sh.map a₅ = sh.map (a₁ ≫ a₄ ≫ a₅)
          exact ((sh.map_comp a₁ (a₄ ≫ a₅)).trans
            (congrArg (sh.map a₁ ≫ ·) (sh.map_comp a₄ a₅))).symm
        have hcomp' : (extensionRestrictionCoverConnectingHomotopy O U V hUV DUV aUV).app K =
            DerivedCategory.triangleOfSESδ hS ≫
              sh.map a₁ ≫ sh.map a₂ ≫ sh.map a₃ ≫ sh.map a₄ ≫ sh.map a₅ :=
          hcomp.trans ((congrArg (fun z => z ≫ (DerivedCategory.triangleOfSESδ hS ≫
            sh.map a₁ ≫ sh.map a₂ ≫ sh.map a₃ ≫ sh.map a₄ ≫ sh.map a₅)) h₀).trans
            (Category.id_comp _))
        rw [Category.id_comp, hlift, hcomp']
        calc DerivedCategory.triangleOfSESδ hS ≫ sh.map eW.hom
            = DerivedCategory.triangleOfSESδ hS ≫
                sh.map a₁ ≫ sh.map a₄ ≫ sh.map a₅ :=
              congrArg (DerivedCategory.triangleOfSESδ hS ≫ ·) hsplit.symm
          _ = DerivedCategory.triangleOfSESδ hS ≫
                sh.map a₁ ≫ 𝟙 _ ≫ sh.map a₄ ≫ sh.map a₅ :=
              congrArg (fun z => DerivedCategory.triangleOfSESδ hS ≫ sh.map a₁ ≫ z)
                (Category.id_comp (sh.map a₄ ≫ sh.map a₅)).symm
          _ = DerivedCategory.triangleOfSESδ hS ≫
                sh.map a₁ ≫ sh.map a₃ ≫ sh.map a₄ ≫ sh.map a₅ :=
              congrArg (fun z => DerivedCategory.triangleOfSESδ hS ≫ sh.map a₁ ≫
                z ≫ sh.map a₄ ≫ sh.map a₅) hs₃.symm
          _ = DerivedCategory.triangleOfSESδ hS ≫
                sh.map a₁ ≫ 𝟙 _ ≫ sh.map a₃ ≫ sh.map a₄ ≫ sh.map a₅ :=
              congrArg (fun z => DerivedCategory.triangleOfSESδ hS ≫ sh.map a₁ ≫ z)
                (Category.id_comp (sh.map a₃ ≫ sh.map a₄ ≫ sh.map a₅)).symm
          _ = DerivedCategory.triangleOfSESδ hS ≫
                sh.map a₁ ≫ sh.map a₂ ≫ sh.map a₃ ≫ sh.map a₄ ≫ sh.map a₅ :=
              congrArg (fun z => DerivedCategory.triangleOfSESδ hS ≫ sh.map a₁ ≫
                z ≫ sh.map a₃ ≫ sh.map a₄ ≫ sh.map a₅) hs₂.symm

end Stacks.ExtensionByZero
