module

public import StacksFrontier.CategoryTheory.Localization.NatTransMapDerivedCategory
public import
  StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExtensionByZeroBaseChangeDerived

/-!
# Transporting the counit compatibility of extension-by-zero base change to the derived level

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, let `U` be an open subspace of `Y`
and let `U' = f^{-1}U`.  The underived base change isomorphism
`Stacks.Cohomology.ExtensionByZeroBaseChange.modulePullbackExtensionRestrictionIso` is pinned down
by the counits `j_!j^* ⟶ 𝟭`
(`Stacks.Cohomology.ExtensionByZeroBaseChange.modulePullbackExtensionRestrictionIso_hom_counit`).
This file carries that compatibility up to the unbounded homotopy category: the isomorphism
`Stacks.Cohomology.ExtensionByZeroBaseChangeDerived.extensionRestrictionHomotopyPullbackIso`
followed by the derived counit of `j_{U',!} ⊣ j_{U'}^*` is the degreewise pullback of the
homotopy-category counit of `j_{U,!} ⊣ j_U^*`.

## Main results

* `CategoryTheory.NatTrans.mapDerivedCategory_factorsh_hom`: the derived form of a
  transformation of exact functors agrees, on the image of `DerivedCategory.Qh`, with its
  homotopy-category form, read through `CategoryTheory.Functor.mapDerivedCategoryFactorsh`.
* `CategoryTheory.NatTrans.mapDerivedCategoryCompToId_app_Qh`: the same for the counit-shaped
  form `D(G) ⋙ D(F) ⟶ 𝟭`.
* `Stacks.Cohomology.ExtensionByZeroBaseChangeDerived.extensionRestrictionHomotopyCounit`: the
  counit compatibility of the base change isomorphism on homotopy categories.
* `extensionRestrictionHomotopyPullbackIso_hom_counit` in the same namespace: the counit
  compatibility of the base change isomorphism against the derived counit.

## Implementation notes

*Two forced coherence isomorphisms.*  The statement of the main result needs two canonical
isomorphisms that no reader would guess from the underived statement, both because the two
sides are otherwise not even composable.  First, `(G ⋙ F).mapDerivedCategory` is not definitionally
`G.mapDerivedCategory ⋙ F.mapDerivedCategory` — each is a separate lift through the localization —
which is why `Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso` exists at all;
`CategoryTheory.NatTrans.mapDerivedCategoryCompToId` is stated on the composite of the derived
functors while
`Stacks.Cohomology.ExtensionByZeroBaseChangeDerived.extensionRestrictionHomotopyPullbackIso` lands
on the derived functor of the composite, so that isomorphism mediates.  Second,
`CategoryTheory.NatTrans.mapHomotopyCategory` of a counit lands in
`(𝟭 _).mapHomotopyCategory _`, not in `𝟭 _`: the functor a `CategoryTheory.Quotient.lift` induces
is the identity on objects of the homotopy category but not on its morphisms, since an opaque
quotient morphism does not reduce, so `CategoryTheory.Functor.mapHomotopyCategoryIdIso` mediates
there.  Both are isomorphisms with no hypotheses, so a consumer can strip either one.

*Ten copies of one isomorphism.*  A comparison `(F ⋙ G).mapDerivedCategory ≅ F.mapDerivedCategory
⋙ G.mapDerivedCategory` is absent from Mathlib and has been built ten times in this library.
Public: `StacksFrontier/Topology/Sheaves/Cohomology/PerfectComplexes/Triangles.lean:123`,
`StacksFrontier/CategoryTheory/Sites/Cohomology/ModulesOnACategory/CartesianObjects.lean:107`,
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/PushforwardClosedImmersion.lean:98`,
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/ProperBaseChange/Basic.lean:170`, and the variant
`mapDerivedCategoryCompIsoOfNatIso` at
`StacksFrontier/CategoryTheory/Sites/Cohomology/ChaoticSite/DerivedChangeOfCoefficients.lean:181`.
Private: `StacksFrontier/Homology/DerivedComplete/CompleteRestrictScalarsEquivalence.lean:2136`,
`StacksFrontier/Homology/PseudoCoherent/Relative/Tower.lean:131`,
`StacksFrontier/Homology/PseudoCoherent/Relative/Localization.lean:348`,
`StacksFrontier/RingTheory/F6Sweep/LocalCohomologySupportSurjectivity.lean:766`,
`StacksFrontier/RingTheory/Dualizing/TrivialDuality.lean:381`.  The copy used here is the one in
`PerfectComplexes/Triangles.lean`, which is forced rather than chosen:
`CategoryTheory.NatTrans.mapDerivedCategoryCompToId` is *defined* from it, so no other copy would
let `CategoryTheory.NatTrans.mapDerivedCategoryCompToId_app` apply.  It also costs no import, being
already in the closure of
`StacksFrontier/CategoryTheory/Localization/NatTransMapDerivedCategory.lean`.

*Why the proofs are terms.*  `DerivedCategory.Qh` and `DerivedCategory.quotientCompQhIso` carry
`no_expose`, so `DerivedCategory.Qh.obj M` and `DerivedCategory.Q.obj M.as` are not interchangeable
even definitionally outside Mathlib, and a composite whose middle object is spelled two ways —
`(F.mapHomotopyCategory c ⋙ DerivedCategory.Qh).obj M` on one side and
`DerivedCategory.Qh.obj ((F.mapHomotopyCategory c).obj M)` on the other — is well typed but opaque
to `rw` and `simp`, whose matching runs below default transparency.  The chases below are therefore
`Eq.trans` and `congrArg` chains, where the conversion check runs at default transparency, and the
crossing between `DerivedCategory.Qh` and `DerivedCategory.Q` happens only through the
isomorphism `DerivedCategory.quotientCompQhIso`.  For the same reason an object of the homotopy
category is used as `M` with `M.as`, never destructured: destructuring replaces it by a
`CategoryTheory.Quotient` term, which leaves the goal ill-typed at `implicit` transparency and
stops `simp` outright.

## References

* [Stacks Project, Tag 00AB](https://stacks.math.columbia.edu/tag/00AB)
* [Stacks Project, Tag 08BU](https://stacks.math.columbia.edu/tag/08BU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction ExtensionByZeroModules
open Stacks.Cohomology.ExtensionByZeroBaseChange
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace CategoryTheory

universe v₁ v₂ u₁ u₂ w₁ w₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]

/-! ### The derived form of a transformation on the image of the homotopy category -/

/-- **The derived functor of `𝟭` is identified with `𝟭` by the homotopy-category comparison.**
On the image of `DerivedCategory.Qh` the isomorphism
`CategoryTheory.Functor.mapDerivedCategoryIdIso` is
`CategoryTheory.Functor.mapHomotopyCategoryIdIso` read through
`CategoryTheory.Functor.mapDerivedCategoryFactorsh`. -/
theorem Functor.mapDerivedCategoryIdIso_hom_app_Qh
    (M : HomotopyCategory C (ComplexShape.up ℤ)) :
    Functor.mapDerivedCategoryIdIso.hom.app (DerivedCategory.Qh.obj M) =
      (𝟭 C).mapDerivedCategoryFactorsh.hom.app M ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app M) := by
  simp [Functor.mapDerivedCategoryIdIso]

section

variable {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- **The derived form of a transformation of exact functors is its homotopy-category form on the
image of `DerivedCategory.Qh`.**  Conjugating by
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` turns
`CategoryTheory.NatTrans.mapDerivedCategory` at `DerivedCategory.Qh.obj M` into
`CategoryTheory.NatTrans.mapHomotopyCategory` at `M`. -/
theorem NatTrans.mapDerivedCategory_factorsh_hom (η : F ⟶ G)
    (M : HomotopyCategory C (ComplexShape.up ℤ)) :
    F.mapDerivedCategoryFactorsh.hom.app M ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory η (ComplexShape.up ℤ)).app M) =
      (NatTrans.mapDerivedCategory η).app (DerivedCategory.Qh.obj M) ≫
        G.mapDerivedCategoryFactorsh.hom.app M := by
  have hid : ∀ {Z : DerivedCategory D} {W : HomotopyCategory D (ComplexShape.up ℤ)}
      (g : Z ⟶ DerivedCategory.Qh.obj W), g ≫ DerivedCategory.Qh.map (𝟙 W) = g :=
    fun g => (congrArg (fun t => g ≫ t) (DerivedCategory.Qh.map_id _)).trans (Category.comp_id g)
  have hfac : ∀ (H : C ⥤ D) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H],
      H.mapDerivedCategoryFactorsh.hom.app M =
        H.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app M.as) ≫
          H.mapDerivedCategoryFactors.hom.app M.as ≫
            (DerivedCategory.quotientCompQhIso D).inv.app
              ((H.mapHomologicalComplex (ComplexShape.up ℤ)).obj M.as) :=
    fun H =>
    (H.mapDerivedCategoryFactorsh_hom_app M.as).trans
      (congrArg (fun t =>
          H.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app M.as) ≫
            H.mapDerivedCategoryFactors.hom.app M.as ≫ t)
        (hid ((DerivedCategory.quotientCompQhIso D).inv.app _)))
  have hF := hfac F
  have hG := hfac G
  have hq := DerivedCategory.quotientCompQhIso_inv_naturality
    ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app M.as)
  have hη := NatTrans.mapDerivedCategory_app_Qh_comp η M
  have key₁ : F.mapDerivedCategoryFactorsh.hom.app M ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory η (ComplexShape.up ℤ)).app M) =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app M.as) ≫
        F.mapDerivedCategoryFactors.hom.app M.as ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app M.as) ≫
          (DerivedCategory.quotientCompQhIso D).inv.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj M.as) :=
    (congrArg (fun t => t ≫ DerivedCategory.Qh.map
        ((NatTrans.mapHomotopyCategory η (ComplexShape.up ℤ)).app M)) hF).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun t =>
            F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app M.as) ≫ t)
            (Category.assoc _ _ _)).trans
          (congrArg (fun t =>
            F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app M.as) ≫
              F.mapDerivedCategoryFactors.hom.app M.as ≫ t) hq.symm)))
  have key₂ : (NatTrans.mapDerivedCategory η).app (DerivedCategory.Qh.obj M) ≫
        G.mapDerivedCategoryFactorsh.hom.app M =
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app M.as) ≫
        F.mapDerivedCategoryFactors.hom.app M.as ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app M.as) ≫
          (DerivedCategory.quotientCompQhIso D).inv.app
            ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj M.as) :=
    (congrArg (fun t =>
        (NatTrans.mapDerivedCategory η).app (DerivedCategory.Qh.obj M) ≫ t) hG).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ (G.mapDerivedCategoryFactors.hom.app M.as ≫
              (DerivedCategory.quotientCompQhIso D).inv.app
                ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj M.as))) hη).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun t =>
              F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app M.as) ≫ t)
              ((Category.assoc _ _ _).trans
                (congrArg (fun t => F.mapDerivedCategoryFactors.hom.app M.as ≫ t)
                  ((Category.assoc _ _ _).trans
                    (congrArg (fun t => DerivedCategory.Q.map
                        ((NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app M.as) ≫ t)
                      (Iso.inv_hom_id_app_assoc G.mapDerivedCategoryFactors M.as _)))))))))
  exact key₁.trans key₂.symm

end

section

variable (G : C ⥤ D) (F : D ⥤ C) [G.Additive] [PreservesFiniteLimits G]
  [PreservesFiniteColimits G] [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **The counit-shaped derived transformation is the homotopy-category counit on the image of
`DerivedCategory.Qh`.**  The counit form of
`CategoryTheory.NatTrans.mapDerivedCategory_factorsh_hom`: the two coherence isomorphisms
`Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso` and
`CategoryTheory.Functor.mapHomotopyCategoryIdIso` are what make the two sides composable. -/
theorem NatTrans.mapDerivedCategoryCompToId_app_Qh (η : G ⋙ F ⟶ 𝟭 C)
    (M : HomotopyCategory C (ComplexShape.up ℤ)) :
    (G ⋙ F).mapDerivedCategoryFactorsh.hom.app M ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory η (ComplexShape.up ℤ)).app M ≫
            (Functor.mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app M) =
      (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso G F).hom.app
          (DerivedCategory.Qh.obj M) ≫
        (NatTrans.mapDerivedCategoryCompToId G F η).app (DerivedCategory.Qh.obj M) := by
  have hA := NatTrans.mapDerivedCategory_factorsh_hom η M
  have hB := Functor.mapDerivedCategoryIdIso_hom_app_Qh (C := C) M
  have hC := NatTrans.mapDerivedCategoryCompToId_app G F η (DerivedCategory.Qh.obj M)
  have key₁ : (G ⋙ F).mapDerivedCategoryFactorsh.hom.app M ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory η (ComplexShape.up ℤ)).app M ≫
            (Functor.mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app M) =
      (NatTrans.mapDerivedCategory η).app (DerivedCategory.Qh.obj M) ≫
        Functor.mapDerivedCategoryIdIso.hom.app (DerivedCategory.Qh.obj M) :=
    (congrArg (fun t => (G ⋙ F).mapDerivedCategoryFactorsh.hom.app M ≫ t)
      (DerivedCategory.Qh.map_comp _ _)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun t => t ≫ DerivedCategory.Qh.map
            ((Functor.mapHomotopyCategoryIdIso C (ComplexShape.up ℤ)).hom.app M)) hA).trans
          ((Category.assoc _ _ _).trans
            (congrArg (fun t =>
              (NatTrans.mapDerivedCategory η).app (DerivedCategory.Qh.obj M) ≫ t) hB.symm))))
  have key₂ : (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso G F).hom.app
          (DerivedCategory.Qh.obj M) ≫
        (NatTrans.mapDerivedCategoryCompToId G F η).app (DerivedCategory.Qh.obj M) =
      (NatTrans.mapDerivedCategory η).app (DerivedCategory.Qh.obj M) ≫
        Functor.mapDerivedCategoryIdIso.hom.app (DerivedCategory.Qh.obj M) :=
    (congrArg (fun t =>
        (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso G F).hom.app
          (DerivedCategory.Qh.obj M) ≫ t) hC).trans
      (Iso.hom_inv_id_app_assoc
        (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso G F)
        (DerivedCategory.Qh.obj M) _)
  exact key₁.trans key₂.symm

end

end CategoryTheory

universe u

namespace Stacks.Cohomology.ExtensionByZeroBaseChangeDerived

/-! ### Base change on the homotopy categories -/

section Homotopy

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (U : Opens Y.carrier)

/-- **Extension by zero of a restriction commutes with pullback, degreewise on the unbounded
homotopy categories.**  The isomorphism
`Stacks.Cohomology.ExtensionByZeroBaseChange.modulePullbackExtensionRestrictionIso` read through
`CategoryTheory.Functor.mapHomotopyCategoryCompIso`. -/
def modulePullbackExtensionRestrictionHomotopyIso :
    (jStar U (structureSheafRing Y) ⋙ jShriek U (structureSheafRing Y)).mapHomotopyCategory
          (ComplexShape.up ℤ) ⋙
        (modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
          jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X)).mapHomotopyCategory
            (ComplexShape.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (modulePullbackExtensionRestrictionIso f U)
      (ComplexShape.up ℤ) ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl (modulePullback f ⋙
      (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
        jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X)))) (ComplexShape.up ℤ)).symm

/-- **The base change isomorphism on homotopy categories is compatible with the counits
`j_!j^* ⟶ 𝟭`.**  The homotopy-category form of
`Stacks.Cohomology.ExtensionByZeroBaseChange.modulePullbackExtensionRestrictionIso_hom_counit`,
of which it is the degreewise consequence. -/
theorem extensionRestrictionHomotopyCounit :
    (modulePullbackExtensionRestrictionHomotopyIso f U).hom ≫
        Functor.whiskerLeft ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ))
          (NatTrans.mapHomotopyCategory
              (jShriekAdjunction ((Opens.map f.hom.base).obj U) (structureSheafRing X)).counit
              (ComplexShape.up ℤ) ≫
            (Functor.mapHomotopyCategoryIdIso (SheafOfModules.{u} (structureSheafRing X))
              (ComplexShape.up ℤ)).hom) =
      Functor.whiskerRight
        (NatTrans.mapHomotopyCategory (jShriekAdjunction U (structureSheafRing Y)).counit
            (ComplexShape.up ℤ) ≫
          (Functor.mapHomotopyCategoryIdIso (SheafOfModules.{u} (structureSheafRing Y))
            (ComplexShape.up ℤ)).hom)
        ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)) := by
  ext N
  have key : (Functor.mapHomologicalComplexCompIso (modulePullbackExtensionRestrictionIso f U)
            (ComplexShape.up ℤ)).hom.app N.as ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (modulePullback f ⋙
            (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
              jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X))))
            (ComplexShape.up ℤ)).inv.app N.as ≫
          (NatTrans.mapHomologicalComplex
              (jShriekAdjunction ((Opens.map f.hom.base).obj U) (structureSheafRing X)).counit
              (ComplexShape.up ℤ)).app
            (((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).obj N.as) =
      ((modulePullback f).mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (jShriekAdjunction U (structureSheafRing Y)).counit
          (ComplexShape.up ℤ)).app N.as) := by
    refine HomologicalComplex.hom_ext _ _ fun i => ?_
    simpa using
      NatTrans.congr_app (modulePullbackExtensionRestrictionIso_hom_counit f U) (N.as.X i)
  have h := congrArg
    (HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)).map key
  simp only [Functor.map_comp] at h
  refine (congrArg (fun t => _ ≫ t) (Category.comp_id _)).trans ?_
  refine (Category.assoc _ _ _).trans (h.trans ?_)
  exact (congrArg ((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).map
    (Category.comp_id
      ((HomotopyCategory.quotient (SheafOfModules.{u} (structureSheafRing Y))
          (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (jShriekAdjunction U (structureSheafRing Y)).counit
          (ComplexShape.up ℤ)).app N.as)))).symm

end Homotopy

/-! ### The derived counit -/

attribute [local instance] HasDerivedCategory.standard

section Derived

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (U : Opens Y.carrier)

/-- **The derived base change isomorphism on the homotopy category is compatible with the
counits `j_!j^* ⟶ 𝟭`.**  Following
`Stacks.Cohomology.ExtensionByZeroBaseChangeDerived.extensionRestrictionHomotopyPullbackIso`
with the derived counit of `j_{U',!} ⊣ j_{U'}^*` gives the degreewise pullback of the
homotopy-category counit of `j_{U,!} ⊣ j_U^*`.

This is the transport to `K(𝒪_Y)` of
`Stacks.Cohomology.ExtensionByZeroBaseChange.modulePullbackExtensionRestrictionIso_hom_counit`. -/
theorem extensionRestrictionHomotopyPullbackIso_hom_counit :
    (extensionRestrictionHomotopyPullbackIso f U).hom ≫
        Functor.whiskerLeft (pullbackOnHomotopy f)
          ((Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso
              (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X))
              (jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X))).hom ≫
            NatTrans.mapDerivedCategoryCompToId
              (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X))
              (jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X))
              (jShriekAdjunction ((Opens.map f.hom.base).obj U) (structureSheafRing X)).counit) =
      Functor.whiskerRight
        (NatTrans.mapHomotopyCategory (jShriekAdjunction U (structureSheafRing Y)).counit
            (ComplexShape.up ℤ) ≫
          (Functor.mapHomotopyCategoryIdIso (SheafOfModules.{u} (structureSheafRing Y))
            (ComplexShape.up ℤ)).hom)
        (pullbackOnHomotopy f) := by
  ext K
  have hiso : (extensionRestrictionHomotopyPullbackIso f U).hom.app K =
      DerivedCategory.Qh.map
          ((modulePullbackExtensionRestrictionHomotopyIso f U).hom.app K) ≫
        (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
          jShriek ((Opens.map f.hom.base).obj U)
            (structureSheafRing X)).mapDerivedCategoryFactorsh.inv.app
          (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := by
    simp [extensionRestrictionHomotopyPullbackIso, modulePullbackExtensionRestrictionHomotopyIso]
  have hstar := NatTrans.mapDerivedCategoryCompToId_app_Qh
    (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X))
    (jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X))
    (jShriekAdjunction ((Opens.map f.hom.base).obj U) (structureSheafRing X)).counit
    (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  have hstep := NatTrans.congr_app (extensionRestrictionHomotopyCounit f U) K
  refine (congrArg (fun t =>
    (extensionRestrictionHomotopyPullbackIso f U).hom.app K ≫ t) hstar.symm).trans ?_
  rw [hiso]
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => DerivedCategory.Qh.map
    ((modulePullbackExtensionRestrictionHomotopyIso f U).hom.app K) ≫ t)
    (Iso.inv_hom_id_app_assoc
      (jStar ((Opens.map f.hom.base).obj U) (structureSheafRing X) ⋙
        jShriek ((Opens.map f.hom.base).obj U) (structureSheafRing X)).mapDerivedCategoryFactorsh
      (((modulePullback f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) _)).trans ?_
  exact (DerivedCategory.Qh.map_comp _ _).symm.trans (congrArg DerivedCategory.Qh.map hstep)

end Derived

end Stacks.Cohomology.ExtensionByZeroBaseChangeDerived

end
