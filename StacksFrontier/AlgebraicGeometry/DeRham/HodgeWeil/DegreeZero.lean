module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.SquareZeroExtensionDerivedHom
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.CupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.SectionsOnASubsingletonSpace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObjectDegreeZero
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence
public import StacksFrontier.AlgebraicGeometry.Variety.Tangent.RelativeEmbeddingDimensionForms
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricAlgebraConstruction.DegreeZero.Basic

/-!
# Hodge cohomology in degree zero and of the point

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a ringed space `X`, and let
`H^q(X, Ω^p)` be the Hodge cohomology groups, the cohomology of the derived global sections of the
sheaf `Ω^p` of relative differential `p`-forms placed in degree `0`. This file records the facts
about these groups in low degrees that axioms (A5) and (A8) of Weil cohomology theories
(Section 0FID) ask of Hodge cohomology in Remark 0FWE:

* `H^q(X, Ω^p) = 0` for `q < 0`;
* `H^0(X, Ω^p) = Γ(X, Ω^p)`, the class of a global form giving the identification, and so
  `H^0(X, Ω^0) = Γ(X, 𝒪_X)` through `r ↦ r · 1`;
* if `X` has at most one point, `H^q(X, Ω^p) = 0` for `q ≠ 0`, since global sections are then
  exact;
* if `f : X ⟶ S` is smooth of relative dimension `e`, then `Ω^p_{X/S} = 0`, hence
  `H^q(X, Ω^p_{X/S}) = 0`, for `p > e`.

For `f : X ⟶ Spec k` an isomorphism, with `k` a field, these combine into the Hodge half of
`H^*(Spec k) = k`: `H^q(X, Ω^p_{X/k}) = 0` unless `p = q = 0`, and `k ⟶ H^0(X, Ω^0_{X/k})` is
bijective.

## Main definitions

* `Stacks.HodgeWeil.globalForms`: the module `Γ(X, Ω^p)` of global `p`-forms.
* `Stacks.HodgeWeil.hodgeSectionClass`: the class `Γ(X, Ω^p) ⟶ H^0(X, Ω^p)` of a global form.

## Main results

* `Stacks.HodgeWeil.isZero_hodgeCohomologyComponent_of_neg`: `H^q(X, Ω^p) = 0` for `q < 0`.
* `Stacks.HodgeWeil.isZero_hodgeCohomologyComponent_of_isZero`: `H^q(X, Ω^p) = 0` if `Ω^p = 0`.
* `Stacks.HodgeWeil.isZero_hodgeCohomologyComponent_of_subsingleton`: `H^q(X, Ω^p) = 0` for
  `q ≠ 0` when `X` has at most one point.
* `Stacks.HodgeWeil.isIso_hodgeSectionClass`, `Stacks.HodgeWeil.bijective_hodgeSectionClass`:
  `H^0(X, Ω^p) = Γ(X, Ω^p)`.
* `Stacks.HodgeWeil.bijective_hodgeSectionClass_smul_one`: `H^0(X, Ω^0) = Γ(X, 𝒪_X)`.
* `Stacks.HodgeWeil.isZero_hodgeCohomologyComponent_of_smoothOfRelativeDimension`:
  `H^q(X, Ω^p_{X/S}) = 0` for `p` above the relative dimension of a smooth morphism.
* `Stacks.HodgeWeil.isZero_hodgeCohomologyComponent_of_isIso` and
  `Stacks.HodgeWeil.bijective_hodgeSectionClass_of_isIso`: the Hodge cohomology of a scheme
  isomorphic over `k` to `Spec k` is `k`, in bidegree `(0, 0)`.

## Implementation notes

The class of a global form is defined through the unit `Γ(X, -) ⟶ RΓ(X, -)` of the derived
functor, and `Stacks.HodgeWeil.hodgeSectionClass_eq` identifies it with the comparison
`Γ(X, -) ⟶ R^0 Γ(X, -)`, which is invertible because global sections are left exact. On a space
with at most one point the source's appeal to Grothendieck's vanishing theorem (Tag 02UZ) is
replaced by the exactness of global sections there, which identifies `RΓ(X, -)` with `Γ(X, -)`.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FID](https://stacks.math.columbia.edu/tag/0FID)
* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.SheafOfModules (hodgeCohomologyComponent deRhamTerm baseRingedSpace)
open Stacks.Cohomology.DerivedSectionsLeray (sectionsOverOpen derivedSectionsOverOpen
  derivedSectionsOverOpenUnit homotopySectionsOverOpen)

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing
  AlgebraicGeometry.SheafedSpace.sheaf AlgebraicGeometry.SheafOfModules.baseRingedSpace
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

section Single

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- A zero object placed in degree `0` of the derived category lives in every degree `≥ n`. -/
private theorem isGE_singleFunctor_obj_of_isZero {M : C} (h : IsZero M) (n : ℤ) :
    ((DerivedCategory.singleFunctor C 0).obj M).IsGE n :=
  DerivedCategory.TStructure.t.isGE_of_isZero (Functor.map_isZero _ h) n

end Single

section RingedSpace

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier)
    (AlgebraicGeometry.SheafOfModules.moduleOfDifferentials.{u, u, u} φ))

/-- Derived global sections of sheaves of modules over the base ring sheaf carry an object living
in degrees `≥ n` to one living in degrees `≥ n`. -/
private theorem isGE_derivedSections_obj
    (K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A))))
    (n : ℤ) (hK : K.IsGE n) :
    ((derivedSectionsOverOpen (baseRingedSpace A) ⊤).obj K).IsGE n :=
  Stacks.SmallDerivedCategory.isGE_obj_of_isGE (sectionsOverOpen (baseRingedSpace A) ⊤)
    (derivedSectionsOverOpen (baseRingedSpace A) ⊤)
    (derivedSectionsOverOpenUnit (baseRingedSpace A) ⊤)
    (fun I hI =>
      (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
      (homotopySectionsOverOpen (baseRingedSpace A) ⊤)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective
        (baseRingedSpace A))).2 DerivedCategory.Qh _ _ I hI) K n hK

/-- **`H^q(X, Ω^p) = 0` for `q < 0`.** -/
theorem isZero_hodgeCohomologyComponent_of_neg (p : ℕ) {q : ℤ} (hq : q < 0) :
    IsZero (hodgeCohomologyComponent B p q) := by
  have hK : ((DerivedCategory.singleFunctor
      (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A))) 0).obj
        (deRhamTerm (X := X) B p)).IsGE 0 := by
    let e := (DerivedCategory.singleFunctorIsoCompQ
      (_root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A))) 0).app
        (deRhamTerm (X := X) B p)
    dsimp only [Functor.comp_obj] at e
    exact DerivedCategory.TStructure.t.isGE_of_iso e.symm 0
  exact DerivedCategory.isZero_of_isGE (hX := isGE_derivedSections_obj _ 0 hK) _ 0 q hq

/-- **`H^q(X, Ω^p) = 0` when `Ω^p = 0`**, in every degree `q`. -/
theorem isZero_hodgeCohomologyComponent_of_isZero {p : ℕ} (h : IsZero (deRhamTerm (X := X) B p))
    (q : ℤ) : IsZero (hodgeCohomologyComponent B p q) := by
  have hK := isGE_singleFunctor_obj_of_isZero
    (C := _root_.SheafOfModules.{u} (structureSheafRing (baseRingedSpace A))) h (q + 1)
  exact DerivedCategory.isZero_of_isGE (hX := isGE_derivedSections_obj _ (q + 1) hK) _ (q + 1) q
    (by omega)

/-- **`H^q(X, Ω^p) = 0` for `q ≠ 0` on a space with at most one point**: global sections are exact
there, so derived global sections are global sections, and the cohomology of a module placed in
degree `0` vanishes outside degree `0`. -/
theorem isZero_hodgeCohomologyComponent_of_subsingleton [Subsingleton X.carrier] (p : ℕ) {q : ℤ}
    (hq : q ≠ 0) : IsZero (hodgeCohomologyComponent B p q) := by
  have : Subsingleton (baseRingedSpace A).carrier := ‹Subsingleton X.carrier›
  have : PreservesFiniteLimits (sectionsOverOpen (baseRingedSpace A) ⊤) :=
    ⟨fun _ _ _ ↦ _root_.SheafOfModules.evaluationPreservesLimitsOfShape _ _ _⟩
  let F := sectionsOverOpen (baseRingedSpace A) ⊤
  let M := deRhamTerm (X := X) B p
  let e : (derivedSectionsOverOpen (baseRingedSpace A) ⊤).obj
      ((DerivedCategory.singleFunctor _ 0).obj M) ≅
      (DerivedCategory.singleFunctor _ 0).obj (F.obj M) :=
    (Stacks.Cohomology.SubsingletonSections.derivedSectionsOverOpenIso
      (baseRingedSpace A) ⊤).app _ ≪≫ (F.mapDerivedCategorySingleFunctor 0).app M
  exact IsZero.of_iso (Stacks.SquareZeroExt.isZero_homology_singleFunctor _ hq)
    ((DerivedCategory.homologyFunctor _ q).mapIso e)

/-- The global sections `Γ(X, Ω^p)` of the sheaf of relative differential `p`-forms, as a module
over the ring of global sections of the base ring sheaf. -/
abbrev globalForms (p : ℕ) :
    ModuleCat.{u} ((AlgebraicGeometry.SheafOfModules.underlyingRingSheaf A).obj.obj (op ⊤)) :=
  (sectionsOverOpen (baseRingedSpace A) ⊤).obj (deRhamTerm (X := X) B p)

/-- **The class of a global `p`-form in `H^0(X, Ω^p)`.** A global section of `Ω^p` is a
degree-`0` cocycle of the global sections of `Ω^p` placed in degree `0`; its class there is
carried to `H^0(X, Ω^p)` by the unit `Γ(X, -) ⟶ RΓ(X, -)` of the derived global sections. -/
def hodgeSectionClass (p : ℕ) : globalForms B p ⟶ hodgeCohomologyComponent (X := X) B p 0 :=
  Stacks.DerivedFunctor.singleZeroClass (sectionsOverOpen (baseRingedSpace A) ⊤)
      (deRhamTerm (X := X) B p) ≫
    (DerivedCategory.homologyFunctor _ ((0 : ℕ) : ℤ)).map
      ((DerivedCategory.quotientCompQhIso _).inv.app _) ≫
    (DerivedCategory.homologyFunctor _ ((0 : ℕ) : ℤ)).map
      ((derivedSectionsOverOpenUnit (baseRingedSpace A) ⊤).app
        ((HomotopyCategory.singleFunctor _ 0).obj (deRhamTerm (X := X) B p))) ≫
    (DerivedCategory.homologyFunctor _ ((0 : ℕ) : ℤ)).map
      ((derivedSectionsOverOpen (baseRingedSpace A) ⊤).map
        ((DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app (deRhamTerm (X := X) B p)))

/-- The class map of global `p`-forms is the comparison of `R^0 Γ(X, -)` with `Γ(X, -)` followed by
the identification of `H^0(X, Ω^p)` with `R^0 Γ(X, Ω^p)`. -/
theorem hodgeSectionClass_eq (p : ℕ) :
    hodgeSectionClass B p =
      (sectionsOverOpen (baseRingedSpace A) ⊤).toRightDerivedZero.app (deRhamTerm (X := X) B p) ≫
        (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleIso
          (sectionsOverOpen (baseRingedSpace A) ⊤) (derivedSectionsOverOpen (baseRingedSpace A) ⊤)
          (derivedSectionsOverOpenUnit (baseRingedSpace A) ⊤)
          (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective
            (baseRingedSpace A)) (deRhamTerm (X := X) B p) 0).inv :=
  (Stacks.DerivedFunctor.toRightDerivedZero_comp_homologyTotalRightDerivedSingleIso_inv
    (sectionsOverOpen (baseRingedSpace A) ⊤) (derivedSectionsOverOpen (baseRingedSpace A) ⊤)
    (derivedSectionsOverOpenUnit (baseRingedSpace A) ⊤)
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective
      (baseRingedSpace A)) (deRhamTerm (X := X) B p)).symm

/-- **`H^0(X, Ω^p) = Γ(X, Ω^p)`**: the class map of global `p`-forms is an isomorphism, global
sections being left exact. -/
instance isIso_hodgeSectionClass (p : ℕ) : IsIso (hodgeSectionClass B p) := by
  have : PreservesFiniteLimits (sectionsOverOpen (baseRingedSpace A) ⊤) :=
    ⟨fun _ _ _ ↦ _root_.SheafOfModules.evaluationPreservesLimitsOfShape _ _ _⟩
  rw [hodgeSectionClass_eq]
  infer_instance

/-- **`H^0(X, Ω^p) = Γ(X, Ω^p)`**, element-wise: every class in `H^0(X, Ω^p)` is the class of a
unique global `p`-form. -/
theorem bijective_hodgeSectionClass (p : ℕ) : Function.Bijective (hodgeSectionClass B p) :=
  ConcreteCategory.bijective_of_isIso _

/-- **`H^0(X, Ω^0_{X/S}) = Γ(X, 𝒪_X)`**: the map `Γ(X, 𝒪_X) ⟶ H^0(X, Ω^0)` sending `r` to the
class of the degree-zero form `r · 1` is bijective. -/
theorem bijective_hodgeSectionClass_smul_one :
    Function.Bijective (fun r : X.sheaf.obj.obj (op ⊤) =>
      hodgeSectionClass B 0 (show globalForms B 0 from r • B.exterior.one.eval (op ⊤))) :=
  (bijective_hodgeSectionClass B 0).comp
    (_root_.SheafOfModules.GradedAlgebra.bijective_smul_one_of_pieceZeroIsoUnit B.exterior
      B.exteriorPieceZeroIsoUnit B.exteriorPieceZeroIsoUnit_one (op ⊤))

end RingedSpace

section Scheme

/-- **`Ω^p_{X/S} = 0`, hence `H^q(X, Ω^p_{X/S}) = 0`, for `p` above the relative dimension** of a
morphism `f : X ⟶ S` smooth of relative dimension `e`, in every degree `q`. -/
theorem isZero_hodgeCohomologyComponent_of_smoothOfRelativeDimension {X S : Scheme.{u}}
    (f : X ⟶ S) (e : ℕ) [SmoothOfRelativeDimension e f] {p : ℕ} (hp : e < p) (q : ℤ) :
    IsZero (hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q) :=
  isZero_hodgeCohomologyComponent_of_isZero _
    ((_root_.SheafOfModules.restrictScalars _).map_isZero
      (Scheme.Hom.isZero_relativeDifferentialForms_of_smoothOfRelativeDimension f e p hp)) q

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k)) [IsIso f]

/-- **The Hodge cohomology of a model of the point vanishes outside bidegree `(0, 0)`**: for
`f : X ⟶ Spec k` an isomorphism, `H^q(X, Ω^p_{X/k}) = 0` unless `p = q = 0`. -/
theorem isZero_hodgeCohomologyComponent_of_isIso {p : ℕ} {q : ℤ} (h : p ≠ 0 ∨ q ≠ 0) :
    IsZero (hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) p q) := by
  rcases h with hp | hq
  · exact isZero_hodgeCohomologyComponent_of_smoothOfRelativeDimension f 0
      (Nat.pos_of_ne_zero hp) q
  · have : Subsingleton X := (Scheme.homeoOfIso (asIso f)).injective.subsingleton
    exact isZero_hodgeCohomologyComponent_of_subsingleton _ p hq

/-- **`H^0(X, Ω^0_{X/k}) = k`** for `f : X ⟶ Spec k` an isomorphism: the map `k ⟶ H^0(X, Ω^0)`
sending `c` to the class of the degree-zero form `f^♯(c) · 1` is bijective. -/
theorem bijective_hodgeSectionClass_of_isIso :
    Function.Bijective (fun c : k =>
      hodgeSectionClass (Scheme.Hom.deRhamAlgebras f) 0
        (show globalForms (Scheme.Hom.deRhamAlgebras f) 0 from
          (show X.sheaf.obj.obj (op ⊤) from
            (f.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) •
            (Scheme.Hom.deRhamAlgebras f).exterior.one.eval (op ⊤))) :=
  (bijective_hodgeSectionClass_smul_one (Scheme.Hom.deRhamAlgebras f)).comp
    ((ConcreteCategory.bijective_of_isIso (f.app ⊤)).comp
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv))

end Scheme

end Stacks.HodgeWeil

end
