module

public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.DeRhamCupProduct
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.WedgeMonoidalIdentities
public import StacksFrontier.AlgebraicGeometry.DeRham.DifferentialGradedAlgebra.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.RingedSiteDerivedAssociatorToTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeCupProductAssociativity
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeMultiplication
import StacksCore.Tactic.StacksAttribute

/-!
# The relative cup product on the derived direct image of the de Rham complex

Differential Graded Sheaves, Remark 0FU6: consider a commutative square of schemes

```
X --f--> Y
|p       |q
v        v
S --h--> T
```

Then `Ω^•_{X/S}` is a sheaf of differential graded `p⁻¹𝒪_S`-algebras, and the relative cup product
of Section 0FU3 is a map

`μ : Rf_*Ω^•_{X/S} ⊗^𝐋_{q⁻¹𝒪_T} Rf_*Ω^•_{X/S} ⟶ Rf_*Ω^•_{X/S}`

in `D(Y, q⁻¹𝒪_T)`, which is associative and recovers the cup product on cohomology.

The first sentence is `AlgebraicGeometry.SheafOfModules.deRhamDifferentialGradedAlgebra`.  This
file supplies the rest.

* `AlgebraicGeometry.SheafOfModules.deRhamDerivedMul`: the multiplication of the differential
  graded algebra `Ω^•` read in the derived category, `Ω^• ⊗^𝐋_A Ω^• ⟶ Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•`,
  with the wedge product of Tag 0FM2 as the second arrow.
  `summandValue_wedgeProduct_heq_mul` says that this wedge product is the multiplication of
  `deRhamDifferentialGradedAlgebra` on local pure tensors.  `deRhamDerivedMul_assoc` says the
  derived multiplication is associative; it comes from the associativity of the wedge product
  (`wedgeProductInt_assoc`, Tag 0FM5) through
  `Stacks.SheafOfModules.DerivedMonoidal.derivedMul_assoc`.
* `AlgebraicGeometry.SheafOfModules.deRhamRelativeCupProduct`: for any morphism of ringed spaces
  `F : (X, A) ⟶ (Y, 𝒪_Y)` out of the space ringed by the base sheaf `A`, this is the relative cup
  product of Tag 0B68 followed by `RF_*` of `deRhamDerivedMul`.  Its associativity
  (`deRhamRelativeCupProduct_assoc`) and its compatibility with the cup product of de Rham
  cohomology through the Leray identification (`lerayMap_deRhamRelativeCupProduct`) are the
  general statements of
  `StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.RelativeMultiplication`.
* `AlgebraicGeometry.Scheme.squareHom`: the morphism of ringed spaces
  `(X, p⁻¹𝒪_S) ⟶ (Y, q⁻¹𝒪_T)` of a commutative square.  Its ring map is `squareRingMap`, the
  adjoint of `𝒪_T ⟶ h_*𝒪_S ⟶ h_*p_*p⁻¹𝒪_S = q_*f_*p⁻¹𝒪_S`.  This is the map through which
  Section 0FU3 reads `f` as a morphism of ringed topoi `(Sh(X), p⁻¹𝒪_S) ⟶ (Sh(Y), q⁻¹𝒪_T)`.
* `AlgebraicGeometry.Scheme.deRhamRelativeCupProduct`,
  `AlgebraicGeometry.Scheme.deRhamRelativeCupProduct_assoc`,
  `AlgebraicGeometry.Scheme.lerayMap_deRhamRelativeCupProduct`: the three assertions of Tag 0FU6
  about `μ`, for the square.

## The statements, clause by clause

* "`μ : Rf_*Ω^• ⊗^𝐋_{q⁻¹𝒪_T} Rf_*Ω^• ⟶ Rf_*Ω^•` in `D(Y, q⁻¹𝒪_T)`": this is
  `Scheme.deRhamRelativeCupProduct w` for `w : f ≫ q = p ≫ h`.  It is a morphism in the derived
  category of sheaves of modules over the structure sheaf `q⁻¹𝒪_T` of
  `baseRingedSpace (q⁻¹𝒪_T)`.  Its source is the derived tensor product of Tag 06YU over that
  sheaf.
* "`μ` is associative": this is `Scheme.deRhamRelativeCupProduct_assoc w`,
  `(μ ⊗ 1) ≫ μ = α ≫ (1 ⊗ μ) ≫ μ`, where `α` is the associativity constraint of the derived
  tensor product (Tag 0FPB, `derivedAssociator`).
* "`μ` recovers the cup product on cohomology": this is
  `Scheme.lerayMap_deRhamRelativeCupProduct w`.  For `ξ, η` in the cohomology of `Rf_*Ω^•` on
  `Y`, the Leray identification `Hⁿ(Y, Rf_*Ω^•) = Hⁿ(X, Ω^•)` sends `Hⁱ⁺ʲ(RΓ(Y, μ))(ξ ∪ η)` to the
  cup product `deRhamCohomologyCup` (Tag 0FM3) of the images of `ξ` and `η`.

## References

* [Stacks Project, Tag 0FU6](https://stacks.math.columbia.edu/tag/0FU6)
* [Stacks Project, Section 0FU3](https://stacks.math.columbia.edu/tag/0FU3)
* [Stacks Project, Tag 0B68](https://stacks.math.columbia.edu/tag/0B68)
* [Stacks Project, Tag 0FP4](https://stacks.math.columbia.edu/tag/0FP4)
* [Stacks Project, Tag 0FM3](https://stacks.math.columbia.edu/tag/0FM3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open TopologicalSpace ComplexShape
open Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedRelativeCupProduct (relativeCupProduct derivedAssociator)
open Stacks.Cohomology.LerayCupPairing
open Stacks.SheafOfModules.DerivedMonoidal (canonicalWhiskerRight canonicalWhiskerLeft
  canonicalAssociatorHom complexAssociatorHom toTensorHom)
open scoped TensorProduct CategoryTheory.Prod Stacks.Topology.SheafTensorAdditiveOnOpens

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose structureSheafRing

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] abelianModules hasSheafifyOpens wEqualsLocallyBijectiveOpens

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))
  (D : DeRhamDifferential B)

/-- **The multiplication of the de Rham complex in the derived category**,
`Ω^• ⊗^𝐋_A Ω^• ⟶ Tot(Ω^• ⊗_A Ω^•) ⟶ Ω^•` in `D(X, A)`: the canonical map from the derived to the
ordinary tensor product, followed by the wedge product of Tag 0FM2 extended to `ℤ`-indexed
complexes. -/
def deRhamDerivedMul :
    ((derivedTensorProductFunctor (baseRingedSpace A).sheaf).obj
        (moduleDerived (deRhamComplex B D))).obj (moduleDerived (deRhamComplex B D)) ⟶
      moduleDerived (deRhamComplex B D) :=
  (canonicalDerivedTensorProduct (baseRingedSpace A).sheaf).toTensor
      ((deRhamComplex B D).extend embeddingUpNat) ((deRhamComplex B D).extend embeddingUpNat) ≫
    DerivedCategory.Q.map (multiplicationInt (wedgeProduct B D))

/-- **The multiplication `deRhamDerivedMul` is that of the differential graded algebra
`Ω^•`** (the first assertion of Tag 0FU6, `deRhamDifferentialGradedAlgebra`): on the summand
`Ω^p ⊗ Ω^q` of the total complex the wedge product of Tag 0FM2 underlying `deRhamDerivedMul`
sends a local pure tensor `ω ⊗ η` to the product `ω · η` in the differential graded algebra. -/
@[stacks 0FU6 "the multiplication of mu is that of the differential graded algebra"]
theorem summandValue_wedgeProduct_heq_mul (p q : ℕ) (U : (Opens X.carrier)ᵒᵖ)
    (ω : (deRhamTerm B p).val.obj U) (η : (deRhamTerm B q).val.obj U)
    (x : ((deRhamDifferentialGradedAlgebra B D).complex.X (p : ℤ)).val.obj U)
    (y : ((deRhamDifferentialGradedAlgebra B D).complex.X (q : ℤ)).val.obj U)
    (hx : HEq x ω) (hy : HEq y η) :
    HEq (((deRhamDifferentialGradedAlgebra B D).mul (p : ℤ) (q : ℤ)).app U x y)
      (summandValue B D (wedgeProduct B D) p q U ω η) :=
  (deRhamDifferentialGradedAlgebra_mul B D p q U x y ω η hx hy).trans
    (heq_of_eq (summandValue_wedgeProduct B D p q U ω η).symm)

section Monoidal

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  Stacks.Cohomology.MonoidalComplexesOfModules.cochainComplexMonoidalCategory

attribute [local instance 100000]
  Stacks.SheafOfModules.DerivedMonoidal.monoidalCategoryStructComplexes

/-- The derived multiplication `Ω' ⊗^𝐋 Ω' ⟶ Ω'` in the pinned spelling of the monoidal derived
category of Tag 0FPT over the base ring sheaf `A`. -/
abbrev deRhamDerivedMulA :
    ((Stacks.SheafOfModules.DerivedMonoidal.derivedTensorBifunctorOfSite.{u + 1} A).obj
        (DerivedCategory.Q.obj ((deRhamComplex B D).extend embeddingUpNat))).obj
        (DerivedCategory.Q.obj ((deRhamComplex B D).extend embeddingUpNat)) ⟶
      DerivedCategory.Q.obj ((deRhamComplex B D).extend embeddingUpNat) :=
  Stacks.SheafOfModules.DerivedMonoidal.derivedMul.{u + 1} A (multiplicationInt (wedgeProduct B D))

/-- **The derived multiplication of the de Rham complex is associative**, in the curried
spelling of the monoidal derived category of Tag 0FPT. -/
theorem deRhamDerivedMulA_assoc :
    canonicalWhiskerRight.{u + 1} A (deRhamDerivedMulA B D)
        (DerivedCategory.Q.obj ((deRhamComplex B D).extend embeddingUpNat)) ≫
        deRhamDerivedMulA B D =
      canonicalAssociatorHom.{u + 1} A
          (DerivedCategory.Q.obj ((deRhamComplex B D).extend embeddingUpNat))
          (DerivedCategory.Q.obj ((deRhamComplex B D).extend embeddingUpNat))
          (DerivedCategory.Q.obj ((deRhamComplex B D).extend embeddingUpNat)) ≫
        canonicalWhiskerLeft.{u + 1} A
          (DerivedCategory.Q.obj ((deRhamComplex B D).extend embeddingUpNat))
          (deRhamDerivedMulA B D) ≫ deRhamDerivedMulA B D :=
  Stacks.SheafOfModules.DerivedMonoidal.derivedMul_assoc.{u + 1} A _ (wedgeProductInt_assoc B D)

end Monoidal

/-- **The derived multiplication of the de Rham complex is associative**, in the uncurried
spelling of the derived tensor bifunctor and with the associativity constraint
`derivedAssociator` of Tag 0FPB, the form
`Stacks.Cohomology.LerayCupPairing.relativeMultiplication_assoc` consumes. -/
theorem deRhamDerivedMul_assoc :
    (Functor.uncurry.obj (derivedTensorProductFunctor (baseRingedSpace A).sheaf)).map
        (deRhamDerivedMul B D ×ₘ 𝟙 (moduleDerived (deRhamComplex B D))) ≫ deRhamDerivedMul B D =
      derivedAssociator (baseRingedSpace A) (moduleDerived (deRhamComplex B D))
          (moduleDerived (deRhamComplex B D)) (moduleDerived (deRhamComplex B D)) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor (baseRingedSpace A).sheaf)).map
          (𝟙 (moduleDerived (deRhamComplex B D)) ×ₘ deRhamDerivedMul B D) ≫
          deRhamDerivedMul B D :=
  (congrArg (· ≫ deRhamDerivedMul B D) (uncurry_map_prod_id _ _ _)).trans
    ((deRhamDerivedMulA_assoc B D).trans
      (congrArg (fun g => derivedAssociator (baseRingedSpace A) _ _ _ ≫ g ≫ deRhamDerivedMul B D)
        (uncurry_map_id_prod _ _ _).symm))

variable {Y : RingedSpace.{u, u}} (F : baseRingedSpace A ⟶ Y)

/-- **The relative cup product of the de Rham complex**
`μ : Rf_*Ω^• ⊗^𝐋 Rf_*Ω^• ⟶ Rf_*(Ω^• ⊗^𝐋 Ω^•) ⟶ Rf_*Ω^•` in `D(Y, 𝒪_Y)`, for a morphism of ringed
spaces `F : (X, A) ⟶ (Y, 𝒪_Y)` out of the space `X` ringed by the base ring sheaf `A`: the
relative cup product of Tag 0B68 followed by `Rf_*` of the derived wedge multiplication
`deRhamDerivedMul`. -/
def deRhamRelativeCupProduct :
    ((derivedTensorProductFunctor Y.sheaf).obj
        ((derivedPushforward F).obj (moduleDerived (deRhamComplex B D)))).obj
        ((derivedPushforward F).obj (moduleDerived (deRhamComplex B D))) ⟶
      (derivedPushforward F).obj (moduleDerived (deRhamComplex B D)) :=
  relativeMultiplication F (deRhamDerivedMul B D)

/-- **The relative cup product of the de Rham complex is associative**:
`(μ ⊗ 1) ≫ μ = α ≫ (1 ⊗ μ) ≫ μ` in `D(Y, 𝒪_Y)`, for the associativity constraint `α` of
Tag 0FPB. -/
theorem deRhamRelativeCupProduct_assoc :
    (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
        (deRhamRelativeCupProduct B D F ×ₘ
          𝟙 ((derivedPushforward F).obj (moduleDerived (deRhamComplex B D)))) ≫
        deRhamRelativeCupProduct B D F =
      derivedAssociator Y ((derivedPushforward F).obj (moduleDerived (deRhamComplex B D)))
          ((derivedPushforward F).obj (moduleDerived (deRhamComplex B D)))
          ((derivedPushforward F).obj (moduleDerived (deRhamComplex B D))) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
          (𝟙 ((derivedPushforward F).obj (moduleDerived (deRhamComplex B D))) ×ₘ
            deRhamRelativeCupProduct B D F) ≫
          deRhamRelativeCupProduct B D F :=
  relativeMultiplication_assoc F _ (deRhamDerivedMul_assoc B D)

/-- **The relative cup product of the de Rham complex induces the cup product on de Rham
cohomology**: for `ξ ∈ Hⁱ(Y, Rf_*Ω^•)` and `η ∈ Hʲ(Y, Rf_*Ω^•)`, the Leray identification
`Hⁿ(Y, Rf_*Ω^•) = Hⁿ(X, Ω^•) = Hⁿ_{dR}` carries `Hⁱ⁺ʲ(RΓ(Y, μ))(ξ ∪ η)` to the cup product
`leray ξ ∪ leray η` of de Rham cohomology (Tag 0FM3, `deRhamCohomologyCup`). -/
theorem lerayMap_deRhamRelativeCupProduct (i j : ℤ)
    (ξ : cohomologyModule ((derivedPushforward F).obj (moduleDerived (deRhamComplex B D))) i)
    (η : cohomologyModule ((derivedPushforward F).obj (moduleDerived (deRhamComplex B D))) j) :
    lerayMap F (moduleDerived (deRhamComplex B D)) (i + j)
      (((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections Y).map
        (deRhamRelativeCupProduct B D F))).hom
        ((cupPairing (cupProductOnSpace Y) _ _ i j).hom (ξ ⊗ₜ η))) =
      deRhamCohomologyCup B D i j (lerayMap F (moduleDerived (deRhamComplex B D)) i ξ)
        (lerayMap F (moduleDerived (deRhamComplex B D)) j η) :=
  lerayMap_relativeMultiplication_cupPairing F _ i j ξ η

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] SheafOfModules.abelianModules SheafOfModules.hasSheafifyOpens
  SheafOfModules.wEqualsLocallyBijectiveOpens

variable {X Y S T : Scheme.{u}} {f : X ⟶ Y} {p : X ⟶ S} {q : Y ⟶ T} {h : S ⟶ T}

/-- For a commutative square `f ≫ q = p ≫ h`, the two ways of pushing a sheaf on `X` forward to
`T` agree. -/
theorem pushforward_pushforward_eq_of_comm (w : f ≫ q = p ≫ h)
    (N : TopCat.Sheaf CommRingCat.{u} X.carrier) :
    (TopCat.Sheaf.pushforward CommRingCat.{u} h.base).obj
        ((TopCat.Sheaf.pushforward CommRingCat.{u} p.base).obj N) =
      (TopCat.Sheaf.pushforward CommRingCat.{u} q.base).obj
        ((TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj N) := by
  have hb : p.base ≫ h.base = f.base ≫ q.base := by
    rw [← Scheme.Hom.comp_base, ← w, Scheme.Hom.comp_base]
  show (TopCat.Sheaf.pushforward CommRingCat.{u} (p.base ≫ h.base)).obj N =
    (TopCat.Sheaf.pushforward CommRingCat.{u} (f.base ≫ q.base)).obj N
  rw [hb]

/-- **The ring map of a commutative square** `f ≫ q = p ≫ h` of schemes,
`q⁻¹𝒪_T ⟶ f_*(p⁻¹𝒪_S)`: adjoint under `q⁻¹ ⊣ q_*` to the composite
`𝒪_T ⟶ h_*𝒪_S ⟶ h_*p_*p⁻¹𝒪_S = q_*f_*p⁻¹𝒪_S` of `h^♯` with `h_*` of the unit of `p⁻¹ ⊣ p_*`.
It is the map of sheaves of rings making `f` a morphism of ringed spaces
`(X, p⁻¹𝒪_S) ⟶ (Y, q⁻¹𝒪_T)` (Differential Graded Sheaves, Section 0FU3). -/
noncomputable def squareRingMap (w : f ≫ q = p ≫ h) :
    (TopCat.Sheaf.pullback CommRingCat.{u} q.base).obj T.sheaf ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} f.base).obj
        ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} q.base).homEquiv T.sheaf _).symm
    ((ObjectProperty.homMk h.c :
        T.sheaf ⟶ (TopCat.Sheaf.pushforward CommRingCat.{u} h.base).obj S.sheaf) ≫
      (TopCat.Sheaf.pushforward CommRingCat.{u} h.base).map
        ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} p.base).unit.app S.sheaf) ≫
      eqToHom (pushforward_pushforward_eq_of_comm w _))

/-- **The morphism of ringed spaces of a commutative square** `f ≫ q = p ≫ h` of schemes,
`(X, p⁻¹𝒪_S) ⟶ (Y, q⁻¹𝒪_T)`: the continuous map of `f` with the ring map `squareRingMap`. -/
noncomputable def squareHom (w : f ≫ q = p ≫ h) :
    SheafOfModules.baseRingedSpace (X := X.toRingedSpace)
        ((TopCat.Sheaf.pullback CommRingCat.{u} p.base).obj S.sheaf) ⟶
      SheafOfModules.baseRingedSpace (X := Y.toRingedSpace)
        ((TopCat.Sheaf.pullback CommRingCat.{u} q.base).obj T.sheaf) :=
  InducedCategory.homMk { base := f.base, c := (squareRingMap w).hom }

/-- The continuous map underlying `squareHom` is that of `f`. -/
theorem squareHom_base (w : f ≫ q = p ≫ h) : (squareHom w).hom.base = f.base :=
  rfl

/-- The relative de Rham complex `Ω^•_{X/S}` of `p`, extended by zero, in the derived category
`D(X, p⁻¹𝒪_S)` of sheaves of `p⁻¹𝒪_S`-modules. -/
noncomputable abbrev deRhamDerived (p : X ⟶ S) :=
  SheafOfModules.moduleDerived (SheafOfModules.deRhamComplex (Scheme.Hom.deRhamAlgebras p)
    (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras p)))

/-- **Stacks Project, Tag 0FU6: the relative cup product of a commutative square.**  For a
commutative square of schemes

```
X --f--> Y
|p       |q
v        v
S --h--> T
```

the relative cup product
`μ : Rf_*Ω^•_{X/S} ⊗^𝐋_{q⁻¹𝒪_T} Rf_*Ω^•_{X/S} ⟶ Rf_*Ω^•_{X/S}` in `D(Y, q⁻¹𝒪_T)`: the relative cup
product of Tag 0B68 for the morphism of ringed spaces `(X, p⁻¹𝒪_S) ⟶ (Y, q⁻¹𝒪_T)` of the square,
followed by `Rf_*` of the wedge multiplication `Ω^•_{X/S} ⊗^𝐋 Ω^•_{X/S} ⟶ Ω^•_{X/S}` of the
differential graded `p⁻¹𝒪_S`-algebra `Ω^•_{X/S}`. -/
@[stacks 0FU6 "the relative cup product mu of a commutative square"]
noncomputable def deRhamRelativeCupProduct (w : f ≫ q = p ≫ h) :
    ((derivedTensorProductFunctor (SheafOfModules.baseRingedSpace (X := Y.toRingedSpace)
          ((TopCat.Sheaf.pullback CommRingCat.{u} q.base).obj T.sheaf)).sheaf).obj
        ((derivedPushforward (squareHom w)).obj (deRhamDerived p))).obj
        ((derivedPushforward (squareHom w)).obj (deRhamDerived p)) ⟶
      (derivedPushforward (squareHom w)).obj (deRhamDerived p) :=
  SheafOfModules.deRhamRelativeCupProduct _ _ (squareHom w)

/-- **Stacks Project, Tag 0FU6: the relative cup product is associative**:
`(μ ⊗ 1) ≫ μ = α ≫ (1 ⊗ μ) ≫ μ` in `D(Y, q⁻¹𝒪_T)`, where `α` is the associativity constraint of
the derived tensor product (Tag 0FPB). -/
@[stacks 0FU6 "mu is associative"]
theorem deRhamRelativeCupProduct_assoc (w : f ≫ q = p ≫ h) :
    (Functor.uncurry.obj (derivedTensorProductFunctor
          (SheafOfModules.baseRingedSpace (X := Y.toRingedSpace)
            ((TopCat.Sheaf.pullback CommRingCat.{u} q.base).obj T.sheaf)).sheaf)).map
        (deRhamRelativeCupProduct w ×ₘ
          𝟙 ((derivedPushforward (squareHom w)).obj (deRhamDerived p))) ≫
        deRhamRelativeCupProduct w =
      derivedAssociator (SheafOfModules.baseRingedSpace (X := Y.toRingedSpace)
            ((TopCat.Sheaf.pullback CommRingCat.{u} q.base).obj T.sheaf))
          ((derivedPushforward (squareHom w)).obj (deRhamDerived p))
          ((derivedPushforward (squareHom w)).obj (deRhamDerived p))
          ((derivedPushforward (squareHom w)).obj (deRhamDerived p)) ≫
        (Functor.uncurry.obj (derivedTensorProductFunctor
            (SheafOfModules.baseRingedSpace (X := Y.toRingedSpace)
              ((TopCat.Sheaf.pullback CommRingCat.{u} q.base).obj T.sheaf)).sheaf)).map
          (𝟙 ((derivedPushforward (squareHom w)).obj (deRhamDerived p)) ×ₘ
            deRhamRelativeCupProduct w) ≫
          deRhamRelativeCupProduct w :=
  SheafOfModules.deRhamRelativeCupProduct_assoc _ _ (squareHom w)

/-- **Stacks Project, Tag 0FU6: the relative cup product induces the cup product on
cohomology.**  For `ξ ∈ Hⁱ(Y, Rf_*Ω^•_{X/S})` and `η ∈ Hʲ(Y, Rf_*Ω^•_{X/S})`, the Leray
identification `Hⁿ(Y, Rf_*Ω^•_{X/S}) = Hⁿ(X, Ω^•_{X/S}) = Hⁿ_{dR}(X/S)` carries
`Hⁱ⁺ʲ(RΓ(Y, μ))(ξ ∪ η)` -- the cup product on `Y` followed by `μ` -- to the cup product
`leray ξ ∪ leray η` on de Rham cohomology of Section 50.4 (Tag 0FM3, `deRhamCohomologyCup`). -/
@[stacks 0FU6 "mu induces the cup product on cohomology"]
theorem lerayMap_deRhamRelativeCupProduct (w : f ≫ q = p ≫ h) (i j : ℤ)
    (ξ : cohomologyModule ((derivedPushforward (squareHom w)).obj (deRhamDerived p)) i)
    (η : cohomologyModule ((derivedPushforward (squareHom w)).obj (deRhamDerived p)) j) :
    lerayMap (squareHom w) (deRhamDerived p) (i + j)
      (((DerivedCategory.homologyFunctor _ (i + j)).map
        ((baseSections (SheafOfModules.baseRingedSpace (X := Y.toRingedSpace)
            ((TopCat.Sheaf.pullback CommRingCat.{u} q.base).obj T.sheaf))).map
          (deRhamRelativeCupProduct w))).hom
        ((cupPairing (cupProductOnSpace (SheafOfModules.baseRingedSpace (X := Y.toRingedSpace)
            ((TopCat.Sheaf.pullback CommRingCat.{u} q.base).obj T.sheaf))) _ _ i j).hom
          (ξ ⊗ₜ η))) =
      SheafOfModules.deRhamCohomologyCup _ _ i j (lerayMap (squareHom w) (deRhamDerived p) i ξ)
        (lerayMap (squareHom w) (deRhamDerived p) j η) :=
  SheafOfModules.lerayMap_deRhamRelativeCupProduct _ _ (squareHom w) i j ξ η

end AlgebraicGeometry.Scheme

end
