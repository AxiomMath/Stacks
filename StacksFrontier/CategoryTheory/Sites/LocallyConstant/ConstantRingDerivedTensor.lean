module

public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Sites.Abelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorGradedPieces
public import StacksFrontier.CategoryTheory.Sites.Modules.ModuleSheavesAsConstantRingModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedAbove

/-!
# The derived tensor product of sheaves of `Λ`-modules

Let `(C, J)` be a small site and `Λ` a commutative ring. This file carries the derived tensor
product of Stacks 06YU across the identification of sheaves of `Λ`-modules with the modules over
a sheafification of the constant presheaf of rings on `Λ`, giving a bifunctor

`D(Sheaf J (ModuleCat Λ)) ⥤ D(Sheaf J (ModuleCat Λ)) ⥤ D(Sheaf J (ModuleCat Λ))`

together with the properties of it that the formalization of Stacks 094H and 094I consumes:
exactness in each variable, and that it takes objects in degrees `≤ a` and `≤ b` to objects in
degrees `≤ a + b`.

## Main definitions

* `Stacks.ConstantRingModules.derivedTensor`: the transported bifunctor, for a sheaf of rings
  given as a sheafification of the constant presheaf of rings on `Λ`.
* `Stacks.ConstantRingModules.constantDerivedTensor`: its instance at the constant sheaf of
  commutative rings on `Λ`, which is the derived tensor product `⊗^L_Λ` of the source.

## Main results

* `Stacks.ConstantRingModules.derivedTensor_commShift`,
  `Stacks.ConstantRingModules.derivedTensor_isTriangulated` and their `_flip` counterparts:
  exactness in each variable.
* `Stacks.ConstantRingModules.isLE_derivedTensor` and
  `Stacks.ConstantRingModules.isLE_constantDerivedTensor`: the degree bound.
* `isFiniteTypeLocallyConstantModuleSheaf_homology_constantDerivedTensor_quotientIdealPow`, in
  the same namespace: **Stacks Tag 094I** for this derived tensor product, with nothing assumed
  of it. Its proof is
  `isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow_of_isLE`, in the
  namespace `Stacks.ConstantSheaf`, of
  `StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorGradedPieces`, whose bifunctor
  parameter is instantiated here.
* `isFiniteTypeLocallyConstantModuleSheaf_homology_constantDerivedTensor_of_bounded`, in the
  same namespace: the reduction of **Stacks Tag 094H** to its bounded case for this derived
  tensor product, so that the bounded case of that tag is the single thing it still lacks. No
  tag is registered on it; the bounded case is that tag's own content.

## Implementation notes

The transport is the one of
`StacksFrontier.Homology.Tor.DerivedTensorUniverse`, where the derived tensor product of modules is
carried across the scalar equivalence in the same way: the bifunctor is conjugated by the
equivalence of derived categories, the shift comparison is transported with
`CategoryTheory.Functor.CommShift.ofIso` and exactness with
`CategoryTheory.Functor.isTriangulated_of_iso`.

The degree bound is not a field of the derived tensor product data; it is
`Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor`, right t-exactness in both
variables, and transporting it needs that the equivalence and its inverse neither create nor
destroy an upper bound on cohomology. That is
`CategoryTheory.Functor.isLE_mapDerivedCategory`, for which an exact *faithful* functor is
enough, and an equivalence and its inverse are faithful.

All four universes are one `u` and the site is small, which is the configuration in which the
library's derived tensor product over a sheaf of commutative rings is available
(`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`); see the implementation notes
there and in
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorIdealPowers`.

## References

* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace Stacks.ConstantRingModules

open Stacks.PresheafOfModules Stacks.DerivedTensor.RingedSite

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] SheafOfModules.instAbelian

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (Λ : Type u) [CommRing Λ] (R : Sheaf J CommRingCat.{u})
  (α : constRing (C := C) Λ ⟶ (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} R).obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [J.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- The identification of sheaves of modules over the structure sheaf with sheaves of
`Λ`-modules. -/
abbrev tensorEquiv : Modules R ≌ Sheaf J (ModuleCat.{u} Λ) :=
  moduleSheafEquivalence.{u} Λ J α

/-- The identification of sheaves of modules over the structure sheaf with sheaves of
`Λ`-modules is additive. -/
instance : (tensorEquiv Λ R α).functor.Additive :=
  inferInstanceAs (toModuleSheaf.{u} Λ J α).Additive

/-- The inverse of the identification of sheaves of modules over the structure sheaf with
sheaves of `Λ`-modules is additive. -/
instance : (tensorEquiv Λ R α).inverse.Additive := (tensorEquiv Λ R α).inverse_additive

/-- Passage from sheaves of modules over the structure sheaf to sheaves of `Λ`-modules, on the
derived categories. -/
abbrev tensorForward : DerivedCategory (Modules R) ⥤ DerivedCategory (Sheaf J (ModuleCat.{u} Λ)) :=
  (tensorEquiv Λ R α).functor.mapDerivedCategory

/-- Passage from sheaves of `Λ`-modules to sheaves of modules over the structure sheaf, on the
derived categories. -/
abbrev tensorBackward :
    DerivedCategory (Sheaf J (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Modules R) :=
  (tensorEquiv Λ R α).inverse.mapDerivedCategory

/-- **The derived tensor product of sheaves of `Λ`-modules**: the derived tensor product of
Stacks 06YU over the structure sheaf, conjugated by the identification of sheaves of modules
over it with sheaves of `Λ`-modules. -/
def derivedTensor :
    DerivedCategory (Sheaf J (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u} Λ)) ⥤
        DerivedCategory (Sheaf J (ModuleCat.{u} Λ)) :=
  tensorBackward Λ R α ⋙ (canonicalDerivedTensorProduct R).tensor ⋙
    (Functor.whiskeringLeft _ _ _).obj (tensorBackward Λ R α) ⋙
      (Functor.whiskeringRight _ _ _).obj (tensorForward Λ R α)

/-- Tensoring with a fixed object `K` is, by definition, passage to sheaves of modules over the
structure sheaf, the derived tensor product there with the image of `K`, and passage back. -/
theorem derivedTensor_obj (K : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) :
    (derivedTensor Λ R α).obj K =
      tensorBackward Λ R α ⋙ (canonicalDerivedTensorProduct R).tensor.obj
        ((tensorBackward Λ R α).obj K) ⋙ tensorForward Λ R α := rfl

/-- **The derived tensor product of sheaves of `Λ`-modules commutes with the shift in its second
variable**, the three functors it is composed of doing so. -/
@[instance_reducible]
instance derivedTensor_commShift (K : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) :
    ((derivedTensor Λ R α).obj K).CommShift ℤ :=
  letI := (canonicalDerivedTensorProduct R).commShift_right ((tensorBackward Λ R α).obj K)
  inferInstanceAs ((tensorBackward Λ R α ⋙
    (canonicalDerivedTensorProduct R).tensor.obj ((tensorBackward Λ R α).obj K) ⋙
      tensorForward Λ R α).CommShift ℤ)

/-- **The derived tensor product of sheaves of `Λ`-modules is exact in its second variable.** -/
instance derivedTensor_isTriangulated (K : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) :
    ((derivedTensor Λ R α).obj K).IsTriangulated :=
  letI := (canonicalDerivedTensorProduct R).commShift_right ((tensorBackward Λ R α).obj K)
  letI := (canonicalDerivedTensorProduct R).exact_right ((tensorBackward Λ R α).obj K)
  inferInstanceAs ((tensorBackward Λ R α ⋙
    (canonicalDerivedTensorProduct R).tensor.obj ((tensorBackward Λ R α).obj K) ⋙
      tensorForward Λ R α).IsTriangulated)

/-- Tensoring on the left with a fixed object, read through the identification. The two
functors agree on objects and morphisms but are built from different terms, so the comparison is
an isomorphism with identity components rather than an equality. -/
def derivedTensorFlipObjIso (L : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) :
    (derivedTensor Λ R α).flip.obj L ≅
      tensorBackward Λ R α ⋙
        (canonicalDerivedTensorProduct R).tensor.flip.obj ((tensorBackward Λ R α).obj L) ⋙
          tensorForward Λ R α :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by intros; simp [derivedTensor])

/-- **The derived tensor product of sheaves of `Λ`-modules commutes with the shift in its first
variable.** -/
@[instance_reducible]
instance derivedTensor_commShift_flip (L : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) :
    ((derivedTensor Λ R α).flip.obj L).CommShift ℤ :=
  letI := (canonicalDerivedTensorProduct R).commShift_left ((tensorBackward Λ R α).obj L)
  Functor.CommShift.ofIso (derivedTensorFlipObjIso Λ R α L).symm ℤ

/-- **The derived tensor product of sheaves of `Λ`-modules is exact in its first variable.** -/
instance derivedTensor_isTriangulated_flip (L : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) :
    ((derivedTensor Λ R α).flip.obj L).IsTriangulated :=
  letI := (canonicalDerivedTensorProduct R).commShift_left ((tensorBackward Λ R α).obj L)
  letI := (canonicalDerivedTensorProduct R).exact_left ((tensorBackward Λ R α).obj L)
  letI i := (derivedTensorFlipObjIso Λ R α L).symm
  letI := Functor.CommShift.ofIso_compatibility i ℤ
  Functor.isTriangulated_of_iso i

/-- **The derived tensor product of sheaves of `Λ`-modules takes objects in degrees `≤ a` and
`≤ b` to objects in degrees `≤ a + b`.** This is the right t-exactness of the derived tensor
product over the structure sheaf, carried across the identification in both directions. -/
theorem isLE_derivedTensor (K L : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) (a b : ℤ)
    [K.IsLE a] [L.IsLE b] : (((derivedTensor Λ R α).obj K).obj L).IsLE (a + b) := by
  have h (M : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) (c : ℤ) [M.IsLE c] :
      ((tensorBackward Λ R α).obj M).IsLE c :=
    Functor.isLE_mapDerivedCategory (tensorEquiv Λ R α).inverse M c
  let _ := isLE_derivedTensorProductFunctor R ((tensorBackward Λ R α).obj K)
    ((tensorBackward Λ R α).obj L) a b
  exact Functor.isLE_mapDerivedCategory (tensorEquiv Λ R α).functor
    (((canonicalDerivedTensorProduct R).tensor.obj ((tensorBackward Λ R α).obj K)).obj
      ((tensorBackward Λ R α).obj L)) (a + b)

/-! ### The constant sheaf of rings -/

section Constant

variable {C : Type u} [SmallCategory.{u} C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ]

/-- The constant sheaf of commutative rings on `Λ`, the structure sheaf over which the derived
tensor product of sheaves of `Λ`-modules is taken. -/
abbrev constantCommRingSheaf : Sheaf J CommRingCat.{u} :=
  (constantSheaf J CommRingCat.{u}).obj (CommRingCat.of Λ)

/-- The sheafification map from the constant presheaf of rings on `Λ` to the sheaf of rings
underlying the constant sheaf of commutative rings on `Λ`. -/
def constantTensorRingMap :
    constRing (C := C) Λ ⟶
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (constantCommRingSheaf J Λ)).obj :=
  Functor.whiskerRight (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ)))
    (forget₂ CommRingCat.{u} RingCat.{u})

/-- The sheafification map onto the constant sheaf of commutative rings on `Λ` is locally
injective, as every sheafification map is. -/
instance constantTensorRingMap_isLocallyInjective :
    Presheaf.IsLocallyInjective J (constantTensorRingMap J Λ) :=
  ⟨fun x y hxy => Presheaf.equalizerSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))) x y hxy⟩

/-- The sheafification map onto the constant sheaf of commutative rings on `Λ` is locally
surjective, as every sheafification map is. -/
instance constantTensorRingMap_isLocallySurjective :
    Presheaf.IsLocallySurjective J (constantTensorRingMap J Λ) :=
  ⟨fun x => Presheaf.imageSieve_mem J
    (toSheafify J ((Functor.const Cᵒᵖ).obj (CommRingCat.of Λ))) x⟩

/-- **The derived tensor product of sheaves of `Λ`-modules over the constant sheaf of
commutative rings on `Λ`.** This is the bifunctor that Stacks 094H and 094I are about. -/
abbrev constantDerivedTensor :
    DerivedCategory (Sheaf J (ModuleCat.{u} Λ)) ⥤
      DerivedCategory (Sheaf J (ModuleCat.{u} Λ)) ⥤
        DerivedCategory (Sheaf J (ModuleCat.{u} Λ)) :=
  derivedTensor Λ (constantCommRingSheaf J Λ) (constantTensorRingMap J Λ)

/-- The degree bound for `Stacks.ConstantRingModules.constantDerivedTensor`, in the shape in
which Stacks 094H and 094I consume it. -/
theorem isLE_constantDerivedTensor
    (K L : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) (a b : ℤ) (hK : K.IsLE a)
    (hL : L.IsLE b) : (((constantDerivedTensor J Λ).obj K).obj L).IsLE (a + b) :=
  isLE_derivedTensor Λ (constantCommRingSheaf J Λ) (constantTensorRingMap J Λ) K L a b

open Stacks.ConstantSheaf in
/-- **The reduction of Stacks Tag 094H to its bounded case, for the derived tensor product
itself.** This is
`Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_homology_of_bounded` with its
bifunctor parameter instantiated at
`Stacks.ConstantRingModules.constantDerivedTensor`, so that nothing is assumed of the derived
tensor product here. What is left is `hbounded`, the conclusion of Tag 094H for bounded `K` and
`L`, which is the tag's own content and not a property of the tensor product; no tag is
registered on this statement for that reason. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_constantDerivedTensor_of_bounded
    (hbounded : ∀ (K L : DerivedCategory.Bounded (Sheaf J (ModuleCat.{u} Λ))),
      (∀ i, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
        ((DerivedCategory.homologyFunctor _ i).obj K.obj)) →
      (∀ i, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
        ((DerivedCategory.homologyFunctor _ i).obj L.obj)) →
      ∀ i, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
        ((DerivedCategory.homologyFunctor _ i).obj
          (((constantDerivedTensor J Λ).obj K.obj).obj L.obj)))
    (K L : DerivedCategory.Minus (Sheaf J (ModuleCat.{u} Λ)))
    (hK : ∀ i, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj K.obj))
    (hL : ∀ i, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj L.obj)) (i : ℤ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (((constantDerivedTensor J Λ).obj K.obj).obj L.obj)) :=
  isFiniteTypeLocallyConstantModuleSheaf_homology_of_bounded J Λ (constantDerivedTensor J Λ)
    (isLE_constantDerivedTensor J Λ) hbounded K L hK hL i

open Stacks.ConstantSheaf in
/-- **Stacks Tag 094I.** Let `(C, J)` be a site, `Λ` a Noetherian commutative ring, `I ⊆ Λ` an
ideal and `K` an object of `D^-` of the sheaves of `Λ`-modules. If the cohomology sheaves of
`K ⊗^L_Λ Λ/I` are locally constant of finite type, then so are those of `K ⊗^L_Λ Λ/Iⁿ` for every
`n ≥ 1`.

The derived tensor product is `Stacks.ConstantRingModules.constantDerivedTensor`, the derived
tensor product of Stacks 06YU over the constant sheaf of commutative rings on `Λ` read through
the identification of sheaves of modules over it with sheaves of `Λ`-modules. The proof is
`isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow_of_isLE`, in the
namespace `Stacks.ConstantSheaf`, whose bifunctor parameter is instantiated here and whose two
properties of it,
exactness in the second variable and the degree bound, are
`Stacks.ConstantRingModules.derivedTensor_isTriangulated` and
`Stacks.ConstantRingModules.isLE_constantDerivedTensor`. -/
@[stacks 094I "for a site whose objects, morphisms and coefficient ring lie in one universe, \
  which is where the library's derived tensor product over a sheaf of commutative rings is \
  available; the derived tensor product is constructed, not a parameter. Beyond the source's \
  own hypotheses the binders hold only `SmallCategory C`, `CommRing Λ` and `IsNoetherianRing \
  Λ`: the sheafification conditions this file's construction uses — `HasSheafify`, \
  `WEqualsLocallyBijective` and `HasSheafCompose` for the forgetful functor to abelian groups — \
  are synthesized at such a site, not assumed"]
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_constantDerivedTensor_quotientIdealPow
    [IsNoetherianRing Λ] (I : Ideal Λ) (b : ℤ)
    (K : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) [K.IsLE b]
    (hbase : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (derivedTensorConstant J Λ (constantDerivedTensor J Λ) K
          (ModuleCat.of Λ (Λ ⧸ I)))))
    (n : ℕ) (hn : 1 ≤ n) (i : ℤ) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (derivedTensorConstant J Λ (constantDerivedTensor J Λ) K
          (ModuleCat.of Λ (Λ ⧸ I ^ n)))) :=
  isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow_of_isLE
    J Λ I (constantDerivedTensor J Λ)
    (isLE_constantDerivedTensor J Λ) b K hbase n hn i

end Constant

end Stacks.ConstantRingModules

end
