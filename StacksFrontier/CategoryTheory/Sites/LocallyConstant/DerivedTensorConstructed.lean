module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedAbove
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingDerivedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BoundedAbove
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorGradedPieces
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks Tag 094I, with the derived tensor product constructed

Let `(C, J)` be a site, let `Λ` be a Noetherian commutative ring and let `I ⊆ Λ` be an ideal.
Stacks Tag 094I asserts that for `K` in `D^-(C, Λ)` whose cohomology sheaves after reduction
modulo `I` are locally constant sheaves of finite type, the same holds after reduction modulo
`Iⁿ` for every `n ≥ 1`.

`StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorGradedPieces` proves the
mathematics of the tag, but for a bifunctor `T` on `D(Sheaf J (ModuleCat Λ))` *supplied by the
caller* to stand for the derived tensor product, together with its exactness in the second
variable and the estimate `K.IsLE a → L.IsLE b → ((T.obj K).obj L).IsLE (a + b)` as hypotheses.
**This file constructs that bifunctor and discharges all four of those binders**, so the tag is
proved with no data and no property of a derived tensor product assumed.

## How the bifunctor is obtained

The derived tensor product of a ringed site is constructed and tagged 06YU, as
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, on
`D(SheafOfModules Oˢʰᵃʳᵖ)` for a sheaf of rings `Oˢʰᵃʳᵖ`. Taking for `Oˢʰᵃʳᵖ` the **constant**
sheaf of rings with value `Λ` and reading the result through the equivalence of abelian
categories

`Stacks.ConstantSheaf.constantSheafModuleEquivalence : Sheaf J (ModuleCat Λ) ≌ SheafOfModules Λ̲`

gives the bifunctor Tag 094I is about. The two directions of that equivalence are exact, so each
induces a triangulated functor on derived categories, `Φ` and `Ψ` below; the bifunctor is
`Stacks.ConstantSheaf.constantDerivedTensor`, whose value is `Ψ (Φ K ⊗^L Φ L)`. Nothing of
the construction is re-done here: `Φ` and `Ψ` are Mathlib's
`CategoryTheory.Functor.mapDerivedCategory` of the two functors of that equivalence, and
the tensor product between them is the 06YU one.

What the three properties come from:

* exactness in the second variable — `Φ`, `Ψ` and `- ⊗^L Φ K` are each triangulated with a
  shift commutation, the first two by Mathlib's instances on `mapDerivedCategory` and the third
  because it is a field of `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`; the composite
  inherits both;
* the bound above — `Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor` is the
  estimate on the ringed site, and `CategoryTheory.Functor.isLE_mapDerivedCategory` carries a
  bound above through `Φ` and through `Ψ` unchanged.

## Main definitions

* `Stacks.ConstantSheaf.constantDerivedTensor`: **the derived tensor product over `Λ` on
  `D(Sheaf J (ModuleCat Λ))`**, the 06YU derived tensor product of the constant ringed
  site read through the equivalence above.
* `Stacks.ConstantSheaf.derivedToModuleSheafCompIso` and
  `Stacks.ConstantSheaf.derivedOfModuleSheafCompIso`: `Φ` and `Ψ` are mutually inverse.
* `Stacks.ConstantSheaf.derivedToModuleSheaf_obj_constantDerivedTensor`: the derived tensor
  product over `Λ` is the ringed site's, under the identification of the two categories.

## Main results

* `isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensorConstant_quotientIdealPow`:
  **Stacks Tag 094I**, with the derived tensor product constructed.
* `Stacks.ConstantSheaf.isLE_constantDerivedTensor`: the derived tensor product over `Λ` carries
  bounds above to their sum.
* `Stacks.ConstantSheaf.constantDerivedTensor_obj_obj`: the definition of the bifunctor, read
  off: `K ⊗^L_Λ L` is the ringed-site derived tensor product of the images of `K` and `L`,
  brought back.

## Implementation notes

**The universes are those of the 06YU construction**, namely a small site and a ring in the
same universe: `C : Type u` with `SmallCategory.{u} C` and `Λ : Type u`. This is where the
existence of K-flat resolutions is available, as
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExistenceOnARingedSite` records, and
it is the Stacks Project's own setting, in which a site is a category with a set of objects.
The theorems of
`StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorGradedPieces` are stated with a
free module universe `max u v w`; they are applied here at `v = w = u`, which is the only place
the generality is spent.

`HasSheafify J (ModuleCat.{u} Λ)` is the one hypothesis on the site that does not resolve on
its own. Every other side condition of the two developments — the sheafification and local
bijectivity hypotheses for `AddCommGrpCat` and `CommRingCat`, the additivity of the sheaf
tensor product and the existence of its total complexes — is found by instance search at these
universes.

`Φ` and `Ψ` are written as `_.mapDerivedCategory` rather than through the existing
`Stacks.ConstantSheaf.constantRingModuleDerivedFunctor` and
`Stacks.ConstantSheaf.moduleSheafOfConstantRingDerivedFunctor`, which are the same functors —
`constantDerivedTensor_eq_constantRingModuleDerivedFunctor_comp` records that they are — because
a `def` is a wall for instance search and the `CommShift` and `IsTriangulated` instances on
`mapDerivedCategory` have to be visible.

## References

* [Stacks Project, Tag 094I](https://stacks.math.columbia.edu/tag/094I)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 03ET](https://stacks.math.columbia.edu/tag/03ET)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.ConstantSheaf

variable {C : Type u} [SmallCategory.{u} C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ] [HasSheafify J (ModuleCat.{u} Λ)]

attribute [local instance] HasDerivedCategory.standard

/-! ### The constant ringed site and the equivalence onto it -/

/-- **The constant ringed site**: the site `(C, J)` with the constant sheaf of rings with value
`Λ` as its structure sheaf. This is the ringed site whose derived tensor product, Tag 06YU, is
the derived tensor product over `Λ`. -/
abbrev constantStructureRingSheaf : Sheaf J CommRingCat.{u} := constantRingSheaf J Λ

/-- **The equivalence of abelian categories `Sheaf J (ModuleCat Λ) ≌ SheafOfModules Λ̲`**,
`Stacks.ConstantSheaf.constantSheafModuleEquivalence`, named here for the two functors it
supplies. -/
abbrev constantModuleEquivalence :=
  constantRingModuleEquivalence J (constantRingSheafMap J Λ)

/-- **Sheaves of `Λ`-modules read as sheaves of modules over the constant ring sheaf, on derived
categories.** Written as `mapDerivedCategory` of the functor of the equivalence so that
Mathlib's shift commutation and triangulatedness instances for it apply; it is
`Stacks.ConstantSheaf.constantRingModuleDerivedFunctor`. -/
abbrev derivedToModuleSheaf := (constantModuleEquivalence J Λ).functor.mapDerivedCategory

/-- **Restriction of scalars back to the constant ring `Λ`, on derived categories**; it is
`Stacks.ConstantSheaf.moduleSheafOfConstantRingDerivedFunctor`. -/
abbrev derivedOfModuleSheaf := (constantModuleEquivalence J Λ).inverse.mapDerivedCategory

/-- **The derived tensor product of the constant ringed site**, Tag 06YU at the constant sheaf
of rings with value `Λ`. -/
abbrev constantRingedSiteDerivedTensor :=
  Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor (constantStructureRingSheaf J Λ)

/-! ### The derived tensor product over `Λ` -/

/-- **The derived tensor product over `Λ` on `D(Sheaf J (ModuleCat Λ))`.** This is the
derived tensor product of Tag 06YU for the constant ringed site, read through the equivalence
`Sheaf J (ModuleCat Λ) ≌ SheafOfModules Λ̲` of Tag 03ET: `K ⊗^L_Λ L` is the ringed-site derived
tensor product of the images of `K` and of `L`, brought back along the inverse equivalence. -/
def constantDerivedTensor : DerivedCategory (Sheaf J (ModuleCat.{u} Λ)) ⥤
    DerivedCategory (Sheaf J (ModuleCat.{u} Λ)) ⥤
    DerivedCategory (Sheaf J (ModuleCat.{u} Λ)) :=
  derivedToModuleSheaf J Λ ⋙ constantRingedSiteDerivedTensor J Λ ⋙
    ((Functor.whiskeringLeft _ _ _).obj (derivedToModuleSheaf J Λ) ⋙
      (Functor.whiskeringRight _ _ _).obj (derivedOfModuleSheaf J Λ))

/-- **The derived tensor product over `Λ`, read off its definition**: `K ⊗^L_Λ L` is the
ringed-site derived tensor product of the images of `K` and `L` under the equivalence, brought
back. -/
theorem constantDerivedTensor_obj_obj
    (K L : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) :
    ((constantDerivedTensor J Λ).obj K).obj L =
      (derivedOfModuleSheaf J Λ).obj
        (((constantRingedSiteDerivedTensor J Λ).obj ((derivedToModuleSheaf J Λ).obj K)).obj
          ((derivedToModuleSheaf J Λ).obj L)) :=
  rfl

/-- **The two functors of the equivalence, on derived categories, are the ones already built**
in `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantRingDerivedEquivalence`: no second
bridge between the two categories is introduced here. -/
theorem constantDerivedTensor_eq_constantRingModuleDerivedFunctor_comp :
    derivedToModuleSheaf J Λ =
      constantRingModuleDerivedFunctor J (constantRingSheafMap J Λ) ∧
    derivedOfModuleSheaf J Λ =
      moduleSheafOfConstantRingDerivedFunctor J (constantRingSheafMap J Λ) :=
  ⟨rfl, rfl⟩

/-! ### `Φ` and `Ψ` are mutually inverse

The equivalence `Sheaf J (ModuleCat Λ) ≌ SheafOfModules Λ̲` is one of abelian categories, so
each direction induces a functor on derived categories; that those two are mutually inverse is
what makes `Stacks.ConstantSheaf.constantDerivedTensor` *the* derived tensor product over `Λ`
rather than merely some bifunctor built out of the ringed site's. Both composites are computed
by descending along the localization `DerivedCategory.Q`, where the corresponding statement is
the unit, respectively the counit, of `CategoryTheory.Equivalence.mapHomologicalComplex`. -/

/-- The descent datum for `Φ ⋙ Ψ`: on complexes, applying the two directions of the equivalence
in turn is the identity, by the unit of `CategoryTheory.Equivalence.mapHomologicalComplex`. -/
def derivedToModuleSheafCompLiftIso :
    DerivedCategory.Q ⋙ (derivedToModuleSheaf J Λ ⋙ derivedOfModuleSheaf J Λ) ≅
      DerivedCategory.Q :=
  Functor.isoWhiskerRight (constantModuleEquivalence J Λ).functor.mapDerivedCategoryFactors
      (derivedOfModuleSheaf J Λ) ≪≫
    Functor.isoWhiskerLeft ((constantModuleEquivalence J Λ).functor.mapHomologicalComplex
        (ComplexShape.up ℤ))
      (constantModuleEquivalence J Λ).inverse.mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerRight ((constantModuleEquivalence J Λ).mapHomologicalComplex
      (ComplexShape.up ℤ)).unitIso.symm DerivedCategory.Q ≪≫
    DerivedCategory.Q.leftUnitor

/-- The descent datum for `Ψ ⋙ Φ`, by the counit of
`CategoryTheory.Equivalence.mapHomologicalComplex`. -/
def derivedOfModuleSheafCompLiftIso :
    DerivedCategory.Q ⋙ (derivedOfModuleSheaf J Λ ⋙ derivedToModuleSheaf J Λ) ≅
      DerivedCategory.Q :=
  Functor.isoWhiskerRight (constantModuleEquivalence J Λ).inverse.mapDerivedCategoryFactors
      (derivedToModuleSheaf J Λ) ≪≫
    Functor.isoWhiskerLeft ((constantModuleEquivalence J Λ).inverse.mapHomologicalComplex
        (ComplexShape.up ℤ))
      (constantModuleEquivalence J Λ).functor.mapDerivedCategoryFactors ≪≫
    Functor.isoWhiskerRight ((constantModuleEquivalence J Λ).mapHomologicalComplex
      (ComplexShape.up ℤ)).counitIso DerivedCategory.Q ≪≫
    DerivedCategory.Q.leftUnitor

/-- **`Ψ ∘ Φ` is the identity on `D(Sheaf J (ModuleCat Λ))`.** -/
def derivedToModuleSheafCompIso :
    derivedToModuleSheaf J Λ ⋙ derivedOfModuleSheaf J Λ ≅ 𝟭 _ :=
  letI : Localization.Lifting (DerivedCategory.Q (C := Sheaf J (ModuleCat.{u} Λ)))
      (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
      DerivedCategory.Q (derivedToModuleSheaf J Λ ⋙ derivedOfModuleSheaf J Λ) :=
    ⟨derivedToModuleSheafCompLiftIso J Λ⟩
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (Sheaf J (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))
    DerivedCategory.Q DerivedCategory.Q
    (derivedToModuleSheaf J Λ ⋙ derivedOfModuleSheaf J Λ) (𝟭 _) (Iso.refl _)

/-- **`Φ ∘ Ψ` is the identity on `D(SheafOfModules Λ̲)`.** -/
def derivedOfModuleSheafCompIso :
    derivedOfModuleSheaf J Λ ⋙ derivedToModuleSheaf J Λ ≅ 𝟭 _ :=
  letI : Localization.Lifting
      (DerivedCategory.Q (C := Stacks.DerivedTensor.RingedSite.Modules
        (constantStructureRingSheaf J Λ)))
      (HomologicalComplex.quasiIso (Stacks.DerivedTensor.RingedSite.Modules
        (constantStructureRingSheaf J Λ)) (ComplexShape.up ℤ))
      DerivedCategory.Q (derivedOfModuleSheaf J Λ ⋙ derivedToModuleSheaf J Λ) :=
    ⟨derivedOfModuleSheafCompLiftIso J Λ⟩
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (Stacks.DerivedTensor.RingedSite.Modules
      (constantStructureRingSheaf J Λ)) (ComplexShape.up ℤ))
    DerivedCategory.Q DerivedCategory.Q
    (derivedOfModuleSheaf J Λ ⋙ derivedToModuleSheaf J Λ) (𝟭 _) (Iso.refl _)

/-- **The derived tensor product over `Λ` is the ringed site's, under the identification of the
two categories**: the image of `K ⊗^L_Λ L` is the ringed-site derived tensor product of the
images of `K` and of `L`. Together with
`Stacks.ConstantSheaf.constantDerivedTensor_obj_obj` this says that
`Stacks.ConstantSheaf.constantDerivedTensor` is the derived tensor product of Tag 06YU read
across the equivalence, with nothing else intervening. -/
def derivedToModuleSheaf_obj_constantDerivedTensor
    (K L : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) :
    (derivedToModuleSheaf J Λ).obj (((constantDerivedTensor J Λ).obj K).obj L) ≅
      ((constantRingedSiteDerivedTensor J Λ).obj ((derivedToModuleSheaf J Λ).obj K)).obj
        ((derivedToModuleSheaf J Λ).obj L) :=
  (derivedOfModuleSheafCompIso J Λ).app _

/-- **The derived tensor product over `Λ` is exact in its second variable**: tensoring with a
fixed `K` commutes with the shift. It is a composite of three functors that do, the two
directions of the equivalence by Mathlib's instances on `mapDerivedCategory` and the
ringed-site derived tensor product by a field of
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`. -/
instance commShift_constantDerivedTensor_obj
    (K : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) :
    ((constantDerivedTensor J Λ).obj K).CommShift ℤ :=
  inferInstanceAs ((derivedToModuleSheaf J Λ ⋙
    (constantRingedSiteDerivedTensor J Λ).obj ((derivedToModuleSheaf J Λ).obj K) ⋙
    derivedOfModuleSheaf J Λ).CommShift ℤ)

/-- **The derived tensor product over `Λ` is exact in its second variable**: tensoring with a
fixed `K` is a triangulated functor, being a composite of three such. -/
instance isTriangulated_constantDerivedTensor_obj
    (K : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) :
    ((constantDerivedTensor J Λ).obj K).IsTriangulated :=
  inferInstanceAs ((derivedToModuleSheaf J Λ ⋙
    (constantRingedSiteDerivedTensor J Λ).obj ((derivedToModuleSheaf J Λ).obj K) ⋙
    derivedOfModuleSheaf J Λ).IsTriangulated)

/-- **The derived tensor product over `Λ` carries bounds above to their sum**: the derived
tensor product of an object of `D^{≤ a}` with an object of `D^{≤ b}` lies in `D^{≤ a + b}`.

The two directions of the equivalence are exact and faithful, so they preserve boundedness
above with the same bound, by `CategoryTheory.Functor.isLE_mapDerivedCategory`; in between, the
estimate is the ringed site's
`Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor`. -/
@[sga "5 I 4.7" "more general"]
theorem isLE_constantDerivedTensor
    (K L : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) (a b : ℤ) [K.IsLE a] [L.IsLE b] :
    (((constantDerivedTensor J Λ).obj K).obj L).IsLE (a + b) := by
  have hK : ((derivedToModuleSheaf J Λ).obj K).IsLE a :=
    (constantModuleEquivalence J Λ).functor.isLE_mapDerivedCategory K a
  have hL : ((derivedToModuleSheaf J Λ).obj L).IsLE b :=
    (constantModuleEquivalence J Λ).functor.isLE_mapDerivedCategory L b
  have hT : (((constantRingedSiteDerivedTensor J Λ).obj ((derivedToModuleSheaf J Λ).obj K)).obj
      ((derivedToModuleSheaf J Λ).obj L)).IsLE (a + b) :=
    Stacks.DerivedTensor.RingedSite.isLE_derivedTensorProductFunctor
      (constantStructureRingSheaf J Λ) _ _ a b
  exact (constantModuleEquivalence J Λ).inverse.isLE_mapDerivedCategory
    (((constantRingedSiteDerivedTensor J Λ).obj ((derivedToModuleSheaf J Λ).obj K)).obj
      ((derivedToModuleSheaf J Λ).obj L)) (a + b)

end Stacks.ConstantSheaf

/-! ### Tag 094I

The namespace is reopened with a `variable` line that does **not** carry
`HasSheafify J (ModuleCat.{u} Λ)`, so that the binders of the tagged statement are the source's
own hypotheses and nothing else. Dropping it costs nothing: for a small site and a ring in the
same universe, instance search finds it through Mathlib's sheafification instance for small
sites. -/

namespace Stacks.ConstantSheaf

variable {C : Type u} [SmallCategory.{u} C] (J : GrothendieckTopology C)
  (Λ : Type u) [CommRing Λ]

attribute [local instance] HasDerivedCategory.standard

section Noetherian

variable [IsNoetherianRing Λ]

/-- **Stacks Tag 094I.** Let `(C, J)` be a site, let `Λ` be a Noetherian commutative ring, let
`I ⊆ Λ` be an ideal and let `K` be an object of `D^-(C, Λ)`. If the cohomology sheaves of
`K ⊗^L_Λ Λ/I` are locally constant sheaves of finite type, then so are those of
`K ⊗^L_Λ Λ/Iⁿ` for every `n ≥ 1`.

The derived tensor product is `Stacks.ConstantSheaf.constantDerivedTensor`, the derived tensor
product of Tag 06YU for the constant ringed site read through the equivalence of Tag 03ET.
Nothing about it is assumed: its exactness in the second variable and its bound above are the
instances and the theorem of this file, and the mathematics of the tag is
`isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow_of_isLE`.

The hypothesis `K.IsLE b` is the source's `K ∈ D^-(C, Λ)`. Local constancy of finite type is
stated over `Λ` rather than over `Λ/Iⁿ`, which is equivalent: a `Λ`-module killed by `Iⁿ` is of
finite type over `Λ` exactly when it is over `Λ/Iⁿ`, by
`Stacks.ConstantSheaf.module_finite_iff_finite_quotient`, and constant for one ring exactly when
constant for the other.

`HasSheafify J (ModuleCat.{u} Λ)` is deliberately **not** a binder here: the namespace is
reopened above with a `variable` line that does not carry it, so that the binder list is the
source's own hypotheses and nothing else. At these universes instance search finds it, through
Mathlib's sheafification instance for small sites. -/
@[stacks 094I "the derived tensor product is constructed, not assumed: it is Tag 06YU for the \
  constant ringed site read through the equivalence Sheaf J (ModuleCat Λ) ≌ SheafOfModules Λ̲; \
  the source's own hypotheses only"]
theorem isFiniteTypeLocallyConstantModuleSheaf_homology_derivedTensorConstant_quotientIdealPow
    (I : Ideal Λ) (b : ℤ) (K : DerivedCategory (Sheaf J (ModuleCat.{u} Λ))) [K.IsLE b]
    (hbase : ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (derivedTensorConstant J Λ (constantDerivedTensor J Λ) K (ModuleCat.of Λ (Λ ⧸ I)))))
    (n : ℕ) (hn : 1 ≤ n) :
    ∀ i : ℤ, IsFiniteTypeLocallyConstantModuleSheaf.{u, u, u} J Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (derivedTensorConstant J Λ (constantDerivedTensor J Λ) K
          (ModuleCat.of Λ (Λ ⧸ I ^ n)))) :=
  isFiniteTypeLocallyConstantModuleSheaf_homology_tensor_quotientIdealPow_of_isLE
    J Λ I (constantDerivedTensor J Λ) (isLE_constantDerivedTensor J Λ) b K hbase n hn

end Noetherian

end Stacks.ConstantSheaf

end
