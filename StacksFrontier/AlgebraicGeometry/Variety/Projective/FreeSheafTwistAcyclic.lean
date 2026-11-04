module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.FiniteTildeTFAE
public import StacksFrontier.AlgebraicGeometry.ProjectiveSerreDevissage.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveTwistAcyclicity.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProjectiveTwist
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The twists of a finite free sheaf on `ℙⁿ` are acyclic in nonnegative degree

For a commutative ring `R`, a dimension `n`, a rank `r` and a degree `b ≥ 0`,

`Hⁱ(ℙⁿ_R, 𝒪^{⊕r}(b)) = 0` for every `i > 0`.

## Main definitions

* `AlgebraicGeometry.freeModules`: the free `𝒪`-module of rank `r` on `ℙⁿ_R`, the coproduct of
  `r` copies of the structure sheaf.
* `AlgebraicGeometry.projectiveTwistUnitIso`: the `b`-th twist of the structure sheaf is `𝒪(b)`.

## Main results

* `AlgebraicGeometry.isZero_obj_of_isColimit_of_additive`: an additive functor kills a finite
  direct sum, presented by a colimit cocone over a discrete diagram, of objects it kills.
* `AlgebraicGeometry.isZero_Hgroup_projectiveTwist_unit`: `Hⁱ(ℙⁿ_R, 𝒪(b)) = 0` for `b ≥ 0` and
  `i > 0`.
* `AlgebraicGeometry.isZero_Hgroup_projectiveTwist_freeModules`: `Hⁱ(ℙⁿ_R, 𝒪^{⊕r}(b)) = 0` for
  `b ≥ 0` and `i > 0`.

## References

* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 08AG](https://stacks.math.columbia.edu/tag/08AG)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Ample (unitModule)
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver twistZeroIsoUnit twistOverMulIso)
open Stacks.AlgebraicGeometry.ProjTwistFunctor (projectiveTwistFunctor)
open Stacks.RelativeVeryAmple (tensorModulesMapIso)

universe v v' u u'

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

/-- An additive functor kills a finite direct sum of objects it kills, with the direct sum
presented by a colimit cocone over a discrete diagram. -/
theorem isZero_obj_of_isColimit_of_additive {C : Type u} [Category.{v} C] [Preadditive C]
    {D : Type u'} [Category.{v'} D] [Preadditive D] (F : C ⥤ D) [F.Additive] {ι : Type}
    [Finite ι] {f : ι → C} {t : Cocone (Discrete.functor f)} (ht : IsColimit t)
    (hD : HasBiproduct fun i => F.obj (f i)) (h : ∀ i, IsZero (F.obj (f i))) :
    IsZero (F.obj t.pt) :=
  have := Fintype.ofFinite ι
  Stacks.HighTwistDevissage.isZero_obj_of_isBilimit F
    (biconeIsBilimitOfColimitCoconeOfIsColimit ht) hD h

/-- The `b`-th twist of the structure sheaf of `ℙⁿ_R` is `𝒪(b)`: `𝒪 ⊗ 𝒪(b) ≅ 𝒪(b)`. -/
def projectiveTwistUnitIso (R : Type u) [CommRing R] (n : ℕ) (b : ℤ) :
    projectiveTwist n (unitModule (projectiveSpaceOverRing n (CommRingCat.of R))) b ≅
      twistOver n (Spec (CommRingCat.of R)) b :=
  tensorModulesMapIso (projectiveSpaceOverRing n (CommRingCat.of R))
      (twistZeroIsoUnit n (Spec (CommRingCat.of R))).symm (Iso.refl _) ≪≫
    twistOverMulIso n (Spec (CommRingCat.of R)) 0 b ≪≫
    eqToIso (congrArg (twistOver n (Spec (CommRingCat.of R))) (zero_add b))

/-- `Hⁱ(ℙⁿ_R, 𝒪(b)) = 0` for `b ≥ 0` and `i > 0`, with `𝒪(b)` the `b`-th twist of the structure
sheaf. -/
theorem isZero_Hgroup_projectiveTwist_unit (R : Type u) [CommRing R] (n : ℕ) (b : ℤ) (hb : 0 ≤ b)
    (i : ℕ) (hi : 0 < i) :
    IsZero (Hgroup (projectiveSpaceOverRing n (CommRingCat.of R)).ringCatSheaf ⊤ i
      (projectiveTwist n (unitModule (projectiveSpaceOverRing n (CommRingCat.of R))) b)) :=
  (Stacks.AlgebraicGeometry.ProjectiveTwistAcyclicity.isZero_Hgroup_twistOver_specOf
      R n b hb i hi).of_iso
    ((Hfunctor (projectiveSpaceOverRing n (CommRingCat.of R)).ringCatSheaf ⊤ i).mapIso
      (projectiveTwistUnitIso R n b))

/-- The free `𝒪`-module `𝒪^{⊕r}` of rank `r` on `ℙⁿ_R`, the coproduct of `r` copies of the
structure sheaf. -/
abbrev freeModules (R : Type u) [CommRing R] (n r : ℕ) :
    (projectiveSpaceOverRing n (CommRingCat.of R)).Modules :=
  ∐ fun _ : Fin r => unitModule (projectiveSpaceOverRing n (CommRingCat.of R))

/-- For `R` Noetherian, the free module of rank `r` on `ℙⁿ_R` is coherent. -/
@[sga "6 I 3.6" "special case"]
instance isCoherent_freeModules (R : Type u) [CommRing R] [IsNoetherianRing R] (n r : ℕ) :
    (freeModules R n r).IsCoherent :=
  haveI : IsLocallyNoetherian (projectiveSpaceOverRing n (CommRingCat.of R)) :=
    projectiveSpaceOver_isLocallyNoetherian n (Spec (CommRingCat.of R))
  CoherentAbelian.isCoherent_of_stacksIsCoherent
    (Stacks.SheafOfModules.isCoherent_sigma _ fun _ ↦
      CoherentAbelian.stacksIsCoherent_of_isCoherent
        (Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent
          (projectiveSpaceOverRing n (CommRingCat.of R))))

/-- `Hⁱ(ℙⁿ_R, 𝒪^{⊕r}(b)) = 0` for `b ≥ 0` and `i > 0`. -/
theorem isZero_Hgroup_projectiveTwist_freeModules (R : Type u) [CommRing R] (n r : ℕ) (b : ℤ)
    (hb : 0 ≤ b) (i : ℕ) (hi : 0 < i) :
    IsZero (Hgroup (projectiveSpaceOverRing n (CommRingCat.of R)).ringCatSheaf ⊤ i
      (projectiveTwist n (freeModules R n r) b)) :=
  have :
      (projectiveTwistFunctor (R := R) n b ⋙
        Hfunctor (projectiveSpaceOverRing n (CommRingCat.of R)).ringCatSheaf ⊤ i).Additive :=
    Stacks.AlgebraicGeometry.ProjectiveSerreDevissage.additive_projectiveTwistFunctor_comp_hfunctor
      n ⊤ i b
  isZero_obj_of_isColimit_of_additive
    (projectiveTwistFunctor (R := R) n b ⋙
      Hfunctor (projectiveSpaceOverRing n (CommRingCat.of R)).ringCatSheaf ⊤ i)
    (colimit.isColimit (Discrete.functor
      fun _ : Fin r => unitModule (projectiveSpaceOverRing n (CommRingCat.of R))))
    inferInstance
    fun _ ↦ isZero_Hgroup_projectiveTwist_unit R n b hb i hi

end AlgebraicGeometry

end
