module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.AcyclicCoveringFamily
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Čech cohomology of an acyclic covering family as derived sections

For a covering family `𝒰` of an object `U` of a site and an abelian sheaf `F` whose higher
cohomology vanishes on every nonempty finite fibre product of members of the family, the Čech
cohomology group `Ȟ^j(𝒰, F)` is isomorphic to `R^j Γ(U, F)`, the cohomology of `F` over `U`.

## Main definitions

* `Stacks.CechSite.Acyclic.cechDerivedHomologyIso`: the degree-`j` homology of the Čech complex
  in `D⁺(Ab)` is the Čech cohomology group `Ȟ^j(𝒰, F)`.
* `Stacks.CechSite.Acyclic.derivedSectionsHomologyIso`: the degree-`j` homology of `RΓ(U, F)` is
  `R^j Γ(U, F)`, the `ℕ`-indexed right derived functor of sections over `U`.
* `Stacks.CechSite.Acyclic.cechCohomologyIsoRightDerivedSections`: the isomorphism
  `Ȟ^j(𝒰, F) ≅ R^j Γ(U, F)` for an abelian sheaf acyclic on the finite fibre products of the
  family.

## References

* [Stacks Project, Tag 03F7](https://stacks.math.columbia.edu/tag/03F7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite

universe v u

namespace Stacks.CechSite.Acyclic

attribute [local instance] HasDerivedCategory.standard

section Sections

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) (U : C)
  [HasSheafify K Ab.{max u v}] [EnoughInjectives (Sheaf K Ab.{max u v})]

/-- The sections functor of abelian sheaves over an object is additive. -/
instance additive_sheafSections_obj :
    ((sheafSections K Ab.{max u v}).obj (op U)).Additive :=
  inferInstanceAs ((sheafToPresheaf K Ab.{max u v} ⋙
    (evaluation Cᵒᵖ Ab.{max u v}).obj (op U)).Additive)

/-- The degree-`j` homology of `RΓ(U, F)` in `D⁺(Ab)` is isomorphic to `R^j Γ(U, F)`, the `j`-th
`ℕ`-indexed right derived functor of the sections functor over `U` applied to `F`. -/
def derivedSectionsHomologyIso (F : Sheaf K Ab.{max u v}) (j : ℕ) :
    (DerivedCategory.Plus.homologyFunctor Ab.{max u v} (j : ℤ)).obj
        ((derivedSectionsFunctor.{max u v} K U).obj F) ≅
      (((sheafSections K Ab.{max u v}).obj (op U)).rightDerived j).obj F :=
  ((Stacks.DerivedIndexing.rightDerivedIso
    ((sheafSections K Ab.{max u v}).obj (op U)) j).app F).symm

end Sections

variable {C : Type u} [Category.{v} C] (K : GrothendieckTopology C) {U : C}
  (E : PreZeroHypercover.{max u v} U)
  [∀ (n : ℕ) (i : Fin (n + 1) → E.I₀), HasProduct (fun b ↦ Over.mk (E.f (i b)))]

/-- The degree-`j` homology, in the bounded below derived category, of the Čech complex of a
covering family is isomorphic to the Čech cohomology group `Ȟ^j(𝒰, F)`. -/
def cechDerivedHomologyIso (F : Sheaf K Ab.{max u v}) (j : ℕ) :
    (DerivedCategory.Plus.homologyFunctor Ab.{max u v} (j : ℤ)).obj
        ((cechDerivedFunctor.{max u v} K E).obj F) ≅
      cechCohomology E F.obj j :=
  (DerivedCategory.homologyFunctorFactors Ab.{max u v} (j : ℤ)).app
      (((cechComplexFunctor E).obj F.obj).extend embeddingUpNat) ≪≫
    HomologicalComplex.extendHomologyIso ((cechComplexFunctor E).obj F.obj) embeddingUpNat
      (embeddingUpNat_f j)

variable [HasSheafify K Ab.{max u v}] [EnoughInjectives (Sheaf K Ab.{max u v})]
  (hE : Sieve.generate E.presieve₀ ∈ K U)

/-- Let `𝒰 = {U_i → U}` be a covering family of an object of a site and let `F` be an abelian
sheaf whose higher cohomology vanishes on every nonempty finite fibre product
`U_{i_0} ×_U ⋯ ×_U U_{i_r}` of members of the family. Then

`Ȟ^j(𝒰, F) ≅ H^j(U, F)`

in every degree, the right hand side being the `j`-th right derived functor of sections over `U`.
The isomorphism is induced by `cechCohomologyToCohomology`. -/
@[stacks 03F7 "the conclusion read as an isomorphism between the Cech cohomology group of the \
family and the j-th right derived sections over the covered object, which is the definition of \
H^j(U, F) that the acyclicity hypothesis of the tag is stated with"]
def cechCohomologyIsoRightDerivedSections (F : Sheaf K Ab.{max u v})
    (hacyclic : ∀ (r : ℕ) (s : Fin (r + 1) → E.I₀) (q : ℕ), 0 < q →
      IsZero (((tupleSections K E s).rightDerived q).obj F))
    (j : ℕ) :
    cechCohomology E F.obj j ≅
      (((sheafSections K Ab.{max u v}).obj (op U)).rightDerived j).obj F :=
  haveI := isIso_cechCohomologyToCohomology_app K E hE F hacyclic (j : ℤ)
  (cechDerivedHomologyIso K E F j).symm ≪≫
    asIso ((cechCohomologyToCohomology.{max u v} K E hE (j : ℤ)).app F) ≪≫
    derivedSectionsHomologyIso K U F j

end Stacks.CechSite.Acyclic

end
