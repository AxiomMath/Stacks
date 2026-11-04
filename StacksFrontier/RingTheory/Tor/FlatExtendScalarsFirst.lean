module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.CategoryTheory.Monoidal.Tor
public import StacksFrontier.Homology.KFlat.BaseChange

/-!
# `Tor` against a module extended along a flat ring map

Let `f : A →+* B` be a flat homomorphism of commutative rings, `M` an `A`-module and `N` a
`B`-module. Then, as `A`-modules,

`Torᵢᴮ(N, B ⊗_A M) ≅ Torᵢᴬ(N, M)`,

where on the right `N` is regarded as an `A`-module through `f`. A projective resolution `P` of
`M` extends to the projective resolution `B ⊗_A P` of `B ⊗_A M`, because extension of scalars along
a flat map is exact and is left adjoint to an exact functor, and `N ⊗_B (B ⊗_A P) ≅ N ⊗_A P`
degreewise.

## Main definitions

* `Stacks.TorFlatExtendScalars.extendScalarsResolution` — the extended resolution.
* `Stacks.TorFlatExtendScalars.torExtendScalarsIso` — the isomorphism above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace Stacks.TorFlatExtendScalars

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/-- A projective resolution of `M` extends along a flat ring map to a projective resolution of
`B ⊗_A M`. -/
noncomputable def extendScalarsResolution (hf : f.Flat) {M : ModuleCat.{u} A}
    (P : ProjectiveResolution M) :
    ProjectiveResolution ((ModuleCat.extendScalars.{u, u, u} f).obj M) :=
  haveI := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hf
  haveI := (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).leftAdjoint_preservesColimits
  haveI : (ModuleCat.extendScalars.{u, u, u} f).Additive :=
    Functor.additive_of_preserves_binary_products _
  haveI : (ModuleCat.extendScalars.{u, u, u} f).PreservesHomology := inferInstance
  { complex := ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex _).obj P.complex
    projective := fun n =>
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} f).map_projective _ (P.projective n)
    π := ((ModuleCat.extendScalars.{u, u, u} f).mapHomologicalComplex _).map P.π ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.extendScalars.{u, u, u} f) (ComplexShape.down ℕ) 0).hom.app M
    quasiIso := by
      have := P.quasiIso
      infer_instance }

/-- `N ⊗_B (B ⊗_A P) ≅ N ⊗_A P`, naturally in the `A`-module `P`, read over `A`. -/
noncomputable def tensorExtendScalarsIso (N : ModuleCat.{u} B) :
    ModuleCat.extendScalars.{u, u, u} f ⋙ tensorLeft N ⋙ ModuleCat.restrictScalars.{u} f ≅
      tensorLeft ((ModuleCat.restrictScalars.{u} f).obj N) :=
  NatIso.ofComponents (fun P => projectionFormulaIso f N P)
    (fun g => projectionFormulaIso_natural_right f N g)

/-- **`Tor` against a module extended along a flat ring map.** For a flat `f : A →+* B`, an
`A`-module `M` and a `B`-module `N`, `Torᵢᴮ(N, B ⊗_A M) ≅ Torᵢᴬ(N, M)` as `A`-modules. -/
noncomputable def torExtendScalarsIso (hf : f.Flat) (N : ModuleCat.{u} B) (M : ModuleCat.{u} A)
    (i : ℕ) :
    (ModuleCat.restrictScalars.{u} f).obj
        (((Tor (ModuleCat.{u} B) i).obj N).obj ((ModuleCat.extendScalars.{u, u, u} f).obj M)) ≅
      ((Tor (ModuleCat.{u} A) i).obj ((ModuleCat.restrictScalars.{u} f).obj N)).obj M := by
  let P := projectiveResolution M
  let Q := extendScalarsResolution f hf P
  let K := ((tensorLeft N).mapHomologicalComplex (ComplexShape.down ℕ)).obj Q.complex
  have e₁ : ((Tor (ModuleCat.{u} B) i).obj N).obj ((ModuleCat.extendScalars.{u, u, u} f).obj M) ≅
      K.homology i := Q.isoLeftDerivedObj (tensorLeft N) i
  have e₂ : (ModuleCat.restrictScalars.{u} f).obj (K.homology i) ≅
      (((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex _).obj K).homology i :=
    ((K.sc i).mapHomologyIso (ModuleCat.restrictScalars.{u} f)).symm
  have e₃ : ((ModuleCat.restrictScalars.{u} f).mapHomologicalComplex _).obj K ≅
      ((tensorLeft ((ModuleCat.restrictScalars.{u} f).obj N)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex :=
    (NatIso.mapHomologicalComplex (tensorExtendScalarsIso f N) (ComplexShape.down ℕ)).app
      P.complex
  have e₄ : ((Tor (ModuleCat.{u} A) i).obj ((ModuleCat.restrictScalars.{u} f).obj N)).obj M ≅
      (((tensorLeft ((ModuleCat.restrictScalars.{u} f).obj N)).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).homology i :=
    P.isoLeftDerivedObj (tensorLeft ((ModuleCat.restrictScalars.{u} f).obj N)) i
  exact (ModuleCat.restrictScalars.{u} f).mapIso e₁ ≪≫ e₂ ≪≫
    (HomologicalComplex.homologyFunctor _ _ i).mapIso e₃ ≪≫ e₄.symm

end Stacks.TorFlatExtendScalars

end
