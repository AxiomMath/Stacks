module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingDimensionDuality
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.DerivedPushforwardDegreeZero
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents

/-!
# Lifting a morphism out of `A[-2]` along a morphism which is an isomorphism on `H^{-2}`

The hypothesis `himage` of
`Stacks.ResolutionOfSurfaces.isReductionToRationalSingularitiesPossible_of_factorisation`
([Stacks, Tag 0B4S] with Grauert-Riemenschneider discharged) asks that `d · Hom(A[-2], ω_A^•)`
factor through every `u : A[-2] ⟶ C` which is an isomorphism on `H^{-2}`, for
`C = RΓ(X, 𝒪_X)[2]`. Granted the trace `RΓ(X, ω_X^•) ⟶ ω_A^•` of
`Stacks.Duality.baseTrace`, that reduces to one statement: every morphism
`A[-2] ⟶ RΓ(X, ω_X^•)` factors through `u`. This file proves the two halves of that statement
which are independent of the duality data.

## Main results

* `DerivedCategory.exists_comp_eq_of_surjective_homologyMap` — **the formal half.** For `P`
  projective and `u : P[q] ⟶ C` an isomorphism on `H^q`, precomposition with `u` is surjective on
  the morphisms into any `Y` for which `H^q` is surjective on the morphisms out of `C`.
* `AlgebraicGeometry.exists_comp_secsOver_map_eq` — **the sheaf-level half.** Every `A`-linear
  map `A ⟶ Γ(X, ℱ)` is the global sections of a morphism `𝒪_X ⟶ ℱ`, precomposed with the global
  section `1` of `𝒪_X`;
  `AlgebraicGeometry.secsOver_map_apply_modificationSecsOverUnitIso_inv_one` discharges the
  hypothesis naming that section for a modification, where `A ⟶ Γ(X, 𝒪_X)` is invertible.
* `AlgebraicGeometry.homologyShiftTwoSingleIso` and
  `AlgebraicGeometry.homologyShiftTwoSingleIso_naturality` — **the comparison between the two.**
  `H^{-2}(RΓ(X, ℱ[0])[2]) ≅ Γ(X, ℱ)`, naturally in `ℱ`, so that `H^{-2}` of `RΓ(X, φ[0])[2]` is
  `Γ(X, φ)`.

## Why the lifting is not a t-structure formality

Write `C = RΓ(X, 𝒪_X)[2]` and `N = RΓ(X, ω_X^•)`. The convention
`Hom(ℳ[p], 𝒩[q]) = Ext^{p-q}(ℳ, 𝒩)` makes `Hom(D^{≥a}, D^{≤b})` nonzero for `b < a`, so the
vanishing axiom of the t-structure says nothing about `Hom(C, N)` with `C` in the degrees
`-2, -1` and `N` in the degree `-2`: the obstruction to lifting along `u` is
`Ext²_A(H¹(X, 𝒪_X), Γ(X, ω_X))`, which does not vanish in general. What makes the lifting
possible is that enough morphisms come from `D(𝒪_X)`. `Γ(X, 𝒪_X) = A` for a modification
(`AlgebraicGeometry.modificationSecsOverUnitIso`), so an `A`-linear map
`Γ(X, 𝒪_X) ⟶ Γ(X, ω_X)` is determined by its value at the section `1` and is therefore
`Γ(X, φ)` for a morphism `φ : 𝒪_X ⟶ ω_X` of sheaves; `H^{-2}` is consequently surjective on
`Hom(C, N)`, and the formal half applies.

## What is still owed

`N = RΓ(X, ω_X^•)` for `ω_X^• = f^×(ω̃_A^•)`, and the three results above are stated for
`RΓ(X, ℱ[0])[2]`. Joining them needs the normalization `ω_X^• ≅ ω_X[2]` of
`Stacks.ResolutionOfSurfaces.exists_isDualizingModule_isZero_firstCohomology`, in the form of the
isomorphism `N ≅ RΓ(X, ω_X[0])[2]` that
`Stacks.ResolutionOfSurfaces.hom_shift_standardDerivedGlobalSectionsUnitShift_eq_zero` builds for
its own use; `H^{-2}` of it carries `AlgebraicGeometry.homologyShiftTwoSingleIso` at `ω_X` to an
isomorphism `H^{-2}(N) ≅ Γ(X, ω_X)`, and
`AlgebraicGeometry.homologyShiftTwoSingleIso_naturality` then turns the sheaf-level half into the
surjectivity of `H^{-2}` on `Hom(C, N)` that the formal half consumes. That step is **not**
performed here, so no part of [Stacks, Tag 0B4S] is discharged by this file and no attribute is
placed on anything in it.

## Implementation notes

`AlgebraicGeometry.homologyShiftTwoSingleIso_naturality` is proved in the section where the three
global locally small instances of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` are
erased in favour of `CategoryTheory.HasDerivedCategory.standard`, which is the model
`AlgebraicGeometry.standardDerivedGlobalSectionsUnitShift` lives at. Two `CategoryStruct` paths
for the sheaves of modules on a scheme coexist there, and goals mentioning them are reported not
type-correct under implicit transparency, so `rw` fails to match even
`CategoryTheory.Category.assoc`; the two naturality squares and the reassociations between them
are therefore supplied as explicitly typed `have`s and composed by `calc`, which does fire.

## References

* [Stacks Project, Tag 0B4S](https://stacks.math.columbia.edu/tag/0B4S)
* [Stacks Project, Tag 0AWG](https://stacks.math.columbia.edu/tag/0AWG)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe w v u

/-! ### The formal half -/

namespace DerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- **Lifting along a morphism out of a projective object placed in one degree.** Let `P` be a
projective object of an abelian category `𝒜`, let `u : P[q] ⟶ C` be a morphism of `D(𝒜)` which is
an isomorphism on `H^q`, and let `Y` be an object for which every morphism `H^q(C) ⟶ H^q(Y)` is
`H^q` of a morphism `C ⟶ Y`. Then every morphism `P[q] ⟶ Y` factors as `u` followed by a morphism
`C ⟶ Y`.

`P[q]` corepresents `H^q` on the whole of `D(𝒜)`
(`DerivedCategory.bijective_homologyFromSingle_of_projective`), so a factorisation through `u` is
a factorisation of `Hom_𝒜(P, H^q(Y))` through `H^q(u)`, which is invertible. -/
theorem exists_comp_eq_of_surjective_homologyMap {P : 𝒜} [Projective P] {q : ℤ}
    {C Y : DerivedCategory 𝒜} (u : (singleFunctor 𝒜 q).obj P ⟶ C)
    (hu : IsIso ((homologyFunctor 𝒜 q).map u))
    (hsurj : Function.Surjective fun w : C ⟶ Y ↦ (homologyFunctor 𝒜 q).map w)
    (s : (singleFunctor 𝒜 q).obj P ⟶ Y) : ∃ w : C ⟶ Y, u ≫ w = s := by
  have := hu
  obtain ⟨w, hw⟩ := hsurj (inv ((homologyFunctor 𝒜 q).map u) ≫
    (singleFunctorCompHomologyFunctorIso 𝒜 q).hom.app P ≫ homologyFromSingle P Y q s)
  have hw' : (homologyFunctor 𝒜 q).map w = inv ((homologyFunctor 𝒜 q).map u) ≫
      (singleFunctorCompHomologyFunctorIso 𝒜 q).hom.app P ≫ homologyFromSingle P Y q s := hw
  refine ⟨w, (bijective_homologyFromSingle_of_projective P Y q).1 ?_⟩
  rw [homologyFromSingle_comp, hw']
  simp [homologyFromSingle_apply]

end DerivedCategory

/-! ### The sheaf-level half -/

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-- **`Γ(X, 𝒪_X) = A` carries `1` to the global section `1`.** For a modification
`f : X ⟶ Spec(A)` the inverse of `AlgebraicGeometry.modificationSecsOverUnitIso` is the structure
map `A ⟶ Γ(X, 𝒪_X)`, so it sends `1` to the global section `1` of `𝒪_X`; the equality is stated
in the form it is used in, namely that the global sections of `ψ : 𝒪_X ⟶ 𝒩` carry that section to
the section of `𝒩` which `ψ` is (`AlgebraicGeometry.unitHomEquivSectionsTop`).

Writing the unit of `Γ(X, 𝒪_X)` down directly is awkward — the `A`-module structure that
`AlgebraicGeometry.globalSectionsOver` installs by restriction of scalars hides the ring
structure — so the statement names it through `ψ` instead. -/
theorem secsOver_map_apply_modificationSecsOverUnitIso_inv_one [IsNormalDomain A]
    (hf : IsModification f) (N : X.Modules) (ψ : SheafOfModules.unit X.ringCatSheaf ⟶ N) :
    ((secsOver f).map ψ).hom ((modificationSecsOverUnitIso f hf).inv.hom (1 : A)) =
      unitHomEquivSectionsTop N ψ := by
  have h1 : ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom (1 : A) = 1 := map_one _
  change ((secsOver f).map ψ).hom
    (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom (1 : A)) = _
  rw [h1]
  rfl

/-- **Every `A`-linear map `A ⟶ Γ(X, ℱ)` is the global sections of a morphism `𝒪_X ⟶ ℱ`**, read
at the global section `1` of `𝒪_X`: a morphism out of the structure sheaf is its value on that
section (`AlgebraicGeometry.unitHomEquivSectionsTop`), and an `A`-linear map out of `A` is its
value at `1`.

The hypothesis on `ι` says that `ι` sends `1` to the global section `1` of `𝒪_X`, in the form it
is used in: the global sections of `ψ : 𝒪_X ⟶ 𝒩` carry it to the section of `𝒩` that `ψ` is.
`AlgebraicGeometry.secsOver_map_apply_modificationSecsOverUnitIso_inv_one` discharges it for the
inverse of `AlgebraicGeometry.modificationSecsOverUnitIso`, which is the structure map of a
modification and is invertible. -/
theorem exists_comp_secsOver_map_eq (M : X.Modules)
    (ι : ModuleCat.of A A ⟶ (secsOver f).obj (SheafOfModules.unit X.ringCatSheaf))
    (hι : ∀ (N : X.Modules) (ψ : SheafOfModules.unit X.ringCatSheaf ⟶ N),
      ((secsOver f).map ψ).hom (ι.hom (1 : A)) = unitHomEquivSectionsTop N ψ)
    (m : ModuleCat.of A A ⟶ (secsOver f).obj M) :
    ∃ φ : SheafOfModules.unit X.ringCatSheaf ⟶ M, ι ≫ (secsOver f).map φ = m := by
  refine ⟨(unitHomEquivSectionsTop M).symm (m.hom 1), ModuleCat.hom_ext (LinearMap.ext_ring ?_)⟩
  exact (hι M _).trans ((unitHomEquivSectionsTop M).apply_symm_apply (m.hom 1))

/-! ### `H^{-2}` of `RΓ(X, -)` of a shifted single complex -/

section Derived

attribute [local instance] HasDerivedCategory.standard

/-- **`H⁰(RΓ(X, ℱ[0])) ≅ Γ(X, ℱ)`, naturally in `ℱ`.** Degree-zero cohomology of derived global
sections of a sheaf placed in degree zero is global sections: it is the zeroth right derived
functor of `Γ(X, -)` (`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`),
which is `Γ(X, -)` itself because `Γ(X, -)` is left exact
(`CategoryTheory.Functor.rightDerivedZeroIsoSelf`). -/
def singleDerivedGlobalSectionsHomologyZeroIso :
    DerivedCategory.singleFunctor X.Modules 0 ⋙ derivedGlobalSectionsOver f ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0 ≅ secsOver f :=
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived (globalSectionsOver f)
      (derivedGlobalSectionsOver f) (derivedGlobalSectionsOverUnit f)
      (Scheme.Modules.exists_quasiIso_isKInjective X) 0 ≪≫
    (globalSectionsOver f).rightDerivedZeroIsoSelf

/-- **`Hⁱ(RΓ(X, ℱ[0])[2]) ≅ Hʲ(RΓ(X, ℱ[0]))` for `2 + i = j`**, the shift sequence of the
cohomology functors (`CategoryTheory.Functor.shiftIso`) at derived global sections of a sheaf
placed in degree zero. This is `AlgebraicGeometry.standardHomologyIsoShift` at an arbitrary
sheaf rather than at the structure sheaf. -/
def homologyShiftIsoSingle (M : X.Modules) (i j : ℤ) (h : 2 + i = j) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj
        (((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj M))⟦(2 : ℤ)⟧) ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj
        ((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj M)) :=
  ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso 2 i j h).app _

/-- **`H^{-2}(RΓ(X, ℱ[0])[2]) ≅ Γ(X, ℱ)`.** The shift sequence of the cohomology functors
(`CategoryTheory.Functor.shiftIso`) moves the two degrees onto each other, and
`AlgebraicGeometry.singleDerivedGlobalSectionsHomologyZeroIso` identifies degree zero with global
sections. At `ℱ = 𝒪_X` the source is `H^{-2}(RΓ(X, 𝒪_X)[2])`, the object
`AlgebraicGeometry.standardDerivedGlobalSectionsUnitShift` of the duality step of
[Stacks, Tag 0B4S]. -/
def homologyShiftTwoSingleIso (M : X.Modules) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).obj
        (((derivedGlobalSectionsOver f).obj
          ((DerivedCategory.singleFunctor X.Modules 0).obj M))⟦(2 : ℤ)⟧) ≅
      (secsOver f).obj M :=
  homologyShiftIsoSingle f M (-2) 0 (by norm_num) ≪≫
    (singleDerivedGlobalSectionsHomologyZeroIso f).app M

/-- **`H^{-2}` of `RΓ(X, -[0])[2]` is `Γ(X, -)`, on morphisms.** For `φ : ℳ ⟶ 𝒩` in `X.Modules`,
the map `H^{-2}(RΓ(X, φ[0])[2])` is `Γ(X, φ)` read through
`AlgebraicGeometry.homologyShiftTwoSingleIso`.

Both identifications used are components of natural isomorphisms, so this is their two
naturality squares composed. -/
theorem homologyShiftTwoSingleIso_naturality {M N : X.Modules} (φ : M ⟶ N) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).map
          ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (2 : ℤ)).map
            ((derivedGlobalSectionsOver f).map
              ((DerivedCategory.singleFunctor X.Modules 0).map φ))) ≫
        (homologyShiftTwoSingleIso f N).hom =
      (homologyShiftTwoSingleIso f M).hom ≫ (secsOver f).map φ := by
  have h2 : (2 : ℤ) + (-2) = 0 := by norm_num
  have sq₁ : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).map
          ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (2 : ℤ)).map
            ((derivedGlobalSectionsOver f).map
              ((DerivedCategory.singleFunctor X.Modules 0).map φ))) ≫
        (homologyShiftIsoSingle f N (-2) 0 h2).hom =
      (homologyShiftIsoSingle f M (-2) 0 h2).hom ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((derivedGlobalSectionsOver f).map
            ((DerivedCategory.singleFunctor X.Modules 0).map φ)) :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).shiftIso 2 (-2) 0 h2).hom.naturality _
  have sq₂ : (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((derivedGlobalSectionsOver f).map
            ((DerivedCategory.singleFunctor X.Modules 0).map φ)) ≫
        ((singleDerivedGlobalSectionsHomologyZeroIso f).app N).hom =
      ((singleDerivedGlobalSectionsHomologyZeroIso f).app M).hom ≫ (secsOver f).map φ :=
    (singleDerivedGlobalSectionsHomologyZeroIso f).hom.naturality φ
  calc (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).map
          ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (2 : ℤ)).map
            ((derivedGlobalSectionsOver f).map
              ((DerivedCategory.singleFunctor X.Modules 0).map φ))) ≫
        ((homologyShiftIsoSingle f N (-2) 0 h2).hom ≫
          ((singleDerivedGlobalSectionsHomologyZeroIso f).app N).hom)
      = ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-2)).map
            ((shiftFunctor (DerivedCategory (ModuleCat.{u} A)) (2 : ℤ)).map
              ((derivedGlobalSectionsOver f).map
                ((DerivedCategory.singleFunctor X.Modules 0).map φ))) ≫
          (homologyShiftIsoSingle f N (-2) 0 h2).hom) ≫
          ((singleDerivedGlobalSectionsHomologyZeroIso f).app N).hom :=
        (Category.assoc _ _ _).symm
    _ = ((homologyShiftIsoSingle f M (-2) 0 h2).hom ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
            ((derivedGlobalSectionsOver f).map
              ((DerivedCategory.singleFunctor X.Modules 0).map φ))) ≫
          ((singleDerivedGlobalSectionsHomologyZeroIso f).app N).hom :=
        congrArg (· ≫ ((singleDerivedGlobalSectionsHomologyZeroIso f).app N).hom) sq₁
    _ = (homologyShiftIsoSingle f M (-2) 0 h2).hom ≫
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
            ((derivedGlobalSectionsOver f).map
              ((DerivedCategory.singleFunctor X.Modules 0).map φ)) ≫
            ((singleDerivedGlobalSectionsHomologyZeroIso f).app N).hom) :=
        Category.assoc _ _ _
    _ = (homologyShiftIsoSingle f M (-2) 0 h2).hom ≫
          (((singleDerivedGlobalSectionsHomologyZeroIso f).app M).hom ≫ (secsOver f).map φ) :=
        congrArg (fun t => (homologyShiftIsoSingle f M (-2) 0 h2).hom ≫ t) sq₂
    _ = ((homologyShiftIsoSingle f M (-2) 0 h2).hom ≫
          ((singleDerivedGlobalSectionsHomologyZeroIso f).app M).hom) ≫ (secsOver f).map φ :=
        (Category.assoc _ _ _).symm

end Derived

end AlgebraicGeometry

end
