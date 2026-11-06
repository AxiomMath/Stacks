module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalSectionSmul
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.Homology.Injectives.DerivedCategory.ProductsAndCoproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections

/-!
# Derived sections over a base ring, and derived limits

Let `(X, 𝒪_X)` be a ringed space and let `ρ : A ⟶ Γ(X, 𝒪_X)` be a homomorphism from a
commutative ring `A`. Sections of a sheaf of `𝒪_X`-modules are then an `A`-module by restriction
of scalars along `ρ`, and the resulting additive functor has an unbounded total right derived
functor `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`, with no boundedness hypothesis on the complex and no
cohomological-dimension hypothesis on `X`.

This functor commutes with derived limits of inverse systems indexed by `ℕ`: if a distinguished
triangle exhibits `L` as the derived limit of `(K_n)` in `D(𝒪_X)`, then `RΓ(X, L)` is the derived
limit of `(RΓ(X, K_n))` in `D(A)`. Consequently the cohomology of `RΓ(X, L)` sits in the Milnor
short exact sequence

`0 ⟶ R¹lim Hᵖ⁻¹(X, K_n) ⟶ Hᵖ(X, L) ⟶ lim Hᵖ(X, K_n) ⟶ 0`

of the inverse system of cohomology modules of the terms.

Specializing that system to the `f`-power Koszul tower `E_n = E ⊗_{𝒪_X} (𝒪_X --fⁿ--> 𝒪_X)` of an
element `f` of `A` gives the middle column

`0 ⟶ R¹lim Hᵖ⁻¹(X, E_n) ⟶ Hᵖ(X, E^) ⟶ lim Hᵖ(X, E_n) ⟶ 0`

of the nine-term diagram of formal functions for a principal ideal, where `E^` is a derived limit
of the tower.

## Main definitions

* `Stacks.Cohomology.DerivedSectionsOverBase.sectionsOver` — global sections of a sheaf of
  `𝒪_X`-modules, as an `A`-module through `ρ`.
* `Stacks.Cohomology.DerivedSectionsOverBase.derivedSectionsOver` — the unbounded total right
  derived functor `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`, together with its unit
  `derivedSectionsOverUnit`.
* `Stacks.Cohomology.DerivedSectionsOverBase.smulComplex` — multiplication by a global section of
  the structure sheaf on a cochain complex of `𝒪_X`-modules.
* `Stacks.Cohomology.DerivedSectionsOverBase.principalKoszulComplexTower` and
  `Stacks.Cohomology.DerivedSectionsOverBase.principalKoszulTower` — the `f`-power Koszul tower
  `n ↦ E ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)`, as cochain complexes and as an inverse system in
  `D(𝒪_X)`.

## Main results

* `Stacks.Cohomology.DerivedSectionsOverBase.derivedSectionsOver_isTriangulated` — `RΓ(X, -)` is
  a triangulated functor.
* `Stacks.Cohomology.DerivedSectionsOverBase.isDerivedLimit_map_derivedSectionsOver` — derived
  sections over a base ring carry a derived limit to a derived limit.
* `Stacks.Cohomology.DerivedSectionsOverBase.exists_shortExact_homology_derivedSectionsOver` —
  the Milnor short exact sequence computing the cohomology of `RΓ(X, L)` from the cohomologies of
  the terms, with its inclusion descending the connecting morphism and its projection
  characterized by the limit projections.
* `Stacks.Cohomology.DerivedSectionsOverBase`
  `.principalKoszulTower_mappingCone_triangle_distinguished` — the `n`-th term of the Koszul tower
  is the cone of multiplication by `f^(n+1)` on `E`.
* `Stacks.Cohomology.DerivedSectionsOverBase`
  `.exists_shortExact_homology_derivedSections_principalKoszulTower` — that short exact sequence
  for the `f`-power Koszul tower.

## Implementation notes

The derived-limit statement is the general one for right derived functors (Tag 08U1), which asks
that the source be Grothendieck abelian, that countable products in the *target* abelian category
be exact, and that the underived functor preserve them. All three hold here: sheaves of modules on
a ringed space are Grothendieck abelian; countable products of `A`-modules are exact; and sections
over an open preserve all limits, as do restriction of scalars. This is what fails for derived
pushforward, whose target is again a category of sheaves of modules, where countable products are
not exact — there the preservation of products has to be read off an adjunction instead.

Only the existence of the product of the images is asserted, not assumed: `D(A)` is not known to
have countable products at this generality, so the product occurring in the derived limit of the
image system is produced as part of the conclusion, from preservation of the product in the source.

The two-term complex `𝒪_X --f^(n+1)--> 𝒪_X` is a complex of free modules of rank one, so the
derived tensor product `E ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)` is the cone of multiplication by
`f^(n+1)` on `E`, and that cone is how the tower is built here: a complex representing `E` is
chosen, and the cones of the powers of multiplication by the image of `f` on it are taken, with
transition maps induced by multiplication by `f` on the source of each cone. This is the same
model of the tower as the algebraic `PrincipalTorsionTower.principalDerivedTensorSystem`, for
which the comparison diagram of Tag 0H32 is stated, so no translation is needed to feed one into
the other. The lemma `principalKoszulTower_mappingCone_triangle_distinguished` records the Koszul
triangle `E --f^(n+1)--> E ⟶ E_n ⟶ E[1]` that pins the terms of the tower down.

The countable products of the tower that the Milnor sequence asks for are carried as hypotheses,
as they are in the general Milnor sequence. They are not vacuous: countable products exist in the
derived category of sheaves of modules on any site, by
`Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules`, and in the derived
category of modules over a ring by `Stacks.DerivedProducts.hasProductsOfShape_derivedCategory`.

## References

* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
* [Stacks Project, Tag 0H3C](https://stacks.math.columbia.edu/tag/0H3C)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray (sectionsOverOpen)

universe u

namespace Stacks.Cohomology.DerivedSectionsOverBase

attribute [local instance] HasDerivedCategory.standard

/-- Restriction of scalars preserves countable products: a product of modules is computed on the
underlying additive groups, which restriction of scalars does not change. -/
instance restrictScalars_preservesCountableProducts {R S : Type u} [Ring R] [Ring S]
    (r : R →+* S) : PreservesLimitsOfShape (Discrete ℕ) (ModuleCat.restrictScalars.{u} r) :=
  ⟨fun {_} ↦ inferInstance⟩

variable (X : RingedSpace.{u, u}) {A : Type u} [CommRing A]
  (ρ : A →+* (structureSheafRing X).obj.obj (op (⊤ : Opens X.carrier)))

/-- **Global sections over a base ring.** Sections of a sheaf of `𝒪_X`-modules, regarded as an
`A`-module by restriction of scalars along `ρ : A ⟶ Γ(X, 𝒪_X)`. -/
abbrev sectionsOver : SheafOfModules.{u} (structureSheafRing X) ⥤ ModuleCat.{u} A :=
  sectionsOverOpen X ⊤ ⋙ ModuleCat.restrictScalars ρ

/-- Global sections over a base ring is an additive functor: addition of sections of a sheaf of
modules is computed open by open, and restriction of scalars is additive. -/
instance sectionsOver_additive : (sectionsOver X ρ).Additive := inferInstance

/-- Global sections over a base ring preserve countable products: limits of sheaves of modules are
computed on sections, and restriction of scalars leaves them unchanged. -/
instance sectionsOver_preservesCountableProducts :
    PreservesLimitsOfShape (Discrete ℕ) (sectionsOver X ρ) := inferInstance

/-- Global sections over a base ring read on the homotopy category of cochain complexes of
`𝒪_X`-modules, with values in `D(A)`. Its right derived functor is `derivedSectionsOver`. -/
abbrev homotopySectionsOver :
    HomotopyCategory (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  (sectionsOver X ρ).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- **Unbounded derived sections over a base ring** `RΓ(X, -) : D(𝒪_X) ⥤ D(A)`: the total right
derived functor of `sectionsOver` on the whole unbounded derived category. It exists because every
complex of `𝒪_X`-modules admits a quasi-isomorphism into a K-injective complex. -/
abbrev derivedSectionsOver :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (ModuleCat.{u} A) :=
  (homotopySectionsOver X ρ).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-- The canonical comparison from termwise sections over a base ring to their unbounded right
derived functor. -/
abbrev derivedSectionsOverUnit :
    homotopySectionsOver X ρ ⟶ DerivedCategory.Qh ⋙ derivedSectionsOver X ρ :=
  (homotopySectionsOver X ρ).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-- The comparison exhibits `derivedSectionsOver` as the right derived functor of sections over a
base ring, which is the universal property characterizing it. -/
instance derivedSectionsOver_isRightDerivedFunctor :
    (derivedSectionsOver X ρ).IsRightDerivedFunctor (derivedSectionsOverUnit X ρ)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :=
  inferInstance

/-- **Derived sections over a base ring are triangulated.** Every object of `D(𝒪_X)` is
represented by a K-injective complex and the unit is an isomorphism there, so a distinguished
triangle may be completed inside the K-injective complexes; in particular `RΓ(X, -)` carries a
mapping cone to a mapping cone. -/
theorem derivedSectionsOver_isTriangulated :
    letI := Functor.IsRightDerivedFunctor.commShift (derivedSectionsOver X ρ)
      (derivedSectionsOverUnit X ρ)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) ℤ
    (derivedSectionsOver X ρ).IsTriangulated := by
  have _ := SheafOfModules.isGrothendieckAbelianU (structureSheafRing X)
  exact Stacks.Injectives.rightDerivedFunctor_isTriangulated (sectionsOver X ρ)
    (derivedSectionsOver X ρ) (derivedSectionsOverUnit X ρ)

/-- **Derived sections over a base ring commute with derived limits.** If a distinguished triangle
exhibits `L` as the derived limit of a countable inverse system `(K_n)` of objects of `D(𝒪_X)`,
then `RΓ(X, L)` is the derived limit of the system `(RΓ(X, K_n))` in `D(A)`; the existence of the
product of the images is part of the conclusion. -/
@[stacks 0D60 "commutation with derived limits, for derived sections over a base ring"]
theorem isDerivedLimit_map_derivedSectionsOver
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hL : IsDerivedLimit K L) :
    ∃ h : HasProduct (fun n : ℕ ↦ (derivedSectionsOver X ρ).obj (K.obj ⟨n⟩)),
      @IsDerivedLimit (DerivedCategory (ModuleCat.{u} A)) _ _ _ _ _ _
        (K ⋙ derivedSectionsOver X ρ) h ((derivedSectionsOver X ρ).obj L) := by
  obtain ⟨p, δ, hT⟩ := hL
  have _ := SheafOfModules.isGrothendieckAbelianU (structureSheafRing X)
  obtain ⟨h, δ', hT'⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor
    (sectionsOver X ρ) (derivedSectionsOver X ρ) (derivedSectionsOverUnit X ρ) K L p ⟨δ, hT⟩
  exact ⟨h, _, δ', hT'⟩

/-- **The Milnor short exact sequence for the cohomology of derived sections of a derived limit.**
With `L` the derived limit of `(K_n)` in `D(𝒪_X)`, the cohomology modules `Hʳ(X, L)` of its derived
sections over `A` fit into short exact sequences

`0 ⟶ R¹lim Hʳ⁻¹(X, K_n) ⟶ Hʳ(X, L) ⟶ lim Hʳ(X, K_n) ⟶ 0`,

where `R¹lim` is the cokernel of `1 - shift` on the product of the cohomologies. The inclusion
descends the connecting morphism of the Milnor triangle and the projection is characterized by the
limit projections.

The product of the images is taken as a hypothesis here, as it is in the general Milnor sequence;
`isDerivedLimit_map_derivedSectionsOver` provides it. -/
@[stacks 0D60 "short exact sequence, for derived sections over a base ring; both maps normalized"]
theorem exists_shortExact_homology_derivedSectionsOver
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hL : IsDerivedLimit K L) :
    let F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) := K ⋙ derivedSectionsOver X ρ
    let Y : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦ F.obj (op n)
    let d : (∏ᶜ Y) ⟶ ∏ᶜ Y := Pi.lift fun n : ℕ ↦
      Pi.π Y n - Pi.π Y (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
    ∃ (a : (derivedSectionsOver X ρ).obj L ⟶ ∏ᶜ Y)
      (b : (∏ᶜ Y) ⟶ ((derivedSectionsOver X ρ).obj L)⟦(1 : ℤ)⟧),
      let T := Triangle.mk a d b
      T ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) ∧
        ∀ r : ℤ,
          let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) r
          let H₁ := DerivedCategory.homologyFunctor (ModuleCat.{u} A) (r - 1)
          let homologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A := F ⋙ H
          let shiftedHomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A := F ⋙ H₁
          let P : ModuleCat.{u} A :=
            ∏ᶜ fun n : ℕ ↦ shiftedHomologySystem.obj (op n)
          let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (op n)) n -
              Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (op n)) (n + 1) ≫
                shiftedHomologySystem.map (homOfLE (Nat.le_succ n)).op
          ∃ (e : H₁.obj (∏ᶜ Y) ≅ P)
            (i : cokernel δ ⟶ H.obj ((derivedSectionsOver X ρ).obj L))
            (q : H.obj ((derivedSectionsOver X ρ).obj L) ⟶ limit homologySystem)
            (w : i ≫ q = 0),
            e.hom = piComparison H₁ Y ∧
              cokernel.π δ ≫ i = e.inv ≫
                DerivedCategory.HomologySequence.δ T (r - 1) r ∧
              (∀ n : ℕ, q ≫ limit.π homologySystem (op n) =
                H.map a ≫ H.map (Pi.π Y n)) ∧
              (ShortComplex.mk i q w).ShortExact := by
  obtain ⟨h, hF⟩ := isDerivedLimit_map_derivedSectionsOver X ρ K L hL
  exact DerivedCategory.isDerivedLimit_homology_shortExact _ _ hF

/-! ### The `f`-power Koszul tower -/

/-- On a ringed space the rings of sections of `structureSheafRing X`, the structure sheaf viewed
through the forgetful functor `CommRingCat ⥤ RingCat`, are commutative. -/
instance ringSheaf_isMulCommutative :
    ∀ U, IsMulCommutative ((structureSheafRing X).obj.obj U) :=
  fun U ↦ inferInstanceAs (IsMulCommutative (X.presheaf.obj U))

/-- **Multiplication by a global section on a cochain complex of `𝒪_X`-modules.** An endomorphism
of the identity functor of sheaves of modules acts on a complex degreewise; naturality in the
module is exactly commutation with the differentials. -/
def smulComplex (a : End (𝟭 (SheafOfModules.{u} (structureSheafRing X))))
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) : End C :=
  .of
    { f := fun i ↦ a.asHom.app (C.X i)
      comm' := fun i j _ ↦ (a.asHom.naturality (C.d i j)).symm }

/-- In degree `i`, `smulComplex X a C` is the component of `a` at the term `C.X i`. -/
@[simp]
lemma smulComplex_f (a : End (𝟭 (SheafOfModules.{u} (structureSheafRing X))))
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) (i : ℤ) :
    HomologicalComplex.Hom.f (smulComplex X a C).asHom i = a.asHom.app (C.X i) := rfl

/-- **Multiplication by the image of `f` in `Γ(X, 𝒪_X)`**, as an endomorphism of the identity
functor of sheaves of `𝒪_X`-modules: a global section of the structure sheaf acts on every sheaf
of modules, naturally in the module. -/
abbrev baseSmul (f : A) : End (𝟭 (SheafOfModules.{u} (structureSheafRing X))) :=
  _root_.Stacks.SheafOfModules.terminalSectionToEnd (structureSheafRing X) ⊤ isTerminalTop (ρ f)

/-- **The `f`-power Koszul tower with coefficients in a complex, as complexes.** The `n`-th term
is the cone of multiplication by `a ^ (n + 1)` on `C`, a model for
`C ⊗_{𝒪_X} (𝒪_X --a^(n+1)--> 𝒪_X)`, and the transition map out of the `(n+1)`-st term is induced
by multiplication by `a` on the source of the cone and the identity on its target. -/
abbrev principalKoszulComplexTower (a : End (𝟭 (SheafOfModules.{u} (structureSheafRing X))))
    (C : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ :=
  Functor.ofOpSequence
    (X := fun n ↦ CochainComplex.mappingCone (smulComplex X a C ^ (n + 1)).asHom)
    (fun n ↦ CochainComplex.mappingCone.map _ _ (smulComplex X a C).asHom (𝟙 C) (by
      have h : smulComplex X a C ^ (n + 1 + 1) =
          smulComplex X a C ^ (n + 1) * smulComplex X a C := pow_succ _ _
      rw [Category.comp_id, h, End.mul_asHom]))

/-- **The `f`-power Koszul tower of an object of `D(𝒪_X)`.** This is the inverse system
`n ↦ E ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)` of [Stacks, Tag 0H3C], realized as the cones of
multiplication by the powers of the image of `f` on a chosen complex representing `E`; the
two-term complex `𝒪_X --f^(n+1)--> 𝒪_X` is a complex of free modules of rank one, so no K-flat
resolution intervenes and the derived tensor product is that cone. -/
def principalKoszulTower (f : A) (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) :=
  principalKoszulComplexTower X (baseSmul X ρ f) (DerivedCategory.Q.objPreimage E) ⋙
    DerivedCategory.Q

/-- The `n`-th term of `principalKoszulTower X ρ f E` is the image in `D(𝒪_X)` of the cone of
multiplication by `f ^ (n + 1)` on the chosen complex representing `E`. -/
@[simp]
lemma principalKoszulTower_obj (f : A)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (n : ℕ) :
    (principalKoszulTower X ρ f E).obj ⟨n⟩ =
      DerivedCategory.Q.obj (CochainComplex.mappingCone
        (smulComplex X (baseSmul X ρ f) (DerivedCategory.Q.objPreimage E) ^ (n + 1)).asHom) := rfl

/-- **The Koszul triangle of the `n`-th term of the tower.** The term is the cone of
multiplication by `f ^ (n + 1)`, so there is a distinguished triangle
`E ⟶ E ⟶ E_n ⟶ E[1]` in `D(𝒪_X)` whose first map is that multiplication. This is what
identifies the terms of `principalKoszulTower` with the derived tensor products
`E ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)` of [Stacks, Tag 0H3C]. -/
theorem principalKoszulTower_mappingCone_triangle_distinguished (f : A)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (n : ℕ) :
    DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
        (smulComplex X (baseSmul X ρ f) (DerivedCategory.Q.objPreimage E) ^ (n + 1)).asHom) ∈
      distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :=
  DerivedCategory.mappingCone_triangle_distinguished _

/-- **Formal functions for a principal ideal: the middle column.** Let `(X, 𝒪_X)` be a ringed
space, let `ρ : A ⟶ Γ(X, 𝒪_X)` be a homomorphism from a commutative ring `A`, let `f ∈ A`, let
`E ∈ D(𝒪_X)`, let `E_n = E ⊗_{𝒪_X} (𝒪_X --f^(n+1)--> 𝒪_X)` be the `f`-power Koszul tower, and let
`E^` be a derived limit `Rlim E_n` of that tower. Then for every `p` the cohomology of
`RΓ(X, E^)` over `A` sits in a short exact sequence

`0 ⟶ R¹lim Hᵖ⁻¹(X, E_n) ⟶ Hᵖ(X, E^) ⟶ lim Hᵖ(X, E_n) ⟶ 0`,

where `R¹lim` is the cokernel of `1 - shift` on the product of the cohomologies. The inclusion
descends the connecting morphism of the Milnor triangle of the tower of derived sections, and the
projection is characterized by the limit projections, so neither map is an arbitrary choice.

This is `exists_shortExact_homology_derivedSectionsOver` at the Koszul tower: the middle column
of the nine-term diagram is the Milnor sequence of that one specific inverse system.  (The
right-hand column of the source's diagram is the identity on the Tate module.) -/
theorem exists_shortExact_homology_derivedSections_principalKoszulTower (f : A)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (Ehat : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hEhat : IsDerivedLimit (principalKoszulTower X ρ f E) Ehat) :
    let F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      principalKoszulTower X ρ f E ⋙ derivedSectionsOver X ρ
    let Y : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦ F.obj (op n)
    let d : (∏ᶜ Y) ⟶ ∏ᶜ Y := Pi.lift fun n : ℕ ↦
      Pi.π Y n - Pi.π Y (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
    ∃ (a : (derivedSectionsOver X ρ).obj Ehat ⟶ ∏ᶜ Y)
      (b : (∏ᶜ Y) ⟶ ((derivedSectionsOver X ρ).obj Ehat)⟦(1 : ℤ)⟧),
      let T := Triangle.mk a d b
      T ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) ∧
        ∀ p : ℤ,
          let H := DerivedCategory.homologyFunctor (ModuleCat.{u} A) p
          let H₁ := DerivedCategory.homologyFunctor (ModuleCat.{u} A) (p - 1)
          let homologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A := F ⋙ H
          let shiftedHomologySystem : ℕᵒᵖ ⥤ ModuleCat.{u} A := F ⋙ H₁
          let P : ModuleCat.{u} A :=
            ∏ᶜ fun n : ℕ ↦ shiftedHomologySystem.obj (op n)
          let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
            Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (op n)) n -
              Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (op n)) (n + 1) ≫
                shiftedHomologySystem.map (homOfLE (Nat.le_succ n)).op
          ∃ (e : H₁.obj (∏ᶜ Y) ≅ P)
            (i : cokernel δ ⟶ H.obj ((derivedSectionsOver X ρ).obj Ehat))
            (q : H.obj ((derivedSectionsOver X ρ).obj Ehat) ⟶ limit homologySystem)
            (w : i ≫ q = 0),
            e.hom = piComparison H₁ Y ∧
              cokernel.π δ ≫ i = e.inv ≫
                DerivedCategory.HomologySequence.δ T (p - 1) p ∧
              (∀ n : ℕ, q ≫ limit.π homologySystem (op n) =
                H.map a ≫ H.map (Pi.π Y n)) ∧
              (ShortComplex.mk i q w).ShortExact :=
  exists_shortExact_homology_derivedSectionsOver X ρ
    (principalKoszulTower X ρ f E) Ehat hEhat

end Stacks.Cohomology.DerivedSectionsOverBase

end
