module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.PuncturedSpectrumCompletedSections
public import StacksFrontier.CategoryTheory.Abelian.InverseSystemModuleCat

/-!
# The comparison of Tag 0DXI on a punctured spectrum, with its Milnor triangle

Let `(A, 𝔪)` be a Noetherian local ring, let `U = Spec A ∖ {𝔪}` be its punctured spectrum, let
`ℱ` be a coherent `𝒪_U`-module, let `I ⊆ A` be an ideal and let `ℒ` be a derived limit in
`D(𝒪_U)` of the adic quotient tower `n ↦ ℱ/Iⁿℱ`.  The module
`StacksFrontier/AlgebraicGeometry/FormalGeometry/PuncturedSpectrumCompletedSections.lean` proves,
under the Mittag-Leffler condition `hML` on `n ↦ H^{i-1}(U, ℱ/Iⁿℱ)`, that the comparison map
`Hⁱ(RΓ(U, ℒ)) ⟶ lim_n Hⁱ(U, ℱ/Iⁿℱ)` is an isomorphism, the comparison being characterized by
its composites with the limit projections through some morphism `a : RΓ(U, ℒ) ⟶ ∏ₙ RΓ(U, ℱₙ)`.
This file strengthens that statement by requiring `a` to fit into the Milnor triangle of the
system `n ↦ RΓ(U, ℱₙ)`, which is what pins the comparison map down.

*Why the morphism `a` carries the distinguished-triangle requirement.*  Given `a`, the map `q` is
pinned, since a morphism into a limit is determined by its composites with the projections and
the `op n` are all the objects of `ℕᵒᵖ`; but `a ↦ q` is additive, so a bare `∃ a` would only say
that the subgroup of `Hom(Hⁱ(RΓ(U, ℒ)), lim_n Hⁱ(U, ℱₙ))` swept out by all of
`Hom(RΓ(U, ℒ), ∏ₙ RΓ(U, ℱₙ))` contains an isomorphism.  Requiring `Triangle.mk a d b` to be
distinguished, where `d` is the Milnor difference map, says that `a` exhibits `RΓ(U, ℒ)` as a
derived limit of that system.  This is also enough: the cone of `d` is unique up to isomorphism,
so two such maps out of the same object differ by an automorphism of it, and whether the induced
`q` is an isomorphism does not depend on which one is taken.  The requirement costs nothing in
the proof:
`Stacks.Cohomology.DerivedSectionsOverBase.exists_shortExact_homology_derivedSectionsOver`
produces `a` together with `b` and the proof that the triangle is distinguished.

The Mittag-Leffler condition is asked for, not proved, so no declaration here carries a
`@[stacks 0DXI]` attribute.  The condition is proved, in every degree, for the adic quotient
tower of a coherent module in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/PuncturedSpectrumCohomologyMittagLeffler.lean`,
and Tag 0DXI itself, with the derived completion `RΓ(U, ℱ)^∧` on the left, is registered in
`StacksFrontier/AlgebraicGeometry/FormalGeometry/PuncturedSpectrumDerivedCompletion.lean`.

## Main results

* `Stacks.Algebraization.exists_milnorTriangle_isIso_toLimit_homology_puncturedSpectrumSections`
  — the comparison map, through a map `a` fitting into the Milnor triangle, exists and is an
  isomorphism, in every degree `i`, the Mittag-Leffler condition being asked for in the single
  degree `i - 1`.
* `Stacks.Algebraization.exists_homologyIso_limit_puncturedSpectrumSections` — the same
  conclusion read as an isomorphism of `A`-modules, carrying the characterization of the
  comparison map rather than asserting an abstract isomorphism.
* `Stacks.Algebraization.exists_isDerivedLimit_single_puncturedSpectrum` — an inverse system of
  `𝒪_U`-modules placed in degree zero has a derived limit in `D(𝒪_U)`, so the hypothesis `hL`
  of those statements names the object `ℒ` and does not restrict them.
* `Stacks.Algebraization.epi_milnorDifference_moduleCat_of_isMittagLefflerCategorical` — the
  vanishing of the first derived inverse limit of a Mittag-Leffler system of modules, for
  modules in an arbitrary universe.

## References

* [Stacks Project, Tag 0A0K](https://stacks.math.columbia.edu/tag/0A0K)
* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
* [Stacks Project, Tag 0DX1](https://stacks.math.columbia.edu/tag/0DX1)
* [Stacks Project, Tag 0DXI](https://stacks.math.columbia.edu/tag/0DXI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsOverBase

universe u v

namespace Stacks.Algebraization

attribute [local instance] HasDerivedCategory.standard

/-! ### Vanishing of the first derived inverse limit of a Mittag-Leffler system -/

section MittagLefflerVanishing

attribute [local instance] limAdditiveOnInvSystemAb

/-- The first derived inverse limit of a Mittag-Leffler inverse system of abelian groups
vanishes: the difference map on the product of the terms is an epimorphism. -/
private theorem epi_delta_of_isMittagLeffler_invSystemAb (G : Rlim.InvSystemAb.{v})
    (hG : (G ⋙ forget Ab).IsMittagLeffler) : Epi (Rlim.delta G) := by
  obtain ⟨RF, α, hRF, _, _, hvanish, _⟩ := Rlim.lim_hasRightDerivedFunctor_and_computations.{v}
  obtain ⟨e⟩ := Rlim.firstDerivedLimit_iso_cokernel_of_isRightDerivedFunctor RF α hRF G
  exact (Preadditive.epi_iff_isZero_cokernel _).2 (e.isZero_iff.1 (hvanish G hG))

/-- **The first derived inverse limit of a Mittag-Leffler system of modules vanishes**, for
modules in an arbitrary universe. The difference map `(xₙ) ↦ (xₙ - fₙ₊₁(xₙ₊₁))` on the product of
the terms of an inverse system of modules satisfying the Mittag-Leffler condition is an
epimorphism. -/
theorem epi_milnorDifference_moduleCat_of_isMittagLefflerCategorical {A : Type u} [Ring A]
    (F : ℕᵒᵖ ⥤ ModuleCat.{v} A) (hF : IsMittagLefflerCategorical F) :
    Epi (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj (op n)) n -
      Pi.π (fun n : ℕ ↦ F.obj (op n)) (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op) := by
  let U : ModuleCat.{v} A ⥤ Ab.{v} := forget₂ (ModuleCat.{v} A) Ab.{v}
  let X : ℕ → ModuleCat.{v} A := fun n ↦ F.obj (op n)
  let d : (∏ᶜ X) ⟶ ∏ᶜ X := Pi.lift fun n : ℕ ↦ Pi.π X n -
    Pi.π X (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let d' : (∏ᶜ fun n : ℕ ↦ U.obj (X n)) ⟶ ∏ᶜ fun n : ℕ ↦ U.obj (X n) :=
    Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ U.obj (X n)) n -
      Pi.π (fun n : ℕ ↦ U.obj (X n)) (n + 1) ≫ U.map (F.map (homOfLE (Nat.le_succ n)).op)
  have hAb : Epi d' := by
    have hdelta := epi_delta_of_isMittagLeffler_invSystemAb (F ⋙ U)
      (_root_.isMittagLeffler_forget_of_isMittagLefflerCategorical F hF)
    rwa [Rlim.delta_eq_lift] at hdelta
  have hd : U.map d ≫ piComparison U X = piComparison U X ≫ d' := by
    refine Pi.hom_ext _ _ fun n ↦ ?_
    rw [Category.assoc, piComparison_comp_π, ← U.map_comp]
    simp only [d, d', Pi.lift_comp_π, U.map_sub, U.map_comp, Category.assoc,
      Preadditive.comp_sub, piComparison_comp_π_assoc, piComparison_comp_π]
  have hmap : Epi (U.map d) := by
    rw [← epi_comp_iff_of_isIso (U.map d) (piComparison U X), hd]
    infer_instance
  exact (ModuleCat.epi_iff_surjective d).2 ((AddCommGrpCat.epi_iff_surjective _).1 hmap)

end MittagLefflerVanishing

/-! ### The comparison map with its Milnor triangle -/

section Comparison

variable (A : Type u) [CommRing A] [IsLocalRing A]

attribute [local instance] derivedCategoryModuleCatHasProductsNat
  derivedCategorySheafOfModulesHasProductsNat puncturedSpectrumRingSheaf_isMulCommutative

/-- An inverse system of `𝒪_U`-modules, placed in degree zero, has a derived limit in `D(𝒪_U)`:
the derived category of sheaves of modules on the punctured spectrum has countable products, so
the Milnor construction applies.  This is what makes the hypothesis `hL` of the comparison below
a naming of the object `ℒ = R lim ℱ/Iⁿℱ` rather than an assumption: some `ℒ` always exists, and
the comparison is asserted for every one of them. -/
theorem exists_isDerivedLimit_single_puncturedSpectrum
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) :
    ∃ L : DerivedCategory
        (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))),
      IsDerivedLimit (S ⋙ DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0) L :=
  Pretriangulated.exists_isDerivedLimit _

/-- **The comparison map of [Stacks, Tag 0DXI] for a tower satisfying the Mittag-Leffler
condition.** Let `(A, 𝔪)` be a Noetherian local ring, let `U = Spec A ∖ {𝔪}` be its punctured
spectrum, let `ℱ` be a coherent `𝒪_U`-module and let `I ⊆ A` be an ideal.  Let `S` be the adic
quotient tower `n ↦ ℱ/Iⁿℱ`, pinned down by the quotient maps `π` through the universal property
of killing multiplication by `Iⁿ`, and let `ℒ` be a derived limit of that tower in `D(𝒪_U)` —
by [Stacks, Tag 0A0K] that is the derived completion `ℱ^∧`.  Then for *every* `i` the comparison
map
`Hⁱ(RΓ(U, ℒ)) ⟶ lim_n Hⁱ(U, ℱ/Iⁿℱ)`
is an isomorphism.  It is characterized by its composites with the limit projections through a
morphism `a : RΓ(U, ℒ) ⟶ ∏ₙ RΓ(U, ℱₙ)` which is itself required to exhibit `RΓ(U, ℒ)` as a
derived limit of `n ↦ RΓ(U, ℱₙ)`, by fitting into the Milnor triangle of that system; that
requirement is what makes the conclusion about the comparison map and not about some map.

This is **not** a registration of Tag 0DXI, and carries no `@[stacks 0DXI]` attribute: the
`R¹lim` term of the Milnor short exact sequence of [Stacks, Tag 0D60] vanishes here because the
inverse system `n ↦ H^{i-1}(U, ℱ/Iⁿℱ)` is Mittag-Leffler, which is the hypothesis `hML`, and for
a countable tower the vanishing of that term is exactly what the conclusion asserts.  The
statement is the general engine, for any tower satisfying the condition in the single degree
`i - 1`; the condition for the adic quotient tower of a coherent module is proved downstream, in
every degree, and
`Stacks.Algebraization.isIso_toLimit_homology_puncturedSpectrumSections_of_isCoherent` is this
statement with `hML` discharged and nothing else changed.

By [Stacks, Tag 0BLX] `RΓ(U, ℱ^∧)` is the derived `I`-adic completion `RΓ(U, ℱ)^∧`, which is how
the source names the left-hand side. Tag 0DXI itself, with that left-hand side, is
`Stacks.Algebraization.isIso_toLimit_homology_derivedCompletion_puncturedSpectrumSections`, which
produces an `ℒ` together with `RΓ(U, ℒ) ≅ RΓ(U, ℱ)^∧` by
`Stacks.Algebraization.exists_isDerivedLimit_and_iso_derivedCompletion_derivedSections`
([Stacks, Tags 0A0K and 0BLX]). -/
theorem exists_milnorTriangle_isIso_toLimit_homology_puncturedSpectrumSections
    [IsNoetherianRing A] (I : Ideal A)
    (F : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    [SheafOfModules.IsCoherent F]
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    (hScoherent : ∀ n : ℕᵒᵖ, SheafOfModules.IsCoherent (S.obj n))
    (π : ∀ n : ℕᵒᵖ, F ⟶ S.obj n)
    (hπ_epi : ∀ n : ℕᵒᵖ, Epi (π n))
    (hπ_nat : ∀ {m n : ℕᵒᵖ} (h : m ⟶ n), π m ≫ S.map h = π n)
    (hπ_smul : ∀ (n : ℕ) (a : A), a ∈ I ^ n →
      (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
        π (op n) = 0)
    (hπ_univ : ∀ (n : ℕ)
      (G : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) (f : F ⟶ G),
      (∀ a ∈ I ^ n,
        (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
          f = 0) →
      ∃ g : S.obj (op n) ⟶ G, π (op n) ≫ g = f)
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))))
    (hL : IsDerivedLimit (S ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0) L)
    (i : ℤ)
    (hML : IsMittagLefflerCategorical (puncturedSpectrumCohomologySystem A S (i - 1))) :
    let Hi := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
    let RΓS : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      S ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0 ⋙
        puncturedSpectrumDerivedSections A
    let Y : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦ RΓS.obj (op n)
    let d : (∏ᶜ Y) ⟶ ∏ᶜ Y := Pi.lift fun n : ℕ ↦
      Pi.π Y n - Pi.π Y (n + 1) ≫ RΓS.map (homOfLE (Nat.le_succ n)).op
    ∃ (a : (puncturedSpectrumDerivedSections A).obj L ⟶ ∏ᶜ Y)
      (b : (∏ᶜ Y) ⟶ ((puncturedSpectrumDerivedSections A).obj L)⟦(1 : ℤ)⟧),
      Triangle.mk a d b ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) ∧
      ∃ q : Hi.obj ((puncturedSpectrumDerivedSections A).obj L) ⟶
          limit (puncturedSpectrumCohomologySystem A S i),
        (∀ n : ℕ, q ≫ limit.π (puncturedSpectrumCohomologySystem A S i) (op n) =
          Hi.map a ≫ Hi.map (Pi.π Y n)) ∧ IsIso q := by
  -- `hScoherent` and the four clauses pinning down the tower are hypotheses of the source
  -- statement; in the source they enter through Tags 0DX1 and 0A0K, that is through `hML` and
  -- `hL`, and are not consumed again by the derivation. They are recorded here so that the
  -- statement is about the adic quotient tower of a coherent module and not about an
  -- arbitrary tower.
  have _ := hScoherent
  have _ := hπ_epi
  have _ : ∀ {m n : ℕᵒᵖ} (h : m ⟶ n), π m ≫ S.map h = π n := hπ_nat
  have _ := hπ_smul
  have _ := hπ_univ
  intro Hi RΓS Y d
  obtain ⟨a, b, hT, hdata⟩ :=
    exists_shortExact_homology_derivedSectionsOver (puncturedSpectrumRingedSpace A)
      (puncturedSpectrumScalars A)
      (S ⋙ DerivedCategory.singleFunctor
        (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0) L hL
  obtain ⟨e, incl, q, w, -, -, hq, hshort⟩ := hdata i
  refine ⟨a, b, hT, q, hq, ?_⟩
  have hepi : Epi (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ (puncturedSpectrumCohomologySystem A S (i - 1)).obj (op n)) n -
        Pi.π (fun n : ℕ ↦ (puncturedSpectrumCohomologySystem A S (i - 1)).obj (op n)) (n + 1) ≫
          (puncturedSpectrumCohomologySystem A S (i - 1)).map (homOfLE (Nat.le_succ n)).op) :=
    epi_milnorDifference_of_isMittagLefflerCategorical
      (puncturedSpectrumCohomologySystem A S (i - 1)) hML
  have hincl : incl = 0 := ((Preadditive.epi_iff_isZero_cokernel _).1 hepi).eq_of_src _ _
  have : Mono q := hshort.exact.mono_g hincl
  have : Epi q := hshort.epi_g
  exact isIso_of_mono_of_epi _

/-- **The comparison of [Stacks, Tag 0DXI] under the Mittag-Leffler condition, read as an
isomorphism of `A`-modules.** In the situation of
`Stacks.Algebraization.exists_milnorTriangle_isIso_toLimit_homology_puncturedSpectrumSections`,
the comparison map exhibits the degree-`i` cohomology of `RΓ(U, ℒ)` as isomorphic to the inverse
limit of the `A`-modules `Hⁱ(U, ℱ/Iⁿℱ)`.  The isomorphism is the comparison map and not merely
some map: it carries the same characterization by the limit projections, and `a` is required to
be a derived-limit structure map of the system `n ↦ RΓ(U, ℱₙ)`, so this is the previous
statement packaged as an `≅` and not the weaker assertion that the two modules are abstractly
isomorphic.

Like that statement this one assumes the Mittag-Leffler condition and so carries no
`@[stacks 0DXI]` attribute; the form with the condition proved is
`Stacks.Algebraization.exists_homologyIso_limit_puncturedSpectrumSections_of_isCoherent`, and the
registered form of the tag is
`Stacks.Algebraization.exists_homologyIso_limit_derivedCompletion_puncturedSpectrumSections`. -/
theorem exists_homologyIso_limit_puncturedSpectrumSections
    [IsNoetherianRing A] (I : Ideal A)
    (F : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    [SheafOfModules.IsCoherent F]
    (S : ℕᵒᵖ ⥤ SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A)))
    (hScoherent : ∀ n : ℕᵒᵖ, SheafOfModules.IsCoherent (S.obj n))
    (π : ∀ n : ℕᵒᵖ, F ⟶ S.obj n)
    (hπ_epi : ∀ n : ℕᵒᵖ, Epi (π n))
    (hπ_nat : ∀ {m n : ℕᵒᵖ} (h : m ⟶ n), π m ≫ S.map h = π n)
    (hπ_smul : ∀ (n : ℕ) (a : A), a ∈ I ^ n →
      (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
        π (op n) = 0)
    (hπ_univ : ∀ (n : ℕ)
      (G : SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) (f : F ⟶ G),
      (∀ a ∈ I ^ n,
        (baseSmul (puncturedSpectrumRingedSpace A) (puncturedSpectrumScalars A) a).asHom.app F ≫
          f = 0) →
      ∃ g : S.obj (op n) ⟶ G, π (op n) ≫ g = f)
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))))
    (hL : IsDerivedLimit (S ⋙ DerivedCategory.singleFunctor
      (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0) L)
    (i : ℤ)
    (hML : IsMittagLefflerCategorical (puncturedSpectrumCohomologySystem A S (i - 1))) :
    let Hi := DerivedCategory.homologyFunctor (ModuleCat.{u} A) i
    let RΓS : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{u} A) :=
      S ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{u} (structureSheafRing (puncturedSpectrumRingedSpace A))) 0 ⋙
        puncturedSpectrumDerivedSections A
    let Y : ℕ → DerivedCategory (ModuleCat.{u} A) := fun n ↦ RΓS.obj (op n)
    let d : (∏ᶜ Y) ⟶ ∏ᶜ Y := Pi.lift fun n : ℕ ↦
      Pi.π Y n - Pi.π Y (n + 1) ≫ RΓS.map (homOfLE (Nat.le_succ n)).op
    ∃ (a : (puncturedSpectrumDerivedSections A).obj L ⟶ ∏ᶜ Y)
      (b : (∏ᶜ Y) ⟶ ((puncturedSpectrumDerivedSections A).obj L)⟦(1 : ℤ)⟧),
      Triangle.mk a d b ∈ distTriang (DerivedCategory (ModuleCat.{u} A)) ∧
      ∃ e : Hi.obj ((puncturedSpectrumDerivedSections A).obj L) ≅
          limit (puncturedSpectrumCohomologySystem A S i),
        ∀ n : ℕ, e.hom ≫ limit.π (puncturedSpectrumCohomologySystem A S i) (op n) =
          Hi.map a ≫ Hi.map (Pi.π Y n) := by
  intro Hi RΓS Y d
  obtain ⟨a, b, hT, q, hq, hiso⟩ :=
    exists_milnorTriangle_isIso_toLimit_homology_puncturedSpectrumSections A I F S
      hScoherent π hπ_epi hπ_nat hπ_smul hπ_univ L hL i hML
  exact ⟨a, b, hT, asIso q, hq⟩

end Comparison

end Stacks.Algebraization

end
