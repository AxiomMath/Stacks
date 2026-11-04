module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjectiveRepresentative
public import StacksFrontier.AlgebraicGeometry.Perfect.Coherator.QuasiCoherentDerivedPushforward
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairDerivedSections
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairLocality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffineSectionsComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedSectionsUnbounded
public import StacksFrontier.AlgebraicGeometry.UnboundedDerivedDirectImage.QuasiCoherence
public import StacksFrontier.Homology.PseudoCoherent.Relative.Finite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relative pseudo-coherence under a finite derived pushforward

Let `π : X ⟶ Y` be a finite morphism of schemes locally of finite type over a base `S`, and let
`E` be an object of `D_{QCoh}(𝒪_X)`. Then `E` is `m`-pseudo-coherent relative to `S` if and only
if `Rπ_* E` is. This is Stacks 09UK.

The whole content is a translation of Stacks 0673 — restriction of scalars along a finite map of
finite-type algebras preserves and reflects relative `m`-pseudo-coherence — into the language of
schemes, and the translation is carried out one compatible pair of affine opens at a time.

## Main results

* `AlgebraicGeometry.derivedSectionsPseudoCoherentOn'_preimage_iff`: the per-pair statement, and
  the heart of this file. At a compatible pair of affine opens `U ⊆ g ⁻¹ᵁ V` the condition of
  Stacks 09VF for `E` at `(π ⁻¹ᵁ U, V)` is the condition for `Rπ_* E` at `(U, V)`.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward`: **Stacks 09UK.**
* `AlgebraicGeometry.nonempty_derivedPreimageSectionsIso` and
  `AlgebraicGeometry.nonempty_derivedSectionsPushforwardIso`: the comparison of derived sections
  over the inverse image of an open with derived sections of the derived pushforward over it. They
  are the Stacks 0D5W pattern read on `AlgebraicGeometry.derivedSectionsUnbounded`, and they are
  public because any later comparison of two derived-sections functors needs them.
* `AlgebraicGeometry.preimage_le_of_comp`: the inverse image along a morphism over `S` of an
  open lying over `V` lies over `V`.

## Implementation notes

**What the two inputs of the source are.** Both are results of the development rather than
hypotheses. Stacks 09VF, which converts relative `m`-pseudo-coherence into a condition on the
derived sections over pairs of affine opens, is
`AlgebraicGeometry.derivedSectionsPseudoCoherentComparison'`, and it is used both for `f` and for
`g`. Clause (1) of Stacks 08D5, that `Rπ_*` carries `D_{QCoh}(𝒪_X)` into `D_{QCoh}(𝒪_Y)`, enters
as `AlgebraicGeometry.preservesQuasicoherentOnAffineTarget` in the affine-target form from which
`AlgebraicGeometry.isQuasicoherent_derivedPushforward_of_affineTarget` deduces the general case.

**How the per-pair statement is proved.** A finite morphism is affine, so `π ⁻¹ᵁ U` is affine
and `Γ(X, π ⁻¹ᵁ U)` is a module-finite algebra over `Γ(Y, U)`; both are of finite type over
`Γ(S, V)` because `f` and `g` are locally of finite type. So Stacks 0673, which is
`PseudoCoherence.isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_iff_restrictScalars`
here, compares relative `m`-pseudo-coherence of `RΓ(π ⁻¹ᵁ U, E)` over `Γ(X, π ⁻¹ᵁ U)` with that
of its restriction of scalars to `Γ(Y, U)`. What identifies that restriction with `RΓ(U, Rπ_* E)`
is Stacks 0D5W, which is `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso`.

**Where the two derived sections functors meet.** Stacks 0D5W is stated over
`Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections`, the right derived functor of
*sections over `π ⁻¹ᵁ U` with scalars already restricted*, while the condition of Stacks 09VF is
stated over `AlgebraicGeometry.derivedSectionsUnbounded`, the right derived functor of sections
alone. Restriction of scalars is exact, so the two agree, but they are different right derived
functors and the comparison has to be made: `CategoryTheory.rightDerivedObjIso` computes each of
them on a K-injective representative, where both are the termwise functor.

**The two spellings of `𝒪`-modules.** `AlgebraicGeometry.Scheme.Modules` and
`SheafOfModules (structureSheafRing X.toSheafedSpace)` are definitionally the
same category with separately declared instances, and Stacks 0D5W lives at the second spelling
while Stacks 09VF lives at the first. Definitional equality is enough for *terms* to cross, but
instance search does not cross it, and a goal that mixes the two spellings — here
`CategoryTheory.Functor.IsLocalization` for `DerivedCategory.Qh` at one spelling against
`CategoryTheory.HomotopyCategory.quasiIso` at the other — is unprovable by search. So
`CategoryTheory.rightDerivedObjIso` takes every typeclass fact it needs as an explicit
argument, and the right derived functor of the composite is rebuilt here at the `X.Modules`
spelling; it is definitionally the functor of Stacks 0D5W, the difference between the two being
confined to `Prop`-valued instance arguments.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes
the same declaration.

**Why that local instance carries a raised priority.** Every statement here is baked at the
standard model, but the locally small model of
`StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` arrives with the imports as a competing
instance of the same priority, and then the two sides of a comparison are resolved in different
categories and nothing unifies. Raising the priority of the standard model is what fixes it; a
`set_option` does not. This file is the third in the cluster to need the bump — the others are
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/AffineDerivedPresentation.lean`, at priority
`10000`, and `StacksFrontier/AlgebraicGeometry/UnboundedDerivedDirectImage/QuasiCoherence.lean`, at
`2000` — so the pattern, rather than any one of the three bumps, is the thing to fix: any module
importing downstream of `StacksFrontier/Homology/DerivedCategory/LocallySmall.lean` that wants the
standard model is exposed, and three
files working around it separately is a sign the repair belongs where the two models are
declared.

## References

* [The Stacks Project, Lemma 36.61.7 (09UK)](https://stacks.math.columbia.edu/tag/09UK)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Lemma 36.61.8 (09VF)](https://stacks.math.columbia.edu/tag/09VF)
* [The Stacks Project, Lemma 15.64.11 (0673)](https://stacks.math.columbia.edu/tag/0673)
* [The Stacks Project, Lemma 36.3.9 (08D5)](https://stacks.math.columbia.edu/tag/08D5)
* [The Stacks Project, Lemma 20.49.9 (0D5W)](https://stacks.math.columbia.edu/tag/0D5W)
* [The Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray

namespace AlgebraicGeometry

universe u

-- The priority is raised because the locally small model arrives with the imports as a competing
-- instance of the same priority; see the module docstring.
attribute [local instance 2000] HasDerivedCategory.standard

/-! ### Derived sections of a derived pushforward -/

/-- Derived sections over `π ⁻¹ᵁ U` with scalars restricted along `π` are computed by restricting
scalars after taking derived sections: the two right derived functors agree, because restriction
of scalars is exact and both are computed by the termwise functor on a K-injective complex.

The isomorphism is produced for a fixed object only, which is all that transporting a `Prop`
needs; it is not claimed to be natural in the object. -/
public lemma nonempty_derivedPreimageSectionsIso {X Y : Scheme.{u}} (π : X ⟶ Y) (U : Y.Opens)
    (E : DerivedCategory X.Modules) :
    Nonempty ((derivedPreimageSections π.toLRSHom.toShHom U).obj E ≅
      (ModuleCat.restrictScalars.{u} (π.app U).hom).mapDerivedCategory.obj
        ((derivedSectionsUnbounded X (π ⁻¹ᵁ U)).obj E)) := by
  have hres := Stacks.Cohomology.Localization.enoughKInjectives (C := X.Modules)
  obtain ⟨I, hI, ⟨e⟩⟩ := exists_isKInjective_representative hres E
  let F := Stacks.Cohomology.sectionsFunctor X (π ⁻¹ᵁ U)
  let R := ModuleCat.restrictScalars.{u} (π.app U).hom
  let D := derivedSectionsUnbounded X (π ⁻¹ᵁ U)
  let G := (F ⋙ R).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh
  let D' := G.totalRightDerived DerivedCategory.Qh (HomotopyCategory.quasiIso X.Modules (.up ℤ))
  let eD := rightDerivedObjIso hres F inferInstance D
    (derivedSectionsUnboundedUnit X (π ⁻¹ᵁ U)) inferInstance I hI
  let eD' := rightDerivedObjIso hres (F ⋙ R) inferInstance D'
    (G.totalRightDerivedUnit DerivedCategory.Qh (HomotopyCategory.quasiIso X.Modules (.up ℤ)))
    inferInstance I hI
  exact ⟨D'.mapIso e.symm ≪≫ eD'.symm ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ)).symm.app I) ≪≫
    (R.mapDerivedCategoryFactors.app _).symm ≪≫
    R.mapDerivedCategory.mapIso (eD ≪≫ D.mapIso e)⟩

/-- **Stacks 0D5W, read on the derived sections of Stacks 09VF.** For `π : X ⟶ Y` and an open
`U ⊆ Y`, the complex `RΓ(π ⁻¹ᵁ U, E)` of `Γ(Y, U)`-modules is `RΓ(U, Rπ_* E)`.

This is `Stacks.Cohomology.DerivedSectionsLeray.derivedSectionsPushforwardIso` followed by
`AlgebraicGeometry.nonempty_derivedPreimageSectionsIso`, which moves the restriction of scalars
out of the derived functor. -/
public lemma nonempty_derivedSectionsPushforwardIso {X Y : Scheme.{u}} (π : X ⟶ Y)
    (U : Y.Opens) (E : DerivedCategory X.Modules) :
    Nonempty ((ModuleCat.restrictScalars.{u} (π.app U).hom).mapDerivedCategory.obj
        ((derivedSectionsUnbounded X (π ⁻¹ᵁ U)).obj E) ≅
      (derivedSectionsUnbounded Y U).obj
        ((RingedSpace.derivedPushforward π.toLRSHom.toShHom).obj E)) :=
  ⟨(nonempty_derivedPreimageSectionsIso π U E).some.symm ≪≫
    ((derivedSectionsPushforwardIso π.toLRSHom.toShHom U).app E).symm⟩

/-! ### The per-pair statement -/

/-- The inverse image of an open over which `g` lands in `V` is an open over which `f` lands in
`V`, for `π` a morphism over `S`. -/
public lemma preimage_le_of_comp {X Y S : Scheme.{u}} (π : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)
    (hπ : π ≫ g = f) (U : Y.Opens) (V : S.Opens) (hUV : U ≤ g ⁻¹ᵁ V) :
    π ⁻¹ᵁ U ≤ f ⁻¹ᵁ V := by
  subst f
  exact fun x hx => hUV hx

open PseudoCoherence in
/-- **The per-pair content of Stacks 09UK.** Let `π : X ⟶ Y` be a finite morphism of schemes
locally of finite type over `S`, and let `U ⊆ g ⁻¹ᵁ V` be a compatible pair of affine opens of
`Y` and `S`. Then the condition of Stacks 09VF for `E` at the pair `(π ⁻¹ᵁ U, V)` holds if and
only if the condition for `Rπ_* E` at the pair `(U, V)` does.

This is Stacks 0673 for the module-finite algebra `Γ(Y, U) ⟶ Γ(X, π ⁻¹ᵁ U)` over `Γ(S, V)`,
transported along the identification of `RΓ(π ⁻¹ᵁ U, E)` with `RΓ(U, Rπ_* E)` of Stacks 0D5W. No
hypothesis on the cohomology sheaves of `E` is needed: Stacks 09VF enters only in the main theorem
below, to turn the per-pair conditions into relative `m`-pseudo-coherence. -/
public theorem derivedSectionsPseudoCoherentOn'_preimage_iff {X Y S : Scheme.{u}} (π : X ⟶ Y)
    (f : X ⟶ S) (g : Y ⟶ S) (hπ : π ≫ g = f) [IsFinite π] [LocallyOfFiniteType f]
    [LocallyOfFiniteType g] (E : DerivedCategory X.Modules) (m : ℤ)
    {U : Y.Opens} (hU : IsAffineOpen U) {V : S.Opens} (hV : IsAffineOpen V)
    (hUV : U ≤ g ⁻¹ᵁ V) :
    f.DerivedSectionsPseudoCoherentOn' E m (hU.preimage π) hV
        (preimage_le_of_comp π f g hπ U V hUV) ↔
      g.DerivedSectionsPseudoCoherentOn'
        ((RingedSpace.derivedPushforward π.toLRSHom.toShHom).obj E) m hU hV hUV := by
  have hXV := preimage_le_of_comp π f g hπ U V hUV
  let : Algebra Γ(S, V) Γ(Y, U) := (g.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(X, π ⁻¹ᵁ U) := (f.appLE V (π ⁻¹ᵁ U) hXV).hom.toAlgebra
  let : Algebra Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := (π.app U).hom.toAlgebra
  have : Algebra.FiniteType Γ(S, V) Γ(Y, U) := g.finiteType_appLE hV hU hUV
  have : Algebra.FiniteType Γ(S, V) Γ(X, π ⁻¹ᵁ U) :=
    f.finiteType_appLE hV (hU.preimage π) hXV
  have : Module.Finite Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := π.finite_app U hU
  have : IsScalarTower Γ(S, V) Γ(Y, U) Γ(X, π ⁻¹ᵁ U) := by
    subst f
    exact .of_algebraMap_eq' (by
      simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.hom_comp,
        Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE])
  refine (isRelativelyPseudoCoherentFrom_and_isRelativelyPseudoCoherent_iff_restrictScalars
    (R := Γ(S, V)) (A := Γ(Y, U)) ((derivedSectionsUnbounded X (π ⁻¹ᵁ U)).obj E) m).1.trans ?_
  obtain ⟨e⟩ := nonempty_derivedSectionsPushforwardIso π U E
  exact ⟨RingHom.isRelativelyPseudoCoherentFrom_of_iso (R := Γ(S, V)) e m,
    RingHom.isRelativelyPseudoCoherentFrom_of_iso (R := Γ(S, V)) e.symm m⟩

/-! ### Stacks 09UK -/

/-- **Stacks 09UK.** Let `π : X ⟶ Y` be a finite morphism of schemes locally of finite type over
a base `S`, and let `E` be an object of the derived category of `𝒪_X`-modules with quasi-coherent
cohomology. Then `E` is `m`-pseudo-coherent relative to `S` if and only if `Rπ_* E` is.

The proof is the translation the source asks for. In one direction Stacks 09VF, which is
`AlgebraicGeometry.derivedSectionsPseudoCoherentComparison'`, turns relative `m`-pseudo-coherence
of `E` into its per-pair condition at *every* compatible pair of affine opens, and
`AlgebraicGeometry.derivedSectionsPseudoCoherentOn'_preimage_iff` carries the condition at
`(π ⁻¹ᵁ U, V)` to the condition at `(U, V)` for `Rπ_* E`, at every pair of the target. In the
other direction the covers the source provides for `Rπ_* E` cannot be used directly — an affine
open of `X` need not be an inverse image — so the "exists an affine cover" form of Stacks 09VF is
used instead and its covers are pulled back along `π`, which is where the morphism being over `S`
enters. That `Rπ_* E` again has quasi-coherent cohomology, so that Stacks 09VF applies to it, is
clause (1) of Stacks 08D5 by way of
`AlgebraicGeometry.preservesQuasicoherentOnAffineTarget`. -/
@[stacks 09UK,
  sga "6 III 2.1" "finite morphism, QCoh",
  sga "6 III 2.2" "special case",
  sga "6 IV 3.3.2" "3.3.2.3"]
public theorem Scheme.Hom.isPseudoCoherentFrom_iff_derivedPushforward
    {X Y S : Scheme.{u}} (π : X ⟶ Y) (f : X ⟶ S) (g : Y ⟶ S)
    (hπ : π ≫ g = f) [IsFinite π] [LocallyOfFiniteType f] [LocallyOfFiniteType g]
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (m : ℤ) :
    Scheme.Hom.IsPseudoCoherentFrom f E m ↔
      Scheme.Hom.IsPseudoCoherentFrom g
        ((RingedSpace.derivedPushforward π.toLRSHom.toShHom).obj E) m := by
  have hF : ∀ i : ℤ, ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((RingedSpace.derivedPushforward π.toLRSHom.toShHom).obj E)).IsQuasicoherent :=
    isQuasicoherent_derivedPushforward_of_affineTarget preservesQuasicoherentOnAffineTarget π
      ⟨E, hE⟩
  constructor
  · intro h
    have h3 := ((derivedSectionsPseudoCoherentComparison' f E hE m).out 1 3).1 h
    refine ((derivedSectionsPseudoCoherentComparison' g _ hF m).out 1 3).2 fun U hU V hV e => ?_
    exact (derivedSectionsPseudoCoherentOn'_preimage_iff π f g hπ E m hU hV e).1
      (h3 _ (hU.preimage π) _ hV _)
  · intro h
    obtain ⟨ι, V, hVtop, hV⟩ := ((derivedSectionsPseudoCoherentComparison' g _ hF m).out 1 2).1 h
    apply ((derivedSectionsPseudoCoherentComparison' f E hE m).out 1 2).2
    refine ⟨ι, V, hVtop, fun i => ?_⟩
    obtain ⟨κ, W, hWcover, hW⟩ := hV i
    refine ⟨κ, fun j => ⟨π ⁻¹ᵁ (W j).1, (W j).2.preimage π⟩, ?_, fun j => ?_⟩
    · show (⨆ j, π ⁻¹ᵁ (W j).1) = f ⁻¹ᵁ (V i).1
      rw [← π.preimage_iSup, hWcover, ← hπ]
      rfl
    · obtain ⟨hWV, hsec⟩ := hW j
      exact ⟨preimage_le_of_comp π f g hπ (W j).1 (V i).1 hWV,
        (derivedSectionsPseudoCoherentOn'_preimage_iff π f g hπ E m (W j).2 (V i).2 hWV).2 hsec⟩

end AlgebraicGeometry

end
