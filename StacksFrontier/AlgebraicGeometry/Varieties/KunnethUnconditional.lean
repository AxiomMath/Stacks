module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.KunnethGlobalCupProduct
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.SingleComparison
public import StacksFrontier.AlgebraicGeometry.HigherDirectImage.RightDerivedPlus
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethScalarTransport
public import StacksFrontier.AlgebraicGeometry.Varieties.Kunneth
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.HgroupAndUnboundedDerivedSections

/-!
# The Künneth formula over a field, with nothing carried

`AlgebraicGeometry.nonempty_kunnethIso` of `StacksFrontier.AlgebraicGeometry.Varieties.Kunneth`
proves the decomposition

`Hⁿ(X ×_k Y, pr₁^*ℱ ⊗ pr₂^*𝒢) ≅ ⨁_{p + q = n} Hᵖ(X, ℱ) ⊗_k H^q(Y, 𝒢)`

from a datum `AlgebraicGeometry.KunnethDerivedData`, which carries the derived global
comparison of [Stacks, Tag 0FLQ].  This file proves the same conclusion without that datum:
`AlgebraicGeometry.nonempty_kunnethIso_of_quasiSeparated` holds under the hypotheses of
[Stacks, Tag 0BEF] alone — `X` and `Y` quasi-compact and quasi-separated over the field, `ℱ` and
`𝒢` quasi-coherent.

## What is not achieved

The conclusion is still `Nonempty (… ≅ …)` rather than a named isomorphism, and for that reason
**no tag is registered here**.  The source asserts a *canonical* isomorphism, and exactly one
link of the chain below is non-canonical: the Künneth splitting of the derived tensor product
over a field in degree `n`,
`CochainComplex.Kunneth.nonempty_derivedTensorHomologyNatIso`, which is built from a chosen
quasi-isomorphism of a complex of vector spaces with its own cohomology.  Its canonical form in
degree zero is `CochainComplex.Kunneth.isIso_cohomologyTensorProduct_map_zero` of
`StacksFrontier.Homology.KunnethDegreeZero`: the cohomology product of [Stacks, Tag 068H] in degree
zero is an isomorphism over a field.  Every other link is a named map: the global Künneth
morphism of [Stacks, Tag 0G7V], the derived external tensor comparison, the comparison of derived
sections with the classical right derived functor, and base change along a ring isomorphism.  The
canonical isomorphism of [Stacks, Tag 0BEF] is proved by another route, as
`AlgebraicGeometry.KunnethQcqs.isIso_kunnethMap`.

## The chain

Write `A = Γ(Spec k, 𝒪)`, which is isomorphic to `k` but not equal to it.

1. `AlgebraicGeometry.gammaSectionsField`: `A` is a field, by transport along
   `AlgebraicGeometry.Scheme.ΓSpecIso`.  This is what makes the Künneth splitting over a field
   available at `D(A)`, the derived category the global Künneth morphism is stated at.
2. `AlgebraicGeometry.homologyIso_sectionsOverBase`: the degree-`n` cohomology of
   `RΓ(X, ℱ[0]) ∈ D(A)` is `Rⁿ Γ(X, -)` at `ℱ` with scalars restricted along `f^♯`.  This is
   `Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived` — the bridge between the
   derived-category and the classical right derived functor — composed with
   `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`, which pulls the exact restriction
   of scalars out of the right derived functor.
   `AlgebraicGeometry.isZero_homology_sectionsOverBase` is its vanishing in negative degrees,
   which the Künneth splitting asks for; it goes through
   `Stacks.DerivedIndexing.rightDerivedPlusIsoRes` and part (1) of [Stacks, Tag 05TD].
3. `AlgebraicGeometry.nonempty_kunnethBaseIso`: the global Künneth morphism of
   [Stacks, Tag 0G7V] at the two modules placed in degree zero is an isomorphism
   (`Stacks.Cohomology.DerivedKunneth.isIso_kunnethGlobalMapScheme`, the second conclusion of
   [Stacks, Tag 0FLQ] with no hypothesis beyond the tag's own), and its target is
   `RΓ(X ×_k Y, (pr₁^*ℱ ⊗ pr₂^*𝒢)[0])` by
   `AlgebraicGeometry.derivedExternalTensorSingleIso`.  Tor independence is automatic over a
   field (`AlgebraicGeometry.torIndependent_over_field`), the base `Spec k` is affine, and the
   structure morphisms are quasi-compact and quasi-separated because their source is.
4. The Künneth splitting over the field `A`, and the transport of the resulting direct sum of
   tensor products from `A`-modules to `k`-modules along
   `Stacks.ModuleCat.RingIsoTransport.restrictDirectSumTensorIso`.
   `AlgebraicGeometry.cohomologyOverField_eq_restrictScalars` is the bookkeeping that the
   `k`-structure of `AlgebraicGeometry.cohomologyOverField` is the `A`-structure restricted
   further along `k ≅ A`.

## References

* [Stacks Project, Tag 0BEF](https://stacks.math.columbia.edu/tag/0BEF)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 0G7V](https://stacks.math.columbia.edu/tag/0G7V)
* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
* [Stacks Project, Tag 05TD](https://stacks.math.columbia.edu/tag/05TD)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace
open scoped DirectSum TensorProduct

attribute [local instance 100000] HasDerivedCategory.standard

universe u v

namespace AlgebraicGeometry

open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedSectionsLeray
  (sectionsOverOpen preimageSections derivedPreimageSections derivedPreimageSectionsUnit)
open Stacks.Cohomology.GlobalKunneth (baseRing tensorBase sectionsOverBase)

/-! ### The global functions on `Spec k` -/

/-- `Γ(Spec k, 𝒪)` is isomorphic to `k`, as a ring. -/
def gammaSectionsRingEquiv (k : Type u) [Field k] :
    (baseRing (Spec (.of k)).toRingedSpace : Type u) ≃+* k :=
  (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv

/-- **`Γ(Spec k, 𝒪)` is a field**, being isomorphic to `k`.  It is not introduced as an instance:
its `CommRing` structure is the one `CommRingCat` carries, and a second path to that structure
through this field would make instance search pick a `Semiring` that the modules of
`ModuleCat ↥Γ(Spec k, 𝒪)` are not stated at. -/
@[instance_reducible]
def gammaSectionsField (k : Type u) [Field k] :
    Field (baseRing (Spec (.of k)).toRingedSpace : Type u) :=
  ((gammaSectionsRingEquiv k).toMulEquiv.isField (Field.toIsField k)).toField

/-- `k ⟶ Γ(Spec k, 𝒪)` on global sections. -/
abbrev gammaSectionsInv (k : Type u) [Field k] :
    k →+* (baseRing (Spec (.of k)).toRingedSpace : Type u) :=
  ((gammaSectionsRingEquiv k).symm : k →+* (baseRing (Spec (.of k)).toRingedSpace : Type u))

/-! ### The cohomology of derived sections over the base -/

section Base

variable {V S : Scheme.{u}} (c : V ⟶ S)

/-- `Γ(S, 𝒪_S) ⟶ Γ(V, 𝒪_V)` on global sections, as a ring homomorphism. -/
abbrev structureSheafGlobalHom : (baseRing S.toRingedSpace : Type u) →+*
    ((structureSheafRing V.toRingedSpace).obj.obj (op (⊤ : Opens V.carrier))) :=
  ((structureSheafHom c.toLRSHom.toShHom).hom.app (op (⊤ : Opens S.carrier))).hom

/-- Restriction of scalars along `Γ(S, 𝒪_S) ⟶ Γ(V, 𝒪_V)` preserves homology. -/
instance : (ModuleCat.restrictScalars.{u} (structureSheafGlobalHom c)).PreservesHomology :=
  Stacks.Cohomology.CechAcyclic.preservesHomology_restrictScalars _

/-- **`Hⁿ(RΓ(V, 𝒩[0]))`, over `Γ(S, 𝒪_S)`, is `Rⁿ Γ(V, -)` at `𝒩`** with scalars restricted
along `c^♯`. -/
def homologyIso_sectionsOverBase (n : ℕ) :
    DerivedCategory.singleFunctor V.Modules 0 ⋙ sectionsOverBase c.toLRSHom.toShHom ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) (n : ℤ) ≅
      (sectionsOverOpen V.toRingedSpace ⊤).rightDerived n ⋙
        ModuleCat.restrictScalars.{u} (structureSheafGlobalHom c) :=
  haveI : (preimageSections c.toLRSHom.toShHom (⊤ : Opens S.carrier)).Additive :=
    Stacks.Cohomology.DerivedSectionsLeray.preimageSections_additive _ _
  Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (preimageSections c.toLRSHom.toShHom ⊤) (derivedPreimageSections c.toLRSHom.toShHom ⊤)
      (derivedPreimageSectionsUnit c.toLRSHom.toShHom ⊤)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective
        V.toRingedSpace) n ≪≫
    (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso
      (sectionsOverOpen V.toRingedSpace ⊤)
      (ModuleCat.restrictScalars.{u} (structureSheafGlobalHom c))
      (preimageSections c.toLRSHom.toShHom ⊤) (Iso.refl _) n).symm

/-- `Hⁿ(RΓ(V, 𝒩[0]))` is the `ℤ`-indexed right derived functor of sections over `c⁻¹ ⊤`, in
every degree. -/
def homologyPlusIso_sectionsOverBase (n : ℤ) :
    DerivedCategory.singleFunctor V.Modules 0 ⋙ sectionsOverBase c.toLRSHom.toShHom ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) n ≅
      (preimageSections c.toLRSHom.toShHom ⊤).rightDerivedPlus n :=
  haveI : (preimageSections c.toLRSHom.toShHom (⊤ : Opens S.carrier)).Additive :=
    Stacks.Cohomology.DerivedSectionsLeray.preimageSections_additive _ _
  Functor.isoWhiskerRight (Stacks.DerivedFunctor.singleIsoResCompQh (A := V.Modules))
      (derivedPreimageSections c.toLRSHom.toShHom ⊤ ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) n) ≪≫
    Stacks.DerivedFunctor.resCompQhReassocIso (derivedPreimageSections c.toLRSHom.toShHom ⊤) n ≪≫
    Functor.isoWhiskerRight (Stacks.DerivedFunctor.resCompUnitIso
        (preimageSections c.toLRSHom.toShHom ⊤) (derivedPreimageSections c.toLRSHom.toShHom ⊤)
        (derivedPreimageSectionsUnit c.toLRSHom.toShHom ⊤)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective
          V.toRingedSpace)).symm
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) n) ≪≫
    Stacks.DerivedFunctor.resCompMapQhHomologyIso (preimageSections c.toLRSHom.toShHom ⊤) n ≪≫
    Functor.isoWhiskerLeft (Stacks.DerivedIndexing.resH (C := V.Modules) ⋙
        (preimageSections c.toLRSHom.toShHom ⊤).mapHomotopyCategory (ComplexShape.up ℤ))
      (DerivedCategory.homologyFunctorFactorsh
        (ModuleCat.{u} (baseRing S.toRingedSpace)) n) ≪≫
    (Stacks.DerivedIndexing.rightDerivedPlusIsoRes
      (preimageSections c.toLRSHom.toShHom ⊤) n).symm

/-- **The cohomology of `RΓ(V, 𝒩[0])` over the base vanishes in negative degrees**, by part (1)
of [Stacks, Tag 05TD]. -/
lemma isZero_homology_sectionsOverBase (n : ℤ) (hn : n < 0) (N : V.Modules) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing S.toRingedSpace)) n).obj
      ((sectionsOverBase c.toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor V.Modules 0).obj N))) :=
  have : (preimageSections c.toLRSHom.toShHom (⊤ : Opens S.carrier)).Additive :=
    Stacks.Cohomology.DerivedSectionsLeray.preimageSections_additive _ _
  (Stacks.RightDerivedPlus.isZero_rightDerivedPlus_obj
    (preimageSections c.toLRSHom.toShHom ⊤) n hn N).of_iso
      ((homologyPlusIso_sectionsOverBase c n).app N)

end Base

/-! ### The global Künneth isomorphism at two modules in degree zero -/

section Main

variable (k : Type u) [Field k] {X Y : Scheme.{u}}

/-- `RΓ(X, ℱ[0])`, an object of `D(Γ(Spec k, 𝒪))`. -/
abbrev baseSectionsSingle (f : X ⟶ Spec (.of k)) (F : X.Modules) :
    DerivedCategory (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) :=
  (sectionsOverBase f.toLRSHom.toShHom).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)

/-- **The derived global Künneth comparison of [Stacks, Tag 0FLQ] at two quasi-coherent modules
placed in degree zero**: over a field the derived tensor product over `Γ(Spec k, 𝒪)` of
`RΓ(X, ℱ[0])` and `RΓ(Y, 𝒢[0])` is `RΓ(X ×_k Y, (pr₁^*ℱ ⊗ pr₂^*𝒢)[0])`.

The isomorphism is the global Künneth morphism of [Stacks, Tag 0G7V], invertible by
`Stacks.Cohomology.DerivedKunneth.isIso_kunnethGlobalMapScheme`, followed by
`AlgebraicGeometry.derivedExternalTensorSingleIso`, which identifies the derived external tensor
product of two modules in degree zero with their external tensor product in degree zero. -/
theorem nonempty_kunnethBaseIso (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] :
    Nonempty (((tensorBase (Spec (.of k)).toRingedSpace).obj (baseSectionsSingle k f F)).obj
        (baseSectionsSingle k g G) ≅
      (sectionsOverBase (pullback.fst f g ≫ f).toLRSHom.toShHom).obj
        ((DerivedCategory.singleFunctor (pullback f g).Modules 0).obj
          (externalTensorSheaf f g F G))) := by
  have hQ : ∀ (W : Scheme.{u}) (M : W.Modules), M.IsQuasicoherent →
      IsQCohAll ((DerivedCategory.singleFunctor W.Modules 0).obj M) := by
    intro W M hM j
    have hcz : (SheafOfModules.isQuasicoherent W.ringCatSheaf).ContainsZero :=
      containsZero_isQuasicoherent W
    have e : (DerivedCategory.homologyFunctor W.Modules j).obj
        ((DerivedCategory.singleFunctor W.Modules 0).obj M) ≅
        ((HomologicalComplex.single W.Modules (ComplexShape.up ℤ) 0).obj M).homology j :=
      (DerivedCategory.homologyFunctor W.Modules j).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ W.Modules 0).app M) ≪≫
        (DerivedCategory.homologyFunctorFactors W.Modules j).app _
    by_cases h0 : j = 0
    · subst h0
      exact (SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_iso
        (e ≪≫ HomologicalComplex.singleObjHomologySelfIso _ _ _).symm hM
    · exact (SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_iso e.symm
        ((SheafOfModules.isQuasicoherent W.ringCatSheaf).prop_of_isZero
          (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M j h0))
  have hiso := Stacks.Cohomology.DerivedKunneth.isIso_kunnethGlobalMapScheme f g
    (torIndependent_over_field k f g) ((DerivedCategory.singleFunctor X.Modules 0).obj F)
    ((DerivedCategory.singleFunctor Y.Modules 0).obj G) (hQ X F ‹_›) (hQ Y G ‹_›)
  exact ⟨@asIso _ _ _ _ _ hiso ≪≫
    (sectionsOverBase (pullback.fst f g ≫ f).toLRSHom.toShHom).mapIso
      (derivedExternalTensorSingleIso k f g F G)⟩

end Main

/-! ### `cohomologyOverField` through the global functions on the base -/

/-- The structure morphism on global sections, read through `Γ(Spec k, 𝒪) ≅ k`: the ring
homomorphism `k ⟶ Γ(X, 𝒪_X)` defining the `k`-structure of
`AlgebraicGeometry.cohomologyOverField` factors through `Γ(Spec k, 𝒪)`. -/
lemma structureRingHom_eq (k : Type u) [Field k] {X : Scheme.{u}} (h : X ⟶ Spec (.of k))
    (hle : (⊤ : X.Opens) ≤ h ⁻¹ᵁ ⊤) :
    ((Scheme.ΓSpecIso (.of k)).inv ≫ h.appLE ⊤ ⊤ hle).hom =
      (structureSheafGlobalHom h).comp (gammaSectionsInv k) := by
  have hA : h.appLE (⊤ : (Spec (.of k)).Opens) (⊤ : X.Opens) hle = h.app ⊤ :=
    h.appLE_eq_app (U := ⊤)
  rw [hA]
  rfl

/-- **`Hⁿ(X, 𝒩)` as a `k`-module is `Rⁿ Γ(X, -)` with its scalars restricted first to
`Γ(Spec k, 𝒪)` and then to `k`.** -/
lemma cohomologyOverField_eq_restrictScalars (k : Type u) [Field k] {X : Scheme.{u}}
    (h : X ⟶ Spec (.of k)) (N : X.Modules) (n : ℕ) :
    cohomologyOverField k h N n =
      (ModuleCat.restrictScalars.{u} (gammaSectionsInv k)).obj
        ((ModuleCat.restrictScalars.{u} (structureSheafGlobalHom h)).obj
          (((sectionsOverOpen X.toRingedSpace ⊤).rightDerived n).obj N)) := by
  unfold cohomologyOverField
  rw [structureRingHom_eq k h _]
  rfl

/-! ### The Künneth splitting over the global functions on the base -/

/-- The Künneth splitting of the derived tensor product over `Γ(Spec k, 𝒪)`, stated with the
ring structure that `CommRingCat` carries.  The field structure of
`AlgebraicGeometry.gammaSectionsField` is introduced only inside the proof, so that it does not
enter the statement, where it would compete with the `CommRingCat` one. -/
theorem nonempty_derivedTensorHomologyNatIso_base (k : Type u) [Field k]
    (K L : DerivedCategory (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)))
    (hK : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) i).obj K))
    (hL : ∀ i : ℤ, i < 0 → IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) i).obj L)) (n : ℕ) :
    Nonempty
      ((DerivedCategory.homologyFunctor
            (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) (n : ℤ)).obj
          (((CochainComplex.DerivedTensor.canonicalDerivedTensorProductFunctor
            (baseRing (Spec (.of k)).toRingedSpace : Type u)).obj K).obj L) ≅
        ModuleCat.of (baseRing (Spec (.of k)).toRingedSpace : Type u)
          (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
            TensorProduct (baseRing (Spec (.of k)).toRingedSpace : Type u)
              ((DerivedCategory.homologyFunctor
                (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) (pq.1.1 : ℤ)).obj K)
              ((DerivedCategory.homologyFunctor
                (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace))
                  (pq.1.2 : ℤ)).obj L))) := by
  let := gammaSectionsField k
  exact CochainComplex.Kunneth.nonempty_derivedTensorHomologyNatIso K L hK hL n

/-- A family of isomorphisms induces one of the direct sums of the termwise tensor products,
over `Γ(Spec k, 𝒪)`. -/
theorem nonempty_directSumTensorIso_base (k : Type u) [Field k]
    {ι : Type v} (P P' Q Q' : ι → ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace))
    (hP : ∀ i, Nonempty (P i ≅ P' i)) (hQ : ∀ i, Nonempty (Q i ≅ Q' i)) :
    Nonempty
      (ModuleCat.of (baseRing (Spec (.of k)).toRingedSpace : Type u)
          (⨁ i, TensorProduct (baseRing (Spec (.of k)).toRingedSpace : Type u) (P i) (Q i)) ≅
        ModuleCat.of (baseRing (Spec (.of k)).toRingedSpace : Type u)
          (⨁ i, TensorProduct (baseRing (Spec (.of k)).toRingedSpace : Type u)
            (P' i) (Q' i))) := by
  let := gammaSectionsField k
  exact CochainComplex.Kunneth.nonempty_directSumTensorIso_of_familyIso P P' Q Q' hP hQ

/-! ### The Künneth formula over a field, with nothing carried -/

/-- `Hⁿ(RΓ(X, ℱ[0]))`, over `Γ(Spec k, 𝒪)`. -/
private abbrev baseHomology (k : Type u) [Field k] {X : Scheme.{u}} (h : X ⟶ Spec (.of k))
    (N : X.Modules) (n : ℕ) : ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace) :=
  (DerivedCategory.homologyFunctor
    (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) (n : ℤ)).obj
      (baseSectionsSingle k h N)

/-- `Rⁿ Γ(X, -)` at `𝒩`, with scalars restricted along `h^♯` to `Γ(Spec k, 𝒪)`. -/
private abbrev baseCohomology (k : Type u) [Field k] {X : Scheme.{u}} (h : X ⟶ Spec (.of k))
    (N : X.Modules) (n : ℕ) : ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace) :=
  (ModuleCat.restrictScalars.{u} (structureSheafGlobalHom h)).obj
    (((sectionsOverOpen X.toRingedSpace ⊤).rightDerived n).obj N)

/-- **The Künneth formula over a field, under the hypotheses of [Stacks, Tag 0BEF] alone.**  For
quasi-coherent modules `ℱ` on `X` and `𝒢` on `Y`, with `X` and `Y` quasi-compact and
quasi-separated schemes over a field `k`, the cohomology of the external tensor product
`pr₁^*ℱ ⊗ pr₂^*𝒢` on `X ×_k Y` is the direct sum of the tensor products
`Hᵖ(X, ℱ) ⊗_k H^q(Y, 𝒢)` over the pairs with `p + q = n`.

This is `AlgebraicGeometry.nonempty_kunnethIso` with its carried
`AlgebraicGeometry.KunnethDerivedData` discharged: the derived global comparison that datum
stands for is the second conclusion of [Stacks, Tag 0FLQ], which holds with no hypothesis beyond
the tag's own.  No tag is registered here because the conclusion is `Nonempty (… ≅ …)` and the
source asserts a canonical isomorphism; the module docstring says which single link of the chain
is the non-canonical one. -/
theorem nonempty_kunnethIso_of_quasiSeparated (k : Type u) [Field k] {X Y : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (F : X.Modules) (G : Y.Modules) [F.IsQuasicoherent] [G.IsQuasicoherent] (n : ℕ) :
    Nonempty
      (cohomologyOverField k (pullback.fst f g ≫ f) (externalTensorSheaf f g F G) n ≅
        ModuleCat.of k
          (⨁ pq : {pq : ℕ × ℕ // pq.1 + pq.2 = n},
            TensorProduct k (cohomologyOverField k f F pq.1.1)
              (cohomologyOverField k g G pq.1.2))) := by
  obtain ⟨eK⟩ := nonempty_derivedTensorHomologyNatIso_base k
    (baseSectionsSingle k f F) (baseSectionsSingle k g G)
    (fun i hi => isZero_homology_sectionsOverBase f i hi F)
    (fun i hi => isZero_homology_sectionsOverBase g i hi G) n
  obtain ⟨eG⟩ := nonempty_kunnethBaseIso k f g F G
  obtain ⟨eS⟩ := nonempty_directSumTensorIso_base k
    (ι := {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (fun pq => baseHomology k f F pq.1.1) (fun pq => baseCohomology k f F pq.1.1)
    (fun pq => baseHomology k g G pq.1.2) (fun pq => baseCohomology k g G pq.1.2)
    (fun pq => ⟨(homologyIso_sectionsOverBase f pq.1.1).app F⟩)
    (fun pq => ⟨(homologyIso_sectionsOverBase g pq.1.2).app G⟩)
  obtain ⟨eF⟩ := CochainComplex.Kunneth.nonempty_directSumTensorIso_of_familyIso
    (ι := {pq : ℕ × ℕ // pq.1 + pq.2 = n})
    (fun pq => (ModuleCat.restrictScalars.{u} (gammaSectionsInv k)).obj
      (baseCohomology k f F pq.1.1))
    (fun pq => cohomologyOverField k f F pq.1.1)
    (fun pq => (ModuleCat.restrictScalars.{u} (gammaSectionsInv k)).obj
      (baseCohomology k g G pq.1.2))
    (fun pq => cohomologyOverField k g G pq.1.2)
    (fun pq => ⟨eqToIso (cohomologyOverField_eq_restrictScalars k f F pq.1.1).symm⟩)
    (fun pq => ⟨eqToIso (cohomologyOverField_eq_restrictScalars k g G pq.1.2).symm⟩)
  exact ⟨eqToIso (cohomologyOverField_eq_restrictScalars k (pullback.fst f g ≫ f)
      (externalTensorSheaf f g F G) n) ≪≫
    (ModuleCat.restrictScalars.{u} (gammaSectionsInv k)).mapIso
      (((homologyIso_sectionsOverBase (pullback.fst f g ≫ f) n).app
        (externalTensorSheaf f g F G)).symm ≪≫
      ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) (n : ℤ)).mapIso eG).symm ≪≫
      eK ≪≫ eS) ≪≫
    Stacks.ModuleCat.RingIsoTransport.restrictDirectSumTensorIso
      (gammaSectionsRingEquiv k).symm _ _ ≪≫ eF⟩

end AlgebraicGeometry

end
