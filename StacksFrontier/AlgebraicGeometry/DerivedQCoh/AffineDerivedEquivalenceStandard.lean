module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence

/-!
# The derived Spec–Γ equivalence at the standard model

Let `R` be a commutative ring. This file proves that derived sheafification
`AlgebraicGeometry.derivedTilde : D(R) ⥤ D_QCoh(𝒪_{Spec R})` is an equivalence of triangulated
categories when both derived categories are taken at `CategoryTheory.HasDerivedCategory.standard`,
and records the resulting translation of morphism groups: the derived functor
`(AlgebraicGeometry.tilde.functor R).mapDerivedCategory : D(R) ⥤ D(𝒪_{Spec R})` is fully
faithful, and its essential image is exactly the complexes with quasi-coherent cohomology.

This is the standard-model counterpart of
`StacksFrontier/AlgebraicGeometry/DerivedQCoh/AffineDerivedEquivalence.lean`; the mathematics is
that file's.

## Main definitions

* `AlgebraicGeometry.StandardModel.derivedQuasicoherent` — `D_QCoh(𝒪_{Spec R})`, the complexes of
  `𝒪_{Spec R}`-modules whose cohomology sheaves are all quasi-coherent.
* `AlgebraicGeometry.StandardModel.derivedTildeQuasicoherentAdjunction` — derived sheafification
  is left adjoint to the restriction of `RΓ(Spec R, -)` to `D_QCoh(𝒪_{Spec R})`.
* `AlgebraicGeometry.StandardModel.mapDerivedCategoryFullyFaithful` — the derived functor of `~`
  on the whole of `D(𝒪_{Spec R})` is fully faithful.
* `AlgebraicGeometry.StandardModel.homEquiv` — the translation
  `Hom_{D(𝒪_{Spec R})}(M̃, Ñ) ≃ Hom_{D(R)}(M, N)`.

## Main results

* `AlgebraicGeometry.StandardModel.derivedTilde_isEquivalence` — derived sheafification
  `D(R) ⥤ D_QCoh(𝒪_{Spec R})` is an equivalence.
* `AlgebraicGeometry.StandardModel.derivedGlobalSectionsQuasicoherent_isEquivalence` — so is
  unbounded derived global sections `D_QCoh(𝒪_{Spec R}) ⥤ D(R)`.
* `AlgebraicGeometry.StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_unit` and
  `AlgebraicGeometry.StandardModel.isIso_derivedTildeGlobalSectionsAdjunction_counit_app` — the
  unit of the derived Spec–Γ adjunction is invertible, and its counit is invertible at every
  object with quasi-coherent cohomology.
* `AlgebraicGeometry.StandardModel.exists_iso_mapDerivedCategory` and
  `AlgebraicGeometry.StandardModel.isQuasicoherent_homology_iff_exists_iso_mapDerivedCategory` —
  a complex of `𝒪_{Spec R}`-modules has quasi-coherent cohomology if and only if it is
  isomorphic to `M̃^•` for some object `M` of `D(R)`.

## Implementation notes

**The standard model is installed at priority `10000`.** The import closure of this file
contains `StacksFrontier.Homology.DerivedCategory.LocallySmall`, whose `HasDerivedCategory`
declarations for `ModuleCat.{u} R`, `SheafOfModules.{u} R` and `X.Modules` are *global*
instances, and a global instance beats a default-priority local attribute: with the plain
`attribute [local instance] HasDerivedCategory.standard` the locally small model would be used.

*Why the proofs are repeated rather than transported.* Every input is stated at free
`[HasDerivedCategory.{w} _]` binders — `AlgebraicGeometry.derivedTilde`,
`AlgebraicGeometry.derivedTildeCompι`, `AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction`,
`AlgebraicGeometry.derivedGlobalSectionsQuasicoherent` with its exactness and shift instances,
`AlgebraicGeometry.derivedTilde_isTriangulated` and
`AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit_app_of_quasiIso` — and the two
analytic inputs, `AlgebraicGeometry.quasiIso_globalSectionsOver_map_tilde` and
`AlgebraicGeometry.isZero_homology_of_isZero_homology_globalSectionsOver`, mention no derived
category at all, so the argument runs unchanged at the standard model. Transporting instead along
an equivalence `D_loc(𝒪_{Spec R}) ≌ D_std(𝒪_{Spec R})` from `CategoryTheory.Localization.uniq`
would need a derived-functor uniqueness argument to identify the comparison with derived
sheafification and with `RΓ(Spec R, -)`, and would leave the equivalences in the type of the
morphism-group translation.

*Restricting the adjunction.* `AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction` is an
adjunction between `D(R)` and the *whole* `D(𝒪_{Spec R})`. Its counit is not invertible —
`RΓ(Spec R, E)^~ ⟶ E` fails as soon as `E` has a cohomology sheaf that is not quasi-coherent — so
the equivalence appears only after restricting the right adjoint along the fully faithful
inclusion of `D_QCoh(𝒪_{Spec R})`, which is
`CategoryTheory.Adjunction.restrictFullyFaithful`.

*Where the Hom translation lives.* The affine case of [Stacks, Tag 0DI7] meets the derived functor
of `~` in the form `(AlgebraicGeometry.tilde.functor R).mapDerivedCategory`, which is derived
sheafification followed by the inclusion of `D_QCoh(𝒪_{Spec R})`
(`AlgebraicGeometry.derivedTildeCompι`); `mapDerivedCategoryFullyFaithful` and
`exists_iso_mapDerivedCategory` are stated at that spelling for that reason.

## References

* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 08D9](https://stacks.math.columbia.edu/tag/08D9)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty AlgebraicGeometry

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.StandardModel

variable (R : CommRingCat.{u})

/-- `D_QCoh(𝒪_{Spec R})` at the standard model of the derived category: the property of a complex
of `𝒪_{Spec R}`-modules that every one of its cohomology sheaves is quasi-coherent. -/
abbrev derivedQuasicoherent : ObjectProperty (DerivedCategory (Spec R).Modules) :=
  DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)

/-- **The unit of the derived Spec–Γ adjunction is invertible.** For every object `M` of `D(R)`
the canonical map `M ⟶ RΓ(Spec R, M^~)` is an isomorphism. -/
theorem isIso_derivedTildeGlobalSectionsAdjunction_unit :
    IsIso (derivedTildeGlobalSectionsAdjunction R).val.unit := by
  have h : ∀ M : DerivedCategory (ModuleCat.{u} R),
      IsIso ((derivedTildeGlobalSectionsAdjunction R).val.unit.app M) := fun M =>
    isIso_derivedTildeGlobalSectionsAdjunction_unit_app_of_quasiIso R
      (fun M' I s hI hs => quasiIso_globalSectionsOver_map_tilde R M' s hI hs) M
  exact NatIso.isIso_of_isIso_app _

/-- **Derived sheafification is left adjoint to derived global sections on
`D_QCoh(𝒪_{Spec R})`.** The restriction of
`AlgebraicGeometry.derivedTildeGlobalSectionsAdjunction` along the fully faithful inclusion of
`D_QCoh(𝒪_{Spec R})` into `D(𝒪_{Spec R})`. -/
def derivedTildeQuasicoherentAdjunction :
    derivedTilde R ⊣ derivedGlobalSectionsQuasicoherent R :=
  Adjunction.restrictFullyFaithful (derivedTildeGlobalSectionsAdjunction R).val
    (Functor.FullyFaithful.id _) (derivedQuasicoherent R).fullyFaithfulι
    (Functor.leftUnitor _) (Functor.rightUnitor _).symm

/-- Derived sheafification followed by the inclusion of `D_QCoh(𝒪_{Spec R})` is fully faithful,
the unit of the derived Spec–Γ adjunction being invertible. -/
def derivedTildeCompιFullyFaithful :
    (derivedTilde R ⋙ (derivedQuasicoherent R).ι).FullyFaithful :=
  have := isIso_derivedTildeGlobalSectionsAdjunction_unit R
  Adjunction.fullyFaithfulLOfIsIsoUnit (derivedTildeGlobalSectionsAdjunction R).val

/-- Derived sheafification is faithful, the inclusion of `D_QCoh(𝒪_{Spec R})` being faithful. -/
instance derivedTilde_faithful : (derivedTilde R).Faithful :=
  have := (derivedTildeCompιFullyFaithful R).faithful
  Functor.Faithful.of_comp _ (derivedQuasicoherent R).ι

/-- Derived sheafification is full; see `AlgebraicGeometry.StandardModel.derivedTilde_faithful`. -/
instance derivedTilde_full : (derivedTilde R).Full :=
  have := (derivedTildeCompιFullyFaithful R).full
  have := (derivedTildeCompιFullyFaithful R).faithful
  Functor.Full.of_comp_faithful _ (derivedQuasicoherent R).ι

/-- **Derived global sections has zero kernel on `D_QCoh(𝒪_{Spec R})`.** An object of
`D(𝒪_{Spec R})` whose cohomology sheaves are quasi-coherent and whose derived global sections
vanish is itself zero. -/
theorem isZero_of_isZero_derivedGlobalSectionsQuasicoherent_obj
    (Z : (derivedQuasicoherent R).FullSubcategory)
    (hZ : IsZero ((derivedGlobalSectionsQuasicoherent R).obj Z)) : IsZero Z := by
  obtain ⟨K, ⟨e⟩⟩ : (DerivedCategory.Q (C := (Spec R).Modules)).essImage Z.obj :=
    Functor.EssSurj.mem_essImage (F := DerivedCategory.Q) Z.obj
  obtain ⟨I, s, hI, hs⟩ := Scheme.Modules.exists_quasiIso_isKInjective (Spec R) K
  -- the cohomology of `K` is that of `Z`, hence quasi-coherent
  have eHom : ∀ n : ℤ, (DerivedCategory.homologyFunctor (Spec R).Modules n).obj Z.obj ≅
      K.homology n := fun n =>
    (DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (Spec R).Modules n).app K
  have hK : ∀ n : ℤ, (K.homology n).IsQuasicoherent := fun n =>
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso (eHom n) (Z.2 n)
  -- `RΓ(Q K) = 0`
  have hRΓ : IsZero ((derivedGlobalSectionsOver (𝟙 (Spec R))).obj (DerivedCategory.Q.obj K)) :=
    IsZero.of_iso hZ ((derivedGlobalSectionsOver (𝟙 (Spec R))).mapIso e)
  have hsQ : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (C := (Spec R).Modules) s).2 hs
  have hcmp : IsIso (globalSectionsComplexComparison (𝟙 (Spec R)) I) :=
    isIso_globalSectionsComplexComparison_of_isKInjective (𝟙 (Spec R)) hI
  -- so the global sections of `I` are acyclic
  have hac : ∀ n : ℤ, IsZero ((((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I).homology n) := by
    intro n
    have hzero : IsZero (DerivedCategory.Q.obj
        (((globalSectionsOver (𝟙 (Spec R))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I)) :=
      IsZero.of_iso (IsZero.of_iso hRΓ
          ((derivedGlobalSectionsOver (𝟙 (Spec R))).mapIso
            (asIso (DerivedCategory.Q.map s))).symm)
        (asIso (globalSectionsComplexComparison (𝟙 (Spec R)) I))
    exact IsZero.of_iso
      (Stacks.SmallDerivedCategory.isZero_homologyFunctor_obj_of_isZero hzero n)
      ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) n).app _).symm
  -- hence `K` is acyclic, hence `Z` is zero
  have hKzero : ∀ n : ℤ, IsZero (K.homology n) := fun n =>
    isZero_homology_of_isZero_homology_globalSectionsOver R K hK s hI hs hac n
  have hobj : IsZero Z.obj :=
    Stacks.SmallDerivedCategory.isZero_of_isZero_homologyFunctor_obj Z.obj fun n =>
      IsZero.of_iso (hKzero n) (eHom n)
  rw [IsZero.iff_id_eq_zero]
  exact ObjectProperty.hom_ext _ (by
    rw [show ((𝟙 Z : Z ⟶ Z)).hom = 𝟙 Z.obj from rfl, hobj.eq_of_src (𝟙 Z.obj) 0]
    rfl)

/-- **Derived sheafification is an equivalence** `D(R) ≌ D_QCoh(𝒪_{Spec R})`, at the standard
model of both derived categories.

Derived sheafification is exact and fully faithful, and its right adjoint, derived global
sections, has zero kernel; by [Stacks, Tag 09J1] that is enough. -/
instance derivedTilde_isEquivalence : (derivedTilde R).IsEquivalence :=
  isEquivalence_of_fullyFaithful_of_adjunction_of_ker_eq_zero (derivedTilde R)
    (derivedGlobalSectionsQuasicoherent R) (derivedTildeQuasicoherentAdjunction R)
    (isZero_of_isZero_derivedGlobalSectionsQuasicoherent_obj R)

/-- **Unbounded derived global sections `D_QCoh(𝒪_{Spec R}) ⥤ D(R)` is an equivalence**, being
right adjoint to the equivalence `AlgebraicGeometry.derivedTilde`. -/
theorem derivedGlobalSectionsQuasicoherent_isEquivalence :
    (derivedGlobalSectionsQuasicoherent R).IsEquivalence :=
  (derivedTildeQuasicoherentAdjunction R).isEquivalence_right_of_isEquivalence_left

/-- **The counit of the derived Spec–Γ adjunction is invertible on `D_QCoh(𝒪_{Spec R})`.** For
every object `E` of `D(𝒪_{Spec R})` with quasi-coherent cohomology sheaves the canonical map
`RΓ(Spec R, E)^~ ⟶ E` is an isomorphism. The restriction cannot be dropped: the map fails to be
invertible as soon as some cohomology sheaf of `E` is not quasi-coherent. -/
theorem isIso_derivedTildeGlobalSectionsAdjunction_counit_app
    (E : (derivedQuasicoherent R).FullSubcategory) :
    IsIso ((derivedTildeGlobalSectionsAdjunction R).val.counit.app
      ((derivedQuasicoherent R).ι.obj E)) := by
  have := (derivedTildeCompιFullyFaithful R).full
  have := (derivedTildeCompιFullyFaithful R).faithful
  exact Adjunction.isIso_counit_app_of_iso _
    ((derivedQuasicoherent R).ι.mapIso ((derivedTilde R).objObjPreimageIso E).symm)

/-! ### The translation of morphism groups -/

/-- **The derived functor of `~` on the whole of `D(𝒪_{Spec R})` is fully faithful.** It is
derived sheafification followed by the inclusion of `D_QCoh(𝒪_{Spec R})`, by
`AlgebraicGeometry.derivedTildeCompι`. -/
def mapDerivedCategoryFullyFaithful : (tilde.functor R).mapDerivedCategory.FullyFaithful :=
  (derivedTildeCompιFullyFaithful R).ofIso (derivedTildeCompι R)

/-- **The morphism groups of `D(𝒪_{Spec R})` between complexes of associated sheaves are those of
`D(R)`:** `Hom_{D(𝒪_{Spec R})}(M̃^•, Ñ^•) ≃ Hom_{D(R)}(M^•, N^•)`. -/
def homEquiv (M N : DerivedCategory (ModuleCat.{u} R)) :
    ((tilde.functor R).mapDerivedCategory.obj M ⟶
      (tilde.functor R).mapDerivedCategory.obj N) ≃ (M ⟶ N) :=
  (mapDerivedCategoryFullyFaithful R).homEquiv.symm

/-- **Every object of `D_QCoh(𝒪_{Spec R})` is a complex of associated sheaves.** A complex of
`𝒪_{Spec R}`-modules all of whose cohomology sheaves are quasi-coherent is isomorphic to `M̃^•`
for some object `M` of `D(R)`. -/
theorem exists_iso_mapDerivedCategory (E : DerivedCategory (Spec R).Modules)
    (hE : ∀ n : ℤ,
      ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E).IsQuasicoherent) :
    ∃ M : DerivedCategory (ModuleCat.{u} R),
      Nonempty ((tilde.functor R).mapDerivedCategory.obj M ≅ E) := by
  let F : (derivedQuasicoherent R).FullSubcategory := ⟨E, hE⟩
  exact ⟨(derivedTilde R).objPreimage F, ⟨((derivedTildeCompι R).app _).symm ≪≫
    (derivedQuasicoherent R).ι.mapIso ((derivedTilde R).objObjPreimageIso F)⟩⟩

/-- **The essential image of the derived functor of `~` is `D_QCoh(𝒪_{Spec R})`.** A complex of
`𝒪_{Spec R}`-modules has quasi-coherent cohomology sheaves in every degree if and only if it is
isomorphic to `M̃^•` for some object `M` of `D(R)`. -/
theorem isQuasicoherent_homology_iff_exists_iso_mapDerivedCategory
    (E : DerivedCategory (Spec R).Modules) :
    (∀ n : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules n).obj E).IsQuasicoherent) ↔
      ∃ M : DerivedCategory (ModuleCat.{u} R),
        Nonempty ((tilde.functor R).mapDerivedCategory.obj M ≅ E) := by
  refine ⟨exists_iso_mapDerivedCategory R E, fun ⟨M, ⟨e⟩⟩ n => ?_⟩
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso e)
    (isQuasicoherent_homology_mapDerivedCategory_obj R M n)

end AlgebraicGeometry.StandardModel

end
