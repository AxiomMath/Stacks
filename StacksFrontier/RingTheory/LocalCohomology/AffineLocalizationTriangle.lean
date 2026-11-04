module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
public import StacksFrontier.RingTheory.LocalCohomology.LowDegree.ExactSequence

/-!
# Derived sections on the complement of a zero locus

Let `A` be a commutative ring, `I ⊆ A` a finitely generated ideal and `U = Spec A \ V(I)`. The
affine localization triangle of Stacks 0DWR is
`RΓ_{V(I)}(M) ⟶ M ⟶ RΓ(U, M̃|U) ⟶ RΓ_{V(I)}(M)[1]`,
and this file builds two of its ingredients.

The first is the right-hand term. Taking sections on `U` is an additive functor from sheaves of
modules on `Spec A` to `A`-modules, scalars being restricted along `A ≅ Γ(Spec A, 𝒪) ⟶ Γ(U, 𝒪)`.
Sheaves of modules on a scheme form a Grothendieck abelian category, so every complex of them
admits a K-injective resolution and the total right derived functor `RΓ(U, -)` therefore exists
on the *unbounded* derived category, with no boundedness or finite-dimensionality hypothesis.

The second is the vanishing of local cohomology in negative degrees. Local cohomology
`RΓ_{V(I)}` is constructed in Stacks 0A6Q/0A6R as an abstract coreflection onto the objects of
`D(A)` with `I`-power-torsion cohomology, so nothing about where its cohomology lives is
available by construction. It follows from the universal property: if `L = RΓ_{V(I)}(M)` had
cohomology below degree zero, then the degree-`≤ -1` truncation of a complex representing `L`
would be another object with `I`-power-torsion cohomology, mapping to `L` by a map which is an
isomorphism on cohomology in degrees `≤ -1`, and which is killed by the counit `L ⟶ M` for
degree reasons alone; the universal property forces that map to vanish, hence the cohomology
too.

## Main definitions

* `Stacks.LocalCohomology.sectionsOnAffineComplement` — sections on `U = Spec A \ V(I)` of a
  sheaf of modules on `Spec A`, as an `A`-module.
* `Stacks.LocalCohomology.derivedSectionsOnAffineComplement` — its total right derived functor
  `RΓ(U, -)` on the unbounded derived category of sheaves of modules on `Spec A`.
* `Stacks.LocalCohomology.derivedSectionsOnAffineComplementUnit` — the canonical comparison
  exhibiting it as that right derived functor.

## Main results

* `Stacks.LocalCohomology.exists_quasiIso_isKInjective_specModules` — K-injective resolutions
  of complexes of sheaves of modules on `Spec A`.
* `Stacks.LocalCohomology.derivedSectionsOnAffineComplement_isRightDerivedFunctor` — the
  universal property of `RΓ(U, -)`.
* `Stacks.LocalCohomology.eq_zero_of_comp_localCohomologyCounit_eq_zero` — a morphism from an
  object with `I`-power-torsion cohomology into `RΓ_{V(I)}(K)` which the counit kills is zero.
* `Stacks.LocalCohomology.isZero_localCohomologyModule_of_neg` — `H^i_{V(I)}(M) = 0` for `i < 0`.
* `Stacks.LocalCohomology.mono_localCohomologyZeroToModule`,
  `Stacks.LocalCohomology.localCohomologyZeroToModule_injective` — injectivity of
  `H⁰_{V(I)}(M) ⟶ M`, the one statement of Stacks 0DWR that the localization triangle does not
  give.
* `Stacks.LocalCohomology.isZero_homology_complement_of_neg` — for any
  `Stacks.LocalCohomology.LocalizationTriangleData`, derived sections on `U` have no cohomology
  in negative degrees.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0A6Q](https://stacks.math.columbia.edu/tag/0A6Q)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open AlgebraicGeometry CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

/-! ### Derived sections on the affine open complement -/

/-- Sections of a sheaf of modules on `Spec A` over the open `U = Spec A \ V(I)`, regarded as an
`A`-module through `A ≅ Γ(Spec A, 𝒪)` and restriction to `U`. -/
def sectionsOnAffineComplement (A : Type u) [CommRing A] (I : Ideal A) :
    (Spec (CommRingCat.of A)).Modules ⥤ ModuleCat.{u} A :=
  SheafOfModules.evaluation (Spec (CommRingCat.of A)).ringCatSheaf
      (op (complementZeroLocus A I)) ⋙
    ModuleCat.restrictScalars
      (((Spec (CommRingCat.of A)).ringCatSheaf.obj.map
          (homOfLE (le_top : complementZeroLocus A I ≤ ⊤)).op).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)

/-- Taking sections on the affine open complement is additive. -/
instance sectionsOnAffineComplement_additive (A : Type u) [CommRing A] (I : Ideal A) :
    (sectionsOnAffineComplement A I).Additive where
  map_add := rfl

/-- Every cochain complex of sheaves of modules on `Spec A` admits a quasi-isomorphism to a
K-injective complex: sheaves of modules form a Grothendieck abelian category, and such a
category carries a functorial K-injective resolution. -/
theorem exists_quasiIso_isKInjective_specModules (A : Type u) [CommRing A]
    (K : CochainComplex (Spec (CommRingCat.of A)).Modules ℤ) :
    ∃ (J : CochainComplex (Spec (CommRingCat.of A)).Modules ℤ) (f : K ⟶ J),
      J.IsKInjective ∧ QuasiIso f :=
  ⟨_, (Stacks.Injectives.kInjectiveResolutionInclusion
    (Spec (CommRingCat.of A)).Modules).app K, inferInstance, inferInstance⟩

/-- Pointwise existence of the unbounded right derived functor of sections on
`U = Spec A \ V(I)`, obtained from K-injective resolutions of complexes of sheaves of modules. -/
instance hasPointwiseRightDerivedSectionsOnAffineComplement
    (A : Type u) [CommRing A] (I : Ideal A) :
    HasPointwiseRightDerivedFunctor
      ((sectionsOnAffineComplement A I).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (Spec (CommRingCat.of A)).Modules (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{u,
      u + 1, u + 1, u + 1, u + 1, u + 1} _
    (exists_quasiIso_isKInjective_specModules A)).1

/-- Derived sections `RΓ(U, -)` on `U = Spec A \ V(I)`, the total right derived functor of
`sectionsOnAffineComplement` on the unbounded derived category of sheaves of modules. -/
def derivedSectionsOnAffineComplement (A : Type u) [CommRing A] (I : Ideal A) :
    DerivedCategory (Spec (CommRingCat.of A)).Modules ⥤ DerivedCategory (ModuleCat.{u} A) :=
  totalRightDerived
    ((sectionsOnAffineComplement A I).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh) DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Spec (CommRingCat.of A)).Modules (ComplexShape.up ℤ))

/-- The canonical comparison from termwise sections on `U` to derived sections on `U`. -/
abbrev derivedSectionsOnAffineComplementUnit (A : Type u) [CommRing A] (I : Ideal A) :
    (sectionsOnAffineComplement A I).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSectionsOnAffineComplement A I :=
  ((sectionsOnAffineComplement A I).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (Spec (CommRingCat.of A)).Modules (ComplexShape.up ℤ))

/-- The comparison exhibits `derivedSectionsOnAffineComplement` as the right derived functor of
sections on `U = Spec A \ V(I)`. -/
instance derivedSectionsOnAffineComplement_isRightDerivedFunctor
    (A : Type u) [CommRing A] (I : Ideal A) :
    (derivedSectionsOnAffineComplement A I).IsRightDerivedFunctor
      (derivedSectionsOnAffineComplementUnit A I)
      (HomotopyCategory.quasiIso (Spec (CommRingCat.of A)).Modules (ComplexShape.up ℤ)) :=
  inferInstanceAs (Functor.IsRightDerivedFunctor
    (((sectionsOnAffineComplement A I).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh).totalRightDerived DerivedCategory.Qh _) _ _)

/-! ### Vanishing of local cohomology in negative degrees -/

/-- Being `I`-power torsion is invariant under isomorphism of modules. -/
theorem isIPowerTorsion_of_iso {A : Type u} [CommRing A] {I : Ideal A}
    {M N : ModuleCat.{v} A} (e : M ≅ N) (h : IsIPowerTorsion A M I) :
    IsIPowerTorsion A N I := fun m => by
  obtain ⟨n, hn, hkill⟩ := h (e.inv.hom m)
  refine ⟨n, hn, fun a ha => ?_⟩
  have h1 : e.hom.hom (a • e.inv.hom m) = a • m := by
    rw [_root_.map_smul]; congr 1
    exact ConcreteCategory.congr_hom e.inv_hom_id m
  rw [hkill a ha, map_zero] at h1
  exact h1.symm

/-- A zero module is `I`-power torsion. -/
theorem isIPowerTorsion_of_isZero {A : Type u} [CommRing A] {I : Ideal A}
    {N : ModuleCat.{v} A} (h : IsZero N) : IsIPowerTorsion A N I := fun m =>
  ⟨1, one_pos, fun a _ => by
    have hm : m = 0 := by
      simpa using ConcreteCategory.congr_hom (h.eq_of_src (𝟙 N) 0) m
    simp [hm]⟩

/-- An isomorphism that is the zero morphism has a zero target. -/
theorem isZero_of_isIso_eq_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y : C} (f : X ⟶ Y) [IsIso f] (hf : f = 0) : IsZero Y :=
  (IsZero.iff_id_eq_zero Y).2
    ((IsIso.inv_hom_id f).symm.trans ((congrArg (inv f ≫ ·) hf).trans comp_zero))

/-- A morphism out of the left adjoint that the counit kills comes from the zero morphism. -/
theorem map_eq_zero_of_comp_counit_eq_zero {C D : Type*} [Category C] [Category D]
    [Preadditive C] [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive]
    {T : C} {Y : D} (g : T ⟶ G.obj Y) (h : F.map g ≫ adj.counit.app Y = 0) :
    F.map g = 0 := by
  have hg : g = 0 := by
    apply (adj.homEquiv T Y).symm.injective
    rw [adj.homEquiv_counit, adj.homEquiv_counit, h, F.map_zero, zero_comp]
  rw [hg, F.map_zero]

/-- A morphism from an object of `D(A)` with `I`-power-torsion cohomology into `RΓ_{V(I)}(K)`
which the counit of the local-cohomology adjunction of Stacks 0A6Q kills is itself zero: by that
adjunction, composing with the counit is a bijection from the morphisms of the torsion
subcategory. -/
theorem eq_zero_of_comp_localCohomologyCounit_eq_zero (A : Type u) [CommRing A] (I : Ideal A)
    (hI : I.FG) (T : Dualizing.PowerTorsionDerivedCategory A I hI)
    (K : DerivedCategory (ModuleCat.{v} A))
    (ρ : (Dualizing.derivedPowerTorsionProperty A I hI).ι.obj T ⟶
      (Dualizing.derivedPowerTorsionProperty A I hI).ι.obj
        ((Dualizing.localCohomologyFunctor A I hI).obj K))
    (h : ρ ≫ (Dualizing.localCohomologyAdjunction A I hI).counit.app K = 0) : ρ = 0 := by
  obtain ⟨g, rfl⟩ := (Dualizing.derivedPowerTorsionProperty A I hI).fullyFaithfulι.map_surjective ρ
  exact map_eq_zero_of_comp_counit_eq_zero (Dualizing.localCohomologyAdjunction A I hI) g h

/-- An object of `D(A)` with `I`-power-torsion cohomology receives a map, isomorphic on cohomology
in degrees `≤ n`, from an object in degrees `≤ n` with `I`-power-torsion cohomology. -/
private theorem exists_truncLE_isPowerTorsion (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (X : DerivedCategory (ModuleCat.{v} A))
    (hX : Dualizing.derivedPowerTorsionProperty A I hI X) (n : ℤ) :
    ∃ (T : DerivedCategory (ModuleCat.{v} A)) (θ : T ⟶ X),
      Dualizing.derivedPowerTorsionProperty A I hI T ∧ DerivedCategory.IsLE T n ∧
        ∀ j ≤ n, IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) j).map θ) := by
  set K := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  set θ : DerivedCategory.Q.obj (K.truncLE n) ⟶ X :=
    DerivedCategory.Q.map (K.ιTruncLE n) ≫ e.hom with hθ
  have hiso : ∀ j ≤ n, IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) j).map θ) := by
    intro j hj
    have : QuasiIsoAt (K.ιTruncLE n) j := CochainComplex.quasiIsoAt_ιTruncLE K n j hj
    have h1 : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) j).map
        (DerivedCategory.Q.map (K.ιTruncLE n))) :=
      (NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors (ModuleCat.{v} A) j)
        (K.ιTruncLE n)).2
        (inferInstanceAs (IsIso (HomologicalComplex.homologyMap (K.ιTruncLE n) j)))
    rw [hθ, Functor.map_comp]
    infer_instance
  have hLE : DerivedCategory.IsLE (DerivedCategory.Q.obj (K.truncLE n)) n := by
    rw [DerivedCategory.isLE_Q_obj_iff]; infer_instance
  refine ⟨_, θ, fun j => ?_, hLE, hiso⟩
  by_cases hj : j ≤ n
  · have := hiso j hj
    exact isIPowerTorsion_of_iso
      (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) j).map θ)).symm (hX j)
  · exact isIPowerTorsion_of_isZero (DerivedCategory.isZero_of_isLE _ n j (by omega))

/-- **Local cohomology vanishes in negative degrees.** For an `A`-module `M` and `i < 0` the
local cohomology module `H^i_{V(I)}(M)` is zero. The local cohomology functor of Stacks 0A6Q is
an abstract coreflection, so this is proved from its universal property: the degree-`≤ -1`
truncation of a complex representing `RΓ_{V(I)}(M)` again has `I`-power-torsion cohomology, the
counit kills the comparison map because a complex concentrated in degrees `≤ -1` admits no
nonzero morphism to a module placed in degree `0`, and the comparison is an isomorphism on
cohomology in degrees `≤ -1`. -/
theorem isZero_localCohomologyModule_of_neg (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) (i : ℤ) (hi : i < 0) :
    IsZero (localCohomologyModule A I hI M i) := by
  set P := Dualizing.derivedPowerTorsionProperty A I hI
  set Y := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M
  set W := (Dualizing.localCohomologyFunctor A I hI).obj Y
  obtain ⟨K', ψ, htor, hLE, hiso⟩ :=
    exists_truncLE_isPowerTorsion A I hI (P.ι.obj W) W.property (-1)
  -- the counit kills the comparison for degree reasons, so the universal property kills it
  set T : Dualizing.PowerTorsionDerivedCategory A I hI := ⟨K', htor⟩
  have hzero : ψ ≫ (Dualizing.localCohomologyAdjunction A I hI).counit.app Y = 0 := by
    have : DerivedCategory.IsLE (P.ι.obj T) (-1) := hLE
    have : DerivedCategory.IsGE ((𝟭 (DerivedCategory (ModuleCat.{v} A))).obj Y) 0 :=
      inferInstanceAs (DerivedCategory.IsGE
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) 0)
    exact DerivedCategory.TStructure.t.zero _ (-1) 0 (by omega)
  have hpsi : ψ = 0 :=
    eq_zero_of_comp_localCohomologyCounit_eq_zero A I hI T Y ψ hzero
  have hmap : (DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map ψ = 0 := by
    rw [hpsi, Functor.map_zero]
  have := hiso i (by omega)
  exact isZero_of_isIso_eq_zero _ hmap

/-! ### Injectivity of the map out of degree-zero local cohomology -/

/-- A submodule of an `I`-power-torsion module is `I`-power torsion; more generally the property
passes to the source of an injective module map. -/
theorem isIPowerTorsion_of_injective {A : Type u} [CommRing A] {I : Ideal A}
    {M N : ModuleCat.{v} A} (f : M ⟶ N) (hf : Function.Injective f.hom)
    (h : IsIPowerTorsion A N I) : IsIPowerTorsion A M I := fun m => by
  obtain ⟨n, hn, hkill⟩ := h (f.hom m)
  exact ⟨n, hn, fun a ha => hf (by rw [_root_.map_smul, hkill a ha, map_zero])⟩

/-- **Stacks 0DWR, injectivity of `H⁰_{V(I)}(M) ⟶ M`.** The remaining statement of the
five-term sequence, which the localization triangle does not give: the canonical map from
degree-zero local cohomology to the module is a monomorphism.

Local cohomology vanishes in negative degrees, so a complex representing `RΓ_{V(I)}(M)`
truncated in degrees `≤ 0` is a module `B` placed in degree zero, mapping to `RΓ_{V(I)}(M)` by a
map which is an isomorphism on `H⁰`; the counit turns it into a module map `B ⟶ M`. Its kernel,
placed in degree zero, is again an object with `I`-power-torsion cohomology whose image in
`RΓ_{V(I)}(M)` the counit kills, so the universal property of Stacks 0A6Q makes that image
vanish; since `H⁰` of the comparison is an isomorphism, the kernel inclusion itself vanishes. -/
theorem mono_localCohomologyZeroToModule (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) : Mono (localCohomologyZeroToModule A I hI M) := by
  set P := Dualizing.derivedPowerTorsionProperty A I hI
  set Y := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M
  set W := (Dualizing.localCohomologyFunctor A I hI).obj Y
  set L := P.ι.obj W
  set ε : L ⟶ Y := (Dualizing.localCohomologyAdjunction A I hI).counit.app Y
  obtain ⟨K', θ, htor, hLE, hiso⟩ :=
    exists_truncLE_isPowerTorsion A I hI (P.ι.obj W) W.property 0
  have hGE : DerivedCategory.IsGE K' 0 := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    have := hiso i (by omega)
    exact IsZero.of_iso (isZero_localCohomologyModule_of_neg A I hI M i hi)
      (asIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map θ))
  -- the truncation is a module placed in degree zero
  obtain ⟨B, ⟨α⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE
    K' 0
  set θ' : (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj B ⟶ L := α.inv ≫ θ with hθ'
  have hθ'iso : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map θ') := by
    have := hiso 0 le_rfl
    rw [hθ', Functor.map_comp]
    infer_instance
  have hBtor : IsIPowerTorsion A B I :=
    isIPowerTorsion_of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).mapIso α ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).app B) (htor 0)
  -- the composite with the counit comes from a module map
  set β : B ⟶ M := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).preimage (θ' ≫ ε)
  have hβ : (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map β = θ' ≫ ε :=
    Functor.map_preimage _ _
  -- its kernel is a torsion module, and the counit kills its image in `L`
  set N := ModuleCat.of A (LinearMap.ker β.hom)
  set ιN : N ⟶ B := ModuleCat.ofHom (LinearMap.ker β.hom).subtype with hιN
  have hιNβ : ιN ≫ β = 0 := ModuleCat.hom_ext (LinearMap.ext fun x => x.2)
  have hNtor : IsIPowerTorsion A N I :=
    isIPowerTorsion_of_injective ιN Subtype.val_injective hBtor
  have hNobj : P ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj N) := by
    intro j
    rcases lt_trichotomy j 0 with hj | hj | hj
    · exact isIPowerTorsion_of_isZero (DerivedCategory.isZero_of_isGE _ 0 j hj)
    · subst hj
      exact isIPowerTorsion_of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).app N).symm
        hNtor
    · exact isIPowerTorsion_of_isZero (DerivedCategory.isZero_of_isLE _ 0 j hj)
  set ρ : (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj N ⟶ L :=
    (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map ιN ≫ θ' with hρ
  have hρε : ρ ≫ ε = 0 := by
    rw [hρ, Category.assoc, ← hβ, ← Functor.map_comp, hιNβ, Functor.map_zero]
  have hρ0 : ρ = 0 :=
    eq_zero_of_comp_localCohomologyCounit_eq_zero A I hI
      ⟨(DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj N, hNobj⟩ Y ρ hρε
  -- hence the kernel inclusion vanishes, so `β` is a monomorphism
  have hmapιN : (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map ιN = 0 := by
    have h1 : (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map ιN ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map θ' = 0 := by
      rw [Functor.comp_map, ← Functor.map_comp, ← hρ, hρ0, Functor.map_zero]
    have := hθ'iso
    simpa using h1
  have : (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).Faithful :=
    Functor.Faithful.of_iso
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).symm
  have hιN0 : ιN = 0 := by
    apply Functor.map_injective (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0)
    rw [hmapιN, Functor.map_zero]
  have hker : LinearMap.ker β.hom = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have h := ConcreteCategory.congr_hom hιN0 (⟨x, hx⟩ : LinearMap.ker β.hom)
    simp only [hιN, ModuleCat.hom_ofHom, ModuleCat.hom_zero, LinearMap.zero_apply] at h
    exact h
  have hβmono : Mono β := (ModuleCat.mono_iff_injective β).2 (LinearMap.ker_eq_bot.1 hker)
  -- `H⁰` of the counit is therefore a monomorphism, and so is the map of Stacks 0DWR
  have : (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0 ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).symm
  have hfac : (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map θ' ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map ε =
      (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0 ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map β := by
    rw [Functor.comp_map, ← Functor.map_comp, hβ]
  have hmonoComp : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map θ' ≫
      (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map ε) := by
    rw [hfac]
    exact Functor.map_mono _ β
  have := hθ'iso
  have hmonoε : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map ε) := by
    have h2 : Mono (inv ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map θ') ≫
        ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map θ' ≫
          (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map ε)) := mono_comp _ _
    simpa using h2
  exact (mono_comp ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map ε)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).hom.app M))

/-- The canonical map `H⁰_{V(I)}(M) ⟶ M` of Stacks 0DWR is injective. -/
theorem localCohomologyZeroToModule_injective (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) :
    Function.Injective (localCohomologyZeroToModule A I hI M).hom :=
  (ModuleCat.mono_iff_injective _).1 (mono_localCohomologyZeroToModule A I hI M)

/-! ### Negative cohomology of derived sections on the complement -/

/-- **Derived sections on the complement have no negative cohomology.** For a localization
triangle `RΓ_{V(I)}(M) ⟶ M ⟶ RΓ(U, M̃|U)` the third term has no cohomology in negative degrees.

This is the long exact sequence together with the two facts about local cohomology proved above:
in degrees `< -1` both neighbours vanish, and in degree `-1` the neighbour `H⁰_{V(I)}(M) ⟶ M` is
injective, which is exactly the vanishing of the connecting map out of `H^{-1}` of the third
term. -/
theorem isZero_homology_complement_of_neg {A : Type u} [CommRing A] {I : Ideal A} {hI : I.FG}
    (D : LocalizationTriangleData.{u, v} A I hI) (M : ModuleCat.{v} A) (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj
      (D.complement.obj M)) := by
  have hT := D.distinguished M
  have hmono : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) (i + 1)).map
      (D.triangle M).mor₁) := by
    rcases lt_or_eq_of_le (show i + 1 ≤ 0 by omega) with h | h
    · exact ⟨fun g k _ =>
        (isZero_localCohomologyModule_of_neg A I hI M (i + 1) h).eq_of_tgt g k⟩
    · rw [h]
      have h2 : Mono ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).map
          (D.triangle M).mor₁ ≫
            (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).hom.app M) :=
        mono_localCohomologyZeroToModule A I hI M
      exact mono_of_mono _
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{v} A) 0).hom.app M)
  have hδ : DerivedCategory.HomologySequence.δ (D.triangle M) i (i + 1) rfl = 0 :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff (D.triangle M) hT i (i + 1)
      rfl).1 hmono
  have hepi : Epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
      (D.triangle M).mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff (D.triangle M) hT i (i + 1)
      rfl).2 hδ
  have hGE : DerivedCategory.IsGE (D.triangle M).obj₂ 0 :=
    inferInstanceAs (DerivedCategory.IsGE
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M) 0)
  have hsrc : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj
      (D.triangle M).obj₂) := DerivedCategory.isZero_of_isGE _ 0 i hi
  have key : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj
      (D.triangle M).obj₃) := by
    refine (IsZero.iff_id_eq_zero _).2 ?_
    refine (cancel_epi ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
      (D.triangle M).mor₂)).1 ?_
    rw [hsrc.eq_of_src ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
      (D.triangle M).mor₂) 0]
    simp
  exact key

end Stacks.LocalCohomology
