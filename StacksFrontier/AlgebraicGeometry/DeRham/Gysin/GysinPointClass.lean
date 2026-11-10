module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinHodgeConormal
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinEtaleSection
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinPointClassInjective
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinPointClassNonvanishing
public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex
public import StacksFrontier.AlgebraicGeometry.HigherRank.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.SupportFromRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.DegreeZeroSections
public import StacksFrontier.AlgebraicGeometry.Duality.ProperOverField.SmoothDualizingModule
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.SmoothEquidimensionalOverField
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage

/-!
# The Gysin class of a rational point

Let `X` be smooth of relative dimension `d` and proper over a field `k`, and let `i : Z ⟶ X` be
a closed immersion with `Z ≅ Spec k` over `k` — the reduced closed subscheme of a `k`-rational
point. This file proves [Stacks, Tag 0G8E]: the Gysin class of the point is nonzero. The
argument is assembled in `gysinHodgeFormsMapOfConormalRank_oneClass_ne_zero_of_dualizingIso` up
to the identification `ω_X^• ≅ Ω^d_{X/k}[d]` of [Stacks, Tag 0FVV] (7), which
`gysinHodgeFormsMapOfConormalRank_oneClass_ne_zero` supplies.
The other input of the argument, the nonvanishing of the sheaf-level Gysin map `γ^0` of
[Stacks, Tag 0G86], is `Stacks.Gysin.conormalGysinHom_ne_zero_of_isIso`.

## Main definitions

* `Stacks.DeRham.CohomologicalGysin.oneClass`: the class of `1 ∈ k = H^0(Z, 𝒪_Z)` in
  `H^0(Z, Ω^0_{Z/k})`.

## Main results

* `Stacks.DeRham.CohomologicalGysin.oneClass_ne_zero`: the class `oneClass` is nonzero when `Z`
  is nonempty.
* `Stacks.DeRham.CohomologicalGysin.finrank_globalSections_pushforwardRelativeForms_zero`: the
  global sections of `i_*Ω^0_{Z/k}` form a one-dimensional `k`-vector space.
* `Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMapOfConormalRank_oneClass_ne_zero_of_iso`.
* `gysinHodgeFormsMapOfConormalRank_oneClass_ne_zero_of_dualizingIso`: the same with the
  nonvanishing of `γ^0` discharged, by `Stacks.Gysin.conormalGysinHom_ne_zero_of_isIso`.
* `Stacks.DeRham.CohomologicalGysin.gysinHodgeFormsMapOfConormalRank_oneClass_ne_zero`:
  [Stacks, Tag 0G8E].
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction Stacks.Cohomology.SupportedComplexes
open AlgebraicGeometry.Scheme.Hom Stacks.Gysin Stacks.AlgebraicGeometry.ConormalEquations

namespace Stacks.DeRham.CohomologicalGysin

universe u

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

attribute [local instance] moduleSheavesHasDerivedCategory

variable {k : Type u} [Field k] {X Z : Scheme.{u}} (π : X ⟶ Spec (.of k)) (i : Z ⟶ X)
  [IsClosedImmersion i]

/-- **The class of `1 ∈ k = H^0(Z, 𝒪_Z)` in `H^0(Z, Ω^0_{Z/k})`**: the global section `1` of
`𝒪_Z`, read in `Ω^0_{Z/k}` through `Ω^0_{Z/k} = 𝒪_Z` and in `H^0` through `H^0 = Γ`. -/
def oneClass : Hgroup Z.ringCatSheaf ⊤ 0 (relativeDifferentialForms (i ≫ π) ((0 : ℕ) : ℤ)) :=
  ((HzeroIso Z.ringCatSheaf ⊤).app _).inv
    ((secF Z.ringCatSheaf ⊤).map (relativeDifferentialFormsZeroIso (i ≫ π)).inv
      (unitSection Z.toRingedSpace))

omit [IsClosedImmersion i] in
/-- The class `oneClass π i` of `1` in `H^0(Z, Ω^0_{Z/k})` is nonzero when `Z` is nonempty. -/
theorem oneClass_ne_zero [Nonempty Z] : oneClass π i ≠ 0 := by
  have : Nonempty (⊤ : Z.Opens) := ⟨⟨Classical.arbitrary Z, trivial⟩⟩
  intro h
  have h1 : (secF Z.ringCatSheaf ⊤).map (relativeDifferentialFormsZeroIso (i ≫ π)).inv
      (unitSection Z.toRingedSpace) = 0 :=
    (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso _).1).1 h
  have h2 : unitSection Z.toRingedSpace = 0 :=
    (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      ((secF Z.ringCatSheaf ⊤).mapIso (relativeDifferentialFormsZeroIso (i ≫ π))).inv).1).1 h1
  exact one_ne_zero (α := Γ(Z, ⊤)) h2

/-- The direct image of `Ω^0_{Z/k}` along a closed immersion, placed in any degree, has its
cohomology supported on the image. -/
theorem cohomologySupportedOn_pushforwardRelativeForms (π : X ⟶ Spec (.of k)) (n : ℤ) :
    AlgebraicGeometry.CohomologySupportedOn (structureSheafRing X.toRingedSpace) (Set.range i.base)
      ((DerivedCategory.singleFunctor
        (_root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) n).obj
          (pushforwardRelativeForms i π (((0 : ℕ) : ℤ)))) :=
  Stacks.Cohomology.RestrictionSupport.cohomologySupportedOn_singleFunctor_obj _ _ n _ fun y hy =>
    Stacks.AlgebraicGeometry.Tag01YMHigherRank.isZero_stalk_pushforward_of_notMem_range i _ y hy

/-- The `k`-linear structure on global sections of `𝒪_X`-modules, through `π`. -/
abbrev globalScalars (π : X ⟶ Spec (.of k)) : k →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ π.appLE ⊤ ⊤ (by simp)).hom

omit [IsClosedImmersion i] in
/-- **The global sections of `i_*Ω^0_{Z/k}` form a one-dimensional `k`-vector space** when
`Z ≅ Spec k` over `k`: every global section is a `k`-multiple of the one corresponding to `1`. -/
theorem finrank_globalSections_pushforwardRelativeForms_zero [IsIso (i ≫ π)] :
    Module.finrank k ((ModuleCat.restrictScalars (globalScalars π)).obj
      ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj
        (pushforwardRelativeForms i π (((0 : ℕ) : ℤ))))) = 1 := by
  have : Nonempty Z := ⟨(inv (i ≫ π)).base (Classical.arbitrary _)⟩
  have : Nonempty (i ⁻¹ᵁ (⊤ : X.Opens)) := ⟨⟨Classical.arbitrary Z, trivial⟩⟩
  let U : Z.Opens := i ⁻¹ᵁ (⊤ : X.Opens)
  let eθ := (_root_.SheafOfModules.evaluation Z.ringCatSheaf (op U)).mapIso
    (relativeDifferentialFormsZeroIso (i ≫ π))
  let a : Γ(Z, U) → (relativeDifferentialForms (i ≫ π) (((0 : ℕ) : ℤ))).val.obj (op U) :=
    fun r => eθ.inv.hom r
  have ha : Function.Bijective a := eθ.symm.toLinearEquiv.bijective
  let ψ : k →+* Γ(Z, U) := (i.app ⊤).hom.comp (globalScalars π)
  have hψ : Function.Bijective ψ := by
    have h : ψ = ((Scheme.ΓSpecIso (.of k)).inv ≫ (i ≫ π).app ⊤).hom := by
      have hπ : π.appLE ⊤ ⊤ (by simp) = π.app ⊤ := (Scheme.Hom.app_eq_appLE π).symm
      ext c
      simp only [ψ, globalScalars, hπ]
      rfl
    rw [h]
    exact ConcreteCategory.bijective_of_isIso _
  let e : (ModuleCat.restrictScalars (globalScalars π)).obj
      ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj
        (pushforwardRelativeForms i π (((0 : ℕ) : ℤ)))) := a 1
  have hsmul : ∀ c : k, c • e = a (ψ c) := by
    intro c
    let E1 := (_root_.SheafOfModules.evaluation Z.ringCatSheaf (op U)).obj
      (SheafOfModules.unit Z.ringCatSheaf)
    change (show (Z.ringCatSheaf.obj.obj (op U) : Type u) from ψ c) •
        eθ.inv.hom (show (E1 : Type u) from (1 : Γ(Z, U))) =
      eθ.inv.hom (show (E1 : Type u) from ψ c)
    rw [← map_smul]
    congr 1
    exact mul_one (ψ c)
  have he : e ≠ 0 := fun h0 =>
    one_ne_zero (ha.1 (show a 1 = a 0 from h0.trans (map_zero eθ.inv.hom).symm))
  refine (finrank_eq_one_iff_of_nonzero' e he).2 fun w => ?_
  obtain ⟨r, hr⟩ := ha.2 w
  obtain ⟨c, rfl⟩ := hψ.2 r
  exact ⟨c, (hsmul c).trans hr⟩

/-- **[Stacks, Tag 0G8E], modulo two inputs.** Let `X` be proper and smooth of relative
dimension `d` over a field `k` and `i : Z ⟶ X` a closed immersion with `Z ≅ Spec k` over `k`.
Given an identification `ω_X^• ≅ Ω^d_{X/k}[d]` of the relative dualizing complex and the
nonvanishing of the sheaf-level Gysin map `γ^0` of [Stacks, Tag 0G86], the image of
`1 ∈ H^0(Z, Ω^0_{Z/k})` under the Gysin map `γ^{0,0}` of [Stacks, Tag 0G8A] is nonzero. -/
theorem gysinHodgeFormsMapOfConormalRank_oneClass_ne_zero_of_iso (d : ℕ) [IsProper π]
    [SmoothOfRelativeDimension d π] [Smooth (i ≫ π)] [FormallyUnramified (i ≫ π)]
    [IsIso (i ≫ π)] [LocallyOfFinitePresentation i]
    [(show X.Modules from pushforwardRelativeForms i π (((0 : ℕ) : ℤ))).IsQuasicoherent]
    (ψ : (Stacks.Duality.relativeDualizingComplex π
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs π)
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))).obj ≅
      (DerivedCategory.singleFunctor X.Modules (-(d : ℤ))).obj
        (relativeDifferentialForms π (((0 : ℕ) : ℤ) + (d : ℤ))))
    (hγ : conormalGysinHom i π 0 (conormalRank_of_formallyUnramified i π d) ≠ 0) :
    gysinHodgeFormsMapOfConormalRank i π (c := d) 0 (conormalRank_of_formallyUnramified i π d)
      (supportVanishing_of_formallyUnramified i π d 0) 0 (oneClass π i) ≠ 0 := by
  have : Nonempty Z := ⟨(inv (i ≫ π)).base (Classical.arbitrary _)⟩
  have hinj := injective_gysinCohomologyMap_zero_of_duality π (Set.range i.base)
    i.isClosedEmbedding.isClosed_range d (pushforwardRelativeForms i π (((0 : ℕ) : ℤ)))
    (relativeDifferentialForms π (((0 : ℕ) : ℤ) + (d : ℤ)))
    (supportVanishing_of_formallyUnramified i π d 0)
    (conormalGysinHom i π 0 (conormalRank_of_formallyUnramified i π d) ≫
      (conormalGysinTargetIso i π d 0).hom)
    (cohomologySupportedOn_pushforwardRelativeForms i π (d : ℤ)) (fun h =>
      hγ ((Iso.cancel_iso_hom_right _ _ (conormalGysinTargetIso i π d 0)).1
        (h.trans zero_comp.symm)))
    (finrank_globalSections_pushforwardRelativeForms_zero π i) ψ
  intro h0
  apply oneClass_ne_zero π i
  have h1 : gysinCohomologyMap (Set.range i.base) i.isClosedEmbedding.isClosed_range d
      (pushforwardRelativeForms i π (((0 : ℕ) : ℤ)))
      (relativeDifferentialForms π (((0 : ℕ) : ℤ) + (d : ℤ)))
      (supportVanishing_of_formallyUnramified i π d 0)
      (conormalGysinHom i π 0 (conormalRank_of_formallyUnramified i π d) ≫
        (conormalGysinTargetIso i π d 0).hom) 0
      (((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso i 0).app
        ⟨_, isQuasicoherent_relativeDifferentialForms (i ≫ π) 0⟩).hom (oneClass π i)) = 0 :=
    h0
  exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    ((Stacks.AffineCohomologyResolution.cohomologyPushforwardIso i 0).app
      ⟨_, isQuasicoherent_relativeDifferentialForms (i ≫ π) 0⟩).hom).1).1
    ((map_eq_zero_iff _ hinj).1 h1)

/-- **[Stacks, Tag 0G8E], modulo the identification of the dualizing complex.** Let `X` be proper
and smooth of relative dimension `d` over a field `k` and `i : Z ⟶ X` a closed immersion with
`Z ≅ Spec k` over `k`. Given an identification `ω_X^• ≅ Ω^d_{X/k}[d]` of the relative dualizing
complex, the image of `1 ∈ H^0(Z, Ω^0_{Z/k})` under the Gysin map `γ^{0,0}` of
[Stacks, Tag 0G8A] is nonzero. The nonvanishing of the sheaf-level Gysin map `γ^0` of
[Stacks, Tag 0G86] that the argument needs is
`Stacks.Gysin.conormalGysinHom_ne_zero_of_isIso`. -/
theorem gysinHodgeFormsMapOfConormalRank_oneClass_ne_zero_of_dualizingIso (d : ℕ) [IsProper π]
    [SmoothOfRelativeDimension d π] [Smooth (i ≫ π)] [FormallyUnramified (i ≫ π)]
    [IsIso (i ≫ π)] [LocallyOfFinitePresentation i]
    [(show X.Modules from pushforwardRelativeForms i π (((0 : ℕ) : ℤ))).IsQuasicoherent]
    (ψ : (Stacks.Duality.relativeDualizingComplex π
        (Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_qcqs π)
        (Stacks.Duality.DerivedPushforward.derivedStructureSheaf (Spec (CommRingCat.of k)))).obj ≅
      (DerivedCategory.singleFunctor X.Modules (-(d : ℤ))).obj
        (relativeDifferentialForms π (((0 : ℕ) : ℤ) + (d : ℤ)))) :
    gysinHodgeFormsMapOfConormalRank i π (c := d) 0 (conormalRank_of_formallyUnramified i π d)
      (supportVanishing_of_formallyUnramified i π d 0) 0 (oneClass π i) ≠ 0 :=
  gysinHodgeFormsMapOfConormalRank_oneClass_ne_zero_of_iso π i d ψ
    (Stacks.Gysin.conormalGysinHom_ne_zero_of_isIso π i d _)

/-- **[Stacks, Tag 0G8E].** Let `k` be a field and `X` an irreducible smooth proper scheme over
`k` of dimension `d`. Let `i : Z ⟶ X` be the reduced closed subscheme consisting of a single
`k`-rational point, i.e. a closed immersion with `Z ≅ Spec k` over `k`. Then the image of
`1 ∈ k = H^0(Z, 𝒪_Z) = H^0(Z, Ω^0_{Z/k})` under the Gysin map
`H^0(Z, Ω^0_{Z/k}) ⟶ H^d(X, Ω^d_{X/k})` of [Stacks, Tag 0G8A] is nonzero. The identification
`ω_X^• ≅ Ω^d_{X/k}[d]` the argument uses is [Stacks, Tag 0FVV], part (7). -/
@[stacks 0G8E "for X irreducible smooth proper over a field k of dimension d and Z the reduced \
closed subscheme of a k-rational point, the Gysin map H^0(Z, Omega^0_{Z/k}) -> \
H^d(X, Omega^d_{X/k}) \
of 0G8A sends 1 to a nonzero class"]
theorem gysinHodgeFormsMapOfConormalRank_oneClass_ne_zero (d : ℕ) [IsProper π] [Smooth π]
    [IrreducibleSpace X] (hd : topologicalKrullDim X = d) [IsIso (i ≫ π)] :
    haveI : SmoothOfRelativeDimension d π := smoothOfRelativeDimension_of_equidimensional k π
      (TopologicalSpace.Equidimensional.of_preirreducibleSpace X) d hd
    haveI : LocallyOfFinitePresentation i := locallyOfFinitePresentation_of_comp i π
    gysinHodgeFormsMapOfConormalRank i π (c := d) 0 (conormalRank_of_formallyUnramified i π d)
      (supportVanishing_of_formallyUnramified i π d 0) 0 (oneClass π i) ≠ 0 :=
  have : SmoothOfRelativeDimension d π := smoothOfRelativeDimension_of_equidimensional k π
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace X) d hd
  have : LocallyOfFinitePresentation i := locallyOfFinitePresentation_of_comp i π
  have : (relativeDifferentialForms (i ≫ π) ((0 : ℕ) : ℤ)).IsQuasicoherent :=
    isQuasicoherent_relativeDifferentialForms (i ≫ π) 0
  have : (show X.Modules from pushforwardRelativeForms i π (((0 : ℕ) : ℤ))).IsQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pushforward_of_isAffineHom i
      (relativeDifferentialForms (i ≫ π) ((0 : ℕ) : ℤ)) inferInstance
  gysinHodgeFormsMapOfConormalRank_oneClass_ne_zero_of_dualizingIso π i d
    ((Stacks.Duality.nonempty_relativeDualizingComplex_iso_and_relativeDualizingModule_iso_of_smooth
      π d).1.some ≪≫ (DerivedCategory.singleFunctor X.Modules (-(d : ℤ))).mapIso
        (eqToIso (by rw [Nat.cast_zero, zero_add]; rfl)))

end Stacks.DeRham.CohomologicalGysin
