module

public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.FiniteLength
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.MaximalDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.WeilDivisors
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentFinitePresentation
public import StacksFrontier.RingTheory.Support.Finite
public import StacksCore.Tactic.StacksAttribute

/-!
# The support of a coherent sheaf and its irreducible components

Let `X` be a locally Noetherian scheme and `F` a coherent `𝒪_X`-module. The support of `F` is
closed, so it carries a canonical reduced closed subscheme structure, and three facts about its
irreducible components are what make the cycle of a coherent sheaf well defined:

* the components form a locally finite family in `X`;
* at the generic point of a component the stalk of `F` has finite length over the local ring of
  `X`, so its length is an integer;
* when `X` lies over the base scheme of chapter 42 and the support has delta-dimension at most
  `k`, a point of the support of delta-dimension `k` is the generic point of a component.

## Main definitions

* `Stacks.Chow.reducedSupport` — the canonical reduced closed subscheme of `X` with underlying
  set the support of a coherent sheaf.

## Main results

* `Stacks.Chow.locallyFinite_irreducibleComponents_supp` — Stacks 02QW (1).
* `Stacks.Chow.isFiniteLength_stalk_of_isGenericPoint_component_supp` — Stacks 02QW (2).
* `Stacks.Chow.isGenericPoint_component_supp_of_relativeDimension_eq` — Stacks 02QW (3).

## Implementation notes

The support is `SheafOfModules.supp`, a subset of `X`; its irreducible components are taken for
the subspace topology and mapped back into `X` by `Subtype.val` whenever a statement needs to be
read in the ambient scheme. Local finiteness is therefore the purely topological
`AlgebraicGeometry.locallyFinite_image_irreducibleComponents_of_isLocallyNoetherianSpace`
applied to the inclusion of the support, with no recourse to the subscheme structure.

Finiteness of the length in (2) is Stacks 00L5: the stalk is a finite module over a Noetherian
local ring whose support is the closed point alone. That the support is the closed point alone
uses that the points of `X` specializing to `ξ` are the primes of `𝒪_{X,ξ}`, in the form of
`AlgebraicGeometry.Scheme.range_fromSpecStalk`, together with the fact that no point of the
support other than `ξ` itself generizes the generic point of a component.

## References

* [Stacks Project, Tag 00L5](https://stacks.math.columbia.edu/tag/00L5)
* [Stacks Project, Tag 01J3](https://stacks.math.columbia.edu/tag/01J3)
* [Stacks Project, Tag 02QW](https://stacks.math.columbia.edu/tag/02QW)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
* [Stacks Project, Tag 0BE1](https://stacks.math.columbia.edu/tag/0BE1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- A coherent sheaf of modules on a scheme is of finite type.

This is the first field of `SheafOfModules.IsCoherent`, restated for a
`AlgebraicGeometry.Scheme.Modules`. Instance search cannot supply it there: the ring sheaf of a
scheme is written through `TopCat.Sheaf`, and matching that against the implicit arguments of
`SheafOfModules.IsFiniteType` needs an unfolding that instance search does not perform. -/
theorem isFiniteType_of_isCoherent (F : X.Modules) [F.IsCoherent] : F.IsFiniteType :=
  SheafOfModules.IsCoherent.isFiniteType

/-- **Stacks 01J3.** The canonical reduced closed subscheme of `X` whose underlying closed set is
the support of a coherent sheaf. -/
noncomputable def reducedSupport (F : X.Modules) [F.IsCoherent] : X.IdealSheafData :=
  have := isFiniteType_of_isCoherent F
  Scheme.IdealSheafData.vanishingIdeal ⟨SheafOfModules.supp F, SheafOfModules.isClosed_supp F⟩

/-- The closed subscheme `Stacks.Chow.reducedSupport` is carried by the support of the sheaf. -/
@[simp]
theorem coe_support_reducedSupport (F : X.Modules) [F.IsCoherent] :
    ((reducedSupport F).support : Set X) = SheafOfModules.supp F := by
  simp [reducedSupport]

/-- **Stacks 02QW (1).** The irreducible components of the support of a coherent sheaf on a
locally Noetherian scheme form a locally finite family. -/
@[stacks 02QW "part (1): local finiteness"]
theorem locallyFinite_irreducibleComponents_supp [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] :
    LocallyFinite fun Z : irreducibleComponents (SheafOfModules.supp F : Set X) ↦
      (Subtype.val '' Z.1 : Set X) :=
  have := isFiniteType_of_isCoherent F
  locallyFinite_image_irreducibleComponents_of_isLocallyNoetherianSpace
    (isLocallyNoetherianSpace_of_isLocallyNoetherian X) Subtype.val
    (SheafOfModules.isClosed_supp F).isClosedEmbedding_subtypeVal

/-- A point of a subspace `T` generizing the generic point of an irreducible component of `T` is
that generic point: it lies in the component by maximality, and specialization is antisymmetric
on a `T0` space. -/
public theorem eq_of_specializes_of_isGenericPoint_component {T : Type u} [TopologicalSpace T]
    [T0Space T] {S : Set T} {C : Set S} (hC : C ∈ irreducibleComponents S) {ξ η : T}
    (hξ : IsGenericPoint ξ (Subtype.val '' C)) (hη : η ∈ S) (hηξ : η ⤳ ξ) : η = ξ := by
  have hsub : C ⊆ closure ({(⟨η, hη⟩ : S)} : Set S) := by
    intro z hz
    rw [closure_subtype]
    simp only [Set.image_singleton]
    exact (hηξ.trans (hξ.specializes ⟨z, hz, rfl⟩)).mem_closure
  have hmem : (⟨η, hη⟩ : S) ∈ C :=
    hC.2 isIrreducible_singleton.closure hsub (subset_closure (Set.mem_singleton _))
  exact (hηξ.antisymm (hξ.specializes ⟨_, hmem, rfl⟩)).eq

/-- A point of `Spec 𝒪_{X,ξ}` is carried by `fromSpecStalk` to a generization of `ξ`. -/
private theorem fromSpecStalk_specializes (ξ : X) (p : PrimeSpectrum (X.presheaf.stalk ξ)) :
    X.fromSpecStalk ξ p ⤳ ξ :=
  (Scheme.range_fromSpecStalk (x := ξ)).subset ⟨p, rfl⟩

/-- A prime of the local ring `𝒪_{X,ξ}` in the support of the stalk `F_ξ` is carried by
`Spec 𝒪_{X,ξ} ⟶ X` to a point of the support of `F`. A section whose germ at `ξ` is not killed
by that prime is, on a small enough affine neighbourhood of the image point, a section with
nonzero image in the localization there. -/
theorem mem_supp_fromSpecStalk_of_mem_support (F : X.Modules) [F.IsQuasicoherent] (ξ : X)
    (p : PrimeSpectrum (X.presheaf.stalk ξ))
    (hp : p ∈ Module.support (X.presheaf.stalk ξ) (F.presheaf.stalk ξ)) :
    X.fromSpecStalk ξ p ∈ SheafOfModules.supp F := by
  classical
  set η : X := X.fromSpecStalk ξ p with hηdef
  have hηξ : η ⤳ ξ := fromSpecStalk_specializes ξ p
  by_contra hmem
  obtain ⟨m, hm⟩ := Module.mem_support_iff'.mp hp
  obtain ⟨U, hξU, hU', s, rfl⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens F.presheaf ξ m
  have hU : IsAffineOpen U := hU'
  have hηU : η ∈ U := hηξ.mem_open U.isOpen hξU
  have hnot : hU.primeIdealOf ⟨η, hηU⟩ ∉ Module.support Γ(X, U) Γ(F, U) := by
    rw [Scheme.Modules.mem_support_sections_iff_mem_supp F ⟨U, hU⟩ η hηU]
    exact hmem
  obtain ⟨a, ha, has⟩ := Module.notMem_support_iff'.mp hnot s
  have hηa : η ∈ X.basicOpen a := by
    have ha' : hU.primeIdealOf ⟨η, hηU⟩ ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen a := by
      rw [hU.fromSpec_preimage_basicOpen]
      exact ha
    change hU.fromSpec (hU.primeIdealOf ⟨η, hηU⟩) ∈ X.basicOpen a at ha'
    simpa only [hU.fromSpec_primeIdealOf] using ha'
  have hagerm : X.presheaf.germ U ξ hξU a ∉ p.asIdeal := by
    have hpre : p ∈ (X.fromSpecStalk ξ) ⁻¹ᵁ X.basicOpen a := hηa
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hξU, IsAffineOpen.fromSpecStalk,
      Scheme.Hom.comp_preimage, hU.fromSpec_preimage_basicOpen] at hpre
    exact hpre
  refine hm (X.presheaf.germ U ξ hξU a) hagerm ?_
  calc
    _ = F.presheaf.germ U ξ hξU (a • s) :=
      (PresheafOfModules.germ_smul (R := X.presheaf) F.val ξ U hξU a s).symm
    _ = 0 := by rw [has, map_zero]

/-- The stalk of a coherent sheaf at `x` has finite length if every prime of `𝒪_{X,x}` in its
support is carried by `fromSpecStalk` to `x` itself and the stalk is nonzero. -/
private theorem isFiniteLength_stalk_of_fromSpecStalk_eq [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent] (x : X) [Nontrivial (F.presheaf.stalk x)]
    (h : ∀ p ∈ Module.support (X.presheaf.stalk x) (F.presheaf.stalk x),
      X.fromSpecStalk x p = x) :
    IsFiniteLength (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  have := isFiniteType_of_isCoherent F
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hfin : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    _root_.SheafOfModules.finite_stalk X.sheaf F x
  refine (support_point (R := X.presheaf.stalk x) (M := F.presheaf.stalk x)).mp
    (Set.Subset.antisymm (fun p hp ↦ ?_) (fun p hp ↦ ?_))
  · refine Set.mem_singleton_iff.mpr ((X.fromSpecStalk x).isEmbedding.injective ?_)
    rw [Scheme.fromSpecStalk_closedPoint]
    exact h p hp
  · rw [Set.mem_singleton_iff.mp hp]
    exact IsLocalRing.closedPoint_mem_support _ _

/-- **Stacks 02QW (2).** At the generic point of an irreducible component of its support, the
stalk of a coherent sheaf on a locally Noetherian scheme has finite length over the local ring
of the scheme. -/
@[stacks 02QW "part (2): finite stalk length", ega "IV 4.7.7" "partial", sga "6 X 1.1.2" "partial"]
theorem isFiniteLength_stalk_of_isGenericPoint_component_supp [IsLocallyNoetherian X]
    (F : X.Modules) [F.IsCoherent]
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X)) (ξ : X)
    (hξ : IsGenericPoint ξ (Subtype.val '' Z.1 : Set X)) :
    IsFiniteLength (X.presheaf.stalk ξ) (F.presheaf.stalk ξ) := by
  have := isFiniteType_of_isCoherent F
  have hξsupp : ξ ∈ SheafOfModules.supp F := by
    obtain ⟨z, hz, hzξ⟩ := hξ.mem
    exact hzξ ▸ z.2
  have : Nontrivial (F.presheaf.stalk ξ) :=
    (SheafOfModules.mem_supp_iff_nontrivial_stalk F ξ).mp hξsupp
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  exact isFiniteLength_stalk_of_fromSpecStalk_eq F ξ fun p hp ↦
    eq_of_specializes_of_isGenericPoint_component Z.2 hξ
      (mem_supp_fromSpecStalk_of_mem_support F ξ p hp) (fromSpecStalk_specializes ξ p)

/-- The stalk at `x` of a coherent sheaf on a locally Noetherian scheme whose support is contained
in `{x}` has finite length over the local ring `𝒪_{X,x}`.

The stalk is a finite module over a Noetherian local ring, so by Stacks 00L5 it is enough, once
the stalk is nonzero, that its support be the closed point alone. The primes of `𝒪_{X,x}` are the
points of `X` generizing `x`, via `AlgebraicGeometry.Scheme.range_fromSpecStalk`, and a prime in
the support of the stalk is carried to a point of the support of the sheaf, hence to `x` itself,
which is the image of the closed point. -/
@[ega "IV 4.7.7" "special case", sga "6 X 1.1.2" "special case"]
theorem isFiniteLength_stalk_of_supp_subset_singleton [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] (x : X) (hsupp : (SheafOfModules.supp F : Set X) ⊆ {x}) :
    IsFiniteLength (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  have : F.IsQuasicoherent := have := isFiniteType_of_isCoherent F; isQuasicoherent_of_isCoherent F
  rcases subsingleton_or_nontrivial (F.presheaf.stalk x) with _ | _
  · exact Module.length_ne_top_iff.mp (by simp [Module.length_eq_zero])
  exact isFiniteLength_stalk_of_fromSpecStalk_eq F x fun p hp ↦
    hsupp (mem_supp_fromSpecStalk_of_mem_support F x p hp)

/-- `Stacks.Chow.isFiniteLength_stalk_of_supp_subset_singleton` with the support hypothesis in the
pointwise form in which it usually arrives: every stalk away from `x` vanishes. -/
theorem isFiniteLength_stalk_of_subsingleton_stalk_ne [IsLocallyNoetherian X] (F : X.Modules)
    [F.IsCoherent] (x : X) (hsupp : ∀ y : X, y ≠ x → Subsingleton (F.presheaf.stalk y)) :
    IsFiniteLength (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  isFiniteLength_stalk_of_supp_subset_singleton F x fun y hy ↦ by
    by_contra hne
    exact not_subsingleton_iff_nontrivial.mpr
      ((SheafOfModules.mem_supp_iff_nontrivial_stalk F y).mp hy) (hsupp y hne)

/-- **Stacks 02QW (3).** If the support of a coherent sheaf has delta-dimension at most `k`, then
a point of the support of delta-dimension `k` is the generic point of an irreducible component of
the support. -/
@[stacks 02QW "part (3): maximal-dimension generic points"]
theorem isGenericPoint_component_supp_of_relativeDimension_eq (C : ChowSituation.{u})
    (f : X ⟶ C.S) [LocallyOfFiniteType f] (F : X.Modules) [F.IsCoherent] (k : ℤ) (ξ : X)
    (hFk : schemeDeltaDimension C ((reducedSupport F).subschemeι ≫ f) ≤ (k : EInt))
    (hξ : ξ ∈ SheafOfModules.supp F)
    (hδ : relativeDimension C.dimensionFunction f ξ = k) :
    ∃ Z : irreducibleComponents (SheafOfModules.supp F : Set X),
      IsGenericPoint ξ (Subtype.val '' Z.1 : Set X) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := isFiniteType_of_isCoherent F
  refine exists_isGenericPoint_of_relativeDimension_eq C f (SheafOfModules.isClosed_supp F)
    (fun y hy ↦ ?_) hξ hδ
  have hy' : y ∈ Set.range (reducedSupport F).subschemeι := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_reducedSupport]
    exact hy
  obtain ⟨z, rfl⟩ := hy'
  exact relativeDimension_le_of_schemeDeltaDimension_le C f _ hFk z

end Stacks.Chow
