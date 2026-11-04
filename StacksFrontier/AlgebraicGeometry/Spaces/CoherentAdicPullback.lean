module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicBiproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicCokernel
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback

/-!
# Pullback of coherent adic systems on an algebraic space

Let `f : X' ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`, let `𝓘 ⊆ 𝒪_X` be a sheaf of ideals on the small étale ringed site of `X` and let
`𝓘' = f⁻¹𝓘 · 𝒪_{X'}`.  Termwise pullback of an inverse system of `𝒪_X`-modules is again an
adic system, so it defines a functor

`f^* : Coh(X, 𝓘) ⟶ Coh(X', 𝓘')`,

and that functor is right exact.  This is the algebraic-spaces counterpart of the scheme-level
`Stacks.Coherent.coherentAdicPullback`
(`StacksFrontier/AlgebraicGeometry/FormalGeometry/CoherentAdicSystem/Pullback.lean`).

The transport of the three defining conditions of a coherent adic system is carried out once,
for an arbitrary functor `L : Mod(𝒪_X) ⥤ Mod(𝒪_{X'})` which preserves cokernels, carries
coherent modules to coherent modules, and is compatible with ideal-power multiples in the sense
of `AlgebraicGeometry.Space.IdealPowerMultipleCompatible`; the pullback of Stacks 03LU is the
instantiation.  Annihilation by `𝓘 ⁿ⁺¹` becomes annihilation by `𝓘' ⁿ⁺¹`, and — `L` being right
exact — the quotient presentation `E_n = E_{n+1} / 𝓘 ⁿ⁺¹ E_{n+1}` is carried to
`L E_n = L E_{n+1} / 𝓘' ⁿ⁺¹ L E_{n+1}`.

Right exactness is the source's argument, with the two inputs the unconditional part of this
tree already supplies: cokernels in `Coh(X, 𝓘)` are the levelwise ones
(`AlgebraicGeometry.Space.preservesColimitParallelPairι`) and pullback of modules preserves all
colimits, being a left adjoint (`AlgebraicGeometry.Space.modulePullbackAdjunction`).  So the
composite of `f^*` with the inclusion of `Coh(X', 𝓘')` preserves finite colimits, and that
inclusion reflects them.

## Main definitions

* `AlgebraicGeometry.Space.IdealPowerMultipleCompatible` — compatibility of a functor on modules
  with the ideal-power multiples of `𝓘` and of `𝓘'`.
* `AlgebraicGeometry.Space.coherentAdicMap` — the functor `Coh(X, 𝓘) ⥤ Coh(X', 𝓘')` induced by
  such a functor on modules.
* `AlgebraicGeometry.Space.coherentAdicPullback` — **the functor `f^* : Coh(X, 𝓘) ⥤ Coh(X', 𝓘')`.**

## Main results

* `AlgebraicGeometry.Space.submodule_ι_eq_zero_iff` — a sheaf submodule vanishes exactly when its
  inclusion does.
* `AlgebraicGeometry.Space.coherentAdicInclusion_preservesFiniteColimits` — the inclusion of
  `Coh(X, 𝓘)` into the inverse systems of `𝒪_X`-modules preserves finite colimits.
* `AlgebraicGeometry.Space.isCoherentAdicSystem_map` — a right exact functor compatible with
  ideal-power multiples carries coherent adic systems to coherent adic systems.
* `AlgebraicGeometry.Space.coherentAdicMap_obj_obj`,
  `AlgebraicGeometry.Space.coherentAdicPullback_obj_obj` — **the functor sends the system `(E_n)`
  to the system `(f^* E_n)`**, and
  `AlgebraicGeometry.Space.coherentAdicMap_map_hom_app`,
  `AlgebraicGeometry.Space.coherentAdicPullback_map_hom_app` for its action on morphisms.
* `AlgebraicGeometry.Space.coherentAdicMap_rightExact`,
  `AlgebraicGeometry.Space.coherentAdicPullback_rightExact` — **right exactness.**

## Implementation notes

### No tag is placed

The scheme-level statement is [Stacks Project, Tag 0887], which is about Noetherian *schemes*;
the algebraic-spaces statement is clause (3) of [Stacks Project, Tag 089P].  Neither tag is
claimed here.  0887 is a scheme-level tag, and 089P (3) asserts in addition that `f^*` is
*exact* when `f` is flat, which is not proved here.  Neither kernels nor the abelian structure
are the obstruction any more: on a Noetherian algebraic space `Coh(X, 𝓘)` has kernels by
`AlgebraicGeometry.Space.hasKernels_coherentAdicSystems` and is abelian by
`AlgebraicGeometry.Space.abelian_coherentAdicSystems`, so exactness of a short complex in
`Coh(X, 𝓘)` is a statement with no side condition.  What is missing is the left exactness
itself: the kernel in `Coh(X, 𝓘)` is not the levelwise kernel, so preservation of kernels by
`f^*` does not follow from flatness of `f` termwise, and flatness enters nowhere below.  What is
proved here is therefore an untagged prerequisite of 089P (3), as is the right exactness of
0887 at scheme level.

### The two hypotheses carried, and why

The scheme-level construction has two inputs for free which this tree does not have at the level
of algebraic spaces, and both are carried as hypotheses rather than quietly assumed:

* **Compatibility with ideal-power multiples.**  `IdealPowerMultipleCompatible` is the
  algebraic-spaces form of `Stacks.Algebraization.pullback_idealPowerMultiple_comp_eq_zero_iff`:
  a morphism out of `f^*M` kills the image of `f^*(𝓘 ⁿ M)` exactly when it kills
  `𝓘' ⁿ (f^*M)`.  It is the statement that `𝓘'` *is* the inverse image ideal `f⁻¹𝓘 · 𝒪_{X'}`,
  in the only form the construction uses.  The intended instance of `𝓘'` is
  `AlgebraicGeometry.Space.pullbackIdealImage`, the image of `f^*𝓘 ⟶ 𝒪_{X'}`, which is defined
  for an arbitrary `f`; `AlgebraicGeometry.Space.pullbackIdealSubsheaf` is the same ideal
  described through base-changed charts and is available only for a representable `f`.

  One half of the equivalence is proved, as
  `AlgebraicGeometry.Space.modulePullback_map_idealPowerMultiple_ι_comp_eq_zero`
  (`StacksFrontier.AlgebraicGeometry.Spaces.PullbackIdealPowerCompatible`): a morphism killing
  `𝓘' ⁿ (f^*M)` kills the image of `f^*(𝓘 ⁿ M)`, which needs only that the unit of `f^* ⊣ f_*`
  is `𝒪_X`-linear.  The other half needs, in addition, that the sections of `f^*M` are locally
  on an étale chart combinations of unit images of sections of `M`; that local generation
  statement *is* now available, as
  `AlgebraicGeometry.Space.spanSieve_modulePullbackUnitSections_mem`
  (`StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackUnitGeneration`).  What is still missing is a *common
  chart*: the generators of `𝓘' ⁿ` and the unit sections generating `f^*M` arrive on the charts
  of different chart diagrams, and the identity that multiplies them,
  `AlgebraicGeometry.Space.modulePullbackUnitSection_smul`, is about one chart diagram.  So the
  equivalence is still not proved here and the compatibility is still a hypothesis.

* **Preservation of coherence.**  Coherence on an algebraic space is quasi-coherence on the small
  étale ringed site together with coherence on that site (`AlgebraicGeometry.Space.IsCoherent`).
  Pullback preserves the first only under the inverse-image hypothesis
  `AlgebraicGeometry.Space.HasLocalInverseImagePresentations` of Stacks 03GA, and this tree has
  no statement at all about pullback and `SheafOfModules.IsCoherentOnSite`.  So preservation of
  coherence is a hypothesis too.

Neither hypothesis touches right exactness: `AlgebraicGeometry.Space.coherentAdicMap_rightExact`
needs only that `L` preserves finite colimits, which for the pullback of Stacks 03LU is its
adjunction.

### Why the transport is stated for a general functor

`AlgebraicGeometry.Space.isCoherentAdicSystem_map` mentions no morphism of algebraic spaces: the
argument uses only that `L` preserves cokernels and is compatible with ideal-power multiples, as
at the scheme level.  Stating it that way keeps the two hypotheses above in one place and makes
the pullback case a single instantiation.

## References

* [Stacks Project, Tag 089P](https://stacks.math.columbia.edu/tag/089P)
* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Sheaf submodules with vanishing inclusion -/

section Submodule

variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- A sheaf submodule of a module on an algebraic space vanishes exactly when its inclusion
vanishes. -/
theorem submodule_ι_eq_zero_iff {M : Modules.{u, u} B S hS F hF} (P : M.Submodule) :
    P.ι = 0 ↔ P = ⊥ := by
  refine ⟨fun h => le_antisymm (fun V z hz => ?_) bot_le,
    submodule_ι_eq_zero_of_eq_bot B S hS F hF⟩
  have h2 := (submodule_ι_comp_eq_zero_iff B S hS F hF P (𝟙 M)).mp (by rw [h, zero_comp])
  obtain rfl : z = 0 := (SheafOfModules.Submodule.mem_ker (𝟙 M) V z).mp (h2 V hz)
  exact ((⊥ : M.Submodule).obj V).zero_mem

/-! ### The inclusion of coherent adic systems is right exact -/

variable (𝓘 : (SheafOfModules.unit
  ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).Submodule)

/-- **The inclusion of `Coh(X, 𝓘)` into the inverse systems of `𝒪_X`-modules preserves finite
colimits.**  Cokernels in `Coh(X, 𝓘)` are the levelwise ones
(`AlgebraicGeometry.Space.preservesColimitParallelPairι`), and a functor between preadditive
categories with cokernels which preserves cokernels preserves all finite colimits.

It is *not* left exact: the levelwise kernel of a morphism of coherent adic systems need not be
one again. -/
theorem coherentAdicInclusion_preservesFiniteColimits :
    PreservesFiniteColimits (ObjectProperty.ι (IsCoherentAdicSystem B S hS F hF 𝓘)) :=
  have : HasCoequalizers (CoherentAdicSystems B S hS F hF 𝓘) :=
    Preadditive.hasCoequalizers_of_hasCokernels
  Functor.preservesFiniteColimits_of_preservesCokernels _

end Submodule

/-! ### Transport of coherent adic systems along a right exact functor -/

section Transport

variable {X X' : AlgebraicSpaces B S hS}
  (L : Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS X'.1 X'.2)
  (𝓘 : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
  (𝓘' : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O))).Submodule)

/-- Compatibility of a functor `L : Mod(𝒪_X) ⥤ Mod(𝒪_{X'})` with the ideal-power multiples of
`𝓘 ⊆ 𝒪_X` and of `𝓘' ⊆ 𝒪_{X'}`: a morphism out of `L M` annihilates the image of `L (𝓘 ⁿ M)`
exactly when it annihilates `𝓘' ⁿ (L M)`.

For `L` the pullback along `f : X' ⟶ X` of Stacks 03LU this is the statement that `𝓘'` is the
inverse-image ideal `f⁻¹𝓘 · 𝒪_{X'}`, in the only form the construction of the pullback functor
on coherent adic systems uses it; see the implementation notes of this file. -/
def IdealPowerMultipleCompatible : Prop :=
  ∀ (n : ℕ) (M : Modules.{u, u} B S hS X.1 X.2) {N : Modules.{u, u} B S hS X'.1 X'.2}
    (φ : L.obj M ⟶ N),
    L.map (idealPowerMultiple B S hS X.1 X.2 𝓘 n M).ι ≫ φ = 0 ↔
      (idealPowerMultiple B S hS X'.1 X'.2 𝓘' n (L.obj M)).ι ≫ φ = 0

/-- Termwise application of a functor preserving finite colimits preserves finite colimits:
colimits in a functor category are computed levelwise. -/
theorem whiskeringRight_preservesFiniteColimits [PreservesFiniteColimits L] :
    PreservesFiniteColimits
      ((Functor.whiskeringRight ℕᵒᵖ (Modules.{u, u} B S hS X.1 X.2)
        (Modules.{u, u} B S hS X'.1 X'.2)).obj L) where
  preservesFiniteColimits J _ _ := by
    have : PreservesColimitsOfShape J L := PreservesFiniteColimits.preservesFiniteColimits J
    infer_instance

variable [L.PreservesZeroMorphisms] [PreservesColimitsOfShape WalkingParallelPair L]

/-- A right exact functor compatible with ideal-power multiples carries the quotient by one to
the quotient by the other, compatibly with the two quotient maps. -/
theorem exists_functor_idealPowerQuotient_iso (n : ℕ) (M : Modules.{u, u} B S hS X.1 X.2)
    (hw : ∀ {N : Modules.{u, u} B S hS X'.1 X'.2} (φ : L.obj M ⟶ N),
      L.map (idealPowerMultiple B S hS X.1 X.2 𝓘 n M).ι ≫ φ = 0 ↔
        (idealPowerMultiple B S hS X'.1 X'.2 𝓘' n (L.obj M)).ι ≫ φ = 0) :
    ∃ e : L.obj (idealPowerQuotient B S hS X.1 X.2 𝓘 n M) ≅
        idealPowerQuotient B S hS X'.1 X'.2 𝓘' n (L.obj M),
      L.map (cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 n M).ι) ≫ e.hom =
        cokernel.π (idealPowerMultiple B S hS X'.1 X'.2 𝓘' n (L.obj M)).ι := by
  set P := idealPowerMultiple B S hS X.1 X.2 𝓘 n M
  set Q := idealPowerMultiple B S hS X'.1 X'.2 𝓘' n (L.obj M)
  have hc := isColimitCoforkMapOfIsColimit' L (cokernel.condition P.ι) (cokernelIsCokernel P.ι)
  let hc' := CokernelCofork.isColimitOfIsColimitOfIff' hc Q.ι fun {_} φ => hw φ
  let e := (cokernelIsCokernel Q.ι).coconePointUniqueUpToIso hc'
  have he : cokernel.π Q.ι ≫ e.hom = L.map (cokernel.π P.ι) :=
    (cokernelIsCokernel Q.ι).comp_coconePointUniqueUpToIso_hom hc' WalkingParallelPair.one
  exact ⟨e.symm, (Iso.comp_inv_eq e).mpr he.symm⟩

/-- **A right exact functor compatible with ideal-power multiples carries coherent adic systems
to coherent adic systems**, provided it preserves coherence termwise. -/
theorem isCoherentAdicSystem_map (hw : IdealPowerMultipleCompatible B S hS L 𝓘 𝓘')
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS X.1 X.2}
    (hE : IsCoherentAdicSystem B S hS X.1 X.2 𝓘 E)
    (hcoh : ∀ n : ℕ, IsCoherent B S hS X'.1 X'.2 (L.obj (E.obj (op n)))) :
    IsCoherentAdicSystem B S hS X'.1 X'.2 𝓘' (E ⋙ L) := by
  refine ⟨hcoh, fun n => ?_, fun n => ?_⟩
  · show idealPowerMultiple B S hS X'.1 X'.2 𝓘' (n + 1) (L.obj (E.obj (op n))) = ⊥
    refine (submodule_ι_eq_zero_iff B S hS X'.1 X'.2 _).mp ?_
    have h := (hw (n + 1) (E.obj (op n)) (𝟙 _)).mp
      (by simp [(submodule_ι_eq_zero_iff B S hS X.1 X.2 _).mpr (hE.2.1 n)])
    exact (Category.comp_id _).symm.trans h
  · obtain ⟨q, hq⟩ := exists_functor_idealPowerQuotient_iso B S hS L 𝓘 𝓘' (n + 1)
      (E.obj (op (n + 1))) (hw (n + 1) (E.obj (op (n + 1))))
    obtain ⟨ei, hei⟩ := hE.2.2 n
    refine ⟨q.symm ≪≫ L.mapIso ei, ?_⟩
    show cokernel.π _ ≫ (q.inv ≫ L.map ei.hom) = _
    rw [← hq, Category.assoc, Iso.hom_inv_id_assoc, ← L.map_comp, hei]
    rfl

variable (hw : IdealPowerMultipleCompatible B S hS L 𝓘 𝓘')
  (hcoh : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 M →
    IsCoherent B S hS X'.1 X'.2 (L.obj M))

/-- The functor `Coh(X, 𝓘) ⥤ Coh(X', 𝓘')` induced by a right exact functor on modules which is
compatible with the ideal-power multiples and preserves coherence.

It is built as a lift of termwise application of `L`, so its action on objects and morphisms is
the canonical one; see `AlgebraicGeometry.Space.coherentAdicMap_obj_obj`. -/
def coherentAdicMap :
    CoherentAdicSystems B S hS X.1 X.2 𝓘 ⥤ CoherentAdicSystems B S hS X'.1 X'.2 𝓘' :=
  ObjectProperty.lift (IsCoherentAdicSystem B S hS X'.1 X'.2 𝓘')
    (ObjectProperty.ι (IsCoherentAdicSystem B S hS X.1 X.2 𝓘) ⋙
      (Functor.whiskeringRight _ _ _).obj L)
    fun E => isCoherentAdicSystem_map B S hS L 𝓘 𝓘' hw E.property
      fun n => hcoh _ (E.property.1 n)

/-- The induced functor sends the system `(E_n)` to the system `(L E_n)`. -/
theorem coherentAdicMap_obj_obj (E : CoherentAdicSystems B S hS X.1 X.2 𝓘) (n : ℕᵒᵖ) :
    ((coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh).obj E).obj.obj n = L.obj (E.obj.obj n) :=
  rfl

/-- The induced functor acts on morphisms termwise. -/
theorem coherentAdicMap_map_hom_app {E E' : CoherentAdicSystems B S hS X.1 X.2 𝓘} (α : E ⟶ E')
    (n : ℕᵒᵖ) :
    ((coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh).map α).hom.app n = L.map (α.hom.app n) :=
  rfl

/-- **The induced functor `Coh(X, 𝓘) ⥤ Coh(X', 𝓘')` is right exact.**

Termwise application of `L` to inverse systems preserves finite colimits, colimits in a functor
category being levelwise; the inclusion of `Coh(X, 𝓘)` preserves finite colimits, cokernels
there being levelwise; so the composite of the induced functor with the inclusion of
`Coh(X', 𝓘')` preserves finite colimits, and that inclusion reflects them. -/
theorem coherentAdicMap_rightExact [PreservesFiniteColimits L] :
    rightExactFunctor _ _ (coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh) := by
  rw [rightExactFunctor_iff]
  have hP : PreservesFiniteColimits
      (ObjectProperty.ι (IsCoherentAdicSystem B S hS X.1 X.2 𝓘)) :=
    coherentAdicInclusion_preservesFiniteColimits B S hS X.1 X.2 𝓘
  have hW := whiskeringRight_preservesFiniteColimits B S hS L (X' := X')
  have hcomp : PreservesFiniteColimits (coherentAdicMap B S hS L 𝓘 𝓘' hw hcoh ⋙
      ObjectProperty.ι (IsCoherentAdicSystem B S hS X'.1 X'.2 𝓘')) := by
    show PreservesFiniteColimits (ObjectProperty.ι (IsCoherentAdicSystem B S hS X.1 X.2 𝓘) ⋙
      (Functor.whiskeringRight _ _ _).obj L)
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (ObjectProperty.ι (IsCoherentAdicSystem B S hS X'.1 X'.2 𝓘'))

end Transport

/-! ### The pullback functor -/

section Pullback

variable {X X' : AlgebraicSpaces B S hS} (f : X' ⟶ X)

/-- Pullback of `𝒪`-modules along a morphism of algebraic spaces preserves all colimits: it is
the left adjoint of the adjunction of Stacks 03LU. -/
theorem preservesColimits_modulePullback :
    PreservesColimitsOfSize.{u, u + 1} (modulePullback B S hS f) :=
  (modulePullbackAdjunction B S hS f).leftAdjoint_preservesColimits

/-- Pullback of `𝒪`-modules along a morphism of algebraic spaces preserves finite colimits. -/
theorem preservesFiniteColimits_modulePullback :
    PreservesFiniteColimits (modulePullback B S hS f) :=
  have := preservesColimits_modulePullback B S hS f
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Pullback of `𝒪`-modules along a morphism of algebraic spaces preserves zero morphisms: it is
a left adjoint. -/
theorem preservesZeroMorphisms_modulePullback :
    (modulePullback B S hS f).PreservesZeroMorphisms :=
  have : (modulePullback B S hS f).IsLeftAdjoint :=
    ⟨_, ⟨modulePullbackAdjunction B S hS f⟩⟩
  inferInstance

variable (𝓘 : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule)
  (𝓘' : (SheafOfModules.unit
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X'.1 X'.2).O))).Submodule)
  (hw : IdealPowerMultipleCompatible B S hS (modulePullback B S hS f) 𝓘 𝓘')
  (hcoh : ∀ M : Modules.{u, u} B S hS X.1 X.2, IsCoherent B S hS X.1 X.2 M →
    IsCoherent B S hS X'.1 X'.2 ((modulePullback B S hS f).obj M))

include hw hcoh in
/-- **Termwise pullback of a coherent adic system along `𝓘` is a coherent adic system along
`𝓘' = f⁻¹𝓘 · 𝒪_{X'}`.** -/
theorem isCoherentAdicSystem_modulePullback
    {E : ℕᵒᵖ ⥤ Modules.{u, u} B S hS X.1 X.2}
    (hE : IsCoherentAdicSystem B S hS X.1 X.2 𝓘 E) :
    IsCoherentAdicSystem B S hS X'.1 X'.2 𝓘' (E ⋙ modulePullback B S hS f) :=
  have := preservesZeroMorphisms_modulePullback B S hS f
  have := preservesFiniteColimits_modulePullback B S hS f
  isCoherentAdicSystem_map B S hS (modulePullback B S hS f) 𝓘 𝓘' hw hE
    fun n => hcoh _ (hE.1 n)

/-- **The functor `f^* : Coh(X, 𝓘) ⥤ Coh(X', 𝓘')`.**  For a morphism `f : X' ⟶ X` of algebraic
spaces and a sheaf of ideals `𝓘 ⊆ 𝒪_X`, termwise pullback is a functor from the coherent adic
systems along `𝓘` to those along `𝓘' = f⁻¹𝓘 · 𝒪_{X'}`.

It is built as a lift of termwise pullback, so its action on objects and morphisms is the
canonical one; see `AlgebraicGeometry.Space.coherentAdicPullback_obj_obj`. -/
def coherentAdicPullback :
    CoherentAdicSystems B S hS X.1 X.2 𝓘 ⥤ CoherentAdicSystems B S hS X'.1 X'.2 𝓘' :=
  have := preservesZeroMorphisms_modulePullback B S hS f
  have := preservesFiniteColimits_modulePullback B S hS f
  coherentAdicMap B S hS (modulePullback B S hS f) 𝓘 𝓘' hw hcoh

/-- **The pullback functor sends the system `(E_n)` to the system `(f^* E_n)`.** -/
theorem coherentAdicPullback_obj_obj (E : CoherentAdicSystems B S hS X.1 X.2 𝓘) (n : ℕᵒᵖ) :
    ((coherentAdicPullback B S hS f 𝓘 𝓘' hw hcoh).obj E).obj.obj n =
      (modulePullback B S hS f).obj (E.obj.obj n) :=
  rfl

/-- The pullback functor on coherent adic systems acts on morphisms by termwise pullback. -/
theorem coherentAdicPullback_map_hom_app
    {E E' : CoherentAdicSystems B S hS X.1 X.2 𝓘} (α : E ⟶ E') (n : ℕᵒᵖ) :
    ((coherentAdicPullback B S hS f 𝓘 𝓘' hw hcoh).map α).hom.app n =
      (modulePullback B S hS f).map (α.hom.app n) :=
  rfl

/-- **The pullback functor on coherent adic systems is right exact.**

Termwise pullback of inverse systems preserves all colimits, being a left adjoint; the inclusion
of `Coh(X, 𝓘)` preserves finite colimits, cokernels there being levelwise; so the composite of
`f^*` with the inclusion of `Coh(X', 𝓘')` preserves finite colimits, and that inclusion reflects
them. -/
theorem coherentAdicPullback_rightExact :
    rightExactFunctor _ _ (coherentAdicPullback B S hS f 𝓘 𝓘' hw hcoh) :=
  have := preservesZeroMorphisms_modulePullback B S hS f
  have := preservesFiniteColimits_modulePullback B S hS f
  coherentAdicMap_rightExact B S hS (modulePullback B S hS f) 𝓘 𝓘' hw hcoh

/-- **The pullback functor on coherent adic systems preserves finite colimits**, the unbundled
form of `AlgebraicGeometry.Space.coherentAdicPullback_rightExact`. -/
theorem preservesFiniteColimits_coherentAdicPullback :
    PreservesFiniteColimits (coherentAdicPullback B S hS f 𝓘 𝓘' hw hcoh) :=
  (rightExactFunctor_iff _).mp (coherentAdicPullback_rightExact B S hS f 𝓘 𝓘' hw hcoh)

end Pullback

end AlgebraicGeometry.Space

end
