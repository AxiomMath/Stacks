module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedPushforwardBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentDerivedComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperSupportHigherDirectImageCoherence

/-!
# The derived direct image of a coherent complex with proper support

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` which is locally of finite
type, with `Y` Noetherian.

* **Stacks 08GK**: if `E ∈ D^b_{Coh}(𝒪_X)` and the support of every `H^i(E)` is proper over `Y`,
  then `Rf_*E ∈ D^b_{Coh}(𝒪_Y)`.
* **Stacks 0D0R**: if `E ∈ D^+_{Coh}(𝒪_X)` and the support of every `H^i(E)` is proper over `Y`,
  then `Rf_*E ∈ D^+_{Coh}(𝒪_Y)`.

**On the statement of Stacks 0D0R.**  The source writes "the support of `H^i(E)` is proper over
`S`".  Read literally this is false, and "over `Y`", as in Stacks 08GK whose proof it invokes, is
meant.  Let `k` be a field, `S = Spec k`, `Y` the projective line over `k` with its origin doubled
(a Noetherian scheme, not separated over `S`), `X ≅ ℙ¹_k` one of its two charts and `f : X → Y`
the open immersion; `f` is locally of finite type.  Take `E = 𝒪_X`: its support `X` is proper over
`S`.  But near the second origin `0'` of `Y`, with coordinate `t`, the preimage of a neighbourhood
`Spec k[t]` of `0'` is `Spec k[t, t⁻¹]`, so `H^0(Rf_*E) = f_*𝒪_X` has sections `k[t, t⁻¹]` there,
which is not a finite `k[t]`-module: `Rf_*E ∉ D^+_{Coh}(𝒪_Y)`.  The statement is formalized here
with the support proper over `Y`.

Here `Rf_*` is `Stacks.DerivedFunctor.totalRightDerived` of
`AlgebraicGeometry.Space.modulePushforward`.

## Main results

* `AlgebraicGeometry.Space.derivedCategoryBBounded_derivedModulePushforward_single`: the case of
  one coherent module with proper support placed in degree zero.
* `AlgebraicGeometry.Space.derivedCategoryBBounded_derivedModulePushforward_of_hasProperSupport`:
  the bounded case.
* `AlgebraicGeometry.Space.derivedCategoryBPlus_derivedModulePushforward_of_hasProperSupport`:
  the bounded below case, with the support proper over `Y`.

## References

* [Stacks Project, Lemma 75.8.1 (Tag 08GK)](https://stacks.math.columbia.edu/tag/08GK)
* [Stacks Project, Lemma 75.8.2 (Tag 0D0R)](https://stacks.math.columbia.edu/tag/0D0R)
* [Stacks Project, Lemma 75.7.10 (Tag 08GC)](https://stacks.math.columbia.edu/tag/08GC)
* [Stacks Project, Tag 073G](https://stacks.math.columbia.edu/tag/073G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits DerivedCategoryB

namespace AlgebraicGeometry.Space

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

attribute [local instance] isGrothendieckAbelian_modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The coherent modules on an algebraic space form a weak Serre subcategory: they contain zero
and are closed under isomorphisms, kernels, cokernels (Stacks 07UC, through Stacks 01BY) and
extensions (Stacks 07UC). -/
instance isCoherent_isWeakSerreClass (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) : (isCoherent.{u, u} B S hS F hF).IsWeakSerreClass where

/-- The coherent modules on an algebraic space form a weak Serre subcategory in the sense of
Stacks 02MO. -/
theorem isWeakSerre_isCoherent (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) : WeakSerre.IsWeakSerre (isCoherent.{u, u} B S hS F hF) :=
  WeakSerre.isWeakSerre_of_isWeakSerreClass _

variable {X Y : AlgebraicSpaces B S hS}

/-- For `f` locally of finite type over a quasi-compact and locally Noetherian `Y`, the derived
direct image of a coherent module with proper support, placed in degree zero, lies in
`D^b_{Coh}(𝒪_Y)`. -/
theorem derivedCategoryBBounded_derivedModulePushforward_single (f : X ⟶ Y)
    (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : HasEtaleLocalProperty B S hS Y.1 (fun T : Scheme.{u} => IsLocallyNoetherian T))
    (hYqc : IsQuasiCompactSpace B S hS Y.1)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (hsupp : HasProperSupport B S hS X.2 Y.2 f.hom hf ((SheafOfModules.toSheaf _).obj F)) :
    derivedCategoryBBounded (isCoherent.{u, u} B S hS Y.1 Y.2)
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F)) := by
  have := hasInjectiveResolutions_modules B S hS X.1 X.2
  obtain ⟨N, hN⟩ := exists_isZero_higherDirectImage_of_hasProperSupport B S hS f hf hY hYqc F hF
    hsupp
  have hneg : ∀ n : ℤ, n < 0 → IsZero ((DerivedCategory.homologyFunctor _ n).obj
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj
        ((DerivedCategory.singleFunctor (Modules.{u, u} B S hS X.1 X.2) 0).obj F))) :=
    fun n hn => isZero_homology_derivedModulePushforward_single B S hS f F n hn
  refine ⟨⟨⟨0, hneg⟩, ⟨N, fun n hn => ?_⟩⟩, fun n => ?_⟩
  · exact IsZero.of_iso (hN n.toNat (by omega))
      (homologyDerivedModulePushforwardSingleIso B S hS f F 0 n n.toNat (by omega))
  · by_cases hn : n < 0
    · exact IsCoherent.of_isZero B S hS _ _ (hneg n hn)
    · exact isCoherent_of_iso B S hS Y.2
        (homologyDerivedModulePushforwardSingleIso B S hS f F 0 n n.toNat (by omega)).symm
        (isCoherent_higherDirectImage_of_hasProperSupport B S hS f hf hY F hF hsupp n.toNat)

/-- The objects of `D(𝒪_X)` whose derived direct image lies in `D^b_{Coh}(𝒪_Y)`. -/
abbrev derivedPushforwardBoundedCoherent (f : X ⟶ Y) :
    ObjectProperty (DerivedCategory (Modules.{u, u} B S hS X.1 X.2)) :=
  (derivedCategoryBBounded (isCoherent.{u, u} B S hS Y.1 Y.2)).inverseImage
    (Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f))

/-- The objects whose derived direct image lies in `D^b_{Coh}(𝒪_Y)` are closed under
isomorphisms. -/
instance (f : X ⟶ Y) :
    (derivedPushforwardBoundedCoherent B S hS f).IsClosedUnderIsomorphisms := by
  have := derivedCategoryBBounded_isClosedUnderIsomorphisms _
    (isWeakSerre_isCoherent B S hS Y.1 Y.2)
  infer_instance

/-- The objects whose derived direct image lies in `D^b_{Coh}(𝒪_Y)` are stable under shifts. -/
instance (f : X ⟶ Y) :
    (derivedPushforwardBoundedCoherent B S hS f).IsStableUnderShift ℤ := by
  have := derivedCategoryBBounded_isStableUnderShift _ (isWeakSerre_isCoherent B S hS Y.1 Y.2)
  refine ⟨fun a ↦ ⟨fun K hK ↦ ?_⟩⟩
  exact (derivedCategoryBBounded_isClosedUnderIsomorphisms _
    (isWeakSerre_isCoherent B S hS Y.1 Y.2)).of_iso
    (((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).commShiftIso a).app
      K).symm ((derivedCategoryBBounded (isCoherent.{u, u} B S hS Y.1 Y.2)).le_shift a _ hK)

/-- The objects whose derived direct image lies in `D^b_{Coh}(𝒪_Y)` are closed under
extensions by distinguished triangles. -/
instance (f : X ⟶ Y) :
    (derivedPushforwardBoundedCoherent B S hS f).IsTriangulatedClosed₂ := by
  have := derivedCategoryBBounded_isClosedUnderIsomorphisms _
    (isWeakSerre_isCoherent B S hS Y.1 Y.2)
  have := derivedCategoryBBounded_isTriangulated _ (isWeakSerre_isCoherent B S hS Y.1 Y.2)
  refine ObjectProperty.IsTriangulatedClosed₂.mk' (fun T hT h₁ h₃ ↦ ?_)
  exact (derivedCategoryBBounded (isCoherent.{u, u} B S hS Y.1 Y.2)).ext_of_isTriangulatedClosed₂
    ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).mapTriangle.obj T)
    ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).map_distinguished
      T hT) h₁ h₃

/-- Let `S` be a scheme and `f : X ⟶ Y` a morphism of algebraic spaces over `S` which is locally
of finite type, with `Y` Noetherian.  Let `E ∈ D^b_{Coh}(𝒪_X)` be such that the support of
`H^i(E)` is proper over `Y` for all `i`.  Then `Rf_*E ∈ D^b_{Coh}(𝒪_Y)`. -/
@[stacks 08GK]
theorem derivedCategoryBBounded_derivedModulePushforward_of_hasProperSupport
    (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : derivedCategoryBBounded (isCoherent.{u, u} B S hS X.1 X.2) E)
    (hsupp : ∀ i : ℤ, HasProperSupport B S hS X.2 Y.2 f.hom hf
      ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E))) :
    derivedCategoryBBounded (isCoherent.{u, u} B S hS Y.1 Y.2)
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj E) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hE.1
  have hGE : E.IsGE a := (DerivedCategory.isGE_iff E a).2 ha
  have hLE : E.IsLE (a + ((b - a).toNat : ℤ)) := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact hb i (by omega)
  refine (derivedPushforwardBoundedCoherent B S hS f).prop_of_isGE_of_isLE a (b - a).toNat E hGE
    hLE fun q _ _ => ?_
  exact derivedCategoryBBounded_derivedModulePushforward_single B S hS f hf hY.2.2 hY.1 _
    (hE.2 q) (hsupp q)

/-- Let `S` be a scheme and `f : X ⟶ Y` a morphism of algebraic spaces over `S` which is locally
of finite type, with `Y` Noetherian.  Let `E ∈ D^+_{Coh}(𝒪_X)` be such that the support of
`H^i(E)` is proper over `Y` for all `i`.  Then `Rf_*E ∈ D^+_{Coh}(𝒪_Y)`.  (With the support
only proper over `S` the statement is false; see the module documentation.) -/
@[stacks 0D0R "with the support of each H^i(E) proper over Y: proper over S, as printed, the \
statement fails (the open immersion of one chart P^1 into the projective line with doubled origin \
over a field, with E = O_X), and Y is what the source's proof, through 08GK, uses"]
theorem derivedCategoryBPlus_derivedModulePushforward_of_hasProperSupport
    (hTop : B.Contains (⊤_ Scheme.{u})) (f : X ⟶ Y) (hf : IsLocallyOfFiniteType B S hS f.hom)
    (hY : IsNoetherian B S hS hTop Y.1)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : derivedCategoryBPlus (isCoherent.{u, u} B S hS X.1 X.2) E)
    (hsupp : ∀ i : ℤ, HasProperSupport B S hS X.2 Y.2 f.hom hf
      ((SheafOfModules.toSheaf _).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, u} B S hS X.1 X.2) i).obj E))) :
    derivedCategoryBPlus (isCoherent.{u, u} B S hS Y.1 Y.2)
      ((Stacks.DerivedFunctor.totalRightDerived (modulePushforward B S hS f)).obj E) := by
  obtain ⟨a, ha⟩ := hE.1
  refine derivedCategoryBPlus_map_obj_of_isGE _ _ (isWeakSerre_isCoherent B S hS Y.1 Y.2)
    (fun L m hL => isGE_derivedModulePushforward_obj B S hS f L m hL) E a
    ((DerivedCategory.isGE_iff E a).2 ha) fun q => ?_
  have h := derivedCategoryBBounded_derivedModulePushforward_single B S hS f hf hY.2.2 hY.1 _
    (hE.2 q) (hsupp q)
  exact ⟨h.1.1, h.2⟩

end AlgebraicGeometry.Space

end
