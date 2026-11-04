module

public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegree
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleReductions
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.LocallyConstantValues
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.ChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.TorAmplitude

/-!
# Constructible complexes with bounded locally constant reduction

Let `X` be a scheme, `Λ` a Noetherian ring and `I ⊆ Λ` an ideal. The proof of Stacks 09C3
proceeds by induction on the length `b - a` of a range `[a, b]` containing the cohomology of a
derived complete complex `K` whose reduction `K ⊗_Λ^L \underline{Λ/I}` has Tor amplitude in
`[a, b]` and locally constant cohomology sheaves. This file records that condition,
`AlgebraicGeometry.ProEtale.HasBoundedLocallyConstantReduction`, for objects of the derived
category of sheaves of `Λ`-modules on `X_proét`, and shows that constructible complexes with
locally constant reduction satisfy it.

The Tor amplitude is phrased over `Λ`, against every sheaf of `Λ`-modules killed by `I`, and
the cohomology of the reduction as that of `K ⊗_Λ^L \underline{Λ/I}` read over `Λ`: in this
form the condition only involves the derived tensor product of sheaves of `Λ`-modules, whose
functors `- ⊗_Λ^L N` are triangulated.

## Main definitions

* `AlgebraicGeometry.ProEtale.quotientConstantSheaf`: the constant sheaf `\underline{Λ/I}` of
  `Λ`-modules.
* `AlgebraicGeometry.ProEtale.HasBoundedLocallyConstantReduction`: the condition above.

## Main results

* `AlgebraicGeometry.ProEtale.exists_hasBoundedLocallyConstantReduction`: an object of
  `D_cons(X, Λ)` with locally constant reduction over a quasi-compact `X` satisfies the
  condition for some range.

## References

* [Stacks Project, Tag 09C2](https://stacks.math.columbia.edu/tag/09C2)
* [Stacks Project, Tag 09C3](https://stacks.math.columbia.edu/tag/09C3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard Sheaf.monoidalCategory
  Stacks.ModuleSheaf.derivedMonoidal Stacks.ModuleSheaf.derivedSymmetric

variable (X : Scheme.{u}) (Λ : Type (max (u + 1) w)) [CommRing Λ] (I : Ideal Λ)

section Reduction

variable [IsNoetherianRing Λ]

/-- `Λ/I`, as a constant sheaf of `Λ`-modules. -/
abbrev quotientConstantSheaf : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ) :=
  (constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)).obj
    ((ModuleCat.restrictScalars.{max (u + 1) w} (Ideal.Quotient.mk I)).obj
      (ModuleCat.of (Λ ⧸ I) (Λ ⧸ I)))

example : Abelian (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) := inferInstance

/-- The category of sheaves of `Λ`-modules on `X_proét` has finite biproducts. -/
instance : HasFiniteBiproducts (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- **Bounded complexes with locally constant reduction.** An object `K` of the derived category
of sheaves of `Λ`-modules on `X_proét` *has bounded locally constant reduction in `[a, b]`* when

* the corresponding object of `D(X_proét, Λ)` is derived complete along `I·\underline{Λ}`;
* `Hⁱ(K) = 0` for `i ∉ [a, b]`;
* `Hⁱ(K ⊗_Λ^L N) = 0` for `i ∉ [a, b]` and every sheaf `N` killed by `I`, that is, the reduction
  `K ⊗_Λ^L \underline{Λ/I}` has Tor amplitude in `[a, b]`;
* every cohomology sheaf of `K ⊗_Λ^L \underline{Λ/I}` is locally constant of finite type.

This is the induction hypothesis of the proof of Stacks 09C3: an object of `D_cons(X, Λ)` with
locally constant reduction over a quasi-compact `X` satisfies it
(`AlgebraicGeometry.ProEtale.exists_hasBoundedLocallyConstantReduction`), and the cone of a lift
of generators of the top cohomology satisfies it on the smaller range. -/
def HasBoundedLocallyConstantReduction
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ)))
    (a b : ℤ) : Prop :=
  RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I)
      ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.obj K) ∧
    (∀ i : ℤ, i ∉ Set.Icc a b → IsZero ((DerivedCategory.homologyFunctor _ i).obj K)) ∧
    (∀ N : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ),
      (∀ x ∈ I, x • 𝟙 N = 0) → ∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj
          (K ⊗ (DerivedCategory.singleFunctor _ 0).obj N))) ∧
    ∀ i : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1,
      max (u + 1) w, max (u + 1) w} (Scheme.ProEt.topology X) Λ
      ((DerivedCategory.homologyFunctor _ i).obj
        (K ⊗ (DerivedCategory.singleFunctor _ 0).obj (quotientConstantSheaf X Λ I)))

omit [IsNoetherianRing Λ] in
variable {X Λ I} in
/-- The condition on `[a, b]` implies the condition on every larger range. -/
theorem HasBoundedLocallyConstantReduction.mono
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))}
    {a b a' b' : ℤ} (h : HasBoundedLocallyConstantReduction X Λ I K a b) (ha : a' ≤ a)
    (hb : b ≤ b') : HasBoundedLocallyConstantReduction X Λ I K a' b' := by
  have hS : Set.Icc a b ⊆ Set.Icc a' b' := Set.Icc_subset_Icc ha hb
  exact ⟨h.1, fun i hi => h.2.1 i fun h' => hi (hS h'),
    fun N hN i hi => h.2.2.1 N hN i fun h' => hi (hS h'), h.2.2.2⟩

omit [IsNoetherianRing Λ] in
variable {X Λ I} in
/-- The condition is invariant under isomorphism. -/
theorem HasBoundedLocallyConstantReduction.of_iso
    {K K' : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))}
    {a b : ℤ} (h : HasBoundedLocallyConstantReduction X Λ I K a b) (e : K ≅ K') :
    HasBoundedLocallyConstantReduction X Λ I K' a b :=
  ⟨(RingedSite.isDerivedComplete_iff_of_iso _ _
      ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).functor.mapIso e)).1 h.1,
    fun i hi => (h.2.1 i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso e.symm),
    fun N hN i hi => (h.2.2.1 N hN i hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (whiskerRightIso e.symm _)),
    fun i => ObjectProperty.prop_of_iso _
      ((DerivedCategory.homologyFunctor _ i).mapIso (whiskerRightIso e _)) (h.2.2.2 i)⟩

/-- **Constructible complexes with locally constant reduction.** Over a quasi-compact scheme, an
object `K` of `D_cons(X, Λ)` whose reduction `K ⊗_Λ^L \underline{Λ/I}` has locally constant
cohomology sheaves has bounded locally constant reduction in some range `[a, b]`: the bounds and
the Tor amplitude are those of Stacks 09C2 (1), (2), and a locally constant constructible sheaf is
locally constant of finite type. -/
theorem exists_hasBoundedLocallyConstantReduction [CompactSpace X]
    (K : DerivedSheaves.{u, max (u + 1) w, w} X Λ)
    (hK : IsConstructibleViaDerivedReduction.{u, w} X Λ I K)
    (hloc : ∀ i : ℤ, Stacks.ConstantSheaf.IsLocallyConstant (Scheme.ProEt.topology X)
      ((DerivedCategory.homologyFunctor _ i).obj ((derivedReduction.{u, w} X Λ I).obj K))) :
    ∃ a b : ℤ, HasBoundedLocallyConstantReduction X Λ I
      ((derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse.obj K) a b := by
  obtain ⟨a, b, ⟨-, h1⟩, h2⟩ :=
    exists_isDerivedLimit_derivedReductionTower_and_hasTorAmplitude X Λ I hK
  let e := derivedModuleEquiv.{u, max (u + 1) w, w} X Λ
  let E := constantCoefficientModuleEquiv.{u, max (u + 1) w, w} X Λ
  have : E.functor.Additive := Functor.additive_of_preserves_binary_products _
  let K' := e.inverse.obj K
  have hT := h2 1
  rw [pow_one] at hT
  refine ⟨a, b, (RingedSite.isDerivedComplete_iff_of_iso _ _ (e.counitIso.app K)).2 hK.1,
    fun i hi => ?_, fun N hN i hi => ?_, fun i => ?_⟩
  · have h₁ : IsZero (E.functor.obj ((DerivedCategory.homologyFunctor _ i).obj K')) :=
      (h1 i hi).of_iso (((E.functor.mapDerivedCategoryHomologyIso i).app K').symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso (e.counitIso.app K))
    exact (E.inverse.map_isZero h₁).of_iso (E.unitIso.app _)
  · exact (Stacks.ModuleSheaf.HasTorAmplitude.isZero_homology_single_tensor_of_smul_id_eq_zero
      I (IsNoetherian.noetherian I) hT 1 N (by simpa using hN) hi).of_iso
      ((DerivedCategory.homologyFunctor _ i).mapIso (β_ _ _))
  · have h3 := isFiniteTypeLocallyConstantModuleSheaf_of_isLocallyConstant (Λ := Λ ⧸ I) _
      (hK.2.1 i) (hl := hloc i)
    replace h3 :=
      (Stacks.ModuleSheaf.isFiniteTypeLocallyConstantModuleSheaf_restrictScalars_iff.{w, u, u + 1}
        (Scheme.ProEt.topology X) (f := Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective _).2 h3
    obtain ⟨b'⟩ := Stacks.ModuleSheaf.nonempty_restrictScalars_derivedExtendScalars_iso
      (J := Scheme.ProEt.topology X) (Ideal.Quotient.mk I) K'
    exact ObjectProperty.prop_of_iso _
      ((((Stacks.ModuleSheaf.restrictScalars _ (Ideal.Quotient.mk I)).mapDerivedCategoryHomologyIso
        i).app _).symm ≪≫ (DerivedCategory.homologyFunctor _ i).mapIso (b' ≪≫ β_ _ _)) h3

omit [IsNoetherianRing Λ] in
variable {X Λ I} in
/-- If the condition holds on `[a, a]`, then `K` is isomorphic to its cohomology sheaf in degree
`a`, placed in degree `a`. -/
theorem HasBoundedLocallyConstantReduction.nonempty_iso_singleFunctor_homology
    {K : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))} {a : ℤ}
    (hK : HasBoundedLocallyConstantReduction X Λ I K a a) :
    Nonempty (K ≅ (DerivedCategory.singleFunctor _ a).obj
      ((DerivedCategory.homologyFunctor _ a).obj K)) :=
  DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero K a fun j hj =>
    hK.2.1 j fun h => hj (le_antisymm h.2 h.1)

end Reduction

end AlgebraicGeometry.ProEtale
