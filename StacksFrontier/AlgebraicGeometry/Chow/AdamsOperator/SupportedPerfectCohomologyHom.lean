module

public import StacksFrontier.AlgebraicGeometry.Chow.AdamsOperator.SupportedCoherentKGroupIso
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerCycleFromCycles
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DimensionLayerKGroupAdditivity
public import StacksFrontier.AlgebraicGeometry.Perfect.KGroups.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentComplex.LocallyFiniteCohomology
public import StacksFrontier.AlgebraicGeometry.TopIdeals.Basic
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.TwoOutOfThreeShortExact
public import StacksFrontier.CategoryTheory.Triangulated.Quotient
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.IsPerfectComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.RetractOfAPerfectObject
import StacksCore.Tactic.StacksAttribute

/-!
# The homomorphism `K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X))`

Let `X` be a locally Noetherian scheme and `Z ⊂ X` a closed subscheme. For a perfect complex `E`
on `X` whose cohomology sheaves are supported on `Z`, the cohomology sheaves `H^i(E)` are coherent
and supported on `Z`, and near every point only finitely many of them are nonzero. Hence the direct
sums `⊕_{i ∈ ℤ} H^{2i}(E)` and `⊕_{i ∈ ℤ} H^{2i + 1}(E)`, taken in the category of `𝒪_X`-modules,
are coherent modules supported on `Z`, and the rule
`E ↦ [⊕_{i ∈ ℤ} H^{2i}(E)] - [⊕_{i ∈ ℤ} H^{2i + 1}(E)]` defines a homomorphism
`K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X)) = K'_0(Z)`, the last identification being
[Stacks, Tag 0FDT].

## Main definitions

* `AlgebraicGeometry.supportedPerfectCohomologyHom`: the homomorphism
  `K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X))`.
* `AlgebraicGeometry.supportedPerfectCohomologyHomToCoherent`: the same homomorphism with target
  `K'_0(Z) = K_0(Coh(𝒪_Z))`.
* `AlgebraicGeometry.SupportedPerfectCohomology.evenHomologySupported` and
  `AlgebraicGeometry.SupportedPerfectCohomology.oddHomologySupported`: the direct sums
  `⊕_i H^{2i}(E)` and `⊕_i H^{2i + 1}(E)` as objects of `Coh_Z(X)`.

## Main results

* `AlgebraicGeometry.supportedPerfectCohomologyHom_cls`: the class of `E` is sent to
  `[⊕_i H^{2i}(E)] - [⊕_i H^{2i + 1}(E)]`.
* `AlgebraicGeometry.SupportedPerfectCohomology.supportedPerfectParityClass_distinguished`: this
  element is additive on distinguished triangles.
* `AlgebraicGeometry.supportedPerfect_isStrictlyFull_isTriangulated_isSaturated`:
  `D_{Z, perf}(𝒪_X)` is a strictly full, saturated, triangulated subcategory of `D(𝒪_X)`.

## Implementation notes

The direct sums are infinite in general (when `X` is not quasi-compact), and the content of the
construction is that they are coherent. Coherence is local, and near a point the sum agrees with a
finite one, which is `Stacks.Chow.isCoherent_coproduct_of_locallyFinite`.

Additivity is the source's argument. A distinguished triangle `E₁ → E₂ → E₃ → E₁[1]` gives the
long exact sequence `⋯ → H^n(E₁) → H^n(E₂) → H^n(E₃) → H^{n+1}(E₁) → ⋯`, which splits into the
short exact sequences `0 → ker → H^n(E_j) → ker → 0` of kernels of consecutive maps. The kernels
are coherent, supported on `Z` and locally finite in `n`, and coproducts of short exact sequences
of `𝒪_X`-modules are short exact, so summing these sequences over all even, respectively all odd,
degrees `n` gives six relations in `K_0(Coh_Z(X))`. After reindexing the kernels of
`H^n(E₁) → H^n(E₂)` along `n ↦ n + 2`, they combine to the additivity.

## References

* [Stacks Project, Tag 0FEP](https://stacks.math.columbia.edu/tag/0FEP)
* [Stacks Project, Tag 0FDT](https://stacks.math.columbia.edu/tag/0FDT)
* [Stacks Project, Tag 0FDN](https://stacks.math.columbia.edu/tag/0FDN)
* [Stacks Project, Tag 08CS](https://stacks.math.columbia.edu/tag/08CS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category.{v} C] [Abelian C]

/-- For a short complex `A → B → C`, the short complex `ker(A → B) → A → ker(B → C)`, the second
map being the factorisation of `A → B` through `ker(B → C)`. -/
abbrev kernelKernelSequence (S : ShortComplex C) : ShortComplex C :=
  ShortComplex.mk (kernel.ι S.f) (kernel.lift S.g S.f S.zero) (by ext; simp)

/-- An exact sequence `A → B → C` gives the short exact sequence
`0 → ker(A → B) → A → ker(B → C) → 0`. -/
theorem shortExact_kernelKernelSequence (S : ShortComplex C) (hS : S.Exact) :
    (kernelKernelSequence S).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_ (inferInstanceAs (Mono (kernel.ι S.f))) hS.epi_kernelLift
  exact ShortComplex.exact_of_f_is_kernel _ (KernelFork.IsLimit.ofι _ _
    (fun k hk => kernel.lift S.f k (by simpa [kernelKernelSequence] using hk =≫ kernel.ι S.g))
    (fun k hk => by simp [kernelKernelSequence])
    (fun k hk m hm => by ext; simpa [kernelKernelSequence] using hm))

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry.SupportedPerfectCohomology

open StrictlyPerfect

universe d

variable {X : Scheme.{u}}

/-- The coproduct of a `ℤ`-indexed family of `𝒪_X`-modules is that of the family indexed by
`ULift ℤ`. -/
private def sigmaUliftIso (F : ℤ → OXMod.{u, u} X.toRingedSpace) :
    (∐ fun n : ULift.{u} ℤ => (F n.down : X.Modules)) ≅ ∐ (F : ℤ → X.Modules) :=
  Sigma.whiskerEquiv Equiv.ulift (fun _ => Iso.refl _)

/-- A direct sum of coherent `𝒪_X`-modules indexed by `ℤ` whose supports form a locally finite
family is coherent. -/
theorem isCoherent_sigma_int_of_locallyFinite [IsLocallyNoetherian X]
    (F : ℤ → OXMod.{u, u} X.toRingedSpace) (hF : ∀ n, (F n).IsCoherent)
    (hl : LocallyFinite fun n => SheafOfModules.supp (F n)) :
    (∐ F).IsCoherent :=
  Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_of_iso (sigmaUliftIso F)
    (Stacks.Chow.isCoherent_coproduct_of_locallyFinite _ (fun n => hF n.down)
      (hl.comp_injective ULift.down_injective))

/-- The support of a direct sum of `𝒪_X`-modules indexed by `ℤ` is contained in any set containing
the supports of all summands. -/
theorem supp_sigma_int_subset (F : ℤ → OXMod.{u, u} X.toRingedSpace) (S : Set X)
    (h : ∀ n, SheafOfModules.supp (F n) ⊆ S) : SheafOfModules.supp (∐ F) ⊆ S :=
  (SheafOfModules.supp_eq_of_iso (sigmaUliftIso F).symm).subset.trans
    ((Stacks.Chow.supp_sigma_subset_iUnion_supp _).trans (Set.iUnion_subset fun n => h n.down))

section Supported

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]

/-- A `ℤ`-indexed family of coherent `𝒪_X`-modules supported on `Z` whose supports form a locally
finite family. -/
def IsLocallyFiniteSupportedFamily (F : ℤ → OXMod.{u, u} X.toRingedSpace) : Prop :=
  (∀ n, (F n).IsCoherent) ∧ (∀ n, SheafOfModules.supp (F n) ⊆ Set.range i.base) ∧
    LocallyFinite fun n => SheafOfModules.supp (F n)

/-- The direct sum of a locally finite family of coherent `𝒪_X`-modules supported on `Z`, as an
object of `Coh_Z(X)`. -/
def sigmaSupportedCoherent (F : ℤ → OXMod.{u, u} X.toRingedSpace)
    (hF : IsLocallyFiniteSupportedFamily i F) : SupportedCoherentModules i :=
  ⟨⟨∐ F, CoherentAbelian.stacksIsCoherent_of_isCoherent
      (isCoherent_sigma_int_of_locallyFinite F hF.1 hF.2.2)⟩,
    supp_sigma_int_subset F _ hF.2.1⟩

/-- Direct sums of termwise short exact sequences of locally finite families are short exact,
so their classes are additive in `K_0(Coh_Z(X))`. -/
theorem mk_sigmaSupportedCoherent_of_shortExact
    (S : ℤ → ShortComplex (OXMod.{u, u} X.toRingedSpace)) (hS : ∀ n, (S n).ShortExact)
    (h₁ : IsLocallyFiniteSupportedFamily i fun n => (S n).X₁)
    (h₂ : IsLocallyFiniteSupportedFamily i fun n => (S n).X₂)
    (h₃ : IsLocallyFiniteSupportedFamily i fun n => (S n).X₃) :
    KZero.mk _ (sigmaSupportedCoherent i _ h₂) =
      KZero.mk _ (sigmaSupportedCoherent i _ h₁) + KZero.mk _ (sigmaSupportedCoherent i _ h₃) := by
  have hzero : (Limits.Sigma.map fun n => (S n).f) ≫ (Limits.Sigma.map fun n => (S n).g) = 0 :=
    Limits.Sigma.hom_ext _ _ fun n => by simp
  have hT := Stacks.SheafOfModules.KFlatTwoOutOfThree.shortExact_coproduct S hS
    (coproductIsCoproduct _) (coproductIsCoproduct _) (coproductIsCoproduct _) _ _ hzero
    (fun n => by simp) (fun n => by simp)
  let T : ShortComplex (SupportedCoherentModules i) :=
    ShortComplex.mk (X₁ := sigmaSupportedCoherent i _ h₁) (X₂ := sigmaSupportedCoherent i _ h₂)
      (X₃ := sigmaSupportedCoherent i _ h₃)
      (ObjectProperty.homMk (ObjectProperty.homMk (Limits.Sigma.map fun n => (S n).f)))
      (ObjectProperty.homMk (ObjectProperty.homMk (Limits.Sigma.map fun n => (S n).g)))
      (by apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; exact hzero)
  exact KZero.mk_of_shortExact T
    (Stacks.Chow.shortExact_of_shortExact_map_ι _ (Stacks.Chow.shortExact_of_shortExact_map_ι _ hT))

/-- Reindexing a locally finite family along a bijection of `ℤ` does not change the class of its
direct sum. -/
theorem mk_sigmaSupportedCoherent_congr (F G : ℤ → OXMod.{u, u} X.toRingedSpace)
    (hF : IsLocallyFiniteSupportedFamily i F) (hG : IsLocallyFiniteSupportedFamily i G)
    (e : ℤ ≃ ℤ) (w : ∀ k, G (e k) ≅ F k) :
    KZero.mk _ (sigmaSupportedCoherent i F hF) = KZero.mk _ (sigmaSupportedCoherent i G hG) :=
  KZero.mk_eq_of_iso (ObjectProperty.isoMk _ (ObjectProperty.isoMk _ (Sigma.whiskerEquiv e w)))

omit [IsClosedImmersion i] [IsLocallyNoetherian X] in
/-- The kernels of a family of maps out of a locally finite family into coherent modules form a
locally finite family. -/
theorem isLocallyFiniteSupportedFamily_kernel (G W : ℤ → OXMod.{u, u} X.toRingedSpace)
    (hG : IsLocallyFiniteSupportedFamily i G) (hW : ∀ n, (W n).IsCoherent)
    (φ : ∀ n, G n ⟶ W n) : IsLocallyFiniteSupportedFamily i fun n => kernel (φ n) := by
  have hsupp : ∀ n, SheafOfModules.supp (kernel (φ n)) ⊆ SheafOfModules.supp (G n) := fun n => by
    have hm : Mono (C := OXMod.{u, u} X.toRingedSpace) (kernel.ι (φ n)) := inferInstance
    exact Stacks.AlgebraicGeometry.Tag01YHTopIdeals.supp_subset_of_mono (X := X)
      (kernel.ι (φ n)) ⟨fun g h hgh => hm.right_cancellation g h hgh⟩
  exact ⟨fun n => ObjectProperty.prop_kernel (fun M : OXMod.{u, u} X.toRingedSpace => M.IsCoherent)
    (φ n) (hG.1 n) (hW n), fun n => (hsupp n).trans (hG.2.1 n), hG.2.2.subset hsupp⟩

/-- For an exact sequence `A → B → C` in each degree, of locally finite families, the class of
`⊕ A` is the sum of the classes of `⊕ ker(A → B)` and `⊕ ker(B → C)`. -/
theorem mk_sigmaSupportedCoherent_eq_of_exact
    (S : ℤ → ShortComplex (OXMod.{u, u} X.toRingedSpace)) (hS : ∀ n, (S n).Exact)
    (h₁ : IsLocallyFiniteSupportedFamily i fun n => (S n).X₁)
    (h₂ : IsLocallyFiniteSupportedFamily i fun n => (S n).X₂)
    (h₃ : ∀ n, ((S n).X₃).IsCoherent) :
    KZero.mk _ (sigmaSupportedCoherent i _ h₁) =
      KZero.mk _ (sigmaSupportedCoherent i (fun n => kernel (S n).f)
        (isLocallyFiniteSupportedFamily_kernel i _ _ h₁ h₂.1 _)) +
      KZero.mk _ (sigmaSupportedCoherent i (fun n => kernel (S n).g)
        (isLocallyFiniteSupportedFamily_kernel i _ _ h₂ h₃ _)) :=
  mk_sigmaSupportedCoherent_of_shortExact i
    (fun n => ShortComplex.kernelKernelSequence (S n))
    (fun n => ShortComplex.shortExact_kernelKernelSequence _ (hS n)) _ h₁ _

end Supported

section Main

open CategoryTheory.Pretriangulated DerivedCategory.HomologySequence

variable [HasDerivedCategory.{d} (OXMod.{u, u} X.toRingedSpace)]

/-- The cohomology sheaves of a perfect object of `D(𝒪_X)` have locally finite supports. -/
theorem locallyFinite_supp_homology (K : DerivedCategory (OXMod.{u, u} X.toRingedSpace))
    (hK : RingedSpace.IsPerfect (X := X.toRingedSpace) K) :
    LocallyFinite fun n : ℤ => SheafOfModules.supp
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) n).obj K) := by
  intro x
  obtain ⟨U, hxU, hfin⟩ :=
    Stacks.AlgebraicGeometry.PerfectCohomology.locally_finite_homology X K hK x
  exact ⟨U, U.isOpen.mem_nhds hxU, hfin.subset fun n ⟨y, hy, hyU⟩ => ⟨y, hyU, hy⟩⟩

variable {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]

/-- For `E` perfect and supported on `Z` and `p : ℤ → ℤ` injective, the cohomology sheaves
`H^{p n}(E)` form a locally finite family of coherent modules supported on `Z`. -/
theorem isLocallyFiniteSupportedFamily_homology (E : supportedPerfectDerivedCategory.{u, d} i)
    (p : ℤ → ℤ) (hp : Function.Injective p) :
    IsLocallyFiniteSupportedFamily i fun n =>
      (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) (p n)).obj E.obj :=
  ⟨fun n => Stacks.AlgebraicGeometry.PerfectCohomology.isCoherent_homology X E.obj
      E.property.1 (p n),
    fun n => E.property.2 (p n),
    (locallyFinite_supp_homology E.obj E.property.1).comp_injective hp⟩

/-- The class in `K_0(Coh_Z(X))` of `⊕_n H^{p n}(E)`. -/
def homologySumClass (E : supportedPerfectDerivedCategory.{u, d} i) (p : ℤ → ℤ)
    (hp : Function.Injective p) : KZero (SupportedCoherentModules i) :=
  KZero.mk _ (sigmaSupportedCoherent i _ (isLocallyFiniteSupportedFamily_homology i E p hp))

/-- The even degrees `n ↦ 2n` enumerate injectively. -/
theorem injective_two_mul : Function.Injective fun n : ℤ => 2 * n :=
  fun a b h => by simpa using h

/-- The odd degrees `n ↦ 2n + 1` enumerate injectively. -/
theorem injective_two_mul_add_one : Function.Injective fun n : ℤ => 2 * n + 1 :=
  fun a b h => by simpa using h

/-- The class of `⊕_n ker(H^{q n}(E₁) → H^{q n}(E₂))` for a triangle `E₁ → E₂ → E₃ → E₁[1]`. -/
def kernelOneClass (T : Triangle (supportedPerfectDerivedCategory.{u, d} i)) (q : ℤ → ℤ)
    (hq : Function.Injective q) : KZero (SupportedCoherentModules i) :=
  KZero.mk _ (sigmaSupportedCoherent i (fun n => kernel
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) (q n)).map
      ((ObjectProperty.ι _).mapTriangle.obj T).mor₁))
    (isLocallyFiniteSupportedFamily_kernel i _ _
      (isLocallyFiniteSupportedFamily_homology i T.obj₁ _ hq)
      (isLocallyFiniteSupportedFamily_homology i T.obj₂ _ hq).1 _))

/-- The class of `⊕_n ker(H^{q n}(E₂) → H^{q n}(E₃))` for a triangle `E₁ → E₂ → E₃ → E₁[1]`. -/
def kernelTwoClass (T : Triangle (supportedPerfectDerivedCategory.{u, d} i)) (q : ℤ → ℤ)
    (hq : Function.Injective q) : KZero (SupportedCoherentModules i) :=
  KZero.mk _ (sigmaSupportedCoherent i (fun n => kernel
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) (q n)).map
      ((ObjectProperty.ι _).mapTriangle.obj T).mor₂))
    (isLocallyFiniteSupportedFamily_kernel i _ _
      (isLocallyFiniteSupportedFamily_homology i T.obj₂ _ hq)
      (isLocallyFiniteSupportedFamily_homology i T.obj₃ _ hq).1 _))

/-- The class of `⊕_n ker(H^{q n}(E₃) → H^{q n + 1}(E₁))` for a triangle
`E₁ → E₂ → E₃ → E₁[1]`. -/
def kernelDeltaClass (T : Triangle (supportedPerfectDerivedCategory.{u, d} i)) (q : ℤ → ℤ)
    (hq : Function.Injective q) (hq' : Function.Injective fun n => q n + 1) :
    KZero (SupportedCoherentModules i) :=
  KZero.mk _ (sigmaSupportedCoherent i (fun n => kernel
    (δ ((ObjectProperty.ι _).mapTriangle.obj T) (q n) (q n + 1) rfl))
    (isLocallyFiniteSupportedFamily_kernel i _ _
      (isLocallyFiniteSupportedFamily_homology i T.obj₃ _ hq)
      (isLocallyFiniteSupportedFamily_homology i T.obj₁ _ hq').1 _))

section Triangle

variable (T : Triangle (supportedPerfectDerivedCategory.{u, d} i)) (hT : T ∈ distTriang _)
  (q : ℤ → ℤ) (hq : Function.Injective q) (hq' : Function.Injective fun n => q n + 1)

include hT

/-- Exactness at `H^q(E₁)`:
`[⊕ H^q(E₁)] = [⊕ ker(H^q(E₁) → H^q(E₂))] + [⊕ ker(H^q(E₂) → H^q(E₃))]`. -/
theorem homologySumClass_obj₁ :
    homologySumClass i T.obj₁ q hq = kernelOneClass i T q hq + kernelTwoClass i T q hq := by
  have hT' := (ObjectProperty.ι _).map_distinguished T hT
  exact mk_sigmaSupportedCoherent_eq_of_exact i
    (fun n => ShortComplex.mk _ _ (by
      rw [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT', Functor.map_zero]))
    (fun n => exact₂ _ hT' (q n)) _ (isLocallyFiniteSupportedFamily_homology i T.obj₂ _ hq)
    (isLocallyFiniteSupportedFamily_homology i T.obj₃ _ hq).1

include hq' in
/-- Exactness at `H^q(E₂)`:
`[⊕ H^q(E₂)] = [⊕ ker(H^q(E₂) → H^q(E₃))] + [⊕ ker(H^q(E₃) → H^{q+1}(E₁))]`. -/
theorem homologySumClass_obj₂ :
    homologySumClass i T.obj₂ q hq = kernelTwoClass i T q hq + kernelDeltaClass i T q hq hq' := by
  have hT' := (ObjectProperty.ι _).map_distinguished T hT
  exact mk_sigmaSupportedCoherent_eq_of_exact i
    (fun n => ShortComplex.mk _ _ (comp_δ _ hT' (q n) (q n + 1) rfl))
    (fun n => exact₃ _ hT' (q n) (q n + 1) rfl) _
    (isLocallyFiniteSupportedFamily_homology i T.obj₃ _ hq)
    (isLocallyFiniteSupportedFamily_homology i T.obj₁ _ hq').1

/-- Exactness at `H^q(E₃)`:
`[⊕ H^q(E₃)] = [⊕ ker(H^q(E₃) → H^{q+1}(E₁))] + [⊕ ker(H^{q+1}(E₁) → H^{q+1}(E₂))]`. -/
theorem homologySumClass_obj₃ :
    homologySumClass i T.obj₃ q hq =
      kernelDeltaClass i T q hq hq' + kernelOneClass i T (fun n => q n + 1) hq' := by
  have hT' := (ObjectProperty.ι _).map_distinguished T hT
  exact mk_sigmaSupportedCoherent_eq_of_exact i
    (fun n => ShortComplex.mk _ _ (δ_comp _ hT' (q n) (q n + 1) rfl))
    (fun n => exact₁ _ hT' (q n) (q n + 1) rfl) _
    (isLocallyFiniteSupportedFamily_homology i T.obj₁ _ hq')
    (isLocallyFiniteSupportedFamily_homology i T.obj₂ _ hq').1

end Triangle

/-- The class `kernelOneClass` depends only on the set of degrees, not on its enumeration. -/
theorem kernelOneClass_reindex (T : Triangle (supportedPerfectDerivedCategory.{u, d} i))
    (q q' : ℤ → ℤ) (hq : Function.Injective q) (hq' : Function.Injective q') (e : ℤ ≃ ℤ)
    (h : ∀ k, q' (e k) = q k) : kernelOneClass i T q hq = kernelOneClass i T q' hq' :=
  mk_sigmaSupportedCoherent_congr i _ _ _ _ e fun k =>
    eqToIso (congrArg (fun m => kernel
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) m).map
        ((ObjectProperty.ι _).mapTriangle.obj T).mor₁)) (h k))

/-- `⊕_{n ∈ ℤ} H^{2n}(E)` for `E` in `D_{Z, perf}(𝒪_X)`, as an object of `Coh_Z(X)`. -/
def evenHomologySupported (E : supportedPerfectDerivedCategory.{u, d} i) :
    SupportedCoherentModules i :=
  sigmaSupportedCoherent i _ (isLocallyFiniteSupportedFamily_homology i E _ injective_two_mul)

/-- `⊕_{n ∈ ℤ} H^{2n + 1}(E)` for `E` in `D_{Z, perf}(𝒪_X)`, as an object of `Coh_Z(X)`. -/
def oddHomologySupported (E : supportedPerfectDerivedCategory.{u, d} i) :
    SupportedCoherentModules i :=
  sigmaSupportedCoherent i _
    (isLocallyFiniteSupportedFamily_homology i E _ injective_two_mul_add_one)

/-- The underlying `𝒪_X`-module of `evenHomologySupported i E` is `⊕_{n ∈ ℤ} H^{2n}(E)`, the
coproduct in the category of `𝒪_X`-modules. -/
@[simp]
theorem evenHomologySupported_obj_obj (E : supportedPerfectDerivedCategory.{u, d} i) :
    (evenHomologySupported i E).obj.obj =
      ∐ fun n : ℤ => (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) (2 * n)).obj
        E.obj :=
  rfl

/-- The underlying `𝒪_X`-module of `oddHomologySupported i E` is `⊕_{n ∈ ℤ} H^{2n + 1}(E)`, the
coproduct in the category of `𝒪_X`-modules. -/
@[simp]
theorem oddHomologySupported_obj_obj (E : supportedPerfectDerivedCategory.{u, d} i) :
    (oddHomologySupported i E).obj.obj =
      ∐ fun n : ℤ =>
        (DerivedCategory.homologyFunctor (OXMod.{u, u} X.toRingedSpace) (2 * n + 1)).obj E.obj :=
  rfl

/-- The element `[⊕_n H^{2n}(E)] - [⊕_n H^{2n + 1}(E)]` of `K_0(Coh_Z(X))`. -/
def supportedPerfectParityClass (E : supportedPerfectDerivedCategory.{u, d} i) :
    KZero (SupportedCoherentModules i) :=
  KZero.mk _ (evenHomologySupported i E) - KZero.mk _ (oddHomologySupported i E)

/-- **The parity class is additive on distinguished triangles.** The long exact cohomology
sequence of a distinguished triangle in `D_{Z, perf}(𝒪_X)` splits into short exact sequences of
kernels, which stay short exact after summing over all even, respectively all odd, degrees. -/
theorem supportedPerfectParityClass_distinguished
    (T : Triangle (supportedPerfectDerivedCategory.{u, d} i)) (hT : T ∈ distTriang _) :
    supportedPerfectParityClass i T.obj₂ =
      supportedPerfectParityClass i T.obj₁ + supportedPerfectParityClass i T.obj₃ := by
  have he₁ : KZero.mk _ (evenHomologySupported i T.obj₁) =
      kernelOneClass i T _ injective_two_mul + kernelTwoClass i T _ injective_two_mul :=
    homologySumClass_obj₁ i T hT _ injective_two_mul
  have he₂ : KZero.mk _ (evenHomologySupported i T.obj₂) =
      kernelTwoClass i T _ injective_two_mul +
        kernelDeltaClass i T _ injective_two_mul injective_two_mul_add_one :=
    homologySumClass_obj₂ i T hT _ injective_two_mul injective_two_mul_add_one
  have he₃ : KZero.mk _ (evenHomologySupported i T.obj₃) =
      kernelDeltaClass i T _ injective_two_mul injective_two_mul_add_one +
        kernelOneClass i T _ injective_two_mul_add_one :=
    homologySumClass_obj₃ i T hT _ injective_two_mul injective_two_mul_add_one
  have ho' : Function.Injective fun n : ℤ => 2 * n + 1 + 1 := fun a b h => by simpa using h
  have ho₁ : KZero.mk _ (oddHomologySupported i T.obj₁) =
      kernelOneClass i T _ injective_two_mul_add_one +
        kernelTwoClass i T _ injective_two_mul_add_one :=
    homologySumClass_obj₁ i T hT _ injective_two_mul_add_one
  have ho₂ : KZero.mk _ (oddHomologySupported i T.obj₂) =
      kernelTwoClass i T _ injective_two_mul_add_one +
        kernelDeltaClass i T _ injective_two_mul_add_one ho' :=
    homologySumClass_obj₂ i T hT _ injective_two_mul_add_one ho'
  have ho₃ : KZero.mk _ (oddHomologySupported i T.obj₃) =
      kernelDeltaClass i T _ injective_two_mul_add_one ho' +
        kernelOneClass i T _ ho' :=
    homologySumClass_obj₃ i T hT _ injective_two_mul_add_one ho'
  have hshift : kernelOneClass i T (fun n : ℤ => 2 * n + 1 + 1) ho' =
      kernelOneClass i T _ injective_two_mul :=
    kernelOneClass_reindex i T _ _ ho' injective_two_mul (Equiv.addRight 1) fun k => by
      simp only [Equiv.coe_addRight]
      ring
  unfold supportedPerfectParityClass
  rw [he₁, he₂, he₃, ho₁, ho₂, ho₃, hshift]
  abel

end Main

end AlgebraicGeometry.SupportedPerfectCohomology

namespace AlgebraicGeometry

open CategoryTheory.Pretriangulated SupportedPerfectCohomology

universe d

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsLocallyNoetherian X]
  [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)]

/-- **The homomorphism `K_0(D_{Z, perf}(𝒪_X)) → K_0(Coh_Z(X))` of [Stacks, Tag 0FEP].**
Let `X` be a locally Noetherian scheme and `Z ⊂ X` a closed subscheme. The rule
`E ↦ [⊕_{i ∈ ℤ} H^{2i}(E)] - [⊕_{i ∈ ℤ} H^{2i + 1}(E)]` is additive on distinguished triangles of
`D_{Z, perf}(𝒪_X)`, hence defines a homomorphism of groups; its value on the class of `E` is
`supportedPerfectCohomologyHom_cls`. -/
@[stacks 0FEP "the homomorphism K_0(D_{Z, perf}(O_X)) → K_0(Coh_Z(X)) for X locally Noetherian \
and Z ⊂ X a closed subscheme; its defining property is `supportedPerfectCohomologyHom_cls`"]
def supportedPerfectCohomologyHom :
    Pretriangulated.K0 (supportedPerfectDerivedCategory.{u, d} i) →+
      KZero (SupportedCoherentModules i) :=
  QuotientAddGroup.lift _ (FreeAbelianGroup.lift (supportedPerfectParityClass i)) fun x hx => by
    refine (AddSubgroup.closure_le
      (K := (FreeAbelianGroup.lift (supportedPerfectParityClass i)).ker)).2 ?_ hx
    rintro _ ⟨T, hT, rfl⟩
    rw [SetLike.mem_coe, AddMonoidHom.mem_ker, map_sub, map_sub, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of,
      supportedPerfectParityClass_distinguished i T hT]
    abel

/-- **The defining property of the homomorphism of [Stacks, Tag 0FEP].** The class of a perfect
complex `E` with cohomology sheaves supported on `Z` is sent to
`[⊕_{i ∈ ℤ} H^{2i}(E)] - [⊕_{i ∈ ℤ} H^{2i + 1}(E)]`, the direct sums being taken in the category
of `𝒪_X`-modules (`evenHomologySupported_obj_obj`, `oddHomologySupported_obj_obj`). -/
@[stacks 0FEP "the defining property: [E] ↦ [⊕_{i ∈ ℤ} H^{2i}(E)] - [⊕_{i ∈ ℤ} H^{2i+1}(E)], the \
direct sums taken in Mod(O_X)"]
theorem supportedPerfectCohomologyHom_cls (E : supportedPerfectDerivedCategory.{u, d} i) :
    supportedPerfectCohomologyHom i (Pretriangulated.K0.cls E) =
      KZero.mk _ (evenHomologySupported i E) - KZero.mk _ (oddHomologySupported i E) :=
  FreeAbelianGroup.lift_apply_of _ _

/-- **The homomorphism of [Stacks, Tag 0FEP] with target `K'_0(Z) = K_0(Coh(𝒪_Z))`**, through
the identification `K_0(Coh(𝒪_Z)) ≅ K_0(Coh_Z(X))` of [Stacks, Tag 0FDT]. -/
@[stacks 0FEP "the same homomorphism with target K'_0(Z) = K_0(Coh(Z)), through the identification \
K_0(Coh_Z(X)) = K'_0(Z) of Stacks 0FDT"]
def supportedPerfectCohomologyHomToCoherent :
    Pretriangulated.K0 (supportedPerfectDerivedCategory.{u, d} i) →+
      KZero (Stacks.SheafOfModules.CoherentModules Z.ringCatSheaf) :=
  (coherentToSupportedCoherentKZeroEquiv i).symm.toAddMonoidHom.comp
    (supportedPerfectCohomologyHom i)

/-- Composed with the isomorphism `K'_0(Z) ≅ K_0(Coh_Z(X))` of [Stacks, Tag 0FDT], the
homomorphism into `K'_0(Z)` is the homomorphism into `K_0(Coh_Z(X))`. -/
theorem coherentToSupportedCoherentKZeroEquiv_supportedPerfectCohomologyHomToCoherent
    (x : Pretriangulated.K0 (supportedPerfectDerivedCategory.{u, d} i)) :
    coherentToSupportedCoherentKZeroEquiv i (supportedPerfectCohomologyHomToCoherent i x) =
      supportedPerfectCohomologyHom i x :=
  (coherentToSupportedCoherentKZeroEquiv i).apply_symm_apply _

/-! ### `D_{Z, perf}(𝒪_X)` is strictly full, saturated and triangulated -/

section Saturated

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
  [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)]

/-- **`D_{Z, perf}(𝒪_X)` is stable under retracts.** A retract `M` of a perfect complex `K` is
perfect, by [Stacks, Tag 08CS]; and `H^n(M)` is a direct summand of `H^n(K)`, so its support is
contained in that of `H^n(K)`. -/
instance isStableUnderRetracts_supportedPerfect :
    ObjectProperty.IsStableUnderRetracts
      (show ObjectProperty (DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)) from
        fun K => RingedSpace.IsPerfect K ∧
          ∀ n : ℤ, SheafOfModules.supp
            ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)
              n).obj K) ⊆ Set.range i.base) where
  of_retract {M K} h hK := by
    let : ∀ V : TopologicalSpace.Opens X.carrier, HasDerivedCategory.{u + 1}
        (StrictlyPerfect.OXMod.{u, u} (X.toRingedSpace.restrict V.isOpenEmbedding)) :=
      fun _ => HasDerivedCategory.standard _
    refine ⟨(RingedSpace.isPerfect_iff_perfectComplexes_isPerfect M).mpr
      (Stacks.Cohomology.PerfectDirectSummands.isPerfect_of_retract h.i h.r h.retract
        ((RingedSpace.isPerfect_iff_perfectComplexes_isPerfect K).mp hK.1)), fun n => ?_⟩
    let H := DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) n
    have hm : Mono (H.map h.i) := inferInstance
    exact (Stacks.AlgebraicGeometry.Tag01YHTopIdeals.supp_subset_of_mono (X := X)
      (H.map h.i) ⟨fun g k hgk => hm.right_cancellation g k hgk⟩).trans (hK.2 n)

/-- **`D_{Z, perf}(𝒪_X)` is a strictly full, saturated, triangulated subcategory of
`D(𝒪_X)`.** The perfect complexes of `𝒪_X`-modules whose cohomology sheaves are set-theoretically
supported on `Z` form a property of objects which is closed under isomorphisms, triangulated, and
stable under retracts, hence saturated (closed under direct summands). -/
@[stacks 0FEP "D_{Z, perf}(O_X) is a strictly full, saturated, triangulated subcategory of \
D(O_X): closed under isomorphisms, triangulated, stable under retracts, hence saturated",
  sga "6 I 5.8.4" "5.8.4 a), special case"]
theorem supportedPerfect_isStrictlyFull_isTriangulated_isSaturated :
    let P : ObjectProperty (DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)) :=
      fun K => RingedSpace.IsPerfect K ∧
        ∀ n : ℤ, SheafOfModules.supp
          ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace)
            n).obj K) ⊆ Set.range i.base
    P.IsClosedUnderIsomorphisms ∧ P.IsTriangulated ∧ P.IsStableUnderRetracts ∧
      P.IsSaturated :=
  ⟨isClosedUnderIsomorphisms_supportedPerfect i, isTriangulated_supportedPerfect i,
    isStableUnderRetracts_supportedPerfect i,
    ObjectProperty.IsSaturated.of_isStableUnderRetracts _⟩

end Saturated

end AlgebraicGeometry
