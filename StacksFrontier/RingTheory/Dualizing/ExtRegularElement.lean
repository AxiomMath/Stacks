module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Triangulated.Yoneda
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Category
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Algebra.Homology.InjectiveDimension.Noetherian
public import StacksFrontier.RingTheory.Depth.Criteria
public import StacksFrontier.RingTheory.Dualizing.Complex

import all StacksFrontier.Algebra.Homology.InjectiveDimension.Noetherian
import all StacksFrontier.RingTheory.Dualizing.Complex

/-!
# Ext groups across a regular element

For a finite module over a Noetherian local ring, quotienting by an element of the
maximal ideal which is a nonzerodivisor lowers both dimension and depth by one.
Applying derived Hom gives the associated long exact sequence of Ext groups.
The quotient of an Ext group by that element embeds in the following Ext group
of the quotient module. For Ext into a dualizing complex, this quotient lowers
support dimension by at most one.

## Main definitions

* `Dualizing.moduleExtInto` denotes integer-graded Ext from a module into a
  derived object.
* `Dualizing.extFromQuotient` and `Dualizing.extConnecting` are the maps in
  the long exact sequence.
* `Dualizing.quotientExtEmbedding` is the embedding induced by the boundary.

## Main results

* `Module.supportDim_quotSMulTop_succ_eq_supportDim` gives the dimension drop.
* `Module.depth_quotSMulTop_succ_eq_depth_and_exists_isRegular_append` gives the
  depth drop in its first assertion.
* `Dualizing.exact_extConnecting_extFromQuotient`,
  `Dualizing.exact_extFromQuotient_lsmul`, and
  `Dualizing.exact_lsmul_extConnecting` give the long exact Ext sequence.
* `Dualizing.supportDim_ext_quotient_add_one` gives the dimension inequality
  for a nonzero Ext group.

## Implementation notes

The dimension and depth equalities are supplied directly by the imported results
listed above, without restating them. They use `+ 1` on the quotient side, the
subtraction-free form appropriate for `WithBot ℕ∞` and `ℕ∞`.
The long exact sequence is expressed by its three recurring exactness conditions,
with the maps specified by the quotient map and the boundary of its short exact
sequence. The embedding is required to be induced by this same boundary.
Normalization is unnecessary: the long exact sequence and embedding hold for an
arbitrary target in the derived category, and only the last inequality requires
a dualizing complex. Nonvanishing of the original module is unnecessary in these
forms.

The smallness of the base ring forced by the existence of a dualizing complex, and
the finiteness of `Ext` from a finite module into a bounded-below object with finite
cohomology, are already available in this library as
`Dualizing.small_base_from_dualizing` and
`StacksDraft.InjectiveDimension.finite_ext_of_isGE`; both are `private`, so they are
reached through `import all` rather than restated here.

## References

* [Stacks Project, proof of Lemma 0A7U](https://stacks.math.columbia.edu/tag/0A7U)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated Pretriangulated.Opposite DerivedCategory
open Pointwise

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Dualizing

/-- The integer-graded Ext group from an `A`-module `M` into a derived object `K`. -/
noncomputable abbrev moduleExtInto {A : Type u} [CommRing A]
    (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (i : ℤ) :=
  DerivedCategory.Ext
    ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj (ModuleCat.of A M)) K i

/-- The map on Ext induced contravariantly by the quotient `M → M/fM`. -/
@[simps]
noncomputable def extFromQuotient
    {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (i : ℤ) :
    moduleExtInto (QuotSMulTop f M) K i →ₗ[A] moduleExtInto M K i where
  toFun x := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).map
    (ModuleCat.ofHom (f • (⊤ : Submodule A M)).mkQ) ≫ x
  map_add' := by intros; simp
  map_smul' := by intros; simp

/-- The connecting map obtained by applying derived Hom to
`0 → M → M → M/fM → 0`, whose first map is multiplication by `f`. -/
noncomputable def extConnecting
    {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (hreg : IsSMulRegular M f) (i : ℤ) :
    moduleExtInto M K i →ₗ[A] moduleExtInto (QuotSMulTop f M) K (i + 1) :=
  (Linear.leftComp A _
    (hreg.smulShortComplex_shortExact (M := ModuleCat.of A M)).singleTriangle.mor₃).comp
      ((Linear.rightComp A _
        ((shiftFunctorAdd' (DerivedCategory (ModuleCat.{v} A)) i 1 (i + 1) rfl).inv.app K)).comp
          ((shiftFunctor (DerivedCategory (ModuleCat.{v} A)) 1).mapLinearMap A))

/-- The boundary map embeds the cokernel of multiplication by `f` on an Ext
group in the next Ext group of the quotient module. The specification fixes
the embedding by its value on every quotient class. -/
noncomputable def quotientExtEmbedding
    {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (hreg : IsSMulRegular M f) (i : ℤ) :
    {ι : QuotSMulTop f (moduleExtInto M K i) →ₗ[A]
        moduleExtInto (QuotSMulTop f M) K (i + 1) //
      Function.Injective ι ∧
      (∀ x : moduleExtInto M K i,
        ι ((f • (⊤ : Submodule A (moduleExtInto M K i))).mkQ x) =
          extConnecting M K f hreg i x)} := by
  have hex : Function.Exact (LinearMap.lsmul A (moduleExtInto M K i) f)
      (extConnecting M K f hreg i) := by
    let S := hreg.smulShortComplex_shortExact (M := ModuleCat.of A M)
    let T := (Pretriangulated.triangleOpEquivalence _).functor.obj
      (Opposite.op S.singleTriangle)
    have hT : T ∈ distTriang _ :=
      Pretriangulated.op_distinguished _ S.singleTriangle_distinguished
    have h := (preadditiveYoneda.obj K).homologySequence_exact₃ T hT i (i + 1) rfl
    rw [ShortComplex.ab_exact_iff_function_exact] at h
    have hm : (fun x : moduleExtInto M K i => f • x) =
        ⇑(((preadditiveYoneda.obj K).shift i).map T.mor₂) := by
      funext x
      change f • x = T.mor₂.unop ≫ x
      rw [show T.mor₂.unop = S.singleTriangle.mor₁ by rfl]
      change f • x = (DerivedCategory.singleFunctor (ModuleCat A) 0).map
        (f • 𝟙 (ModuleCat.of A M)) ≫ x
      simp [Functor.map_smul, Linear.smul_comp]
    have hδ : ⇑(extConnecting M K f hreg i) =
        ⇑((preadditiveYoneda.obj K).homologySequenceδ T i (i + 1) rfl) := by
      change (fun x : ((preadditiveYoneda.obj K).shift i).obj T.obj₃ =>
          extConnecting M K f hreg i x) =
        fun x => ((preadditiveYoneda.obj K).homologySequenceδ T i (i + 1) rfl) x
      funext x
      symm
      change ((preadditiveYoneda.obj K).homologySequenceδ T i (i + 1) rfl) x =
        (extConnecting M K f hreg i) x
      rw [Pretriangulated.preadditiveYoneda_homologySequenceδ_apply
        (T := S.singleTriangle) i (i + 1) rfl x]
      rfl
    change Function.Exact (fun x : moduleExtInto M K i => f • x)
      (extConnecting M K f hreg i)
    rw [hm, hδ]
    exact h
  have hker : LinearMap.ker (extConnecting M K f hreg i) =
      f • (⊤ : Submodule A (moduleExtInto M K i)) := by
    rw [LinearMap.exact_iff.mp hex]
    ext x
    rw [Submodule.mem_smul_pointwise_iff_exists]
    simp [LinearMap.mem_range, LinearMap.lsmul_apply]
  exact ⟨Submodule.liftQ _ _ hker.ge,
    LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ hker.ge hker.le), fun _ => rfl⟩

/-- The opposite of the triangle of the short exact sequence `0 → M → M → M/fM → 0`. -/
private noncomputable abbrev opSingleTriangle
    {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M] (f : A)
    (hreg : IsSMulRegular M f) :=
  (Pretriangulated.triangleOpEquivalence _).functor.obj
    (Opposite.op (hreg.smulShortComplex_shortExact (M := ModuleCat.of A M)).singleTriangle)

private theorem opSingleTriangle_distinguished
    {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M] (f : A)
    (hreg : IsSMulRegular M f) : opSingleTriangle M f hreg ∈ distTriang _ :=
  Pretriangulated.op_distinguished _ (hreg.smulShortComplex_shortExact
    (M := ModuleCat.of A M)).singleTriangle_distinguished

/-- The boundary `extConnecting` is the connecting map of the Yoneda homology sequence. -/
private theorem coe_extConnecting_eq_homologySequenceδ
    {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (hreg : IsSMulRegular M f) (i : ℤ) :
    ⇑(extConnecting M K f hreg i) = ⇑((preadditiveYoneda.obj K).homologySequenceδ
      (opSingleTriangle M f hreg) i (i + 1) rfl) := by
  funext x
  exact (Pretriangulated.preadditiveYoneda_homologySequenceδ_apply
    (T := (hreg.smulShortComplex_shortExact (M := ModuleCat.of A M)).singleTriangle)
    i (i + 1) rfl x).symm

/-- Multiplication by `f` on Ext is induced by the second map of the opposite triangle. -/
private theorem smul_eq_map_opSingleTriangle_mor₂
    {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (hreg : IsSMulRegular M f) (i : ℤ) :
    (fun x : moduleExtInto M K i => f • x) =
      ⇑(((preadditiveYoneda.obj K).shift i).map (opSingleTriangle M f hreg).mor₂) := by
  funext x
  change f • x = (DerivedCategory.singleFunctor (ModuleCat A) 0).map
    (f • 𝟙 (ModuleCat.of A M)) ≫ x
  simp [Functor.map_smul, Linear.smul_comp]

/-- `extFromQuotient` is induced by the first map of the opposite triangle. -/
private theorem coe_extFromQuotient_eq_map_opSingleTriangle_mor₁
    {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (hreg : IsSMulRegular M f) (i : ℤ) :
    ⇑(extFromQuotient M K f i) =
      ⇑(((preadditiveYoneda.obj K).shift i).map (opSingleTriangle M f hreg).mor₁) := by
  funext x
  change (DerivedCategory.singleFunctor (ModuleCat A) 0).map
    (ModuleCat.ofHom (f • (⊤ : Submodule A M)).mkQ) ≫ x = (DerivedCategory.singleFunctor
      (ModuleCat A) 0).map (ModuleCat.smulShortComplex (ModuleCat.of A M) f).g ≫ x
  congr 1

/-- Exactness at the Ext group of `M/fM` in the long exact sequence. -/
theorem exact_extConnecting_extFromQuotient
    {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (hreg : IsSMulRegular M f) (i : ℤ) :
    Function.Exact (extConnecting M K f hreg i) (extFromQuotient M K f (i + 1)) := by
  have h := (preadditiveYoneda.obj K).homologySequence_exact₁ _
    (opSingleTriangle_distinguished M f hreg) i (i + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  rw [coe_extConnecting_eq_homologySequenceδ, coe_extFromQuotient_eq_map_opSingleTriangle_mor₁]
  exact h

/-- Exactness at the source of multiplication by `f` on Ext. -/
theorem exact_extFromQuotient_lsmul
    {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (hreg : IsSMulRegular M f) (i : ℤ) :
    Function.Exact (extFromQuotient M K f i)
      (LinearMap.lsmul A (moduleExtInto M K i) f) := by
  have h := (preadditiveYoneda.obj K).homologySequence_exact₂ _
    (opSingleTriangle_distinguished M f hreg) i
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  change Function.Exact (extFromQuotient M K f i) (fun x => f • x)
  rw [coe_extFromQuotient_eq_map_opSingleTriangle_mor₁, smul_eq_map_opSingleTriangle_mor₂]
  exact h

/-- Exactness at the target of multiplication by `f` on Ext. -/
theorem exact_lsmul_extConnecting
    {A : Type u} [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (f : A) (hreg : IsSMulRegular M f) (i : ℤ) :
    Function.Exact (LinearMap.lsmul A (moduleExtInto M K i) f)
      (extConnecting M K f hreg i) := by
  have h := (preadditiveYoneda.obj K).homologySequence_exact₃ _
    (opSingleTriangle_distinguished M f hreg) i (i + 1) rfl
  rw [ShortComplex.ab_exact_iff_function_exact] at h
  change Function.Exact (fun x : moduleExtInto M K i => f • x) (extConnecting M K f hreg i)
  rw [smul_eq_map_opSingleTriangle_mor₂, coe_extConnecting_eq_homologySequenceδ]
  exact h

/-- If an Ext group into a dualizing complex is nonzero, quotienting it by an
element of the maximal ideal lowers its support dimension by at most one. -/
theorem supportDim_ext_quotient_add_one
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDualizingComplex K)
    {f : A} (hf : f ∈ IsLocalRing.maximalIdeal A) (i : ℤ)
    [Nontrivial (moduleExtInto M K i)] :
    Module.supportDim A (moduleExtInto M K i) ≤
      Module.supportDim A (QuotSMulTop f (moduleExtInto M K i)) + 1 := by
  have : Module.Finite A (moduleExtInto M K i) := by
    have : Small.{v} A := small_base_from_dualizing K hK
    obtain ⟨a, b, ⟨J, hJGE, -, -, ⟨e⟩⟩⟩ := hK.finiteInjectiveDimension
    have : J.IsStrictlyGE a := hJGE
    have : K.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso e.symm a
    exact StacksDraft.InjectiveDimension.finite_ext_of_isGE (ModuleCat.of A M) K a
      hK.finiteCohomology i
  exact Module.supportDim_le_supportDim_quotSMulTop_succ hf

end Dualizing
