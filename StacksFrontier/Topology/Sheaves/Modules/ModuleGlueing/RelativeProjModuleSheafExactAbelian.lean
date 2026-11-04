module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LeftGradedModuleAbelian
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderCokernels
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderKernels
public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.RelativeProjModuleSheafExactFunctor

/-!
# The construction `ℳ ↦ ℳ̃` on a relative projective spectrum is an exact functor

Let `s` be a relative `Proj` situation. The quasi-coherent graded modules over its graded
algebra `𝒜` — the graded modules all of whose homogeneous pieces are quasi-coherent — form an
abelian category, a full subcategory of the left graded `𝒜`-modules closed under kernels,
cokernels and finite products. The functor `ℳ ↦ ℳ̃` of property (4) of [Stacks, Tag 01O7] from
that abelian category to the modules on `Proj_S(𝒜)` is exact: it is additive and preserves finite
limits and finite colimits, equivalently it carries short exact sequences to short exact
sequences. This is property (5) of the tag.

## Main results

* `Stacks.RelativeProj.Situation.qcohGradedModule_abelian`: the quasi-coherent graded modules
  form an abelian category, a full subcategory of the left graded modules closed under kernels,
  cokernels and finite products.
* `Stacks.RelativeProj.Situation.shortExact_degreewise`: a short exact sequence of quasi-coherent
  graded modules is short exact in every degree.
* `Stacks.RelativeProj.Situation.moduleSheafFunctor_exact`: the functor `ℳ ↦ ℳ̃` is exact.

## References

* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.SheafOfModules
open ZeroObject

universe u

namespace Stacks.AlgebraicGeometry.QuasicoherentColimits

/-- The point of a limit cone over a pair of quasi-coherent modules is quasi-coherent. -/
theorem isQuasicoherent_of_isLimit_pair {X : Scheme.{u}} {D : Discrete WalkingPair ⥤ X.Modules}
    (hD : ∀ j, (D.obj j).IsQuasicoherent) {c : Cone D} (hc : IsLimit c) :
    c.pt.IsQuasicoherent := by
  have hb := binaryBiconeIsBilimitOfLimitConeOfIsLimit
    ((IsLimit.postcomposeHomEquiv (diagramIsoPair D) c).symm hc)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_isColimit hb.isColimit
    (by rintro ⟨_ | _⟩ <;> exact hD _)

end Stacks.AlgebraicGeometry.QuasicoherentColimits

namespace Stacks.RelativeProj.Situation

variable (s : Situation.{u})

/-! ### The abelian category of quasi-coherent graded modules -/

/-- The property of a graded module over the graded algebra of a relative `Proj` situation that
all its homogeneous pieces are quasi-coherent. -/
abbrev qcohGradedProperty :
    ObjectProperty (SheafOfModules.LeftGradedModule.{u, u, u, u, u} s.algebra) :=
  fun ℳ => ∀ n : ℤ, (ℳ.piece n).IsQuasicoherent

/-- The property that all homogeneous pieces are quasi-coherent is stable under isomorphism. -/
instance qcohGradedProperty_isClosedUnderIsomorphisms :
    (qcohGradedProperty s).IsClosedUnderIsomorphisms where
  of_iso e h n := (SheafOfModules.isQuasicoherent s.base.ringCatSheaf).prop_of_iso
    ((SheafOfModules.LeftGradedModule.pieceFunctor s.algebra n).mapIso e) (h n)

/-- Some zero graded module has all its homogeneous pieces quasi-coherent. -/
instance qcohGradedProperty_containsZero : (qcohGradedProperty s).ContainsZero where
  exists_zero := by
    have : (SheafOfModules.isQuasicoherent s.base.ringCatSheaf).ContainsZero :=
      ⟨SheafOfModules.free (R := s.base.ringCatSheaf) (PEmpty : Type u),
        (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun n => n.elim), inferInstance⟩
    exact ⟨0, isZero_zero _, fun n =>
      (SheafOfModules.isQuasicoherent s.base.ringCatSheaf).prop_of_isZero
        ((SheafOfModules.LeftGradedModule.pieceFunctor s.algebra n).map_isZero (isZero_zero _))⟩

/-- A kernel of a homomorphism of quasi-coherent graded modules is quasi-coherent. -/
instance qcohGradedProperty_isClosedUnderKernels :
    (qcohGradedProperty s).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩ n
    exact (SheafOfModules.isQuasicoherent s.base.ringCatSheaf).prop_of_isLimit_kernelFork
      (KernelFork.mapIsLimit k hk (SheafOfModules.LeftGradedModule.pieceFunctor s.algebra n))
      (hX n) (hY n)

/-- A cokernel of a homomorphism of quasi-coherent graded modules is quasi-coherent. -/
instance qcohGradedProperty_isClosedUnderCokernels :
    (qcohGradedProperty s).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩ n
    exact (SheafOfModules.isQuasicoherent s.base.ringCatSheaf).prop_of_isColimit_cokernelCofork
      (CokernelCofork.mapIsColimit k hk (SheafOfModules.LeftGradedModule.pieceFunctor s.algebra n))
      (hX n) (hY n)

/-- A product of two quasi-coherent graded modules is quasi-coherent. -/
instance qcohGradedProperty_isClosedUnderBinaryProducts :
    (qcohGradedProperty s).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro M ⟨h⟩ n
    exact Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_isLimit_pair
      (D := h.diag ⋙ SheafOfModules.LeftGradedModule.pieceFunctor s.algebra n)
      (fun j => h.prop_diag_obj j n)
      (isLimitOfPreserves (SheafOfModules.LeftGradedModule.pieceFunctor s.algebra n) h.isLimit)

/-- Quasi-coherent graded modules are closed under finite products. -/
instance qcohGradedProperty_isClosedUnderFiniteProducts :
    (qcohGradedProperty s).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- The quasi-coherent graded modules over the graded algebra of a relative `Proj` situation
form an abelian category, a full subcategory of the abelian category of left graded modules
closed under kernels, cokernels and finite products. -/
instance qcohGradedModule_abelian : Abelian (QcohGradedModule s) :=
  inferInstanceAs (Abelian (qcohGradedProperty s).FullSubcategory)

/-- The inclusion of the quasi-coherent graded modules into all graded modules preserves finite
limits. -/
instance preservesFiniteLimits_qcohGradedProperty_ι :
    PreservesFiniteLimits (qcohGradedProperty s).ι :=
  have := (qcohGradedProperty s).preservesKernels_ι
  have : HasEqualizers (QcohGradedModule s) := Preadditive.hasEqualizers_of_hasKernels
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- The inclusion of the quasi-coherent graded modules into all graded modules preserves finite
colimits. -/
instance preservesFiniteColimits_qcohGradedProperty_ι :
    PreservesFiniteColimits (qcohGradedProperty s).ι :=
  have := (qcohGradedProperty s).preservesCokernels_ι
  have : HasCoequalizers (QcohGradedModule s) := Preadditive.hasCoequalizers_of_hasCokernels
  Functor.preservesFiniteColimits_of_preservesCokernels _

variable {s}

/-- A short exact sequence of quasi-coherent graded modules is short exact in every degree. -/
theorem shortExact_degreewise {S : ShortComplex (QcohGradedModule s)} (hS : S.ShortExact) :
    SheafOfModules.LeftGradedModule.ShortExact S.f.hom S.g.hom
      (fun n => congrArg (fun φ : S.X₁ ⟶ S.X₃ => φ.hom.app n) S.zero) := fun n =>
  hS.map_of_exact
    ((qcohGradedProperty s).ι ⋙ SheafOfModules.LeftGradedModule.pieceFunctor s.algebra n)

/-! ### Exactness of `ℳ ↦ ℳ̃` -/

/-- `ℳ ↦ ℳ̃` carries a short exact sequence of quasi-coherent graded modules to a short exact
sequence of modules on the relative projective spectrum; the vanishing of the composite of the
images is part of the conclusion. -/
theorem exists_shortExact_moduleSheafFunctor_map (S : ShortComplex (QcohGradedModule s))
    (hS : S.ShortExact) :
    ∃ w, (ShortComplex.mk ((moduleSheafFunctor s).map S.f) ((moduleSheafFunctor s).map S.g)
      w).ShortExact := by
  have : ∀ n : ℤ, (S.X₁.obj.piece n).IsQuasicoherent := S.X₁.property
  have : ∀ n : ℤ, (S.X₂.obj.piece n).IsQuasicoherent := S.X₂.property
  have : ∀ n : ℤ, (S.X₃.obj.piece n).IsQuasicoherent := S.X₃.property
  exact ⟨_, shortExact_moduleSheafMap_of_shortExact S.f.hom S.g.hom _ (shortExact_degreewise hS)⟩

variable (s) in
/-- `ℳ ↦ ℳ̃` takes the zero graded module to a zero module. -/
theorem isZero_moduleSheafFunctor_obj_zero : IsZero ((moduleSheafFunctor s).obj 0) := by
  let S0 : ShortComplex (QcohGradedModule s) :=
    ShortComplex.mk (𝟙 0) (𝟙 0) ((isZero_zero _).eq_of_src _ _)
  have h0 : S0.ShortExact := { exact := ShortComplex.exact_of_isZero_X₂ _ (isZero_zero _) }
  obtain ⟨w, -⟩ := exists_shortExact_moduleSheafFunctor_map S0 h0
  have w' : (moduleSheafFunctor s).map (𝟙 0) ≫ (moduleSheafFunctor s).map (𝟙 0) = 0 := w
  rw [CategoryTheory.Functor.map_id, Category.comp_id] at w'
  exact (IsZero.iff_id_eq_zero _).2 w'

variable (s) in
/-- `ℳ ↦ ℳ̃` preserves zero morphisms. -/
instance moduleSheafFunctor_preservesZeroMorphisms :
    (moduleSheafFunctor s).PreservesZeroMorphisms :=
  Functor.preservesZeroMorphisms_of_map_zero_object
    (isZero_moduleSheafFunctor_obj_zero s).isoZero

/-- `ℳ ↦ ℳ̃` carries a short exact sequence of quasi-coherent graded modules to a short exact
sequence of modules on the relative projective spectrum. -/
theorem moduleSheafFunctor_map_shortExact (S : ShortComplex (QcohGradedModule s))
    (hS : S.ShortExact) : (S.map (moduleSheafFunctor s)).ShortExact :=
  (exists_shortExact_moduleSheafFunctor_map S hS).choose_spec

variable (s) in
/-- `ℳ ↦ ℳ̃` preserves binary biproducts. -/
instance moduleSheafFunctor_preservesBinaryBiproducts :
    PreservesBinaryBiproducts (moduleSheafFunctor s) where
  preserves {X Y} := ⟨fun {b} hb => by
    let S : ShortComplex (QcohGradedModule s) := ShortComplex.mk b.inl b.snd b.inl_snd
    let σ : S.Splitting :=
      { r := b.fst
        s := b.inr
        f_r := b.inl_fst
        s_g := b.inr_snd
        id := IsBilimit.binary_total hb }
    exact ⟨BinaryBicone.isBilimitOfKernelInl _
      (moduleSheafFunctor_map_shortExact S σ.shortExact).fIsKernel⟩⟩

variable (s) in
/-- `ℳ ↦ ℳ̃` is an additive functor. -/
instance moduleSheafFunctor_additive : (moduleSheafFunctor s).Additive :=
  Functor.additive_of_preservesBinaryBiproducts _

variable (s) in
/-- The functor `Stacks.RelativeProj.Situation.moduleSheafFunctor`, from the abelian category of
quasi-coherent graded modules over the graded algebra `𝒜` of the situation to the modules on the
relative projective spectrum `Proj_S(𝒜)`, is additive, preserves finite limits and preserves
finite colimits; equivalently, it carries short exact sequences of quasi-coherent graded modules
to short exact sequences of modules on `Proj_S(𝒜)`. -/
@[stacks 01O7 "property (5): the construction ℳ ↦ ℳ̃ is an exact functor from the abelian
category of quasi-coherent graded modules over 𝒜 to modules on the relative projective spectrum",
  ega "II 8.14.1" "partial"]
public theorem moduleSheafFunctor_exact :
    (moduleSheafFunctor s).Additive ∧ PreservesFiniteLimits (moduleSheafFunctor s) ∧
      PreservesFiniteColimits (moduleSheafFunctor s) ∧
      ∀ S : ShortComplex (QcohGradedModule s), S.ShortExact →
        (S.map (moduleSheafFunctor s)).ShortExact :=
  have h : PreservesFiniteLimits (moduleSheafFunctor s) ∧
      PreservesFiniteColimits (moduleSheafFunctor s) :=
    ((Functor.exact_tfae (moduleSheafFunctor s)).out 1 4).1
    moduleSheafFunctor_map_shortExact
  ⟨inferInstance, h.1, h.2, moduleSheafFunctor_map_shortExact⟩

/-- `ℳ ↦ ℳ̃` preserves finite limits. -/
instance moduleSheafFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (moduleSheafFunctor s) :=
  (moduleSheafFunctor_exact s).2.1

/-- `ℳ ↦ ℳ̃` preserves finite colimits. -/
instance moduleSheafFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (moduleSheafFunctor s) :=
  (moduleSheafFunctor_exact s).2.2.1

end Stacks.RelativeProj.Situation

end
