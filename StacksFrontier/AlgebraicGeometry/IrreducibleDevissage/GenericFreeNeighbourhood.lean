module

public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Coproduct
public import StacksFrontier.AlgebraicGeometry.CoherentKernel.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import Mathlib.AlgebraicGeometry.FunctionField
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A coherent module on an integral scheme is free near the generic point

The first step of the proof of [Stacks, Tag 01YE] is local freeness at the generic point: a
coherent module `G` on an integral, locally Noetherian scheme `Z` becomes a finite free module
after restriction to some open neighbourhood of the generic point `ξ`. The stalk `G_ξ` is a
finite module over `𝒪_{Z,ξ}`, that local ring is the function field of `Z` and therefore a
field, so `G_ξ` is a finite-dimensional vector space; [Stacks, Tag 0B8J] spreads a basis of it
out to a neighbourhood of `ξ`.

The conclusion is delivered as an isomorphism between objects of
`AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι`, which is the form in which the rest of
the dévissage consumes a generic triviality, rather than in the `SheafOfModules.over U` form
[Stacks, Tag 0B8J] produces.

## Main results

* `exists_isIso_restrictFunctor_free_near_genericPoint`, in the namespace
  `Stacks.AlgebraicGeometry.IrreducibleDevissage`: **a coherent module on an integral, locally
  Noetherian scheme is isomorphic to a finite free module on a neighbourhood of the generic
  point**, with the isomorphism stated after restriction along `U.ι`.
* `exists_isIso_restrictFunctor_free_near_genericPoint_of_isFinitePresentation`: the same for
  a module of finite presentation on an integral scheme, with no Noetherian hypothesis;
  coherence is used only through finite presentation.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.restrictFunctorIsoOfOverIso` and
  `Stacks.AlgebraicGeometry.IrreducibleDevissage.overIsoOfRestrictIso`: the two passages between
  a trivialisation of `G.over U` and a trivialisation of `G.restrict U.ι`. The two spellings of
  the restriction of a module to an open live in different categories, so neither statement is
  the other read differently; `AlgebraicGeometry.Scheme.Modules.overEquiv` is what relates them.
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_free_ulift`: **a finite free module
  on a locally Noetherian scheme is coherent**, from the coherence of the structure sheaf,
  [Stacks, Tag 01XZ].
* `Stacks.AlgebraicGeometry.IrreducibleDevissage.freeCoproductIso` and
  `freeCoproductIso_hom_ι`: the finite coproduct of `r` copies of the structure sheaf is the
  free module on `ULift (Fin r)`, with the computation of the isomorphism on each inclusion.

## Implementation notes

**The stalk of the structure sheaf is spelled twice, and the two spellings must be bridged.**
`SheafOfModules.finite_stalk` produces a module over `↑(Z.presheaf.stalk ξ)`, the filtered
colimit taken in `CommRingCat`, while [Stacks, Tag 0B8J] phrases its hypothesis over
`↑(TopCat.Presheaf.stalk Z.ringCatSheaf.obj ξ)`, the same colimit taken in `RingCat`. These are
different types. `SemilinearStalk.comm_smul_eq` says that the two actions on the stalk of the
module agree through `SemilinearStalk.commStalkRingEquiv`, and `module_finite_of_ringEquiv`
below is all that is then needed: finiteness only involves spans, and the two rings span the
same submodules.

**The field structure on the stalk is not installed as an instance until the last moment.**
Introducing `Field K` for `K` a `RingCat` stalk makes instance search for `Module K M` fail,
because the `Semiring K` it then looks through is the one derived from the field and not the one
carried by `RingCat`. `nonempty_linearEquiv_finsupp_of_isField` therefore takes `IsField` and
`Module.Finite` as ordinary arguments, with the module structure fixed by its binders, and
installs the field only inside its own proof.

**`freeCoproductIso` is proved over an abstract sheaf of rings.** Over `Z.ringCatSheaf` the
rewrites that drive the two triangle identities fail: `TopCat.Sheaf` is a `def`, so the
coproduct instances in the goal and in `CategoryTheory.Limits.Sigma.ι_desc` are not equal at the
transparency instance search uses. Stating the isomorphism for an arbitrary
`CategoryTheory.Sheaf J RingCat` removes the obstruction, and the scheme-level statement is then
an instance of it. For the same reason the construction stays inside the coproduct vocabulary
and never mentions `SheafOfModules.freeCofan`, whose point is `SheafOfModules.free I` only up to
unfolding.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace
open Opposite

universe u

namespace Stacks.AlgebraicGeometry.IrreducibleDevissage

variable {Z : Scheme.{u}}

/-! ### Transporting finiteness and a basis along a ring equivalence -/

/-- **Finiteness of a module transports along a ring equivalence that matches the two scalar
actions.** Only spans are involved: a `K`-submodule of `M` is an `L`-submodule of `M`, because
`l • m = e.symm l • m`, so the `L`-span of a finite set is contained in its `K`-span. -/
theorem module_finite_of_ringEquiv {K L M : Type*} [Ring K] [Ring L] [AddCommGroup M]
    [Module K M] [Module L M] (e : K ≃+* L) (he : ∀ (a : K) (m : M), e a • m = a • m)
    (h : Module.Finite L M) : Module.Finite K M := by
  obtain ⟨S, hS⟩ := h.1
  refine ⟨⟨S, le_antisymm le_top fun m _ => ?_⟩⟩
  have key : ∀ y : M, y ∈ Submodule.span L (↑S : Set M) → y ∈ Submodule.span K (↑S : Set M) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact Submodule.subset_span hz
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | smul l z _ hz =>
      rw [show l • z = e.symm l • z by rw [← he (e.symm l) z, e.apply_symm_apply]]
      exact Submodule.smul_mem _ _ hz
  exact key m (hS ▸ Submodule.mem_top)

/-- **A finite module over a ring which is a field is a finite free module**, in the form
[Stacks, Tag 0B8J] asks for its hypothesis: a linear equivalence with the finitely supported
functions on `ULift (Fin r)`. The field structure is installed only inside the proof; see the
implementation notes. -/
theorem nonempty_linearEquiv_finsupp_of_isField {K V : Type u} [Ring K] [AddCommGroup V]
    [Module K V] (hK : IsField K) (hV : Module.Finite K V) :
    ∃ r : ℕ, Nonempty (V ≃ₗ[K] (ULift.{u} (Fin r) →₀ K)) :=
  let : Field K := hK.toField
  ⟨Module.finrank K V, ⟨((Module.finBasis K V).reindex Equiv.ulift.symm).repr⟩⟩

/-! ### The stalk at the generic point of an integral scheme -/

/-- **The local ring of an integral scheme at its generic point is a field**: it is the function
field of the scheme. -/
@[ega "I 8.2.1" "partial", ega "IV 8.1.2" "partial"]
theorem isField_stalk_of_isGenericPoint [IsIntegral Z] (ξ : Z)
    (hξ : IsGenericPoint ξ (Set.univ : Set Z)) : IsField (Z.presheaf.stalk ξ) := by
  have : IrreducibleSpace Z := irreducibleSpace_of_isIntegral Z
  obtain rfl := hξ.eq (genericPoint_spec Z)
  exact Field.toIsField Z.functionField

/-- **The stalk of a module of finite type at the generic point of an integral scheme is a
finite-dimensional vector space**, in the shape [Stacks, Tag 0B8J] consumes: a linear
equivalence over the `RingCat`-valued stalk of the structure sheaf.

The stalk is a finite module over the `CommRingCat`-valued stalk by
`SheafOfModules.finite_stalk`, and that stalk is a field by
`isField_stalk_of_isGenericPoint`; both are carried across to the `RingCat`-valued stalk along
`SemilinearStalk.commStalkRingEquiv`. -/
theorem exists_nonempty_stalk_linearEquiv_finsupp_of_isGenericPoint [IsIntegral Z]
    (G : Z.Modules) [G.IsFiniteType] (ξ : Z) (hξ : IsGenericPoint ξ (Set.univ : Set Z)) :
    ∃ r : ℕ, Nonempty (ToType (TopCat.Presheaf.stalk G.val.presheaf ξ)
      ≃ₗ[ToType (TopCat.Presheaf.stalk Z.ringCatSheaf.obj ξ)]
        (ULift.{u} (Fin r) →₀ ToType (TopCat.Presheaf.stalk Z.ringCatSheaf.obj ξ))) := by
  let _ : Module (ToType (Z.presheaf.stalk ξ))
      (ToType (TopCat.Presheaf.stalk G.val.presheaf ξ)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Z.presheaf) G.val ξ
  have hfin : Module.Finite (ToType (TopCat.Presheaf.stalk Z.ringCatSheaf.obj ξ))
      (ToType (TopCat.Presheaf.stalk G.val.presheaf ξ)) :=
    module_finite_of_ringEquiv (SemilinearStalk.commStalkRingEquiv Z.presheaf ξ)
      (fun a m => SemilinearStalk.comm_smul_eq Z.presheaf ξ G.val a m)
      (_root_.SheafOfModules.finite_stalk Z.sheaf G ξ)
  exact nonempty_linearEquiv_finsupp_of_isField
    ((SemilinearStalk.commStalkRingEquiv Z.presheaf ξ).toMulEquiv.isField
      (isField_stalk_of_isGenericPoint ξ hξ)) hfin

/-- **[Stacks, Tag 0B8J] at the generic point of an integral scheme**: a module of finite
presentation on an integral scheme is isomorphic, after restriction to some open neighbourhood
of the generic point, to a finite free module. Its stalk there is a finite-dimensional vector
space over the function field, and [Stacks, Tag 0B8J] spreads a basis of it out. -/
theorem exists_nonempty_over_iso_free_near_genericPoint_of_isFinitePresentation [IsIntegral Z]
    (G : Z.Modules) [G.IsFinitePresentation] (ξ : Z) (hξ : IsGenericPoint ξ (Set.univ : Set Z)) :
    ∃ (r : ℕ) (U : Z.Opens), ξ ∈ U ∧
      Nonempty (G.over U ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) := by
  have : G.IsFiniteType :=
    (CoherentTFAE.isQuasicoherent_isFiniteType_of_isFinitePresentation G inferInstance).2
  obtain ⟨r, he⟩ := exists_nonempty_stalk_linearEquiv_finsupp_of_isGenericPoint G ξ hξ
  obtain ⟨U, hU, e⟩ :=
    Stacks.SheafOfModules.exists_iso_free_over_of_stalk_iso_free G inferInstance ξ r he
  exact ⟨r, U, hU, e⟩

/-- **[Stacks, Tag 0B8J] at the generic point, for a coherent module**: a coherent module on an
integral, locally Noetherian scheme is isomorphic, after restriction to some open neighbourhood
of the generic point, to a finite free module. Coherence gives finite presentation by the
equivalence [Stacks, Tag 01XZ], and
`exists_nonempty_over_iso_free_near_genericPoint_of_isFinitePresentation` applies. -/
theorem exists_nonempty_over_iso_free_near_genericPoint [IsIntegral Z] [IsLocallyNoetherian Z]
    (G : Z.Modules) [G.IsCoherent] (ξ : Z) (hξ : IsGenericPoint ξ (Set.univ : Set Z)) :
    ∃ (r : ℕ) (U : Z.Opens), ξ ∈ U ∧
      Nonempty (G.over U ≅ SheafOfModules.free.{u} (ULift.{u} (Fin r))) := by
  have htfae := (CoherentKernel.coherent_tfae Z G).out 1 3
  have : G.IsFinitePresentation := htfae.mp inferInstance
  exact exists_nonempty_over_iso_free_near_genericPoint_of_isFinitePresentation G ξ hξ

/-! ### From `over U` to `restrictFunctor U.ι` -/

/-- The free module on an open subscheme is the image under
`AlgebraicGeometry.Scheme.Modules.overEquiv` of the free module over the sliced structure sheaf:
that equivalence is a left adjoint, so it preserves the coproduct defining a free module. -/
def freeOverEquivIso (X : Scheme.{u}) (U : X.Opens) (I : Type u) :
    SheafOfModules.free (R := (U : Scheme).ringCatSheaf) I ≅
      (Scheme.Modules.overEquiv U).functor.obj
        (SheafOfModules.free (R := X.ringCatSheaf.over U) I) := by
  let F := (Scheme.Modules.overEquiv U).functor
  haveI h : Limits.PreservesColimitsOfShape.{u, u} (Discrete I) F :=
    Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1} F
  exact @SheafOfModules.mapFreeIso _ _ _ _ _ _ _ _ _ _ _ _ F I h (Iso.refl _)

/-- **A trivialisation of `G` over `U` read as a trivialisation of the restriction of `G` along
`U.ι`.** The passage is the composite of four isomorphisms: `restrictFunctor_obj_free_iso`
identifies the restriction of the free module with the free module on the open subscheme,
`freeOverEquivIso` identifies that with the image of the free module over the sliced structure
sheaf, the given trivialisation is transported by `AlgebraicGeometry.Scheme.Modules.overEquiv`,
and `AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` turns `G.over U` back into the
restriction of `G`. -/
def restrictFunctorIsoOfOverIso (U : Z.Opens) (I : Type u) (G : Z.Modules)
    (eG : G.over U ≅ SheafOfModules.free.{u} (R := Z.ringCatSheaf.over U) I) :
    (Scheme.Modules.restrictFunctor U.ι).obj (SheafOfModules.free.{u} (R := Z.ringCatSheaf) I) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj G :=
  _root_.restrictFunctor_obj_free_iso U.ι I ≪≫ freeOverEquivIso Z U I ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso eG.symm ≪≫
      (Scheme.Modules.overFunctorEquiv U).app G

/-- **A trivialisation of the restriction of `G` along `U.ι` read as a trivialisation of `G`
over `U`**, the passage converse to `restrictFunctorIsoOfOverIso`. The two spellings of the
restriction of a module to an open live in different categories — `G.over U` over the sliced
sheaf of rings `Z.ringCatSheaf.over U`, and `G.restrict U.ι` over `(U : Scheme).ringCatSheaf` —
and `AlgebraicGeometry.Scheme.Modules.overEquiv` is the equivalence between them. Read through
`AlgebraicGeometry.Scheme.Modules.overFunctorEquiv` and `freeOverEquivIso`, the given
trivialisation becomes an isomorphism between the images under that equivalence of `G.over U`
and of the free module over the sliced sheaf of rings; the equivalence is fully faithful, so the
isomorphism descends. -/
def overIsoOfRestrictIso (U : Z.Opens) (I : Type u) (G : Z.Modules)
    (eG : (Scheme.Modules.restrictFunctor U.ι).obj G ≅
      SheafOfModules.free.{u} (R := (U : Scheme.{u}).ringCatSheaf) I) :
    G.over U ≅ SheafOfModules.free.{u} (R := Z.ringCatSheaf.over U) I :=
  (Scheme.Modules.overEquiv U).functor.preimageIso
    ((Scheme.Modules.overFunctorEquiv U).app G ≪≫ eG ≪≫ freeOverEquivIso Z U I)

/-- **A module of finite presentation on an integral scheme is a finite free module near the
generic point**, with the isomorphism stated after restriction along the inclusion of the
neighbourhood. This is [Stacks, Tag 0B8J] applied at the generic point, where the local ring is
the function field, composed with the comparison `restrictFunctorIsoOfOverIso` between the two
ways of restricting a module to an open. -/
theorem exists_isIso_restrictFunctor_free_near_genericPoint_of_isFinitePresentation
    [IsIntegral Z] (G : Z.Modules) [G.IsFinitePresentation]
    (ξ : Z) (hξ : IsGenericPoint ξ (Set.univ : Set Z)) :
    ∃ (r : ℕ) (U : Z.Opens), ξ ∈ U ∧
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj
          (SheafOfModules.free.{u} (R := Z.ringCatSheaf) (ULift.{u} (Fin r))) ≅
        (Scheme.Modules.restrictFunctor U.ι).obj G) := by
  obtain ⟨r, U, hU, ⟨eG⟩⟩ :=
    exists_nonempty_over_iso_free_near_genericPoint_of_isFinitePresentation G ξ hξ
  exact ⟨r, U, hU, ⟨restrictFunctorIsoOfOverIso U (ULift.{u} (Fin r)) G eG⟩⟩

/-- **A coherent module on an integral, locally Noetherian scheme is a finite free module near
the generic point**, with the isomorphism stated after restriction along the inclusion of the
neighbourhood. This is [Stacks, Tag 0B8J] applied at the generic point, where the local ring is
the function field, composed with the comparison `restrictFunctorIsoOfOverIso` between the two
ways of restricting a module to an open. -/
theorem exists_isIso_restrictFunctor_free_near_genericPoint
    [IsIntegral Z] [IsLocallyNoetherian Z] (G : Z.Modules) [G.IsCoherent]
    (ξ : Z) (hξ : IsGenericPoint ξ (Set.univ : Set Z)) :
    ∃ (r : ℕ) (U : Z.Opens), ξ ∈ U ∧
      Nonempty ((Scheme.Modules.restrictFunctor U.ι).obj
          (SheafOfModules.free.{u} (R := Z.ringCatSheaf) (ULift.{u} (Fin r))) ≅
        (Scheme.Modules.restrictFunctor U.ι).obj G) := by
  have htfae := (CoherentKernel.coherent_tfae Z G).out 1 3
  have : G.IsFinitePresentation := htfae.mp inferInstance
  exact exists_isIso_restrictFunctor_free_near_genericPoint_of_isFinitePresentation G ξ hξ

/-! ### The free module on `ULift (Fin r)` as a finite coproduct -/

section Coproduct

variable {C : Type*} [Category.{u} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

-- Instance search for these coproducts times out on Mathlib v4.35.0; supply them directly.
local instance (J' : Type u) : HasColimitsOfShape (Discrete J') (PresheafOfModules.{u} R.obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

/-- **The coproduct of `r` copies of the structure sheaf is the free module on
`ULift (Fin r)`**, over an arbitrary sheaf of rings. Both morphisms are defined by the universal
property of the coproduct, `SheafOfModules.free` being a coproduct by definition; see the
implementation notes for why the abstract form is the one that is proved. -/
def freeCoproductIsoAux (r : ℕ)
    [HasCoproduct (fun _ : Fin r => SheafOfModules.unit R)] :
    (∐ fun _ : Fin r => SheafOfModules.unit R) ≅
      SheafOfModules.free.{u} (R := R) (ULift.{u} (Fin r)) where
  hom := Sigma.desc fun j => SheafOfModules.ιFree (ULift.up j)
  inv := Sigma.desc (f := fun _ : ULift.{u} (Fin r) => SheafOfModules.unit R)
    fun j => Sigma.ι (fun _ : Fin r => SheafOfModules.unit R) j.down
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun j => ?_
    change Sigma.ι (fun _ : Fin r => SheafOfModules.unit R) j ≫
        (Sigma.desc fun k => Sigma.ι (fun _ : ULift.{u} (Fin r) => SheafOfModules.unit R)
          (ULift.up k)) ≫
        Sigma.desc (f := fun _ : ULift.{u} (Fin r) => SheafOfModules.unit R)
          (fun k => Sigma.ι (fun _ : Fin r => SheafOfModules.unit R) k.down) = _
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact (Category.comp_id _).symm
  inv_hom_id := by
    change Sigma.desc (f := fun _ : ULift.{u} (Fin r) => SheafOfModules.unit R)
          (fun k => Sigma.ι (fun _ : Fin r => SheafOfModules.unit R) k.down) ≫
        (Sigma.desc fun k => Sigma.ι (fun _ : ULift.{u} (Fin r) => SheafOfModules.unit R)
          (ULift.up k)) = _
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    exact (Category.comp_id _).symm

/-- The abstract form of `freeCoproductIso_hom_ι`: the `j`-th inclusion into the coproduct
becomes the `ULift.up j`-th inclusion into the free module. -/
lemma freeCoproductIsoAux_hom_ι (r : ℕ)
    [HasCoproduct (fun _ : Fin r => SheafOfModules.unit R)] (j : Fin r) :
    Sigma.ι (fun _ : Fin r => SheafOfModules.unit R) j ≫ (freeCoproductIsoAux R r).hom =
      SheafOfModules.ιFree (ULift.up j) :=
  Sigma.ι_comp_desc _ _

end Coproduct

/-- **The coproduct of `r` copies of the structure sheaf of a scheme is the free module on
`ULift (Fin r)`.** The index type of `SheafOfModules.free` must live in `Type u`, so a finite
free module of rank `r` is spelled over `ULift (Fin r)` there and over `Fin r` wherever a
coproduct is formed; this is the bridge between the two spellings. -/
def freeCoproductIso (Z : Scheme.{u}) (r : ℕ) :
    (∐ fun _ : Fin r => SheafOfModules.unit Z.ringCatSheaf) ≅
      SheafOfModules.free.{u} (R := Z.ringCatSheaf) (ULift.{u} (Fin r)) :=
  freeCoproductIsoAux Z.ringCatSheaf r

/-- `freeCoproductIso` sends the `j`-th coproduct inclusion to the `ULift.up j`-th inclusion
into the free module. -/
lemma freeCoproductIso_hom_ι (Z : Scheme.{u}) (r : ℕ) (j : Fin r) :
    Limits.Sigma.ι (fun _ : Fin r => SheafOfModules.unit Z.ringCatSheaf) j ≫
        (freeCoproductIso Z r).hom =
      SheafOfModules.ιFree (ULift.up j) :=
  freeCoproductIsoAux_hom_ι Z.ringCatSheaf r j

-- The category of modules on a scheme is abelian, hence has finite products, hence finite
-- biproducts; the last implication is deliberately not an instance in Mathlib, so the
-- declaration of `StacksFrontier/AlgebraicGeometry/IrreducibleDevissage/Coproduct.lean` is
-- re-enabled here, together with the transparency that lets instance search see through
-- `AlgebraicGeometry.Scheme.Modules`. Both are confined to the end of the file: they are what
-- makes the biproduct below available, and they interfere with the coproduct rewriting above.
attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules
attribute [local instance] hasFiniteBiproducts_modules

/-- **A finite free module on a locally Noetherian scheme is coherent.** The structure sheaf is
coherent by [Stacks, Tag 01XZ], a finite biproduct of copies of a coherent module is coherent by
`Stacks.AlgebraicGeometry.IrreducibleDevissage.isCoherent_biproduct_const`, and the free module
on `ULift (Fin r)` is such a biproduct through `freeCoproductIso` and
`CategoryTheory.Limits.biproduct.isoCoproduct`. -/
theorem isCoherent_free_ulift [IsLocallyNoetherian Z] (r : ℕ) :
    (SheafOfModules.free.{u} (R := Z.ringCatSheaf) (ULift.{u} (Fin r))).IsCoherent :=
  isCoherent_of_iso' ((freeCoproductIso Z r).symm ≪≫ (biproduct.isoCoproduct _).symm)
    (isCoherent_biproduct_const (SheafOfModules.unit Z.ringCatSheaf)
      (CoherentKernel.structureSheaf_isCoherent Z) r (Fin r) inferInstance inferInstance
      (Fintype.card_fin r))

end Stacks.AlgebraicGeometry.IrreducibleDevissage

end
