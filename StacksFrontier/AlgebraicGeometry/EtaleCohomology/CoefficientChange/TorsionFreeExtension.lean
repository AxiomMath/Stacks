module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CoefficientChange.IntegralCoefficients
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.ModuleCohomologyComparison

/-!
# Extension of coefficients stays injective on a torsion-free quotient

Let `Λ` be a commutative ring and `X` a scheme.  Extension of coefficients along `ℤ → Λ` is only
right exact, and that is the whole difficulty of [Stacks, Tag 0GL6].  What is true, and is the
input the dévissage behind [Stacks, Tag 0D6J] runs on, is that it keeps the first map of a short
exact sequence of abelian étale sheaves a monomorphism **provided the quotient has sectionwise
torsion-free sections**.

## Main results

* `Stacks.EtaleCohomology.mono_etaleIntModuleExtend_map_of_shortExact`: the statement for the
  `ℤ`-module spelling of integral coefficients.

## Implementation notes

**Where the whole route through `ℤ` leans on `ℤ`.**  A reader may reasonably ask why Tag 0GL6 is
proved by comparing both coefficient rings with `ℤ` instead of working over `Λ₁` directly.  There
are two independent reasons, and both are visible in this one file.

*The mathematics.*  The one substantive input is
`ModuleSheafCohomology.lTensor_injective_of_exact_of_isTorsionFree`, which holds over any
Dedekind domain and needs only `Function.Exact f g` with `f` injective and the third term
torsion-free -- crucially **not** surjectivity of `g`, which a short exact sequence of sheaves
does not give sectionwise.  Over a general coefficient ring the corresponding class is flatness,
which is neither closed under subobjects nor preserved by sheafification; since closure under
subobjects is a *hypothesis* of the generic dévissage
(`ModuleSheafCohomology.ext_eq_zero_of_adjunction`), it cannot be run over `Λ₁` at all.

*The plumbing.*  `ModuleCat.extendScalars` builds its own `Algebra ℤ Λ` structure rather than
taking the ambient one, so the goal and the tensor lemma speak of different `Module ℤ Λ`
instances.  Over `ℤ` these are equal -- `Algebra ℤ R` and `Module ℤ M` are both subsingletons --
so pinning the instances reconciles them.  Over a general base ring the two algebra structures
would differ in substance and not merely in spelling, and no amount of instance pinning would
help.

*Why two `letI`s and not one, which is the opposite of what the neighbouring file needs.*
`ModuleCat.extendScalars_preservesKernel_of_flat` reconciles the same two instances with the
single `let _ := f.toAlgebra`, and that is **correct over a general base ring**: there is then no
ambient `Algebra R S`, so the `let` is the only candidate and instance search for `Module R S`
finds it.  Over `ℤ` an ambient instance does exist and outranks a `let`, so `Module ℤ Λ` resolves
to `AddCommGroup.toIntModule` while the goal carries `Algebra.toModule`; the symptoms are
`convert` bottoming out in `HEq` with provably equal carriers, and `show` rejected at both the
`LinearMap.baseChange` and the `LinearMap.lTensor` spellings.  The fix is to pin both -- the
algebra structure, and then the module structure as its `toModule` -- which is what the proof
below does.  So the single-`let` idiom is right where it stands and insufficient here, and the
route through `ℤ` genuinely costs something at this one step while paying for itself twice above.

So the route through `ℤ` is load-bearing twice over, in two unrelated steps, rather than being a
convenience.

**Why sectionwise left exactness is enough, and why it is all one gets.**  A short exact sequence
of sheaves is exact sectionwise only on the left: the sheaf image of `S.f` is in general strictly
bigger than the sectionwise image, so `S.g` need not be sectionwise surjective.  Left exactness
is obtained from `PreservesFiniteLimits` of the sections functor
(`Stacks.ConstantSheaf.sheafSections_preservesFiniteLimits`) through
`CategoryTheory.Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono`, and that is exactly
the hypothesis shape the tensor lemma wants.

Monomorphy is then checked on the underlying presheaf and transported by sheafification, which is
left exact.  On sections, with the instances pinned as above, the map
`CategoryTheory.ModuleCat.extendScalars` induces *is* `LinearMap.lTensor`, so no rewriting along
`LinearMap.baseChange_eq_ltensor` is needed.

## References

* [Stacks Project, Tag 0GL6](https://stacks.math.columbia.edu/tag/0GL6)
* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u r

namespace Stacks.EtaleCohomology

variable (Λ : Type r) [CommRing Λ] (X : Scheme.{u})

/-- Sections over an object of the small étale site, of a sheaf of `ℤ`-modules, as a functor. -/
abbrev intSectionsFunctor (V : X.Etaleᵒᵖ) :
    EtaleIntModules.{u, r} X ⥤ ModuleCat.{max (u + 1) r} ℤ :=
  sheafToPresheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} ℤ) ⋙
    (evaluation X.Etaleᵒᵖ (ModuleCat.{max (u + 1) r} ℤ)).obj V

/-- **A short exact sequence of sheaves of `ℤ`-modules is left exact on sections.**  Only left
exactness holds: the sheaf image of `S.f` can be strictly bigger than its sectionwise image, so
`S.g` need not be sectionwise surjective.  This is the observation the proof of
`Stacks.EtaleCohomology.mono_etaleIntModuleExtend_map_of_shortExact` turns on. -/
theorem exact_and_mono_intSections_map_of_shortExact
    (S : ShortComplex (EtaleIntModules.{u, r} X)) (hS : S.ShortExact) (V : X.Etaleᵒᵖ) :
    (S.map (intSectionsFunctor.{u, r} X V)).Exact ∧
      Mono (S.map (intSectionsFunctor.{u, r} X V)).f :=
  (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (intSectionsFunctor.{u, r} X V)).mp inferInstance S hS

/-- **Extension of coefficients along `ℤ → Λ` keeps the inclusion of a short exact sequence of
abelian étale sheaves a monomorphism, when the quotient is sectionwise torsion free.** -/
theorem mono_etaleIntModuleExtend_map_of_shortExact
    (S : ShortComplex (EtaleIntModules.{u, r} X)) (hS : S.ShortExact)
    (hP : ∀ V, Module.IsTorsionFree ℤ (S.X₃.obj.obj V)) :
    Mono ((etaleIntModuleExtend.{u, r} Λ X).map S.f) := by
  have hsec : ∀ V : X.Etaleᵒᵖ,
      Mono ((ModuleCat.extendScalars.{0, r, max (u + 1) r} (Int.castRingHom Λ)).map
        (S.f.hom.app V)) := by
    intro V
    have hTF := hP V
    obtain ⟨hE, hEm⟩ := exact_and_mono_intSections_map_of_shortExact.{u, r} X S hS V
    -- `ModuleCat.extendScalars` builds its own `Algebra ℤ Λ` instance rather than taking the
    -- ambient one, so the goal and the tensor lemma otherwise speak of different `Module ℤ Λ`
    -- instances and nothing bridges them by definitional equality.  Putting the ring map's own
    -- algebra structure in scope makes both sides use it, after which the categorical map and
    -- `LinearMap.lTensor` agree on the nose; this is the idiom of
    -- `ModuleCat.extendScalars_preservesKernel_of_flat`.
    let instA : Algebra ℤ Λ := ((algebraMap Λ Λ).comp (Int.castRingHom Λ)).toAlgebra
    let instM : Module ℤ Λ := instA.toModule
    refine (ModuleCat.mono_iff_injective _).mpr ?_
    change Function.Injective ⇑(LinearMap.lTensor Λ (S.f.hom.app V).hom)
    exact ModuleSheafCohomology.lTensor_injective_of_exact_of_isTorsionFree
      (S.f.hom.app V).hom (S.g.hom.app V).hom ((ModuleCat.mono_iff_injective _).mp hEm)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
        (S.map (intSectionsFunctor.{u, r} X V))).mp hE) Λ
  have : ∀ V : X.Etaleᵒᵖ, Mono ((((Functor.whiskeringRight X.Etaleᵒᵖ
      (ModuleCat.{max (u + 1) r} ℤ) (ModuleCat.{max (u + 1) r} Λ)).obj
        (ModuleCat.extendScalars.{0, r, max (u + 1) r} (Int.castRingHom Λ))).map
      ((sheafToPresheaf X.smallEtaleTopology
        (ModuleCat.{max (u + 1) r} ℤ)).map S.f)).app V) := hsec
  have : Mono (((Functor.whiskeringRight X.Etaleᵒᵖ (ModuleCat.{max (u + 1) r} ℤ)
      (ModuleCat.{max (u + 1) r} Λ)).obj
        (ModuleCat.extendScalars.{0, r, max (u + 1) r} (Int.castRingHom Λ))).map
      ((sheafToPresheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} ℤ)).map S.f)) :=
    NatTrans.mono_of_mono_app _
  exact (presheafToSheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) r} Λ)).map_mono _

/-- Extension of coefficients is additive, being a left adjoint of an additive functor. -/
instance etaleIntModuleExtend_additive :
    (etaleIntModuleExtend.{u, r} Λ X).Additive :=
  (etaleIntModuleExtendForgetAdj.{u, r} Λ X).left_adjoint_additive

/-- Extension of coefficients preserves colimits, being a left adjoint. -/
instance etaleIntModuleExtend_preservesColimits :
    PreservesColimitsOfSize.{0, 0} (etaleIntModuleExtend.{u, r} Λ X) :=
  (etaleIntModuleExtendForgetAdj.{u, r} Λ X).leftAdjoint_preservesColimits

/-- **Extension of coefficients carries a short exact sequence with sectionwise torsion-free
quotient to a short exact sequence.**  Right exactness is free, extension of coefficients being
a left adjoint; the content is monomorphy of the first map, which is
`Stacks.EtaleCohomology.mono_etaleIntModuleExtend_map_of_shortExact`. -/
theorem shortExact_map_etaleIntModuleExtend_of_isTorsionFree
    (S : ShortComplex (EtaleIntModules.{u, r} X)) (hS : S.ShortExact)
    (hP : ∀ V, Module.IsTorsionFree ℤ (S.X₃.obj.obj V)) :
    (S.map (etaleIntModuleExtend.{u, r} Λ X)).ShortExact := by
  obtain ⟨hE, hEp⟩ := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (etaleIntModuleExtend.{u, r} Λ X)).mp inferInstance S hS
  exact ShortComplex.ShortExact.mk' hE
    (mono_etaleIntModuleExtend_map_of_shortExact.{u, r} Λ X S hS hP) hEp

/-! ### The abelian-group spelling, bridged from the `ℤ`-module one

The engine above lives in the `ℤ`-module spelling, because that is where
`CategoryTheory.ModuleCat.extendScalars` and its adjunction are natural.  The chain that consumes
it runs in the abelian-group spelling instead: the torsion-free class is stated there, and the
corepresentation of sections cannot be had in `Sheaf J (ModuleCat ℤ)` at all, `ModuleCat.free`
tying the type, ring and module universes together.  The two are bridged here, once; everything
downstream consumes only the abelian-group statements.

The bridge is definitional on functors -- `etaleAbelianSheafExtend` *is* the equivalence followed
by `etaleIntModuleExtend` -- but not on sectionwise torsion-freeness.

**Two provably-equal instances cannot be bridged by rewriting.**  The goal carries `ModuleCat`'s
own `Module ℤ` structure on a carrier, while any map supplied by the equivalence's unit lives in
`AddCommGrpCat` and so carries `AddCommGroup.toIntModule`.  The two are equal, `Module ℤ M` being
a subsingleton, and that equality is nevertheless unusable: `exact` and `show` fail on the
mismatch, `convert` bottoms out in `HEq` with the carriers provably equal, and
`rw [Subsingleton.elim ..]` cannot place its equation because the goal's instance is an
already-elaborated term rather than the literal `inferInstance`.  The way through is an argument
that never mentions the instance -- supply the scalar-compatibility hypothesis by hand and let
`int_smul_eq_zsmul` convert the exotic `ℤ`-action to the canonical one, which is what Mathlib
itself does for this very pair of spellings in
`Mathlib/Algebra/Category/Grp/ZModuleEquivalence.lean`.  Worth remembering as a
rule: between two Mathlib spellings of the same `ℤ`-linear structure, expect an instance path
rather than mathematics, and reach for elements rather than a rewrite.

An `EssSurj` witness proves nothing here either.  Mathlib makes
`forget₂ (ModuleCat ℤ) AddCommGrpCat` essentially surjective with the identity as witnessing
isomorphism, which invites the hope that the transport is free; but the equivalence's *functor*
is obtained through `CategoryTheory.Functor.inv`, so Lean never sees the carrier of
`e.functor.obj A` as literally `A`.
-/

/-- The coefficient equivalence is additive, being an equivalence. -/
instance etaleIntCoefficientEquivalence_functor_additive :
    (etaleIntCoefficientEquivalence.{u, r} X).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- **Sectionwise torsion-freeness transports across the coefficient equivalence.** -/
theorem isTorsionFree_etaleIntCoefficientEquivalence_functor_obj
    (F : EtaleAbelianSheaves.{u, r} X) (V : X.Etaleᵒᵖ)
    (h : Module.IsTorsionFree ℤ (F.obj.obj V)) :
    Module.IsTorsionFree ℤ
      (((etaleIntCoefficientEquivalence.{u, r} X).functor.obj F).obj.obj V) := by
  have : Module.IsTorsionFree ℤ ↑(((𝟭 (EtaleAbelianSheaves.{u, r} X)).obj F).obj.obj V) := h
  let φ := ((etaleIntCoefficientEquivalence.{u, r} X).unitIso.app F).inv.hom.app V
  exact Function.Injective.moduleIsTorsionFree (⇑φ.hom)
    ((AddCommGrpCat.mono_iff_injective φ).mp inferInstance) (fun n y => by
      convert! map_zsmul φ.hom n y using 2
      exact congrArg _ (int_smul_eq_zsmul _ n y))

/-- **`hL` in the abelian-group spelling**, carried across the coefficient equivalence. -/
theorem mono_etaleAbelianSheafExtend_map_of_shortExact
    (S : ShortComplex (EtaleAbelianSheaves.{u, r} X)) (hS : S.ShortExact)
    (hP : ∀ V, Module.IsTorsionFree ℤ (S.X₃.obj.obj V)) :
    Mono ((etaleAbelianSheafExtend.{u, r} Λ X).map S.f) :=
  mono_etaleIntModuleExtend_map_of_shortExact.{u, r} Λ X
    (S.map (etaleIntCoefficientEquivalence.{u, r} X).functor)
    (hS.map_of_exact _)
    (fun V => isTorsionFree_etaleIntCoefficientEquivalence_functor_obj.{u, r} X S.X₃ V (hP V))

/-- **Extension of coefficients carries a short exact sequence of abelian étale sheaves with
sectionwise torsion-free quotient to a short exact sequence.** -/
theorem shortExact_map_etaleAbelianSheafExtend_of_isTorsionFree
    (S : ShortComplex (EtaleAbelianSheaves.{u, r} X)) (hS : S.ShortExact)
    (hP : ∀ V, Module.IsTorsionFree ℤ (S.X₃.obj.obj V)) :
    (S.map (etaleAbelianSheafExtend.{u, r} Λ X)).ShortExact :=
  shortExact_map_etaleIntModuleExtend_of_isTorsionFree.{u, r} Λ X
    (S.map (etaleIntCoefficientEquivalence.{u, r} X).functor)
    (hS.map_of_exact _)
    (fun V => isTorsionFree_etaleIntCoefficientEquivalence_functor_obj.{u, r} X S.X₃ V (hP V))

end Stacks.EtaleCohomology

end
