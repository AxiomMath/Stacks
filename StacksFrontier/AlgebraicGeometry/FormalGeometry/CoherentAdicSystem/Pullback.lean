module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.Abelian
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.PullbackIdealPower
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.CoherentPullbackPushforward
public import StacksFrontier.Topology.Sheaves.Functors.Module.FlatPullback
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-!
# Pullback of coherent adic systems

**Stacks 0887.** Let `f : X ⟶ Y` be a morphism of Noetherian schemes, let `𝒥 ⊆ 𝒪_Y` be a
quasi-coherent sheaf of ideals and set `ℐ = f^{-1}𝒥 𝒪_X`. Termwise pullback of an inverse system
is again an adic system, so it defines a functor

`f^* : Coh(Y, 𝒥) ⟶ Coh(X, ℐ)`,

which is right exact, and exact when `f` is flat.

That termwise pullback lands in `Coh(X, ℐ)` is the content of
`Stacks.Algebraization.pullback_idealPowerMultiple_comp_eq_zero_iff`: coherence is preserved by
pullback, annihilation by `𝒥 ⁿ⁺¹` becomes annihilation by `ℐ ⁿ⁺¹`, and — since pullback is a left
adjoint, hence right exact — the quotient presentation `G_n = G_{n+1} / 𝒥 ⁿ⁺¹ G_{n+1}` is carried
to `f^*G_n = f^*G_{n+1} / ℐ ⁿ⁺¹ f^*G_{n+1}`.

Right exactness is the source's argument: cokernels in `Coh` are the levelwise ones
(`Stacks.Coherent.preservesColimitParallelPairι`), pullback of modules preserves all colimits, so
the composite with the inclusion of the full subcategory preserves finite colimits and the
inclusion reflects them.

For a flat `f` the source deduces exactness from the construction of kernels. Here that is done
through monomorphisms: a functor between abelian categories which is right exact and preserves
monomorphisms preserves finite limits. A monomorphism `α` of coherent adic systems has zero
kernel, so at each level `n` the levelwise kernel of `α_l` dies under the transition `F_l ⟶ F_n`
for some `l ≥ n` — this is what the stable-kernel-image analysis of
`Stacks.Coherent.kernelImageQuotients_eventuallyConstant` records. Flatness makes pullback commute
with the levelwise kernel, and the transition maps of a coherent adic system are epimorphisms, so
every component of a morphism annihilated by `f^*α` vanishes.

## Main definitions

* `Stacks.Coherent.coherentAdicPullback` — **the functor `f^* : Coh(Y, 𝒥) ⟶ Coh(X, ℐ)`.**

## Main results

* `Stacks.Coherent.isCoherentAdicSystem_pullback` — termwise pullback of a coherent adic system
  along `𝒥` is a coherent adic system along `ℐ`.
* `Stacks.Coherent.coherentAdicPullback_obj_obj` — its terms are the pullbacks of the terms.
* `Stacks.Coherent.coherentAdicPullback_rightExact` — **the functor is right exact.**
* `Stacks.Coherent.coherentAdicPullback_exact` — **it is exact when `f` is flat.**

## Implementation notes

The inverse-image ideal sheaf `f^{-1}𝒥 𝒪_X` is `AlgebraicGeometry.Scheme.IdealSheafData.comap`,
the ideal sheaf of the scheme-theoretic preimage of the closed subscheme cut out by `𝒥`.

`Stacks.Coherent.isCoherentAdicSystem_map` is stated for an arbitrary right exact functor between
categories of modules compatible with ideal-power multiples, which is all the transport argument
uses; the pullback case is the instantiation.

## References

* [Stacks Project, Tag 0887](https://stacks.math.columbia.edu/tag/0887)
* [Stacks Project, Tag 087W](https://stacks.math.columbia.edu/tag/087W)
* [Stacks Project, Tag 087X](https://stacks.math.columbia.edu/tag/087X)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

universe u

attribute [local instance] AlgebraicGeometry.Scheme.Modules.submoduleCompleteLattice

namespace Stacks.Coherent

open Stacks.Algebraization

/-! The zero morphism out of a sheaf of modules presented without `Scheme.Modules` is supplied by
the `local instance` of `CoherentAdicSystem.PullbackIdealPower`, reactivated here rather than
restated: instance search does not see through `AlgebraicGeometry.Scheme.Modules`, a semireducible
definition, to find the zero morphisms of `X.Modules` for a source presented as a bare
`SheafOfModules X.ringCatSheaf`. -/

attribute [local instance] Stacks.Algebraization.zeroHomOfSheafOfModules

/-! ### The inclusion of coherent adic systems is right exact -/

/-- **The inclusion of `Coh(X, ℐ)` into inverse systems of modules preserves finite colimits.**
Cokernels in `Coh(X, ℐ)` are the levelwise ones, and a functor between preadditive categories
with cokernels which preserves cokernels preserves all finite colimits.

It is *not* left exact: the levelwise kernel of a morphism of coherent adic systems need not be
one again. -/
public theorem coherentAdicInclusion_preservesFiniteColimits {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) :
    PreservesFiniteColimits (ObjectProperty.ι (IsCoherentAdicSystem I)) :=
  have : HasFiniteBiproducts (CoherentAdicSystems I) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasBinaryBiproducts (CoherentAdicSystems I) :=
    hasBinaryBiproducts_of_finite_biproducts _
  have : HasZeroObject (CoherentAdicSystems I) := hasZeroObject_of_hasFiniteBiproducts _
  have : HasCoequalizers (CoherentAdicSystems I) := Preadditive.hasCoequalizers_of_hasCokernels
  Functor.preservesFiniteColimits_of_preservesCokernels _

/-! ### Transport of coherent adic systems along a right exact functor -/

/-- A right exact functor compatible with ideal-power multiples carries the quotient by one to
the quotient by the other, compatibly with the two quotient maps. -/
public theorem exists_functor_idealPowerQuotient_iso
    {Z W : Scheme.{u}} (L : Z.Modules ⥤ W.Modules) [L.PreservesZeroMorphisms]
    [PreservesColimitsOfShape WalkingParallelPair L]
    (J : Z.IdealSheafData) (K : W.IdealSheafData) (n : ℕ) (M : Z.Modules)
    (hw : ∀ {N : W.Modules} (φ : L.obj M ⟶ N),
      L.map (idealPowerMultiple J n M).ι ≫ φ = 0 ↔
        (idealPowerMultiple K n (L.obj M)).ι ≫ φ = 0) :
    ∃ e : L.obj (idealPowerQuotient J n M) ≅ idealPowerQuotient K n (L.obj M),
      L.map (cokernel.π (idealPowerMultiple J n M).ι) ≫ e.hom =
        cokernel.π (idealPowerMultiple K n (L.obj M)).ι := by
  set P := idealPowerMultiple J n M
  set Q := idealPowerMultiple K n (L.obj M)
  have hc := isColimitCoforkMapOfIsColimit' L (cokernel.condition P.ι) (cokernelIsCokernel P.ι)
  let hc' := CokernelCofork.isColimitOfIsColimitOfIff' hc Q.ι (fun {N} φ => hw φ)
  let e := (cokernelIsCokernel Q.ι).coconePointUniqueUpToIso hc'
  exact ⟨e.symm, (Iso.comp_inv_eq e).mpr
    ((cokernelIsCokernel Q.ι).comp_coconePointUniqueUpToIso_hom hc' WalkingParallelPair.one).symm⟩

/-- A functor compatible with ideal-power multiples carries a module annihilated by `J ⁿ` to one
annihilated by `K ⁿ`. -/
private theorem idealPowerMultiple_eq_bot_map
    {Z W : Scheme.{u}} (L : Z.Modules ⥤ W.Modules) [L.PreservesZeroMorphisms]
    (J : Z.IdealSheafData) (K : W.IdealSheafData) (n : ℕ) (M : Z.Modules)
    (hw : ∀ {N : W.Modules} (φ : L.obj M ⟶ N),
      L.map (idealPowerMultiple J n M).ι ≫ φ = 0 ↔
        (idealPowerMultiple K n (L.obj M)).ι ≫ φ = 0)
    (hM : idealPowerMultiple J n M = ⊥) :
    idealPowerMultiple K n (L.obj M) = ⊥ := by
  refine (submodule_ι_eq_zero_iff _).mp ?_
  have hp := (submodule_ι_eq_zero_iff _).mpr hM
  have h := (hw (𝟙 _)).mp
    (by
      rw [hp]
      exact (Category.comp_id _).trans (L.map_zero _ _))
  exact (Category.comp_id _).symm.trans h

/-- **A right exact functor compatible with ideal-power multiples carries coherent adic systems
to coherent adic systems**, provided it preserves coherence termwise. -/
public theorem isCoherentAdicSystem_map
    {Z W : Scheme.{u}} (L : Z.Modules ⥤ W.Modules) [L.PreservesZeroMorphisms]
    [PreservesColimitsOfShape WalkingParallelPair L]
    (J : Z.IdealSheafData) (K : W.IdealSheafData)
    (hw : ∀ (n : ℕ) (M : Z.Modules) {N : W.Modules} (φ : L.obj M ⟶ N),
      L.map (idealPowerMultiple J n M).ι ≫ φ = 0 ↔
        (idealPowerMultiple K n (L.obj M)).ι ≫ φ = 0)
    (F : CoherentAdicSystems J)
    (hF : ∀ n : ℕ, (L.obj (F.obj.obj (op n))).IsCoherent) :
    IsCoherentAdicSystem K (F.obj ⋙ L) := by
  refine ⟨hF, fun n => ?_, fun n => ?_⟩
  · exact idealPowerMultiple_eq_bot_map L J K (n + 1) _ (hw (n + 1) _)
      (F.property.idealPowerMultiple_eq_bot n)
  · obtain ⟨q, hq⟩ := exists_functor_idealPowerQuotient_iso L J K (n + 1)
      (F.obj.obj (op (n + 1))) (hw (n + 1) (F.obj.obj (op (n + 1))))
    refine ⟨q.symm ≪≫ L.mapIso (F.property.quotientIso n), ?_⟩
    change cokernel.π _ ≫ (q.inv ≫ L.map (F.property.quotientIso n).hom) = _
    refine Eq.trans (congrArg (fun τ => τ ≫ (q.inv ≫ L.map (F.property.quotientIso n).hom))
      hq.symm) ?_
    refine (Category.assoc _ q.hom _).trans ?_
    refine (congrArg (fun τ => L.map (cokernel.π (idealPowerMultiple J (n + 1)
      (F.obj.obj (op (n + 1)))).ι) ≫ τ) (Iso.hom_inv_id_assoc q _)).trans ?_
    exact (L.map_comp _ _).symm.trans
      (congrArg L.map (F.property.cokernel_π_comp_quotientIso n))

/-! ### The pullback functor -/

/-- **Termwise pullback of a coherent adic system along `𝒥` is a coherent adic system along
`ℐ = f^{-1}𝒥 𝒪_X`.** -/
public theorem isCoherentAdicSystem_pullback
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) (G : CoherentAdicSystems J) :
    IsCoherentAdicSystem (J.comap f) (G.obj ⋙ Scheme.Modules.pullback f) :=
  isCoherentAdicSystem_map (Scheme.Modules.pullback f) J (J.comap f)
    (fun n M _ φ => pullback_idealPowerMultiple_comp_eq_zero_iff f J n M φ) G
    (fun n => by
      have _ : (G.obj.obj (op n)).IsCoherent := G.property.isCoherent n
      exact AlgebraicGeometry.isCoherent_pullback f (G.obj.obj (op n)))

/-- **Stacks 0887: the functor `f^* : Coh(Y, 𝒥) ⟶ Coh(X, ℐ)`.** For a morphism `f : X ⟶ Y` of
Noetherian schemes and a quasi-coherent sheaf of ideals `𝒥` on `Y`, termwise pullback is a functor
from the coherent adic systems along `𝒥` to those along `ℐ = f^{-1}𝒥 𝒪_X`.

It is built as a lift of termwise pullback, so its action on objects and morphisms is the
canonical one; see `Stacks.Coherent.coherentAdicPullback_obj_obj`. -/
@[stacks 0887 "the functor f^*"]
public def coherentAdicPullback {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) :
    CoherentAdicSystems J ⥤ CoherentAdicSystems (J.comap f) :=
  ObjectProperty.lift (IsCoherentAdicSystem (J.comap f))
    (ObjectProperty.ι (IsCoherentAdicSystem J) ⋙
      (Functor.whiskeringRight _ _ _).obj (Scheme.Modules.pullback f))
    (isCoherentAdicSystem_pullback f J)

/-- **The functor of Stacks 0887 sends the system `(G_n)` to the system `(f^*G_n)`.** -/
@[stacks 0887 "the functor sends (G n) to (f^* G n)"]
public theorem coherentAdicPullback_obj_obj {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) (G : CoherentAdicSystems J) (n : ℕᵒᵖ) :
    ((coherentAdicPullback f J).obj G).obj.obj n =
      (Scheme.Modules.pullback f).obj (G.obj.obj n) :=
  rfl

/-- The pullback functor on coherent adic systems acts on morphisms by termwise pullback. -/
public theorem coherentAdicPullback_map_hom_app {X Y : Scheme.{u}} [IsNoetherian X]
    [IsNoetherian Y] (f : X ⟶ Y) (J : Y.IdealSheafData) {F G : CoherentAdicSystems J}
    (α : F ⟶ G) (n : ℕᵒᵖ) :
    ((coherentAdicPullback f J).map α).hom.app n =
      (Scheme.Modules.pullback f).map (α.hom.app n) :=
  rfl

/-! ### Right exactness -/

/-- **Stacks 0887: the pullback functor on coherent adic systems is right exact.**

Termwise pullback of inverse systems preserves all colimits, being a left adjoint; the inclusion
of `Coh(Y, 𝒥)` preserves finite colimits, cokernels there being levelwise; so the composite of
`f^*` with the inclusion of `Coh(X, ℐ)` preserves finite colimits, and that inclusion reflects
them. -/
@[stacks 0887 "right exactness"]
public theorem coherentAdicPullback_rightExact {X Y : Scheme.{u}} [IsNoetherian X]
    [IsNoetherian Y] (f : X ⟶ Y) (J : Y.IdealSheafData) :
    rightExactFunctor _ _ (coherentAdicPullback f J) := by
  rw [rightExactFunctor_iff]
  set ιP := ObjectProperty.ι (IsCoherentAdicSystem J)
  set ιQ := ObjectProperty.ι (IsCoherentAdicSystem (J.comap f))
  set Wh : (ℕᵒᵖ ⥤ Y.Modules) ⥤ (ℕᵒᵖ ⥤ X.Modules) :=
    (Functor.whiskeringRight _ _ _).obj (Scheme.Modules.pullback f)
  have _ : PreservesFiniteColimits ιP := coherentAdicInclusion_preservesFiniteColimits J
  have _ : PreservesColimits Wh :=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).whiskerRight
      ℕᵒᵖ).leftAdjoint_preservesColimits
  have _ : PreservesFiniteColimits Wh := PreservesColimitsOfSize.preservesFiniteColimits Wh
  have hcomp : PreservesFiniteColimits (coherentAdicPullback f J ⋙ ιQ) := by
    change PreservesFiniteColimits (ιP ⋙ Wh)
    infer_instance
  exact preservesFiniteColimits_of_reflects_of_preserves _ ιQ

/-! ### Exactness along a flat morphism -/

/-- **A monomorphism of coherent adic systems eventually kills its levelwise kernels.** If `α` is
a monomorphism then, at each level `n`, the levelwise kernel of `α_l` at some higher level `l`
dies under the transition map `F_l ⟶ F_n`.

The kernel of `α` in `Coh(X, ℐ)` is zero, so its terms vanish; by
`Stacks.Coherent.kernelImageQuotients_eventuallyConstant` those terms are the adic quotients of
the stable kernel images, so a stable kernel image maps to zero in `F_n`, and the kernel of `α_l`
factors through it at the stabilization level. -/
public theorem mono_eventualKernelVanishes {X : Scheme.{u}} [IsNoetherian X]
    (I : X.IdealSheafData) {F G : CoherentAdicSystems I} (α : F ⟶ G) [Mono α] (n : ℕ) :
    ∃ (l : ℕ) (h : n ≤ l), kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE h).op = 0 := by
  have hz : coherentAdicKernelι I α = 0 := by
    refine (cancel_mono α).1 ?_
    simpa only [zero_comp] using coherentAdicKernelι_comp I α
  obtain ⟨c, hc⟩ := kernelImageQuotients_eventuallyConstant I α n
  set m := n + c
  obtain ⟨e, he⟩ := hc m (le_refl m)
  have hzapp : (coherentAdicKernelι I α).hom.app (op n) = 0 := by
    simpa using congrArg (fun k : coherentAdicKernel I α ⟶ F => k.hom.app (op n)) hz
  have hnm : n ≤ m := Nat.le_add_right n c
  have hs : stableKernelImageIncl I α m ≫ F.obj.map (homOfLE hnm).op = 0 := by
    rw [hzapp] at he
    exact he.symm.trans comp_zero
  set l := kernelStableLevel I α m
  have hml : m ≤ l := le_kernelStableLevel I α m
  refine ⟨l, hnm.trans hml, ?_⟩
  set k := kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE hml).op with hk
  have hfac : factorThruImage k ≫ stableKernelImageIncl I α m = k := image.fac k
  calc kernel.ι (α.hom.app (op l)) ≫ F.obj.map (homOfLE (hnm.trans hml)).op
      = k ≫ F.obj.map (homOfLE hnm).op := by
        rw [hk, Category.assoc, ← F.obj.map_comp]
        congr 1
    _ = (factorThruImage k ≫ stableKernelImageIncl I α m) ≫ F.obj.map (homOfLE hnm).op := by
        rw [hfac]
    _ = factorThruImage k ≫ stableKernelImageIncl I α m ≫ F.obj.map (homOfLE hnm).op :=
        Category.assoc _ _ _
    _ = 0 :=
        (congrArg (fun z : stableKernelImage I α m ⟶ F.obj.obj (op n) =>
          factorThruImage k ≫ z) hs).trans comp_zero

/-- **Along a flat morphism, pullback of coherent adic systems preserves monomorphisms.**

If `α` is a monomorphism then at each level `n` the kernel of `α_l` dies after a transition to
some higher level `l`; flatness makes the pullback commute with that kernel, and the transition
maps of a coherent adic system are epimorphisms, so every component of a morphism annihilated by
the pullback of `α` vanishes. -/
public theorem coherentAdicPullback_preservesMonomorphisms {X Y : Scheme.{u}} [IsNoetherian X]
    [IsNoetherian Y] (f : X ⟶ Y) (J : Y.IdealSheafData) [Flat f] :
    (coherentAdicPullback f J).PreservesMonomorphisms where
  preserves {F G} α hα := by
    have _ := AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat f
    rw [Preadditive.mono_iff_cancel_zero]
    intro H γ hγ
    have key : ∀ n : ℕ, γ.hom.app (op n) = 0 := by
      intro n
      obtain ⟨l, hnl, hker⟩ := mono_eventualKernelVanishes J α n
      have hγl : γ.hom.app (op l) ≫ (Scheme.Modules.pullback f).map (α.hom.app (op l)) = 0 :=
        congrArg (fun k : H ⟶ (coherentAdicPullback f J).obj G => k.hom.app (op l)) hγ
      have hki : kernel.ι ((Scheme.Modules.pullback f).map (α.hom.app (op l))) ≫
          (Scheme.Modules.pullback f).map (F.obj.map (homOfLE hnl).op) = 0 := by
        rw [← cancel_epi (kernelComparison (α.hom.app (op l)) (Scheme.Modules.pullback f)),
          comp_zero, ← Category.assoc, kernelComparison_comp_ι, ← Functor.map_comp, hker,
          Functor.map_zero]
      have hfac : γ.hom.app (op l) ≫
          (Scheme.Modules.pullback f).map (F.obj.map (homOfLE hnl).op) = 0 :=
        (congrArg (fun z => z ≫ (Scheme.Modules.pullback f).map (F.obj.map (homOfLE hnl).op))
          (kernel.lift_ι ((Scheme.Modules.pullback f).map (α.hom.app (op l)))
            (γ.hom.app (op l)) hγl).symm).trans
          ((Category.assoc _ _ _).trans (by rw [hki, comp_zero]))
      have _ := H.property.epi_map hnl
      rw [← cancel_epi (H.obj.map (homOfLE hnl).op), comp_zero, γ.hom.naturality]
      exact hfac
    refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun k => ?_))
    obtain ⟨n⟩ := k
    simpa using key n

/-- A functor between abelian categories which preserves finite colimits and monomorphisms also
preserves finite limits.

The statement is isolated from its application so that the ambient `Abelian` instances are
variables: all of `Preadditive`, `HasZeroMorphisms`, `HasKernels` and `HasFiniteProducts` are then
forced to come from those `Abelian` instances, which is what
`CategoryTheory.Functor.preservesHomology_of_preservesMonos_and_cokernels` and
`CategoryTheory.Functor.preservesFiniteLimits_of_preservesHomology` must agree on. The conclusion
`PreservesFiniteLimits` carries no such data, so the lemma applies to a category whose `Abelian`
instance is opaque. -/
public theorem preservesFiniteLimits_of_preservesMonos_of_rightExact
    {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
    (L : A ⥤ B) [PreservesFiniteColimits L] [L.PreservesMonomorphisms] :
    PreservesFiniteLimits L := by
  have := L.preservesHomology_of_preservesMonos_and_cokernels
  have : PreservesBinaryBiproducts L := preservesBinaryBiproducts_of_preservesBinaryCoproducts L
  have : L.Additive := Functor.additive_of_preservesBinaryBiproducts L
  exact L.preservesFiniteLimits_of_preservesHomology

/-- **Stacks 0887: along a flat morphism the pullback functor on coherent adic systems is
exact.** -/
@[stacks 0887 "exactness when f is flat"]
public theorem coherentAdicPullback_exact {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) (J : Y.IdealSheafData) [Flat f] :
    exactFunctor _ _ (coherentAdicPullback f J) := by
  rw [exactFunctor_iff]
  have hcolim : PreservesFiniteColimits (coherentAdicPullback f J) :=
    (rightExactFunctor_iff _).mp (coherentAdicPullback_rightExact f J)
  have _ := coherentAdicPullback_preservesMonomorphisms f J
  exact ⟨preservesFiniteLimits_of_preservesMonos_of_rightExact _, hcolim⟩

/-! ### Pullback and annihilation by a power of the ideal sheaf -/

/-- **Pullback carries annihilation by `𝒥 ⁿ` to annihilation by `ℐ ⁿ` for `ℐ = f^{-1}𝒥 𝒪_X`.**
No flatness is needed, and the exponent is unchanged.

The subsheaf `𝒥 ⁿ M` is zero exactly when its inclusion is the zero morphism, by
`Stacks.Algebraization.submodule_ι_eq_zero_iff`, and
`Stacks.Algebraization.pullback_idealPowerMultiple_comp_eq_zero_iff` applied to the identity of
`f^*M` identifies the vanishing of the pullback of that inclusion with the vanishing of the
inclusion of `ℐ ⁿ (f^*M)`. -/
public theorem idealPowerMultiple_eq_bot_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    (J : Y.IdealSheafData) (n : ℕ) (M : Y.Modules)
    (hM : idealPowerMultiple J n M = ⊥) :
    idealPowerMultiple (J.comap f) n ((Scheme.Modules.pullback f).obj M) = ⊥ := by
  exact idealPowerMultiple_eq_bot_map (Scheme.Modules.pullback f) J (J.comap f) n M
    (fun φ => pullback_idealPowerMultiple_comp_eq_zero_iff f J n M φ) hM

/-- **Along a flat morphism, termwise pullback preserves the hypothesis of Tag 0888 (1).** If the
levelwise kernels and cokernels of a morphism `α` of inverse systems of `𝒪_Y`-modules are
annihilated by `𝒥 ᵗ`, then those of its termwise pullback are annihilated by `ℐ ᵗ` for the same
exponent `t` and `ℐ = f^{-1}𝒥 𝒪_X`.

Flatness makes pullback preserve the levelwise kernels, and it preserves the levelwise cokernels
because it is a left adjoint; `Stacks.Coherent.idealPowerMultiple_eq_bot_pullback` carries the
annihilation of each across, and
`Stacks.Algebraization.idealPowerMultiple_eq_bot_of_iso` transports it along the comparison
isomorphism. -/
public theorem isKernelCokernelAnnihilatedByPower_whiskerRight_pullback {X Y : Scheme.{u}}
    (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData) {F G : ℕᵒᵖ ⥤ Y.Modules} (α : F ⟶ G)
    (hα : IsKernelCokernelAnnihilatedByPower J α) :
    IsKernelCokernelAnnihilatedByPower (J.comap f)
      (Functor.whiskerRight α (Scheme.Modules.pullback f)) := by
  obtain ⟨t, ht, h⟩ := hα
  have _ : PreservesFiniteLimits (Scheme.Modules.pullback f) :=
    AlgebraicGeometry.preservesFiniteLimits_modulesPullback_of_flat f
  have _ : PreservesColimits (Scheme.Modules.pullback f) :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).leftAdjoint_preservesColimits
  refine ⟨t, ht, fun k => ⟨?_, ?_⟩⟩
  · exact idealPowerMultiple_eq_bot_of_iso (J.comap f)
      (PreservesKernel.iso (Scheme.Modules.pullback f) (α.app (op k))).symm t
      (idealPowerMultiple_eq_bot_pullback f J t _ (h k).1)
  · exact idealPowerMultiple_eq_bot_of_iso (J.comap f)
      (PreservesCokernel.iso (Scheme.Modules.pullback f) (α.app (op k))).symm t
      (idealPowerMultiple_eq_bot_pullback f J t _ (h k).2)

/-- **The functor `f^*` of Tag 0887 preserves the hypothesis of Tag 0888 (1) when `f` is flat.**
This is `Stacks.Coherent.isKernelCokernelAnnihilatedByPower_whiskerRight_pullback` read through
`Stacks.Coherent.coherentAdicPullback_map_hom_app`: the pullback functor on coherent adic systems
acts on morphisms by termwise pullback. -/
public theorem isKernelCokernelAnnihilatedByPower_coherentAdicPullback_map {X Y : Scheme.{u}}
    [IsNoetherian X] [IsNoetherian Y] (f : X ⟶ Y) [Flat f] (J : Y.IdealSheafData)
    {F G : CoherentAdicSystems J} (α : F ⟶ G)
    (hα : IsKernelCokernelAnnihilatedByPower J α.hom) :
    IsKernelCokernelAnnihilatedByPower (J.comap f) ((coherentAdicPullback f J).map α).hom :=
  isKernelCokernelAnnihilatedByPower_whiskerRight_pullback f J α.hom hα

end Stacks.Coherent

end
