module

public import Mathlib.Algebra.Category.Ring.Under.Property
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.RingTheory.RingHom.Smooth
public import StacksFrontier.RingTheory.MilnorPatching.RelativeProperties
public import StacksFrontier.RingTheory.Localization.Glueing.CategoricalPullback
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Algebras over a fibre product of rings

An algebraic system over a fibre product `B' = B ×_A A'` is an algebra `D` over `B`, an algebra
`C'` over `A'`, and an identification of their base changes to `A`.  The fibre product
`D ×_C C'` is then an algebra over `B'`, and it is of finite type, flat, of finite presentation,
smooth, or étale exactly when both `D` and `C'` are.  Flat algebras are moreover canonically
recovered from their two base changes, so the flat algebras over `B'` are equivalent to the
compatible systems of flat algebras.

## Main definitions

* `MilnorPatching.ringPushout` expresses that a square of rings in independent universes is a
  pushout.

## Main results

* `MilnorPatching.ringHom_properties_pullback_iff_and_reconstruction` collects the five
  ring-map comparisons together with canonical reconstruction of a flat algebra.
* `MilnorPatching.flatAlgebrasOverFibreProduct_equivalence` isolates the categorical statement.
* `MilnorPatching.ringHom_properties_pullback_iff_and_flatAlgebra_equivalence` is Stacks Tag
  08KQ: the five comparisons, canonical reconstruction, and the induced equivalence of
  flat-algebra categories, as stated in the source.

## Implementation notes

The common algebra `C` is pinned down by two pushout squares, saying that it is the base change
of `D` from `B` to `A` and the base change of `C'` from `A'` to `A`, the latter being the
quotient `C' / I C'`.  `MilnorPatching.ringPushout` lifts the rings into a common universe so
that `D`, `C'` and `C` may have independent universes.  The categorical statement is phrased with
under-categories of flat ring maps, and its two displayed natural isomorphisms record that the
equivalence is the one induced by the canonical base-change functors.

## References

* [Stacks Project, Tag 08KQ](https://stacks.math.columbia.edu/tag/08KQ)
-/

section

open CategoryTheory CategoryTheory.Limits
open ModuleGlueing

universe u v w x z

namespace MilnorPatching
open ModuleGlueing

-- The vertex of the cartesian square of a ring fibre product has to be identified with the
-- subring `RingHom.pullback`, and instance search will not unfold the cone to do it. This is
-- what makes `backward.isDefEq.respectTransparency` unnecessary below.
attribute [local implicit_reducible] CommRingCat.pullbackCone

/-- A pushout square of commutative rings whose four rings may live in different
universes. Lifting all four rings into a common universe recovers the usual categorical
pushout condition. -/
@[expose] public def ringPushout
    {R : Type u} {S : Type v} {T : Type w} {U : Type x}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : R →+* T) (h : S →+* U) (i : T →+* U) : Prop :=
  IsPushout
    (CommRingCat.ofHom (f.ulift.{max u v w x, max u v w x}))
    (CommRingCat.ofHom (g.ulift.{max u v w x, max u v w x}))
    (CommRingCat.ofHom (h.ulift.{max u v w x, max u v w x}))
    (CommRingCat.ofHom (i.ulift.{max u v w x, max u v w x}))

/-- An ordinary pushout square of commutative rings gives a `ringPushout` square.
The rings share a universe because the input square lies in one `CommRingCat`. -/
public theorem ringPushout_of_isPushout
    {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : R →+* T) (h : S →+* U) (i : T →+* U)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom h) (CommRingCat.ofHom i)) : ringPushout f g h i := by
  unfold ringPushout
  apply sq.of_iso ULift.ringEquiv.symm.toCommRingCatIso
    ULift.ringEquiv.symm.toCommRingCatIso ULift.ringEquiv.symm.toCommRingCatIso
    ULift.ringEquiv.symm.toCommRingCatIso
  all_goals
    ext r
    rfl

/-- The square of a `ringPushout` commutes. -/
public theorem ringPushout_comm
    {R : Type u} {S : Type v} {T : Type w} {U : Type x}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    {f : R →+* S} {g : R →+* T} {h : S →+* U} {i : T →+* U}
    (sq : ringPushout f g h i) : h.comp f = i.comp g := by
  apply RingHom.ext
  intro r
  have hh := congrArg CommRingCat.Hom.hom sq.w
  have hr := DFunLike.congr_fun hh (ULift.up r)
  simpa [RingHom.ulift_apply] using hr

section FlatAlgebraGluing

open scoped TensorProduct ChangeOfRings

-- Reduce the property-restricted pushout functors locally so that their underlying
-- ring objects agree during the categorical compatibility calculations.
set_option allowUnsafeReducibility true in
attribute [local reducible] MorphismProperty.Under.pushout MorphismProperty.Under.mk

/-- The module of compatible pairs of a compatible pair of flat modules over the two factors of
a ring fibre product is flat over the fibre product. -/
public theorem flat_compatiblePairs
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    (X : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
      (ModuleCat.extendScalars.{u, u, u} surjection))
    (hX : Module.Flat B X.fst ∧ Module.Flat A' X.snd) :
    Module.Flat base.fibreProduct
      (compatiblePairsModule base.pullbackCone.fst.hom
        base.pullbackCone.snd.hom toBase surjection
        (RingHom.pullback_comm_sq toBase surjection) X) := by
  obtain ⟨F, e, adj, _, _⟩ :=
    exists_rightAdjoint_extensionOfScalarsToPullback
      base.pullbackCone.fst.hom base.pullbackCone.snd.hom toBase surjection
      (RingHom.pullback_comm_sq toBase surjection)
  obtain ⟨F₀, _, adj₀, _, _, hflat, _, _⟩ :=
    flatModulesEquivalenceOverFibreProduct toBase surjection I base
  have : Module.Flat base.fibreProduct (F₀.obj X) := hflat X hX
  have : Module.Flat base.fibreProduct (F.obj X) :=
    Module.Flat.of_linearEquiv ((adj.rightAdjointUniq adj₀).app X).toLinearEquiv
  exact Module.Flat.of_linearEquiv (e X).symm

/-- A pushout square of commutative rings presents its target as the base change of the
left-hand ring along the bottom map. -/
@[expose] public noncomputable def pushoutLinearEquiv
    {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : R →+* T) (h : S →+* U) (i : T →+* U)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom h) (CommRingCat.ofHom i)) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R T := g.toAlgebra
    letI : Algebra T U := i.toAlgebra
    T ⊗[R] S ≃ₗ[T] U := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R T := g.toAlgebra
  letI : Algebra T U := i.toAlgebra
  letI : Algebra S U := h.toAlgebra
  letI : Algebra R U := (i.comp g).toAlgebra
  have hc : h.comp f = i.comp g := congrArg CommRingCat.Hom.hom sq.w
  letI : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' hc.symm
  haveI : Algebra.IsPushout R T S U := CommRingCat.isPushout_iff_isPushout.mp sq.flip
  exact (Algebra.IsPushout.equiv R T S U).toLinearEquiv

/-- The base-change equivalence of a pushout square of rings sends `t ⊗ s` to the product of the
images of `t` and `s` in the target. -/
public theorem pushoutLinearEquiv_tmul
    {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : R →+* T) (h : S →+* U) (i : T →+* U)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom h) (CommRingCat.ofHom i)) (t : T) (s : S) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R T := g.toAlgebra
    letI : Algebra T U := i.toAlgebra
    pushoutLinearEquiv f g h i sq (t ⊗ₜ[R] s) = i t * h s := by
  simp only [pushoutLinearEquiv, AlgEquiv.toLinearEquiv_apply, Algebra.IsPushout.equiv_tmul]
  rfl

/-- The compatible system of modules `(D, C')` attached to two pushout squares over `toBase` and
`surjection`. -/
private noncomputable def pushoutCompatibleSystem
    {A A' B D C' C : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D] [CommRing C'] [CommRing C]
    (toBase : B →+* A) (surjection : A' →+* A)
    (BtoD : B →+* D) (A'toC' : A' →+* C') (AtoC : A →+* C)
    (DtoC : D →+* C) (C'toC : C' →+* C)
    (hD : IsPushout (CommRingCat.ofHom BtoD) (CommRingCat.ofHom toBase)
      (CommRingCat.ofHom DtoC) (CommRingCat.ofHom AtoC))
    (hC' : IsPushout (CommRingCat.ofHom A'toC') (CommRingCat.ofHom surjection)
      (CommRingCat.ofHom C'toC) (CommRingCat.ofHom AtoC)) :
    CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
      (ModuleCat.extendScalars.{u, u, u} surjection) :=
  letI : Algebra B D := BtoD.toAlgebra
  letI : Algebra A' C' := A'toC'.toAlgebra
  letI : Algebra A C := AtoC.toAlgebra
  letI : Algebra B A := toBase.toAlgebra
  letI : Algebra A' A := surjection.toAlgebra
  { fst := ModuleCat.of B D
    snd := ModuleCat.of A' C'
    iso := ((pushoutLinearEquiv BtoD toBase DtoC AtoC hD).trans
      (pushoutLinearEquiv A'toC' surjection C'toC AtoC hC').symm).toModuleIso }

/-- The fibre product `D ×_C C'` is, as a module over the fibre product `B ×_A A'`, the module of
compatible pairs of the system `(D, C')`. -/
private noncomputable def pullbackLinearEquivCompatiblePairs
    {A A' B D C' C : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D] [CommRing C'] [CommRing C]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    (BtoD : B →+* D) (A'toC' : A' →+* C') (AtoC : A →+* C)
    (DtoC : D →+* C) (C'toC : C' →+* C)
    (hD : IsPushout (CommRingCat.ofHom BtoD) (CommRingCat.ofHom toBase)
      (CommRingCat.ofHom DtoC) (CommRingCat.ofHom AtoC))
    (hC' : IsPushout (CommRingCat.ofHom A'toC') (CommRingCat.ofHom surjection)
      (CommRingCat.ofHom C'toC) (CommRingCat.ofHom AtoC))
    (f : base.fibreProduct →+* RingHom.pullback DtoC C'toC)
    (hf₁ : ∀ r, (f r).1.1 = BtoD (base.pullbackCone.fst.hom r))
    (hf₂ : ∀ r, (f r).1.2 = A'toC' (base.pullbackCone.snd.hom r)) :
    letI : Algebra base.fibreProduct (RingHom.pullback DtoC C'toC) := f.toAlgebra
    RingHom.pullback DtoC C'toC ≃ₗ[base.fibreProduct]
      compatiblePairsModule base.pullbackCone.fst.hom
        base.pullbackCone.snd.hom toBase surjection
        (RingHom.pullback_comm_sq toBase surjection)
        (pushoutCompatibleSystem toBase surjection BtoD A'toC' AtoC DtoC C'toC hD hC') := by
  letI : Algebra base.fibreProduct (RingHom.pullback DtoC C'toC) := f.toAlgebra
  let : Algebra B D := BtoD.toAlgebra
  let : Algebra A' C' := A'toC'.toAlgebra
  let : Algebra A C := AtoC.toAlgebra
  let : Algebra B A := toBase.toAlgebra
  let : Algebra A' A := surjection.toAlgebra
  let eD := pushoutLinearEquiv BtoD toBase DtoC AtoC hD
  let eC' := pushoutLinearEquiv A'toC' surjection C'toC AtoC hC'
  have hcompat (d : D) (c : C') :
      (pushoutCompatibleSystem toBase surjection BtoD A'toC' AtoC DtoC C'toC hD hC').iso.hom
          ((1 : A) ⊗ₜ[B,toBase] d) = (1 : A) ⊗ₜ[A',surjection] c ↔
        DtoC d = C'toC c := by
    change eC'.symm (eD ((1 : A) ⊗ₜ[B] d)) = (1 : A) ⊗ₜ[A'] c ↔ _
    rw [LinearEquiv.symm_apply_eq]
    simp only [eD, eC', pushoutLinearEquiv_tmul, map_one, one_mul]
  exact
    { toFun := fun p => ⟨p.1, (hcompat _ _).mpr p.2⟩
      invFun := fun p => ⟨p.1, (hcompat _ _).mp p.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro r p
        apply Subtype.ext
        apply Prod.ext
        · change (f r).1.1 * p.1.1 = BtoD (base.pullbackCone.fst.hom r) * p.1.1
          rw [hf₁]
        · change (f r).1.2 * p.1.2 = A'toC' (base.pullbackCone.snd.hom r) * p.1.2
          rw [hf₂] }

/-- **Milnor patching, flatness.** The fibre product `D ×_C C'` of two flat algebras over the two
factors of a ring fibre product `B ×_A A'` is flat over `B ×_A A'`. -/
public theorem pullback_flat_of_components
    {A A' B D C' C : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D] [CommRing C'] [CommRing C]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    (BtoD : B →+* D) (A'toC' : A' →+* C') (AtoC : A →+* C)
    (DtoC : D →+* C) (C'toC : C' →+* C)
    (hD : IsPushout (CommRingCat.ofHom BtoD) (CommRingCat.ofHom toBase)
      (CommRingCat.ofHom DtoC) (CommRingCat.ofHom AtoC))
    (hC' : IsPushout (CommRingCat.ofHom A'toC') (CommRingCat.ofHom surjection)
      (CommRingCat.ofHom C'toC) (CommRingCat.ofHom AtoC))
    (f : base.fibreProduct →+* RingHom.pullback DtoC C'toC)
    (hf₁ : ∀ r, (f r).1.1 = BtoD (base.pullbackCone.fst.hom r))
    (hf₂ : ∀ r, (f r).1.2 = A'toC' (base.pullbackCone.snd.hom r))
    (hflatD : BtoD.Flat) (hflatC' : A'toC'.Flat) : f.Flat := by
  let : Algebra B D := BtoD.toAlgebra
  let : Algebra A' C' := A'toC'.toAlgebra
  let : Algebra base.fibreProduct (RingHom.pullback DtoC C'toC) := f.toAlgebra
  let X := pushoutCompatibleSystem toBase surjection BtoD A'toC' AtoC DtoC C'toC hD hC'
  have : Module.Flat base.fibreProduct
      (compatiblePairsModule base.pullbackCone.fst.hom base.pullbackCone.snd.hom toBase surjection
        (RingHom.pullback_comm_sq toBase surjection) X) :=
    flat_compatiblePairs base X ⟨hflatD, hflatC'⟩
  exact Module.Flat.of_linearEquiv
    (pullbackLinearEquivCompatiblePairs base BtoD A'toC' AtoC DtoC C'toC hD hC' f hf₁ hf₂)

/-- A module over the fibre product whose two scalar extensions realize a compatible pair has
both of the realizing maps bijective. -/
public theorem compatiblePairs_baseChange_bijective
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    (X : CategoricalPullback (ModuleCat.extendScalars.{u, u, u} toBase)
      (ModuleCat.extendScalars.{u, u, u} surjection))
    (L : ModuleCat.{u} base.fibreProduct)
    (eL : L ≃ₗ[base.fibreProduct]
      compatiblePairsModule base.pullbackCone.fst.hom
        base.pullbackCone.snd.hom toBase surjection
        (RingHom.pullback_comm_sq toBase surjection) X)
    (d₁ : (ModuleCat.extendScalars base.pullbackCone.fst.hom).obj L ⟶ X.fst)
    (d₂ : (ModuleCat.extendScalars base.pullbackCone.snd.hom).obj L ⟶ X.snd)
    (h₁ : ∀ l, d₁ ((1 : B) ⊗ₜ[base.fibreProduct,base.pullbackCone.fst.hom] l) =
      (eL l).1.1)
    (h₂ : ∀ l, d₂ ((1 : A') ⊗ₜ[base.fibreProduct,base.pullbackCone.snd.hom] l) =
      (eL l).1.2) :
    Function.Bijective d₁ ∧ Function.Bijective d₂ := by
  obtain ⟨F, e, adj, _, he⟩ :=
    exists_rightAdjoint_extensionOfScalarsToPullback
      base.pullbackCone.fst.hom base.pullbackCone.snd.hom toBase surjection
      (RingHom.pullback_comm_sq toBase surjection)
  obtain ⟨F₀, _, adj₀, _, hc⟩ :=
    compatiblePairsRightAdjoint_counit_isIso toBase surjection I base
  let E := extensionOfScalarsToPullback
    base.pullbackCone.fst.hom base.pullbackCone.snd.hom toBase surjection
    (RingHom.pullback_comm_sq toBase surjection)
  have : IsIso adj₀.counit := hc
  have hcomp := adj₀.rightAdjointUniq_hom_app_counit adj X
  have : IsIso (adj.counit.app X) := by
    apply (isIso_comp_left_iff (E.map ((adj₀.rightAdjointUniq adj).hom.app X)) _).mp
    rw [hcomp]
    infer_instance
  let e' : L ≃ₗ[base.fibreProduct] F.obj X := eL ≪≫ₗ (e X).symm
  let i : L ⟶ F.obj X := ModuleCat.ofHom e'.toLinearMap
  have : IsIso i := e'.toModuleIso.isIso_hom
  let d := (adj.homEquiv L X).symm i
  have hd : d = E.map i ≫ adj.counit.app X := adj.homEquiv_counit L X i
  have : IsIso d := by rw [hd]; infer_instance
  have hcoord (l : L) :
      d.fst ((1 : B) ⊗ₜ[base.fibreProduct,base.pullbackCone.fst.hom] l) = (eL l).1.1 ∧
      d.snd ((1 : A') ⊗ₜ[base.fibreProduct,base.pullbackCone.snd.hom] l) = (eL l).1.2 := by
    have hh := he L X i l
    have hi : e X (i l) = eL l := (e X).apply_symm_apply _
    exact ⟨hh.1.symm.trans (congrArg (fun p => p.1.1) hi),
      hh.2.symm.trans (congrArg (fun p => p.1.2) hi)⟩
  have hd₁ : d₁ = d.fst := by
    apply (ModuleCat.extendRestrictScalarsAdj base.pullbackCone.fst.hom).homEquiv _ _ |>.injective
    ext l
    exact (h₁ l).trans (hcoord l).1.symm
  have hd₂ : d₂ = d.snd := by
    apply (ModuleCat.extendRestrictScalarsAdj base.pullbackCone.snd.hom).homEquiv _ _ |>.injective
    ext l
    exact (h₂ l).trans (hcoord l).2.symm
  rw [hd₁, hd₂]
  exact ⟨ConcreteCategory.bijective_of_isIso d.fst, ConcreteCategory.bijective_of_isIso d.snd⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Milnor patching, base change.** The fibre product of two algebras that become each other's
base changes over the base of a ring fibre product is itself the base change of each of them. -/
public theorem pullback_baseChange
    {A A' B D C' C : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D] [CommRing C'] [CommRing C]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    (BtoD : B →+* D) (A'toC' : A' →+* C') (AtoC : A →+* C)
    (DtoC : D →+* C) (C'toC : C' →+* C)
    (hD : IsPushout (CommRingCat.ofHom BtoD) (CommRingCat.ofHom toBase)
      (CommRingCat.ofHom DtoC) (CommRingCat.ofHom AtoC))
    (hC' : IsPushout (CommRingCat.ofHom A'toC') (CommRingCat.ofHom surjection)
      (CommRingCat.ofHom C'toC) (CommRingCat.ofHom AtoC))
    (f : base.fibreProduct →+* RingHom.pullback DtoC C'toC)
    (hf₁ : ∀ r, (f r).1.1 = BtoD (base.pullbackCone.fst.hom r))
    (hf₂ : ∀ r, (f r).1.2 = A'toC' (base.pullbackCone.snd.hom r)) :
    IsPushout (CommRingCat.ofHom f) base.pullbackCone.fst
        (CommRingCat.ofHom (DtoC.pullbackFst C'toC)) (CommRingCat.ofHom BtoD) ∧
      IsPushout (CommRingCat.ofHom f) base.pullbackCone.snd
        (CommRingCat.ofHom (DtoC.pullbackSnd C'toC)) (CommRingCat.ofHom A'toC') := by
  let R := base.fibreProduct
  let P := RingHom.pullback DtoC C'toC
  let : Algebra B D := BtoD.toAlgebra
  let : Algebra A' C' := A'toC'.toAlgebra
  let : Algebra A C := AtoC.toAlgebra
  let : Algebra B A := toBase.toAlgebra
  let : Algebra A' A := surjection.toAlgebra
  let : Algebra R P := f.toAlgebra
  let : Algebra R B := base.pullbackCone.fst.hom.toAlgebra
  let : Algebra R A' := base.pullbackCone.snd.hom.toAlgebra
  let : Algebra R D := (BtoD.comp base.pullbackCone.fst.hom).toAlgebra
  let : Algebra R C' := (A'toC'.comp base.pullbackCone.snd.hom).toAlgebra
  let : Algebra P D := (DtoC.pullbackFst C'toC).toAlgebra
  let : Algebra P C' := (DtoC.pullbackSnd C'toC).toAlgebra
  let : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R A' C' := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R P D := IsScalarTower.of_algebraMap_eq (fun r => (hf₁ r).symm)
  let : IsScalarTower R P C' := IsScalarTower.of_algebraMap_eq (fun r => (hf₂ r).symm)
  let X := pushoutCompatibleSystem toBase surjection BtoD A'toC' AtoC DtoC C'toC hD hC'
  let e := pullbackLinearEquivCompatiblePairs base BtoD A'toC' AtoC DtoC C'toC hD hC' f hf₁ hf₂
  let d₁ := AlgHom.liftEquiv R B P D (IsScalarTower.toAlgHom R P D)
  let d₂ := AlgHom.liftEquiv R A' P C' (IsScalarTower.toAlgHom R P C')
  have hh := compatiblePairs_baseChange_bijective base X (ModuleCat.of R P) e
    (ModuleCat.ofHom d₁.toLinearMap) (ModuleCat.ofHom d₂.toLinearMap)
    (fun p => by change (1 : B) • p.1.1 = p.1.1; simp)
    (fun p => by change (1 : A') • p.1.2 = p.1.2; simp)
  constructor
  · have : Algebra.IsPushout R B P D := ⟨IsBaseChange.of_equiv
      (AlgEquiv.ofBijective d₁ hh.1).toLinearEquiv (fun p => by
        change (1 : B) • p.1.1 = p.1.1; simp)⟩
    exact (CommRingCat.isPushout_of_isPushout R B P D).flip
  · have : Algebra.IsPushout R A' P C' := ⟨IsBaseChange.of_equiv
      (AlgEquiv.ofBijective d₂ hh.2).toLinearEquiv (fun p => by
        change (1 : A') • p.1.2 = p.1.2; simp)⟩
    exact (CommRingCat.isPushout_of_isPushout R A' P C').flip

private noncomputable abbrev flatComparison
    {R B A' A : CommRingCat.{u}} (toB : R ⟶ B) (toA' : R ⟶ A')
    (toBase : B ⟶ A) (surjection : A' ⟶ A)
    (comm : toB ≫ toBase = toA' ≫ surjection) :
    CommRingCat.flat.Under ⊤ R ⥤ CategoricalPullback
      (MorphismProperty.Under.pushout CommRingCat.flat ⊤ toBase)
      (MorphismProperty.Under.pushout CommRingCat.flat ⊤ surjection) :=
  let L := MorphismProperty.Under.pushout CommRingCat.flat ⊤ toB
  let M := MorphismProperty.Under.pushout CommRingCat.flat ⊤ toA'
  let α := (MorphismProperty.Under.pushoutComp (P := CommRingCat.flat) (Q := ⊤)
      toB toBase).symm ≪≫
    MorphismProperty.Under.pushoutCongr (P := CommRingCat.flat) (Q := ⊤) comm ≪≫
    MorphismProperty.Under.pushoutComp (P := CommRingCat.flat) (Q := ⊤) toA' surjection
  { obj := fun X => { fst := L.obj X, snd := M.obj X, iso := α.app X }
    map := fun f => { fst := L.map f, snd := M.map f, w := α.hom.naturality f }
    map_id := by intro X; ext <;> simp
    map_comp := by intro X Y Z f g; ext <;> simp }

set_option backward.isDefEq.respectTransparency false in
private theorem flatComparison_mkIso
    {R B A' A : CommRingCat.{u}} (toB : R ⟶ B) (toA' : R ⟶ A')
    (toBase : B ⟶ A) (surjection : A' ⟶ A)
    (comm : toB ≫ toBase = toA' ≫ surjection)
    (X : CommRingCat.flat.Under ⊤ R)
    (Y : CategoricalPullback
      (MorphismProperty.Under.pushout CommRingCat.flat ⊤ toBase)
      (MorphismProperty.Under.pushout CommRingCat.flat ⊤ surjection))
    (i₁ : ((flatComparison toB toA' toBase surjection comm).obj X).fst ≅ Y.fst)
    (i₂ : ((flatComparison toB toA' toBase surjection comm).obj X).snd ≅ Y.snd)
    (h : pushout.inl X.hom toB ≫ i₁.hom.right ≫ pushout.inl Y.fst.hom toBase ≫
        Y.iso.hom.right =
      pushout.inl X.hom toA' ≫ i₂.hom.right ≫ pushout.inl Y.snd.hom surjection) :
    Nonempty ((flatComparison toB toA' toBase surjection comm).obj X ≅ Y) := by
  refine ⟨CategoricalPullback.mkIso i₁ i₂ ?_⟩
  apply MorphismProperty.Under.Hom.ext
  apply pushout.hom_ext
  · dsimp [flatComparison, MorphismProperty.Under.pushout]
    simp only [Category.assoc]
    apply pushout.hom_ext
    · simpa [Category.assoc, MorphismProperty.Under.pushoutCongr] using h
    · simp only [MorphismProperty.Under.homMk_hom, Under.homMk_right, colimit.ι_desc_assoc,
        span_left, PushoutCocone.mk_ι_app, Category.assoc,
        MorphismProperty.Under.pushoutComp_inv_app_right, pushout.map_id, Category.comp_id,
        MorphismProperty.Under.pushoutCongr, Functor.const_obj_obj, Functor.id_obj,
        NatIso.ofComponents_hom_app, MorphismProperty.Under.isoMk_hom_right, pushout.congrHom_hom,
        MorphismProperty.Under.pushoutComp_hom_app_right, Category.id_comp,
        inr_inl_pushoutLeftPushoutInrIso_hom_assoc, span_right,
        inr_pushoutLeftPushoutInrIso_inv_assoc, colimit.ι_desc]
      rw [← Category.assoc, ← Category.assoc, MorphismProperty.Under.w i₁.hom,
        pushout.condition, Category.assoc, MorphismProperty.Under.w Y.iso.hom]
  · exact (MorphismProperty.Under.w
        ((MorphismProperty.Under.pushout CommRingCat.flat ⊤ toBase).map i₁.hom ≫ Y.iso.hom)).trans
      (MorphismProperty.Under.w
        (((flatComparison toB toA' toBase surjection comm).obj X).iso.hom ≫
        (MorphismProperty.Under.pushout CommRingCat.flat ⊤ surjection).map i₂.hom)).symm

set_option backward.isDefEq.respectTransparency false in
private theorem flatComparison_essSurj
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I) :
    (flatComparison base.pullbackCone.fst base.pullbackCone.snd
      (CommRingCat.ofHom toBase) (CommRingCat.ofHom surjection)
      base.pullbackCone.condition).EssSurj where
  mem_essImage X := by
    let H := MorphismProperty.Under.pushout CommRingCat.flat ⊤ (CommRingCat.ofHom toBase)
    let K := MorphismProperty.Under.pushout CommRingCat.flat ⊤ (CommRingCat.ofHom surjection)
    let D := X.fst.right
    let C' := X.snd.right
    let C := (K.obj X.snd).right
    let BtoD : B →+* D := X.fst.hom.hom
    let A'toC' : A' →+* C' := X.snd.hom.hom
    let AtoC : A →+* C := (K.obj X.snd).hom.hom
    let DtoC : D →+* C :=
      (pushout.inl X.fst.hom (CommRingCat.ofHom toBase) ≫ X.iso.hom.right).hom
    let C'toC : C' →+* C := (pushout.inl X.snd.hom (CommRingCat.ofHom surjection)).hom
    have hD : IsPushout (CommRingCat.ofHom BtoD) (CommRingCat.ofHom toBase)
        (CommRingCat.ofHom DtoC) (CommRingCat.ofHom AtoC) := by
      let i : (H.obj X.fst).right ≅ (K.obj X.snd).right :=
        (MorphismProperty.Under.forget CommRingCat.flat ⊤ (CommRingCat.of A) ⋙
          CategoryTheory.Under.forget _).mapIso X.iso
      exact (IsPushout.of_hasPushout X.fst.hom (CommRingCat.ofHom toBase)).of_iso
        (Iso.refl _) (Iso.refl _) (Iso.refl _) i
        (by simp [BtoD]) (by simp) (by simp [i, DtoC])
        (by simpa [i, AtoC, K] using MorphismProperty.Under.w X.iso.hom)
    have hC' : IsPushout (CommRingCat.ofHom A'toC') (CommRingCat.ofHom surjection)
        (CommRingCat.ofHom C'toC) (CommRingCat.ofHom AtoC) :=
      IsPushout.of_hasPushout X.snd.hom (CommRingCat.ofHom surjection)
    let f : base.fibreProduct →+* RingHom.pullback DtoC C'toC :=
      RingHom.codRestrict
        ((BtoD.comp base.pullbackCone.fst.hom).prod
          (A'toC'.comp base.pullbackCone.snd.hom)) _ (fun r => by
            change DtoC (BtoD (base.pullbackCone.fst.hom r)) =
              C'toC (A'toC' (base.pullbackCone.snd.hom r))
            have hd := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hD.w)
              (base.pullbackCone.fst.hom r)
            have hc := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hC'.w)
              (base.pullbackCone.snd.hom r)
            exact hd.trans ((congrArg AtoC r.2).trans hc.symm))
    have hf : f.Flat := pullback_flat_of_components base BtoD A'toC' AtoC DtoC C'toC
      hD hC' f (fun _ => rfl) (fun _ => rfl) X.fst.prop X.snd.prop
    let Y : CommRingCat.flat.Under ⊤ base.pullbackCone.pt :=
      MorphismProperty.Under.mk ⊤ (CommRingCat.ofHom f) hf
    obtain ⟨h₁, h₂⟩ := pullback_baseChange base BtoD A'toC' AtoC DtoC C'toC
      hD hC' f (fun _ => rfl) (fun _ => rfl)
    let E := flatComparison base.pullbackCone.fst base.pullbackCone.snd
      (CommRingCat.ofHom toBase) (CommRingCat.ofHom surjection)
      base.pullbackCone.condition
    let i₁ : (E.obj Y).fst ≅ X.fst :=
      MorphismProperty.Under.isoMk h₁.isoPushout.symm h₁.inr_isoPushout_inv
    let i₂ : (E.obj Y).snd ≅ X.snd :=
      MorphismProperty.Under.isoMk h₂.isoPushout.symm h₂.inr_isoPushout_inv
    refine ⟨Y, flatComparison_mkIso _ _ _ _ _ Y X i₁ i₂ ?_⟩
    change (pushout.inl _ _ ≫ h₁.isoPushout.inv) ≫
        pushout.inl X.fst.hom (CommRingCat.ofHom toBase) ≫ X.iso.hom.right =
      (pushout.inl _ _ ≫ h₂.isoPushout.inv) ≫
        pushout.inl X.snd.hom (CommRingCat.ofHom surjection)
    rw [h₁.inl_isoPushout_inv, h₂.inl_isoPushout_inv]
    ext p
    exact p.2

/-- Base change along a flat ring map preserves the cartesian square of a ring fibre product,
given that the two base changes sit in pushout squares over the original two maps. -/
public theorem flat_baseChange_pullback
    {R B A' A E D C' C : CommRingCat.{u}}
    {toB : R ⟶ B} {toA' : R ⟶ A'} {toBase : B ⟶ A} {surjection : A' ⟶ A}
    (base : IsPullback toB toA' toBase surjection)
    {f : R ⟶ E} (hf : f.hom.Flat)
    {eD : E ⟶ D} {eC' : E ⟶ C'} {BtoD : B ⟶ D} {A'toC' : A' ⟶ C'}
    {DtoC : D ⟶ C} {C'toC : C' ⟶ C} {AtoC : A ⟶ C}
    (h₁ : IsPushout f toB eD BtoD) (h₂ : IsPushout f toA' eC' A'toC')
    (hD : IsPushout BtoD toBase DtoC AtoC)
    (hC' : IsPushout A'toC' surjection C'toC AtoC)
    (comm : eD ≫ DtoC = eC' ≫ C'toC) : IsPullback eD eC' DtoC C'toC := by
  let r : Under R := Under.mk (𝟙 R)
  let b : Under R := Under.mk toB
  let a' : Under R := Under.mk toA'
  let a : Under R := Under.mk (toB ≫ toBase)
  let rb : r ⟶ b := Under.homMk toB (by simp [r, b])
  let ra' : r ⟶ a' := Under.homMk toA' (by simp [r, a'])
  let ba : b ⟶ a := Under.homMk toBase rfl
  let a'a : a' ⟶ a := Under.homMk surjection base.w.symm
  have hb : IsPullback rb ra' ba a'a :=
    IsPullback.of_map_of_faithful (Under.forget R) base
  let T := Under.pushout f ⋙ Under.forget E
  have : PreservesFiniteLimits (Under.pushout f) :=
    CommRingCat.Under.preservesFiniteLimits_of_flat f hf
  have ht := hb.map T
  have h₀ : IsPushout (𝟙 R) f f (𝟙 E) := IsPushout.of_id_fst
  have hA : IsPushout (toB ≫ toBase) f AtoC (eD ≫ DtoC) :=
    (h₁.paste_vert hD).flip
  apply ht.of_iso h₀.isoPushout.symm h₁.flip.isoPushout.symm
    h₂.flip.isoPushout.symm hA.isoPushout.symm
  · apply pushout.hom_ext <;>
      simp [T, rb, r, b, Under.pushout, Category.assoc, h₁.w,
        IsPushout.inl_isoPushout_inv, IsPushout.inr_isoPushout_inv]
  · apply pushout.hom_ext <;>
      simp [T, ra', r, a', Under.pushout, Category.assoc, h₂.w,
        IsPushout.inl_isoPushout_inv, IsPushout.inr_isoPushout_inv]
  · apply pushout.hom_ext <;>
      simp [T, ba, b, a, Under.pushout, Category.assoc, hD.w,
        IsPushout.inl_isoPushout_inv, IsPushout.inr_isoPushout_inv]
  · apply pushout.hom_ext <;>
      simp [T, a'a, a', a, Under.pushout, Category.assoc, hC'.w, comm,
        IsPushout.inl_isoPushout_inv, IsPushout.inr_isoPushout_inv]

set_option backward.isDefEq.respectTransparency false in
private theorem flatComparison_unit_pullback
    {R B A' A : CommRingCat.{u}} {toB : R ⟶ B} {toA' : R ⟶ A'}
    {toBase : B ⟶ A} {surjection : A' ⟶ A}
    (base : IsPullback toB toA' toBase surjection)
    (X : CommRingCat.flat.Under ⊤ R) :
    let F := flatComparison toB toA' toBase surjection base.w
    IsPullback (pushout.inl X.hom toB) (pushout.inl X.hom toA')
      (pushout.inl (pushout.inr X.hom toB) toBase ≫ (F.obj X).iso.hom.right)
      (pushout.inl (pushout.inr X.hom toA') surjection) := by
  let F := flatComparison toB toA' toBase surjection base.w
  have hD : IsPushout (pushout.inr X.hom toB) toBase
      (pushout.inl (pushout.inr X.hom toB) toBase ≫ (F.obj X).iso.hom.right)
      (pushout.inr (pushout.inr X.hom toA') surjection) := by
    let i := (MorphismProperty.Under.forget CommRingCat.flat ⊤ A ⋙
      Under.forget A).mapIso (F.obj X).iso
    exact (IsPushout.of_hasPushout (pushout.inr X.hom toB) toBase).of_iso
      (Iso.refl _) (Iso.refl _) (Iso.refl _) i
      (by simp) (by simp) (by simp [i])
      (MorphismProperty.Under.w (F.obj X).iso.hom)
  apply flat_baseChange_pullback base X.prop
    (IsPushout.of_hasPushout _ _) (IsPushout.of_hasPushout _ _)
    hD (IsPushout.of_hasPushout _ _)
  dsimp [F, flatComparison]
  simp [MorphismProperty.Under.pushoutCongr]

set_option backward.isDefEq.respectTransparency false in
private theorem flatComparison_full
    {R B A' A : CommRingCat.{u}} {toB : R ⟶ B} {toA' : R ⟶ A'}
    {toBase : B ⟶ A} {surjection : A' ⟶ A}
    (base : IsPullback toB toA' toBase surjection) :
    (flatComparison toB toA' toBase surjection base.w).Full where
  map_surjective {X Y} f := by
    let F := flatComparison toB toA' toBase surjection base.w
    let K := MorphismProperty.Under.pushout CommRingCat.flat ⊤ surjection
    let pX := flatComparison_unit_pullback base X
    let pY := flatComparison_unit_pullback base Y
    let a := pushout.inl X.hom toB ≫ f.fst.right
    let b := pushout.inl X.hom toA' ≫ f.snd.right
    have hc : a ≫ pushout.inl (pushout.inr Y.hom toB) toBase ≫ (F.obj Y).iso.hom.right =
        b ≫ pushout.inl (pushout.inr Y.hom toA') surjection := by
      have he := congrArg (fun h => pushout.inl X.hom toB ≫
        pushout.inl (pushout.inr X.hom toB) toBase ≫ h.right) f.w
      have hp := congrArg (fun h => h ≫ (K.map f.snd).right) pX.w
      simpa [F, a, b, K, Category.assoc, MorphismProperty.Under.pushout, MorphismProperty.Under.mk]
        using he.trans hp
    let g : X ⟶ Y := MorphismProperty.Under.homMk (pY.lift a b hc) (by
      apply pY.hom_ext
      · simp only [Category.assoc, IsPullback.lift_fst]
        dsimp [a]
        rw [← Category.assoc, pushout.condition, Category.assoc,
          MorphismProperty.Under.w f.fst, ← pushout.condition]
      · simp only [Category.assoc, IsPullback.lift_snd]
        dsimp [b]
        rw [← Category.assoc, pushout.condition, Category.assoc,
          MorphismProperty.Under.w f.snd, ← pushout.condition])
    refine ⟨g, ?_⟩
    apply CategoricalPullback.hom_ext
    · apply MorphismProperty.Under.Hom.ext
      apply pushout.hom_ext
      · simp [flatComparison, MorphismProperty.Under.pushout, g, a]
      · exact (MorphismProperty.Under.w
          (((MorphismProperty.Under.pushout CommRingCat.flat ⊤ toB).map g))).trans
          (MorphismProperty.Under.w f.fst).symm
    · apply MorphismProperty.Under.Hom.ext
      apply pushout.hom_ext
      · simp [flatComparison, MorphismProperty.Under.pushout, g, b]
      · exact (MorphismProperty.Under.w
          (((MorphismProperty.Under.pushout CommRingCat.flat ⊤ toA').map g))).trans
          (MorphismProperty.Under.w f.snd).symm

set_option backward.isDefEq.respectTransparency false in
private theorem flatComparison_faithful
    {R B A' A : CommRingCat.{u}} {toB : R ⟶ B} {toA' : R ⟶ A'}
    {toBase : B ⟶ A} {surjection : A' ⟶ A}
    (base : IsPullback toB toA' toBase surjection) :
    (flatComparison toB toA' toBase surjection base.w).Faithful where
  map_injective {X Y} f g h := by
    apply MorphismProperty.Under.Hom.ext
    apply (flatComparison_unit_pullback base Y).hom_ext
    · have hh := congrArg (fun h => pushout.inl X.hom toB ≫ h.fst.right) h
      simpa [flatComparison, MorphismProperty.Under.pushout, Category.assoc] using hh
    · have hh := congrArg (fun h => pushout.inl X.hom toA' ≫ h.snd.right) h
      simpa [flatComparison, MorphismProperty.Under.pushout, Category.assoc] using hh

/-- The algebra-level gluing step in Stacks Project, Tag 08KQ: flat algebras over a
fibre-product ring form the categorical pullback of the two flat-algebra base-change
functors. This assertion concerns algebra maps and their multiplication and unit; the
module equivalence of Tag 07RW alone does not supply it. -/
public theorem flatAlgebrasOverFibreProduct_equivalence
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    (toBase : B →+* A) (surjection : A' →+* A) (I : Ideal A')
    (base : RingFibreProduct.Situation toBase surjection I) :
    let toB : base.fibreProduct →+* B := base.pullbackCone.fst.hom
    let toA' : base.fibreProduct →+* A' := base.pullbackCone.snd.hom
    let flat := CommRingCat.flat
    let BtoA := MorphismProperty.Under.pushout flat ⊤ (CommRingCat.ofHom toBase)
    let A'toA := MorphismProperty.Under.pushout flat ⊤ (CommRingCat.ofHom surjection)
    let B'toB := MorphismProperty.Under.pushout flat ⊤ (CommRingCat.ofHom toB)
    let B'toA' := MorphismProperty.Under.pushout flat ⊤ (CommRingCat.ofHom toA')
    ∃ q : (flat.Under ⊤ (CommRingCat.of base.fibreProduct)) ≌
        CategoricalPullback BtoA A'toA,
      Nonempty (q.functor ⋙ CategoricalPullback.π₁ BtoA A'toA ≅ B'toB) ∧
        Nonempty (q.functor ⋙ CategoricalPullback.π₂ BtoA A'toA ≅ B'toA') := by
  have hp : IsPullback base.pullbackCone.fst base.pullbackCone.snd
      (CommRingCat.ofHom toBase) (CommRingCat.ofHom surjection) :=
    ⟨⟨base.pullbackCone.condition⟩, ⟨base.pullbackConeIsLimit⟩⟩
  let F := flatComparison base.pullbackCone.fst base.pullbackCone.snd
    (CommRingCat.ofHom toBase) (CommRingCat.ofHom surjection) base.pullbackCone.condition
  have : F.Full := flatComparison_full hp
  have : F.Faithful := flatComparison_faithful hp
  have : F.EssSurj := flatComparison_essSurj base
  have : F.IsEquivalence := { }
  exact ⟨F.asEquivalence, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩

end FlatAlgebraGluing

section RingPropertyDescent

open scoped TensorProduct ChangeOfRings

private theorem module_subsingleton_of_baseChange
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    (M : Type v) [AddCommGroup M] [Module base.fibreProduct M] :
    letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
    letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
    Subsingleton (B ⊗[base.fibreProduct] M) →
      Subsingleton (A' ⊗[base.fibreProduct] M) → Subsingleton M := by
  let R := base.fibreProduct
  let : Algebra R B := (toBase.pullbackFst surjection).toAlgebra
  let : Algebra R A' := (toBase.pullbackSnd surjection).toAlgebra
  intro hB hA'
  have := hB
  have := hA'
  have hj (j : RingHom.ker (toBase.pullbackFst surjection)) (m : M) : (j : R) • m = 0 := by
    have hj₁ : j.1.1.1 = 0 := j.2
    have hj₂ : surjection j.1.1.2 = 0 :=
      j.1.2.symm.trans ((congrArg toBase hj₁).trans (map_zero _))
    let l : A' →ₗ[R] R :=
      { toFun := fun a => ⟨(0, j.1.1.2 * a), by simp [hj₂]⟩
        map_add' := by
          intro a b
          apply Subtype.ext
          apply Prod.ext
          · change (0 : B) = 0 + 0; simp
          · change j.1.1.2 * (a + b) = j.1.1.2 * a + j.1.1.2 * b
            exact mul_add _ _ _
        map_smul' := by
          intro r a
          apply Subtype.ext
          apply Prod.ext
          · change (0 : B) = r.1.1 * 0; simp
          · change j.1.1.2 * (r.1.2 * a) = r.1.2 * (j.1.1.2 * a)
            ring }
    let g : A' ⊗[R] M →ₗ[R] M :=
      TensorProduct.lift ((LinearMap.lsmul R M).comp l)
    have hz : g ((1 : A') ⊗ₜ[R] m) = 0 := by
      rw [Subsingleton.elim ((1 : A') ⊗ₜ[R] m) 0, map_zero]
    have hl : l 1 = j := Subtype.ext (Prod.ext hj₁.symm (mul_one _))
    change l 1 • m = 0 at hz
    rwa [hl] at hz
  have hm (m : M) : m ∈ RingHom.ker (toBase.pullbackFst surjection) •
      (⊤ : Submodule R M) := by
    rw [← ker_tensorProductMk_of_surjective
      (toBase.pullbackFst surjection)
      (RingHom.surjective_pullbackFst_of_surjective _ _ base.surjective_surjection)]
    exact Subsingleton.elim _ _
  have hbot : RingHom.ker (toBase.pullbackFst surjection) •
      (⊤ : Submodule R M) ≤ ⊥ :=
    Submodule.smul_le.mpr fun j hj' m _ => hj ⟨j, hj'⟩ m
  exact ⟨fun m n => (hbot (hm m)).trans (hbot (hm n)).symm⟩

private theorem tensor_cokernel_subsingleton_of_surjective
    {R : Type*} [CommRing R] {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (f : M →ₗ[R] N)
    (T : Type*) [AddCommGroup T] [Module R T]
    (hf : Function.Surjective (LinearMap.lTensor T f)) :
    Subsingleton (T ⊗[R] (N ⧸ LinearMap.range f)) := by
  have hc : (LinearMap.range f).mkQ.comp f = 0 := by
    ext m
    exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mpr ⟨m, rfl⟩
  have hzero (x : T ⊗[R] (N ⧸ LinearMap.range f)) : x = 0 := by
    obtain ⟨n, rfl⟩ := LinearMap.lTensor_surjective T (LinearMap.range f).mkQ_surjective x
    obtain ⟨m, rfl⟩ := hf n
    change ((LinearMap.lTensor T (LinearMap.range f).mkQ).comp
      (LinearMap.lTensor T f)) m = 0
    rw [← LinearMap.lTensor_comp, hc]
    simp
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

private theorem surjective_of_baseChange
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    [Module base.fibreProduct M] [Module base.fibreProduct N]
    (f : M →ₗ[base.fibreProduct] N) :
    letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
    letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
    Function.Surjective (LinearMap.lTensor B f) →
      Function.Surjective (LinearMap.lTensor A' f) → Function.Surjective f := by
  let : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
  let : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
  intro hB hA'
  have : Subsingleton (N ⧸ LinearMap.range f) := module_subsingleton_of_baseChange base _
    (tensor_cokernel_subsingleton_of_surjective f B hB)
    (tensor_cokernel_subsingleton_of_surjective f A' hA')
  intro n
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range f)).mp
    (Subsingleton.elim (Submodule.Quotient.mk (p := LinearMap.range f) n) 0)

private theorem finiteType_of_baseChange
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    (P : Type v) [CommRing P] [Algebra base.fibreProduct P] :
    letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
    letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
    Algebra.FiniteType B (B ⊗[base.fibreProduct] P) →
      Algebra.FiniteType A' (A' ⊗[base.fibreProduct] P) →
        Algebra.FiniteType base.fibreProduct P := by
  classical
  let R := base.fibreProduct
  let : Algebra R B := (toBase.pullbackFst surjection).toAlgebra
  let : Algebra R A' := (toBase.pullbackSnd surjection).toAlgebra
  intro hB hA'
  obtain ⟨s, hs⟩ := hB.out
  obtain ⟨t, ht⟩ := hA'.out
  choose ks bs ps hbs using fun x : s => TensorProduct.exists_sum_tmul_eq x.1
  choose kt at' pt hat using fun x : t => TensorProduct.exists_sum_tmul_eq x.1
  let σ := (Σ x : s, Fin (ks x)) ⊕ (Σ x : t, Fin (kt x))
  let f : MvPolynomial σ R →ₐ[R] P := MvPolynomial.aeval
    (Sum.elim (fun ⟨x, i⟩ => ps x i) (fun ⟨x, i⟩ => pt x i))
  apply Algebra.FiniteType.of_surjective f
  apply surjective_of_baseChange base f.toLinearMap
  · change Function.Surjective (Algebra.TensorProduct.map (.id B B) f)
    rw [← AlgHom.range_eq_top, eq_top_iff, ← hs, Algebra.adjoin_le_iff]
    intro x hx
    let i : s := ⟨x, hx⟩
    use ∑ j : Fin (ks i), bs i j ⊗ₜ MvPolynomial.X (Sum.inl ⟨i, j⟩)
    simpa [f, i] using (hbs i).symm
  · change Function.Surjective (Algebra.TensorProduct.map (.id A' A') f)
    rw [← AlgHom.range_eq_top, eq_top_iff, ← ht, Algebra.adjoin_le_iff]
    intro x hx
    let i : t := ⟨x, hx⟩
    use ∑ j : Fin (kt i), at' i j ⊗ₜ MvPolynomial.X (Sum.inr ⟨i, j⟩)
    simpa [f, i] using (hat i).symm

private theorem reconstruction
    {A A' B E : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing E]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    (f : base.fibreProduct →+* E) (hf : f.Flat) :
    let s : RelativeModuleFibreProductSituation (D' := E) base := ⟨f⟩
    Function.Bijective s.toRelativePullback := by
  let s : RelativeModuleFibreProductSituation (D' := E) base := ⟨f⟩
  let : Algebra base.fibreProduct E := f.toAlgebra
  let : Algebra base.fibreProduct B := base.pullbackCone.fst.hom.toAlgebra
  let : Algebra base.fibreProduct A' := base.pullbackCone.snd.hom.toAlgebra
  let : Module.Flat base.fibreProduct E := hf
  obtain ⟨F, e, adj, he, _, _, hu, _⟩ :=
    flatModulesEquivalenceOverFibreProduct toBase surjection I base
  let L := ModuleCat.of base.fibreProduct E
  have : IsIso (adj.unit.app L) := hu L inferInstance
  refine ⟨fun a b hab ↦ ?_, s.toRelativePullback_surjective⟩
  apply (ConcreteCategory.bijective_of_isIso (adj.unit.app L)).1
  apply (e _).injective
  apply Subtype.ext
  apply Prod.ext
  · have ha := (he L _ (adj.unit.app L) a).1
    have hb := (he L _ (adj.unit.app L) b).1
    rw [adj.homEquiv_symm_unit] at ha hb
    change _ = (1 : B) ⊗ₜ[base.fibreProduct] a at ha
    change _ = (1 : B) ⊗ₜ[base.fibreProduct] b at hb
    have h : (a ⊗ₜ[base.fibreProduct] (1 : B)) = b ⊗ₜ[base.fibreProduct] (1 : B) :=
      congrArg (fun z => z.1.1) hab
    exact ha.trans ((congrArg (TensorProduct.comm base.fibreProduct E B) h).trans hb.symm)
  · have ha := (he L _ (adj.unit.app L) a).2
    have hb := (he L _ (adj.unit.app L) b).2
    rw [adj.homEquiv_symm_unit] at ha hb
    change _ = (1 : A') ⊗ₜ[base.fibreProduct] a at ha
    change _ = (1 : A') ⊗ₜ[base.fibreProduct] b at hb
    have h : (a ⊗ₜ[base.fibreProduct] (1 : A')) = b ⊗ₜ[base.fibreProduct] (1 : A') :=
      congrArg (fun z => z.1.2) hab
    exact ha.trans ((congrArg (TensorProduct.comm base.fibreProduct E A') h).trans hb.symm)

private noncomputable def pushoutAlgEquiv
    {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : R →+* T) (h : S →+* U) (i : T →+* U)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom h) (CommRingCat.ofHom i)) :
    letI : Algebra R S := f.toAlgebra
    letI : Algebra R T := g.toAlgebra
    letI : Algebra T U := i.toAlgebra
    T ⊗[R] S ≃ₐ[T] U := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R T := g.toAlgebra
  letI : Algebra T U := i.toAlgebra
  letI : Algebra S U := h.toAlgebra
  letI : Algebra R U := (i.comp g).toAlgebra
  have hc : h.comp f = i.comp g := congrArg CommRingCat.Hom.hom sq.w
  letI : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' hc.symm
  haveI : Algebra.IsPushout R T S U := CommRingCat.isPushout_iff_isPushout.mp sq.flip
  exact Algebra.IsPushout.equiv R T S U

-- Lift finitely many tensor components of generators, then descend the resulting surjection.
private theorem module_finite_of_baseChange
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    (S M : Type v) [CommRing S] [Algebra base.fibreProduct S]
    [AddCommGroup M] [Module S M] [Module base.fibreProduct M]
    [IsScalarTower base.fibreProduct S M] :
    letI : Algebra base.fibreProduct B := base.pullbackCone.fst.hom.toAlgebra
    letI : Algebra base.fibreProduct A' := base.pullbackCone.snd.hom.toAlgebra
    Module.Finite (S ⊗[base.fibreProduct] B) ((S ⊗[base.fibreProduct] B) ⊗[S] M) →
      Module.Finite (S ⊗[base.fibreProduct] A') ((S ⊗[base.fibreProduct] A') ⊗[S] M) →
        Module.Finite S M := by
  classical
  let R := base.fibreProduct
  let : Algebra R B := base.pullbackCone.fst.hom.toAlgebra
  let : Algebra R A' := base.pullbackCone.snd.hom.toAlgebra
  intro hB hA'
  obtain ⟨n, xs, hxs⟩ := Module.Finite.exists_fin (R := S ⊗[R] B)
    (M := (S ⊗[R] B) ⊗[S] M)
  obtain ⟨m, ys, hys⟩ := Module.Finite.exists_fin (R := S ⊗[R] A')
    (M := (S ⊗[R] A') ⊗[S] M)
  choose k ts ms hx using fun i : Fin n => TensorProduct.exists_sum_tmul_eq (xs i)
  choose l us ns hy using fun i : Fin m => TensorProduct.exists_sum_tmul_eq (ys i)
  let σ := (Σ i : Fin n, Fin (k i)) ⊕ (Σ i : Fin m, Fin (l i))
  let f : (σ → S) →ₗ[S] M := (Pi.basisFun S σ).constr S
    (Sum.elim (fun ⟨i, j⟩ => ms i j) (fun ⟨i, j⟩ => ns i j))
  apply Module.Finite.of_surjective f
  apply surjective_of_baseChange base (f.restrictScalars R)
  · have hf : Function.Surjective (f.baseChange (S ⊗[R] B)) := by
      rw [← LinearMap.range_eq_top, eq_top_iff, ← hxs, Submodule.span_le,
        Set.range_subset_iff]
      intro i
      use ∑ j : Fin (k i), ts i j ⊗ₜ[S] Pi.basisFun S σ (Sum.inl ⟨i, j⟩)
      simpa only [map_sum, LinearMap.baseChange_tmul, f, Module.Basis.constr_basis,
        Sum.elim_inl, Sum.elim_inr] using (hx i).symm
    intro x
    obtain ⟨z, hz⟩ := hf ((tensorBaseChangeEquiv R S B M).symm x)
    refine ⟨tensorBaseChangeEquiv R S B (σ → S) z, ?_⟩
    rw [← tensorBaseChangeEquiv_natural, hz, LinearEquiv.apply_symm_apply]
  · have hf : Function.Surjective (f.baseChange (S ⊗[R] A')) := by
      rw [← LinearMap.range_eq_top, eq_top_iff, ← hys, Submodule.span_le,
        Set.range_subset_iff]
      intro i
      use ∑ j : Fin (l i), us i j ⊗ₜ[S] Pi.basisFun S σ (Sum.inr ⟨i, j⟩)
      simpa only [map_sum, LinearMap.baseChange_tmul, f, Module.Basis.constr_basis,
        Sum.elim_inl, Sum.elim_inr] using (hy i).symm
    intro x
    obtain ⟨z, hz⟩ := hf ((tensorBaseChangeEquiv R S A' M).symm x)
    refine ⟨tensorBaseChangeEquiv R S A' (σ → S) z, ?_⟩
    rw [← tensorBaseChangeEquiv_natural, hz, LinearEquiv.apply_symm_apply]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
private theorem module_fp_tensor_of_algebra_fp
    (R Q P T : Type*) [CommRing R] [CommRing Q] [CommRing P] [CommRing T]
    [Algebra R Q] [Algebra R P] [Algebra R T] [Algebra Q P] [IsScalarTower R Q P]
    [Algebra.FinitePresentation R Q] [Algebra.FinitePresentation T (T ⊗[R] P)]
    (hf : Function.Surjective (algebraMap Q P)) :
    Module.FinitePresentation (Q ⊗[R] T) ((Q ⊗[R] T) ⊗[Q] P) := by
  let U := (Q ⊗[R] T) ⊗[Q] P
  let eR : U ≃ₐ[R] T ⊗[R] P :=
    ((Algebra.TensorProduct.comm Q (Q ⊗[R] T) P).restrictScalars R).trans
      (((Algebra.TensorProduct.cancelBaseChange R Q P P T).restrictScalars R).trans
        (Algebra.TensorProduct.comm R P T))
  let e : U ≃ₐ[T] T ⊗[R] P :=
    { eR with
      commutes' := fun t => by
        change eR ((1 ⊗ₜ[R] t) ⊗ₜ[Q] (1 : P)) = t ⊗ₜ[R] (1 : P)
        change (Algebra.TensorProduct.comm R P T)
          ((Algebra.TensorProduct.cancelBaseChange R Q P P T)
            ((1 : P) ⊗ₜ[Q] ((1 : Q) ⊗ₜ[R] t))) = _
        rw [Algebra.TensorProduct.cancelBaseChange_tmul]
        change t ⊗ₜ[R] ((1 : Q) • (1 : P)) = t ⊗ₜ[R] (1 : P)
        rw [one_smul] }
  have : Algebra.FinitePresentation T U := Algebra.FinitePresentation.equiv e.symm
  have : Algebra.FinitePresentation T (Q ⊗[R] T) :=
    Algebra.FinitePresentation.equiv (Algebra.TensorProduct.commRight R T Q)
  have : Algebra.FinitePresentation (Q ⊗[R] T) U :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation T (Q ⊗[R] T) U
  have hs : Function.Surjective (algebraMap (Q ⊗[R] T) U) :=
    Algebra.TensorProduct.includeLeft_surjective (Q ⊗[R] T) (Q ⊗[R] T) hf
  have : Module.Finite (Q ⊗[R] T) U :=
    Module.Finite.of_surjective (Algebra.linearMap (Q ⊗[R] T) U) hs
  exact Module.FinitePresentation.of_finite_of_finitePresentation (Q ⊗[R] T) U

set_option backward.isDefEq.respectTransparency false in
private theorem finitePresentation_of_baseChange
    {A A' B P : Type u} [CommRing A] [CommRing A'] [CommRing B] [CommRing P]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    [Algebra base.fibreProduct P] [Module.Flat base.fibreProduct P] :
    letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
    letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
    Algebra.FinitePresentation B (B ⊗[base.fibreProduct] P) →
      Algebra.FinitePresentation A' (A' ⊗[base.fibreProduct] P) →
        Algebra.FinitePresentation base.fibreProduct P := by
  let R := base.fibreProduct
  let : Algebra R B := (toBase.pullbackFst surjection).toAlgebra
  let : Algebra R A' := (toBase.pullbackSnd surjection).toAlgebra
  intro hB hA'
  have : Algebra.FiniteType R P := finiteType_of_baseChange base P inferInstance inferInstance
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R P)
  let Q := MvPolynomial (Fin n) R
  let : Algebra Q P := f.toRingHom.toAlgebra
  let : IsScalarTower R Q P := IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let l := Algebra.linearMap Q P
  have : Module.FinitePresentation (Q ⊗[R] B) ((Q ⊗[R] B) ⊗[Q] P) :=
    module_fp_tensor_of_algebra_fp R Q P B hf
  have : Module.FinitePresentation (Q ⊗[R] A') ((Q ⊗[R] A') ⊗[Q] P) :=
    module_fp_tensor_of_algebra_fp R Q P A' hf
  have : Module.Finite Q (LinearMap.ker l) := module_finite_of_baseChange base Q
    (LinearMap.ker l)
    (finite_baseChange_ker_of_flat R Q B Q P l hf)
    (finite_baseChange_ker_of_flat R Q A' Q P l hf)
  exact Algebra.FinitePresentation.of_surjective hf
    (Module.Finite.iff_fg.mp (inferInstance : Module.Finite Q (LinearMap.ker l)))

private theorem property_of_pushout
    (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
    (hP : RingHom.IsStableUnderBaseChange P)
    {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : R →+* T) (h : S →+* U) (i : T →+* U)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom h) (CommRingCat.ofHom i)) (hf : P f) : P i := by
  have : (RingHom.toMorphismProperty P).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.mpr hP
  exact MorphismProperty.of_isPushout (P := RingHom.toMorphismProperty P) sq.flip hf

private theorem finiteType_of_pushouts
    {A A' B P D C' : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing P] [CommRing D] [CommRing C']
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    (f : base.fibreProduct →+* P) (BtoD : B →+* D) (A'toC' : A' →+* C')
    (pD : P →+* D) (pC' : P →+* C')
    (hD : IsPushout (CommRingCat.ofHom f) base.pullbackCone.fst
      (CommRingCat.ofHom pD) (CommRingCat.ofHom BtoD))
    (hC' : IsPushout (CommRingCat.ofHom f) base.pullbackCone.snd
      (CommRingCat.ofHom pC') (CommRingCat.ofHom A'toC'))
    (hb : BtoD.FiniteType) (ha : A'toC'.FiniteType) : f.FiniteType := by
  let : Algebra base.fibreProduct P := f.toAlgebra
  let : Algebra base.fibreProduct B := base.pullbackCone.fst.hom.toAlgebra
  let : Algebra base.fibreProduct A' := base.pullbackCone.snd.hom.toAlgebra
  let : Algebra B D := BtoD.toAlgebra
  let : Algebra A' C' := A'toC'.toAlgebra
  have : Algebra.FiniteType B D := hb
  have : Algebra.FiniteType A' C' := ha
  exact finiteType_of_baseChange base P
    (Algebra.FiniteType.equiv inferInstance
      (pushoutAlgEquiv f base.pullbackCone.fst.hom pD BtoD hD).symm)
    (Algebra.FiniteType.equiv inferInstance
      (pushoutAlgEquiv f base.pullbackCone.snd.hom pC' A'toC' hC').symm)

-- A field-valued map either kills the projection kernel or inverts one of its elements.
private theorem field_factor
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    {K : Type v} [Field K] (f : base.fibreProduct →+* K) :
    (∃ g : B →+* K, g.comp (toBase.pullbackFst surjection) = f) ∨
      (∃ g : A' →+* K, g.comp (toBase.pullbackSnd surjection) = f) := by
  classical
  let R := base.fibreProduct
  by_cases hf : RingHom.ker (toBase.pullbackFst surjection) ≤ RingHom.ker f
  · let hs := RingHom.surjective_pullbackFst_of_surjective toBase surjection
      base.surjective_surjection
    exact Or.inl ⟨(toBase.pullbackFst surjection).liftOfSurjective hs ⟨f, hf⟩,
      RingHom.liftOfSurjective_comp _ hs _⟩
  · obtain ⟨j, hj, hfj⟩ := IsConcreteLE.not_le_iff_exists.mp hf
    have hj₁ : j.1.1 = 0 := hj
    have hj₂ : surjection j.1.2 = 0 :=
      j.2.symm.trans ((congrArg toBase hj₁).trans (map_zero _))
    have hfj : f j ≠ 0 := hfj
    let l : A' →+ R :=
      { toFun := fun a => ⟨(0, j.1.2 * a), by simp [hj₂]⟩
        map_zero' := Subtype.ext (Prod.ext rfl (mul_zero _))
        map_add' := fun a b => Subtype.ext (Prod.ext (zero_add _).symm (mul_add ..)) }
    have hl₁ : l 1 = j := Subtype.ext (Prod.ext hj₁.symm (mul_one _))
    have hlmul (a b : A') : l a * l b = j * l (a * b) := by
      apply Subtype.ext
      apply Prod.ext
      · change (0 : B) * 0 = j.1.1 * 0
        simp
      · change (j.1.2 * a) * (j.1.2 * b) = j.1.2 * (j.1.2 * (a * b))
        ring
    let g : A' →+* K :=
      { toFun := fun a => f (l a) / f j
        map_zero' := by simp
        map_one' := by rw [hl₁, div_self hfj]
        map_add' := fun a b => by rw [map_add, map_add, add_div]
        map_mul' := fun a b => by
          rw [div_mul_div_comm, ← f.map_mul, hlmul, f.map_mul]
          field_simp }
    refine Or.inr ⟨g, RingHom.ext fun r => ?_⟩
    have h : l r.1.2 = j * r :=
      Subtype.ext (Prod.ext (by change 0 = j.1.1 * r.1.1; simp [hj₁]) rfl)
    change f (l r.1.2) / f j = f r
    rw [h, map_mul, mul_div_cancel_left₀ _ hfj]
private theorem smooth_of_baseChange
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    (P : Type v) [CommRing P] [Algebra base.fibreProduct P]
    [Module.Flat base.fibreProduct P] [Algebra.FinitePresentation base.fibreProduct P] :
    letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
    letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
    Algebra.Smooth B (B ⊗[base.fibreProduct] P) →
      Algebra.Smooth A' (A' ⊗[base.fibreProduct] P) →
        Algebra.Smooth base.fibreProduct P := by
  let R := base.fibreProduct
  let : Algebra R B := (toBase.pullbackFst surjection).toAlgebra
  let : Algebra R A' := (toBase.pullbackSnd surjection).toAlgebra
  intro hB hA'
  apply Algebra.Smooth.of_formallySmooth_fiber
  intro q hq
  rcases field_factor base (algebraMap R q.ResidueField) with ⟨g, hg⟩ | ⟨g, hg⟩
  · let : Algebra B q.ResidueField := g.toAlgebra
    let : IsScalarTower R B q.ResidueField := IsScalarTower.of_algebraMap_eq' hg.symm
    exact Algebra.FormallySmooth.of_equiv
      (Algebra.TensorProduct.cancelBaseChange R B q.ResidueField q.ResidueField P)
  · let : Algebra A' q.ResidueField := g.toAlgebra
    let : IsScalarTower R A' q.ResidueField := IsScalarTower.of_algebraMap_eq' hg.symm
    exact Algebra.FormallySmooth.of_equiv
      (Algebra.TensorProduct.cancelBaseChange R A' q.ResidueField q.ResidueField P)

private theorem unramified_of_baseChange
    {A A' B : Type u} [CommRing A] [CommRing A'] [CommRing B]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    (P : Type v) [CommRing P] [Algebra base.fibreProduct P] :
    letI : Algebra base.fibreProduct B := (toBase.pullbackFst surjection).toAlgebra
    letI : Algebra base.fibreProduct A' := (toBase.pullbackSnd surjection).toAlgebra
    Algebra.FormallyUnramified B (B ⊗[base.fibreProduct] P) →
      Algebra.FormallyUnramified A' (A' ⊗[base.fibreProduct] P) →
        Algebra.FormallyUnramified base.fibreProduct P := by
  let R := base.fibreProduct
  let : Algebra R B := (toBase.pullbackFst surjection).toAlgebra
  let : Algebra R A' := (toBase.pullbackSnd surjection).toAlgebra
  let : Algebra P (B ⊗[R] P) := Algebra.TensorProduct.rightAlgebra
  let : Algebra P (A' ⊗[R] P) := Algebra.TensorProduct.rightAlgebra
  intro hB hA'
  exact ⟨module_subsingleton_of_baseChange base _
    (KaehlerDifferential.tensorKaehlerEquivBase R B P (B ⊗[R] P)).injective.subsingleton
    (KaehlerDifferential.tensorKaehlerEquivBase R A' P (A' ⊗[R] P)).injective.subsingleton⟩

private theorem pullback_properties
    {A A' B D C' C : Type u}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D] [CommRing C'] [CommRing C]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    (BtoD : B →+* D) (A'toC' : A' →+* C') (AtoC : A →+* C)
    (DtoC : D →+* C) (C'toC : C' →+* C)
    (hD : IsPushout (CommRingCat.ofHom BtoD) (CommRingCat.ofHom toBase)
      (CommRingCat.ofHom DtoC) (CommRingCat.ofHom AtoC))
    (hC' : IsPushout (CommRingCat.ofHom A'toC') (CommRingCat.ofHom surjection)
      (CommRingCat.ofHom C'toC) (CommRingCat.ofHom AtoC))
    (f : base.fibreProduct →+* RingHom.pullback DtoC C'toC)
    (hf₁ : ∀ r, (f r).1.1 = BtoD (base.pullbackCone.fst.hom r))
    (hf₂ : ∀ r, (f r).1.2 = A'toC' (base.pullbackCone.snd.hom r))
 :
    (f.FiniteType ↔ BtoD.FiniteType ∧ A'toC'.FiniteType) ∧
    (f.Flat ↔ BtoD.Flat ∧ A'toC'.Flat) ∧
    (f.Flat ∧ f.FinitePresentation ↔
      (BtoD.Flat ∧ BtoD.FinitePresentation) ∧ (A'toC'.Flat ∧ A'toC'.FinitePresentation)) ∧
    (f.Smooth ↔ BtoD.Smooth ∧ A'toC'.Smooth) ∧
    (f.Etale ↔ BtoD.Etale ∧ A'toC'.Etale) := by
  let R := base.fibreProduct
  let P := RingHom.pullback DtoC C'toC
  let : Algebra R P := f.toAlgebra
  let : Algebra R B := base.pullbackCone.fst.hom.toAlgebra
  let : Algebra R A' := base.pullbackCone.snd.hom.toAlgebra
  let : Algebra B D := BtoD.toAlgebra
  let : Algebra A' C' := A'toC'.toAlgebra
  obtain ⟨hpB, hpA⟩ := pullback_baseChange base BtoD A'toC' AtoC DtoC C'toC hD hC' f hf₁ hf₂
  let eB : B ⊗[R] P ≃ₐ[B] D := pushoutAlgEquiv f base.pullbackCone.fst.hom
    (DtoC.pullbackFst C'toC) BtoD hpB
  let eA : A' ⊗[R] P ≃ₐ[A'] C' := pushoutAlgEquiv f base.pullbackCone.snd.hom
    (DtoC.pullbackSnd C'toC) A'toC' hpA
  have forwards (Q : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)
      (hQ : RingHom.IsStableUnderBaseChange Q) (hf : Q f) : Q BtoD ∧ Q A'toC' :=
    ⟨property_of_pushout Q hQ _ _ _ _ hpB hf,
      property_of_pushout Q hQ _ _ _ _ hpA hf⟩
  have hflat : f.Flat ↔ BtoD.Flat ∧ A'toC'.Flat :=
    ⟨forwards _ RingHom.Flat.isStableUnderBaseChange,
      fun h => pullback_flat_of_components base BtoD A'toC' AtoC DtoC C'toC
        hD hC' f hf₁ hf₂ h.1 h.2⟩
  have hfp : f.Flat ∧ f.FinitePresentation ↔
      (BtoD.Flat ∧ BtoD.FinitePresentation) ∧ (A'toC'.Flat ∧ A'toC'.FinitePresentation) := by
    constructor
    · exact forwards _ (RingHom.Flat.isStableUnderBaseChange.and
        RingHom.finitePresentation_isStableUnderBaseChange)
    · intro h
      have hf : f.Flat := hflat.mpr ⟨h.1.1, h.2.1⟩
      refine ⟨hf, ?_⟩
      have : Module.Flat R P := hf
      have : Algebra.FinitePresentation B D := h.1.2
      have : Algebra.FinitePresentation A' C' := h.2.2
      exact finitePresentation_of_baseChange base
        (Algebra.FinitePresentation.equiv eB.symm) (Algebra.FinitePresentation.equiv eA.symm)
  refine ⟨⟨forwards _ RingHom.finiteType_isStableUnderBaseChange, ?_⟩, hflat, hfp,
    ⟨forwards _ RingHom.Smooth.isStableUnderBaseChange, ?_⟩,
    ⟨forwards _ RingHom.Etale.isStableUnderBaseChange, ?_⟩⟩
  · intro h
    exact finiteType_of_pushouts base f BtoD A'toC' _ _ hpB hpA h.1 h.2
  · intro h
    have hf := hfp.mpr ⟨⟨h.1.flat, h.1.finitePresentation⟩,
      ⟨h.2.flat, h.2.finitePresentation⟩⟩
    have : Module.Flat R P := hf.1
    have : Algebra.FinitePresentation R P := hf.2
    have : Algebra.Smooth B D := h.1
    have : Algebra.Smooth A' C' := h.2
    exact smooth_of_baseChange base P (Algebra.Smooth.of_equiv eB.symm)
      (Algebra.Smooth.of_equiv eA.symm)
  · intro h
    have hb := RingHom.Etale.iff_flat_and_formallyUnramified.mp h.1
    have ha := RingHom.Etale.iff_flat_and_formallyUnramified.mp h.2
    have hf := hfp.mpr ⟨⟨hb.1, hb.2.2⟩, ⟨ha.1, ha.2.2⟩⟩
    apply RingHom.Etale.iff_flat_and_formallyUnramified.mpr
    refine ⟨hf.1, ?_, hf.2⟩
    have : Algebra.FormallyUnramified B D := hb.2.1
    have : Algebra.FormallyUnramified A' C' := ha.2.1
    exact unramified_of_baseChange base P
      (Algebra.FormallyUnramified.of_equiv eB.symm)
      (Algebra.FormallyUnramified.of_equiv eA.symm)

private theorem properties_equiv
    {R : Type u} {S : Type v} {R' : Type w} {S' : Type x}
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (eR : R' ≃+* R) (eS : S ≃+* S') :
    let f' := eS.toRingHom.comp (f.comp eR.toRingHom)
    (f'.FiniteType ↔ f.FiniteType) ∧ (f'.Flat ↔ f.Flat) ∧
    (f'.FinitePresentation ↔ f.FinitePresentation) ∧ (f'.Smooth ↔ f.Smooth) ∧
    (f'.Etale ↔ f.Etale) := by
  let f' := eS.toRingHom.comp (f.comp eR.toRingHom)
  have cancel : eS.symm.toRingHom.comp (f'.comp eR.symm.toRingHom) = f := by
    ext r
    simp [f']
  have hflat : f'.Flat ↔ f.Flat := by
    dsimp only [f']
    rw [RingHom.Flat.comp_iff_of_bijective_left eS.bijective,
      RingHom.Flat.comp_iff_of_bijective_right eR.bijective]
  have hsmooth : f'.Smooth ↔ f.Smooth := by
    constructor
    · intro h
      rw [← cancel]
      exact ((RingHom.Smooth.of_bijective eR.symm.bijective).comp h).comp
        (RingHom.Smooth.of_bijective eS.symm.bijective)
    · intro h
      exact ((RingHom.Smooth.of_bijective eR.bijective).comp h).comp
        (RingHom.Smooth.of_bijective eS.bijective)
  have hunram : f'.FormallyUnramified ↔ f.FormallyUnramified := by
    constructor
    · intro h
      rw [← cancel]
      exact ((RingHom.FormallyUnramified.of_surjective eR.symm.surjective).comp h).comp
        (RingHom.FormallyUnramified.of_surjective eS.symm.surjective)
    · intro h
      exact ((RingHom.FormallyUnramified.of_surjective eR.surjective).comp h).comp
        (RingHom.FormallyUnramified.of_surjective eS.surjective)
  refine ⟨?_, hflat, ?_, hsmooth, ?_⟩
  · constructor
    · intro h
      rw [← cancel]
      exact (RingHom.FiniteType.of_surjective _ eS.symm.surjective).comp
        (h.comp (RingHom.FiniteType.of_surjective _ eR.symm.surjective))
    · intro h
      exact (RingHom.FiniteType.of_surjective _ eS.surjective).comp
        (h.comp (RingHom.FiniteType.of_surjective _ eR.surjective))
  · constructor
    · intro h
      rw [← cancel]
      exact (RingHom.FinitePresentation.of_bijective eS.symm.bijective).comp
        (h.comp (RingHom.FinitePresentation.of_bijective eR.symm.bijective))
    · intro h
      exact (RingHom.FinitePresentation.of_bijective eS.bijective).comp
        (h.comp (RingHom.FinitePresentation.of_bijective eR.bijective))
  · change f'.Etale ↔ f.Etale
    rw [RingHom.etale_iff_formallyUnramified_and_smooth,
      RingHom.etale_iff_formallyUnramified_and_smooth]
    exact and_congr hunram hsmooth

private def pullbackUliftEquiv
    {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]
    (f : B →+* A) (g : C →+* A) :
    RingHom.pullback f.ulift.{z,z} g.ulift.{z,z} ≃+* RingHom.pullback f g where
  toFun p := ⟨(p.1.1.down, p.1.2.down), congrArg ULift.down p.2⟩
  invFun p := ⟨(ULift.up p.1.1, ULift.up p.1.2), congrArg ULift.up p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

-- Each supplied pushout has its own universe bound; raise both bounds before gluing.
set_option backward.isDefEq.respectTransparency false in
private theorem isPushout_ulift
    {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : R →+* T) (h : S →+* U) (i : T →+* U)
    (sq : IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g)
      (CommRingCat.ofHom h) (CommRingCat.ofHom i)) :
    IsPushout (CommRingCat.ofHom f.ulift.{v,v}) (CommRingCat.ofHom g.ulift.{v,v})
      (CommRingCat.ofHom h.ulift.{v,v}) (CommRingCat.ofHom i.ulift.{v,v}) := by
  let : Algebra R S := f.toAlgebra
  let : Algebra R T := g.toAlgebra
  let : Algebra T U := i.toAlgebra
  let : Algebra S U := h.toAlgebra
  let : Algebra R U := (i.comp g).toAlgebra
  have hc : h.comp f = i.comp g := congrArg CommRingCat.Hom.hom sq.w
  let : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' hc.symm
  have : Algebra.IsPushout R T S U := CommRingCat.isPushout_iff_isPushout.mp sq.flip
  let : Algebra (ULift.{v} R) (ULift.{v} S) := f.ulift.toAlgebra
  let : Algebra (ULift.{v} R) (ULift.{v} T) := g.ulift.toAlgebra
  let : Algebra (ULift.{v} T) (ULift.{v} U) := i.ulift.toAlgebra
  let : Algebra (ULift.{v} S) (ULift.{v} U) := h.ulift.toAlgebra
  let : Algebra (ULift.{v} R) (ULift.{v} U) := (i.comp g).ulift.toAlgebra
  let : IsScalarTower (ULift.{v} R) (ULift.{v} T) (ULift.{v} U) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower (ULift.{v} R) (ULift.{v} S) (ULift.{v} U) :=
    IsScalarTower.of_algebraMap_eq fun r => congrArg ULift.up (DFunLike.congr_fun hc.symm r.down)
  let e : (ULift.{v} T ⊗[ULift.{v} R] ULift.{v} S) ≃+* ULift.{v} U :=
    (Algebra.TensorProduct.uliftEquiv.{v,v,v,v} R T T S).symm.toRingEquiv |>.trans
      (ULift.ringEquiv.trans ((Algebra.IsPushout.equiv R T S U).toRingEquiv.trans
        ULift.ringEquiv.symm))
  have he (t : ULift.{v} T) (s : ULift.{v} S) :
      e (t ⊗ₜ[ULift.{v} R] s) = i.ulift t * h.ulift s := by
    apply ULift.ext
    change (Algebra.IsPushout.equiv R T S U)
      (((Algebra.TensorProduct.uliftEquiv.{v,v,v,v} R T T S).symm (t ⊗ₜ s)).down) = _
    rw [Algebra.TensorProduct.down_uliftEquiv_symm_tmul, Algebra.IsPushout.equiv_tmul]
    rfl
  let ea : (ULift.{v} T ⊗[ULift.{v} R] ULift.{v} S) ≃ₐ[ULift.{v} T] ULift.{v} U :=
    { e with
      commutes' := fun t => by
        change e (t ⊗ₜ[ULift.{v} R] (1 : ULift.{v} S)) = i.ulift t
        rw [he, map_one, mul_one] }
  have : Algebra.IsPushout (ULift.{v} R) (ULift.{v} T) (ULift.{v} S) (ULift.{v} U) :=
    ⟨IsBaseChange.of_equiv ea.toLinearEquiv (fun s => by
      change e ((1 : ULift.{v} T) ⊗ₜ[ULift.{v} R] s) = h.ulift s
      rw [he, map_one, one_mul])⟩
  exact (CommRingCat.isPushout_of_isPushout (ULift.{v} R) (ULift.{v} T)
    (ULift.{v} S) (ULift.{v} U)).flip

private def uliftFlattenEquiv (R : Type u) [CommRing R] :
    ULift.{v} (ULift.{w} R) ≃+* ULift.{max v w} R where
  toFun r := ⟨r.down.down⟩
  invFun r := ⟨⟨r.down⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

private theorem ringPushout_lift
    {R : Type u} {S : Type v} {T : Type w} {U : Type x}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (g : R →+* T) (h : S →+* U) (i : T →+* U)
    (sq : IsPushout
      (CommRingCat.ofHom f.ulift.{max u v w x, max u v w x})
      (CommRingCat.ofHom g.ulift.{max u v w x, max u v w x})
      (CommRingCat.ofHom h.ulift.{max u v w x, max u v w x})
      (CommRingCat.ofHom i.ulift.{max u v w x, max u v w x})) :
    IsPushout
      (CommRingCat.ofHom f.ulift.{max u v w x z, max u v w x z})
      (CommRingCat.ofHom g.ulift.{max u v w x z, max u v w x z})
      (CommRingCat.ofHom h.ulift.{max u v w x z, max u v w x z})
      (CommRingCat.ofHom i.ulift.{max u v w x z, max u v w x z}) := by
  have hs := isPushout_ulift.{max u v w x,z} _ _ _ _ sq
  exact hs.of_iso (uliftFlattenEquiv R).toCommRingCatIso
    (uliftFlattenEquiv S).toCommRingCatIso (uliftFlattenEquiv T).toCommRingCatIso
    (uliftFlattenEquiv U).toCommRingCatIso rfl rfl rfl rfl

private theorem pullback_properties_large
    {A A' B : Type u} {D : Type v} {C' : Type w} {C : Type x}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D] [CommRing C'] [CommRing C]
    {toBase : B →+* A} {surjection : A' →+* A} {I : Ideal A'}
    (base : RingFibreProduct.Situation toBase surjection I)
    (BtoD : B →+* D) (A'toC' : A' →+* C') (AtoC : A →+* C)
    (DtoC : D →+* C) (C'toC : C' →+* C)
    (hD : ringPushout BtoD toBase DtoC AtoC)
    (hC' : ringPushout A'toC' surjection C'toC AtoC)
    (f : base.fibreProduct →+* RingHom.pullback DtoC C'toC)
    (hf₁ : ∀ r, (f r).1.1 = BtoD (base.pullbackCone.fst.hom r))
    (hf₂ : ∀ r, (f r).1.2 = A'toC' (base.pullbackCone.snd.hom r))
 :
    (f.FiniteType ↔ BtoD.FiniteType ∧ A'toC'.FiniteType) ∧
    (f.Flat ↔ BtoD.Flat ∧ A'toC'.Flat) ∧
    (f.Flat ∧ f.FinitePresentation ↔
      (BtoD.Flat ∧ BtoD.FinitePresentation) ∧ (A'toC'.Flat ∧ A'toC'.FinitePresentation)) ∧
    (f.Smooth ↔ BtoD.Smooth ∧ A'toC'.Smooth) ∧
    (f.Etale ↔ BtoD.Etale ∧ A'toC'.Etale) := by
  let toBaseL := toBase.ulift.{max u v w x, max u v w x}
  let surjectionL := surjection.ulift.{max u v w x, max u v w x}
  let baseL : RingFibreProduct.Situation toBaseL surjectionL
      (RingHom.ker surjectionL) :=
    ⟨fun a => by
      obtain ⟨a', ha'⟩ := base.surjective_surjection a.down
      exact ⟨ULift.up a', congrArg ULift.up ha'⟩, rfl⟩
  let eR : baseL.fibreProduct ≃+* base.fibreProduct := pullbackUliftEquiv toBase surjection
  let eP : RingHom.pullback DtoC.ulift.{max u v w x, max u v w x}
      C'toC.ulift.{max u v w x, max u v w x} ≃+* RingHom.pullback DtoC C'toC :=
    pullbackUliftEquiv DtoC C'toC
  let fL := eP.symm.toRingHom.comp (f.comp eR.toRingHom)
  have hDL := ringPushout_lift.{u,v,u,x,w} BtoD toBase DtoC AtoC hD
  have hAL := ringPushout_lift.{u,w,u,x,v} A'toC' surjection C'toC AtoC hC'
  obtain ⟨hft, hflat, hfp, hsmooth, hetale⟩ := pullback_properties baseL
    BtoD.ulift.{max u v w x, max u v w x} A'toC'.ulift.{max u v w x, max u v w x}
    AtoC.ulift.{max u v w x, max u v w x} DtoC.ulift.{max u v w x, max u v w x}
    C'toC.ulift.{max u v w x, max u v w x} hDL hAL fL
    (fun r => congrArg ULift.up (hf₁ (eR r)))
    (fun r => congrArg ULift.up (hf₂ (eR r)))
  obtain ⟨eft, eflat, efp, esmooth, eetale⟩ := properties_equiv f eR eP.symm
  obtain ⟨bft, bflat, bfp, bsmooth, betale⟩ := properties_equiv BtoD
    (ULift.ringEquiv : ULift.{max u v w x} B ≃+* B)
    (ULift.ringEquiv.symm : D ≃+* ULift.{max u v w x} D)
  obtain ⟨aft, aflat, afp, asmooth, aetale⟩ := properties_equiv A'toC'
    (ULift.ringEquiv : ULift.{max u v w x} A' ≃+* A')
    (ULift.ringEquiv.symm : C' ≃+* ULift.{max u v w x} C')
  exact ⟨eft.symm.trans (hft.trans (and_congr bft aft)),
    eflat.symm.trans (hflat.trans (and_congr bflat aflat)),
    (and_congr eflat efp).symm.trans (hfp.trans
      (and_congr (and_congr bflat bfp) (and_congr aflat afp))),
    esmooth.symm.trans (hsmooth.trans (and_congr bsmooth asmooth)),
    eetale.symm.trans (hetale.trans (and_congr betale aetale))⟩

end RingPropertyDescent

/-- The five ring-map properties and canonical reconstruction asserted in Tag 08KQ.
The categorical gluing assertion is stated separately above. -/
public theorem ringHom_properties_pullback_iff_and_reconstruction
    {A A' B : Type u} {D : Type v} {C' : Type w} {C : Type x}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D] [CommRing C'] [CommRing C]
    (toBase : B →+* A) (surjection : A' →+* A) (I : Ideal A')
    (base : RingFibreProduct.Situation toBase surjection I)
    (BtoD : B →+* D) (A'toC' : A' →+* C') (AtoC : A →+* C)
    (DtoC : D →+* C) (C'toC : C' →+* C)
    (hD : ringPushout BtoD toBase DtoC AtoC)
    (hC' : ringPushout A'toC' surjection C'toC AtoC) :
    let toB : base.fibreProduct →+* B := base.pullbackCone.fst.hom
    let toA' : base.fibreProduct →+* A' := base.pullbackCone.snd.hom
    let toD' : base.fibreProduct →+* RingHom.pullback DtoC C'toC :=
      RingHom.codRestrict ((BtoD.comp toB).prod (A'toC'.comp toA'))
        (RingHom.pullback DtoC C'toC) (fun x ↦ by
          change DtoC (BtoD (toB x)) = C'toC (A'toC' (toA' x))
          have hd : DtoC.comp BtoD = AtoC.comp toBase := ringPushout_comm hD
          have hc : C'toC.comp A'toC' = AtoC.comp surjection := ringPushout_comm hC'
          calc
            _ = AtoC (toBase (toB x)) := DFunLike.congr_fun hd (toB x)
            _ = AtoC (surjection (toA' x)) := congrArg AtoC
              (DFunLike.congr_fun
                (congrArg CommRingCat.Hom.hom base.pullbackCone.condition) x)
            _ = _ := (DFunLike.congr_fun hc (toA' x)).symm)
    (toD'.FiniteType ↔ BtoD.FiniteType ∧ A'toC'.FiniteType) ∧
      (toD'.Flat ↔ BtoD.Flat ∧ A'toC'.Flat) ∧
      (toD'.Flat ∧ toD'.FinitePresentation ↔
        (BtoD.Flat ∧ BtoD.FinitePresentation) ∧
          (A'toC'.Flat ∧ A'toC'.FinitePresentation)) ∧
      (toD'.Smooth ↔ BtoD.Smooth ∧ A'toC'.Smooth) ∧
      (toD'.Etale ↔ BtoD.Etale ∧ A'toC'.Etale) ∧
      (∀ (E : Type u) [CommRing E] (f : base.fibreProduct →+* E), f.Flat →
        let s : RelativeModuleFibreProductSituation (D' := E) base := ⟨f⟩
        Function.Bijective s.toRelativePullback) := by
  let toB : base.fibreProduct →+* B := base.pullbackCone.fst.hom
  let toA' : base.fibreProduct →+* A' := base.pullbackCone.snd.hom
  let toD' : base.fibreProduct →+* RingHom.pullback DtoC C'toC :=
    RingHom.codRestrict ((BtoD.comp toB).prod (A'toC'.comp toA'))
      (RingHom.pullback DtoC C'toC) (fun x ↦ by
        change DtoC (BtoD (toB x)) = C'toC (A'toC' (toA' x))
        have hd : DtoC.comp BtoD = AtoC.comp toBase := ringPushout_comm hD
        have hc : C'toC.comp A'toC' = AtoC.comp surjection := ringPushout_comm hC'
        calc
          _ = AtoC (toBase (toB x)) := DFunLike.congr_fun hd (toB x)
          _ = AtoC (surjection (toA' x)) := congrArg AtoC
            (DFunLike.congr_fun
              (congrArg CommRingCat.Hom.hom base.pullbackCone.condition) x)
          _ = _ := (DFunLike.congr_fun hc (toA' x)).symm)
  obtain ⟨hft, hflat, hfp, hsmooth, hetale⟩ := pullback_properties_large base
    BtoD A'toC' AtoC DtoC C'toC hD hC' toD' (fun _ => rfl) (fun _ => rfl)
  exact ⟨hft, hflat, hfp, hsmooth, hetale, fun E _ f hf => reconstruction base f hf⟩

/-- **Stacks Project, Tag 08KQ.** Properties of an algebra obtained by gluing algebras over a
fibre product are detected on its two base changes. Every flat algebra over the fibre product
is canonically reconstructed from those base changes, and base change induces an equivalence
with the category of compatible systems of flat algebras. -/
@[stacks 08KQ]
public theorem ringHom_properties_pullback_iff_and_flatAlgebra_equivalence
    {A A' B : Type u} {D : Type v} {C' : Type w} {C : Type x}
    [CommRing A] [CommRing A'] [CommRing B] [CommRing D] [CommRing C'] [CommRing C]
    (toBase : B →+* A) (surjection : A' →+* A) (I : Ideal A')
    (base : RingFibreProduct.Situation toBase surjection I)
    (BtoD : B →+* D) (A'toC' : A' →+* C') (AtoC : A →+* C)
    (DtoC : D →+* C) (C'toC : C' →+* C)
    (hD : ringPushout BtoD toBase DtoC AtoC)
    (hC' : ringPushout A'toC' surjection C'toC AtoC) :
    let toB : base.fibreProduct →+* B := base.pullbackCone.fst.hom
    let toA' : base.fibreProduct →+* A' := base.pullbackCone.snd.hom
    let toD' : base.fibreProduct →+* RingHom.pullback DtoC C'toC :=
      RingHom.codRestrict ((BtoD.comp toB).prod (A'toC'.comp toA'))
        (RingHom.pullback DtoC C'toC) (fun x ↦ by
          change DtoC (BtoD (toB x)) = C'toC (A'toC' (toA' x))
          have hd : DtoC.comp BtoD = AtoC.comp toBase := ringPushout_comm hD
          have hc : C'toC.comp A'toC' = AtoC.comp surjection := ringPushout_comm hC'
          calc
            _ = AtoC (toBase (toB x)) := DFunLike.congr_fun hd (toB x)
            _ = AtoC (surjection (toA' x)) := congrArg AtoC
              (DFunLike.congr_fun
                (congrArg CommRingCat.Hom.hom base.pullbackCone.condition) x)
            _ = _ := (DFunLike.congr_fun hc (toA' x)).symm)
    let flat := CommRingCat.flat
    let BtoA := MorphismProperty.Under.pushout flat ⊤ (CommRingCat.ofHom toBase)
    let A'toA := MorphismProperty.Under.pushout flat ⊤ (CommRingCat.ofHom surjection)
    let B'toB := MorphismProperty.Under.pushout flat ⊤ (CommRingCat.ofHom toB)
    let B'toA' := MorphismProperty.Under.pushout flat ⊤ (CommRingCat.ofHom toA')
    (toD'.FiniteType ↔ BtoD.FiniteType ∧ A'toC'.FiniteType) ∧
      (toD'.Flat ↔ BtoD.Flat ∧ A'toC'.Flat) ∧
      (toD'.Flat ∧ toD'.FinitePresentation ↔
        (BtoD.Flat ∧ BtoD.FinitePresentation) ∧
          (A'toC'.Flat ∧ A'toC'.FinitePresentation)) ∧
      (toD'.Smooth ↔ BtoD.Smooth ∧ A'toC'.Smooth) ∧
      (toD'.Etale ↔ BtoD.Etale ∧ A'toC'.Etale) ∧
      (∀ (E : Type u) [CommRing E] (f : base.fibreProduct →+* E), f.Flat →
        let s : RelativeModuleFibreProductSituation (D' := E) base := ⟨f⟩
        Function.Bijective s.toRelativePullback) ∧
      ∃ q : (flat.Under ⊤ (CommRingCat.of base.fibreProduct)) ≌
          CategoricalPullback BtoA A'toA,
        Nonempty (q.functor ⋙ CategoricalPullback.π₁ BtoA A'toA ≅ B'toB) ∧
          Nonempty (q.functor ⋙ CategoricalPullback.π₂ BtoA A'toA ≅ B'toA') := by
  obtain ⟨hft, hflat, hfp, hsmooth, hetale, hreconstruct⟩ :=
    ringHom_properties_pullback_iff_and_reconstruction toBase surjection I base
      BtoD A'toC' AtoC DtoC C'toC hD hC'
  exact ⟨hft, hflat, hfp, hsmooth, hetale, hreconstruct,
    flatAlgebrasOverFibreProduct_equivalence toBase surjection I base⟩

end MilnorPatching

end
