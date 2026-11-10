module

public import Mathlib
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkwiseExactness
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.AffineSections
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.EmptySupportVanishing
public import StacksFrontier.AlgebraicGeometry.DevissageNoetherian.Support
public import StacksFrontier.AlgebraicGeometry.Modules.StalkMono
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.QuasicoherentCriteria
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.AffineOfModuleCategory
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineTilde
public import StacksFrontier.RingTheory.Flat.UniversallyInjective
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# Monomorphy of a module map after an arbitrary base change

The dévissage step of [Stacks, Tag 0815] presents the module being flattened as the middle term
of a short exact sequence `0 → 𝒪_X^{⊕ r} → ℱ → ℋ → 0`, and feeds that sequence to
[Stacks, Tag 080W] (`AlgebraicGeometry.strictTransformSheaf_shortExact`), which asks for the
sequence to stay short exact after *every* base change of the base. Right exactness is automatic,
since pullback of modules is a left adjoint; what has to be proved is that the pullback of the
first map stays a monomorphism.

That is what this file supplies, from the algebraic hypothesis the source's Tags 05I3 and 05CL
produce: **universal injectivity** of the map of sections over the affine charts, in the sense of
[Stacks, Tag 058K] (`Stacks.UniversalInjectivity.LocalizationCriteria.UniversallyInjective`).

## Main results

* `AlgebraicGeometry.mono_pullback_map_of_universallyInjective`: if the map of sections of `α`
  over every affine open of `X` lying above an affine open of `S` is universally injective over
  the ring of that open of `S`, then the pullback of `α` to `X ×_S T` is a monomorphism, for
  every `T ⟶ S`.
* `AlgebraicGeometry.shortExact_map_pullback_of_universallyInjective`: hence a short exact
  sequence whose first map has that property stays short exact after every base change — the
  hypothesis of [Stacks, Tag 080W].

## Implementation notes

The reduction to algebra is by charts. A point of `X ×_S T` lies in the image of
`Spec (Γ(X, U) ⊗_{Γ(S, V)} Γ(T, W)) ⟶ X ×_S T` for suitable affine opens `U ⊆ X`, `V ⊆ S`,
`W ⊆ T`, and on that chart the pullback of `α` is the associated sheaf of the extension of
scalars of the map of sections. Extension of scalars along `Γ(X, U) → Γ(X, U) ⊗_{Γ(S, V)}
Γ(T, W)` is injective exactly because the map of sections is universally injective over
`Γ(S, V)`: the base change `(A ⊗_R R') ⊗_A M ≅ M ⊗_R R'` turns it into tensoring with the
`Γ(S, V)`-module `Γ(T, W)`. Monomorphy is then local on `X ×_S T`, and the charts cover it.

Monomorphy is checked through the stalks of the underlying presheaves of abelian groups, which is
a third reading of "monomorphism" beside the two the repository already records for modules on a
scheme (see `StacksFrontier/AlgebraicGeometry/Modules/StalkMono.lean`): the functor
`Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor` is the one along which the
restriction-to-an-open comparison `Scheme.Modules.restrictStalkNatIso` is available, which is
what makes monomorphy local on the base here. The private helpers below work in that reading
only.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 080W](https://stacks.math.columbia.edu/tag/080W)
* [Stacks Project, Tag 058K](https://stacks.math.columbia.edu/tag/058K)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.UniversalInjectivity.LocalizationCriteria

universe u

namespace AlgebraicGeometry

/-- **The stalk of the underlying presheaf of abelian groups is an exact functor.** The functor
`Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor` is additive, and takes a short
exact sequence of modules to a short exact sequence of abelian groups by [Stacks, Tag 01AG]
(`AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact`), so it preserves finite
limits and finite colimits. -/
theorem Scheme.Modules.presheafStalk_preservesFiniteLimitsAndColimits
    {X : Scheme.{u}} (x : X) :
    PreservesFiniteLimits (Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) ∧
    PreservesFiniteColimits (Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x) := by
  let A := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : A.Additive := by
    refine ⟨?_⟩
    intro F G a b
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map (a + b).mapPresheaf = _
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (a.mapPresheaf + b.mapPresheaf) = _
    exact Functor.map_add _
  exact (A.exact_tfae.out 2 4).mp fun D hD =>
    (AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact _ D).mp hD x

/-- A module whose presheaf-of-abelian-groups stalk at `x` is zero has no support at `x`. -/
theorem Scheme.Modules.notMem_supp_of_presheafStalk_isZero {X : Scheme.{u}}
    (F : X.Modules) (x : X)
    (hx : IsZero ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj F)) :
    x ∉ SheafOfModules.supp F := by
  intro ⟨a, ha⟩
  exact ha (AddCommGrpCat.subsingleton_of_isZero hx |>.elim a 0)


private def pullbackOpenStalkIso {X : Scheme.{u}} (V : X.Opens) (x : V) :
    Scheme.Modules.pullback V.ι ⋙ Scheme.Modules.toPresheaf V.toScheme ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x ≅
      Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x.val :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback V.ι).symm _ ≪≫
    Scheme.Modules.restrictStalkNatIso V.ι x


private theorem mono_map_of_natIso {C D : Type*} [Category C] [Category D]
    {F₁ F₂ : C ⥤ D} (e : F₁ ≅ F₂) {A B : C} (h : A ⟶ B) (hm : Mono (F₁.map h)) :
    Mono (F₂.map h) := by
  have key : e.inv.app A ≫ F₁.map h ≫ e.hom.app B = F₂.map h := by
    rw [e.hom.naturality h, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  rw [← key]
  have : Mono (F₁.map h ≫ e.hom.app B) := mono_comp _ _
  exact mono_comp _ _

/-- Cancelling an isomorphism on the left preserves monomorphy. -/
private theorem mono_of_mono_iso_comp {C : Type*} [Category C] {A B D : C} (i : A ⟶ B) [IsIso i]
    (m : B ⟶ D) (h : Mono (i ≫ m)) : Mono m := by
  have hm : m = inv i ≫ (i ≫ m) := by simp
  rw [hm]
  exact mono_comp _ _

/-- **A morphism of modules on a scheme is a monomorphism as soon as it is one on the stalks of
the underlying presheaves of abelian groups.**

This is a third reading of the stalkwise criterion for monomorphy, beside
`AlgebraicGeometry.SheafOfModules.mono_of_stalk_mono`, which is stated for the stalk functor
landing in modules over the local ring, and the two readings of `Mono` itself recorded in
`StacksFrontier/AlgebraicGeometry/Modules/StalkMono.lean`. The functor used here is the one along
which the restriction-to-an-open comparison `Scheme.Modules.restrictStalkNatIso` is available,
which is what makes monomorphy local on the base below. -/
theorem Scheme.Modules.mono_of_presheafStalk_mono {X : Scheme.{u}} {G F : X.Modules} (β : G ⟶ F)
    (hβ : ∀ x : X, Mono ((Scheme.Modules.toPresheaf X ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map β)) : Mono β := by
  have hsupp : SheafOfModules.supp (kernel β) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    let A := Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
    have : PreservesFiniteLimits A :=
      (Scheme.Modules.presheafStalk_preservesFiniteLimitsAndColimits x).1
    have : Mono (A.map β) := hβ x
    have hz : IsZero (A.obj (kernel β)) :=
      (isZero_kernel_of_mono (A.map β)).of_iso (PreservesKernel.iso A β)
    exact Scheme.Modules.notMem_supp_of_presheafStalk_isZero _ x hz hx
  exact Abelian.mono_of_kernel_ι_eq_zero _
    ((_root_.SheafOfModules.isZero_of_supp_eq_empty _ hsupp).eq_of_src _ _)


/-- Monomorphy of a morphism of sheaves of modules is local on the base: it suffices to
check it after restriction to the members of an open cover. -/
private theorem mono_of_opens_cover {Y : Scheme.{u}} {G F : Y.Modules} (β : G ⟶ F)
    {ι : Type*} (V : ι → Y.Opens) (hcov : ∀ y : Y, ∃ i, y ∈ V i)
    (h : ∀ i, Mono ((Scheme.Modules.pullback (V i).ι).map β)) : Mono β := by
  apply Scheme.Modules.mono_of_presheafStalk_mono
  intro y
  obtain ⟨i, hy⟩ := hcov y
  let z : (V i) := ⟨y, hy⟩
  let B := Scheme.Modules.toPresheaf (V i).toScheme ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} z
  have : PreservesFiniteLimits B :=
    (Scheme.Modules.presheafStalk_preservesFiniteLimitsAndColimits (X := (V i).toScheme) z).1
  have hpm : B.PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape B
  have hm : Mono (B.map ((Scheme.Modules.pullback (V i).ι).map β)) := by
    have := h i
    exact B.map_mono _
  exact mono_map_of_natIso (pullbackOpenStalkIso (V i) z) β hm

/-- Pulling back along an isomorphism of schemes is a faithful operation on modules. -/
private instance faithful_pullback_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    (Scheme.Modules.pullback e.hom).Faithful := by
  refine Functor.Faithful.of_comp_iso (G := Scheme.Modules.pullback e.inv)
    (H := 𝟭 Y.Modules) ?_
  exact Scheme.Modules.pullbackComp e.inv e.hom ≪≫
    Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫ Scheme.Modules.pullbackId Y


/-- Monomorphy of a restriction to the range of an open immersion follows from monomorphy
of the pullback along that open immersion. -/
private theorem mono_pullback_opensRange {Y Z : Scheme.{u}} (c : Z ⟶ Y)
    [IsOpenImmersion c] {G F : Y.Modules} (β : G ⟶ F)
    (h : Mono ((Scheme.Modules.pullback c).map β)) :
    Mono ((Scheme.Modules.pullback c.opensRange.ι).map β) := by
  have hc : c.isoOpensRange.hom ≫ c.opensRange.ι = c := by
    rw [← c.isoOpensRange_inv_comp, Iso.hom_inv_id_assoc]
  rw [← hc] at h
  have h2 := mono_map_of_natIso
    (Scheme.Modules.pullbackComp c.isoOpensRange.hom c.opensRange.ι).symm β h
  exact (Scheme.Modules.pullback c.isoOpensRange.hom).mono_of_mono_map h2

/-- The associated-sheaf functor turns an injective map of modules into a monomorphism. -/
private theorem mono_tilde_map_of_injective (R : CommRingCat.{u}) {M N : ModuleCat.{u} R}
    (b : M ⟶ N) (hb : Function.Injective b.hom) : Mono ((tilde.functor R).map b) := by
  have : Mono b := (ModuleCat.mono_iff_injective b).mpr hb
  have : PreservesLimitsOfShape WalkingCospan (tilde.functor R) :=
    PreservesFiniteLimits.preservesFiniteLimits (F := tilde.functor R) WalkingCospan
  have : (tilde.functor R).PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  exact (tilde.functor R).map_mono b

/-- A square over a monomorphism is a pullback square precisely over its target. -/
private theorem isPullback_of_mono_comp {C : Type*} [Category C] {U W V T : C}
    (a : U ⟶ V) (b : W ⟶ V) (i : V ⟶ T) [Mono i] [HasPullback a b] :
    IsPullback (pullback.fst a b) (pullback.snd a b) (a ≫ i) (b ≫ i) := by
  have ht : IsPullback b (𝟙 W) i (b ≫ i) := by
    refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk (by simp) (fun s => s.snd) ?_ ?_ ?_)
    · intro s
      refine (cancel_mono i).mp ?_
      rw [Category.assoc, ← s.condition]
    · intro s; simp
    · intro s m h1 h2; simpa using h2
  simpa using (IsPullback.of_hasPullback a b).paste_vert ht

/-- Restricting the left leg of a fibre product along a morphism gives a pullback square
over the first projection. -/
private theorem isPullback_leftChart {X Y Z U : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) (u : U ⟶ X) :
    IsPullback (pullback.fst (u ≫ f) g)
      (pullback.lift (pullback.fst (u ≫ f) g ≫ u) (pullback.snd (u ≫ f) g)
        (by rw [Category.assoc]; exact pullback.condition))
      u (pullback.fst f g) := by
  apply IsPullback.of_bot (v₂₁ := pullback.snd f g) (v₂₂ := f) ?_ ?_
    (IsPullback.of_hasPullback f g)
  · rw [pullback.lift_snd]
    exact IsPullback.of_hasPullback (u ≫ f) g
  · rw [pullback.lift_fst]

/-- Restricting the right leg of a fibre product along a morphism gives a pullback square
over the second projection. -/
private theorem isPullback_rightChart {X Y Z W : Scheme.{u}}
    (f : X ⟶ Z) (g : Y ⟶ Z) (w : W ⟶ Y) :
    IsPullback (pullback.snd f (w ≫ g))
      (pullback.lift (pullback.fst f (w ≫ g)) (pullback.snd f (w ≫ g) ≫ w)
        (by rw [Category.assoc]; exact pullback.condition))
      w (pullback.snd f g) := by
  apply IsPullback.of_bot (v₂₁ := pullback.fst f g) (v₂₂ := g) ?_ ?_
    (IsPullback.of_hasPullback f g).flip
  · rw [pullback.lift_fst]
    exact (IsPullback.of_hasPullback f (w ≫ g)).flip
  · rw [pullback.lift_snd]


open scoped TensorProduct in
/-- The comparison identifying base change along the inclusion of the left tensor factor
with base change of scalars along the right one. -/
private noncomputable def leftIncludeBaseChangeEquiv
    (R A R' : Type u) [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    (M : Type u) [AddCommGroup M] [Module A M] [Module R M] [IsScalarTower R A M] :
    (A ⊗[R] R') ⊗[A] M ≃ₗ[A] M ⊗[R] R' :=
  (TensorProduct.comm A (A ⊗[R] R') M).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R A A M R')

open scoped TensorProduct in
/-- Base change of a universally injective module map along the inclusion of the left factor
of a tensor product of algebras stays injective. -/
private theorem injective_baseChange_of_universallyInjective
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    {M N : Type u} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    [Module R M] [Module R N] [IsScalarTower R A M] [IsScalarTower R A N]
    (b : M →ₗ[A] N) (hb : _root_.UniversallyInjective (b.restrictScalars R)) :
    Function.Injective (LinearMap.baseChange (A ⊗[R] R') b) := by
  have hsq : ∀ x : (A ⊗[R] R') ⊗[A] M,
      leftIncludeBaseChangeEquiv R A R' N (LinearMap.baseChange (A ⊗[R] R') b x) =
        ((b.restrictScalars R).rTensor R') (leftIncludeBaseChangeEquiv R A R' M x) := by
    have htmul : ∀ (c : A ⊗[R] R') (m : M),
        leftIncludeBaseChangeEquiv R A R' N (LinearMap.baseChange (A ⊗[R] R') b (c ⊗ₜ m)) =
          ((b.restrictScalars R).rTensor R')
            (leftIncludeBaseChangeEquiv R A R' M (c ⊗ₜ m)) := by
      intro c m
      induction c using TensorProduct.inductionOn with
      | tmul a r => simp [leftIncludeBaseChangeEquiv]
      | add c₁ c₂ h₁ h₂ => rw [TensorProduct.add_tmul]; simp only [map_add, h₁, h₂]
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul c m => exact htmul c m
    | add x y hx hy => simp only [map_add, hx, hy]
  have hinj := hb R'
  intro x y hxy
  apply (leftIncludeBaseChangeEquiv R A R' M).injective
  apply hinj
  rw [← hsq x, ← hsq y, hxy]


/-- Monomorphy of a pullback of a morphism of quasi-coherent modules on an affine scheme
can be tested on the associated sheaf of its map of global sections. -/
private theorem mono_pullback_map_of_mono_tilde {A : CommRingCat.{u}} {Z : Scheme.{u}}
    (h : Z ⟶ Spec A) {G' F' : (Spec A).Modules} [G'.IsQuasicoherent] [F'.IsQuasicoherent]
    (β : G' ⟶ F')
    (hm : Mono ((Scheme.Modules.pullback h).map
      ((moduleSpecΓFunctor ⋙ tilde.functor A).map β))) :
    Mono ((Scheme.Modules.pullback h).map β) := by
  have : IsIso (Scheme.Modules.fromTildeΓNatTrans.app G') :=
    (inferInstance : IsIso G'.fromTildeΓ)
  have : IsIso (Scheme.Modules.fromTildeΓNatTrans.app F') :=
    (inferInstance : IsIso F'.fromTildeΓ)
  have : IsIso ((Scheme.Modules.pullback h).map
      (Scheme.Modules.fromTildeΓNatTrans.app G')) := Functor.map_isIso _ _
  have : IsIso ((Scheme.Modules.pullback h).map
      (Scheme.Modules.fromTildeΓNatTrans.app F')) := Functor.map_isIso _ _
  have h1 : Mono ((Scheme.Modules.pullback h).map
      ((moduleSpecΓFunctor ⋙ tilde.functor A).map β) ≫
      (Scheme.Modules.pullback h).map
        (Scheme.Modules.fromTildeΓNatTrans.app F')) := mono_comp _ _
  rw [← Functor.map_comp, Scheme.Modules.fromTildeΓNatTrans.naturality β,
    Functor.map_comp] at h1
  exact mono_of_mono_iso_comp _ _ h1


/-- Transport of injectivity of a base change along an equality of algebra structures. -/
private theorem injective_baseChange_of_algebra_eq {A C : Type u} [CommSemiring A] [Semiring C]
    {M N : Type u} [AddCommMonoid M] [Module A M] [AddCommMonoid N] [Module A N]
    {i j : Algebra A C} (h : i = j) (b : M →ₗ[A] N)
    (hb : letI := j; Function.Injective (LinearMap.baseChange C b)) :
    letI := i; Function.Injective (LinearMap.baseChange C b) := by
  cases h
  exact hb

open scoped TensorProduct in
/-- `injective_baseChange_of_universallyInjective` in the form produced by Mathlib's
extension-of-scalars functor, which is what the affine pullback comparison speaks. -/
private theorem injective_extendScalars_map_of_universallyInjective
    {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']
    {M N : ModuleCat.{u} A} (b : M ⟶ N)
    (hb : _root_.UniversallyInjective
      ((ModuleCat.restrictScalars (algebraMap R A)).map b).hom) :
    Function.Injective ((ModuleCat.extendScalars
      (CommRingCat.ofHom (algebraMap A (A ⊗[R] R'))).hom).map b).hom := by
  let iM : Module R (M : Type u) := Module.compHom _ (algebraMap R A)
  let iN : Module R (N : Type u) := Module.compHom _ (algebraMap R A)
  have hM : IsScalarTower R A (M : Type u) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hN : IsScalarTower R A (N : Type u) := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have key : Function.Injective (LinearMap.baseChange (A ⊗[R] R') b.hom) :=
    @injective_baseChange_of_universallyInjective R A R' _ _ _ _ _ (M : Type u) (N : Type u)
      _ _ _ _ iM iN hM hN b.hom hb
  let inst : Algebra A (A ⊗[R] R') := (algebraMap A (A ⊗[R] R')).toAlgebra
  change Function.Injective (b.hom.baseChange (A ⊗[R] R'))
  refine injective_baseChange_of_algebra_eq (i := inst) ?_ _ key
  exact Algebra.algebra_ext _ _ fun _ => rfl

open scoped TensorProduct in
/-- **The chart computation.** On the affine chart `Spec (A ⊗[R] R')` over an affine chart
`Spec A` of `X`, the pullback of a map of quasi-coherent modules which is universally
injective over `R` on sections is a monomorphism. -/
private theorem mono_pullback_tensorChart
    (R : Type u) [CommRing R] (A : CommRingCat.{u}) [Algebra R A] (R' : Type u) [CommRing R']
    [Algebra R R']
    {Y : Scheme.{u}} {G F : Y.Modules} (α : G ⟶ F) (u : Spec A ⟶ Y)
    [((Scheme.Modules.pullback u).obj G).IsQuasicoherent]
    [((Scheme.Modules.pullback u).obj F).IsQuasicoherent]
    (hα : _root_.UniversallyInjective
      ((ModuleCat.restrictScalars (algebraMap R A)).map
        (moduleSpecΓFunctor.map ((Scheme.Modules.pullback u).map α))).hom) :
    Mono ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] R'))) ≫ u)).map α) := by
  refine mono_map_of_natIso (Scheme.Modules.pullbackComp
    (Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] R')))) u) α ?_
  refine mono_pullback_map_of_mono_tilde _ ((Scheme.Modules.pullback u).map α) ?_
  refine mono_map_of_natIso (AlgebraicGeometry.pullbackTildeIso
    A (CommRingCat.of (A ⊗[R] R'))
    (CommRingCat.ofHom (algebraMap A (A ⊗[R] R')))).symm
    (moduleSpecΓFunctor.map ((Scheme.Modules.pullback u).map α)) ?_
  refine mono_tilde_map_of_injective _ _ ?_
  exact injective_extendScalars_map_of_universallyInjective (R := R) (R' := R') _ hα


/-- A point in the image of an open immersion is hit by the parallel leg of any pullback
square over it. -/
private theorem mem_range_of_isPullback {P X Y Z : Scheme.{u}} {p₁ : P ⟶ X} {p₂ : P ⟶ Y}
    {i : X ⟶ Z} {k : Y ⟶ Z} (h : IsPullback p₁ p₂ i k) [IsOpenImmersion i] (y : Y)
    (hy : k y ∈ Set.range i.base) : y ∈ Set.range p₂.base := by
  have hy' : y ∈ Set.range (pullback.snd i k).base := by
    rw [IsOpenImmersion.range_pullbackSnd i k]
    exact hy
  obtain ⟨r, hr⟩ := hy'
  have he : h.isoPullback.inv ≫ p₂ = pullback.snd i k :=
    (Iso.inv_comp_eq _).2 h.isoPullback_hom_snd.symm
  refine ⟨h.isoPullback.inv r, ?_⟩
  rw [← Scheme.Hom.comp_apply, he]
  exact hr


/-- The open chart of a fibre product obtained by restricting its left leg. -/
private theorem exists_leftChart {X Y Z U : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (u : U ⟶ X) :
    ∃ m : pullback (u ≫ f) g ⟶ pullback f g,
      IsPullback (pullback.fst (u ≫ f) g) m u (pullback.fst f g) ∧
        m ≫ pullback.snd f g = pullback.snd (u ≫ f) g :=
  ⟨_, isPullback_leftChart f g u, pullback.lift_snd _ _ _⟩

/-- The open chart of a fibre product obtained by restricting its right leg. -/
private theorem exists_rightChart {X Y Z W : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) (w : W ⟶ Y) :
    ∃ m : pullback f (w ≫ g) ⟶ pullback f g,
      IsPullback (pullback.snd f (w ≫ g)) m w (pullback.snd f g) ∧
        m ≫ pullback.fst f g = pullback.fst f (w ≫ g) :=
  ⟨_, isPullback_rightChart f g w, pullback.lift_fst _ _ _⟩

/-- Precomposition with an isomorphism does not change the image of a morphism. -/
private theorem mem_range_comp_of_isIso {X Y Z : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (k : Y ⟶ Z)
    (z : Z) (h : z ∈ Set.range k.base) : z ∈ Set.range (e ≫ k).base := by
  obtain ⟨y, hy⟩ := h
  refine ⟨(asIso e).inv y, ?_⟩
  have he : e ((asIso e).inv y) = y := by
    rw [← Scheme.Hom.comp_apply]
    simp
  rw [Scheme.Hom.comp_apply, he]
  exact hy


/-- The chart of `X ×ₛ T` through affine opens `U ⊆ f ⁻¹ V` and `W ⊆ g ⁻¹ V` around `z`, on
which the pullback of `α` is a monomorphism. -/
private theorem exists_chart_mono_of_affine_opens
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) {G F : X.Modules}
    [G.IsQuasicoherent] [F.IsQuasicoherent] (α : G ⟶ F) (z : (pullback f g : Scheme.{u}))
    {V : S.Opens} (hV : IsAffineOpen V) {U : X.Opens} (hU : IsAffineOpen U)
    {W : T.Opens} (hW : IsAffineOpen W) (hUV : U ≤ f ⁻¹ᵁ V) (hWV : W ≤ g ⁻¹ᵁ V)
    (hxU : pullback.fst f g z ∈ (U : Set X)) (htW : pullback.snd f g z ∈ (W : Set T))
    (hα : letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      _root_.UniversallyInjective
        ((ModuleCat.restrictScalars (algebraMap Γ(S, V) Γ(X, U))).map
          (moduleSpecΓFunctor.map ((Scheme.Modules.pullback hU.fromSpec).map α))).hom) :
    ∃ (Z : Scheme.{u}) (c : Z ⟶ pullback f g), IsOpenImmersion c ∧
      z ∈ Set.range c.base ∧
      Mono ((Scheme.Modules.pullback (c ≫ pullback.fst f g)).map α) := by
  let hGqc : SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) G :=
    inferInstanceAs (SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) G)
  let hFqc : SheafOfModules.IsQuasicoherent (R := structureSheafRing X.toRingedSpace) F :=
    inferInstanceAs (SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) F)
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  let : Algebra Γ(S, V) Γ(T, W) := (g.appLE V W hWV).hom.toAlgebra
  have huf : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U))) ≫ hV.fromSpec =
      hU.fromSpec ≫ f := IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hUV
  have hwg : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(T, W))) ≫ hV.fromSpec =
      hW.fromSpec ≫ g := IsAffineOpen.SpecMap_appLE_fromSpec g hV hW hWV
  have hk : IsPullback
      (pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U))))
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(T, W)))))
      (pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U))))
        (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) Γ(T, W)))))
      (hU.fromSpec ≫ f) (hW.fromSpec ≫ g) := by
    rw [← huf, ← hwg]
    exact isPullback_of_mono_comp _ _ hV.fromSpec
  obtain ⟨m₁, h1, h1'⟩ := exists_leftChart f g hU.fromSpec
  obtain ⟨m₂, h2, h2'⟩ := exists_rightChart (hU.fromSpec ≫ f) g hW.fromSpec
  have : IsOpenImmersion m₁ := MorphismProperty.of_isPullback h1 inferInstance
  have : IsOpenImmersion m₂ := MorphismProperty.of_isPullback h2 inferInstance
  refine ⟨_, (pullbackSpecIso Γ(S, V) Γ(X, U) Γ(T, W)).inv ≫
    hk.isoPullback.hom ≫ m₂ ≫ m₁, inferInstance, ?_, ?_⟩
  · obtain ⟨z₁, hz₁⟩ := mem_range_of_isPullback h1 z (by rwa [hU.range_fromSpec])
    obtain ⟨z₂, hz₂⟩ := mem_range_of_isPullback h2 z₁ (by
      rwa [hW.range_fromSpec, ← h1', Scheme.Hom.comp_apply, hz₁])
    refine mem_range_comp_of_isIso _ _ z (mem_range_comp_of_isIso _ _ z ⟨z₂, ?_⟩)
    rw [Scheme.Hom.comp_apply, hz₂, hz₁]
  · rw [Category.assoc, Category.assoc, Category.assoc, ← h1.w, reassoc_of% h2',
      hk.isoPullback_hom_fst_assoc, pullbackSpecIso_inv_fst_assoc]
    have : ((Scheme.Modules.pullback hU.fromSpec).obj G).IsQuasicoherent :=
      @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
        hU.fromSpec.toLRSHom.toShHom G hGqc
    have : ((Scheme.Modules.pullback hU.fromSpec).obj F).IsQuasicoherent :=
      @AlgebraicGeometry.SheafOfModules.modulePullback_isQuasicoherent _ _
        hU.fromSpec.toLRSHom.toShHom F hFqc
    exact mono_pullback_tensorChart Γ(S, V) Γ(X, U) Γ(T, W) α hU.fromSpec
      hα

/-- Monomorphy of the pullback of `α` to `X ×ₛ T` follows from monomorphy on charts covering it. -/
private theorem mono_pullback_fst_of_charts
    {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S) {G F : X.Modules} (α : G ⟶ F)
    (hchart : ∀ z : (pullback f g : Scheme.{u}),
      ∃ (Z : Scheme.{u}) (c : Z ⟶ pullback f g), IsOpenImmersion c ∧
        z ∈ Set.range c.base ∧
        Mono ((Scheme.Modules.pullback (c ≫ pullback.fst f g)).map α)) :
    Mono ((Scheme.Modules.pullback (pullback.fst f g)).map α) := by
  choose Z c hc hzc hmono using hchart
  refine mono_of_opens_cover _ (fun z => (c z).opensRange) (fun y => ⟨y, hzc y⟩) fun z => ?_
  have := hc z
  exact mono_pullback_opensRange (c z) _
    (mono_map_of_natIso (Scheme.Modules.pullbackComp (c z) (pullback.fst f g)).symm α (hmono z))

/-- A short exact sequence of modules stays short exact after pullback along `p` once the
pullback of its first map is a monomorphism. -/
private theorem shortExact_map_pullback_of_mono
    {X Y : Scheme.{u}} (p : X ⟶ Y) (C : ShortComplex Y.Modules) (hC : C.ShortExact)
    (hm : Mono ((Scheme.Modules.pullback p).map C.f)) :
    (C.map (Scheme.Modules.pullback p)).ShortExact := by
  obtain ⟨hex, hepi⟩ := (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (Scheme.Modules.pullback p)).mp inferInstance C hC
  exact { exact := hex, mono_f := hm, epi_g := hepi }


open scoped TensorProduct in
/-- **The bridge from module-level universal injectivity to monomorphy after base change.**
Let `f : X ⟶ S` and let `α` be a morphism of quasi-coherent modules on `X`.  Assume that for
every affine open `V` of `S` and every affine open `U` of `X` above it, the map of global
sections of `α` over `U` is universally injective as a map of `Γ(S, V)`-modules.  Then the
pullback of `α` to `X ×_S T` is a monomorphism for every scheme `T` over `S`.  This is the
hypothesis required by `AlgebraicGeometry.strictTransformSheaf_shortExact`. -/
theorem mono_pullback_map_of_universallyInjective
    {X S : Scheme.{u}} (f : X ⟶ S) {G F : X.Modules}
    [G.IsQuasicoherent] [F.IsQuasicoherent] (α : G ⟶ F)
    (hα : ∀ (V : S.Opens) (_ : IsAffineOpen V) (U : X.Opens) (hU : IsAffineOpen U)
      (hUV : U ≤ f ⁻¹ᵁ V),
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      _root_.UniversallyInjective
        ((ModuleCat.restrictScalars (algebraMap Γ(S, V) Γ(X, U))).map
          (moduleSpecΓFunctor.map ((Scheme.Modules.pullback hU.fromSpec).map α))).hom)
    {T : Scheme.{u}} (g : T ⟶ S) :
    Mono ((Scheme.Modules.pullback (pullback.fst f g)).map α) := by
  refine mono_pullback_fst_of_charts f g α fun z => ?_
  have hcond : f (pullback.fst f g z) = g (pullback.snd f g z) := by
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  obtain ⟨-, ⟨V : S.Opens, hV, rfl⟩, hsV, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f (pullback.fst f g z))) isOpen_univ
  obtain ⟨-, ⟨U : X.Opens, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show pullback.fst f g z ∈ (f ⁻¹ᵁ V : Set X) from hsV) (f ⁻¹ᵁ V).isOpen
  have htV : g (pullback.snd f g z) ∈ (V : Set S) := hcond ▸ hsV
  obtain ⟨-, ⟨W : T.Opens, hW, rfl⟩, htW, hWV⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open
      (show pullback.snd f g z ∈ (g ⁻¹ᵁ V : Set T) from htV) (g ⁻¹ᵁ V).isOpen
  exact exists_chart_mono_of_affine_opens f g α z hV hU hW hUV hWV hxU htW (hα V hV U hU hUV)


/-- **The hypothesis of [Stacks, Tag 080W], produced.** A short exact
sequence of quasi-coherent modules on `X` whose first map has universally injective sections
over every affine open of `X` above an affine open of `S` stays short exact after every base
change of `S`. -/
theorem shortExact_map_pullback_of_universallyInjective
    {X S : Scheme.{u}} (f : X ⟶ S) (C : ShortComplex X.Modules)
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] (hC : C.ShortExact)
    (hα : ∀ (V : S.Opens) (_ : IsAffineOpen V) (U : X.Opens) (hU : IsAffineOpen U)
      (hUV : U ≤ f ⁻¹ᵁ V),
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
      _root_.UniversallyInjective
        ((ModuleCat.restrictScalars (algebraMap Γ(S, V) Γ(X, U))).map
          (moduleSpecΓFunctor.map ((Scheme.Modules.pullback hU.fromSpec).map C.f))).hom)
    {T : Scheme.{u}} (g : T ⟶ S) :
    (C.map (Scheme.Modules.pullback (pullback.fst f g))).ShortExact :=
  shortExact_map_pullback_of_mono _ C hC
    (mono_pullback_map_of_universallyInjective f C.f hα g)

/-! ### The affine case -/

open scoped TensorProduct in
/-- **The bridge from module-level universal injectivity to monomorphy after base change.**
Let `f : X ⟶ S` and let `α` be a morphism of quasi-coherent modules on `X`.  Assume that for
every affine open `V` of `S` and every affine open `U` of `X` above it, the map of global
sections of `α` over `U` is universally injective as a map of `Γ(S, V)`-modules.  Then the
pullback of `α` to `X ×_S T` is a monomorphism for every scheme `T` over `S`.  This is the
hypothesis required by `AlgebraicGeometry.strictTransformSheaf_shortExact`. -/
theorem mono_pullback_map_of_universallyInjective_of_isAffine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) {G F : X.Modules}
    [G.IsQuasicoherent] [F.IsQuasicoherent] (α : G ⟶ F)
    (hUV : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens))
    (hα : letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ hUV).hom.toAlgebra
      _root_.UniversallyInjective
        ((ModuleCat.restrictScalars (algebraMap Γ(S, ⊤) Γ(X, ⊤))).map
          (moduleSpecΓFunctor.map
            ((Scheme.Modules.pullback (isAffineOpen_top X).fromSpec).map α))).hom)
    {T : Scheme.{u}} (g : T ⟶ S) :
    Mono ((Scheme.Modules.pullback (pullback.fst f g)).map α) := by
  refine mono_pullback_fst_of_charts f g α fun z => ?_
  obtain ⟨-, ⟨W : T.Opens, hW, rfl⟩, htW, hWV⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open
      (show pullback.snd f g z ∈ (g ⁻¹ᵁ (⊤ : S.Opens) : Set T) from trivial)
      (g ⁻¹ᵁ (⊤ : S.Opens)).isOpen
  exact exists_chart_mono_of_affine_opens f g α z (isAffineOpen_top S) (isAffineOpen_top X) hW
    hUV hWV trivial htW hα

/-- **The hypothesis of [Stacks, Tag 080W] produced on an affine chart.** The affine case of
`AlgebraicGeometry.shortExact_map_pullback_of_universallyInjective`. -/
theorem shortExact_map_pullback_of_universallyInjective_of_isAffine
    {X S : Scheme.{u}} [IsAffine X] [IsAffine S] (f : X ⟶ S) (C : ShortComplex X.Modules)
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] (hC : C.ShortExact)
    (hUV : (⊤ : X.Opens) ≤ f ⁻¹ᵁ (⊤ : S.Opens))
    (hα : letI : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appLE ⊤ ⊤ hUV).hom.toAlgebra
      _root_.UniversallyInjective
        ((ModuleCat.restrictScalars (algebraMap Γ(S, ⊤) Γ(X, ⊤))).map
          (moduleSpecΓFunctor.map
            ((Scheme.Modules.pullback (isAffineOpen_top X).fromSpec).map C.f))).hom)
    {T : Scheme.{u}} (g : T ⟶ S) :
    (C.map (Scheme.Modules.pullback (pullback.fst f g))).ShortExact :=
  shortExact_map_pullback_of_mono _ C hC
    (mono_pullback_map_of_universallyInjective_of_isAffine f C.f hUV hα g)

end AlgebraicGeometry

end
