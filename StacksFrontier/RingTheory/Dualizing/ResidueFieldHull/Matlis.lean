module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.AdicCompletion.Topology
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.RingTheory.Dualizing.ResidueFieldHull

/-!
# Matlis duality

Let `R` be a complete Noetherian local ring and let `E` be an injective hull of its residue field.
Matlis duality sends an `R`-module `M` to `Hom_R(M, E)`.  It exchanges the two chain conditions:
the dual of a module with the descending chain condition satisfies the ascending chain condition
and conversely, and the resulting contravariant functor is an anti-equivalence between the
category of Artinian `R`-modules and the category of Noetherian `R`-modules.  On both sides the
canonical map from a module to its double Matlis dual is an isomorphism.

The dual functor itself is Mathlib's `CategoryTheory.linearYoneda` evaluated at `E`, so it is not
duplicated here; `Dualizing.matlisDualityFunctorIso` records that the functor underlying the
anti-equivalence is that one.  Modules live in `ModuleCat.{max u v} R`, so the module universe is
independent of the universe of `R` while every dual keeps the same scalar ring; the residue field
is moved into that universe by `Dualizing.residueFieldModule`.

## Main definitions

* `Dualizing.ArtinianModules` and `Dualizing.NoetherianModules` — the full subcategories of
  `ModuleCat R` cut out by `IsArtinian` and `IsNoetherian`.
* `Dualizing.residueFieldModule` — the universe-lifted residue field, with unchanged scalars.
* `Dualizing.matlisBidual` and `Dualizing.matlisEvaluation` — the double-dual endofunctor and the
  canonical natural evaluation map into it.
* `Dualizing.matlisForward`, `Dualizing.matlisBackward`, `Dualizing.matlisUnitIso`,
  `Dualizing.matlisCounitIso` and `Dualizing.matlisDuality` — the anti-equivalence and its data.

## Main results

* `Dualizing.isIso_matlisEvaluation_of_isArtinian` and
  `Dualizing.isIso_matlisEvaluation_of_isNoetherian` — biduality on the two sides.
* `Dualizing.matlisDualityFunctorIso` — the anti-equivalence is induced by `Hom_R(-, E)`.

## References

* [Stacks Project, Tag 08Z9](https://stacks.math.columbia.edu/tag/08Z9)
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace Dualizing

/-- An order isomorphism of subobject lattices matching two monomorphisms transports
essentiality. -/
private lemma isEssentialMono_iff_of_orderIso
    {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroObject C] [Limits.HasPullbacks C]
    [Limits.HasZeroObject D] [Limits.HasPullbacks D]
    {A B : C} {A' B' : D} {f : A ⟶ B} {f' : A' ⟶ B'} [Mono f] [Mono f']
    (e : Subobject B ≃o Subobject B') (h : e (Subobject.mk f) = Subobject.mk f') :
    Module.IsEssentialMono f ↔ Module.IsEssentialMono f' := by
  change (∀ Q, Q ≠ ⊥ → Q ⊓ Subobject.mk f ≠ ⊥) ↔ ∀ Q, Q ≠ ⊥ → Q ⊓ Subobject.mk f' ≠ ⊥
  rw [← h]
  refine e.toEquiv.forall_congr fun Q => ?_
  change _ ↔ (e Q ≠ ⊥ → e Q ⊓ e _ ≠ ⊥)
  rw [← e.map_inf, ← e.map_bot]
  simp only [Ne, e.apply_eq_iff_eq]

private lemma essential_map_equivalence
    {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroObject C] [Limits.HasPullbacks C]
    [Limits.HasZeroObject D] [Limits.HasPullbacks D]
    (F : C ≌ D) {A B : C} (f : A ⟶ B) [Mono f]
    (hf : Module.IsEssentialMono f) :
    Module.IsEssentialMono (F.functor.map f) :=
  (isEssentialMono_iff_of_orderIso
    (Subobject.lowerEquivalence (MonoOver.congr (X := B) F)).toOrderIso rfl).mp hf

private lemma essential_reflect_equivalence
    {C D : Type*} [Category C] [Category D]
    [Limits.HasZeroObject C] [Limits.HasPullbacks C]
    [Limits.HasZeroObject D] [Limits.HasPullbacks D]
    (F : C ≌ D) {A B : C} (f : A ⟶ B) [Mono f]
    (hf : Module.IsEssentialMono (F.functor.map f)) :
    Module.IsEssentialMono f :=
  (isEssentialMono_iff_of_orderIso
    (Subobject.lowerEquivalence (MonoOver.congr (X := B) F)).toOrderIso rfl).mpr hf

private lemma essential_post_iso
    {C : Type*} [Category C] [Limits.HasZeroObject C] [Limits.HasPullbacks C]
    {A B B' : C} (f : A ⟶ B) [Mono f] (e : B ≅ B')
    (hf : Module.IsEssentialMono f) :
    Module.IsEssentialMono (f ≫ e.hom) :=
  (isEssentialMono_iff_of_orderIso (Subobject.mapIso e).toOrderIso (f' := f ≫ e.hom) rfl).mp hf

private lemma essential_pre_iso
    {C : Type*} [Category C] [Limits.HasZeroObject C] [Limits.HasPullbacks C]
    {A B D : C} (e : A ≅ B) (f : B ⟶ D) [Mono f]
    (hf : Module.IsEssentialMono f) :
    Module.IsEssentialMono (e.hom ≫ f) := by
  have hmk : Subobject.mk f = Subobject.mk (e.hom ≫ f) :=
    Subobject.mk_eq_mk_of_comm f (e.hom ≫ f) e.symm (by simp)
  intro Q hQ
  rw [← hmk]
  exact hf Q hQ

add_to_stacks 08Z9 "the functor" CategoryTheory.linearYoneda

/-- The full category of `R`-modules satisfying the descending chain condition. -/
public abbrev ArtinianModules (R : Type u) [CommRing R] :=
  (show ObjectProperty (ModuleCat.{max u v} R) from fun M ↦ IsArtinian R M).FullSubcategory

/-- The full category of `R`-modules satisfying the ascending chain condition. -/
public abbrev NoetherianModules (R : Type u) [CommRing R] :=
  (show ObjectProperty (ModuleCat.{max u v} R) from fun M ↦ IsNoetherian R M).FullSubcategory

/-- The residue field, canonically lifted into the universe in which the modules under
consideration live. The scalar ring is unchanged. -/
public noncomputable def residueFieldModule (R : Type u) [CommRing R] [IsLocalRing R] :
    ModuleCat.{max u v} R :=
  (ModuleCat.uliftFunctor.{v, u} R).obj
    (ModuleCat.of R (IsLocalRing.ResidueField R))

private noncomputable def residueFieldChangeIso
    (R : Type u) [CommRing R] [IsLocalRing R]
    (S : Type (max u v)) [CommRing S] [IsLocalRing S]
    (e : R ≃+* S) :
    residueFieldModule.{u, v} R ≅
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv e).functor.obj
        (ModuleCat.of S (IsLocalRing.ResidueField S)) := by
  let φ := IsLocalRing.ResidueField.mapEquiv e
  let l : ULift.{v} (IsLocalRing.ResidueField R) ≃ₗ[R]
      ((ModuleCat.restrictScalars (e : R →+* S)).obj
        (ModuleCat.of S (IsLocalRing.ResidueField S))) :=
    { toFun := fun x => φ x.down
      invFun := fun x => ULift.up (φ.symm x)
      left_inv := fun x => ULift.ext (φ.symm_apply_apply x.down)
      right_inv := fun x => φ.apply_symm_apply x
      map_add' := fun x y => map_add φ x.down y.down
      map_smul' := by
        intro r x
        change φ (IsLocalRing.residue R r * x.down) =
          IsLocalRing.residue S (e r) * φ x.down
        rw [map_mul]
        change IsLocalRing.ResidueField.map e (IsLocalRing.residue R r) * φ x.down = _
        rw [IsLocalRing.ResidueField.map_residue]
        rfl }
  exact LinearEquiv.toModuleIso l

private theorem transport_injective_hull
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (S : Type (max u v)) [CommRing S] [IsLocalRing S]
    (e : R ≃+* S)
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    ∃ (i' : ModuleCat.of S (IsLocalRing.ResidueField S) ⟶
        (ModuleCat.restrictScalars (e.symm : S →+* R)).obj E),
      ∃ (hmono : Mono i'), (letI : Mono i' := hmono; Module.IsInjectiveHull i') := by
  let F : ModuleCat.{max u v} S ≌ ModuleCat.{max u v} R :=
    ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let E' := (ModuleCat.restrictScalars (e.symm : S →+* R)).obj E
  let α := residueFieldChangeIso R S e
  let β := F.counitIso.app E
  let j : F.functor.obj (ModuleCat.of S (IsLocalRing.ResidueField S)) ⟶
      F.functor.obj E' := α.inv ≫ (i ≫ β.inv)
  have : Mono α.inv := by infer_instance
  have : Mono β.inv := by infer_instance
  have hbase : Mono (i ≫ β.inv) := mono_comp i β.inv
  let : Mono (i ≫ β.inv) := hbase
  have hj : Mono j := by dsimp [j]; exact mono_comp α.inv (i ≫ β.inv)
  let i' := F.functor.preimage j
  have hmap : F.functor.map i' = j := F.functor.map_preimage j
  have hmapMono : Mono (F.functor.map i') := by simpa only [hmap] using hj
  have hmono : Mono i' := F.functor.mono_of_mono_map hmapMono
  let : Mono i' := hmono
  have hessJ : Module.IsEssentialMono j :=
    essential_pre_iso α.symm (i ≫ β.inv) (essential_post_iso i β.symm hi.2)
  have hessMap : Module.IsEssentialMono (F.functor.map i') := by
    simpa only [hmap] using hessJ
  exact ⟨i', hmono, F.inverse.injective_obj_of_injective hi.1,
    essential_reflect_equivalence F i' hessMap⟩

private noncomputable def endRingChangeEquiv
    (R : Type u) [CommRing R] (S : Type (max u v)) [CommRing S]
    (e : R ≃+* S) (E : ModuleCat.{max u v} R) :
    Module.End R E ≃+* Module.End S
      ((ModuleCat.restrictScalars (e.symm : S →+* R)).obj E) := by
  let F := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let G := F.inverse
  letI : G.Full := F.full_inverse
  letI : Module S E := ((ModuleCat.restrictScalars (e.symm : S →+* R)).obj E).isModule
  exact {
    toFun := fun f => (G.map (ModuleCat.ofHom f)).hom
    invFun := fun f => (G.preimage (ModuleCat.ofHom f)).hom
    left_inv := by
      intro f
      change (G.preimage (G.map (ModuleCat.ofHom f))).hom = f
      simp
    right_inv := by
      intro f
      change (G.map (G.preimage (ModuleCat.ofHom f))).hom = f
      exact congrArg ModuleCat.Hom.hom (G.map_preimage (ModuleCat.ofHom f))
    map_add' := by intro f g; ext x; rfl
    map_mul' := by intro f g; ext x; rfl }

private theorem endRingChangeEquiv_algebraMap
    (R : Type u) [CommRing R] (S : Type (max u v)) [CommRing S]
    (e : R ≃+* S) (E : ModuleCat.{max u v} R) (r : R) :
    endRingChangeEquiv R S e E (algebraMap R (Module.End R E) r) =
      algebraMap S (Module.End S
        ((ModuleCat.restrictScalars (e.symm : S →+* R)).obj E)) (e r) := by
  let E' := (ModuleCat.restrictScalars (e.symm : S →+* R)).obj E
  let : Module S E' := E'.isModule
  let sc : SMulCommClass S S E' := ⟨fun s t x => by
    show e.symm s • (e.symm t • x) = e.symm t • (e.symm s • x)
    rw [smul_smul, smul_smul, mul_comm]⟩
  let tower : IsScalarTower S S E' := ⟨fun s t x => by
    show e.symm (s * t) • x = e.symm s • (e.symm t • x)
    rw [map_mul]
    exact mul_smul _ _ _⟩
  let : Algebra S (Module.End S E') :=
    @Module.End.instAlgebra S S E' _ _ _ E'.isModule E'.isModule sc inferInstance tower
  ext x
  show r • x = e.symm (e r) • x
  simp

private theorem algebraMap_end_bijective
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    Function.Bijective (algebraMap R (Module.End R E)) := by
  let S := ULift.{v, u} R
  let e : R ≃+* S := ULift.ringEquiv.symm
  let : IsLocalRing S := RingEquiv.isLocalRing e
  let : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  have hmax : (IsLocalRing.maximalIdeal R).map e = IsLocalRing.maximalIdeal S :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  let : IsAdicComplete (IsLocalRing.maximalIdeal S) S := by
    rw [← hmax]
    exact (IsAdicComplete.congr_ringEquiv (IsLocalRing.maximalIdeal R) e).mpr
      (inferInstance : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
  let E' := (ModuleCat.restrictScalars (e.symm : S →+* R)).obj E
  let : Module S E' := E'.isModule
  let sc : SMulCommClass S S (↑E') := ⟨fun s t x => by
    show e.symm s • (e.symm t • x) = e.symm t • (e.symm s • x)
    rw [smul_smul, smul_smul, mul_comm]⟩
  let tower : IsScalarTower S S (↑E') := ⟨fun s t x => by
    show e.symm (s * t) • x = e.symm s • (e.symm t • x)
    rw [map_mul]
    exact mul_smul _ _ _⟩
  let : Algebra S (Module.End S (↑E')) :=
    @Module.End.instAlgebra S S (↑E') _ _ _ E'.isModule E'.isModule sc inferInstance tower
  obtain ⟨i', hmono, hiTransport⟩ := transport_injective_hull R S e E i hi
  have : Mono i' := hmono
  have hi' : Module.IsInjectiveHull i' := hiTransport
  let j : ModuleCat.of S (S ⧸ IsLocalRing.maximalIdeal S) ⟶ ModuleCat.of S E' := i'
  have hj : Mono j := hmono
  let a : Module.End S E' ≃ₐ[S] AdicCompletion (IsLocalRing.maximalIdeal S) S := by
    let : Mono j := hj
    exact endAlgEquivAdicCompletion S E' j hi'
  let c := AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal S)
  let f := c.trans a.symm
  have hf : f.toAlgHom = algebraMap S (Module.End S E') :=
    RingHom.ext fun s => by simpa using f.commutes s
  have hS : Function.Bijective (algebraMap S (Module.End S E')) := by
    rw [← hf]
    exact f.bijective
  let eEnd := endRingChangeEquiv R S e E
  have heq (r : R) : eEnd (algebraMap R (Module.End R E) r) =
      algebraMap S (Module.End S E') (e r) := endRingChangeEquiv_algebraMap R S e E r
  have hfun : ⇑(algebraMap R (Module.End R E)) =
      ⇑eEnd.symm ∘ ⇑(algebraMap S (Module.End S E')) ∘ ⇑e :=
    funext fun r => (eEnd.symm_apply_apply _).symm.trans (congrArg eEnd.symm (heq r))
  rw [hfun]
  exact eEnd.symm.bijective.comp (hS.comp e.bijective)

private theorem isArtinian_hom_of_finite
    (R : Type u) [CommRing R] (M E : ModuleCat.{max u v} R)
    [Module.Finite R M] [IsArtinian R E] :
    IsArtinian R (M ⟶ E) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  have hfree : IsArtinian R ((Fin n → R) →ₗ[R] E) := by
    let : IsArtinian R (Fin n → E) := inferInstance
    exact isArtinian_of_linearEquiv (Module.piEquiv (Fin n) R E)
  exact (ModuleCat.homLinearEquiv (R := R) (S := R) (M := M) (N := E)).isArtinian_iff.mpr
    (isArtinian_of_injective (LinearMap.lcomp R E f)
      (LinearMap.lcomp_injective_of_surjective f hf))

private theorem isArtinian_of_injectiveHull_residueField
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (i : IsLocalRing.ResidueField R →ₗ[R] E)
    [Mono (ModuleCat.ofHom i)]
    (hi : Module.IsInjectiveHull (ModuleCat.ofHom i)) :
    IsArtinian R E := by
  apply (isArtinian_iff_powerTorsion_and_finiteSocle R E).mpr
  apply (powerTorsion_and_finiteSocle_iff_exists_finite_copresentation
    R E E i hi).mpr
  let f : E →ₗ[R] (Fin 1 → E) :=
    (LinearEquiv.piUnique R (fun _ : Fin 1 => E)).symm.toLinearMap
  let g : (Fin 1 → E) →ₗ[R] (Fin 0 → E) := 0
  refine ⟨1, 0, f, g, ?_, ?_⟩
  · exact (LinearEquiv.piUnique R (fun _ : Fin 1 => E)).symm.injective
  · exact (LinearMap.exact_zero_iff_surjective (Fin 0 → E) f).mpr
      (LinearEquiv.piUnique R (fun _ : Fin 1 => E)).symm.surjective

/-- Artinianity is invariant under the change of rings along a ring equivalence. -/
private theorem isArtinian_ringChange_iff
    (R : Type u) [CommRing R] (S : Type (max u v)) [CommRing S]
    (e : R ≃+* S) (M : ModuleCat.{max u v} R) :
    IsArtinian S ((ModuleCat.restrictScalars (e.symm : S →+* R)).obj M) ↔ IsArtinian R M := by
  let M' := (ModuleCat.restrictScalars (e.symm : S →+* R)).obj M
  let l : M →ₛₗ[(e : R →+* S)] M' :=
    { toFun := id
      map_add' := by intros; rfl
      map_smul' := by
        intro r x
        show r • x = e.symm (e r) • x
        simp }
  have hl : Function.Bijective l := ⟨fun _ _ h => h, fun y => ⟨y, rfl⟩⟩
  exact (LinearMap.isArtinian_iff_of_bijective l hl).symm

private theorem isArtinian_hull
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) : IsArtinian R E := by
  let S := ULift.{v, u} R
  let e : R ≃+* S := ULift.ringEquiv.symm
  let : IsLocalRing S := RingEquiv.isLocalRing e
  let : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  let E' := (ModuleCat.restrictScalars (e.symm : S →+* R)).obj E
  obtain ⟨i', hmono, hiTransport⟩ := transport_injective_hull R S e E i hi
  have : Mono i' := hmono
  have hE' : IsArtinian S E' := by
    let j : IsLocalRing.ResidueField S →ₗ[S] E' := i'.hom
    have : Mono (ModuleCat.ofHom j) := hmono
    exact isArtinian_of_injectiveHull_residueField S E' j hiTransport
  exact (isArtinian_ringChange_iff R S e E).mp hE'

private theorem isArtinian_hom_of_isNoetherian
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (E M : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) [IsNoetherian R M] :
    IsArtinian R (M ⟶ E) := by
  have : Module.Finite R M :=
    (isNoetherian_iff_module_finite R M).mp inferInstance
  have : IsArtinian R E := isArtinian_hull R E i hi
  exact isArtinian_hom_of_finite R M E

private theorem isNoetherian_hom_of_embedding_into_fin_hull
    (R : Type u) [CommRing R] (M E : ModuleCat.{max u v} R)
    [Module.Injective R E] [IsNoetherian R (Module.End R E)]
    (n : ℕ) (f : M →ₗ[R] (Fin n → E)) (hf : Function.Injective f) :
    IsNoetherian R (M ⟶ E) := by
  have hfree : IsNoetherian R ((Fin n → E) →ₗ[R] E) := by
    have : IsNoetherian R (Fin n → Module.End R E) := inferInstance
    exact isNoetherian_of_linearEquiv
      (LinearMap.lsum R (fun _ : Fin n => E) R)
  have hsurj : Function.Surjective (LinearMap.lcomp R E f) := by
    intro g
    obtain ⟨h, hh⟩ := Module.Injective.out f hf g
    exact ⟨h, LinearMap.ext hh⟩
  have hhom : IsNoetherian R (M →ₗ[R] E) :=
    isNoetherian_of_surjective (LinearMap.lcomp R E f)
      (LinearMap.range_eq_top.mpr hsurj)
  exact (ModuleCat.homLinearEquiv (R := R) (S := R) (M := M) (N := E))
    |>.isNoetherian_iff.mpr hhom

private theorem isNoetherian_hom_of_isArtinian_same
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (M E : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup E] [Module R E] [IsArtinian R M]
    [IsNoetherian R (Module.End R E)]
    (i : IsLocalRing.ResidueField R →ₗ[R] E)
    [Mono (ModuleCat.ofHom i)]
    (hi : Module.IsInjectiveHull (ModuleCat.ofHom i)) :
    IsNoetherian R (M →ₗ[R] E) := by
  have hparts := (isArtinian_iff_powerTorsion_and_finiteSocle R M).mp
    (inferInstance : IsArtinian R M)
  obtain ⟨n, m, f, g, hf, hfg⟩ :=
    (powerTorsion_and_finiteSocle_iff_exists_finite_copresentation
      R M E i hi).mp hparts
  have : CategoryTheory.Injective (ModuleCat.of R E) := hi.1
  have : Module.Injective R E := Module.injective_module_of_injective_object R E
  have h : IsNoetherian R (ModuleCat.of R M ⟶ ModuleCat.of R E) :=
    isNoetherian_hom_of_embedding_into_fin_hull R
      (ModuleCat.of R M) (ModuleCat.of R E) n f hf
  exact (ModuleCat.homLinearEquiv (R := R) (S := R)
    (M := ModuleCat.of R M) (N := ModuleCat.of R E)).isNoetherian_iff.mp h

private noncomputable def homRingChangeMap
    (R : Type u) [CommRing R] (S : Type (max u v)) [CommRing S]
    (e : R ≃+* S) (M E : ModuleCat.{max u v} R) :
    (M ⟶ E) →ₛₗ[(e : R →+* S)]
      ((ModuleCat.restrictScalars (e.symm : S →+* R)).obj M ⟶
        (ModuleCat.restrictScalars (e.symm : S →+* R)).obj E) := by
  let F := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let G := F.inverse
  exact {
    toFun := fun f => G.map f
    map_add' := by intro f g; ext x; rfl
    map_smul' := by
      intro r f
      ext x
      change r • f x = e.symm (e r) • f x
      simp }

private theorem homRingChangeMap_bijective
    (R : Type u) [CommRing R] (S : Type (max u v)) [CommRing S]
    (e : R ≃+* S) (M E : ModuleCat.{max u v} R) :
    Function.Bijective (homRingChangeMap R S e M E) := by
  let F := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  let G := F.inverse
  let : G.Full := F.full_inverse
  exact ⟨fun _ _ h => G.map_injective h, fun f => ⟨G.preimage f, G.map_preimage f⟩⟩

private theorem isNoetherian_end_ringChange
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (S : Type (max u v)) [CommRing S] [IsNoetherianRing S]
    (e : R ≃+* S) (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    IsNoetherian S (Module.End S
      ((ModuleCat.restrictScalars (e.symm : S →+* R)).obj E)) := by
  let E' := (ModuleCat.restrictScalars (e.symm : S →+* R)).obj E
  let : Module S E' := E'.isModule
  let a := endRingChangeEquiv R S e E
  have hsurj : Function.Surjective (algebraMap S (Module.End S E')) := by
    intro g
    obtain ⟨r, hr⟩ := (algebraMap_end_bijective R E i hi).2 (a.symm g)
    refine ⟨e r, ?_⟩
    rw [← endRingChangeEquiv_algebraMap R S e E r]
    simpa using congrArg a hr
  exact isNoetherian_of_surjective (Algebra.linearMap S (Module.End S E'))
    (LinearMap.range_eq_top.mpr hsurj)

private theorem isNoetherian_hom_of_isArtinian
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E M : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) [IsArtinian R M] :
    IsNoetherian R (M ⟶ E) := by
  let S := ULift.{v, u} R
  let e : R ≃+* S := ULift.ringEquiv.symm
  let : IsLocalRing S := RingEquiv.isLocalRing e
  let : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  let M' := (ModuleCat.restrictScalars (e.symm : S →+* R)).obj M
  let E' := (ModuleCat.restrictScalars (e.symm : S →+* R)).obj E
  let : Module S M' := M'.isModule
  let : Module S E' := E'.isModule
  let sc : SMulCommClass S S E' := ⟨fun s t x => by
    show e.symm s • (e.symm t • x) = e.symm t • (e.symm s • x)
    rw [smul_smul, smul_smul, mul_comm]⟩
  let tower : IsScalarTower S S E' := ⟨fun s t x => by
    show e.symm (s * t) • x = e.symm s • (e.symm t • x)
    rw [map_mul]
    exact mul_smul _ _ _⟩
  let : SMulCommClass S S E' := sc
  let : IsScalarTower S S E' := tower
  let alg : Algebra S (Module.End S E') :=
    @Module.End.instAlgebra S S E' _ _ _ E'.isModule E'.isModule sc inferInstance tower
  let : Algebra S (Module.End S E') := alg
  let : Module S (M' →ₗ[S] E') :=
    @LinearMap.module S S S M' E' _ _ _ _ M'.isModule E'.isModule
      (RingHom.id S) _ E'.isModule sc
  have : IsArtinian S M' := (isArtinian_ringChange_iff R S e M).mpr inferInstance
  have : IsNoetherian S (Module.End S E') :=
    isNoetherian_end_ringChange R S e E i hi
  obtain ⟨i', hmono, hiTransport⟩ := transport_injective_hull R S e E i hi
  let j : IsLocalRing.ResidueField S →ₗ[S] E' := i'.hom
  have : Mono (ModuleCat.ofHom j) := hmono
  have hlin : IsNoetherian S (M' →ₗ[S] E') :=
    isNoetherian_hom_of_isArtinian_same S M' E' j hiTransport
  have hcat : IsNoetherian S (M' ⟶ E') :=
    (@ModuleCat.homLinearEquiv S _ M' E' S _ E'.isModule sc)
      |>.isNoetherian_iff.mpr hlin
  exact (LinearMap.isNoetherian_iff_of_bijective
    (homRingChangeMap R S e M E) (homRingChangeMap_bijective R S e M E)).mpr hcat

/-- The endofunctor taking an `R`-module to its double dual with respect to `E`. -/
public def matlisBidual (R : Type u) [CommRing R] (E : ModuleCat.{max u v} R) :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R where
  obj M := ModuleCat.of R (ModuleCat.of R (M ⟶ E) ⟶ E)
  map {M N} f := ModuleCat.ofHom
    { toFun := fun phi ↦ ModuleCat.ofHom
        { toFun := fun g ↦ phi (f ≫ g)
          map_add' := by intros; simp
          map_smul' := by intros; simp }
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  map_id M := by ext phi g; rfl
  map_comp f g := by ext phi h; rfl

/-- The canonical evaluation map from a module to its double Matlis dual, natural in the module. -/
public def matlisEvaluation (R : Type u) [CommRing R] (E : ModuleCat.{max u v} R) :
    𝟭 (ModuleCat.{max u v} R) ⟶ matlisBidual R E where
  app M := ModuleCat.ofHom
    { toFun := fun m ↦ ModuleCat.ofHom
        { toFun := fun f ↦ f m
          map_add' := by intros; simp
          map_smul' := by intros; simp }
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
  naturality M N f := by ext m; rfl

@[simp]
public lemma matlisEvaluation_app_apply (R : Type u) [CommRing R]
    (E M : ModuleCat.{max u v} R) (m : M) (f : M ⟶ E) :
    ModuleCat.Hom.hom
      (show ModuleCat.of R (M ⟶ E) ⟶ E from (matlisEvaluation R E).app M m) f = f m :=
  rfl

private def freeRankOneHom (R : Type u) [CommRing R]
    (E : ModuleCat.{max u v} R) (x : E) :
    ModuleCat.of R (ULift.{v} R) ⟶ E :=
  ModuleCat.ofHom
    { toFun := fun r => r.down • x
      map_add' := fun _ _ => add_smul _ _ _
      map_smul' := fun _ _ => mul_smul _ _ _ }

private def freeRankOneHomLinear (R : Type u) [CommRing R]
    (E : ModuleCat.{max u v} R) :
    E →ₗ[R] (ModuleCat.of R (ULift.{v} R) ⟶ E) :=
  { toFun := freeRankOneHom R E
    map_add' := by intro x y; ext r; exact smul_add _ _ _
    map_smul' := by intro a x; ext r; exact smul_comm _ _ _ }

private theorem eval_bijective_freeRankOne
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    Function.Bijective
      ((matlisEvaluation R E).app (ModuleCat.of R (ULift.{v} R))) := by
  let M := ModuleCat.of R (ULift.{v} R)
  let q := freeRankOneHomLinear R E
  have hq (f : M ⟶ E) : q (f (ULift.up (1 : R))) = f := by
    ext s
    show s.down • f (ULift.up (1 : R)) = f s
    have hs : s = s.down • ULift.up (1 : R) := by ext; simp
    rw [hs, map_smul]
    simp
  have hb := algebraMap_end_bijective R E i hi
  constructor
  · intro x y h
    apply ULift.ext
    apply hb.1
    ext z
    exact congrArg (fun a : ModuleCat.of R (M ⟶ E) ⟶ E => a (q z)) h
  · intro a
    let t : Module.End R E := a.hom.comp q
    obtain ⟨r, hr⟩ := hb.2 t
    refine ⟨ULift.up r, ?_⟩
    apply ModuleCat.Hom.ext
    ext f
    have h := congrArg (fun k : Module.End R E => k (f (ULift.up (1 : R)))) hr
    change r • f (ULift.up (1 : R)) = a.hom (q (f (ULift.up (1 : R)))) at h
    rw [hq] at h
    show f (ULift.up r) = a.hom f
    simpa only [show ULift.up r = r • ULift.up (1 : R) from by ext; simp,
      map_smul] using h

private def evalLinear (R : Type*) [CommRing R]
    (E : Type*) [AddCommGroup E] [Module R E]
    (M : Type*) [AddCommGroup M] [Module R M] :
    M →ₗ[R] ((M →ₗ[R] E) →ₗ[R] E) :=
  { toFun := fun m =>
      { toFun := fun f => f m
        map_add' := by intros; simp
        map_smul' := by intros; simp }
    map_add' := by intros; ext; simp
    map_smul' := by intros; ext; simp }

private theorem evalLinear_surjective_of_surjective
    (R : Type*) [CommRing R]
    (E : Type w) [AddCommGroup E] [Module R E] [Module.Injective R E]
    (F M : Type w) [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M]
    (f : F →ₗ[R] M) (hf : Function.Surjective f)
    (hF : Function.Surjective (evalLinear R E F)) :
    Function.Surjective (evalLinear R E M) := by
  let df : (M →ₗ[R] E) →ₗ[R] (F →ₗ[R] E) := LinearMap.lcomp R E f
  have hdf : Function.Injective df := LinearMap.lcomp_injective_of_surjective f hf
  intro b
  obtain ⟨c, hc⟩ := Module.Injective.out df hdf b
  obtain ⟨a, ha⟩ := hF c
  refine ⟨f a, ?_⟩
  ext g
  have h := congrArg (fun k : (F →ₗ[R] E) →ₗ[R] E => k (df g)) ha
  change (df g) a = c (df g) at h
  show g (f a) = b g
  have h' : g (f a) = c (df g) := by simpa [df, LinearMap.lcomp] using h
  exact h'.trans (hc g)

private theorem evalLinear_bijective_of_surjective
    (R : Type*) [CommRing R]
    (E : Type w) [AddCommGroup E] [Module R E] [Module.Injective R E]
    (F M : Type w) [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M]
    (f : F →ₗ[R] M) (hf : Function.Surjective f)
    (hF : Function.Bijective (evalLinear R E F))
    (hK : Function.Surjective (evalLinear R E f.ker)) :
    Function.Bijective (evalLinear R E M) := by
  let df : (M →ₗ[R] E) →ₗ[R] (F →ₗ[R] E) := LinearMap.lcomp R E f
  let dk : (F →ₗ[R] E) →ₗ[R] (f.ker →ₗ[R] E) :=
    LinearMap.lcomp R E f.ker.subtype
  have hdf : Function.Injective df := LinearMap.lcomp_injective_of_surjective f hf
  have hdk : Function.Surjective dk := by
    intro g
    obtain ⟨h, hh⟩ := Module.Injective.out f.ker.subtype
      (Submodule.subtype_injective _) g
    exact ⟨h, LinearMap.ext hh⟩
  have hex₁ : Function.Exact df dk :=
    LinearMap.exact_lcomp_of_exact_of_surjective E
      (LinearMap.exact_subtype_ker_map f) hf
  have hex₂ : Function.Exact
      (LinearMap.lcomp R E dk) (LinearMap.lcomp R E df) :=
    LinearMap.exact_lcomp_of_exact_of_surjective E hex₁ hdk
  constructor
  · intro x y hxy
    have hzero : evalLinear R E M (x - y) = 0 := by
      rw [map_sub, sub_eq_zero.mpr hxy]
    obtain ⟨a, ha⟩ := hf (x - y)
    have ha₀ : (LinearMap.lcomp R E df) (evalLinear R E F a) = 0 := by
      ext g
      show g (f a) = 0
      rw [ha]
      exact congrArg (fun k : (M →ₗ[R] E) →ₗ[R] E => k g) hzero
    obtain ⟨b, hb⟩ := (hex₂ _).mp ha₀
    obtain ⟨k, hk⟩ := hK b
    have heq : evalLinear R E F (f.ker.subtype k) = evalLinear R E F a := by
      ext g
      have h₁ := congrArg (fun t : (f.ker →ₗ[R] E) →ₗ[R] E => t (dk g)) hk
      have h₂ := congrArg (fun t : (F →ₗ[R] E) →ₗ[R] E => t g) hb
      change g (f.ker.subtype k) = b (dk g) at h₁
      change b (dk g) = g a at h₂
      exact h₁.trans h₂
    have hak := hF.1 heq
    rw [← sub_eq_zero, ← ha, ← hak]
    exact k.property
  · exact evalLinear_surjective_of_surjective R E F M f hf hF.2

private theorem evalLinear_bijective_ulift
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    Function.Bijective (evalLinear R E (ULift.{v} R)) := by
  let M := ModuleCat.of R (ULift.{v} R)
  let e : (M ⟶ E) ≃ₗ[R] (ULift.{v} R →ₗ[R] E) :=
    ModuleCat.homLinearEquiv
  have hc := eval_bijective_freeRankOne R E i hi
  constructor
  · intro x y hxy
    apply hc.1
    apply ModuleCat.Hom.ext
    ext f
    exact congrArg (fun k : (ULift.{v} R →ₗ[R] E) →ₗ[R] E => k (e f)) hxy
  · intro a
    let b : ModuleCat.of R (M ⟶ E) ⟶ E := ModuleCat.ofHom (a.comp e.toLinearMap)
    obtain ⟨x, hx⟩ := hc.2 b
    refine ⟨x, ?_⟩
    ext g
    exact congrArg (fun k : ModuleCat.of R (M ⟶ E) ⟶ E => k (ModuleCat.ofHom g)) hx

private theorem evalLinear_bijective_of_linearEquiv
    (R : Type*) [CommRing R]
    (E : Type*) [AddCommGroup E] [Module R E]
    (M N : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N)
    (hN : Function.Bijective (evalLinear R E N)) :
    Function.Bijective (evalLinear R E M) := by
  let de : (M →ₗ[R] E) ≃ₗ[R] (N →ₗ[R] E) := LinearEquiv.congrLeft E R e
  let dde : ((M →ₗ[R] E) →ₗ[R] E) ≃ₗ[R]
      ((N →ₗ[R] E) →ₗ[R] E) := LinearEquiv.congrLeft E R de
  have hc (m : M) : dde (evalLinear R E M m) = evalLinear R E N (e m) := by
    ext g
    rfl
  constructor
  · intro x y h
    apply e.injective
    apply hN.1
    rw [← hc, ← hc, h]
  · intro φ
    obtain ⟨n, hn⟩ := hN.2 (dde φ)
    obtain ⟨m, rfl⟩ := e.surjective n
    refine ⟨m, dde.injective ?_⟩
    rw [hc]
    exact hn

private theorem evalLinear_bijective_prod
    (R : Type*) [CommRing R]
    (E : Type*) [AddCommGroup E] [Module R E]
    (M N : Type*) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]
    (hM : Function.Bijective (evalLinear R E M))
    (hN : Function.Bijective (evalLinear R E N)) :
    Function.Bijective (evalLinear R E (M × N)) := by
  let de : ((M →ₗ[R] E) × (N →ₗ[R] E)) ≃ₗ[R] ((M × N) →ₗ[R] E) :=
    LinearMap.coprodEquiv R
  let dde : (((M × N) →ₗ[R] E) →ₗ[R] E) ≃ₗ[R]
      (((M →ₗ[R] E) →ₗ[R] E) × ((N →ₗ[R] E) →ₗ[R] E)) :=
    (LinearEquiv.congrLeft E R de.symm).trans (LinearMap.coprodEquiv R).symm
  have hc (x : M × N) :
      dde (evalLinear R E (M × N) x) =
        (evalLinear R E M x.1, evalLinear R E N x.2) := by
    apply Prod.ext <;> ext f <;>
      simp [dde, de, evalLinear, LinearMap.coprodEquiv]
  constructor
  · intro x y h
    have h' : (evalLinear R E M x.1, evalLinear R E N x.2) =
        (evalLinear R E M y.1, evalLinear R E N y.2) := by
      rw [← hc, ← hc, h]
    exact Prod.ext (hM.1 (congrArg Prod.fst h'))
      (hN.1 (congrArg Prod.snd h'))
  · intro φ
    obtain ⟨m, hm⟩ := hM.2 (dde φ).1
    obtain ⟨n, hn⟩ := hN.2 (dde φ).2
    refine ⟨(m, n), dde.injective ?_⟩
    rw [hc]
    exact Prod.ext hm hn

private theorem evalLinear_bijective_finPi
    (R : Type*) [CommRing R]
    (E A : Type*) [AddCommGroup E] [Module R E]
    [AddCommGroup A] [Module R A]
    (hA : Function.Bijective (evalLinear R E A)) (n : ℕ) :
    Function.Bijective (evalLinear R E (Fin n → A)) := by
  induction n with
  | zero =>
      constructor
      · intro x y _
        exact Subsingleton.elim x y
      · intro φ
        refine ⟨0, ?_⟩
        ext f
        have hf : f = 0 := by ext x; exact Fin.elim0 x
        subst f
        simp [evalLinear]
  | succ n ih =>
      let e : (Fin (n + 1) → A) ≃ₗ[R] A × (Fin n → A) :=
        (Fin.consLinearEquiv R (fun _ : Fin (n + 1) => A)).symm
      exact evalLinear_bijective_of_linearEquiv R E _ _ e
        (evalLinear_bijective_prod R E _ _ hA ih)

private theorem evalLinear_bijective_finFree
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) (n : ℕ) :
    Function.Bijective (evalLinear R E (Fin n → ULift.{v} R)) :=
  evalLinear_bijective_finPi R E _ (evalLinear_bijective_ulift R E i hi) n

private theorem exists_finFree_surjection
    (R : Type u) [CommRing R]
    (M : Type (max u v)) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ n : ℕ, ∃ f : (Fin n → ULift.{v} R) →ₗ[R] M,
      Function.Surjective f := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' R M
  let e : (Fin n → ULift.{v} R) ≃ₗ[R] (Fin n → R) :=
    LinearEquiv.piCongrRight (fun _ => (ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R))
  exact ⟨n, f.comp e.toLinearMap, hf.comp e.surjective⟩

private theorem evalLinear_bijective_of_isNoetherian
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i)
    (M : Type (max u v)) [AddCommGroup M] [Module R M] [IsNoetherian R M] :
    Function.Bijective (evalLinear R E M) := by
  have : CategoryTheory.Injective E := hi.1
  have : Module.Injective R E := Module.injective_module_of_injective_object R E
  have : Module.Finite R M :=
    (isNoetherian_iff_module_finite R M).mp inferInstance
  obtain ⟨n, f, hf⟩ := exists_finFree_surjection R M
  have : IsNoetherian R (ULift.{v} R) :=
    isNoetherian_of_linearEquiv (ULift.moduleEquiv : ULift.{v} R ≃ₗ[R] R).symm
  have : IsNoetherian R (Fin n → ULift.{v} R) := inferInstance
  have : IsNoetherian R f.ker := inferInstance
  have : Module.Finite R f.ker :=
    (isNoetherian_iff_module_finite R f.ker).mp inferInstance
  obtain ⟨m, g, hg⟩ := exists_finFree_surjection R f.ker
  have hK : Function.Surjective (evalLinear R E f.ker) :=
    evalLinear_surjective_of_surjective R E _ _ g hg
      (evalLinear_bijective_finFree R E i hi m).2
  exact evalLinear_bijective_of_surjective R E _ _ f hf
    (evalLinear_bijective_finFree R E i hi n) hK

private theorem isIso_matlisEvaluation_of_evalLinear_bijective
    (R : Type u) [CommRing R]
    (E M : ModuleCat.{max u v} R)
    (h : Function.Bijective (evalLinear R E M)) :
    IsIso ((matlisEvaluation R E).app M) := by
  let e : (M ⟶ E) ≃ₗ[R] (M →ₗ[R] E) := ModuleCat.homLinearEquiv
  let b : (ModuleCat.of R (M ⟶ E) ⟶ E) ≃ₗ[R]
      ((M →ₗ[R] E) →ₗ[R] E) :=
    (ModuleCat.homLinearEquiv).trans (LinearEquiv.congrLeft E R e)
  have hc (m : M) : b ((matlisEvaluation R E).app M m) = evalLinear R E M m := by
    ext f
    rfl
  apply (ConcreteCategory.isIso_iff_bijective ((matlisEvaluation R E).app M)).mpr
  constructor
  · intro x y hxy
    apply h.1
    rw [← hc, ← hc, hxy]
  · intro φ
    obtain ⟨m, hm⟩ := h.2 (b φ)
    refine ⟨m, b.injective ?_⟩
    rw [hc]
    exact hm

private theorem evalLinear_bijective_hull
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    Function.Bijective (evalLinear R E E) := by
  have hb := algebraMap_end_bijective R E i hi
  constructor
  · intro x y h
    have h' := congrArg (fun f : (Module.End R E) →ₗ[R] E => f (LinearMap.id)) h
    simpa [evalLinear] using h'
  · intro f
    refine ⟨f LinearMap.id, ?_⟩
    ext g
    obtain ⟨r, hr⟩ := hb.2 g
    rw [← hr, Module.algebraMap_end_eq_smul_id]
    simp [evalLinear]

private theorem dual_exact_of_exact
    (R : Type*) [CommRing R]
    (E : Type w) [AddCommGroup E] [Module R E] [Module.Injective R E]
    (M₁ M₂ M₃ : Type w)
    [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂]
    [AddCommGroup M₃] [Module R M₃]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (h : Function.Exact f g) :
    Function.Exact (LinearMap.lcomp R E g) (LinearMap.lcomp R E f) := by
  let gr : M₂ →ₗ[R] g.range := g.rangeRestrict
  have hgr : Function.Surjective gr := g.surjective_rangeRestrict
  have hex : Function.Exact f gr := fun y =>
    ⟨fun hy => (h y).mp (congrArg Subtype.val hy), fun hy => Subtype.ext ((h y).mpr hy)⟩
  have hleft : Function.Exact (LinearMap.lcomp R E gr) (LinearMap.lcomp R E f) :=
    LinearMap.exact_lcomp_of_exact_of_surjective E hex hgr
  have hcomp : (LinearMap.lcomp R E g) =
      (LinearMap.lcomp R E gr).comp (LinearMap.lcomp R E g.range.subtype) := by
    ext φ y
    rfl
  intro φ
  constructor
  · intro hφ
    obtain ⟨ψ, hψ⟩ := (hleft φ).mp hφ
    obtain ⟨ξ, hξ⟩ := Module.Injective.out g.range.subtype
      (Submodule.subtype_injective _) ψ
    refine ⟨ξ, ?_⟩
    rw [hcomp, LinearMap.comp_apply]
    ext y
    show ξ (g.range.subtype (gr y)) = φ y
    rw [hξ (gr y)]
    exact congrArg (fun t : (M₂ →ₗ[R] E) => t y) hψ
  · rintro ⟨ξ, rfl⟩
    rw [hcomp, LinearMap.comp_apply]
    exact (hleft _).mpr ⟨_, rfl⟩

private theorem evalLinear_bijective_ker
    (R : Type*) [CommRing R]
    (E : Type w) [AddCommGroup E] [Module R E] [Module.Injective R E]
    (F G : Type w) [AddCommGroup F] [Module R F]
    [AddCommGroup G] [Module R G]
    (g : F →ₗ[R] G)
    (hF : Function.Bijective (evalLinear R E F))
    (hG : Function.Bijective (evalLinear R E G)) :
    Function.Bijective (evalLinear R E g.ker) := by
  let k : g.ker →ₗ[R] F := g.ker.subtype
  let dg : (G →ₗ[R] E) →ₗ[R] (F →ₗ[R] E) := LinearMap.lcomp R E g
  let dk : (F →ₗ[R] E) →ₗ[R] (g.ker →ₗ[R] E) := LinearMap.lcomp R E k
  have hdk : Function.Surjective dk := by
    intro φ
    obtain ⟨ψ, hψ⟩ := Module.Injective.out k (Submodule.subtype_injective _) φ
    exact ⟨ψ, LinearMap.ext hψ⟩
  have hex : Function.Exact dg dk :=
    dual_exact_of_exact R E _ _ _ k g (LinearMap.exact_subtype_ker_map g)
  have hex₂ : Function.Exact (LinearMap.lcomp R E dk) (LinearMap.lcomp R E dg) :=
    LinearMap.exact_lcomp_of_exact_of_surjective E hex hdk
  have hddk : Function.Injective (LinearMap.lcomp R E dk) :=
    LinearMap.lcomp_injective_of_surjective dk hdk
  have hnatk (x : g.ker) :
      (LinearMap.lcomp R E dk) (evalLinear R E g.ker x) =
        evalLinear R E F (k x) := by
    ext φ
    rfl
  have hnatg (x : F) :
      (LinearMap.lcomp R E dg) (evalLinear R E F x) =
        evalLinear R E G (g x) := by
    ext φ
    rfl
  constructor
  · intro x y hxy
    apply Subtype.val_injective
    apply hF.1
    show evalLinear R E F (k x) = evalLinear R E F (k y)
    rw [← hnatk, ← hnatk, hxy]
  · intro α
    obtain ⟨z, hz⟩ := hF.2 ((LinearMap.lcomp R E dk) α)
    have hgz : g z = 0 := by
      apply hG.1
      rw [← hnatg, hz, map_zero]
      exact (hex₂ _).mpr ⟨α, rfl⟩
    let x : g.ker := ⟨z, hgz⟩
    refine ⟨x, hddk ?_⟩
    rw [hnatk]
    exact hz

private theorem exists_finCopresentation
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (E M : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) [IsArtinian R M] :
    ∃ (n m : ℕ) (f : M →ₗ[R] (Fin n → E))
      (g : (Fin n → E) →ₗ[R] (Fin m → E)),
      Function.Injective f ∧ Function.Exact f g := by
  let S := ULift.{v, u} R
  let e : R ≃+* S := ULift.ringEquiv.symm
  let : IsLocalRing S := RingEquiv.isLocalRing e
  let : IsNoetherianRing S := isNoetherianRing_of_ringEquiv R e
  let M' := (ModuleCat.restrictScalars (e.symm : S →+* R)).obj M
  let E' := (ModuleCat.restrictScalars (e.symm : S →+* R)).obj E
  let : Module S M' := M'.isModule
  let : Module S E' := E'.isModule
  have : IsArtinian S M' := (isArtinian_ringChange_iff R S e M).mpr inferInstance
  obtain ⟨i', hmono, hiTransport⟩ := transport_injective_hull R S e E i hi
  let j : IsLocalRing.ResidueField S →ₗ[S] E' := i'.hom
  have : Mono (ModuleCat.ofHom j) := hmono
  have hparts := (isArtinian_iff_powerTorsion_and_finiteSocle S M').mp
    (inferInstance : IsArtinian S M')
  obtain ⟨n, m, f', g', hf', hfg'⟩ :=
    (powerTorsion_and_finiteSocle_iff_exists_finite_copresentation
      S M' E' j hiTransport).mp hparts
  let f : M →ₗ[R] (Fin n → E) :=
    { toFun := f'
      map_add' := by intro x y; exact f'.map_add x y
      map_smul' := by
        intro r x
        have h := f'.map_smul (e r) x
        change f' (e.symm (e r) • x) =
          (fun j => e.symm (e r) • (f' x) j) at h
        show f' (r • x) = (fun j => r • (f' x) j)
        simpa only [e.symm_apply_apply] using h }
  let g : (Fin n → E) →ₗ[R] (Fin m → E) :=
    { toFun := g'
      map_add' := by intro x y; exact g'.map_add x y
      map_smul' := by
        intro r x
        have h := g'.map_smul (e r) x
        change g' (fun j => e.symm (e r) • x j) =
          (fun j => e.symm (e r) • (g' x) j) at h
        show g' (fun j => r • x j) = (fun j => r • (g' x) j)
        simpa only [e.symm_apply_apply] using h }
  exact ⟨n, m, f, g, hf', hfg'⟩

private theorem evalLinear_bijective_of_isArtinian
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i)
    (M : ModuleCat.{max u v} R) [IsArtinian R M] :
    Function.Bijective (evalLinear R E M) := by
  obtain ⟨n, m, f, g, hf, hfg⟩ := exists_finCopresentation R E M i hi
  have : CategoryTheory.Injective E := hi.1
  have : Module.Injective R E := Module.injective_module_of_injective_object R E
  let k : M →ₗ[R] g.ker := f.codRestrict g.ker (fun x => hfg.apply_apply_eq_zero x)
  have hk : Function.Bijective k := by
    refine ⟨fun x y h => hf (congrArg Subtype.val h), fun z => ?_⟩
    obtain ⟨x, hx⟩ := (hfg z.val).mp z.property
    exact ⟨x, Subtype.ext hx⟩
  let e : M ≃ₗ[R] g.ker := LinearEquiv.ofBijective k hk
  exact evalLinear_bijective_of_linearEquiv R E _ _ e
    (evalLinear_bijective_ker R E _ _ g
      (evalLinear_bijective_finPi R E E (evalLinear_bijective_hull R E i hi) n)
      (evalLinear_bijective_finPi R E E (evalLinear_bijective_hull R E i hi) m))

/-- The canonical map to the double Matlis dual is an isomorphism for every module satisfying
the descending chain condition. -/
@[stacks 08Z9 "biduality for modules with the descending chain condition"]
public theorem isIso_matlisEvaluation_of_isArtinian
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E M : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) [IsArtinian R M] :
    IsIso ((matlisEvaluation R E).app M) :=
  isIso_matlisEvaluation_of_evalLinear_bijective R E M
    (evalLinear_bijective_of_isArtinian R E i hi M)

/-- The canonical map to the double Matlis dual is an isomorphism for every module satisfying
the ascending chain condition. -/
@[stacks 08Z9 "biduality for modules with the ascending chain condition"]
public theorem isIso_matlisEvaluation_of_isNoetherian
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E M : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) [IsNoetherian R M] :
    IsIso ((matlisEvaluation R E).app M) :=
  isIso_matlisEvaluation_of_evalLinear_bijective R E M
    (evalLinear_bijective_of_isNoetherian R E i hi M)

public noncomputable def matlisForward
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    (ArtinianModules.{u, v} R)ᵒᵖ ⥤ NoetherianModules.{u, v} R :=
  (show ObjectProperty (ModuleCat.{max u v} R) from
    fun M => IsNoetherian R M).lift
    ((ObjectProperty.ι (fun M : ModuleCat.{max u v} R => IsArtinian R M)).op ⋙
      (linearYoneda R (ModuleCat.{max u v} R)).obj E)
    (by
      intro X
      change IsNoetherian R (X.unop.obj ⟶ E)
      let : IsArtinian R X.unop.obj := X.unop.property
      exact isNoetherian_hom_of_isArtinian R E X.unop.obj i hi)

public noncomputable def matlisBackward
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    NoetherianModules.{u, v} R ⥤ (ArtinianModules.{u, v} R)ᵒᵖ :=
  opOp (NoetherianModules.{u, v} R) ⋙
    ((show ObjectProperty (ModuleCat.{max u v} R) from
      fun M => IsArtinian R M).lift
      ((ObjectProperty.ι (fun M : ModuleCat.{max u v} R => IsNoetherian R M)).op ⋙
        (linearYoneda R (ModuleCat.{max u v} R)).obj E)
      (by
        intro X
        change IsArtinian R (X.unop.obj ⟶ E)
        let : IsNoetherian R X.unop.obj := X.unop.property
        exact isArtinian_hom_of_isNoetherian R E X.unop.obj i hi)).op

private lemma matlisBackwardForward_map
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i)
    {X Y : NoetherianModules.{u, v} R} (f : X ⟶ Y) :
    (((matlisBackward R E i hi) ⋙ (matlisForward R E i hi)).map f).hom =
      (matlisBidual R E).map f.hom := by
  ext φ
  rfl

public noncomputable def matlisCounitIso
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    matlisBackward R E i hi ⋙ matlisForward R E i hi ≅
      𝟭 (NoetherianModules.{u, v} R) :=
  NatIso.ofComponents
    (fun X => by
      letI : IsNoetherian R X.obj := X.property
      letI : IsIso ((matlisEvaluation R E).app X.obj) :=
        isIso_matlisEvaluation_of_isNoetherian R E X.obj i hi
      exact (show ObjectProperty (ModuleCat.{max u v} R) from
        fun M => IsNoetherian R M).isoMk
          (asIso ((matlisEvaluation R E).app X.obj)).symm)
    (by
      intro X Y f
      let : IsNoetherian R X.obj := X.property
      let : IsNoetherian R Y.obj := Y.property
      let : IsIso ((matlisEvaluation R E).app X.obj) :=
        isIso_matlisEvaluation_of_isNoetherian R E X.obj i hi
      let : IsIso ((matlisEvaluation R E).app Y.obj) :=
        isIso_matlisEvaluation_of_isNoetherian R E Y.obj i hi
      apply ObjectProperty.hom_ext
      change (matlisBidual R E).map f.hom ≫ inv ((matlisEvaluation R E).app Y.obj) =
        inv ((matlisEvaluation R E).app X.obj) ≫ f.hom
      apply (cancel_mono ((matlisEvaluation R E).app Y.obj)).1
      have hnat : f.hom ≫ (matlisEvaluation R E).app Y.obj =
          (matlisEvaluation R E).app X.obj ≫ (matlisBidual R E).map f.hom := by
        ext m
        rfl
      have hYi : inv ((matlisEvaluation R E).app Y.obj) ≫
          (matlisEvaluation R E).app Y.obj = 𝟙 _ := IsIso.inv_hom_id _
      have hXi : inv ((matlisEvaluation R E).app X.obj) ≫
          (matlisEvaluation R E).app X.obj = 𝟙 _ := IsIso.inv_hom_id _
      calc
        ((matlisBidual R E).map f.hom ≫ inv ((matlisEvaluation R E).app Y.obj)) ≫
            (matlisEvaluation R E).app Y.obj =
          (matlisBidual R E).map f.hom := by
            rw [Category.assoc, hYi, Category.comp_id]
        _ = inv ((matlisEvaluation R E).app X.obj) ≫
            ((matlisEvaluation R E).app X.obj ≫ (matlisBidual R E).map f.hom) := by
              rw [← Category.assoc, hXi, Category.id_comp]
        _ = inv ((matlisEvaluation R E).app X.obj) ≫
            (f.hom ≫ (matlisEvaluation R E).app Y.obj) := by rw [hnat]
        _ = (inv ((matlisEvaluation R E).app X.obj) ≫ f.hom) ≫
            (matlisEvaluation R E).app Y.obj := by simp [Category.assoc])

private lemma matlisForwardBackward_map
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i)
    {X Y : (ArtinianModules.{u, v} R)ᵒᵖ} (f : X ⟶ Y) :
    ((((matlisForward R E i hi) ⋙ (matlisBackward R E i hi)).map f).unop).hom =
      (matlisBidual R E).map f.unop.hom := by
  ext φ
  rfl

private theorem matlisEvaluation_inv_naturality
    (R : Type u) [CommRing R]
    (E M N : ModuleCat.{max u v} R)
    [IsIso ((matlisEvaluation R E).app M)]
    [IsIso ((matlisEvaluation R E).app N)]
    (f : M ⟶ N) :
    (matlisBidual R E).map f ≫ inv ((matlisEvaluation R E).app N) =
      inv ((matlisEvaluation R E).app M) ≫ f := by
  rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
  ext m
  rfl

public noncomputable def matlisUnitIso
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    𝟭 ((ArtinianModules.{u, v} R)ᵒᵖ) ≅
      matlisForward R E i hi ⋙ matlisBackward R E i hi :=
  NatIso.ofComponents
    (fun X => by
      letI : IsArtinian R X.unop.obj := X.unop.property
      letI : IsIso ((matlisEvaluation R E).app X.unop.obj) :=
        isIso_matlisEvaluation_of_isArtinian R E X.unop.obj i hi
      let e : X.unop.obj ≅ (matlisBidual R E).obj X.unop.obj :=
        asIso ((matlisEvaluation R E).app X.unop.obj)
      let e' : X.unop ≅
          ((matlisForward R E i hi ⋙ matlisBackward R E i hi).obj X).unop :=
        (show ObjectProperty (ModuleCat.{max u v} R) from
          fun M => IsArtinian R M).isoMk e
      exact e'.symm.op)
    (by
      intro X Y f
      let : IsArtinian R X.unop.obj := X.unop.property
      let : IsArtinian R Y.unop.obj := Y.unop.property
      let : IsIso ((matlisEvaluation R E).app X.unop.obj) :=
        isIso_matlisEvaluation_of_isArtinian R E X.unop.obj i hi
      let : IsIso ((matlisEvaluation R E).app Y.unop.obj) :=
        isIso_matlisEvaluation_of_isArtinian R E Y.unop.obj i hi
      apply Quiver.Hom.unop_inj
      apply ObjectProperty.hom_ext
      change inv ((matlisEvaluation R E).app Y.unop.obj) ≫ f.unop.hom =
        (matlisBidual R E).map f.unop.hom ≫
          inv ((matlisEvaluation R E).app X.unop.obj)
      exact (matlisEvaluation_inv_naturality R E Y.unop.obj X.unop.obj f.unop.hom).symm)

/-- **Matlis duality (Stacks Project, Tag 08Z9).** The canonical anti-equivalence between
Artinian and Noetherian modules over a complete local Noetherian ring. -/
@[stacks 08Z9 "anti-equivalence", sga "2 IV 5.1" "special case"]
public noncomputable def matlisDuality
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    (ArtinianModules.{u, v} R)ᵒᵖ ≌ NoetherianModules.{u, v} R :=
  CategoryTheory.Equivalence.mk (matlisForward R E i hi) (matlisBackward R E i hi)
    (matlisUnitIso R E i hi) (matlisCounitIso R E i hi)

/-- The functor underlying `matlisDuality`, after inclusion in all modules, is naturally
isomorphic to `Hom_R(-, E)`. -/
@[stacks 08Z9 "the anti-equivalence is induced by the Matlis dual functor"]
public noncomputable def matlisDualityFunctorIso
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    (E : ModuleCat.{max u v} R)
    (i : residueFieldModule.{u, v} R ⟶ E) [Mono i]
    (hi : Module.IsInjectiveHull i) :
    (matlisDuality R E i hi).functor ⋙
        ObjectProperty.ι (fun M : ModuleCat.{max u v} R ↦ IsNoetherian R M) ≅
      (ObjectProperty.ι (fun M : ModuleCat.{max u v} R ↦ IsArtinian R M)).op ⋙
        (linearYoneda R (ModuleCat.{max u v} R)).obj E :=
  Iso.refl _

end Dualizing
