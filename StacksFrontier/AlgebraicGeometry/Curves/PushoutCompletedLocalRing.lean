module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.RingTheory.Rig.AdicCompletionMap
public import StacksFrontier.AlgebraicGeometry.Curves.Pushout
public import StacksFrontier.AlgebraicGeometry.Pushout.FiniteType
public import StacksFrontier.AlgebraicGeometry.Pushout.Gluing
public import StacksFrontier.AlgebraicGeometry.Variety.CompleteLocal.Stalk
public import StacksFrontier.RingTheory.AdicCompletion.FiniteAlgebra
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Localization.Glueing.IdealPowerTorsion

/-!
# Completed local rings of a pushout of curves

Let `k` be a field and let `X = Y ⨿_Z X'` be a pushout of schemes over `k` along a closed
immersion `Z ⟶ X'` and an integral morphism `Z ⟶ Y`, in which `Y = Spec k'` for a field `k'`
and `Z = Spec (k'_1 × ⋯ × k'_n)` for finite extensions `k'_i/k'`.  Writing `x` for the image of
`Y` in `X` and `x'_i` for the image of `Spec k'_i` in `X'`, the square formed by `k'`, the
product of the `k'_i`, the completed local ring `𝒪_{X, x}^∧` and the product of the completed
local rings `𝒪_{X', x'_i}^∧`, with the horizontal maps given by the maps to the residue fields,
is cartesian.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.exists_pushoutCompletedLocalRing_isPullback`: the completed local ring of
  the pushout is the fibre product of the product of the completed local rings upstairs and the
  ground field over the product of the residue extensions, over an arbitrary base and under the
  assumption that the pushout is locally Noetherian.
* `AlgebraicGeometry.exists_pushoutCompletedLocalRing_isPullback_of_locallyOfFiniteType`: the
  same conclusion over a base that is the spectrum of a field `k`, with `X` locally of finite type
  over `k` and `Y` and `Z` finite over `k` and `Z ⟶ Y` surjective.  There the locally Noetherian
  hypothesis is discharged rather than assumed.
* `AlgebraicGeometry.exists_curvePushoutCompletedLocalRing_isPullback`: the same conclusion under
  the four conditions of [Stacks Project, Tag 0E35] alone, with the standing situation of
  [Stacks Project, Tag 0ECI] derived from them by `curvePushoutSituation` rather than assumed.

## Implementation notes

The lower-left and upper-left corners are literally the field `k'` and the product of the fields
`k'_i`; the horizontal arrows are determined after completion by the stalk maps associated to
the morphisms from the spectra of those fields.  The existential form of the statement avoids
choosing explicit lifts of these maps to the completions.

The argument is split along the division in the source: the geometric half chooses an affine
open around `x` and reads off the cartesian square of rings, the finiteness of the maps and the
primes of the upstairs ring lying over the chosen maximal ideal, while the algebraic half is
`exists_isPullback_adicCompletion`, which completes that square.  Stating the algebraic half
over opaque rings matters for more than readability: with the rings left as `Γ(X, W)` every
definitional comparison unfolds the pushout construction itself.

The argument needs the local ring at `x` to be Noetherian, so the general statement carries the
assumption that the pushout is locally Noetherian.  That assumption is not part of
[Stacks Project, Tag 0E35]: there the base is the spectrum of a field and the three schemes of
the diagram are of finite type over it, so the pushout is locally of finite type over the base by
[Stacks Project, Tag 0E27] and therefore locally Noetherian.  This is what the specialized
statement does.

## References

* [Stacks Project, Tag 0E36](https://stacks.math.columbia.edu/tag/0E36)
* [Stacks Project, Tag 0E35](https://stacks.math.columbia.edu/tag/0E35)
* [Stacks Project, Tag 0E27](https://stacks.math.columbia.edu/tag/0E27)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

private noncomputable def primeSpectrumPiFieldEquivFin
    {n : ℕ} (K : Fin n → Type u) [∀ i, Field (K i)] :
    PrimeSpectrum (∀ i, K i) ≃ Fin n := by
  classical
  let e₁ : PrimeSpectrum (∀ i, K i) ≃ (Σ i, PrimeSpectrum (K i)) :=
    (PrimeSpectrum.sigmaToPiHomeo K).symm.toEquiv
  let e₂ : (Σ i, PrimeSpectrum (K i)) ≃ Fin n :=
    { toFun := Sigma.fst
      invFun := fun i ↦ ⟨i, closedPoint (K i)⟩
      left_inv := by
        rintro ⟨i, p⟩
        have hp : p = closedPoint (K i) := by
          apply PrimeSpectrum.ext
          have hpb : p.asIdeal = ⊥ :=
            (p.asIdeal.eq_bot_or_top).resolve_right p.2.ne_top
          change p.asIdeal = IsLocalRing.maximalIdeal (K i)
          rw [hpb, IsLocalRing.maximalIdeal_eq_bot]
        subst p
        rfl
      right_inv := fun _ ↦ rfl }
  exact e₁.trans e₂

private lemma adicCompletionMap_toField_comp
    {A K : Type u} [CommRing A] [IsLocalRing A] [Field K]
    (f : A →+* K) [IsLocalHom f] :
    (((AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal K)).symm.toRingEquiv.toRingHom).comp
      (adicCompletionMap f (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal K)
        (IsLocalRing.map_maximalIdeal_le f))).comp
      (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) = f := by
  apply RingHom.ext
  intro a
  change (((AdicCompletion.ofAlgEquiv (IsLocalRing.maximalIdeal K)).symm.toRingEquiv.toRingHom).comp
      ((adicCompletionMap f (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal K)
        (IsLocalRing.map_maximalIdeal_le f)).comp
        (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)))) a = f a
  rw [adicCompletionMap_comp_algebraMap]
  simp

private lemma adicCompletionMap_isLocalHom
    {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing A] [IsNoetherianRing B]
    (f : A →+* B) [IsLocalHom f] :
    IsLocalHom (adicCompletionMap f (IsLocalRing.maximalIdeal A)
      (IsLocalRing.maximalIdeal B) (IsLocalRing.map_maximalIdeal_le f)) := by
  apply ((IsLocalRing.local_hom_TFAE _).out 1 3).mpr
  rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map,
    adicCompletionMap_comp_algebraMap, ← Ideal.map_map,
    AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.map_mono (IsLocalRing.map_maximalIdeal_le f)

private lemma stalk_eqToHom_eq_stalkCongr (X : Scheme) (x y : X) (h : x = y) :
    (eqToHom (congrArg (fun p ↦ CommRingCat.of (X.presheaf.stalk p)) h)).hom =
      (X.presheaf.stalkCongr (Inseparable.of_eq h)).hom.hom := by
  cases h
  simp [TopCat.Presheaf.stalkCongr_hom]

private lemma adicCompletionRingHom_ext
    {A B : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (f g : AdicCompletion (IsLocalRing.maximalIdeal A) A →+* B)
    (hf : Ideal.map f (IsLocalRing.maximalIdeal
      (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ≤ IsLocalRing.maximalIdeal B)
    (hg : Ideal.map g (IsLocalRing.maximalIdeal
      (AdicCompletion (IsLocalRing.maximalIdeal A) A)) ≤ IsLocalRing.maximalIdeal B)
    (hfg : f.comp (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A)) =
      g.comp (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))) :
    f = g := by
  apply RingHom.ext
  intro x
  apply AdicCompletion.induction_on (IsLocalRing.maximalIdeal A) A x
  intro c
  let J : Ideal B := IsLocalRing.maximalIdeal B
  have hJ : J ≠ ⊤ := (inferInstance : J.IsMaximal).ne_top
  rw [← sub_eq_zero]
  apply Ideal.mem_bot.mp
  rw [← Ideal.iInf_pow_eq_bot_of_isLocalRing J hJ]
  simp only [Ideal.mem_iInf]
  intro n
  let T := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let : IsNoetherianRing T := AdicCompletion.isNoetherianRing _
  let : IsLocalRing T := inferInstance
  have happrox : (AdicCompletion.mk (IsLocalRing.maximalIdeal A) A c) -
      algebraMap A T (c n) ∈ (IsLocalRing.maximalIdeal T) ^ n := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    rw [← Ideal.map_pow]
    change (AdicCompletion.mk (IsLocalRing.maximalIdeal A) A c) -
      algebraMap A T (c n) ∈ Submodule.restrictScalars A
        (Ideal.map (algebraMap A T) ((IsLocalRing.maximalIdeal A) ^ n))
    rw [← Ideal.smul_top_eq_map]
    rw [AdicCompletion.pow_smul_top_eq_ker_eval
      (Ideal.fg_of_isNoetherianRing (IsLocalRing.maximalIdeal A)), LinearMap.mem_ker]
    simp [T, AdicCompletion.eval, AdicCompletion.algebraMap_apply]
  have hJf : Ideal.map f ((IsLocalRing.maximalIdeal T) ^ n) ≤ J ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hf n
  have hJg : Ideal.map g ((IsLocalRing.maximalIdeal T) ^ n) ≤ J ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hg n
  have hfx : f (AdicCompletion.mk (IsLocalRing.maximalIdeal A) A c) -
      f (algebraMap A T (c n)) ∈ J ^ n := by
    rw [← map_sub]
    exact hJf (Ideal.mem_map_of_mem f happrox)
  have hgx : g (algebraMap A T (c n)) -
      g (AdicCompletion.mk (IsLocalRing.maximalIdeal A) A c) ∈ J ^ n := by
    simpa only [map_sub, neg_sub] using
      (J ^ n).neg_mem (hJg (Ideal.mem_map_of_mem g happrox))
  have hmid : f (algebraMap A T (c n)) = g (algebraMap A T (c n)) :=
    DFunLike.congr_fun hfg (c n)
  convert (J ^ n).add_mem hfx hgx using 1
  rw [hmid]
  abel

private lemma completedLocalRing_congr_germ (X : Scheme.{u}) (V : X.Opens)
    (x y : X) (h : x = y) (hx : x ∈ V) (hy : y ∈ V) (a : Γ(X, V)) :
    (eqToHom (congrArg (fun p ↦ CommRingCat.of (Scheme.completedLocalRing X p)) h)).hom
      (algebraMap (X.presheaf.stalk x) (Scheme.completedLocalRing X x)
        ((X.presheaf.germ V x hx).hom a)) =
      algebraMap (X.presheaf.stalk y) (Scheme.completedLocalRing X y)
        ((X.presheaf.germ V y hy).hom a) := by
  cases h
  rfl

private lemma completion_ringHom_ext_of_localization
    {R L D : Type u} [CommRing R] [CommRing L] [CommRing D]
    [IsLocalRing L] [IsNoetherianRing L] [IsLocalRing D] [IsNoetherianRing D]
    [Algebra R L] (p : Ideal R) [p.IsPrime] [IsLocalization.AtPrime L p]
    (f g : AdicCompletion (maximalIdeal L) L →+* D)
    [IsLocalHom (g.comp (algebraMap L (AdicCompletion (maximalIdeal L) L)))]
    (h : f.comp (algebraMap R _) = g.comp (algebraMap R _)) : f = g := by
  have hL : f.comp (algebraMap L _) = g.comp (algebraMap L _) :=
    IsLocalization.ringHom_ext p.primeCompl h
  apply adicCompletionRingHom_ext f g
  · rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hL]
    exact IsLocalRing.map_maximalIdeal_le _
  · rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map]
    exact IsLocalRing.map_maximalIdeal_le _
  · exact hL

private lemma app_eq_top_transport {X Y : Scheme.{u}} (f : X ⟶ Y)
    (V : Y.Opens) (hV : V = ⊤) (hW : f ⁻¹ᵁ V = ⊤) :
    f.app V ≫ eqToHom (congrArg (fun U ↦ Γ(X, U)) hW) =
      eqToHom (congrArg (fun U ↦ Γ(Y, U)) hV) ≫ f.appTop := by
  subst V
  change f.appTop ≫ 𝟙 _ = 𝟙 _ ≫ f.appTop
  simp

private lemma germ_to_field_of_iso {Y : Scheme.{u}} {K : Type u} [Field K]
    (e : Y ≅ Spec (.of K)) (V : Y.Opens) (hV : V = ⊤)
    (hy : e.inv (closedPoint K) ∈ V) :
    Y.presheaf.germ V _ hy ≫ Scheme.stalkClosedPointTo e.inv =
      eqToHom (congrArg (fun U ↦ Γ(Y, U)) hV) ≫
        e.inv.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom := by
  subst V
  rw [Scheme.germ_stalkClosedPointTo]
  change e.inv.appTop ≫ (Spec (.of K)).presheaf.map (𝟙 _) ≫
    (Scheme.ΓSpecIso (.of K)).hom = e.inv.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom
  simp

private lemma germ_to_field_of_pi_iso {Z : Scheme.{u}} {n : ℕ}
    {K : Fin n → Type u} [∀ i, Field (K i)]
    (e : Z ≅ Spec (.of (∀ i, K i))) (V : Z.Opens) (hV : V = ⊤) (i : Fin n)
    (hy : (Spec.map (CommRingCat.ofHom (Pi.evalRingHom K i)) ≫ e.inv)
      (closedPoint (K i)) ∈ V) :
    Z.presheaf.germ V _ hy ≫
        Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom (Pi.evalRingHom K i)) ≫ e.inv) =
      eqToHom (congrArg (fun U ↦ Γ(Z, U)) hV) ≫ e.inv.appTop ≫
        (Scheme.ΓSpecIso (.of (∀ i, K i))).hom ≫ CommRingCat.ofHom (Pi.evalRingHom K i) := by
  subst V
  rw [Scheme.germ_stalkClosedPointTo
    (f := Spec.map (CommRingCat.ofHom (Pi.evalRingHom K i)) ≫ e.inv) ⊤ hy]
  simp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [Subsingleton.elim (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem
    (Spec.map (CommRingCat.ofHom (Pi.evalRingHom K i)) ≫ e.inv) hy).symm).op.hom (𝟙 _)]
  simp only [Scheme.Hom.comp_base, Opens.map_comp_obj, Opens.map_top, Scheme.Hom.comp_app,
    CategoryTheory.Functor.map_id, Category.id_comp, eqToHom_refl, Scheme.Hom.appTop,
    ← Scheme.ΓSpecIso_naturality]
  exact Category.assoc _ _ _

private lemma tensor_completion_bijective_of_annihilated
    {R : Type u} [CommRing R] (p : Ideal R) [p.IsMaximal]
    (L : Type u) [CommRing L] [Algebra R L] [IsLocalization.AtPrime L p]
    [IsLocalRing L] [IsNoetherianRing L]
    (M : Type u) [AddCommGroup M] [Module R M]
    (hM : ∀ r ∈ p, ∀ m : M, r • m = 0) :
    Function.Bijective ((TensorProduct.mk R M
      (AdicCompletion (maximalIdeal L) L)).flip 1) := by
  let T := AdicCompletion (maximalIdeal L) L
  have : Module.Flat R L := IsLocalization.flat L p.primeCompl
  have : Module.Flat L T := AdicCompletion.flat_of_isNoetherian (maximalIdeal L)
  have : Module.Flat R T := Module.Flat.trans R L T
  have hm : p.map (algebraMap R T) = maximalIdeal T := by
    rw [IsScalarTower.algebraMap_eq R L T, ← Ideal.map_map,
      IsLocalization.AtPrime.map_eq_maximalIdeal p L,
      ← AdicCompletion.maximalIdeal_eq_map]
  have hq : Function.Bijective
      (Ideal.quotientMap (p.map (algebraMap R T)) (algebraMap R T)
        Ideal.le_comap_map) := by
    have h := (AdicCompletion.residueField_map_bijective L).comp
      (IsLocalization.AtPrime.equivQuotMaximalIdeal p L).bijective
    let e := Ideal.quotEquivOfEq hm
    have heq : e.toRingHom.comp
        (Ideal.quotientMap (p.map (algebraMap R T)) (algebraMap R T) Ideal.le_comap_map) =
        (IsLocalRing.ResidueField.map (algebraMap L T)).comp
          (IsLocalization.AtPrime.equivQuotMaximalIdeal p L).toRingHom := by
      ext r
      simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
      rfl
    have hb : Function.Bijective (e.toRingHom.comp
        (Ideal.quotientMap (p.map (algebraMap R T)) (algebraMap R T) Ideal.le_comap_map)) := by
      rw [heq]
      exact h
    refine ⟨fun x y hxy ↦ hb.1 (congrArg e hxy), fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := hb.2 (e y)
    exact ⟨x, e.injective hx⟩
  apply (IPowerTorsion.baseChange_bijective_iff_quotientMap_bijective
    R T p inferInstance).mpr hq M
  intro m
  exact ⟨1, by omega, fun a ha ↦ hM a (by simpa using ha) m⟩

/-- A prime ideal of a ring isomorphic to a field is zero. -/
private lemma eq_bot_of_ringEquiv_field {B K : Type u} [CommRing B] [Field K] (η : B ≃+* K)
    (I : Ideal B) [I.IsPrime] : I = ⊥ :=
  (Ideal.map_eq_bot_iff_of_injective η.injective).mp
    (Ideal.eq_bot_of_prime (I.map η) (h := Ideal.map_isPrime_of_equiv η))

/-- Moving a scalar of `R` across a tensor product with an `R`-algebra. -/
private lemma tmul_algebraMap_eq_smul_tmul_one {R T A : Type u} [CommRing R] [CommRing T]
    [CommRing A] [Algebra R T] [Algebra R A] (r : R) (t : T) :
    t ⊗ₜ[R] algebraMap R A r = (r • t) ⊗ₜ[R] (1 : A) := by
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

/-- A cartesian square of `R`-modules `B ×_C A` stays cartesian as a square of rings after
tensoring with a flat `R`-algebra `T`, once the three outer corners are identified with `k'`, the
product of the `k'_i` and the product of the `V i` by the given isomorphisms. -/
private lemma isPullback_commRingCat_of_tensor
    {R A B C T : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R T]
    [Algebra A C] [Algebra B C] [IsScalarTower R A C] [IsScalarTower R B C]
    [Module.Flat R T]
    {n : ℕ} {k' : Type u} [Field k'] {k'_i : Fin n → Type u} [∀ i, Field (k'_i i)]
    [∀ i, Algebra k' (k'_i i)]
    {V : Fin n → Type u} [∀ i, CommRing (V i)]
    (eA : TensorProduct R T A ≃+* (∀ i, V i))
    (eBT : B ≃+* TensorProduct R T B) (eCT : C ≃+* TensorProduct R T C)
    (eB : CommRingCat.of B ≅ CommRingCat.of k') (eC' : C ≃+* (∀ i, k'_i i))
    (completionMap : T →+* (∀ i, V i)) (bottomResidueMap : T →+* k')
    (componentResidueMap : ∀ i, V i →+* k'_i i)
    (hPBmod : IsPullback (ModuleCat.ofHom (Algebra.linearMap R B))
      (ModuleCat.ofHom (Algebra.linearMap R A))
      (ModuleCat.ofHom ((Algebra.linearMap B C).restrictScalars R))
      (ModuleCat.ofHom ((Algebra.linearMap A C).restrictScalars R)))
    (hAright : ∀ (t : T) (i : Fin n), eA (t ⊗ₜ[R] (1 : A)) i = completionMap t i)
    (hbottomTmul : ∀ t : T,
      eB.commRingCatIsoToRingEquiv (eBT.symm (t ⊗ₜ[R] (1 : B))) = bottomResidueMap t)
    (hγT : ∀ b : TensorProduct R T B,
      eC' (eCT.symm (TensorProduct.map (LinearMap.id : T →ₗ[R] T)
        ((Algebra.linearMap B C).restrictScalars R) b)) =
      (RingHom.pi fun i ↦ algebraMap k' (k'_i i)) (eB.commRingCatIsoToRingEquiv (eBT.symm b)))
    (hresTensor : ∀ (t : T) (a : A) (i : Fin n),
      componentResidueMap i (eA (t ⊗ₜ[R] a) i) =
        eC' (eCT.symm (t ⊗ₜ[R] algebraMap A C a)) i) :
    IsPullback (CommRingCat.ofHom bottomResidueMap) (CommRingCat.ofHom completionMap)
      (CommRingCat.ofHom (RingHom.pi fun i ↦ algebraMap k' (k'_i i)))
      (CommRingCat.ofHom (RingHom.pi fun i ↦
        (componentResidueMap i).comp (Pi.evalRingHom V i))) := by
  apply IsPullback.of_map_of_faithful (forget CommRingCat)
  let F := CategoryTheory.MonoidalCategory.tensorLeft (ModuleCat.of R T)
  have hPBtensor := hPBmod.map F
  let h := hPBtensor.map (forget (ModuleCat R))
  refine h.of_iso
    (TensorProduct.rid R T).toEquiv.toIso
    (eBT.symm.trans eB.commRingCatIsoToRingEquiv).toEquiv.toIso
    eA.toEquiv.toIso
    (eCT.symm.trans eC').toEquiv.toIso ?_ ?_ ?_ ?_
  · apply ConcreteCategory.hom_ext
    intro v
    change eB.commRingCatIsoToRingEquiv (eBT.symm
      (TensorProduct.map (LinearMap.id : T →ₗ[R] T) (Algebra.linearMap R B) v)) =
        bottomResidueMap (TensorProduct.rid R T v)
    induction v using TensorProduct.inductionOn with
    | tmul t r =>
      rw [TensorProduct.map_tmul, TensorProduct.rid_tmul]
      change eB.commRingCatIsoToRingEquiv (eBT.symm (t ⊗ₜ[R] (algebraMap R B r))) = _
      rw [tmul_algebraMap_eq_smul_tmul_one, hbottomTmul]
    | add v w hv hw => simpa only [map_add] using congrArg₂ (· + ·) hv hw
  · apply ConcreteCategory.hom_ext
    intro v
    apply funext
    intro i
    change eA (TensorProduct.map (LinearMap.id : T →ₗ[R] T)
      (Algebra.linearMap R A) v) i = completionMap (TensorProduct.rid R T v) i
    induction v using TensorProduct.inductionOn with
    | tmul t r =>
      rw [TensorProduct.map_tmul, TensorProduct.rid_tmul]
      change eA (t ⊗ₜ[R] (algebraMap R A r)) i = _
      rw [tmul_algebraMap_eq_smul_tmul_one, hAright]
    | add v w hv hw => simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hv hw
  · apply ConcreteCategory.hom_ext
    intro v
    exact hγT v
  · apply ConcreteCategory.hom_ext
    intro v
    apply funext
    intro i
    change eC' (eCT.symm (TensorProduct.map (LinearMap.id : T →ₗ[R] T)
      ((Algebra.linearMap A C).restrictScalars R) v)) i =
        componentResidueMap i (eA v i)
    induction v using TensorProduct.inductionOn with
    | tmul t a => exact (hresTensor t a i).symm
    | add v w hv hw => simpa only [map_add, Pi.add_apply] using congrArg₂ (· + ·) hv hw

/-- The two residue maps out of `T ⊗[R] B` agree, and the component residue maps on
`T ⊗[R] A` are computed by the map to `T ⊗[R] C`.  These are the compatibilities that make
the completed square commute on elements. -/
private lemma residueMap_tmul_compat
    {R A B C T : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C] [CommRing T]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R T]
    [Algebra A C] [Algebra B C] [IsScalarTower R A C] [IsScalarTower R B C]
    {n : ℕ} {k' : Type u} [Field k'] {k'_i : Fin n → Type u} [∀ i, Field (k'_i i)]
    [∀ i, Algebra k' (k'_i i)]
    {V : Fin n → Type u} [∀ i, CommRing (V i)]
    (eA : TensorProduct R T A ≃+* (∀ i, V i))
    (eBT : B ≃+* TensorProduct R T B) (eCT : C ≃+* TensorProduct R T C)
    (eB : CommRingCat.of B ≅ CommRingCat.of k') (eC' : C ≃+* (∀ i, k'_i i))
    (completionMap : T →+* (∀ i, V i)) (bottomResidueMap : T →+* k')
    (componentResidueMap : ∀ i, V i →+* k'_i i)
    (hγgeom : ∀ b : B, eC' (algebraMap B C b) =
      (RingHom.pi fun i ↦ algebraMap k' (k'_i i)) (eB.commRingCatIsoToRingEquiv b))
    (heBT : ∀ b : B, eBT b = (1 : T) ⊗ₜ[R] b)
    (heCT : ∀ c : C, eCT c = (1 : T) ⊗ₜ[R] c)
    (hbottomTmul : ∀ t : T,
      eB.commRingCatIsoToRingEquiv (eBT.symm (t ⊗ₜ[R] (1 : B))) = bottomResidueMap t)
    (hAright : ∀ (t : T) (i : Fin n), eA (t ⊗ₜ[R] (1 : A)) i = completionMap t i)
    (hresA : ∀ (a : A) (i : Fin n),
      componentResidueMap i (eA ((1 : T) ⊗ₜ[R] a) i) = eC' (algebraMap A C a) i)
    (hresT : ∀ (t : T) (i : Fin n),
      componentResidueMap i (completionMap t i) = algebraMap k' (k'_i i) (bottomResidueMap t)) :
    (∀ b : TensorProduct R T B,
        eC' (eCT.symm (TensorProduct.map (LinearMap.id : T →ₗ[R] T)
          ((Algebra.linearMap B C).restrictScalars R) b)) =
        (RingHom.pi fun i ↦ algebraMap k' (k'_i i))
          (eB.commRingCatIsoToRingEquiv (eBT.symm b))) ∧
      (∀ (t : T) (a : A) (i : Fin n),
        componentResidueMap i (eA (t ⊗ₜ[R] a) i) =
          eC' (eCT.symm (t ⊗ₜ[R] algebraMap A C a)) i) := by
  have hγT (b : TensorProduct R T B) :
      eC' (eCT.symm (TensorProduct.map (LinearMap.id : T →ₗ[R] T)
        ((Algebra.linearMap B C).restrictScalars R) b)) =
      (RingHom.pi fun i ↦ algebraMap k' (k'_i i))
        (eB.commRingCatIsoToRingEquiv (eBT.symm b)) := by
    obtain ⟨b₀, hb₀⟩ := eBT.surjective b
    rw [← hb₀, eBT.symm_apply_apply, heBT, TensorProduct.map_tmul]
    change eC' (eCT.symm ((1 : T) ⊗ₜ[R] algebraMap B C b₀)) = _
    rw [← heCT (algebraMap B C b₀), eCT.symm_apply_apply]
    exact hγgeom b₀
  refine ⟨hγT, ?_⟩
  have hCTleft (t : T) : eC' (eCT.symm (t ⊗ₜ[R] (1 : C))) =
      (RingHom.pi fun i ↦ algebraMap k' (k'_i i)) (bottomResidueMap t) := by
    rw [← hbottomTmul t]
    simpa only [TensorProduct.map_tmul, LinearMap.id_apply, LinearMap.restrictScalars_apply,
      Algebra.linearMap_apply, map_one] using hγT (t ⊗ₜ[R] (1 : B))
  have hCTmul (t : T) (c : C) : eC' (eCT.symm (t ⊗ₜ[R] c)) =
      (RingHom.pi fun i ↦ algebraMap k' (k'_i i)) (bottomResidueMap t) * eC' c := by
    have hmul : t ⊗ₜ[R] c = (t ⊗ₜ[R] (1 : C)) * ((1 : T) ⊗ₜ[R] c) := by
      simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [hmul, map_mul, map_mul, hCTleft, ← heCT c, eCT.symm_apply_apply]
  intro t a i
  have hmul : t ⊗ₜ[R] a = (t ⊗ₜ[R] (1 : A)) * ((1 : T) ⊗ₜ[R] a) := by
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [hmul, eA.map_mul]
  change componentResidueMap i (eA (t ⊗ₜ[R] (1 : A)) i * eA ((1 : T) ⊗ₜ[R] a) i) = _
  rw [map_mul, hAright, hresT, hresA, hCTmul]
  rfl

/-- **The completion step of [Stacks 0E36].**  Let `B ×_C A` be a cartesian square of rings over
`R`, let `L` be the localization of `R` at a maximal ideal `p` that kills `B`, and let the `Lᵢ` be
local rings receiving `A` and `L` compatibly.  If the completion of `A ⊗_R L` splits as the
product of the completions of the `Lᵢ`, then the completions fit into a cartesian square whose
horizontal maps are the given maps `φ` and `φᵢ` to the residue fields.

This is the half of the source argument that is pure commutative algebra: the square survives
`p`-adic completion because everything is finite over `R`, and the completion of `A` is identified
by [Stacks 07N9], which enters here as `eCompletion`. -/
private lemma exists_isPullback_adicCompletion
    {R A B C L : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [CommRing L] [IsLocalRing L] [IsNoetherianRing L]
    [Algebra R A] [Algebra R B] [Algebra R C] [Algebra A C] [Algebra B C]
    [IsScalarTower R A C] [IsScalarTower R B C] [Algebra R L]
    {n : ℕ} {k' : Type u} [Field k'] {k'_i : Fin n → Type u} [∀ i, Field (k'_i i)]
    [∀ i, Algebra k' (k'_i i)]
    {Lᵢ : Fin n → Type u} [∀ i, CommRing (Lᵢ i)] [∀ i, IsLocalRing (Lᵢ i)]
    [∀ i, IsNoetherianRing (Lᵢ i)] [∀ i, Algebra A (Lᵢ i)]
    (p : Ideal R) [p.IsMaximal] [IsLocalization.AtPrime L p]
    (σ : ∀ i, L →+* Lᵢ i) [∀ i, IsLocalHom (σ i)]
    (φ : L →+* k') [hφloc : IsLocalHom φ] (φᵢ : ∀ i, Lᵢ i →+* k'_i i)
    [hφᵢloc : ∀ i, IsLocalHom (φᵢ i)]
    (eB : CommRingCat.of B ≅ CommRingCat.of k') (eC' : C ≃+* (∀ i, k'_i i))
    (eCompletion :
      TensorProduct R A (AdicCompletion (IsLocalRing.maximalIdeal L) L) ≃+*
        (∀ i, AdicCompletion (IsLocalRing.maximalIdeal (Lᵢ i)) (Lᵢ i)))
    (heCompletion : ∀ (a : A) (i : Fin n),
      eCompletion (algebraMap A
          (TensorProduct R A (AdicCompletion (IsLocalRing.maximalIdeal L) L)) a) i =
        algebraMap (Lᵢ i) (AdicCompletion (IsLocalRing.maximalIdeal (Lᵢ i)) (Lᵢ i))
          (algebraMap A (Lᵢ i) a))
    (hPBmod : IsPullback (ModuleCat.ofHom (Algebra.linearMap R B))
      (ModuleCat.ofHom (Algebra.linearMap R A))
      (ModuleCat.ofHom ((Algebra.linearMap B C).restrictScalars R))
      (ModuleCat.ofHom ((Algebra.linearMap A C).restrictScalars R)))
    (hpB : ∀ r ∈ p, algebraMap R B r = 0)
    (hσ : ∀ (i : Fin n) (r : R),
      σ i (algebraMap R L r) = algebraMap A (Lᵢ i) (algebraMap R A r))
    (hφ : ∀ r : R, φ (algebraMap R L r) = eB.commRingCatIsoToRingEquiv (algebraMap R B r))
    (hφᵢ : ∀ (i : Fin n) (a : A), φᵢ i (algebraMap A (Lᵢ i) a) = eC' (algebraMap A C a) i)
    (hγ : ∀ b : B, eC' (algebraMap B C b) =
      (RingHom.pi fun i ↦ algebraMap k' (k'_i i)) (eB.commRingCatIsoToRingEquiv b)) :
    ∃ (completionMap : AdicCompletion (IsLocalRing.maximalIdeal L) L →+*
          (∀ i, AdicCompletion (IsLocalRing.maximalIdeal (Lᵢ i)) (Lᵢ i)))
      (bottomResidueMap : AdicCompletion (IsLocalRing.maximalIdeal L) L →+* k')
      (componentResidueMap :
        ∀ i, AdicCompletion (IsLocalRing.maximalIdeal (Lᵢ i)) (Lᵢ i) →+* k'_i i),
      (∀ i, ((Pi.evalRingHom _ i).comp completionMap).comp
          (algebraMap L (AdicCompletion (IsLocalRing.maximalIdeal L) L)) =
        (algebraMap (Lᵢ i) (AdicCompletion (IsLocalRing.maximalIdeal (Lᵢ i)) (Lᵢ i))).comp
          (σ i)) ∧
      (bottomResidueMap.comp
        (algebraMap L (AdicCompletion (IsLocalRing.maximalIdeal L) L)) = φ) ∧
      (∀ i, (componentResidueMap i).comp
        (algebraMap (Lᵢ i) (AdicCompletion (IsLocalRing.maximalIdeal (Lᵢ i)) (Lᵢ i))) = φᵢ i) ∧
      IsPullback (CommRingCat.ofHom bottomResidueMap) (CommRingCat.ofHom completionMap)
        (CommRingCat.ofHom (RingHom.pi fun i ↦ algebraMap k' (k'_i i)))
        (CommRingCat.ofHom (RingHom.pi fun i ↦ (componentResidueMap i).comp
          (Pi.evalRingHom (fun i ↦
            AdicCompletion (IsLocalRing.maximalIdeal (Lᵢ i)) (Lᵢ i)) i))) := by
  let T := AdicCompletion (IsLocalRing.maximalIdeal L) L
  let Tᵢ : ∀ i, Type u := fun i ↦ AdicCompletion (IsLocalRing.maximalIdeal (Lᵢ i)) (Lᵢ i)
  have : IsScalarTower R L T := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Flat R L := IsLocalization.flat _ p.primeCompl
  have : Module.Flat L T := AdicCompletion.flat_of_isNoetherian (IsLocalRing.maximalIdeal L)
  have : Module.Flat R T := Module.Flat.trans R L T
  have hBunit := tensor_completion_bijective_of_annihilated p L B (by
    intro r hr b
    rw [Algebra.smul_def, hpB r hr, zero_mul])
  have hCunit := tensor_completion_bijective_of_annihilated p L C (by
    intro r hr c
    rw [Algebra.smul_def, IsScalarTower.algebraMap_apply R B C, hpB r hr, map_zero, zero_mul])
  let eBT : B ≃+* TensorProduct R T B :=
    (RingEquiv.ofBijective (Algebra.TensorProduct.includeLeftRingHom
      (R := R) (A := B) (B := T)) hBunit).trans
      (Algebra.TensorProduct.comm R B T).toRingEquiv
  let eCT : C ≃+* TensorProduct R T C :=
    (RingEquiv.ofBijective (Algebra.TensorProduct.includeLeftRingHom
      (R := R) (A := C) (B := T)) hCunit).trans
      (Algebra.TensorProduct.comm R C T).toRingEquiv
  let eA : TensorProduct R T A ≃+* (∀ i, Tᵢ i) :=
    (Algebra.TensorProduct.comm R T A).toRingEquiv.trans eCompletion
  let completionMap : T →+* (∀ i, Tᵢ i) :=
    RingHom.pi fun i ↦ adicCompletionMap (σ i) (IsLocalRing.maximalIdeal L)
      (IsLocalRing.maximalIdeal (Lᵢ i)) (IsLocalRing.map_maximalIdeal_le _)
  let bottomResidueMap : T →+* k' :=
    eB.commRingCatIsoToRingEquiv.toRingHom.comp
      (eBT.symm.toRingHom.comp
        (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := T) (B := B)))
  let componentResidueMap : ∀ i, Tᵢ i →+* k'_i i := fun i ↦
    ((AdicCompletion.ofAlgEquiv
        (IsLocalRing.maximalIdeal (k'_i i))).symm.toRingEquiv.toRingHom).comp
      (adicCompletionMap (φᵢ i) (IsLocalRing.maximalIdeal (Lᵢ i))
        (IsLocalRing.maximalIdeal (k'_i i)) (IsLocalRing.map_maximalIdeal_le _))
  have hcompletionBase (i : Fin n) :
      ((Pi.evalRingHom _ i).comp completionMap).comp (algebraMap L T) =
        (algebraMap (Lᵢ i) (Tᵢ i)).comp (σ i) :=
    adicCompletionMap_comp_algebraMap (σ i) (IsLocalRing.maximalIdeal L)
      (IsLocalRing.maximalIdeal (Lᵢ i)) (IsLocalRing.map_maximalIdeal_le _)
  have hcomponent (i : Fin n) :
      (componentResidueMap i).comp (algebraMap (Lᵢ i) (Tᵢ i)) = φᵢ i :=
    adicCompletionMap_toField_comp (φᵢ i)
  have hAleft (a : A) (i : Fin n) :
      eA ((1 : T) ⊗ₜ[R] a) i = algebraMap (Lᵢ i) (Tᵢ i) (algebraMap A (Lᵢ i) a) := by
    change eCompletion (a ⊗ₜ[R] (1 : T)) i = _
    rw [show (a ⊗ₜ[R] (1 : T)) = algebraMap A (TensorProduct R A T) a from rfl, heCompletion]
  let eFactor : ∀ i, T →+* Tᵢ i := fun i ↦
    (Pi.evalRingHom _ i).comp (eA.toRingHom.comp
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := T) (B := A)))
  have hFactorRestrict (i : Fin n) :
      (eFactor i).comp (algebraMap L T) =
        ((Pi.evalRingHom _ i).comp completionMap).comp (algebraMap L T) := by
    apply IsLocalization.ringHom_ext p.primeCompl
    apply RingHom.ext
    intro r
    rw [RingHom.comp_assoc, RingHom.comp_assoc]
    simp only [RingHom.comp_apply]
    have hLT : algebraMap L T (algebraMap R L r) = algebraMap R T r := rfl
    rw [hLT]
    change eA ((algebraMap R T r) ⊗ₜ[R] (1 : A)) i = _
    rw [Algebra.TensorProduct.tmul_one_eq_one_tmul, hAleft, ← hσ i r]
    exact (DFunLike.congr_fun (hcompletionBase i) (algebraMap R L r)).symm
  have heFactor (i : Fin n) : eFactor i = (Pi.evalRingHom _ i).comp completionMap := by
    have hlocal : IsLocalHom ((Pi.evalRingHom _ i).comp completionMap) := by
      dsimp [completionMap]
      exact adicCompletionMap_isLocalHom _
    apply adicCompletionRingHom_ext
    · rw [AdicCompletion.maximalIdeal_eq_map, Ideal.map_map, hFactorRestrict i]
      calc
        (IsLocalRing.maximalIdeal L).map
            (((Pi.evalRingHom _ i).comp completionMap).comp (algebraMap L T))
            = ((IsLocalRing.maximalIdeal L).map (algebraMap L T)).map
                ((Pi.evalRingHom _ i).comp completionMap) := by rw [Ideal.map_map]
        _ ≤ (IsLocalRing.maximalIdeal T).map ((Pi.evalRingHom _ i).comp completionMap) :=
            Ideal.map_mono (AdicCompletion.maximalIdeal_eq_map (R := L)).ge
        _ ≤ IsLocalRing.maximalIdeal (Tᵢ i) := IsLocalRing.map_maximalIdeal_le _
    · exact IsLocalRing.map_maximalIdeal_le _
    · exact hFactorRestrict i
  have hAright (t : T) (i : Fin n) : eA (t ⊗ₜ[R] (1 : A)) i = completionMap t i :=
    DFunLike.congr_fun (heFactor i) t
  have hbottomBase : bottomResidueMap.comp (algebraMap R T) =
      eB.commRingCatIsoToRingEquiv.toRingHom.comp (algebraMap R B) := by
    ext r
    change eB.commRingCatIsoToRingEquiv (eBT.symm
      (Algebra.TensorProduct.includeLeftRingHom (algebraMap R T r))) =
        eB.commRingCatIsoToRingEquiv (algebraMap R B r)
    congr 1
    apply eBT.injective
    rw [eBT.apply_symm_apply]
    change Algebra.TensorProduct.includeLeftRingHom (algebraMap R T r) =
      Algebra.TensorProduct.includeRight (algebraMap R B r)
    exact DFunLike.congr_fun
      (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := R) (A := T) (B := B)) r
  have hbottom : bottomResidueMap.comp (algebraMap L T) = φ := by
    apply IsLocalization.ringHom_ext p.primeCompl
    rw [RingHom.comp_assoc]
    change bottomResidueMap.comp (algebraMap R T) = _
    rw [hbottomBase]
    exact (RingHom.ext fun r ↦ hφ r).symm
  have hresA (a : A) (i : Fin n) : componentResidueMap i (eA ((1 : T) ⊗ₜ[R] a) i) =
      eC' (algebraMap A C a) i := by
    rw [hAleft, ← RingHom.comp_apply, hcomponent]
    exact hφᵢ i a
  have hresT (t : T) (i : Fin n) : componentResidueMap i (completionMap t i) =
      algebraMap k' (k'_i i) (bottomResidueMap t) := by
    let f := (componentResidueMap i).comp ((Pi.evalRingHom _ i).comp completionMap)
    let g := (algebraMap k' (k'_i i)).comp bottomResidueMap
    have : IsLocalHom (g.comp (algebraMap L T)) := by
      change IsLocalHom (((algebraMap k' (k'_i i)).comp bottomResidueMap).comp (algebraMap L T))
      rw [RingHom.comp_assoc, hbottom]
      exact RingHom.isLocalHom_comp (algebraMap k' (k'_i i)) φ
    have heq : f = g := by
      apply completion_ringHom_ext_of_localization p
      ext r
      change componentResidueMap i (completionMap (algebraMap R T r) i) =
        algebraMap k' (k'_i i) (bottomResidueMap (algebraMap R T r))
      rw [← hAright]
      rw [Algebra.TensorProduct.tmul_one_eq_one_tmul, hresA]
      have hb : bottomResidueMap (algebraMap R T r) =
          eB.commRingCatIsoToRingEquiv (algebraMap R B r) :=
        DFunLike.congr_fun hbottomBase r
      rw [hb, ← IsScalarTower.algebraMap_apply R A C,
        IsScalarTower.algebraMap_apply R B C, hγ]
      rfl
    exact DFunLike.congr_fun heq t
  obtain ⟨hγT, hresTensor⟩ := residueMap_tmul_compat eA eBT eCT eB eC' completionMap
    bottomResidueMap componentResidueMap hγ (fun _ ↦ rfl) (fun _ ↦ rfl) (fun _ ↦ rfl)
    hAright hresA hresT
  exact ⟨completionMap, bottomResidueMap, componentResidueMap, hcompletionBase, hbottom,
    hcomponent, isPullback_commRingCat_of_tensor eA eBT eCT eB eC' completionMap
      bottomResidueMap componentResidueMap hPBmod hAright (fun _ ↦ rfl) hγT hresTensor⟩

/-- A general form of [Stacks Project, Tag 0E36], over an arbitrary base and asking only that the
pushout be locally Noetherian.  At the point of a pushout obtained by
identifying the spectrum of a finite product of finite field extensions with the spectrum of the
ground field, the completed local ring is the fibre product of the product of the completed local
rings upstairs and the given ground field over the product of the given extension fields.

The equations following the pullback assertion pin down the four maps in the diagram.

The tag itself is registered on `exists_curvePushoutCompletedLocalRing_isPullback`, which states
this under the four conditions of [Stacks Project, Tag 0E35] alone, deriving both the standing
situation and the locally Noetherian hypothesis from them. -/
public theorem exists_pushoutCompletedLocalRing_isPullback
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    [IsLocallyNoetherian (pushoutScheme s)] [Surjective s.j]
    (n : ℕ) (k' : Type u) (k'_i : Fin n → Type u)
    [Field k'] [∀ i, Field (k'_i i)]
    [∀ i, Algebra k' (k'_i i)] [∀ i, Module.Finite k' (k'_i i)]
    (eZ : s.Z ≅ Spec (.of (∀ i, k'_i i)))
    (eY : s.Y ≅ Spec (.of k'))
    (hj : s.j = eZ.hom ≫
      Spec.map (CommRingCat.ofHom (RingHom.pi fun i ↦ algebraMap k' (k'_i i))) ≫ eY.inv) :
    let y : s.Y := eY.inv (closedPoint k')
    let specPoint : ∀ i, Spec (.of (k'_i i)) ⟶ s.Z := fun i ↦
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom k'_i i)) ≫ eZ.inv
    let z : Fin n → s.Z := fun i ↦ specPoint i (closedPoint (k'_i i))
    let x : pushoutScheme s := pushoutInr s y
    let x' : Fin n → s.X := fun i ↦ s.i (z i)
    ∃ (hx : ∀ i, pushoutInl s (x' i) = x)
      (completionMap : Scheme.completedLocalRing (pushoutScheme s) x →+*
        (∀ i, Scheme.completedLocalRing s.X (x' i)))
      (bottomResidueMap : Scheme.completedLocalRing (pushoutScheme s) x →+* k')
      (componentResidueMap : ∀ i, Scheme.completedLocalRing s.X (x' i) →+* k'_i i),
      let topResidueMap : (∀ i, Scheme.completedLocalRing s.X (x' i)) →+* (∀ i, k'_i i) :=
        RingHom.pi fun i ↦ (componentResidueMap i).comp (Pi.evalRingHom _ i)
      (∀ i, ((Pi.evalRingHom _ i).comp completionMap).comp (algebraMap _ _) =
        (algebraMap _ _).comp
          ((eqToHom (congrArg (fun p ↦ (pushoutScheme s).presheaf.stalk p)
            (hx i).symm) ≫ (pushoutInl s).stalkMap (x' i)).hom)) ∧
      (bottomResidueMap.comp
          (algebraMap ((pushoutScheme s).presheaf.stalk x)
            (Scheme.completedLocalRing (pushoutScheme s) x)) =
        (Scheme.stalkClosedPointTo (eY.inv ≫ pushoutInr s)).hom) ∧
      (∀ i, (componentResidueMap i).comp
          (algebraMap (s.X.presheaf.stalk (x' i))
            (Scheme.completedLocalRing s.X (x' i))) =
        (Scheme.stalkClosedPointTo (specPoint i ≫ s.i)).hom) ∧
      IsPullback
        (CommRingCat.ofHom bottomResidueMap)
        (CommRingCat.ofHom completionMap)
        (CommRingCat.ofHom (RingHom.pi fun i ↦ algebraMap k' (k'_i i)))
        (CommRingCat.ofHom topResidueMap) := by
  classical
  let y : s.Y := eY.inv (closedPoint k')
  let specPoint : ∀ i, Spec (.of (k'_i i)) ⟶ s.Z := fun i ↦
    Spec.map (CommRingCat.ofHom (Pi.evalRingHom k'_i i)) ≫ eZ.inv
  let z : ∀ i, s.Z := fun i ↦ specPoint i (closedPoint (k'_i i))
  let x : pushoutScheme s := pushoutInr s y
  let x' : ∀ i, s.X := fun i ↦ s.i (z i)
  have hmor (i : Fin n) : specPoint i ≫ s.j =
      Spec.map (CommRingCat.ofHom (algebraMap k' (k'_i i))) ≫ eY.inv := by
    dsimp [specPoint]
    rw [hj]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Spec.map_comp_assoc]
    congr 1
  have hjz (i : Fin n) : s.j (z i) = y := by
    change (specPoint i ≫ s.j) (closedPoint (k'_i i)) = eY.inv (closedPoint k')
    rw [hmor i]
    exact congrArg eY.inv (Spec_closedPoint (f :=
      CommRingCat.ofHom (algebraMap k' (k'_i i))))
  have hx (i : Fin n) : pushoutInl s (x' i) = x := by
    dsimp [x, x']
    have hw := congrArg (fun f : s.Z ⟶ pushoutScheme s => f (z i))
      (pushoutAlongClosedImmersionAndIntegral s).isPushout.w
    simpa only [Scheme.Hom.comp_apply] using hw.trans (congrArg (pushoutInr s) (hjz i))
  let W := ((pushoutScheme s).affineCover.f
    ((pushoutScheme s).affineCover.idx x)).opensRange
  have hW : IsAffineOpen W :=
    isAffineOpen_opensRange ((pushoutScheme s).affineCover.f
      ((pushoutScheme s).affineCover.idx x))
  have hxW : x ∈ W := by
    exact (pushoutScheme s).affineCover.covers x
  let Vx : s.X.Opens := pushoutInl s ⁻¹ᵁ W
  let Vy : s.Y.Opens := pushoutInr s ⁻¹ᵁ W
  let Vz : s.Z.Opens := s.j ⁻¹ᵁ Vy
  have hVx : IsAffineOpen Vx := hW.preimage (pushoutInl s)
  have hVy : IsAffineOpen Vy := hW.preimage (pushoutInr s)
  have hVz : IsAffineOpen Vz := hVy.preimage s.j
  have hyVy : y ∈ Vy := by
    change pushoutInr s y ∈ W
    exact hxW
  have hYsub : Subsingleton s.Y := by
    let : Subsingleton (Spec (.of k')) := inferInstance
    have hInj : Function.Injective (eY.hom : s.Y → Spec (.of k')) :=
      fun a b hab ↦ by
        calc
          a = eY.inv (eY.hom a) := by simp
          _ = eY.inv (eY.hom b) := congrArg eY.inv hab
          _ = b := by simp
    exact ⟨fun a b ↦ hInj (Subsingleton.elim _ _)⟩
  have hVyTop : Vy = ⊤ := by
    ext y'
    constructor
    · intro _
      trivial
    · intro _
      have hy' : y' = y := hYsub.elim _ _
      simpa [hy'] using hyVy
  have hVzTop : Vz = ⊤ := by
    dsimp [Vz]
    rw [hVyTop]
    simp
  have hPB0 := pushoutStructureSheaf_isPullback s W
  let R := Γ(pushoutScheme s, W)
  let A := Γ(s.X, Vx)
  let B := Γ(s.Y, Vy)
  let C := Γ(s.Z, Vz)
  let e : s.i ⁻¹ᵁ Vx = s.j ⁻¹ᵁ Vy :=
    congrArg (fun f : s.Z ⟶ pushoutScheme s ↦ f ⁻¹ᵁ W)
      (pushoutAlongClosedImmersionAndIntegral s).isPushout.w
  let α : R →+* A := ((pushoutInl s).app W).hom
  have hαapp : ((pushoutInl s).appLE W Vx le_rfl).hom = α := by
    dsimp [α, Vx]
    rw [Scheme.Hom.appLE_eq_app]
  let β : R →+* B := ((pushoutInr s).app W).hom
  let γ : B →+* C := ((s.j.app Vy).hom)
  let δ : A →+* C := (s.i.app Vx ≫ eqToHom (congrArg (fun U ↦ Γ(s.Z, U)) e)).hom
  have hαβ : IsPullback (CommRingCat.ofHom β) (CommRingCat.ofHom α)
      (CommRingCat.ofHom γ) (CommRingCat.ofHom δ) := by
    simpa [R, A, B, C, β, α, γ, δ, e, Vy, Vx, Vz] using hPB0
  have hType := hαβ.map (forget CommRingCat)
  let : IsNoetherianRing R := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hβsurj : Function.Surjective β := by
    dsimp [β]
    exact (pushoutInr s).app_surjective W hW
  let : Algebra R B := β.toAlgebra
  have hBfinite : Module.Finite R B :=
    Module.Finite.of_surjective (Algebra.linearMap R B) hβsurj
  have hδsurj : Function.Surjective δ := by
    dsimp [δ]
    apply Function.Surjective.comp
    · exact (ConcreteCategory.bijective_of_isIso
        (eqToHom (congrArg (fun U ↦ Γ(s.Z, U)) e))).2
    · exact s.i.app_surjective Vx hVx
  have hPiFinite : Module.Finite k' (∀ i, k'_i i) := inferInstance
  let : Module.Finite k' (∀ i, k'_i i) := hPiFinite
  have hSpecFinite : IsFinite
      (Spec.map (CommRingCat.ofHom (RingHom.pi fun i ↦ algebraMap k' (k'_i i)))) := by
    rw [IsFinite.SpecMap_iff]
    have hpi : RingHom.pi (fun i ↦ algebraMap k' (k'_i i)) =
        (algebraMap k' (∀ i, k'_i i)) := by
      ext a i
      rfl
    change RingHom.Finite (RingHom.pi fun i ↦ algebraMap k' (k'_i i))
    rw [hpi]
    exact RingHom.finite_algebraMap.mpr hPiFinite
  have hjFinite : IsFinite s.j := by
    rw [hj]
    infer_instance
  let : IsFinite s.j := hjFinite
  let : Algebra B C := γ.toAlgebra
  have hγfinite : Module.Finite B C := by
    rw [← RingHom.finite_algebraMap]
    change γ.Finite
    dsimp [γ]
    exact s.j.finite_app Vy hVy
  let : Algebra R C := (γ.comp β).toAlgebra
  let : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Module.Finite R B := hBfinite
  let : Module.Finite B C := hγfinite
  have hCfinite : Module.Finite R C := Module.Finite.trans B C
  let : Algebra R A := α.toAlgebra
  let : Algebra A C := δ.toAlgebra
  have hcomp : γ.comp β = δ.comp α := by
    apply RingHom.ext
    intro r
    have hw := congrArg CommRingCat.Hom.hom hαβ.w
    rw [RingHom.comp_apply, RingHom.comp_apply]
    exact congrArg (fun f : R →+* C => f r) hw
  have hcomp' (r : R) : δ (α r) = γ (β r) := (DFunLike.congr_fun hcomp r).symm
  let : IsScalarTower R A C :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (hcomp' r).symm
  let fRB : R →ₗ[R] A × B :=
    { toFun := fun r ↦ (α r, β r)
      map_add' := by intro r r'; simp
      map_smul' := by
        intro r r'
        change (α (r * r'), β (r * r')) = (α r * α r', β r * β r')
        simp }
  let gBC : A × B →ₗ[R] C :=
    { toFun := fun ab ↦ δ ab.1 - γ ab.2
      map_add' := by
        intro ab ab'
        change δ (ab.1 + ab'.1) - γ (ab.2 + ab'.2) =
          (δ ab.1 - γ ab.2) + (δ ab'.1 - γ ab'.2)
        simp only [map_add]
        abel
      map_smul' := by
        intro r ab
        change δ (α r * ab.1) - γ (β r * ab.2) =
          γ (β r) * (δ ab.1 - γ ab.2)
        rw [map_mul, map_mul]
        rw [hcomp']
        ring }
  have hfexact : Function.Exact fRB gBC := by
    intro ab
    constructor
    · intro hab
      have heq : γ ab.2 = δ ab.1 := (sub_eq_zero.mp hab).symm
      obtain ⟨r, hrB, hrA⟩ := CategoryTheory.Limits.Types.exists_of_isPullback
        hType ab.2 ab.1 heq
      change α r = ab.1 at hrA
      change β r = ab.2 at hrB
      exact ⟨r, Prod.ext hrA hrB⟩
    · rintro ⟨r, hr⟩
      have h1 : α r = ab.1 := by simpa [fRB] using congrArg Prod.fst hr
      have h2 : β r = ab.2 := by simpa [fRB] using congrArg Prod.snd hr
      change δ ab.1 - γ ab.2 = 0
      rw [← h1, ← h2]
      exact sub_eq_zero.mpr (hcomp' r)
  have hPBmod : IsPullback
      (ModuleCat.ofHom (Algebra.linearMap R B)) (ModuleCat.ofHom (Algebra.linearMap R A))
      (ModuleCat.ofHom ((Algebra.linearMap B C).restrictScalars R))
      (ModuleCat.ofHom ((Algebra.linearMap A C).restrictScalars R)) := by
    apply IsPullback.of_map_of_faithful (forget (ModuleCat R))
    convert hType using 1 <;> rfl
  have heY₁ : eY.inv.appTop ≫ eY.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    simp
  have heY₂ : eY.hom.appTop ≫ eY.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    simp
  have heZ₁ : eZ.inv.appTop ≫ eZ.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    simp
  have heZ₂ : eZ.hom.appTop ≫ eZ.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop]
    simp
  let eYΓ : Γ(s.Y, ⊤) ≅ Γ(Spec (.of k'), ⊤) :=
    ⟨eY.inv.appTop, eY.hom.appTop, heY₁, heY₂⟩
  let eZΓ : Γ(s.Z, ⊤) ≅ Γ(Spec (.of (∀ i, k'_i i)), ⊤) :=
    ⟨eZ.inv.appTop, eZ.hom.appTop, heZ₁, heZ₂⟩
  let eB : CommRingCat.of B ≅ CommRingCat.of k' :=
    eqToIso (congrArg (fun U : s.Y.Opens ↦ CommRingCat.of (Γ(s.Y, U))) hVyTop) ≪≫
      eYΓ ≪≫ Scheme.ΓSpecIso (CommRingCat.of k')
  let eC : CommRingCat.of C ≅ CommRingCat.of (∀ i, k'_i i) :=
    eqToIso (congrArg (fun U : s.Z.Opens ↦ CommRingCat.of (Γ(s.Z, U))) hVzTop) ≪≫
      eZΓ ≪≫ Scheme.ΓSpecIso (CommRingCat.of (∀ i, k'_i i))
  have hβgeom : (pushoutScheme s).presheaf.germ W x hxW ≫
      Scheme.stalkClosedPointTo (eY.inv ≫ pushoutInr s) =
        CommRingCat.ofHom β ≫ eB.hom := by
    rw [Scheme.stalkClosedPointTo_comp, Scheme.Hom.germ_stalkMap_assoc]
    rw [germ_to_field_of_iso eY Vy hVyTop hyVy]
    rfl
  have hδgeom (i : Fin n) (hi : x' i ∈ Vx) :
      s.X.presheaf.germ Vx (x' i) hi ≫
        Scheme.stalkClosedPointTo (specPoint i ≫ s.i) =
      CommRingCat.ofHom δ ≫ eC.hom ≫ CommRingCat.ofHom (Pi.evalRingHom k'_i i) := by
    have key := germ_to_field_of_pi_iso eZ (s.i ⁻¹ᵁ Vx) (e.trans hVzTop) i hi
    rw [Scheme.stalkClosedPointTo_comp, Scheme.Hom.germ_stalkMap_assoc]
    refine Eq.trans (congrArg (fun f ↦ Scheme.Hom.app s.i Vx ≫ f) key) ?_
    simp only [δ, eC, eZΓ, Iso.trans_hom, eqToIso.hom, CommRingCat.ofHom_hom,
      Category.assoc]
    change s.i.app Vx ≫
      eqToHom (congrArg (fun U ↦ Γ(s.Z, U)) (e.trans hVzTop)) ≫
      eZ.inv.appTop ≫ (Scheme.ΓSpecIso (.of (∀ i, k'_i i))).hom ≫
        CommRingCat.ofHom (Pi.evalRingHom k'_i i) =
      (s.i.app Vx ≫ eqToHom (congrArg (fun U ↦ Γ(s.Z, U)) e)) ≫
        eqToHom (congrArg (fun U ↦ Γ(s.Z, U)) hVzTop) ≫
        eZ.inv.appTop ≫ (Scheme.ΓSpecIso (.of (∀ i, k'_i i))).hom ≫
          CommRingCat.ofHom (Pi.evalRingHom k'_i i)
    simp only [Category.assoc, eqToHom_trans_assoc]
  have hγgeom : CommRingCat.ofHom γ ≫ eC.hom =
      eB.hom ≫ CommRingCat.ofHom (RingHom.pi fun i ↦ algebraMap k' (k'_i i)) := by
    have htop : s.j.appTop ≫ eZ.inv.appTop ≫
        (Scheme.ΓSpecIso (.of (∀ i, k'_i i))).hom =
      eY.inv.appTop ≫ (Scheme.ΓSpecIso (.of k')).hom ≫
        CommRingCat.ofHom (RingHom.pi fun i ↦ algebraMap k' (k'_i i)) := by
      rw [← Scheme.Hom.comp_appTop_assoc]
      have hj' : eZ.inv ≫ s.j =
          Spec.map (CommRingCat.ofHom (RingHom.pi fun i ↦ algebraMap k' (k'_i i))) ≫
            eY.inv := by simp [hj]
      rw [hj', Scheme.Hom.comp_appTop]
      simp only [Category.assoc, Scheme.ΓSpecIso_naturality]
    dsimp only [γ, eC, eB, eYΓ, eZΓ, Iso.trans_hom, eqToIso.hom]
    simp only [Category.assoc]
    change s.j.app Vy ≫ eqToHom (congrArg (fun U ↦ Γ(s.Z, U)) hVzTop) ≫
      eZ.inv.appTop ≫ (Scheme.ΓSpecIso (.of (∀ i, k'_i i))).hom =
      eqToHom (congrArg (fun U ↦ Γ(s.Y, U)) hVyTop) ≫
        eY.inv.appTop ≫ (Scheme.ΓSpecIso (.of k')).hom ≫ _
    rw [← Category.assoc, app_eq_top_transport s.j Vy hVyTop hVzTop]
    simpa only [Category.assoc] using congrArg
      (fun f ↦ eqToHom (congrArg (fun U ↦ Γ(s.Y, U)) hVyTop) ≫ f) htop
  let pW : Ideal R := (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
  have hqYbot : (hVy.primeIdealOf ⟨y, hyVy⟩).asIdeal = ⊥ :=
    have := (hVy.primeIdealOf ⟨y, hyVy⟩).2
    eq_bot_of_ringEquiv_field eB.commRingCatIsoToRingEquiv _
  let p : Ideal R := RingHom.ker β
  have hpW : pW = p := by
    have hpoint := IsAffineOpen.comap_primeIdealOf_appLE
      (f := pushoutInr s) W hW Vy hVy le_rfl hyVy
    have hβapp : ((pushoutInr s).appLE W Vy le_rfl).hom = β := by
      dsimp [β, Vy]
      rw [Scheme.Hom.appLE_eq_app]
    have hpoint' : (hVy.primeIdealOf ⟨y, hyVy⟩).asIdeal.comap β = pW := by
      rw [← hβapp]
      change (hVy.primeIdealOf ⟨y, hyVy⟩).asIdeal.comap
          ((pushoutInr s).appLE W Vy le_rfl).hom =
        (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
      exact congrArg (fun q : PrimeSpectrum R ↦ q.asIdeal) hpoint
    change pW = RingHom.ker β
    rw [← hpoint', hqYbot]
    rfl
  let β' : R →+* k' := eB.commRingCatIsoToRingEquiv.toRingHom.comp β
  have hkerβ' : RingHom.ker β' = p := by
    ext r
    simp [β', p, RingHom.mem_ker]
  have hp : p.IsPrime := by
    rw [← hkerβ']
    change (Ideal.comap β' (⊥ : Ideal k')).IsPrime
    let : (⊥ : Ideal k').IsPrime := inferInstance
    exact Ideal.comap_isPrime β' (⊥ : Ideal k')
  let : p.IsPrime := hp
  have : p.IsMaximal := by
    rw [← hkerβ']
    exact RingHom.ker_isMaximal_of_surjective β'
      (eB.commRingCatIsoToRingEquiv.surjective.comp hβsurj)
  have hmapαp : Ideal.map α p = RingHom.ker δ := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro r hr
      change β r = 0 at hr
      change δ (α r) = 0
      simpa [hr] using hcomp' r
    · intro a ha
      have ha0 : δ a = 0 := RingHom.mem_ker.mp ha
      obtain ⟨r, hrβ, hrα⟩ := CategoryTheory.Limits.Types.exists_of_isPullback
        hType 0 a (by simp [ha0])
      have hrp : r ∈ p := by
        change β r = 0
        exact hrβ
      rw [← hrα]
      exact Ideal.mem_map_of_mem α hrp
  have hδker_le (q : p.primesOver A) : RingHom.ker δ ≤ q.1 := by
    rw [← hmapαp, Ideal.map_le_iff_le_comap]
    exact le_of_eq q.2.2.over
  let primesEquiv : p.primesOver A ≃ PrimeSpectrum C :=
    { toFun := fun q ↦ ⟨Ideal.map δ q.1,
        Ideal.map_isPrime_of_surjective hδsurj (hδker_le q)⟩
      invFun := fun q ↦ ⟨Ideal.comap δ q.asIdeal, by
        let : q.asIdeal.IsPrime := q.2
        have hγq : Ideal.comap γ q.asIdeal = ⊥ :=
          eq_bot_of_ringEquiv_field eB.commRingCatIsoToRingEquiv _
        refine ⟨Ideal.comap_isPrime δ q.asIdeal, ⟨?_⟩⟩
        change p = Ideal.comap α (Ideal.comap δ q.asIdeal)
        rw [Ideal.comap_comap α δ]
        rw [← hcomp]
        rw [← Ideal.comap_comap β γ, hγq]
        simp [p, RingHom.ker_eq_comap_bot]⟩
      left_inv := by
        intro q
        apply Subtype.ext
        change Ideal.comap δ (Ideal.map δ q.1) = q.1
        rw [Ideal.comap_map_of_surjective δ hδsurj]
        rw [show Ideal.comap δ (⊥ : Ideal C) = RingHom.ker δ by rfl,
          sup_eq_left.mpr (hδker_le q)]
      right_inv := by
        intro q
        apply PrimeSpectrum.ext
        change Ideal.map δ (Ideal.comap δ q.asIdeal) = q.asIdeal
        exact Ideal.map_comap_of_surjective δ hδsurj q.asIdeal }
  let eC' : C ≃+* (∀ i, k'_i i) := eC.commRingCatIsoToRingEquiv
  let primesEquivFin : p.primesOver A ≃ Fin n :=
    primesEquiv.trans ((PrimeSpectrum.comapEquiv eC').toEquiv.trans
      (primeSpectrumPiFieldEquivFin k'_i))
  have hgsurj : Function.Surjective gBC := by
    intro c
    obtain ⟨a, ha⟩ := hδsurj c
    exact ⟨(a, 0), by simp [gBC, ha]⟩
  have hABfinite : Module.Finite R (A × B) :=
    Module.Finite.of_exact hfexact hgsurj
  let : Module.Finite R (A × B) := hABfinite
  have hAfinite : Module.Finite R A :=
    Module.Finite.of_injective (LinearMap.inl R A B) (by intro a a' h; exact congrArg Prod.fst h)
  let : Module.Finite R A := hAfinite
  let : IsNoetherianRing A := IsNoetherianRing.of_finite R A
  have hxVx (i : Fin n) : x' i ∈ Vx := by
    change pushoutInl s (x' i) ∈ W
    rw [hx i]
    exact hxW
  let qX : Fin n → Ideal A := fun i ↦ (hVx.primeIdealOf ⟨x' i, hxVx i⟩).asIdeal
  have hqXover (i : Fin n) : qX i ∈ p.primesOver A := by
    have hpoint := IsAffineOpen.comap_primeIdealOf_appLE
      (f := pushoutInl s) W hW Vx hVx le_rfl (hxVx i)
    have hcomap : (qX i).comap α = pW := by
      rw [← hαapp]
      change (hVx.primeIdealOf ⟨x' i, hxVx i⟩).asIdeal.comap
          ((pushoutInl s).appLE W Vx le_rfl).hom
        = (hW.primeIdealOf ⟨x, hxW⟩).asIdeal
      let w' : W := ⟨pushoutInl s (x' i), by
        rw [hx i]
        exact hxW⟩
      have hw' : w' = ⟨x, hxW⟩ := Subtype.ext (hx i)
      have hpoint' : PrimeSpectrum.comap
          ((pushoutInl s).appLE W Vx le_rfl).hom
          (hVx.primeIdealOf ⟨x' i, hxVx i⟩) = hW.primeIdealOf ⟨x, hxW⟩ := by
        rw [← hw']
        exact hpoint
      simpa only [PrimeSpectrum.comap_asIdeal] using
        congrArg (fun q : PrimeSpectrum R ↦ q.asIdeal) hpoint'
    let : (qX i).IsPrime := (hVx.primeIdealOf ⟨x' i, hxVx i⟩).2
    change (qX i).IsPrime ∧ (qX i).LiesOver p
    refine ⟨inferInstance, ?_⟩
    rw [Ideal.liesOver_iff]
    change p = (qX i).comap α
    rw [← hpW, hcomap]
  let xq : p.primesOver A → s.X := fun q ↦ hVx.fromSpec ⟨q.1, q.2.1⟩
  have hxqV (q : p.primesOver A) : xq q ∈ Vx := by
    have hmem : (⟨q.1, q.2.1⟩ : PrimeSpectrum A) ∈ hVx.fromSpec ⁻¹ᵁ Vx := by
      rw [hVx.fromSpec_preimage_self]
      trivial
    change hVx.fromSpec ⟨q.1, q.2.1⟩ ∈ Vx
    exact hmem
  let : ∀ q : p.primesOver A, Algebra A (s.X.presheaf.stalk (xq q)) := fun q ↦
    (s.X.presheaf.germ Vx (xq q) (hxqV q)).hom.toAlgebra
  let : ∀ q : p.primesOver A, Algebra R (s.X.presheaf.stalk (xq q)) := fun q ↦
    (((algebraMap A (s.X.presheaf.stalk (xq q))).comp α).toAlgebra)
  have : ∀ q : p.primesOver A, IsScalarTower R A (s.X.presheaf.stalk (xq q)) := fun q ↦
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hlocq (q : p.primesOver A) :
      IsLocalization.AtPrime (s.X.presheaf.stalk (xq q)) q.1 := by
    have h := hVx.isLocalization_stalk ⟨xq q, hxqV q⟩
    have hq : hVx.primeIdealOf ⟨xq q, hxqV q⟩ = ⟨q.1, q.2.1⟩ := by
      have hsub : (⟨xq q, hxqV q⟩ : Vx) = hVx.isoSpec.inv ⟨q.1, q.2.1⟩ := by
        apply Subtype.ext
        rfl
      change hVx.isoSpec.hom ⟨xq q, hxqV q⟩ = ⟨q.1, q.2.1⟩
      rw [hsub]
      exact congrArg (fun f : Spec (.of A) ⟶ Spec (.of A) => f ⟨q.1, q.2.1⟩)
        hVx.isoSpec.inv_hom_id
    simpa [hq] using h
  let : ∀ q : p.primesOver A, IsLocalization.AtPrime
      (s.X.presheaf.stalk (xq q)) q.1 := hlocq
  let : ∀ q : p.primesOver A, IsNoetherianRing (s.X.presheaf.stalk (xq q)) := fun q =>
    IsLocalization.isNoetherianRing q.1.primeCompl (s.X.presheaf.stalk (xq q)) inferInstance
  let : Algebra R ((pushoutScheme s).presheaf.stalk x) :=
    (pushoutScheme s).presheaf.algebra_section_stalk ⟨x, hxW⟩
  have hlocx : IsLocalization.AtPrime ((pushoutScheme s).presheaf.stalk x) p := by
    convert hW.isLocalization_stalk ⟨x, hxW⟩ using 1
    exact hpW.symm
  let : IsLocalization.AtPrime ((pushoutScheme s).presheaf.stalk x) p := hlocx
  let : IsNoetherianRing ((pushoutScheme s).presheaf.stalk x) :=
    IsLocalization.isNoetherianRing p.primeCompl _ inferInstance
  let qXi : Fin n → p.primesOver A := fun i ↦ ⟨qX i, hqXover i⟩
  have hxqXi (i : Fin n) : xq (qXi i) = x' i := by
    have hspec : (⟨qX i, (hqXover i).1⟩ : PrimeSpectrum A) =
        hVx.primeIdealOf ⟨x' i, hxVx i⟩ := by
      apply PrimeSpectrum.ext
      rfl
    dsimp [xq, qXi]
    rw [hspec]
    exact hVx.fromSpec_primeIdealOf ⟨x' i, hxVx i⟩
  have hqXi_inj : Function.Injective qXi := by
    intro i j hij
    have hxij : x' i = x' j := by
      rw [← hxqXi i, ← hxqXi j, hij]
    have hzij : z i = z j := ((IsClosedImmersion.isClosedEmbedding s.i).injective hxij)
    have hspec := congrArg eZ.hom hzij
    change eZ.hom (eZ.inv (PrimeSpectrum.comap (Pi.evalRingHom k'_i i)
      (closedPoint (k'_i i)))) = eZ.hom (eZ.inv (PrimeSpectrum.comap
        (Pi.evalRingHom k'_i j) (closedPoint (k'_i j)))) at hspec
    change (eZ.inv ≫ eZ.hom) _ = (eZ.inv ≫ eZ.hom) _ at hspec
    simp only [eZ.inv_hom_id] at hspec
    apply_fun (fun p : Spec (.of (∀ i, k'_i i)) ↦ p) at hspec
    exact congrArg Sigma.fst (PrimeSpectrum.sigmaToPi_injective k'_i
      (show PrimeSpectrum.sigmaToPi k'_i ⟨i, closedPoint (k'_i i)⟩ =
        PrimeSpectrum.sigmaToPi k'_i ⟨j, closedPoint (k'_i j)⟩ from hspec))
  have hqXi_surj : Function.Surjective qXi := by
    have h := Finite.surjective_of_injective (primesEquivFin.injective.comp hqXi_inj)
    intro q
    obtain ⟨i, hi⟩ := h (primesEquivFin q)
    exact ⟨i, primesEquivFin.injective hi⟩
  let eIndex : Fin n ≃ p.primesOver A := Equiv.ofBijective qXi ⟨hqXi_inj, hqXi_surj⟩
  let T := Scheme.completedLocalRing (pushoutScheme s) x
  let : ∀ i, Algebra A (s.X.presheaf.stalk (x' i)) := fun i ↦
    (s.X.presheaf.germ Vx (x' i) (hxVx i)).hom.toAlgebra
  let : ∀ i, IsNoetherianRing (s.X.presheaf.stalk (x' i)) := fun i ↦ by
    rw [← hxqXi i]
    infer_instance
  let Sq : p.primesOver A → Type u := fun q ↦ s.X.presheaf.stalk (xq q)
  have hCompletionEquiv : Nonempty
      (TensorProduct (↑R) (↑A) T ≃ₐ[↑A]
        ∀ q : p.primesOver A, AdicCompletion
          (IsLocalRing.maximalIdeal (Sq q)) (Sq q)) :=
    AdicCompletion.nonempty_algEquiv_pi_primesOver
    (R := R) (S := A) p ((pushoutScheme s).presheaf.stalk x) Sq
  obtain ⟨eCompletion₀⟩ := hCompletionEquiv
  let eProd : (∀ q : p.primesOver A, Scheme.completedLocalRing s.X (xq q)) ≃+*
      (∀ i, Scheme.completedLocalRing s.X (x' i)) :=
    (RingEquiv.piCongrLeft _ eIndex).symm.trans
      (RingEquiv.piCongrRight fun i ↦
        (eqToIso (congrArg (fun y : s.X ↦ CommRingCat.of (Scheme.completedLocalRing s.X y))
          (hxqXi i))).commRingCatIsoToRingEquiv)
  let eCompletion : TensorProduct (↑R) (↑A) T ≃+*
      (∀ i, Scheme.completedLocalRing s.X (x' i)) :=
    eCompletion₀.toRingEquiv.trans eProd
  have heCompletion (a : A) (i : Fin n) :
      eCompletion (algebraMap (↑A) (TensorProduct (↑R) (↑A) T) a) i =
        algebraMap (s.X.presheaf.stalk (x' i)) (Scheme.completedLocalRing s.X (x' i))
          (algebraMap (↑A) (s.X.presheaf.stalk (x' i)) a) := by
    change (eqToHom (congrArg (fun y : s.X ↦ CommRingCat.of (Scheme.completedLocalRing s.X y))
      (hxqXi i))).hom
      (eCompletion₀ (algebraMap (↑A) (TensorProduct (↑R) (↑A) T) a) (qXi i)) = _
    rw [eCompletion₀.commutes]
    exact completedLocalRing_congr_germ s.X Vx _ _ (hxqXi i) _ _ a
  have hσ (i : Fin n) (r : R) :
      (eqToHom (congrArg (fun q ↦ (pushoutScheme s).presheaf.stalk q) (hx i).symm) ≫
          (pushoutInl s).stalkMap (x' i)).hom
          (algebraMap (↑R) ((pushoutScheme s).presheaf.stalk x) r) =
        algebraMap (↑A) (s.X.presheaf.stalk (x' i)) (algebraMap (↑R) (↑A) r) := by
    have hyW : pushoutInl s (x' i) ∈ W := by rw [hx i]; exact hxW
    have htransport :
        ((eqToHom (congrArg (fun q ↦ (pushoutScheme s).presheaf.stalk q)
          (hx i).symm)).hom)
          (algebraMap (↑R) ((pushoutScheme s).presheaf.stalk x) r) =
          ((pushoutScheme s).presheaf.germ W (pushoutInl s (x' i)) hyW).hom r := by
      rw [stalk_eqToHom_eq_stalkCongr (pushoutScheme s) x (pushoutInl s (x' i))
        (hx i).symm]
      change (pushoutScheme s).presheaf.stalkSpecializes
          (Inseparable.of_eq (hx i).symm).ge
          (((pushoutScheme s).presheaf.germ W x hxW).hom r) = _
      have h := TopCat.Presheaf.germ_stalkSpecializes
        (pushoutScheme s).presheaf (U := W) (y := x) hxW
        (specializes_of_eq (hx i))
      exact DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp h) r
    simp only [CommRingCat.hom_comp, RingHom.comp_apply]
    rw [htransport, Scheme.Hom.germ_stalkMap_apply]
    rfl
  obtain ⟨completionMap, bottomResidueMap, componentResidueMap, h1, h2, h3, h4⟩ :=
    exists_isPullback_adicCompletion p
      (fun i ↦ (eqToHom (congrArg (fun q ↦ (pushoutScheme s).presheaf.stalk q) (hx i).symm) ≫
        (pushoutInl s).stalkMap (x' i)).hom)
      (Scheme.stalkClosedPointTo (eY.inv ≫ pushoutInr s)).hom
      (fun i ↦ (Scheme.stalkClosedPointTo (specPoint i ≫ s.i)).hom)
      (hφloc := Scheme.isLocalHom_stalkClosedPointTo _)
      (hφᵢloc := fun i ↦ Scheme.isLocalHom_stalkClosedPointTo _)
      eB eC' eCompletion heCompletion hPBmod (fun _ hr ↦ hr) hσ
      (fun r ↦ congrArg (fun f ↦ (CommRingCat.Hom.hom f) r) hβgeom)
      (fun i a ↦ congrArg (fun f ↦ (CommRingCat.Hom.hom f) a) (hδgeom i (hxVx i)))
      (fun b ↦ congrArg (fun f ↦ (CommRingCat.Hom.hom f) b) hγgeom)
  exact ⟨hx, completionMap, bottomResidueMap, componentResidueMap, h1, h2, h3, h4⟩


/-- A general form of [Stacks Project, Tag 0E36], taking the standing situation of
[Stacks Project, Tag 0ECI] as given rather than deriving it from the conditions of
[Stacks Project, Tag 0E35].  A pushout along a closed immersion and an integral morphism over a
base whose scheme `X` is locally of finite type and whose `Y` and `Z` are finite, with `Z ⟶ Y`
surjective: let `Y` be the spectrum of a field `k'` and `Z` the spectrum of a finite product of
finite extensions `k'_i/k'`.  Writing `x` for the image of `Y` in the pushout and `x'_i` for the
image of `Spec (k'_i)` in `X`, the completed local ring at `x` is the fibre product of the product
of the completed local rings at the `x'_i` and the field `k'` over the product of the `k'_i`.

The equations following the pullback assertion pin down the four maps in the diagram.

This is `exists_pushoutCompletedLocalRing_isPullback` with the hypothesis that the pushout is
locally Noetherian discharged: the pushout is locally of finite type over the base by
[Stacks Project, Tag 0E27] (`pushoutToBase_locallyOfFiniteType`), and the base is the spectrum of
a field, hence locally Noetherian.

The tag itself is registered on `exists_curvePushoutCompletedLocalRing_isPullback`, which assumes
only the four conditions of [Stacks Project, Tag 0E35] and derives the standing situation from
them; this statement assumes the standing situation, which 0E35 proves. -/
public theorem exists_pushoutCompletedLocalRing_isPullback_of_locallyOfFiniteType
    (s : PushoutAlongClosedImmersionAndIntegralSituation.{u})
    (k : Type u) [Field k] (eS : s.S ≅ Spec (.of k))
    [LocallyOfFiniteType s.pX] [IsFinite s.pY] [IsFinite s.pZ] [Surjective s.j]
    (n : ℕ) (k' : Type u) (k'_i : Fin n → Type u)
    [Field k'] [∀ i, Field (k'_i i)]
    [∀ i, Algebra k' (k'_i i)] [∀ i, Module.Finite k' (k'_i i)]
    (eZ : s.Z ≅ Spec (.of (∀ i, k'_i i)))
    (eY : s.Y ≅ Spec (.of k'))
    (hj : s.j = eZ.hom ≫
      Spec.map (CommRingCat.ofHom (RingHom.pi fun i ↦ algebraMap k' (k'_i i))) ≫ eY.inv) :
    let y : s.Y := eY.inv (closedPoint k')
    let specPoint : ∀ i, Spec (.of (k'_i i)) ⟶ s.Z := fun i ↦
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom k'_i i)) ≫ eZ.inv
    let z : Fin n → s.Z := fun i ↦ specPoint i (closedPoint (k'_i i))
    let x : pushoutScheme s := pushoutInr s y
    let x' : Fin n → s.X := fun i ↦ s.i (z i)
    ∃ (hx : ∀ i, pushoutInl s (x' i) = x)
      (completionMap : Scheme.completedLocalRing (pushoutScheme s) x →+*
        (∀ i, Scheme.completedLocalRing s.X (x' i)))
      (bottomResidueMap : Scheme.completedLocalRing (pushoutScheme s) x →+* k')
      (componentResidueMap : ∀ i, Scheme.completedLocalRing s.X (x' i) →+* k'_i i),
      let topResidueMap : (∀ i, Scheme.completedLocalRing s.X (x' i)) →+* (∀ i, k'_i i) :=
        RingHom.pi fun i ↦ (componentResidueMap i).comp (Pi.evalRingHom _ i)
      (∀ i, ((Pi.evalRingHom _ i).comp completionMap).comp (algebraMap _ _) =
        (algebraMap _ _).comp
          ((eqToHom (congrArg (fun p ↦ (pushoutScheme s).presheaf.stalk p)
            (hx i).symm) ≫ (pushoutInl s).stalkMap (x' i)).hom)) ∧
      (bottomResidueMap.comp
          (algebraMap ((pushoutScheme s).presheaf.stalk x)
            (Scheme.completedLocalRing (pushoutScheme s) x)) =
        (Scheme.stalkClosedPointTo (eY.inv ≫ pushoutInr s)).hom) ∧
      (∀ i, (componentResidueMap i).comp
          (algebraMap (s.X.presheaf.stalk (x' i))
            (Scheme.completedLocalRing s.X (x' i))) =
        (Scheme.stalkClosedPointTo (specPoint i ≫ s.i)).hom) ∧
      IsPullback
        (CommRingCat.ofHom bottomResidueMap)
        (CommRingCat.ofHom completionMap)
        (CommRingCat.ofHom (RingHom.pi fun i ↦ algebraMap k' (k'_i i)))
        (CommRingCat.ofHom topResidueMap) := by
  have : IsLocallyNoetherian s.S := isLocallyNoetherian_of_isOpenImmersion eS.hom
  have : IsLocallyNoetherian (pushoutScheme s) :=
    LocallyOfFiniteType.isLocallyNoetherian (pushoutToBase s)
  exact exists_pushoutCompletedLocalRing_isPullback s n k' k'_i eZ eY hj

/-- **Stacks Project, Tag 0E36.**  Stated in the situation of [Stacks Project, Tag 0E35] itself:
`k` is a field, `X` is separated of finite type over `k` of dimension `≤ 1`, `i : Z ⟶ X` is a
closed immersion, `Z` and `Y` are finite over `Spec k` and `j : Z ⟶ Y` is surjective.  Let `Y` be
the spectrum of a field `k'` and `Z` the spectrum of a product of finite extensions `k'_i/k'`,
let `x` be the image of `Y` in the pushout `Y ⨿_Z X` and `x'_i` the image of `Spec (k'_i)` in `X`.
Then the completed local ring at `x` is the fibre product of the product of the completed local
rings at the `x'_i` and the field `k'` over the product of the `k'_i`, the horizontal maps being
the maps to the residue fields.

The equations following the pullback assertion pin down the four maps in the diagram.

Against the notation of [Stacks Project, Tag 0E35] the translation is `Z = Z'`, `X = X'` and
`Y = Z`, following the library's `PushoutAlongClosedImmersionAndIntegralSituation`.  The standing
situation of [Stacks Project, Tag 0ECI] is *derived* from the four conditions here, by
`curvePushoutSituation` ([Stacks Project, Tag 0E35]), rather than assumed; the locally Noetherian
hypothesis of `exists_pushoutCompletedLocalRing_isPullback` is discharged along the way through
[Stacks Project, Tag 0E27]. -/
@[stacks 0E36]
public theorem exists_curvePushoutCompletedLocalRing_isPullback
    (k : Type u) [Field k] {X Y Z : Scheme.{u}}
    (pX : X ⟶ Spec (.of k)) (pY : Y ⟶ Spec (.of k)) (pZ : Z ⟶ Spec (.of k))
    (i : Z ⟶ X) (j : Z ⟶ Y) (hi : i ≫ pX = pZ) (hj : j ≫ pY = pZ)
    [IsSeparated pX] [LocallyOfFiniteType pX] (hdim : topologicalKrullDim X ≤ 1)
    [IsClosedImmersion i] [IsFinite pY] [IsFinite pZ] [Surjective j]
    (n : ℕ) (k' : Type u) (k'_i : Fin n → Type u)
    [Field k'] [∀ a, Field (k'_i a)]
    [∀ a, Algebra k' (k'_i a)] [∀ a, Module.Finite k' (k'_i a)]
    (eZ : Z ≅ Spec (.of (∀ a, k'_i a)))
    (eY : Y ≅ Spec (.of k'))
    (hjeq : j = eZ.hom ≫
      Spec.map (CommRingCat.ofHom (RingHom.pi fun a ↦ algebraMap k' (k'_i a))) ≫ eY.inv) :
    let s : PushoutAlongClosedImmersionAndIntegralSituation.{u} :=
      curvePushoutSituation k pX pY pZ i j hi hj hdim
    let y : Y := eY.inv (closedPoint k')
    let specPoint : ∀ a, Spec (.of (k'_i a)) ⟶ Z := fun a ↦
      Spec.map (CommRingCat.ofHom (Pi.evalRingHom k'_i a)) ≫ eZ.inv
    let z : Fin n → Z := fun a ↦ specPoint a (closedPoint (k'_i a))
    let x : pushoutScheme s := pushoutInr s y
    let x' : Fin n → X := fun a ↦ i (z a)
    ∃ (hx : ∀ a, pushoutInl s (x' a) = x)
      (completionMap : Scheme.completedLocalRing (pushoutScheme s) x →+*
        (∀ a, Scheme.completedLocalRing X (x' a)))
      (bottomResidueMap : Scheme.completedLocalRing (pushoutScheme s) x →+* k')
      (componentResidueMap : ∀ a, Scheme.completedLocalRing X (x' a) →+* k'_i a),
      let topResidueMap : (∀ a, Scheme.completedLocalRing X (x' a)) →+* (∀ a, k'_i a) :=
        RingHom.pi fun a ↦ (componentResidueMap a).comp (Pi.evalRingHom _ a)
      (∀ a, ((Pi.evalRingHom _ a).comp completionMap).comp
          (algebraMap ((pushoutScheme s).presheaf.stalk x)
            (Scheme.completedLocalRing (pushoutScheme s) x)) =
        (algebraMap (X.presheaf.stalk (x' a)) (Scheme.completedLocalRing X (x' a))).comp
          ((eqToHom (congrArg (fun p ↦ (pushoutScheme s).presheaf.stalk p)
            (hx a).symm) ≫ (pushoutInl s).stalkMap (x' a)).hom)) ∧
      (bottomResidueMap.comp
          (algebraMap ((pushoutScheme s).presheaf.stalk x)
            (Scheme.completedLocalRing (pushoutScheme s) x)) =
        (Scheme.stalkClosedPointTo (eY.inv ≫ pushoutInr s)).hom) ∧
      (∀ a, (componentResidueMap a).comp
          (algebraMap (X.presheaf.stalk (x' a))
            (Scheme.completedLocalRing X (x' a))) =
        (Scheme.stalkClosedPointTo (specPoint a ≫ i)).hom) ∧
      IsPullback
        (CommRingCat.ofHom bottomResidueMap)
        (CommRingCat.ofHom completionMap)
        (CommRingCat.ofHom (RingHom.pi fun a ↦ algebraMap k' (k'_i a)))
        (CommRingCat.ofHom topResidueMap) := by
  have hFT : LocallyOfFiniteType (curvePushoutSituation k pX pY pZ i j hi hj hdim).pX :=
    inferInstanceAs (LocallyOfFiniteType pX)
  have hFY : IsFinite (curvePushoutSituation k pX pY pZ i j hi hj hdim).pY :=
    inferInstanceAs (IsFinite pY)
  have hFZ : IsFinite (curvePushoutSituation k pX pY pZ i j hi hj hdim).pZ :=
    inferInstanceAs (IsFinite pZ)
  have hSurj : Surjective (curvePushoutSituation k pX pY pZ i j hi hj hdim).j :=
    inferInstanceAs (Surjective j)
  exact exists_pushoutCompletedLocalRing_isPullback_of_locallyOfFiniteType
    (curvePushoutSituation k pX pY pZ i j hi hj hdim) k (Iso.refl _) n k' k'_i eZ eY hjeq

end AlgebraicGeometry

end
