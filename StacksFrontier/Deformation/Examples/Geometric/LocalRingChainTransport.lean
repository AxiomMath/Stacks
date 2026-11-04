module

public import StacksFrontier.Deformation.Examples.Geometric.IsolatedSingularitiesChain
public import StacksFrontier.RingTheory.AdicCompletion.AdicCompletionMapUniqueness
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The henselization and completion maps of the chain of Stacks 0DZF at isomorphic local rings

Tag 0DZF proves that, for a finite type `k`-algebra `P` smooth away from maximal ideals
`𝔪_1, …, 𝔪_n`, the maps `∏ Def_{P_{𝔪 i}} ⟶ ∏ Def_{P^h_{𝔪 i}} ⟶ ∏ Def_{P^∧_{𝔪 i}}` are smooth and
induce isomorphisms on tangent spaces. This file transfers the two conclusions along ring
isomorphisms, to families of local rings which are only *isomorphic* to the `P_{𝔪 i}`, such as
the local rings `𝒪_{X, p_i}` of a curve.

## Main definitions

* `Deformation.Examples.henselizationFunctorsAt`: the second map of the chain at an arbitrary
  family of local rings.
* `Deformation.Examples.completedLocalRingFunctorsAt`: the third map of the chain at an arbitrary
  family of Noetherian local rings.

## Main results

* `Deformation.Examples.nonempty_basedIso_adicCompletionFunctor_congr`: completion is compatible
  with transport along an isomorphism of the rings being completed.
* `Deformation.Examples.isSmooth_of_conj`, `Deformation.Examples.bijective_differential_of_conj`:
  smoothness and bijectivity on tangent spaces pass across conjugation by transports.
* `Deformation.Examples.localRingChainAt_conclusions`: the two conclusions for the second and
  third maps at local rings isomorphic to the `P_{𝔪 i}`.
-/

@[expose] public section

open CategoryTheory

universe uι u w v₁ u₁ v₂ u₂ v₃ u₃

namespace Deformation.Examples

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### Isomorphisms of based functors: whiskering and products -/

section Glue

variable {𝓐 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓑 : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓒 : BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-- Precomposing an isomorphism of based functors with a based functor. -/
noncomputable def basedIsoWhiskerLeft (F : BasedFunctor 𝓐 𝓑) {G H : BasedFunctor 𝓑 𝓒}
    (e : G ≅ H) : BasedFunctor.comp F G ≅ BasedFunctor.comp F H :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerLeft F.toFunctor ((BasedNatTrans.forgetful 𝓑 𝓒).mapIso e))
    (fun a => (e.hom.isHomLift (F.w_obj a) : _))

/-- Postcomposing an isomorphism of based functors with a based functor. -/
noncomputable def basedIsoWhiskerRight {F G : BasedFunctor 𝓐 𝓑} (e : F ≅ G)
    (H : BasedFunctor 𝓑 𝓒) : BasedFunctor.comp F H ≅ BasedFunctor.comp G H :=
  BasedNatIso.mkNatIso
    (Functor.isoWhiskerRight ((BasedNatTrans.forgetful 𝓐 𝓑).mapIso e) H.toFunctor)
    (fun a => by
      have : 𝓑.p.IsHomLift (𝟙 (𝓐.p.obj a)) (((BasedNatTrans.forgetful 𝓐 𝓑).mapIso e).hom.app a) :=
        e.hom.isHomLift' a
      exact BasedFunctor.preserves_isHomLift H _ _)

variable {ι : Type uι}

/-- Componentwise isomorphisms of based functors into the factors of a product assemble to an
isomorphism of the induced functors into the product. -/
noncomputable def piLiftIsoOfComponents {𝓖 : ι → BasedCategory.{v₂, u₂}
      (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (φ ψ : ∀ i, BasedFunctor 𝓐 (𝓖 i)) (e : ∀ i, φ i ≅ ψ i) : piLift φ ≅ piLift ψ := by
  refine BasedNatIso.mkNatIso (NatIso.ofComponents (fun a =>
    { hom := { hbase := 𝟙 _, component := fun i => (e i).hom.app a,
               hcomponent := fun i => (e i).hom.isHomLift rfl }
      inv := { hbase := 𝟙 _, component := fun i => (e i).inv.app a,
               hcomponent := fun i => (e i).inv.isHomLift rfl }
      hom_inv_id := PiOver.Hom.ext' (Category.comp_id _) fun i =>
        congrArg (fun t => t.toNatTrans.app a) (e i).hom_inv_id
      inv_hom_id := PiOver.Hom.ext' (Category.comp_id _) fun i =>
        congrArg (fun t => t.toNatTrans.app a) (e i).inv_hom_id }) ?_) ?_
  · intro a b f
    exact PiOver.Hom.ext' ((Category.comp_id _).trans (Category.id_comp _).symm) fun i =>
      (e i).hom.naturality f
  · intro a
    change (PiOver.structureFunctor _).IsHomLift (𝟙 _) (_ : PiOver.Hom _ _)
    exact IsHomLift.of_fac' _ _ _ rfl rfl (by simp; rfl)

/-- Componentwise isomorphisms of based functors between the factors of two products assemble
to an isomorphism of the induced functors between the products. -/
noncomputable def piMapIsoOfComponents
    {𝓖 : ι → BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    {𝓗 : ι → BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
    (φ ψ : ∀ i, BasedFunctor (𝓖 i) (𝓗 i)) (e : ∀ i, φ i ≅ ψ i) : piMap φ ≅ piMap ψ :=
  piLiftIsoOfComponents _ _ fun i => basedIsoWhiskerLeft (piProj 𝓖 i) (e i)

end Glue

/-! ### Composing two transports -/

section TransportComp

variable {R S T : Type w} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S] [CommRing T]
  [Algebra k T]

/-- Transporting along two ring isomorphisms in succession is transporting along any ring
isomorphism agreeing with their composite. -/
noncomputable def ringDeformationTransportCompIso (a : R ≃+* S)
    (ha : ∀ x : k, a (algebraMap k R x) = algebraMap k S x) (b : S ≃+* T)
    (hb : ∀ x : k, b (algebraMap k S x) = algebraMap k T x) (c : R ≃+* T)
    (hc : ∀ x : k, c (algebraMap k R x) = algebraMap k T x) (h : ∀ r, b (a r) = c r) :
    BasedFunctor.comp (ringDeformationTransport (Λ := Λ) a ha) (ringDeformationTransport b hb) ≅
      ringDeformationTransport (Λ := Λ) c hc :=
  basedIsoOfFiberEquiv _ _ (fun _ => RingEquiv.refl _)
    (fun _ x => (congrArg _ (eqToHom_hom_refl _ x)).symm)
    (fun _ _ => (h _).symm.trans rfl) (fun _ _ _ _ => rfl)

end TransportComp

attribute [local instance 100] henselizationAlgebra

/-- The henselization of a Noetherian local ring along its maximal ideal is Noetherian. -/
@[ega "IV 18.6.6" "(v)", sga "4 VIII 4.1"]
theorem isNoetherianRing_henselization_maximalIdeal (R : Type w) [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] :
    IsNoetherianRing (henselization R (IsLocalRing.maximalIdeal R) : Type w) := by
  classical
  obtain ⟨H, hH, j, hh, hj⟩ := exists_henselization R (IsLocalRing.maximalIdeal R)
  let : CommRing H := hH
  let : Algebra R H := j.toAlgebra
  have hj' : ∀ (B : Type w) (_ : CommRing B) (J : Ideal B),
      HenselianPair B J → ∀ f : R →+* B,
        IsLocalRing.maximalIdeal R ≤ J.comap f →
          ∃! g : H →+* B,
            g.comp (algebraMap R H) = f ∧
              (IsLocalRing.maximalIdeal R).map (algebraMap R H) ≤ J.comap g := by
    intro B hB J hJ f hf
    simpa only [RingHom.algebraMap_toAlgebra] using hj B hB J hJ f hf
  have : IsNoetherianRing H :=
    (henselization_isNoetherian_and_completion_equiv R
      (IsLocalRing.maximalIdeal R) H hh hj').2.1
  obtain ⟨e⟩ := nonempty_algEquiv_henselization R (IsLocalRing.maximalIdeal R) H hh hj'
  exact isNoetherianRing_of_ringEquiv H e.toRingEquiv.symm

/-- The canonical identification of the completion of a ring along `I` with the completion of
its henselization along the extension of `I`. -/
noncomputable def adicCompletionHenselizationEquiv (R : Type w) [CommRing R] (I : Ideal R) :
    AdicCompletion I R ≃+*
      AdicCompletion (I.map (algebraMap R (henselization R I : Type w)))
        (henselization R I : Type w) :=
  RingEquiv.ofBijective _ (bijective_adicCompletionMap_henselization R I)

/-- That identification is `k`-linear, read backwards. -/
theorem algebraMap_adicCompletionHenselizationEquiv_symm (R : Type w) [CommRing R]
    [Algebra k R] (I : Ideal R) (a : k) :
    (adicCompletionHenselizationEquiv R I).symm
        (algebraMap k (AdicCompletion (I.map (algebraMap R (henselization R I : Type w)))
          (henselization R I : Type w)) a) =
      algebraMap k (AdicCompletion I R) a := by
  apply (adicCompletionHenselizationEquiv R I).injective
  rw [RingEquiv.apply_symm_apply]
  have h := DFunLike.congr_fun
    (adicCompletionMap_comp_algebraMap (algebraMap R (henselization R I : Type w)) I
      (I.map (algebraMap R (henselization R I : Type w))) le_rfl)
    (algebraMap k R a)
  simp only [RingHom.coe_comp, Function.comp_apply] at h
  show _ = adicCompletionMap (algebraMap R (henselization R I : Type w)) I
      (I.map (algebraMap R (henselization R I : Type w))) le_rfl
      (algebraMap k (AdicCompletion I R) a)
  rw [IsScalarTower.algebraMap_apply k R (AdicCompletion I R), h,
    IsScalarTower.algebraMap_apply k (henselization R I : Type w)
      (AdicCompletion (I.map (algebraMap R (henselization R I : Type w)))
        (henselization R I : Type w))]
  rfl


/-! ### Completion is compatible with transport along a ring isomorphism -/

section CompletionCongr

/-- The canonical map on completions, evaluated on the image of an element. -/
theorem adicCompletionMap_algebraMap_apply {R S : Type w} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S) (h : I.map f ≤ J) (r : R) :
    adicCompletionMap f I J h (algebraMap R (AdicCompletion I R) r) =
      algebraMap S (AdicCompletion J S) (f r) := by
  simpa using RingHom.congr_fun (adicCompletionMap_comp_algebraMap f I J h) r

/-- Two ring homomorphisms between completions, both determined on the base by `f`, are equal. -/
private theorem ringHom_eq_of_apply_algebraMap_eq {A B : Type*} [CommRing A] [CommRing B]
    (f : A →+* B) (J : Ideal A) (I : Ideal B) (hf : J.map f ≤ I) (hJ : J.FG)
    (g₁ g₂ : AdicCompletion J A →+* AdicCompletion I B)
    (h₁ : ∀ a, g₁ (algebraMap A (AdicCompletion J A) a) = algebraMap B (AdicCompletion I B) (f a))
    (h₂ : ∀ a, g₂ (algebraMap A (AdicCompletion J A) a) = algebraMap B (AdicCompletion I B) (f a)) :
    g₁ = g₂ :=
  (eq_adicCompletionMap_of_apply_algebraMap f J I hf hJ g₁ h₁).trans
    (eq_adicCompletionMap_of_apply_algebraMap f J I hf hJ g₂ h₂).symm

/-- **A ring isomorphism carrying one finitely generated ideal onto another lifts to the adic
completions.** -/
theorem exists_ringEquiv_adicCompletion_of_ringEquiv {R S : Type w} [CommRing R] [CommRing S]
    (d : R ≃+* S) (I : Ideal R) (J : Ideal S) (h : I.map d.toRingHom = J) (hI : I.FG)
    (hJ : J.FG) :
    ∃ D : AdicCompletion I R ≃+* AdicCompletion J S,
      ∀ r, D (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion J S) (d r) := by
  have h' : J.map d.symm.toRingHom = I := by
    rw [← h, Ideal.map_map]
    convert Ideal.map_id I
    ext r
    exact d.symm_apply_apply r
  let f := adicCompletionMap d.toRingHom I J h.le
  let g := adicCompletionMap d.symm.toRingHom J I h'.le
  have hgf : g.comp f = RingHom.id _ := by
    refine ringHom_eq_of_apply_algebraMap_eq (RingHom.id R) I I (by simp) hI _ _ (fun r => ?_)
      fun r => rfl
    simp only [RingHom.coe_comp, Function.comp_apply, f, g, adicCompletionMap_algebraMap_apply]
    exact congrArg _ (d.symm_apply_apply r)
  have hfg : f.comp g = RingHom.id _ := by
    refine ringHom_eq_of_apply_algebraMap_eq (RingHom.id S) J J (by simp) hJ _ _ (fun r => ?_)
      fun r => rfl
    simp only [RingHom.coe_comp, Function.comp_apply, f, g, adicCompletionMap_algebraMap_apply]
    exact congrArg _ (d.apply_symm_apply r)
  exact ⟨RingEquiv.ofRingHom f g hfg hgf, fun r =>
    adicCompletionMap_algebraMap_apply d.toRingHom I J h.le r⟩

variable {R S : Type w} [CommRing R] [Algebra k R] [CommRing S] [Algebra k S]
  [IsNoetherianRing R] [IsNoetherianRing S]
  (d : R ≃+* S) (hd : ∀ a : k, d (algebraMap k R a) = algebraMap k S a)
  (I : Ideal R) (J : Ideal S) (hIJ : I.map d.toRingHom = J)
  (D : AdicCompletion I R ≃+* AdicCompletion J S)
  (hD : ∀ r, D (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion J S) (d r))
  (hDk : ∀ a : k, D (algebraMap k (AdicCompletion I R) a) =
    algebraMap k (AdicCompletion J S) a)

omit [IsNoetherianRing R] [IsNoetherianRing S] in
include hIJ in
/-- Transport along `d` carries the inverse image of `I` to the inverse image of `J`. -/
theorem comap_transport_eq (X : ringDeformationCategory (Λ := Λ) (k := k) R) :
    I.comap X.hom.map.hom =
      J.comap ((ringDeformationTransport (Λ := Λ) d hd).obj X).hom.map.hom := by
  refine Ideal.ext fun z => ?_
  show X.hom.map.hom z ∈ I ↔ d (X.hom.map.hom z) ∈ J
  rw [← hIJ]
  refine ⟨Ideal.mem_map_of_mem _, fun hz => ?_⟩
  have hz' : X.hom.map.hom z ∈ (I.map d.toRingHom).comap d.toRingHom := hz
  rwa [Ideal.comap_map_of_bijective d.toRingHom d.bijective] at hz'

/-- The isomorphism between the completion of a deformation along `I` and the completion of its
transport along `J`: both are the completion of one ring along one ideal. -/
noncomputable def completionCongrEquiv (X : ringDeformationCategory (Λ := Λ) (k := k) R) :
    ((adicCompletionFunctor (Λ := Λ) (k := k) R I).functor.obj X).left.fiber ≃+*
      ((adicCompletionFunctor (Λ := Λ) (k := k) S J).functor.obj
        ((ringDeformationTransport (Λ := Λ) d hd).obj X)).left.fiber :=
  ((adicCompletionFunctor (Λ := Λ) (k := k) R I).fiberEquiv X).trans
    ((adicCompletionEquivOfIdealEq (I.comap X.hom.map.hom)
      (J.comap ((ringDeformationTransport (Λ := Λ) d hd).obj X).hom.map.hom)
        (comap_transport_eq d hd I J hIJ X)).val.trans
      ((adicCompletionFunctor (Λ := Λ) (k := k) S J).fiberEquiv
        ((ringDeformationTransport (Λ := Λ) d hd).obj X)).symm)

/-- The isomorphism of fibres carries the canonical map into the completion of a deformation to
the canonical map into the completion of its transport. -/
theorem completionCongrEquiv_completionUnit (X : ringDeformationCategory (Λ := Λ) (k := k) R)
    (x : X.left.fiber) :
    completionCongrEquiv d hd I J hIJ X
        (completionUnit I (adicCompletionFunctor (Λ := Λ) (k := k) R I) X x) =
      completionUnit J (adicCompletionFunctor (Λ := Λ) (k := k) S J)
        ((ringDeformationTransport (Λ := Λ) d hd).obj X) x := by
  unfold completionCongrEquiv completionUnit
  simp only [RingEquiv.trans_apply, RingHom.coe_comp, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, Function.comp_apply, RingEquiv.apply_symm_apply]
  exact congrArg _ ((adicCompletionEquivOfIdealEq (I.comap X.hom.map.hom)
      (J.comap ((ringDeformationTransport (Λ := Λ) d hd).obj X).hom.map.hom)
        (comap_transport_eq d hd I J hIJ X)).property x)

/-- The isomorphism of fibres is linear over the Artinian base. -/
theorem completionCongrEquiv_algebraMap (X : ringDeformationCategory (Λ := Λ) (k := k) R)
    (a : (((adicCompletionFunctor (Λ := Λ) (k := k) R I).functor.obj X).left.base :
      Type w))
    (b : (((adicCompletionFunctor (Λ := Λ) (k := k) S J).functor.obj
        ((ringDeformationTransport (Λ := Λ) d hd).obj X)).left.base : Type w))
    (hab : (eqToHom ((adicCompletionFunctor (Λ := Λ) (k := k) S J).functor.w_obj
        ((ringDeformationTransport (Λ := Λ) d hd).obj X))).hom b =
      (eqToHom
        ((adicCompletionFunctor (Λ := Λ) (k := k) R I).functor.w_obj X)).hom a) :
    completionCongrEquiv d hd I J hIJ X (algebraMap _ _ a) = algebraMap _ _ b := by
  rw [← completionUnit_algebraMap I _
      (isBaseCompatible_adicCompletionFunctor R I) X a,
    completionCongrEquiv_completionUnit,
    ← completionUnit_algebraMap J _
      (isBaseCompatible_adicCompletionFunctor S J) _ b, hab]
  rfl

include hD in
/-- The isomorphism of fibres is compatible with the reductions to the special fibres. -/
theorem completionCongrEquiv_special (X : ringDeformationCategory (Λ := Λ) (k := k) R)
    (x : ((adicCompletionFunctor (Λ := Λ) (k := k) R I).functor.obj X).left.fiber) :
    ((adicCompletionFunctor (Λ := Λ) (k := k) S J).functor.obj
        ((ringDeformationTransport (Λ := Λ) d hd).obj X)).hom.map.hom
        (completionCongrEquiv d hd I J hIJ X x) =
      D (((adicCompletionFunctor (Λ := Λ) (k := k) R I).functor.obj X).hom.map.hom
        x) := by
  let C := adicCompletionFunctor (Λ := Λ) (k := k) R I
  let C' := adicCompletionFunctor (Λ := Λ) (k := k) S J
  obtain ⟨y, rfl⟩ := (C.fiberEquiv X).symm.surjective x
  have hfg : (I.comap X.hom.map.hom).FG :=
    deformation_ideal_comap_fg I (Ideal.fg_of_isNoetherianRing I) X
  have hmap : (I.comap X.hom.map.hom).map (d.toRingHom.comp X.hom.map.hom) ≤ J := by
    rw [← hIJ]
    calc (I.comap X.hom.map.hom).map (d.toRingHom.comp X.hom.map.hom)
        = ((I.comap X.hom.map.hom).map X.hom.map.hom).map d.toRingHom :=
          (Ideal.map_map _ _).symm
      _ ≤ I.map d.toRingHom := Ideal.map_mono Ideal.map_comap_le
  let α : AdicCompletion (I.comap X.hom.map.hom) X.left.fiber →+* AdicCompletion J S :=
    ((C'.functor.obj ((ringDeformationTransport (Λ := Λ) d hd).obj X)).hom.map.hom.comp
      (completionCongrEquiv d hd I J hIJ X).toRingHom).comp (C.fiberEquiv X).symm.toRingHom
  let β : AdicCompletion (I.comap X.hom.map.hom) X.left.fiber →+* AdicCompletion J S :=
    (D.toRingHom.comp (C.functor.obj X).hom.map.hom).comp (C.fiberEquiv X).symm.toRingHom
  have hαβ : α = β := by
    symm
    refine ringHom_eq_of_apply_algebraMap_eq _ _ _ hmap hfg β α (fun z => ?_) (fun z => ?_)
    · show D ((C.functor.obj X).hom.map.hom (completionUnit I C X z)) = _
      unfold completionUnit
      exact (congrArg D (C.special_comm X z)).trans (hD _)
    · show (C'.functor.obj ((ringDeformationTransport (Λ := Λ) d hd).obj X)).hom.map.hom
        (completionCongrEquiv d hd I J hIJ X (completionUnit I C X z)) = _
      rw [completionCongrEquiv_completionUnit]
      exact C'.special_comm ((ringDeformationTransport (Λ := Λ) d hd).obj X) z
  exact RingHom.congr_fun hαβ y

/-- The isomorphism of fibres is natural in morphisms of deformations. -/
theorem completionCongrEquiv_naturality {X Y : ringDeformationCategory (Λ := Λ) (k := k) R}
    (f : X ⟶ Y)
    (x : ((adicCompletionFunctor (Λ := Λ) (k := k) R I).functor.obj X).left.fiber) :
    completionCongrEquiv d hd I J hIJ Y
        (((adicCompletionFunctor (Λ := Λ) (k := k) R I).functor.map f).left.map.hom
          x) =
      ((adicCompletionFunctor (Λ := Λ) (k := k) S J).functor.map
        ((ringDeformationTransport (Λ := Λ) d hd).map f)).left.map.hom
        (completionCongrEquiv d hd I J hIJ X x) := by
  let C := adicCompletionFunctor (Λ := Λ) (k := k) R I
  let C' := adicCompletionFunctor (Λ := Λ) (k := k) S J
  let TY := (ringDeformationTransport (Λ := Λ) d hd).obj Y
  obtain ⟨y, rfl⟩ := (C.fiberEquiv X).symm.surjective x
  have hfg : (I.comap X.hom.map.hom).FG :=
    deformation_ideal_comap_fg I (Ideal.fg_of_isNoetherianRing I) X
  let N := J.comap TY.hom.map.hom
  let φ : X.left.fiber →+* TY.left.fiber := f.left.map.hom
  have hmap : (I.comap X.hom.map.hom).map φ ≤ N := by
    refine Ideal.map_le_iff_le_comap.mpr fun z hz => ?_
    show d (Y.hom.map.hom (f.left.map.hom z)) ∈ J
    have hw : Y.hom.map.hom (f.left.map.hom z) = X.hom.map.hom z :=
      congrArg (fun t => t.map.hom z) (Over.w f)
    rw [hw, ← hIJ]
    exact Ideal.mem_map_of_mem _ hz
  let α : AdicCompletion (I.comap X.hom.map.hom) X.left.fiber →+* AdicCompletion N TY.left.fiber :=
    (((C'.fiberEquiv TY).toRingHom.comp (completionCongrEquiv d hd I J hIJ Y).toRingHom).comp
      (C.functor.map f).left.map.hom).comp (C.fiberEquiv X).symm.toRingHom
  let β : AdicCompletion (I.comap X.hom.map.hom) X.left.fiber →+* AdicCompletion N TY.left.fiber :=
    (((C'.fiberEquiv TY).toRingHom.comp
      (C'.functor.map ((ringDeformationTransport (Λ := Λ) d hd).map f)).left.map.hom).comp
      (completionCongrEquiv d hd I J hIJ X).toRingHom).comp (C.fiberEquiv X).symm.toRingHom
  have hαβ : α = β := by
    symm
    refine ringHom_eq_of_apply_algebraMap_eq _ _ _ hmap hfg β α (fun z => ?_) (fun z => ?_)
    · have h1 := completionCongrEquiv_completionUnit d hd I J hIJ X z
      have h2 := C'.map_comm ((ringDeformationTransport (Λ := Λ) d hd).map f) z
      exact (congrArg (fun t => C'.fiberEquiv TY ((C'.functor.map
        ((ringDeformationTransport (Λ := Λ) d hd).map f)).left.map.hom t)) h1).trans
          ((congrArg (C'.fiberEquiv TY) h2).trans (RingEquiv.apply_symm_apply _ _))
    · have h1 := C.map_comm f z
      have h2 := completionCongrEquiv_completionUnit d hd I J hIJ Y (f.left.map.hom z)
      exact (congrArg (fun t => C'.fiberEquiv TY (completionCongrEquiv d hd I J hIJ Y t)) h1).trans
          ((congrArg (C'.fiberEquiv TY) h2).trans (RingEquiv.apply_symm_apply _ _))
  exact (C'.fiberEquiv TY).injective (RingHom.congr_fun hαβ y)

include hIJ hD in
/-- **Completion is compatible with transport along an isomorphism of the algebras being
completed.** For an isomorphism `R ≅ S` of Noetherian `k`-algebras carrying `I` onto `J`,
completing along `I` and transporting along the induced isomorphism `R^∧_I ≅ S^∧_J` is isomorphic,
over `𝒞_Λ`, to transporting along `R ≅ S` and then completing along `J`. -/
theorem nonempty_basedIso_adicCompletionFunctor_congr :
    Nonempty (BasedFunctor.comp (adicCompletionFunctor (Λ := Λ) (k := k) R I).functor
        (ringDeformationTransport D hDk) ≅
      BasedFunctor.comp (ringDeformationTransport d hd)
        (adicCompletionFunctor (Λ := Λ) (k := k) S J).functor) :=
  ⟨basedIsoOfFiberEquiv _ _ (completionCongrEquiv d hd I J hIJ)
    (fun X a => completionCongrEquiv_algebraMap d hd I J hIJ X a _
      (eqToHom_hom_trans _ _ a))
    (fun X x => completionCongrEquiv_special d hd I J hIJ D hD X x)
    (fun _ _ f x => completionCongrEquiv_naturality d hd I J hIJ f x)⟩

end CompletionCongr



/-! ### Smoothness and tangent-space isomorphisms across conjugate morphisms -/

section Conj

variable {𝓐 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓐' : BasedCategory.{v₂, u₂} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓑 : BasedCategory.{v₃, u₃} (ArtinianLocalAlgCat.{u, w, w} Λ k)}
  {𝓑' : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, w, w} Λ k)}

/-- If `S ⋙ F ≅ G ⋙ T` with `S`, `G` and `T` smooth, and the source of `S` is a predeformation
category, then `F` is smooth: `S` is essentially surjective. -/
theorem isSmooth_of_conj (hA' : IsPredeformationCategory 𝓐'.p)
    (hA : IsPredeformationCategory 𝓐.p) (S : BasedFunctor 𝓐' 𝓐) (F : BasedFunctor 𝓐 𝓑)
    (G : BasedFunctor 𝓐' 𝓑') (T : BasedFunctor 𝓑' 𝓑)
    (e : BasedFunctor.comp S F ≅ BasedFunctor.comp G T) (hS : IsSmooth S) (hG : IsSmooth G)
    (hT : IsSmooth T) : IsSmooth F := by
  have := essSurj_of_isSmooth hA' hA S hS
  exact isSmooth_of_essSurj_comp hA'.cofibered S F (isSmooth_of_iso e (isSmooth_comp G T hG hT))

/-- If `S ⋙ F ≅ G ⋙ T` with `S`, `G` and `T` bijective on tangent spaces, then so is `F`. -/
theorem bijective_differential_of_conj (hA' : IsCofiberedInGroupoids 𝓐'.p)
    (hA : IsCofiberedInGroupoids 𝓐.p) (hB : IsCofiberedInGroupoids 𝓑.p)
    (hB' : IsCofiberedInGroupoids 𝓑'.p) (S : BasedFunctor 𝓐' 𝓐) (F : BasedFunctor 𝓐 𝓑)
    (G : BasedFunctor 𝓐' 𝓑') (T : BasedFunctor 𝓑' 𝓑)
    (e : BasedFunctor.comp S F ≅ BasedFunctor.comp G T)
    (hS : Function.Bijective (differential hA' hA S))
    (hG : Function.Bijective (differential hA' hB' G))
    (hT : Function.Bijective (differential hB' hB T)) :
    Function.Bijective (differential hA hB F) := by
  let A := augmentedDualNumbers (Λ := Λ) (k := k)
  have hS' : Function.Bijective (mapIsomorphismClasses hA' hA S A) := hS
  have hG' : Function.Bijective (mapIsomorphismClasses hA' hB' G A) := hG
  have hT' : Function.Bijective (mapIsomorphismClasses hB' hB T A) := hT
  have key : (mapIsomorphismClasses hA hB F A) ∘ (mapIsomorphismClasses hA' hA S A) =
      (mapIsomorphismClasses hB' hB T A) ∘ (mapIsomorphismClasses hA' hB' G A) :=
    (mapIsomorphismClasses_comp hA' hA hB S F A).symm.trans
      ((mapIsomorphismClasses_eq_of_iso hA' hB _ _ e A).trans
        (mapIsomorphismClasses_comp hA' hB' hB G T A))
  have hFS : Function.Bijective
      ((mapIsomorphismClasses hA hB F A) ∘ (mapIsomorphismClasses hA' hA S A)) := by
    rw [key]
    exact hT'.comp hG'
  exact (hS'.of_comp_iff _).mp hFS

end Conj

variable {ι : Type uι} (O : ι → Type w) [∀ i, CommRing (O i)] [∀ i, Algebra k (O i)]
  [∀ i, IsLocalRing (O i)]

/-- The second map of the chain at a family of local rings: henselize each along its maximal
ideal. -/
noncomputable def henselizationFunctorsAt :
    BasedFunctor (piBasedCategory fun i => ringDeformationBasedCategory Λ k (O i))
      (piBasedCategory fun i => ringDeformationBasedCategory Λ k
        (henselization (O i) (IsLocalRing.maximalIdeal (O i)) : Type w)) :=
  piMap fun i => (henselizationFunctor (Λ := Λ) (k := k) (IsLocalRing.maximalIdeal (O i))).functor

/-- The third map of the chain at a family of Noetherian local rings: complete each henselization
along the extension of the maximal ideal, and read the result as the completion of the local ring
itself. -/
noncomputable def completedLocalRingFunctorsAt [∀ i, IsNoetherianRing (O i)] :
    BasedFunctor
      (piBasedCategory fun i => ringDeformationBasedCategory Λ k
        (henselization (O i) (IsLocalRing.maximalIdeal (O i)) : Type w))
      (piBasedCategory fun i => ringDeformationBasedCategory Λ k
        (AdicCompletion (IsLocalRing.maximalIdeal (O i)) (O i))) :=
  piMap fun i => by
    letI := isNoetherianRing_henselization_maximalIdeal (O i)
    exact BasedFunctor.comp
      (adicCompletionFunctor (Λ := Λ) (k := k)
        (henselization (O i) (IsLocalRing.maximalIdeal (O i)) : Type w)
        ((IsLocalRing.maximalIdeal (O i)).map
          (algebraMap (O i)
            (henselization (O i) (IsLocalRing.maximalIdeal (O i)) : Type w)))).functor
      (ringDeformationTransport
        (adicCompletionHenselizationEquiv (O i) (IsLocalRing.maximalIdeal (O i))).symm
        (algebraMap_adicCompletionHenselizationEquiv_symm (O i) (IsLocalRing.maximalIdeal (O i))))

/-- The henselization functor of a local ring isomorphic to some `P_{𝔪 i}` is smooth and
bijective on tangent spaces. -/
private theorem henselizationFunctor_conclusions_of_ringEquiv {P : Type w} [CommRing P]
    [Algebra k P] [Algebra.FiniteType k P] {ι : Type w} [Finite ι] (m : ι → PrimeSpectrum P)
    (hmax : ∀ i, (m i).asIdeal.IsMaximal) (hinj : Function.Injective m)
    (hsm : ∀ q : PrimeSpectrum P, ¬ Algebra.IsSmoothAt k q.asIdeal → ∃ i, m i = q) (i : ι)
    (Q : Type w) [CommRing Q] [Algebra k Q] [IsLocalRing Q] (e : localRingAt (m i) ≃+* Q)
    (he : ∀ a : k, e (algebraMap k (localRingAt (m i)) a) = algebraMap k Q a) :
    IsSmooth (henselizationFunctor (Λ := Λ) (k := k) (IsLocalRing.maximalIdeal Q)).functor ∧
      Function.Bijective (differential
        (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k) (P := Q))
        (isCofiberedInGroupoids_ringDeformationProjection (Λ := Λ) (k := k)
          (P := (henselization Q (IsLocalRing.maximalIdeal Q) : Type w)))
        (henselizationFunctor (Λ := Λ) (k := k) (IsLocalRing.maximalIdeal Q)).functor) := by
  let : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  have hmaxe := IsLocalRing.map_maximalIdeal_of_surjective e.toRingHom e.surjective
  obtain ⟨d, hdchar⟩ := exists_ringEquiv_henselization_of_ringEquiv e _ _ hmaxe
  have hd : ∀ a : k, d (algebraMap k _ a) = algebraMap k _ a :=
    algebraMap_comm_of_henselizationCongrEquiv (k := k) e he _ _ d hdchar
  obtain ⟨cmp⟩ := nonempty_basedIso_henselizationFunctor_congr (Λ := Λ) (k := k) e he
    _ _ d hmaxe hd hdchar
  have h0 := henselizationFunctor_localRingAt_conclusions (Λ := Λ) m hmax hinj hsm i
  exact ⟨isSmooth_henselizationFunctor_of_ringEquiv _ _ _ _ d hd cmp h0.1,
    bijective_differential_henselizationFunctor_of_ringEquiv _ _ _ _ d hd cmp h0.2⟩

/-- At one point, completing the henselization of a local ring `Q` isomorphic to the henselized
local ring at `q` is conjugate, by transports, to completing the henselized local ring at `q`. -/
private theorem exists_basedIso_adicCompletion_henselization_conj {P : Type w} [CommRing P]
    [Algebra k P] (q : PrimeSpectrum P) [IsNoetherianRing (henselizedLocalRingAt q)]
    (Q : Type w) [CommRing Q] [Algebra k Q] [IsLocalRing Q]
    [IsNoetherianRing (henselization Q (IsLocalRing.maximalIdeal Q) : Type w)]
    (d : henselizedLocalRingAt q ≃+* (henselization Q (IsLocalRing.maximalIdeal Q) : Type w))
    (hd : ∀ a : k, d (algebraMap k _ a) = algebraMap k _ a)
    (hJ : (henselizedMaximalIdealAt q).map d.toRingHom =
      (IsLocalRing.maximalIdeal Q).map
        (algebraMap Q (henselization Q (IsLocalRing.maximalIdeal Q) : Type w))) :
    ∃ (c : AdicCompletion (IsLocalRing.maximalIdeal (localRingAt q)) (localRingAt q) ≃+*
        AdicCompletion (IsLocalRing.maximalIdeal Q) Q)
      (hc : ∀ a : k, c (algebraMap k _ a) = algebraMap k _ a),
      Nonempty (BasedFunctor.comp (ringDeformationTransport (Λ := Λ) d hd)
          (BasedFunctor.comp (adicCompletionFunctor (Λ := Λ) (k := k)
            (henselization Q (IsLocalRing.maximalIdeal Q) : Type w)
            ((IsLocalRing.maximalIdeal Q).map (algebraMap Q
              (henselization Q (IsLocalRing.maximalIdeal Q) : Type w)))).functor
            (ringDeformationTransport
              (adicCompletionHenselizationEquiv Q (IsLocalRing.maximalIdeal Q)).symm
              (algebraMap_adicCompletionHenselizationEquiv_symm Q
                (IsLocalRing.maximalIdeal Q)))) ≅
        BasedFunctor.comp
          (BasedFunctor.comp (adicCompletionFunctor (Λ := Λ) (k := k)
            (henselizedLocalRingAt q) (henselizedMaximalIdealAt q)).functor
            (ringDeformationTransport (adicCompletionHenselizedLocalRingEquiv q).symm
              (algebraMap_adicCompletionHenselizedLocalRingEquiv_symm (k := k) q)))
          (ringDeformationTransport (Λ := Λ) c hc)) := by
  obtain ⟨D, hD⟩ := exists_ringEquiv_adicCompletion_of_ringEquiv d _ _ hJ
    (Ideal.fg_of_isNoetherianRing _) (Ideal.fg_of_isNoetherianRing _)
  have hDk : ∀ a : k, D (algebraMap k _ a) = algebraMap k _ a := fun a => by
    rw [IsScalarTower.algebraMap_apply k (henselizedLocalRingAt q), hD, hd,
      ← IsScalarTower.algebraMap_apply]
  have htO : ∀ a : k, (adicCompletionHenselizationEquiv Q (IsLocalRing.maximalIdeal Q)).symm
      (algebraMap k _ a) = algebraMap k _ a :=
    algebraMap_adicCompletionHenselizationEquiv_symm Q (IsLocalRing.maximalIdeal Q)
  let c := (adicCompletionHenselizedLocalRingEquiv q).trans
    (D.trans (adicCompletionHenselizationEquiv Q (IsLocalRing.maximalIdeal Q)).symm)
  have hc : ∀ a : k, c (algebraMap k _ a) = algebraMap k _ a := fun a => by
    simp only [c, RingEquiv.trans_apply]
    rw [algebraMap_adicCompletionHenselizedLocalRingEquiv (k := k), hDk, htO]
  let c₀ := D.trans (adicCompletionHenselizationEquiv Q (IsLocalRing.maximalIdeal Q)).symm
  have hc₀ : ∀ a : k, c₀ (algebraMap k _ a) = algebraMap k _ a := fun a => by
    simp only [c₀, RingEquiv.trans_apply]
    rw [hDk, htO]
  refine ⟨c, hc, ⟨?_⟩⟩
  let CL := (adicCompletionFunctor (Λ := Λ) (k := k)
    (henselizedLocalRingAt q) (henselizedMaximalIdealAt q)).functor
  let CO := (adicCompletionFunctor (Λ := Λ) (k := k)
    (henselization Q (IsLocalRing.maximalIdeal Q) : Type w)
    ((IsLocalRing.maximalIdeal Q).map (algebraMap Q
      (henselization Q (IsLocalRing.maximalIdeal Q) : Type w)))).functor
  let trD := ringDeformationTransport (Λ := Λ) D hDk
  let trO := ringDeformationTransport (Λ := Λ)
    (adicCompletionHenselizationEquiv Q (IsLocalRing.maximalIdeal Q)).symm htO
  let trd := ringDeformationTransport (Λ := Λ) d hd
  let trL := ringDeformationTransport (Λ := Λ) (adicCompletionHenselizedLocalRingEquiv q).symm
    (algebraMap_adicCompletionHenselizedLocalRingEquiv_symm (k := k) q)
  let trc := ringDeformationTransport (Λ := Λ) c hc
  let trc₀ := ringDeformationTransport (Λ := Λ) c₀ hc₀
  let cmp : BasedFunctor.comp CL trD ≅ BasedFunctor.comp trd CO := Classical.choice
    (nonempty_basedIso_adicCompletionFunctor_congr (Λ := Λ) d hd _ _ hJ D hD hDk)
  have i1 : BasedFunctor.comp trd (BasedFunctor.comp CO trO) ≅
      BasedFunctor.comp (BasedFunctor.comp CL trD) trO := basedIsoWhiskerRight cmp.symm trO
  have i2 : BasedFunctor.comp (BasedFunctor.comp CL trD) trO ≅ BasedFunctor.comp CL trc₀ :=
    basedIsoWhiskerLeft CL (ringDeformationTransportCompIso D hDk
      (adicCompletionHenselizationEquiv Q (IsLocalRing.maximalIdeal Q)).symm htO
      c₀ hc₀ (fun _ => rfl))
  have i3 : BasedFunctor.comp (BasedFunctor.comp CL trL) trc ≅ BasedFunctor.comp CL trc₀ :=
    basedIsoWhiskerLeft CL (ringDeformationTransportCompIso
      (adicCompletionHenselizedLocalRingEquiv q).symm
      (algebraMap_adicCompletionHenselizedLocalRingEquiv_symm (k := k) q) c hc
      c₀ hc₀ (fun r => by simp [c, c₀]))
  exact i1 ≪≫ i2 ≪≫ i3.symm

/-- **The second and third maps of the chain of Stacks 0DZF, read at local rings isomorphic to
the `P_{𝔪 i}`.** Let `P` be a finite type `k`-algebra smooth away from the distinct maximal
ideals `m i`, and let each local ring `O i` be isomorphic over `k` to the localization of `P` at
`m i`. Then henselizing the `O i` along their maximal ideals, and completing the henselizations,
are smooth maps of products of deformation categories which are bijective on tangent spaces. -/
theorem localRingChainAt_conclusions {P : Type w} [CommRing P] [Algebra k P]
    [Algebra.FiniteType k P] {ι : Type w} [Finite ι] (m : ι → PrimeSpectrum P)
    (hmax : ∀ i, (m i).asIdeal.IsMaximal) (hinj : Function.Injective m)
    (hsm : ∀ q : PrimeSpectrum P, ¬ Algebra.IsSmoothAt k q.asIdeal → ∃ i, m i = q)
    (O : ι → Type w) [∀ i, CommRing (O i)] [∀ i, Algebra k (O i)] [∀ i, IsLocalRing (O i)]
    [∀ i, IsNoetherianRing (O i)]
    (e : ∀ i, localRingAt (m i) ≃+* O i)
    (he : ∀ i (a : k), e i (algebraMap k (localRingAt (m i)) a) = algebraMap k (O i) a) :
    IsSmooth (henselizationFunctorsAt (Λ := Λ) (k := k) O) ∧
      Function.Bijective (differential
        (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k) O)
        (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
          fun i => (henselization (O i) (IsLocalRing.maximalIdeal (O i)) : Type w))
        (henselizationFunctorsAt (Λ := Λ) (k := k) O)) ∧
      IsSmooth (completedLocalRingFunctorsAt (Λ := Λ) (k := k) O) ∧
      Function.Bijective (differential
        (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
          fun i => (henselization (O i) (IsLocalRing.maximalIdeal (O i)) : Type w))
        (isCofiberedInGroupoids_pi_ringDeformation (Λ := Λ) (k := k)
          fun i => AdicCompletion (IsLocalRing.maximalIdeal (O i)) (O i))
        (completedLocalRingFunctorsAt (Λ := Λ) (k := k) O)) := by
  classical
  let : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  have hH := fun i =>
    henselizationFunctor_conclusions_of_ringEquiv (Λ := Λ) m hmax hinj hsm i (O i) (e i) (he i)
  refine ⟨piMap_isSmooth_of_components _ fun i => (hH i).1,
    bijective_differential_piMap_of_components _ _ _ fun i => (hH i).2, ?_⟩
  have hmaxe : ∀ i, (IsLocalRing.maximalIdeal (localRingAt (m i))).map (e i).toRingHom =
      IsLocalRing.maximalIdeal (O i) := fun i =>
    IsLocalRing.map_maximalIdeal_of_surjective (e i).toRingHom (e i).surjective
  choose d hdchar using fun i => exists_ringEquiv_henselization_of_ringEquiv (e i) _ _ (hmaxe i)
  have hd : ∀ i (a : k), d i (algebraMap k _ a) = algebraMap k _ a := fun i =>
    algebraMap_comm_of_henselizationCongrEquiv (k := k) (e i) (he i) _ _ (d i) (hdchar i)
  have hNL : ∀ i, IsNoetherianRing (henselizedLocalRingAt (m i)) := fun i =>
    isNoetherianRing_henselizedLocalRingAt (k := k) (m i)
  have hNO : ∀ i, IsNoetherianRing
      (henselization (O i) (IsLocalRing.maximalIdeal (O i)) : Type w) := fun i =>
    isNoetherianRing_henselization_maximalIdeal (O i)
  have hJ : ∀ i, (henselizedMaximalIdealAt (m i)).map (d i).toRingHom =
      (IsLocalRing.maximalIdeal (O i)).map (algebraMap (O i)
        (henselization (O i) (IsLocalRing.maximalIdeal (O i)) : Type w)) := fun i => by
    have hcomp : (d i).toRingHom.comp (algebraMap (localRingAt (m i)) (henselizedLocalRingAt (m i)))
        = (algebraMap (O i) (henselization (O i) (IsLocalRing.maximalIdeal (O i)) : Type w)).comp
          (e i).toRingHom := RingHom.ext fun r => hdchar i r
    rw [henselizedMaximalIdealAt, Ideal.map_map, hcomp, ← Ideal.map_map, hmaxe i]
  choose c hc hiso using fun i =>
    exists_basedIso_adicCompletion_henselization_conj (Λ := Λ) (m i) (O i) (d i) (hd i) (hJ i)
  have hdefL := isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k)
    fun i => henselizedLocalRingAt (m i)
  have hdefO := isDeformationCategory_pi_ringDeformation (Λ := Λ) (k := k)
    fun i => (henselization (O i) (IsLocalRing.maximalIdeal (O i)) : Type w)
  have e3 : BasedFunctor.comp
        (piMap fun i => ringDeformationTransport (Λ := Λ) (d i) (hd i))
        (completedLocalRingFunctorsAt (Λ := Λ) (k := k) O) ≅
      BasedFunctor.comp (completedLocalRingFunctors (Λ := Λ) (k := k) m)
        (piMap fun i => ringDeformationTransport (Λ := Λ) (c i) (hc i)) :=
    piMapIsoOfComponents _ _ fun i => (hiso i).some
  refine ⟨isSmooth_of_conj hdefL.predeformation hdefO.predeformation _ _ _ _ e3
    (piMap_isSmooth_of_components _ fun i => isSmooth_ringDeformationTransport _ _)
    (isSmooth_completedLocalRingFunctors m hmax hinj hsm)
    (piMap_isSmooth_of_components _ fun i => isSmooth_ringDeformationTransport _ _), ?_⟩
  exact bijective_differential_of_conj _ _ _ _ _ _ _ _ e3
    (bijective_differential_piMap_of_components _ _ _ fun i =>
      bijective_differential_ringDeformationTransport _ _)
    (bijective_differential_completedLocalRingFunctors m hmax hinj hsm)
    (bijective_differential_piMap_of_components _ _ _ fun i =>
      bijective_differential_ringDeformationTransport _ _)

end Deformation.Examples
