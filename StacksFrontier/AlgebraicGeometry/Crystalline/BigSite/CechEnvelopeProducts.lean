module

public import Mathlib.RingTheory.PiTensorProduct
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.BinaryProductAffine
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeAcyclicity
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeObjects
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope
public import StacksFrontier.AlgebraicGeometry.Crystalline.EnvelopeRetract
public import StacksFrontier.AlgebraicGeometry.Schemes.ZariskiAndSeparation.IntersectionGeneration

/-!
# The products of the smooth-lift objects are divided power envelopes

Fix a global crystalline situation `(p, (S, I, γ), X)` with `S` affine, `A = Γ(S, ⊤)`, `p`
nilpotent in `A` and `X` separated, affine opens `U_0, …, U_n` of `X`, and smooth lifts
`L_k = (B_k, Γ(U_k) ≅ B_k/IB_k)` of them
(`Crystalline.GlobalCrystallineSituation.CechEnvelope.SmoothLift`), with objects
`D_k = (U_k, Y_k = Spec B_k, γ_k)` of `CRIS(X/S)`.  The intersection `U_s = U_0 ∩ ⋯ ∩ U_n` is
affine and `U_s ⟶ Y_0 ×_S ⋯ ×_S Y_n` is a closed immersion: on global sections,
`B_0 ⊗_A ⋯ ⊗_A B_n → Γ(U_s)` is surjective (`CechEnvelope.surjective_tensorMap`), being generated
by the images of the `Γ(U_k)` ([Stacks, Tag 01KP]).  Let `K` be its kernel and `D` the divided
power envelope of `K` relative to `(A, I, γ)` ([Stacks, Tag 07H9],
`Crystalline.dividedPowerEnvelope`), so that `D/J̄ ≅ Γ(U_s)` ([Stacks, Tag 07HA]).

This file proves that the object `D_s = (U_s, Spec D, δ)` of `CRIS(X/S)`
(`CechEnvelope.envelopeObject`) is a **product** of `D_0, …, D_n` in `CRIS(X/S)`
(`CechEnvelope.isLimitFan`): the projections are `B_k → B_0 ⊗ ⋯ ⊗ B_n → D`
(`CechEnvelope.proj`); and for an arbitrary object `T` with maps `f_k : T ⟶ D_k` the maps
`B_k → Γ(T, ⊤)` combine to `Φ : B_0 ⊗ ⋯ ⊗ B_n → Γ(T, ⊤)`, which carries `K` into the divided power
ideal of `T` because the latter is the kernel of restriction to the thickened scheme of `T`
(`Crystalline.SchemeThickening.sectionsIdeal_eq_ker_appTop`) and `Φ` read there factors through
`Γ(U_s)`.  The universal property of the envelope extends `Φ` to a divided power morphism
`D → Γ(T, ⊤)` over `A`, and that is the lift (`CechEnvelope.lift`); its uniqueness is the
uniqueness in the envelope's universal property (`Crystalline.envelopeHom_ext`) together with
the extensionality of maps out of a tensor product.

In particular the categorical product `∏ D_k` is `D_s` (`CechEnvelope.piIsoEnvelopeObject`): it
lies in `Cris(X/S)`, its ambient scheme is affine, and its ring of global sections is the divided
power envelope `D`; and a quasi-coherent module on `CRIS(X/S)` has no higher cohomology over it
(`CechEnvelope.isZero_bigRightDerivedSections_pi`).

## Main definitions

* `CechEnvelope.tensorRing`, `CechEnvelope.tensorMap`, `CechEnvelope.tensorIdeal` —
  `B_0 ⊗_A ⋯ ⊗_A B_n`, its map onto `Γ(U_0 ∩ ⋯ ∩ U_n)` and the kernel `K`.
* `CechEnvelope.envelope` — **the divided power envelope `D` of `K`**, and
  `CechEnvelope.envelopeEquiv` the identification `D/J̄ ≅ Γ(U_0 ∩ ⋯ ∩ U_n)`.
* `CechEnvelope.envelopeThickening` — `D` as an object of `CRIS(Γ(U_0 ∩ ⋯ ∩ U_n)/A)`.
* `CechEnvelope.envelopeObject` — **the object `(U_0 ∩ ⋯ ∩ U_n, Spec D, δ)` of `CRIS(X/S)`.**
* `CechEnvelope.proj` — the projections `D_s ⟶ D_k`; `CechEnvelope.lift` — the lift.

## Main results

* **`CechEnvelope.isLimitFan`** — `D_s` with the projections is a product of `D_0, …, D_n`.
* `CechEnvelope.hasProduct_object`, `CechEnvelope.piIsoEnvelopeObject` — the product exists and
  is `D_s`.
* `CechEnvelope.isZero_bigRightDerivedSections_pi` — the higher cohomology of a quasi-coherent
  module over `∏ D_k` vanishes.

## References

* [Stacks Project, Tag 07H9](https://stacks.math.columbia.edu/tag/07H9)
* [Stacks Project, Tag 07HA](https://stacks.math.columbia.edu/tag/07HA)
* [Stacks Project, Tag 01KP](https://stacks.math.columbia.edu/tag/01KP)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

open SmallSite

/-! ### Generalities -/

/-- A morphism of `CRIS(X/S)` into an object with affine ambient scheme is determined by its map
on global sections of the ambient schemes. -/
theorem hom_ext_of_targetHom_appTop {S : GlobalCrystallineSituation.{u}} {T B : Thickening S}
    [IsAffine B.thickening.target.scheme] {g g' : T ⟶ B}
    (h : g.targetHom.hom.appTop = g'.targetHom.hom.appTop) : g = g' := by
  have hT : g.targetHom = g'.targetHom := DividedPowerScheme.Hom.ext (ext_of_isAffine h)
  have hS : g.sourceHom = g'.sourceHom := by
    refine (cancel_mono B.thickening.immersion).mp ?_
    rw [← g.immersion_naturality, ← g'.immersion_naturality, hT]
  exact Thickening.Hom.ext hS hT

section PiLift

variable {R : Type*} [CommRing R] {K : Type} [Fintype K] [DecidableEq K] {B : K → Type*}
  [∀ k, CommRing (B k)] [∀ k, Algebra R (B k)] {C : Type*} [CommRing C] [Algebra R C]

/-- The map of `A`-algebras out of a finite tensor product of commutative `A`-algebras given by a
family of maps of the factors: `b_0 ⊗ ⋯ ⊗ b_n ↦ ∏ g_k(b_k)`. -/
def piLift (g : ∀ k, B k →ₐ[R] C) : (⨂[R] k, B k) →ₐ[R] C :=
  PiTensorProduct.liftAlgHom
    ((MultilinearMap.mkPiAlgebra R K C).compLinearMap fun k ↦ (g k).toLinearMap)
    (by simp [MultilinearMap.mkPiAlgebra_apply])
    (fun x y ↦ by simp [MultilinearMap.mkPiAlgebra_apply, Finset.prod_mul_distrib])

/-- `piLift` restricts to the `k`-th given map on the `k`-th factor. -/
theorem piLift_single (g : ∀ k, B k →ₐ[R] C) (k : K) (b : B k) :
    piLift g (PiTensorProduct.singleAlgHom k b) = g k b := by
  simp only [piLift, PiTensorProduct.singleAlgHom_apply, PiTensorProduct.liftAlgHom_apply,
    PiTensorProduct.lift.tprod, MultilinearMap.compLinearMap_apply,
    MultilinearMap.mkPiAlgebra_apply, AlgHom.toLinearMap_apply]
  rw [Fintype.prod_eq_single k fun j hj ↦ by simp [Pi.mulSingle_eq_of_ne hj]]
  simp

end PiLift

section Envelope

variable {A : DividedPowerRing.{u}} {B : Type u} [CommRing B] {f : A →+* B} {J : Ideal B}
  {hJ : A.ideal.map f ≤ J} (D : DividedPowerEnvelope A f J hJ) (C : DividedPowerRing.{u})
  (a : DividedPowers.DPMorphism A.dividedPowers C.dividedPowers) (φ : B →+* C)
  (hφ : J.map φ ≤ C.ideal) (hφa : φ.comp f = a.toRingHom)

/-- The divided power morphism out of an envelope over `A` attached to a morphism of pairs from
`(B, J)` over `A`, by the universal property of the envelope. -/
def envLift : DividedPowers.DPMorphism D.object.dividedPowers C.dividedPowers :=
  ((D.homEquiv C a).symm ⟨IdealPair.Hom.ofRingHom φ hφ,
    IdealPair.Hom.ext_toRingHom _ _ hφa⟩).1

/-- `envLift` is a morphism over `A`. -/
theorem envLift_comp_structureMap : (envLift D C a φ hφ hφa).comp D.structureMap = a :=
  ((D.homEquiv C a).symm _).2

/-- `envLift` restricts along `B → D` to the given ring map. -/
theorem envLift_comp_algebraMap :
    (envLift D C a φ hφ hφa).toRingHom.comp D.algebraMap.toRingHom = φ := by
  have h := D.homEquiv_apply C a ((D.homEquiv C a).symm ⟨IdealPair.Hom.ofRingHom φ hφ,
    IdealPair.Hom.ext_toRingHom _ _ hφa⟩)
  have h2 := congrArg (fun x ↦ (x.1 : IdealPair.Hom J C.ideal).toRingHom)
    ((D.homEquiv C a).apply_symm_apply ⟨IdealPair.Hom.ofRingHom φ hφ,
      IdealPair.Hom.ext_toRingHom _ _ hφa⟩)
  exact (congrArg IdealPair.Hom.toRingHom h).symm.trans h2

end Envelope

/-! ### The tensor product of the smooth lifts and its map to the intersection -/

section Setup

variable {S : GlobalCrystallineSituation.{u}} {n : ℕ} (U : Fin (n + 1) → S.X.Opens)

/-- The intersection `U_0 ∩ ⋯ ∩ U_n`. -/
abbrev inter : S.X.Opens := ⨅ k, U k

/-- The intersection lies in each member. -/
theorem inter_le (k : Fin (n + 1)) : inter U ≤ U k := iInf_le U k

/-- Restriction `Γ(U_k) → Γ(U_0 ∩ ⋯ ∩ U_n)`. -/
abbrev restr (k : Fin (n + 1)) : Γ((U k).toScheme, ⊤) →+* Γ((inter U).toScheme, ⊤) :=
  (S.X.homOfLE (inter_le U k)).appTop.hom

/-- The structure maps to the base of `U_k` and of the intersection are compatible. -/
theorem homOfLE_sourceToBase (k : Fin (n + 1)) :
    S.X.homOfLE (inter_le U k) ≫ sourceToBase (overSituation S (U k).ι) =
      sourceToBase (overSituation S (inter U).ι) := by
  simp only [sourceToBase, ← Category.assoc, Scheme.homOfLE_ι]

/-- Restriction to the intersection is compatible with the maps from `A`. -/
theorem restr_sourceToBase (k : Fin (n + 1)) (a : Γ(S.S.scheme, ⊤)) :
    restr U k ((sourceToBase (overSituation S (U k).ι)).appTop.hom a) =
      (sourceToBase (overSituation S (inter U).ι)).appTop.hom a := by
  rw [← homOfLE_sourceToBase U k, Scheme.Hom.comp_appTop]
  rfl

/-- Two restriction maps of the structure presheaf compose to the restriction map. -/
theorem presheaf_map_map (X : Scheme.{u}) {a b c : X.Opens} (f : b ⟶ a) (g : c ⟶ b)
    (h : c ⟶ a) (x : Γ(X, a)) :
    (X.presheaf.map g.op).hom ((X.presheaf.map f.op).hom x) = (X.presheaf.map h.op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

variable [hU : ∀ k, IsAffine (U k)]

/-- The intersection of finitely many affine opens of a separated scheme is affine. -/
instance isAffine_inter [S.X.IsSeparated] : IsAffine (inter U).toScheme :=
  IsAffineOpen.iInf fun k ↦ hU k

/-- **`Γ(U_0 ∩ ⋯ ∩ U_n)` is generated as a ring by the images of the `Γ(U_k)`** for a separated
`X`, [Stacks, Tag 01KP], read on the global sections of the open subschemes. -/
theorem closure_range_restr [S.X.IsSeparated] :
    Subring.closure (⋃ k, Set.range (restr U k)) = ⊤ := by
  let e : Γ((inter U).toScheme, ⊤) ≃+* Γ(S.X, inter U) :=
    (inter U).topIso.commRingCatIsoToRingEquiv
  have key : ∀ k c, e (restr U k c) =
      sectionsRestrict (inter_le U k) ((U k).topIso.hom.hom c) := fun k c ↦ by
    have hr : restr U k c = (S.X.presheaf.map
        (homOfLE (S.X.ι_image_homOfLE_le_ι_image (inter_le U k) ⊤)).op).hom c := by
      rw [restr, Scheme.homOfLE_appTop]
      rfl
    rw [hr]
    have hle : inter U ≤ (U k).ι ''ᵁ ⊤ := (inter_le U k).trans (Scheme.Opens.ι_image_top (U k)).ge
    exact (presheaf_map_map S.X _ _ (homOfLE hle) c).trans
      (presheaf_map_map S.X _ _ (homOfLE hle) c).symm
  have himage : e.toRingHom '' (⋃ k, Set.range (restr U k)) =
      ⋃ k, Set.range (sectionsRestrict (inter_le U k)) := by
    ext y
    simp only [Set.mem_image, Set.mem_iUnion, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨k, c, rfl⟩, rfl⟩
      exact ⟨k, _, (key k c).symm⟩
    · rintro ⟨k, c, rfl⟩
      refine ⟨_, ⟨k, (U k).topIso.inv.hom c, rfl⟩, ?_⟩
      change e (restr U k _) = _
      rw [key]
      congr 1
      exact ConcreteCategory.congr_hom (U k).topIso.inv_hom_id c
  refine eq_top_iff.mpr fun y _ ↦ ?_
  obtain ⟨x, hx, hxy⟩ : e y ∈ (Subring.closure (⋃ k, Set.range (restr U k))).map e.toRingHom := by
    rw [RingHom.map_closure, himage, closure_iUnion_range_sectionsRestrict_eq_top n U
      (fun k ↦ hU k) (inter U) rfl (inter_le U)]
    trivial
  rwa [show x = y from e.injective hxy] at hx

end Setup

section Tensor

variable {S : GlobalCrystallineSituation.{u}} {n : ℕ} {U : Fin (n + 1) → S.X.Opens}
  (L : ∀ k, SmoothLift S (U k).ι)

/-- The `A`-algebra structure of `Γ(U_0 ∩ ⋯ ∩ U_n)`. -/
abbrev interAlgebra (U : Fin (n + 1) → S.X.Opens) :
    Algebra (baseSectionsRing S) Γ((inter U).toScheme, ⊤) :=
  (sourceToBase (overSituation S (inter U).ι)).appTop.hom.toAlgebra

attribute [local instance] interAlgebra

/-- The tensor product `B_0 ⊗_A ⋯ ⊗_A B_n` of the smooth lifts. -/
abbrev tensorRing : Type u := ⨂[baseSectionsRing S] k, (L k).ring

/-- The map `B_k → B_k/IB_k ≅ Γ(U_k) → Γ(U_0 ∩ ⋯ ∩ U_n)`. -/
def component (k : Fin (n + 1)) :
    (L k).ring →ₐ[baseSectionsRing S] Γ((inter U).toScheme, ⊤) where
  toRingHom := (restr U k).comp ((L k).equiv.symm.toRingHom.comp (Ideal.Quotient.mk _))
  commutes' a := by
    change restr U k ((L k).equiv.symm (Ideal.Quotient.mk _ (algebraMap _ _ a))) =
      (sourceToBase (overSituation S (inter U).ι)).appTop.hom a
    rw [← (L k).equiv_sourceToBase a, RingEquiv.symm_apply_apply]
    exact restr_sourceToBase U k a

/-- The value of `component`. -/
theorem component_apply (k : Fin (n + 1)) (b : (L k).ring) :
    component L k b = restr U k ((L k).equiv.symm (Ideal.Quotient.mk _ b)) := rfl

/-- **The map `B_0 ⊗_A ⋯ ⊗_A B_n → Γ(U_0 ∩ ⋯ ∩ U_n)`.** -/
def tensorMap : tensorRing L →ₐ[baseSectionsRing S] Γ((inter U).toScheme, ⊤) :=
  piLift (component L)

/-- `tensorMap` on the `k`-th factor is `component k`. -/
theorem tensorMap_single (k : Fin (n + 1)) (b : (L k).ring) :
    tensorMap L (PiTensorProduct.singleAlgHom k b) = component L k b :=
  piLift_single _ _ _

/-- **`B_0 ⊗_A ⋯ ⊗_A B_n → Γ(U_0 ∩ ⋯ ∩ U_n)` is surjective**, `U_0 ∩ ⋯ ∩ U_n ⟶ Y_0 ×_S ⋯ ×_S Y_n`
being a closed immersion: the target is generated by the images of the `Γ(U_k)`, each of which is
in the image. -/
theorem surjective_tensorMap [∀ k, IsAffine (U k)] [S.X.IsSeparated] :
    Function.Surjective (tensorMap L) := by
  have h : Subring.closure (⋃ k, Set.range (restr U k)) ≤
      (tensorMap L : tensorRing L →+* Γ((inter U).toScheme, ⊤)).range := by
    refine Subring.closure_le.mpr fun y hy ↦ ?_
    obtain ⟨k, c, rfl⟩ := Set.mem_iUnion.mp hy
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((L k).equiv c)
    refine ⟨PiTensorProduct.singleAlgHom k b, ?_⟩
    change tensorMap L (PiTensorProduct.singleAlgHom k b) = _
    rw [tensorMap_single, component_apply, hb, RingEquiv.symm_apply_apply]
  rw [closure_range_restr] at h
  exact fun y ↦ h trivial

/-- The ideal `K = ker(B_0 ⊗_A ⋯ ⊗_A B_n → Γ(U_0 ∩ ⋯ ∩ U_n))`. -/
abbrev tensorIdeal : Ideal (tensorRing L) :=
  RingHom.ker (tensorMap L : tensorRing L →+* Γ((inter U).toScheme, ⊤))

/-- The divided power ideal `I` of `A` maps into `K`, as `I` dies on `X`. -/
theorem map_le_tensorIdeal :
    (baseSectionsRing S).ideal.map (algebraMap (baseSectionsRing S) (tensorRing L)) ≤
      tensorIdeal L := by
  refine Ideal.map_le_iff_le_comap.mpr fun a ha ↦ ?_
  change tensorMap L (algebraMap _ _ a) = 0
  rw [AlgHom.commutes]
  exact baseSectionsToSections_eq_zero_of_mem (overSituation S (inter U).ι) a ha

/-- **The divided power envelope `D` of `K` in `B_0 ⊗_A ⋯ ⊗_A B_n`**, relative to `(A, I, γ)`. -/
def envelope : DividedPowerEnvelope (baseSectionsRing S)
    (algebraMap (baseSectionsRing S) (tensorRing L)) (tensorIdeal L) (map_le_tensorIdeal L) :=
  dividedPowerEnvelope _ _ _ _

/-- The envelope factors the quotient map by `K`, with kernel its divided power ideal, [Stacks,
Tag 07HA]. -/
theorem exists_envelopeProj :
    ∃ p : (envelope L).object →+* tensorRing L ⧸ tensorIdeal L,
      p.comp (envelope L).algebraMap.toRingHom = Ideal.Quotient.mk _ ∧
        Function.Surjective p ∧ RingHom.ker p = (envelope L).object.ideal := by
  obtain ⟨-, p, h1, -, h3, h4, -⟩ := dividedPowerEnvelope_factorization _ _ _ _ (envelope L)
  exact ⟨p, h1, h3, h4⟩

/-- The map `D → (B_0 ⊗_A ⋯ ⊗_A B_n)/K`. -/
def envelopeProj : (envelope L).object →+* tensorRing L ⧸ tensorIdeal L :=
  Classical.choose (exists_envelopeProj L)

/-- `envelopeProj` restricts to the quotient map along `B_0 ⊗ ⋯ ⊗ B_n → D`. -/
theorem envelopeProj_algebraMap (x : tensorRing L) :
    envelopeProj L ((envelope L).algebraMap.toRingHom x) = Ideal.Quotient.mk _ x :=
  RingHom.congr_fun (Classical.choose_spec (exists_envelopeProj L)).1 x

variable [∀ k, IsAffine (U k)] [S.X.IsSeparated]

/-- **`D/J̄ ≅ Γ(U_0 ∩ ⋯ ∩ U_n)`.** -/
def envelopeEquiv :
    (envelope L).object ⧸ (envelope L).object.ideal ≃+* Γ((inter U).toScheme, ⊤) :=
  (Ideal.quotEquivOfEq (Classical.choose_spec (exists_envelopeProj L)).2.2.symm).trans
    ((RingHom.quotientKerEquivOfSurjective
      (Classical.choose_spec (exists_envelopeProj L)).2.1).trans
      (RingHom.quotientKerEquivOfSurjective (surjective_tensorMap L)))

/-- `envelopeEquiv` on the class of an element of `B_0 ⊗ ⋯ ⊗ B_n`. -/
theorem envelopeEquiv_mk_algebraMap (x : tensorRing L) :
    envelopeEquiv L (Ideal.Quotient.mk _ ((envelope L).algebraMap.toRingHom x)) =
      tensorMap L x := by
  simp only [envelopeEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  refine (congrArg (RingHom.quotientKerEquivOfSurjective (surjective_tensorMap L))
    ((RingHom.quotientKerEquivOfSurjective_apply_mk _ _).trans
      (envelopeProj_algebraMap L x))).trans ?_
  exact RingHom.quotientKerEquivOfSurjective_apply_mk _ _

end Tensor

/-! ### The envelope object and its projections -/

section Object

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) {n : ℕ} {U : Fin (n + 1) → S.X.Opens}
  [∀ k, IsAffine (U k)] [S.X.IsSeparated] (L : ∀ k, SmoothLift S (U k).ι)

attribute [local instance] interAlgebra

/-- The envelope `(D, J̄, δ)` as an object of `CRIS(Γ(U_0 ∩ ⋯ ∩ U_n)/A)`. -/
def envelopeThickening :
    DividedPowerThickening.{u, u, u} (affineSituation (overSituation S (inter U).ι)
      (isNilpotent_prime_over S (inter U).ι hp)) where
  ring := (envelope L).object
  fromBase := (envelope L).structureMap
  prime_nilpotent := by
    have h : ((S.p : ℕ) : (envelope L).object) =
        (envelope L).structureMap ((S.p : ℕ) : baseSectionsRing S) :=
      (map_natCast (envelope L).structureMap.toRingHom _).symm
    change IsNilpotent ((S.p : ℕ) : (envelope L).object)
    rw [h]
    exact hp.map (envelope L).structureMap.toRingHom
  toQuotient := (envelopeEquiv L).symm.toRingHom
  commutes := RingHom.ext fun a ↦ by
    have h0 : (envelope L).structureMap.toRingHom a =
        (envelope L).algebraMap.toRingHom (algebraMap (baseSectionsRing S) (tensorRing L) a) :=
      (RingHom.congr_fun (envelope L).algebraMap_comp a).symm
    have h1 : envelopeEquiv L (Ideal.Quotient.mk _ ((envelope L).structureMap.toRingHom a)) =
        (sourceToBase (overSituation S (inter U).ι)).appTop.hom a := by
      rw [h0, envelopeEquiv_mk_algebraMap]
      exact (tensorMap L).commutes a
    exact (RingEquiv.eq_symm_apply _).mpr h1

/-- **The envelope object `D_s = (U_0 ∩ ⋯ ∩ U_n, Spec D, δ)` of `CRIS(X/S)`.** -/
def envelopeObject : Thickening S :=
  (overPush S (inter U).ι).obj
    (specThickeningOfAffine (isNilpotent_prime_over S (inter U).ι hp) (envelopeThickening hp L))

/-- The map of the envelope object to `X`. -/
theorem envelopeObject_toX :
    (envelopeObject hp L).toX =
      specToX (isNilpotent_prime_over S (inter U).ι hp) (envelopeThickening hp L) ≫
        (inter U).ι := rfl

omit [IsAffine S.S.scheme] in
/-- The thickened scheme of the envelope object is `U_0 ∩ ⋯ ∩ U_n`. -/
theorem isIso_envelope_specToX :
    IsIso (specToX (isNilpotent_prime_over S (inter U).ι hp) (envelopeThickening hp L)) :=
  GlobalCrystallineSituation.isIso_specToX _ _ (envelopeEquiv L).symm.bijective

/-- The envelope object lies in `Cris(X/S)`. -/
instance isOpenImmersion_envelopeObject_toX : IsOpenImmersion (envelopeObject hp L).toX := by
  have := isIso_envelope_specToX hp L
  have : IsOpenImmersion (specToX (isNilpotent_prime_over S (inter U).ι hp)
    (envelopeThickening hp L)) := IsOpenImmersion.of_isIso _
  rw [envelopeObject_toX]
  exact IsOpenImmersion.comp (X := Spec _) (Y := (inter U).toScheme) (Z := S.X) _ _

/-- The ambient scheme of the envelope object is affine. -/
instance isAffine_envelopeObject_target :
    IsAffine (envelopeObject hp L).thickening.target.scheme := by
  change IsAffine (Spec _)
  infer_instance

/-- The thickened scheme of the envelope object is affine. -/
instance isAffine_envelopeObject_source : IsAffine (envelopeObject hp L).thickening.source := by
  change IsAffine (Spec _)
  infer_instance

/-- The ring map `B_k → D → Γ(Spec D, ⊤)`. -/
def projRingHom (k : Fin (n + 1)) :
    (L k).ring →+* Γ((envelopeObject hp L).thickening.target.scheme, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom.comp
    ((envelope L).algebraMap.toRingHom.comp (PiTensorProduct.singleAlgHom
      (R := baseSectionsRing S) (A := fun j ↦ (L j).ring) k).toRingHom)

/-- `projRingHom` is compatible with the maps from `A`. -/
theorem projRingHom_comp_algebraMap (k : Fin (n + 1)) :
    (projRingHom hp L k).comp (algebraMap (baseSectionsRing S) (L k).ring) =
      (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom.comp
        (envelope L).structureMap.toRingHom := by
  refine RingHom.ext fun a ↦ ?_
  change (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom
    ((envelope L).algebraMap.toRingHom (PiTensorProduct.singleAlgHom
      (R := baseSectionsRing S) (A := fun j ↦ (L j).ring) k (algebraMap _ _ a))) = _
  rw [AlgHom.commutes]
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom
    (RingHom.congr_fun (envelope L).algebraMap_comp a)

/-- `B_k → Γ(Spec D, ⊤)` is a divided power morphism: `IB_k` is generated by the image of `I`, on
which `γ_k` and the divided powers of the envelope both restrict `γ`. -/
theorem isDPMorphism_projRingHom (k : Fin (n + 1)) :
    DividedPowers.IsDPMorphism (L k).dividedPowerRing.dividedPowers
      (envelopeObject hp L).thickening.sectionsRing.dividedPowers (projRingHom hp L k) :=
  DividedPowers.IsDPMorphism.of_comp (baseSectionsRing S).dividedPowers _ _
    (algebraMap (baseSectionsRing S) (L k).ring) (projRingHom hp L k) rfl
    (L k).isDPMorphism_algebraMap
    ((projRingHom_comp_algebraMap hp L k).symm ▸
      ((DividedPowerScheme.specSectionsRingIso (envelope L).object).hom.comp
        (envelope L).structureMap).isDPMorphism)

/-- The map of the thickened scheme of the envelope object to `U_k`. -/
abbrev projToU (k : Fin (n + 1)) : (envelopeObject hp L).thickening.source ⟶ (U k).toScheme :=
  specToX (isNilpotent_prime_over S (inter U).ι hp) (envelopeThickening hp L) ≫
    S.X.homOfLE (inter_le U k)

/-- `projToU` followed by the inclusion of `U_k` is the map of the envelope object to `X`. -/
theorem projToU_ι (k : Fin (n + 1)) : projToU hp L k ≫ (U k).ι = (envelopeObject hp L).toX := by
  have h : S.X.homOfLE (inter_le U k) ≫ (U k).ι = (inter U).ι := Scheme.homOfLE_ι _ _
  exact (Category.assoc _ _ _).trans (congrArg (fun g ↦ specToX _ _ ≫ g) h)

/-- The envelope object read over `U_k`. -/
abbrev envelopeOver (k : Fin (n + 1)) : Thickening (overSituation S (U k).ι) :=
  overLift S (U k).ι (envelopeObject hp L) (projToU hp L k) (projToU_ι hp L k)

/-- The thickened scheme of `envelopeOver` is affine. -/
instance isAffine_envelopeOver_source (k : Fin (n + 1)) :
    IsAffine (envelopeOver hp L k).thickening.source :=
  inferInstanceAs (IsAffine (Spec _))

/-- The image of an element of `B_k` in the thickened scheme of the envelope object is the
restriction of the corresponding section of `U_k`. -/
theorem immersion_appTop_projRingHom (k : Fin (n + 1)) (c : Γ((U k).toScheme, ⊤))
    (b : (L k).ring) (hb : Ideal.Quotient.mk _ b = (L k).equiv c) :
    (envelopeObject hp L).thickening.immersion.appTop.hom (projRingHom hp L k b) =
      (specToX (isNilpotent_prime_over S (inter U).ι hp) (envelopeThickening hp L)).appTop.hom
        (restr U k c) := by
  refine appTop_specQuotientImmersion_eq (isNilpotent_prime_over S (inter U).ι hp)
    (envelopeThickening hp L) ?_
  change _ = (envelopeEquiv L).symm (restr U k c)
  refine (RingEquiv.eq_symm_apply _).mpr ?_
  refine (envelopeEquiv_mk_algebraMap L (PiTensorProduct.singleAlgHom
    (R := baseSectionsRing S) (A := fun j ↦ (L j).ring) k b)).trans ?_
  rw [tensorMap_single, component_apply, hb, RingEquiv.symm_apply_apply]

/-- `B_k → Γ(Spec D, ⊤)` as a divided power morphism. -/
def projDPMorphism (k : Fin (n + 1)) :
    (L k).dividedPowerRing ⟶ (envelopeObject hp L).thickening.sectionsRing :=
  DividedPowers.DPMorphism.mk' (isDPMorphism_projRingHom hp L k)

/-- The value of `projDPMorphism`. -/
theorem projDPMorphism_apply (k : Fin (n + 1)) (b : (L k).ring) :
    projDPMorphism hp L k b = projRingHom hp L k b := rfl

/-- The projection of the envelope to the `k`-th smooth lift, on divided power thickenings. -/
def projThickeningHom (k : Fin (n + 1)) :
    (L k).thickening hp ⟶
      wholeThickeningToAffine (isNilpotent_prime_over S (U k).ι hp) (envelopeOver hp L k) where
  hom := projDPMorphism hp L k
  fromBase_comp := by
    ext a
    have h1 := RingHom.congr_fun (projRingHom_comp_algebraMap hp L k) a
    have h2 := congrArg (fun φ ↦ DividedPowers.DPMorphism.toRingHom φ a)
      (DividedPowerScheme.globalSectionsDPMorphism_homOfSectionsDPMorphism
        (specFromBase (isNilpotent_prime_over S (inter U).ι hp) (envelopeThickening hp L)))
    exact h1.trans h2.symm
  toQuotient_comp := RingHom.ext fun c ↦ by
    refine (envelopeOver hp L k).thickening.sectionsQuotientEquiv.injective ?_
    obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective ((L k).equiv c)
    refine Eq.trans ?_
      (sectionsQuotientEquiv_wholeSectionsToQuotient (envelopeOver hp L k) c).symm
    have e1 : ((L k).thickening hp).toQuotient c =
        Ideal.Quotient.mk (L k).dividedPowerRing.ideal b := hb.symm
    refine (congrArg (fun q ↦ (envelopeOver hp L k).thickening.sectionsQuotientEquiv
      (DividedPowerRing.quotientRingHom (projDPMorphism hp L k) q)) e1).trans ?_
    refine (congrArg (envelopeOver hp L k).thickening.sectionsQuotientEquiv
      (DividedPowerRing.quotientRingHom_mk (projDPMorphism hp L k) b)).trans ?_
    refine (SchemeThickening.sectionsQuotientEquiv_mk _ _).trans ?_
    refine (immersion_appTop_projRingHom hp L k c b hb).trans ?_
    exact (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop
      (specToX (isNilpotent_prime_over S (inter U).ι hp) (envelopeThickening hp L))
      (S.X.homOfLE (inter_le U k))) c).symm

/-- **The projection `D_s ⟶ D_k`.** -/
def proj (k : Fin (n + 1)) : envelopeObject hp L ⟶ (L k).object hp :=
  haveI := (L k).isIso_specToX hp
  haveI : IsIso (specThickeningOfAffine (isNilpotent_prime_over S (U k).ι hp)
    ((L k).thickening hp)).toX := (L k).isIso_specToX hp
  haveI : IsAffine (specThickeningOfAffine (isNilpotent_prime_over S (U k).ι hp)
    ((L k).thickening hp)).thickening.source := inferInstanceAs (IsAffine (Spec _))
  homOfOverLift S (U k).ι (homOfAffineSections (isNilpotent_prime_over S (U k).ι hp)
    ((wholeThickeningToAffineSpecIso (isNilpotent_prime_over S (U k).ι hp)
      ((L k).thickening hp)).hom ≫ projThickeningHom hp L k))

/-- The projection on global sections of the ambient schemes. -/
theorem proj_targetHom_appTop (k : Fin (n + 1))
    (x : Γ(((L k).object hp).thickening.target.scheme, ⊤)) :
    (proj hp L k).targetHom.hom.appTop.hom x =
      projRingHom hp L k
        ((Scheme.ΓSpecIso (CommRingCat.of (L k).dividedPowerRing)).hom.hom x) :=
  ConcreteCategory.congr_hom (DividedPowerScheme.homOfSectionsDPMorphism_hom_appTop _) x

end Object

/-! ### The universal property -/

section Lift

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) {n : ℕ} {U : Fin (n + 1) → S.X.Opens}
  [∀ k, IsAffine (U k)] [S.X.IsSeparated] (L : ∀ k, SmoothLift S (U k).ι)
  {T : Thickening S} (f : ∀ k, T ⟶ (L k).object hp)

attribute [local instance] interAlgebra

/-- The `A`-algebra structure of the global sections of the ambient scheme of an object. -/
abbrev targetAlgebra (T : Thickening S) :
    Algebra (baseSectionsRing S) Γ(T.thickening.target.scheme, ⊤) :=
  T.toBase.hom.appTop.hom.toAlgebra

/-- The `A`-algebra structure of the global sections of the thickened scheme of an object. -/
abbrev sourceAlgebra (T : Thickening S) :
    Algebra (baseSectionsRing S) Γ(T.thickening.source, ⊤) :=
  (T.thickening.immersion ≫ T.toBase.hom).appTop.hom.toAlgebra

attribute [local instance] targetAlgebra sourceAlgebra

omit [S.X.IsSeparated] in
include f in
/-- An object mapping to every `D_k` maps into `U_0 ∩ ⋯ ∩ U_n`. -/
theorem toX_mem_inter (z : T.thickening.source) : T.toX z ∈ inter U := by
  change T.toX z ∈ ((⨅ k, U k : S.X.Opens) : Set S.X)
  rw [TopologicalSpace.Opens.coe_iInf, Set.mem_iInter]
  intro k
  rw [← (f k).toX_naturality]
  change ((L k).object hp).toX ((f k).sourceHom z) ∈ U k
  rw [SmoothLift.object_toX]
  change (U k).ι _ ∈ U k
  exact ((U k).ι_apply _).symm ▸ (Subtype.prop _)

/-- The map of the thickened scheme of `T` to `U_0 ∩ ⋯ ∩ U_n`. -/
def liftToInter : T.thickening.source ⟶ (inter U).toScheme :=
  IsOpenImmersion.lift (inter U).ι T.toX (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact toX_mem_inter hp L f z)

omit [S.X.IsSeparated] in
/-- `liftToInter` followed by the inclusion is the map to `X`. -/
theorem liftToInter_ι : liftToInter hp L f ≫ (inter U).ι = T.toX :=
  IsOpenImmersion.lift_fac _ _ _

/-- The ring map `B_k ≅ Γ(Spec B_k, ⊤) → Γ(T, ⊤)` of the `k`-th leg. -/
def legRingHom (k : Fin (n + 1)) : (L k).ring →+* Γ(T.thickening.target.scheme, ⊤) :=
  (f k).targetHom.hom.appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (L k).dividedPowerRing)).inv.hom

omit [S.X.IsSeparated] in
/-- The map to the base of the object of a smooth lift, on global sections. -/
theorem toBase_appTop_object (k : Fin (n + 1)) (a : baseSectionsRing S) :
    ((L k).object hp).toBase.hom.appTop.hom a =
      (Scheme.ΓSpecIso (CommRingCat.of (L k).dividedPowerRing)).inv.hom
        (algebraMap (baseSectionsRing S) (L k).ring a) :=
  ConcreteCategory.congr_hom (DividedPowerScheme.homOfSectionsDPMorphism_hom_appTop _) a

/-- The `k`-th leg as a map of `A`-algebras. -/
def legAlgHom (k : Fin (n + 1)) :
    (L k).ring →ₐ[baseSectionsRing S] Γ(T.thickening.target.scheme, ⊤) where
  toRingHom := legRingHom hp L f k
  commutes' a := by
    change (f k).targetHom.hom.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (L k).dividedPowerRing)).inv.hom
        (algebraMap (baseSectionsRing S) (L k).ring a)) = T.toBase.hom.appTop.hom a
    rw [← toBase_appTop_object hp L k a, ← (f k).base_naturality]
    rfl

/-- **The map `Φ : B_0 ⊗_A ⋯ ⊗_A B_n → Γ(T, ⊤)` of the legs.** -/
def legTensorMap : tensorRing L →ₐ[baseSectionsRing S] Γ(T.thickening.target.scheme, ⊤) :=
  piLift (legAlgHom hp L f)

/-- Restriction `Γ(U_0 ∩ ⋯ ∩ U_n) → Γ(U_T)` along `liftToInter`, over `A`. -/
def interToSource : Γ((inter U).toScheme, ⊤) →ₐ[baseSectionsRing S] Γ(T.thickening.source, ⊤) where
  toRingHom := (liftToInter hp L f).appTop.hom
  commutes' a := by
    have h : liftToInter hp L f ≫ sourceToBase (overSituation S (inter U).ι) =
        T.thickening.immersion ≫ T.toBase.hom := by
      rw [T.over_base, ← liftToInter_ι hp L f]
      simp only [sourceToBase, Category.assoc]
    exact ConcreteCategory.congr_hom
      ((Scheme.Hom.comp_appTop _ _).symm.trans (congrArg Scheme.Hom.appTop h)) a

/-- Restriction `Γ(T, ⊤) → Γ(U_T, ⊤)`, over `A`. -/
def immersionAlgHom (T : Thickening S) :
    Γ(T.thickening.target.scheme, ⊤) →ₐ[baseSectionsRing S] Γ(T.thickening.source, ⊤) where
  toRingHom := T.thickening.immersion.appTop.hom
  commutes' a := (ConcreteCategory.congr_hom (Scheme.Hom.comp_appTop _ _) a).symm

omit [S.X.IsSeparated] in
/-- The `k`-th leg read on the thickened scheme of `T` is the restriction of the corresponding
section of `U_k`. -/
theorem immersion_legRingHom (k : Fin (n + 1)) (b : (L k).ring) :
    T.thickening.immersion.appTop.hom (legRingHom hp L f k b) =
      (liftToInter hp L f).appTop.hom (component L k b) := by
  have h1 := appTop_specQuotientImmersion_eq (isNilpotent_prime_over S (U k).ι hp)
    ((L k).thickening hp) (β := b) (y := (L k).equiv.symm (Ideal.Quotient.mk _ b))
    ((L k).equiv.apply_symm_apply (Ideal.Quotient.mk _ b)).symm
  let sx : ((L k).object hp).thickening.source ⟶ (U k).toScheme :=
    specToX (isNilpotent_prime_over S (U k).ι hp) ((L k).thickening hp)
  have h2 : (f k).sourceHom ≫ sx = liftToInter hp L f ≫ S.X.homOfLE (inter_le U k) := by
    refine (cancel_mono (U k).ι).mp ?_
    rw [Category.assoc, Category.assoc, Scheme.homOfLE_ι, liftToInter_ι]
    exact (f k).toX_naturality
  have hn := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop (f k).immersion_naturality)
    ((Scheme.ΓSpecIso (CommRingCat.of (L k).dividedPowerRing)).inv.hom b)
  simp only [Scheme.Hom.comp_appTop] at hn
  have h3 := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop h2)
    ((L k).equiv.symm (Ideal.Quotient.mk _ b))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h3
  exact hn.trans ((congrArg (f k).sourceHom.appTop.hom h1).trans h3)

omit [S.X.IsSeparated] in
/-- `Φ` read on the thickened scheme of `T` is `B_0 ⊗ ⋯ ⊗ B_n → Γ(U_0 ∩ ⋯ ∩ U_n) → Γ(U_T)`. -/
theorem immersion_legTensorMap (x : tensorRing L) :
    T.thickening.immersion.appTop.hom (legTensorMap hp L f x) =
      (liftToInter hp L f).appTop.hom (tensorMap L x) := by
  have h : (immersionAlgHom T).comp (legTensorMap hp L f) =
      (interToSource hp L f).comp (tensorMap L) := by
    refine PiTensorProduct.algHom_ext fun k ↦ AlgHom.ext fun b ↦ ?_
    change T.thickening.immersion.appTop.hom (legTensorMap hp L f
      (PiTensorProduct.singleAlgHom k b)) =
        (liftToInter hp L f).appTop.hom (tensorMap L (PiTensorProduct.singleAlgHom k b))
    rw [legTensorMap, piLift_single, tensorMap_single]
    exact immersion_legRingHom hp L f k b
  exact AlgHom.congr_fun h x

/-- `Φ` as a ring map into the divided power ring of global sections of `T`. -/
def legTensorRingHom : tensorRing L →+* T.thickening.sectionsRing :=
  (legTensorMap hp L f).toRingHom

omit [S.X.IsSeparated] in
/-- `Φ` carries `K` into the divided power ideal of `T`, which is the kernel of restriction to
the thickened scheme. -/
theorem map_tensorIdeal_le :
    (tensorIdeal L).map (legTensorRingHom hp L f) ≤
      T.thickening.sectionsRing.ideal := by
  refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
  change legTensorMap hp L f x ∈ SchemeThickening.sectionsIdeal T.thickening
  rw [SchemeThickening.sectionsIdeal_eq_ker_appTop, RingHom.mem_ker, immersion_legTensorMap,
    show tensorMap L x = 0 from hx, map_zero]

omit [S.X.IsSeparated] in
/-- `Φ` is a map over `A`. -/
theorem legTensorMap_comp_algebraMap :
    (legTensorRingHom hp L f).comp (algebraMap (baseSectionsRing S) (tensorRing L)) =
      (globalSectionsDPMorphism T.toBase).toRingHom :=
  RingHom.ext (legTensorMap hp L f).commutes

/-- **The map `ψ : D → Γ(T, ⊤)`** of divided power rings over `A` extending `Φ`. -/
def legEnvelopeMap :
    DividedPowers.DPMorphism (envelope L).object.dividedPowers
      T.thickening.sectionsRing.dividedPowers :=
  envLift (envelope L) T.thickening.sectionsRing (globalSectionsDPMorphism T.toBase)
    (legTensorRingHom hp L f) (map_tensorIdeal_le hp L f)
    (legTensorMap_comp_algebraMap hp L f)

omit [S.X.IsSeparated] in
/-- `ψ` restricts to `Φ`. -/
theorem legEnvelopeMap_algebraMap (x : tensorRing L) :
    legEnvelopeMap hp L f ((envelope L).algebraMap.toRingHom x) = legTensorMap hp L f x :=
  RingHom.congr_fun (envLift_comp_algebraMap _ _ _ _ _ _) x

omit [S.X.IsSeparated] in
/-- `ψ` is a map over `A`. -/
theorem legEnvelopeMap_structureMap (a : baseSectionsRing S) :
    legEnvelopeMap hp L f ((envelope L).structureMap a) = T.toBase.hom.appTop.hom a :=
  congrArg (fun φ ↦ DividedPowers.DPMorphism.toRingHom φ a)
    (envLift_comp_structureMap _ _ _ _ _ _)

/-- `ψ` read on `Γ(Spec D, ⊤)`. -/
def liftSectionsMap :
    (envelopeObject hp L).thickening.sectionsRing ⟶ T.thickening.sectionsRing :=
  (DividedPowerScheme.specSectionsRingIso (envelope L).object).inv ≫ legEnvelopeMap hp L f

/-- The value of `liftSectionsMap`. -/
theorem liftSectionsMap_apply (z : Γ((envelopeObject hp L).thickening.target.scheme, ⊤)) :
    liftSectionsMap hp L f z = legEnvelopeMap hp L f
      ((Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).hom.hom z) := rfl

/-- The map of ambient schemes `T ⟶ Spec D` of the lift. -/
def liftTargetHom : T.thickening.target ⟶ (envelopeObject hp L).thickening.target :=
  DividedPowerScheme.homOfSectionsDPMorphism (liftSectionsMap hp L f)

/-- The map of ambient schemes of the lift, on global sections. -/
theorem liftTargetHom_appTop (z : Γ((envelopeObject hp L).thickening.target.scheme, ⊤)) :
    (liftTargetHom hp L f).hom.appTop.hom z = liftSectionsMap hp L f z :=
  ConcreteCategory.congr_hom (DividedPowerScheme.homOfSectionsDPMorphism_hom_appTop _) z

/-- The map of ambient schemes of the lift, on the image of `D` in `Γ(Spec D, ⊤)`. -/
private theorem liftTargetHom_appTop_inv (y : (envelope L).object) :
    (liftTargetHom hp L f).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom y) =
      legEnvelopeMap hp L f y :=
  (liftTargetHom_appTop hp L f _).trans
    (congrArg (legEnvelopeMap hp L f) (DividedPowerScheme.ΓSpecIso_hom_inv_apply _ _))

/-- The map of the envelope object to the base, on global sections. -/
theorem envelopeObject_toBase_appTop (a : baseSectionsRing S) :
    (envelopeObject hp L).toBase.hom.appTop.hom a =
      (Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom
        ((envelope L).structureMap a) :=
  ConcreteCategory.congr_hom (DividedPowerScheme.homOfSectionsDPMorphism_hom_appTop _) a

/-- The map of ambient schemes of the lift is a map over the base. -/
theorem liftTargetHom_base : liftTargetHom hp L f ≫ (envelopeObject hp L).toBase = T.toBase := by
  refine DividedPowerScheme.Hom.ext
    (ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun c ↦ ?_)))
  refine (congrArg (liftTargetHom hp L f).hom.appTop.hom
    (envelopeObject_toBase_appTop hp L c)).trans ?_
  exact (liftTargetHom_appTop_inv hp L f _).trans (legEnvelopeMap_structureMap hp L f c)

/-- The map of thickened schemes of the lift, followed by the identification with the
intersection, is `liftToInter`: checked on global sections of the affine intersection, which are
hit by `B_0 ⊗ ⋯ ⊗ B_n`. -/
theorem liftSource_specToX :
    SchemeThickening.sourceMapOfTargetMap (liftTargetHom hp L f) ≫
      specToX (isNilpotent_prime_over S (inter U).ι hp) (envelopeThickening hp L) =
        liftToInter hp L f := by
  refine ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext fun y ↦ ?_))
  obtain ⟨x, rfl⟩ := surjective_tensorMap L y
  have h1 := appTop_specQuotientImmersion_eq (isNilpotent_prime_over S (inter U).ι hp)
    (envelopeThickening hp L) (β := (envelope L).algebraMap.toRingHom x) (y := tensorMap L x)
    ((RingEquiv.eq_symm_apply _).mpr (envelopeEquiv_mk_algebraMap L x))
  have h2 := ConcreteCategory.congr_hom (congrArg Scheme.Hom.appTop
    (SchemeThickening.sourceMapOfTargetMap_immersion (liftTargetHom hp L f)))
    ((Scheme.ΓSpecIso (CommRingCat.of (envelope L).object)).inv.hom
      ((envelope L).algebraMap.toRingHom x))
  refine Eq.trans (congrArg (SchemeThickening.sourceMapOfTargetMap
    (liftTargetHom hp L f)).appTop.hom h1.symm) ?_
  refine h2.symm.trans ?_
  refine (congrArg T.thickening.immersion.appTop.hom ((liftTargetHom_appTop_inv hp L f _).trans
    (legEnvelopeMap_algebraMap hp L f x))).trans ?_
  exact immersion_legTensorMap hp L f x

/-- The map of thickened schemes of the lift is a map over `X`. -/
theorem liftSource_toX :
    SchemeThickening.sourceMapOfTargetMap (liftTargetHom hp L f) ≫
      (envelopeObject hp L).toX = T.toX :=
  (congrArg (fun g ↦ SchemeThickening.sourceMapOfTargetMap (liftTargetHom hp L f) ≫ g)
    (envelopeObject_toX hp L)).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (inter U).ι) (liftSource_specToX hp L f)).trans (liftToInter_ι hp L f)))

/-- **The lift `T ⟶ D_s` of a family of maps `T ⟶ D_k`.** -/
def lift : T ⟶ envelopeObject hp L where
  sourceHom := SchemeThickening.sourceMapOfTargetMap (liftTargetHom hp L f)
  targetHom := liftTargetHom hp L f
  immersion_naturality := SchemeThickening.sourceMapOfTargetMap_immersion _
  base_naturality := liftTargetHom_base hp L f
  toX_naturality := liftSource_toX hp L f

/-- `Γ(Spec R, ⊤) ≅ R` read backwards and forwards. -/
theorem ΓSpecIso_inv_hom_apply (R : CommRingCat.{u}) (z : Γ(Spec R, ⊤)) :
    (Scheme.ΓSpecIso R).inv.hom ((Scheme.ΓSpecIso R).hom.hom z) = z :=
  ConcreteCategory.congr_hom (Scheme.ΓSpecIso R).hom_inv_id z

omit [S.X.IsSeparated] in
/-- `Φ` on the `k`-th factor is the `k`-th leg. -/
theorem legTensorMap_single (k : Fin (n + 1)) (b : (L k).ring) :
    legTensorMap hp L f (PiTensorProduct.singleAlgHom k b) = legAlgHom hp L f k b :=
  piLift_single (legAlgHom hp L f) k b

omit [S.X.IsSeparated] in
/-- The value of the `k`-th leg. -/
theorem legAlgHom_apply (k : Fin (n + 1)) (b : (L k).ring) :
    legAlgHom hp L f k b = (f k).targetHom.hom.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (L k).dividedPowerRing)).inv.hom b) := rfl

/-- The lift followed by the `k`-th projection is the `k`-th leg. -/
theorem lift_proj (k : Fin (n + 1)) : lift hp L f ≫ proj hp L k = f k := by
  refine hom_ext_of_targetHom_appTop (CommRingCat.hom_ext (RingHom.ext fun x ↦ ?_))
  refine (congrArg (liftTargetHom hp L f).hom.appTop.hom (proj_targetHom_appTop hp L k x)).trans ?_
  refine (liftTargetHom_appTop_inv hp L f _).trans ?_
  refine (legEnvelopeMap_algebraMap hp L f _).trans ?_
  refine (legTensorMap_single hp L f k _).trans ((legAlgHom_apply hp L f k _).trans ?_)
  exact congrArg (f k).targetHom.hom.appTop.hom (ΓSpecIso_inv_hom_apply _ x)

/-- Any morphism into the envelope object is the lift of its composites with the projections. -/
theorem eq_lift (m : T ⟶ envelopeObject hp L) (hm : ∀ k, m ≫ proj hp L k = f k) :
    m = lift hp L f := by
  let θ : DividedPowers.DPMorphism (envelope L).object.dividedPowers
      T.thickening.sectionsRing.dividedPowers :=
    (globalSectionsDPMorphism m.targetHom).comp
      (DividedPowerScheme.specSectionsRingIso (envelope L).object).hom
  have hθs : ∀ a, θ ((envelope L).structureMap a) = T.toBase.hom.appTop.hom a := fun a ↦ by
    change m.targetHom.hom.appTop.hom ((Scheme.ΓSpecIso _).inv.hom
      ((envelope L).structureMap a)) = _
    exact (congrArg m.targetHom.hom.appTop.hom (envelopeObject_toBase_appTop hp L a).symm).trans
      (ConcreteCategory.congr_hom (congrArg (fun g : T.thickening.target ⟶ S.S ↦ g.hom.appTop)
        m.base_naturality) (show Γ(S.S.scheme, ⊤) from a))
  have hθ : θ = legEnvelopeMap hp L f := by
    refine envelopeHom_ext (envelope L) T.thickening.sectionsRing θ _ ?_ ?_
    · ext a
      exact (hθs a).trans (legEnvelopeMap_structureMap hp L f a).symm
    · let θA : tensorRing L →ₐ[baseSectionsRing S] Γ(T.thickening.target.scheme, ⊤) :=
        { toRingHom := θ.toRingHom.comp (envelope L).algebraMap.toRingHom
          commutes' := fun a ↦
            (congrArg θ (RingHom.congr_fun (envelope L).algebraMap_comp a)).trans (hθs a) }
      have h : θA = legTensorMap hp L f := by
        refine PiTensorProduct.algHom_ext fun k ↦ AlgHom.ext fun b ↦ ?_
        change m.targetHom.hom.appTop.hom (projRingHom hp L k b) =
          legTensorMap hp L f (PiTensorProduct.singleAlgHom k b)
        have h1 := proj_targetHom_appTop hp L k
          ((Scheme.ΓSpecIso (CommRingCat.of (L k).dividedPowerRing)).inv.hom b)
        have h1' := h1.trans
          (congrArg (projRingHom hp L k) (DividedPowerScheme.ΓSpecIso_hom_inv_apply
            (CommRingCat.of (L k).dividedPowerRing) (show (L k).dividedPowerRing from b)))
        rw [← h1']
        refine Eq.trans ?_ ((legTensorMap_single hp L f k b).trans
          (legAlgHom_apply hp L f k b)).symm
        rw [← hm k]
        rfl
      exact RingHom.ext fun x ↦
        (AlgHom.congr_fun h x).trans (legEnvelopeMap_algebraMap hp L f x).symm
  refine hom_ext_of_targetHom_appTop (CommRingCat.hom_ext (RingHom.ext fun z ↦ ?_))
  have h := congrArg (fun φ : DividedPowers.DPMorphism (envelope L).object.dividedPowers
    T.thickening.sectionsRing.dividedPowers ↦ φ ((Scheme.ΓSpecIso _).hom.hom z)) hθ
  refine Eq.trans ?_ (h.trans (liftTargetHom_appTop hp L f z).symm)
  exact (congrArg m.targetHom.hom.appTop.hom (ΓSpecIso_inv_hom_apply _ z)).symm

end Lift

/-! ### The envelope object is a product -/

section Product

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) {n : ℕ} {U : Fin (n + 1) → S.X.Opens}
  [∀ k, IsAffine (U k)] [S.X.IsSeparated] (L : ∀ k, SmoothLift S (U k).ι)

/-- **The envelope object `D_s` with its projections is a product of the `D_k`.** -/
def isLimitFan :
    IsLimit (Fan.mk (envelopeObject hp L) (proj hp L) :
      Fan fun k ↦ (L k).object hp) :=
  Fan.IsLimit.mk _ (fun s ↦ lift hp L s.proj) (fun s k ↦ lift_proj hp L s.proj k)
    (fun s m hm ↦ eq_lift hp L s.proj m hm)

/-- The objects of the smooth lifts have products of finite nonempty families. -/
instance hasProduct_object : HasProduct fun k ↦ (L k).object hp :=
  HasLimit.mk ⟨_, isLimitFan hp L⟩

/-- **The product of the `D_k` is the envelope object.** -/
def piIsoEnvelopeObject : (∏ᶜ fun k ↦ (L k).object hp) ≅ envelopeObject hp L :=
  (limit.isLimit _).conePointUniqueUpToIso (isLimitFan hp L)

/-- The identification of the product with the envelope object is compatible with the
projections. -/
@[reassoc (attr := simp)]
theorem piIsoEnvelopeObject_hom_proj (k : Fin (n + 1)) :
    (piIsoEnvelopeObject hp L).hom ≫ proj hp L k = Pi.π (fun k ↦ (L k).object hp) k :=
  (limit.isLimit _).conePointUniqueUpToIso_hom_comp (isLimitFan hp L) ⟨k⟩

/-- **A quasi-coherent module has no higher cohomology over the envelope object.** -/
theorem isZero_bigRightDerivedSections_envelopeObject
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N.IsQuasicoherentOnSite)
    (q : ℕ) (hq : 0 < q) :
    IsZero ((((sheafSections (topology S) AddCommGrpCat.{u + 1}).obj
      (op (envelopeObject hp L))).rightDerived q).obj
        ((SmallSite.bigToAbelianSheaf S).obj ((SmallSite.bigModuleULift S).obj N))) :=
  SmallSite.isZero_bigRightDerivedSections_of_isAffine N hN _ q hq

/-- **A quasi-coherent module has no higher cohomology over a finite product of the objects of
smooth lifts**: the product is the envelope object, whose map to `X` is an open immersion and
whose ambient scheme is affine. -/
theorem isZero_bigRightDerivedSections_pi
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N.IsQuasicoherentOnSite)
    (q : ℕ) (hq : 0 < q) :
    IsZero ((((sheafSections (topology S) AddCommGrpCat.{u + 1}).obj
      (op (∏ᶜ fun k ↦ (L k).object hp))).rightDerived q).obj
        ((SmallSite.bigToAbelianSheaf S).obj ((SmallSite.bigModuleULift S).obj N))) :=
  (isZero_bigRightDerivedSections_envelopeObject hp L N hN q hq).of_iso
    ((Functor.rightDerivedIsoOfNatIso
      ((sheafSections (topology S) AddCommGrpCat.{u + 1}).mapIso
        (piIsoEnvelopeObject hp L).op) q).app _).symm

end Product

end Crystalline.GlobalCrystallineSituation.CechEnvelope
