module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.RingTheory.CompleteIntersection.Defs
public import StacksFrontier.RingTheory.CompleteIntersection.Basic
public import StacksFrontier.RingTheory.CompleteIntersection.LocalRing
public import StacksFrontier.RingTheory.CompleteIntersection.FieldExtension
public import StacksFrontier.RingTheory.Syntomic.BaseChange
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksFrontier.RingTheory.Syntomic.Morphisms
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension

/-!
# Local complete intersections over a field

For a scheme locally of finite type over a field, being a local complete intersection is
equivalent to having affine global-complete-intersection neighbourhoods at every point and to
having complete-intersection local rings at every point.

## Main results

* `AlgebraicGeometry.localCompleteIntersection_tfae` gives the three equivalent conditions.

## Implementation notes

The structure morphism supplies the algebra structures on rings of sections and on stalks. The
affine-neighbourhood condition uses the coordinate ring of the affine open itself, with its
induced algebra structure, rather than choosing a separate isomorphic presentation.

All three branches of the equivalence need the same comparison between `k` and the global
sections `Γ(Spec k, ⊤)` of its spectrum, which is a field isomorphic to `k` but not equal to it.
That comparison is isolated in
`AlgebraicGeometry.syntomic_sections_iff_isLocalCompleteIntersection`, which is what lets each
branch be short enough to elaborate within the default budget.

The condition on a scheme over a field from `AlgebraicGeometry.Morphisms.Syntomic.Defs` is
`AlgebraicGeometry.IsLocalCompleteIntersectionOverField`; the ring-theoretic predicate of Stacks
00S9 is `_root_.IsLocalCompleteIntersection`.

## References

* [Stacks Project, Tag 01UG](https://stacks.math.columbia.edu/tag/01UG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CommRingCat

universe u

namespace AlgebraicGeometry

section Aux

universe w v

/-- Over a field, being syntomic and being a local complete intersection agree. -/
private theorem syntomic_iff_lci_over_field (k : Type w) [Field k] (A : Type v)
    [CommRing A] [Algebra k A] :
    Algebra.Syntomic k A ↔ _root_.IsLocalCompleteIntersection k A := by
  let : Algebra A ((⊥ : Ideal k).Fiber A) := Algebra.TensorProduct.rightAlgebra
  have : Algebra.IsPushout k (⊥ : Ideal k).ResidueField A ((⊥ : Ideal k).Fiber A) :=
    inferInstance
  have key := Algebra.IsPushout.isLocalCompleteIntersection_iff k (⊥ : Ideal k).ResidueField A
    ((⊥ : Ideal k).Fiber A)
  refine ⟨fun h => ?_, fun ⟨s, hs, hg⟩ => ?_⟩
  · exact key.mp (h.isLocalCompleteIntersection_fiber ⊥)
  · have : Algebra.FiniteType k A :=
      Algebra.FiniteType.of_span_eq_top_target s hs (fun g hgs => (hg g hgs).finiteType)
    refine
      { flat := inferInstance
        finitePresentation := Algebra.FinitePresentation.of_finiteType.mp inferInstance
        isLocalCompleteIntersection_fiber := fun p hp => ?_ }
    obtain rfl : p = ⊥ := Ideal.eq_bot_of_prime p
    exact key.mpr ⟨s, hs, hg⟩

/-- Along a bijective map of fields, syntomicity over the target agrees with being a local
complete intersection over the source. -/
private theorem syntomic_iff_lci_of_fieldEquiv {k K : Type w} [Field k] [Field K]
    [Algebra k K] (hbij : Function.Bijective (algebraMap k K)) (A : Type v) [CommRing A]
    [Algebra k A] [Algebra K A] [IsScalarTower k K A] :
    Algebra.Syntomic K A ↔ _root_.IsLocalCompleteIntersection k A := by
  have hff : (algebraMap k K).FaithfullyFlat := RingHom.FaithfullyFlat.of_bijective hbij
  have : Module.FaithfullyFlat k K :=
    (RingHom.faithfullyFlat_algebraMap_iff (R := k) (S := K)).mp hff
  have : Algebra.IsPushout k K A A :=
    (Algebra.IsPushout.of_bijective_left (T := A) (A := K) hbij).symm
  exact (Algebra.IsPushout.syntomic_iff k K A A).trans (syntomic_iff_lci_over_field k A)

end Aux

/-- The global sections of the spectrum of a field form a field, canonically isomorphic to it. -/
private lemma bijective_algebraMap_specGlobalSections (k : Type u) [Field k] :
    Function.Bijective
      (CommRingCat.ofHom (RingHom.id k) ≫ (Scheme.ΓSpecIso (.of k)).inv).hom := by
  have hinv := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).inv
  change Function.Bijective (((Scheme.ΓSpecIso (.of k)).inv).hom.comp (RingHom.id k))
  exact hinv.comp Function.bijective_id

/-- On an affine open of a scheme over a field, syntomicity of the ring map from the global
sections of `Spec k` agrees with being a local complete intersection over `k`.

This is the comparison between `k` and `Γ(Spec k, ⊤)` that each branch of
`localCompleteIntersection_tfae` needs. The two algebra structures are supplied by the caller,
together with the equations identifying their structure maps. -/
private theorem syntomic_sections_iff_isLocalCompleteIntersection
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) (U : X.Opens)
    (hU : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens))
    [Algebra Γ(Spec (.of k), ⊤) Γ(X, U)] [Algebra k Γ(X, U)]
    (hK : algebraMap Γ(Spec (.of k), ⊤) Γ(X, U) = (f.appLE ⊤ U hU).hom)
    (hk : algebraMap k Γ(X, U) =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U hU).hom) :
    Algebra.Syntomic Γ(Spec (.of k), ⊤) Γ(X, U) ↔
      _root_.IsLocalCompleteIntersection k Γ(X, U) := by
  let K : Type u := Γ(Spec (.of k), ⊤)
  let eK := CommRingCat.ofHom (RingHom.id k) ≫ (Scheme.ΓSpecIso (.of k)).inv
  have hKfield : IsField K :=
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField
      (Field.toIsField k)
  let : Field K := hKfield.toField
  let : Algebra k K := eK.hom.toAlgebra
  have : IsScalarTower k K Γ(X, U) := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    rw [hk, hK]
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U hU).hom a =
      (f.appLE ⊤ U hU).hom (eK.hom a)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
    rfl
  have hbij : Function.Bijective (algebraMap k K) :=
    bijective_algebraMap_specGlobalSections k
  exact syntomic_iff_lci_of_fieldEquiv (k := k) (K := K) hbij Γ(X, U)

/-- The algebra structures on sections over `U` and on the stalk at `x ∈ U` form a scalar tower
over `k`. -/
private theorem isScalarTower_sections_stalk (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) (U : X.Opens) (x : X) (hx : x ∈ U)
    [Algebra k Γ(X, U)] [Algebra k (X.presheaf.stalk x)] [Algebra Γ(X, U) (X.presheaf.stalk x)]
    (hk : algebraMap k Γ(X, U) = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom)
    (hs : algebraMap k (X.presheaf.stalk x) = ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x (by simp)).hom)
    (hg : algebraMap Γ(X, U) (X.presheaf.stalk x) = (X.presheaf.germ U x hx).hom) :
    IsScalarTower k Γ(X, U) (X.presheaf.stalk x) := by
  apply IsScalarTower.of_algebraMap_eq
  intro a
  rw [hs, hg, hk]
  change (X.presheaf.germ ⊤ x (by simp))
      (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom a) =
    (X.presheaf.germ U x hx)
      ((f.appTop ≫ X.presheaf.map (homOfLE le_top).op)
        (((Scheme.ΓSpecIso (.of k)).inv).hom a))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [← X.presheaf.germ_res_apply (homOfLE le_top) x hx]

/-- A local complete intersection over a field has complete-intersection local rings. -/
private theorem stalk_completeIntersection_of_lci (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (U : X.affineOpens) (x : X)
    (hx : x ∈ U.1) :
    letI : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    letI : Algebra k (X.presheaf.stalk x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
    _root_.IsLocalCompleteIntersection k Γ(X, U.1) →
      IsCompleteIntersection k (X.presheaf.stalk x) := by
  let : Algebra k Γ(X, U.1) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
  let : Algebra k (X.presheaf.stalk x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
      X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
  intro h
  let : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
    (X.presheaf.germ U.1 x hx).hom.toAlgebra
  have := isScalarTower_sections_stalk k X f U.1 x hx
    (RingHom.algebraMap_toAlgebra _) (RingHom.algebraMap_toAlgebra _)
    (RingHom.algebraMap_toAlgebra _)
  let q : Ideal Γ(X, U.1) := (U.2.primeIdealOf ⟨x, hx⟩).asIdeal
  have : q.IsPrime := (U.2.primeIdealOf ⟨x, hx⟩).isPrime
  have : IsLocalization.AtPrime (X.presheaf.stalk x) q := U.2.isLocalization_stalk ⟨x, hx⟩
  have : Algebra.FiniteType k Γ(X, U.1) := by
    obtain ⟨s, hs, hg⟩ := h
    exact Algebra.FiniteType.of_span_eq_top_target s hs (fun g hgs => (hg g hgs).finiteType)
  have hci := ((_root_.IsLocalCompleteIntersection.tfae k Γ(X, U.1)).out 1 2).mp h
  exact hci q (X.presheaf.stalk x)

/-- **Stacks Project, Tag 01UG.** For a scheme locally of finite type over a field, being a
local complete intersection is equivalent to the existence of affine neighbourhoods with
global-complete-intersection coordinate rings, and to all local rings being complete
intersections over the field. -/
@[stacks 01UG]
theorem localCompleteIntersection_tfae (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    let globalCI := fun U : X.Opens ↦
      letI : Algebra k Γ(X, U) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
      IsGlobalCompleteIntersection k Γ(X, U)
    let localCI := fun x : X ↦
      letI : Algebra k (X.presheaf.stalk x) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
          X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
      IsCompleteIntersection k (X.presheaf.stalk x)
    List.TFAE [
      IsLocalCompleteIntersectionOverField f,
      ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧ globalCI U.1,
      ∀ x : X, localCI x] := by
  tfae_have 1 → 3 := by
    intro hf x
    obtain ⟨U, hxU, V, hUV, hsyn⟩ := (syntomicAt_iff f x).mp (hf x)
    have hfxV : f x ∈ V.1 := hUV hxU
    have hVtop : V.1 = ⊤ := by
      apply le_antisymm le_top
      intro y _
      have hy : y = f x := by
        apply PrimeSpectrum.ext
        have : y.asIdeal.IsPrime := y.isPrime
        have : (f x).asIdeal.IsPrime := (f x).isPrime
        exact (Ideal.eq_bot_of_prime y.asIdeal).trans
          (Ideal.eq_bot_of_prime (f x).asIdeal).symm
      rw [hy]
      exact hfxV
    have hV : V = ⟨(⊤ : (Spec (.of k)).Opens), isAffineOpen_top _⟩ := Subtype.ext hVtop
    subst V
    let : Algebra Γ(Spec (.of k), ⊤) Γ(X, U.1) := (f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    exact stalk_completeIntersection_of_lci k X f U x hxU
      ((syntomic_sections_iff_isLocalCompleteIntersection k X f U.1 (by simp)
        (RingHom.algebraMap_toAlgebra _) (RingHom.algebraMap_toAlgebra _)).mp hsyn)
  tfae_have 3 → 2 := by
    intro h x
    obtain ⟨_, ⟨U₀, hU₀, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    let U : X.affineOpens := ⟨U₀, hU₀⟩
    let : Algebra Γ(Spec (.of k), ⊤) Γ(X, U.1) := (f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    let : Algebra k (X.presheaf.stalk x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom.toAlgebra
    let : Algebra Γ(X, U.1) (X.presheaf.stalk x) :=
      (X.presheaf.germ U.1 x hxU).hom.toAlgebra
    have := isScalarTower_sections_stalk k X f U.1 x hxU
      (RingHom.algebraMap_toAlgebra _) (RingHom.algebraMap_toAlgebra _)
      (RingHom.algebraMap_toAlgebra _)
    let q : Ideal Γ(X, U.1) := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal
    have : q.IsPrime := (U.2.primeIdealOf ⟨x, hxU⟩).isPrime
    have : IsLocalization.AtPrime (X.presheaf.stalk x) q :=
      U.2.isLocalization_stalk ⟨x, hxU⟩
    have : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(X, U.1) :=
      f.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)
    let : Algebra k Γ(Spec (.of k), ⊤) :=
      (CommRingCat.ofHom (RingHom.id k) ≫ (Scheme.ΓSpecIso (.of k)).inv).hom.toAlgebra
    have : IsScalarTower k Γ(Spec (.of k), ⊤) Γ(X, U.1) := by
      apply IsScalarTower.of_algebraMap_eq
      intro a
      simp only [RingHom.algebraMap_toAlgebra]
      change ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom a =
        (f.appLE ⊤ U.1 (by simp)).hom
          ((CommRingCat.ofHom (RingHom.id k) ≫ (Scheme.ΓSpecIso (.of k)).inv).hom a)
      simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
      rfl
    have : Algebra.FiniteType k Γ(Spec (.of k), ⊤) := RingHom.finiteType_algebraMap.mp
      (.of_surjective _ (bijective_algebraMap_specGlobalSections k).2)
    have : Algebra.FiniteType k Γ(X, U.1) :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k Γ(Spec (.of k), ⊤))
        (inferInstance : Algebra.FiniteType Γ(Spec (.of k), ⊤) Γ(X, U.1))
    obtain ⟨g, hgq, hgci⟩ :=
      ((IsCompleteIntersection.localization_atPrime_tfae.{u, u, u, u} k Γ(X, U.1) q
        (X.presheaf.stalk x)).out 1 3).mp (h x)
    let V : X.affineOpens := X.affineBasicOpen g
    have hxV : x ∈ V.1 := by
      change x ∈ X.basicOpen g
      rw [← U.2.fromSpec_image_basicOpen]
      exact ⟨U.2.primeIdealOf ⟨x, hxU⟩, (PrimeSpectrum.mem_basicOpen g _).2 hgq,
        U.2.fromSpec_primeIdealOf ⟨x, hxU⟩⟩
    let : Algebra Γ(X, U.1) Γ(X, V.1) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom.toAlgebra
    let : Algebra k Γ(X, V.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V.1 (by simp)).hom.toAlgebra
    have : IsScalarTower k Γ(X, U.1) Γ(X, V.1) := by
      apply IsScalarTower.of_algebraMap_eq
      intro a
      simp only [RingHom.algebraMap_toAlgebra]
      have hUtop : U.1 ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
      have hVtop : V.1 ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
      have hcomp :
          ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 hUtop) ≫
              X.presheaf.map (homOfLE (X.basicOpen_le g)).op =
            (Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ V.1 hVtop := by
        rw [Category.assoc, f.appLE_map hUtop (homOfLE (X.basicOpen_le g)).op]
        rfl
      exact (congrArg (fun φ : CommRingCat.of k ⟶ CommRingCat.of Γ(X, V.1) => φ.hom a)
        hcomp).symm
    have : IsLocalization.Away g Γ(X, V.1) := U.2.isLocalization_basicOpen g
    let e : Localization.Away g ≃ₐ[Γ(X, U.1)] Γ(X, V.1) :=
      IsLocalization.algEquiv (.powers g) (Localization.Away g) Γ(X, V.1)
    exact ⟨V, hxV, gci_transport k (e.restrictScalars k) hgci⟩
  tfae_have 2 → 1 := by
    intro h x
    obtain ⟨U, hxU, hgci⟩ := h x
    let : Algebra Γ(Spec (.of k), ⊤) Γ(X, U.1) := (f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    let : Algebra k Γ(X, U.1) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ U.1 (by simp)).hom.toAlgebra
    exact (syntomicAt_iff f x).mpr ⟨U, hxU, ⟨⊤, isAffineOpen_top _⟩, by simp,
      (syntomic_sections_iff_isLocalCompleteIntersection k X f U.1 (by simp)
        (RingHom.algebraMap_toAlgebra _) (RingHom.algebraMap_toAlgebra _)).mpr
        hgci.isLocalCompleteIntersection⟩
  tfae_finish

end AlgebraicGeometry
