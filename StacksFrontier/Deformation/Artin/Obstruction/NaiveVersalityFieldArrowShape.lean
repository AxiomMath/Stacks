module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityDerivation
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldLift

/-!
# Every dual-numbers arrow over `Spec A` is a tangent vector

Let `Λ ⟶ A` be a ring map, `k` a field which is an `A`-algebra, and let `x` be an object of a
category fibred in groupoids over the big fppf site of `S` lying over `Spec A`, with
`Spec A ⟶ S` factoring through `Spec Λ`. The arrows

`Spec k[k] ⟶ Spec A`

of the site over `S` which are compatible with the augmentation `Spec k ⟶ Spec k[k]`, in the
sense that their restriction along it is the point `Spec k ⟶ Spec A` determined by the
`A`-algebra structure of `k`, are exactly the arrows
`Deformation.Artin.canonicalDualNumbersArrow θ` attached to an `A`-linear map
`θ : Ω_{A⁄Λ} → k`, and `θ` is uniquely determined.

This is the converse of the construction of `canonicalDualNumbersArrow`, and it is what turns
a *given* lift of `x` over the dual numbers of `k` into a tangent vector of `Spec A` at the
point: the lift lies over some arrow `Spec k[k] ⟶ Spec A`, and this identifies that arrow with
the one attached to a `θ`, after which the class equation
`Deformation.Artin.canonicalFieldBaseChangeEquiv_canonicalTangentMap` computes the class of the
lift as the image of `θ` under the map on tangent spaces.

## Main results

* `Deformation.Artin.exists_unique_eq_canonicalDualNumbersArrow` — the classification: an
  augmentation-compatible arrow `Spec k[k] ⟶ Spec A` of the site over `S` is
  `canonicalDualNumbersArrow θ` for a unique `θ : Ω[A⁄Λ] →ₗ[A] k`.
* `Deformation.Artin.exists_squareZeroArrow_toScheme_spec` and
  `Deformation.Artin.exists_squareZeroOver_inclusion_hom` — the morphisms of spectra underlying
  the square-zero immersion `Spec A ⟶ Spec A[M]` and the structure morphism of `Spec A[M]`,
  together with the two component properties of the ring maps they come from.

## Implementation notes

The hypothesis on the chosen affine open `Spec Λ` of the source is used here only through
`Mono baseMap`, which an open immersion supplies; it is what forces the ring map underlying the
arrow to be a `Λ`-algebra map, hence its second component to be a `Λ`-derivation. Stated with
the monomorphism hypothesis rather than with `IsOpenImmersion` so that the statement does not
depend on the stronger property.

Both the arrow and its augmentation condition are transported to `CommRingCat` through
`AlgebraicGeometry.Spec.map_surjective` and `AlgebraicGeometry.Spec.map_injective`, the
underlying objects of the site being spectra of rings; the arrow of the site is then recovered
from its ring map because `AlgebraicGeometry.BigFppfOver.toScheme` is faithful, being the
composite of the forgetful functor of a slice with the inclusion of a full subcategory. The
forced shape of the ring map is `Deformation.Artin.exists_unique_kaehler_of_fstHom_comp_eq`,
and `Deformation.Artin.canonicalDualNumbersMap_apply` says that `canonicalDualNumbersArrow θ`'s
own ring map has exactly that shape, so the two match without any further computation; in
particular the uniqueness of `θ` is the uniqueness of that lemma and needs no separate argument
about generators of `Ω[A⁄Λ]`.

Two instance-level precautions are taken, both forced. First, the ring maps underlying the
structural arrows of the site are produced by the *existential* lemmas
`exists_squareZeroArrow_toScheme_spec` and `exists_squareZeroOver_inclusion_hom`, stated with
the site module abstract: writing `TrivSqZeroExt.inlHom k (ModuleCat.of k k)` here instead
would re-run instance synthesis for `Module kᵐᵒᵖ k` at the concrete module and obtain
`Semiring.toOppositeModule` rather than the site's `Deformation.Artin.oppositeModule`, which is
a different ring structure on the same carrier. Second, and for the same reason, the ring map
underlying the arrow has to be transported by hand from `k[k]` as the site forms it to
`TrivSqZeroExt k k`, which is the ring that
`Deformation.Artin.exists_unique_kaehler_of_fstHom_comp_eq` is stated over: the two have the
same carrier and the same operations, but they obtain the right action of `k` on `k` from the
two different instances — one multiplies on the right, the other on the left — which agree by
`mul_comm` and not definitionally. The transport is componentwise, and `mul_comm` is its only
non-reflexivity step.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v

/-! ### The ring maps underlying the structural arrows of the site -/

section SpecDescriptions

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))

/-- The square-zero immersion `Spec A ⟶ Spec A[M]` of the site is the morphism of spectra
determined by the augmentation `A[M] ⟶ A`, which reads off the first component. Produced as an
existential, with the site module `M` abstract, so that instantiating it at a concrete module
substitutes into an already-elaborated statement rather than re-running instance synthesis for
the two actions of `A` on `M` that the square-zero extension ring depends on. -/
public theorem exists_squareZeroArrow_toScheme_spec (M : SiteModule A B) :
    ∃ q : squareZeroRing A M.obj ⟶ CommRingCat.of A,
      (∀ z : (squareZeroRing A M.obj : Type u), q.hom z = z.fst) ∧
        (BigFppfOver.toScheme B S hS).map (squareZeroArrow A B S hS toS hA M) = Spec.map q :=
  ⟨CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom, fun _ => rfl, rfl⟩

/-- The structure morphism to `S` of the object `Spec A[M]` of the site is the morphism of
spectra determined by the inclusion `A ⟶ A[M]` of the first component, followed by the
structure morphism of `Spec A`. Produced as an existential with the site module `M` abstract,
for the reason recorded at `Deformation.Artin.exists_squareZeroArrow_toScheme_spec`. -/
public theorem exists_squareZeroOver_inclusion_hom (M : SiteModule A B) :
    ∃ j : CommRingCat.of A ⟶ squareZeroRing A M.obj,
      (∀ a : A, (j.hom a).fst = a) ∧ (∀ a : A, (j.hom a).snd = 0) ∧
        B.inclusion.map (squareZeroOver A B S hS toS M).hom = Spec.map j ≫ toS :=
  ⟨CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj), fun _ => rfl, fun _ => rfl, rfl⟩

/-- The structure morphism to `S` of the object `Spec A` of the site is the given
`Spec A ⟶ S`. -/
public theorem algebraOver_inclusion_hom :
    B.inclusion.map (algebraOver A B S hS toS hA).hom = toS :=
  rfl

end SpecDescriptions

/-- The arrow `Spec A' ⟶ Spec A` of the site attached to a ring map `A ⟶ A'` is the morphism of
spectra determined by that ring map. -/
public theorem algebraOverMapOfRingHom_toScheme_spec {A A' : Type u} [CommRing A] [CommRing A']
    (f : A →+* A') (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (toS : Spec (.of A) ⟶ S) (toS' : Spec (.of A') ⟶ S)
    (hA : B.Contains (Spec (.of A))) (hA' : B.Contains (Spec (.of A')))
    (hf : Spec.map (CommRingCat.ofHom f) ≫ toS = toS') :
    (BigFppfOver.toScheme B S hS).map (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf) =
      Spec.map (CommRingCat.ofHom f) :=
  rfl

/-- The first component of `inl c + inr m` is `c`. -/
private theorem fst_inl_add_inr {R M : Type*} [AddZeroClass R] [AddZeroClass M] (c : R) (m : M) :
    (TrivSqZeroExt.inl c + TrivSqZeroExt.inr m : TrivSqZeroExt R M).fst = c :=
  add_zero c

/-- The second component of `inl c + inr m` is `m`. -/
private theorem snd_inl_add_inr {R M : Type*} [AddZeroClass R] [AddZeroClass M] (c : R) (m : M) :
    (TrivSqZeroExt.inl c + TrivSqZeroExt.inr m : TrivSqZeroExt R M).snd = m :=
  zero_add m

/-! ### The classification of the dual-numbers arrows -/

variable (Λ A k : Type u) [CommRing Λ] [CommRing A] [Field k] [Algebra Λ A] [Algebra A k]
  [Algebra Λ k] [IsScalarTower Λ A k]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A))) (hAk : B.Contains (Spec (.of k)))
variable {X : Type v} [Category X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
  (hkk : B.Contains (Spec (squareZeroRing k (ModuleCat.of k k))))
  (baseMap : Spec (.of Λ) ⟶ S)
  (baseFactorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)

include B S hS toS hA hAk x hx hp hRS hΩ hkk baseMap baseFactorization in
/-- **Stacks 07YM.** An arrow `ν : Spec k[k] ⟶ Spec A` of the site over `S` whose restriction
along the square-zero immersion `Spec k ⟶ Spec k[k]` is the point of `Spec A` determined by the
`A`-algebra structure of `k` is `Deformation.Artin.canonicalDualNumbersArrow θ` for a unique
`A`-linear map `θ : Ω[A⁄Λ] →ₗ[A] k`.

The ring map `r : A ⟶ k[k]` underlying `ν` exists because the two objects are spectra and
`Spec` is full; the compatibility of `ν` with the structure morphisms to `S`, combined with the
factorization of `Spec A ⟶ S` through the monomorphism `baseMap`, makes `r` a `Λ`-algebra map,
and the hypothesis on the augmentation says that composing it with the projection `k[k] ⟶ k` is
the structure map `A ⟶ k`. By
`Deformation.Artin.exists_unique_kaehler_of_fstHom_comp_eq` such an `r` is
`a ↦ (a mod 𝔭, θ (d a))` for a unique `θ`, which is the ring map of
`canonicalDualNumbersArrow θ` by `Deformation.Artin.canonicalDualNumbersMap_apply`. -/
@[stacks 07YM "the dual-numbers arrows over Spec A are the tangent vectors"]
public theorem exists_unique_eq_canonicalDualNumbersArrow [Mono baseMap]
    (ν : squareZeroOver k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)
          (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ⟶
        algebraOver A B S hS toS hA)
    (hν : squareZeroArrow k B S hS (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
          (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B) ≫ ν =
        algebraOverMapOfRingHom (algebraMap A k) B S hS toS
          (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl) :
    ∃! θ : Ω[A⁄Λ] →ₗ[A] k,
      ν = canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ := by
  obtain ⟨r, hr⟩ := Spec.map_surjective (R := CommRingCat.of A)
    (S := squareZeroRing k (ModuleCat.of k k))
    ((BigFppfOver.toScheme B S hS).map ν)
  obtain ⟨aug, haugfst, haugspec⟩ := exists_squareZeroArrow_toScheme_spec k B S hS
    (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hAk
    (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
  obtain ⟨j, hjfst, hjsnd, hjspec⟩ := exists_squareZeroOver_inclusion_hom k B S hS
    (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS)
    (⟨ModuleCat.of k k, hkk⟩ : SiteModule k B)
  -- The restriction of `ν` along the augmentation is the structure map `A ⟶ k`.
  have haug : ∀ a : A, (r.hom a).fst = algebraMap A k a := by
    have h := congrArg (BigFppfOver.toScheme B S hS).map hν
    rw [(BigFppfOver.toScheme B S hS).map_comp, haugspec,
      algebraOverMapOfRingHom_toScheme_spec (algebraMap A k) B S hS toS
        (Spec.map (CommRingCat.ofHom (algebraMap A k)) ≫ toS) hA hAk rfl, ← hr] at h
    have h2 : Spec.map (r ≫ aug) = Spec.map (CommRingCat.ofHom (algebraMap A k)) :=
      (Spec.map_comp r aug).trans h
    intro a
    have h3 : aug.hom (r.hom a) = algebraMap A k a :=
      RingHom.congr_fun (CommRingCat.hom_ext_iff.mp (Spec.map_injective h2)) a
    exact (haugfst (r.hom a)).symm.trans h3
  -- `ν` is a morphism over `S`, so its ring map is a `Λ`-algebra map.
  have hw := congrArg B.inclusion.map (Over.w ν)
  rw [B.inclusion.map_comp, algebraOver_inclusion_hom A B S hS toS hA, hjspec] at hw
  have hbase : ∀ l : Λ, r.hom (algebraMap Λ A l) = TrivSqZeroExt.inl (algebraMap Λ k l) := by
    have key : Spec.map (CommRingCat.ofHom (algebraMap Λ A) ≫ r) ≫ baseMap =
        Spec.map (CommRingCat.ofHom (algebraMap Λ A) ≫
          CommRingCat.ofHom (algebraMap A k) ≫ j) ≫ baseMap := by
      simp only [Spec.map_comp, Category.assoc, baseFactorization]
      rw [hr]
      exact hw
    have hring := Spec.map_injective ((cancel_mono baseMap).mp key)
    intro l
    have hl : r.hom (algebraMap Λ A l) = j.hom (algebraMap A k (algebraMap Λ A l)) :=
      RingHom.congr_fun (CommRingCat.hom_ext_iff.mp hring) l
    rw [hl, ← IsScalarTower.algebraMap_apply]
    refine TrivSqZeroExt.ext ?_ ?_
    · change (j.hom (algebraMap Λ k l)).fst = algebraMap Λ k l
      exact hjfst _
    · change (j.hom (algebraMap Λ k l)).snd = 0
      exact hjsnd _
  -- The same ring map, read in `TrivSqZeroExt k k`: the two rings have the same carrier and
  -- the same operations, and differ only in which instance supplies the right action of `k`
  -- on itself, so the transport is componentwise and costs one `mul_comm`.
  let q : A →ₐ[Λ] TrivSqZeroExt k k :=
    { toFun := fun a => ((r.hom a).fst, ((r.hom a).snd : k))
      map_one' := congrArg
        (fun z => ((TrivSqZeroExt.fst z, (TrivSqZeroExt.snd z : k)) : TrivSqZeroExt k k))
        (map_one r.hom)
      map_zero' := congrArg
        (fun z => ((TrivSqZeroExt.fst z, (TrivSqZeroExt.snd z : k)) : TrivSqZeroExt k k))
        (map_zero r.hom)
      map_add' := fun a b => congrArg
        (fun z => ((TrivSqZeroExt.fst z, (TrivSqZeroExt.snd z : k)) : TrivSqZeroExt k k))
        (map_add r.hom a b)
      map_mul' := fun a b => by
        refine (congrArg
          (fun z => ((TrivSqZeroExt.fst z, (TrivSqZeroExt.snd z : k)) : TrivSqZeroExt k k))
          (map_mul r.hom a b)).trans ?_
        refine TrivSqZeroExt.ext rfl ?_
        change ((r.hom a).fst * ((r.hom b).snd : k) + (r.hom b).fst * ((r.hom a).snd : k) : k) =
          (r.hom a).fst * ((r.hom b).snd : k) + ((r.hom a).snd : k) * (r.hom b).fst
        ring
      commutes' := fun l => by
        rw [hbase l]
        exact (TrivSqZeroExt.algebraMap_eq_inl' Λ k k l).symm }
  -- The shape of `r` and the shape of `q` say the same thing.
  have hiff : ∀ (a : A) (v : k),
      (q a = TrivSqZeroExt.inl (algebraMap A k a) + TrivSqZeroExt.inr v) ↔
        r.hom a = TrivSqZeroExt.inl (algebraMap A k a) + TrivSqZeroExt.inr v := by
    intro a v
    rw [TrivSqZeroExt.ext_iff, fst_inl_add_inr, snd_inl_add_inr]
    exact ⟨fun h => TrivSqZeroExt.ext (h.1.trans (fst_inl_add_inr _ _).symm)
        (h.2.trans (snd_inl_add_inr _ _).symm),
      fun h => ⟨(congrArg TrivSqZeroExt.fst h).trans (fst_inl_add_inr _ _),
        (congrArg TrivSqZeroExt.snd h).trans (snd_inl_add_inr _ _)⟩⟩
  -- The forced shape of such a ring map.
  obtain ⟨θ, hθ, hθuniq⟩ := exists_unique_kaehler_of_fstHom_comp_eq
    (Λ := Λ) (A := A) (k := k) (IsScalarTower.toAlgHom Λ A k) (fun _ => rfl) q
    (AlgHom.ext fun a => haug a)
  have hshape : ∀ a : A, r.hom a = TrivSqZeroExt.inl (algebraMap A k a) +
      TrivSqZeroExt.inr (θ (KaehlerDifferential.D Λ A a)) := fun a =>
    (hiff a (θ (KaehlerDifferential.D Λ A a))).mp (hθ a)
  -- A ring map of that shape is the ring map of `canonicalDualNumbersArrow`.
  have hmap : ∀ θ' : Ω[A⁄Λ] →ₗ[A] k, (∀ a : A, r.hom a =
      TrivSqZeroExt.inl (algebraMap A k a) +
        TrivSqZeroExt.inr (θ' (KaehlerDifferential.D Λ A a))) →
      ν = canonicalDualNumbersArrow Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
        baseFactorization θ' := by
    intro θ' hθ'
    apply (BigFppfOver.toScheme B S hS).map_injective
    rw [canonicalDualNumbersArrow_spec Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
      baseFactorization θ', ← hr]
    refine congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun a => ?_))
    exact (hθ' a).trans (canonicalDualNumbersMap_apply Λ A k B S hS toS hA p x hx hp hRS hΩ
      baseMap baseFactorization θ' a).symm
  refine ⟨θ, hmap θ hshape, fun θ' hθ' => hθuniq θ' fun a => ?_⟩
  -- Conversely, an arrow equal to `canonicalDualNumbersArrow θ'` has `θ'`'s shape.
  have hrθ' : r = CommRingCat.ofHom (canonicalDualNumbersMap Λ A k B S hS toS hA p x hx hp hRS
      hΩ baseMap baseFactorization θ') := by
    apply Spec.map_injective
    rw [hr, hθ']
    exact canonicalDualNumbersArrow_spec Λ A k B S hS toS hA p x hx hp hRS hΩ hkk baseMap
      baseFactorization θ'
  have hgoal : r.hom a = TrivSqZeroExt.inl (algebraMap A k a) +
      TrivSqZeroExt.inr (θ' (KaehlerDifferential.D Λ A a)) := by
    have h2 : r.hom a = canonicalDualNumbersMap Λ A k B S hS toS hA p x hx hp hRS hΩ baseMap
        baseFactorization θ' a :=
      RingHom.congr_fun (CommRingCat.hom_ext_iff.mp hrθ') a
    exact h2.trans (canonicalDualNumbersMap_apply Λ A k B S hS toS hA p x hx hp hRS hΩ baseMap
      baseFactorization θ' a)
  exact (hiff a (θ' (KaehlerDifferential.D Λ A a))).mpr hgoal

end Deformation.Artin
