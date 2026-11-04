module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.Envelope

/-!
# The codiagonal `ε_b : D(b) → D`

Work in an affine crystalline situation `(A, I, γ)` with target `C`, fix a surjection
`f : P = A[x_i] → C`, and let `D` be the `p`-adically completed divided power envelope of
`J = ker f` and `D(b)` the one of the kernel `J(b)` of the surjection
`P ⊗_A ⋯ ⊗_A P → C` on the `(b + 1)`-fold tensor power.

The proof of [Stacks, Proposition 60.21.3, Tag 07LG] needs, for its second spectral sequence,
that the `b + 1` maps `D → D(b)` all induce the *same* map on cohomology, and the reason the
source gives is that "the inverse is given by the co-diagonal map `D(b) → D` (corresponding to
the multiplication map `P ⊗_A ⋯ ⊗_A P → P`)".  This module constructs that map.

## How it is constructed

The multiplication map `P ⊗_A ⋯ ⊗_A P → P` is, in the presentation this library uses, the
renaming of variables `MvPolynomial.rename Prod.snd` which forgets which tensor factor a variable
came from; and the surjection `P ⊗_A ⋯ ⊗_A P → C` is by *definition*
`Crystalline.tensorPowerPresentation`, which is `f` composed with exactly that renaming.  So the
renaming commutes with the two presentations of `C` on the nose, and
`Crystalline.polynomialEnvelopeMap` — the functoriality of the divided power envelope of a
polynomial presentation, which is also what the cosimplicial structure maps
`Crystalline.envelopeReindex` are built from — turns it into a divided power morphism of the
envelopes over the base.  `Crystalline.adicCompletionRingMap` then completes it.

Nothing here uses the coproduct description of `D(b)` of [Stacks, Tag 07L4]: the universal
property of the envelope of a polynomial presentation is enough, and it gives a map pinned by its
values on the polynomial algebra, which `Crystalline.envelopeCoproductIsColimit` — a
`Classical`-style choice out of a `Nonempty` — does not.

## Main definitions

* `Crystalline.envelopeCodiagonal` — **the codiagonal `D(b)_env → D_env` of the uncompleted
  envelopes**, as a divided power morphism over the base.
* `Crystalline.envelopePolynomialCoprojection` — the `j`-th coprojection `D_env → D(b)_env`, built
  the same way from `Crystalline.mvPolynomialCoprojection`.
* `Crystalline.completedEnvelopeCodiagonal` — **the codiagonal `ε_b : D(b) → D`** of the
  `p`-adically completed envelopes.
* `Crystalline.completedEnvelopeCoprojectionRingHom` — the `j`-th coprojection `D → D(b)` of the
  completed envelopes.
* `Crystalline.zeroEnvelopeRingEquiv` — **the isomorphism `D(0) ≅ D`**, the codiagonal in degree
  zero and the unique coprojection being mutually inverse.

## Main results

* `Crystalline.envelopeCodiagonal_comp_reindex` and
  `Crystalline.completedEnvelopeCodiagonal_map` — **the codiagonal is a retraction of the whole
  cosimplicial object**: `ε_n ∘ D(φ) = ε_m` for every `φ : ⦋m⦌ ⟶ ⦋n⦌` of the simplex category,
  which for the cofaces is the identity `ε_{b+1} ∘ d^i = ε_b` the source uses.
* `Crystalline.completedEnvelopeCodiagonal_coprojection` — `ε_b ∘ (the j-th coprojection) = 𝟙_D`,
  for every one of the `b + 1` coprojections.  This is the sense in which `ε_b` is "the inverse"
  of each of the `b + 1` maps `D → D(b)`.
* `Crystalline.completedEnvelopeCodiagonal_isDPMorphism` — the codiagonal is a divided power
  morphism of the completed divided power envelopes, not merely a ring map.

No tag attribute is placed: the codiagonal is a construction inside the proof of
[Stacks, Tag 07LG] and is not the statement of a tag.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.19.2, Tag 07L2](https://stacks.math.columbia.edu/tag/07L2)
* [Stacks Project, Equation 60.17.3, Tag 07JF](https://stacks.math.columbia.edu/tag/07JF)
* [Stacks Project, Tag 07J8](https://stacks.math.columbia.edu/tag/07J8)
-/

@[expose] public section

open CategoryTheory Opposite Simplicial

universe u v w

namespace Crystalline

section Codiagonal

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C)

/-- **The codiagonal `D(b)_env → D_env` of the uncompleted divided power envelopes.**

The multiplication map `P ⊗_A ⋯ ⊗_A P → P` is the renaming `MvPolynomial.rename Prod.snd` of the
variables which forgets the tensor factor, and
`Crystalline.tensorPowerPresentation s f b = f.comp (MvPolynomial.rename Prod.snd)` by
definition, so that renaming commutes with the two presentations of `C` on the nose and
`Crystalline.polynomialEnvelopeMap` applies. -/
public noncomputable def envelopeCodiagonal (b : ℕ) :
    {q : DividedPowers.DPMorphism (tensorPowerEnvelope s f b).object.dividedPowers
        (polynomialDividedPowerEnvelope s f).object.dividedPowers //
      q.comp (tensorPowerEnvelope s f b).structureMap =
        (polynomialDividedPowerEnvelope s f).structureMap} :=
  polynomialEnvelopeMap s (tensorPowerPresentation s f b) f
    (MvPolynomial.rename Prod.snd) rfl

/-- The codiagonal forgets the tensor factor of each variable, on the image of the polynomial
algebra. -/
public lemma envelopeCodiagonal_polynomial (b : ℕ)
    (x : MvPolynomial (Fin (b + 1) × ι) s.A) :
    (envelopeCodiagonal s f b).1 ((tensorPowerEnvelope s f b).algebraMap.toRingHom x) =
      (polynomialDividedPowerEnvelope s f).algebraMap.toRingHom
        (MvPolynomial.rename Prod.snd x) :=
  polynomialEnvelopeMap_polynomial s _ _ _ _ x

/-- Composites of divided power morphisms of polynomial envelopes which are compatible with the
structure maps are again compatible. -/
private theorem dpMorphism_comp_comp_structureMap {κ κ' κ'' : Type w}
    (g : MvPolynomial κ s.A →ₐ[s.A] s.C) (g' : MvPolynomial κ' s.A →ₐ[s.A] s.C)
    (g'' : MvPolynomial κ'' s.A →ₐ[s.A] s.C)
    (a : DividedPowers.DPMorphism (polynomialDividedPowerEnvelope s g).object.dividedPowers
      (polynomialDividedPowerEnvelope s g').object.dividedPowers)
    (b : DividedPowers.DPMorphism (polynomialDividedPowerEnvelope s g').object.dividedPowers
      (polynomialDividedPowerEnvelope s g'').object.dividedPowers)
    (ha : a.comp (polynomialDividedPowerEnvelope s g).structureMap =
      (polynomialDividedPowerEnvelope s g').structureMap)
    (hb : b.comp (polynomialDividedPowerEnvelope s g').structureMap =
      (polynomialDividedPowerEnvelope s g'').structureMap) :
    (b.comp a).comp (polynomialDividedPowerEnvelope s g).structureMap =
      (polynomialDividedPowerEnvelope s g'').structureMap := by
  ext x
  exact (congrArg (fun q => b (q x)) ha).trans (congrArg (fun q => q x) hb)

/-- **The codiagonal is a retraction of the whole cosimplicial object**: composing the reindexing
morphism `D(n)_env → D(m)_env` of a map of finite ordinals with the codiagonal of `D(m)_env` gives
the codiagonal of `D(n)_env`.

For a coface `φ = d^i : ⦋b⦌ ⟶ ⦋b + 1⦌` this is `ε_{b+1} ∘ d^i = ε_b`.  On the polynomial algebra
both sides are `MvPolynomial.rename Prod.snd`, because `Prod.snd` is unchanged by reindexing the
first coordinate; the uniqueness half of the universal property of the envelope,
`Crystalline.polynomialEnvelopeMap_ext`, upgrades that to the envelopes. -/
public lemma envelopeCodiagonal_comp_reindex {n m : SimplexCategory} (φ : n ⟶ m)
    (x : (tensorPowerEnvelope s f n.len).object) :
    (envelopeCodiagonal s f m.len).1 ((envelopeReindex s f φ).1 x) =
      (envelopeCodiagonal s f n.len).1 x := by
  have h : (envelopeCodiagonal s f m.len).1.comp (envelopeReindex s f φ).1 =
      (envelopeCodiagonal s f n.len).1 := by
    refine polynomialEnvelopeMap_ext s (tensorPowerPresentation s f n.len) f _ _ ?_
      (envelopeCodiagonal s f n.len).2 ?_
    · exact dpMorphism_comp_comp_structureMap s _ _ _ _ _ (envelopeReindex s f φ).2
        (envelopeCodiagonal s f m.len).2
    · intro a
      show (envelopeCodiagonal s f m.len).1 ((envelopeReindex s f φ).1 _) = _
      rw [envelopeReindex_polynomial, envelopeCodiagonal_polynomial,
        envelopeCodiagonal_polynomial, MvPolynomial.rename_rename]
      rfl
  exact congrArg (fun q => q x) h

/-- **The `j`-th coprojection `D_env → D(b)_env` of the uncompleted envelopes**, built from
`Crystalline.mvPolynomialCoprojection` the same way the codiagonal is built from the
multiplication map. -/
public noncomputable def envelopePolynomialCoprojection (b : ℕ) (j : Fin (b + 1)) :
    {q : DividedPowers.DPMorphism (polynomialDividedPowerEnvelope s f).object.dividedPowers
        (tensorPowerEnvelope s f b).object.dividedPowers //
      q.comp (polynomialDividedPowerEnvelope s f).structureMap =
        (tensorPowerEnvelope s f b).structureMap} :=
  polynomialEnvelopeMap s f (tensorPowerPresentation s f b)
    (mvPolynomialCoprojection s.A j) (tensorPowerPresentation_comp_coprojection s f j)

/-- The coprojection places every variable in the `j`-th tensor factor, on the image of the
polynomial algebra. -/
public lemma envelopePolynomialCoprojection_polynomial (b : ℕ) (j : Fin (b + 1))
    (x : MvPolynomial ι s.A) :
    (envelopePolynomialCoprojection s f b j).1
        ((polynomialDividedPowerEnvelope s f).algebraMap.toRingHom x) =
      (tensorPowerEnvelope s f b).algebraMap.toRingHom (mvPolynomialCoprojection s.A j x) :=
  polynomialEnvelopeMap_polynomial s _ _ _ _ x

/-- **The codiagonal is a retraction of each of the `b + 1` coprojections.**  On the polynomial
algebra this is `Prod.snd ∘ (fun i ↦ (j, i)) = id`. -/
public lemma envelopeCodiagonal_comp_coprojection (b : ℕ) (j : Fin (b + 1))
    (x : (polynomialDividedPowerEnvelope s f).object) :
    (envelopeCodiagonal s f b).1 ((envelopePolynomialCoprojection s f b j).1 x) = x := by
  have h : (envelopeCodiagonal s f b).1.comp (envelopePolynomialCoprojection s f b j).1 =
      DividedPowers.DPMorphism.id
        (polynomialDividedPowerEnvelope s f).object.dividedPowers := by
    refine polynomialEnvelopeMap_ext s f f _ _ ?_ ?_ ?_
    · exact dpMorphism_comp_comp_structureMap s _ _ _ _ _ (envelopePolynomialCoprojection s f b j).2
        (envelopeCodiagonal s f b).2
    · ext a
      rfl
    · intro a
      show (envelopeCodiagonal s f b).1 ((envelopePolynomialCoprojection s f b j).1 _) = _
      rw [envelopePolynomialCoprojection_polynomial, envelopeCodiagonal_polynomial,
        mvPolynomialCoprojection, MvPolynomial.rename_rename]
      show (polynomialDividedPowerEnvelope s f).algebraMap.toRingHom
        (MvPolynomial.rename id a) = _
      rw [MvPolynomial.rename_id]
      rfl
  exact congrArg (fun q => q x) h

/-- **In degree zero the coprojection is a retraction of the codiagonal too**, so the two are
mutually inverse: on the polynomial algebra the composite is
`(fun i ↦ (0, i)) ∘ Prod.snd = id`, which holds because `Fin 1` has one element. -/
public lemma envelopePolynomialCoprojection_comp_envelopeCodiagonal_zero
    (x : (tensorPowerEnvelope s f 0).object) :
    (envelopePolynomialCoprojection s f 0 0).1 ((envelopeCodiagonal s f 0).1 x) = x := by
  have h : (envelopePolynomialCoprojection s f 0 0).1.comp (envelopeCodiagonal s f 0).1 =
      DividedPowers.DPMorphism.id (tensorPowerEnvelope s f 0).object.dividedPowers := by
    refine polynomialEnvelopeMap_ext s (tensorPowerPresentation s f 0)
      (tensorPowerPresentation s f 0) _ _ ?_ ?_ ?_
    · exact dpMorphism_comp_comp_structureMap s _ _ _ _ _ (envelopeCodiagonal s f 0).2
        (envelopePolynomialCoprojection s f 0 0).2
    · ext a
      rfl
    · intro a
      show (envelopePolynomialCoprojection s f 0 0).1 ((envelopeCodiagonal s f 0).1 _) = _
      rw [envelopeCodiagonal_polynomial, envelopePolynomialCoprojection_polynomial,
        mvPolynomialCoprojection, MvPolynomial.rename_rename]
      show (tensorPowerEnvelope s f 0).algebraMap.toRingHom (MvPolynomial.rename _ a) = _
      rw [show ((fun i => ((0 : Fin 1), i)) ∘ (Prod.snd : Fin 1 × ι → ι)) =
          (id : Fin 1 × ι → Fin 1 × ι) from
        funext fun q => Prod.ext (Subsingleton.elim _ _) rfl, MvPolynomial.rename_id]
      rfl
  exact congrArg (fun q => q x) h

end Codiagonal

/-! ### The codiagonal of the completed envelopes -/

section Completed

variable (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
  (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (hf : Function.Surjective f)

/-- **The codiagonal `ε_b : D(b) → D`** of the `p`-adically completed divided power envelopes: the
`p`-adic completion of `Crystalline.envelopeCodiagonal`. -/
public noncomputable def completedEnvelopeCodiagonal (b : ℕ) :
    pAdicCompletedTensorPowerEnvelope s f hf b →+* pAdicCompletedDividedPowerEnvelope s f hf :=
  adicCompletionRingMap (envelopeCodiagonal s f b).1.toRingHom (map_pAdicIdeal_le s.p _)

/-- The codiagonal of the completed envelopes forgets the tensor factor of each variable, on the
image of the polynomial algebra. -/
public lemma completedEnvelopeCodiagonal_polynomial (b : ℕ)
    (x : MvPolynomial (Fin (b + 1) × ι) s.A) :
    completedEnvelopeCodiagonal s f hf b (tensorPowerEnvelopeMap s f hf b x) =
      toPAdicCompletedDividedPowerEnvelope s f hf (MvPolynomial.rename Prod.snd x) := by
  show adicCompletionRingMap (envelopeCodiagonal s f b).1.toRingHom _
    (AdicCompletion.of _ _ ((tensorPowerEnvelope s f b).algebraMap.toRingHom x)) = _
  rw [adicCompletionRingMap_of]
  exact congrArg (AdicCompletion.of _ _) (envelopeCodiagonal_polynomial s f b x)

/-- **`ε_n ∘ D(φ) = ε_m` for every map of finite ordinals `φ : ⦋m⦌ ⟶ ⦋n⦌`**: the codiagonals of
the completed envelopes are a retraction of the cosimplicial ring
`Crystalline.cosimplicialEnvelopeRing`.

For a coface `φ = d^i` this is the identity `ε_{b+1} ∘ d^i = ε_b` the proof of
[Stacks, Tag 07LG] uses to see that the `b + 1` maps `D → D(b)` induce the same map on
cohomology. -/
public lemma completedEnvelopeCodiagonal_map {n m : SimplexCategory} (φ : n ⟶ m)
    (x : pAdicCompletedTensorPowerEnvelope s f hf n.len) :
    completedEnvelopeCodiagonal s f hf m.len ((cosimplicialEnvelopeRing s f hf).map φ x) =
      completedEnvelopeCodiagonal s f hf n.len x :=
  (adicCompletionMapₛₗ_comp_apply (ringHomₛₗ (envelopeReindex s f φ).1.toRingHom)
    (ringHomₛₗ (envelopeCodiagonal s f m.len).1.toRingHom)
    (ringHomₛₗ (envelopeCodiagonal s f n.len).1.toRingHom)
    (map_pAdicIdeal_le s.p _) (map_pAdicIdeal_le s.p _) (map_pAdicIdeal_le s.p _)
    (fun y => (envelopeCodiagonal_comp_reindex s f φ y).symm) x).symm

/-- **The `j`-th coprojection `D → D(b)`** of the completed envelopes. -/
public noncomputable def completedEnvelopeCoprojectionRingHom (b : ℕ) (j : Fin (b + 1)) :
    pAdicCompletedDividedPowerEnvelope s f hf →+*
      pAdicCompletedTensorPowerEnvelope s f hf b :=
  adicCompletionRingMap (envelopePolynomialCoprojection s f b j).1.toRingHom
    (map_pAdicIdeal_le s.p _)

/-- **`ε_b` is a retraction of each of the `b + 1` coprojections `D → D(b)`.** -/
public lemma completedEnvelopeCodiagonal_coprojection (b : ℕ) (j : Fin (b + 1))
    (x : pAdicCompletedDividedPowerEnvelope s f hf) :
    completedEnvelopeCodiagonal s f hf b
        (completedEnvelopeCoprojectionRingHom s f hf b j x) = x :=
  ((adicCompletionMapₛₗ_comp_apply
    (ringHomₛₗ (envelopePolynomialCoprojection s f b j).1.toRingHom)
    (ringHomₛₗ (envelopeCodiagonal s f b).1.toRingHom)
    (ringHomₛₗ (RingHom.id _)) (map_pAdicIdeal_le s.p _) (map_pAdicIdeal_le s.p _)
    (map_pAdicIdeal_le s.p _)
    (fun y => (envelopeCodiagonal_comp_coprojection s f b j y).symm) x).symm).trans
    (adicCompletionMapₛₗ_id_apply _ _ (fun _ => rfl) x)

/-- The codiagonal of the completed envelopes is a divided power morphism of the completed
divided power envelopes, not merely a ring homomorphism.  The divided powers of `D` are written
out rather than named: the name `Crystalline.completedEnvelopeDPRing` for them lives in
`StacksFrontier/AlgebraicGeometry/Crystalline/AffineSite/Coproduct.lean`, which this module does not
import, and a second name for one object is what breaks a library. -/
public lemma completedEnvelopeCodiagonal_isDPMorphism (b : ℕ) :
    DividedPowers.IsDPMorphism
      (DividedPowers.completedDividedPowers (tensorPowerEnvelope s f b).object.ideal
        (tensorPowerEnvelope s f b).object.dividedPowers s.p
        (completedTensorPowerDifferential s f hf b).1).1
      (DividedPowers.completedDividedPowers (polynomialDividedPowerEnvelope s f).object.ideal
        (polynomialDividedPowerEnvelope s f).object.dividedPowers s.p
        (completedDividedPowerDifferential s f hf).1).1
      (completedEnvelopeCodiagonal s f hf b) :=
  adicCompletionRingMap_isDPMorphism _ _ s.p
    (completedTensorPowerDifferential s f hf b).1
    (completedDividedPowerDifferential s f hf).1
    (envelopeCodiagonal s f b).1

/-- **The isomorphism `D(0) ≅ D`.**  In degree zero the codiagonal and the unique coprojection are
mutually inverse: the renamings `Prod.snd` and `fun i ↦ (0, i)` are inverse bijections of
`Fin 1 × ι` with `ι`. -/
public noncomputable def zeroEnvelopeRingEquiv :
    pAdicCompletedTensorPowerEnvelope s f hf 0 ≃+*
      pAdicCompletedDividedPowerEnvelope s f hf where
  __ := completedEnvelopeCodiagonal s f hf 0
  invFun := completedEnvelopeCoprojectionRingHom s f hf 0 0
  left_inv x :=
    ((adicCompletionMapₛₗ_comp_apply (ringHomₛₗ (envelopeCodiagonal s f 0).1.toRingHom)
      (ringHomₛₗ (envelopePolynomialCoprojection s f 0 0).1.toRingHom)
      (ringHomₛₗ (RingHom.id _)) (map_pAdicIdeal_le s.p _) (map_pAdicIdeal_le s.p _)
      (map_pAdicIdeal_le s.p _)
      (fun y =>
        (envelopePolynomialCoprojection_comp_envelopeCodiagonal_zero s f y).symm) x).symm).trans
      (adicCompletionMapₛₗ_id_apply _ _ (fun _ => rfl) x)
  right_inv := completedEnvelopeCodiagonal_coprojection s f hf 0 0

end Completed

end Crystalline

end
