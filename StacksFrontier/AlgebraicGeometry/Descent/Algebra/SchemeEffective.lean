module

public import StacksFrontier.AlgebraicGeometry.Descent.Algebra.Effective
public import StacksFrontier.AlgebraicGeometry.Descent.Algebra.SpecProduct
public import StacksFrontier.AlgebraicGeometry.Descent.Scheme.EffectiveCriterion

/-!
# Effective descent of affine schemes along a faithfully flat map of affines

This is the affine case of Stacks 0245 at the level of schemes.  Let `R → A` be a faithfully
flat ring map, let `B` be an `A`-algebra and let `θ : B ⊗[R] A ≃ₐ[R] A ⊗[R] B` be a transition
isomorphism over `A ⊗[R] A`.  The spectra of these rings carry a descent datum of schemes
relative to `Spec A ⟶ Spec R`, and that descent datum is effective: it is the canonical descent
datum of `Spec C`, where `C` is the subalgebra of elements of `B` fixed by `θ`.

## Main definitions

* `Stacks.SchemeDescent.srcIso` and `Stacks.SchemeDescent.tgtIso` identify
  `Spec B ×_{Spec R} Spec A` with `Spec (B ⊗[R] A)` and `Spec A ×_{Spec R} Spec B` with
  `Spec (A ⊗[R] B)`.
* `Stacks.SchemeDescent.transitionIso` is the isomorphism
  `Spec B ×_{Spec R} Spec A ≅ Spec A ×_{Spec R} Spec B` attached to `θ`.
* `Stacks.SchemeDescent.pushIso` identifies `Spec B` viewed over `Spec R` through `Spec A` with
  `Spec B` viewed over `Spec R` directly.
* `Stacks.SchemeDescent.gluingOfTransition` is `transitionIso` read over
  `Spec A ×_{Spec R} Spec A`, which is the gluing isomorphism of a descent datum.
* `Stacks.SchemeDescent.descentDataOfTransition` is the descent datum of schemes it belongs to.

## Main results

* `Stacks.SchemeDescent.transitionIso_hom_fst` and
  `Stacks.SchemeDescent.transitionIso_hom_snd` say that `transitionIso` is a morphism over
  `Spec A ×_{Spec R} Spec A`; they are the geometric content of the hypotheses `hleft` and
  `hright` on `θ`.
* `Stacks.SchemeDescent.transitionIso_invariant`: the morphism to `Spec C` cut out by a
  subalgebra of `θ`-invariants is invariant under `transitionIso`.
* `Stacks.SchemeDescent.isPullback_specOverMap_of_tensorEquiv`: if `C ⊗[R] A ≅ B` over `A`, then
  `Spec B` is the fibre product of `Spec C` and `Spec A` over `Spec R`.
* `Stacks.SchemeDescent.isEffective_of_transition`: **a descent datum of schemes relative to a
  faithfully flat morphism of affines whose gluing isomorphism comes from an algebra transition
  satisfying the cocycle condition is effective.**
* `Stacks.SchemeDescent.isEffective_descentDataOfTransition` is the same statement for the datum
  built here from the transition.
* `Stacks.SchemeDescent.cocycle_of_transition` reduces the cocycle condition on the triple
  product to a single equation: two of its three components are the two base components of
  `transitionIso`, and the third says that the two ways of carrying the `Spec B`-component across
  the triple product agree.
* `Stacks.SchemeDescent.transitionIso_hom_snd_eq_fst` and
  `Stacks.SchemeDescent.cocycle_component_of_snd_eq_fst` discharge that remaining equation when
  `θ (b ⊗ 1) = 1 ⊗ b`.
* `Stacks.SchemeDescent.isEffective_descentDataOfTrivialTransition` discharges *every* hypothesis
  of the producing theorem at once, for the identity covering `Spec R ⟶ Spec R`, an arbitrary
  `R`-algebra `B` and the canonical transition `B ⊗[R] R ≅ R ⊗[R] B`.  That is what shows the
  producing theorem is not vacuous.  It uses the trivial covering; the corresponding witness for
  a non-trivial faithfully flat `R → A` is `B := A ⊗[R] C`, whose remaining cocycle component is
  not the degenerate one and needs the identification described under Scope.

## Scope

The cocycle condition is used in the ring-theoretic form
`cocycle12 θ ∘ cocycle01 θ = cocycle02 θ` of `Stacks.AlgebraDescent`, and it is a hypothesis
separate from the cocycle condition that the descent datum carries on the triple product
`Spec B ×_{Spec R} Spec A ×_{Spec R} Spec A`.  The two are equivalent — the triple product is
the spectrum of `(B ⊗[R] A) ⊗[R] A`, and the three morphisms of the triangle are `Spec` of the
three maps `cocycle01`, `cocycle12`, `cocycle02` of the inverse transition — but that
identification is not carried out here, so the scheme-level cocycle condition is not used to
produce the ring-level one.  What is proved is therefore the implication from the ring-level
cocycle condition, which is exactly the form in which
`Stacks.AlgebraDescent.exists_subalgebra_tensorEquiv_of_faithfullyFlat` consumes it.  The
scheme-level condition has however been cut down to one equation, by
`Stacks.SchemeDescent.cocycle_of_transition`, and that equation is the whole of what the missing
identification has to supply.

## Implementation notes

The descended scheme is the relative spectrum of the descended algebra, which over an affine
base is `Spec C` for `C` the invariant subalgebra
`Stacks.AlgebraDescent.invariantSubalgebra`; that `A ⊗[R] C → B` is an isomorphism is
`Stacks.AlgebraDescent.exists_subalgebra_tensorEquiv_of_faithfullyFlat`, the
ring-theoretic form of the affine case, whose own input is effective descent for modules along a
universally injective ring map (Stacks 08XA).

Effectivity is obtained from `AlgebraicGeometry.DescentData.isEffective_of_isPullback_prod`,
which asks for the descended scheme `U`, a morphism `φ` exhibiting the underlying scheme as
`X ×_S U`, and the invariance of `φ` under the gluing isomorphism.  Here `φ` is `Spec` of the
inclusion `C → B`; that the square is a fibre product is `Spec` of the isomorphism
`C ⊗[R] A ≅ B`, and the invariance is, after `AlgebraicGeometry.specOverMap_injective`,
precisely the defining property `θ (c ⊗ 1) = 1 ⊗ c` of the invariant subalgebra.

All computations with products go through `AlgebraicGeometry.specOverProdIso`: a morphism
between spectra of `R`-algebras over `Spec R` is `Spec` of an algebra map, and two such are
equal as soon as the algebra maps are.

Two points of elaboration, both about where the concrete object `Spec B ⟶ Spec A ⟶ Spec R`
may appear.

First, that composite is not syntactically the structure morphism of `B` as an `R`-algebra, only
equal to it.  `Stacks.SchemeDescent.pushIso` is the resulting identification; it is the identity
on the underlying scheme.

Second, and the reason the first half of this file quantifies over an arbitrary object `W` of
`Over (Spec R)` with an isomorphism `e : W ≅ Spec B` rather than using `pushIso` directly: with
`W` instantiated to that concrete object, deciding an equation between two separately elaborated
copies of a composite of canonical isomorphisms of `W ⨯ Spec A` exhausts the kernel's budget,
because the `CategoryTheory.Limits.HasBinaryProduct` instances for the concrete object have to be
compared.  With `W` a variable the same equations are decided syntactically.  So every
computation is carried out for a variable `W` and instantiated only once, at `pushIso`, where no
further unfolding is required.

## References

* [Stacks Project, Tag 0245](https://stacks.math.columbia.edu/tag/0245)
* [Stacks Project, Tag 023Z](https://stacks.math.columbia.edu/tag/023Z)
-/

@[expose] public section

noncomputable section

universe u

namespace Stacks.SchemeDescent

open CategoryTheory CategoryTheory.Limits TensorProduct CommRingCat AlgebraicGeometry

/-! ### The transition isomorphism of an algebra transition -/

section Abstract

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
  {W : Over (Spec (.of R))} (e : W ≅ specOver R B)
  (A : Type u) [CommRing A] [Algebra R A]

/-- `Spec B ×_{Spec R} Spec A`, identified with `Spec (B ⊗[R] A)`. -/
def srcIso : (W ⨯ specOver R A) ≅ specOver R (B ⊗[R] A) :=
  prod.mapIso e (Iso.refl (specOver R A)) ≪≫ specOverProdIso R B A

/-- `Spec A ×_{Spec R} Spec B`, identified with `Spec (A ⊗[R] B)`. -/
def tgtIso : (specOver R A ⨯ W) ≅ specOver R (A ⊗[R] B) :=
  prod.mapIso (Iso.refl (specOver R A)) e ≪≫ specOverProdIso R A B

/-- The first projection of `W ⨯ Spec A`, read through `Stacks.SchemeDescent.srcIso`, is `Spec`
of the left inclusion `B → B ⊗[R] A` followed by `e.inv`. -/
lemma srcIso_inv_fst :
    (srcIso e A).inv ≫ prod.fst =
      specOverMap (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := B) (B := A)) ≫
        e.inv := by
  rw [srcIso, Iso.trans_inv, Category.assoc, prod.mapIso_inv, Iso.refl_inv, prod.map_fst,
    ← Category.assoc, specOverProdIso_inv_fst]

/-- The second projection of `W ⨯ Spec A`, read through `Stacks.SchemeDescent.srcIso`, is `Spec`
of the right inclusion `A → B ⊗[R] A`. -/
lemma srcIso_inv_snd :
    (srcIso e A).inv ≫ prod.snd =
      specOverMap (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := A)) := by
  rw [srcIso, Iso.trans_inv, Category.assoc, prod.mapIso_inv, Iso.refl_inv, prod.map_snd,
    Category.comp_id, specOverProdIso_inv_snd]

/-- The first projection of `Spec A ⨯ W`, read through `Stacks.SchemeDescent.tgtIso`, is `Spec`
of the left inclusion `A → A ⊗[R] B`. -/
lemma tgtIso_inv_fst :
    (tgtIso e A).inv ≫ prod.fst =
      specOverMap (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := B)) := by
  rw [tgtIso, Iso.trans_inv, Category.assoc, prod.mapIso_inv, Iso.refl_inv, prod.map_fst,
    Category.comp_id, specOverProdIso_inv_fst]

/-- The second projection of `Spec A ⨯ W`, read through `Stacks.SchemeDescent.tgtIso`, is `Spec`
of the right inclusion `B → A ⊗[R] B` followed by `e.inv`. -/
lemma tgtIso_inv_snd :
    (tgtIso e A).inv ≫ prod.snd =
      specOverMap (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B)) ≫ e.inv := by
  rw [tgtIso, Iso.trans_inv, Category.assoc, prod.mapIso_inv, Iso.refl_inv, prod.map_snd,
    ← Category.assoc, specOverProdIso_inv_snd]

variable (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))

/-- The isomorphism `Spec B ×_{Spec R} Spec A ≅ Spec A ×_{Spec R} Spec B` attached to an algebra
transition `θ`. -/
def transitionIso : (W ⨯ specOver R A) ≅ (specOver R A ⨯ W) :=
  srcIso e A ≪≫ specOverMapIso θ.symm ≪≫ (tgtIso e A).symm

/-- Read through `Stacks.SchemeDescent.srcIso` and `Stacks.SchemeDescent.tgtIso`, the transition
isomorphism is `Spec` of `θ.symm`. -/
lemma srcIso_inv_transitionIso_hom :
    (srcIso e A).inv ≫ (transitionIso e A θ).hom =
      specOverMap θ.symm.toAlgHom ≫ (tgtIso e A).inv := by
  rw [transitionIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom, specOverMapIso_hom,
    Iso.inv_hom_id_assoc]

/-- The `W`-component of the transition isomorphism, read through `Stacks.SchemeDescent.srcIso`,
is `Spec` of `θ.symm` composed with the right inclusion, followed by `e.inv`. -/
private lemma srcIso_inv_transitionIso_hom_snd :
    (srcIso e A).inv ≫ (transitionIso e A θ).hom ≫ prod.snd =
      specOverMap (θ.symm.toAlgHom.comp
        (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := B))) ≫ e.inv := by
  rw [← Category.assoc, srcIso_inv_transitionIso_hom, Category.assoc, tgtIso_inv_snd,
    ← Category.assoc, specOverMap_comp]

variable {A} (σ : W ⟶ specOver R A) (p : A →ₐ[R] B)
  (he : e.inv ≫ σ = specOverMap p)

include he in
/-- The transition isomorphism preserves the first base component: the geometric form of the
hypothesis that `θ` is a morphism over the first factor of `A ⊗[R] A`. -/
lemma transitionIso_hom_fst
    (hleft : ∀ a : A, θ (p a ⊗ₜ[R] (1 : A)) = a ⊗ₜ[R] (1 : B)) :
    (transitionIso e A θ).hom ≫ prod.fst = prod.fst ≫ σ := by
  have hL : (srcIso e A).inv ≫ (transitionIso e A θ).hom ≫ prod.fst =
      specOverMap (θ.symm.toAlgHom.comp
        (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := A) (B := B))) := by
    rw [← Category.assoc, srcIso_inv_transitionIso_hom, Category.assoc, tgtIso_inv_fst,
      specOverMap_comp]
  have hR : (srcIso e A).inv ≫ prod.fst ≫ σ =
      specOverMap ((Algebra.TensorProduct.includeLeft
        (R := R) (S := R) (A := B) (B := A)).comp p) := by
    rw [← Category.assoc, srcIso_inv_fst, Category.assoc, he, specOverMap_comp]
  rw [← cancel_epi (srcIso e A).inv, hL, hR]
  refine congrArg specOverMap (AlgHom.ext fun a ↦ ?_)
  simpa using θ.symm_apply_eq.2 (hleft a).symm

include he in
/-- The transition isomorphism preserves the second base component: the geometric form of the
hypothesis that `θ` is a morphism over the second factor of `A ⊗[R] A`. -/
lemma transitionIso_hom_snd
    (hright : ∀ a : A, θ ((1 : B) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] p a) :
    (transitionIso e A θ).hom ≫ prod.snd ≫ σ = prod.snd := by
  rw [← cancel_epi (srcIso e A).inv, reassoc_of% (srcIso_inv_transitionIso_hom_snd e _ θ), he,
    srcIso_inv_snd]
  simp only [specOverMap_comp]
  refine congrArg specOverMap (AlgHom.ext fun a ↦ ?_)
  simpa using θ.symm_apply_eq.2 (hright a).symm

include he in
/-- **The cocycle condition for the gluing isomorphism attached to `θ` reduces to one
equation.**  Two of the three components of the triangle on the triple product hold for formal
reasons — they are the two base components of `transitionIso` — and the third is the displayed
equation, which says that the two ways of carrying the `W`-component across the triple product
agree. -/
lemma cocycle_of_transition
    (hleft : ∀ a : A, θ (p a ⊗ₜ[R] (1 : A)) = a ⊗ₜ[R] (1 : B))
    (hright : ∀ a : A, θ ((1 : B) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] p a)
    (h₃ : prod.lift (prod.fst ≫ (transitionIso e A θ).hom ≫ prod.snd) prod.snd ≫
          (transitionIso e A θ).hom ≫ prod.snd =
        prod.lift (prod.fst ≫ prod.fst) prod.snd ≫
          (transitionIso e A θ).hom ≫ prod.snd) :
    prod.map (transitionIso e A θ).hom (𝟙 (specOver R A)) ≫
        prodMapLastTwo (transitionIso e A θ).hom =
      prodMapFirstThird (transitionIso e A θ).hom := by
  have hf := transitionIso_hom_fst e θ σ p he hleft
  refine prod.hom_ext (prod.hom_ext ?_ ?_) ?_ <;>
    simp only [prodMapLastTwo, prodMapFirstThird, prod.associator_hom, prod.associator_inv,
      prod.braiding_hom, prod.comp_lift, prod.comp_lift_assoc, prod.lift_fst, prod.lift_snd,
      prod.lift_fst_assoc, prod.lift_snd_assoc, prod.map_fst, prod.map_snd, prod.map_fst_assoc,
      prod.map_snd_assoc, Category.comp_id]
  · rw [hf, prod.lift_fst_assoc, Category.assoc]
  · rw [hf, prod.lift_fst_assoc, Category.assoc, Category.assoc,
      transitionIso_hom_snd e θ σ p he hright]
  · exact h₃

/-- The `W`-component of the transition isomorphism is the first projection exactly when `θ`
carries `b ⊗ 1` to `1 ⊗ b`. -/
lemma transitionIso_hom_snd_eq_fst
    (hflip : ∀ b : B, θ (b ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] b) :
    (transitionIso e A θ).hom ≫ prod.snd = prod.fst := by
  rw [← cancel_epi (srcIso e A).inv, srcIso_inv_transitionIso_hom_snd, srcIso_inv_fst]
  refine congrArg (fun k ↦ k ≫ e.inv) (congrArg specOverMap (AlgHom.ext fun b ↦ ?_))
  simpa using θ.symm_apply_eq.2 (hflip b).symm

/-- A sufficient condition for the remaining cocycle component: that the `W`-component of the
transition isomorphism is the first projection.  This happens exactly when
`θ (b ⊗ 1) = 1 ⊗ b`. -/
lemma cocycle_component_of_snd_eq_fst
    (hβ : (transitionIso e A θ).hom ≫ prod.snd = prod.fst) :
    prod.lift (prod.fst ≫ (transitionIso e A θ).hom ≫ prod.snd) prod.snd ≫
        (transitionIso e A θ).hom ≫ prod.snd =
      prod.lift (prod.fst ≫ prod.fst) prod.snd ≫
        (transitionIso e A θ).hom ≫ prod.snd := by
  rw [hβ, prod.lift_fst]

variable {C : Type u} [CommRing C] [Algebra R C] (q : C →ₐ[R] B)

/-- The morphism to `Spec C` determined by an algebra map `q : C → B` whose image consists of
`θ`-invariant elements is invariant under the transition isomorphism. -/
lemma transitionIso_invariant
    (hq : ∀ c : C, θ (q c ⊗ₜ[R] (1 : A)) = (1 : A) ⊗ₜ[R] q c) :
    (transitionIso e A θ).hom ≫ prod.snd ≫ (e.hom ≫ specOverMap q) =
      prod.fst ≫ (e.hom ≫ specOverMap q) := by
  rw [← cancel_epi (srcIso e A).inv, reassoc_of% (srcIso_inv_transitionIso_hom_snd e _ θ),
    Iso.inv_hom_id_assoc, ← Category.assoc, srcIso_inv_fst, Category.assoc,
    Iso.inv_hom_id_assoc]
  simp only [specOverMap_comp]
  refine congrArg specOverMap (AlgHom.ext fun c ↦ ?_)
  simpa using θ.symm_apply_eq.2 (hq c).symm

end Abstract

/-! ### The affine descent datum and its effectivity -/

section Affine

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- The morphism `Spec A ⟶ Spec R` of an `R`-algebra `A`. -/
abbrev baseMap : Spec (.of A) ⟶ Spec (.of R) := Spec.map (ofHom (algebraMap R A))

/-- `Spec B` as a scheme over `Spec A`. -/
abbrev datumObj : Over (Spec (.of A)) := Over.mk (Spec.map (ofHom (algebraMap A B)))

/-- `Spec B` viewed over `Spec R` through `Spec A`, identified with `Spec B` viewed over
`Spec R` directly.  The underlying morphism of schemes is the identity. -/
def pushIso : (Over.map (baseMap R A)).obj (datumObj A B) ≅ specOver R B :=
  Over.isoMk (Iso.refl _) (by
    dsimp only [specOver, Over.mk_hom, Over.map_obj_hom, Iso.refl_hom]
    rw [Category.id_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact IsScalarTower.algebraMap_apply R A B r)

/-- The underlying morphism of schemes of `Stacks.SchemeDescent.pushIso` is the identity. -/
@[simp]
lemma pushIso_hom_left : (pushIso R A B).hom.left = 𝟙 (Spec (.of B)) := rfl

/-- The underlying morphism of schemes of the inverse of `Stacks.SchemeDescent.pushIso` is the
identity. -/
@[simp]
lemma pushIso_inv_left : (pushIso R A B).inv.left = 𝟙 (Spec (.of B)) := rfl

/-- The structure morphism of the datum, read through `Stacks.SchemeDescent.pushIso`, is `Spec`
of the structure map of `B` as an `A`-algebra. -/
lemma pushIso_inv_structureMap :
    (pushIso R A B).inv ≫ structureMap (baseMap R A) (datumObj A B) =
      specOverMap (IsScalarTower.toAlgHom R A B) := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, pushIso_inv_left, specOverMap_left]
  rfl

/-- If `C ⊗[R] A ≅ B` compatibly with the two structure maps, then `Spec B` is the fibre product
of `Spec C` and `Spec A` over `Spec R`. -/
lemma isPullback_specOverMap_of_tensorEquiv (C : Type u) [CommRing C] [Algebra R C]
    (q : C →ₐ[R] B) (g : (C ⊗[R] A) ≃ₐ[R] B)
    (hgl : ∀ c : C, g (c ⊗ₜ[R] (1 : A)) = q c)
    (hgr : ∀ a : A, g ((1 : C) ⊗ₜ[R] a) = algebraMap A B a) :
    IsPullback (Spec.map (ofHom q.toRingHom)) (Spec.map (ofHom (algebraMap A B)))
      (Spec.map (ofHom (algebraMap R C))) (baseMap R A) := by
  have hsq : Spec.map (ofHom q.toRingHom) ≫ Spec.map (ofHom (algebraMap R C)) =
      Spec.map (ofHom (algebraMap A B)) ≫ baseMap R A := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    exact (q.commutes r).trans (IsScalarTower.algebraMap_apply R A B r)
  let iso : Spec (.of B) ≅ Spec (.of (C ⊗[R] A)) :=
    { hom := Spec.map (ofHom g.toAlgHom.toRingHom)
      inv := Spec.map (ofHom g.symm.toAlgHom.toRingHom)
      hom_inv_id := by
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
        exact CommRingCat.hom_ext (RingHom.ext fun x ↦ g.apply_symm_apply x)
      inv_hom_id := by
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
        exact CommRingCat.hom_ext (RingHom.ext fun x ↦ g.symm_apply_apply x) }
  refine IsPullback.of_iso_pullback ⟨hsq⟩ (iso ≪≫ (pullbackSpecIso R C A).symm) ?_ ?_
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackSpecIso_inv_fst,
      show iso.hom = Spec.map (ofHom g.toAlgHom.toRingHom) from rfl, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun c ↦ hgl c)
  · rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, pullbackSpecIso_inv_snd,
      show iso.hom = Spec.map (ofHom g.toAlgHom.toRingHom) from rfl, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext (RingHom.ext fun a ↦ hgr a)

end Affine

/-! ### The affine producing theorem -/

section Producing

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  {D : DescentData (S := Spec (.of R)) (X := fun _ : Unit ↦ Spec (.of A))
    (fun _ ↦ baseMap R A)}
  (e : (Over.map (baseMap R A)).obj (D.obj ()) ≅ specOver R B)
  (he : e.inv ≫ structureMap (baseMap R A) (D.obj ()) =
    specOverMap (IsScalarTower.toAlgHom R A B))
  (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))
  (hglue : (D.gluing () ()).hom.left = (transitionIso e A θ).hom)

include e he θ hglue in
/-- **The affine case of Stacks 0245.**  Let `R → A` be a faithfully flat ring map and let `D` be
a descent datum of schemes relative to `Spec A ⟶ Spec R` whose underlying scheme is `Spec B` for
an `A`-algebra `B`, and whose gluing isomorphism is the one attached to a transition isomorphism
`θ : B ⊗[R] A ≃ₐ[R] A ⊗[R] B` over `A ⊗[R] A` satisfying the cocycle condition.  Then `D` is
effective: it is the canonical descent datum of a scheme over `Spec R`, namely of the spectrum of
the algebra of `θ`-invariants. -/
theorem isEffective_of_transition [Module.FaithfullyFlat R A]
    (hleft : ∀ a : A, θ (algebraMap A B a ⊗ₜ[R] (1 : A)) = a ⊗ₜ[R] (1 : B))
    (hright : ∀ a : A, θ ((1 : B) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] algebraMap A B a)
    (hcoc : Stacks.AlgebraDescent.cocycle12 R A B θ.toLinearMap ∘ₗ
        Stacks.AlgebraDescent.cocycle01 R A B θ.toLinearMap =
      Stacks.AlgebraDescent.cocycle02 R A B θ.toLinearMap) :
    D.IsEffective := by
  obtain ⟨C, hCmem, g₀, hg₀tmul, -⟩ :=
    Stacks.AlgebraDescent.exists_subalgebra_tensorEquiv_of_faithfullyFlat R A B θ hleft hright hcoc
  have hab : (ofHom (IsScalarTower.toAlgHom R A B).toRingHom :
      CommRingCat.of A ⟶ CommRingCat.of B) = ofHom (algebraMap A B) := rfl
  have hbase : e.inv.left ≫ (D.obj ()).hom = Spec.map (ofHom (algebraMap A B)) := by
    simpa only [Over.comp_left, specOverMap_left, Over.homMk_left, hab] using
      congrArg Over.Hom.left he
  refine DescentData.isEffective_of_isPullback_prod (specOver R C)
    (e.hom.left ≫ Spec.map (ofHom (C.val : C →ₐ[R] B).toRingHom)) ?_ ?_
  · have H := isPullback_specOverMap_of_tensorEquiv R A B C (C.val : C →ₐ[R] B)
      ((Algebra.TensorProduct.comm R C A).trans (g₀.restrictScalars R))
      (fun c ↦ (hg₀tmul 1 c).trans (one_smul A _))
      (fun a ↦ (hg₀tmul a 1).trans ((Algebra.smul_def a (1 : B)).trans (mul_one _)))
    refine H.of_iso ((Over.forget (Spec (.of R))).mapIso e).symm (Iso.refl _) (Iso.refl _)
      (Iso.refl _) ?_ ?_ (by simp) (by simp)
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Functor.mapIso_inv, Over.forget_map,
        ← Category.assoc, ← Over.comp_left, e.inv_hom_id, Over.id_left]
      exact (Category.id_comp _).symm
    · rw [Iso.refl_hom, Category.comp_id, Iso.symm_hom, Functor.mapIso_inv, Over.forget_map]
      exact hbase.symm
  · rw [hglue]
    simpa only [Over.comp_left, specOverMap_left, Category.assoc] using
      congrArg Over.Hom.left (transitionIso_invariant e θ (C.val : C →ₐ[R] B)
        fun c ↦ (hCmem (C.val c)).mp c.2)

end Producing

/-! ### The descent datum attached to an algebra transition -/

section Datum

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  (θ : (B ⊗[R] A) ≃ₐ[R] (A ⊗[R] B))
  (hleft : ∀ a : A, θ (algebraMap A B a ⊗ₜ[R] (1 : A)) = a ⊗ₜ[R] (1 : B))
  (hright : ∀ a : A, θ ((1 : B) ⊗ₜ[R] a) = (1 : A) ⊗ₜ[R] algebraMap A B a)

include hleft hright in
/-- The gluing isomorphism of the descent datum attached to an algebra transition. -/
def gluingOfTransition :
    Over.mk (prod.map (structureMap (baseMap R A) (datumObj A B))
        (𝟙 (Over.mk (baseMap R A)))) ≅
      Over.mk (prod.map (𝟙 (Over.mk (baseMap R A)))
        (structureMap (baseMap R A) (datumObj A B))) :=
  Over.isoMk (transitionIso (pushIso R A B) A θ) (by
    dsimp only [Over.mk_hom]
    apply prod.hom_ext
    · rw [Category.assoc, prod.map_fst, Category.comp_id, prod.map_fst]
      exact transitionIso_hom_fst (pushIso R A B) θ _ _ (pushIso_inv_structureMap R A B) hleft
    · rw [Category.assoc, prod.map_snd, prod.map_snd, Category.comp_id]
      exact transitionIso_hom_snd (pushIso R A B) θ _ _ (pushIso_inv_structureMap R A B) hright)

/-- The underlying morphism of schemes of `Stacks.SchemeDescent.gluingOfTransition` is the
transition isomorphism of `θ`. -/
lemma gluingOfTransition_hom_left :
    (gluingOfTransition R A B θ hleft hright).hom.left =
      (transitionIso (pushIso R A B) A θ).hom := rfl

include hleft hright in
/-- The descent datum of schemes relative to `Spec A ⟶ Spec R` attached to an algebra transition,
given the cocycle condition on the triple product.  By
`Stacks.SchemeDescent.cocycle_of_transition` that condition reduces to a single equation. -/
def descentDataOfTransition
    (hcocycle : prod.map (transitionIso (pushIso R A B) A θ).hom
          (𝟙 (Over.mk (baseMap R A))) ≫
        prodMapLastTwo (transitionIso (pushIso R A B) A θ).hom =
      prodMapFirstThird (transitionIso (pushIso R A B) A θ).hom) :
    DescentData (S := Spec (.of R)) (X := fun _ : Unit ↦ Spec (.of A))
      (fun _ ↦ baseMap R A) where
  obj _ := datumObj A B
  gluing _ _ := gluingOfTransition R A B θ hleft hright
  cocycle _ _ _ := hcocycle

include hleft hright in
/-- **The affine case of Stacks 0245 for the datum attached to a transition.**  The descent datum
of schemes built from an algebra transition `θ` along a faithfully flat ring map `R → A` is
effective. -/
theorem isEffective_descentDataOfTransition [Module.FaithfullyFlat R A]
    (hcoc : Stacks.AlgebraDescent.cocycle12 R A B θ.toLinearMap ∘ₗ
        Stacks.AlgebraDescent.cocycle01 R A B θ.toLinearMap =
      Stacks.AlgebraDescent.cocycle02 R A B θ.toLinearMap)
    (hcocycle : prod.map (transitionIso (pushIso R A B) A θ).hom
          (𝟙 (Over.mk (baseMap R A))) ≫
        prodMapLastTwo (transitionIso (pushIso R A B) A θ).hom =
      prodMapFirstThird (transitionIso (pushIso R A B) A θ).hom) :
    (descentDataOfTransition R A B θ hleft hright hcocycle).IsEffective :=
  isEffective_of_transition (pushIso R A B) (pushIso_inv_structureMap R A B) θ
    (gluingOfTransition_hom_left R A B θ hleft hright) hleft hright hcoc

end Datum

/-! ### The hypotheses are satisfiable -/

section Nonvacuity

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The canonical transition isomorphism for the identity covering `Spec R ⟶ Spec R`. -/
def trivialTransition : (B ⊗[R] R) ≃ₐ[R] (R ⊗[R] B) :=
  (Algebra.TensorProduct.rid R R B).trans (Algebra.TensorProduct.lid R B).symm

/-- `Stacks.SchemeDescent.trivialTransition` sends `b ⊗ r` to `1 ⊗ r • b`. -/
@[simp]
lemma trivialTransition_tmul (b : B) (r : R) :
    trivialTransition R B (b ⊗ₜ[R] r) = (1 : R) ⊗ₜ[R] (r • b) := by
  simp [trivialTransition]

/-- `Stacks.SchemeDescent.trivialTransition` sends `a ⊗ 1` to `a ⊗ 1` for `a ∈ R`. -/
lemma trivialTransition_left (a : R) :
    trivialTransition R B (algebraMap R B a ⊗ₜ[R] (1 : R)) = a ⊗ₜ[R] (1 : B) := by
  rw [trivialTransition_tmul, one_smul, Algebra.algebraMap_eq_smul_one,
    ← TensorProduct.smul_tmul, smul_eq_mul, mul_one]

/-- `Stacks.SchemeDescent.trivialTransition` sends `1 ⊗ a` to `1 ⊗ a` for `a ∈ R`. -/
lemma trivialTransition_right (a : R) :
    trivialTransition R B ((1 : B) ⊗ₜ[R] a) = (1 : R) ⊗ₜ[R] algebraMap R B a := by
  rw [trivialTransition_tmul, Algebra.algebraMap_eq_smul_one]

/-- `Stacks.SchemeDescent.trivialTransition` sends `b ⊗ 1` to `1 ⊗ b`. -/
lemma trivialTransition_flip (b : B) :
    trivialTransition R B (b ⊗ₜ[R] (1 : R)) = (1 : R) ⊗ₜ[R] b := by
  rw [trivialTransition_tmul, one_smul]

/-- `Stacks.SchemeDescent.trivialTransition` satisfies the cocycle condition
`θ₁₂ ∘ θ₀₁ = θ₀₂`. -/
lemma trivialTransition_cocycle :
    Stacks.AlgebraDescent.cocycle12 R R B (trivialTransition R B).toLinearMap ∘ₗ
        Stacks.AlgebraDescent.cocycle01 R R B (trivialTransition R B).toLinearMap =
      Stacks.AlgebraDescent.cocycle02 R R B (trivialTransition R B).toLinearMap := by
  refine TensorProduct.ext' fun q c ↦ ?_
  induction q using TensorProduct.inductionOn with
  | add x y hx hy => rw [add_tmul, map_add, map_add, hx, hy]
  | tmul b a =>
    simp only [Stacks.AlgebraDescent.cocycle01, Stacks.AlgebraDescent.cocycle12,
      Stacks.AlgebraDescent.cocycle02, LinearMap.comp_apply, LinearMap.rTensor_tmul,
      LinearMap.lTensor_tmul, AlgEquiv.toLinearMap_apply, LinearEquiv.coe_coe,
      TensorProduct.assoc_tmul, TensorProduct.assoc_symm_tmul, TensorProduct.rightComm_tmul,
      trivialTransition_tmul]
    rw [show ((1 : R) ⊗ₜ[R] a : R ⊗[R] R) = a • ((1 : R) ⊗ₜ[R] (1 : R)) by
        rw [← TensorProduct.tmul_smul, smul_eq_mul, mul_one],
      TensorProduct.smul_tmul, smul_comm]

/-- The transition isomorphism of `Stacks.SchemeDescent.trivialTransition` satisfies the cocycle
condition on the triple product. -/
lemma trivialTransition_scheme_cocycle :
    prod.map (transitionIso (pushIso R R B) R (trivialTransition R B)).hom
        (𝟙 (Over.mk (baseMap R R))) ≫
      prodMapLastTwo (transitionIso (pushIso R R B) R (trivialTransition R B)).hom =
    prodMapFirstThird (transitionIso (pushIso R R B) R (trivialTransition R B)).hom :=
  cocycle_of_transition (pushIso R R B) (trivialTransition R B) _ _
    (pushIso_inv_structureMap R R B) (trivialTransition_left R B) (trivialTransition_right R B)
    (cocycle_component_of_snd_eq_fst (pushIso R R B) (trivialTransition R B)
      (transitionIso_hom_snd_eq_fst (pushIso R R B) (trivialTransition R B)
        (trivialTransition_flip R B)))

/-- **The hypotheses of `Stacks.SchemeDescent.isEffective_descentDataOfTransition` are
satisfiable, so it is not vacuous.**  They all hold for the identity covering
`Spec R ⟶ Spec R`, an arbitrary `R`-algebra `B` and the canonical transition isomorphism. -/
theorem isEffective_descentDataOfTrivialTransition :
    (descentDataOfTransition R R B (trivialTransition R B) (trivialTransition_left R B)
      (trivialTransition_right R B) (trivialTransition_scheme_cocycle R B)).IsEffective :=
  isEffective_descentDataOfTransition R R B (trivialTransition R B)
    (trivialTransition_left R B) (trivialTransition_right R B) (trivialTransition_cocycle R B)
    (trivialTransition_scheme_cocycle R B)

end Nonvacuity

end Stacks.SchemeDescent

end

end
