module

public import StacksFrontier.Deformation.ArtinianBaseSpecialFiber
public import StacksFrontier.Deformation.Examples.Geometric.CompletionTangentSpace
public import StacksFrontier.Deformation.FlatAlgebraLiftCompletion
public import StacksFrontier.Deformation.FlatModuleLiftBaseChangeAbstract
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Smoothness of the completion functor on deformations

Let `k` be a field, `P` a finite type `k`-algebra which is smooth over `k` outside the zero set
of an ideal `J ⊆ P`, and `P^` the `J`-adic completion. Completion of deformations is a functor
`𝓓_P ⟶ 𝓓_{P^}` over `𝒞_Λ` (**Stacks 0DYV**), and **Stacks 0DZ5** asserts that it is smooth and
induces an isomorphism on tangent spaces. The tangent-space conclusion is
`Deformation.Examples.bijective_differential_adicCompletionFunctorData`. This file supplies the
other input of the criterion of **Stacks 0DYP**, the correspondence of liftability, and
concludes smoothness.

Liftability of a deformation along a morphism of Artinian bases is the same thing as the
existence of a flat algebra lift in the sense of `Deformation.HasFlatAlgebraLift`: an object of
the deformation category over `A` is a flat `A`-algebra `Q` with `k ⊗_A Q = P`, a morphism into
it over `f : B ⟶ A` is a flat `B`-algebra `C` with `A ⊗_B C = Q`, and the structural map to
`(k, P)` of the lift is the composite. That translation is the content of
`Deformation.Examples.hasFlatAlgebraLift_of_flatAlgebraHom` and
`Deformation.Examples.exists_isHomLift_of_hasFlatAlgebraLift`.

With it, the correspondence of liftability is exactly **Stacks 0DZ3** for the ideal
`𝔟 = π⁻¹(J)` of `Q`, where `π : Q → P` is the reduction: the completion of the deformation is
the `𝔟`-adic completion of `Q`, by the fibre identification of the completion functor datum, and
the hypotheses of 0DZ3 hold because `B → A` is a small extension, `Q` is flat and of finite type
over the Artinian base, and `A → Q_h` is syntomic for every `h ∈ 𝔟` — the last by
`Deformation.syntomic_localizationAway_specialFiber`, since `h ∈ 𝔟` means `π(h) ∈ J`, so
`D(π(h))` lies in the smooth locus of `P` over `k`.

Only one implication of Stacks 0DZ3 is wanted, and only at a small extension, whose kernel has
square zero. That is
`Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion_of_sq_zero`, which carries
no hypothesis standing for Stacks 0DZ2: the square-zero case of 0DZ2 in the shape the proof of
0DZ3 consumes is proved in
`StacksFrontier.Deformation.FlatModuleLiftBaseChangeAbstract`.

## Main results

* `Deformation.Examples.isPushout_deformationSpecialFiber`: the reduction square of a
  deformation, read as a base change of algebras.
* `Deformation.Examples.surjective_and_sq_ker_comp_eqToHom` and
  `Deformation.Examples.surjective_and_isNilpotent_ker_comp_eqToHom`: composing with
  identifications of Artinian bases changes neither surjectivity nor squareness, respectively
  nilpotency, of the kernel.
* `Deformation.Examples.lifts_adicCompletionFunctorData_unconditional`: **the correspondence of
  liftability**.
* `Deformation.Examples.isSmooth_adicCompletionFunctorData_unconditional`: **the smoothness
  conclusion of Stacks 0DZ5**, over an arbitrary base-compatible completion functor datum.
* `Deformation.Examples.bijective_differential_adicCompletionFunctor` and
  `Deformation.Examples.isSmooth_adicCompletionFunctor`: the two conclusions of Stacks
  0DZ5, at the completion functor `Deformation.Examples.adicCompletionFunctor` of Stacks
  0DYV.
* `Deformation.Examples.isSmooth_and_bijective_differential_adicCompletionFunctor`: **Stacks
  0DZ5**, both conclusions together.
* `Deformation.Examples.bijective_differential_baseCompatibleAdicCompletionFunctor`: the
  tangent-space conclusion at `Deformation.Examples.baseCompatibleAdicCompletionFunctor`.
* `Deformation.Examples.lifts_adicCompletionFunctorData`,
  `Deformation.Examples.isSmooth_adicCompletionFunctorData` and
  `Deformation.Examples.isSmooth_baseCompatibleAdicCompletionFunctor`: the earlier shapes of
  the same results, each taking a hypothesis `h0DZ2` it no longer needs, retained for
  developments stated against them and carrying no Stacks attribute.

The tag `@[stacks 0DZ5]` is carried by
`Deformation.Examples.isSmooth_and_bijective_differential_adicCompletionFunctor`, which states
both conclusions together at `Deformation.Examples.adicCompletionFunctor`.

## Implementation notes

**No registration in this file carries a hypothesis standing for Stacks 0DZ2, and none of them
is vacuous.** The distinction has to be made, because the ∀-quantified form of 0DZ2 is false:
`Deformation.FlatModuleLiftBaseChangeStatement` — Stacks 0DZ2 at the source's hypotheses,
restricted to a finite module — is refuted by
`StacksFrontier.Deformation.Examples.Linear.NodalArtinSchreierLift`, whose counterexample module is
finite and cyclic. So a proof of Stacks 0DZ5 may not route through the conditional implications
of Stacks 0DZ3 in `StacksFrontier.Deformation.FlatAlgebraLiftCompletion`, whose `h0DZ2` that
refutation kills; the unconditional 0DZ3 is
`Deformation.hasFlatAlgebraLift_iff_hasFlatAlgebraLift_adicCompletion`.

It does not route through it. As the discussion above records,
`Deformation.Examples.lifts_adicCompletionFunctorData_unconditional` needs 0DZ3 only at a small
extension, whose kernel has square zero, and there 0DZ2 is a theorem rather than a hypothesis:
the proof applies
`Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion_of_sq_zero`
(`StacksFrontier.Deformation.FlatModuleLiftBaseChangeAbstract`), which takes no such binder,
having discharged it by `Deformation.flatModuleLiftBaseChangeStatementAt_of_sq_zero`.
`Deformation.Examples.isSmooth_adicCompletionFunctorData_unconditional` inherits that, being
assembled from it and from the differential. Both conclusions of Stacks 0DZ5 are therefore
established at the source's own hypotheses, and they are registered together on
`Deformation.Examples.isSmooth_and_bijective_differential_adicCompletionFunctor`.

Three declarations here do still take `h0DZ2` —
`Deformation.Examples.lifts_adicCompletionFunctorData`,
`Deformation.Examples.isSmooth_adicCompletionFunctorData` and
`Deformation.Examples.isSmooth_baseCompatibleAdicCompletionFunctor`. They are the earlier shapes
of the results above, kept so that developments stated against them continue to typecheck, and
each is now a thin wrapper that discards the hypothesis. None of them carries a Stacks
attribute, precisely because a theorem taking a refuted hypothesis establishes nothing, and an
attribute is what `tag_grep`, the audit rows and the dashboard read as the tag being formalized.

What the square-zero route leaves open is Stacks 0DZ3 itself at a general nilpotent kernel,
which Stacks 0DZ5 does not need. That gap is recorded where it belongs, in
`StacksFrontier.Deformation.FlatAlgebraLiftCompletion`, together with the analysis of why the
conditional 0DZ3 implications there rest on the refuted `h0DZ2`.

* `Deformation.hasFlatAlgebraLift_of_ringEquiv`: a flat algebra lift transports along
  isomorphisms of the base and of the algebra.
* `Deformation.Examples.hasFlatAlgebraLift_of_flatAlgebraHom`: a base-change morphism of flat
  algebras exhibits the target as a flat lift of the source's base.
* `Deformation.Examples.exists_isHomLift_of_hasFlatAlgebraLift`: a flat algebra lift of a
  deformation gives a morphism of the deformation category lying over the base morphism.


The translation lemmas take the `Algebra` structure on the pair of Artinian bases as an
instance argument together with an equation identifying its structural map with the categorical
morphism, rather than installing it with a `let` inside a statement; a caller then chooses the
structure once and uses it on both sides of the correspondence.

`Deformation.hasFlatAlgebraLift_of_ringEquiv` transports a flat lift along an isomorphism of the
base ring as well as of the algebra. Both are needed: the completion functor sends a deformation
over `A` to one over an object of `𝒞_Λ` that is *equal* to `A` only through the functor's own
compatibility with the projections, and its flat algebra is identified with the adic completion
only through the datum's `fiberEquiv`, which is semilinear for that identification of bases
precisely by `Deformation.Examples.AdicCompletionFunctorData.IsBaseCompatible`.

The two conclusions are recorded at `Deformation.Examples.adicCompletionFunctor`, the
completion functor of Stacks 0DYV, which is chosen from the *subtype* of base-compatible data
and therefore satisfies `Deformation.Examples.isBaseCompatible_adicCompletionFunctor`; so
neither conclusion carries a hypothesis on the functor.

## References

* [Stacks Project, Tag 0DZ5](https://stacks.math.columbia.edu/tag/0DZ5)
* [Stacks Project, Tag 0DZ3](https://stacks.math.columbia.edu/tag/0DZ3)
* [Stacks Project, Tag 0DYP](https://stacks.math.columbia.edu/tag/0DYP)
* [Stacks Project, Tag 0DYV](https://stacks.math.columbia.edu/tag/0DYV)
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u w

namespace Deformation

/-! ### Transport of a flat algebra lift -/

section Transport

variable {A' A B A₂ B₂ : Type u} [CommRing A'] [CommRing A] [CommRing B] [CommRing A₂]
  [CommRing B₂] [Algebra A' A] [Algebra A B] [Algebra A' A₂] [Algebra A₂ B₂]

/-- **A flat algebra lift transports along isomorphisms of the base and of the algebra.** If
`eA : A ≃ A₂` is an isomorphism of `A'`-algebras and `eB : B ≃ B₂` is a ring isomorphism
semilinear for it, then a flat lift of `B` to `A'` over `A` is a flat lift of `B₂` to `A'` over
`A₂`: the same `A'`-algebra works, because `A₂ ⊗_{A'} B' ≅ A ⊗_{A'} B' ≅ B ≅ B₂`. -/
theorem hasFlatAlgebraLift_of_ringEquiv
    (eA : A ≃+* A₂) (heA : ∀ a : A', eA (algebraMap A' A a) = algebraMap A' A₂ a)
    (eB : B ≃+* B₂) (heB : ∀ x : A, eB (algebraMap A B x) = algebraMap A₂ B₂ (eA x))
    (h : HasFlatAlgebraLift A' A B) : HasFlatAlgebraLift A' A₂ B₂ := by
  obtain ⟨C, _, _, hflat, ⟨e⟩⟩ := h
  refine ⟨C, inferInstance, inferInstance, hflat, ⟨?_⟩⟩
  let eA' : A ≃ₐ[A'] A₂ := AlgEquiv.ofRingEquiv heA
  let t : A₂ ⊗[A'] C ≃ₐ[A'] A ⊗[A'] C :=
    Algebra.TensorProduct.congr eA'.symm (AlgEquiv.refl (R := A') (A₁ := C))
  refine AlgEquiv.ofRingEquiv (f := (t.toRingEquiv.trans e.toRingEquiv).trans eB) fun a => ?_
  have h₁ : t (algebraMap A₂ (A₂ ⊗[A'] C) a) = algebraMap A (A ⊗[A'] C) (eA'.symm a) := by
    change t (a ⊗ₜ[A'] (1 : C)) = _
    simp [t]
  change eB (e (t (algebraMap A₂ (A₂ ⊗[A'] C) a))) = algebraMap A₂ B₂ a
  rw [h₁, e.commutes, heB, show eA (eA'.symm a) = a from eA.apply_symm_apply a]

end Transport

namespace Examples

/-! ### Deformations and flat algebra lifts -/

section Bridge

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- A pushout square of `CommRingCat` given by structure maps is a pushout of algebras. -/
private theorem algebra_isPushout_of_isPushout {R S T U : Type w} [CommRing R] [CommRing S]
    [CommRing T] [CommRing U] [Algebra R S] [Algebra R T] [Algebra S U] [Algebra T U]
    [Algebra R U] [IsScalarTower R S U] [IsScalarTower R T U]
    (h : IsPushout (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom (algebraMap R T))
      (CommRingCat.ofHom (algebraMap S U)) (CommRingCat.ofHom (algebraMap T U))) :
    Algebra.IsPushout R T S U :=
  Algebra.IsPushout.symm (CommRingCat.isPushout_iff_isPushout.mp h)

/-- **A base-change morphism of flat algebras exhibits the target's flat algebra as a flat lift
to the source's base.** A morphism `m : Y ⟶ X` of flat algebras over `𝒞_Λ` makes the square of
underlying rings a pushout, i.e. `X.fiber = X.base ⊗_{Y.base} Y.fiber`; so `Y.fiber` is a flat
`Y.base`-algebra lifting `X.fiber`. -/
theorem hasFlatAlgebraLift_of_flatAlgebraHom {Y X : FlatAlgebraCategory.{u, w} Λ k} (m : Y ⟶ X)
    [Algebra (Y.base : Type w) (X.base : Type w)]
    (hm : algebraMap (Y.base : Type w) (X.base : Type w) = m.base.hom.toRingHom) :
    Deformation.HasFlatAlgebraLift (Y.base : Type w) (X.base : Type w) X.fiber := by
  let : Algebra Y.fiber X.fiber := m.map.hom.toAlgebra
  let : Algebra (Y.base : Type w) X.fiber :=
    ((algebraMap (X.base : Type w) X.fiber).comp
      (algebraMap (Y.base : Type w) (X.base : Type w))).toAlgebra
  have : IsScalarTower (Y.base : Type w) (X.base : Type w) X.fiber :=
    IsScalarTower.of_algebraMap_eq' rfl
  have hw : (algebraMap Y.fiber X.fiber).comp (algebraMap (Y.base : Type w) Y.fiber)
      = (algebraMap (X.base : Type w) X.fiber).comp
        (algebraMap (Y.base : Type w) (X.base : Type w)) := by
    rw [hm]
    exact congrArg CommRingCat.Hom.hom m.cartesian.w
  have : IsScalarTower (Y.base : Type w) Y.fiber X.fiber :=
    IsScalarTower.of_algebraMap_eq' hw.symm
  have : Algebra.IsPushout (Y.base : Type w) (X.base : Type w) Y.fiber X.fiber :=
    algebra_isPushout_of_isPushout (by rw [hm]; exact m.cartesian)
  exact ⟨Y.fiber, inferInstance, inferInstance, Y.flat,
    ⟨Algebra.IsPushout.equiv (Y.base : Type w) (X.base : Type w) Y.fiber X.fiber⟩⟩

variable {P : Type w} [CommRing P] [Algebra k P]

/-- **A flat algebra lift of a deformation is a lift in the deformation category.** If the flat
algebra of a deformation `X` of `P` has a flat lift to `B` along `f : B ⟶ X.left.base`, then `X`
admits a morphism from an object of the deformation category lying over `f`: the lift is a flat
`B`-algebra whose base change is the flat algebra of `X`, and its structural map to `(k, P)` is
obtained by composing with that of `X`. -/
theorem exists_isHomLift_of_hasFlatAlgebraLift
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    {B : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : B ⟶ X.left.base)
    [Algebra (B : Type w) (X.left.base : Type w)]
    (hf : algebraMap (B : Type w) (X.left.base : Type w) = f.hom.toRingHom)
    (hl : Deformation.HasFlatAlgebraLift (B : Type w) (X.left.base : Type w) X.left.fiber) :
    ∃ (X' : ringDeformationCategory (Λ := Λ) (k := k) P) (m : X' ⟶ X),
      (ringDeformationProjection Λ k P).IsHomLift f m := by
  obtain ⟨C, _, _, hflat, ⟨e⟩⟩ := hl
  let Y : FlatAlgebraCategory.{u, w} Λ k := { base := B, fiber := C, flat := hflat }
  let mmap : CommRingCat.of C ⟶ CommRingCat.of X.left.fiber :=
    CommRingCat.ofHom (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)
  have hcart : IsPushout (FlatAlgebraCategory.structureMap Y)
      (FlatAlgebraCategory.baseMap (X := Y) (Y := X.left) f) mmap
      (FlatAlgebraCategory.structureMap X.left) := by
    refine ((CommRingCat.isPushout_tensorProduct (B : Type w) (X.left.base : Type w)
      C).flip).of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
        e.toRingEquiv.toCommRingCatIso (by simp) ?_ ?_ ?_
    · ext b
      simp [hf]
    · ext c
      simp [mmap]
    · ext a
      simpa using e.commutes a
  let m : Y ⟶ X.left := { base := f, map := mmap, cartesian := hcart }
  let X' : ringDeformationCategory (Λ := Λ) (k := k) P := Over.mk (m ≫ X.hom)
  let mm : X' ⟶ X := Over.homMk m rfl
  refine ⟨X', mm, ?_⟩
  refine IsHomLift.of_fac' (ringDeformationProjection Λ k P) f mm rfl rfl ?_
  change m.base = eqToHom rfl ≫ f ≫ eqToHom rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

/-- **The reduction square of a deformation, read as a base change of algebras.** The flat
algebra of a deformation `X` of `P` over an Artinian base `A` satisfies `P = k ⊗_A X.left.fiber`
for the structural map `A → k` of the base-change morphism to `(k, P)`. -/
theorem isPushout_deformationSpecialFiber
    (X : ringDeformationCategory (Λ := Λ) (k := k) P)
    [Algebra (X.left.base : Type w) k] [Algebra X.left.fiber P]
    [Algebra (X.left.base : Type w) P]
    (hb : algebraMap (X.left.base : Type w) k = X.hom.base.hom.toRingHom)
    (hm : algebraMap X.left.fiber P = X.hom.map.hom)
    [IsScalarTower (X.left.base : Type w) k P]
    [IsScalarTower (X.left.base : Type w) X.left.fiber P] :
    Algebra.IsPushout (X.left.base : Type w) k X.left.fiber P := by
  exact algebra_isPushout_of_isPushout (by rw [hb, hm]; exact X.hom.cartesian)

/-- **Pre- and post-composing with identifications of objects of `𝒞_Λ` preserves surjectivity
and squareness of the kernel.** The two outer maps are isomorphisms of carriers, so they change
neither property. -/
theorem surjective_and_sq_ker_comp_eqToHom
    {B A B' A' : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : B ⟶ A) (hB : B' = B) (hA : A = A')
    (hsurj : Function.Surjective f.hom)
    (hsq : RingHom.ker f.hom.toRingHom ^ 2 = ⊥) :
    Function.Surjective (eqToHom hB ≫ f ≫ eqToHom hA).hom ∧
      RingHom.ker (eqToHom hB ≫ f ≫ eqToHom hA).hom.toRingHom ^ 2 = ⊥ := by
  subst hB
  subst hA
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ⟨hsurj, hsq⟩

/-- **Pre- and post-composing with identifications of objects of `𝒞_Λ` preserves surjectivity
and nilpotency of the kernel.** The two outer maps are isomorphisms of carriers, so they change
neither property. -/
theorem surjective_and_isNilpotent_ker_comp_eqToHom
    {B A B' A' : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : B ⟶ A) (hB : B' = B) (hA : A = A')
    (hsurj : Function.Surjective f.hom)
    (hnil : IsNilpotent (RingHom.ker f.hom.toRingHom)) :
    Function.Surjective (eqToHom hB ≫ f ≫ eqToHom hA).hom ∧
      IsNilpotent (RingHom.ker (eqToHom hB ≫ f ≫ eqToHom hA).hom.toRingHom) := by
  subst hB
  subst hA
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact ⟨hsurj, hnil⟩

end Bridge

/-! ### The correspondence of liftability, and smoothness -/

section Smoothness

open InfinitesimalLifting

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  (P : Type w) [CommRing P] [Algebra k P] (J : Ideal P)

/-- **The correspondence of liftability for the completion functor.** This is the second input
of the criterion of **Stacks 0DYP**: a deformation of `P` lifts along a small extension of its
Artinian base whenever its completion does.

Under the translation of `Deformation.Examples.hasFlatAlgebraLift_of_flatAlgebraHom` and
`Deformation.Examples.exists_isHomLift_of_hasFlatAlgebraLift` the assertion is **Stacks 0DZ3**
for the ideal `𝔟 = π⁻¹(J)` of the flat algebra `Q`, `π : Q → P` being the reduction: the flat
algebra of the completed deformation is the `𝔟`-adic completion of `Q`, by the fibre
identification of the datum, which is semilinear over the identification of the two Artinian
bases because the datum is base-compatible. The hypotheses of 0DZ3 hold: `B → A` is surjective
with nilpotent kernel because it is a small extension, `Q` is flat and of finite type over the
Artinian base by `Deformation.finiteType_of_isPushout_specialFiber`, and `A → Q_h` is syntomic
for every `h ∈ 𝔟` by `Deformation.syntomic_localizationAway_specialFiber`. -/
theorem lifts_adicCompletionFunctorData_unconditional [Algebra.FiniteType k P]
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J) (hF : F.IsBaseCompatible)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    ∀ ⦃B A : ArtinianLocalAlgCat.{u, w, w} Λ k⦄ (f : B ⟶ A),
      IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
        ∀ x : (ringDeformationBasedCategory Λ k P).p.Fiber A,
          (∃ (y' : (ringDeformationBasedCategory Λ k (AdicCompletion J P)).obj)
              (g : y' ⟶ F.functor.obj x.1),
            (ringDeformationBasedCategory Λ k (AdicCompletion J P)).p.IsHomLift f g) →
            ∃ (x' : (ringDeformationBasedCategory Λ k P).obj) (h : x' ⟶ x.1),
              (ringDeformationBasedCategory Λ k P).p.IsHomLift f h := by
  intro B A f hsmall x hyp
  obtain ⟨y', g, hg⟩ := hyp
  obtain ⟨X, hXA⟩ := x
  -- the three identifications of Artinian bases in play
  have hXA : X.left.base = A := hXA
  have hdomB : y'.left.base = B :=
    IsHomLift.domain_eq (ringDeformationBasedCategory Λ k (AdicCompletion J P)).p f g
  have hcodA : (F.functor.obj X).left.base = A :=
    IsHomLift.codomain_eq (ringDeformationBasedCategory Λ k (AdicCompletion J P)).p f g
  have hb : (F.functor.obj X).left.base = X.left.base := F.functor.w_obj X
  -- the base map of `g`, and its correction to a map into the base of `X`
  set f₁ : y'.left.base ⟶ (F.functor.obj X).left.base :=
    eqToHom hdomB ≫ f ≫ eqToHom hcodA.symm with hf₁
  set f₂ : y'.left.base ⟶ X.left.base :=
    eqToHom hdomB ≫ f ≫ eqToHom (hcodA.symm.trans hb) with hf₂
  have hf₁₂ : f₁ ≫ eqToHom hb = f₂ := by
    simp only [hf₁, hf₂, Category.assoc, eqToHom_trans]
  have hgb : g.left.base = f₁ :=
    IsHomLift.fac' (ringDeformationBasedCategory Λ k (AdicCompletion J P)).p f g
  let : Algebra ((y'.left.base : Type w)) ((F.functor.obj X).left.base : Type w) :=
    f₁.hom.toRingHom.toAlgebra
  let : Algebra ((y'.left.base : Type w)) ((X.left.base : Type w)) :=
    f₂.hom.toRingHom.toAlgebra
  -- the flat algebra of the completed deformation is a flat lift along the base map of `g`
  have hliftC : Deformation.HasFlatAlgebraLift ((y'.left.base : Type w))
      ((F.functor.obj X).left.base : Type w) (F.functor.obj X).left.fiber :=
    hasFlatAlgebraLift_of_flatAlgebraHom g.left (by
      rw [RingHom.algebraMap_toAlgebra, hgb])
  -- transport it to the adic completion of the flat algebra of `X`
  have hliftA : Deformation.HasFlatAlgebraLift ((y'.left.base : Type w))
      ((X.left.base : Type w))
      (AdicCompletion (J.comap X.hom.map.hom) X.left.fiber) := by
    refine Deformation.hasFlatAlgebraLift_of_ringEquiv
      (ringEquivOfEq hb) (fun a => ?_)
      (F.fiberEquiv X) (fun z => ?_) hliftC
    · rw [← hom_eqToHom_apply, RingHom.algebraMap_toAlgebra,
        RingHom.algebraMap_toAlgebra]
      exact congrArg (fun m : y'.left.base ⟶ X.left.base => m.hom a) hf₁₂
    · rw [hF X z, ← hom_eqToHom_apply]
      rfl
  -- the remaining hypotheses of Stacks 0DZ3
  let : Algebra ((X.left.base : Type w)) k := X.hom.base.hom.toRingHom.toAlgebra
  let : Algebra X.left.fiber P := X.hom.map.hom.toAlgebra
  let : Algebra ((X.left.base : Type w)) P :=
    ((algebraMap k P).comp (algebraMap ((X.left.base : Type w)) k)).toAlgebra
  have : IsScalarTower ((X.left.base : Type w)) k P := IsScalarTower.of_algebraMap_eq' rfl
  have hwX : (algebraMap X.left.fiber P).comp
      (algebraMap ((X.left.base : Type w)) X.left.fiber)
      = (algebraMap k P).comp (algebraMap ((X.left.base : Type w)) k) :=
    congrArg CommRingCat.Hom.hom X.hom.cartesian.w
  have : IsScalarTower ((X.left.base : Type w)) X.left.fiber P :=
    IsScalarTower.of_algebraMap_eq' hwX.symm
  have : Algebra.IsPushout ((X.left.base : Type w)) k X.left.fiber P :=
    isPushout_deformationSpecialFiber X rfl rfl
  have hsurjBase : Function.Surjective (algebraMap ((X.left.base : Type w)) k) :=
    surjective_deformationHomBase P X
  have : Algebra.FiniteType ((X.left.base : Type w)) X.left.fiber :=
    Deformation.finiteType_of_isPushout_specialFiber (P := P) hsurjBase
  obtain ⟨-, -, hsurjf, hker2⟩ := hsmall.isSquareZeroSurjection
  obtain ⟨hsurj₂, hsq₂⟩ :=
    surjective_and_sq_ker_comp_eqToHom f hdomB (hcodA.symm.trans hb) hsurjf hker2
  have hsurjA : Function.Surjective (algebraMap ((y'.left.base : Type w))
      ((X.left.base : Type w))) := by
    rw [RingHom.algebraMap_toAlgebra]
    exact hsurj₂
  have hzeroA : RingHom.ker (algebraMap ((y'.left.base : Type w))
      ((X.left.base : Type w))) ^ 2 = ⊥ := by
    rw [RingHom.algebraMap_toAlgebra]
    exact hsq₂
  have hsyn : ∀ h ∈ J.comap X.hom.map.hom,
      Algebra.Syntomic ((X.left.base : Type w)) (Localization.Away h) := fun h hh =>
    Deformation.syntomic_localizationAway_specialFiber (P := P) hsurjBase J hsm h hh
  -- Stacks 0DZ3, read backwards
  have hliftQ : Deformation.HasFlatAlgebraLift ((y'.left.base : Type w))
      ((X.left.base : Type w)) X.left.fiber :=
    Deformation.hasFlatAlgebraLift_of_hasFlatAlgebraLift_adicCompletion_of_sq_zero
      ((y'.left.base : Type w)) ((X.left.base : Type w)) X.left.fiber hsurjA hzeroA
      (J.comap X.hom.map.hom) hsyn hliftA
  -- translate back into the deformation category
  obtain ⟨X', mm, hmm⟩ := exists_isHomLift_of_hasFlatAlgebraLift X f₂
    (RingHom.algebraMap_toAlgebra _) hliftQ
  refine ⟨X', mm, ?_⟩
  have hinst : (ringDeformationProjection Λ k P).IsHomLift f₂ mm := hmm
  have h1 : (ringDeformationProjection Λ k P).IsHomLift (f₂ ≫ eqToHom hXA) mm :=
    IsHomLift.lift_comp_eqToHom (ringDeformationProjection Λ k P) f₂ mm hXA
  have h2 : (ringDeformationProjection Λ k P).IsHomLift
      (eqToHom hdomB.symm ≫ f₂ ≫ eqToHom hXA) mm :=
    IsHomLift.lift_eqToHom_comp (ringDeformationProjection Λ k P) (f₂ ≫ eqToHom hXA) mm
      hdomB.symm
  have heq : eqToHom hdomB.symm ≫ f₂ ≫ eqToHom hXA = f := by
    simp only [hf₂, Category.assoc, eqToHom_trans, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp, Category.comp_id]
  exact heq ▸ h2

/-- **Stacks 0DZ5, the smoothness conclusion.** Let `k` be a field, `P` a finite type
`k`-algebra, `J ⊆ P` an ideal such that `Spec(P) → Spec(k)` is smooth outside `V(J)`, and `P^`
the `J`-adic completion. The completion functor `𝓓_P ⟶ 𝓓_{P^}` of **Stacks 0DYV** is smooth.

The criterion of **Stacks 0DYP** reduces this to surjectivity of the differential, which is
`Deformation.Examples.bijective_differential_adicCompletionFunctorData`, and to the
correspondence of liftability, which is
`Deformation.Examples.lifts_adicCompletionFunctorData_unconditional`. -/
@[sga "7 VI 4.13" "(a), special case"]
theorem isSmooth_adicCompletionFunctorData_unconditional [Algebra.FiniteType k P]
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J) (hF : F.IsBaseCompatible)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    IsSmooth F.functor :=
  isSmooth_adicCompletionFunctorData_of_lifts P J F hF hsm
    (lifts_adicCompletionFunctorData_unconditional P J F hF hsm)

/-! ### The earlier forms that carried Stacks 0DZ2 as a hypothesis

The two declarations below are the earlier shapes of the two above, each taking
`h0DZ2 : Deformation.FlatModuleLiftBaseChangeStatement.{w}` — Stacks 0DZ2 at the source's
hypotheses restricted to a finite module. They are retained unchanged, as thin wrappers that
discard `h0DZ2`, because other developments are stated against them. Neither carries a Stacks
attribute: `h0DZ2` is refuted (see the implementation notes above), so a theorem taking it
establishes nothing, and the tag belongs on the unconditional forms. -/

/-- **The correspondence of liftability for the completion functor, in the form that carries
Stacks 0DZ2.** This is
`Deformation.Examples.lifts_adicCompletionFunctorData_unconditional` with an unused hypothesis
`_h0DZ2` in front; the conclusion no longer needs it, because only the square-zero case of
Stacks 0DZ3 is consumed and that case is a theorem. -/
theorem lifts_adicCompletionFunctorData [Algebra.FiniteType k P]
    (_h0DZ2 : Deformation.FlatModuleLiftBaseChangeStatement.{w})
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J) (hF : F.IsBaseCompatible)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    ∀ ⦃B A : ArtinianLocalAlgCat.{u, w, w} Λ k⦄ (f : B ⟶ A),
      IsSmallExtension (CommRingCat.ofHom f.hom.toRingHom) →
        ∀ x : (ringDeformationBasedCategory Λ k P).p.Fiber A,
          (∃ (y' : (ringDeformationBasedCategory Λ k (AdicCompletion J P)).obj)
              (g : y' ⟶ F.functor.obj x.1),
            (ringDeformationBasedCategory Λ k (AdicCompletion J P)).p.IsHomLift f g) →
            ∃ (x' : (ringDeformationBasedCategory Λ k P).obj) (h : x' ⟶ x.1),
              (ringDeformationBasedCategory Λ k P).p.IsHomLift f h :=
  lifts_adicCompletionFunctorData_unconditional P J F hF hsm

/-- **Stacks 0DZ5, the smoothness conclusion, in the form that carries Stacks 0DZ2.** This is
`Deformation.Examples.isSmooth_adicCompletionFunctorData_unconditional` with an unused
hypothesis `_h0DZ2` in front. -/
theorem isSmooth_adicCompletionFunctorData [Algebra.FiniteType k P]
    (_h0DZ2 : Deformation.FlatModuleLiftBaseChangeStatement.{w})
    (F : AdicCompletionFunctorData (Λ := Λ) (k := k) P J) (hF : F.IsBaseCompatible)
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    IsSmooth F.functor :=
  isSmooth_adicCompletionFunctorData_unconditional P J F hF hsm

/-! ### The two conclusions at the completion functor -/

/-- **Stacks 0DZ5, the tangent-space conclusion.** This is
`Deformation.Examples.bijective_differential_adicCompletionFunctorData` specialized to the
completion functor `Deformation.Examples.adicCompletionFunctor` of **Stacks 0DYV**, whose
base-compatibility is `Deformation.Examples.isBaseCompatible_adicCompletionFunctor`; so no
hypothesis on the functor remains. -/
theorem bijective_differential_adicCompletionFunctor [Algebra.FiniteType k P]
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    letI : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
    Function.Bijective (differential (𝓕 := ringDeformationBasedCategory Λ k P)
      (𝓖 := ringDeformationBasedCategory Λ k (AdicCompletion J P))
      isCofiberedInGroupoids_ringDeformationProjection
      isCofiberedInGroupoids_ringDeformationProjection
      (adicCompletionFunctor (Λ := Λ) (k := k) P J).functor) :=
  let : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  bijective_differential_adicCompletionFunctorData P J
    (adicCompletionFunctor (Λ := Λ) (k := k) P J)
    (isBaseCompatible_adicCompletionFunctor P J) hsm

/-- **Stacks 0DZ5, the smoothness conclusion.** This is
`Deformation.Examples.isSmooth_adicCompletionFunctorData_unconditional` specialized to the
completion functor `Deformation.Examples.adicCompletionFunctor` of **Stacks 0DYV**, whose
base-compatibility is `Deformation.Examples.isBaseCompatible_adicCompletionFunctor`; so no
hypothesis on the functor remains. -/
theorem isSmooth_adicCompletionFunctor [Algebra.FiniteType k P]
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    letI : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
    IsSmooth (adicCompletionFunctor (Λ := Λ) (k := k) P J).functor :=
  let : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  isSmooth_adicCompletionFunctorData_unconditional P J
    (adicCompletionFunctor (Λ := Λ) (k := k) P J)
    (isBaseCompatible_adicCompletionFunctor P J) hsm

/-- **Stacks 0DZ5.** Let `k` be a field, `P` a finite type `k`-algebra, `J ⊆ P` an ideal such
that `Spec(P) → Spec(k)` is smooth on the complement of `V(J)`, and `P^` the `J`-adic
completion. Then the completion functor `𝓓_P ⟶ 𝓓_{P^}` of **Stacks 0DYV**
(`Deformation.Examples.adicCompletionFunctor`) is smooth and induces an isomorphism on tangent
spaces.

As in the source, this is the criterion of **Stacks 0DYP** applied to the two inputs: the
isomorphism on tangent spaces, from **Stacks 0DZ4** with `N = B`
(`Deformation.Examples.bijective_differential_adicCompletionFunctor`), and the correspondence of
liftability, from **Stacks 0DZ3** at a small extension
(`Deformation.Examples.lifts_adicCompletionFunctorData_unconditional`), which together give
smoothness (`Deformation.Examples.isSmooth_adicCompletionFunctor`). -/
@[stacks 0DZ5 "both conclusions, at the completion functor \
`Deformation.Examples.adicCompletionFunctor` of Stacks 0DYV: it is smooth, and its differential \
on tangent spaces is bijective. The hypotheses are the source's: `P` of finite type over the \
field `k`, and `P` smooth over `k` at every prime not containing `J`"]
theorem isSmooth_and_bijective_differential_adicCompletionFunctor [Algebra.FiniteType k P]
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    letI : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
    IsSmooth (adicCompletionFunctor (Λ := Λ) (k := k) P J).functor ∧
      Function.Bijective (differential (𝓕 := ringDeformationBasedCategory Λ k P)
        (𝓖 := ringDeformationBasedCategory Λ k (AdicCompletion J P))
        isCofiberedInGroupoids_ringDeformationProjection
        isCofiberedInGroupoids_ringDeformationProjection
        (adicCompletionFunctor (Λ := Λ) (k := k) P J).functor) :=
  ⟨isSmooth_adicCompletionFunctor P J hsm, bijective_differential_adicCompletionFunctor P J hsm⟩

/-! ### The two conclusions at the canonical base-compatible completion functor

The two declarations below state the same two conclusions at
`Deformation.Examples.baseCompatibleAdicCompletionFunctor`, the canonical datum whose
base-compatibility is its own second component. They are retained unchanged because other
developments are stated against them.

Neither carries a Stacks attribute; the tag is on
`Deformation.Examples.isSmooth_and_bijective_differential_adicCompletionFunctor`. The second
still takes `h0DZ2`, which is refuted, and does not use it. -/

/-- **Stacks 0DZ5, the tangent-space conclusion, at the canonical base-compatible completion
functor.** This is `Deformation.Examples.bijective_differential_adicCompletionFunctorData`
specialized to `Deformation.Examples.baseCompatibleAdicCompletionFunctor`, whose
base-compatibility is its own second component; so no hypothesis on the functor remains. -/
theorem bijective_differential_baseCompatibleAdicCompletionFunctor
    [Algebra.FiniteType k P] [IsNoetherianRing P]
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    Function.Bijective (differential (𝓕 := ringDeformationBasedCategory Λ k P)
      (𝓖 := ringDeformationBasedCategory Λ k (AdicCompletion J P))
      isCofiberedInGroupoids_ringDeformationProjection
      isCofiberedInGroupoids_ringDeformationProjection
      (baseCompatibleAdicCompletionFunctor (Λ := Λ) (k := k) P J).1.functor) :=
  bijective_differential_adicCompletionFunctorData P J
    (baseCompatibleAdicCompletionFunctor (Λ := Λ) (k := k) P J).1
    (baseCompatibleAdicCompletionFunctor (Λ := Λ) (k := k) P J).2 hsm

/-- **Stacks 0DZ5, the smoothness conclusion, at the canonical base-compatible completion
functor.** This is `Deformation.Examples.isSmooth_adicCompletionFunctorData` specialized to
`Deformation.Examples.baseCompatibleAdicCompletionFunctor`, whose base-compatibility is its own
second component; so no hypothesis on the functor remains.

The hypothesis `h0DZ2` is inherited from the shape of
`Deformation.Examples.isSmooth_adicCompletionFunctorData` that this specializes, and is not
needed: the unconditional form is
`Deformation.Examples.isSmooth_adicCompletionFunctorData_unconditional`. -/
theorem isSmooth_baseCompatibleAdicCompletionFunctor
    [Algebra.FiniteType k P] [IsNoetherianRing P]
    (h0DZ2 : Deformation.FlatModuleLiftBaseChangeStatement.{w})
    (hsm : ∀ q : PrimeSpectrum P, ¬ J ≤ q.asIdeal → Algebra.IsSmoothAt k q.asIdeal) :
    IsSmooth (baseCompatibleAdicCompletionFunctor (Λ := Λ) (k := k) P J).1.functor :=
  isSmooth_adicCompletionFunctorData P J h0DZ2
    (baseCompatibleAdicCompletionFunctor (Λ := Λ) (k := k) P J).1
    (baseCompatibleAdicCompletionFunctor (Λ := Λ) (k := k) P J).2 hsm

end Smoothness

end Examples

end Deformation

end
