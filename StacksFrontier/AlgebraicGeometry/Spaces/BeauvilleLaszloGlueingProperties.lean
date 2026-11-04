module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.BeauvilleLaszlo.AlgebraProperties

/-!
# Properties of morphisms under the Beauville--Laszlo glueing functor (Stacks 0F9R)

Let `(R → R', f)` be a glueing pair and write `X = Spec R`, `U = Spec R_f`, `X' = Spec R'` and
`U' = Spec R'_f`. The glueing functor of Stacks 0F9N sends a scheme `Y` over `X` to the triple
of base changes `(U ×_X Y, U' ×_X Y, X' ×_X Y)`, and a morphism `h : Y → Z` over `X` to the
triple of its base changes. Stacks 0F9Q makes this functor an equivalence between the affine
`Y` over `X` which are glueable for the pair and the triples with affine components, so a
morphism of triples with affine components is the image of a unique morphism `h` of affine
schemes over `X`. Stacks 0F9R says that `h` has `P` exactly when the three components of its
image have `P`, for `P` one of: finite, closed immersion, flat, of finite type, flat and of
finite presentation, étale.

This file proves that statement for every morphism `h : Spec B → Spec A` of affine schemes over
`Spec R`, where `A` is glueable for the pair. The components of its image under the glueing
functor are the base changes `((Over.pullback j).map h).left` along the three morphisms
`j : U → X`, `j : U' → X` and `j : X' → X`.

## Main results

* `BeauvilleLaszlo.morphismProperty_iff_baseChange`: for a property of morphisms of schemes that
  is stable under base change and is read on morphisms of affine schemes as a property of ring
  maps for which the algebra form of the statement holds, a morphism of affine schemes over
  `X` has the property if and only if its three base changes do.
* `BeauvilleLaszlo.isFinite_iff_baseChange`, `BeauvilleLaszlo.isClosedImmersion_iff_baseChange`,
  `BeauvilleLaszlo.flat_iff_baseChange`, `BeauvilleLaszlo.locallyOfFiniteType_iff_baseChange`,
  `BeauvilleLaszlo.flat_and_locallyOfFinitePresentation_iff_baseChange` and
  `BeauvilleLaszlo.etale_iff_baseChange`: a morphism of affine schemes over `X` is finite, a
  closed immersion, flat, of finite type, flat and of finite presentation, or étale if and only
  if its three base changes are.

## Implementation notes

A morphism of schemes over `X` is a morphism of `Over X`, and the base change functor along
`j : T → X` is `Over.pullback j`, so the three components of the image of `h` are the `left`
parts of `(Over.pullback j).map h`.

Glueability of `A` is used for flatness and for the two properties that contain it; glueability
of `B`, which the source also assumes, is used for none of the six properties. The rows for
finiteness and for closed immersions use only the isomorphisms `R/fⁿR → R'/fⁿR'` of the glueing
pair, but are stated for a glueing pair as in the source.

## References

* [Stacks Project, Tag 0F9N](https://stacks.math.columbia.edu/tag/0F9N)
* [Stacks Project, Tag 0F9Q](https://stacks.math.columbia.edu/tag/0F9Q)
* [Stacks Project, Tag 0F9R](https://stacks.math.columbia.edu/tag/0F9R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace BeauvilleLaszlo

variable {R R' A B : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
  [Algebra R R'] [Algebra R A] [Algebra R B]

/-- The `R`-algebra homomorphism `A → B` underlying a morphism `Spec B → Spec A` of schemes over
`Spec R`. -/
noncomputable def overSpecAlgHom
    (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) : A →ₐ[R] B :=
  have hw : CommRingCat.ofHom (algebraMap R A) ≫ Spec.preimage h.left =
      CommRingCat.ofHom (algebraMap R B) :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_preimage]; exact Over.w h)
  { (Spec.preimage h.left).hom with
    commutes' := fun r => by
      simpa using congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of B => k.hom r) hw }

/-- A morphism `Spec B → Spec A` of schemes over `Spec R` is `Spec` of its underlying
`R`-algebra homomorphism. -/
theorem SpecMap_overSpecAlgHom
    (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    Spec.map (CommRingCat.ofHom (overSpecAlgHom h).toRingHom) = h.left := by
  change Spec.map (CommRingCat.ofHom (Spec.preimage h.left).hom) = h.left
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

/-- The base change of a morphism `Spec φ : Spec B → Spec A` of schemes over `Spec R` along
`Spec C → Spec R` has a property `P` respecting isomorphisms exactly when `Spec (φ ⊗ C)` has
it. -/
theorem baseChange_iff_SpecMap_tensorMap (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (C : Type u) [CommRing C] [Algebra R C] (φ : A →ₐ[R] B)
    (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A))))
    (hh : h.left = Spec.map (CommRingCat.ofHom φ.toRingHom)) :
    P ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R C)))).map h).left ↔
      P (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map φ (AlgHom.id R C)).toRingHom)) := by
  have key : (pullbackSpecIso R B C).inv ≫
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R C)))).map h).left =
      Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.map φ (AlgHom.id R C)).toRingHom) ≫
        (pullbackSpecIso R A C).inv := by
    apply pullback.hom_ext
    · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_fst, Over.mk_hom,
        pullbackSpecIso_inv_fst_assoc, pullbackSpecIso_inv_fst, hh, ← Spec.map_comp]
      congr 1
    · simp only [Category.assoc, Over.pullback_map_left, pullback.lift_snd, Over.mk_hom,
        pullbackSpecIso_inv_snd, ← Spec.map_comp]
      congr 1
      ext x
      simp
  rw [← P.cancel_left_of_respectsIso (pullbackSpecIso R B C).inv, key,
    P.cancel_right_of_respectsIso]

/-- For a property `Q` of ring maps respecting isomorphisms, `Q` of the base change
`φ ⊗ R_f : A ⊗[R] R_f → B ⊗[R] R_f` gives `Q` of the localization `A_f → B_f` of `φ` away from
`f`. -/
theorem awayMap_of_tensorMap
    (Q : ∀ {X Y : Type u} [CommRing X] [CommRing Y], (X →+* Y) → Prop)
    (hQ : RingHom.RespectsIso Q) (f : R) (φ : A →ₐ[R] B)
    (h : Q (Algebra.TensorProduct.map φ (AlgHom.id R (Localization.Away f))).toRingHom) :
    Q (Localization.awayMap φ.toRingHom (algebraMap R A f)) := by
  let g := algebraMap R A f
  let eA := IsLocalization.algEquiv (Submonoid.powers g) (A ⊗[R] Localization.Away f)
    (Localization.Away g)
  have : IsLocalization.Away (φ g) (B ⊗[R] Localization.Away f) := by
    rw [show φ g = algebraMap R B f from φ.commutes f]
    infer_instance
  let eB := IsLocalization.algEquiv (Submonoid.powers (φ g)) (B ⊗[R] Localization.Away f)
    (Localization.Away (φ g))
  have hcomm : Localization.awayMap φ.toRingHom g =
      eB.toRingEquiv.toRingHom.comp
        ((Algebra.TensorProduct.map φ (AlgHom.id R (Localization.Away f))).toRingHom.comp
          eA.symm.toRingEquiv.toRingHom) := by
    refine IsLocalization.ringHom_ext (Submonoid.powers g) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, Localization.awayMap, IsLocalization.Away.map,
      IsLocalization.map_eq]
    have h₁ : eA.symm (algebraMap A (Localization.Away g) a) =
        algebraMap A (A ⊗[R] Localization.Away f) a := eA.symm.commutes a
    have h₂ : Algebra.TensorProduct.map φ (AlgHom.id R (Localization.Away f))
        (algebraMap A (A ⊗[R] Localization.Away f) a) =
        algebraMap B (B ⊗[R] Localization.Away f) (φ a) := by
      simp [Algebra.TensorProduct.algebraMap_apply]
    change _ = eB (Algebra.TensorProduct.map φ (AlgHom.id R (Localization.Away f))
      (eA.symm (algebraMap A (Localization.Away g) a)))
    rw [h₁, h₂, eB.commutes]
    rfl
  rw [hcomm]
  exact hQ.1 _ _ (hQ.2 _ _ h)

/-- **The geometric form of Stacks 0F9R, for a general property.** Let `(R → R', f)` be a
glueing pair, let `P` be a property of morphisms of schemes stable under base change which on
morphisms of affine schemes is the property `Q` of the ring maps, and assume the algebra form
of the statement for `Q`: an `R`-algebra homomorphism out of `A` has `Q` when its localization
away from `f` and its scalar extension to `R'` have `Q`. Then a morphism `h : Spec B → Spec A`
of schemes over `X = Spec R` has `P` if and only if its base changes to `U = Spec R_f`,
`U' = Spec R'_f` and `X' = Spec R'` do. -/
theorem morphismProperty_iff_baseChange (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange]
    (Q : ∀ {X Y : Type u} [CommRing X] [CommRing Y], (X →+* Y) → Prop)
    (hQ : RingHom.RespectsIso Q)
    (hPQ : ∀ {X Y : CommRingCat.{u}} (g : X ⟶ Y), P (Spec.map g) ↔ Q g.hom) (f : R)
    (halg : ∀ φ : A →ₐ[R] B, Q (Localization.awayMap φ.toRingHom (algebraMap R A f)) →
      Q (Algebra.TensorProduct.map φ (AlgHom.id R R')).toRingHom → Q φ.toRingHom)
    (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    P h.left ↔
      P ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization.Away f))))).map h).left ∧
        P ((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap R (Localization.Away (algebraMap R R' f)))))).map h).left ∧
          P ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).map h).left := by
  refine ⟨fun hP => ?_, fun ⟨hU, _, hX'⟩ => ?_⟩
  · refine ⟨?_, ?_, ?_⟩ <;> exact MorphismProperty.overPullbackMap (P := P) _ h hP
  have hh := (SpecMap_overSpecAlgHom h).symm
  rw [baseChange_iff_SpecMap_tensorMap P _ (overSpecAlgHom h) h hh, hPQ] at hU hX'
  rw [hh, hPQ]
  exact halg _ (awayMap_of_tensorMap Q hQ f _ hU) hX'

/-- Let `(R → R', f)` be a glueing pair. A morphism `h : Spec B → Spec A` of schemes over
`X = Spec R` is finite if and only if its base changes to `U = Spec R_f`, `U' = Spec R'_f` and
`X' = Spec R'`, the three components of its image under the glueing functor of Stacks 0F9N, are
finite. -/
@[stacks 0F9R "P = finite"]
theorem isFinite_iff_baseChange (f : R) (hglue : IsGlueingPair (algebraMap R R') f)
    (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    IsFinite h.left ↔
      IsFinite ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization.Away f))))).map h).left ∧
        IsFinite ((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap R (Localization.Away (algebraMap R R' f)))))).map h).left ∧
          IsFinite ((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap R R')))).map h).left :=
  morphismProperty_iff_baseChange @IsFinite RingHom.Finite RingHom.finite_respectsIso
    (fun g => IsFinite.SpecMap_iff g) f
    (fun φ h₁ h₂ => (finite_iff_baseChange_and_awayMap_finite f hglue.1 φ).2 ⟨h₁, h₂⟩) h

/-- A morphism of affine schemes `Spec S → Spec R` is a closed immersion if and only if the
ring map `R → S` is surjective. -/
theorem isClosedImmersion_SpecMap_iff {X Y : CommRingCat.{u}} (g : X ⟶ Y) :
    IsClosedImmersion (Spec.map g) ↔ Function.Surjective g.hom := by
  have : HasAffineProperty @IsClosedImmersion
      (affineAnd fun {X Y : Type u} [CommRing X] [CommRing Y] (k : X →+* Y) =>
        Function.Surjective k) :=
    IsClosedImmersion.hasAffineProperty
  exact HasAffineProperty.SpecMap_iff_of_affineAnd this RingHom.surjective_respectsIso g

/-- Let `(R → R', f)` be a glueing pair. A morphism `h : Spec B → Spec A` of schemes over
`X = Spec R` is a closed immersion if and only if its base changes to `U = Spec R_f`,
`U' = Spec R'_f` and `X' = Spec R'`, the three components of its image under the glueing functor of
Stacks 0F9N, are closed immersions. -/
@[stacks 0F9R "P = closed immersion"]
theorem isClosedImmersion_iff_baseChange (f : R) (hglue : IsGlueingPair (algebraMap R R') f)
    (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    IsClosedImmersion h.left ↔
      IsClosedImmersion ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization.Away f))))).map h).left ∧
        IsClosedImmersion ((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap R (Localization.Away (algebraMap R R' f)))))).map h).left ∧
          IsClosedImmersion ((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap R R')))).map h).left :=
  morphismProperty_iff_baseChange @IsClosedImmersion
    (fun {X Y : Type u} [CommRing X] [CommRing Y] (k : X →+* Y) => Function.Surjective k)
    RingHom.surjective_respectsIso isClosedImmersion_SpecMap_iff f
    (fun φ h₁ h₂ =>
      (surjective_iff_baseChange_and_awayMap_surjective f hglue φ).2 ⟨h₁, h₂⟩) h

/-- Let `(R → R', f)` be a glueing pair and let the `R`-algebra `A` be glueable for it. A morphism
`h : Spec B → Spec A` of schemes over `X = Spec R` is flat if and only if its base changes to
`U = Spec R_f`, `U' = Spec R'_f` and `X' = Spec R'`, the three components of its image under the
glueing functor of Stacks 0F9N, are flat. -/
@[stacks 0F9R "P = flat"]
theorem flat_iff_baseChange (f : R) (hglue : IsGlueingPair (algebraMap R R') f)
    (hA : (beauvilleLaszloModuleSequence (S := R') A f).ShortExact)
    (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    Flat h.left ↔
      Flat ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization.Away f))))).map h).left ∧
        Flat ((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap R (Localization.Away (algebraMap R R' f)))))).map h).left ∧
          Flat ((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap R R')))).map h).left :=
  morphismProperty_iff_baseChange @Flat RingHom.Flat RingHom.Flat.respectsIso
    (fun _ => HasRingHomProperty.Spec_iff) f
    (fun φ h₁ h₂ => (flat_iff_baseChange_and_awayMap_flat f hglue.1 hA φ).2 ⟨h₁, h₂⟩) h

/-- Let `(R → R', f)` be a glueing pair. A morphism `h : Spec B → Spec A` of schemes over
`X = Spec R` is locally of finite type if and only if its base changes to `U = Spec R_f`,
`U' = Spec R'_f` and `X' = Spec R'`, the three components of its image under the glueing functor of
Stacks 0F9N, are. A morphism of affine schemes is of finite type exactly when it is locally of
finite type, being quasi-compact. -/
@[stacks 0F9R "P = finite type"]
theorem locallyOfFiniteType_iff_baseChange (f : R) (hglue : IsGlueingPair (algebraMap R R') f)
    (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    LocallyOfFiniteType h.left ↔
      LocallyOfFiniteType ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization.Away f))))).map h).left ∧
        LocallyOfFiniteType ((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap R (Localization.Away (algebraMap R R' f)))))).map h).left ∧
          LocallyOfFiniteType ((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap R R')))).map h).left :=
  morphismProperty_iff_baseChange @LocallyOfFiniteType RingHom.FiniteType
    RingHom.finiteType_respectsIso (fun _ => HasRingHomProperty.Spec_iff) f
    (fun φ h₁ h₂ =>
      (finiteType_iff_baseChange_and_awayMap_finiteType f hglue φ).2 ⟨h₁, h₂⟩) h

/-- Let `(R → R', f)` be a glueing pair and let the `R`-algebra `A` be glueable for it. A morphism
`h : Spec B → Spec A` of schemes over `X = Spec R` is flat and locally of finite presentation if
and only if its base changes to `U = Spec R_f`, `U' = Spec R'_f` and `X' = Spec R'`, the three
components of its image under the glueing functor of Stacks 0F9N, are. A morphism of affine schemes
is of finite presentation exactly when it is locally of finite presentation, being quasi-compact
and quasi-separated. -/
@[stacks 0F9R "P = flat and finite presentation"]
theorem flat_and_locallyOfFinitePresentation_iff_baseChange (f : R)
    (hglue : IsGlueingPair (algebraMap R R') f)
    (hA : (beauvilleLaszloModuleSequence (S := R') A f).ShortExact)
    (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    (Flat h.left ∧ LocallyOfFinitePresentation h.left) ↔
      (Flat ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization.Away f))))).map h).left ∧
        LocallyOfFinitePresentation ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization.Away f))))).map h).left) ∧
      (Flat ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization.Away (algebraMap R R' f)))))).map h).left ∧
        LocallyOfFinitePresentation ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization.Away (algebraMap R R' f)))))).map h).left) ∧
      (Flat ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R R')))).map h).left ∧
        LocallyOfFinitePresentation ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R R')))).map h).left) := by
  have : MorphismProperty.IsStableUnderBaseChange
      (@Flat ⊓ @LocallyOfFinitePresentation : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  exact morphismProperty_iff_baseChange (@Flat ⊓ @LocallyOfFinitePresentation)
    (fun {X Y : Type u} [CommRing X] [CommRing Y] (k : X →+* Y) =>
      k.Flat ∧ k.FinitePresentation)
    (RingHom.Flat.respectsIso.and RingHom.finitePresentation_respectsIso)
    (fun _ => and_congr HasRingHomProperty.Spec_iff HasRingHomProperty.Spec_iff) f
    (fun φ h₁ h₂ =>
      (flat_and_finitePresentation_iff_baseChange_and_awayMap f hglue hA φ).2 ⟨h₁, h₂⟩) h

/-- Let `(R → R', f)` be a glueing pair and let the `R`-algebra `A` be glueable for it. A morphism
`h : Spec B → Spec A` of schemes over `X = Spec R` is étale if and only if its base changes to
`U = Spec R_f`, `U' = Spec R'_f` and `X' = Spec R'`, the three components of its image under the
glueing functor of Stacks 0F9N, are étale. -/
@[stacks 0F9R "P = étale"]
theorem etale_iff_baseChange (f : R) (hglue : IsGlueingPair (algebraMap R R') f)
    (hA : (beauvilleLaszloModuleSequence (S := R') A f).ShortExact)
    (h : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R B))) ⟶
      Over.mk (Spec.map (CommRingCat.ofHom (algebraMap R A)))) :
    Etale h.left ↔
      Etale ((Over.pullback (Spec.map (CommRingCat.ofHom
          (algebraMap R (Localization.Away f))))).map h).left ∧
        Etale ((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap R (Localization.Away (algebraMap R R' f)))))).map h).left ∧
          Etale ((Over.pullback (Spec.map (CommRingCat.ofHom
            (algebraMap R R')))).map h).left :=
  morphismProperty_iff_baseChange @Etale RingHom.Etale RingHom.Etale.respectsIso
    (fun _ => HasRingHomProperty.Spec_iff) f
    (fun φ h₁ h₂ => (etale_iff_baseChange_and_awayMap_etale f hglue hA φ).2 ⟨h₁, h₂⟩) h

end BeauvilleLaszlo

end
