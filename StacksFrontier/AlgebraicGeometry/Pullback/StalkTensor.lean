module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.Flat.Localization
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk

/-!
# The local rings of a fibre product over an affine base

Let `A → B` be a homomorphism of commutative rings, let `X` be a scheme over `Spec A` and let

```
W = X ×_{Spec A} Spec B
```

be the base change of `X` along `Spec B → Spec A`, with first projection `pr : W ⟶ X`. Fix a
point `w` of `W` and let `x = pr w` be its image. **Then the local ring of `W` at `w` is a
localization of `𝒪_{X, x} ⊗[A] B` at a prime ideal**, namely at the contraction of its own
maximal ideal along the canonical map

```
𝒪_{X, x} ⊗[A] B → 𝒪_{W, w}
```

whose two components are the map on local rings induced by `pr` and the structure map of `W` as
a `B`-scheme. In particular the local rings of a base change are not merely tensor products of
local rings: one must still localize, because a tensor product of a local ring with another ring
has in general many primes above the maximal ideal, one for each point of the fibre.

The proof is a flatness argument rather than a computation with affine opens. The canonical map
is realized geometrically: `𝒪_{X, x} ⊗[A] B` is the pushout of `A → 𝒪_{X, x}` with `A → B` in
the category of commutative rings, so `Spec (𝒪_{X, x} ⊗[A] B)` is the fibre product of
`Spec 𝒪_{X, x} → X` with `W → X`. That morphism `Spec (𝒪_{X, x} ⊗[A] B) ⟶ W` is a base change
of the canonical morphism `Spec 𝒪_{X, x} ⟶ X`, which is flat and a preimmersion; hence so is it,
and a flat preimmersion is an isomorphism on local rings. Comparing local rings at the closed
point of `Spec 𝒪_{W, w}` and using that the local rings of an affine scheme are localizations of
its ring of sections then gives the assertion.

## Main results

* `AlgebraicGeometry.exists_isLocalization_atPrime_stalk_tensorProduct`: the local ring of
  `X ×_{Spec A} Spec B` at a point `w` is a localization of `𝒪_{X, pr w} ⊗[A] B` at a prime,
  for the canonical ring map out of the tensor product, which is recorded together with its
  restrictions to the two tensor factors.
* `AlgebraicGeometry.specMap_stalkStructureMap`: the structure map `A → 𝒪_{X, x}` of a scheme
  over `Spec A` has `Spec` the canonical morphism `Spec 𝒪_{X, x} ⟶ X` followed by the structure
  morphism. This is the step used to read the structure map off the points of `Spec A`.

## Implementation notes

The tensor product is used in place of an abstract pushout: `CommRingCat.isPushout_tensorProduct`
exhibits `𝒪_{X, x} ⊗[A] B` as a pushout square in `CommRingCat` whose two legs are
`Algebra.TensorProduct.includeLeftRingHom` and `Algebra.TensorProduct.includeRight`, so the
canonical map and the two compatibilities in the statement are the universal map of that square
and its defining equations, and no identification of a pushout with a tensor product is needed.

The `A`-algebra structure on `𝒪_{X, x}` appearing in the statement is the one coming from the
morphism `X ⟶ Spec A`, written as the germ at `x` of the map on global sections; this is the
only `A`-algebra structure available, and it must be named in the statement because the tensor
product depends on it.

## References

* [Stacks Project, Tag 0C4Y](https://stacks.math.columbia.edu/tag/0C4Y), which is the case of a
  field extension `A → B`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- For a morphism `f : X ⟶ Spec R` and a point `x` of `X`, the composite
`R → Γ(X, ⊤) → 𝒪_{X, x}` of the map on global sections with the germ at `x` has `Spec` the
canonical morphism `Spec 𝒪_{X, x} ⟶ X` followed by `f`. In other words, `Spec 𝒪_{X, x} ⟶ X`
is a morphism of schemes over `Spec R`. -/
lemma specMap_stalkStructureMap {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (x : X) :
    Spec.map ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial) =
      X.fromSpecStalk x ≫ f := by
  rw [Spec.map_comp, Spec.map_comp, ← Scheme.fromSpecStalk_toSpecΓ]
  simp only [Category.assoc]
  rw [← Scheme.toSpecΓ_naturality_assoc]
  simp only [toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- If `g : Spec 𝒪_{W, w} ⟶ Y` composed with a flat preimmersion `v : Y ⟶ W` is the canonical
morphism `Spec 𝒪_{W, w} ⟶ W`, then `g` identifies the local ring of `Y` at the image of the
closed point with `𝒪_{W, w}`. -/
lemma isIso_stalkClosedPointTo_of_comp_eq_fromSpecStalk {W Y : Scheme.{u}} {w : W}
    (g : Spec (W.presheaf.stalk w) ⟶ Y) (v : Y ⟶ W) [Flat v] [IsPreimmersion v]
    (h : g ≫ v = W.fromSpecStalk w) : IsIso (Scheme.stalkClosedPointTo g) := by
  have hgv : IsIso (Scheme.stalkClosedPointTo (g ≫ v)) := by
    rw [h, Scheme.stalkClosedPointTo_fromSpecStalk]
    infer_instance
  rw [Scheme.stalkClosedPointTo_comp] at hgv
  exact (@isIso_comp_left_iff _ _ _ _ _ _ _ (isIso_stalkMap_of_flat_isPreimmersion v _)).mp hgv

/-- If a ring map `Φ : P ⟶ R` to a local ring identifies the local ring of `Spec P` at the image
of the closed point with `R`, then `R` is the localization of `P` at the contraction of its
maximal ideal. -/
lemma isLocalization_atPrime_of_isIso_stalkClosedPointTo {P R : CommRingCat.{u}}
    [IsLocalRing R] (Φ : P ⟶ R) [IsIso (Scheme.stalkClosedPointTo (Spec.map Φ))] :
    letI := Φ.hom.toAlgebra
    IsLocalization.AtPrime R (Ideal.comap Φ.hom (IsLocalRing.maximalIdeal R)) := by
  let q : Spec P := Spec.map Φ (IsLocalRing.closedPoint R)
  let ρ : (Spec P).presheaf.stalk q ⟶ R := Scheme.stalkClosedPointTo (Spec.map Φ)
  have : IsIso ρ := ‹_›
  let : Algebra P ((Spec P).presheaf.stalk q) := StructureSheaf.stalkAlgebra P q
  have hmap : CommRingCat.ofHom (algebraMap P ((Spec P).presheaf.stalk q)) ≫ ρ = Φ := by
    show ((Scheme.ΓSpecIso P).inv ≫ (Spec P).presheaf.germ ⊤ q trivial) ≫ ρ = Φ
    rw [Category.assoc, Scheme.germ_stalkClosedPointTo_Spec]
    simp
  let : Algebra P R := Φ.hom.toAlgebra
  let ae : ((Spec P).presheaf.stalk q : Type u) ≃ₐ[P] R :=
    AlgEquiv.ofRingEquiv (f := (asIso ρ).commRingCatIsoToRingEquiv)
      (fun r => DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp hmap) r)
  have : q.asIdeal.IsPrime := q.2
  have : IsLocalization.AtPrime ((Spec P).presheaf.stalk q) q.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk P q
  exact IsLocalization.isLocalization_of_algEquiv q.asIdeal.primeCompl ae

/-- **The local ring of a fibre product over an affine base is a localization of a tensor
product at a prime ideal.** Let `A → B` be a homomorphism of commutative rings, let
`f : X ⟶ Spec A` be a scheme over `Spec A`, let `W = X ×_{Spec A} Spec B` with projections
`pr : W ⟶ X` and `sn : W ⟶ Spec B`, and let `w` be a point of `W`. There is a ring
homomorphism `ψ : 𝒪_{X, pr w} ⊗[A] B → 𝒪_{W, w}` restricting on the left factor to the map on
local rings induced by `pr` and on the right factor to the structure map of `W` over `Spec B`,
and `ψ` exhibits `𝒪_{W, w}` as the localization of `𝒪_{X, pr w} ⊗[A] B` at the prime ideal
obtained by contracting the maximal ideal of `𝒪_{W, w}` along `ψ`. -/
theorem exists_isLocalization_atPrime_stalk_tensorProduct
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of A))
    (w : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B))) : Scheme.{u})) :
    let W := (pullback f (Spec.map (CommRingCat.ofHom (algebraMap A B))) : Scheme.{u})
    let pr : W ⟶ X := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    let sn : W ⟶ Spec (.of B) := pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap A B)))
    letI : Algebra A (X.presheaf.stalk (pr w)) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ (pr w) trivial).hom.toAlgebra
    ∃ ψ : X.presheaf.stalk (pr w) ⊗[A] B →+* W.presheaf.stalk w,
      ψ.comp Algebra.TensorProduct.includeLeftRingHom = (pr.stalkMap w).hom ∧
      ψ.comp Algebra.TensorProduct.includeRight.toRingHom =
        ((Scheme.ΓSpecIso (.of B)).inv ≫ sn.appTop ≫ W.presheaf.germ ⊤ w trivial).hom ∧
      letI : Algebra (X.presheaf.stalk (pr w) ⊗[A] B) (W.presheaf.stalk w) := ψ.toAlgebra
      IsLocalization.AtPrime (W.presheaf.stalk w)
        (Ideal.comap ψ (IsLocalRing.maximalIdeal (W.presheaf.stalk w))) := by
  let b : CommRingCat.of A ⟶ CommRingCat.of B := CommRingCat.ofHom (algebraMap A B)
  let W := (pullback f (Spec.map b) : Scheme.{u})
  let pr : W ⟶ X := pullback.fst f (Spec.map b)
  let sn : W ⟶ Spec (.of B) := pullback.snd f (Spec.map b)
  let a : CommRingCat.of A ⟶ X.presheaf.stalk (pr w) :=
    (Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ (pr w) trivial
  let c : CommRingCat.of B ⟶ W.presheaf.stalk w :=
    (Scheme.ΓSpecIso (.of B)).inv ≫ sn.appTop ≫ W.presheaf.germ ⊤ w trivial
  let : Algebra A (X.presheaf.stalk (pr w)) := a.hom.toAlgebra
  let P : CommRingCat.{u} := CommRingCat.of (X.presheaf.stalk (pr w) ⊗[A] B)
  let il : X.presheaf.stalk (pr w) ⟶ P :=
    CommRingCat.ofHom (R := X.presheaf.stalk (pr w))
      (S := X.presheaf.stalk (pr w) ⊗[A] B) Algebra.TensorProduct.includeLeftRingHom
  let ir : CommRingCat.of B ⟶ P :=
    CommRingCat.ofHom (R := B) (S := X.presheaf.stalk (pr w) ⊗[A] B)
      Algebra.TensorProduct.includeRight.toRingHom
  have hpo : IsPushout a b il ir :=
    CommRingCat.isPushout_tensorProduct A (X.presheaf.stalk (pr w)) B
  have ha : Spec.map a = X.fromSpecStalk (pr w) ≫ f := specMap_stalkStructureMap f (pr w)
  have hc : Spec.map c = W.fromSpecStalk w ≫ sn := specMap_stalkStructureMap sn w
  have hab : a ≫ pr.stalkMap w = b ≫ c := by
    apply Spec.map_injective
    simp only [Spec.map_comp, ha, hc, ← Category.assoc]
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk, Category.assoc, Category.assoc]
    exact congrArg (W.fromSpecStalk w ≫ ·) pullback.condition
  let Φ : P ⟶ W.presheaf.stalk w := hpo.desc (pr.stalkMap w) c hab
  have hleft : il ≫ Φ = pr.stalkMap w := hpo.inl_desc _ _ _
  have hright : ir ≫ Φ = c := hpo.inr_desc _ _ _
  refine ⟨Φ.hom, congrArg CommRingCat.Hom.hom hleft, congrArg CommRingCat.Hom.hom hright, ?_⟩
  let v : Spec P ⟶ W := pullback.lift
    (Spec.map il ≫ X.fromSpecStalk (pr w)) (Spec.map ir) (by
      rw [Category.assoc, ← ha, ← Spec.map_comp, ← Spec.map_comp, hpo.w])
  have hvleft : v ≫ pr = Spec.map il ≫ X.fromSpecStalk (pr w) := pullback.lift_fst _ _ _
  have hvright : v ≫ sn = Spec.map ir := pullback.lift_snd _ _ _
  have hv : IsPullback v (Spec.map il) pr (X.fromSpecStalk (pr w)) := by
    refine IsPullback.of_right (h₁₂ := sn) (h₂₂ := f) (v₁₃ := Spec.map b) ?_ hvleft
      (IsPullback.of_hasPullback f (Spec.map b)).flip
    rw [hvright, ← ha]
    exact (isPullback_SpecMap_of_isPushout a b il ir hpo).flip
  have : Flat v :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hv.flip (flat_fromSpecStalk X (pr w))
  have : IsPreimmersion v :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hv.flip inferInstance
  have hfac : Spec.map Φ ≫ v = W.fromSpecStalk w := by
    apply pullback.hom_ext
    · rw [Category.assoc, hvleft, ← Category.assoc, ← Spec.map_comp, hleft,
        Scheme.SpecMap_stalkMap_fromSpecStalk]
    · rw [Category.assoc, hvright, ← Spec.map_comp, hright, hc]
  have := isIso_stalkClosedPointTo_of_comp_eq_fromSpecStalk _ v hfac
  exact isLocalization_atPrime_of_isIso_stalkClosedPointTo Φ

end AlgebraicGeometry

end
