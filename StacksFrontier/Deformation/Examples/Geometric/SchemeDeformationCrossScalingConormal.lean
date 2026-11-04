module

public import StacksFrontier.Deformation.Applications.TwoFibreProductBoundaryLinear
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationTangentScalingConormal
public import StacksFrontier.Deformation.Examples.Geometric.SchemeMorphismLiftTorsor
public import StacksFrontier.Deformation.LiftsOfObjects.Action.Difference

/-!
# The coordinate scaling of a first-order deformation, read in `𝒞_Λ`

The scalar action on the tangent space of a deformation category is transport along the
self-map `ε ↦ cε` of a dual-number base object, and
`Deformation.tangentClassAt_smul_of_isHomLift` reads that transport at the self-map

`k[c · 𝟙] := (Deformation.squareZeroExtensionArtinian Λ k).map (c • 𝟙 M)`

of the square-zero extension **of `𝒞_Λ` itself**. The scaling the infinitesimal-automorphism
API provides, `Deformation.tangentScaling`, is not that self-map: it is a self-map of
`Deformation.dualNumbersUnder`, the dual numbers read as an algebra *under* the base object of
the point, whose underlying object of `𝒞_Λ` carries the `Λ`-algebra structure composed through
that base object. The two objects share a carrier and differ in their `Algebra Λ` instance, so
no equality transports the one self-map to the other — the equation
`(Deformation.Examples.firstOrderPushforward P).base = k[M]` is *false*, as recorded at
`Deformation.Examples.firstOrderPushforwardCross_base`.

What this file does is supply the scaling datum on the side where the base object *is* the
square-zero extension of `𝒞_Λ` on the nose, namely at `Deformation.squareZeroCrossUnder`:

* the coordinate computation at `k[c · 𝟙]` itself, with no transport at all
  (`Deformation.Examples.exists_squareZeroExtensionArtinian_smul_generator`);
* the base arrow of the chosen pushforward's scaling self-arrow, identified with `k[c · 𝟙]`
  (`Deformation.Examples.isHomLift_map_squareZeroCrossUnderMap` and
  `Deformation.Examples.map_squareZeroCrossUnderMap_base_eq`).

## Main results

* `Deformation.Examples.exists_squareZeroExtensionArtinian_smul_generator`: **the base datum for
  `k[c · 𝟙]` at the dual-number object of `𝒞_Λ`** — a generator of the maximal ideal and an
  element of residue `c` by which `k[c · 𝟙]` multiplies it. This is the companion of
  `Deformation.Examples.exists_tangentScaling_base_generator` on the `𝒞_Λ` side, and unlike it
  needs no transport: the base object is given, not merely equal to a given one.
* `Deformation.Examples.isHomLift_map_squareZeroCrossUnderMap`: **the base arrow of the scaling
  self-arrow of a chosen pushforward to the re-based square-zero extension is `k[c · 𝟙]`**, in
  the shape `Deformation.tangentClassAt_smul_of_isHomLift` consumes.
* `Deformation.Examples.map_squareZeroCrossUnderMap_base_eq`: the same identification written as
  a factorisation through the two `eqToHom`s, which is the shape
  `Deformation.Examples.morphismDeformationHom_isHomLift` consumes.
* `Deformation.Examples.exists_crossScaling_base_generator`: the base datum transported to the
  re-based first-order pushforward of a point of the deformation category of a scheme.
* `Deformation.Examples.conormalSelfMap_crossScaling_eq_smul`: **the endomorphism of the conormal
  sections of the special fibre induced by the re-based coordinate scaling is multiplication by
  the scalar.**

## Implementation notes

The scaling self-arrow here is `Deformation.squareZeroCrossUnderMap A (c • 𝟙 M)` where
`Deformation.Examples.exists_tangentScaling_base_generator` has `Deformation.tangentScaling c`.
The point of the change is `Deformation.squareZeroCrossUnderMap_right`, which is `rfl`: the
underlying arrow of `𝒞_Λ` of the re-based coordinate map *is* `k[c · 𝟙]`, with no restriction of
scalars in the way. So the arrow identification that the scalar half of
[Stacks Project, Tag 0E3V] needs is free on this side, and what is left to compute is the
coordinate datum, which is the dual-number computation of
`Deformation.Examples.apply_eq_mul_of_fst_snd` performed directly at
`Deformation.artinianDualNumbers`.

At `Deformation.tangentScaling` no such identification exists, and none can: the two objects of
`𝒞_Λ` are not equal. That is why the scalar half is developed at
`Deformation.squareZeroCrossUnder`, exactly as the third and fourth spots of the source's
sequence are restated at `Deformation.Examples.firstOrderPushforwardCross`.

The square-zero hypothesis on the defining ideal is carried rather than discharged, as in
`Deformation.Examples.conormalSelfMap_tangentScaling_eq_smul`;
`Deformation.Examples.maximalIdeal_pow_two_eq_bot_of_coordinate` discharges it at the re-based
pushforward through `Deformation.Examples.firstOrderPushforwardCrossCoordinate`.

## References

* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
* [Stacks Project, Tag 06IH](https://stacks.math.columbia.edu/tag/06IH)
* [Stacks Project, Tag 0CK2](https://stacks.math.columbia.edu/tag/0CK2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### The base datum for the scaling of the square-zero extension of `𝒞_Λ` -/

/-- **The base datum of `k[c · 𝟙]` at the dual-number object of `𝒞_Λ`.** There is a generator
`t` of the maximal ideal of `Deformation.artinianDualNumbers Λ k` and an element of residue `c`
by which `(Deformation.squareZeroExtensionArtinian Λ k).map (c • 𝟙)` multiplies it.

The generator is `ε` and the element is `c`: the scaling fixes the residue coordinate
(`Deformation.squareZeroExtensionArtinian_map_fst`) and multiplies the infinitesimal one by `c`
(`Deformation.squareZeroExtensionArtinian_map_snd`), and
`Deformation.Examples.apply_eq_mul_of_fst_snd` turns those two coordinate computations into the
product.

This is the companion of `Deformation.Examples.exists_tangentScaling_base_generator`, and it is
cheaper: there the base object is only *equal* to the dual numbers, so the computation has to be
transported along `CategoryTheory.IsHomLift.fac'`, while here the object is the dual-number
object of `𝒞_Λ` itself. -/
theorem exists_squareZeroExtensionArtinian_smul_generator (c : k) :
    ∃ t c' : (Deformation.artinianDualNumbers.{u, u, u} Λ k : Type u),
      IsLocalRing.maximalIdeal (Deformation.artinianDualNumbers.{u, u, u} Λ k : Type u) =
          Ideal.span {t} ∧
        Deformation.Artin.residueMap (Deformation.artinianDualNumbers.{u, u, u} Λ k) c' = c ∧
        ((squareZeroExtensionArtinian.{u, u, u} Λ k).map
            (c • 𝟙 (FGModuleCat.of k (ULift.{u} k)))).hom t = c' * t := by
  set e : (Deformation.artinianDualNumbers.{u, u, u} Λ k : Type u) ≃+* DualNumber k :=
    (artinianDualNumbersCoordinate (Λ := Λ) (k := k)).toRingEquiv with he
  have hfst_e : ∀ v, TrivSqZeroExt.fst (e v) = TrivSqZeroExt.fst v := fun v =>
    Deformation.dualNumbersEquiv_fst.{u, u, u} (Λ := Λ) (k := k) v
  have hsnd_e : ∀ v, TrivSqZeroExt.snd (e v) = ULift.down (TrivSqZeroExt.snd v) := fun v =>
    dualNumbersEquiv_snd (Λ := Λ) (k := k) v
  set t := e.symm (DualNumber.eps (R := k)) with ht
  have hft : TrivSqZeroExt.fst t = 0 := by
    rw [← hfst_e t, ht, e.apply_symm_apply, DualNumber.fst_eps]
  have hst : ULift.down (TrivSqZeroExt.snd t) = 1 := by
    rw [← hsnd_e t, ht, e.apply_symm_apply, DualNumber.snd_eps]
  refine ⟨t, e.symm (TrivSqZeroExt.inl c),
    maximalIdeal_eq_span_of_dualNumberRingEquiv e, ?_, ?_⟩
  · show TrivSqZeroExt.fst (e.symm (TrivSqZeroExt.inl c)) = c
    rw [← hfst_e, e.apply_symm_apply, TrivSqZeroExt.fst_inl]
  · refine apply_eq_mul_of_fst_snd e c (e.apply_symm_apply _) ?_ ?_
    · rw [hfst_e, squareZeroExtensionArtinian_map_fst, hft]
    · rw [hsnd_e, squareZeroExtensionArtinian_map_snd]
      show c * ULift.down (TrivSqZeroExt.snd t) = c
      rw [hst, mul_one]

/-! ### The base arrow of the re-based scaling self-arrow -/

section Cross

universe u₁ v₁

variable {F : Type u₁} [Category.{v₁} F]
  {p : F ⥤ ArtinianLocalAlgCat.{u, u, u} Λ k} {x : F}

/-- **The base arrow of the scaling self-arrow of a chosen pushforward to the re-based
square-zero extension is the coordinate map of `𝒞_Λ` itself.** The arrow
`Deformation.ChosenPushforwardsAt.map (Deformation.squareZeroCrossUnderMap (p.obj x) h)` lies
over the underlying arrow of `𝒞_Λ` of `Deformation.squareZeroCrossUnderMap (p.obj x) h`, which
is `(Deformation.squareZeroExtensionArtinian Λ k).map h` by
`Deformation.squareZeroCrossUnderMap_right`, that lemma being `rfl`.

This is the hypothesis `Deformation.tangentClassAt_smul_of_isHomLift` asks for, at `h = c • 𝟙 M`:
the morphism of `𝒞_Λ` the arrow lies over is `k[c · 𝟙]` on the nose. The corresponding statement
at `Deformation.tangentScaling` does not hold — the two objects of `𝒞_Λ` differ in their
`Algebra Λ` instance — which is why the scaling is read here. -/
theorem isHomLift_map_squareZeroCrossUnderMap (P : ChosenPushforwardsAt p x)
    {M N : FGModuleCat.{u} k} (h : M ⟶ N) :
    p.IsHomLift ((squareZeroExtensionArtinian.{u, u, u} Λ k).map h)
      (P.map (squareZeroCrossUnderMap.{u, u, u} (p.obj x) h)) :=
  P.map_isHomLift (squareZeroCrossUnderMap.{u, u, u} (p.obj x) h)

end Cross

/-! ### The base datum at a deformation over the dual-number object -/

/-- **The base datum of `k[c · 𝟙]`, transported to an object of `𝒞_Λ` equal to the dual-number
object.** `Deformation.Examples.exists_squareZeroExtensionArtinian_smul_generator` carried across
an equality of objects by `Deformation.Examples.exists_generator_of_eq`.

Unlike the corresponding hypothesis at `Deformation.Examples.firstOrderPushforward`, the equality
`hA` is satisfiable: `Deformation.Examples.firstOrderPushforwardCross_base` discharges it at the
re-based first-order pushforward, where it holds because
`Deformation.squareZeroCrossUnder_right` is `rfl`. -/
theorem exists_base_generator_of_eq_artinianDualNumbers
    {A : ArtinianLocalAlgCat.{u, u, u} Λ k}
    (hA : A = Deformation.artinianDualNumbers.{u, u, u} Λ k) (c : k) :
    ∃ t c' : (A : Type u),
      IsLocalRing.maximalIdeal (A : Type u) = Ideal.span {t} ∧
        Deformation.Artin.residueMap A c' = c ∧
        (eqToHom hA ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map
              (c • 𝟙 (FGModuleCat.of k (ULift.{u} k))) ≫ eqToHom hA.symm).hom t = c' * t := by
  obtain ⟨t, c', ht, hres, hmul⟩ :=
    exists_squareZeroExtensionArtinian_smul_generator (Λ := Λ) (k := k) c
  exact exists_generator_of_eq hA _ c ht hres hmul

/-! ### The re-based coordinate scaling on the conormal sections -/

section Geometric

attribute [local instance] deformationSpecialMap_isClosedImmersion

variable {X : Over (Spec (CommRingCat.of k))}

/-- **The base arrow of the re-based scaling self-arrow of a chosen pushforward, as a
factorisation through the two `eqToHom`s.** This is
`Deformation.Examples.isHomLift_map_squareZeroCrossUnderMap` read through
`CategoryTheory.IsHomLift.fac'`, which is the shape
`Deformation.Examples.morphismDeformationHom_isHomLift` and
`Deformation.Examples.conormalSelfMap_eq_smul` consume: the base component of the arrow is the
coordinate map of `𝒞_Λ` conjugated by the equalities identifying the bases of the two
pushforwards with the square-zero extensions. -/
theorem map_squareZeroCrossUnderMap_base
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀)
    {M N : FGModuleCat.{u} k} (h : M ⟶ N) :
    (P.map (squareZeroCrossUnderMap.{u, u, u}
        ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).obj x₀) h)).base =
      eqToHom (P.obj (squareZeroCrossUnder.{u, u, u}
          ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).obj x₀) M)).2 ≫
        (squareZeroExtensionArtinian.{u, u, u} Λ k).map h ≫
          eqToHom (P.obj (squareZeroCrossUnder.{u, u, u}
            ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).obj x₀) N)).2.symm :=
  CategoryTheory.IsHomLift.fac'
    (p := schemeDeformationCategoryProjection (Λ := Λ) (k := k) X)
    (f := (squareZeroCrossUnderMap.{u, u, u}
      ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).obj x₀) h).right)
    (φ := P.map (squareZeroCrossUnderMap.{u, u, u}
      ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).obj x₀) h))

/-- **The endomorphism of the conormal sections of the special fibre induced by the re-based
coordinate scaling is multiplication by the scalar.** Let `P` be a first-order deformation of `X`
whose base object *is* the dual-number object of `𝒞_Λ`, and let `φ` be a self-arrow of `P` whose
base component is `k[c · 𝟙]` conjugated by that equality. Then `φ` induces on the conormal
sections of the special fibre multiplication by the function `c` determines on `X`.

This is `Deformation.Examples.conormalSelfMap_eq_smul` with its base datum supplied by
`Deformation.Examples.exists_base_generator_of_eq_artinianDualNumbers`, and it is the companion
of `Deformation.Examples.conormalSelfMap_tangentScaling_eq_smul` on the `𝒞_Λ` side: there the
scaling is `Deformation.tangentScaling`, read on a base object merely isomorphic to the
square-zero extension of `𝒞_Λ`, and here it is the coordinate map of `𝒞_Λ` itself.

Both hypotheses are satisfiable at the re-based first-order pushforward: `hP` is
`Deformation.Examples.firstOrderPushforwardCross_base` and `hφ` is
`Deformation.Examples.map_squareZeroCrossUnderMap_base` at `h = c • 𝟙`. -/
theorem conormalSelfMap_crossScaling_eq_smul
    {P : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (hsq : P.specialMap.ker ^ 2 = ⊥)
    (hP : P.base = Deformation.artinianDualNumbers.{u, u, u} Λ k) (c : k) (φ : P ⟶ P)
    (hφ : φ.base = eqToHom hP ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map
      (c • 𝟙 (FGModuleCat.of k (ULift.{u} k))) ≫ eqToHom hP.symm)
    (V : P.scheme.Opens)
    (s : Γ(Stacks.Thickenings.conormalModules P.specialMap, P.specialMap ⁻¹ᵁ V)) :
    Stacks.Thickenings.conormalSelfMap hsq φ.special_compat V s =
      baseSection X.hom c (P.specialMap ⁻¹ᵁ V) • s := by
  obtain ⟨t, c', ht, hres, hb⟩ := exists_base_generator_of_eq_artinianDualNumbers hP c
  rw [conormalSelfMap_eq_smul hsq φ ht (by rw [hφ]; exact hb) V s, hres]

/-- **The hypotheses of `Deformation.Examples.conormalSelfMap_crossScaling_eq_smul` are jointly
satisfiable.** At the chosen pushforward of a point of the deformation category of `X` to the
re-based square-zero extension by the rank-one module there is a first-order deformation whose
base object *is* the dual-number object of `𝒞_Λ`, whose special-fibre ideal has square zero, and
which carries a self-arrow whose base component is `k[c · 𝟙]` conjugated by that equality.

So the preceding theorem is not a statement about an empty hypothesis. This is recorded because
the corresponding equality at `Deformation.Examples.firstOrderPushforward` is **false** — see
`Deformation.Examples.firstOrderPushforwardCross_base` — so that a reader meeting a hypothesis
of the form "the base of this pushforward is the square-zero extension of `𝒞_Λ`" has reason to
ask which pushforward it is about.

The three components are `Deformation.ChosenPushforwardsAt.obj`'s second component read through
`Deformation.squareZeroCrossUnder_right` (which is `rfl`),
`Deformation.Examples.ker_specialMap_pow_two_eq_bot` at
`Deformation.Examples.maximalIdeal_artinianDualNumbers_sq_eq_bot`, and
`Deformation.Examples.map_squareZeroCrossUnderMap_base`. -/
theorem exists_crossScaling_selfMap
    {x₀ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (P : ChosenPushforwardsAt
      (schemeDeformationCategoryProjection (Λ := Λ) (k := k) X) x₀) (c : k) :
    ∃ (Q : SchemeDeformationCategory (Λ := Λ) (k := k) X)
        (hQ : Q.base = Deformation.artinianDualNumbers.{u, u, u} Λ k) (φ : Q ⟶ Q),
      Q.specialMap.ker ^ 2 = ⊥ ∧
        φ.base = eqToHom hQ ≫ (squareZeroExtensionArtinian.{u, u, u} Λ k).map
          (c • 𝟙 (FGModuleCat.of k (ULift.{u} k))) ≫ eqToHom hQ.symm := by
  have hQ : ((P.obj (squareZeroCrossUnder.{u, u, u}
        ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).obj x₀)
        (FGModuleCat.of k (ULift.{u} k)))).1).base =
      Deformation.artinianDualNumbers.{u, u, u} Λ k :=
    (P.obj (squareZeroCrossUnder.{u, u, u}
      ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).obj x₀)
      (FGModuleCat.of k (ULift.{u} k)))).2
  refine ⟨_, hQ, P.map (squareZeroCrossUnderMap.{u, u, u}
      ((schemeDeformationCategoryProjection (Λ := Λ) (k := k) X).obj x₀)
      (c • 𝟙 (FGModuleCat.of k (ULift.{u} k)))), ?_,
    map_squareZeroCrossUnderMap_base P _⟩
  refine ker_specialMap_pow_two_eq_bot _ ?_
  rw [hQ]
  exact maximalIdeal_artinianDualNumbers_sq_eq_bot

end Geometric

end Deformation.Examples

end
