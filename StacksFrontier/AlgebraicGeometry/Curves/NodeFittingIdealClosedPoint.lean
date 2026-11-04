module

public import StacksFrontier.AlgebraicGeometry.Curves.NodeFieldExtension
public import StacksFrontier.AlgebraicGeometry.Curves.NodeFittingIdealRationalPoint
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdealsDifferentials
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Variety.ClosedPointFinrank
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.RationalMap.MaximalIdealFieldChange
public import StacksFrontier.RingTheory.Depth.FlatLocalHom
public import StacksFrontier.RingTheory.Serre.Reduced

/-!
# The six characterizations of a node at an arbitrary closed point

Let `k` be a field, let `X` be a one-dimensional scheme locally of finite type over `k` and let
`x` be a closed point of `X`. The six conditions of Stacks Tag 0C4D are equivalent at `x`, with
no hypothesis on the residue field: that `x` be a node; that `𝒪_{X,x}` be a nodal `k`-algebra;
that every point of `X_{k̄}` above `x` be an ordinary double point; two conditions on the first
Fitting ideal of `Ω_{X/k}`, one asking in addition that `𝒪_{X,x}` be reduced and one that it
have depth one; and that `κ(x)/k` be separable while `𝒪_{X,x}` is reduced of delta invariant one
with two geometric branches.

This removes the rationality of `κ(x)` from `Stacks.Curves.isNode_tfae_of_rational`. A
presentation of an affine chart whose generators vanish at `x` — the form in which the Jacobian
criterion of Tag 0C4C is available — forces `κ(x) = k`, so the general case is reached by base
change rather than by a chart: at a closed point `y` of `X_{k̄}` above `x` the residue field is
`k̄`, and the rational case applies there.

## Main results

* `Stacks.Curves.isNode_tfae_of_isClosed` — all six conditions of Stacks Tag 0C4D are
  equivalent at an arbitrary closed point of a one-dimensional scheme locally of finite type
  over an arbitrary field.

## Implementation notes

The base change is to the algebraic closure `k̄`, where the hypotheses of the rational case are
free: a point above a closed point is closed
(`Stacks.Curves.isClosed_singleton_baseChange_of_isClosed`) and the residue field at a closed
point over an algebraically closed field is the base field
(`AlgebraicGeometry.bijective_algebraMap_residueField_of_isClosed`).

Four things are then carried between `x` and `y`.

* The node condition, which is invariant under extension of the base field (Tag 0C56,
  `Stacks.Curves.isNode_iff_of_fieldExtension`).
* The Fitting-ideal condition. The Fitting ideal sheaf upstairs is the inverse image of the one
  downstairs (Tag 0C3I), so by `AlgebraicGeometry.IdealSheafData.stalk_comap` its stalk is the
  extension of the stalk downstairs; the maximal ideal upstairs is the extension of the maximal
  ideal downstairs (Tag 0C50), whose two hypotheses are the equality of the dimensions of the
  two local rings — automatic at a closed point — and the reducedness of `κ(x) ⊗_k k̄`, which is
  the separability of `κ(x)/k`; and the stalk map is faithfully flat, so extension of ideals is
  injective.
* Reducedness, which *descends*: the stalk map is faithfully flat, hence injective.
* Depth one, which *ascends*: a regular element of `𝔪_x` stays regular upstairs because
  `𝒪_{X_{k̄},y}` is flat over `𝒪_{X,x}`, and the dimension upstairs is at most one.

The last two are not inverse to one another, and that is why both appear. Reducedness does not
ascend — a reduced curve over an imperfect field need not be geometrically reduced — so the
implication from condition (4) to the node is routed through condition (5) upstairs: a reduced
local ring of dimension one has depth one, and the dimension at `x` is one because otherwise
that local ring would be a field, making the cotangent space upstairs zero against the two
dimensions a nodal quadratic relation forces.

Separability of `κ(x)/k` is a hypothesis of the two base-change steps, and it is no
restriction: each of the six conditions implies it, conditions (2), (4), (5) and (6) outright
and conditions (1) and (3) by
`Stacks.Curves.isSeparableExtension_residueField_of_isNode`. The six are therefore joined by a
cycle of implications, each run with the separability of its source clause in hand.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C3I](https://stacks.math.columbia.edu/tag/0C3I)
* [Stacks Project, Tag 0C50](https://stacks.math.columbia.edu/tag/0C50)
* [Stacks Project, Tag 0C56](https://stacks.math.columbia.edu/tag/0C56)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped TensorProduct

namespace Stacks.Curves

universe u

/-- The structure map of the residue field at a point, as the germ of the structure morphism
followed by the residue map, is the global evaluation at that point. -/
private lemma residue_comp_germ_appTop_eq {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) :
    (X.residue x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x (by simp)).hom =
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom := by
  rw [← CommRingCat.hom_comp]
  rfl

/-- At a closed point of a scheme locally of finite type over an algebraically closed field the
germ of the structure morphism followed by the residue map is surjective: the residue field
there is the base field. -/
private lemma surjective_residue_germ_appTop_of_isClosed
    (K : Type u) [Field K] [IsAlgClosed K] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of K))
    [LocallyOfFiniteType h] (z : Z) (hz : IsClosed ({z} : Set Z)) :
    Function.Surjective ((Z.residue z).hom.comp
      ((Scheme.ΓSpecIso (.of K)).inv ≫ h.appTop ≫
        Z.presheaf.germ ⊤ z (by simp)).hom) := by
  have hb := bijective_algebraMap_residueField_of_isClosed h z hz
  rw [RingHom.algebraMap_toAlgebra] at hb
  exact (residue_comp_germ_appTop_eq h z).symm ▸ hb.2

/-- The local rings at a closed point and at a closed point of the base change above it have the
same Krull dimension. -/
private lemma ringKrullDim_stalk_baseChange_eq_of_isClosed
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hx : IsClosed ({(pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y} : Set X)) :
    ringKrullDim (X.presheaf.stalk
        ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y)) =
      ringKrullDim ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        Scheme.{u}).presheaf.stalk y) := by
  have hy : IsClosed ({y} : Set
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :=
    isClosed_singleton_baseChange_of_isClosed k K X f y hx
  have : LocallyOfFiniteType (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := inferInstance
  rw [← topologicalKrullDimAt_eq_krullDimOfRing_stalk k X f _ hx,
    ← topologicalKrullDimAt_eq_krullDimOfRing_stalk K
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y hy]
  exact (topologicalKrullDimAt_baseChange_eq k K X f y).symm

/-- **The maximal ideal downstairs generates the maximal ideal upstairs**, at a closed point
whose residue field is separable over the base field. This is Tag 0C50, whose two hypotheses are
the equality of dimensions — automatic at a closed point — and the reducedness of
`κ(x) ⊗_k K`, which is separability of `κ(x)/k`. -/
theorem map_maximalIdeal_stalkMap_baseChange_eq_of_isSeparableExtension
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hx : IsClosed ({(pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y} : Set X))
    (hsep :
      letI : Algebra k (X.residueField ((pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y)) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation ((pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y)).hom.toAlgebra
      Algebra.IsSeparableExtension k (X.residueField ((pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y))) :
    Ideal.map ((pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y).hom
        (maximalIdeal (X.presheaf.stalk ((pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y))) =
      maximalIdeal ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        Scheme.{u}).presheaf.stalk y) := by
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p : (pullback f g : Scheme.{u}) ⟶ X := pullback.fst f g
  have : LocallyOfFiniteType (pullback.snd f g) := inferInstance
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  exact map_maximalIdeal_stalkMap_eq_of_isReduced_tensorProduct k K X f y
    (ringKrullDim_stalk_baseChange_eq_of_isClosed k K X f y hx) (by
      dsimp
      let : (f (p.base y)).asIdeal.IsPrime := (f (p.base y)).isPrime
      let : Algebra k (X.residueField (p.base y)) :=
        ((CommRingCat.ofHom (algebraMap k (f (p.base y)).asIdeal.ResidueField)) ≫
          (Scheme.Spec.residueFieldIso (.of k) (f (p.base y))).inv ≫
          f.residueFieldMap (p.base y)).hom.toAlgebra
      apply Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated
      left
      have hcat :
          CommRingCat.ofHom (algebraMap k (f (p.base y)).asIdeal.ResidueField) ≫
              (Scheme.Spec.residueFieldIso (.of k) (f (p.base y))).inv ≫
              f.residueFieldMap (p.base y) =
            (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (p.base y) := by
        calc
          _ = ((Scheme.ΓSpecIso (.of k)).inv ≫
              (Spec (.of k)).presheaf.germ ⊤ (f (p.base y)) (by simp) ≫
              (Spec (.of k)).residue (f (p.base y))) ≫
              f.residueFieldMap (p.base y) := by
                rw [← Category.assoc,
                  Scheme.Spec.algebraMap_residueFieldIso_inv (.of k) (f (p.base y))]
          _ = _ := by
            simpa only [Category.assoc, Scheme.germ_residue] using
              congrArg ((Scheme.ΓSpecIso (.of k)).inv ≫ ·)
                (Scheme.Γevaluation_naturality f (p.base y))
      exact hcat.symm ▸ hsep)

/-- The stalk map of the projection of a base change along a field extension is faithfully flat. -/
private lemma faithfullyFlat_stalkMap_fst_baseChange
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    letI : Algebra (X.presheaf.stalk ((pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y))
      ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        Scheme.{u}).presheaf.stalk y) :=
      ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y).hom.toAlgebra
    Module.FaithfullyFlat (X.presheaf.stalk ((pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y))
      ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        Scheme.{u}).presheaf.stalk y) := by
  have : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  have : Flat (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) := inferInstance
  let := ((pullback.fst f
    (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap y).hom.toAlgebra
  have : Module.Flat _ _ :=
    Flat.stalkMap (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) y
  have : IsLocalHom (algebraMap (X.presheaf.stalk ((pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y))
      ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
        Scheme.{u}).presheaf.stalk y)) :=
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).toLRSHom.prop y
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- **The Fitting-ideal condition of Tag 0C4D is unchanged by extension of the base field**, at a
closed point whose residue field is separable over the base field.

The Fitting ideal sheaf upstairs is the inverse image of the one downstairs (Tag 0C3I), so its
stalk is the extension of the stalk downstairs; the maximal ideal upstairs is the extension of
the maximal ideal downstairs (Tag 0C50, whose two hypotheses are the equality of dimensions at a
closed point and the reducedness of `κ(x) ⊗_k K`, here separability of `κ(x)/k`); and the stalk
map is faithfully flat, so extension of ideals is injective. -/
private lemma stalk_fittingIdeal_eq_maximalIdeal_baseChange_iff
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    (X : Scheme.{u}) (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (y : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hx : IsClosed ({(pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y} : Set X))
    (hsep :
      letI : Algebra k (X.residueField ((pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y)) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation ((pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y)).hom.toAlgebra
      Algebra.IsSeparableExtension k (X.residueField ((pullback.fst f
        (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y))) :
    (IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials f) (1 : ℤ))
          ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y) =
        maximalIdeal (X.presheaf.stalk ((pullback.fst f
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).base y))) ↔
      (IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials
            (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))) (1 : ℤ)) y =
        maximalIdeal ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) :
          Scheme.{u}).presheaf.stalk y)) := by
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p : (pullback f g : Scheme.{u}) ⟶ X := pullback.fst f g
  have hsq : IsPullback p (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have : LocallyOfFiniteType (pullback.snd f g) := inferInstance
  -- the maximal ideal upstairs is the extension of the maximal ideal downstairs
  have hmax := map_maximalIdeal_stalkMap_baseChange_eq_of_isSeparableExtension k K X f y hx hsep
  -- the Fitting ideal upstairs is the extension of the Fitting ideal downstairs
  have hfit : IdealSheafData.stalk (fittingIdeal
        (Scheme.Hom.relativeDifferentials (pullback.snd f g)) (1 : ℤ)) y =
      Ideal.map (p.stalkMap y).hom (IdealSheafData.stalk
        (fittingIdeal (Scheme.Hom.relativeDifferentials f) (1 : ℤ)) (p.base y)) := by
    rw [← fittingIdeal_relativeDifferentials_comap p (pullback.snd f g) f g hsq 1]
    exact IdealSheafData.stalk_comap _ p y
  -- faithful flatness of the stalk map
  let : Algebra (X.presheaf.stalk (p.base y))
      ((pullback f g : Scheme.{u}).presheaf.stalk y) := (p.stalkMap y).hom.toAlgebra
  have halg : algebraMap (X.presheaf.stalk (p.base y))
      ((pullback f g : Scheme.{u}).presheaf.stalk y) = (p.stalkMap y).hom := rfl
  have := faithfullyFlat_stalkMap_fst_baseChange k K X f y
  rw [hfit]
  refine ⟨fun h => by rw [h, hmax], fun h => ?_⟩
  have hc := congrArg (Ideal.comap (p.stalkMap y).hom) (h.trans hmax.symm)
  rwa [← halg, Ideal.comap_map_eq_self_of_faithfullyFlat,
    Ideal.comap_map_eq_self_of_faithfullyFlat] at hc

/-- A regular element of the maximal ideal witnesses that the depth is at least one. -/
private lemma one_le_depth_of_isSMulRegular {A : Type u} [CommRing A] [IsLocalRing A]
    {t : A} (ht : t ∈ maximalIdeal A) (htreg : IsSMulRegular A t) :
    1 ≤ Module.depth A (maximalIdeal A) A := by
  have hmem : ∀ r ∈ [t], r ∈ maximalIdeal A := by simpa using ht
  have hreg : RingTheory.Sequence.IsRegular A [t] :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hmem).mpr
      ((RingTheory.Sequence.isWeaklyRegular_singleton_iff A t).mpr htreg)
  simpa using Module.le_depth_of_isRegular (maximalIdeal A) hmem hreg

/-- **A flat local homomorphism carries a regular element of the maximal ideal to one**, so that
a ring of dimension at most one which is flat over a local ring with a regular element in its
maximal ideal has depth exactly one. -/
private lemma depth_eq_one_of_isSMulRegular_of_flat {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing B] [Algebra A B] [Module.Flat A B]
    [IsLocalHom (algebraMap A B)]
    {t : A} (ht : t ∈ maximalIdeal A) (htreg : IsSMulRegular A t)
    (hdim : ringKrullDim B ≤ 1) :
    Module.depth B (maximalIdeal B) B = 1 := by
  have htnzd : t ∈ nonZeroDivisors A := by
    rw [mem_nonZeroDivisors_iff_right]
    intro a ha
    exact htreg (by simpa [smul_eq_mul, mul_comm] using ha)
  have hregA : IsSMulRegular B t := Module.Flat.isSMulRegular_of_nonZeroDivisors htnzd
  have hregB : IsSMulRegular B (algebraMap A B t) := by
    intro b₁ b₂ hb
    exact hregA (by simpa [Algebra.smul_def] using hb)
  have htB : algebraMap A B t ∈ maximalIdeal B := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at ht ⊢
    exact fun hu => ht (IsLocalHom.map_nonunit _ hu)
  refine le_antisymm ?_ (one_le_depth_of_isSMulRegular htB hregB)
  have htop : maximalIdeal B • (⊤ : Submodule B B) ≠ ⊤ := by
    simpa using (IsLocalRing.maximalIdeal.isMaximal B).ne_top
  have hle := Module.depth_le_supportDim B (maximalIdeal B) B htop
  rw [Module.supportDim_self_eq_ringKrullDim] at hle
  exact_mod_cast hle.trans hdim

/-- **The node condition of Tag 0C4D is the Fitting-ideal condition at a closed point whose
residue field is separable over the base field**, and the Fitting-ideal condition together with
depth one forces a node there.

Both halves pass to the base change `X_{k̄}` to the algebraic closure, where every closed point
has residue field `k̄` and `Stacks.Curves.isNode_tfae_of_rational` applies: the node condition is
invariant under extension of the base field (Tag 0C56), the Fitting-ideal condition is invariant
by `Stacks.Curves.stalk_fittingIdeal_eq_maximalIdeal_baseChange_iff`, reducedness descends along
the faithfully flat stalk map, and depth one ascends because a regular element of the maximal
ideal downstairs stays regular upstairs by flatness, the dimension upstairs being one. -/
private lemma isNode_iff_and_isNode_of_depth_of_isSeparableExtension
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X))
    (hsep :
      letI : Algebra k (X.residueField x) :=
        ((X.residue x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫
          (X ↘ Spec (.of k)).appTop ≫ X.presheaf.germ ⊤ x (by simp)).hom).toAlgebra
      Algebra.IsSeparableExtension k (X.residueField x)) :
    letI : Algebra k (X.residueField x) :=
      ((X.residue x).hom.comp ((Scheme.ΓSpecIso (.of k)).inv ≫
        (X ↘ Spec (.of k)).appTop ≫ X.presheaf.germ ⊤ x (by simp)).hom).toAlgebra
    (IsNode k X x ↔ (Algebra.IsSeparableExtension k (X.residueField x) ∧
        _root_.IsReduced (X.presheaf.stalk x) ∧
          IdealSheafData.stalk (fittingIdeal
            (Scheme.Hom.relativeDifferentials (X ↘ Spec (.of k))) (1 : ℤ)) x =
              maximalIdeal (X.presheaf.stalk x))) ∧
      ((Algebra.IsSeparableExtension k (X.residueField x) ∧
          Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
              (X.presheaf.stalk x) = 1 ∧
            IdealSheafData.stalk (fittingIdeal
              (Scheme.Hom.relativeDifferentials (X ↘ Spec (.of k))) (1 : ℤ)) x =
                maximalIdeal (X.presheaf.stalk x)) → IsNode k X x) := by
  set f : X ⟶ Spec (.of k) := X ↘ Spec (.of k) with hfdef
  let K := AlgebraicClosure k
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  obtain ⟨y, hxy, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x
    (IsLocalRing.closedPoint K) (Subsingleton.elim _ _)
  subst hxy
  have hsq : IsPullback (pullback.fst f g) (pullback.snd f g) f g := IsPullback.of_hasPullback f g
  have : LocallyOfFiniteType (pullback.snd f g) := inferInstance
  let : (pullback f g : Scheme.{u}).Over (Spec (.of K)) := ⟨pullback.snd f g⟩
  have : LocallyOfFiniteType ((pullback f g : Scheme.{u}) ↘ Spec (.of K)) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd f g))
  have hyc : IsClosed ({y} : Set (pullback f g : Scheme.{u})) :=
    isClosed_singleton_baseChange_of_isClosed k K X f y hx
  have hdimY : topologicalKrullDim (pullback f g : Scheme.{u}) = 1 :=
    (AlgebraicGeometry.topologicalKrullDim_baseChange k K (pullback.fst f g)
      (pullback.snd f g) f hsq).trans hX
  have hrat : Function.Surjective (((pullback f g : Scheme.{u}).residue y).hom.comp
      ((Scheme.ΓSpecIso (.of K)).inv ≫ ((pullback f g : Scheme.{u}) ↘ Spec (.of K)).appTop ≫
        (pullback f g : Scheme.{u}).presheaf.germ ⊤ y (by simp)).hom) :=
    surjective_residue_germ_appTop_of_isClosed K
      ((pullback f g : Scheme.{u}) ↘ Spec (.of K)) y hyc
  have hTFAE := isNode_tfae_of_rational K (pullback f g : Scheme.{u}) hdimY y hyc hrat
  let : Algebra K ((pullback f g : Scheme.{u}).residueField y) :=
    (((pullback f g : Scheme.{u}).residue y).hom.comp
      ((Scheme.ΓSpecIso (.of K)).inv ≫ ((pullback f g : Scheme.{u}) ↘ Spec (.of K)).appTop ≫
        (pullback f g : Scheme.{u}).presheaf.germ ⊤ y (by simp)).hom).toAlgebra
  have hsepΓ :
      let : Algebra k (X.residueField ((pullback.fst f g).base y)) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
          X.Γevaluation ((pullback.fst f g).base y)).hom.toAlgebra
      Algebra.IsSeparableExtension k (X.residueField ((pullback.fst f g).base y)) := by
    rw [← residue_comp_germ_appTop_eq f ((pullback.fst f g).base y)]
    exact hsep
  have hmax := map_maximalIdeal_stalkMap_baseChange_eq_of_isSeparableExtension k K X f y hx hsepΓ
  have hfitiff := stalk_fittingIdeal_eq_maximalIdeal_baseChange_iff k K X f y hx hsepΓ
  let : Algebra (X.presheaf.stalk ((pullback.fst f g).base y))
      ((pullback f g : Scheme.{u}).presheaf.stalk y) :=
    ((pullback.fst f g).stalkMap y).hom.toAlgebra
  have : Module.FaithfullyFlat (X.presheaf.stalk ((pullback.fst f g).base y))
      ((pullback f g : Scheme.{u}).presheaf.stalk y) :=
    faithfullyFlat_stalkMap_fst_baseChange k K X f y
  have : IsLocalHom (algebraMap (X.presheaf.stalk ((pullback.fst f g).base y))
      ((pullback f g : Scheme.{u}).presheaf.stalk y)) := (pullback.fst f g).toLRSHom.prop y
  have : IsNoetherianRing ((pullback f g : Scheme.{u}).presheaf.stalk y) :=
    (isNagataRing_stalk_of_locallyOfFiniteType K
      ((pullback f g : Scheme.{u}) ↘ Spec (.of K)) y).isNoetherianRing
  have : IsNoetherianRing (X.presheaf.stalk ((pullback.fst f g).base y)) :=
    (isNagataRing_stalk_of_locallyOfFiniteType k f ((pullback.fst f g).base y)).isNoetherianRing
  have hdimB : ringKrullDim ((pullback f g : Scheme.{u}).presheaf.stalk y) ≤ 1 :=
    (ringKrullDim_stalk_le_topologicalKrullDim y).trans hdimY.le
  have hdimA : ringKrullDim (X.presheaf.stalk ((pullback.fst f g).base y)) ≤ 1 :=
    (ringKrullDim_stalk_le_topologicalKrullDim _).trans hX.le
  have hnode : IsNode k X ((pullback.fst f g).base y) ↔
      IsNode K (pullback f g : Scheme.{u}) y :=
    isNode_iff_of_fieldExtension k K X f hX ((pullback.fst f g).base y) y rfl
  -- the Fitting-ideal condition upstairs and a regular element downstairs give a node
  have hfive : IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials
        (pullback.snd f g)) (1 : ℤ)) y =
          maximalIdeal ((pullback f g : Scheme.{u}).presheaf.stalk y) →
      ∀ t ∈ maximalIdeal (X.presheaf.stalk ((pullback.fst f g).base y)),
        IsSMulRegular (X.presheaf.stalk ((pullback.fst f g).base y)) t →
          IsNode k X ((pullback.fst f g).base y) := by
    intro hfitB t ht htreg
    refine hnode.mpr ((hTFAE.out 5 1).mp ?_)
    exact ⟨Algebra.isSeparableExtension_of_perfectField K _,
      depth_eq_one_of_isSMulRegular_of_flat ht htreg hdimB, hfitB⟩
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun h => ?_⟩
  · obtain ⟨-, hredB, hfitB⟩ := (hTFAE.out 1 4).mp (hnode.mp h)
    have := hredB
    refine ⟨isSeparableExtension_residueField_of_isNode k X hX _ h, ?_, hfitiff.mpr hfitB⟩
    exact isReduced_of_injective (algebraMap (X.presheaf.stalk ((pullback.fst f g).base y))
      ((pullback f g : Scheme.{u}).presheaf.stalk y))
      (FaithfulSMul.algebraMap_injective _ _)
  · obtain ⟨-, hredA, hfitA⟩ := h
    have hfitB := hfitiff.mp hfitA
    have := hredA
    have hcot2 : Module.finrank
        (ResidueField ((pullback f g : Scheme.{u}).presheaf.stalk y))
        (CotangentSpace ((pullback f g : Scheme.{u}).presheaf.stalk y)) = 2 :=
      finrank_cotangentSpace_eq_two_of_hasNodalQuadraticRelation
        ((stalk_fittingIdeal_eq_maximalIdeal_iff_hasNodalQuadraticRelation_of_rational K
          ((pullback f g : Scheme.{u}) ↘ Spec (.of K)) y hyc hrat).mp hfitB)
    have hne0 : ringKrullDim (X.presheaf.stalk ((pullback.fst f g).base y)) ≠ 0 := by
      intro h0
      let : Ring.KrullDimLE 0 (X.presheaf.stalk ((pullback.fst f g).base y)) :=
        ringKrullDimZero_iff_ringKrullDim_eq_zero.mpr h0
      have hmA : maximalIdeal (X.presheaf.stalk ((pullback.fst f g).base y)) = ⊥ :=
        IsLocalRing.isField_iff_maximalIdeal_eq.mp Ring.KrullDimLE.isField_of_isReduced
      have hmB : maximalIdeal ((pullback f g : Scheme.{u}).presheaf.stalk y) = ⊥ := by
        rw [← hmax, hmA, Ideal.map_bot]
      rw [finrank_cotangentSpace_eq_zero_iff.mpr
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hmB)] at hcot2
      exact absurd hcot2 (by norm_num)
    have hdimA1 : ringKrullDim (X.presheaf.stalk ((pullback.fst f g).base y)) = 1 := by
      have hbot : ringKrullDim (X.presheaf.stalk ((pullback.fst f g).base y)) ≠ ⊥ :=
        ringKrullDim_ne_bot
      have htop : ringKrullDim (X.presheaf.stalk ((pullback.fst f g).base y)) ≠ ⊤ :=
        ringKrullDim_ne_top
      lift ringKrullDim (X.presheaf.stalk ((pullback.fst f g).base y)) to ℕ∞ using hbot with d hd
      lift d to ℕ using (by simpa using htop) with n hn
      have hn1 : n ≤ 1 := by exact_mod_cast hdimA
      have hnne0 : n ≠ 0 := by
        intro he
        exact hne0 (by norm_num [he])
      have : n = 1 := by omega
      norm_num [this]
    obtain ⟨t, ht, htreg⟩ := exists_regular_mem_maximalIdeal
      (S := X.presheaf.stalk ((pullback.fst f g).base y)) (by rw [hdimA1]; simp)
    exact hfive hfitB t ht htreg
  · obtain ⟨-, hdepthA, hfitA⟩ := h
    obtain ⟨t, ht, htreg⟩ :=
      Stacks.Depth.ModNonzerodivisor.exists_mem_isSMulRegular_of_depth_ne_zero
        (I := maximalIdeal (X.presheaf.stalk ((pullback.fst f g).base y)))
        (by rw [hdepthA]; norm_num)
    exact hfive (hfitiff.mp hfitA) t ht htreg

/-- **Stacks Project, Tag 0C4D.** Let `k` be a field, let `X` be a one-dimensional scheme
locally of finite type over `k` and let `x` be a closed point of `X`. The following are
equivalent.

1. `x` is a node.
2. `𝒪_{X,x}` is a nodal `k`-algebra.
3. Every point of `X_{k̄}` above `x` is an ordinary double point.
4. `κ(x)/k` is separable, `𝒪_{X,x}` is reduced, and the stalk at `x` of the first Fitting ideal
   sheaf of `Ω_{X/k}` is the maximal ideal of `𝒪_{X,x}`.
5. The same with reducedness replaced by depth one.
6. `κ(x)/k` is separable and `𝒪_{X,x}` is reduced of delta invariant one with two geometric
   branches.

Each of the six conditions implies that `κ(x)/k` is separable: conditions (2), (4), (5) and (6)
say so outright, and conditions (1) and (3) by
`Stacks.Curves.isSeparableExtension_residueField_of_isNode`. Under that separability the six are
equivalent by
`Stacks.Curves.isNode_iff_and_isNode_of_depth_of_isSeparableExtension`, which supplies the two
Fitting-ideal equivalences that
`Stacks.Curves.isNode_tfae_of_fittingIdeal_equivalence` leaves open; so the cycle of
implications `1 → 2 → 3 → 4 → 5 → 6 → 1` may be run with the separability of its source clause
in hand. -/
@[stacks 0C4D]
theorem isNode_tfae_of_isClosed
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX : topologicalKrullDim X = 1) (x : X) (hx : IsClosed ({x} : Set X)) :
    let f : X ⟶ Spec (.of k) := X ↘ Spec (.of k)
    let kToStalk : k →+* X.presheaf.stalk x :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x (by simp)).hom
    letI : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
    letI : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
    let fittingCondition : Prop :=
      IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials f) (1 : ℤ)) x =
        maximalIdeal (X.presheaf.stalk x)
    let c₁ : Prop := IsNode k X x
    let c₂ : Prop := IsNodalAlgebra k (X.presheaf.stalk x)
    let c₃ : Prop :=
      (let K := AlgebraicClosure k
       let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
       let Y := (pullback f g : Scheme.{u})
       let p : Y ⟶ X := pullback.fst f g
       let q : Y ⟶ Spec (.of K) := pullback.snd f g
       letI : Y.Over (Spec (.of K)) := ⟨q⟩
       ∀ xbar : Y, p.base xbar = x → IsOrdinaryDoublePoint K Y xbar)
    let c₄ : Prop :=
      Algebra.IsSeparableExtension k (X.residueField x) ∧
        _root_.IsReduced (X.presheaf.stalk x) ∧ fittingCondition
    let c₅ : Prop :=
      Algebra.IsSeparableExtension k (X.residueField x) ∧
        Module.depth (X.presheaf.stalk x) (maximalIdeal (X.presheaf.stalk x))
            (X.presheaf.stalk x) = 1 ∧
          fittingCondition
    let c₆ : Prop :=
      Algebra.IsSeparableExtension k (X.residueField x) ∧
        _root_.IsReduced (X.presheaf.stalk x) ∧
          Ring.deltaInvariant (X.presheaf.stalk x) = 1 ∧
            AlgebraicGeometry.numberOfGeometricBranches X x = 2
    List.TFAE [c₁, c₂, c₃, c₄, c₅, c₆] := by
  intro f kToStalk fittingCondition c₁ c₂ c₃ c₄ c₅ c₆
  let : Algebra k (X.presheaf.stalk x) := kToStalk.toAlgebra
  let : Algebra k (X.residueField x) := ((X.residue x).hom.comp kToStalk).toAlgebra
  have hfull : Algebra.IsSeparableExtension k (X.residueField x) →
      List.TFAE [c₁, c₂, c₃, c₄, c₅, c₆] := by
    intro hsep
    have hkey := isNode_iff_and_isNode_of_depth_of_isSeparableExtension k X hX x hx hsep
    exact isNode_tfae_of_fittingIdeal_equivalence k X hX x hx hkey.1
      fun h₅ => hkey.1.mp (hkey.2 h₅)
  have hsep₁ : c₁ → Algebra.IsSeparableExtension k (X.residueField x) :=
    isSeparableExtension_residueField_of_isNode k X hX x
  have hsep₂ : c₂ → Algebra.IsSeparableExtension k (X.residueField x) :=
    fun h => hsep₁ (isNode_of_isNodalAlgebra_stalk k X hX x h)
  have hsep₃ : c₃ → Algebra.IsSeparableExtension k (X.residueField x) :=
    fun h => hsep₁ (isNode_of_forall_isOrdinaryDoublePoint k X x hx h)
  tfae_have 1 → 2 := fun h => ((hfull (hsep₁ h)).out 1 2).mp h
  tfae_have 2 → 3 := fun h => ((hfull (hsep₂ h)).out 2 3).mp h
  tfae_have 3 → 4 := fun h => ((hfull (hsep₃ h)).out 3 4).mp h
  tfae_have 4 → 5 := fun h => ((hfull h.1).out 4 5).mp h
  tfae_have 5 → 6 := fun h => ((hfull h.1).out 5 6).mp h
  tfae_have 6 → 1 := fun h => ((hfull h.1).out 6 1).mp h
  tfae_finish

end Stacks.Curves

end



