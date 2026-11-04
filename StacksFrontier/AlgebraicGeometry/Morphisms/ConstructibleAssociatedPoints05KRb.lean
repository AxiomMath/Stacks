module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.ConstructibleAssociatedPoints05KR
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.NoetherianFibre
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre

/-!
# Descent of the fibrewise associated-point condition along an arbitrary base change

Let `f : X ⟶ Y` be a morphism locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module,
let `U ⊆ X` be an open subscheme and write

`E(f, F, U) = {y : Y | Ass(F_y) ⊆ U_y}`

for the locus on the base over which all associated points of the fibre of `F` lie in `U`. For a
morphism `g : Y' ⟶ Y` and a point `z` of `Y'` this file proves the implication

`g z ∈ E(f, F, U) → z ∈ E(f', F', U')`,

where `f'` is the base change of `f`, `F'` the pullback of `F` and `U'` the inverse image of `U`
along the projection. Equivalently, `g ⁻¹' E(f, F, U) ⊆ E(f', F', U')`.

This is one of the two implications of Stacks 05KQ, with **no hypothesis on `g`**. It is
therefore not a consequence of
`Stacks.Divisors.associatedPoints_fiber_subset_iff_baseChange`, which proves both implications
but only for a `g` that is surjective on stalks: a morphism lying in the class treated here and
not in that one is `Spec ℚ(i) ⟶ Spec ℚ`, and more to the point the morphism
`Spec A ⟶ Spec Aᵢ` onto a finite-type `ℤ`-subalgebra, which is the base change the limit
argument of Stacks 05KR performs and whose stalk maps are localizations rather than
surjections.

What is *not* proved here is the converse implication `z ∈ E(f', F', U') → g z ∈ E(f, F, U)`.
That direction needs the existence of an associated point of the base-changed fibre above a
given associated point of the fibre, which is the remaining content of Stacks Divisors 31.7.3
(Stacks 05DC): the points above `x` that work are the generic points of the irreducible
components of `Spec (κ(z) ⊗_{κ(g z)} κ(x))`, and producing one of them is not a formal
consequence of the descent statement used here. See the implementation notes.

## Main results

* `AlgebraicGeometry.baseChangeFiberMap_eq_fiberPullbackIso_hom_comp`: the comparison morphism
  of fibres of a base change is the canonical isomorphism onto the explicit fibre product of the
  fibre with the residue field, followed by its first projection.
* `Stacks.Divisors.associatedPoints_fiber_baseChange_eq_preimage`: the associated points of the
  fibre of the base change are the inverse image, under that isomorphism, of the associated
  points of the pullback to the explicit fibre product. This holds for an arbitrary `g`.
* `Stacks.Divisors.mem_associatedPoints_fiber_of_baseChange`: an associated point of the fibre
  of the base change is carried by the comparison morphism of fibres to an associated point of
  the fibre.
* `Stacks.Divisors.associatedPoints_fiber_subset_of_baseChange`: the implication of Stacks 05KQ
  described above, at a single point of `Y'`.
* `Stacks.Divisors.setOf_associatedPoints_fiber_subset_baseChange_subset`: the same implication
  read as an inclusion of loci on `Y'`.

## Implementation notes

The fibre of the base change at `z` is the fibre of `f` at `g z` base changed along the
extension of residue fields `κ(g z) ⟶ κ(z)`; the identification is
`AlgebraicGeometry.fiberPullbackIso`, and its compatibility with the comparison morphism of
fibres is `AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`, whose first leg
is by definition `AlgebraicGeometry.baseChangeFiberMap`. So the geometric input is
already available and the whole statement reduces to a question about a scheme over a field and
its base change along a field extension.

For that question the descent of *weakly* associated points is Stacks 0CUC,
`AlgebraicGeometry.isWeaklyAssociatedPoint_of_baseChange`. The passage between associated and
weakly associated points is free in the direction needed: an associated point is always weakly
associated (Stacks 05AM), and the converse holds on the fibre of `f` because that fibre is
locally Noetherian (Stacks 05AR). This is the only use made of `LocallyOfFiniteType f`.

The hypothesis that `F` be of finite type, which the source imposes, is not needed for this
implication and is not assumed: Stacks 0CUC holds for an arbitrary quasi-coherent module.

The converse implication is where finite type on `F` and the structure of
`Spec (κ(z) ⊗_{κ(g z)} κ(x))` enter. It would follow from the statement shape

```
theorem mem_associatedPoints_pullback_of_isField_baseChange
    {k K : Type u} [Field k] [Field K] [Algebra k K] {W : Scheme.{u}}
    (p : W ⟶ Spec (.of k)) (G : W.Modules) [G.IsQuasicoherent] [G.IsFiniteType]
    (x : W) (hx : x ∈ Stacks.Divisors.associatedPoints G) :
    ∃ w : (pullback p (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}),
      pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))) w = x ∧
      w ∈ Stacks.Divisors.associatedPoints
        ((Scheme.Modules.pullback
          (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap k K))))).obj G)
```

together with the present `Stacks.Divisors.associatedPoints_fiber_baseChange_eq_preimage` and
`AlgebraicGeometry.preimage_baseChangeFiberMap_eq`, in exactly the way
`Stacks.Divisors.associatedPoints_fiber_subset_of_baseChange` is assembled below.

The base-change morphism is passed to the auxiliary lemma as a morphism `φ` of commutative
rings rather than as `CommRingCat.ofHom (algebraMap k K)`, and the `Algebra` instance is
introduced from `φ` inside the proof. Writing `algebraMap` at the call site instead makes the
elaborator unfold `Scheme.residueField` while looking for the `CommSemiring` instance on its
carrier, and the locally introduced `Algebra` instance is then no longer found.

## References

* [Stacks Project, Tag 05AM](https://stacks.math.columbia.edu/tag/05AM)
* [Stacks Project, Tag 05AR](https://stacks.math.columbia.edu/tag/05AR)
* [Stacks Project, Tag 05DC](https://stacks.math.columbia.edu/tag/05DC)
* [Stacks Project, Tag 05KQ](https://stacks.math.columbia.edu/tag/05KQ)
* [Stacks Project, Tag 05KR](https://stacks.math.columbia.edu/tag/05KR)
* [Stacks Project, Tag 0CUC](https://stacks.math.columbia.edu/tag/0CUC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The comparison morphism from the fibre at `z` of the base change of `f` along `g` to the
fibre of `f` at `g z` factors as the canonical isomorphism onto the fibre product of that fibre
with `Spec κ(z)` over `Spec κ(g z)`, followed by the first projection.

Both sides are the first leg of the pullback square
`AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`. -/
theorem baseChangeFiberMap_eq_fiberPullbackIso_hom_comp {X Y Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (z : Y') :
    baseChangeFiberMap f g z = (fiberPullbackIso f g z).hom ≫
      pullback.fst (f.fiberToSpecResidueField (g z)) (Spec.map (g.residueFieldMap z)) :=
  ((isPullback_fiberToSpecResidueField_of_isPullback
    (IsPullback.of_hasPullback f g) z).isoPullback_hom_fst).symm

end AlgebraicGeometry

namespace Stacks.Divisors

/-- The affine-base case of the descent: for a scheme `W` over a field `k` which is locally
Noetherian and a quasi-coherent `𝒪_W`-module `G`, an associated point of the pullback of `G` to
the base change of `W` along a field extension `k ⟶ K` lies over an associated point of `G`.

An associated point is weakly associated (Stacks 05AM); weakly associated points descend along
a base change by a field extension (Stacks 0CUC); and on the locally Noetherian `W` a weakly
associated point is associated (Stacks 05AR). -/
private theorem mem_associatedPoints_of_baseChange_field
    {k K : Type u} [Field k] [Field K] {W : Scheme.{u}} [IsLocallyNoetherian W]
    (p : W ⟶ Spec (.of k)) (φ : CommRingCat.of k ⟶ CommRingCat.of K)
    (G : W.Modules) [G.IsQuasicoherent] (w : (pullback p (Spec.map φ) : Scheme.{u}))
    (hw : w ∈ associatedPoints
      ((Scheme.Modules.pullback (pullback.fst p (Spec.map φ))).obj G)) :
    pullback.fst p (Spec.map φ) w ∈ associatedPoints G := by
  let : Algebra k K := φ.hom.toAlgebra
  have hφ : CommRingCat.ofHom (algebraMap k K) = φ := by
    rw [RingHom.algebraMap_toAlgebra]
    ext
    rfl
  have h := isWeaklyAssociatedPoint_of_baseChange (k := k) (K := K) p G
  rw [hφ] at h
  rw [mem_associatedPoints_iff, ← mem_associatedPoints_iff,
    associatedPoints_eq_weaklyAssociatedPoints]
  exact h w _ rfl (associatedPoints_subset_weaklyAssociatedPoints _ hw)

variable {X Y Y' : Scheme.{u}}

/-- The associated points of the restriction of the pullback of `F` to the fibre at `z` of the
base change of `f` along `g` are the inverse image, under the canonical isomorphism of that
fibre with the fibre product of the fibre of `f` at `g z` with `Spec κ(z)`, of the associated
points of the pullback of `F` to that fibre product.

No hypothesis is placed on `g`: all four modules in sight are pullbacks of `F` along the legs
of one commutative square, so they agree up to the pullback comparison isomorphisms, and the
only morphism inverted is the isomorphism `AlgebraicGeometry.fiberPullbackIso`. -/
theorem associatedPoints_fiber_baseChange_eq_preimage (f : X ⟶ Y) (g : Y' ⟶ Y) (F : X.Modules)
    (z : Y') :
    associatedPoints ((Scheme.Modules.pullback ((pullback.snd f g).fiberι z)).obj
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) =
      (fiberPullbackIso f g z).hom ⁻¹' associatedPoints
        ((Scheme.Modules.pullback (pullback.fst (f.fiberToSpecResidueField (g z))
          (Spec.map (g.residueFieldMap z)))).obj
          ((Scheme.Modules.pullback (f.fiberι (g z))).obj F)) := by
  rw [associatedPoints_pullback_comp, ← baseChangeFiberMap_comp_fiberι,
    ← associatedPoints_pullback_comp, baseChangeFiberMap_eq_fiberPullbackIso_hom_comp,
    ← associatedPoints_pullback_comp]
  exact associatedPoints_pullback_of_iso (fiberPullbackIso f g z) _

/-- **Half of Stacks Project, Tag 05KQ, pointwise.** For `f` locally of finite type and `F`
quasi-coherent, an associated point of the fibre at `z` of the pullback of `F` along the base
change of `f` by an arbitrary `g` is carried by the comparison morphism of fibres to an
associated point of the fibre of `F` at `g z`.

The fibre at `z` is the fibre at `g z` base changed along the residue field extension
`κ(g z) ⟶ κ(z)`, so this is `mem_associatedPoints_of_baseChange_field` applied to the fibre of
`f` at `g z`, which is locally Noetherian because `f` is locally of finite type. -/
theorem mem_associatedPoints_fiber_of_baseChange (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) (F : X.Modules) [F.IsQuasicoherent] (z : Y')
    (x' : (pullback.snd f g).fiber z)
    (hx' : x' ∈ associatedPoints ((Scheme.Modules.pullback ((pullback.snd f g).fiberι z)).obj
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F))) :
    baseChangeFiberMap f g z x' ∈
      associatedPoints ((Scheme.Modules.pullback (f.fiberι (g z))).obj F) := by
  let : IsLocallyNoetherian (f.fiber (g z)) :=
    isLocallyNoetherian_fiber_of_locallyOfFiniteType f (g z)
  rw [associatedPoints_fiber_baseChange_eq_preimage f g F z] at hx'
  have hw := mem_associatedPoints_of_baseChange_field
    (f.fiberToSpecResidueField (g z)) (g.residueFieldMap z)
    ((Scheme.Modules.pullback (f.fiberι (g z))).obj F)
    ((fiberPullbackIso f g z).hom x') hx'
  rw [baseChangeFiberMap_eq_fiberPullbackIso_hom_comp, Scheme.Hom.comp_apply]
  exact hw

/-- **Half of Stacks Project, Tag 05KQ.** For `f` locally of finite type, `F` quasi-coherent and
`g` arbitrary: if all associated points of the fibre of `F` at `g z` lie in `U`, then all
associated points of the fibre at `z` of the pullback of `F` lie in the inverse image of `U`.

Both sides are read through the comparison morphism of fibres:
`AlgebraicGeometry.preimage_baseChangeFiberMap_eq` matches the two inverse images of `U`, and
`mem_associatedPoints_fiber_of_baseChange` carries an associated point of the base-changed fibre
to one of the fibre, where the hypothesis applies. The converse implication is not available at
this generality; see the module documentation. -/
theorem associatedPoints_fiber_subset_of_baseChange (f : X ⟶ Y) [LocallyOfFiniteType f]
    (g : Y' ⟶ Y) (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) (z : Y')
    (h : associatedPoints ((Scheme.Modules.pullback (f.fiberι (g z))).obj F) ⊆
      f.fiberι (g z) ⁻¹' (U : Set X)) :
    associatedPoints ((Scheme.Modules.pullback ((pullback.snd f g).fiberι z)).obj
        ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) ⊆
      (pullback.snd f g).fiberι z ⁻¹' ((pullback.fst f g ⁻¹ᵁ U : (pullback f g).Opens) :
        Set ↥(pullback f g)) := by
  intro x' hx'
  rw [show ((pullback.fst f g ⁻¹ᵁ U : (pullback f g).Opens) : Set ↥(pullback f g)) =
    pullback.fst f g ⁻¹' (U : Set X) from rfl, Set.mem_preimage]
  have hmem : x' ∈ (pullback.snd f g).fiberι z ⁻¹' (pullback.fst f g ⁻¹' (U : Set X)) := by
    rw [preimage_baseChangeFiberMap_eq f g z U]
    exact h (mem_associatedPoints_fiber_of_baseChange f g F z x' hx')
  exact hmem

/-- **Half of Stacks Project, Tag 05KQ, as an inclusion of loci.** For `f` locally of finite
type, `F` quasi-coherent and `g` arbitrary, the inverse image under `g` of the fibrewise
containment locus of `(f, F, U)` is contained in the fibrewise containment locus of the base
change of `(f, F, U)` along `g`.

This is the form in which the limit argument of Stacks 05KR uses Stacks 05KQ, for the base
change `Spec A ⟶ Spec Aᵢ` onto a finite-type `ℤ`-subalgebra; that argument needs the opposite
inclusion as well, and only this one is proved. -/
theorem setOf_associatedPoints_fiber_subset_baseChange_subset (f : X ⟶ Y)
    [LocallyOfFiniteType f] (g : Y' ⟶ Y) (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens) :
    g ⁻¹' {y : Y | associatedPoints ((Scheme.Modules.pullback (f.fiberι y)).obj F) ⊆
        f.fiberι y ⁻¹' (U : Set X)} ⊆
      {z : Y' | associatedPoints ((Scheme.Modules.pullback ((pullback.snd f g).fiberι z)).obj
          ((Scheme.Modules.pullback (pullback.fst f g)).obj F)) ⊆
        (pullback.snd f g).fiberι z ⁻¹' ((pullback.fst f g ⁻¹ᵁ U : (pullback f g).Opens) :
          Set ↥(pullback f g))} :=
  fun z hz => associatedPoints_fiber_subset_of_baseChange f g F U z hz

end Stacks.Divisors

end
