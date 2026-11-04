module

public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.CategoryTheory.Retract
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedComplex
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.ImmersionIndependence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentSummand
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PushforwardOXMod
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StrictlyPerfectLocalRep

/-!
# The pushforward of a strictly perfect complex along a pseudo-coherent closed immersion

Let `i : Z ⟶ X` be a morphism of ringed spaces and assume that `i_*𝒪_Z` is a pseudo-coherent
`𝒪_X`-module, which is the hypothesis of Stacks 09VA. This file proves that `i_*𝒫` is an
`m`-pseudo-coherent object of `D(𝒪_X)` for every `m` and every strictly perfect complex `𝒫` of
`𝒪_Z`-modules.

That is the second of the two facts the forward half of Stacks 09VA rests on, the first being
exactness of `i_*` and hence `Ri_* = i_*`. The source instead runs an induction on the top
nonvanishing cohomological degree of `E`; replacing the induction by the local strictly perfect
approximation that `m`-pseudo-coherence of `E` provides turns the forward half into this file
plus the localization.

## Main results

* `CategoryTheory.exists_iso_biprod_of_retract`: a retract in an abelian category is a direct
  summand, that is, the ambient object is a binary biproduct with the retract as one factor.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_of_retract_biproduct`: a
  retract of `G^{⊕n}` placed in degree `j` is `m`-pseudo-coherent as soon as `G` placed in
  degree `j` is.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_pushforward`: the
  pushforward of a direct summand of a finite free `𝒪_Z`-module, placed in any degree, is
  `m`-pseudo-coherent.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_pushforward_isStrictlyPerfect`: the
  degreewise pushforward of a strictly perfect complex is `m`-pseudo-coherent.

## Implementation notes

`StrictlyPerfect.IsDirectSummandOfFiniteFree` is phrased as a `CategoryTheory.Retract` of
`𝒪_Z^{⊕n}`, so to apply Stacks 064X
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_biprod`, in the form with a global
degree bound) the retract first has to be split off as a genuine biproduct factor. In an abelian
category that is `CategoryTheory.ShortComplex.Splitting.ofExactOfRetraction` applied to
`0 ⟶ A ⟶ F ⟶ coker ⟶ 0`, followed by
`CategoryTheory.ShortComplex.Splitting.isoBinaryBiproduct`.

The degree bound needed by
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_biprod_of_isZero_homology_gt` is
available *globally* here, because the object in question is concentrated in a single degree;
that is why the localizing form of Stacks 064X — which would force instance hypotheses about the
doubly restricted spaces — is not needed, and the statements below carry only
`[HasDerivedCategory (OXMod Y)]`.

`CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts` is a lemma and not an
instance, so `CategoryTheory.Functor.mapBiprod` on `DerivedCategory.singleFunctor` needs it
declared as a local instance.

Passing from degree zero to degree `j` is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero`; the
hypothesis of Stacks 09VA is about `i_*𝒪_Z` in degree zero, while the terms of `i_*𝒫` are used
in their own degrees.

## References

* [Stacks Project, Tag 064X](https://stacks.math.columbia.edu/tag/064X)
* [Stacks Project, Lemma 20.46.14 (Tag 09V7)](https://stacks.math.columbia.edu/tag/09V7)
* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

universe d u v₁ u₁

attribute [local instance] CategoryTheory.Limits.preservesBinaryBiproducts_of_preservesBiproducts

namespace CategoryTheory

/-- **A retract in an abelian category is a direct summand.** If `A` is a retract of `F` then `F`
is a binary biproduct of `A` and the cokernel of the retract inclusion.

The short complex `A ⟶ F ⟶ coker` is exact with `F ⟶ coker` an epimorphism, and the retraction
splits it, so `CategoryTheory.ShortComplex.Splitting.isoBinaryBiproduct` applies. -/
public theorem exists_iso_biprod_of_retract {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {A F : C} (h : Retract A F) : ∃ B : C, Nonempty (F ≅ A ⊞ B) :=
  ⟨Limits.cokernel h.i, ⟨(ShortComplex.Splitting.ofExactOfRetraction
    (ShortComplex.mk h.i (Limits.cokernel.π h.i) (Limits.cokernel.condition h.i))
    (ShortComplex.exact_of_g_is_cokernel _ (Limits.cokernelIsCokernel h.i)) h.r h.retract
    inferInstance).isoBinaryBiproduct⟩⟩

end CategoryTheory

namespace AlgebraicGeometry.RingedSpace

/-! ### Modules placed in a single degree -/

variable {Y : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} Y)]

/-- The cohomology of an `𝒪_Y`-module placed in degree `j` in the derived category vanishes in
every degree other than `j`: the complex representing it is the module placed in degree `j`. -/
public theorem isZero_homology_singleFunctor_of_ne (F : OXMod.{u, u} Y) (j k : ℤ) (hk : k ≠ j) :
    IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) k).obj
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) j).obj F)) :=
  IsZero.of_iso (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) j F k hk)
    ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) k).mapIso
      ((DerivedCategory.singleFunctorIsoCompQ (OXMod.{u, u} Y) j).app F) ≪≫
      derivedHomologyIso
        ((HomologicalComplex.single (OXMod.{u, u} Y) (ComplexShape.up ℤ) j).obj F) k)

/-- **A retract of `G^{⊕n}` placed in degree `j` is `m`-pseudo-coherent as soon as `G` placed in
degree `j` is.**

Split the retract off as a biproduct factor (`CategoryTheory.exists_iso_biprod_of_retract`) and
apply `DerivedCategory.singleFunctor j`, which is additive and therefore carries the `n`-fold
biproduct of `G` to the `n`-fold biproduct of `G` in degree `j` — `m`-pseudo-coherent by
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_biproduct_const` — and the splitting to a
binary biproduct of the two factors in degree `j`. Both have no cohomology above degree `j`, so
Stacks 064X in the form with a global degree bound finishes. -/
public theorem isPseudoCoherentFrom_singleFunctor_of_retract_biproduct (m j : ℤ)
    {A G : OXMod.{u, u} Y} {n : ℕ} (h : Retract A (biproduct (fun _ : Fin n => G)))
    (hG : IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) j).obj G) m) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) j).obj A) m := by
  obtain ⟨B, ⟨e⟩⟩ := CategoryTheory.exists_iso_biprod_of_retract h
  have eS : (DerivedCategory.singleFunctor (OXMod.{u, u} Y) j).obj
        (biproduct (fun _ : Fin n => G)) ≅
      (DerivedCategory.singleFunctor (OXMod.{u, u} Y) j).obj A ⊞
        (DerivedCategory.singleFunctor (OXMod.{u, u} Y) j).obj B :=
    (DerivedCategory.singleFunctor (OXMod.{u, u} Y) j).mapIso e ≪≫
      (DerivedCategory.singleFunctor (OXMod.{u, u} Y) j).mapBiprod A B
  have eB : (DerivedCategory.singleFunctor (OXMod.{u, u} Y) j).obj
        (biproduct (fun _ : Fin n => G)) ≅
      biproduct (fun _ : Fin n => (DerivedCategory.singleFunctor (OXMod.{u, u} Y) j).obj G) :=
    Functor.mapBiproduct _ _
  refine (isPseudoCoherentFrom_of_biprod_of_isZero_homology_gt m j
    ((isPseudoCoherentFrom_biproduct_const m hG n).ofIso (eB.symm ≪≫ eS)) fun k hk => ?_).1
  exact (isZero_homology_singleFunctor_of_ne (biproduct (fun _ : Fin n => G)) j k
    (by omega)).of_iso ((DerivedCategory.homologyFunctor (OXMod.{u, u} Y) k).mapIso eS.symm)

/-- A pseudo-coherent `𝒪_Y`-module placed in any degree `j` is `m`-pseudo-coherent for every `m`:
placing it in degree `j` is shifting by `-j`, and shifting by `-j` shifts the pseudo-coherence
bound by `j`.

The hypothesis is the degreewise form of pseudo-coherence of the module — `k`-pseudo-coherence
in degree zero for every `k` — rather than
`AlgebraicGeometry.RingedSpace.IsPseudoCoherent`, which is formally stronger because it asks for
one complex that works for all `k` at once. Only the weaker form is used, and only the weaker
form survives restriction to an open subspace. -/
public theorem isPseudoCoherentFrom_singleFunctor_of_isPseudoCoherent {G : OXMod.{u, u} Y}
    (hG : ∀ k : ℤ, IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) 0).obj G) k)
    (m j : ℤ) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} Y) j).obj G) m :=
  isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero G m j (hG (m - j))

/-! ### The pushforward of a strictly perfect complex -/

variable {Z X : RingedSpace.{u, u}} (i : Z ⟶ X) [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- **The pushforward of a direct summand of a finite free `𝒪_Z`-module, placed in any degree, is
`m`-pseudo-coherent**, as soon as `i_*𝒪_Z` is a pseudo-coherent `𝒪_X`-module.

Pushforward is additive, so it carries a retract of `𝒪_Z^{⊕n}` to a retract of
`(i_*𝒪_Z)^{⊕n}` (`AlgebraicGeometry.RingedSpace.pushforwardFiniteFreeIso`), and
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_of_retract_biproduct`
applies. -/
public theorem isPseudoCoherentFrom_singleFunctor_pushforward
    (hO : ∀ k : ℤ, IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
      (pushforwardStructureModule i)) k)
    (m j : ℤ) {A : OXMod.{u, u} Z} (hA : IsDirectSummandOfFiniteFree A) :
    IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) j).obj
      ((pushforwardOXMod i).obj A)) m := by
  obtain ⟨n, ⟨ret⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract _).mp hA
  exact isPseudoCoherentFrom_singleFunctor_of_retract_biproduct m j
    ((ret.map (pushforwardOXMod i)).trans
      ⟨(pushforwardFiniteFreeIso i n).hom, (pushforwardFiniteFreeIso i n).inv, by simp⟩)
    (isPseudoCoherentFrom_singleFunctor_of_isPseudoCoherent hO m j)

/-- **The degreewise pushforward of a strictly perfect complex of `𝒪_Z`-modules is an
`m`-pseudo-coherent object of `D(𝒪_X)`**, for every `m`, as soon as `i_*𝒪_Z` is a
pseudo-coherent `𝒪_X`-module.

The pushforward complex is bounded, because a strictly perfect complex has only finitely many
nonzero terms and pushforward carries a zero module to a zero module, and each of its terms,
placed in its own degree, is `m`-pseudo-coherent by
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_pushforward`. The passage from
the terms to the complex is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_of_bounded`.

This is what the forward half of Stacks 09VA applies to a local strictly perfect approximation
of `E`. -/
public theorem isPseudoCoherentFrom_Q_pushforward_isStrictlyPerfect (m : ℤ)
    (hO : ∀ k : ℤ, IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
      (pushforwardStructureModule i)) k)
    {P : CochainComplex (OXMod.{u, u} Z) ℤ} (hP : IsStrictlyPerfect P) :
    IsPseudoCoherentFrom (DerivedCategory.Q.obj
      (((pushforwardOXMod i).mapHomologicalComplex (ComplexShape.up ℤ)).obj P)) m := by
  obtain ⟨a, ha⟩ := Stacks.Cohomology.LocalNullHomotopy.exists_lower_bound hP
  obtain ⟨b, hb⟩ := exists_forall_gt_isZero hP
  refine isPseudoCoherentFrom_Q_of_bounded m _ ⟨a, b, fun p hp => ?_, fun p hp => ?_⟩ fun k =>
    isPseudoCoherentFrom_singleFunctor_pushforward i hO m k (hP.directSummand k)
  · exact Functor.map_isZero (pushforwardOXMod i) (ha p hp)
  · exact Functor.map_isZero (pushforwardOXMod i) (hb p hp)

end AlgebraicGeometry.RingedSpace

end
