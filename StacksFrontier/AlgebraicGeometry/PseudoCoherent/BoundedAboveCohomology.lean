module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedAbove
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedComplex
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentLocal

/-!
# Pseudo-coherence of a bounded above object from its cohomology sheaves

Let `X` be a ringed space, let `m` be an integer and let `E` be an object of `D(𝒪_X)` whose
cohomology sheaves vanish in high degrees on a neighbourhood of every point. If the cohomology
sheaf `H^i(E)`, viewed in degree zero, is `(m - i)`-pseudo-coherent for every `i ≥ m`, then `E` is
`m`-pseudo-coherent.

This is the companion of Stacks 09V7, which is the same statement with the *terms* of a complex
representing `E` in place of its cohomology sheaves; the source proves both with the hint "use
Lemma 08CD and truncations", and here the truncations are the canonical ones of the standard
t-structure rather than the stupid ones.

## Main results

* `CategoryTheory.Functor.mapDerivedCategoryObjHomologyIso`: an exact functor commutes with the
  cohomology of an object of the derived category.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_isGE_of_isLE`: an object concentrated in
  a single degree `a` is `m`-pseudo-coherent as soon as its cohomology there is
  `(m - a)`-pseudo-coherent in degree zero.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_homology_of_boundedAbove`: the globally
  bounded above case.
* `AlgebraicGeometry.RingedSpace.derivedRestrictModulesHomologyIso`: restriction to an open
  subspace commutes with cohomology.
* `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_homology_of_locally_boundedAbove`: the
  locally bounded above case.

## Implementation notes

No declaration in this file carries a `stacks` attribute. The statement about the cohomology
sheaves is a tag of its own in the source, but in this development it is a step towards the
relative statement of Stacks 09UQ, which is where the attribute sits; the tag is recorded in the
references below as a source, in the same spirit as
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairs`.

The induction is on the number of degrees between `m` and an upper bound for the cohomology, with
`m` fixed and the bound descending. At each step the canonical triangle
`τ^{<d}E ⟶ E ⟶ τ^{≥d}E` of the standard t-structure splits off the top cohomology degree: the
third vertex is concentrated in degree `d` and the first has one degree less room above `m`, so
Stacks 08CD part (2) assembles the two. The two comparison facts the induction needs about the
truncations are that `τ^{<d}` does not change the cohomology in degrees below `d` and `τ^{≥d}`
does not change it in degrees at least `d`; these are
`DerivedCategory.isIso_homologyFunctor_map_truncLTι` and
`DerivedCategory.isIso_homologyFunctor_map_truncGEπ`. When the bound equals
`m` the first vertex has no cohomology at all in degrees at least `m` and
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_isZero_homology_ge` finishes it.

An object concentrated in a single degree is isomorphic to its cohomology sheaf placed in that
degree (`DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`), and the passage from
degree zero to degree `a` is
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero`.

The hypothesis on the cohomology sheaves is only used in degrees at least `m`, which is weaker
than the source's hypothesis in every degree; the conclusion is the same.

Localizing is `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_restrict`, and it needs
the two hypotheses carried to the open subspace. Restriction is exact, so it commutes with
cohomology — that is
`CategoryTheory.Functor.mapDerivedCategoryObjHomologyIso` at the restriction functor, named here
`AlgebraicGeometry.RingedSpace.derivedRestrictModulesHomologyIso` — and
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedRestrictModules` together with
`AlgebraicGeometry.RingedSpace.derivedRestrictSingleFunctorIso` carries the pseudo-coherence of
each cohomology sheaf.

## References

* [Stacks Project, Lemma 20.46.15 (Tag 09V8)](https://stacks.math.columbia.edu/tag/09V8)
* [Stacks Project, Lemma 20.46.14 (Tag 09V7)](https://stacks.math.columbia.edu/tag/09V7)
* [Stacks Project, Lemma 20.46.10 (Tag 08CD)](https://stacks.math.columbia.edu/tag/08CD)
* [Stacks Project, Lemma 36.61.10 (Tag 09UQ)](https://stacks.math.columbia.edu/tag/09UQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open TopologicalSpace StrictlyPerfect

universe d d' u v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{d} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{d'} D]

/-- **An exact functor commutes with the cohomology of an object of the derived category.** For
`F : C ⥤ D` exact and `E` an object of `D(C)`, the `i`-th cohomology of `F(E)` is `F` applied to
the `i`-th cohomology of `E`.

Both sides are computed on a complex representing `E`: the derived functor is computed degreewise
there (`CategoryTheory.Functor.mapDerivedCategoryFactors`) and an exact functor commutes with the
homology of the short complex in each degree (`CategoryTheory.ShortComplex.mapHomologyIso`). -/
public def mapDerivedCategoryObjHomologyIso (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (E : DerivedCategory C) (i : ℤ) :
    (DerivedCategory.homologyFunctor D i).obj (F.mapDerivedCategory.obj E) ≅
      F.obj ((DerivedCategory.homologyFunctor C i).obj E) :=
  let K := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  (DerivedCategory.homologyFunctor D i).mapIso (F.mapDerivedCategory.mapIso e.symm) ≪≫
    (DerivedCategory.homologyFunctor D i).mapIso (F.mapDerivedCategoryFactors.app K) ≪≫
    (DerivedCategory.homologyFunctorFactors D i).app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≪≫
    (K.sc i).mapHomologyIso F ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors C i).app K).symm ≪≫
    F.mapIso ((DerivedCategory.homologyFunctor C i).mapIso e)

end CategoryTheory.Functor

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u, u}} [HasDerivedCategory.{d} (OXMod.{u, u} X)]

/-- **An object concentrated in a single degree is `m`-pseudo-coherent as soon as its cohomology
there is.** If `E` has no cohomology outside the degree `a` and `H^a(E)`, placed in degree zero, is
`(m - a)`-pseudo-coherent, then `E` is `m`-pseudo-coherent.

Such an `E` is isomorphic to `H^a(E)` placed in degree `a`
(`DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE`, with the module it produces
identified with `H^a(E)` through `DerivedCategory.singleFunctorCompHomologyFunctorIso`), and
placing a module in degree `a` shifts the pseudo-coherence bound by `a`
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero`). -/
public theorem isPseudoCoherentFrom_of_isGE_of_isLE (E : DerivedCategory (OXMod.{u, u} X))
    (a m : ℤ) [E.IsGE a] [E.IsLE a]
    (h : IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) a).obj E)) (m - a)) :
    IsPseudoCoherentFrom E m := by
  obtain ⟨Y, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE E a
  have q : (DerivedCategory.homologyFunctor (OXMod.{u, u} X) a).obj E ≅ Y :=
    (DerivedCategory.homologyFunctor (OXMod.{u, u} X) a).mapIso e ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (OXMod.{u, u} X) a).app Y
  exact (isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero _ m a h).ofIso
    ((DerivedCategory.singleFunctor (OXMod.{u, u} X) a).mapIso q ≪≫ e.symm)

/-- If `E` has no cohomology above degree `d` and `H^d(E)` is `(m - d)`-pseudo-coherent, then
`τ^{≥d}E` is `m`-pseudo-coherent. -/
private theorem isPseudoCoherentFrom_truncGE_of_homology (E : DerivedCategory (OXMod.{u, u} X))
    (d m : ℤ) [E.IsLE d]
    (h : IsPseudoCoherentFrom ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
      ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) d).obj E)) (m - d)) :
    IsPseudoCoherentFrom ((DerivedCategory.TStructure.t.truncGE d).obj E) m := by
  refine isPseudoCoherentFrom_of_isGE_of_isLE _ d m ?_
  let := DerivedCategory.isIso_homologyFunctor_map_truncGEπ d d le_rfl E
  exact h.ofIso ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).mapIso
    (asIso ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) d).map
      ((DerivedCategory.TStructure.t.truncGEπ d).app E))))

/-- The induction behind
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_homology_of_boundedAbove`, on the number
`n` of degrees between `m` and the upper bound. -/
private theorem isPseudoCoherentFrom_of_homology_aux (m : ℤ) (n : ℕ) :
    ∀ E : DerivedCategory (OXMod.{u, u} X), E.IsLE (m + n) →
      (∀ i : ℤ, m ≤ i → IsPseudoCoherentFrom
        ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
          ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E)) (m - i)) →
      IsPseudoCoherentFrom E m := by
  induction n with
  | zero =>
      intro E hLE hcoh
      let : E.IsLE m := by simpa using hLE
      have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished m E
      have h₁ : IsPseudoCoherentFrom ((DerivedCategory.TStructure.t.truncLT m).obj E) m :=
        isPseudoCoherentFrom_of_isZero_homology_ge _ m fun j hj =>
          DerivedCategory.isZero_of_isLE _ (m - 1) j (by omega)
      have h₃ := isPseudoCoherentFrom_truncGE_of_homology E m m (hcoh m le_rfl)
      exact isPseudoCoherentFrom_obj₂_of_distinguished m _ hT h₁ h₃
  | succ n ih =>
      intro E hLE hcoh
      have hcast : m + ((n + 1 : ℕ) : ℤ) = m + (n : ℤ) + 1 := by push_cast; ring
      let : E.IsLE (m + (n : ℤ) + 1) := hcast ▸ hLE
      have hT := DerivedCategory.TStructure.t.triangleLTGE_distinguished (m + (n : ℤ) + 1) E
      have h₁ : IsPseudoCoherentFrom
          ((DerivedCategory.TStructure.t.truncLT (m + (n : ℤ) + 1)).obj E) m := by
        refine ih _ (DerivedCategory.TStructure.t.isLE_of_le _ (m + (n : ℤ) + 1 - 1) _
          (by omega)) fun i hmi => ?_
        by_cases hi : i < m + (n : ℤ) + 1
        · let := DerivedCategory.isIso_homologyFunctor_map_truncLTι (m + (n : ℤ) + 1) i hi E
          exact (hcoh i hmi).ofIso ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).mapIso
            (asIso ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).map
              ((DerivedCategory.TStructure.t.truncLTι (m + (n : ℤ) + 1)).app E))).symm)
        · refine isPseudoCoherentFrom_of_isZero_homology_ge _ (m - i) fun j _ => ?_
          exact Functor.map_isZero _ (Functor.map_isZero _
            (DerivedCategory.isZero_of_isLE _ (m + (n : ℤ) + 1 - 1) i (by omega)))
      have h₃ := isPseudoCoherentFrom_truncGE_of_homology E (m + (n : ℤ) + 1) m
        (hcoh _ (by omega))
      exact isPseudoCoherentFrom_obj₂_of_distinguished m _ hT h₁ h₃

/-- **A bounded above object of `D(𝒪_X)` whose cohomology sheaves are pseudo-coherent is
pseudo-coherent.** If the cohomology of `E` vanishes in every degree above `b` and `H^i(E)`, placed
in degree zero, is `(m - i)`-pseudo-coherent for every `i ≥ m`, then `E` is `m`-pseudo-coherent.

This is the globally bounded above case; the induction runs over the degrees between `m` and the
larger of `b` and `m`. -/
public theorem isPseudoCoherentFrom_of_homology_of_boundedAbove (m b : ℤ)
    (E : DerivedCategory (OXMod.{u, u} X))
    (hb : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E))
    (hcoh : ∀ i : ℤ, m ≤ i → IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E)) (m - i)) :
    IsPseudoCoherentFrom E m := by
  let : E.IsLE (max b m) := by
    rw [DerivedCategory.isLE_iff]
    exact fun i hi => hb i (lt_of_le_of_lt (le_max_left b m) hi)
  exact isPseudoCoherentFrom_of_homology_aux m (max b m - m).toNat E
    (DerivedCategory.TStructure.t.isLE_of_le E (max b m) _ (by omega)) hcoh

/-! ### The locally bounded above case -/

variable [∀ U : Opens X.carrier,
  HasDerivedCategory.{d'} (OXMod.{u, u} (X.restrict U.isOpenEmbedding))]

/-- **Restriction to an open subspace commutes with cohomology.** The `i`-th cohomology sheaf of
`E|_U` is the restriction of the `i`-th cohomology sheaf of `E`.

This is `CategoryTheory.Functor.mapDerivedCategoryObjHomologyIso` at
`AlgebraicGeometry.RingedSpace.restrictModules`, which is exact by
`AlgebraicGeometry.RingedSpace.exactFunctor_restrictModules`. -/
public def derivedRestrictModulesHomologyIso (U : Opens X.carrier) (i : ℤ)
    (E : DerivedCategory (OXMod.{u, u} X)) :
    (DerivedCategory.homologyFunctor (OXMod.{u, u} (X.restrict U.isOpenEmbedding)) i).obj
        ((derivedRestrictModules X U).obj E) ≅
      (restrictModules X U).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E) :=
  (restrictModules X U).mapDerivedCategoryObjHomologyIso E i

/-- **A locally bounded above object of `D(𝒪_X)` whose cohomology sheaves are pseudo-coherent is
pseudo-coherent.** Let `E` be an object of `D(𝒪_X)` whose cohomology sheaves vanish in high degrees
on a neighbourhood of every point, and suppose that `H^i(E)`, placed in degree zero, is
`(m - i)`-pseudo-coherent for every `i ≥ m`. Then `E` is `m`-pseudo-coherent.

`m`-pseudo-coherence is local on `X`
(`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_local_restrict`), and on an open subspace
where the cohomology vanishes in high degrees the restriction of `E` satisfies the globally
bounded above statement
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_of_homology_of_boundedAbove`: its cohomology
sheaves are the restrictions of those of `E`, which are still pseudo-coherent in the same degrees
by `AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_derivedRestrictModules` and
`AlgebraicGeometry.RingedSpace.derivedRestrictSingleFunctorIso`. -/
public theorem isPseudoCoherentFrom_of_homology_of_locally_boundedAbove (m : ℤ)
    (E : DerivedCategory (OXMod.{u, u} X))
    (hbdd : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧ ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((restrictModules X U).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E)))
    (hcoh : ∀ i : ℤ, m ≤ i → IsPseudoCoherentFrom
      ((DerivedCategory.singleFunctor (OXMod.{u, u} X) 0).obj
        ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) i).obj E)) (m - i)) :
    IsPseudoCoherentFrom E m := by
  refine isPseudoCoherentFrom_of_local_restrict E m fun x => ?_
  obtain ⟨U, hxU, b, hb⟩ := hbdd x
  refine ⟨U, hxU, isPseudoCoherentFrom_of_homology_of_boundedAbove m b _
    (fun i hi => (hb i hi).of_iso (derivedRestrictModulesHomologyIso U i E)) fun i hi => ?_⟩
  exact ((isPseudoCoherentFrom_derivedRestrictModules _ (m - i) (hcoh i hi) U).ofIso
      (derivedRestrictSingleFunctorIso U 0 _)).ofIso
    ((DerivedCategory.singleFunctor _ 0).mapIso (derivedRestrictModulesHomologyIso U i E).symm)

end AlgebraicGeometry.RingedSpace

end
