module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.DerivedSectionsAndInverseLimits
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.LocallyBijectiveHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.PushforwardBoundedCohomologicalDimension
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.TruncationConvergenceWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CohomologySheavesOfTheDerivedDirectImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.DerivedGlobalSectionsOfModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.DerivedDirectImageAndRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.Exactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.SingleObject
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedToposSiteHomOfRingedSite
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.EventuallyConstantDifference
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorTriangleOfTower
import StacksCore.Tactic.StacksAttribute

/-!
# Bounded cohomological dimension of a derived direct image, with bounds on the target

Let `f : (C, O) ⟶ (C', O')` be a morphism of ringed sites, let `A ⊂ Mod(O)` be a weak Serre
subcategory and let `N` be an integer such that

* `C, O, A` satisfy the standing Olsson--Laszlo hypothesis of Stacks 0D6R: there is a class `B`
  of objects covering every object of `C`, and every `V ∈ B` carries an integer bound `d_V` and a
  cofinal system of coverings of `V` on whose members the cohomology of every module of `A`
  vanishes in degrees `> d_V`;
* `f` and `A` satisfy the standing hypothesis of Stacks 0D6V, the relative version of the
  previous one: there is a class `B'` of objects covering every object of `C'`, and every
  `V' ∈ B'` carries an integer bound `d_{V'}` and a cofinal system of coverings of `V'` such that
  the cohomology, computed on `C` over the image `u(V'_i)` of a member, of every module of `A`
  vanishes in degrees `> d_{V'}`;
* `Rᵖf_*F = 0` for every `p > N` and every `F` of `A`.

Then for every `K` of `D_A(O)` the canonical map

`Hʲ(Rf_*K) ⟶ Hʲ(Rf_*(τ_{≥ -n}K))`

induced by the truncation `K ⟶ τ_{≥ -n}K` is an isomorphism for every `j ≥ N - n`. This is
Stacks 0D6W, a version of [Laszlo--Olsson, six-I, Lemma 2.1.10] with slightly changed
hypotheses, and the content of this file. It differs from Stacks 0D6U, which concludes the same
in the presence of a weak Serre subcategory `A' ⊂ Mod(O')` satisfying the hypothesis of Stacks
0D6R and receiving the higher direct images of `A`: here no subcategory of `Mod(O')` is given,
and the local cohomological bounds on the target are the relative ones of Stacks 0D6V.

## The argument

Both sides of the map are cohomology *sheaves* on `C'`, and such a sheaf is the sheafification of
the presheaf `V' ↦ Hʲ(V', Rf_*-)` (Stacks 0D6I); so the assertion is that the induced map of
those presheaves is locally bijective, and that may be checked over the members of the cofinal
coverings of the objects of `B'`, allowing a locally bijective approximation over each of them
(Stacks 0D6T's local criterion). Fix `V' ∈ B'` and factor the map as

`Hʲ(Rf_*K) ⟶ Hʲ(Rf_*(τ_{≥ -m}K)) ⟶ Hʲ(Rf_*(τ_{≥ -n}K))`

for an `m ≥ n` depending on `V'`, `j` and `d_{V'}`. The second factor is invertible already as a
map of sheaves: the vanishing of `Rᵖf_*` above `N` makes the transition maps of the tower
`n ↦ Hʲ(Rf_*(τ_{≥ -n}K))` invertible from the index `N - j` on, which is Stacks 0D6U's
stabilisation lemma and needs nothing about the target site. The first factor is invertible on
sections over every member of every distinguished covering of `V'`, because over such a member
`V'_i` the value of the presheaf is `Hʲ(u(V'_i), K)` — again Stacks 0D6I — and there the bound
`d_{V'}` of Stacks 0D6V applies: the fibre of a transition map of the truncation tower is a
single cohomology module of `K`, hence lies in `A`, so its derived sections over `u(V'_i)` are
concentrated in a band of width `d_{V'}`, the tower `k ↦ Hʲ(u(V'_i), τ_{≥ -k}K)` is eventually
constant, and the Milnor short exact sequence of Stacks 0D6K — whose outer terms are therefore a
single late stage and zero — identifies `Hʲ(u(V'_i), K)` with that stage. The convergence of the
truncation tower that the Milnor sequence rests on is Stacks 0D6S, the only place where the
hypothesis of Stacks 0D6R on the source enters.

## Main results

* `Stacks.Cohomology.OlssonLaszlo.isIso_homology_derivedPushforward_truncGEπ_of_relativeSituation`
  (Stacks 0D6W): the truncation comparison is an isomorphism on `Hʲ` for `j ≥ N - n`.
* `isIso_homology_derivedPushforward_truncGEπ_of_relativeSituation_of_flat`, in the same
  namespace: the same for a flat morphism, with the carried input of Stacks 093Y discharged.

Along the way:

* `Stacks.Cohomology.OlssonLaszlo.isIso_homology_derivedPushforward_map_iff_w`: a map is inverted
  by the degree-`j` cohomology sheaf of `Rf_*` exactly when the induced map of the cohomology
  presheaves on the target site is locally bijective.
* `Stacks.Cohomology.OlssonLaszlo.isZero_homology_derivedSectionsOverObject_single`: a module
  whose cohomology over `U` vanishes above `d`, placed in degree `a`, has derived sections over
  `U` concentrated in degrees `≤ a + d`.
* `Stacks.Cohomology.OlssonLaszlo.isIso_homologyMap_derivedSectionsOverObject_truncGETower_succ`:
  consequently one step of the truncation tower is invertible on `Hʲ(U, -)` once the index is
  large compared with `j` and `d`.
* `Stacks.Cohomology.OlssonLaszlo.isIso_homologyMap_derivedSectionsOverObject_truncGEπ`:
  `Hʲ(U, K) ⟶ Hʲ(U, τ_{≥ -m}K)` is an isomorphism for `m` large.

## Implementation notes

**The two standing hypotheses are carried as loose data**, as they are for Stacks 0D6U and
0D7V: a class of objects of each site, an integer bound and a cofinal system of coverings of each
member of the class, rather than as `Stacks.Cohomology.OlssonLaszloSituation` and
`Stacks.Cohomology.OlssonLaszloPrimeSituation` arguments, because each of those structures
bundles its own site and sheaf of rings, which here must be those of `X` and of `Y`. The
situation of Stacks 0D6R on the source is assembled from that data internally, so the hypotheses
are the fields of Stacks 0D6R and of Stacks 0D6V verbatim; in particular the cohomology appearing
in the hypothesis read from Stacks 0D6V is cohomology on the *source* site, over the image
`f.u.obj (𝒰.X i)` of a member of a distinguished covering of the target.

**`Rᵖf_*F` is read as `Hᵖ(Rf_*(F[0]))`**, the convention of Stacks 0D6U: the `p`-th cohomology
sheaf of the unbounded derived direct image of `F` placed in degree zero. Every statement is
then about one and the same functor, the unbounded `Rf_*` of Stacks 07A5, and no comparison
between a bounded below and the unbounded derived functor is needed.

**Stacks 093Y is carried as the named hypothesis `h093Y`**, exactly as it is by the library's
Stacks 0D6H and 0D6I, on which the identification `Hʲ(V', Rf_*K) = Hʲ(u(V'), K)` used here
rests: degreewise `f_*` carries K-injective complexes of `O`-modules to K-injective complexes of
`O'`-modules. It is not a hypothesis of the source, which obtains the identification from the
composition law of Stacks 0D6E instead; it is discharged for a flat morphism of ringed sites by
`Stacks.Cohomology.LerayUnbounded.isKInjective_pushforwardTopos_of_flat`, which gives the
`…_of_flat` form of the result. Whoever proves Stacks 093Y for a general morphism of ringed sites
obtains the unrestricted statement by one application.

**The morphism is a morphism of ringed sites**, `AlgebraicGeometry.RingedSite.Hom`, read as a
site-presented morphism of ringed topoi through
`AlgebraicGeometry.RingedSite.Hom.toRingedToposSiteHom` where the derived direct image and the
results of Stacks 0D6U are stated. The three universes of both ringed sites are collapsed, as
they already are in `AlgebraicGeometry.RingedSite.Hom` and throughout the unbounded derived
development on sites.

**Derived sections over an object are the abelian-group-valued ones**,
`Stacks.Cohomology.Localization.derivedSectionsOverObject`, since that is the functor the
identification of Stacks 0D6I and the Milnor sequence of Stacks 0D6K are stated for; the
vanishing hypotheses are phrased with `Stacks.Cohomology.moduleCohomology`, the module-valued
cohomology of Stacks 0D6R, and the two are compared by exactness of the forgetful functor.

## References

* [Stacks Project, Tag 0D6W](https://stacks.math.columbia.edu/tag/0D6W)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
* [Stacks Project, Tag 0D6V](https://stacks.math.columbia.edu/tag/0D6V)
* [Stacks Project, Tag 0D6S](https://stacks.math.columbia.edu/tag/0D6S)
* [Stacks Project, Tag 0D6K](https://stacks.math.columbia.edu/tag/0D6K)
* [Stacks Project, Tag 0D6I](https://stacks.math.columbia.edu/tag/0D6I)
* [Stacks Project, Tag 0D6U](https://stacks.math.columbia.edu/tag/0D6U)
* [Stacks Project, Tag 093Y](https://stacks.math.columbia.edu/tag/093Y)
* [Stacks Project, Tag 08J5](https://stacks.math.columbia.edu/tag/08J5)
* [Stacks Project, Tag 07A5](https://stacks.math.columbia.edu/tag/07A5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry

namespace Stacks.Cohomology.OlssonLaszlo

universe u

attribute [local instance 2000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

open Stacks.Cohomology.Localization (sectionsOverObject homotopySectionsOverObject
  derivedSectionsOverObject)
open Stacks.Cohomology.ModuleSections (derivedSectionsOverObjectUnit)

section Local

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- **Cohomology of a module over an object computes the right derived functors of sections.**
If the cohomology module `Hᵖ(U, M)` vanishes then so does the `p`-th right derived functor of
sections over `U` with values in abelian groups, the forgetful functor being exact. -/
lemma isZero_rightDerived_sectionsOverObject (U : X.C)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (p : ℕ)
    (h : IsZero (moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U p M)) :
    IsZero (((sectionsOverObject X U).rightDerived p).obj M) := by
  let E := SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (Opposite.op U)
  let G := forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj
    (Opposite.op U))) AddCommGrpCat.{u}
  let _ : E.Additive := ⟨rfl⟩
  exact IsZero.of_iso (G.map_isZero h) (rightDerivedExactPostcompositionIso E G M p).symm

/-- **Derived sections over an object of a module placed in a single degree are concentrated in a
band of width the cohomological bound.** If the cohomology of `M` over `U` vanishes above `d`,
then the derived sections over `U` of `M` placed in degree `a` have no cohomology in any degree
`m` with `a < m` and `a + d < m`. -/
lemma isZero_homology_derivedSectionsOverObject_single (U : X.C)
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (d : ℤ)
    (hM : ∀ p : ℕ, d < (p : ℤ) → IsZero
      (moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U p M))
    (a m : ℤ) (ham : a < m) (hd : a + d < m) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).obj
      ((derivedSectionsOverObject X U).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a).obj M))) := by
  refine IsZero.of_iso ?_ (Stacks.DerivedFunctor.homologyTotalRightDerivedSingleShiftIso
    (sectionsOverObject X U) (derivedSectionsOverObject X U) (derivedSectionsOverObjectUnit X U)
    Stacks.Cohomology.Localization.enoughKInjectives M a m (m - a).toNat (by omega))
  exact isZero_rightDerived_sectionsOverObject X U M (m - a).toNat (hM _ (by omega))

/-- **The derived sections over an object of a one-step interval truncation are concentrated in a
band of width the cohomological bound.** The interval truncation `τ_{< a + 1}(τ_{≥ a}K)` is the
cohomology module `H^a(K)` placed in degree `a`, so the previous lemma applies to it. -/
lemma isZero_homology_derivedSectionsOverObject_truncLTGE (U : X.C)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (d a b : ℤ) (hb : a + 1 = b)
    (hK : ∀ p : ℕ, d < (p : ℤ) → IsZero
      (moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U p
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a).obj K)))
    (i : ℤ) (hi : a < i) (hid : a + d < i) :
    IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
      ((derivedSectionsOverObject X U).obj
        ((DerivedCategory.TStructure.t.truncLTGE a b).obj K))) := by
  subst hb
  obtain ⟨e⟩ := Stacks.TruncationLevel.nonempty_iso_singleFunctor_truncLTGE a K
  refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).mapIso
    ((derivedSectionsOverObject X U).mapIso e))
  exact isZero_homology_derivedSectionsOverObject_single X U _ d hK a i hi hid

/-- **One step of the truncation tower is invertible on the cohomology of derived sections over an
object, above the cohomological bound.** The fibre of `τ_{≥ a}K ⟶ τ_{≥ a + 1}K` is `H^a(K)` placed
in degree `a`, whose derived sections over `U` have no cohomology in degrees `> a + d`; a map in a
distinguished triangle whose complementary vertex has no cohomology in the two adjacent degrees is
inverted by cohomology. -/
lemma isIso_homologyMap_derivedSectionsOverObject_natTransTruncGEOfLE (U : X.C)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (d a b : ℤ) (hb : a + 1 = b)
    (hab : a ≤ b)
    (hK : ∀ p : ℕ, d < (p : ℤ) → IsZero
      (moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U p
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) a).obj K)))
    (j : ℤ) (hj : a < j) (hjd : a + d < j) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).map
      ((derivedSectionsOverObject X U).map
        ((DerivedCategory.TStructure.t.natTransTruncGEOfLE a b hab).app K))) := by
  let _ := Functor.IsRightDerivedFunctor.commShift (derivedSectionsOverObject X U)
    (derivedSectionsOverObjectUnit X U)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (ComplexShape.up ℤ)) ℤ
  have htri : (derivedSectionsOverObject X U).IsTriangulated :=
    Stacks.DerivedFunctor.isTriangulated_of_isRightDerivedFunctor
      Stacks.Cohomology.Localization.enoughKInjectives (homotopySectionsOverObject X U)
      (derivedSectionsOverObject X U) (derivedSectionsOverObjectUnit X U)
  obtain ⟨δ, hδ⟩ := Stacks.TruncationLevel.exists_distTriang_truncGE
    DerivedCategory.TStructure.t a b hab K
  exact Stacks.TruncationLevel.isIso_homologyMap_mor₂ _
    ((derivedSectionsOverObject X U).map_distinguished _ hδ) j
    (isZero_homology_derivedSectionsOverObject_truncLTGE X U K d a b hb hK j hj hjd)
    (isZero_homology_derivedSectionsOverObject_truncLTGE X U K d a b hb hK (j + 1)
      (by omega) (by omega))

/-- **The transition maps of the truncation tower are invertible on the cohomology of derived
sections over an object, once the index is large compared with the degree and the cohomological
bound.** This is the successor-indexed form that the vanishing of `R¹lim` and the eventual
constancy of the tower both consume. -/
lemma isIso_homologyMap_derivedSectionsOverObject_truncGETower_succ (U : X.C)
    (P : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB P K) (d : ℤ)
    (hvan : ∀ p : ℕ, d < (p : ℤ) →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), P F →
      IsZero (moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U p F))
    (j : ℤ) (k : ℕ) (hk : -j ≤ (k : ℤ)) (hkd : d - j ≤ (k : ℤ)) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).map
      ((derivedSectionsOverObject X U).map
        ((Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).map
          (homOfLE (Nat.le_succ k)).op))) := by
  rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
  exact isIso_homologyMap_derivedSectionsOverObject_natTransTruncGEOfLE X U K d
    (-((k + 1 : ℕ) : ℤ)) (-(k : ℤ)) (by omega) (by omega)
    (fun p hp ↦ hvan p hp _ (hK _)) j (by omega) (by omega)

/-- **Truncation from below does not change the cohomology of derived sections over an object, in
the range allowed by the local cohomological bound.** Let `K` be an object of the derived category
whose cohomology modules all satisfy `P`, let the cohomology over `U` of every module satisfying
`P` vanish above `d`, and assume `K` is a derived limit of its truncation tower in the strong sense
that every comparison map to such a derived limit is invertible (which is Stacks 0D6S in the
Olsson--Laszlo situation). Then `H^j(U, K) ⟶ H^j(U, τ_{≥ -m}K)` is an isomorphism as soon as
`m ≥ 1 - j` and `m ≥ d - j + 1`.

The tower of cohomology modules `n ↦ H^j(U, τ_{≥ -n}K)` has invertible transition maps past `m`,
so its first derived inverse limit vanishes and its inverse limit is the stage `m`; the Milnor
short exact sequence of Stacks 0D6K then identifies `H^j(U, K)` with that stage. -/
theorem isIso_homologyMap_derivedSectionsOverObject_truncGEπ (U : X.C)
    (P : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦
      (Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).obj ⟨n⟩]
    (hK : DerivedCategoryB.derivedCategoryB P K) (d : ℤ)
    (hvan : ∀ p : ℕ, d < (p : ℤ) →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), P F →
      IsZero (moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U p F))
    (hconv : ∀ (L : DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (c : K ⟶ L)
      (pr : L ⟶ ∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).obj ⟨n⟩)
      (δ : (∏ᶜ fun n : ℕ ↦
        (Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).obj ⟨n⟩) ⟶
          L⟦(1 : ℤ)⟧),
      Triangle.mk pr (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).obj ⟨n⟩)
            (n + 1) ≫
          (Stacks.DerivedLimit.truncGETower
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).map
            (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang
            (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) →
        (∀ n : ℕ, c ≫ pr ≫ Pi.π (fun n : ℕ ↦
          (Stacks.DerivedLimit.truncGETower
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).obj ⟨n⟩) n =
          (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K) → IsIso c)
    (j : ℤ) (m : ℕ) (hm : 1 - j ≤ (m : ℤ)) (hmd : d - j + 1 ≤ (m : ℤ)) :
    IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).map
      ((derivedSectionsOverObject X U).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K))) := by
  obtain ⟨δ, hδ⟩ := Stacks.InverseSystem.exists_distTriang_milnor_of_isIso
    (Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K)
    (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)
    (fun n ↦ by
      rw [Stacks.DerivedLimit.truncGETower_map_homOfLE_succ]
      exact DerivedCategory.TStructure.t.π_natTransTruncGEOfLE_app
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega) K)
    hconv
  obtain ⟨_, _, _, _, _, _, _, r, _, _, _, hseq, hr⟩ :=
    Stacks.Cohomology.DerivedSectionsMilnor.exists_shortExact_limOne_cohomology_derivedSections
      X U (Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K) K
      (Pi.lift fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)
      ⟨δ, hδ⟩ j
  have hzero := Stacks.InverseSystem.isZero_cokernel_milnorDifference_functor
    ((Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K ⋙
      derivedSectionsOverObject X U) ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u} (j - 1)) m
    (fun n hn ↦ isIso_homologyMap_derivedSectionsOverObject_truncGETower_succ X U P K hK d hvan
      (j - 1) n (by omega) (by omega))
  have hπlim : IsIso (limit.π ((Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K ⋙
        derivedSectionsOverObject X U) ⋙
      DerivedCategory.homologyFunctor AddCommGrpCat.{u} j) ⟨m⟩) :=
    (isEventuallyConstantTo_of_isIso_succ _ m fun n hn ↦
      isIso_homologyMap_derivedSectionsOverObject_truncGETower_succ X U P K hK d hvan
        j n (by omega) (by omega)).isIso_π_of_isLimit (limit.isLimit _)
  have hlift : (Pi.lift (f := fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).obj ⟨n⟩)
        fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K) ≫
      Pi.π (fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).obj ⟨n⟩) m =
      (DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K :=
    Pi.lift_π (f := fun n : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).obj ⟨n⟩)
      (fun n : ℕ ↦ (DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K) m
  have h3 : (DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).map
        ((derivedSectionsOverObject X U).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K)) =
      r ≫ limit.π ((Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K ⋙
          derivedSectionsOverObject X U) ⋙
        DerivedCategory.homologyFunctor AddCommGrpCat.{u} j) ⟨m⟩ :=
    (congrArg (fun f ↦ (DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).map
      ((derivedSectionsOverObject X U).map f)) hlift).symm.trans (hr m).symm
  rw [h3]
  exact IsIso.comp_isIso' (hseq.isIso_g_iff.mpr hzero) hπlim

end Local

section Relative

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction (derivedPushforward)
open Stacks.Cohomology.SiteCohomologyPresheaf (derivedSectionsPresheaf)
open Stacks.Cohomology.UnboundedHigherDirectImageOnSites

variable {X Y : RingedSite.{u, u, u}} (f : RingedSite.Hom X Y)
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]

attribute [local instance] AlgebraicGeometry.RingedSite.Hom.pushforwardTopos_additive

/-- The presheaf of degree-`j` cohomology of the unbounded derived direct image, with values read
as presheaves of abelian groups on the target site. This is the presheaf `V ↦ H^j(V, Rf_*K)` of
Stacks 0D6I, whose sheafification is the degree-`j` cohomology sheaf of `Rf_*K`. -/
abbrev derivedPushforwardCohomologyAbPresheafFunctor (j : ℤ) :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      (Y.Cᵒᵖ ⥤ AddCommGrpCat.{u}) :=
  derivedPushforward.{u} f.toRingedToposSiteHom ⋙ derivedSectionsPresheaf Y ⋙
    DerivedCategory.homologyFunctor
      (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) j ⋙
    PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj

omit [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))] in
/-- **The cohomology sheaves of a derived direct image are a local matter on the target site.**
A map of `D(O_X)` is inverted by the degree-`j` cohomology sheaf of `Rf_*` exactly when the
induced map of the cohomology presheaves `V ↦ H^j(V, Rf_*-)` is locally bijective, because the
cohomology sheaf is the sheafification of that presheaf. -/
theorem isIso_homology_derivedPushforward_map_iff_w
    {K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : K ⟶ L) (j : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
        ((derivedPushforward.{u} f.toRingedToposSiteHom).map g)) ↔
      Y.J.W ((derivedPushforwardCohomologyAbPresheafFunctor f j).map g) := by
  show IsIso ((derivedPushforward.{u} f.toRingedToposSiteHom ⋙
    DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map g) ↔ _
  rw [NatIso.isIso_map_iff (higherDirectImageIsoSheafifyCohomologyPresheaf f j) g]
  exact Iff.symm (show
    (Y.J.W.inverseImage
      (PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)) _ ↔
    ((MorphismProperty.isomorphisms _).inverseImage
      (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj))) _ by
    rw [PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)])

variable (A : ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  [hA : A.IsWeakSerreClass]
  (B : Set X.C)
  (basisCover : ∀ U : X.C, ∃ 𝒰 : PreZeroHypercover.{u} U,
    𝒰.sieve₀ ∈ X.J U ∧ ∀ i, B (𝒰.X i))
  (degreeBound : ∀ V : X.C, B V → ℤ)
  (coverings : ∀ V : X.C, B V → Stacks.Cohomology.CofinalCoveringSystem X.J V)
  (vanishing : ∀ (V : X.C) (hV : B V) (𝒰 : PreZeroHypercover.{u} V),
    (coverings V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
        IsZero (moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (𝒰.X i) p F))
  (B' : Set Y.C)
  (basisCover' : ∀ U : Y.C, ∃ 𝒰 : PreZeroHypercover.{u} U,
    𝒰.sieve₀ ∈ Y.J U ∧ ∀ i, B' (𝒰.X i))
  (degreeBound' : ∀ V : Y.C, B' V → ℤ)
  (coverings' : ∀ V : Y.C, B' V → Stacks.Cohomology.CofinalCoveringSystem Y.J V)
  (vanishing' : ∀ (V : Y.C) (hV : B' V) (𝒰 : PreZeroHypercover.{u} V),
    (coverings' V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound' V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
        IsZero
          (moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O) (f.u.obj (𝒰.X i)) p F))
  (N : ℤ)
  (hvanishImage : ∀ p : ℕ, N < (p : ℤ) →
    ∀ F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
    IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (p : ℤ)).obj
      ((derivedPushforward.{u} f.toRingedToposSiteHom).obj
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj F))))
  (h093Y : ∀ I : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ, I.IsKInjective →
    CochainComplex.IsKInjective
      ((f.toRingedToposSiteHom.pushforwardTopos.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I))

/-- The Olsson--Laszlo situation of Stacks 0D6R on the source ringed site, assembled from the
loose data of a locally covering class of objects with cofinal systems of coverings and integer
bounds. -/
private def sourceSituation : Stacks.Cohomology.OlssonLaszloSituation.{u, u, u, u} where
  C := X.C
  J := X.J
  O := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  A := A
  B := B
  basis_cover := basisCover
  degreeBound := degreeBound
  coverings := coverings
  vanishing := vanishing

attribute [local implicit_reducible] sourceSituation

include hA basisCover vanishing basisCover' vanishing' hvanishImage h093Y in
/-- **Stacks Project, Tag 0D6W.** Let `f : (C, O) ⟶ (C', O')` be a morphism of ringed sites, let
`A ⊂ Mod(O)` be a weak Serre subcategory and let `N` be an integer such that

* `C, O, A` satisfy the standing hypothesis of Stacks 0D6R: a class `B` of objects covering every
  object of `C`, each `V ∈ B` carrying an integer bound `d_V` and a cofinal system of coverings of
  `V` on whose members the cohomology of every module of `A` vanishes above `d_V`;
* `f` and `A` satisfy the standing hypothesis of Stacks 0D6V: a class `B'` of objects covering
  every object of `C'`, each `V' ∈ B'` carrying an integer bound `d_{V'}` and a cofinal system of
  coverings of `V'` on the images under `f` of whose members the cohomology, computed on `C`, of
  every module of `A` vanishes above `d_{V'}`;
* `Rᵖf_*F = 0` for every `p > N` and every `F` of `A`.

Then for every `K` of `D_A(O)` the canonical map `Hʲ(Rf_*K) ⟶ Hʲ(Rf_*(τ_{≥ -n}K))` induced by the
truncation `K ⟶ τ_{≥ -n}K` is an isomorphism for every `j ≥ N - n`. -/
@[stacks 0D6W]
theorem isIso_homology_derivedPushforward_truncGEπ_of_relativeSituation
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K)
    (n : ℕ) (j : ℤ) (hj : N - (n : ℤ) ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
      ((derivedPushforward.{u} f.toRingedToposSiteHom).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) := by
  have hmos := f.isMorphismOfSites_toRingedToposSiteHom
  have hprod : HasProduct fun k : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).obj ⟨k⟩ :=
    Stacks.Cohomology.HypercohomologyEdge.hasProduct_truncGETower
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) K
  have hprodS : HasProduct fun k : ℕ ↦ (Stacks.DerivedLimit.truncGETower
      (SheafOfModules.{u} (sourceSituation A B basisCover degreeBound coverings vanishing).O)
      K).obj ⟨k⟩ := hprod
  -- The pushed-forward truncation tower has invertible transition maps on `Hʲ` past `n`.
  have hW (m : ℕ) (hnm : n ≤ m) :
      Y.J.W ((derivedPushforwardCohomologyAbPresheafFunctor f j).map
        ((Stacks.DerivedLimit.truncGETower
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).map
          (homOfLE hnm).op)) :=
    (isIso_homology_derivedPushforward_map_iff_w f _ j).1 <| (isEventuallyConstantTo_of_isIso_succ
      (Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K ⋙
        derivedPushforward.{u} f.toRingedToposSiteHom ⋙
        DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j) n
      (fun k hk ↦ isIso_homology_derivedPushforward_truncGETower_succ
        f.toRingedToposSiteHom hmos A N hvanishImage K hK k j (by omega))).isIso_map
      (homOfLE hnm).op (𝟙 _)
  rw [isIso_homology_derivedPushforward_map_iff_w f _ j]
  apply Stacks.Cohomology.w_of_cofinal_local_isomorphisms Y.J B' basisCover' coverings'
  intro V hV
  obtain ⟨m, hnm, hm1, hm2⟩ : ∃ m : ℕ, n ≤ m ∧ 1 - j ≤ (m : ℤ) ∧
      degreeBound' V hV - j + 1 ≤ (m : ℤ) :=
    ⟨max n (max (1 - j).toNat (degreeBound' V hV - j + 1).toNat), by omega, by omega, by omega⟩
  refine ⟨(derivedPushforwardCohomologyAbPresheafFunctor f j).obj
      ((Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).obj ⟨m⟩),
    (derivedPushforwardCohomologyAbPresheafFunctor f j).map
      ((DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K),
    (derivedPushforwardCohomologyAbPresheafFunctor f j).map
      ((Stacks.DerivedLimit.truncGETower
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) K).map
        (homOfLE hnm).op), ?_, hW m hnm, ?_⟩
  · exact ((derivedPushforwardCohomologyAbPresheafFunctor f j).map_comp _ _).symm.trans
      (congrArg (derivedPushforwardCohomologyAbPresheafFunctor f j).map
        (Stacks.Cohomology.HypercohomologyEdge.truncGEπ_comp_truncGETower_map K
          (homOfLE hnm).op))
  · intro 𝒰 h𝒰 i
    exact (NatIso.isIso_map_iff
      (derivedPushforwardCohomologyPresheafSourceValueIso f (𝒰.X i) j h093Y)
      ((DerivedCategory.TStructure.t.truncGEπ (-(m : ℤ))).app K)).2
      (isIso_homologyMap_derivedSectionsOverObject_truncGEπ X (f.u.obj (𝒰.X i)) A K hK
        (degreeBound' V hV) (vanishing' V hV 𝒰 h𝒰 i)
        (fun L c pr δ hL hc ↦
          Stacks.Cohomology.isIso_to_isDerivedLimit_truncGETower_of_derivedCategoryB
            (sourceSituation A B basisCover degreeBound coverings vanishing)
            K hK L pr ⟨δ, hL⟩ c hc)
        j m hm1 hm2)

include hA basisCover vanishing basisCover' vanishing' hvanishImage in
/-- **Stacks Project, Tag 0D6W for a flat morphism of ringed sites**, with no input carried.
Flatness — left exactness of `f^*`, Stacks 03DJ — gives Stacks 093Y, hence the identification
`Hʲ(V', Rf_*K) = Hʲ(u(V'), K)` of Stacks 0D6I through which the conclusion is read locally. -/
theorem isIso_homology_derivedPushforward_truncGEπ_of_relativeSituation_of_flat
    [PreservesFiniteLimits f.toRingedToposSiteHom.pullbackTopos]
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K)
    (n : ℕ) (j : ℤ) (hj : N - (n : ℤ) ≤ j) :
    IsIso ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
      ((derivedPushforward.{u} f.toRingedToposSiteHom).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) :=
  isIso_homology_derivedPushforward_truncGEπ_of_relativeSituation f A B basisCover degreeBound
    coverings vanishing B' basisCover' degreeBound' coverings' vanishing' N hvanishImage
    (Stacks.Cohomology.LerayUnbounded.isKInjective_pushforwardTopos_of_flat f) K hK n j hj

end Relative

end Stacks.Cohomology.OlssonLaszlo

end
