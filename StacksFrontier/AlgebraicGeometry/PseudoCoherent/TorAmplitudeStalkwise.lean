module

public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.Triangles
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
public import StacksFrontier.Topology.Sheaves.Modules.StalkExactness
public import StacksFrontier.Topology.Sheaves.Modules.StalkSkyscraperAdjunction
import StacksCore.Tactic.StacksAttribute

/-!
# Tor amplitude is detected on stalks

Let `O` be a sheaf of rings on a topological space `X`, so that `(X, O)` is a ringed space and
`SheafOfModules O` is the category of `O`-modules. An object `E` of `D(O)` has Tor amplitude in
`[a, b]` exactly when, for every point `x` of `X`, the stalk `E_x` has Tor amplitude in `[a, b]`
as an object of `D(O_x)`. This is Stacks 09U9.

## Main definitions

* `CategoryTheory.DerivedCategory.HasTorAmplitudeIn`: Tor amplitude in `[a, b]` with respect to
  a derived tensor bifunctor on the derived category of an arbitrary abelian category. This is
  the Stacks 08CG predicate, generalised from `𝒪_X`-modules to an arbitrary abelian category so
  that the same words can be said about `D(O)` and about `D(O_x)`.

## Main results

* `AlgebraicGeometry.SheafOfModules.hasTorAmplitudeIn_iff_forall_stalk`: Tor amplitude in
  `[a, b]` holds on `X` if and only if it holds at every stalk. This is the engine of
  **Stacks 09U9**, stated for derived tensor products supplied as bifunctors; the tag sits on
  `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_iff_forall_stalk`
  (`StacksFrontier/Topology/Sheaves/Cohomology/TorAmplitude/DerivedTensorStalk.lean`), where the
  bifunctors are the canonical ones and no hypothesis is left.
* `AlgebraicGeometry.SheafOfModules.isZero_iff_forall_isZero_stalkFunctor_obj`: a sheaf of
  modules vanishes exactly when all of its stalks vanish, in the `ModuleCat`-valued form taken
  by `AlgebraicGeometry.SheafOfModules.stalkFunctor`.
* `AlgebraicGeometry.SheafOfModules.stalkFunctor_essSurj`: every module over the stalk ring is
  the stalk of a sheaf of modules, namely of its skyscraper.
* `CategoryTheory.DerivedCategory.hasTorAmplitudeIn_iff_hasTorAmplitude`: the predicate used
  here is the one of `TorAmplitude.HasTorAmplitude`, whose derived tensoring is given by a
  bifunctor.

## Implementation notes

**Why the derived tensor products are bifunctor arguments here.** `- ⊗^{L} -` on `D(O)` is
taken as data, as a bifunctor `D ⥤ D ⥤ D`, and so is `- ⊗^{L}_{O_x} -` on each `D(O_x)`;
`CategoryTheory.DerivedCategory.HasTorAmplitudeIn` is the Stacks 08CG vanishing condition for a
supplied bifunctor. This is not because the canonical operations are unavailable — they are
`Stacks.Cohomology.TorAmplitude.derTensor` (Stacks 06YU) and
`CochainComplex.DerivedTensor.canonicalDerivedTensorProduct` (Stacks 0BYI) — but so that the
assembly below depends on nothing about them, and in particular not on the ringed-space
certificate bundle of Stacks 08CG, which carries an `IsLeftDerivedFunctor` field that 09U9
makes no use of. On `OXMod X` the predicate is `Iff.rfl`-equal to
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.HasTorAmplitudeIn` with the
certificate's `derivedTensor` substituted.

**The hypothesis `hstalk`, and where it is discharged.** The theorem takes as a hypothesis the
isomorphism
`(E_x ⊗^{L}_{O_x} F_x) ≅ (E ⊗^{L}_{O} F)_x`,
i.e. that taking stalks carries the sheaf-level derived tensor product to the stalk-level one.
This is precisely the pair of facts the Stacks proof of 09U9 cites: taking stalks commutes with
tensor products (Stacks 01CB) and taking stalks is exact. For bifunctors supplied as data no
relation between the two can be derived, so it has to be an argument; it does *not* contain the
statement being proved, being an isomorphism of objects of `D(O_x)` for each `E` and `F` with no
reference to any interval, to any vanishing, or to any quantification over points.

At the canonical bifunctors it is a theorem, not a hypothesis:
`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIso`
(`StacksFrontier/Topology/Sheaves/Cohomology/TorAmplitude/DerivedTensorStalk.lean`) proves it by
resolving both arguments by K-flat complexes (Stacks 06YS), on which both derived tensor
products are total tensor complexes, and using that the stalk of a K-flat complex is K-flat
(Stacks 06YB) and that the stalk of a total tensor complex is the total tensor complex of the
stalks (Stacks 01CB, through
`AlgebraicGeometry.SheafOfModules.stalkTotalComplexIso`). Feeding that into the theorem below
gives `Stacks.Cohomology.TorAmplitude.hasTorAmplitude_iff_forall_stalk`, which is the
unconditional Stacks 09U9 and carries the tag.

**What is proved outright.** Everything else in the Stacks proof, namely the two genuine
ingredients and the assembly:

* the direction (2) `⇒` (1) needs that a sheaf of modules all of whose stalks vanish is zero —
  `isZero_iff_forall_isZero_stalkFunctor_obj`, obtained from Mathlib's
  `TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero` by reflecting along the faithful additive
  functor `SheafOfModules.toSheaf`;
* the direction (1) `⇒` (2) needs that every `O_x`-module occurs as a stalk —
  `stalkFunctor_essSurj`, which is the skyscraper at `x`, via
  `AlgebraicGeometry.SheafOfModules.skyscraperStalkIso`. This is the Stacks proof's "taking
  stalks at `x` is the same thing as pulling back by the morphism of ringed spaces
  `(x, O_x) → (X, O)`", read through the adjunction rather than through Stacks 09U8: the
  skyscraper *is* the pushforward along that morphism, and realising an arbitrary module as a
  stalk is all that direction uses;
* both directions need that the stalk functor commutes with the cohomology functors of the
  derived categories, which is
  `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` applied to the exact functor
  `stalkFunctor O x`.

`(stalkFunctor O x).mapDerivedCategory` is the derived stalk functor; it is the body of
`AlgebraicGeometry.SheafOfModules.derivedStalkFunctor`
(`StacksFrontier/AlgebraicGeometry/Perfect/DerivedStalk/StalkwiseIsomorphism.lean`) and so is
definitionally equal to it. That file is not imported here because it pins both derived categories
to `HasDerivedCategory.standard` with a `local instance`, whereas the statements below leave the
`HasDerivedCategory` instances as binders and are therefore strictly more general.

## References

* [Stacks Project, Lemma 20.48.8 (Tag 09U9)](https://stacks.math.columbia.edu/tag/09U9)
* [Stacks Project, Definition 20.48.1 (Tag 08CG)](https://stacks.math.columbia.edu/tag/08CG)
* [Stacks Project, Lemma 17.16.1 (Tag 01CB)](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Lemma 17.3.1 (Tag 01AG)](https://stacks.math.columbia.edu/tag/01AG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w w' u

namespace CategoryTheory.DerivedCategory

variable {A : Type*} [Category A] [Abelian A] [HasDerivedCategory.{w} A]

/-- **Stacks 08CG (1)**, for a derived tensor product given as a bifunctor on `D(A)`. An object
`E` of `D(A)` *has Tor amplitude in `[a, b]`* when `H^i(E ⊗^{L} F) = 0` for every object `F` of
`A` and every `i` outside `[a, b]`, the object `F` being read in degree `0`.

On `A = OXMod X` this is
`AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.HasTorAmplitudeIn` with `T` the
certificate's `derivedTensor`, and the identification is `Iff.rfl`;
`hasTorAmplitudeIn_iff_hasTorAmplitude` identifies it with the `TorAmplitude.HasTorAmplitude` of
Stacks 08CJ.

This form is stated for a bifunctor `T` on the derived category of an arbitrary abelian
category. `AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring.HasTorAmplitudeIn`
(`StacksFrontier/AlgebraicGeometry/Perfect/TorDimension.lean`) is the same clause for a bundle that
also records an underived tensor product, a comparison and an `IsLeftDerivedFunctor` field, and
`Stacks.Cohomology.TorAmplitude.HasTorAmplitude`
(`StacksFrontier/Topology/Sheaves/Cohomology/TorAmplitude/OnARingedSpace.lean`) is the clause for
the derived tensor product of Stacks 06YU. -/
@[stacks 08CG "tor amplitude in an interval, for a derived tensor bifunctor T over an arbitrary \
abelian category: H^i(E ⊗^L F) = 0 for every object F in degree 0 and every i outside [a, b]; \
at the derivedTensor of AlgebraicGeometry.RingedSpace.CertifiedDerivedSheafTensoring it is \
CertifiedDerivedSheafTensoring.HasTorAmplitudeIn by Iff.rfl"]
public def HasTorAmplitudeIn
    (T : DerivedCategory A ⥤ DerivedCategory A ⥤ DerivedCategory A)
    (E : DerivedCategory A) (a b : ℤ) : Prop :=
  ∀ (F : A) (i : ℤ), i ∉ Set.Icc a b →
    IsZero ((DerivedCategory.homologyFunctor A i).obj
      ((T.obj E).obj ((DerivedCategory.singleFunctor A 0).obj F)))

/-- The Tor amplitude of this file is the Tor amplitude of Stacks 08CJ, the derived tensoring
functors being those of the bifunctor `T`. -/
public theorem hasTorAmplitudeIn_iff_hasTorAmplitude
    (T : DerivedCategory A ⥤ DerivedCategory A ⥤ DerivedCategory A)
    (E : DerivedCategory A) (a b : ℤ) :
    HasTorAmplitudeIn T E a b ↔
      TorAmplitude.HasTorAmplitude
        (fun F => T.flip.obj ((DerivedCategory.singleFunctor A 0).obj F)) E a b := by
  constructor
  · intro h F i hi
    exact h F i (by simp only [Set.mem_Icc, not_and_or, not_le]; omega)
  · intro h F i hi
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hi
    exact h F i (by omega)

end CategoryTheory.DerivedCategory

namespace AlgebraicGeometry.SheafOfModules

variable {X : TopCat.{u}}
  (O : CategoryTheory.Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- **Stacks 01AG, in the form used to detect Tor amplitude.** A sheaf of `O`-modules is a zero
object exactly when its stalk at every point is a zero object.

The forward direction is additivity of the stalk functor. The converse is Mathlib's
`TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero` for the underlying sheaf of abelian groups,
reflected back along the faithful additive functor `SheafOfModules.toSheaf`.

This is the vanishing case of Stacks 01AG, namely its exactness clause — tagged on
`AlgebraicGeometry.SheafOfModules.exact_iff_stalkShortComplex_exact` in
`StacksFrontier/Topology/Sheaves/Modules/Exactness.lean` — read at the short complex `0 ⟶ M ⟶ 0`,
whose exactness at `M` is vanishing of `M`. It is a restriction of that clause, not a form of it
with fewer hypotheses, so it carries no 01AG attribute of its own: a bare tag on a restricted
case would make the covering set of 01AG look wider than it is. -/
public theorem isZero_iff_forall_isZero_stalkFunctor_obj (M : _root_.SheafOfModules.{u} O) :
    IsZero M ↔ ∀ x : X, IsZero ((stalkFunctor O x).obj M) := by
  refine ⟨fun h x => Functor.map_isZero _ h, fun h => ?_⟩
  have hH : IsZero ((_root_.SheafOfModules.toSheaf O).obj M) :=
    (TopCat.Sheaf.isZero_iff_stalkFunctor_obj_isZero
      ((_root_.SheafOfModules.toSheaf O).obj M)).mpr
      fun x => (isZero_stalkFunctor_obj_iff O x M).1 (h x)
  rw [IsZero.iff_id_eq_zero]
  exact Functor.map_injective (_root_.SheafOfModules.toSheaf O) (hH.eq_of_src _ _)

/-- **Every module over the stalk ring at `x` is the stalk at `x` of a sheaf of modules**, namely
of its skyscraper at `x`.

This is what the Stacks proof of 09U9 uses when it says that taking stalks at `x` is pulling
back along the morphism of ringed spaces `(x, O_x) → (X, O)`: the skyscraper is the pushforward
along that morphism, and `AlgebraicGeometry.SheafOfModules.skyscraperStalkIso` says the stalk of
the pushforward is the module one started with. -/
public theorem stalkFunctor_essSurj (x : X)
    (N : ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)) :
    ∃ M : _root_.SheafOfModules.{u} O, Nonempty ((stalkFunctor O x).obj M ≅ N) :=
  ⟨(skyscraperFunctor O x).obj N, ⟨(skyscraperStalkIso O x).app N⟩⟩

section Stalkwise

variable [HasDerivedCategory.{w} (_root_.SheafOfModules.{u} O)]
  [∀ x : X, HasDerivedCategory.{w'}
    (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))]

/-- **The engine of Stacks 09U9.** Let `(X, O)` be a ringed space and `E` an object of `D(O)`.
Then `E` has Tor amplitude in `[a, b]` if and only if, for every point `x` of `X`, the stalk
`E_x` has Tor amplitude in `[a, b]` as an object of `D(O_x)`.

`T` is the derived tensor product `- ⊗^{L}_{O} -` on `D(O)` and `T' x` is `- ⊗^{L}_{O_x} -` on
`D(O_x)`; both are arguments rather than the canonical operations, so that this proof depends on
nothing about them. The hypothesis `hstalk` says that taking stalks carries one to the other,
which is the derived form of Stacks 01CB together with exactness of stalks — the two facts the
Stacks proof of 09U9 cites. See the implementation notes of this file.

The stalk of `E` is `(stalkFunctor O x).mapDerivedCategory.obj E`, the stalk functor being exact
and so inducing a triangulated functor `D(O) ⥤ D(O_x)`.

No `@[stacks 09U9]` attribute is placed here. The tag's covering declaration is
`Stacks.Cohomology.TorAmplitude.hasTorAmplitude_iff_forall_stalk`
(`StacksFrontier/Topology/Sheaves/Cohomology/TorAmplitude/DerivedTensorStalk.lean`): this theorem
read at the derived tensor product of Stacks 06YU on `D(O_X)` and the canonical one of
Stacks 0BYI over each stalk ring, with `hstalk` supplied by
`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIso`. Quantified over arbitrary
bifunctors, the statement below is more general than the source in its conclusion and, taken
alone, conditional, so it is not what 09U9 asserts. -/
public theorem hasTorAmplitudeIn_iff_forall_stalk
    (T : DerivedCategory (_root_.SheafOfModules.{u} O) ⥤
      DerivedCategory (_root_.SheafOfModules.{u} O) ⥤ DerivedCategory (_root_.SheafOfModules.{u} O))
    (T' : ∀ x : X,
      DerivedCategory (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)) ⥤
        DerivedCategory
            (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)) ⥤
          DerivedCategory
            (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)))
    (hstalk : ∀ (x : X) (E : DerivedCategory (_root_.SheafOfModules.{u} O))
        (F : _root_.SheafOfModules.{u} O),
      ((T' x).obj ((stalkFunctor O x).mapDerivedCategory.obj E)).obj
          ((DerivedCategory.singleFunctor _ 0).obj ((stalkFunctor O x).obj F)) ≅
        (stalkFunctor O x).mapDerivedCategory.obj
          ((T.obj E).obj ((DerivedCategory.singleFunctor _ 0).obj F)))
    (E : DerivedCategory (_root_.SheafOfModules.{u} O)) (a b : ℤ) :
    DerivedCategory.HasTorAmplitudeIn T E a b ↔
      ∀ x : X, DerivedCategory.HasTorAmplitudeIn (T' x)
        ((stalkFunctor O x).mapDerivedCategory.obj E) a b := by
  have key := fun (x : X) F (i : ℤ) =>
    ((DerivedCategory.homologyFunctor _ i).mapIso (hstalk x E F) ≪≫
      ((stalkFunctor O x).mapDerivedCategoryHomologyIso i).app _).isZero_iff
  constructor
  · intro h x N i hi
    -- Realise `N` as the stalk of its skyscraper, and transport along that isomorphism.
    refine IsZero.of_iso ?_ ((DerivedCategory.homologyFunctor _ i).mapIso
      (((T' x).obj ((stalkFunctor O x).mapDerivedCategory.obj E)).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          ((skyscraperStalkIso O x).app N).symm)))
    exact (key x _ i).2 (Functor.map_isZero (stalkFunctor O x) (h _ i hi))
  · intro h F i hi
    exact (isZero_iff_forall_isZero_stalkFunctor_obj O _).2 fun x => (key x F i).1 (h x _ i hi)

/-- **The hypotheses of `hasTorAmplitudeIn_iff_forall_stalk` are satisfiable, and this is what
they give at the cheapest witness**: taking both bifunctors to be the first projection
`(E, F) ↦ E`, for which the stalk compatibility is the identity, Tor amplitude degenerates to
vanishing of cohomology outside `[a, b]` and the theorem says that such vanishing is detected on
stalks.

This is the analogue of
`AlgebraicGeometry.RingedSpace.hasTorAmplitudeIn_firstProjection_iff`, and it measures how weak
the cheapest instance of `hasTorAmplitudeIn_iff_forall_stalk` is. It is not what shows that
theorem to be non-vacuous: the canonical derived tensor products satisfy its hypotheses, by
`Stacks.SheafOfModules.DerivedTensorStalk.derivedTensorStalkIso`. -/
public theorem isZero_homology_iff_forall_stalk
    (E : DerivedCategory (_root_.SheafOfModules.{u} O)) (a b : ℤ) :
    (∀ i : ℤ, i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (_root_.SheafOfModules.{u} O) i).obj E)) ↔
      ∀ (x : X) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj
          ((stalkFunctor O x).mapDerivedCategory.obj E)) := by
  have key := hasTorAmplitudeIn_iff_forall_stalk O
    (Functor.const (DerivedCategory (_root_.SheafOfModules.{u} O))
      (C := DerivedCategory (_root_.SheafOfModules.{u} O)))
    (fun x => Functor.const
      (DerivedCategory (ModuleCat.{u}
        (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x)))
      (C := DerivedCategory (ModuleCat.{u}
        (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X) O.obj x))))
    (fun _ _ _ => Iso.refl _) E a b
  exact ⟨fun h x i hi => key.1 (fun _ i hi => h i hi) x
      ((stalkFunctor O x).obj (_root_.SheafOfModules.unit O)) i hi,
    fun h i hi => key.2 (fun x _ i hi => h x i hi) (_root_.SheafOfModules.unit O) i hi⟩

end Stalkwise

end AlgebraicGeometry.SheafOfModules

end
