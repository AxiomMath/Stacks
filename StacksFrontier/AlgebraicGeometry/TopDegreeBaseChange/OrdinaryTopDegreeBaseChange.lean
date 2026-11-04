module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeTransposeSections
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatPullback
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.OrdinaryTopDegreeTranspose

/-!
# The transpose of the top-degree base change map, written through the ordinary data

`BaseChangeTransposeSections.lean` computes the transpose, under the adjunction `h^* ⊣ h_*` of
[Stacks, Tag 01BH], of the canonical map `γ⁺` of conclusion (c) of [Stacks, Tag 0EX3]: by
`homEquiv_topDirectImageBaseChangeMapPlus_eq_unit` it is

> `R^d f'_* F' ⟶ H^d(Rf'_*(F'[0])) ⟶ h_* h^* H^d(Rf'_*(F'[0])) ⟶ h_* H^d(Lh^* Rf'_*(F'[0]))`
> `⟶ h_* H^d(Rf''_*((h')^* F'[0])) ⟶ h_* R^d f''_* (h')^* F'`,

the crossing of the two models of `Rf_*` inverted, the **ordinary** unit of `h^* ⊣ h_*`, and the
direct images along `h` of the identification of conclusion (a), of the degree-`d` cohomology of
the derived base change map of [Stacks, Tag 08HY] followed by the derived pushforward of the
comparison from derived to ordinary pullback, and of the crossing at `f''`.

This file removes the derived base change map and the derived unit from it. Three inputs do the
work:

* `unit_comp_map_topDirectImagePullbackIso` (`EdgeCompatPullback.lean`) replaces the second and
  third factors — the ordinary unit and `h_*` of conclusion (a)'s identification — by `H^d` of
  the **derived** unit of `Lh^* ⊣ Rh_*` followed by the cohomology edge morphism
  `H^d(Rh_* -) ⟶ h_* H^d(-)`;
* `map_unit_comp_edge_comp_map` (`OrdinaryTopDegreeTranspose.lean`) then absorbs the fourth
  factor into the edge morphism: the derived unit followed by the edge and by `h_*` of `H^d` of a
  map is `H^d` of the **transpose** of that map, followed by the edge. What stands in front of
  the edge is now one morphism of `D(𝒪_{Y'})`, the transpose along the bottom of the square of
  the two-step derived composite `γ⁺` displays;
* `derivedPushforwardUnit_comp_map_hom_comp_homEquiv_fac` (ibid.), which is
  `Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparison_fac` transported to the
  presentation of `F'[0]` and to the trailing identification that
  `derivedToOrdinaryPullbackSingle` carries, computes that transpose: it is the route of the
  **degreewise** units of [Stacks, Tag 0096].

*Why the comparison `Q(f'_*(F'[0])) ⟶ Rf'_*(F'[0])` stands in front of
`homEquiv_topDirectImageBaseChangeMapPlus_eq_ordinary`, and what that costs.*
`derivedPushforwardComparison_fac` is an identity between two morphisms out of `Q(f_* M)`, not
out of `Rf_*(Q M)`, and the comparison between them is not invertible — the degreewise direct
image is not exact, which is the whole reason `R^d f'_* F'` is interesting. So the identity it
yields with no derived unit in it is the one for the transpose of `γ⁺` precomposed with the
degree-`d` cohomology of that comparison.

**At the single complex `F'[0]` that cohomology is taken at the zero object.**
`isZero_homologyFunctor_pushforwardToDerivedCategory_singleFunctor` says that
`Q(f'_*(F'[0]))` is `(f'_* F')[0]`, whose degree-`d` cohomology vanishes for every `d > 0`, and
`isZero_homologyFunctor_pushforwardToDerivedCategory_single_of_ne_zero` reads that off at the
situation. So for `S.d > 0` both sides of
`homEquiv_topDirectImageBaseChangeMapPlus_eq_ordinary` are morphisms out of the zero object: the
identity holds for that reason alone, and it says nothing about the transpose of `γ⁺`.

The identity that does determine the transpose is
`homEquiv_topDirectImageBaseChangeMapPlus_eq_edge`, whose source is `R^d f'_* F'` itself and
which carries the derived base change map transposed inside one morphism of `D(𝒪_{Y'})` in front
of the cohomology edge morphism. Reaching the ordinary data from there means transposing at a
complex where the comparison above is invertible — a K-injective one, by
`…DerivedAdjunctionOnRingedSpaces.isIso_derivedPushforwardUnit_app_of_isKInjective` — and
`derivedPushforwardUnit_comp_map_hom_comp_homEquiv_fac` is stated at an arbitrary `M` with an
arbitrary isomorphism `Q M ≅ K`, so it admits that instantiation.

## Main results

* `…TopDegreeBaseChange.homEquiv_topDirectImageBaseChangeMapPlus_eq_edge`: **the transpose of
  `γ⁺` with no ordinary unit and no `h_*` of a cohomology map left in it** — the crossing
  inverted, `H^d` of the transpose along the bottom of the derived composite, the cohomology edge
  morphism, and `h_*` of the crossing at `f''`.
* `…TopDegreeBaseChange.homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv`: the same with
  the crossing moved to the other side.
* `…TopDegreeBaseChange.derivedPushforwardUnit_comp_homEquiv_baseChange_fac`: **that transpose,
  preceded by the comparison `Q(f'_*(F'[0])) ⟶ Rf'_*(F'[0])`, is the route of the degreewise
  units of [Stacks, Tag 0096]** — the ordinary unit of `h^* ⊣ h_*` on complexes, the ordinary
  base change map `Stacks.Cohomology.DerivedBaseChange.homotopyBaseChangeSquare` of the square,
  and the comparisons of the models of `Rh_*` and `Rf''_*`.
* `…TopDegreeBaseChange.homEquiv_topDirectImageBaseChangeMapPlus_eq_ordinary`: the degree-`d`
  cohomology of the comparison out of the degreewise direct image, then the crossing of the two
  models, then the transpose of `γ⁺`, equals the degree-`d` cohomology of the ordinary route,
  then the edge morphism, then `h_*` of the crossing at `f''`. Its two sides are morphisms out of
  the degree-`d` cohomology of `(f'_* F')[0]`, which the next two results compute.
* `…TopDegreeBaseChange.isZero_homologyFunctor_pushforwardToDerivedCategory_singleFunctor`:
  **the degreewise direct image of a single complex has no cohomology in positive degrees.**
  For a morphism of ringed spaces `k` and a module `M`, `H^d(Q(k_*(M[0])))` is the zero object
  for every `d > 0`.
* `…TopDegreeBaseChange.isZero_homologyFunctor_pushforwardToDerivedCategory_single_of_ne_zero`:
  **the same at the situation**, so the common source of the two sides of
  `homEquiv_topDirectImageBaseChangeMapPlus_eq_ordinary` is the zero object whenever `S.d ≠ 0`.
* `…TopDegreeBaseChange.derivedToOrdinaryPullbackSingle_eq_comp`: the comparison from derived to
  ordinary pullback at a single complex, split at the derived-pullback comparison it contains.

## Implementation notes

*The whole proof is the three inputs and the variable-level rearrangements.* Every reassociation,
every cancellation of a crossing and every naturality square is an application of a lemma of
`OrdinaryTopDegreeTranspose.lean` stated at variables of abstract categories; no `Category.assoc`
rewrite and no `rw` of a naturality square is performed on a composite of morphisms between
objects spelled as iterated derived functors.

*The two definitional identifications are `rfl` lemmas of their own.*
`derivedToOrdinaryPullbackSingle_eq_comp` splits
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle` into the shape
`Lh'^*(e.inv) ≫ (derived-pullback comparison) ≫ r` that the generic identity consumes; the
exchange of the wrapper `derivedBaseChangeMap` for the component of the base change two-square
needs no lemma, being `rfl`. The split is used only in argument position: the
isomorphism `e` is `(singleFunctorIsoCompQh _ 0).app F'` reversed and `r` is the remainder of
`derivedToOrdinaryPullbackSingle`, so the elaborator checks the identifications where it is cheap
and nothing is rewritten.

## References

* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedBaseChange
open Stacks.DerivedPullback.Composition
open DerivedCategory

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance] RingedSpaceModuleAdjunction.preservesFiniteColimits_modulePullback

/-! ### The comparison from derived to ordinary pullback, split -/

section Bridges

variable {A B : RingedSpace.{u, u}} (k : A ⟶ B)

/-- **The canonical map `Lk^*(M[-d]) ⟶ (k^* M)[-d]`, split at the derived-pullback comparison it
contains.** By definition
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.derivedToOrdinaryPullbackSingle` is the
derived pullback of the identification of the two single functors, the derived-pullback
comparison at the homotopy-category single complex, and the two remaining identifications; this
reads it as

> `Lk^*(e.inv) ≫ (derived-pullback comparison) ≫ r`

with `e` the identification `M[-d] ≅ Q(M[-d])` of the two single functors and `r` the remainder.
-/
theorem derivedToOrdinaryPullbackSingle_eq_comp
    (M : SheafOfModules.{u} (structureSheafRing B)) (d : ℤ) :
    derivedToOrdinaryPullbackSingle k M d =
      (derivedPullback k).map
          (((singleFunctorIsoCompQh
            (SheafOfModules.{u} (structureSheafRing B)) d).app M).symm).inv ≫
        (derivedPullbackComparison k).app
            ((HomotopyCategory.singleFunctor
              (SheafOfModules.{u} (structureSheafRing B)) d).obj M) ≫
          (Qh.map ((Functor.mapHomotopyCategorySingleFunctor (modulePullback k) d).hom.app M) ≫
            (singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing A)) d).inv.app
              ((modulePullback k).obj M)) :=
  rfl

end Bridges

/-! ### The degreewise direct image of a single complex, in positive degrees -/

section Degreewise

variable {A B : RingedSpace.{u, u}}

/-- **The degreewise direct image of a single complex has no cohomology in positive degrees.**
`Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforwardToDerivedCategory` applies
`k_*` term by term and then localises, so at the single complex `M[0]` it returns `(k_* M)[0]`,
whose degree-`d` cohomology is the zero object for every `d > 0`. -/
theorem isZero_homologyFunctor_pushforwardToDerivedCategory_singleFunctor (k : A ⟶ B)
    (M : SheafOfModules.{u} (structureSheafRing A)) (d : ℤ) (hd : 0 < d) :
    IsZero ((homologyFunctor (SheafOfModules.{u} (structureSheafRing B)) d).obj
      ((pushforwardToDerivedCategory k).obj
        ((HomotopyCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing A)) 0).obj M))) :=
  IsZero.of_iso
    (DerivedCategory.isZero_of_isLE
      ((DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing B)) 0).obj
        ((modulePushforward k).obj M)) 0 d hd)
    ((homologyFunctor (SheafOfModules.{u} (structureSheafRing B)) d).mapIso
      (Qh.mapIso ((Functor.mapHomotopyCategorySingleFunctor (modulePushforward k) 0).app M) ≪≫
        ((singleFunctorIsoCompQh (SheafOfModules.{u} (structureSheafRing B)) 0).app
          ((modulePushforward k).obj M)).symm))

/-- **The source of the left-hand side of
`homEquiv_topDirectImageBaseChangeMapPlus_eq_ordinary` is the zero object whenever `S.d` is
positive.** -/
theorem isZero_homologyFunctor_pushforwardToDerivedCategory_single_of_ne_zero
    (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u}) (F' : S.X'.Modules)
    (hd : S.d ≠ 0) :
    IsZero ((homologyFunctor S.Y'.Modules (S.d : ℤ)).obj
      ((pushforwardToDerivedCategory S.f'.toLRSHom.toShHom).obj
        ((HomotopyCategory.singleFunctor S.X'.Modules 0).obj F'))) :=
  isZero_homologyFunctor_pushforwardToDerivedCategory_singleFunctor S.f'.toLRSHom.toShHom F'
    (S.d : ℤ) (by exact_mod_cast Nat.pos_of_ne_zero hd)

end Degreewise

/-! ### The transpose of `γ⁺` through the ordinary data -/

section Card

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
  (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
    = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom)

/-- **The transpose of `γ⁺`, with the ordinary unit and conclusion (a)'s identification traded
for the derived transpose and the cohomology edge morphism.** It is

> `R^d f'_* F' ⟶ H^d(Rf'_*(F'[0])) ⟶ H^d(Rh_*(Rf''_*((h')^* F'[0])))`
> `⟶ h_* H^d(Rf''_*((h')^* F'[0])) ⟶ h_* R^d f''_* (h')^* F'`,

the crossing of the two models of `Rf_*` inverted, the degree-`d` cohomology of the transpose
under `Lh^* ⊣ Rh_*` of the two-step derived composite `γ⁺` displays, the cohomology edge morphism
of `Rh_*`, and `h_*` of the crossing at `f''`. -/
theorem homEquiv_topDirectImageBaseChangeMapPlus_eq_edge :
    (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
        (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) =
      (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).inv ≫
        (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
            ((derivedAdjunction h.toLRSHom.toShHom).homEquiv _ _
              (derivedBaseChangeMap h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                  S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq
                  ((singleFunctor S.X'.Modules 0).obj F') ≫
                (derivedPushforward f''.toLRSHom.toShHom).map
                  (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0))) ≫
          (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
            ((derivedPushforward f''.toLRSHom.toShHom).obj
              ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
          (Scheme.Modules.pushforward h).map
            (homologyFunctorDerivedPushforwardIso f''
              ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom :=
  (homEquiv_topDirectImageBaseChangeMapPlus_eq_unit S F' h' f'' h sq).trans
    (comp_pair_comp_comp (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).inv
      (unit_comp_map_topDirectImagePullbackIso S F' h)
      (map_unit_comp_edge_comp_map (derivedAdjunction h.toLRSHom.toShHom)
        (homologyFunctor S.Y'.Modules (S.d : ℤ)) (homologyFunctor Y''.Modules (S.d : ℤ))
        (Scheme.Modules.pushforward h)
        (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)) _)
      ((Scheme.Modules.pushforward h).map
        (homologyFunctorDerivedPushforwardIso f''
          ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom))

/-- **`homEquiv_topDirectImageBaseChangeMapPlus_eq_edge` with the crossing of the two models on
the other side.** Since the crossing is an isomorphism, the transpose of `γ⁺` preceded by it is
the three remaining factors. -/
theorem homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv :
    (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
          (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) =
      (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
          ((derivedAdjunction h.toLRSHom.toShHom).homEquiv _ _
            (derivedBaseChangeMap h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq
                ((singleFunctor S.X'.Modules 0).obj F') ≫
              (derivedPushforward f''.toLRSHom.toShHom).map
                (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0))) ≫
        (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
          ((derivedPushforward f''.toLRSHom.toShHom).obj
            ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
        (Scheme.Modules.pushforward h).map
          (homologyFunctorDerivedPushforwardIso f''
            ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom :=
  iso_hom_comp_eq (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ))
    (homEquiv_topDirectImageBaseChangeMapPlus_eq_edge S F' h' f'' h sq)

omit [SheafOfModules.IsQuasicoherent F'] in
/-- **The transpose of the derived composite of `γ⁺`, preceded by the comparison out of the
degreewise direct image, is the route of the degreewise units of [Stacks, Tag 0096].** The
comparison `Q(f'_*(F'[0])) ⟶ Rf'_*(F'[0])`, read through the identification of the two single
functors, followed by the transpose under `Lh^* ⊣ Rh_*` of

> `Lh^*(Rf'_*(F'[0])) ⟶ Rf''_*(Lh'^*(F'[0])) ⟶ Rf''_*((h')^* F'[0])`,

equals the **ordinary** unit of `h^* ⊣ h_*` on complexes, the comparison
`Q(h^*(f'_*(F'[0]))) ⟶ Rh_*(Q(h^*(f'_*(F'[0]))))`, and `Rh_*` of the ordinary base change map
`Stacks.Cohomology.DerivedBaseChange.homotopyBaseChangeSquare` of the square, of the comparison
`Q(f''_*((h')^*(F'[0]))) ⟶ Rf''_*(Q((h')^*(F'[0])))` and of the two remaining identifications of
the single functors. -/
theorem derivedPushforwardUnit_comp_homEquiv_baseChange_fac :
    (derivedPushforwardUnit S.f'.toLRSHom.toShHom).app
          ((HomotopyCategory.singleFunctor S.X'.Modules 0).obj F') ≫
        (derivedPushforward S.f'.toLRSHom.toShHom).map
          ((singleFunctorIsoCompQh S.X'.Modules 0).inv.app F') ≫
        (derivedAdjunction h.toLRSHom.toShHom).homEquiv _ _
          (derivedBaseChangeMap h'.toLRSHom.toShHom f''.toLRSHom.toShHom
              S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq
              ((singleFunctor S.X'.Modules 0).obj F') ≫
            (derivedPushforward f''.toLRSHom.toShHom).map
              (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0)) =
      Qh.map ((homotopyPullbackPushforwardAdjunction h.toLRSHom.toShHom).unit.app
          (((modulePushforward S.f'.toLRSHom.toShHom).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.singleFunctor S.X'.Modules 0).obj F'))) ≫
        (derivedPushforwardUnit h.toLRSHom.toShHom).app
          (((modulePullback h.toLRSHom.toShHom).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            (((modulePushforward S.f'.toLRSHom.toShHom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.singleFunctor S.X'.Modules 0).obj F'))) ≫
        (derivedPushforward h.toLRSHom.toShHom).map
          (Qh.map ((homotopyBaseChangeSquare h'.toLRSHom.toShHom f''.toLRSHom.toShHom
            S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq).app
            ((HomotopyCategory.singleFunctor S.X'.Modules 0).obj F'))) ≫
        (derivedPushforward h.toLRSHom.toShHom).map
          ((derivedPushforwardUnit f''.toLRSHom.toShHom).app
            (((modulePullback h'.toLRSHom.toShHom).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.singleFunctor S.X'.Modules 0).obj F'))) ≫
        (derivedPushforward h.toLRSHom.toShHom).map
          ((derivedPushforward f''.toLRSHom.toShHom).map
            (Qh.map ((Functor.mapHomotopyCategorySingleFunctor
                (modulePullback h'.toLRSHom.toShHom) 0).hom.app F') ≫
              (singleFunctorIsoCompQh X''.Modules 0).inv.app
                ((modulePullback h'.toLRSHom.toShHom).obj F'))) :=
  derivedPushforwardUnit_comp_map_hom_comp_homEquiv_fac h'.toLRSHom.toShHom
    f''.toLRSHom.toShHom S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq
    ((HomotopyCategory.singleFunctor S.X'.Modules 0).obj F')
    ((singleFunctorIsoCompQh S.X'.Modules 0).app F').symm
    (Qh.map ((Functor.mapHomotopyCategorySingleFunctor
        (modulePullback h'.toLRSHom.toShHom) 0).hom.app F') ≫
      (singleFunctorIsoCompQh X''.Modules 0).inv.app
        ((modulePullback h'.toLRSHom.toShHom).obj F'))

/-- **The transpose of `γ⁺` with neither a derived base change map nor a derived unit in it.**
The degree-`d` cohomology of the comparison `Q(f'_*(F'[0])) ⟶ Rf'_*(F'[0])` read through the
identification of the two single functors, then the crossing of the two models of `Rf_*`, then
the transpose of `γ⁺` under `h^* ⊣ h_*`, equals the degree-`d` cohomology of the route of the
**degreewise** units of [Stacks, Tag 0096] — the ordinary unit of `h^* ⊣ h_*` on complexes, the
ordinary base change map `Stacks.Cohomology.DerivedBaseChange.homotopyBaseChangeSquare` of the
square, and the comparisons of the models of `Rh_*` and `Rf''_*` with the identifications of the
single functors — followed by the cohomology edge morphism of `Rh_*` and by `h_*` of the crossing
at `f''`.

On the right-hand side the derived machinery `γ⁺` is built from no longer appears: what stands
there is the ordinary unit, the ordinary base change map of the square, and the crossings and
comparisons that relate the models.

*What the two sides are morphisms out of.* The comparison out of the degreewise direct image
stands in front because `derivedPushforwardComparison_fac` determines only the composite with it,
and at the single complex `F'[0]` its degree-`d` cohomology is taken at the zero object:
`isZero_homologyFunctor_pushforwardToDerivedCategory_single_of_ne_zero` shows the common source
of the two sides is zero whenever `S.d ≠ 0`. So for positive `S.d` this identity holds for
that reason alone and says nothing about the transpose of `γ⁺`; the identity that determines the
transpose is `homEquiv_topDirectImageBaseChangeMapPlus_eq_edge`. -/
theorem homEquiv_topDirectImageBaseChangeMapPlus_eq_ordinary :
    (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
          ((derivedPushforwardUnit S.f'.toLRSHom.toShHom).app
              ((HomotopyCategory.singleFunctor S.X'.Modules 0).obj F') ≫
            (derivedPushforward S.f'.toLRSHom.toShHom).map
              ((singleFunctorIsoCompQh S.X'.Modules 0).inv.app F')) ≫
        (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).hom ≫
        (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
          (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) =
      (homologyFunctor S.Y'.Modules (S.d : ℤ)).map
          (Qh.map ((homotopyPullbackPushforwardAdjunction h.toLRSHom.toShHom).unit.app
              (((modulePushforward S.f'.toLRSHom.toShHom).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj
                ((HomotopyCategory.singleFunctor S.X'.Modules 0).obj F'))) ≫
            (derivedPushforwardUnit h.toLRSHom.toShHom).app
              (((modulePullback h.toLRSHom.toShHom).mapHomotopyCategory
                (ComplexShape.up ℤ)).obj
                (((modulePushforward S.f'.toLRSHom.toShHom).mapHomotopyCategory
                  (ComplexShape.up ℤ)).obj
                  ((HomotopyCategory.singleFunctor S.X'.Modules 0).obj F'))) ≫
            (derivedPushforward h.toLRSHom.toShHom).map
              (Qh.map ((homotopyBaseChangeSquare h'.toLRSHom.toShHom f''.toLRSHom.toShHom
                S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq).app
                ((HomotopyCategory.singleFunctor S.X'.Modules 0).obj F'))) ≫
            (derivedPushforward h.toLRSHom.toShHom).map
              ((derivedPushforwardUnit f''.toLRSHom.toShHom).app
                (((modulePullback h'.toLRSHom.toShHom).mapHomotopyCategory
                  (ComplexShape.up ℤ)).obj
                  ((HomotopyCategory.singleFunctor S.X'.Modules 0).obj F'))) ≫
            (derivedPushforward h.toLRSHom.toShHom).map
              ((derivedPushforward f''.toLRSHom.toShHom).map
                (Qh.map ((Functor.mapHomotopyCategorySingleFunctor
                    (modulePullback h'.toLRSHom.toShHom) 0).hom.app F') ≫
                  (singleFunctorIsoCompQh X''.Modules 0).inv.app
                    ((modulePullback h'.toLRSHom.toShHom).obj F')))) ≫
        (derivedPushforwardHomologyComparison h.toLRSHom.toShHom (S.d : ℤ)).app
          ((derivedPushforward f''.toLRSHom.toShHom).obj
            ((singleFunctor X''.Modules 0).obj ((Scheme.Modules.pullback h').obj F'))) ≫
        (Scheme.Modules.pushforward h).map
          (homologyFunctorDerivedPushforwardIso f''
            ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom :=
  (((homologyFunctor S.Y'.Modules (S.d : ℤ)).map
        ((derivedPushforwardUnit S.f'.toLRSHom.toShHom).app
            ((HomotopyCategory.singleFunctor S.X'.Modules 0).obj F') ≫
          (derivedPushforward S.f'.toLRSHom.toShHom).map
            ((singleFunctorIsoCompQh S.X'.Modules 0).inv.app F'))) ≫=
      homologyFunctorDerivedPushforwardIso_hom_comp_homEquiv S F' h' f'' h sq).trans
    (map_comp_map_comp_comp (homologyFunctor S.Y'.Modules (S.d : ℤ))
      (derivedPushforwardUnit_comp_homEquiv_baseChange_fac S F' h' f'' h sq) _ _)

end Card

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
