module

public import StacksFrontier.AlgebraicGeometry.PullbackSections.Transpose
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeMapSections

/-!
# The adjunction transpose of the top-degree base-change map, and its sections

`BaseChangeMapSections.lean` reduces conclusion (c) of [Stacks, Tag 0EX3] to the bijectivity of

> `Γ(W, γ⁺) : Γ(W, h^* R^d f'_* F') ⟶ Γ(W, R^d f''_* (h')^* F')`

for the affine opens `W` of `Y''` lying over an affine open `V` of `Y'`
(`isIso_topDirectImageBaseChangeMap_of_bijective_app_plus_affineOpens`). The source of `γ⁺` is a
pullback, so a section of it over `W` is built from the pullbacks
`AlgebraicGeometry.Scheme.Modules.pullbackSection h A V W` of the sections of
`A = R^d f'_* F'` over `V`, and `AlgebraicGeometry.Scheme.Modules.pullbackSection_homEquiv` says
what `γ⁺` does to such a section: it is the restriction to `W` of the value over `V` of the
**adjoint transpose**

> `γ̃⁺ : R^d f'_* F' ⟶ h_* R^d f''_* (h')^* F'`

of `γ⁺` under the adjunction `h^* ⊣ h_*` of [Stacks, Tag 01BH]. So the sections question is a
question about `γ̃⁺`, and this file computes `γ̃⁺`: it is the four-fold composite of the canonical
factors `γ⁺` is assembled from, each one transposed or pushed forward along `h`.

Concretely, `γ⁺` is

> `h^* R^d f'_* F' ⟶ h^* H^d(Rf'_*(F'[0])) ⟶ H^d(Lh^* Rf'_* (F'[0])) ⟶`
> `H^d(Rf''_*((h')^* F'[0])) ⟶ R^d f''_* (h')^* F'`,

the two outer factors being the crossing `homologyFunctorDerivedPushforwardIso` of the two models
of `Rf_*`, the second the identification `topDirectImagePullbackIso` that conclusion (a) of the
tag supplies, and the third the degree-`d` cohomology of the two-step composition the source
displays — the derived base change map of [Stacks, Tag 08HY] followed by the derived pushforward
of the comparison from derived to ordinary pullback. Transposing it is formal: the first factor is
`h^*` of a morphism, so the transposition passes it unchanged, the transposition of the second is
all that is left of the adjunction, and the remaining two are carried by `h_*`.

The square is taken **commutative**, not cartesian: nothing here uses more, and
`toShHom_comm_of_isPullback` supplies the commutativity from a cartesian square, which is the form
conclusion (c) has.

## Main results

* `…TopDegreeBaseChange.homEquiv_topDirectImageBaseChangeMapPlus`: **the transpose of `γ⁺` is the
  transpose of `γ` conjugated by the two crossings of the models of `Rf_*`.**
* `…TopDegreeBaseChange.homEquiv_topDirectImageBaseChangeMap`: **the transpose of `γ`** is the
  transpose of the identification of conclusion (a), followed by `h_*` of the degree-`d`
  cohomology of the two-step composition the source displays.
* `…TopDegreeBaseChange.homEquiv_topDirectImageBaseChangeMapPlus_eq`: **the transpose of `γ⁺` as a
  four-fold composite of canonical factors.**
* `…TopDegreeBaseChange.homEquiv_topDirectImageBaseChangeMapPlus_eq_unit`: **the same with no
  adjunction left in it** — the unit of `h^* ⊣ h_*` and the direct images along `h` of the three
  other factors of `γ⁺`.
* `…TopDegreeBaseChange.topDirectImageBaseChangeMapPlus_app_pullbackSection`: **`γ⁺` on the
  pullback of a section**, over an open `W` of `Y''` inside the inverse image of an open `V` of
  `Y'`: it is the restriction to `W` of the value over `V` of that five-fold composite.
* `…TopDegreeBaseChange.homEquiv_map_comp_comp`, `…TopDegreeBaseChange.comp_middle_comp` and
  `…TopDegreeBaseChange.comp_homEquiv_comp`: the three rearrangements the computation needs, at
  variables of abstract categories.

## Implementation notes

*The rearrangements are hoisted onto variables.* Both `γ⁺` and its transpose are composites of
morphisms between objects spelled as iterated applications of derived functors, and a
`Category.assoc` rewrite on such a composite is the `isDefEq` timeout this directory records
repeatedly. `homEquiv_map_comp_comp`, `comp_middle_comp` and `comp_homEquiv_comp` are therefore
stated at variables of abstract categories, where the reassociation costs nothing, and the unifier
meets the concrete spelling only at the application. This is the technique
`Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparison_fac` and its neighbours in
`StacksFrontier/Topology/Sheaves/Cohomology/DerivedPushforward/PushforwardComparisonAgreesWithOrdinary.lean` measure for the same shape of
calculation one level up, in the derived category.

*Why the two crossings transpose so cheaply.* The first factor of `γ⁺` is
`(Scheme.Modules.pullback h).mapIso (homologyFunctorDerivedPushforwardIso S.f' F' d)` inverted,
and `CategoryTheory.Functor.mapIso` has `inv := F.map i.inv`, so that factor *is* `h^*` of a
morphism and `CategoryTheory.Adjunction.homEquiv_naturality_left` applies to it with one
definitional step. The last factor is a morphism of the target, where
`CategoryTheory.Adjunction.homEquiv_naturality_right` applies. Neither is reconciled at a
component `.app K`.

*The transposes are applied in term mode.* Each of the four sheaf-level identities below is a
single application of one of the three rearrangement lemmas, or the composition of two such by
`Eq.trans`; no rewrite motive is formed over an object of the derived category. The one tactic
proof is the sections statement, where the two rewrites are of morphisms of sheaves of modules on
`Y'`.

## What the next step owes

The four factors of `γ̃⁺` are canonical and named, and three of them are still to be computed
against the geometry over the pair of opens `V` and `W`. What the consumer wants is the identity
with `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap` of
`AffineOpenCohomologyPullback.lean` — the degree-`d` cohomology of the unit of
`(h' ∣)^* ⊣ (h' ∣)_*`, read through the Leray comparison of [Stacks, Tag 089W] — under the
identifications of [Stacks, Tag 01XK] over the two opens. Two steps separate the composite below
from it:

* *the transport of the derived identity through sections.*
  `Stacks.Cohomology.DerivedBaseChange.derivedPushforwardComparison_fac` says that the derived
  base change map of [Stacks, Tag 08HY], transposed along the bottom of the square, is the
  composite of the **degreewise** units of [Stacks, Tag 0096]. Its two sides live in `D(𝒪_{Y'})`,
  and what the third factor of `γ̃⁺` presents is `h_*` of `H^d` of the untransposed map. Passing
  from one to the other is the compatibility of `topDirectImagePullbackIso` and of the canonical
  map `H^d(Rh_* K) ⟶ h_* H^d K` with the two units.

  **The second of those two maps is available.** It is
  `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardHomologyComparison`,
  for every morphism of ringed spaces and in every degree with no hypothesis, together with the
  factorisation `…derivedPushforwardHomologyComparison_fac_app` that pins it down — the degree-`q`
  cohomology of the comparison `f_* M ⟶ Rf_* M`, followed by it, is the comparison of `H^q` with
  `f_*` on the homotopy category. It is an instantiation of
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.derivedHomologyComparison` at the
  direct image, which is left exact. What is still owed is only the first map's half: the
  compatibility of `topDirectImagePullbackIso` with it. The handle on `topDirectImagePullbackIso`
  is its cycle-class characterisation `topDirectImagePullbackIso_cycles`, and the edge morphism is
  characterised at the cycle level too, by
  `Stacks.Cohomology.HypercohomologyEdge.HomologyComparison.homologyπ_comp_homologyComparison`, so
  the two are to be matched at a common representative complex of `Rf'_*(F'[0])`;
* *derived sections over an open against derived global sections of the restriction.*
  `topDirectImageSectionsIsoDerivedSections` of `TopDirectImageSectionsDerived.lean` computes
  `Γ(V, H^d(Rf'_*(F'[0])))` as `H^d(RΓ(f'⁻¹V, F'[0]))` with the derived sections of
  [Stacks, Tag 0D5W] in the spelling
  `Stacks.Cohomology.DerivedSectionsLeray.derivedPreimageSections`, over the **open** `f'⁻¹V` of
  `X'`, whereas `affineOpenCohomologyPullbackMap` is stated at the derived functor of
  `Stacks.Cohomology.moduleGlobalSections` of the **scheme** `f'⁻¹V`. The comparison of those two
  derived functors is what joins the two halves of the computation, and it is
  `…TopDegreeBaseChange.derivedPreimageSectionsHomologyIso` of
  `EdgeCompatPreimageSections.lean`, read across `f'` as the consumer meets it: for a morphism of
  schemes, an open of the target, a sheaf of modules and a degree, with no hypothesis on any of
  them.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0096](https://stacks.math.columbia.edu/tag/0096)
* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 08HY](https://stacks.math.columbia.edu/tag/08HY)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open DerivedCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### The three rearrangements, on variables -/

/-- **Transposing a composite whose first factor is the image of a morphism under the left
adjoint.** The transposition moves past that factor, and a last factor is carried by the right
adjoint. Stated at variables of abstract categories, which is where the reassociation is free;
at the application the unifier meets the concrete spelling only once. -/
theorem homEquiv_map_comp_comp {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A A' : C} {B B' : D} (u : A ⟶ A') (w : L.obj A' ⟶ B) (c : B ⟶ B') :
    adj.homEquiv A B' (L.map u ≫ w ≫ c) = u ≫ adj.homEquiv A' B w ≫ R.map c := by
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]

/-- **Splitting the middle factor of a three-fold composite.** Substituting a two-fold composite
for the middle factor of `u ≫ m ≫ c` and reassociating, at variables of an abstract category.
This is what turns the transpose of `γ⁺` with the transpose of `γ` named into the four-fold
composite of canonical factors, without a `Category.assoc` rewrite on the concrete spelling. -/
theorem comp_middle_comp {C : Type*} [Category C] {A A' X B B' : C} (u : A ⟶ A')
    {m : A' ⟶ B} {t₁ : A' ⟶ X} {t₂ : X ⟶ B} (hm : m = t₁ ≫ t₂) (c : B ⟶ B') :
    u ≫ m ≫ c = u ≫ t₁ ≫ t₂ ≫ c := by
  rw [hm, Category.assoc]

/-- **A transpose inside a composite, written through the unit.** A transposed morphism occurring
as the second factor of a four-fold composite is the unit of the adjunction followed by the right
adjoint of the morphism, by `CategoryTheory.Adjunction.homEquiv_unit`. Stated at variables of
abstract categories: this is where the reassociation the substitution needs is free. -/
theorem comp_homEquiv_comp {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) {A A' Z Z' : C} {B : D} (u : A ⟶ A') (w : L.obj A' ⟶ B) (x : R.obj B ⟶ Z)
    (y : Z ⟶ Z') :
    u ≫ adj.homEquiv A' B w ≫ x ≫ y = u ≫ adj.unit.app A' ≫ R.map w ≫ x ≫ y := by
  rw [Adjunction.homEquiv_unit, Category.assoc]

/-! ### The transpose of the base-change map -/

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y')
  (sq : h'.toLRSHom.toShHom ≫ S.f'.toLRSHom.toShHom
    = f''.toLRSHom.toShHom ≫ h.toLRSHom.toShHom)

/-- **The transpose of `γ⁺` is the transpose of `γ` conjugated by the two crossings of the models
of `Rf_*`.** `γ⁺` is `γ` with the crossing
`homologyFunctorDerivedPushforwardIso` inverted in front — pulled back along `h`, hence `h^*` of
a morphism — and the crossing at `f''` behind it, so transposing it under `h^* ⊣ h_*` leaves the
first factor where it is and carries the last into `h_*`. -/
theorem homEquiv_topDirectImageBaseChangeMapPlus :
    (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
        (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) =
      (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).inv ≫
        (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
          (topDirectImageBaseChangeMap S F' h' f'' h sq) ≫
        (Scheme.Modules.pushforward h).map
          (homologyFunctorDerivedPushforwardIso f''
            ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom :=
  homEquiv_map_comp_comp (Scheme.Modules.pullbackPushforwardAdjunction h)
    (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).inv
    (topDirectImageBaseChangeMap S F' h' f'' h sq)
    (homologyFunctorDerivedPushforwardIso f''
      ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom

/-- **The transpose of the canonical map `γ` of [Stacks, Tag 0EX3].** `γ` is the identification
`h^* R^d f'_* F' ≅ H^d(Lh^* Rf'_*(F'[0]))` of conclusion (a) followed by the degree-`d`
cohomology of the two-step composition the source displays, so its transpose under `h^* ⊣ h_*` is
the transpose of that identification followed by `h_*` of the latter. -/
theorem homEquiv_topDirectImageBaseChangeMap :
    (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
        (topDirectImageBaseChangeMap S F' h' f'' h sq) =
      (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
          (topDirectImagePullbackIso S F' h).hom ≫
        (Scheme.Modules.pushforward h).map
          ((homologyFunctor Y''.Modules (S.d : ℤ)).map
            (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap h'.toLRSHom.toShHom
                f''.toLRSHom.toShHom S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq
                ((singleFunctor S.X'.Modules 0).obj F') ≫
              (derivedPushforward f''.toLRSHom.toShHom).map
                (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0))) :=
  (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv_naturality_right _ _

/-- **The transpose of `γ⁺`, as a four-fold composite of canonical factors**:

> `R^d f'_* F' ⟶ H^d(Rf'_*(F'[0])) ⟶ h_* H^d(Lh^* Rf'_*(F'[0])) ⟶`
> `h_* H^d(Rf''_*((h')^* F'[0])) ⟶ h_* R^d f''_* (h')^* F'`,

the crossing of the two models of `Rf_*` inverted, the transpose of the identification of
conclusion (a), the direct image of the degree-`d` cohomology of the two-step composition the
source displays, and the direct image of the crossing at `f''`.

This is the sheaf-level identity the sections statement
`topDirectImageBaseChangeMapPlus_app_pullbackSection` reads over a pair of opens. -/
theorem homEquiv_topDirectImageBaseChangeMapPlus_eq :
    (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
        (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) =
      (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).inv ≫
        (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
            (topDirectImagePullbackIso S F' h).hom ≫
          (Scheme.Modules.pushforward h).map
            ((homologyFunctor Y''.Modules (S.d : ℤ)).map
              (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap h'.toLRSHom.toShHom
                  f''.toLRSHom.toShHom S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq
                  ((singleFunctor S.X'.Modules 0).obj F') ≫
                (derivedPushforward f''.toLRSHom.toShHom).map
                  (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0))) ≫
          (Scheme.Modules.pushforward h).map
            (homologyFunctorDerivedPushforwardIso f''
              ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom :=
  (homEquiv_topDirectImageBaseChangeMapPlus S F' h' f'' h sq).trans
    (comp_middle_comp _ (homEquiv_topDirectImageBaseChangeMap S F' h' f'' h sq) _)

/-- **The transpose of `γ⁺` with no adjunction left in it: the unit of `h^* ⊣ h_*` and the direct
images of the factors of `γ⁺`.** Replacing the transpose of the identification of conclusion (a)
by the unit of `h^* ⊣ h_*` followed by `h_*` of that identification
(`CategoryTheory.Adjunction.homEquiv_unit`) turns
`homEquiv_topDirectImageBaseChangeMapPlus_eq` into a composite of five morphisms, of which the
only one that is not a crossing, a derived base change map or a comparison is the unit itself:

> `R^d f'_* F' ⟶ H^d(Rf'_*(F'[0])) ⟶ h_* h^* H^d(Rf'_*(F'[0])) ⟶ h_* H^d(Lh^* Rf'_*(F'[0]))`
> `⟶ h_* H^d(Rf''_*((h')^* F'[0])) ⟶ h_* R^d f''_* (h')^* F'`.

This is the shape in which the transpose is to be matched with the pullback map on top-degree
cohomology over a pair of affine opens: that map, too, is the degree-`d` cohomology of a unit read
through comparisons. -/
theorem homEquiv_topDirectImageBaseChangeMapPlus_eq_unit :
    (Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _
        (topDirectImageBaseChangeMapPlus S F' h' f'' h sq) =
      (homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).inv ≫
        (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app
            ((homologyFunctor S.Y'.Modules (S.d : ℤ)).obj
              ((derivedPushforward S.f'.toLRSHom.toShHom).obj
                ((singleFunctor S.X'.Modules 0).obj F'))) ≫
          (Scheme.Modules.pushforward h).map (topDirectImagePullbackIso S F' h).hom ≫
          (Scheme.Modules.pushforward h).map
            ((homologyFunctor Y''.Modules (S.d : ℤ)).map
              (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap h'.toLRSHom.toShHom
                  f''.toLRSHom.toShHom S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq
                  ((singleFunctor S.X'.Modules 0).obj F') ≫
                (derivedPushforward f''.toLRSHom.toShHom).map
                  (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0))) ≫
          (Scheme.Modules.pushforward h).map
            (homologyFunctorDerivedPushforwardIso f''
              ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom :=
  (homEquiv_topDirectImageBaseChangeMapPlus_eq S F' h' f'' h sq).trans
    (comp_homEquiv_comp (Scheme.Modules.pullbackPushforwardAdjunction h) _
      (topDirectImagePullbackIso S F' h).hom _ _)

/-! ### `γ⁺` on the pullback of a section -/

/-- **`γ⁺` on the pullback of a section, over a pair of compatible opens.** Let `V` be an open of
`Y'` and `W` an open of `Y''` inside the inverse image of `V`. A section `a` of
`A = R^d f'_* F'` over `V` pulls back, through the unit of `h^* ⊣ h_*` and restriction, to a
section `pullbackSection h A V W hWV a` of `h^* A` over `W`, and the value of `γ⁺` on it is the
restriction to `W` of the value over `V` of the five-fold composite
`homEquiv_topDirectImageBaseChangeMapPlus_eq_unit` computes — the unit of `h^* ⊣ h_*` and the
direct images along `h` of the identification of conclusion (a), of the degree-`d` cohomology of
the two-step composition the source displays, and of the crossing of the two models of `Rf_*`.

This is the form in which the remaining content of conclusion (c) of [Stacks, Tag 0EX3] is to be
attacked: for `V` and `W` affine the sections of the source of `γ⁺` over `W` are the base change
of the sections of `A` over `V`, by `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, whose
generators are exactly these pullbacks, so the right-hand side determines `Γ(W, γ⁺)`. -/
theorem topDirectImageBaseChangeMapPlus_app_pullbackSection
    (V : S.Y'.Opens) (W : Y''.Opens) (hWV : W ≤ h ⁻¹ᵁ V)
    (a : (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F').val.obj (op V)) :
    (topDirectImageBaseChangeMapPlus S F' h' f'' h sq).val.app (op W)
        (Scheme.Modules.pullbackSection h
          (((Scheme.Modules.pushforward S.f').rightDerivedPlus (S.d : ℤ)).obj F') V W hWV a) =
      (((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
            ((Scheme.Modules.pullback h').obj F')).val.map (homOfLE hWV).op
        (((homologyFunctorDerivedPushforwardIso S.f' F' (S.d : ℤ)).inv ≫
            (Scheme.Modules.pullbackPushforwardAdjunction h).unit.app
                ((homologyFunctor S.Y'.Modules (S.d : ℤ)).obj
                  ((derivedPushforward S.f'.toLRSHom.toShHom).obj
                    ((singleFunctor S.X'.Modules 0).obj F'))) ≫
              (Scheme.Modules.pushforward h).map (topDirectImagePullbackIso S F' h).hom ≫
              (Scheme.Modules.pushforward h).map
                ((homologyFunctor Y''.Modules (S.d : ℤ)).map
                  (Stacks.Cohomology.DerivedBaseChange.derivedBaseChangeMap h'.toLRSHom.toShHom
                      f''.toLRSHom.toShHom S.f'.toLRSHom.toShHom h.toLRSHom.toShHom sq
                      ((singleFunctor S.X'.Modules 0).obj F') ≫
                    (derivedPushforward f''.toLRSHom.toShHom).map
                      (derivedToOrdinaryPullbackSingle h'.toLRSHom.toShHom F' 0))) ≫
              (Scheme.Modules.pushforward h).map
                (homologyFunctorDerivedPushforwardIso f''
                  ((Scheme.Modules.pullback h').obj F') (S.d : ℤ)).hom).val.app (op V) a) := by
  rw [Scheme.Modules.pullbackSection_homEquiv,
    homEquiv_topDirectImageBaseChangeMapPlus_eq_unit]

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
