module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenCohomologyNaturality
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.AffineOpenCohomologyPullback
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The pullback map over a compatible pair of affine opens, read downstairs on `V`

For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'`, an affine open `W` of `Y''` with `W ≤ h⁻¹(V)` and a quasi-coherent
`𝒪_{X'}`-module `F'`, write

* `k : f''⁻¹(W) ⟶ f'⁻¹(V)` for `h'` restricted to that pair of opens, affine by
  `…TopDegreeBaseChange.isAffineHom_resLE_of_isPullback`;
* `G` for the restriction of `F'` to `f'⁻¹(V)`;
* `η : G ⟶ k_* k^* G` for the unit of `k^* ⊣ k_*`.

`…TopDegreeBaseChange.affineOpenCohomologyPullbackMap` is, by its own characterising identity
`…affineOpenCohomologyPullbackMap_comp_cohomologyPullbackIsoPushforward_hom`, nothing but
`H^n(f'⁻¹(V), η)` followed by the inverse of the Leray comparison
`…TopDegreeBaseChange.cohomologyPullbackIsoPushforward` along the affine `k`, which is
[Stacks, Tag 089W]. This file carries that statement across [Stacks, Tag 01XK] for the morphism
`f' ∣_ V`, whose target is the affine *scheme* `V`, and so expresses the map as

`Γ(V, R^n (f' ∣_ V)_* η)`,

a morphism that lives downstairs on `V`. This is the (A) side of conclusion (c) of
[Stacks, Tag 0EX3] over a compatible pair of affine opens, with nothing upstairs left in it
except the two identifications conjugating it.

## Main results

* `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap_comp_rightDerivedIso_hom`: **the pullback
  map, read in the `ℤ`-indexing, is `H^n` of the unit** — the characterising identity with the
  `ℕ`-vs-`ℤ` indexing crossing performed.
* `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap_comp_cohomologyIsoGlobalSections_hom`:
  **the pullback map is the sections over `V` of the degree-`n` direct image of the unit**, as a
  commuting square whose vertical edges are the two instances of [Stacks, Tag 01XK].
* `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap_eq_sections_rightDerivedPlus_unit`: the
  same, solved for the pullback map: it **is** `Γ(V, R^n (f' ∣_ V)_* η)` conjugated by the Leray
  comparison, the indexing comparison and [Stacks, Tag 01XK].

## Implementation notes

*Why the target of the morphism matters.* [Stacks, Tag 01XK] is stated, in this repository, for a
quasi-compact quasi-separated morphism whose target is an affine scheme, as an isomorphism of
functors on the quasi-coherent modules of the source. The unit `η` is a morphism of
quasi-coherent modules on `f'⁻¹(V)` and not the restriction of anything on `X'`, so what carries
it downstairs is naturality of that isomorphism **in the coefficient**, at the morphism
`f' ∣_ V`; that square is
`…TopDegreeBaseChange.cohomologyIsoGlobalSectionsRightDerivedPushforward_hom_naturality`. The
isomorphism itself is never unfolded: only its naturality and `CategoryTheory.Iso.hom_inv_id_app`
are used.

*The two indexings.* The pullback map is built from the `ℕ`-indexed
`CategoryTheory.Functor.rightDerived`, because the Leray comparison of [Stacks, Tag 089W] is;
[Stacks, Tag 01XK] is stated at the `ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus`. The
crossing is `Stacks.DerivedIndexing.rightDerivedIso`, a *natural* isomorphism, so its square at
`η` is free — exactly as in `…TopDegreeBaseChange.affineOpenCohomologyNatIso` and
`…TopDegreeBaseChange.restrictPullbackRightDerivedPlusIso`, whose spelling is the one used here.
It is performed in its own lemma, so that no declaration of this file crosses the indexing twice.

*Every reassociation is hoisted.* The four `private` lemmas of the `Rearrange` section are
pasting statements about abstract categories, applied once each at the concrete spelling. This is
not decoration: the goals here mention `Stacks.Cohomology.AffineBase.moduleGlobalSections`, that
is `SheafOfModules.evaluation _.ringCatSheaf _`, which is not type-correct at `implicit`
transparency, so `rw` and `simp only` — including on `CategoryTheory.Category.assoc` and
`CategoryTheory.Functor.map_comp` — are not available on them.

*How the unit is read as a morphism of quasi-coherent modules.* A morphism of
`CategoryTheory.ObjectProperty.FullSubcategory` is **not** a morphism of the ambient category:
`η` ascribed to the type `⟨G, _⟩ ⟶ ⟨k_* k^* G, _⟩` is rejected. It is
`CategoryTheory.ObjectProperty.homMk η` that is such a morphism, and
`(SheafOfModules.isQuasicoherent _).ι.map (ObjectProperty.homMk η) = η` by `rfl`, which is why
the statements of this file can be written at `η` itself. The two objects of the full subcategory
are supplied as named arguments: left implicit, their membership fields are metavariables whose
projections unification cannot solve, and the elaboration runs out of heartbeats.

*What the quasi-coherence of `k_* k^* G` is.* It is [Stacks, Tag 02KG] along the affine `k`,
`AlgebraicGeometry.pushforward_isQuasicoherent_of_isAffineHom`, at the quasi-coherent `k^* G`
of [Stacks, Tag 01BG]; the latter is not an instance, so it is named in a `haveI` in each
statement, exactly as `…TopDegreeBaseChange.cohomologyPullbackIsoPushforward` does.

*Finiteness is where the situation puts it.* The hypotheses are quasi-compactness and
quasi-separatedness of `f'`, taken as instances, and nothing else: a consumer holding a
`Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation` supplies them from
`…TopDegreeBaseChangeSituation.quasiCompact_f'` and `…quasiSeparated_f'` and takes `n := S.d`,
as `…TopDegreeBaseChange.sourceCohomologyIsoSections_topDirectImage` does. Neither `Y'` nor `Y''`
nor `h` carries any hypothesis.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

attribute [local instance 10000] HasDerivedCategory.standard

section Rearrange

variable {C D : Type*} [Category* C] [Category* D]

/-- A commuting square pasted onto a commuting triangle. Stated at variables of an abstract
category, so that the only step performed at the concrete spelling of a cohomology module is one
application of this lemma. -/
private lemma comp₂_comp_eq_of_comp_eq {W X Y Z T : C} {a : W ⟶ X} {b : X ⟶ Y} {c : W ⟶ Y}
    {d : Y ⟶ Z} {e : W ⟶ T} {g : T ⟶ Z} (h₁ : a ≫ b = c) (h₂ : c ≫ d = e ≫ g) :
    a ≫ b ≫ d = e ≫ g := by
  rw [← Category.assoc, h₁, h₂]

/-- A commuting triangle carried through a functor and pasted onto a commuting square. The
functor is `ModuleCat.restrictScalars` along `(f ∣_ V)^♯` in both uses below, and the square is
the naturality of [Stacks, Tag 01XK] in the coefficient. -/
private lemma map_comp_square (R : C ⥤ D) {W Y Z : C} {P Q : D} {m : W ⟶ Y} {e : W ⟶ Z}
    {g : Z ⟶ Y} {u : R.obj Y ⟶ P} {v : R.obj Z ⟶ Q} {w : Q ⟶ P} (h₁ : m = e ≫ g)
    (h₂ : R.map g ≫ u = v ≫ w) : R.map m ≫ u = R.map e ≫ v ≫ w := by
  rw [h₁, R.map_comp, Category.assoc, h₂]

/-- Two retractions compose to a retraction, in the bracketing a composite of two isomorphisms
is met in: the hypotheses are `CategoryTheory.Iso.hom_inv_id` and
`CategoryTheory.Iso.hom_inv_id_app` of the two factors. -/
private lemma comp_comp_comp_eq_id {X Y Z : C} {a : X ⟶ Y} {a' : Y ⟶ X} {b : Y ⟶ Z}
    {b' : Z ⟶ Y} (ha : a ≫ a' = 𝟙 X) (hb : b ≫ b' = 𝟙 Y) : (a ≫ b) ≫ b' ≫ a' = 𝟙 X := by
  rw [Category.assoc, ← Category.assoc b, hb, Category.id_comp, ha]

/-- A commuting square whose right-hand edge is a composite of a functor image of a retraction
and a retraction, solved for the top edge. This is the inversion that turns the square of
`…TopDegreeBaseChange.affineOpenCohomologyPullbackMap_comp_cohomologyIsoGlobalSections_hom` into
a formula for the pullback map itself. -/
private lemma map_eq_comp_comp_of_comp_eq (R : C ⥤ D) {W Y Z : C} {P : D} {p : W ⟶ Y}
    {t : Y ⟶ Z} {t' : Z ⟶ Y} {u : R.obj Z ⟶ P} {u' : P ⟶ R.obj Z} {y : R.obj W ⟶ P}
    (ht : t ≫ t' = 𝟙 Y) (hu : u ≫ u' = 𝟙 (R.obj Z)) (h : R.map (p ≫ t) ≫ u = y) :
    R.map p = y ≫ u' ≫ R.map t' := by
  have h₁ : R.map (p ≫ t) = y ≫ u' := by rw [← h, Category.assoc, hu, Category.comp_id]
  rw [← Category.assoc, ← h₁, ← R.map_comp, Category.assoc, ht, Category.comp_id]

end Rearrange

variable {X' Y' X'' Y'' : Scheme.{u}} {f' : X' ⟶ Y'} {h' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}
  {h : Y'' ⟶ Y'}

/-- **The pullback map on cohomology over a compatible pair of affine opens, read in the
`ℤ`-indexing, is `H^n` of the unit.** For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
an affine open `V` of `Y'`, an affine open `W` of `Y''` with `W ≤ h⁻¹(V)` and a quasi-coherent
`F'`, composing `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap` with the Leray comparison
of [Stacks, Tag 089W] along the affine `h' ∣` and then with the comparison of the two indexings
of the right derived functors returns `H^n(f'⁻¹(V), -)` of the unit
`F'| ⟶ (h' ∣)_* (h' ∣)^* (F'|)`, taken at `CategoryTheory.Functor.rightDerivedPlus`.

This is the characterising identity
`…affineOpenCohomologyPullbackMap_comp_cohomologyPullbackIsoPushforward_hom` with the `ℕ`-vs-`ℤ`
indexing crossing performed, which is the form [Stacks, Tag 01XK] can be applied to. The
crossing is one naturality square of `Stacks.DerivedIndexing.rightDerivedIso` and is done here,
alone, so that no later declaration has to cross the indexing at all. -/
theorem affineOpenCohomologyPullbackMap_comp_rightDerivedIso_hom
    (hsq : IsPullback h' f'' f' h) {V : Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens}
    [IsAffine (W : Scheme)] (hWV : W ≤ h ⁻¹ᵁ V) (hle : f'' ⁻¹ᵁ W ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V))
    (F' : X'.Modules) (hF' : F'.IsQuasicoherent) (n : ℕ) :
    haveI := hF'
    haveI := isAffineHom_resLE_of_isPullback hsq hWV hle
    affineOpenCohomologyPullbackMap hsq hWV hle F' hF' n ≫
          (cohomologyPullbackIsoPushforward (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)
            ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')
            (Scheme.Modules.isQuasicoherent_restrictFunctor (f' ⁻¹ᵁ V).ι F') n).hom ≫
        (Stacks.DerivedIndexing.rightDerivedIso
            (moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)) n).hom.app
          ((Scheme.Modules.pushforward (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
            ((Scheme.Modules.pullback (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
              ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F'))) =
      (Stacks.DerivedIndexing.rightDerivedIso
            (moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)) n).hom.app
          ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F') ≫
        ((moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)).rightDerivedPlus (n : ℤ)).map
          ((Scheme.Modules.pullbackPushforwardAdjunction
              (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).unit.app
            ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')) := by
  have := hF'
  have := isAffineHom_resLE_of_isPullback hsq hWV hle
  exact comp₂_comp_eq_of_comp_eq
    (affineOpenCohomologyPullbackMap_comp_cohomologyPullbackIsoPushforward_hom hsq hWV hle F'
      hF' n)
    ((Stacks.DerivedIndexing.rightDerivedIso
        (moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)) n).hom.naturality _)

/-- **The pullback map on cohomology over a compatible pair of affine opens is the sections over
`V` of the degree-`n` direct image of the unit.** For a cartesian square
```
X'' --h'--> X'
|f''        |f'
Y'' --h-->  Y'
```
with `f'` quasi-compact and quasi-separated, an affine open `V` of `Y'`, an affine open `W` of
`Y''` with `W ≤ h⁻¹(V)` and a quasi-coherent `F'`, write `G` for the restriction of `F'` to
`f'⁻¹(V)` and `η : G ⟶ (h' ∣)_* (h' ∣)^* G` for the unit of `(h' ∣)^* ⊣ (h' ∣)_*`. Then the
composite

`H^n(f'⁻¹(V), G) ⟶ H^n(f'⁻¹(V), (h' ∣)_* (h' ∣)^* G) ⟶ Γ(V, R^n (f' ∣_ V)_* (h' ∣)_* (h' ∣)^* G)`

agrees with

`H^n(f'⁻¹(V), G) ⟶ Γ(V, R^n (f' ∣_ V)_* G) ⟶ Γ(V, R^n (f' ∣_ V)_* (h' ∣)_* (h' ∣)^* G)`,

the second arrows being [Stacks, Tag 01XK] for `f' ∣_ V` at the two coefficients, the first
arrow on the left `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap` read through
[Stacks, Tag 089W] and the indexing comparison, as
`…affineOpenCohomologyPullbackMap_comp_rightDerivedIso_hom` computes it, and the first arrow on
the right `Γ(V, R^n (f' ∣_ V)_* η)`.

So the (A) side of conclusion (c) of [Stacks, Tag 0EX3] over such a pair of opens is the sections
over `V` of the degree-`n` direct image of `η`: a morphism that lives downstairs on `V`. The
square is the form to rewrite with when the comparisons are met in the direction they are built
in; the next lemma solves it for the pullback map. -/
theorem affineOpenCohomologyPullbackMap_comp_cohomologyIsoGlobalSections_hom
    [QuasiCompact f'] [QuasiSeparated f'] (hsq : IsPullback h' f'' f' h) {V : Y'.Opens}
    [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)] (hWV : W ≤ h ⁻¹ᵁ V)
    (hle : f'' ⁻¹ᵁ W ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V)) (F' : X'.Modules) (hF' : F'.IsQuasicoherent)
    (n : ℕ) :
    haveI := hF'
    haveI := isAffineHom_resLE_of_isPullback hsq hWV hle
    haveI := AffineBaseChange.isQuasicoherent_pullback
      (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle) ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')
    (ModuleCat.restrictScalars (f' ∣_ V).appTop.hom).map
          (affineOpenCohomologyPullbackMap hsq hWV hle F' hF' n ≫
            (cohomologyPullbackIsoPushforward (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)
                ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')
                (Scheme.Modules.isQuasicoherent_restrictFunctor (f' ⁻¹ᵁ V).ι F') n).hom ≫
              (Stacks.DerivedIndexing.rightDerivedIso
                  (moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)) n).hom.app
                ((Scheme.Modules.pushforward (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
                  ((Scheme.Modules.pullback (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
                    ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')))) ≫
        (cohomologyIsoGlobalSectionsRightDerivedPushforward (f' ∣_ V) (n : ℤ)).hom.app
          ⟨(Scheme.Modules.pushforward (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
            ((Scheme.Modules.pullback (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
              ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')), inferInstance⟩ =
      (ModuleCat.restrictScalars (f' ∣_ V).appTop.hom).map
            ((Stacks.DerivedIndexing.rightDerivedIso
                (moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)) n).hom.app
              ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')) ≫
          (cohomologyIsoGlobalSectionsRightDerivedPushforward (f' ∣_ V) (n : ℤ)).hom.app
            ⟨(Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F', inferInstance⟩ ≫
        (moduleGlobalSections (V : Scheme)).map
          (((Scheme.Modules.pushforward (f' ∣_ V)).rightDerivedPlus (n : ℤ)).map
            ((Scheme.Modules.pullbackPushforwardAdjunction
                (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).unit.app
              ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F'))) := by
  have := hF'
  have := isAffineHom_resLE_of_isPullback hsq hWV hle
  have := AffineBaseChange.isQuasicoherent_pullback
    (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle) ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')
  exact map_comp_square _
    (affineOpenCohomologyPullbackMap_comp_rightDerivedIso_hom hsq hWV hle F' hF' n)
    (cohomologyIsoGlobalSectionsRightDerivedPushforward_hom_naturality (f' ∣_ V) (n : ℤ)
      (A := ⟨(Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F', inferInstance⟩)
      (B := ⟨(Scheme.Modules.pushforward (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
        ((Scheme.Modules.pullback (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
          ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')), inferInstance⟩)
      (ObjectProperty.homMk
        ((Scheme.Modules.pullbackPushforwardAdjunction
            (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).unit.app
          ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F'))))

/-- **The pullback map on cohomology over a compatible pair of affine opens is
`Γ(V, R^n (f' ∣_ V)_* η)`, conjugated by the comparisons.** The square of
`…TopDegreeBaseChange.affineOpenCohomologyPullbackMap_comp_cohomologyIsoGlobalSections_hom`
solved for its top edge: `…TopDegreeBaseChange.affineOpenCohomologyPullbackMap`, its scalars
restricted along `(f' ∣_ V)^♯`, is the sections over `V` of the degree-`n` direct image of the
unit `η` of `(h' ∣)^* ⊣ (h' ∣)_*`, conjugated by [Stacks, Tag 01XK] at the two coefficients, by
the comparison of the two indexings of the right derived functors and by the Leray comparison of
[Stacks, Tag 089W] along the affine `h' ∣`.

Every factor on the right-hand side is one of those four named comparisons; nothing is an
`CategoryTheory.eqToHom`, and no definition is unfolded. This is the form in which a consumer
rewrites the (A) side of conclusion (c) of [Stacks, Tag 0EX3] into a statement about `V`. -/
theorem affineOpenCohomologyPullbackMap_eq_sections_rightDerivedPlus_unit
    [QuasiCompact f'] [QuasiSeparated f'] (hsq : IsPullback h' f'' f' h) {V : Y'.Opens}
    [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)] (hWV : W ≤ h ⁻¹ᵁ V)
    (hle : f'' ⁻¹ᵁ W ≤ h' ⁻¹ᵁ (f' ⁻¹ᵁ V)) (F' : X'.Modules) (hF' : F'.IsQuasicoherent)
    (n : ℕ) :
    haveI := hF'
    haveI := isAffineHom_resLE_of_isPullback hsq hWV hle
    haveI := AffineBaseChange.isQuasicoherent_pullback
      (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle) ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')
    (ModuleCat.restrictScalars (f' ∣_ V).appTop.hom).map
        (affineOpenCohomologyPullbackMap hsq hWV hle F' hF' n) =
      ((ModuleCat.restrictScalars (f' ∣_ V).appTop.hom).map
              ((Stacks.DerivedIndexing.rightDerivedIso
                  (moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)) n).hom.app
                ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')) ≫
            (cohomologyIsoGlobalSectionsRightDerivedPushforward (f' ∣_ V) (n : ℤ)).hom.app
              ⟨(Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F', inferInstance⟩ ≫
          (moduleGlobalSections (V : Scheme)).map
            (((Scheme.Modules.pushforward (f' ∣_ V)).rightDerivedPlus (n : ℤ)).map
              ((Scheme.Modules.pullbackPushforwardAdjunction
                  (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).unit.app
                ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')))) ≫
        (cohomologyIsoGlobalSectionsRightDerivedPushforward (f' ∣_ V) (n : ℤ)).inv.app
            ⟨(Scheme.Modules.pushforward (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
              ((Scheme.Modules.pullback (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
                ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')), inferInstance⟩ ≫
          (ModuleCat.restrictScalars (f' ∣_ V).appTop.hom).map
            ((Stacks.DerivedIndexing.rightDerivedIso
                  (moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)) n).inv.app
                ((Scheme.Modules.pushforward (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
                  ((Scheme.Modules.pullback (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)).obj
                    ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F'))) ≫
              (cohomologyPullbackIsoPushforward (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)
                  ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')
                  (Scheme.Modules.isQuasicoherent_restrictFunctor (f' ⁻¹ᵁ V).ι F') n).inv) := by
  have := hF'
  have := isAffineHom_resLE_of_isPullback hsq hWV hle
  have := AffineBaseChange.isQuasicoherent_pullback
    (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle) ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')
  exact map_eq_comp_comp_of_comp_eq _
    (comp_comp_comp_eq_id
      (cohomologyPullbackIsoPushforward (h'.resLE (f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W) hle)
        ((Scheme.Modules.restrictFunctor (f' ⁻¹ᵁ V).ι).obj F')
        (Scheme.Modules.isQuasicoherent_restrictFunctor (f' ⁻¹ᵁ V).ι F') n).hom_inv_id
      ((Stacks.DerivedIndexing.rightDerivedIso
        (moduleGlobalSections (f' ⁻¹ᵁ V : Scheme)) n).hom_inv_id_app _))
    ((cohomologyIsoGlobalSectionsRightDerivedPushforward (f' ∣_ V) (n : ℤ)).hom_inv_id_app _)
    (affineOpenCohomologyPullbackMap_comp_cohomologyIsoGlobalSections_hom hsq hWV hle F' hF' n)

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
