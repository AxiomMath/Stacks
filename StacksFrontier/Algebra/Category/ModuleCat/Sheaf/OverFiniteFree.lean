module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Finite local freeness of a sheaf of modules descends from a covering family

Let `R` be a sheaf of rings on a site `(C, J)` and let `F` be a sheaf of `R`-modules. Suppose
a family of objects `Y : I → C` covers the terminal object and that for every `i` the
restriction `F.over (Y i)` is a *finite* coproduct of copies of the structure sheaf. Then
every object `W` of `C` has a covering family on whose members `F` is again a finite
coproduct of copies of the structure sheaf.

The mathematical content is that finite freeness is stable under further restriction. A
*finite* coproduct of copies of the unit sheaf is a biproduct, and biproducts are described by
equations between morphisms (`ι i ≫ π j = δ i j` and `∑ i, π i ≫ ι i = 𝟙`); hence they are
preserved by any additive functor, and restriction along `Over.map h` is additive. No
sheafification, no abelian structure and no pullbacks in `C` are needed. This is in sharp
contrast with the infinite-rank case: an infinite coproduct of sheaves of modules is the
*sheafification* of the objectwise coproduct, and its preservation under restriction is not
available at this generality (see the implementation notes).

## Main results

* `SheafOfModules.instAdditivePushforward`, with its two unfoldings
  `SheafOfModules.instAdditiveOverFunctor` and `SheafOfModules.instAdditiveOverMap`:
  restriction of sheaves of modules along a continuous functor is an additive functor.
* `Stacks.SheafOfModules.isColimitCofanOver`: the restriction along `h : Z ⟶ Y` of a finite
  free cofan on `F.over Y` is a finite free cofan on `F.over Z`.
* `Stacks.SheafOfModules.exists_isColimitCofan_over_of_le`: the same statement in existential
  form — if `F.over Y` is finite free then so is `F.over Z` for any `h : Z ⟶ Y`.
* `Stacks.SheafOfModules.exists_cover_isColimitCofan_of_coversTop`: the descent statement.
  Together with `Sieve.ofArrows` this is exactly the covering-family criterion for finite
  local freeness.

## Implementation notes

The additivity instance is proved by `rfl`: `SheafOfModules.pushforward` acts on a morphism by
reindexing its components along `F.op` and restricting scalars, and both operations are the
identity on the underlying additive maps.

`SheafOfModules.overMap R h` is restriction along `Over.map h`, so it goes from the slice site
over `Y` to the slice site over `Z`. Mathlib knows it is a *right* adjoint always
(`SheafOfModules.pullbackPushforwardAdjunction`) and a *left* adjoint only under
`[Limits.HasPullbacks C]` (`SheafOfModules.overMapPushforwardAdj`, which needs the functor
`Over.pullback h`). Left adjointness is what would give preservation of arbitrary coproducts.
Additivity needs no hypothesis on `C` at all but only reaches *finite* coproducts, so the
infinite-rank analogue of `exists_cover_isColimitCofan_of_coversTop` does not follow from this
file without `[Limits.HasPullbacks C]`.

The index type of the covering family produced by
`exists_cover_isColimitCofan_of_coversTop` is `Σ Z : C, {g : Z ⟶ W // (Sieve.ofObjects Y W) g}`,
which lives in `Type (max u v)`. The hypothesis's index type `I` is left completely free, so the
statement applies to a covering family indexed in any universe.

The module universe is kept equal to the universe of the sheaf of rings, which is forced:
`SheafOfModules.unit R` and hence the notion of a free sheaf of modules only typecheck there.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL) — the definitions of
  free, finite free and finite locally free sheaves of modules on a ringed site.
-/

@[expose] public section

open CategoryTheory Limits

universe t w v u

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {D : Type*} [Category* D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {G : C ⥤ D}
  {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}} [Functor.IsContinuous G J K]

/-- Restriction of sheaves of modules along a continuous functor is additive. -/
instance instAdditivePushforward
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{w} J K).obj R) :
    (SheafOfModules.pushforward.{w} φ).Additive where
  map_add := rfl

variable (T : Sheaf J RingCat.{w})

/-- Restriction of sheaves of modules to a slice site is additive. -/
instance instAdditiveOverFunctor (X : C) : (SheafOfModules.overFunctor.{w} T X).Additive where
  map_add := rfl

/-- Restriction of sheaves of modules from the slice site over `Y` to the slice site over `X`
along `h : X ⟶ Y` is additive. -/
instance instAdditiveOverMap {X Y : C} (h : X ⟶ Y) :
    (SheafOfModules.overMap.{w} T h).Additive where
  map_add := rfl

end SheafOfModules

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- Restriction along `h : Z ⟶ Y` of a cofan exhibiting `F.over Y` as a coproduct of `n`
copies of the structure sheaf, as a cofan exhibiting `F.over Z` as a coproduct of `n` copies
of the structure sheaf. -/
noncomputable def isColimitCofanOver
    (F : SheafOfModules.{w} R) {Z Y : C} (h : Z ⟶ Y) {n : ℕ}
    (ι : Fin n → (SheafOfModules.unit (R.over Y) ⟶ F.over Y))
    (hc : IsColimit (Cofan.mk (F.over Y) ι)) :
    IsColimit (Cofan.mk (F.over Z)
      (fun j => (SheafOfModules.overMap R h).map (ι j) ≫
        ((SheafOfModules.overFunctorMap R h).app F).hom)) := by
  have hp : PreservesColimit
      (Discrete.functor (fun _ : Fin n => SheafOfModules.unit (R.over Y)))
      (SheafOfModules.overMap.{w} R h) :=
    preservesCoproduct_of_preservesBiproduct _
  refine IsColimit.ofIsoColimit
    (isColimitOfPreserves (SheafOfModules.overMap.{w} R h) hc)
    (Cocone.ext ((SheafOfModules.overFunctorMap R h).app F) ?_)
  rintro ⟨j⟩
  rfl

/-- Finite freeness of a sheaf of modules on a slice site is inherited by every smaller
slice site. -/
theorem exists_isColimitCofan_over_of_le
    (F : SheafOfModules.{w} R) {Z Y : C} (h : Z ⟶ Y)
    (hF : ∃ (n : ℕ) (ι : Fin n → (SheafOfModules.unit (R.over Y) ⟶ F.over Y)),
      Nonempty (IsColimit (Cofan.mk (F.over Y) ι))) :
    ∃ (n : ℕ) (ι : Fin n → (SheafOfModules.unit (R.over Z) ⟶ F.over Z)),
      Nonempty (IsColimit (Cofan.mk (F.over Z) ι)) := by
  obtain ⟨n, ι, ⟨hc⟩⟩ := hF
  exact ⟨n, _, ⟨isColimitCofanOver F h ι hc⟩⟩

/-- If a family of objects `Y` covers the terminal object and the restriction of `F` to each
`Y i` is a coproduct of finitely many copies of the structure sheaf, then every object `W`
carries a covering family of arrows on whose sources the same holds. -/
theorem exists_cover_isColimitCofan_of_coversTop
    {I : Type t} (Y : I → C) (hY : J.CoversTop Y) (F : SheafOfModules.{w} R)
    (hF : ∀ i, ∃ (n : ℕ)
      (ι : Fin n → (SheafOfModules.unit (R.over (Y i)) ⟶ F.over (Y i))),
      Nonempty (IsColimit (Cofan.mk (F.over (Y i)) ι)))
    (W : C) :
    ∃ (I' : Type (max u v)) (V : I' → C) (f : ∀ i, V i ⟶ W),
      Sieve.ofArrows V f ∈ J W ∧
        ∀ i, ∃ (n : ℕ)
          (ι : Fin n → (SheafOfModules.unit (R.over (V i)) ⟶ F.over (V i))),
          Nonempty (IsColimit (Cofan.mk (F.over (V i)) ι)) := by
  refine ⟨Σ Z : C, { g : Z ⟶ W // (Sieve.ofObjects Y W).arrows g }, fun x => x.1,
    fun x => x.2.1, ?_, ?_⟩
  · refine J.superset_covering ?_ (hY W)
    intro Z g hg
    exact Sieve.ofArrows_mk _ _ (⟨Z, g, hg⟩ : Σ Z : C, { g : Z ⟶ W // _ })
  · rintro ⟨Z, g, i, ⟨h⟩⟩
    exact exists_isColimitCofan_over_of_le F h (hF i)

end Stacks.SheafOfModules

end
