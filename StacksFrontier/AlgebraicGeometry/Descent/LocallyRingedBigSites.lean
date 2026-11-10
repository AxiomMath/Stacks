module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherentModulesAndAffines
public import StacksFrontier.AlgebraicGeometry.Topologies.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.ConstantSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Zariski.ConstantSheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.OneIsNeverZero

/-!
# The big sites of a scheme are locally ringed

Let `S` be a scheme and let `τ` be one of the Zariski, étale, smooth, syntomic or fppf
topologies. The big `τ`-site of `S`, carrying the sheaf `T ↦ Γ(T, 𝒪_T)` of global functions as
its structure sheaf, is a locally ringed site in the sense of Stacks 04EU.

Both conditions are checked on sections, with no reference to points of the site. For a global
function `a` on the scheme underlying an object, the two standard opens `D(a)` and `D(1 - a)`
cover that scheme, because `a + (1 - a) = 1` is a unit everywhere; on the first `a` is
invertible and on the second `1 - a` is. A Zariski open covering is a covering in each of the
five topologies, so the two opens generate a covering sieve and every section is locally either
a unit or has unit complement. For the other condition, a scheme whose ring of global functions
satisfies `0 = 1` is empty — the germ at any of its points would be a map to a local ring
sending `0` to `1` — and an empty object is covered by the empty sieve.

## Main results

* `AlgebraicGeometry.RingedSite.isLocallyRinged_globalFunctions`: a site of schemes carrying
  global functions as its structure sheaf is locally ringed as soon as every open cover of the
  scheme underlying an object is refined by a covering family of the site.
* `AlgebraicGeometry.bigZariskiOverRingedSite_isLocallyRinged` and its étale, smooth, syntomic
  and fppf counterparts: the five big sites of Stacks 0GZV are locally ringed.

## Implementation notes

The hypothesis of the general statement is the predicate already used for the constant sheaf on
these sites, `AlgebraicGeometry.bigZariskiOver_openCoverData` and its four counterparts: an open
cover of the scheme underlying an object, indexed by the points of that scheme, is refined by a
covering family each of whose members maps into one of the opens. It is exactly what the Zariski
representative theorems of Stacks 03WV, 03WW, 03WX, 03WZ and 03X2 supply, and the empty-sieve
half is `AlgebraicGeometry.openCoverData_bottom`, which is derived from it.

The `1 ≠ 0` condition is the sheaf-level one of Stacks 05D7, read through
`Stacks.Sheaves.LocallyRingedSite.isIso_oneIsNeverZero_iff`: the morphism from the empty sheaf
to the equalizer of the zero and one sections is an isomorphism exactly when `0 ≠ 1` over every
object the empty sieve does not cover. The two spellings of that morphism — the one of
`AlgebraicGeometry.RingedSite.oneIsNeverZero` and the one of
`Stacks.Sheaves.LocallyRingedSite.oneIsNeverZero` — are the same term, so no comparison enters.

The stalk criterion `AlgebraicGeometry.RingedSite.isLocallyRinged_of_local_stalks` is not used.
It asks for a conservative family of points of the site whose fibres live in the universe of the
sections, and the families available for the big sites, such as
`AlgebraicGeometry.bigFppf_hasConservativeFamily`, live one universe higher.

## References

* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU)
* [Stacks Project, Tag 05D7](https://stacks.math.columbia.edu/tag/05D7)
* [Stacks Project, Tag 0GZV](https://stacks.math.columbia.edu/tag/0GZV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Units among the global functions of a scheme -/

/-- A global function pulls back to a unit along any morphism whose image lies in the standard
open of that function: the standard open of the pullback is then the whole source, so the germ
of the pullback is a unit at every point, and invertibility of a section is local. -/
public theorem Scheme.isUnit_appTop_of_range_subset_basicOpen {Y Z : Scheme.{u}} (φ : Z ⟶ Y)
    (b : Γ(Y, ⊤)) (h : Set.range φ.base ⊆ (Y.basicOpen b : Set Y)) :
    IsUnit (φ.appTop b) := by
  have hb : Z.basicOpen (φ.appTop b) = ⊤ := by
    rw [← Scheme.preimage_basicOpen_top]
    exact le_antisymm le_top fun z _ => h ⟨z, rfl⟩
  exact Z.toRingedSpace.isUnit_of_isUnit_germ ⊤ (φ.appTop b) fun z _ =>
    (Z.mem_basicOpen_top _ z).1 (by rw [hb]; trivial)

/-- The standard opens of a function and of its complement cover: at every point one of the two
germs is a unit, because their sum is `1`. -/
public theorem Scheme.basicOpen_sup_basicOpen_one_sub (X : Scheme.{u}) (U : X.Opens)
    (a : Γ(X, U)) : X.basicOpen a ⊔ X.basicOpen (1 - a) = U := by
  refine le_antisymm (sup_le (X.basicOpen_le _) (X.basicOpen_le _)) ?_
  calc U = X.basicOpen (1 : Γ(X, U)) := X.basicOpen_one.symm
    _ = X.basicOpen (a + (1 - a)) := by rw [add_sub_cancel]
    _ ≤ _ := X.basicOpen_add_le _ _

/-! ### Local ringedness of a site of schemes with global functions -/

namespace RingedSite

variable {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})

/-- Every global function on the scheme underlying an object of the site is, on a covering,
either a unit or has unit complement: the two standard opens of the function and of its
complement cover, and an open cover is refined by a covering family. -/
public theorem locallyEitherUnit_globalFunctions
    (hsh : Presheaf.IsSheaf J (F.op ⋙ Scheme.Γ))
    (hOpen : ∀ {T : C} (U : F.obj T → (F.obj T).Opens), IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → C) (a : ∀ i, W i ⟶ T) (r : I → F.obj T),
        Sieve.ofArrows W a ∈ J T ∧ ∀ i y, F.map (a i) y ∈ U (r i)) :
    LocallyEitherUnit (J := J) ⟨F.op ⋙ Scheme.Γ, hsh⟩ := by
  classical
  intro T a
  set Y : Scheme.{u} := F.obj T with hY
  set b : Γ(Y, ⊤) := a with hb
  set U : Y → Y.Opens := fun x => if x ∈ Y.basicOpen b then Y.basicOpen b
    else Y.basicOpen (1 - b) with hU
  have hmem : ∀ x : Y, x ∈ U x := by
    intro x
    by_cases hx : x ∈ Y.basicOpen b
    · simpa only [hU, ite_eq_left hx] using hx
    · have h1 : x ∈ (Y.basicOpen b ⊔ Y.basicOpen (1 - b) : Y.Opens) := by
        rw [Y.basicOpen_sup_basicOpen_one_sub]; trivial
      have h2 : x ∈ Y.basicOpen b ∨ x ∈ Y.basicOpen (1 - b) := by
        simpa only [← SetLike.mem_coe, Opens.coe_sup, Set.mem_union] using h1
      simpa only [hU, ite_eq_right hx] using h2.resolve_left hx
  have hcover : IsOpenCover U :=
    le_antisymm le_top fun x _ => Opens.mem_iSup.2 ⟨x, hmem x⟩
  obtain ⟨I, W, g, r, hmemJ, hmaps⟩ := hOpen U hcover
  refine ⟨Sieve.ofArrows W g, hmemJ, ?_⟩
  intro V h hh
  obtain ⟨i, e, rfl⟩ := (Sieve.mem_ofArrows_iff W g h).1 hh
  have hrange : Set.range (F.map (g i)).base ⊆ (U (r i) : Set Y) := by
    rintro y ⟨z, rfl⟩
    exact hmaps i z
  have hmap : ((F.op ⋙ Scheme.Γ).map (e ≫ g i).op) =
      (F.map (g i)).appTop ≫ (F.map e).appTop := by
    change (F.map (e ≫ g i)).appTop = _
    rw [F.map_comp, Scheme.Hom.comp_appTop]
  by_cases hx : r i ∈ Y.basicOpen b
  · refine Or.inl ?_
    have h0 : IsUnit ((F.map (g i)).appTop b) :=
      Scheme.isUnit_appTop_of_range_subset_basicOpen _ _ (by
        simpa only [hU, ite_eq_left hx] using hrange)
    rw [hmap]
    exact h0.map (CommRingCat.Hom.hom (F.map e).appTop)
  · refine Or.inr ?_
    have h0 : IsUnit ((F.map (g i)).appTop (1 - b)) :=
      Scheme.isUnit_appTop_of_range_subset_basicOpen _ _ (by
        simpa only [hU, ite_eq_right hx] using hrange)
    rw [hmap]
    exact h0.map (CommRingCat.Hom.hom (F.map e).appTop)

/-- **Stacks Project, Tag 04EU.** A site of schemes carrying the sheaf of global functions as
its structure sheaf is locally ringed, as soon as every open cover of the scheme underlying an
object is refined by a covering family of the site. -/
public theorem isLocallyRinged_globalFunctions
    (hsh : Presheaf.IsSheaf J (F.op ⋙ Scheme.Γ))
    (hOpen : ∀ {T : C} (U : F.obj T → (F.obj T).Opens), IsOpenCover U →
      ∃ (I : Type (u + 1)) (W : I → C) (a : ∀ i, W i ⟶ T) (r : I → F.obj T),
        Sieve.ofArrows W a ∈ J T ∧ ∀ i y, F.map (a i) y ∈ U (r i)) :
    IsLocallyRinged (⟨C, J, ⟨F.op ⋙ Scheme.Γ, hsh⟩⟩ : RingedSite.{u + 1, u, u}) := by
  refine ⟨?_, locallyEitherUnit_globalFunctions J F hsh hOpen⟩
  refine (Stacks.Sheaves.LocallyRingedSite.isIso_oneIsNeverZero_iff
    (⟨F.op ⋙ Scheme.Γ, hsh⟩ : Sheaf J CommRingCat.{u})).2 ?_
  intro T hT h01
  refine hT (openCoverData_bottom F J hOpen ⟨fun x => ?_⟩)
  have h0 : (0 : Γ(F.obj T, ⊤)) = 1 := h01
  have h2 := ((F.obj T).presheaf.germ ⊤ x trivial).hom.congr_arg h0
  simp only [map_zero, map_one] at h2
  exact zero_ne_one h2

end RingedSite

/-! ### The five big sites of Stacks 0GZV -/

/-- **The big Zariski site of a scheme is locally ringed.** -/
public theorem bigZariskiOverRingedSite_isLocallyRinged (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    RingedSite.IsLocallyRinged (bigZariskiOverRingedSite B S hS) :=
  RingedSite.isLocallyRinged_globalFunctions _ (BigZariskiOver.toScheme B S hS)
    (bigZariskiOverRingedSite B S hS).O.property (bigZariskiOver_openCoverData B S hS)

/-- **The big étale site of a scheme is locally ringed.** -/
public theorem bigEtaleOverRingedSite_isLocallyRinged (B : BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    RingedSite.IsLocallyRinged (bigEtaleOverRingedSite B S hS) :=
  RingedSite.isLocallyRinged_globalFunctions _ (BigEtaleOver.toScheme B S hS)
    (bigEtaleOverRingedSite B S hS).O.property (bigEtaleOver_openCoverData B S hS)

/-- **The big smooth site of a scheme is locally ringed.** -/
public theorem bigSmoothOverRingedSite_isLocallyRinged (B : BigSmoothSite.{u})
    (S : Scheme.{u}) (hS : S.size < B.cutoff) :
    RingedSite.IsLocallyRinged (bigSmoothOverRingedSite B S hS) :=
  RingedSite.isLocallyRinged_globalFunctions _ (BigSmoothOver.toScheme B S hS)
    (bigSmoothOverRingedSite B S hS).O.property (bigSmoothOver_openCoverData B S hS)

/-- **The big syntomic site of a scheme is locally ringed.** -/
public theorem bigSyntomicOverRingedSite_isLocallyRinged (B : BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    RingedSite.IsLocallyRinged (bigSyntomicOverRingedSite B S hS) :=
  RingedSite.isLocallyRinged_globalFunctions _ (BigSyntomicOver.toScheme B S hS)
    (bigSyntomicOverRingedSite B S hS).O.property (bigSyntomicOver_openCoverData B S hS)

/-- **The big fppf site of a scheme is locally ringed.** -/
public theorem bigFppfOverRingedSite_isLocallyRinged (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    RingedSite.IsLocallyRinged (bigFppfOverRingedSite B S hS) :=
  RingedSite.isLocallyRinged_globalFunctions _ (BigFppfOver.toScheme B S hS)
    (bigFppfOverRingedSite B S hS).O.property (bigFppfOver_openCoverData B S hS)

end AlgebraicGeometry

end
