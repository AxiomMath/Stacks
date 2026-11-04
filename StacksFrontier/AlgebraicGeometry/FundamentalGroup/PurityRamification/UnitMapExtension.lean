module

public import StacksFrontier.AlgebraicGeometry.Divisors.HartogsExtension.Basic
public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayDualizingModule
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamification.GorensteinStep
public import StacksFrontier.RingTheory.CohenMacaulay.Module

/-!
# Extending the map `𝒪_X ⟶ ω_{X/Y}` across the closure of a point

The proof of [Stacks, Tag 0EA3] uses a map `𝒪_X ⟶ ω_{X/Y} = H⁰(f^!𝒪_Y)` which is an
isomorphism over `X ∖ closure {x}`, and takes it from [Stacks, Tag 0EA0] with `r = 0`.  The
construction in that tag has two halves: over the open `U` where `f` is a local complete
intersection the map is the one of [Stacks, Tag 0E9Z] (for `r = 0` an identification
`𝒪_U ≅ ω_{U/Y}` over the étale locus), and that map *extends* from `U` to `X` because
`ω_{X/Y}` is `(S₂)` and `U` contains every point of codimension at most one, so
`j_*ω_{U/Y} = ω_{X/Y}` by [Stacks, Tag 0E9I].

This file proves the extension half, in the following general form: on a locally Noetherian
scheme, restriction to an open `V` is *full* on morphisms whose target is a coherent module
whose stalks have depth at least two outside `V`.  Tag 0E9I is exactly the statement that such
a module is the pushforward of its restriction, and that identification turns a morphism defined
over `V` into a morphism defined over `X`.  Consequently the map of [Stacks, Tag 0EA3] need not
be assumed to exist: an isomorphism `𝒪_V ≅ ω|_V` over an open `V` containing the complement of
`closure {x}` is enough.

The depth-two bound that the extension needs is *not* taken as a hypothesis: the source reads it
off Serre's condition `(S₂)` of [Stacks, Tag 0E9V], and the same bound is already available from
the Cohen–Macaulayness of a dualizing module, [Stacks, Tag 0AWT], which this library has.  So
the only content used below and not proved is the identification `𝒪_V ≅ ω|_V` over the étale
locus, which is the `r = 0` case of [Stacks, Tag 0E9Z]; that tag is registered elsewhere in the
project, so no `@[stacks ...]` attribute appears below.

## Main results

* `Stacks.PurityRamification.exists_hom_restrict_eq_of_two_le_depth` — restriction to an open
  `V` is full on morphisms into a coherent module of depth at least two outside `V`.  This is
  the extension step of [Stacks, Tag 0EA0], read through [Stacks, Tag 0E9I].
* `Stacks.PurityRamification.two_le_depth_stalk_of_isDualizingComplex_single` — a module whose
  degree-zero complex is a dualizing complex has depth at least two at a point where the
  support of its stalk has dimension at least two.  This is the Cohen–Macaulayness clause of
  [Stacks, Tag 0AWT] read as Serre's condition, and it is what the proof of
  [Stacks, Tag 0EA3] uses [Stacks, Tag 0E9V] for.
* `Stacks.PurityRamification.isGorenstein_of_restrictIso_unit_of_notSpecializes_mem` — the
  Gorenstein step of [Stacks, Tag 0EA3] with no map as data: a coherent module `ω` on a
  locally Noetherian normal scheme which is a dualizing complex in degree zero, whose support
  has dimension at least two along `closure {x}`, and which restricts to `𝒪_V` on an open `V`
  containing every point outside `closure {x}`, forces `X` to be Gorenstein.
* `Stacks.PurityRamification.isGorensteinLocalRing_stalk_of_restrictIso_unit` — the same
  conclusion read at `x`, with hypothesis (2) of [Stacks, Tag 0EA3] in the source's shape: the
  local ring `𝒪_{X, x}` is normal (here: `X` is normal) of dimension at least two.

## Implementation notes

The extension is built from the unit of `AlgebraicGeometry.Scheme.Modules.restrictAdjunction`
rather than from the unit of `AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction`,
at which [Stacks, Tag 0E9I] is stated: the two units differ by the comparison
`AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` of the two left adjoints, which is
an isomorphism, so one is an isomorphism exactly when the other is.  Working with the
restriction adjunction is what makes the extension a one-line computation with
`CategoryTheory.Adjunction.homEquiv`: the transpose of `ψ` followed by the inverse of the unit
at the target is a morphism whose restriction is `ψ`, because the restriction of a transpose is
the transpose back.

The depth hypotheses are written in the shape the consumers use — pointwise on stalks, with the
module structure the one typeclass inference finds on
`TopCat.Presheaf.stalk (C := Ab) G.val.presheaf y` — so that no translation is needed at the
call sites in `GorensteinStep`.

## References

* [Stacks Project, Tag 0EA3](https://stacks.math.columbia.edu/tag/0EA3)
* [Stacks Project, Tag 0EA0](https://stacks.math.columbia.edu/tag/0EA0)
* [Stacks Project, Tag 0E9Z](https://stacks.math.columbia.edu/tag/0E9Z)
* [Stacks Project, Tag 0E9V](https://stacks.math.columbia.edu/tag/0E9V)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 0AWT](https://stacks.math.columbia.edu/tag/0AWT)
* [Stacks Project, Tag 0343](https://stacks.math.columbia.edu/tag/0343)
* [Stacks Project, Tag 02IZ](https://stacks.math.columbia.edu/tag/02IZ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

attribute [local instance] HasDerivedCategory.standard

universe u w

namespace Stacks.PurityRamification

variable {X : Scheme.{u}}

/-! ### Restriction is full on maps into a module of depth at least two -/

/-- **A morphism defined over an open extends, if its target has depth at least two outside that
open.**

Let `G` be a coherent module on a locally Noetherian scheme `X` whose stalk at every point
outside an open `V` has depth at least two.  Then every morphism `ψ : F|_V ⟶ G|_V` is the
restriction of a morphism `F ⟶ G`.

This is the extension step in the construction of [Stacks, Tag 0EA0]: there `G = ω_{X/Y}`, the
depth hypothesis comes from `ω_{X/Y}` being `(S₂)` together with `V` containing every point of
codimension at most one, and `ψ` is the identification of [Stacks, Tag 0E9Z] over the locus
where the morphism is a local complete intersection.

The proof is [Stacks, Tag 0E9I]: the depth hypothesis makes `G` the pushforward of `G|_V`, so
`ψ` may be transposed to a morphism `F ⟶ G|_V`-pushed-forward and then corrected by the inverse
of that identification; the restriction of the result is the transpose back of the transpose of
`ψ`, that is `ψ`. -/
theorem exists_hom_restrict_eq_of_two_le_depth [IsLocallyNoetherian X] {F G : X.Modules}
    [G.IsCoherent] (V : X.Opens)
    (hdepth : ∀ y : X, y ∉ (V : Set X) → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf y))
    (ψ : (Scheme.Modules.restrictFunctor V.ι).obj F ⟶
      (Scheme.Modules.restrictFunctor V.ι).obj G) :
    ∃ φ : F ⟶ G, (Scheme.Modules.restrictFunctor V.ι).map φ = ψ := by
  have hpull := AlgebraicGeometry.isIso_unit_restrict_pushforward_of_depth_ge_two X G V hdepth
  have hcomp : (Scheme.Modules.restrictAdjunction V.ι).unit.app G ≫
      (Scheme.Modules.pushforward V.ι).map
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app G) =
      (Scheme.Modules.pullbackPushforwardAdjunction V.ι).unit.app G :=
    Adjunction.unit_leftAdjointUniq_hom_app _ _ G
  have h₁ : IsIso ((Scheme.Modules.restrictAdjunction V.ι).unit.app G ≫
      (Scheme.Modules.pushforward V.ι).map
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app G)) := by
    rw [hcomp]; exact hpull
  have h₂ : IsIso ((Scheme.Modules.pushforward V.ι).map
      ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app G)) := inferInstance
  have h₃ : IsIso ((Scheme.Modules.restrictAdjunction V.ι).unit.app G) :=
    IsIso.of_isIso_comp_right ((Scheme.Modules.restrictAdjunction V.ι).unit.app G)
      ((Scheme.Modules.pushforward V.ι).map
        ((Scheme.Modules.restrictFunctorIsoPullback V.ι).hom.app G))
  refine ⟨(Scheme.Modules.restrictAdjunction V.ι).homEquiv F _ ψ ≫
    inv ((Scheme.Modules.restrictAdjunction V.ι).unit.app G), ?_⟩
  rw [Functor.map_comp, Functor.map_inv,
    IsIso.inv_eq_of_hom_inv_id
      ((Scheme.Modules.restrictAdjunction V.ι).left_triangle_components G),
    ← Adjunction.homEquiv_counit, Equiv.symm_apply_apply]

/-! ### The depth of a dualizing module, from Tag 0AWT -/

section SchemeGorenstein

variable [IsLocallyNoetherian X] [HasDerivedCategory.{w} X.Modules]

/-- **A dualizing module has depth at least two wherever its support has dimension at least
two.**

If `ω[0]` is a dualizing complex on a locally Noetherian scheme then `ω` is a Cohen–Macaulay
`𝒪_X`-module in the sense of [Stacks, Tag 0343] — this is
`Stacks.Duality.sheafIsCohenMacaulay_homology_of_concentrated`, the Cohen–Macaulayness clause of
[Stacks, Tag 0AWT] — so Serre's condition `(S₂)` holds for it: at every point the depth of the
stalk is at least the minimum of two and the dimension of the support of the stalk.

This is what the proof of [Stacks, Tag 0EA3] needs the `(S₂)` property of
[Stacks, Tag 0E9V] for, and it supersedes it there: `ω_{X/Y} = H⁰(f^!𝒪_Y)` is the cohomology of
a dualizing complex concentrated in degree zero, so the `(S₂)` property is already available
from the dualizing complex itself. -/
theorem two_le_depth_stalk_of_isDualizingComplex_single {G : X.Modules} [G.IsCoherent]
    (hdual : Stacks.Duality.IsDualizingComplex
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)) (y : X)
    (hsupp : (2 : WithBot ℕ∞) ≤ Module.supportDim (X.presheaf.stalk y) (G.presheaf.stalk y)) :
    (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) (G.presheaf.stalk y) := by
  have hn : ∀ i : ℤ, i ≠ 0 → Limits.IsZero ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)) := by
    intro i hi
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · exact DerivedCategory.isZero_of_isGE _ 0 i hlt
    · exact DerivedCategory.isZero_of_isLE _ 0 i hgt
  have hcm := Stacks.Duality.sheafIsCohenMacaulay_homology_of_concentrated _ hdual 0 hn
  have hcoh : _root_.SheafOfModules.IsCoherent ((DerivedCategory.homologyFunctor X.Modules 0).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)) :=
    Stacks.Duality.isCoherent_homology_of_isDualizingComplex hdual 0
  have hfin := AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent
    ((DerivedCategory.homologyFunctor X.Modules 0).obj
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)) y
  have hfinG := AlgebraicGeometry.Scheme.Modules.finite_stalk_of_isCoherent G y
  have elin : (((DerivedCategory.homologyFunctor X.Modules 0).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj G)).presheaf.stalk y)
      ≃ₗ[X.presheaf.stalk y] (G.presheaf.stalk y) :=
    AlgebraicGeometry.schemeStalkLinearEquiv
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app G) y
  have hpt :=
    Stacks.AlgebraicGeometry.ReflexiveModules.min_supportDim_le_depth_of_sheafHasPropertySk
      ((DerivedCategory.homologyFunctor X.Modules 0).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj G)) 2 (hcm 2) y
  rw [_root_.supportDim_eq_of_linearEquiv elin,
    Module.depth_eq_depth_of_linearEquiv _ elin] at hpt
  exact WithBot.coe_le_coe.mp (le_trans (le_min (by norm_num) hsupp) hpt)

/-! ### The Gorenstein step of Tag 0EA3 with no map as data -/

/-- **The Gorenstein step of [Stacks, Tag 0EA3], with the map of [Stacks, Tag 0EA0] replaced by
its restriction.**

Let `X` be a locally Noetherian normal scheme, `x ∈ X` a point of codimension at least two and
`ω` a coherent `𝒪_X`-module whose degree-zero complex is a dualizing complex on `X`.  Suppose
the support of `ω` has dimension at least two at every point of `closure {x}`, and that on some
open `V` containing every point outside `closure {x}` there is an isomorphism `𝒪_V ≅ ω|_V`.
Then `X` is Gorenstein.

In [Stacks, Tag 0EA3] `ω = ω_{X/Y} = H⁰(f^!𝒪_Y)`; the isomorphism over `V` is the `r = 0` case
of [Stacks, Tag 0E9Z] on the locus where `f` is étale, and the dualizing property is
[Stacks, Tag 0AA3] after the Cohen–Macaulay shrinking of [Stacks, Tag 0AWT].  The depth bound
that the source takes from Serre's condition `(S₂)` of [Stacks, Tag 0E9V] is supplied here by
`Stacks.PurityRamification.two_le_depth_stalk_of_isDualizingComplex_single`, so only the
dimension of the support appears as a hypothesis.

Unlike `Stacks.PurityRamification.isGorenstein_of_isIso_restrict_of_notSpecializes_mem` this
takes no map `𝒪_X ⟶ ω` as data: the map is produced from the isomorphism over `V` by
`Stacks.PurityRamification.exists_hom_restrict_eq_of_two_le_depth`, which is the extension step
of [Stacks, Tag 0EA0]. -/
theorem isGorenstein_of_restrictIso_unit_of_notSpecializes_mem [IsNormal X] {x : X}
    (hx : (2 : ℕ∞) ≤ Order.coheight x) {G : X.Modules} [G.IsQuasicoherent] [G.IsCoherent]
    (V : X.Opens) (hV : ∀ y : X, ¬ x ⤳ y → y ∈ V)
    (e : (Scheme.Modules.restrictFunctor V.ι).obj (Stacks.Ample.unitModule X) ≅
      (Scheme.Modules.restrictFunctor V.ι).obj G)
    (hsupp : ∀ y : X, x ⤳ y →
      (2 : WithBot ℕ∞) ≤ Module.supportDim (X.presheaf.stalk y) (G.presheaf.stalk y))
    (hdual : Stacks.Duality.IsDualizingComplex
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)) :
    AlgebraicGeometry.IsGorenstein X := by
  have hdepth : ∀ y : X, x ⤳ y → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk y)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y))
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf y) := fun y hy =>
    two_le_depth_stalk_of_isDualizingComplex_single hdual y (hsupp y hy)
  obtain ⟨φ, hφ⟩ :=
    exists_hom_restrict_eq_of_two_le_depth (F := Stacks.Ample.unitModule X) V
      (fun y hy => hdepth y (by by_contra h; exact hy (hV y h))) e.hom
  have hiso : IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ) := by
    rw [hφ]; infer_instance
  exact isGorenstein_of_isIso_restrict_of_notSpecializes_mem hx φ V hV
    (fun y hy => le_trans (by norm_num) (hdepth y hy)) hdual

/-- **The local ring at `x` is Gorenstein**, which is the conclusion the proof of
[Stacks, Tag 0EA3] draws at this point of its argument, under hypothesis (2) of that tag in the
source's shape: `𝒪_{X, x}` is normal — here `X` is normal — of dimension at least two.

The dimension is read as the Krull dimension of the local ring, which is the codimension of `x`
on the space by [Stacks, Tag 02IZ]. -/
theorem isGorensteinLocalRing_stalk_of_restrictIso_unit [IsNormal X] {x : X}
    (hdim : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
    {G : X.Modules} [G.IsQuasicoherent] [G.IsCoherent]
    (V : X.Opens) (hV : ∀ y : X, ¬ x ⤳ y → y ∈ V)
    (e : (Scheme.Modules.restrictFunctor V.ι).obj (Stacks.Ample.unitModule X) ≅
      (Scheme.Modules.restrictFunctor V.ι).obj G)
    (hsupp : ∀ y : X, x ⤳ y →
      (2 : WithBot ℕ∞) ≤ Module.supportDim (X.presheaf.stalk y) (G.presheaf.stalk y))
    (hdual : Stacks.Duality.IsDualizingComplex
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)) :
    Dualizing.IsGorensteinLocalRing (X.presheaf.stalk x) :=
  have hx : (2 : ℕ∞) ≤ Order.coheight x := by
    rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at hdim
    exact WithBot.coe_le_coe.mp hdim
  AlgebraicGeometry.IsGorenstein.isGorensteinLocalRing
    (self := isGorenstein_of_restrictIso_unit_of_notSpecializes_mem hx V hV e hsupp hdual) x

end SchemeGorenstein

end Stacks.PurityRamification

end
