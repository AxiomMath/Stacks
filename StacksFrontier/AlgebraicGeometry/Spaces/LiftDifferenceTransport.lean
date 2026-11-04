module

public import StacksFrontier.AlgebraicGeometry.Spaces.LiftDifferenceDescent

/-!
# Transporting the difference of two lifts along a map of ambient rings

Let `q : A ⟶ O` be a locally surjective morphism of sheaves of rings, and let `M ⊆ 𝒜` and
`M' ⊆ 𝒜'` be two square-zero ideals of values (`Stacks.Sites.SquareZeroValues`) for two
`O`-modules `M` and `M'`.  A morphism of sheaves of rings `τ : 𝒜 ⟶ 𝒜'` carrying `M` into `M'`
induces an `O`-linear map `κ : M ⟶ M'` with `ι' ∘ κ = τ ∘ ι`, as soon as the `O`-actions on both
modules are the `A`-actions through a map `f : A ⟶ 𝒜` and through `f ≫ τ`.

If two pairs of lifts `(f, g)` into `𝒜` and `(f ≫ τ, g ≫ τ)` into `𝒜'` are given, the difference
of the second pair is `κ` applied to the difference of the first, and so is its descent to `O`.
For algebraic spaces this says that the linear map out of the pulled back differentials attached
to the second pair is the one attached to the first, followed by `κ`.  This is the form in which
the difference of two morphisms of thickenings, [Stacks Project, Tag 0618], is compatible with
restriction along a morphism of thickenings.

## Main definitions

* `Stacks.Sites.SquareZeroValues.transport`: the `O`-linear map `κ : M ⟶ M'` induced by `τ`.

## Main results

* `Stacks.Sites.SquareZeroValues.ι_transport`: its defining equation `ι' ∘ κ = τ ∘ ι`.
* `Stacks.Sites.LiftDifferenceData.diff_eq_transport` and
  `Stacks.Sites.LiftDifferenceData.descend_eq_transport`: the difference of the transported pair,
  and its descent, are `κ` of those of the given pair.
* `AlgebraicGeometry.Space.homEquiv_liftDifferenceDifferentialsHom_eq_comp`: the transpose of the
  linear map attached to the transported pair is that of the given pair followed by `κ`.

## References

* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v₁ u₁

namespace Stacks.Sites

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {A O : Sheaf J RingCat.{u}} {q : A ⟶ O} {M M' : SheafOfModules.{u} O}

namespace SquareZeroValues

variable (E : SquareZeroValues M) (E' : SquareZeroValues M') (τ : E.ambient ⟶ E'.ambient)
  (hτ : ∀ {V : Cᵒᵖ} (m : M.val.obj V), ∃ m' : M'.val.obj V, E'.ι m' = τ.hom.app V (E.ι m))

/-- The map on sections induced by `τ`: the unique section of `M'` whose image in `𝒜'` is the
image under `τ` of the image of the given section in `𝒜`. -/
def transportApp {V : Cᵒᵖ} (m : M.val.obj V) : M'.val.obj V := (hτ m).choose

/-- The image in `𝒜'` of the induced section is the image under `τ` of the image in `𝒜` of the
given section. -/
theorem ι_transportApp {V : Cᵒᵖ} (m : M.val.obj V) :
    E'.ι (transportApp E E' τ hτ m) = τ.hom.app V (E.ι m) :=
  (hτ m).choose_spec

/-- The map on sections induced by `τ` is additive. -/
theorem transportApp_add {V : Cᵒᵖ} (m n : M.val.obj V) :
    transportApp E E' τ hτ (m + n) = transportApp E E' τ hτ m + transportApp E E' τ hτ n :=
  E'.ι_injective (by rw [ι_transportApp, map_add, map_add, map_add, ι_transportApp,
    ι_transportApp])

/-- The map on sections induced by `τ` commutes with restriction along `h : V ⟶ W`. -/
theorem transportApp_map {V W : Cᵒᵖ} (h : V ⟶ W) (m : M.val.obj V) :
    transportApp E E' τ hτ (V := W) (M.val.map h m) =
      (M'.val.map h (transportApp E E' τ hτ m) : M'.val.obj W) :=
  E'.ι_injective ((ι_transportApp E E' τ hτ (V := W) _).trans
    ((congrArg (τ.hom.app W) (E.ι_map h m)).trans
      ((ConcreteCategory.congr_hom (τ.hom.naturality h) (E.ι m)).trans
        ((congrArg (E'.ambient.obj.map h) (ι_transportApp E E' τ hτ m)).symm.trans
          (E'.ι_map h _).symm))))

/-- Restricting `r • m` along `g` is acting by any section `x` of `A` with `q x = g^* r`. -/
private theorem map_smul_of_app_eq {N : SheafOfModules.{u} O} {V : Cᵒᵖ} {Y : C} {g : Y ⟶ V.unop}
    {r : O.obj.obj V} {x : A.obj.obj (Opposite.op Y)}
    (hx : q.hom.app (Opposite.op Y) x = O.obj.map g.op r) (m : N.val.obj V) :
    (N.val.map g.op (r • m) : N.val.obj (Opposite.op Y)) =
      q.hom.app (Opposite.op Y) x • (N.val.map g.op m : N.val.obj (Opposite.op Y)) :=
  (N.val.map_smul g.op r m).trans (congrArg (· • _) hx.symm)

variable [hq : Sheaf.IsLocallySurjective q] (f : A ⟶ E.ambient)
  (hf : ∀ {V : Cᵒᵖ} (x : A.obj.obj V) (m : M.val.obj V),
    E.ι (q.hom.app V x • m) = f.hom.app V x * E.ι m)
  (hf' : ∀ {V : Cᵒᵖ} (x : A.obj.obj V) (m : M'.val.obj V),
    E'.ι (q.hom.app V x • m) = (f ≫ τ).hom.app V x * E'.ι m)

omit hq in
include hf hf' in
/-- The map on sections induced by `τ` commutes with the action of a section of `O` coming from
`A`: both actions are multiplication by the image of that section. -/
theorem transportApp_smul_app {V : Cᵒᵖ} (x : A.obj.obj V) (m : M.val.obj V) :
    transportApp E E' τ hτ (q.hom.app V x • m) = q.hom.app V x • transportApp E E' τ hτ m :=
  E'.ι_injective ((ι_transportApp E E' τ hτ _).trans
    ((congrArg (τ.hom.app V) (hf x m)).trans ((map_mul (τ.hom.app V).hom _ _).trans
      ((congrArg (fun t => (f ≫ τ).hom.app V x * t) (ι_transportApp E E' τ hτ m)).symm.trans
        (hf' x _).symm))))

include hf hf' in
/-- The map on sections induced by `τ` is `O`-linear.  On a section `q(x)` of `O` coming from `A`
this is `Stacks.Sites.SquareZeroValues.transportApp_smul_app`, and every section of `O` is
locally of that form. -/
theorem transportApp_smul {V : Cᵒᵖ} (r : O.obj.obj V) (m : M.val.obj V) :
    transportApp E E' τ hτ (r • m) = r • transportApp E E' τ hτ m := by
  refine M'.isSheaf.isSeparated V.unop (Presheaf.imageSieve q.hom r)
    (Presheaf.imageSieve_mem J q.hom r) _ _ ?_
  intro Y g hg
  obtain ⟨x, hx⟩ := hg
  exact (transportApp_map E E' τ hτ g.op (r • m)).symm.trans ((congrArg
    (transportApp E E' τ hτ) (map_smul_of_app_eq hx m)).trans
    ((transportApp_smul_app E E' τ hτ f hf hf' x _).trans
    ((congrArg (q.hom.app (Opposite.op Y) x • ·) (transportApp_map E E' τ hτ g.op m)).trans
      (map_smul_of_app_eq hx _).symm)))

/-- **The `O`-linear map `M ⟶ M'` induced by a map of ambient sheaves of rings carrying the
first ideal of values into the second.** -/
def transport : M ⟶ M' :=
  ⟨PresheafOfModules.homMk
    { app := fun V => AddCommGrpCat.ofHom
        (AddMonoidHom.mk' (transportApp E E' τ hτ) (transportApp_add E E' τ hτ))
      naturality := fun _ _ h => by
        ext m
        exact transportApp_map E E' τ hτ h m }
    (fun _ r m => transportApp_smul E E' τ hτ f hf hf' r m)⟩

/-- On sections over `V`, the induced map `κ` is `Stacks.Sites.SquareZeroValues.transportApp`. -/
theorem transport_val_app {V : Cᵒᵖ} (m : M.val.obj V) :
    (transport E E' τ hτ f hf hf').val.app V m = transportApp E E' τ hτ m := rfl

/-- **The defining equation of the induced map: `ι' ∘ κ = τ ∘ ι`.** -/
theorem ι_transport {V : Cᵒᵖ} (m : M.val.obj V) :
    E'.ι ((transport E E' τ hτ f hf hf').val.app V m) = τ.hom.app V (E.ι m) :=
  ι_transportApp E E' τ hτ m

end SquareZeroValues

namespace LiftDifferenceData

variable {E : SquareZeroValues M} {E' : SquareZeroValues M'} (τ : E.ambient ⟶ E'.ambient)
  (L : LiftDifferenceData q E) (L' : LiftDifferenceData q E') (κ : M ⟶ M')
  (hκ : ∀ {V : Cᵒᵖ} (m : M.val.obj V), E'.ι (κ.val.app V m) = τ.hom.app V (E.ι m))
  (hf : L'.f = L.f ≫ τ) (hg : L'.g = L.g ≫ τ)

include hκ hf hg

/-- **The difference of the transported pair is the transport of the difference.** -/
theorem diff_eq_transport {V : Cᵒᵖ} (x : A.obj.obj V) : L'.diff x = κ.val.app V (L.diff x) :=
  E'.ι_injective (by rw [L'.ι_diff, hκ, L.ι_diff, map_sub, hf, hg]; rfl)

/-- **The descent of the difference of the transported pair is the transport of the descent of
the difference.**  Both sides restrict, on the covering sieve over which a section of `O` lifts
to `A`, to the transport of the difference at the lift. -/
theorem descend_eq_transport [Sheaf.IsLocallySurjective q] [HasSheafify J AddCommGrpCat.{u}]
    {V : Cᵒᵖ} (t : O.obj.obj V) :
    L'.toQuotientDerivation.descend t = κ.val.app V (L.toQuotientDerivation.descend t) := by
  refine M'.isSheaf.isSeparated V.unop (Presheaf.imageSieve q.hom t)
    (Presheaf.imageSieve_mem J q.hom t) _ _ ?_
  intro Y g hg
  obtain ⟨x, hx⟩ := hg
  show M'.val.map g.op _ = M'.val.map g.op _
  rw [← QuotientDerivation.descend_map, ← hx, QuotientDerivation.descend_app,
    ← PresheafOfModules.naturality_apply, ← QuotientDerivation.descend_map, ← hx,
    QuotientDerivation.descend_app, toQuotientDerivation_d, toQuotientDerivation_d]
  exact diff_eq_transport τ L L' κ hκ hf hg x

end LiftDifferenceData

end Stacks.Sites

namespace AlgebraicGeometry.Space

open Stacks.Sites

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {Y T : AlgebraicSpaces B S hS} (b : Y ⟶ T)
  {A : Sheaf (SmallEtale.topology B S hS Y.1) RingCat.{u}}
  {q : A ⟶ structureRingSheaf B S hS Y} [hq : Sheaf.IsLocallySurjective q]
  {X X₂ : AlgebraicSpaces B S hS} (a : X ⟶ Y) (a₂ : X₂ ⟶ Y)
  (C : Modules B S hS X.1 X.2) (C₂ : Modules B S hS X₂.1 X₂.2)
  {E : SquareZeroValues ((modulePushforward B S hS a).obj C)}
  {E₂ : SquareZeroValues ((modulePushforward B S hS a₂).obj C₂)}
  (τ : E.ambient ⟶ E₂.ambient) (L : LiftDifferenceData q E) (L₂ : LiftDifferenceData q E₂)
  (hz : ∀ (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (s : (inverseImageStructureSheaf B S hS b).obj.obj V),
    L.toQuotientDerivation.descend ((structureSharpInverseImage B S hS b).hom.app V s) = 0)
  (hz₂ : ∀ (V : (SmallEtale B S hS Y.1)ᵒᵖ)
    (s : (inverseImageStructureSheaf B S hS b).obj.obj V),
    L₂.toQuotientDerivation.descend ((structureSharpInverseImage B S hS b).hom.app V s) = 0)
  (κ : (modulePushforward B S hS a).obj C ⟶ (modulePushforward B S hS a₂).obj C₂)
  (hκ : ∀ {V : (SmallEtale B S hS Y.1)ᵒᵖ} (m : ((modulePushforward B S hS a).obj C).val.obj V),
    E₂.ι (κ.val.app V m) = τ.hom.app V (E.ι m))
  (hf : L₂.f = L.f ≫ τ) (hg : L₂.g = L.g ≫ τ)

include hq hκ hf hg in
/-- **The linear map attached to a transported pair of lifts, [Stacks Project, Tag 0618] with
Equation (0619), is the one attached to the given pair followed by the transport.**  Read through
the adjunctions `a^* ⊣ a_*` and `a₂^* ⊣ a₂_*`: the transpose
`Ω_{Y/T} ⟶ (a₂)_*C₂` of the map of the pair `(f ≫ τ, g ≫ τ)` is the transpose
`Ω_{Y/T} ⟶ a_*C` of the map of the pair `(f, g)`, followed by `κ : a_*C ⟶ (a₂)_*C₂`. -/
theorem homEquiv_liftDifferenceDifferentialsHom_eq_comp :
    (modulePullbackAdjunction B S hS a₂).homEquiv _ _
        (liftDifferenceDifferentialsHom B S hS b a₂ C₂ L₂ hz₂) =
      (modulePullbackAdjunction B S hS a).homEquiv _ _
          (liftDifferenceDifferentialsHom B S hS b a C L hz) ≫ κ := by
  have key := eq_descendedDifferentialsHom_of_spec B S hS b a₂ C₂ L₂.toQuotientDerivation hz₂
    (((modulePullbackAdjunction B S hS a₂).homEquiv _ _).symm
      ((modulePullbackAdjunction B S hS a).homEquiv _ _
          (liftDifferenceDifferentialsHom B S hS b a C L hz) ≫ κ)) (fun V t => by
      rw [Equiv.apply_symm_apply]
      exact (congrArg (κ.val.app V)
          (descendedDifferentialsHom_spec B S hS b a C L.toQuotientDerivation hz t)).trans
        (LiftDifferenceData.descend_eq_transport (q := q) τ L L₂ κ hκ hf hg t).symm)
  exact (congrArg ((modulePullbackAdjunction B S hS a₂).homEquiv _ _) key.symm).trans
    (Equiv.apply_symm_apply _ _)

end AlgebraicGeometry.Space

end
