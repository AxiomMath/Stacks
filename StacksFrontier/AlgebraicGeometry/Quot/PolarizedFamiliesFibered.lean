module

public import StacksCore.CategoryTheory.FiberedInGroupoids
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamilies
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.RingedSpace

/-!
# Polarized families form a category fibred in groupoids

The projection `AlgebraicGeometry.polarizedProjection` taking a polarized family to its base scheme
is a category fibred in groupoids over the big fppf site, provided relative ampleness of an
invertible sheaf of modules is stable under base change. Fill-ins exist and are unique without
this hypothesis; lifts are given by base change of polarized families.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.RelativelyAmpleBaseChange`: the assertion that relative
  ampleness of an invertible sheaf of modules is stable under base change.
* `AlgebraicGeometry.PolarizedFamily.fillInTotalMap` and
  `AlgebraicGeometry.PolarizedFamily.fillIn`: the fill-in of a morphism of polarized families
  through another one over a given morphism of base schemes.
* `AlgebraicGeometry.PolarizedFamily.baseChange` and
  `AlgebraicGeometry.PolarizedFamily.baseChangeHom`: the base change of a polarized family along
  a morphism of base schemes, and the morphism of polarized families it carries.

## Main results

* `AlgebraicGeometry.PolarizedFamily.Hom.eq_of_comp_eq`: a morphism of polarized families is
  determined by its base map together with its composite with a fixed morphism.
* `AlgebraicGeometry.polarizedProjection_uniqueLift`: fill-ins along the projection exist and are
  unique.
* `AlgebraicGeometry.polarizedProjection_existsLift`: given
  `AlgebraicGeometry.Scheme.Modules.RelativelyAmpleBaseChange`, morphisms of base schemes lift
  along the projection.
* `AlgebraicGeometry.polarizedProjection_isFiberedInGroupoids`: given
  `AlgebraicGeometry.Scheme.Modules.RelativelyAmpleBaseChange`, the projection is fibred in
  groupoids.

## References

* [Stacks Project, Tag 0D1M](https://stacks.math.columbia.edu/tag/0D1M)
* [Stacks Project, Tag 003S](https://stacks.math.columbia.edu/tag/003S)
* [Stacks Project, Tag 0D1E](https://stacks.math.columbia.edu/tag/0D1E)
* [Stacks Project, Tag 0D3Y](https://stacks.math.columbia.edu/tag/0D3Y)
* [Stacks Project, Tag 0D43](https://stacks.math.columbia.edu/tag/0D43)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 01VJ](https://stacks.math.columbia.edu/tag/01VJ)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Base change of relative ampleness -/

namespace Scheme.Modules

/-- Relative ampleness of an invertible sheaf of modules is stable under base change: if `L` is
ample relative to `f : X ⟶ S` and `f' : X' ⟶ S'` is the base change of `f` along `S' ⟶ S`, then
the pullback of `L` to `X'` is ample relative to `f'`. -/
def RelativelyAmpleBaseChange : Prop :=
  ∀ {X S X' S' : Scheme.{u}} {p : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {g : S' ⟶ S},
    IsPullback p f' f g → ∀ (L : X.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
      [AlgebraicGeometry.SheafOfModules.IsInvertible X'.presheaf X'.ringCatSheaf.2
        ((Scheme.Modules.pullback p).obj L)],
      Stacks.RelativeAmple.IsRelativelyAmple f L →
        Stacks.RelativeAmple.IsRelativelyAmple f' ((Scheme.Modules.pullback p).obj L)

end Scheme.Modules

namespace PolarizedFamily

variable {B : BigFppfSite.{u}}

/-! ### The fill-in -/

/-- Equal morphisms of polarized families have the same comparison of polarizations. -/
theorem heq_lineBundleIso {X Y : PolarizedFamily B} {f g : X ⟶ Y} (h : f = g) :
    Hom.lineBundleIso f ≍ Hom.lineBundleIso g := by
  cases h
  rfl

/-- The comparison of polarizations of a composite of morphisms of polarized families. -/
private theorem lineBundleIso_comp {x y z : PolarizedFamily B} (φ : y ⟶ x) (ψ : z ⟶ y) :
    Hom.lineBundleIso (ψ ≫ φ) =
      (Scheme.Modules.pullbackComp ψ.totalMap φ.totalMap).symm.app x.lineBundle ≪≫
        (Scheme.Modules.pullback ψ.totalMap).mapIso φ.lineBundleIso ≪≫ ψ.lineBundleIso := rfl

/-- A morphism of polarized families is determined by its base map together with its composite
with a fixed morphism `φ`. -/
theorem Hom.eq_of_comp_eq {x y z : PolarizedFamily B} (φ : y ⟶ x) {η η' : z ⟶ y}
    (hbase : η.baseMap = η'.baseMap) (h : η ≫ φ = η' ≫ φ) : η = η' := by
  obtain ⟨b, t, c, i⟩ := η
  obtain ⟨b', t', c', i'⟩ := η'
  obtain rfl : b = b' := hbase
  obtain rfl : t = t' :=
    φ.cartesian.hom_ext (congrArg Hom.totalMap h) (c.w.trans c'.w.symm)
  obtain rfl : c = c' := rfl
  have hheq := heq_lineBundleIso h
  have hiso := eq_of_heq hheq
  have key := congrArg Iso.hom
    ((lineBundleIso_comp φ ⟨b, t, c, i⟩).symm.trans
      (hiso.trans (lineBundleIso_comp φ ⟨b, t, c, i'⟩)))
  simp only [Iso.trans_hom] at key
  exact Hom.ext rfl rfl (heq_of_eq (Iso.ext ((cancel_epi _).1 ((cancel_epi _).1 key))))

/-- The map of total spaces of the fill-in: the morphism into the total space of `y` induced by
the cartesian square of `φ` from the map of total spaces of `ψ` and the structure morphism of `z`
read over the base map `f`. -/
def fillInTotalMap {x y z : PolarizedFamily B} (φ : y ⟶ x) (ψ : z ⟶ x) (f : z.base ⟶ y.base)
    (hcomm : f ≫ φ.baseMap = ψ.baseMap) : z.total ⟶ y.total :=
  φ.cartesian.lift ψ.totalMap (z.toBase ≫ B.inclusion.map f)
    (ψ.cartesian.w.trans
      ((congrArg (fun k => z.toBase ≫ B.inclusion.map k) hcomm).symm.trans
        ((congrArg (fun k => z.toBase ≫ k) (B.inclusion.map_comp f φ.baseMap)).trans
          (Category.assoc z.toBase (B.inclusion.map f) (B.inclusion.map φ.baseMap)).symm)))

/-- The fill-in composes with `φ` to `ψ` on total spaces. -/
theorem fillInTotalMap_comp_totalMap {x y z : PolarizedFamily B} (φ : y ⟶ x) (ψ : z ⟶ x)
    (f : z.base ⟶ y.base) (hcomm : f ≫ φ.baseMap = ψ.baseMap) :
    fillInTotalMap φ ψ f hcomm ≫ φ.totalMap = ψ.totalMap :=
  φ.cartesian.lift_fst _ _ _

/-- The fill-in lies over the base map `f`. -/
theorem fillInTotalMap_comp_toBase {x y z : PolarizedFamily B} (φ : y ⟶ x) (ψ : z ⟶ x)
    (f : z.base ⟶ y.base) (hcomm : f ≫ φ.baseMap = ψ.baseMap) :
    fillInTotalMap φ ψ f hcomm ≫ y.toBase = z.toBase ≫ B.inclusion.map f :=
  φ.cartesian.lift_snd _ _ _

/-- The square of structure morphisms of the fill-in is cartesian. -/
theorem isPullback_fillInTotalMap {x y z : PolarizedFamily B} (φ : y ⟶ x) (ψ : z ⟶ x)
    (f : z.base ⟶ y.base) (hcomm : f ≫ φ.baseMap = ψ.baseMap) :
    IsPullback (fillInTotalMap φ ψ f hcomm) z.toBase y.toBase (B.inclusion.map f) := by
  refine IsPullback.of_right ?_ (fillInTotalMap_comp_toBase φ ψ f hcomm) φ.cartesian
  rw [fillInTotalMap_comp_totalMap φ ψ f hcomm, ← B.inclusion.map_comp, hcomm]
  exact ψ.cartesian

/-- The fill-in for polarized families: given `φ : y ⟶ x`, `ψ : z ⟶ x` and a morphism `f` of base
schemes with `f ≫ φ.baseMap = ψ.baseMap`, the morphism `z ⟶ y` over `f` whose composite with `φ`
is `ψ`. Its map of total spaces is induced by the cartesian square of `φ`, and its comparison of
polarizations is that of `ψ` read through that of `φ`. -/
def fillIn {x y z : PolarizedFamily B} (φ : y ⟶ x) (ψ : z ⟶ x) (f : z.base ⟶ y.base)
    (hcomm : f ≫ φ.baseMap = ψ.baseMap) : z ⟶ y where
  baseMap := f
  totalMap := fillInTotalMap φ ψ f hcomm
  cartesian := isPullback_fillInTotalMap φ ψ f hcomm
  lineBundleIso :=
    ((Scheme.Modules.pullback (fillInTotalMap φ ψ f hcomm)).mapIso φ.lineBundleIso).symm ≪≫
      ((Scheme.Modules.pullbackComp (fillInTotalMap φ ψ f hcomm) φ.totalMap).symm.app
        x.lineBundle).symm ≪≫
        eqToIso (congrArg (fun k => (Scheme.Modules.pullback k).obj x.lineBundle)
          (fillInTotalMap_comp_totalMap φ ψ f hcomm)) ≪≫ ψ.lineBundleIso

/-- The base map of the fill-in is the given morphism of base schemes. -/
@[simp]
theorem fillIn_baseMap {x y z : PolarizedFamily B} (φ : y ⟶ x) (ψ : z ⟶ x)
    (f : z.base ⟶ y.base) (hcomm : f ≫ φ.baseMap = ψ.baseMap) :
    (fillIn φ ψ f hcomm).baseMap = f := rfl

/-- The fill-in composes with `φ` to `ψ`. -/
theorem fillIn_comp {x y z : PolarizedFamily B} (φ : y ⟶ x) (ψ : z ⟶ x) (f : z.base ⟶ y.base)
    (hcomm : f ≫ φ.baseMap = ψ.baseMap) : fillIn φ ψ f hcomm ≫ φ = ψ := by
  refine Hom.ext hcomm (fillInTotalMap_comp_totalMap φ ψ f hcomm) ?_
  refine HEq.trans (heq_of_eq ?_)
    (eqToIso_trans_heq (congrArg (fun k => (Scheme.Modules.pullback k).obj x.lineBundle)
      (fillInTotalMap_comp_totalMap φ ψ f hcomm)) ψ.lineBundleIso)
  rw [lineBundleIso_comp]
  exact Iso.ext (by simp [fillIn])

end PolarizedFamily

/-! ### Uniqueness of fill-ins -/

/-- For morphisms `φ : y ⟶ x` and `ψ : z ⟶ x` of
polarized families and a morphism `f` of their base schemes with `f ≫ φ.baseMap = ψ.baseMap`,
there is a unique morphism `z ⟶ y` over `f` whose composite with `φ` is `ψ`. -/
theorem polarizedProjection_uniqueLift {B : BigFppfSite.{u}} {x y z : PolarizedFamily B}
    (φ : y ⟶ x) (ψ : z ⟶ x)
    (f : (polarizedProjection B).obj z ⟶ (polarizedProjection B).obj y)
    (hcomm : f ≫ (polarizedProjection B).map φ = (polarizedProjection B).map ψ) :
    ∃! χ : z ⟶ y, (polarizedProjection B).map χ = f ∧ χ ≫ φ = ψ :=
  ⟨PolarizedFamily.fillIn φ ψ f hcomm, ⟨rfl, PolarizedFamily.fillIn_comp φ ψ f hcomm⟩,
    fun _ hη => PolarizedFamily.Hom.eq_of_comp_eq φ hη.1
      (hη.2.trans (PolarizedFamily.fillIn_comp φ ψ f hcomm).symm)⟩

/-! ### Existence of lifts -/

namespace PolarizedFamily

variable {B : BigFppfSite.{u}}

/-- The polarization of a polarized family stays invertible after base change along a morphism of
base schemes. -/
theorem isInvertible_pullback_lineBundle (x : PolarizedFamily B) {V : B.Schemes}
    (g : V ⟶ x.base) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (Limits.pullback x.toBase (B.inclusion.map g)).presheaf
      (Limits.pullback x.toBase (B.inclusion.map g)).ringCatSheaf.2
      ((Scheme.Modules.pullback (Limits.pullback.fst x.toBase (B.inclusion.map g))).obj
        x.lineBundle) :=
  have := x.invertible
  Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback
    (Limits.pullback.fst x.toBase (B.inclusion.map g)).toLRSHom.toShHom x.lineBundle

/-- The base change of a polarized family along a morphism `g : V ⟶ x.base` of base schemes: the
total space is the fibre product, the polarization is pulled back along the projection, and
`hample` is the relative ampleness of the pulled back polarization. -/
def baseChange (x : PolarizedFamily B) {V : B.Schemes} (g : V ⟶ x.base)
    (hample :
      letI := x.isInvertible_pullback_lineBundle g
      Stacks.RelativeAmple.IsRelativelyAmple (Limits.pullback.snd x.toBase (B.inclusion.map g))
        ((Scheme.Modules.pullback (Limits.pullback.fst x.toBase (B.inclusion.map g))).obj
          x.lineBundle)) : PolarizedFamily B where
  base := V
  total := Limits.pullback x.toBase (B.inclusion.map g)
  toBase := Limits.pullback.snd x.toBase (B.inclusion.map g)
  proper := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback x.toBase (B.inclusion.map g)) x.proper
  flat := MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat)
    (IsPullback.of_hasPullback x.toBase (B.inclusion.map g)) x.flat
  finitePresentation :=
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @LocallyOfFinitePresentation)
        (IsPullback.of_hasPullback x.toBase (B.inclusion.map g)) x.finitePresentation.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact)
        (IsPullback.of_hasPullback x.toBase (B.inclusion.map g)) x.finitePresentation.2.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiSeparated)
        (IsPullback.of_hasPullback x.toBase (B.inclusion.map g)) x.finitePresentation.2.2⟩
  lineBundle :=
    (Scheme.Modules.pullback (Limits.pullback.fst x.toBase (B.inclusion.map g))).obj x.lineBundle
  invertible := x.isInvertible_pullback_lineBundle g
  relativelyAmple := hample

/-- The morphism of polarized families carried by a base change: the projections of the fibre
product, with the identity comparison of polarizations. -/
def baseChangeHom (x : PolarizedFamily B) {V : B.Schemes} (g : V ⟶ x.base)
    (hample :
      letI := x.isInvertible_pullback_lineBundle g
      Stacks.RelativeAmple.IsRelativelyAmple (Limits.pullback.snd x.toBase (B.inclusion.map g))
        ((Scheme.Modules.pullback (Limits.pullback.fst x.toBase (B.inclusion.map g))).obj
          x.lineBundle)) : x.baseChange g hample ⟶ x where
  baseMap := g
  totalMap := Limits.pullback.fst x.toBase (B.inclusion.map g)
  cartesian := IsPullback.of_hasPullback x.toBase (B.inclusion.map g)
  lineBundleIso := Iso.refl _

/-- The base change of a polarized family has the given scheme as its base. -/
@[simp]
theorem baseChange_base (x : PolarizedFamily B) {V : B.Schemes} (g : V ⟶ x.base) (hample) :
    (x.baseChange g hample).base = V := rfl

/-- The morphism carried by a base change has the given morphism of base schemes as its base
map. -/
@[simp]
theorem baseChangeHom_baseMap (x : PolarizedFamily B) {V : B.Schemes} (g : V ⟶ x.base) (hample) :
    (x.baseChangeHom g hample).baseMap = g := rfl

end PolarizedFamily

/-- Given `AlgebraicGeometry.Scheme.Modules.RelativelyAmpleBaseChange`, every morphism of base
schemes lifts to a morphism of polarized families into any polarized family over its target. -/
theorem polarizedProjection_existsLift {B : BigFppfSite.{u}}
    (hbc : Scheme.Modules.RelativelyAmpleBaseChange.{u}) {V U : B.Schemes} (f : V ⟶ U)
    (x : PolarizedFamily B) (hx : (polarizedProjection B).obj x = U) :
    ∃ (y : PolarizedFamily B) (φ : y ⟶ x), (polarizedProjection B).IsHomLift f φ := by
  subst hx
  have := x.invertible
  have := x.isInvertible_pullback_lineBundle f
  have hample :
      Stacks.RelativeAmple.IsRelativelyAmple (Limits.pullback.snd x.toBase (B.inclusion.map f))
        ((Scheme.Modules.pullback (Limits.pullback.fst x.toBase (B.inclusion.map f))).obj
          x.lineBundle) :=
    hbc (IsPullback.of_hasPullback x.toBase (B.inclusion.map f)) x.lineBundle x.relativelyAmple
  exact ⟨x.baseChange f hample, x.baseChangeHom f hample,
    Functor.IsHomLift.map (p := polarizedProjection B) (x.baseChangeHom f hample)⟩

/-! ### Fibredness in groupoids -/

/-- Given `AlgebraicGeometry.Scheme.Modules.RelativelyAmpleBaseChange`, polarized families form a
category fibred in groupoids over the big fppf site. -/
theorem polarizedProjection_isFiberedInGroupoids {B : BigFppfSite.{u}}
    (hbc : Scheme.Modules.RelativelyAmpleBaseChange.{u}) :
    (polarizedProjection B).IsFiberedInGroupoids where
  exists_lift f x hx := polarizedProjection_existsLift hbc f x hx
  unique_lift φ ψ f hcomm := polarizedProjection_uniqueLift φ ψ f hcomm

end AlgebraicGeometry

end
